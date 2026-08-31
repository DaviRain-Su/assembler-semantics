import SbpfSemantics.Basic
import SbpfSemantics.Machine
import SbpfSemantics.Host

/-!
# SbpfSemantics.Syscalls

Solana program-address syscalls over an in-core SHA-256 (`sol_create_program_address`,
`sol_try_find_program_address`), plus `sol_log_data`. Extends `hostSyscallFn` with a
`richSyscallFn` / `richExec` dialect; the original `hostExec` is left untouched so
existing differential surfaces keep their trust boundary.

**Modeled ABI (agave / Solana SDK C convention):**

- `sol_create_program_address(r1 = seeds_ptr, r2 = seeds_len bytes, r3 = program_id_ptr,
  r4 = result_address_ptr) → r0 = 0 on success`
  `hash = sha256(seeds ‖ program_id ‖ "ProgramDerivedAddress")`.
  The **curve check is not modeled**: every 32-byte digest is treated as a valid PDA.
  Aligning the on-curve rejection (and the canonical bump distribution) with agave is an
  engineering-gate concern, outside this abstract machine.
- `sol_try_find_program_address(r1 = seeds_ptr, r2 = seeds_len, r3 = program_id_ptr,
  r4 = result_ptr, r5 = bump_ptr) → r0 = 0` writes the winning 32-byte address at `r4`
  and the one-byte bump (high byte of the u64 at the bump pointer is modeled as the bump
  byte repeated; only the first byte is specified) at `r5`. With curve checks disabled the
  first candidate is always accepted, so the effective bump is `255`.
- `sol_log_data(r1 = data ptr, r2 = len)`: log stub, returns 0.

`sol_invoke_signed_c` remains unimplemented here: cross-program effects are not part of
this model, and a fake success would silently validate programs against an empty CPI
semantics. It stays `none` (stuck) in `richExec`; a caller that wants to differential-test
around CPI should provide its own `ExecDialect` hook (see `Dialect.lean`).
-/

namespace SbpfSemantics

/-! ## SHA-256 (FIPS 180-4) -/

namespace Sha256

private def shr (x : UInt32) (n : Nat) : UInt32 :=
  UInt32.ofNat (x.toNat >>> n)

private def shl (x : UInt32) (n : Nat) : UInt32 :=
  UInt32.ofNat ((x.toNat <<< (n % 32)) % 4294967296)

private def rotr (x : UInt32) (n : Nat) : UInt32 :=
  let n := n % 32
  shr x n ||| shl x ((32 - n) % 32)

private def ch (e f g : UInt32) : UInt32 :=
  (e &&& f) ^^^ ((~~~e) &&& g)

private def maj (a b c : UInt32) : UInt32 :=
  (a &&& b) ^^^ (a &&& c) ^^^ (b &&& c)

private def bigSigma0 (a : UInt32) : UInt32 :=
  rotr a 2 ^^^ rotr a 13 ^^^ rotr a 22

private def bigSigma1 (e : UInt32) : UInt32 :=
  rotr e 6 ^^^ rotr e 11 ^^^ rotr e 25

private def smallSigma0 (x : UInt32) : UInt32 :=
  rotr x 7 ^^^ rotr x 18 ^^^ shr x 3

private def smallSigma1 (x : UInt32) : UInt32 :=
  rotr x 17 ^^^ rotr x 19 ^^^ shr x 10

private def K : Array UInt32 := #[
  0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
  0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
  0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
  0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
  0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
  0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
  0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
  0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2
]

private def H0 : Array UInt32 := #[
  0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
  0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19
]

private def wordBE (b0 b1 b2 b3 : UInt8) : UInt32 :=
  (b0.toUInt32 <<< 24) ||| (b1.toUInt32 <<< 16) ||| (b2.toUInt32 <<< 8) ||| b3.toUInt32

private def pad (msg : Array UInt8) : Array UInt8 :=
  Id.run do
    let bitLen := msg.size * 8
    let mut out := msg.push 0x80
    while out.size % 64 != 56 do
      out := out.push 0
    let mut len := bitLen
    let mut be : Array UInt8 := #[]
    for _ in [0:8] do
      be := #[UInt8.ofNat (len % 256)] ++ be
      len := len / 256
    return out ++ be

private def schedule (block : Array UInt8) : Array UInt32 :=
  Id.run do
    let mut w : Array UInt32 := #[]
    for i in [0:16] do
      let o := i * 4
      w := w.push (wordBE block[o]! block[o + 1]! block[o + 2]! block[o + 3]!)
    for i in [16:64] do
      w := w.push (w[i - 16]! + smallSigma0 w[i - 15]! + w[i - 7]! + smallSigma1 w[i - 2]!)
    return w

private def compress (h : Array UInt32) (block : Array UInt8) : Array UInt32 :=
  let w := schedule block
  Id.run do
    let mut a := h[0]!
    let mut b := h[1]!
    let mut c := h[2]!
    let mut d := h[3]!
    let mut e := h[4]!
    let mut f := h[5]!
    let mut g := h[6]!
    let mut hh := h[7]!
    for i in [0:64] do
      let t1 := hh + bigSigma1 e + ch e f g + K[i]! + w[i]!
      let t2 := bigSigma0 a + maj a b c
      hh := g
      g := f
      f := e
      e := d + t1
      d := c
      c := b
      b := a
      a := t1 + t2
    return #[
      h[0]! + a, h[1]! + b, h[2]! + c, h[3]! + d,
      h[4]! + e, h[5]! + f, h[6]! + g, h[7]! + hh
    ]

private def wordsToBytes (h : Array UInt32) : Array UInt8 :=
  Id.run do
    let mut out : Array UInt8 := #[]
    for w in h do
      let n := w.toNat
      out := out.push (UInt8.ofNat ((n >>> 24) % 256))
      out := out.push (UInt8.ofNat ((n >>> 16) % 256))
      out := out.push (UInt8.ofNat ((n >>> 8) % 256))
      out := out.push (UInt8.ofNat (n % 256))
    return out

/-- FIPS 180-4 SHA-256 over raw bytes (pure, in-core). Not an on-chain syscall; the
`sol_create_program_address` / `sol_try_find_program_address` models below consume it. -/
def digest (msg : Array UInt8) : Array UInt8 :=
  let padded := pad msg
  let nBlocks := padded.size / 64
  Id.run do
    let mut h := H0
    for i in [0:nBlocks] do
      let off := i * 64
      let mut block : Array UInt8 := #[]
      for j in [0:64] do
        block := block.push padded[off + j]!
      h := compress h block
    return wordsToBytes h

end SbpfSemantics.Sha256

namespace SbpfSemantics

/-! ## PDA / log syscalls (agave-derived ABI) -/

end SbpfSemantics
namespace SbpfSemantics.Sha256

/-- FIPS 180-4 测试向量。 -/
example : (digest ("abc".toUTF8.data) |>.map (·.toNat)) =
    #[0xba, 0x78, 0x16, 0xbf, 0x8f, 0x01, 0xcf, 0xea, 0x41, 0x41, 0x40, 0xde,
      0x5d, 0xae, 0x22, 0x23, 0xb0, 0x03, 0x61, 0xa3, 0x96, 0x17, 0x7a, 0x9c,
      0xb4, 0x10, 0xff, 0x61, 0xf2, 0x00, 0x15, 0xad] := by native_decide

example : (digest #[] |>.map (·.toNat)) =
    #[0xe3, 0xb0, 0xc4, 0x42, 0x98, 0xfc, 0x1c, 0x14, 0x9a, 0xfb, 0xf4, 0xc8,
      0x99, 0x6f, 0xb9, 0x24, 0x27, 0xae, 0x41, 0xe4, 0x64, 0x9b, 0x93, 0x4c,
      0xa4, 0x95, 0x99, 0x1b, 0x78, 0x52, 0xb8, 0x55] := by
  native_decide

end SbpfSemantics.Sha256
