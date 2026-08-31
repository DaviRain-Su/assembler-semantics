import SbpfSemantics.Basic
import SbpfSemantics.Machine
import SbpfSemantics.Dialect
import SbpfSemantics.Step
import SbpfSemantics.Run
import SbpfSemantics.Sha256

/-!
# SbpfSemantics.Syscalls

PDA / log / CPI syscalls following the **agave C ABI** (args `r1`–`r5`,
result in `r0`). These cover the syscall surface that ProofForge's emitted
programs reach on top of the memory/return-data set in `Host.lean`.

Modeled (documented, deliberate) abstractions:

- **Curve check is not modeled**: every SHA-256 digest is accepted as a
  valid PDA. Consequences: `hostTryFindProgramAddress` always succeeds at
  `bump = 255`, and byte equality of a `create_program_address` digest with
  an observed PDA is the only meaningful differential (agave's bump
  distribution may differ). Downstream differentials must pin addresses via
  this library's own goldens, not via live RPC dumps.
- **`sol_invoke_signed_c` is a placeholder**: cross-program effects are not
  modeled. The default rich dispatch rejects it (stuck), so forgetting the
  hook fails closed; `invokeExec` lets a caller install an explicit,
  reviewed CPI effect handler.

## ABI notes

- `sol_create_program_address(seeds_ptr r1, seeds_len r2, program_id r3, out r4) → r0`
- `sol_try_find_program_address(seeds_ptr r1, seeds_len r2, program_id r3,
  out r4, bump_out r5) → r0`
- `sol_log_data(data r1, len r2) → r0` (no effect)
- `sol_invoke_signed_c(accounts r1, accounts_len r2, data r3, data_len r4,
  signers_seeds r5) → r0` (dispatch-dependent)
-/

namespace SbpfSemantics

/-- `seeds ‖ program_id ‖ "ProgramDerivedAddress"`. -/
def pdaDomainTag : Array UInt8 :=
  "ProgramDerivedAddress".toUTF8.data

def pdaInput (seeds programId : Array UInt8) : Array UInt8 :=
  seeds ++ programId ++ pdaDomainTag

/-- One `create_program_address` digest; `bump = none` appends no bump byte. -/
def pdaDigest (seeds programId : Array UInt8) (bump : Option UInt8) : Array UInt8 :=
  let suffix :=
    match bump with
    | none => #[]
    | some b => #[b]
  Sha256.digest (pdaInput (seeds ++ suffix) programId)

/-- `sol_create_program_address`: writes the 32-byte digest of
`seeds ‖ program_id ‖ "ProgramDerivedAddress"` at `r4`, returns `0`.
Stuck if any input region is out of bounds. -/
def hostCreateProgramAddress (m : Machine) : Option HostResult := do
  let seedsPtr := m.arg ⟨0, by omega⟩
  let seedsLen := (m.arg ⟨1, by omega⟩).toNat
  let progId := m.arg ⟨2, by omega⟩
  let out := m.arg ⟨3, by omega⟩
  let seeds ← m.mem.readBytes seedsPtr seedsLen
  let programIdBytes ← m.mem.readBytes progId 32
  let addr := Sha256.digest (pdaInput seeds programIdBytes)
  let mem ← m.mem.writeBytes out addr
  pure ({ m with mem := mem }, word0)

/-- `sol_try_find_program_address`: search bump candidates from 255
downwards; success (`r0 = 0`) writes the 32-byte address at `r4` and the
winning bump as a single byte at `r5`. Stuck if any region is out of
bounds. Curve check omitted => the winning bump is 255. -/
def hostTryFindProgramAddress (m : Machine) : Option HostResult := do
  let seedsPtr := m.arg ⟨0, by omega⟩
  let seedsLen := (m.arg ⟨1, by omega⟩).toNat
  let progId := m.arg ⟨2, by omega⟩
  let out := m.arg ⟨3, by omega⟩
  let bumpOut := m.arg ⟨4, by omega⟩
  let seeds ← m.mem.readBytes seedsPtr seedsLen
  let programIdBytes ← m.mem.readBytes progId 32
  let bump : UInt8 := 255
  let addr := pdaDigest seeds programIdBytes (some bump)
  let mem1 ← m.mem.writeBytes out addr
  let mem2 ← mem1.writeBytes bumpOut #[bump]
  pure ({ m with mem := mem2 }, word0)

/-! ### Rich dispatch -/

/-- Rich syscall table: everything from `hostSyscallFn` plus the agave-ABI
syscalls modeled here. -/
def richSyscallFn (name : String) (m : Machine) : Option HostResult :=
  if name == "sol_create_program_address" then hostCreateProgramAddress m
  else if name == "sol_try_find_program_address" then hostTryFindProgramAddress m
  else if name == "sol_log_data" then some (hostLog m)
  else hostSyscallFn name m

/-- Rich dialect: the executable rich syscall table, as a relation.
The post-state and return value are exactly those of `richSyscallFn`. -/
def richDialect : Dialect where
  Syscall := fun name m m' r => richSyscallFn name m = some (m', r)

/-- Rich executable host: `hostSyscallFn` plus PDA / log syscalls.
`sol_invoke_signed_c` is **not** in this table (stuck, fail-closed);
use `invokeExec` to install an explicit CPI hook. -/
def richExec : ExecDialect where
  toDialect :=
    { Syscall := fun name m m' r => richSyscallFn name m = some (m', r) }
  syscallFn := richSyscallFn
  lawful := by
    intro name m m' r h
    exact h

/-- One step under the rich host. -/
def richStep (P : Program) (m : Machine) : Option Machine :=
  execStep richExec P m

/-! ### Dispatch / PDA tests -/

/-- Empty input: seed region unreadable -> stuck (fail-closed). -/
example : (richSyscallFn "sol_create_program_address"
    (Machine.entry #[] #[])) = none := by native_decide

/-- PDA golden: empty seeds + all-`9` program id; the 32-byte digest lands
at the out pointer and `r0 = 0`. -/
def createAddressRun : Option (Array UInt8 × Word) := do
  -- input region: [0..32) = program id (all 9s); out window at base + 192
  let base : Word := inputStart
  let outAddr : Word := base + 192#64
  let m0 := Machine.entry #[] #[]
  -- r1 = seeds ptr (seeds_len = 0), r3 = program id ptr, r4 = out pointer
  let m := m0.setReg ⟨1, by omega⟩ base
  let m := m.setReg ⟨3, by omega⟩ base
  let m := m.setReg ⟨4, by omega⟩ outAddr
  let m := { m with mem := { m.mem with
    input := (Array.replicate 32 9) ++ (Array.replicate 256 0) } }
  match richSyscallFn "sol_create_program_address" m with
  | none => none
  | some (m', r) => do
      let bytes ← m'.mem.readBytes outAddr 32
      pure (bytes, r)

/-- The PDA digest lands at `out` with 32 bytes and `r0 = 0`, and equals the
pure-library `pdaDigest` for the same inputs. -/
def createAddressGolden : Bool :=
  match createAddressRun with
  | some (bytes, r) =>
      bytes.size == 32 && r == word0
        && bytes == pdaDigest #[] (Array.replicate 32 9) none
  | none => false

/-- PDA 端到端：syscall 写出的 32 字节摘要与纯库输出一致、r0 = 0。 -/
example : createAddressGolden = true := by
  native_decide


/-! ## try_find：bump = 255 端到端 -/

/-- `sol_try_find_program_address` golden：空 seeds、全 9 program id。
成功（r0 = 0）、地址 = `pdaDigest seeds prog (some 255)`、
bump 字节落在 `bump_out` 指针。 -/
def tryFindRun : Option (Array UInt8 × Word × Array UInt8) := do
  let base : Word := inputStart
  let outAddr : Word := base + 192#64
  let bumpAddr : Word := base + 256#64
  let m0 := Machine.entry #[] #[]
  let m := m0.setReg ⟨1, by omega⟩ base
  let m := m.setReg ⟨3, by omega⟩ base
  let m := m.setReg ⟨4, by omega⟩ outAddr
  let m := m.setReg ⟨5, by omega⟩ bumpAddr
  let m := { m with mem := { m.mem with
    input := (Array.replicate 32 9) ++ (Array.replicate 256 0) } }
  match richSyscallFn "sol_try_find_program_address" m with
  | none => none
  | some (m', r) => do
      let bytes ← m'.mem.readBytes outAddr 32
      let bumpBytes ← m'.mem.readBytes bumpAddr 1
      pure (bytes, r, bumpBytes)

/-- 端到端：输出地址 = 纯库 `pdaDigest … (some 255)`，bump 字节 = 255，
r0 = 0（无 curve 检查时的约定冠军）。 -/
def tryFindGolden : Bool :=
  match tryFindRun with
  | some (bytes, r, bumpBytes) =>
      bytes == pdaDigest #[] (Array.replicate 32 9) (some 255)
        && r == word0 && bumpBytes == #[255]
  | none => false

example : tryFindGolden = true := by
  native_decide

end SbpfSemantics
