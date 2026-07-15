import SbpfSemantics.Basic
import SbpfSemantics.Machine
import SbpfSemantics.Dialect

/-!
# SbpfSemantics.Host

Richer executable host effects: log stubs, abort-as-halt, and memory syscalls
(`sol_memcpy_`, `sol_memmove_`, `sol_memset_`, `sol_memcmp_`) with the Solana
register convention **args in `r1`–`r5`**, return in `r0` (set by `execSyscall`).
-/

namespace SbpfSemantics

/-- Syscall argument registers: `r1` … `r5`. -/
def Machine.arg (m : Machine) (i : Fin 5) : Word :=
  m.getReg ⟨i.val + 1, by omega⟩

/-- Result of a host call before the ISA layer writes `r0` / advances PC.
If `halted` is already set, `execSyscall` will not advance PC. -/
abbrev HostResult := Machine × Word

def hostLog (m : Machine) : HostResult := (m, word0)

def hostAbort (m : Machine) : HostResult :=
  (m.halt 1#64, word0)

def hostMemcpy (m : Machine) : Option HostResult := do
  let dst := m.arg 0
  let src := m.arg 1
  let n := (m.arg 2).toNat
  if !(Memory.nonoverlapping src.toNat n dst.toNat n) then none
  else do
    let data ← m.mem.readBytes src n
    let mem ← m.mem.writeBytes dst data
    pure ({ m with mem := mem }, word0)

def hostMemmove (m : Machine) : Option HostResult := do
  let dst := m.arg 0
  let src := m.arg 1
  let n := (m.arg 2).toNat
  let data ← m.mem.readBytes src n
  let mem ← m.mem.writeBytes dst data
  pure ({ m with mem := mem }, word0)

def hostMemset (m : Machine) : Option HostResult := do
  let dst := m.arg 0
  let c := UInt8.ofNat ((m.arg 1).toNat &&& 0xff)
  let n := (m.arg 2).toNat
  let mem ← m.mem.memset dst c n
  pure ({ m with mem := mem }, word0)

/-- `sol_memcmp_`: compare `n` bytes; store signed `i32` result at `r4`. -/
def hostMemcmp (m : Machine) : Option HostResult := do
  let s1 := m.arg 0
  let s2 := m.arg 1
  let n := (m.arg 2).toNat
  let resultPtr := m.arg 3
  let a ← m.mem.readBytes s1 n
  let b ← m.mem.readBytes s2 n
  let rec cmp (i : Nat) : Int :=
    if i ≥ n then 0
    else
      let da := a[i]!.toNat
      let db := b[i]!.toNat
      if da == db then cmp (i + 1)
      else (da : Int) - (db : Int)
  let diff := cmp 0
  -- saturate to i32 range for storage
  let diff32 : Word := BitVec.ofInt 64 (max (-(2^31)) (min (2^31 - 1) diff))
  let mem ← m.mem.writeU32 resultPtr diff32
  pure ({ m with mem := mem }, word0)

/-- `sol_set_return_data(ptr, len)` — args `r1`, `r2`. -/
def hostSetReturnData (m : Machine) : Option HostResult := do
  let ptr := m.arg 0
  let n := (m.arg 1).toNat
  let data ← m.mem.readBytes ptr n
  pure ({ m with returnData := data }, word0)

/-- `sol_get_return_data` simplified: write length to `r0` via return value;
copy min(len, buf_len) bytes to `r1` buffer; `r2` is buf capacity.
Full Solana ABI also returns program id; we only model the data blob. -/
def hostGetReturnData (m : Machine) : Option HostResult := do
  let dst := m.arg 0
  let cap := (m.arg 1).toNat
  let n := min cap m.returnData.size
  let slice := m.returnData.extract 0 n
  let mem ← m.mem.writeBytes dst slice
  pure ({ m with mem := mem }, BitVec.ofNat 64 m.returnData.size)

/-- Dispatch known host ops; `none` means stuck. -/
def hostSyscallFn (name : String) (m : Machine) : Option HostResult :=
  if isLogSyscall name then some (hostLog m)
  else if name == "abort" || name == "sol_panic_" then some (hostAbort m)
  else if name == "sol_memcpy_" then hostMemcpy m
  else if name == "sol_memmove_" then hostMemmove m
  else if name == "sol_memset_" then hostMemset m
  else if name == "sol_memcmp_" then hostMemcmp m
  else if name == "sol_set_return_data" then hostSetReturnData m
  else if name == "sol_get_return_data" then hostGetReturnData m
  else none

/-- Relational image of `hostSyscallFn`. -/
def hostDialect : Dialect where
  Syscall := fun name m m' r => hostSyscallFn name m = some (m', r)

def hostExec : ExecDialect where
  toDialect := hostDialect
  syscallFn := hostSyscallFn
  lawful := by
    intro name m m' r h
    exact h

end SbpfSemantics
