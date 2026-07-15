import SbpfSemantics.Instr
import SbpfSemantics.EncodePreserve
import SbpfSemantics.ByteBisim
import SbpfSemantics.Interp

/-!
# SbpfSemantics.Corpus

Hand-written L2 programs used as regression corpus (no text parser).
-/

namespace SbpfSemantics.Corpus

open SbpfSemantics

private def r0 : Reg := ⟨0, by omega⟩
private def r1 : Reg := ⟨1, by omega⟩

def fibIter : Program :=
  -- r0 = n, compute rough loop: for demo just n steps of add
  #[
    .binImm .Mov64Imm r0 5#64,       -- n
    .binImm .Mov64Imm r1 0#64,       -- acc
    -- loop head at index 2: if r0 == 0 goto exit
    .jumpImm .JeqImm r0 0#64 (BitVec.ofInt 16 3),
    .binImm .Add64Imm r1 1#64,
    .binImm .Sub64Imm r0 1#64,
    .ja (BitVec.ofInt 16 (-4)),
    .binReg .Mov64Reg r0 r1,
    .exit
  ]

def maskBits : Program :=
  #[
    .binImm .Mov64Imm r0 0xff00#64,
    .binImm .And64Imm r0 0x0ff0#64,
    .binImm .Or64Imm r0 0x000f#64,
    .exit
  ]

def allCorpus : Array Program :=
  #[fibIter, maskBits] ++ bisimProgs

def corpusHalts : Bool :=
  allCorpus.all fun P =>
    match (runFuel closedExec P 256 (Machine.entry)).2 with
    | .halted _ => true
    | _ => false

theorem corpus_halts : corpusHalts = true := by
  native_decide

def corpusRoundTripEncode : Bool :=
  allCorpus.all fun P =>
    match redecodeProgram? P with
    | some P' => P'.size == P.size
    | none => false

theorem corpus_redecode_size : corpusRoundTripEncode = true := by
  native_decide

end SbpfSemantics.Corpus
