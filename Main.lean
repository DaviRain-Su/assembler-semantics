import SbpfSemantics

/-- Library status entry point. -/
def main : IO Unit := do
  IO.println "assembler-semantics 0.1.0 — sBPF ISA semantics (Lean 4)"
  IO.println "  import SbpfSemantics.Api          — stable ProofForge surface"
  IO.println "  import SbpfSemantics.CounterScenario — Counter init/inc/get goldens"
  IO.println "  See DESIGN.md and docs/proof-forge-interface.md"
