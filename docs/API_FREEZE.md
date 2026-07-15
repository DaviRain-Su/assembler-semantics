# API freeze policy (assembly layer)

## Stable surface

Integrators should depend on:

```lean
import SbpfSemantics.Api
```

### Stable names (`asm*`)

| Symbol | Role |
|--------|------|
| `AsmProgram`, `AsmInstr`, `AsmMachine`, `AsmHost`, `AsmObservation` | Types |
| `asmClosedHost`, `asmDefaultHost`, `asmStubHost` | Hosts |
| `asmRun`, `asmRunMachine`, `asmStep` | List-PC execution |
| `asmStepBytes`, `asmRunBytes` | Byte-PC execution |
| `asmEncode`, `asmDecode?`, `asmEncodeInstr`, `asmDecodeInstr?` | L3 |
| `asmEncodable`, `asmSameExec`, `asmRoundTrip` | Encode checks |
| `asmEncodeInstr_size`, `asmEncode_size` | Encode length theorems |
| `asmV3SafeRoundTripWitnesses` | V3 opcode witness table |
| `asmIndexByteRoundtrip`, `asmIndexToByte_byteToIndex` | Layout index ↔ byte |
| `asmEntry`, `asmEntryCell`, `asmReadyForNext` | Machine setup |

### Compatibility aliases (`pf*`)

Same as `asm*` with old names. Prefer `asm*` for new code. Aliases remain at
least through **0.2.x**.

## Stability rules

**Semver-compatible (minor/patch):**

- New theorems, new optional helpers
- New host stubs
- Stronger proofs behind existing defs

**Semver-breaking (major):**

- Remove/rename `asm*` symbols
- Change `Observation` fields used by integrators
- Change step meaning of an existing opcode without a version flag
- Change `Machine` memory map constants

## Out of freeze

Internal modules (`Alu`, `Step` helpers, test-only programs) may change freely.

## Version

Current library version: **0.1.x** (`lakefile.toml` / `CHANGELOG.md`).
