# diff_oracle

Cross-check golden ALU / program vectors shared with Lean `DiffTests.lean`.

## Quick check (no Rust)

```bash
python3 tools/diff_oracle/check_vectors.py
```

## Optional: blueshift sbpf

```bash
git clone --depth 1 https://github.com/blueshift-gg/sbpf.git /tmp/sbpf
cd /tmp/sbpf && cargo test -p sbpf-common execute
```

Map failures against `vectors.json` `classic` entries (same numbers as
`test_add64_imm`, etc.).

## Lean

```bash
lake build SbpfSemantics.DiffTests
lake build SbpfSemantics.EncodeSem
```

## Vector format

See `vectors.json`. `r1_out: null` means the step is stuck (`none` / division by zero).
