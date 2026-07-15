#!/usr/bin/env python3
"""Validate tools/diff_oracle/vectors.json against a pure-Python reference.

Does not call blueshift/sbpf. Ensures checked-in goldens match the arithmetic
rules used in Lean (classic wraparound ALU + SIMD-0174 PQR basics).
"""

from __future__ import annotations

import json
import sys
from pathlib import Path

MASK64 = (1 << 64) - 1
MASK32 = (1 << 32) - 1


def u64(x: int) -> int:
    return x & MASK64


def i64(x: int) -> int:
    x = u64(x)
    return x - (1 << 64) if x >= (1 << 63) else x


def sext32(r: int) -> int:
    r &= MASK32
    if r & (1 << 31):
        return u64(r | ~MASK32)
    return r


def apply_op(op: str, r1: int, imm: int) -> int | None:
    a, b = u64(r1), u64(imm)
    if op == "Add64Imm":
        return u64(a + b)
    if op == "Sub64Imm":
        return u64(a - b)
    if op in ("Mul64Imm", "Lmul64Imm"):
        return u64(a * b)
    if op in ("Div64Imm", "Udiv64Imm"):
        return None if b == 0 else a // b
    if op in ("Mod64Imm", "Urem64Imm"):
        return None if b == 0 else a % b
    if op == "Or64Imm":
        return a | b
    if op == "And64Imm":
        return a & b
    if op == "Xor64Imm":
        return a ^ b
    if op == "Mov64Imm":
        return b
    if op == "Lsh64Imm":
        return u64(a << b) if b < 64 else 0
    if op == "Rsh64Imm":
        return a >> b if b < 64 else 0
    if op == "Arsh64Imm":
        sh = b if b < 64 else 63
        return u64(i64(a) >> sh)
    if op == "Neg64":
        return u64(-a)
    if op == "Neg32":
        # zero-extend of i32 negation bit pattern (sbpf)
        return u64((- (a & MASK32)) & MASK32)
    if op == "Add32Imm":
        return sext32((a & MASK32) + (b & MASK32))
    if op == "Sub32Imm":
        return sext32((a & MASK32) - (b & MASK32))
    if op == "Mul32Imm":
        return sext32((a & MASK32) * (b & MASK32))
    if op == "Lmul32Imm":
        return (a & MASK32) * (b & MASK32) & MASK32
    if op == "Udiv32Imm":
        aa, bb = a & MASK32, b & MASK32
        return None if bb == 0 else aa // bb
    if op == "Uhmul64Imm":
        return (a * b) >> 64
    if op == "Sdiv64Imm":
        if b == 0:
            return None
        aa, bb = i64(a), i64(b)
        if aa == -(1 << 63) and bb == -1:
            return None
        q = abs(aa) // abs(bb)
        if (aa < 0) != (bb < 0):
            q = -q
        return u64(q)
    if op == "Srem64Imm":
        if b == 0:
            return None
        aa, bb = i64(a), i64(b)
        if aa == -(1 << 63) and bb == -1:
            return None
        # toward-zero remainder: a - trunc(a/b)*b
        q = abs(aa) // abs(bb)
        if (aa < 0) != (bb < 0):
            q = -q
        return u64(aa - q * bb)
    raise KeyError(f"unsupported op {op}")


def main() -> int:
    path = Path(__file__).with_name("vectors.json")
    data = json.loads(path.read_text())
    failed = 0
    for section in ("classic", "pqr"):
        for v in data[section]:
            got = apply_op(v["op"], v["r1_in"], v["imm"])
            exp = v["r1_out"]
            if exp is None:
                ok = got is None
            else:
                ok = got == u64(exp)
            if not ok:
                failed += 1
                print(f"FAIL {section} {v}: got {got}")
            else:
                print(f"ok   {section} {v['op']} r1={v['r1_in']}")
    if failed:
        print(f"{failed} failure(s)", file=sys.stderr)
        return 1
    print("all vector checks passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
