#!/usr/bin/env python3
"""Audit the mathematical UNSAT classification of all original unknown QF_BV files.

Run lake build first. Source status labels remain unchanged. Optional exhaustive
small-width evaluation is independent of the symbolic identity proofs.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import re
import subprocess

from audit_library import strip_comments
from audit_qfbv_sat import ROOT, check_axioms, evaluate, lean_term, parse_expression


def collect() -> list[dict]:
    sources = {int(p.stem.rsplit("_", 1)[1]): p for p in (ROOT / "BV/QF_BV/unsat").glob("*.smt2")
               if "(set-info :status unknown)" in p.read_text()}
    translations = {int(p.stem.rsplit("_", 1)[1]): p for p in (ROOT / "BV_LEAN/QF_BV/unsat").glob("*.lean")}
    assert sources.keys() <= translations.keys(), {
        "missing": sorted(sources.keys() - translations.keys()),
        "extra": sorted(translations.keys() - sources.keys()),
    }
    rows = []
    for number, source in sorted(sources.items()):
        raw = source.read_text()
        assert "(set-info :status unknown)" in raw, source
        assert re.findall(r"\(declare-fun ([st]) \(\) \(_ BitVec (\d+)\)\)", raw) == [("s", "32"), ("t", "32")], source
        assertions = [line for line in raw.splitlines() if line.startswith("(assert")]
        assert len(assertions) == 1, source
        assertion = parse_expression(assertions[0])
        assert assertion[0] == "assert" and assertion[1][0] == "not" and assertion[1][1][0] == "=", source
        left, right = assertion[1][1][1:]
        path = translations[number]
        code = strip_comments(path.read_text())
        assert not re.search(r"\b(sorry|admit|axiom|native_decide|bv_decide)\b", code), path
        name = f"bv_term_small_rw_{number}"
        compact = lambda s: re.sub(r"\s+", "", s)
        l, r = lean_term(left), lean_term(right)
        identity = re.search(r"theorem " + name + r"\s*:\s*∀ \(n : Nat\) \(s t : BitVec n\),\s*(.*?) := by", code, re.S)
        assert identity and compact(identity[1]) == compact(f"{l} = {r}"), f"Identity mismatch: {path}"
        declarations = re.findall(r"^theorem\s+(\w+)", code, re.M)
        assert declarations == [name], path
        rows.append({"rule": number, "name": name, "left": left, "right": right,
                     "classification": "unsat", "module": ".".join(path.relative_to(ROOT).with_suffix("").parts),
                     "declarations": ["BV.QF_BV.Unsat." + decl for decl in declarations]})
    return rows


def verify_small(rows: list[dict], max_width: int, output: Path) -> int:
    source = output / "qfbv-unknown-small.lean"
    header = """
open SMT.BitVec
set_option maxRecDepth 10000
set_option linter.unusedVariables false
def checkIdentity (n : Nat) (test : BitVec n → BitVec n → Bool) : Bool :=
  (List.range (2 ^ n)).all fun a =>
    (List.range (2 ^ n)).all fun b => test (literal n a) (literal n b)
"""
    commands = []
    for row in rows:
        expr = f"{lean_term(row['left'])} = {lean_term(row['right'])}"
        for n in range(max_width + 1):
            commands.append(f'#eval IO.println ("{row["rule"]} {n} " ++ toString (let n := {n}; checkIdentity n (fun s t => decide ({expr}))))')
    source.write_text("\n".join(["import " + row["module"] for row in rows]) + header + "\n".join(commands) + "\n")
    result = subprocess.run(["lake", "env", "lean", str(source)], cwd=ROOT, text=True, capture_output=True)
    (output / "qfbv-unknown-small.txt").write_text(result.stdout)
    if result.returncode:
        raise RuntimeError(result.stdout + result.stderr)
    expected = [f"{row['rule']} {n} true" for row in rows for n in range(max_width + 1)]
    assert result.stdout.splitlines() == expected, "Lean evaluation found a mismatch"
    checked = 0
    for row in rows:
        for n in range(max_width + 1):
            for a in range(1 << n):
                for b in range(1 << n):
                    assert evaluate(row["left"], n, a, b) == evaluate(row["right"], n, a, b), (row["rule"], n, a, b)
                    checked += 1
    return checked


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--verify-small", type=int, metavar="MAX_WIDTH", help="Exhaustively check widths 0..MAX_WIDTH (0..8)")
    args = parser.parse_args()
    if args.verify_small is not None and not 0 <= args.verify_small <= 8:
        parser.error("--verify-small must be between 0 and 8")
    rows = collect()
    output = ROOT / ".lake"
    output.mkdir(exist_ok=True)
    axioms, declaration_count = check_axioms(rows, output,
        support_module="BV_LEAN.QF_BV.UnsatSupport", namespace="BV.QF_BV.Unsat", report_stem="qfbv-unknown")
    checked = verify_small(rows, args.verify_small, output) if args.verify_small is not None else None
    report = {
        "status": "passed", "source_correspondences": len(rows),
        "classified_unsat": len(rows), "classified_sat": 0, "unresolved": 0,
        "arbitrary_width_identity_proofs": len(rows),
        "checked_declarations": declaration_count, "axioms": axioms, "sorryAx": False,
        "small_width_max": args.verify_small, "exhaustive_assignment_checks": checked,
    }
    (output / "qfbv-unknown-audit.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
