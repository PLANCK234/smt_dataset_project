#!/usr/bin/env python3
"""Audit SAT source correspondence, complete solution proofs, and compiled axioms.

Run lake build first. Optionally compare the Lean arithmetic conditions against
an independent SMT-LIB evaluator on every input at small widths. No SMT solver
or nonstandard Python package is needed.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import re
import subprocess

from audit_library import strip_comments

ROOT = Path(__file__).resolve().parents[1]
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def parse_expression(source: str):
    tokens = iter(re.findall(r"\(|\)|[^\s()]+", source))

    def parse(token):
        if token != "(":
            return token
        result = []
        for token in tokens:
            if token == ")":
                return result
            result.append(parse(token))
        raise ValueError("Unclosed SMT-LIB expression")

    result = parse(next(tokens))
    assert next(tokens, None) is None, "Trailing SMT-LIB tokens"
    return result


def lean_term(term) -> str:
    if isinstance(term, str):
        if term.startswith("#b"):
            # Only width-polymorphic zero literals occur in these source assertions.
            assert len(term) == 34 and int(term[2:], 2) == 0, term
            return "(literal n 0)"
        assert term in {"s", "t"}, term
        return term
    op, *args = term
    assert op in {"bvnot", "bvneg", "bvadd", "bvmul", "bvand", "bvor", "bvshl", "bvlshr"}, op
    assert len(args) == (1 if op in {"bvnot", "bvneg"} else 2), term
    return "(" + " ".join([op, *(lean_term(arg) for arg in args)]) + ")"


def evaluate(term, n: int, a: int, b: int) -> int:
    """Independent finite-word semantics, with unsigned and nonwrapping counts."""
    if isinstance(term, str):
        if term == "s":
            return a
        if term == "t":
            return b
        return int(term[2:], 2)
    op, *args = term
    values = [evaluate(arg, n, a, b) for arg in args]
    x, y = values[0], values[-1]
    mask = (1 << n) - 1
    if op == "bvnot":
        return x ^ mask
    if op == "bvneg":
        return -x & mask
    if op == "bvadd":
        return (x + y) & mask
    if op == "bvmul":
        return x * y & mask
    if op == "bvand":
        return x & y
    if op == "bvor":
        return x | y
    if op == "bvshl":
        return 0 if y >= n else (x << y) & mask
    if op == "bvlshr":
        return 0 if y >= n else x >> y
    raise ValueError(op)


def collect() -> list[dict]:
    sources = {int(p.stem.rsplit("_", 1)[1]): p for p in (ROOT / "BV/QF_BV/sat").glob("*.smt2")}
    translations = {int(p.stem.rsplit("_", 1)[1]): p for p in (ROOT / "BV_LEAN/QF_BV/sat").glob("*.lean")}
    assert sources.keys() == translations.keys(), {
        "missing": sorted(sources.keys() - translations.keys()),
        "extra": sorted(translations.keys() - sources.keys()),
    }
    rows = []
    for number, source in sorted(sources.items()):
        raw = source.read_text()
        assert "(set-info :status sat)" in raw, source
        assert re.findall(r"\(declare-fun ([st]) \(\) \(_ BitVec (\d+)\)\)", raw) == [("s", "32"), ("t", "32")], source
        assertions = [line for line in raw.splitlines() if line.startswith("(assert")]
        assert len(assertions) == 1, source
        assertion = parse_expression(assertions[0])
        assert assertion[0] == "assert" and assertion[1][0] == "not" and assertion[1][1][0] == "=", source
        left, right = assertion[1][1][1:]
        path = translations[number]
        code = strip_comments(path.read_text())
        assert not re.search(r"\b(sorry|admit|axiom|native_decide)\b", code), path
        name = f"bv_term_small_rw_{number}"
        original = re.search(r"def " + name + r" \(n : Nat\) \(s t : BitVec n\) : Prop :=\s*(.*?)\n\n", code, re.S)
        assert original, path
        compact = lambda s: re.sub(r"\s+", "", s)
        assert compact(original[1]) == compact(f"{lean_term(left)} ≠ {lean_term(right)}"), f"Source mismatch: {path}"
        condition = re.search(r"def " + name + r"_condition \(n a b : Nat\) : Prop :=\s*(.*?)\n\n", code, re.S)
        assert condition and not re.search(r"BitVec|bv_term|\bbv[a-z]+\b", condition[1]), path
        assert re.search(r"def " + name + r"_solutions .*?SolutionSet n \(" + name + r"_condition n\)", code, re.S), path
        declarations = re.findall(r"^theorem\s+(\w+)", code, re.M)
        assert set(declarations) == {name + suffix for suffix in ("_iff", "_solutions_iff", "_sat32")}, path
        witness = re.search(r"theorem " + name + r"_sat32\s*:\s*" + name + r" 32 \(literal 32 (\d+)\) \(literal 32 (\d+)\)", code)
        assert witness, path
        a, b = map(int, witness.groups())
        assert 0 <= a < 2**32 and 0 <= b < 2**32, path
        assert evaluate(left, 32, a, b) != evaluate(right, 32, a, b), path
        rows.append({"rule": number, "name": name, "left": left, "right": right,
                     "module": ".".join(path.relative_to(ROOT).with_suffix("").parts),
                     "declarations": ["BV.QF_BV.Sat." + decl for decl in declarations]})
    return rows


def check_axioms(rows: list[dict], output: Path, *,
                 support_module: str = "BV_LEAN.QF_BV.SatSupport",
                 namespace: str = "BV.QF_BV.Sat",
                 report_stem: str = "qfbv-sat") -> tuple[list[str], int]:
    support = strip_comments((ROOT / Path(*support_module.split("."))).with_suffix(".lean").read_text())
    assert not re.search(r"\b(sorry|admit|axiom|native_decide)\b", support)
    declarations = [decl for row in rows for decl in row["declarations"]]
    declarations += [namespace + "." + decl for decl in re.findall(r"^theorem\s+(\w+)", support, re.M)]
    assert len(declarations) == len(set(declarations))
    source = output / (report_stem + "-axioms.lean")
    source.write_text("\n".join(["import " + row["module"] for row in rows] + [""] +
                                ["#print axioms " + decl for decl in declarations]) + "\n")
    result = subprocess.run(["lake", "env", "lean", "--json", str(source)], cwd=ROOT, text=True, capture_output=True)
    (output / (report_stem + "-axioms.jsonl")).write_text(result.stdout)
    if result.returncode:
        raise RuntimeError(result.stdout + result.stderr)
    messages = [json.loads(line) for line in result.stdout.splitlines() if line.strip()]
    assert len(messages) == len(declarations), "Missing axiom reports"
    seen, axioms = set(), set()
    for message in messages:
        assert message["severity"] == "information", message
        text = message["data"]
        match = re.match(r"'([^']+)' (?:depends on axioms|does not depend on any axioms)", text)
        assert match and match[1] not in seen, text
        seen.add(match[1])
        if "depends on axioms" in text:
            names = re.search(r"\[([^]]*)\]", text)
            assert names, text
            axioms.update(name.strip() for name in names[1].split(",") if name.strip())
    assert seen == set(declarations)
    assert axioms <= ALLOWED_AXIOMS, f"Unexpected axioms: {axioms - ALLOWED_AXIOMS}"
    return sorted(axioms), len(declarations)


def verify_small(rows: list[dict], max_width: int, output: Path) -> int:
    source = output / "qfbv-sat-small.lean"
    header = """
open BV.QF_BV.Sat
set_option maxRecDepth 10000
def solutionBits (n : Nat) (C : Nat → Nat → Prop) [∀ a b, Decidable (C a b)] : String :=
  String.ofList ((List.range (2 ^ n)).flatMap fun a =>
    (List.range (2 ^ n)).map fun b => if C a b then '1' else '0')
"""
    commands = [f'#eval IO.println ("{row["rule"]} {n} " ++ solutionBits {n} ({row["name"]}_condition {n}))'
                for row in rows for n in range(max_width + 1)]
    source.write_text("\n".join(["import " + row["module"] for row in rows]) + header + "\n".join(commands) + "\n")
    result = subprocess.run(["lake", "env", "lean", str(source)], cwd=ROOT, text=True, capture_output=True)
    (output / "qfbv-sat-small.txt").write_text(result.stdout)
    if result.returncode:
        raise RuntimeError(result.stdout + result.stderr)
    lines = result.stdout.splitlines()
    assert len(lines) == len(commands), "Missing or additional small-width results"
    by_rule = {row["rule"]: row for row in rows}
    checked, seen = 0, set()
    for line in lines:
        number, width, bits = line.split()
        number, n = int(number), int(width)
        assert (number, n) not in seen and 0 <= n <= max_width
        seen.add((number, n))
        row = by_rule[number]
        p = 1 << n
        assert len(bits) == p * p
        for a in range(p):
            for b in range(p):
                expected = evaluate(row["left"], n, a, b) != evaluate(row["right"], n, a, b)
                assert bits[a * p + b] == ("1" if expected else "0"), (number, n, a, b)
                checked += 1
    return checked


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--verify-small", type=int, metavar="MAX_WIDTH", help="Exhaustively compare widths 0..MAX_WIDTH (0..8)")
    args = parser.parse_args()
    if args.verify_small is not None and not 0 <= args.verify_small <= 8:
        parser.error("--verify-small must be between 0 and 8")
    rows = collect()
    output = ROOT / ".lake"
    output.mkdir(exist_ok=True)
    axioms, declaration_count = check_axioms(rows, output)
    checked = verify_small(rows, args.verify_small, output) if args.verify_small is not None else None
    report = {
        "status": "passed", "source_correspondences": len(rows),
        "input_iff_proofs": len(rows), "complete_solution_set_iff_proofs": len(rows),
        "kernel_checked_sat32_witnesses": len(rows), "checked_declarations": declaration_count,
        "axioms": axioms, "sorryAx": False,
        "small_width_max": args.verify_small, "exhaustive_assignment_checks": checked,
    }
    (output / "qfbv-sat-audit.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
