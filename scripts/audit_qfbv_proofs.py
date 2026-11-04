#!/usr/bin/env python3
"""Check compiled axioms of QF_BV proofs, refutations, and conditional repairs.

Run `lake build` first. Discover declarations from the canonical Lean sources.
Open declarations are reported, never counted as completed proofs.
"""
from __future__ import annotations

import json
from pathlib import Path
import re
import subprocess


ROOT = Path(__file__).resolve().parents[1]
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def main() -> None:
    from qfbv_proof_status import collect
    rows = collect()
    assert not any(r['status'] == 'open' for r in rows), 'Unfinished proofs remain'
    declarations = [name for row in rows for name in row['declarations']]
    imports = ['import ' + '.'.join(Path(row['lean']).with_suffix('').parts) for row in rows]
    repairs = []
    for row in rows:
        for name in row['declarations']:
            short = name.split('.')[-1]
            if short.endswith('_width_iff'):
                kind = 'exact_width'
            elif short.endswith('_iff'):
                kind = 'exact_input'
            elif short.endswith('_restricted'):
                kind = 'conditional'
            elif '_counterexample_' in short:
                kind = 'additional_counterexample'
            else:
                continue
            repairs.append({'rule': row['rule'], 'kind': kind})
    assert len(declarations) == len(set(declarations)), "Duplicate proof declarations"
    imports = list(dict.fromkeys(imports))
    output_dir = ROOT / ".lake"
    output_dir.mkdir(exist_ok=True)
    check = output_dir / "qfbv-proof-audit.lean"
    check.write_text("\n".join(imports + [""] + [
        f"#print axioms {name}" for name in declarations
    ]) + "\n")
    result = subprocess.run(
        ["lake", "env", "lean", "--json", str(check)],
        cwd=ROOT, text=True, capture_output=True, check=False,
    )
    (output_dir / "qfbv-proof-axioms.jsonl").write_text(result.stdout)
    if result.returncode:
        raise SystemExit(result.stdout + result.stderr)
    messages = [json.loads(line) for line in result.stdout.splitlines() if line.strip()]
    assert all(m["severity"] == "information" for m in messages), messages
    assert len(messages) == len(declarations), "Missing axiom reports"
    seen = set()
    axioms = set()
    for message in messages:
        text = message["data"]
        match = re.match(r"'([^']+)' (?:depends on axioms|does not depend on any axioms)", text)
        assert match, text
        assert match[1] not in seen, text
        seen.add(match[1])
        if "depends on axioms" in text:
            names = re.search(r"\[([^]]*)\]", text)
            assert names, text
            axioms.update(name.strip() for name in names[1].split(",") if name.strip())
    assert seen == set(declarations), "Unexpected declaration set"
    assert axioms <= ALLOWED_AXIOMS, f"Unapproved axioms: {axioms - ALLOWED_AXIOMS}"
    report = {
        "status": "passed",
        "proved": sum(r["status"] == "proved" for r in rows),
        "refuted": sum(r["status"] == "refuted" for r in rows),
        "open": sum(r["status"] == "open" for r in rows),
        "conditional_proofs": sum(r["kind"] == "conditional" for r in repairs),
        "conditionally_repaired_rules": len({r["rule"] for r in repairs if r["kind"] == "conditional"}),
        "additional_counterexamples": sum(r["kind"] == "additional_counterexample" for r in repairs),
        "exact_input_iff_proofs": sum(r["kind"] == "exact_input" for r in repairs),
        "exact_width_iff_proofs": sum(r["kind"] == "exact_width" for r in repairs),
        "checked_declarations": len(declarations),
        "axioms": sorted(axioms),
        "sorryAx": False,
    }
    (output_dir / "qfbv-proof-audit.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
