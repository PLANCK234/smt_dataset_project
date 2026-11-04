#!/usr/bin/env python3
"""Inspect the canonical QF_BV translations without generating progress tables."""
from __future__ import annotations
import argparse
from collections import Counter
import json
from pathlib import Path
import re
from audit_library import strip_comments

ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / 'BV/QF_BV/unsat'
LEAN = ROOT / 'BV_LEAN/QF_BV/unsat'


def collect() -> list[dict]:
    sources = {p.stem.rsplit('_', 1)[1]: p for p in SOURCE.glob('bv-term-small-rw_*.smt2')}
    translations = {p.stem.rsplit('_', 1)[1]: p for p in LEAN.glob('bv_term_small_rw_*.lean')}
    assert sources.keys() == translations.keys(), {
        'missing': sorted(sources.keys() - translations.keys()),
        'extra': sorted(translations.keys() - sources.keys()),
    }
    rows = []
    for number in sorted(sources, key=int):
        path = translations[number]
        code = strip_comments(path.read_text())
        name = 'bv_term_small_rw_' + number
        declarations = re.findall(r'^theorem\s+(bv_term_small_rw_\w+)', code, re.M)
        assert not re.search(r'\baxiom\b', code), path
        if re.search(r'\b(sorry|admit)\b', code):
            status = 'open'
        elif name + '_counterexample' in declarations:
            assert re.search(r'^def\s+' + name + r'\s*:\s*Prop\s*:=', code, re.M), path
            assert name + '_iff' in declarations and name + '_width_iff' in declarations, path
            status = 'refuted'
        else:
            assert name in declarations, path
            status = 'proved'
        rows.append({'rule': number, 'status': status,
                     'lean': str(path.relative_to(ROOT)),
                     'declarations': ['BV.QF_BV.Unsat.' + n for n in declarations]})
    return rows


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--json', type=Path, help='Optional detailed output, preferably under .lake/')
    args = parser.parse_args()
    rows = collect()
    if args.json:
        args.json.parent.mkdir(parents=True, exist_ok=True)
        args.json.write_text(json.dumps(rows, indent=2) + '\n')
    counts = Counter(r['status'] for r in rows)
    print(f"{len(rows)} rules: {counts['proved']} proved, {counts['refuted']} refuted, {counts['open']} open")
    print('Source inspection only; run audit_qfbv_proofs.py for compiled axiom checks.')


if __name__ == '__main__':
    main()
