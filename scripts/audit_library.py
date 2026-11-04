#!/usr/bin/env python3
"""Audit local operator bridges, provenance, and mathematical import boundaries.
Uses only Python's standard library and the installed pinned Lean sources.
"""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]


def strip_comments(text: str) -> str:
    # Preserve newlines for diagnostics, including nested Lean block comments.
    out = []; depth = 0; i = 0; string = False
    while i < len(text):
        if depth:
            if text.startswith('/-', i): depth += 1; out.extend('  '); i += 2
            elif text.startswith('-/', i): depth -= 1; out.extend('  '); i += 2
            else: out.append('\n' if text[i] == '\n' else ' '); i += 1
        elif string:
            out.append(' ')
            if text[i] == '\\' and i + 1 < len(text): out.append(' '); i += 2
            else:
                if text[i] == '"': string = False
                i += 1
        elif text.startswith('/-', i): depth = 1; out.extend('  '); i += 2
        elif text.startswith('--', i):
            end = text.find('\n', i)
            if end < 0: end = len(text)
            out.append(' ' * (end - i)); i = end
        elif text[i] == '"': string = True; out.append(' '); i += 1
        else: out.append(text[i]); i += 1
    return ''.join(out)


def imports(text: str) -> set[str]:
    clean = strip_comments(text)
    result = set(re.findall(r'^\s*(?:(?:public|meta)\s+)*import\s+(?:all\s+)?([\w.]+)', clean, re.M))
    if not re.search(r'^prelude\s*$', clean, re.M): result.add('Init')
    return result


def run() -> dict:
    manifest = json.loads((ROOT/'lake-manifest.json').read_text())
    assert not manifest['packages'], 'This library must remain free of external packages'
    metadata = json.loads((ROOT/'upstream.json').read_text())
    prefix = Path(subprocess.check_output(['lake','env','lean','--print-prefix'],cwd=ROOT,text=True).strip())
    source_root = prefix/'src/lean'
    revision = subprocess.check_output(['lake', 'env', 'lean', '--githash'], cwd=ROOT, text=True).strip()
    verified_sources = 0
    for source in metadata['sources']:
        if not source['id'].startswith('lean:'):
            continue
        assert source['revision'] == revision, 'Provenance does not match the installed Lean revision'
        path = source_root / source['path']
        assert hashlib.sha256(path.read_bytes()).hexdigest() == source['sha256'], path
        verified_sources += 1
    cache = {}
    def get_source(module):
        if module not in cache:
            path = (ROOT if module.startswith(('SMT', 'LEMMAS_learned')) else source_root)/Path(*module.split('.')).with_suffix('.lean')
            if not path.is_file(): raise AssertionError(f'Cannot inspect import {module}: {path}')
            cache[module] = path.read_text()
        return cache[module]
    def closure(module):
        seen = set(); todo = [module]
        while todo:
            current = todo.pop()
            if current in seen: continue
            seen.add(current)
            todo.extend(imports(get_source(current)) - seen)
        return seen
    # Fail on unproved declarations, even if normal compilation would accept sorry.
    for path in [*(ROOT/'SMT').rglob('*.lean'), *(ROOT/'LEMMAS_learned').rglob('*.lean')]:
        code = strip_comments(path.read_text())
        assert not re.search(r'\b(sorry|admit|axiom)\b',code), path
        assert not any(m.startswith(('Mathlib','Batteries')) for m in imports(code)), path
        assert not any(m.startswith(('waiting', 'BV_LEAN')) for m in imports(code)), path
        if path.is_relative_to(ROOT/'SMT'):
            assert not any(m.startswith('LEMMAS_learned') for m in imports(code)), path
    for row in metadata['declarations']:
        code = strip_comments((ROOT/row['file']).read_text())
        name = row['name'].split('.')[-1]
        assert re.search(r'\b(?:theorem|lemma|def|abbrev)\s+'+re.escape(name)+r'\b',code), row
        assert name in code.splitlines()[row['line'] - 1], ('Stale declaration location', row)
    seen = set()
    for row in metadata['operations']:
        assert row['operation'] not in seen, row
        seen.add(row['operation'])
        code = strip_comments((ROOT/row['bridge_file']).read_text())
        name = row['bridge'].split('.')[-1]
        assert re.search(r'\btheorem\s+'+re.escape(name)+r'\b',code), row
    expected = set()
    for name in ['Basic','Arithmetic','Bitwise','Division','Shift','Structure','Comparison','Overflow','Conversion']:
        code = strip_comments((ROOT/f'SMT/BitVec/{name}.lean').read_text())
        expected.update(n.strip('«»') for n in re.findall(r'\b(?:def|abbrev)\s+([\w«»]+)',code))
    assert seen == expected, {'missing':sorted(expected-seen),'unexpected':sorted(seen-expected)}
    roots = ['SMT.Nat', 'SMT.BitVec.ToNat.Arithmetic', 'SMT.BitVec.ToNat',
             'SMT.BitVec.Rewrite', 'SMT.BitVec.Lemmas', 'SMT.BitVec.Semantics',
             'LEMMAS_learned.Nat', 'LEMMAS_learned.BitVec', 'LEMMAS_learned']
    graphs = {}
    for name in roots:
        deps = closure(name)
        forbidden = sorted(m for m in deps if m.startswith(('Mathlib','Batteries','Std.Tactic.BVDecide','Lean.Meta.Tactic.BVDecide','Lean.Elab.Tactic.BVDecide')))
        assert not forbidden, (name,forbidden)
        graphs[name] = {'transitive_module_count':len(deps),'local_modules':sorted(m for m in deps if m.startswith(('SMT', 'LEMMAS_learned')))}
    # Check compiled proof terms as well as source-level import and placeholder scans.
    output_dir = ROOT/'.lake'
    output_dir.mkdir(exist_ok=True)
    names = [r['name'] for r in metadata['declarations']]
    assert len(names) == len(set(names)), 'Duplicate library declarations'
    modules = sorted({'.'.join(Path(r['file']).with_suffix('').parts) for r in metadata['declarations']})
    check = output_dir/'library-proof-audit.lean'
    private_rows = [r for r in metadata['declarations'] if r.get('visibility') == 'private']
    private_modules = {'.'.join(Path(r['file']).with_suffix('').parts) for r in private_rows}
    check.write_text('\n'.join(['module'] + [
        ('import all ' if m in private_modules else 'import ') + m for m in modules
    ] + ['#print axioms '+n for n in names])+'\n')
    result = subprocess.run(['lake','env','lean','--json',str(check)], cwd=ROOT, text=True, capture_output=True)
    (output_dir/'library-proof-axioms.jsonl').write_text(result.stdout)
    messages = [json.loads(line) for line in result.stdout.splitlines() if line.strip()]
    assert result.returncode == 0, '\n'.join(
        m['data'] for m in messages if m['severity'] != 'information'
    ) + result.stderr
    assert len(messages) == len(names), 'Missing library axiom reports'
    checked = set(); axioms = set()
    for message in messages:
        assert message['severity'] == 'information', message
        data = message['data']
        match = re.match(r"'([^']+)' (?:depends on axioms|does not depend on any axioms)",data)
        assert match, data
        actual = match[1]
        if actual.startswith('_private.'):
            logical = [r['name'] for r in private_rows if re.fullmatch(
                r'_private\.' + re.escape('.'.join(Path(r['file']).with_suffix('').parts)) +
                r'\.\d+\.' + re.escape(r['name']), actual)]
            assert len(logical) == 1, ('Unexpected private declaration', actual)
            actual = logical[0]
        assert actual not in checked, ('Duplicate axiom report', actual)
        checked.add(actual)
        if 'depends on axioms' in data:
            axioms.update(x.strip() for x in re.search(r'\[([^]]*)\]',data)[1].split(',') if x.strip())
    assert checked == set(names), 'Unexpected library axiom reports'
    assert axioms <= {'propext','Classical.choice','Quot.sound'}, axioms
    return {'status':'passed','operator_bridges':len(seen),
            'base_declarations':sum(r['name'].startswith('SMT.') for r in metadata['declarations']),
            'learned_declarations':sum(r['name'].startswith('Learned.') for r in metadata['declarations']),
            'compiled_declarations_checked':len(checked),
            'private_declarations_checked':len(private_rows), 'axioms':sorted(axioms),
            'verified_toolchain_sources':verified_sources,
            'indexed_declarations':len(metadata['declarations']),'imports':graphs,
            'notes':'Counts include implicit Init imports; they are measured closure sizes, not a proof of global minimality.'}

if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path)
    args = parser.parse_args()
    result = run()
    if args.output:
        args.output.parent.mkdir(parents=True,exist_ok=True)
        args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))
