#!/usr/bin/env python3
"""Refresh the attribution index from pinned Lean and a supplied Mathlib source tree.
No Mathlib package is installed or imported. Only Python's standard library is used.
"""
from pathlib import Path
import argparse
import hashlib
import json
import re
import subprocess

root = Path(__file__).resolve().parents[1]
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--mathlib-source', type=Path, required=True,
                    help='Source directory containing the three pinned Mathlib/Data files')
args = parser.parse_args()
lean = Path(subprocess.check_output(['lake', 'env', 'lean', '--print-prefix'],
                                   cwd=root, text=True).strip()) / 'src/lean'
mathlib = args.mathlib_source.resolve()
# Prevent a newer checkout from being incorrectly attributed to the pinned revision.
previous = json.loads((root / 'upstream.json').read_text())
for source in previous['sources']:
    base = lean if source['id'].startswith('lean:') else mathlib
    path = base / source['path']
    if hashlib.sha256(path.read_bytes()).hexdigest() != source['sha256']:
        raise SystemExit(f'Pinned source hash mismatch: {path}')

revs={'lean':'5045d0056413266e57c625dcd7c365b10e377c52','mathlib':'d13f23b723b8a846827a245b89c10fc7d3f11612'}
urls={'lean':'https://github.com/leanprover/lean4','mathlib':'https://github.com/leanprover-community/mathlib4'}
pat=re.compile(r'(?m)^(?:@\[[^\n]*\]\s*)?(?:(?:private|protected|noncomputable)\s+)*(theorem|lemma|def|abbrev)\s+([\w.\'«»]+)')
sources=[];native={};math={}
files=[('lean',lean,p) for p in sorted((lean/'Init/Data/BitVec').glob('*.lean'))]
files += [('lean',lean,lean/p) for p in ['Init/Prelude.lean','Init/Data/Nat/Bitwise/Lemmas.lean','Init/Data/Nat/Mod.lean','Init/Data/Nat/Div/Lemmas.lean']]
files += [('mathlib', mathlib, mathlib / path) for path in ['Mathlib/Data/BitVec.lean', 'Mathlib/Data/Nat/Bits.lean', 'Mathlib/Data/Nat/Bitwise.lean']]
for kind,base,p in files:
    text=p.read_text();rel=p.relative_to(base).as_posix();id=kind+':'+rel
    item={'id':id,'repository':urls[kind],'revision':revs[kind],'path':rel,'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'license':'Apache-2.0','url':f'{urls[kind]}/blob/{revs[kind]}/'+('src/lean/' if kind=='lean' else '')+rel}
    sources.append(item)
    namespace='Nat' if '/Nat/' in rel else 'BitVec'
    for m in pat.finditer(text):
        row={'source':id,'name':namespace+'.'+m[2].strip('«»'),'line':text.count('\n',0,m.start(1))+1}
        (native if kind=='lean' else math).setdefault(row['name'],row)
bridges={
'Basic':{'literal':'toNat_literal'},
'Arithmetic':{op:'toNat_'+op for op in ['bvneg','bvadd','bvsub','bvmul']},
'Bitwise':{op:'toNat_'+op for op in ['bvnot','bvand','bvor','bvxor','bvnand','bvnor','bvxnor','bvcomp']},
'Division':{op:'toNat_'+op for op in ['bvudiv','bvurem','bvsdiv','bvsrem','bvsmod']},
'Shift':{op:'toNat_'+op for op in ['bvshl','bvlshr','bvashr']},
'Structure':{op:'toNat_'+op for op in ['concat','extract','zeroExtend','signExtend','repeat','rotateLeft','rotateRight','pextract','pzero_extend','psign_extend']},
'Comparison':{op:op+'_toNat' for op in ['bvult','bvule','bvugt','bvuge','bvslt','bvsle','bvsgt','bvsge']},
'Overflow':{op:op+'_toNat' for op in ['bvnego','bvuaddo','bvsaddo','bvusubo','bvssubo','bvumulo','bvsmulo','bvsdivo']},
'Conversion':{'ubv_to_int':'ubv_to_int_toNat','sbv_to_int':'sbv_to_int_toNat','int_to_bv':'toNat_int_to_bv','int_to_pbv':'toNat_int_to_pbv'}}
operations=[{'operation':op,'category':cat,'definition':f'SMT/BitVec/{cat}.lean','bridge':'SMT.BitVec.'+thm,'bridge_file':f'SMT/BitVec/ToNat/{cat}.lean'} for cat,ops in bridges.items() for op,thm in ops.items()]
mapnames={'toNat_injective':'toNat_injective','toFin_injective':'toFin_injective','eq_iff_toNat_eq':'toNat_eq','toNat_lt':'isLt','toNat_literal':'toNat_ofNat','toNat_literal_of_lt':'toNat_ofNat','toNat_mod':'toNat_mod_cancel','literal_toNat':'ofNat_toNat','signedValue':'toInt_eq_toNat_cond','toInt_toNat':'toInt_eq_toNat_cond','toNat_of_toInt':'ofInt_toInt','toNat_bvcomp':'toNat_ofBool','toNat_bvudiv':'smtUDiv_eq','toNat_bvsdiv':'smtSDiv_zero','toNat_repeat':'replicate_succ'}
replace={'bvneg':'neg','bvadd':'add','bvsub':'sub','bvmul':'mul','bvnot':'not','bvand':'and','bvor':'or','bvxor':'xor','bvshl':'shiftLeft','bvlshr':'ushiftRight','bvashr':"sshiftRight'",'concat':'append','extract':'extractLsb','zeroExtend':'setWidth','int_to_bv':'ofInt','int_to_pbv':'ofInt','bvurem':'umod','bvsrem':'srem','bvsmod':'smod'}
records=[]
for p in sorted([*(root/'SMT').rglob('*.lean'), *(root/'LEMMAS_learned').rglob('*.lean')]):
    if 'LEMMAS_learned' not in p.parts and not any(part in p.parts for part in ['ToNat','Rewrite','Semantics','Nat']):continue
    text=p.read_text();ms=list(pat.finditer(text))
    namespace=('Learned' if 'LEMMAS_learned' in p.parts else 'SMT') + ('.Nat' if 'Nat' in p.parts else '.BitVec')
    for i,m in enumerate(ms):
        name=m[2].strip('«»');block=text[m.start():ms[i+1].start() if i+1<len(ms) else len(text)]
        row={'name':namespace+'.'+name,'kind':m[1],'file':p.relative_to(root).as_posix(),'line':text.count('\n',0,m.start(1))+1,'upstream':[]}
        row['visibility'] = 'private' if re.search(r'\bprivate\b', m[0]) else 'public'
        if namespace.endswith('.Nat'):
            orig=math.get('Nat.'+name) if p.stem=='Mathlib' else native.get('Nat.'+name)
            if orig:row['upstream'].append(orig)
            row['adaptation']='proof extracted and adapted to local namespace' if orig else 'local modular helper'
        else:
            target=mapnames.get(name,name)
            for a,b in sorted(replace.items(),key=lambda kv:-len(kv[0])):target=target.replace(a,b)
            orig=(math.get('BitVec.'+target) if name in ['toNat_injective','toFin_injective'] else native.get('BitVec.'+target))
            if orig:row['upstream'].append(orig)
            for ref in re.findall(r'_root_\.BitVec\.([\w\']+)',block):
                orig=native.get('BitVec.'+ref)
                if orig and orig not in row['upstream']:row['upstream'].append(orig)
            row['adaptation']='SMT API specialization or local derived theorem; uses Lean Init proofs' if row['upstream'] else 'local derived contract/rewrite'
        if namespace.startswith('Learned.'):
            row['adaptation'] = 'local derived theorem; separated from the original SMT library'
            row['local_dependencies'] = sorted(set(re.findall(r'(?<![\w.])(?:SMT|Learned)\.(?:Nat|BitVec)\.[\w]+', block)))
        records.append(row)
(root/'upstream.json').write_text(json.dumps({'schema_version':1,'lean_version':'4.34.1','mathlib_version':'4.34.1','sources':sources,'operations':operations,'declarations':records},indent=2,ensure_ascii=False)+'\n')
notices=['# Third-party notices\n','Extracted or adapted source is licensed under Apache-2.0. The full license is in `THIRD_PARTY_LICENSES/Apache-2.0.txt`. Source revisions, hashes, and declaration locations are in `upstream.json`.\n']
for kind,base,p in files:
    text=p.read_text();notice=re.match(r'/-(.*?)\-/',text,re.S)
    if notice:
        notices += ['## '+kind+': '+p.relative_to(base).as_posix()+'\n','```text\n'+notice[1].strip()+'\n```\n']
(root/'THIRD_PARTY_NOTICES.md').write_text('\n'.join(notices))
index = [
    '# BV / PBV 运算索引\n',
    '全部 51 个当前公开运算及其数学桥接。命名空间均为 `SMT.BitVec`。',
    '符号宽度使用、依赖和来源规范见 [UPSTREAM.md](../../UPSTREAM.md)。\n',
    'Bool 结果的桥接名通常为 `*_toNat`；BV 结果为 `toNat_*`。',
    '有符号运算通过 `signedValue` 使用 Int，不会丢弃符号。\n',
]
for category in bridges:
    index += [f'## {category}\n',
              f'按需导入 `SMT.BitVec.ToNat.{category}`。\n',
              '| 运算 | 桥接定理 |', '| --- | --- |']
    for operation, theorem in bridges[category].items():
        index.append(f'| [`{operation}`]({category}.lean) | [`{theorem}`](ToNat/{category}.lean) |')
    index.append('')
index += ['## 重写规则\n', '按需 import 以下模块，使用 `rw` 或 `simp only`。\n']
for path in sorted((root/'SMT/BitVec/Rewrite').glob('*.lean')):
    names = [r['name'].split('.')[-1] for r in records if r['file'] == path.relative_to(root).as_posix()]
    index += [f'### [Rewrite.{path.stem}](Rewrite/{path.name})\n',
              ', '.join(f'`{name}`' for name in names) + '\n']
index += ['## Nat 辅助库\n',
          'Nat 位测试、位运算、掩码和数值辅助定理见 [SMT.Nat 索引](../Nat/INDEX.md)。\n']
(root/'SMT/BitVec/INDEX.md').write_text('\n'.join(index))
nat_index = ['# SMT.Nat 声明索引\n',
             '所有声明都在 `SMT.Nat` 命名空间。每个文件可单独 import；',
             '模块依赖和来源说明见 [UPSTREAM.md](../../UPSTREAM.md)。\n']
for path in sorted((root/'SMT/Nat').glob('*.lean')):
    nat_index += [f'## [{path.stem}]({path.name})\n',
                  f'`import SMT.Nat.{path.stem}`\n',
                  '| 声明 | 种类 |', '| --- | --- |']
    for row in records:
        if row['file'] == path.relative_to(root).as_posix():
            nat_index.append(f"| `{row['name'].split('.')[-1]}` | {row['kind']} |")
    nat_index.append('')
(root/'SMT/Nat/INDEX.md').write_text('\n'.join(nat_index))
print(len(operations),'operator bridges;',len(records),'local declaration records;',len(sources),'pinned source files')
