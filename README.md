# SMT Dataset Project

[![Lean CI](https://github.com/PLANCK234/smt_dataset_project/actions/workflows/lean.yml/badge.svg)](https://github.com/PLANCK234/smt_dataset_project/actions/workflows/lean.yml)

Lean 4 proofs that the bit-vector rewrite rules of the SMT-LIB family
**20190311-bv-term-small-rw-Noetzli** hold at **every** bit width, including zero, or exact
characterizations of where they fail.

The family's 1,575 benchmarks come from CVC4's syntax-guided rewrite enumeration
(Noetzli et al., SAT 2019). Each benchmark asserts `l ≠ r` for a candidate rule `l = r` over two
32-bit variables, using `bvadd`, `bvmul`, `bvneg`, `bvnot`, `bvand`, `bvor`, `bvshl`, and `bvlshr`.

## Results

| Result | Count |
| --- | ---: |
| UNSAT inputs whose equality is proved for all widths `n` | 1,467 |
| UNSAT inputs that fail at other widths, with exact input-level and width-level `↔` conditions | 19 |
| SAT inputs with an exact BitVec-free solution set and a checked width-32 witness | 89 |
| Unfinished | 0 |

The 1,486 UNSAT inputs include 54 labeled `unknown` in SMT-LIB; all 54 are proved. The source files keep
their original labels. An UNSAT result at width 32 is not by itself a proof for other widths, so each
benchmark is restated over `n : Nat`.

## Significance

**What this adds**

- **Width-independence of solver rewrites.** Solvers apply these rules at whatever width they meet,
  but the rules were only checked at width 32. 1,467 hold for all widths. 19 do not: for example,
  296/298/379/380 fail exactly when some `e ≤ n` has `e + ν₂(e) = n`, and 301/477 hold at 32 but fail
  at 8 and 64. Each failure comes with the exact condition, which is the precise side condition for a
  sound conditional rewrite. See [EXACT_CONDITIONS.md](BV_LEAN/QF_BV/EXACT_CONDITIONS.md).
- **Exact SAT solution sets.** For the 89 rules that are false at width 32, the inputs where `l ≠ r`
  are characterized exactly, not just witnessed.
- **A dependency-free SMT-LIB BV semantics in Lean.** It covers all 51 BV/PBV operations, with SMT-LIB
  division by zero, width 0, and `toNat` bridges. It can serve as a verification back end for other
  BV transformations.

**What it does not do**

- These are equivalence-preserving term rewrites from a 2018 enumeration. Rewrites of this kind are
  well studied, and most proofs here close with `simp` (about 93% are under 30 lines).
- The instances are easy for solvers. Nothing here measures or improves solver search, and there are
  no equisatisfiable transformations (variable elimination, invertibility conditions, width reduction).
  Those would be stated as `(∃ x, φ) ↔ (∃ x', ψ)` with model reconstruction; `SMT/` and the SAT
  solution-set machinery are the natural starting points.

## Layout

| Path | Content |
| --- | --- |
| `SMT/` | Base library: operation semantics, `toNat` bridges, base rewrites ([index](SMT/BitVec/INDEX.md), [conventions](UPSTREAM.md)) |
| `LEMMAS_learned/` | 94 general lemmas extracted from benchmark proofs ([list](LEMMAS_learned/README.md)) |
| `BV_LEAN/QF_BV/unsat/` | 1,486 all-width proofs and refutations |
| `BV_LEAN/QF_BV/sat/` | 89 exact solution sets |
| `BV_LEAN/QF_BV/*.lean` | Shared predicates and helpers for the benchmark proofs |
| `BV/QF_BV/` | Original SMT-LIB inputs |
| `scripts/` | Audits (Python standard library only) |

Dependencies point one way: benchmarks → `LEMMAS_learned` → `SMT` → Lean `Init`. There are no Lake
package dependencies; selected Mathlib proofs are extracted and attributed locally.

## Build

Install [elan](https://github.com/leanprover/elan#installation); it reads `lean-toolchain`
(Lean 4.34.1). Then:

```sh
lake build                     # libraries and all benchmarks
lake build SMT LEMMAS_learned  # libraries only
lake env lean BV_LEAN/QF_BV/unsat/bv_term_small_rw_234.lean
```

Example use of a learned lemma:

```lean
import LEMMAS_learned.BitVec.Shift.Conditions
open SMT.BitVec Learned.BitVec

example (x y : BitVec n) :
    bvshl x y = literal n 0 ↔ 2 ^ n ∣ x.toNat * 2 ^ y.toNat :=
  bvshl_eq_zero_iff_dvd x y
```

## Verification

After `lake build` (Python 3.10+):

```sh
python3 scripts/qfbv_proof_status.py      # every input has a translation
python3 scripts/audit_qfbv_proofs.py      # compiled axioms of all UNSAT theorems
python3 scripts/audit_qfbv_sat.py         # SAT translations match their sources
python3 scripts/audit_qfbv_unknown.py     # the 54 reclassified inputs match their sources
python3 scripts/audit_library.py --output .lake/library-audit.json
python3 scripts/classify_refuted_widths.py --max-width 16 --verify-small 7
```

The axiom audits allow only `propext`, `Classical.choice`, and `Quot.sound`. The last command checks the
19 exact conditions on every input at widths 0–7. CI runs all of these.

## License

Library code: [Apache-2.0](LICENSE). Upstream notices are in
[THIRD_PARTY_NOTICES.md](THIRD_PARTY_NOTICES.md), and pinned sources are in [upstream.json](upstream.json).
The SMT-LIB benchmarks are [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/); each translation
names its source file.
