# SMT Dataset Project

[![Lean CI](https://github.com/PLANCK234/smt_dataset_project/actions/workflows/lean.yml/badge.svg)](https://github.com/PLANCK234/smt_dataset_project/actions/workflows/lean.yml)

A Lean 4 project for formalizing SMT bit-vector operations and proving rewrite rules across arbitrary bit widths, including width zero.

The project contains a local mathematical library, reusable lemmas developed from benchmark proofs, and **1,575 translated QF_BV benchmarks** from the SMT-LIB Benchmark Library family **20190311-bv-term-small-rw-Noetzli**. It uses **Lean 4.34.1** and has no external Lake package dependencies. Selected upstream proofs are extracted and attributed locally; Mathlib is not required to build the project.

## Quick start

Install [elan, the Lean toolchain manager](https://github.com/leanprover/elan#installation), and Git. On Linux, macOS, or WSL:

```sh
curl -sSf https://elan.lean-lang.org/elan-init.sh | sh -s -- -y --default-toolchain none
. "$HOME/.elan/env"
```

Clone the repository and build it from the repository root:

```sh
git clone https://github.com/PLANCK234/smt_dataset_project.git
cd smt_dataset_project
lake build
```

Elan reads `lean-toolchain` and downloads the pinned toolchain when needed. `lake build` checks the libraries and every translated benchmark. A successful build ends with `Build completed successfully`.

For Windows, follow elan's Windows installation instructions, or use the WSL commands above. In VS Code, install the **Lean 4** extension (`leanprover.lean4`) and open the repository root to inspect goals and proofs interactively.

## Build and inspect proofs

Build only the mathematical libraries:

```sh
lake build SMT LEMMAS_learned
```

After building, check an individual benchmark:

```sh
lake env lean BV_LEAN/QF_BV/unsat/bv_term_small_rw_234.lean
```

To use a learned lemma, import its topic module:

```lean
import LEMMAS_learned.BitVec.Shift.Conditions

open SMT.BitVec Learned.BitVec

example (x y : BitVec n) :
    bvshl x y = literal n 0 ↔ 2 ^ n ∣ x.toNat * 2 ^ y.toNat :=
  bvshl_eq_zero_iff_dvd x y
```

Translated formulas use readable names such as `bvadd`, `bvand`, and `bvshl`, with their namespaces opened explicitly.

## Project structure

| Path | Purpose |
| --- | --- |
| `SMT/` | SMT-compatible operations, mathematical semantics, `toNat` bridges, and base rewrite lemmas. All 51 public BV/PBV operations have mathematical bridges. |
| `LEMMAS_learned/` | 94 reusable lemmas, organized by Nat arithmetic, bitwise operations, shifts, bounds, and exact characterizations. |
| `BV_LEAN/QF_BV/unsat/` | 1,486 translations, including 54 formerly unknown inputs now proved UNSAT. |
| `BV_LEAN/QF_BV/sat/` | 89 SAT translations with exact solution conditions and checked width-32 witnesses. |
| `BV_LEAN/QF_BV/ExactConditions.lean` | Shared arithmetic predicates used by the conditional benchmark results. |
| `BV/QF_BV/{sat,unsat}/` | Original SMT-LIB inputs; the 54 reclassified files retain their original unknown status labels. |
| `scripts/` | Proof audits, library audits, width classification, and provenance maintenance. Python standard library only. |
| `upstream.json` | Pinned upstream revisions, source hashes, and declaration-level provenance. |
| `lean-toolchain`, `lakefile.toml`, `lake-manifest.json` | Reproducible Lean and Lake configuration. |

The mathematical dependency direction is:

```text
Benchmark proofs → LEMMAS_learned → SMT mathematical modules → Lean Init
```

The base library does not import learned lemmas, and neither library imports benchmarks. The optional `SMT.QFBV` entry point also exposes the toolchain's bundled bit-vector decision tactic.

## What is proved?

The inputs assert the negation of an equality at **width 32**. The UNSAT translations prove identities for **every `n : Nat`**, including `n = 0`, or characterize counterexamples to that generalization. All 54 originally unknown inputs are now proved UNSAT and stored in `unsat/`. The 89 SAT inputs have exact solution conditions and checked width-32 witnesses.

| Result | Count |
| --- | ---: |
| All-width equalities proved | 1,467 |
| SAT inputs with exact conditions and width-32 witnesses | 89 |
| All-width generalizations refuted by checked counterexamples | 19 |
| Unfinished original claims | 0 |
| Exact input-level `↔` characterizations for the refuted rules | 19 |
| Exact all-input width-level `↔` characterizations for the refuted rules | 19 |

The 19 refuted files preserve the original proposition and its counterexample, then prove corrected conditions. An UNSAT label on a width-32 input is not itself a proof of an arbitrary-width statement.

The exact width theorems are formalized using the arithmetic predicates in `ExactConditions.lean`. Further valuation-based simplifications and quantifier elimination for some width conditions are described mathematically in the [exact-condition notes](BV_LEAN/QF_BV/EXACT_CONDITIONS.md), but are not all separately formalized in Lean. The notes identify that boundary explicitly.

## Verification

Install **Python 3.10 or newer** to run the audit tools. No pip packages are needed. After `lake build`:

```sh
python3 scripts/qfbv_proof_status.py
python3 scripts/audit_qfbv_proofs.py
python3 scripts/audit_qfbv_sat.py
python3 scripts/audit_qfbv_unknown.py
python3 scripts/audit_library.py --output .lake/library-audit.json
python3 scripts/classify_refuted_widths.py --max-width 16 --verify-small 7
```

- The status command checks that every original input has a corresponding translation.
- The benchmark audit checks compiled axiom dependencies of all **1,558 public UNSAT benchmark theorems**, including conditional results and counterexamples. Separate audits check the 89 SAT translations and the 54 reclassified source correspondences.
- The library audit checks **461 indexed declarations**, including two private helpers, operator coverage, source hashes, and import boundaries.
- Both axiom audits permit only `propext`, `Classical.choice`, and `Quot.sound`; they reject `sorryAx` and additional axioms.
- The width classifier independently checks all 21,845 input pairs at widths 0 through 7 against the 19 refuted rules and their exact input conditions. Finite checks complement the Lean proofs.

Generated audit reports and compiled files stay under `.lake/`. GitHub Actions runs the build and these checks on pushes and pull requests.

## Mathematical references and provenance

The following detailed notes are currently in Chinese:

- [Base-library structure, semantics, and provenance](UPSTREAM.md)
- [Bit-vector operation index](SMT/BitVec/INDEX.md)
- [Nat declaration index](SMT/Nat/INDEX.md)
- [Learned lemma categories](LEMMAS_learned/README.md)
- [Exact conditions for the 19 refuted generalizations](BV_LEAN/QF_BV/EXACT_CONDITIONS.md)

Each translated file identifies its source library, benchmark family, original `.smt2` filename, and license. Upstream library code is pinned and attributed through source headers, `upstream.json`, and [third-party notices](THIRD_PARTY_NOTICES.md).

To refresh provenance after editing library declarations, provide a source checkout matching the Mathlib revision recorded in `upstream.json`:

```sh
python3 scripts/update_upstream.py --mathlib-source /path/to/pinned-mathlib
```

That command checks source hashes and updates metadata; it does not install Mathlib or change proofs.

## Contributing and licenses

Keep generally reusable mathematics in the appropriate library module and benchmark-specific proof steps in their benchmark file. Include source attribution for extracted or adapted results, cover width zero where the statement allows it, and run the build and audits before submitting a change.

The mathematical library code is licensed under [Apache-2.0](LICENSE), with upstream notices preserved. The original SMT-LIB benchmark files declare [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/); translations retain their source attribution. Consult file headers and [THIRD_PARTY_NOTICES.md](THIRD_PARTY_NOTICES.md) for provenance.
