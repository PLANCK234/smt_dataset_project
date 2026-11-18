# Semantics and provenance

`SMT/` is the base library: semantics for the 51 BV/PBV operations, `toNat` bridges, base rewrites,
and Nat bit lemmas extracted from upstream. `LEMMAS_learned/` contains local derivations; `SMT/` never
imports it. Mathlib and Batteries are neither installed nor imported. Selected Mathlib proofs are
copied and adapted locally, and everything else comes from the pinned toolchain's `Init`.

## Semantic conventions

- Unsigned operations are modulo `2^n`. BV subtraction is not truncated Nat subtraction.
- Signed comparison, division, remainder, and overflow use `signedValue : Int`.
- `bvudiv`/`bvsdiv` keep SMT-LIB division-by-zero behavior. `bvsrem` uses `Int.tmod`, and `bvsmod` uses `Int.fmod`.
- Shift amounts use the full unsigned value; rotation amounts are reduced modulo the width.
- `BitVec 0` is allowed. A theorem requires positive width or valid indices only when stated.
- PBV operations keep the SMT-LIB argument order: `int_to_pbv n z`, `pextract hi lo x`,
  `pzero_extend extra x`, `psign_extend extra x`. They are well-formed only when `n > 0`,
  `extra ≥ 0`, and `lo ≤ hi < n`. Integer width constraints must be proved before casting to Nat.
- Commutativity and bridge lemmas are not global `[simp]`; choose a direction with `rw` or `simp only`.

## Pinned upstream

| Upstream | Version / commit | Used for |
| --- | --- | --- |
| [Lean](https://github.com/leanprover/lean4/tree/5045d0056413266e57c625dcd7c365b10e377c52) | v4.34.1 / `5045d00` | `Init` BitVec API, Nat bitwise proofs |
| [Mathlib](https://github.com/leanprover-community/mathlib4/tree/d13f23b723b8a846827a245b89c10fc7d3f11612) | v4.34.1 / `d13f23b` | BitVec injectivity, Nat bitwise lemmas |

File headers say whether a file is adapted from upstream or derived locally.
[upstream.json](upstream.json) records revisions, source SHA-256 hashes, and declaration locations.
An `upstream` entry names the identifiable basis of a declaration; it does not mean the proof was copied
verbatim. Copyright notices are in [THIRD_PARTY_NOTICES.md](THIRD_PARTY_NOTICES.md).

To refresh `upstream.json`, `THIRD_PARTY_NOTICES.md`, and the [operation index](SMT/BitVec/INDEX.md)
after moving declarations, use a Mathlib checkout at the pinned revision:

```sh
python3 scripts/update_upstream.py --mathlib-source /path/to/pinned-mathlib
```
