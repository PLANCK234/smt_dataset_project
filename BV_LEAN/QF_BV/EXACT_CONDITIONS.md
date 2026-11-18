# Exact conditions for the 19 width-dependent rules

These 19 rules hold at width 32 but fail at some other widths. Each file in `unsat/` keeps the
original statement and a checked counterexample, and proves two equivalences:

- `bv_term_small_rw_ID_iff`: for given `n, s, t`, the equality holds **iff** an input condition holds.
- `bv_term_small_rw_ID_width_iff`: for given `n`, the equality holds **for all** `s, t` **iff** a width condition holds.

The two differ. For 1246, the width condition is `n ≠ 1`, yet the input `n = 1, s = 0` still satisfies
the equality.

## Notation

`P = 2^n`, `a = s.toNat`, `d = t.toNat`, so `0 ≤ a, d < P`. Bits are indexed from 0 (least significant).
`&` is bitwise AND on naturals. The Lean names of the predicates are given in parentheses and are
defined in [ExactConditions.lean](ExactConditions.lean).

1. **Balanced shift** (`ShiftBalanced n a q`): `E_n(a,q) :⇔ 2^(n+q) ∣ (2^(2q)−1)·a + (a mod 2^q)`.
   This is exactly `a << q = a >> q`. It includes `q = 0`, `q ≥ n`, and balanced bit patterns for
   `0 < q < n`.
2. **Complement admissible** (`ComplementAdmissible n v`): `H_n(v) :⇔ v·2^(P−1−v) mod P ≠ 2^(n−1)`.
   The inner shift is not just the top bit. For `n = 0`, `H` is true.
3. **Self-shift admissible** (`SelfShiftAdmissible n v`): `D_n(v) :⇔ v = 0 ∨ n ≤ v ∨ P ∤ v·2^v`.
4. **Cross admissible** (`CrossAdmissible n x y`): with `b = x·2^y mod P`,
   `K_n(x,y) :⇔ b = 0 ∨ (y & ⌊x/2^b⌋) = 0`. No set bit `j` of `y` meets a set bit `b+j` of `x`.
   Partial truncation is allowed.

## Input-level conditions (`_iff`)

| Rule | Equality holds iff | Note on the original side condition |
| --- | --- | --- |
| [223](unsat/bv_term_small_rw_223.lean) | `(n≠1 ∨ a≠1) ∧ (n≠2 ∨ a≠2)` | Exact only over all inputs |
| [238](unsat/bv_term_small_rw_238.lean) | `n≠2 ∨ a≠1` | Only `a = 1` fails at `n = 2` |
| [270](unsat/bv_term_small_rw_270.lean) | `n≠2 ∨ d≠1 ∨ a<2` | |
| [271](unsat/bv_term_small_rw_271.lean) | `n≠2 ∨ d≠1 ∨ a mod 2 = 0` | |
| [296](unsat/bv_term_small_rw_296.lean), [298](unsat/bv_term_small_rw_298.lean) | `H_n(a)` | Exact |
| [301](unsat/bv_term_small_rw_301.lean) | `E_n(a, ⌊a/2^r⌋)`, `r = a² mod P` | "`q = 0` or `q ≥ n`" is only sufficient |
| [379](unsat/bv_term_small_rw_379.lean), [380](unsat/bv_term_small_rw_380.lean) | `a = 0 ∨ H_n(d)` | Missed `s = 0` |
| [458](unsat/bv_term_small_rw_458.lean), [1101](unsat/bv_term_small_rw_1101.lean) | `K_n(a,d)` | "All or no truncation" is only sufficient |
| [473](unsat/bv_term_small_rw_473.lean), [1343](unsat/bv_term_small_rw_1343.lean) | `K_n(d,a)` | Same, inputs swapped |
| [477](unsat/bv_term_small_rw_477.lean) | `E_n(a, ⌊d/2^r⌋)`, `r = d² mod P` | Exact only over all `s` |
| [522](unsat/bv_term_small_rw_522.lean) | `P ∤ d·2^d ∨ E_n(a,d)` | Exact only over all `s` |
| [669](unsat/bv_term_small_rw_669.lean), [670](unsat/bv_term_small_rw_670.lean) | `D_n(a)` | Exact |
| [719](unsat/bv_term_small_rw_719.lean) | `a = 0 ∨ P ∤ a·2^a ∨ P ∣ d·2^a` | Missed `t << s = 0` |
| [1246](unsat/bv_term_small_rw_1246.lean) | `n≠1 ∨ a = 0` | Only `n = 1, a = 1` fails |

Inputs showing that the original side conditions are not necessary:
301 at `n=6, a=34` (q = 2, both sides 8); 379/380 at `n=1, a=0, d=1`; 458 at `n=3, a=6, d=1`
(partial truncation to 4); 719 at `n=3, a=2, d=0`.

## Width-level conditions (`_width_iff`)

Let `ν₂(v)` be the 2-adic valuation and `R(n,r) = {v < P | v² ≡ r (mod P)}`.

- **T(n)**: no `1 ≤ e ≤ n` with `e + ν₂(e) = n`.
- **S(n)**: no `1 ≤ v < n` with `v + ν₂(v) ≥ n`; equivalently, no `1 ≤ j < n` with `n ≡ j (mod 2^j)`.
- **C(n)**: for every `d ≥ 1` with `2^d < n` and `r = n mod 2^d`, no set bit `j` of `d` satisfies `j < r ≤ d + j`.
- **Q₃₀₁(n)**: for every `r < n` and `v ∈ R(n,r)`, `E_n(v, ⌊v/2^r⌋)`.
- **Q₄₇₇(n)**: for every `r < n`, `R(n,r)` avoids `[2^r, n·2^r)`.

| Rules | Hold for all inputs iff | Lean predicate |
| --- | --- | --- |
| 223 | `n = 0 ∨ n ≥ 3` | same |
| 238, 270, 271 | `n ≠ 2` | same |
| 1246 | `n ≠ 1` | same |
| 296, 298, 379, 380 | T(n) | `ComplementWidth` |
| 522, 669, 670, 719 | S(n) | `SelfShiftWidth` |
| 458, 473, 1101, 1343 | C(n) | `CrossWidth` |
| 301 | Q₃₀₁(n) | `SquareWidth301` |
| 477 | Q₄₇₇(n) | `SquareWidth477` |

None of these reduces to "n is a power of two" or a lower bound: T(12), T(24), S(12), and S(24) are
true; C(12) is false (`d=3, r=4, j=1`) and C(24) is true. Both square rules fail at width 8 and 64 and
hold at width 32.

**Formalization boundary.** Lean proves each `_width_iff` against the predicate in the right column.
`ComplementWidth`, `SelfShiftWidth`, and `CrossWidth` are stated as "every admissible input satisfies
H / D / K". Their reduction to the ν₂ forms T, S, and the residue form C is argued below but not
formalized. Q₃₀₁ and Q₄₇₇ appear directly in Lean.

## Reductions to T, S, C (paper proofs)

**T.** Let `A = x << ~x`, `B = x << −x`. Each is 0 or at least n, and `B = 2A mod P`, so they disagree
on zeroness only when `A = P/2`. For `x ≠ 0` put `e = P − x > 0`; then `A ≡ −e·2^(e−1) (mod P)`.
This equals `P/2` iff `ν₂(e) + e − 1 = n − 1`. If such an `e` exists, `x = P − e` is a counterexample
(`s = x` for 296/298; `t = x, s = 1` for 379/380).

**S.** For `0 < v < n`, the self-shift `v << v` is zero iff `v + ν₂(v) ≥ n`. With `j = n − v` this is
`n ≡ j (mod 2^j)`. A bad `v` gives counterexamples: `s = v` (669/670), `t = v, s = 1` (522), and
`s = v, t = 1` (719, where `s << s = 0` but `(s|1) << s = 2^v`).

**C.** Only `0 < b < n` can fail, and `b` is a positive multiple of `2^d` with `d ≥ 1`. With
`u = x mod 2^(n−d)`, `b = u·2^d` and `u < 2^b`, so low bits of `x` cannot collide. A collision needs a
set bit `j` of `d` with `n − d ≤ b + j < n`. Since `j < d ≤ 2^(d−1)`, this forces `b = n − r` with
`r = n mod 2^d > 0`, giving `j < r ≤ d + j`. Conversely, for such `d, j`, the input
`x = (n−r)/2^d + 2^(n−r+j)`, `y = d` violates K.

**Square rules.** If `r = v² mod P ≥ n` then `⌊v/2^r⌋ = 0`, so only `r < n` matters. For 301 the same
`v` is inner and outer, so every root must satisfy `E` (Q₃₀₁). For 477 the outer value is free.
Taking `s = 1` shows that `0 < q < n` fails, so the forbidden roots are exactly those in `[2^r, n·2^r)` (Q₄₇₇).
The divisibility form of E is `Learned.BitVec.bvshl_eq_bvlshr_iff_dvd`.

## Executable check

[classify_refuted_widths.py](../../scripts/classify_refuted_widths.py) decides T, S, C, and the square
conditions and builds a concrete counterexample for each bad width:

```sh
python3 scripts/classify_refuted_widths.py --widths 8 12 16 24 32 64
python3 scripts/classify_refuted_widths.py --max-width 128 --verify-small 7
```

`--verify-small 7` checks all 21,845 input pairs at widths 0–7 against the 19 input predicates. It
checks the implementation; it is not a proof for all widths.
