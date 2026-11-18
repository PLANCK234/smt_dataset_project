# Learned lemmas

These 94 lemmas were extracted from benchmark proofs because they hold in general. They live in the
`Learned.Nat` and `Learned.BitVec` namespaces, use the operations from `SMT.BitVec`, and depend only
on `SMT` and Lean `Init`.

| Module | Content | Lemmas |
| --- | --- | ---: |
| [BitVec.Arithmetic](BitVec/Arithmetic.lean) | AND/OR decomposition, masked subtraction, lowest set bit | 7 |
| [BitVec.Bitwise](BitVec/Bitwise.lean) | Complement, absorption, carry-free arithmetic on disjoint bits | 12 |
| [BitVec.Shift.Basic](BitVec/Shift/Basic.lean) | Shift distributivity, clearing conditions, low/high splits, round-trip masks | 22 |
| [BitVec.Shift.Bounds](BitVec/Shift/Bounds.lean) | Divisibility, value bounds, composed shifts, non-wrapping addition | 13 |
| [BitVec.Shift.Carry](BitVec/Shift/Carry.lean) | Low bits unaffected by high additions; doubling and carry masks | 9 |
| [BitVec.Shift.Characterization](BitVec/Shift/Characterization.lean) | Exact divisibility criterion for `x << q = x >> q`, mask duality, top-bit obstruction | 3 |
| [BitVec.Shift.Conditions](BitVec/Shift/Conditions.lean) | Divisibility criterion for clearing, unified left/right conditions, conditional masks | 9 |
| [BitVec.Shift.Quotient](BitVec/Shift/Quotient.lean) | Bounds on negated and complemented right-shift quotients | 5 |
| [BitVec.Shift.Self](BitVec/Shift/Self.lean) | Width lower bounds for negated self-shifts | 2 |
| [Nat.Bitwise](Nat/Bitwise.lean) | Carry-free OR equals addition; low masks depend only on residues | 2 |
| [Nat.Div](Nat/Div.lean) | Quotient bounds for powers of two; quotient of exact differences | 3 |
| [Nat.Mod](Nat/Mod.lean) | Residues and divisibility of differences | 1 |
| [Nat.Pow](Nat/Pow.lean) | Linear and quadratic bounds by powers of two | 5 |
| [Nat.Shift](Nat/Shift.lean) | Divisibility bound for nonzero self-shifts | 1 |

Import a module directly (`import LEMMAS_learned.BitVec.Shift.Conditions`) or use the
`LEMMAS_learned.Nat` / `LEMMAS_learned.BitVec` entry points.

A lemma belongs here if it is a self-contained algebraic law, bound, mask property, or exact criterion
that covers width zero. Rewrites that serve a single benchmark stay private to that benchmark.
