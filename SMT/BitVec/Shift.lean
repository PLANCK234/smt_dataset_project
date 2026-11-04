module
prelude

public import Init.Data.Nat.Lemmas
public import Init.ByCases
public import Init.Omega

public import SMT.BitVec.Basic
public import Init.Data.BitVec.Lemmas

@[expose] public section

namespace SMT.BitVec

/-- SMT `bvshl`: N_n(U(x)*2^U(y)); x and y have the same width.
The count is unsigned and is not reduced modulo n; counts at least n yield zero.
The evaluation guard prevents allocating an intermediate integer with U(y) bits.
`bvshl_normalize` exposes a bounded-count primitive to `bv_decide`. -/
def bvshl {n : Nat} (x y : _root_.BitVec n) : _root_.BitVec n :=
  if n ≤ y.toNat then 0 else x <<< y

theorem bvshl_eq_shiftLeft (x y : _root_.BitVec n) :
    bvshl x y = x <<< y := by
  unfold bvshl
  split
  next h => exact (_root_.BitVec.shiftLeft_eq_zero h).symm
  next => rfl

/-- Clamp only counts at least the width to the width (not modulo the width).
This avoids huge intermediate naturals even during tactic ground reduction. -/
theorem bvshl_normalize (x y : _root_.BitVec n) :
    bvshl x y = x <<<
      (bif (_root_.BitVec.ofNat n n).ule y then _root_.BitVec.ofNat n n else y) := by
  have hc : (_root_.BitVec.ofNat n n).toNat = n := by
    exact Nat.mod_eq_of_lt Nat.lt_two_pow_self
  by_cases h : n ≤ y.toNat
  · simp only [bvshl, h, ↓reduceIte, _root_.BitVec.ule, hc, decide_true, Bool.cond_true]
    exact (_root_.BitVec.shiftLeft_eq_zero (by simpa only [hc] using Nat.le_refl n)).symm
  · simp [bvshl, h, _root_.BitVec.ule, hc]
/-- SMT `bvlshr`: floor(U(x)/2^U(y)); x and y have the same width.
Counts at least n yield zero, without reducing the count modulo n. -/
abbrev bvlshr {n : Nat} (x y : _root_.BitVec n) : _root_.BitVec n := x >>> y
/-- SMT `bvashr`: N_n(floor(S(x)/2^U(y))); count width equals value width.
Counts at least n fill every result bit with the input sign bit. -/
abbrev bvashr {n : Nat} (x y : _root_.BitVec n) : _root_.BitVec n := x.sshiftRight' y

end SMT.BitVec
