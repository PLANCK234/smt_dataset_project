module
prelude

public import Init.Data.BitVec.Bootstrap
public import Init.Data.BitVec.Bitblast

public import SMT.BitVec.Model
public import SMT.BitVec.Division
public import SMT.BitVec.Comparison
public import Init.Data.BitVec.Lemmas

/-! Division semantic contracts, split from SMT.BitVec.Semantics.
Public theorem names and statements are preserved. -/
@[expose] public section

namespace SMT.BitVec

private theorem allOnes_literal (n : Nat) :
    _root_.BitVec.allOnes n = literal n (unsignedMax n) := by
  apply _root_.BitVec.eq_of_toNat_eq
  simp only [_root_.BitVec.toNat_allOnes, literal, unsignedMax, _root_.BitVec.toNat_ofNat]
  exact (Nat.mod_eq_of_lt (Nat.sub_lt (Nat.two_pow_pos n) (by decide))).symm

theorem bvudiv_zero (x : _root_.BitVec n) :
    bvudiv x (literal n 0) = literal n (unsignedMax n) := by
  exact _root_.BitVec.smtUDiv_zero.trans (allOnes_literal n)
theorem bvurem_zero (x : _root_.BitVec n) : bvurem x (literal n 0) = x := by simp
theorem bvsdiv_zero (x : _root_.BitVec n) :
    bvsdiv x (literal n 0) =
      if bvslt x (literal n 0) then literal n 1 else literal n (unsignedMax n) := by
  simpa only [allOnes_literal] using (_root_.BitVec.smtSDiv_zero (x := x))
theorem bvsrem_zero (x : _root_.BitVec n) : bvsrem x (literal n 0) = x :=
  _root_.BitVec.srem_zero
theorem bvsmod_zero (x : _root_.BitVec n) : bvsmod x (literal n 0) = x :=
  _root_.BitVec.smod_zero
theorem bvurem_semantics (x y : _root_.BitVec n) :
    toUnsigned (bvurem x y) = toUnsigned x % toUnsigned y := rfl
theorem bvudiv_semantics (x y : _root_.BitVec n) :
    toUnsigned (bvudiv x y) =
      if y = literal n 0 then unsignedMax n else toUnsigned x / toUnsigned y := by
  simp only [bvudiv, _root_.BitVec.smtUDiv, toUnsigned]
  split <;> simp_all [literal, unsignedMax]

private theorem bvsdiv_nonzero (x y : _root_.BitVec n) (hy : y ≠ literal n 0) :
    bvsdiv x y = x.sdiv y := by
  cases hx : x.msb <;> cases hy' : y.msb <;>
    simp [bvsdiv, _root_.BitVec.smtSDiv, _root_.BitVec.sdiv, hx, hy',
      _root_.BitVec.smtUDiv, hy]

/-- The quotient is truncating, with modular construction covering signed-min / -1. -/
theorem bvsdiv_semantics (x y : _root_.BitVec n) (hy : y ≠ literal n 0) :
    bvsdiv x y = fromInt n ((toSigned x).tdiv (toSigned y)) := by
  rw [bvsdiv_nonzero x y hy]
  apply _root_.BitVec.eq_of_toInt_eq
  simpa only [fromInt, toSigned, _root_.BitVec.toInt_ofInt] using
    (_root_.BitVec.toInt_sdiv x y)
theorem bvsrem_semantics (x y : _root_.BitVec n) :
    toSigned (bvsrem x y) = (toSigned x).tmod (toSigned y) :=
  _root_.BitVec.toInt_srem x y
theorem bvsmod_semantics (x y : _root_.BitVec n) :
    toSigned (bvsmod x y) = (toSigned x).fmod (toSigned y) :=
  _root_.BitVec.toInt_smod

end SMT.BitVec
