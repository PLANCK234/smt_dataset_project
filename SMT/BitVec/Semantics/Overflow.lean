module
prelude

public import Init.Omega

public import SMT.BitVec.Model
public import SMT.BitVec.Overflow
public import Init.Data.BitVec.Bitblast

/-! Overflow semantic contracts, split from SMT.BitVec.Semantics.
Public theorem names and statements are preserved. -/
@[expose] public section

namespace SMT.BitVec

theorem bvuaddo_semantics (x y : _root_.BitVec n) :
    bvuaddo x y = true ↔ toUnsigned x + toUnsigned y ≥ 2 ^ n := by
  simp [bvuaddo, _root_.BitVec.uaddOverflow]
theorem bvusubo_semantics (x y : _root_.BitVec n) :
    bvusubo x y = true ↔ toUnsigned x < toUnsigned y := by
  simp [bvusubo, _root_.BitVec.usubOverflow]
theorem bvumulo_semantics (x y : _root_.BitVec n) :
    bvumulo x y = true ↔ toUnsigned x * toUnsigned y ≥ 2 ^ n := by
  simp [bvumulo, _root_.BitVec.umulOverflow]
theorem bvnego_semantics (x : _root_.BitVec n) :
    bvnego x = true ↔ toSigned x = signedMin n := by
  simp [bvnego, _root_.BitVec.negOverflow, toSigned, signedMin]
theorem bvsaddo_semantics (x y : _root_.BitVec n) :
    bvsaddo x y = true ↔
      toSigned x + toSigned y < signedMin n ∨ signedMax n < toSigned x + toSigned y := by
  simp only [bvsaddo, _root_.BitVec.saddOverflow, Bool.or_eq_true, decide_eq_true_eq,
    toSigned, signedMin, signedMax]
  omega
theorem bvssubo_semantics (x y : _root_.BitVec n) :
    bvssubo x y = true ↔
      toSigned x - toSigned y < signedMin n ∨ signedMax n < toSigned x - toSigned y := by
  simp only [bvssubo, _root_.BitVec.ssubOverflow, Bool.or_eq_true, decide_eq_true_eq,
    toSigned, signedMin, signedMax]
  omega
theorem bvsmulo_semantics (x y : _root_.BitVec n) :
    bvsmulo x y = true ↔
      toSigned x * toSigned y < signedMin n ∨ signedMax n < toSigned x * toSigned y := by
  simp only [bvsmulo, _root_.BitVec.smulOverflow, Bool.or_eq_true, decide_eq_true_eq,
    toSigned, signedMin, signedMax]
  omega

theorem bvsdivo_semantics (hn : 0 < n) (x y : _root_.BitVec n) :
    bvsdivo x y = true ↔ toSigned x = signedMin n ∧ toSigned y = -1 := by
  simp only [bvsdivo, _root_.BitVec.sdivOverflow_eq, Bool.and_eq_true,
    decide_eq_true_eq, hn, true_and]
  rw [← _root_.BitVec.toInt_inj, ← _root_.BitVec.toInt_inj]
  simp only [_root_.BitVec.toInt_intMin_of_pos hn, _root_.BitVec.toInt_allOnes,
    hn, ↓reduceIte, toSigned, signedMin]

end SMT.BitVec
