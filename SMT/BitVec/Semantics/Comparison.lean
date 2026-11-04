module
prelude

public import SMT.BitVec.Model
public import SMT.BitVec.Comparison
public import Init.Data.BitVec.Lemmas

/-! Comparison semantic contracts, split from SMT.BitVec.Semantics.
Public theorem names and statements are preserved. -/
@[expose] public section

namespace SMT.BitVec

theorem bvult_semantics (x y : _root_.BitVec n) :
    bvult x y = true ↔ toUnsigned x < toUnsigned y := by simp [bvult, _root_.BitVec.ult]
theorem bvule_semantics (x y : _root_.BitVec n) :
    bvule x y = true ↔ toUnsigned x ≤ toUnsigned y := by simp [bvule, _root_.BitVec.ule]
theorem bvugt_semantics (x y : _root_.BitVec n) :
    bvugt x y = true ↔ toUnsigned x > toUnsigned y := bvult_semantics y x
theorem bvuge_semantics (x y : _root_.BitVec n) :
    bvuge x y = true ↔ toUnsigned x ≥ toUnsigned y := bvule_semantics y x
theorem bvslt_semantics (x y : _root_.BitVec n) :
    bvslt x y = true ↔ toSigned x < toSigned y := by simp [bvslt, _root_.BitVec.slt]
theorem bvsle_semantics (x y : _root_.BitVec n) :
    bvsle x y = true ↔ toSigned x ≤ toSigned y := by simp [bvsle, _root_.BitVec.sle]
theorem bvsgt_semantics (x y : _root_.BitVec n) :
    bvsgt x y = true ↔ toSigned x > toSigned y := bvslt_semantics y x
theorem bvsge_semantics (x y : _root_.BitVec n) :
    bvsge x y = true ↔ toSigned x ≥ toSigned y := bvsle_semantics y x

end SMT.BitVec
