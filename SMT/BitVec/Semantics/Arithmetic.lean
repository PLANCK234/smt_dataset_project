module
prelude

public import Init.Data.BitVec.Bootstrap

public import SMT.BitVec.Model
public import SMT.BitVec.Arithmetic
public import Init.Data.BitVec.Lemmas

/-! Arithmetic semantic contracts, split from SMT.BitVec.Semantics.
Public theorem names and statements are preserved. -/
@[expose] public section

namespace SMT.BitVec

theorem bvneg_semantics (x : _root_.BitVec n) :
    toUnsigned (bvneg x) = (2 ^ n - toUnsigned x) % 2 ^ n :=
  _root_.BitVec.toNat_neg x
theorem bvadd_semantics (x y : _root_.BitVec n) :
    toUnsigned (bvadd x y) = (toUnsigned x + toUnsigned y) % 2 ^ n := rfl
theorem bvsub_semantics (x y : _root_.BitVec n) :
    toUnsigned (bvsub x y) = ((2 ^ n - toUnsigned y) + toUnsigned x) % 2 ^ n := rfl
theorem bvmul_semantics (x y : _root_.BitVec n) :
    toUnsigned (bvmul x y) = (toUnsigned x * toUnsigned y) % 2 ^ n := rfl

end SMT.BitVec
