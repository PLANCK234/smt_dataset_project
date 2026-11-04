module
prelude

public import SMT.BitVec.Model
public import SMT.BitVec.Bitwise
public import Init.Data.BitVec.Lemmas

/-! Bitwise semantic contracts, split from SMT.BitVec.Semantics.
Public theorem names and statements are preserved. -/
@[expose] public section

namespace SMT.BitVec

theorem bvnot_semantics (x : _root_.BitVec n) (hi : i < n) :
    (bvnot x).getLsbD i = !x.getLsbD i := by simp [hi]
theorem bvand_semantics (x y : _root_.BitVec n) :
    (bvand x y).getLsbD i = (x.getLsbD i && y.getLsbD i) := _root_.BitVec.getLsbD_and
theorem bvor_semantics (x y : _root_.BitVec n) :
    (bvor x y).getLsbD i = (x.getLsbD i || y.getLsbD i) := _root_.BitVec.getLsbD_or
theorem bvxor_semantics (x y : _root_.BitVec n) :
    (bvxor x y).getLsbD i = (Bool.xor (x.getLsbD i) (y.getLsbD i)) :=
  _root_.BitVec.getLsbD_xor
theorem bvnand_semantics (x y : _root_.BitVec n) (hi : i < n) :
    (bvnand x y).getLsbD i = !(x.getLsbD i && y.getLsbD i) := by simp [hi]
theorem bvnor_semantics (x y : _root_.BitVec n) (hi : i < n) :
    (bvnor x y).getLsbD i = !(x.getLsbD i || y.getLsbD i) := by simp [hi]
theorem bvxnor_semantics (x y : _root_.BitVec n) (hi : i < n) :
    (bvxnor x y).getLsbD i = !(Bool.xor (x.getLsbD i) (y.getLsbD i)) := by simp [hi]
theorem bvcomp_semantics (x y : _root_.BitVec n) :
    bvcomp x y = if x = y then literal 1 1 else literal 1 0 := by
  simp [bvcomp, _root_.BitVec.ofBool]

end SMT.BitVec
