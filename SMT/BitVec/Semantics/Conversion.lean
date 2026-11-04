module
prelude

public import Init.Data.BitVec.Bootstrap

public import SMT.BitVec.Model
public import SMT.BitVec.Conversion
public import Init.Data.BitVec.Lemmas

/-! Conversion semantic contracts, split from SMT.BitVec.Semantics.
Public theorem names and statements are preserved. -/
@[expose] public section

namespace SMT.BitVec

theorem ubv_to_int_semantics (x : _root_.BitVec n) :
    ubv_to_int x = (toUnsigned x : Int) := rfl
theorem sbv_to_int_semantics (x : _root_.BitVec n) :
    sbv_to_int x = toSigned x := rfl

theorem int_to_bv_semantics (n : Nat) (z : Int) :
    toUnsigned (int_to_bv n z) = (z % (2 ^ n : Nat)).toNat :=
  _root_.BitVec.toNat_ofInt z
theorem unsigned_roundtrip (x : _root_.BitVec n) : int_to_bv n (ubv_to_int x) = x := by
  simp [int_to_bv, ubv_to_int]
theorem signed_roundtrip (x : _root_.BitVec n) : int_to_bv n (sbv_to_int x) = x :=
  _root_.BitVec.ofInt_toInt

/-- PBV integer conversion agrees with the nonnegative residue, at every valid width. -/
theorem int_to_pbv_semantics (n : Nat) (z : Int) (_hn : 0 < n) :
    toUnsigned (int_to_pbv n z) = (z % (2 ^ n : Nat)).toNat :=
  int_to_bv_semantics n z

end SMT.BitVec
