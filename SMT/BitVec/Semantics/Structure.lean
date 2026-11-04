module
prelude

public import Init.Data.BitVec.Bootstrap
public import Init.Data.Nat.Bitwise.Lemmas
public import Init.Omega

public import SMT.BitVec.Model
public import SMT.BitVec.Structure
public import Init.Data.BitVec.Lemmas

/-! Structure semantic contracts, split from SMT.BitVec.Semantics.
Public theorem names and statements are preserved. -/
@[expose] public section

namespace SMT.BitVec

theorem concat_semantics (x : _root_.BitVec m) (y : _root_.BitVec n) :
    toUnsigned (concat x y) = toUnsigned x * 2 ^ n + toUnsigned y := by
  simp only [concat, toUnsigned, _root_.BitVec.toNat_append]
  rw [← Nat.shiftLeft_add_eq_or_of_lt y.isLt, Nat.shiftLeft_eq]
theorem extract_semantics (hi lo : Nat) (x : _root_.BitVec n)
    (_hlo : lo ≤ hi) (_hhi : hi < n) :
    toUnsigned (extract hi lo x) = (toUnsigned x / 2 ^ lo) % 2 ^ (hi - lo + 1) := by
  simp [extract, toUnsigned, Nat.shiftRight_eq_div_pow]

theorem zeroExtend_semantics (extra : Nat) (x : _root_.BitVec n) :
    toUnsigned (zeroExtend extra x) = toUnsigned x :=
  _root_.BitVec.toNat_setWidth_of_le (Nat.le_add_right _ _)
theorem signExtend_semantics (extra : Nat) (x : _root_.BitVec n) :
    toSigned (signExtend extra x) = toSigned x :=
  _root_.BitVec.toInt_signExtend_of_le (Nat.le_add_right _ _)
theorem repeat_semantics (count : Nat) (x : _root_.BitVec n)
    (_hcount : 0 < count) (hi : i < n * count) :
    (SMT.BitVec.repeat count x).getLsbD i = x.getLsbD (i % n) := by
  simp only [SMT.BitVec.repeat, _root_.BitVec.getLsbD_replicate, hi, decide_true, Bool.true_and]
theorem rotateLeft_semantics (count : Nat) (x : _root_.BitVec n) (hi : i < n) :
    (rotateLeft count x).getLsbD i = x.getLsbD ((i + n - count % n) % n) := by
  have hn : 0 < n := by omega
  have hc : count % n < n := Nat.mod_lt count hn
  rw [_root_.BitVec.getLsbD_rotateLeft]
  split
  next h =>
    have he : (i + n - count % n) % n = n - count % n + i := by
      rw [Nat.mod_eq_of_lt (by omega)]
      omega
    rw [he]
  next h =>
    simp only [hi, decide_true, Bool.true_and]
    have he : i + n - count % n = (i - count % n) + n := by omega
    rw [he, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : i - count % n < n)]
theorem rotateRight_semantics (count : Nat) (x : _root_.BitVec n) (hi : i < n) :
    (rotateRight count x).getLsbD i = x.getLsbD ((i + count % n) % n) := by
  have hn : 0 < n := by omega
  have hc : count % n < n := Nat.mod_lt count hn
  rw [_root_.BitVec.getLsbD_rotateRight]
  split
  next h =>
    have he : (i + count % n) % n = i + count % n := Nat.mod_eq_of_lt (by omega)
    rw [he]
    congr 1
    omega
  next h =>
    simp only [hi, decide_true, Bool.true_and]
    have he : i + count % n = (i - (n - count % n)) + n := by omega
    rw [he, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : i - (n - count % n) < n)]
theorem rotateLeft_periodic (count : Nat) (x : _root_.BitVec n) :
    rotateLeft (count % n) x = rotateLeft count x :=
  _root_.BitVec.rotateLeft_mod_eq_rotateLeft
theorem rotateRight_periodic (count : Nat) (x : _root_.BitVec n) :
    rotateRight (count % n) x = rotateRight count x :=
  _root_.BitVec.rotateRight_mod_eq_rotateRight

/-- PBV extraction with symbolic indices has the same valid-domain slice semantics. -/
theorem pextract_semantics (hi lo : Nat) (x : _root_.BitVec n)
    (hlo : lo ≤ hi) (hhi : hi < n) :
    toUnsigned (pextract hi lo x) = (toUnsigned x / 2 ^ lo) % 2 ^ (hi - lo + 1) :=
  extract_semantics hi lo x hlo hhi
/-- Zero extension preserves the unsigned value for every nonnegative extension amount. -/
theorem pzero_extend_semantics (extra : Nat) (x : _root_.BitVec n) (_hn : 0 < n) :
    toUnsigned (pzero_extend extra x) = toUnsigned x :=
  zeroExtend_semantics extra x
/-- Sign extension preserves the signed value for every nonnegative extension amount. -/
theorem psign_extend_semantics (extra : Nat) (x : _root_.BitVec n) (_hn : 0 < n) :
    toSigned (psign_extend extra x) = toSigned x :=
  signExtend_semantics extra x

end SMT.BitVec
