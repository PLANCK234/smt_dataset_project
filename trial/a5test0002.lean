import Mathlib.Data.Num.Bitwise


/-- Signed interpretation (two's complement) of a bitvector. -/
def sbv_to_int {n : Nat} (x : BitVec n) : Int :=
  x.toInt

/-- Signed less-than (SMT-LIB `bvslt`). -/
def bvslt {n : Nat} (x y : BitVec n) : Prop :=
  sbv_to_int x < sbv_to_int y

/-
SMT-LIB:

(declare-fun a () (_ BitVec 32))
(assert (not (bvslt (_ bv100 32) a)))
(check-sat)

Meaning (sat): ∃ a : BitVec 32, ¬ bvslt (100:32) a
-/
theorem a5test0002.smt2 :
    ∃ a : BitVec 32, ¬ bvslt (BitVec.ofNat 32 100) a := by
  -- Witness: a = 0 works because 100 <_s 0 is false.
  exact ⟨100, by simp only [bvslt, BitVec.ofNat_eq_ofNat, lt_self_iff_false, not_false_eq_true]⟩
