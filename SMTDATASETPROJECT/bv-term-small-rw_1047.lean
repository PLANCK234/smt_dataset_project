import Mathlib.Data.Num.Bitwise
import Reap

variable {n : Nat} {npos : 0 < n}

/--
SMT:
(assert (not (= (bvshl s (bvshl (bvand t 0) t)) s)))

unsat means: there do not exist `s t : BitVec 32` making the asserted `not (= ...)` true.
-/
theorem bv_term_small_rw_1047 :
  ¬ ∃ (s t : BitVec 32),
      ¬ (((s <<< ((t &&& (0#32)) <<< t)) = s)) := by
  simp only [BitVec.and_zero, BitVec.shiftLeft_eq', BitVec.zero_shiftLeft, BitVec.toNat_ofNat,
    Nat.reducePow, Nat.zero_mod, BitVec.shiftLeft_zero, not_true_eq_false, exists_const,
    not_false_eq_true]

theorem bv_term_small_rw_1047_p1 :
  ¬ ∃ (s t : BitVec 32),
      ¬ (((s <<< ((t &&& (0#32)) <<< t)) = s)) := by
  intro h
  rcases h with ⟨s, t, hnot⟩
  have : (s <<< ((t &&& (0#32)) <<< t)) = s := by
    -- key simplifications:
    -- t &&& 0 = 0
    -- 0 <<< t = 0
    -- s <<< 0 = s
    simp
  exact hnot this

theorem bv_term_small_rw_1047' :
  ¬ ∃ (s t : BitVec n),
      ¬ (((s <<< ((t &&& (0#n)) <<< t)) = s)) := by
    simp only [BitVec.and_zero, BitVec.shiftLeft_eq', BitVec.zero_shiftLeft, BitVec.toNat_ofNat,
      Nat.zero_mod, BitVec.shiftLeft_zero, not_true_eq_false, exists_const, not_false_eq_true]
