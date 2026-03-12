import Mathlib.Data.Num.Bitwise
import Reap

variable {n : Nat} {npos : 0 < n}

/--
Translation of the SMT assertion:

(assert (not (= (bvor s (bvmul (bvand t 0) s)) s)))

"unsat" means: there do not exist `s t : BitVec 32` making that assertion true.
-/
theorem bv_term_small_rw_1001 :
  ¬ ∃ (s t : BitVec 32),
      ¬ ((s ||| ((t &&& (0#32)) * s)) = s) := by
  simp only [BitVec.and_zero, BitVec.zero_mul, BitVec.or_zero, not_true_eq_false, exists_const,
    not_false_eq_true]

theorem bv_term_small_rw_1001' :
    ¬ ∃ (s t : BitVec n),
      ¬ ((s ||| ((t &&& (0#n)) * s)) = s) := by
  simp only [BitVec.and_zero, BitVec.zero_mul, BitVec.or_zero, not_true_eq_false, exists_const,
    not_false_eq_true]
