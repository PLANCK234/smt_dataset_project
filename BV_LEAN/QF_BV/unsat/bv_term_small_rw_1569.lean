/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_1569.smt2
License: CC BY 4.0
-/
import SMT.BitVec.Lemmas

set_option linter.unusedVariables false

namespace BV.QF_BV.Unsat

open SMT.BitVec

private theorem bvlshr_bvlshr_bvshl_self (x y : BitVec n) : bvlshr (bvlshr (bvshl x y) x) y = literal n 0 := by
  apply toNat_injective
  simp only [toNat_bvlshr, toNat_bvshl, toNat_literal, Nat.zero_mod]
  rw [Nat.div_div_eq_div_mul, ← Nat.pow_add]
  apply Nat.div_eq_of_lt
  apply Nat.lt_of_le_of_lt (Nat.mod_le _ _)
  rw [Nat.pow_add]
  exact Nat.mul_lt_mul_of_pos_right Nat.lt_two_pow_self (Nat.two_pow_pos _)

theorem bv_term_small_rw_1569 :
    ∀ (n : Nat) (s t : BitVec n),
      (bvlshr (bvlshr (bvshl s t) s) t) = (literal n 0) := by
  intro n s t
  simp only [bvlshr_bvlshr_bvshl_self]

end BV.QF_BV.Unsat
