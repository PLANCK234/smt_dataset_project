/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_1547.smt2
License: CC BY 4.0
-/
import SMT.BitVec.Lemmas

set_option linter.unusedVariables false

namespace BV.QF_BV.Unsat

open SMT.BitVec

private theorem bvlshr_bvlshr_bvadd_self (x y : BitVec n) : bvlshr (bvlshr (bvadd x y) x) y = literal n 0 := by
  apply toNat_injective
  simp only [toNat_bvlshr, toNat_bvadd, toNat_literal, Nat.zero_mod]
  rw [Nat.div_div_eq_div_mul, ← Nat.pow_add]
  exact Nat.div_eq_of_lt (Nat.lt_of_le_of_lt (Nat.mod_le _ _) Nat.lt_two_pow_self)

theorem bv_term_small_rw_1547 :
    ∀ (n : Nat) (s t : BitVec n),
      (bvlshr (bvlshr (bvadd s t) s) t) = (literal n 0) := by
  intro n s t
  simp only [bvlshr_bvlshr_bvadd_self]

end BV.QF_BV.Unsat
