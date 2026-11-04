/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_1559.smt2
License: CC BY 4.0
-/
import LEMMAS_learned.BitVec.Shift.Basic
import SMT.BitVec.Lemmas

set_option linter.unusedVariables false

namespace BV.QF_BV.Unsat

open SMT.BitVec
open Learned.BitVec

private theorem bvlshr_bvmul_bvlshr_self (x y : BitVec n) : bvlshr (bvmul (bvlshr x y) y) x = literal n 0 := by
  apply bvlshr_eq_zero_of_lt
  rw [toNat_bvmul, toNat_bvlshr]
  apply Nat.lt_of_le_of_lt (Nat.mod_le _ _)
  apply Nat.lt_of_le_of_lt (Nat.mul_le_mul_left _ (Nat.le_of_lt Nat.lt_two_pow_self))
  exact Nat.lt_of_le_of_lt (Nat.div_mul_le_self _ _) Nat.lt_two_pow_self

theorem bv_term_small_rw_1559 :
    ∀ (n : Nat) (s t : BitVec n),
      (bvlshr (bvmul (bvlshr s t) t) s) = (literal n 0) := by
  intro n s t
  exact bvlshr_bvmul_bvlshr_self s t

end BV.QF_BV.Unsat
