/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_1445.smt2
License: CC BY 4.0
-/
import Init.Data.Nat.MinMax
import LEMMAS_learned.BitVec.Shift.Basic
import LEMMAS_learned.Nat.Pow
import SMT.BitVec.ToNat.Arithmetic

set_option linter.unusedVariables false

namespace BV.QF_BV.Unsat

open SMT.BitVec
open Learned.BitVec

private theorem bvshl_bvlshr_bvmul_self (x : BitVec n) :
    bvshl (bvlshr x (bvmul x x)) x = literal n 0 := by
  by_cases hn : n ≤ x.toNat
  · exact bvshl_large _ _ hn
  have hp := Learned.Nat.sq_lt_two_pow_succ x.toNat
  have he : 2 ^ (x.toNat + 1) ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) (by omega)
  have hb : x.toNat ≤ (bvmul x x).toNat := by
    rw [toNat_bvmul, Nat.mod_eq_of_lt (by omega)]
    exact Nat.le_mul_self _
  rw [bvlshr_eq_zero_of_le x _ hb]
  simp [bvshl_eq_shiftLeft, literal]

theorem bv_term_small_rw_1445 :
    ∀ (n : Nat) (s t : BitVec n),
      (bvshl (bvlshr s (bvmul s s)) s) = (literal n 0) := by
  intro n s t
  exact bvshl_bvlshr_bvmul_self s

end BV.QF_BV.Unsat
