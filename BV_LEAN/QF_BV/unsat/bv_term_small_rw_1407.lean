/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_1407.smt2
License: CC BY 4.0
-/
import Init.Data.Nat.MinMax
import LEMMAS_learned.BitVec.Shift.Basic
import SMT.BitVec.ToNat.Arithmetic

set_option linter.unusedVariables false

namespace BV.QF_BV.Unsat

open SMT.BitVec
open Learned.BitVec

private theorem bvlshr_bvnot_bvneg (x : BitVec n) :
    bvlshr (bvnot (bvneg x)) x = bvlshr (bvnot x) (bvneg x) := by
  by_cases hx : x = literal n 0
  · subst x; simp [bvneg, literal]
  have hx0 : 0 < x.toNat := by
    apply Nat.pos_of_ne_zero
    intro h; apply hx; apply toNat_injective; simpa only [toNat_literal, Nat.zero_mod] using h
  have hlt := x.isLt
  have hp := Nat.two_pow_pos n
  have hn : (bvneg x).toNat = 2 ^ n - x.toNat := by
    rw [toNat_bvneg, Nat.mod_eq_of_lt (by omega)]
  rw [bvlshr_eq_zero_of_le (bvnot (bvneg x)) x (by rw [toNat_bvnot, hn]; omega),
    bvlshr_eq_zero_of_le (bvnot x) (bvneg x) (by rw [toNat_bvnot, hn]; omega)]

theorem bv_term_small_rw_1407 :
    ∀ (n : Nat) (s t : BitVec n),
      (bvlshr (bvnot (bvneg s)) s) = (bvlshr (bvnot s) (bvneg s)) := by
  intro n s t
  exact bvlshr_bvnot_bvneg s

end BV.QF_BV.Unsat
