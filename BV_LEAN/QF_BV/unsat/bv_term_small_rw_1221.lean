/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_1221.smt2
License: CC BY 4.0
-/
import Init.Data.BitVec.Bitblast
import Init.Data.Nat.MinMax
import LEMMAS_learned.BitVec.Shift.Basic
import SMT.BitVec.ToNat.Arithmetic

set_option linter.unusedVariables false

namespace BV.QF_BV.Unsat

open SMT.BitVec
open Learned.BitVec

private theorem bvand_bvneg_bvshl_same (x : BitVec n) :
    bvand (bvneg x) (bvshl x x) = bvshl x x := by
  by_cases hx : x = literal n 0
  · subst x; simp [bvneg, bvshl_eq_shiftLeft, bvand, literal]
  have hx0 : 0 < x.toNat := by
    apply Nat.pos_of_ne_zero
    intro h; apply hx; apply toNat_injective; simpa only [toNat_literal, Nat.zero_mod] using h
  have hlt := x.isLt
  have hp := Nat.two_pow_pos n
  have hb : (bvnot (bvneg x)).toNat < 2 ^ x.toNat := by
    rw [toNat_bvnot, toNat_bvneg, Nat.mod_eq_of_lt (by omega)]
    have := Nat.lt_two_pow_self (n := x.toNat)
    omega
  have hd := bvand_bvshl_eq_zero_of_lt _ x x hb
  rw [bvand_comm] at hd
  have h := bvand_bvnot_of_bvand_eq_zero _ _ hd
  simpa only [bvnot_bvnot, bvand_comm] using h

theorem bv_term_small_rw_1221 :
    ∀ (n : Nat) (s t : BitVec n),
      (bvand (bvneg s) (bvshl s s)) = (bvshl s s) := by
  intro n s t
  exact bvand_bvneg_bvshl_same s

end BV.QF_BV.Unsat
