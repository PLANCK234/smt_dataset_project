/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_1544.smt2
License: CC BY 4.0
-/
import LEMMAS_learned.BitVec.Shift.Basic
import LEMMAS_learned.Nat.Pow
import SMT.BitVec.Lemmas

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace BV.QF_BV.Unsat

open SMT.BitVec
open Learned.BitVec
open _root_.BitVec (shiftLeft_add shiftLeft_eq' shiftRight_add toNat_add ushiftRight_eq')

theorem bv_term_small_rw_1544 :
    ∀ (n : Nat) (s t : BitVec n),
      (bvshl (bvshl (bvshl s s) s) s) = (bvshl (bvshl s s) (bvadd s s)) := by
  intro n s t
  by_cases h : n ≤ s.toNat
  · have hl (x : BitVec n) := bvshl_large x s h
    have hr (x : BitVec n) := bvlshr_large x s h
    simp only [hl, hr] <;>
      simp [bvshl_eq_shiftLeft, bvlshr, literal]
  · have hsum : s.toNat + s.toNat < 2^n := by
      have := @Learned.Nat.two_mul_le_two_pow n
      omega
    simp only [bvshl_eq_shiftLeft, bvlshr,
      bvadd, shiftLeft_eq', ushiftRight_eq',
      toNat_add, Nat.mod_eq_of_lt hsum,
      ← shiftLeft_add, ← shiftRight_add, Nat.add_assoc]

end BV.QF_BV.Unsat
