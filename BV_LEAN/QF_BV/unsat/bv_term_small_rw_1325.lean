/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_1325.smt2
License: CC BY 4.0
-/
import LEMMAS_learned.BitVec.Shift.Basic
import SMT.BitVec.Lemmas

set_option linter.unusedVariables false

namespace BV.QF_BV.Unsat

open SMT.BitVec
open Learned.BitVec

private theorem bvlshr_bvnot_self (x : BitVec n) :
    bvlshr (bvnot x) x = bvlshr (bvnot (literal n 0)) x := by
  rw [← bvor_bvnot x, bvlshr_bvor, bvlshr_self]
  simp [bvor, literal]

private theorem bvlshr_bvand_bvnot (x y : BitVec n) :
    bvlshr (bvand x y) (bvnot x) = bvlshr y (bvnot x) := by
  have h := bvlshr_bvnot_self (bvnot x)
  simp only [bvnot_bvnot] at h
  rw [bvlshr_bvand, h, bvand_comm, ← bvlshr_bvand, bvand_bvnot_zero]

theorem bv_term_small_rw_1325 :
    ∀ (n : Nat) (s t : BitVec n),
      (bvlshr (bvand s t) (bvnot s)) = (bvlshr t (bvnot (bvand s s))) := by
  intro n s t
  rw [bvand_self]
  exact bvlshr_bvand_bvnot s t

end BV.QF_BV.Unsat
