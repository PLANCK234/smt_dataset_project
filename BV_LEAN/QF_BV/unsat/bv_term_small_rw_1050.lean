/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_1050.smt2
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

private theorem bvlshr_bvnot_self (x : BitVec n) :
    bvlshr (bvnot x) x = bvlshr (bvnot (literal n 0)) x := by
  rw [← bvor_bvnot x, bvlshr_bvor, bvlshr_self]
  simp [bvor, literal]

private theorem bvlshr_bvand_bvnot (x y : BitVec n) :
    bvlshr (bvand x y) (bvnot x) = bvlshr y (bvnot x) := by
  have h := bvlshr_bvnot_self (bvnot x)
  simp only [bvnot_bvnot] at h
  rw [bvlshr_bvand, h, bvand_comm, ← bvlshr_bvand, bvand_bvnot_zero]

private theorem bvlshr_bvnot_bvand_same (x y : BitVec n) :
    bvlshr y (bvnot (bvand x y)) = bvlshr x (bvnot (bvand x y)) := by
  have hy := bvlshr_bvand_bvnot (bvand x y) y
  have hx := bvlshr_bvand_bvnot (bvand x y) x
  rw [bvand_assoc, bvand_self] at hy
  have he : bvand (bvand x y) x = bvand x y := by
    rw [bvand_comm (bvand x y) x, ← bvand_assoc, bvand_self]
  rw [he] at hx
  exact hy.symm.trans hx

theorem bv_term_small_rw_1050 :
    ∀ (n : Nat) (s t : BitVec n),
      (bvlshr t (bvnot (bvand s t))) = (bvlshr s (bvnot (bvand s t))) := by
  intro n s t
  exact bvlshr_bvnot_bvand_same s t

end BV.QF_BV.Unsat
