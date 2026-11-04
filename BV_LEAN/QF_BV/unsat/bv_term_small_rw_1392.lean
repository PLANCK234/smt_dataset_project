/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_1392.smt2
License: CC BY 4.0
-/
import LEMMAS_learned.BitVec.Shift.Bounds
import SMT.BitVec.Lemmas

set_option linter.unusedVariables false

namespace BV.QF_BV.Unsat

open SMT.BitVec
open Learned.BitVec
open _root_.BitVec (shiftLeft_add shiftLeft_eq')

private theorem bvshl_bvshl_bvlshr (x y z : BitVec n) :
    bvshl (bvshl x y) (bvlshr z y) = bvshl x (bvadd y (bvlshr z y)) := by
  simp only [bvshl_eq_shiftLeft, shiftLeft_eq',
    toNat_bvadd_bvlshr, shiftLeft_add]

theorem bv_term_small_rw_1392 :
    ∀ (n : Nat) (s t : BitVec n),
      (bvshl (bvshl s t) (bvlshr s t)) = (bvshl s (bvadd t (bvlshr s t))) := by
  intro n s t
  simp only [bvshl_bvshl_bvlshr]

end BV.QF_BV.Unsat
