/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_431.smt2
License: CC BY 4.0
-/
import LEMMAS_learned.BitVec.Shift.Bounds
import SMT.BitVec.Lemmas

set_option linter.unusedVariables false

namespace BV.QF_BV.Unsat

open SMT.BitVec
open Learned.BitVec

private theorem bvlshr_bvadd_bvlshr (x y : BitVec n) :
    bvlshr x (bvadd y (bvlshr x y)) = literal n 0 := by
  apply bvlshr_eq_zero_of_lt
  rw [toNat_bvadd_bvlshr, toNat_bvlshr]
  exact Learned.Nat.lt_two_pow_add_div x.toNat y.toNat

theorem bv_term_small_rw_431 :
    ∀ (n : Nat) (s t : BitVec n),
      (bvlshr s (bvadd t (bvlshr s t))) = (literal n 0) := by
  intro n s t
  simp only [bvlshr_bvadd_bvlshr]

end BV.QF_BV.Unsat
