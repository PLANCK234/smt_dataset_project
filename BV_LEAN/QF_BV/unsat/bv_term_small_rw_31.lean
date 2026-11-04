/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_31.smt2
License: CC BY 4.0
-/
import SMT.BitVec.Lemmas

set_option linter.unusedVariables false

namespace BV.QF_BV.Unsat

open SMT.BitVec

theorem bv_term_small_rw_31 :
    ∀ (n : Nat) (s t : BitVec n),
      (bvshl s (bvnot (literal n 0))) = (literal n 0) := by
  intro n s t
  have hpow : n < 2 ^ n := Nat.lt_two_pow_self
  have h : n ≤ (bvnot (literal n 0)).toNat := by
    simp only [toNat_bvnot, toNat_literal,
      Nat.zero_mod, Nat.sub_zero]
    omega
  exact bvshl_large s _ h

end BV.QF_BV.Unsat
