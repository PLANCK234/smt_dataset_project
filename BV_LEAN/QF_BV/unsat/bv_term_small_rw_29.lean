/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_29.smt2
License: CC BY 4.0
-/
import SMT.BitVec.Lemmas

set_option linter.unusedVariables false

namespace BV.QF_BV.Unsat

open SMT.BitVec
open _root_.BitVec (ushiftRight_eq' ushiftRight_eq_zero)

theorem bv_term_small_rw_29 :
    ∀ (n : Nat) (s t : BitVec n),
      (bvlshr s (bvnot (literal n 0))) = (literal n 0) := by
  intro n s t
  have hpow : n < 2 ^ n := Nat.lt_two_pow_self
  have h : n ≤ (bvnot (literal n 0)).toNat := by
    simp only [toNat_bvnot, toNat_literal,
      Nat.zero_mod, Nat.sub_zero]
    omega
  simp only [bvlshr, literal, ushiftRight_eq']
  exact ushiftRight_eq_zero h

end BV.QF_BV.Unsat
