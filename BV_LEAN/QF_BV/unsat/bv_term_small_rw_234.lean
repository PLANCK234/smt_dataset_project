/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_234.smt2
License: CC BY 4.0
-/
import LEMMAS_learned.BitVec.Shift.Self

set_option linter.unusedVariables false

namespace BV.QF_BV.Unsat

open SMT.BitVec
open Learned.BitVec
open _root_.BitVec (neg_zero)

/- Proof sketch: let b=s<<s. If b=0 both sides are s; otherwise b≥2^s>s and the right side is zero.
The left side is cleared by (-b).toNat≥n, using divisibility when 2^s≥n and the half-range bound when 2^s<n.
The argument covers n=0. -/

private theorem bvshl_bvneg_bvshl_self (x : BitVec n) :
    bvshl x (bvneg (bvshl x x)) = bvlshr x (bvshl x x) := by
  by_cases hb : bvshl x x = literal n 0
  · rw [hb]
    simp only [bvneg, literal, neg_zero, bvshl_zero, bvlshr_zero]
  · have hc := width_le_toNat_bvneg_bvshl_self x hb
    have hr : bvlshr x (bvshl x x) = literal n 0 :=
      bvlshr_eq_zero_of_le x _ (Nat.le_of_lt (lt_toNat_bvshl_of_ne_zero x x hb))
    rw [bvshl_large _ _ hc, hr]

theorem bv_term_small_rw_234 :
    ∀ (n : Nat) (s t : BitVec n),
      (bvshl s (bvneg (bvshl s s))) = (bvlshr s (bvshl s s)) := by
  intro n s t
  exact bvshl_bvneg_bvshl_self s

end BV.QF_BV.Unsat
