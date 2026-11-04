/-
Released under Apache 2.0; see THIRD_PARTY_LICENSES/Apache-2.0.txt.
Local derivations from Lean 4.34.1 Init and the SMT API.
Source dependencies and pinned revisions: upstream.json.
-/
module
prelude

public import LEMMAS_learned.BitVec.Shift.Carry
public import LEMMAS_learned.BitVec.Shift.Self
public import LEMMAS_learned.Nat.Shift

@[expose] public section

namespace Learned.BitVec
open SMT.BitVec

/-- An n-bit left shift vanishes exactly when its natural product is divisible by 2^n. -/
theorem bvshl_eq_zero_iff_dvd (x y : _root_.BitVec n) :
    bvshl x y = literal n 0 ↔ 2 ^ n ∣ x.toNat * 2 ^ y.toNat := by
  rw [eq_iff_toNat_eq, toNat_bvshl, toNat_literal, Nat.zero_mod]
  exact Nat.dvd_iff_mod_eq_zero.symm

/-- Left and right shifts agree uniformly in the word exactly for zero or clearing counts. -/
theorem bvshl_eq_bvlshr_forall_iff (y : _root_.BitVec n) :
    (∀ x : _root_.BitVec n, bvshl x y = bvlshr x y) ↔
      y.toNat = 0 ∨ n ≤ y.toNat := by
  constructor
  · intro h
    by_cases hz : y.toNat = 0
    · exact Or.inl hz
    by_cases hn : n ≤ y.toNat
    · exact Or.inr hn
    have hn0 : 0 < n := by omega
    have hp : 1 < 2 ^ n := Nat.one_lt_two_pow (by omega)
    have hy : 1 < 2 ^ y.toNat := Nat.one_lt_two_pow (by omega)
    have he := congrArg _root_.BitVec.toNat (h (literal n 1))
    simp only [toNat_bvshl, toNat_bvlshr, toNat_literal, Nat.mod_eq_of_lt hp,
      Nat.one_mul, Nat.div_eq_of_lt hy] at he
    have hlt : 2 ^ y.toNat < 2 ^ n := Nat.pow_lt_pow_right (by decide) (by omega)
    rw [Nat.mod_eq_of_lt hlt] at he
    have := Nat.two_pow_pos y.toNat
    omega
  · intro h x
    rcases h with hz | hn
    · have he : y = literal n 0 := by
        apply toNat_injective
        simpa only [toNat_literal, Nat.zero_mod] using hz
      rw [he, bvshl_zero, bvlshr_zero]
    · rw [bvshl_large _ _ hn, Learned.BitVec.bvlshr_large _ _ hn]

/-- A word shifted by its negation is zero or large enough to clear an n-bit word. -/
theorem width_le_toNat_bvshl_bvneg_self (x : _root_.BitVec n)
    (h : bvshl x (bvneg x) ≠ literal n 0) : n ≤ (bvshl x (bvneg x)).toNat := by
  have he : bvshl x (bvneg x) = bvneg (bvshl (bvneg x) (bvneg x)) := by
    rw [← Learned.BitVec.bvshl_bvneg, bvneg_bvneg]
  have hb : bvshl (bvneg x) (bvneg x) ≠ literal n 0 := by
    intro hb
    apply h
    rw [he, hb]
    simp only [bvneg, literal, _root_.BitVec.neg_zero]
  rw [he]
  exact Learned.BitVec.width_le_toNat_bvneg_bvshl_self (bvneg x) hb

/-- Doubling a shifted word only loses its last nonzero bit when that word is the top bit. -/
theorem bvshl_bvnot_eq_zero_iff_bvshl_bvneg_eq_zero (x : _root_.BitVec n)
    (hhalf : (bvshl x (bvnot x)).toNat ≠ 2 ^ (n - 1)) :
    bvshl x (bvnot x) = literal n 0 ↔ bvshl x (bvneg x) = literal n 0 := by
  have he : bvshl x (bvneg x) = bvadd (bvshl x (bvnot x)) (bvshl x (bvnot x)) := by
    rw [← Learned.BitVec.bvshl_bvadd_self_bvnot_same, Learned.BitVec.bvshl_bvadd]
  rw [he, eq_iff_toNat_eq, eq_iff_toNat_eq, toNat_bvadd, toNat_literal, Nat.zero_mod]
  constructor
  · intro h; rw [h]; simp
  · intro h
    have ha := (bvshl x (bvnot x)).isLt
    by_cases hn : n = 0
    · subst n; simp only [Nat.pow_zero] at ha; omega
    have hp : 2 ^ n = 2 ^ (n - 1) * 2 := by
      conv => lhs; rw [show n = n - 1 + 1 by omega, Nat.pow_succ]
    have hdouble : (bvshl x (bvnot x)).toNat + (bvshl x (bvnot x)).toNat < 2 * 2 ^ n := by omega
    by_cases hlo : (bvshl x (bvnot x)).toNat + (bvshl x (bvnot x)).toNat < 2 ^ n
    · rw [Nat.mod_eq_of_lt hlo] at h; omega
    · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)] at h
      omega

/-- Without truncation, a left shift is at least its unshifted input. -/
theorem toNat_le_bvshl_of_mul_lt (x y : _root_.BitVec n)
    (h : x.toNat * 2 ^ y.toNat < 2 ^ n) : x.toNat ≤ (bvshl x y).toNat := by
  rw [toNat_bvshl, Nat.mod_eq_of_lt h]
  exact Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)

/-- Except at width two, the complement of a self-shift clears every word.
The width-two exception is witnessed by x=1. Widths zero and one are included. -/
theorem width_le_toNat_bvnot_bvshl_self (x : _root_.BitVec n) (hn : n ≠ 2) :
    n ≤ (bvnot (bvshl x x)).toNat := by
  by_cases hn0 : n = 0
  · subst n; exact Nat.zero_le _
  by_cases hn1 : n = 1
  · subst n
    have hx : x.toNat < 2 := x.isLt
    have hcases : x.toNat = 0 ∨ x.toNat = 1 := by omega
    rw [toNat_bvnot, toNat_bvshl]
    rcases hcases with h | h <;> simp [h]
  have hn3 : 3 ≤ n := by omega
  have hx := x.isLt
  have hb_lt := (bvshl x x).isLt
  have hwidth := Learned.Nat.two_mul_le_two_pow (n := n)
  by_cases hz : bvshl x x = literal n 0
  · rw [hz]; exact Learned.BitVec.width_le_toNat_bvnot_zero
  have hb0 : 0 < (bvshl x x).toNat := by
    by_cases h : (bvshl x x).toNat = 0
    · exact False.elim (hz (toNat_injective (by simpa only [toNat_literal, Nat.zero_mod] using h)))
    · omega
  have hc : (bvneg (bvshl x x)).toNat = 2 ^ n - (bvshl x x).toNat := by
    rw [toNat_bvneg, Nat.mod_eq_of_lt (by omega)]
  by_cases ha : n < 2 ^ x.toNat
  · have hd : 2 ^ x.toNat ∣ (bvneg (bvshl x x)).toNat := by
      rw [← Learned.BitVec.bvshl_bvneg]
      exact Learned.BitVec.two_pow_dvd_toNat_bvshl _ _
    have hle := Nat.le_of_dvd (show 0 < (bvneg (bvshl x x)).toNat by rw [hc]; omega) hd
    rw [toNat_bvnot]
    rw [hc] at hle
    omega
  by_cases heq : n = 2 ^ x.toNat
  · have ha2 : 2 ≤ x.toNat := by
      by_cases h0 : x.toNat = 0
      · simp only [h0, Nat.pow_zero] at heq; omega
      by_cases h1 : x.toNat = 1
      · simp only [h1, Nat.pow_one] at heq; omega
      omega
    have htwice := Learned.Nat.two_mul_le_two_pow (n := x.toNat)
    have hprod : (x.toNat + 1) * 2 ^ x.toNat < 2 ^ n := by
      calc
        (x.toNat + 1) * 2 ^ x.toNat < 2 ^ x.toNat * 2 ^ x.toNat :=
          Nat.mul_lt_mul_of_pos_right (Learned.Nat.succ_lt_two_pow_of_two_le _ ha2) (Nat.two_pow_pos _)
        _ = 2 ^ (x.toNat + x.toNat) := (Nat.pow_add ..).symm
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) (by omega)
    have hb : (bvshl x x).toNat ≤ x.toNat * 2 ^ x.toNat := by
      rw [toNat_bvshl]; exact Nat.mod_le _ _
    rw [Nat.add_mul, Nat.one_mul] at hprod
    rw [toNat_bvnot]
    omega
  · have htwice := Learned.Nat.two_mul_le_two_pow (n := x.toNat)
    have hprod : x.toNat * 2 ^ x.toNat < 2 ^ (n - 1) := by
      calc
        x.toNat * 2 ^ x.toNat < 2 ^ x.toNat * 2 ^ x.toNat :=
          Nat.mul_lt_mul_of_pos_right Nat.lt_two_pow_self (Nat.two_pow_pos _)
        _ = 2 ^ (x.toNat + x.toNat) := (Nat.pow_add ..).symm
        _ ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by decide) (by omega)
    have hb : (bvshl x x).toNat < 2 ^ (n - 1) := by
      rw [toNat_bvshl]; exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) hprod
    have hp : 2 ^ n = 2 ^ (n - 1) * 2 := by
      conv => lhs; rw [show n = n - 1 + 1 by omega, Nat.pow_succ]
    rw [toNat_bvnot]
    omega

/-- At a power-of-two width of at least two, shifting by the complement cannot leave only the top bit. -/
theorem bvshl_bvnot_self_ne_top_of_pow_width (n k : Nat) (hwidth : n = 2 ^ (k + 1)) (x : BitVec n) :
    (bvshl x (bvnot x)).toNat ≠ 2 ^ (n - 1) := by
  have hn : 2 ≤ n := by
    rw [hwidth]; exact Nat.pow_le_pow_right (n := 2) (by decide) (show 1 ≤ k + 1 by omega)
  have hp : 2 ^ n = 2 ^ (n - 1) * 2 := by
    conv => lhs; rw [show n = n - 1 + 1 by omega, Nat.pow_succ]
  intro hhalf
  have hA : bvshl x (bvnot x) ≠ literal n 0 := by
    intro hz
    have he := congrArg _root_.BitVec.toNat hz
    simp only [toNat_literal, Nat.zero_mod] at he
    have hpos := Nat.two_pow_pos (n - 1)
    change (bvshl x (bvnot x)).toNat = 2 ^ (n - 1) at hhalf
    omega
  have hx : 0 < x.toNat := by
    by_cases hz : x.toNat = 0
    · apply False.elim; apply hA; apply toNat_injective
      simp only [toNat_bvshl, hz, Nat.zero_mul, Nat.zero_mod, toNat_literal]
    · omega
  have hxlt := x.isLt
  have hd : (bvneg x).toNat = 2 ^ n - x.toNat := by
    rw [toNat_bvneg, Nat.mod_eq_of_lt (by change 2 ^ n - x.toNat < 2 ^ n; omega)]
  have hd0 : 0 < (bvneg x).toNat := by rw [hd]; omega
  have hB : bvshl x (bvneg x) = literal n 0 := by
    rw [← Learned.BitVec.bvshl_bvadd_self_bvnot_same, Learned.BitVec.bvshl_bvadd]
    apply toNat_injective
    rw [toNat_bvadd, hhalf, toNat_literal, Nat.zero_mod]
    change (2 ^ (n - 1) + 2 ^ (n - 1)) % 2 ^ n = 0
    rw [show 2 ^ (n - 1) + 2 ^ (n - 1) = 2 ^ n by omega, Nat.mod_self]
  have hD : bvshl (bvneg x) (bvneg x) = literal n 0 := by
    rw [Learned.BitVec.bvshl_bvneg, hB]
    simp only [bvneg, literal, _root_.BitVec.neg_zero]
  have hdge : n ≤ (bvneg x).toNat := by
    by_cases hlt : (bvneg x).toNat < n
    · have hdiv := (Learned.BitVec.bvshl_eq_zero_iff_dvd _ _).mp hD
      rw [show 2 ^ n = 2 ^ (2 ^ (k + 1)) by rw [hwidth]] at hdiv
      have hlt' : (bvneg x).toNat < 2 ^ (k + 1) := by omega
      exact False.elim ((Learned.Nat.not_two_pow_dvd_self_shift_of_pow_width (k + 1) _ hd0 hlt') hdiv)
    · omega
  have hnot : (bvnot x).toNat = (bvneg x).toNat - 1 := by
    rw [toNat_bvnot, hd]; omega
  have hdle : (bvneg x).toNat ≤ n := by
    by_cases hlt : n < (bvneg x).toNat
    · exact False.elim (hA (bvshl_large _ _ (by rw [hnot]; omega)))
    · omega
  have hdeq : (bvneg x).toNat = n := by omega
  have hevenN : 2 ∣ n := by
    rw [hwidth]; exact Nat.pow_dvd_pow 2 (show 1 ≤ k + 1 by omega)
  have hevenP : 2 ∣ 2 ^ n := Nat.pow_dvd_pow 2 (show 1 ≤ n by omega)
  have hevenX : 2 ∣ x.toNat := by
    have he : x.toNat = 2 ^ n - n := by rw [hd] at hdeq; omega
    rw [he]; exact Nat.dvd_sub hevenP hevenN
  apply hA
  apply (Learned.BitVec.bvshl_eq_zero_iff_dvd _ _).mpr
  rw [hnot, hdeq, hp]
  have hmul := Nat.mul_dvd_mul_right hevenX (2 ^ (n - 1))
  simpa only [Nat.mul_comm 2] using hmul

/-- At power-of-two widths, a nonzero inner shift cannot make the crossed left shift overlap x. -/
theorem bvand_bvshl_bvshl_swap_of_pow_width (n k : Nat) (hw : n = 2 ^ k) (x y : BitVec n)
    (hb : bvshl x y ≠ literal n 0) :
    bvand x (bvshl y (bvshl x y)) = literal n 0 := by
  let b := (bvshl x y).toNat
  have hb0 : 0 < b := by
    by_cases hz : b = 0
    · exact False.elim (hb (toNat_injective (by simpa only [toNat_literal, Nat.zero_mod] using hz)))
    · omega
  by_cases hlarge : n ≤ b
  · rw [bvshl_large _ _ hlarge, bvand_zero]
  have hbn : b < n := by omega
  have hdvd : 2 ^ y.toNat ∣ b := Learned.BitVec.two_pow_dvd_toNat_bvshl x y
  have hdle : 2 ^ y.toNat ≤ b := Nat.le_of_dvd hb0 hdvd
  have hyk : y.toNat < k := by
    apply (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp
    calc
      2 ^ y.toNat ≤ b := hdle
      _ < n := hbn
      _ = 2 ^ k := hw
  have hyn : y.toNat ≤ n := by
    have := Nat.lt_two_pow_self (n := y.toNat); omega
  have hdN : 2 ^ y.toNat ∣ n := by
    conv => rhs; rw [hw]
    exact Nat.pow_dvd_pow 2 (Nat.le_of_lt hyk)
  have hdgap : 2 ^ y.toNat ≤ n - b := Nat.le_of_dvd (by omega) (Nat.dvd_sub hdN hdvd)
  have htwice := Learned.Nat.two_mul_le_two_pow (n := y.toNat)
  have hsum : b + y.toNat + y.toNat ≤ n := by omega
  have hproduct : y.toNat * 2 ^ b < 2 ^ (n - y.toNat) := by
    calc
      y.toNat * 2 ^ b < 2 ^ y.toNat * 2 ^ b :=
        Nat.mul_lt_mul_of_pos_right Nat.lt_two_pow_self (Nat.two_pow_pos _)
      _ = 2 ^ (y.toNat + b) := (Nat.pow_add ..).symm
      _ ≤ 2 ^ (n - y.toNat) := Nat.pow_le_pow_right (by decide) (by omega)
  have hshift : (bvshl y (bvshl x y)).toNat < 2 ^ (n - y.toNat) := by
    rw [toNat_bvshl]
    exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) hproduct
  let a := x.toNat % 2 ^ (n - y.toNat)
  have hfactor : b = 2 ^ y.toNat * a := by
    dsimp [b, a]
    rw [toNat_bvshl, show 2 ^ n = 2 ^ y.toNat * 2 ^ (n - y.toNat) by rw [← Nat.pow_add, Nat.add_sub_of_le hyn],
      Nat.mul_comm x.toNat, Nat.mul_mod_mul_left]
  have hab : a ≤ b := by rw [hfactor]; exact Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _)
  have halow : a < 2 ^ n := Nat.lt_of_le_of_lt (Nat.mod_le _ _) x.isLt
  have hz := Learned.BitVec.bvand_bvshl_eq_zero_of_lt (literal n a) y (bvshl x y)
    (by rw [toNat_literal, Nat.mod_eq_of_lt halow]; exact Nat.lt_of_le_of_lt hab Nat.lt_two_pow_self)
  have hnat := congrArg _root_.BitVec.toNat hz
  simp only [toNat_bvand, toNat_literal, Nat.zero_mod, Nat.mod_eq_of_lt halow] at hnat
  apply toNat_injective
  rw [toNat_bvand, toNat_literal, Nat.zero_mod, SMT.Nat.and_comm]
  rw [Learned.Nat.and_eq_of_mod_two_pow_eq hshift (c := a) (by dsimp [a]; rw [Nat.mod_mod])]
  rw [SMT.Nat.and_comm]
  exact hnat

/-- Move a mask across a logical right shift; shifted-out high bits are immaterial. -/
theorem bvand_bvlshr_eq_bvlshr_bvand_bvshl (x y z : BitVec n) :
    bvand y (bvlshr x z) = bvlshr (bvand x (bvshl y z)) z := by
  have hm : bvand (bvlshr x z) (bvlshr (bvnot (literal n 0)) z) = bvlshr x z := by
    rw [← Learned.BitVec.bvlshr_bvand]
    simp only [bvand, bvnot, literal, _root_.BitVec.not_zero, _root_.BitVec.and_allOnes]
  rw [Learned.BitVec.bvlshr_bvand, Learned.BitVec.bvlshr_bvshl_mask]
  have he : bvand (bvlshr x z) (bvand y (bvlshr (bvnot (literal n 0)) z)) =
      bvand (bvand (bvlshr x z) (bvlshr (bvnot (literal n 0)) z)) y := by
    rw [bvand_comm y (bvlshr (bvnot (literal n 0)) z), ← bvand_assoc]
  rw [he, hm, bvand_comm]

end Learned.BitVec
