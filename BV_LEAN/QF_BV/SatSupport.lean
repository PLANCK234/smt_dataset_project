/-
Released under Apache 2.0; see THIRD_PARTY_LICENSES/Apache-2.0.txt.
Local mathematical derivations for the SAT solution sets.

Notation used by the per-benchmark analyses in `sat/`:
P = 2^n, a = s.toNat, b = t.toNat (so a, b < P), L n a q = (a * 2^min(n,q)) mod P,
and R n a q = a / 2^min(n,q). Each benchmark proves `_iff` (the negated equality holds
iff a BitVec-free `_condition` holds) and `_solutions_iff` (every bounded natural solution
comes from a BitVec input), plus a kernel-checked width-32 witness `_sat32`.
-/
import LEMMAS_learned.BitVec.Shift.Characterization
import SMT.BitVec.ToNat
import SMT.Nat

namespace BV.QF_BV.Sat
open SMT.BitVec

/-- Counts are clamped, never reduced modulo the width. -/
def L (n a q : Nat) : Nat := (a * 2 ^ min n q) % 2 ^ n
def R (n a q : Nat) : Nat := a / 2 ^ min n q

theorem toNat_left (x y : BitVec n) : (bvshl x y).toNat = L n x.toNat y.toNat := by
  by_cases h : n ≤ y.toNat
  · rw [bvshl_large _ _ h]
    simp [L, Nat.min_eq_left h]
  · simp only [L, Nat.min_eq_right (by omega : y.toNat ≤ n), toNat_bvshl]

theorem toNat_right (x y : BitVec n) : (bvlshr x y).toNat = R n x.toNat y.toNat := by
  by_cases h : n ≤ y.toNat
  · rw [Learned.BitVec.bvlshr_large _ _ h]
    simp [R, Nat.min_eq_left h, Nat.div_eq_of_lt x.isLt]
  · simp only [R, Nat.min_eq_right (by omega : y.toNat ≤ n), toNat_bvlshr]

/-- Positive quotient: exactly the interval above the power-of-two threshold. -/
def RightNonzero (n a q : Nat) : Prop := q < n ∧ 2 ^ q ≤ a

instance : Decidable (RightNonzero n a q) := inferInstanceAs (Decidable (_ ∧ _))

theorem right_nonzero_iff (x y : BitVec n) :
    bvlshr x y ≠ literal n 0 ↔ RightNonzero n x.toNat y.toNat := by
  rw [ne_eq, eq_iff_toNat_eq, toNat_bvlshr, toNat_literal, Nat.zero_mod]
  have hp := Nat.two_pow_pos y.toNat
  have hx := x.isLt
  have hbound : 2 ^ y.toNat ≤ x.toNat → y.toNat < n := by
    intro h
    exact (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp (by omega)
  simp only [Nat.div_eq_zero_iff, Nat.ne_of_gt hp, false_or, Nat.not_lt]
  exact ⟨fun h => ⟨hbound h, h⟩, fun h => h.2⟩

/-- A left shift survives iff its product is not a multiple of the modulus. -/
def LeftNonzero (n a q : Nat) : Prop := q < n ∧ ¬ 2 ^ n ∣ a * 2 ^ q

instance : Decidable (LeftNonzero n a q) := inferInstanceAs (Decidable (_ ∧ _))

theorem left_nonzero_iff (x y : BitVec n) :
    bvshl x y ≠ literal n 0 ↔ LeftNonzero n x.toNat y.toNat := by
  constructor
  · intro h
    have hn : y.toNat < n := by
      by_cases hh : n ≤ y.toNat
      · exact False.elim (h (bvshl_large _ _ hh))
      · omega
    exact ⟨hn, fun hd => h ((Learned.BitVec.bvshl_eq_zero_iff_dvd x y).mpr hd)⟩
  · intro h he
    exact h.2 ((Learned.BitVec.bvshl_eq_zero_iff_dvd x y).mp he)

/-- A common right shift only sees differing bits at or above its count. -/
theorem common_right_different_iff (x y q : BitVec n) :
    bvlshr x q ≠ bvlshr y q ↔ RightNonzero n (x.toNat ^^^ y.toNat) q.toNat := by
  have he : bvxor (bvlshr x q) (bvlshr y q) = bvlshr (bvxor x y) q :=
    (_root_.BitVec.ushiftRight_xor_distrib x y q.toNat).symm
  have hh : bvlshr x q ≠ bvlshr y q ↔ bvxor (bvlshr x q) (bvlshr y q) ≠ literal n 0 :=
    not_congr _root_.BitVec.xor_eq_zero_iff.symm
  rw [he, right_nonzero_iff, toNat_bvxor] at hh
  exact hh

/-- Different left/right shifts, with all exceptional balanced patterns excluded. -/
def ShiftDifferent (n a q : Nat) : Prop :=
  0 < q ∧ q < n ∧ ¬ 2 ^ (n + q) ∣ (2 ^ (q + q) - 1) * a + a % 2 ^ q

instance : Decidable (ShiftDifferent n a q) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))

theorem shift_different_iff (x y : BitVec n) :
    bvshl x y ≠ bvlshr x y ↔ ShiftDifferent n x.toNat y.toNat := by
  have he := Learned.BitVec.bvshl_eq_bvlshr_iff_dvd x y
  constructor
  · intro h
    have hq : ¬ (y.toNat = 0 ∨ n ≤ y.toNat) := by
      intro hh
      exact h ((Learned.BitVec.bvshl_eq_bvlshr_forall_iff y).mpr hh x)
    exact ⟨by omega, by omega, fun hh => h (he.mpr hh)⟩
  · intro h hh
    exact h.2.2 (he.mp hh)

/-- Distinct right-shift counts distinguish a word exactly above the smaller threshold. -/
def RightDifferent (n a q r : Nat) : Prop :=
  q ≠ r ∧ min q r < n ∧ 2 ^ min q r ≤ a

instance : Decidable (RightDifferent n a q r) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))

private theorem div_pow_strict (a q r : Nat) (hqr : q < r) (ha : 2 ^ q ≤ a) :
    a / 2 ^ r < a / 2 ^ q := by
  have hd : 0 < a / 2 ^ q := (Nat.le_div_iff_mul_le (Nat.two_pow_pos q)).mpr (by simpa using ha)
  have he : 1 < 2 ^ (r - q) := Nat.one_lt_two_pow (by omega)
  rw [show r = q + (r - q) by omega, Nat.pow_add, ← Nat.div_div_eq_div_mul]
  exact Nat.div_lt_self hd he

theorem right_quotients_different_iff (haBound : a < 2 ^ n) (q r : Nat) :
    a / 2 ^ q ≠ a / 2 ^ r ↔ RightDifferent n a q r := by
  constructor
  · intro h
    have hne : q ≠ r := by intro he; exact h (by rw [he])
    have ha : 2 ^ min q r ≤ a := by
      by_cases hc : 2 ^ min q r ≤ a
      · exact hc
      apply False.elim
      have hy : a < 2 ^ q := Nat.lt_of_lt_of_le (by omega)
        (Nat.pow_le_pow_right (by decide) (Nat.min_le_left q r))
      have hz : a < 2 ^ r := Nat.lt_of_lt_of_le (by omega)
        (Nat.pow_le_pow_right (by decide) (Nat.min_le_right q r))
      exact h (by rw [Nat.div_eq_of_lt hy, Nat.div_eq_of_lt hz])
    have hn : min q r < n :=
      (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp (Nat.lt_of_le_of_lt ha haBound)
    exact ⟨hne, hn, ha⟩
  · intro ⟨hne, _, ha⟩ he
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · rw [Nat.min_eq_left (by omega)] at ha
      have := div_pow_strict a q r h ha
      omega
    · rw [Nat.min_eq_right (by omega)] at ha
      have := div_pow_strict a r q h ha
      omega

theorem right_different_iff (x y z : BitVec n) :
    bvlshr x y ≠ bvlshr x z ↔ RightDifferent n x.toNat y.toNat z.toNat := by
  rw [ne_eq, eq_iff_toNat_eq, toNat_bvlshr, toNat_bvlshr]
  exact right_quotients_different_iff x.isLt _ _

/-- Sequential right shifts add natural counts without bit-vector wraparound. -/
theorem nested_right_different_iff (x p q r : BitVec n) :
    bvlshr (bvlshr x p) q ≠ bvlshr x r ↔
      RightDifferent n x.toNat (p.toNat + q.toNat) r.toNat := by
  rw [ne_eq, eq_iff_toNat_eq, toNat_bvlshr, toNat_bvlshr, toNat_bvlshr,
    Nat.div_div_eq_div_mul, ← Nat.pow_add]
  exact right_quotients_different_iff x.isLt _ _

private theorem nat_add_eq_or_add_and (a b : Nat) :
    a + b = (a ||| b) + (a &&& b) := by
  induction a using SMT.Nat.div2Induction generalizing b with
  | ind a ih =>
    by_cases ha : a = 0
    · subst a; simp
    have hid := ih (by omega) (b / 2)
    have hor := SMT.Nat.or_div_two (a := a) (b := b)
    have hand := SMT.Nat.and_div_two (a := a) (b := b)
    have hom := SMT.Nat.or_mod_two_pow (n := 1) (a := a) (b := b)
    have ham := SMT.Nat.and_mod_two_pow (n := 1) (a := a) (b := b)
    have ha2 : a % 2 = 0 ∨ a % 2 = 1 := by omega
    have hb2 : b % 2 = 0 ∨ b % 2 = 1 := by omega
    rcases ha2 with ha2 | ha2 <;> rcases hb2 with hb2 | hb2 <;>
      simp only [Nat.pow_one, ha2, hb2, SMT.Nat.zero_and, SMT.Nat.and_zero,
        SMT.Nat.and_self, SMT.Nat.zero_or, SMT.Nat.or_zero, SMT.Nat.or_self] at hom ham <;> omega

private theorem left_shift_ne_self_iff (x : BitVec n) (d : Nat) :
    x <<< d ≠ x ↔ d ≠ 0 ∧ x ≠ literal n 0 := by
  have he : x <<< d = x ↔ d = 0 ∨ x = literal n 0 := by
    constructor
    · intro h
      by_cases hd : d = 0
      · exact Or.inl hd
      have hiter : ∀ k : Nat, x <<< (k * d) = x := by
        intro k
        induction k with
        | zero => simp
        | succ k ih => rw [Nat.succ_mul, _root_.BitVec.shiftLeft_add, ih, h]
      have hz : x <<< (n * d) = literal n 0 :=
        _root_.BitVec.shiftLeft_eq_zero (Nat.le_mul_of_pos_right n (by omega))
      exact Or.inr ((hiter n).symm.trans hz)
    · rintro (rfl | rfl) <;> simp [literal]
  simpa only [not_or] using not_congr he

/-- Sequential left shifts differ from the OR count iff the counts overlap and the OR shift survives. -/
def SequentialLeftDifferent (n a p q : Nat) : Prop :=
  p &&& q ≠ 0 ∧ LeftNonzero n a (p ||| q)

instance : Decidable (SequentialLeftDifferent n a p q) := inferInstanceAs (Decidable (_ ∧ _))

theorem sequential_left_different_iff (x p q : BitVec n) :
    bvshl (bvshl x p) q ≠ bvshl x (bvor p q) ↔
      SequentialLeftDifferent n x.toNat p.toNat q.toNat := by
  have he : bvshl (bvshl x p) q = (bvshl x (bvor p q)) <<< (p.toNat &&& q.toNat) := by
    simp only [bvshl_eq_shiftLeft, _root_.BitVec.shiftLeft_eq', toNat_bvor]
    rw [← _root_.BitVec.shiftLeft_add, nat_add_eq_or_add_and, _root_.BitVec.shiftLeft_add]
  rw [he, left_shift_ne_self_iff, left_nonzero_iff, toNat_bvor]
  rfl

/-- A modular product equals a bounded target iff this nonnegative difference is divisible. -/
def ResidueDifferent (n u v : Nat) : Prop := ¬ 2 ^ n ∣ u + 2 ^ n - v

instance : Decidable (ResidueDifferent n u v) := inferInstanceAs (Decidable (¬ _))

theorem residue_different_iff (hv : v < 2 ^ n) :
    u % 2 ^ n ≠ v ↔ ResidueDifferent n u v := by
  have he := Learned.Nat.mod_eq_iff_dvd_sub_of_le hv
    (show v ≤ u + 2 ^ n by omega)
  simpa only [ResidueDifferent, Nat.add_mod_right] using not_congr he

theorem mul_different_iff (x y z : BitVec n) :
    bvmul x y ≠ z ↔ ResidueDifferent n (x.toNat * y.toNat) z.toNat := by
  rw [ne_eq, eq_iff_toNat_eq, toNat_bvmul]
  exact residue_different_iff z.isLt

theorem neg_different_iff (x y : BitVec n) :
    bvneg x ≠ y ↔ ResidueDifferent n (2 ^ n - x.toNat) y.toNat := by
  rw [ne_eq, eq_iff_toNat_eq, toNat_bvneg]
  exact residue_different_iff y.isLt

theorem left_different_iff (x y z : BitVec n) :
    bvshl x y ≠ z ↔ ResidueDifferent n (x.toNat * 2 ^ min n y.toNat) z.toNat := by
  rw [ne_eq, eq_iff_toNat_eq, toNat_left]
  exact residue_different_iff z.isLt

/-- A nonzero mask is a common set bit; masks retain arbitrary bitwise structure. -/
theorem and_nonzero_iff (x y : BitVec n) :
    bvand x y ≠ literal n 0 ↔ x.toNat &&& y.toNat ≠ 0 := by
  rw [ne_eq, eq_iff_toNat_eq, toNat_bvand, toNat_literal, Nat.zero_mod]

theorem xor_nonzero_iff (x y : BitVec n) :
    x ≠ y ↔ x.toNat ^^^ y.toNat ≠ 0 := by
  have h : bvxor x y = literal n 0 ↔ x = y := _root_.BitVec.xor_eq_zero_iff
  have hn : bvxor x y = literal n 0 ↔ x.toNat ^^^ y.toNat = 0 := by
    rw [eq_iff_toNat_eq, toNat_bvxor, toNat_literal, Nat.zero_mod]
  exact not_congr (h.symm.trans hn)

theorem masked_different_iff (m x y : BitVec n) :
    bvand m x ≠ bvand m y ↔ m.toNat &&& (x.toNat ^^^ y.toNat) ≠ 0 := by
  have he : bvxor (bvand m x) (bvand m y) = bvand m (bvxor x y) := by
    apply _root_.BitVec.eq_of_getElem_eq
    intro i hi
    simp only [bvand, bvxor, _root_.BitVec.getElem_and, _root_.BitVec.getElem_xor]
    cases m[i] <;> cases x[i] <;> cases y[i] <;> decide
  have hh := xor_nonzero_iff (bvand m x) (bvand m y)
  change _ ↔ (bvxor (bvand m x) (bvand m y)).toNat ≠ 0 at hh
  simpa only [he, toNat_bvand, toNat_bvxor] using hh

theorem mask_loss_iff (m x : BitVec n) :
    bvand m x ≠ x ↔ (2 ^ n - 1 - m.toNat) &&& x.toNat ≠ 0 := by
  have he : bvxor (bvand m x) x = bvand (bvnot m) x := by
    apply _root_.BitVec.eq_of_getElem_eq
    intro i hi
    simp only [bvand, bvxor, bvnot, _root_.BitVec.getElem_and,
      _root_.BitVec.getElem_xor, _root_.BitVec.getElem_not]
    cases m[i] <;> cases x[i] <;> decide
  have hh := xor_nonzero_iff (bvand m x) x
  change _ ↔ (bvxor (bvand m x) x).toNat ≠ 0 at hh
  simpa only [he, toNat_bvand, toNat_bvnot] using hh

/-- A quotient misses v exactly outside v's half-open division interval. -/
def QuotientDifferent (n a q v : Nat) : Prop :=
  a < v * 2 ^ min n q ∨ (v + 1) * 2 ^ min n q ≤ a

instance : Decidable (QuotientDifferent n a q v) := inferInstanceAs (Decidable (_ ∨ _))

theorem quotient_different_iff (x y z : BitVec n) :
    bvlshr x y ≠ z ↔ QuotientDifferent n x.toNat y.toNat z.toNat := by
  rw [ne_eq, eq_iff_toNat_eq, toNat_right]
  unfold R QuotientDifferent
  rw [Nat.div_eq_iff (Nat.two_pow_pos _)]
  have := Nat.two_pow_pos (min n y.toNat)
  rw [Nat.add_mul, Nat.one_mul]
  omega

theorem or_gain_iff (m x : BitVec n) :
    bvor m x ≠ m ↔ (2 ^ n - 1 - m.toNat) &&& x.toNat ≠ 0 := by
  have he : bvxor (bvor m x) m = bvand (bvnot m) x := by
    apply _root_.BitVec.eq_of_getElem_eq
    intro i hi
    simp only [bvor, bvand, bvxor, bvnot, _root_.BitVec.getElem_or,
      _root_.BitVec.getElem_and, _root_.BitVec.getElem_xor, _root_.BitVec.getElem_not]
    cases m[i] <;> cases x[i] <;> decide
  have hh := xor_nonzero_iff (bvor m x) m
  change _ ↔ (bvxor (bvor m x) m).toNat ≠ 0 at hh
  simpa only [he, toNat_bvand, toNat_bvnot] using hh

/-- A masked value differs from a target through a supported mismatch or a missing target bit. -/
theorem mask_target_different_iff (m x y : BitVec n) :
    bvand m x ≠ y ↔
      (m.toNat &&& (x.toNat ^^^ y.toNat)) ||| ((2 ^ n - 1 - m.toNat) &&& y.toNat) ≠ 0 := by
  have he : bvxor (bvand m x) y =
      bvor (bvand m (bvxor x y)) (bvand (bvnot m) y) := by
    apply _root_.BitVec.eq_of_getElem_eq
    intro i hi
    simp only [bvor, bvand, bvxor, bvnot, _root_.BitVec.getElem_or,
      _root_.BitVec.getElem_and, _root_.BitVec.getElem_xor, _root_.BitVec.getElem_not]
    cases m[i] <;> cases x[i] <;> cases y[i] <;> decide
  have hh := xor_nonzero_iff (bvand m x) y
  change _ ↔ (bvxor (bvand m x) y).toNat ≠ 0 at hh
  simpa only [he, toNat_bvor, toNat_bvand, toNat_bvxor, toNat_bvnot] using hh

/-- All bounded natural assignments satisfying the independently stated arithmetic condition. -/
def SolutionSet (n : Nat) (C : Nat → Nat → Prop) (p : Nat × Nat) : Prop :=
  p.1 < 2 ^ n ∧ p.2 < 2 ^ n ∧ C p.1 p.2

/-- Executable enumeration for small widths; the symbolic SolutionSet works at all widths. -/
def solutionPairs (n : Nat) (C : Nat → Nat → Prop) [∀ a b, Decidable (C a b)] : List (Nat × Nat) :=
  ((List.range (2 ^ n)).flatMap fun a =>
    (List.range (2 ^ n)).map fun b => (a, b)).filter fun p => decide (C p.1 p.2)

theorem mem_solutionPairs_iff (n : Nat) (C : Nat → Nat → Prop) [∀ a b, Decidable (C a b)]
    (a b : Nat) : (a, b) ∈ solutionPairs n C ↔ SolutionSet n C (a, b) := by
  simp [solutionPairs, SolutionSet, and_assoc]

theorem solutionSet_toNat_iff (s t : BitVec n) (C : Nat → Nat → Prop) :
    SolutionSet n C (s.toNat, t.toNat) ↔ C s.toNat t.toNat :=
  ⟨fun h => h.2.2, fun h => ⟨s.isLt, t.isLt, h⟩⟩

theorem solutionSet_iff_exists (C : Nat → Nat → Prop) (P : BitVec n → BitVec n → Prop)
    (h : ∀ s t, P s t ↔ C s.toNat t.toNat) (a b : Nat) :
    SolutionSet n C (a, b) ↔ ∃ s t, s.toNat = a ∧ t.toNat = b ∧ P s t := by
  constructor
  · intro ⟨ha, hb, hc⟩
    have hs : (literal n a).toNat = a := toNat_literal_of_lt n a ha
    have ht : (literal n b).toNat = b := toNat_literal_of_lt n b hb
    exact ⟨literal n a, literal n b, hs, ht, (h _ _).mpr (by simpa only [hs, ht] using hc)⟩
  · rintro ⟨s, t, rfl, rfl, hp⟩
    exact ⟨s.isLt, t.isLt, (h s t).mp hp⟩

end BV.QF_BV.Sat
