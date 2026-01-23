import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Data.Fintype.Card
import Reap
open Filter

section StolzTheoremFinity

theorem StolzFinite (x : ℕ → ℝ) (y : ℕ → ℝ) {L : ℝ} (hyp_y_strictlymono : StrictMono y)
(hyp_y_attop : Tendsto y atTop atTop)
    (hyp_frac_convergence : Tendsto (fun n ↦ (x (n + 1) - x n) /
    (y (n + 1) - y n)) atTop (nhds L)) :
    Tendsto (fun n ↦ x n / y n) atTop (nhds L) := by
  -- Setup: auxiliary sequences and basic properties
  let f := fun n ↦ (x (n + 1) - x n) - L * (y (n + 1) - y n)
  let g := fun n ↦ y (n + 1) - y n
  have g_pos (n : ℕ) : 0 < g n := by
    simp only [g]
    exact sub_pos.mpr (hyp_y_strictlymono (Nat.lt_succ_self n))
  have g_nonneg : ∀ n : ℕ, 0 ≤ g n := by
    intro n
    apply le_of_lt
    apply sub_pos.mpr (hyp_y_strictlymono (Nat.lt_succ_self n))
  -- Telescoping sums
  have sum_f (n : ℕ) :
      (∑ i ∈ Finset.range n, f i) = x n - x 0 - L * (y n - y 0) := by
    calc
      ∑ i ∈ Finset.range n, f i
          = ∑ i ∈ Finset.range n, ((x (i + 1) - x i) - L * (y (i + 1) - y i)) := by rfl
      _ = (∑ i ∈ Finset.range n, (x (i + 1) - x i)) - L *
      (∑ i ∈ Finset.range n, (y (i + 1) - y i)) := by
        rw [Finset.sum_sub_distrib, Finset.mul_sum]
      _ = (x n - x 0) - L * (y n - y 0) := by
        rw [Finset.sum_range_sub, Finset.sum_range_sub]
  have sum_g (n : ℕ) :
      (∑ i ∈ Finset.range n, g i) = y n - y 0 := by
    unfold g
    simp only [Finset.sum_range_sub y]
  -- Limits
  have lim_a1 :
      -- Method 1
      Tendsto (fun n ↦ (y n - y 0) / y n) atTop (nhds 1) := by
    have h1 : ∀ n : ℕ, n ≥ 1 → y n > y 0 := by
      intro n hn
      induction n with
      | zero => linarith
      | succ n ih =>
        cases n with
        | zero =>
          have h3 : y 1 > y 0 := hyp_y_strictlymono (by norm_num)
          exact h3
        | succ n =>
          have h3 : y (n + 2) > y (n + 1) := hyp_y_strictlymono (by norm_num)
          have h4 : y (n + 1) > y 0 := ih (by linarith)
          linarith
    have h_pos : ∃ N, ∀ n ≥ N, y n > 0 := by
      have h1 : Tendsto y atTop atTop := hyp_y_attop
      rcases tendsto_atTop_atTop.mp h1 1 with ⟨N, hN⟩
      use N
      intro n hn
      have h2 : y n ≥ 1 := hN n hn
      linarith
    have h2 : ∃ N, ∀ n ≥ N, y n ≠ 0 := by
      rcases h_pos with ⟨N, hN⟩
      use N
      intro n hn
      have h_pos_n : y n > 0 := hN n hn
      linarith
    rcases h2 with ⟨N, hN⟩
    have h3 : ∀ n ≥ N, (y n - y 0) / y n = 1 - y 0 / y n := by
      intro n hn
      have : y n ≠ 0 := hN n hn
      field_simp [this]
    have h4 : ∀ᶠ n in atTop, (y n - y 0) / y n = 1 - y 0 / y n := by
      filter_upwards [eventually_ge_atTop N] with n hn using h3 n hn
    rw [tendsto_congr' h4]
    have h5 : Tendsto (fun n ↦ y 0 / y n) atTop (nhds 0) := by
      apply Tendsto.const_div_atTop
      exact hyp_y_attop
    have h6 : Tendsto (fun n ↦ 1 - y 0 / y n) atTop (nhds (1 - 0 : ℝ)) :=
      Tendsto.const_sub 1 h5
    simpa using h6
  have lim_a1 :
      -- Method 2
      Tendsto (fun n ↦ (y n - y 0) / y n) atTop (nhds 1) := by
    have eq : ∀ᶠ n in atTop, (y n - y 0) / y n = 1 - y 0 / y n := by
      have hy_pos : ∀ᶠ n in atTop, y n ≠ 0 := by
        rw [tendsto_atTop_atTop] at hyp_y_attop
        rcases hyp_y_attop (max (y 0 + 1) 1) with ⟨N, hN⟩
        filter_upwards [Ici_mem_atTop N] with n hn
        have : y n ≥ max (y 0 + 1) 1 := hN n hn
        linarith [le_max_right (y 0 + 1) 1]
      filter_upwards [hy_pos] with n hn
      field_simp [hn]
    have h : Tendsto (fun n ↦ y 0 / y n) atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop hyp_y_attop
    rw [tendsto_congr' eq]
    simpa using Tendsto.const_sub 1 h
  have lim_a2' :
      Tendsto (fun n ↦ (x n - x 0 - L * (y n - y 0)) / (y n - y 0)) atTop (nhds 0) := by
    have h1 : ∀ n, x n - x 0 - L * (y n - y 0) = ∑ i ∈ Finset.range n, f i := by
      intro n
      rw [sum_f]
    have h2 : ∀ n, y n - y 0 = ∑ i ∈ Finset.range n, g i := by
      intro n
      rw [sum_g]
    have h3 :
        ∀ᶠ n in atTop,
          (x n - x 0 - L * (y n - y 0)) / (y n - y 0)
            = (∑ i ∈ Finset.range n, f i) / (∑ i ∈ Finset.range n, g i) := by
      filter_upwards [eventually_ge_atTop 0] with n hn
      rw [h1 n, h2 n]
    rw [tendsto_congr' h3]
    have h4 : ∀ n, f n / g n =
        (x (n + 1) - x n) / (y (n + 1) - y n) - L := by
      intro n
      have hg : g n ≠ 0 := ne_of_gt (g_pos n)
      simp only [f, g]
      field_simp [hg]
      have: (y (n + 1) - y n) ≠ 0 := ne_of_gt (g_pos n)
      field_simp [this]
    have h5 : Tendsto (fun n ↦ f n / g n) atTop (nhds 0) := by
      have h6 :
          Tendsto (fun n ↦ (x (n + 1) - x n) / (y (n + 1) - y n) - L)
            atTop (nhds (L - L)) := by
        have h7 : Tendsto (fun n ↦ (x (n + 1) - x n) / (y (n + 1) - y n))
          atTop (nhds L) := hyp_frac_convergence
        exact Tendsto.sub_const h7 L
      simpa [h4] using h6
    have h8 : (fun n ↦ f n) =o[atTop] (fun n ↦ g n) := by
      have hg_ne_zero : ∀ n, g n ≠ 0 := by
        intro n
        exact ne_of_gt (g_pos n)
      apply (Asymptotics.isLittleO_iff_tendsto (fun n h => absurd h (hg_ne_zero n))).mpr
      exact h5
    have h9 :
        Tendsto (fun n ↦ (∑ i ∈ Finset.range n, f i) /
         (∑ i ∈ Finset.range n, g i)) atTop (nhds 0) := by
      have h10 :
          (fun n ↦ (∑ i ∈ Finset.range n, f i)) =o[atTop]
           (fun n ↦ (∑ i ∈ Finset.range n, g i)) := by
        have h11 :
            Tendsto (fun n ↦ (∑ i ∈ Finset.range n, g i)) atTop atTop := by
          have : (fun n ↦ (∑ i ∈ Finset.range n, g i)) = (fun n ↦ y n - y 0) := by
            ext n
            exact sum_g n
          rw [this]
          apply Filter.tendsto_atTop_add_const_right atTop (- y 0) hyp_y_attop
        exact Asymptotics.IsLittleO.sum_range h8 g_nonneg h11
      apply Asymptotics.IsLittleO.tendsto_div_nhds_zero h10
    exact h9
  have lim_a2 :
      Tendsto (fun n ↦ (x n - x 0 - L * (y n - y 0)) / y n) atTop (nhds 0) := by
    have hy_pos : ∀ᶠ n in atTop, y n ≠ 0 := by
      rw [tendsto_atTop_atTop] at hyp_y_attop
      rcases hyp_y_attop (max (y 0 + 1) 1) with ⟨N, hN⟩
      filter_upwards [Ici_mem_atTop N] with n hn
      have : y n ≥ max (y 0 + 1) 1 := hN n hn
      linarith [le_max_right (y 0 + 1) 1]
    have hy_diff_pos : ∀ᶠ n in atTop, y n - y 0 ≠ 0 := by
      filter_upwards [hy_pos, eventually_gt_atTop 0] with n hn1 hn2
      have : y n > y 0 := hyp_y_strictlymono hn2
      exact ne_of_gt (sub_pos.mpr this)
    have eq_split : ∀ n, y n ≠ 0 → y n - y 0 ≠ 0 →
        (x n - x 0 - L * (y n - y 0)) / y n =
        ((x n - x 0 - L * (y n - y 0)) / (y n - y 0)) * ((y n - y 0) / y n) := by
      intro n hn hndiff
      field_simp [hn, hndiff]
    have eq_lim : ∀ᶠ n in atTop,
        (x n - x 0 - L * (y n - y 0)) / y n =
        ((x n - x 0 - L * (y n - y 0)) / (y n - y 0)) * ((y n - y 0) / y n) := by
      filter_upwards [hy_pos, hy_diff_pos] with n hn1 hn2
      exact eq_split n hn1 hn2
    rw [tendsto_congr' eq_lim]
    have h_mul := Filter.Tendsto.mul lim_a2' lim_a1
    convert h_mul using 1
    norm_num
  have lim_b :
      Tendsto (fun n ↦ (x 0 - L * (y 0)) / y n) atTop (nhds 0) := by
    exact tendsto_const_nhds.div_atTop hyp_y_attop
  -- Final step
  have total_lim :
      Tendsto (fun n ↦ x n / y n - L) atTop (nhds 0) := by
    have h_pos : ∃ N, ∀ n ≥ N, y n > 0 := by
      rcases tendsto_atTop_atTop.mp hyp_y_attop 1 with ⟨N, hN⟩
      use N
      intro n hn
      have : y n ≥ 1 := hN n hn
      linarith
    have h_neq : ∃ N, ∀ n ≥ N, y n ≠ 0 := by
      rcases h_pos with ⟨N, hN⟩
      use N
      intro n hn
      exact ne_of_gt (hN n hn)
    rcases h_neq with ⟨N, hN⟩
    have eq_1 : ∀ n ≥ N, x n / y n - L =
        (x n - x 0 - L * (y n - y 0)) / y n + (x 0 - L * y 0) / y n := by
      intro n hn
      have : y n ≠ 0 := hN n hn
      field_simp [this]
      ring
    have eq_lim : ∀ᶠ n in atTop, x n / y n - L =
        (x n - x 0 - L * (y n - y 0)) / y n + (x 0 - L * y 0) / y n := by
      apply eventually_of_mem (Ici_mem_atTop N)
      exact eq_1
    rw [tendsto_congr' eq_lim]
    have h_combined :
        Tendsto (fun n ↦ (x n - x 0 - L * (y n - y 0)) / y n + (x 0 - L * y 0) / y n)
        atTop (nhds (0 + 0)) :=
      Tendsto.add lim_a2 lim_b
    simp only [add_zero] at h_combined
    exact h_combined
  have := Tendsto.add_const L total_lim
  simp only [sub_add_cancel, zero_add] at this
  exact this

end StolzTheoremFinity

section StolzTheoremInfinity

theorem StolzPosInfinity (x : ℕ → ℝ) (y : ℕ → ℝ) (hyp_y_strictlymono : StrictMono y)
    (hyp_y_attop : Tendsto y atTop atTop)
    (hyp_frac_divergence : Tendsto (fun n ↦ (x (n + 1) - x n) / (y (n + 1) - y n)) atTop
    (atTop : Filter ℝ)) :
    Tendsto (fun n ↦ x n / y n) atTop atTop := by
    -- Step 1: Show that Δx > 0 eventually
    have h_x_eventually_mono : ∃ N, ∀ n ≥ N, x (n + 1) - x n > 0 := by
        rcases (tendsto_atTop_atTop.mp hyp_frac_divergence 1) with ⟨N, hN⟩
        use N; intro n hn
        have h_ratio : 1 ≤ (x (n + 1) - x n) / (y (n + 1) - y n) := hN n hn
        have y_incr : y (n + 1) - y n > 0 :=
            sub_pos.mpr (hyp_y_strictlymono (Nat.lt_succ_self n))
        have : x (n + 1) - x n ≥ y (n + 1) - y n := by
            calc
                y (n + 1) - y n
                    = 1 * (y (n + 1) - y n) := by ring
                _ ≤ (x (n + 1) - x n) / (y (n + 1) - y n) * (y (n + 1) - y n) :=
                    mul_le_mul_of_nonneg_right h_ratio (le_of_lt y_incr)
                _ = x (n + 1) - x n := by field_simp [ne_of_gt y_incr]
        exact lt_of_le_of_lt' this y_incr
    rcases h_x_eventually_mono with ⟨N₀, hN₀⟩
    -- Step 2: Define auxiliary sequence z
    let z : ℕ → ℝ := fun n ↦ if n ≤ N₀ then x N₀ + (n - N₀) else x n
    have heq_z_x : ∀ᶠ n in atTop, z n = x n := by
        filter_upwards [eventually_ge_atTop (N₀ + 1)] with n hn
        simp only [ite_eq_right_iff, z]
        have : ¬ (n ≤ N₀) := by omega
        simp only [this, IsEmpty.forall_iff]
    have h_y_pos : ∀ᶠ n in atTop, y n > 0 := by
        rw [tendsto_atTop_atTop] at hyp_y_attop
        rcases hyp_y_attop 1 with ⟨N, hN⟩
        filter_upwards [eventually_ge_atTop N] with n hn
        linarith [hN n hn]
    have heq_div : ∀ᶠ n in atTop, z n / y n = x n / y n := by
        filter_upwards [heq_z_x, h_y_pos] with n h_eq h_pos
        rw [h_eq]
    -- Step 3: Show z is strictly monotone
    have h_z_strict_mono : StrictMono z := by
        have h_succ : ∀ i, z i < z (i + 1) := by
            intro i
            by_cases h₁ : i < N₀
            · simp only [h₁.le, ↓reduceIte, Nat.cast_add, Nat.cast_one, z]
              split_ifs with h
              · simp only [add_lt_add_iff_left]
                norm_num
              linarith
            by_cases h₂ : i = N₀
            · simp only [h₂.le, ↓reduceIte, Nat.cast_add, Nat.cast_one, z]
              rw [h₂]
              specialize hN₀ N₀ (le_refl N₀)
              split_ifs
              · simp only [sub_self, add_zero, add_sub_cancel_left, lt_add_iff_pos_right,
                zero_lt_one]
              simp only [sub_self, add_zero]
              linarith
            have h₃ : i > N₀ := lt_of_le_of_ne (not_lt.mp h₁) (Ne.symm h₂)
            have zi_eq : z i = x i := by simp only [not_le.mpr h₃, ↓reduceIte, z]
            have zip1_eq : z (i + 1) = x (i + 1) := by exact if_neg h₁
            rw [zi_eq, zip1_eq]; exact lt_of_sub_pos (hN₀ i (le_of_lt h₃))
        exact strictMono_nat_of_lt_succ h_succ
    -- Step 4: Show x → +∞
    have h_x_at_top : Tendsto x atTop atTop := by
        have M : ℝ := 1
        have ⟨K, hK⟩ : ∃ K : ℝ, 0 < K := ⟨1, by norm_num⟩
        have h_frac_gt : ∃ N₁, ∀ n ≥ N₁, (x (n+1) - x n) / (y (n+1) - y n) > K := by
            obtain ⟨N, hN⟩ := tendsto_atTop_atTop.mp hyp_frac_divergence (K + 1)
            use N; intro n hn; specialize hN n hn
            exact lt_of_lt_of_le (lt_add_one K) hN
        obtain ⟨N₁, hN₁⟩ := h_frac_gt
        have h_diff : ∀ n ≥ N₁, x (n+1) - x n > K * (y (n+1) - y n) := by
            intros n hn; specialize hN₁ n hn
            have h_denom_pos : 0 < y (n+1) - y n :=
                sub_pos_of_lt (hyp_y_strictlymono (Nat.lt_succ_self n))
            exact (lt_div_iff₀ h_denom_pos).mp hN₁
        have h_diff' : ∀ n ≥ N₁, x (n+1) - x n ≥ K * (y (n+1) - y n) :=
            fun n a => le_of_lt (h_diff n a)
        have h_sum_diff : ∀ n ≥ N₁, x n ≥ x N₁ + K * (y n - y N₁) := by
            have h_sum_diff1 : ∀ n ≥ N₁, x n - x N₁ ≥ K * (y n - y N₁) := by
              have H : ∀ k, x (N₁ + k) - x N₁ ≥ K * (y (N₁ + k) - y N₁) := by
                intro k
                induction k
                · simp only [add_zero, sub_self, mul_zero, ge_iff_le, le_refl]
                rw [← add_assoc]
                rename_i n a
                have h₁ : N₁ + n ≥ N₁ := by linarith
                have h₂ : x (N₁ + n + 1) - x (N₁ + n) ≥ K * (y (N₁ + n + 1) - y (N₁ + n)) :=
                by exact h_diff' (N₁ + n) h₁
                calc x (N₁ + n + 1) - x N₁
                    = x (N₁ + n + 1) - x (N₁ + n) + (x (N₁ + n) - x N₁) := by ring
                    _ ≥ K * (y (N₁ + n + 1) - y (N₁ + n)) + K * (y (N₁ + n) - y N₁) := by linarith
                    _ = K * (y (N₁ + n + 1) - y N₁) := by ring
              intro n hn; rcases Nat.exists_eq_add_of_le hn with ⟨k, rfl⟩
              simpa using H k
            intro n hn; have h_diff1 := h_sum_diff1 n hn; linarith
        have h_final : ∀ M, ∃ N, ∀ n ≥ N, x n > M := by
            intro M
            have h_y : ∀ L : ℝ, ∃ N, ∀ n ≥ N, y n ≥ L :=
                by rwa [tendsto_atTop_atTop] at hyp_y_attop
            obtain ⟨N₂, hN₂⟩ := h_y (((M + 1) - x N₁) / K + y N₁)
            use max N₁ N₂; intro n hn
            have h₁ : n ≥ N₁ := le_of_max_le_left hn
            have h₂ : n ≥ N₂ := le_of_max_le_right hn
            have h₃ := h_sum_diff n h₁; have h₄ := hN₂ n h₂
            have h_sub : y n - y N₁ ≥ ((M + 1) - x N₁) / K := by linarith
            have k_pos: K ≠ 0 := by exact Ne.symm (ne_of_lt hK)
            have k_replay: K * (((M + 1) - x N₁) / K) = (M + 1) - x N₁ := by
                exact mul_div_cancel₀ (M + 1 - x N₁) k_pos
            calc x n ≥ x N₁ + K * (y n - y N₁) := h₃
                _ ≥ x N₁ + K * (((M + 1) - x N₁) / K) := by gcongr
                _ = x N₁ + ((M + 1) - x N₁)  := by rw [k_replay]
                _ > M := by linarith
        apply tendsto_atTop_atTop.mpr; intro b
        obtain ⟨i, hi⟩ := h_final b; use i
        intro a ha; exact (hi a ha).le
    -- Step 5: Show z → +∞
    have h_z_at_top : Tendsto z atTop atTop := by
        apply tendsto_atTop_atTop_of_monotone
        · intro n m hnm
          exact (StrictMono.le_iff_le h_z_strict_mono).mpr hnm
        intro b
        obtain ⟨a, ha⟩ := tendsto_atTop_atTop.mp h_x_at_top b
        let a' := max a N₀; use a'
        have ha'_ge : a' ≥ a := le_max_left _ _
        have ha'_ge_N0 : a' ≥ N₀ := le_max_right _ _
        have hxa' : b ≤ x a' := ha a' ha'_ge
        have hza : z a' = x a' := by
            by_cases h : a' = N₀
            · rw [h]
              simp only [le_refl, ↓reduceIte, sub_self, add_zero, z]
            have h' : a' > N₀ := Nat.lt_of_le_of_ne ha'_ge_N0 (Ne.symm h)
            simp only [not_le.mpr h', ↓reduceIte, z]
        rw [hza]; exact hxa'
    -- Step 6: Show reciprocal of Δx/Δy → 0
    have h_x_inv_tendsto_zero :
        Tendsto (fun n ↦ (y (n + 1) - y n) / (x (n + 1) - x n)) atTop (nhds 0) := by
        apply Tendsto.congr' _ (Filter.Tendsto.inv_tendsto_atTop hyp_frac_divergence)
        filter_upwards [eventually_ge_atTop N₀] with n hn
        simp only [Pi.inv_apply, inv_div]
    -- Step 7: Show reciprocal for z
    have h_z_inv_tendsto_zero :
        Tendsto (fun n ↦ (y (n + 1) - y n) / (z (n + 1) - z n)) atTop (nhds 0) := by
        apply Tendsto.congr' _ h_x_inv_tendsto_zero
        filter_upwards [eventually_gt_atTop N₀] with n hn
        simp only [not_le.mpr (Nat.lt_succ_of_lt hn), ↓reduceIte, not_le.mpr hn, z]
    -- Step 8: Apply StolzFinite to get y/z → 0
    have h_lim' : Tendsto (fun n ↦ y n / z n) atTop (nhds 0) :=
        StolzFinite y z h_z_strict_mono h_z_at_top h_z_inv_tendsto_zero
    have h_z_pos : ∀ᶠ n in atTop, z n > 0 := by
        rcases tendsto_atTop_atTop.mp h_z_at_top 1 with ⟨N, hN⟩
        filter_upwards [eventually_ge_atTop N] with n hn
        exact lt_of_lt_of_le zero_lt_one (hN n hn)
    have h_lim'_pos : Tendsto (fun n ↦ y n / z n) atTop (nhdsWithin 0 (Set.Ioi 0)) :=
        tendsto_nhdsWithin_iff.mpr ⟨h_lim', by
            filter_upwards [h_y_pos, h_z_pos] with n hy hz
            exact div_pos hy hz⟩
    -- Step 9: Take reciprocal to get z/y → +∞
    have h_lim : Tendsto (fun n ↦ z n / y n) atTop atTop := by
        obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp h_y_pos
        obtain ⟨N₂, hN₂⟩ := eventually_atTop.mp h_z_pos
        let N := max N₁ N₂
        have : (fun n ↦ z n / y n) = (fun n ↦ (y n / z n)⁻¹) := by
          ext n;field_simp [h_z_pos, h_y_pos]
        rw [this]; exact Filter.Tendsto.inv_tendsto_nhdsGT_zero h_lim'_pos
    rwa [← (tendsto_congr' heq_div)]

theorem StolzNegInfinity (x : ℕ → ℝ) (y : ℕ → ℝ) (hyp_y_strictlymono : StrictMono y)
(hyp_y_attop : Tendsto y atTop atTop)
    (hyp_frac_divergence : Tendsto (fun n ↦ (x (n + 1) - x n) /
    (y (n + 1) - y n)) atTop (atBot : Filter ℝ)) :
    Tendsto (fun n ↦ x n / y n) atTop (atBot : Filter ℝ) := by
  let z := fun n ↦ - x n
  have h1 :
    ∀ n : ℕ, (x (n + 1) - x n) / (y (n + 1) - y n) = - ((z (n + 1) - z n) / (y (n + 1) - y n)) := by
      intro n;
      simp only [sub_neg_eq_add, z]; ring
  have func_eq : (fun n ↦ (x (n + 1) - x n) / (y (n + 1) - y n)) =
    (fun n ↦ - ((z (n + 1) - z n) / (y (n + 1) - y n))) := by ext n; exact h1 n
  have h2 : Tendsto (fun n ↦ (z (n + 1) - z n) / (y (n + 1) - y n)) atTop atTop := by
    rw [func_eq] at hyp_frac_divergence
    apply Filter.tendsto_neg_atBot_iff.1
    exact hyp_frac_divergence
  have h3 : Tendsto (fun n ↦ z n / y n) atTop atTop
    := StolzPosInfinity z y hyp_y_strictlymono hyp_y_attop h2
  have : (fun n ↦ x n / y n) = (fun n ↦ - (z n / y n)) := by
    ext n;simp only [neg_div, neg_neg, z]
  rw [this]
  apply Filter.tendsto_neg_atBot_iff.2
  exact h3

end StolzTheoremInfinity

open Finset

example (m n : ℕ) (h : m ≥ n) :
    card (range n ∪ (range n).image (fun i ↦ m + i)) = 2 * n := by
  classical
  have hdisj : Disjoint (range n) ((range n).image (fun i ↦ m + i)) := by
    -- use `Finset.disjoint_left`
    rw [Finset.disjoint_left]
    intro a ha haimg
    -- unpack membership in the image using `Finset.mem_image`
    rcases (Finset.mem_image.mp haimg) with ⟨i, hi, hmi⟩
    have ha' : a < n := Finset.mem_range.mp ha
    have hn : n ≤ m := h
    have hni : n ≤ m + i := le_trans hn (Nat.le_add_right m i)
    -- from hmi : m + i = a, rewrite to get n ≤ a, contradiction with a < n
    have : n ≤ a := by simpa [hmi] using hni
    exact (not_lt_of_ge this) ha'
  have hcard :
      card (range n ∪ (range n).image (fun i ↦ m + i))
        = card (range n) + card ((range n).image (fun i ↦ m + i)) := by
    exact (Finset.card_union_eq_card_add_card).2 hdisj
  -- compute card of the image
  have hinj : Function.Injective (fun i : ℕ ↦ m + i) := by
    intro a b hab
    exact Nat.add_left_cancel hab
  have himage : card ((range n).image (fun i ↦ m + i)) = card (range n) := by
    simpa using (Finset.card_image_of_injective (s := range n) hinj)
  -- finish
  calc
    card (range n ∪ (range n).image (fun i ↦ m + i))
        = card (range n) + card ((range n).image (fun i ↦ m + i)) := hcard
    _ = n + n := by simp [Finset.card_range, himage]
    _ = 2 * n := by ring
