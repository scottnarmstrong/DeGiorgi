import DeGiorgi.MoserIteration.CutoffPrep.Basics

/-!
# Moser Regularized Profiles

This module contains the smooth and exact-on-support scalar profile functions used in the Chapter 06 regularization arguments.
-/

noncomputable section

open MeasureTheory Filter

namespace DeGiorgi

variable {d : ℕ} [NeZero d]

local notation "E" => AmbientSpace d

/-- Smooth scalar clipping profile for the regularized Moser power argument.

It equals `0` on `(-∞, 0]`, equals the identity on `[ε, N]`, and equals `N`
on `[N + 1, ∞)`. The transition zones are controlled by
`Real.smoothTransition`. -/
noncomputable def moserSmoothClip (ε N : ℝ) : ℝ → ℝ :=
  fun t =>
    let σ₀ : ℝ := Real.smoothTransition (t / ε)
    let σ₁ : ℝ := Real.smoothTransition (N + 1 - t)
    t * σ₀ * σ₁ + N * (1 - σ₁)

theorem moserSmoothClip_contDiff {ε N : ℝ} (_hε : 0 < ε) :
    ContDiff ℝ (⊤ : ℕ∞) (moserSmoothClip ε N) := by
  have hσ₀ :
      ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ => Real.smoothTransition (t / ε)) := by
    have hlin : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ => t / ε) := by
      simpa [div_eq_mul_inv, mul_comm] using
        ((contDiff_const : ContDiff ℝ (⊤ : ℕ∞) fun _ : ℝ => ε⁻¹).mul contDiff_id)
    simpa using Real.smoothTransition.contDiff.comp hlin
  have hσ₁ :
      ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ => Real.smoothTransition (N + 1 - t)) := by
    have hlin : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ => N + 1 - t) := by
      simpa using
        ((contDiff_const : ContDiff ℝ (⊤ : ℕ∞) fun _ : ℝ => N + 1).sub contDiff_id)
    simpa using Real.smoothTransition.contDiff.comp hlin
  simpa [moserSmoothClip]
    using (((contDiff_id.mul hσ₀).mul hσ₁).add
    (contDiff_const.mul (contDiff_const.sub hσ₁))
      : ContDiff ℝ (⊤ : ℕ∞)
          (fun t : ℝ =>
            t * Real.smoothTransition (t / ε) * Real.smoothTransition (N + 1 - t) +
              N * (1 - Real.smoothTransition (N + 1 - t))))

theorem moserSmoothClip_eq_zero_of_nonpos
    {ε N t : ℝ} (hε : 0 < ε) (hN : 0 ≤ N) (ht : t ≤ 0) :
    moserSmoothClip ε N t = 0 := by
  have hσ₀ : Real.smoothTransition (t / ε) = 0 := by
    apply Real.smoothTransition.zero_of_nonpos
    rw [div_eq_mul_inv]
    exact mul_nonpos_of_nonpos_of_nonneg ht (inv_nonneg.mpr hε.le)
  have hσ₁ : Real.smoothTransition (N + 1 - t) = 1 := by
    apply Real.smoothTransition.one_of_one_le
    linarith
  simp [moserSmoothClip, hσ₀, hσ₁]

theorem moserSmoothClip_eq_self_on_midrange
    {ε N t : ℝ} (hε : 0 < ε) (hεt : ε ≤ t) (htN : t ≤ N) :
    moserSmoothClip ε N t = t := by
  have hσ₀ : Real.smoothTransition (t / ε) = 1 := by
    apply Real.smoothTransition.one_of_one_le
    rw [le_div_iff₀ hε]
    linarith
  have hσ₁ : Real.smoothTransition (N + 1 - t) = 1 := by
    apply Real.smoothTransition.one_of_one_le
    linarith
  simp [moserSmoothClip, hσ₀, hσ₁]

theorem moserSmoothClip_eq_top_of_top_le
    {ε N t : ℝ} (ht : N + 1 ≤ t) :
    moserSmoothClip ε N t = N := by
  have hσ₁ : Real.smoothTransition (N + 1 - t) = 0 := by
    apply Real.smoothTransition.zero_of_nonpos
    linarith
  simp [moserSmoothClip, hσ₁]

theorem moserSmoothClip_deriv_bounded
    {ε N : ℝ} (hε : 0 < ε) (hN : 0 ≤ N) :
    ∃ M, ∀ t, |deriv (moserSmoothClip ε N) t| ≤ M := by
  have h1 : ContDiff ℝ 1 (moserSmoothClip ε N) :=
    (moserSmoothClip_contDiff (ε := ε) (N := N) hε).of_le (by simp)
  have hcont : Continuous (deriv (moserSmoothClip ε N)) := h1.continuous_deriv_one
  obtain ⟨M, -, hM_max⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := N + 1)).exists_isMaxOn
    (Set.nonempty_Icc.2 (by linarith : (0 : ℝ) ≤ N + 1)) hcont.norm.continuousOn
  have hbound : ∀ t : ℝ, ‖deriv (moserSmoothClip ε N) t‖ ≤ ‖deriv (moserSmoothClip ε N) M‖ := by
    intro t
    by_cases ht0 : t < 0
    · have hloc : moserSmoothClip ε N =ᶠ[nhds t] fun _ => (0 : ℝ) := by
        filter_upwards [Iio_mem_nhds ht0] with y hy
        exact moserSmoothClip_eq_zero_of_nonpos (ε := ε) (N := N) hε hN hy.le
      rw [hloc.deriv_eq, deriv_const, norm_zero]
      exact norm_nonneg _
    · by_cases ht1 : N + 1 < t
      · have hloc : moserSmoothClip ε N =ᶠ[nhds t] fun _ => N := by
          filter_upwards [Ioi_mem_nhds ht1] with y hy
          exact moserSmoothClip_eq_top_of_top_le (ε := ε) (N := N) hy.le
        rw [hloc.deriv_eq, deriv_const, norm_zero]
        exact norm_nonneg _
      · push_neg at ht0 ht1
        exact Filter.eventually_principal.mp hM_max t (Set.mem_Icc.2 ⟨ht0, ht1⟩)
  refine ⟨‖deriv (moserSmoothClip ε N) M‖, ?_⟩
  intro t
  exact (Real.norm_eq_abs _).ge.trans (hbound t)

/-- Regularized power profile used to approximate `t ↦ t^(p/2)` on the positive
half-line while keeping a smooth globally bounded derivative. -/
noncomputable def moserRegPow (ε N p : ℝ) : ℝ → ℝ :=
  fun t => (ε + moserSmoothClip ε N t) ^ (p / 2) - ε ^ (p / 2)

theorem moserRegPow_contDiff {ε N p : ℝ} (hε : 0 < ε) (hN : 0 ≤ N) :
    ContDiff ℝ (⊤ : ℕ∞) (moserRegPow ε N p) := by
  have hbase : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ => ε + moserSmoothClip ε N t) := by
    exact contDiff_const.add (moserSmoothClip_contDiff (ε := ε) (N := N) hε)
  have hbase_ne : ∀ t : ℝ, ε + moserSmoothClip ε N t ≠ 0 := by
    intro t
    have hclip_nonneg : 0 ≤ moserSmoothClip ε N t := by
      by_cases ht0 : t ≤ 0
      · rw [moserSmoothClip_eq_zero_of_nonpos (ε := ε) (N := N) hε hN ht0]
      · have ht0' : 0 < t := lt_of_not_ge ht0
        by_cases ht1 : N + 1 ≤ t
        · rw [moserSmoothClip_eq_top_of_top_le (ε := ε) (N := N) ht1]
          exact hN
        · have hσ₀_nonneg : 0 ≤ Real.smoothTransition (t / ε) := Real.smoothTransition.nonneg _
          have hσ₁_nonneg : 0 ≤ Real.smoothTransition (N + 1 - t) := Real.smoothTransition.nonneg _
          have hσ₁_le : Real.smoothTransition (N + 1 - t) ≤ 1 := Real.smoothTransition.le_one _
          have hterm1_nonneg :
              0 ≤ t * Real.smoothTransition (t / ε) * Real.smoothTransition (N + 1 - t) := by
            positivity
          have hterm2_nonneg :
              0 ≤ N * (1 - Real.smoothTransition (N + 1 - t)) := by
            have : 0 ≤ 1 - Real.smoothTransition (N + 1 - t) := by linarith
            exact mul_nonneg hN this
          dsimp [moserSmoothClip]
          positivity
    linarith
  simpa [moserRegPow] using (hbase.rpow_const_of_ne hbase_ne).sub contDiff_const

theorem moserRegPow_eq_zero_of_nonpos
    {ε N p t : ℝ} (hε : 0 < ε) (hN : 0 ≤ N) (ht : t ≤ 0) :
    moserRegPow ε N p t = 0 := by
  rw [moserRegPow, moserSmoothClip_eq_zero_of_nonpos (ε := ε) (N := N) hε hN ht]
  ring_nf

theorem moserRegPow_eq_shifted_on_midrange
    {ε N p t : ℝ} (hε : 0 < ε) (hεt : ε ≤ t) (htN : t ≤ N) :
    moserRegPow ε N p t = (ε + t) ^ (p / 2) - ε ^ (p / 2) := by
  rw [moserRegPow, moserSmoothClip_eq_self_on_midrange (ε := ε) (N := N) hε hεt htN]

theorem moserRegPow_deriv_bounded
    {ε N p : ℝ} (hε : 0 < ε) (hN : 0 ≤ N) :
    ∃ M, ∀ t, |deriv (moserRegPow ε N p) t| ≤ M := by
  have h1 : ContDiff ℝ 1 (moserRegPow ε N p) :=
    (moserRegPow_contDiff (ε := ε) (N := N) (p := p) hε hN).of_le (by simp)
  have hcont : Continuous (deriv (moserRegPow ε N p)) := h1.continuous_deriv_one
  obtain ⟨M, -, hM_max⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := N + 1)).exists_isMaxOn
    (Set.nonempty_Icc.2 (by linarith : (0 : ℝ) ≤ N + 1)) hcont.norm.continuousOn
  have hbound : ∀ t : ℝ, ‖deriv (moserRegPow ε N p) t‖ ≤ ‖deriv (moserRegPow ε N p) M‖ := by
    intro t
    by_cases ht0 : t < 0
    · have hloc : moserRegPow ε N p =ᶠ[nhds t] fun _ => (0 : ℝ) := by
        filter_upwards [Iio_mem_nhds ht0] with y hy
        exact moserRegPow_eq_zero_of_nonpos (ε := ε) (N := N) (p := p) hε hN hy.le
      rw [hloc.deriv_eq, deriv_const, norm_zero]
      exact norm_nonneg _
    · by_cases ht1 : N + 1 < t
      · have hconst :
            moserRegPow ε N p =ᶠ[nhds t]
              fun _ => (ε + N) ^ (p / 2) - ε ^ (p / 2) := by
          filter_upwards [Ioi_mem_nhds ht1] with y hy
          rw [moserRegPow, moserSmoothClip_eq_top_of_top_le (ε := ε) (N := N) hy.le]
        rw [hconst.deriv_eq, deriv_const, norm_zero]
        exact norm_nonneg _
      · push_neg at ht0 ht1
        exact Filter.eventually_principal.mp hM_max t (Set.mem_Icc.2 ⟨ht0, ht1⟩)
  refine ⟨‖deriv (moserRegPow ε N p) M‖, ?_⟩
  intro t
  exact (Real.norm_eq_abs _).ge.trans (hbound t)

/-- Regularized test profile approximating `t ↦ t^(p-1)` on the positive
half-line while keeping a smooth globally bounded derivative. -/
noncomputable def moserRegTestPow (ε N p : ℝ) : ℝ → ℝ :=
  fun t => (ε + moserSmoothClip ε N t) ^ (p - 1) - ε ^ (p - 1)

theorem moserRegTestPow_contDiff {ε N p : ℝ} (hε : 0 < ε) (hN : 0 ≤ N) :
    ContDiff ℝ (⊤ : ℕ∞) (moserRegTestPow ε N p) := by
  have hbase : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ => ε + moserSmoothClip ε N t) := by
    exact contDiff_const.add (moserSmoothClip_contDiff (ε := ε) (N := N) hε)
  have hbase_ne : ∀ t : ℝ, ε + moserSmoothClip ε N t ≠ 0 := by
    intro t
    have hclip_nonneg : 0 ≤ moserSmoothClip ε N t := by
      by_cases ht0 : t ≤ 0
      · rw [moserSmoothClip_eq_zero_of_nonpos (ε := ε) (N := N) hε hN ht0]
      · have ht0' : 0 < t := lt_of_not_ge ht0
        by_cases ht1 : N + 1 ≤ t
        · rw [moserSmoothClip_eq_top_of_top_le (ε := ε) (N := N) ht1]
          exact hN
        · have hσ₀_nonneg : 0 ≤ Real.smoothTransition (t / ε) := Real.smoothTransition.nonneg _
          have hσ₁_nonneg : 0 ≤ Real.smoothTransition (N + 1 - t) := Real.smoothTransition.nonneg _
          have hσ₁_le : Real.smoothTransition (N + 1 - t) ≤ 1 := Real.smoothTransition.le_one _
          dsimp [moserSmoothClip]
          have hterm1_nonneg :
              0 ≤ t * Real.smoothTransition (t / ε) * Real.smoothTransition (N + 1 - t) := by
            positivity
          have hterm2_nonneg :
              0 ≤ N * (1 - Real.smoothTransition (N + 1 - t)) := by
            have : 0 ≤ 1 - Real.smoothTransition (N + 1 - t) := by linarith
            exact mul_nonneg hN this
          linarith
    linarith
  simpa [moserRegTestPow] using (hbase.rpow_const_of_ne hbase_ne).sub contDiff_const

theorem moserRegTestPow_eq_zero_of_nonpos
    {ε N p t : ℝ} (hε : 0 < ε) (hN : 0 ≤ N) (ht : t ≤ 0) :
    moserRegTestPow ε N p t = 0 := by
  rw [moserRegTestPow, moserSmoothClip_eq_zero_of_nonpos (ε := ε) (N := N) hε hN ht]
  ring_nf

theorem moserRegTestPow_eq_shifted_on_midrange
    {ε N p t : ℝ} (hε : 0 < ε) (hεt : ε ≤ t) (htN : t ≤ N) :
    moserRegTestPow ε N p t = (ε + t) ^ (p - 1) - ε ^ (p - 1) := by
  rw [moserRegTestPow, moserSmoothClip_eq_self_on_midrange (ε := ε) (N := N) hε hεt htN]

theorem moserRegTestPow_deriv_bounded
    {ε N p : ℝ} (hε : 0 < ε) (hN : 0 ≤ N) :
    ∃ M, ∀ t, |deriv (moserRegTestPow ε N p) t| ≤ M := by
  have h1 : ContDiff ℝ 1 (moserRegTestPow ε N p) :=
    (moserRegTestPow_contDiff (ε := ε) (N := N) (p := p) hε hN).of_le (by simp)
  have hcont : Continuous (deriv (moserRegTestPow ε N p)) := h1.continuous_deriv_one
  obtain ⟨M, -, hM_max⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := N + 1)).exists_isMaxOn
    (Set.nonempty_Icc.2 (by linarith : (0 : ℝ) ≤ N + 1)) hcont.norm.continuousOn
  have hbound : ∀ t : ℝ, ‖deriv (moserRegTestPow ε N p) t‖ ≤ ‖deriv (moserRegTestPow ε N p) M‖ := by
    intro t
    by_cases ht0 : t < 0
    · have hloc : moserRegTestPow ε N p =ᶠ[nhds t] fun _ => (0 : ℝ) := by
        filter_upwards [Iio_mem_nhds ht0] with y hy
        exact moserRegTestPow_eq_zero_of_nonpos (ε := ε) (N := N) (p := p) hε hN hy.le
      rw [hloc.deriv_eq, deriv_const, norm_zero]
      exact norm_nonneg _
    · by_cases ht1 : N + 1 < t
      · have hconst :
            moserRegTestPow ε N p =ᶠ[nhds t]
              fun _ => (ε + N) ^ (p - 1) - ε ^ (p - 1) := by
          filter_upwards [Ioi_mem_nhds ht1] with y hy
          rw [moserRegTestPow, moserSmoothClip_eq_top_of_top_le (ε := ε) (N := N) hy.le]
        rw [hconst.deriv_eq, deriv_const, norm_zero]
        exact norm_nonneg _
      · push_neg at ht0 ht1
        exact Filter.eventually_principal.mp hM_max t (Set.mem_Icc.2 ⟨ht0, ht1⟩)
  refine ⟨‖deriv (moserRegTestPow ε N p) M‖, ?_⟩
  intro t
  exact (Real.norm_eq_abs _).ge.trans (hbound t)

/-! #### Exact-on-support regularization for the final Moser step

The original `moserSmoothClip` regularizes both the lower and upper ends of the
positive part. For the last subsolution-testing step we only need a smooth
global extension that agrees with the exact shifted powers on the bounded
nonnegative range where the cutoff `η` sees `u₊`. The qualitative `L^∞` bound
from Chapter 05 supplies that range. -/

/-- Smooth left transition used to extend the exact shifted powers below `0`
while keeping them unchanged on `[0, ∞)`. -/
noncomputable def moserExactLeftTransition (ε : ℝ) : ℝ → ℝ :=
  fun t => Real.smoothTransition (1 + (2 / ε) * t)

/-- Smooth identity profile which equals `t` on `[0, N]`, is constant `N`
for `t ≥ N + 1`, and stays above `-ε / 2` globally. -/
noncomputable def moserExactInput (ε N : ℝ) : ℝ → ℝ :=
  fun t =>
    let σL := moserExactLeftTransition ε t
    let σR := Real.smoothTransition (N + 1 - t)
    t * σL * σR + N * (1 - σR)

theorem moserExactLeftTransition_eq_one_of_nonneg
    {ε t : ℝ} (hε : 0 < ε) (ht : 0 ≤ t) :
    moserExactLeftTransition ε t = 1 := by
  apply Real.smoothTransition.one_of_one_le
  dsimp [moserExactLeftTransition]
  have haux : 1 ≤ 1 + (2 / ε) * t := by
    have : 0 ≤ (2 / ε) * t := by positivity
    linarith
  exact haux

theorem moserExactInput_eq_self_of_nonneg_le_N
    {ε N t : ℝ} (hε : 0 < ε) (ht0 : 0 ≤ t) (htN : t ≤ N) :
    moserExactInput ε N t = t := by
  have hσL : moserExactLeftTransition ε t = 1 :=
    moserExactLeftTransition_eq_one_of_nonneg (ε := ε) hε ht0
  have hσR : Real.smoothTransition (N + 1 - t) = 1 := by
    apply Real.smoothTransition.one_of_one_le
    linarith
  simp [moserExactInput, hσL, hσR]

theorem moserExactInput_eq_top_of_top_le
    {ε N t : ℝ} (ht : N + 1 ≤ t) :
    moserExactInput ε N t = N := by
  have hσR : Real.smoothTransition (N + 1 - t) = 0 := by
    apply Real.smoothTransition.zero_of_nonpos
    linarith
  simp [moserExactInput, hσR]

theorem moserExactInput_lower_bound
    {ε N t : ℝ} (hε : 0 < ε) (hN : 0 ≤ N) :
    -ε / 2 ≤ moserExactInput ε N t := by
  by_cases ht0 : t ≤ -ε / 2
  · have hσL : moserExactLeftTransition ε t = 0 := by
      apply Real.smoothTransition.zero_of_nonpos
      dsimp [moserExactLeftTransition]
      have : 1 + (2 / ε) * t ≤ 0 := by
        have hcoeff_nonneg : 0 ≤ 2 / ε := by positivity
        have hmul : (2 / ε) * t ≤ (2 / ε) * (-ε / 2) :=
          mul_le_mul_of_nonneg_left ht0 hcoeff_nonneg
        have hEq : (2 / ε) * (-ε / 2) = (-1 : ℝ) := by
          field_simp [hε.ne']
        linarith [hmul, hEq]
      exact this
    have hσR_nonneg : 0 ≤ Real.smoothTransition (N + 1 - t) := Real.smoothTransition.nonneg _
    have hσR_le : Real.smoothTransition (N + 1 - t) ≤ 1 := Real.smoothTransition.le_one _
    calc
      -ε / 2 ≤ 0 := by linarith
      _ ≤ moserExactInput ε N t := by
        dsimp [moserExactInput]
        have : 0 ≤ N * (1 - Real.smoothTransition (N + 1 - t)) := by
          have hfac : 0 ≤ 1 - Real.smoothTransition (N + 1 - t) := by linarith
          exact mul_nonneg hN hfac
        simpa [hσL] using this
  · have ht0' : -ε / 2 < t := lt_of_not_ge ht0
    have hσL_nonneg : 0 ≤ moserExactLeftTransition ε t := Real.smoothTransition.nonneg _
    have hσR_nonneg : 0 ≤ Real.smoothTransition (N + 1 - t) := Real.smoothTransition.nonneg _
    have hσR_le : Real.smoothTransition (N + 1 - t) ≤ 1 := Real.smoothTransition.le_one _
    have hterm1 : -ε / 2 ≤ t * moserExactLeftTransition ε t * Real.smoothTransition (N + 1 - t) := by
      have hmul_nonneg :
          0 ≤ moserExactLeftTransition ε t * Real.smoothTransition (N + 1 - t) := by
        positivity
      have hmul_le_one :
          moserExactLeftTransition ε t * Real.smoothTransition (N + 1 - t) ≤ 1 := by
        have hσL_le : moserExactLeftTransition ε t ≤ 1 := Real.smoothTransition.le_one _
        have hmul :
            moserExactLeftTransition ε t * Real.smoothTransition (N + 1 - t) ≤
              1 * Real.smoothTransition (N + 1 - t) := by
          exact mul_le_mul_of_nonneg_right hσL_le hσR_nonneg
        linarith
      by_cases ht_nonneg : 0 ≤ t
      · have hnonneg_term : 0 ≤ t * moserExactLeftTransition ε t * Real.smoothTransition (N + 1 - t) := by
          positivity
        linarith
      · have ht_neg : t < 0 := lt_of_not_ge ht_nonneg
        have hmono : t ≤ t * (moserExactLeftTransition ε t * Real.smoothTransition (N + 1 - t)) := by
          have hle := mul_le_mul_of_nonpos_left hmul_le_one ht_neg.le
          simpa using hle
        linarith
    have hterm2 : 0 ≤ N * (1 - Real.smoothTransition (N + 1 - t)) := by
      have hfac : 0 ≤ 1 - Real.smoothTransition (N + 1 - t) := by linarith
      exact mul_nonneg hN hfac
    dsimp [moserExactInput]
    linarith

theorem moserExactInput_nonneg_of_nonneg
    {ε N t : ℝ} (hε : 0 < ε) (hN : 0 ≤ N) (ht : 0 ≤ t) :
    0 ≤ moserExactInput ε N t := by
  by_cases htN : t ≤ N
  · rw [moserExactInput_eq_self_of_nonneg_le_N (ε := ε) hε ht htN]
    exact ht
  · have htN' : N < t := lt_of_not_ge htN
    by_cases htop : N + 1 ≤ t
    · rw [moserExactInput_eq_top_of_top_le (ε := ε) htop]
      exact hN
    · have hσL : moserExactLeftTransition ε t = 1 :=
        moserExactLeftTransition_eq_one_of_nonneg (ε := ε) hε ht
      have hσR_nonneg : 0 ≤ Real.smoothTransition (N + 1 - t) := Real.smoothTransition.nonneg _
      have hσR_le : Real.smoothTransition (N + 1 - t) ≤ 1 := Real.smoothTransition.le_one _
      dsimp [moserExactInput]
      have hterm1 : 0 ≤ t * 1 * Real.smoothTransition (N + 1 - t) := by positivity
      have hterm2 : 0 ≤ N * (1 - Real.smoothTransition (N + 1 - t)) := by
        have hfac : 0 ≤ 1 - Real.smoothTransition (N + 1 - t) := by linarith
        exact mul_nonneg hN hfac
      simp [hσL]
      linarith

/-- Exact-on-support regularized power: on the bounded nonnegative interval
seen by the cutoff support, this is exactly `t ↦ (ε + t)^(p/2) - ε^(p/2)`. -/
noncomputable def moserExactRegPow (ε N p : ℝ) : ℝ → ℝ :=
  fun t => (ε + moserExactInput ε N t) ^ (p / 2) - ε ^ (p / 2)

/-- Exact-on-support regularized test power: on the bounded nonnegative interval
seen by the cutoff support, this is exactly `t ↦ (ε + t)^(p-1) - ε^(p-1)`. -/
noncomputable def moserExactRegTestPow (ε N p : ℝ) : ℝ → ℝ :=
  fun t => (ε + moserExactInput ε N t) ^ (p - 1) - ε ^ (p - 1)

theorem moserExactRegPow_eq_shifted_of_nonneg_le_N
    {ε N p t : ℝ} (hε : 0 < ε) (ht0 : 0 ≤ t) (htN : t ≤ N) :
    moserExactRegPow ε N p t = (ε + t) ^ (p / 2) - ε ^ (p / 2) := by
  rw [moserExactRegPow, moserExactInput_eq_self_of_nonneg_le_N (ε := ε) hε ht0 htN]

theorem moserExactRegTestPow_eq_shifted_of_nonneg_le_N
    {ε N p t : ℝ} (hε : 0 < ε) (ht0 : 0 ≤ t) (htN : t ≤ N) :
    moserExactRegTestPow ε N p t = (ε + t) ^ (p - 1) - ε ^ (p - 1) := by
  rw [moserExactRegTestPow, moserExactInput_eq_self_of_nonneg_le_N (ε := ε) hε ht0 htN]

theorem moserExactLeftTransition_contDiff
    {ε : ℝ} (_hε : 0 < ε) :
    ContDiff ℝ (⊤ : ℕ∞) (moserExactLeftTransition ε) := by
  have hlin : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ => (2 / ε) * t + 1) := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      ((contDiff_const : ContDiff ℝ (⊤ : ℕ∞) fun _ : ℝ => 2 / ε).mul contDiff_id).add
        contDiff_const
  simpa [moserExactLeftTransition, add_comm, add_left_comm, add_assoc] using
    Real.smoothTransition.contDiff.comp hlin

theorem moserExactInput_contDiff
    {ε N : ℝ} (hε : 0 < ε) :
    ContDiff ℝ (⊤ : ℕ∞) (moserExactInput ε N) := by
  have hσL :
      ContDiff ℝ (⊤ : ℕ∞) (moserExactLeftTransition ε) := by
    exact moserExactLeftTransition_contDiff (ε := ε) hε
  have hσR :
      ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ => Real.smoothTransition (N + 1 - t)) := by
    have hlin : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ => N + 1 - t) := by
      simpa using
        ((contDiff_const : ContDiff ℝ (⊤ : ℕ∞) fun _ : ℝ => N + 1).sub contDiff_id)
    simpa using Real.smoothTransition.contDiff.comp hlin
  simpa [moserExactInput, moserExactLeftTransition] using
    (((contDiff_id.mul hσL).mul hσR).add
      (contDiff_const.mul (contDiff_const.sub hσR))
      : ContDiff ℝ (⊤ : ℕ∞)
          (fun t : ℝ =>
            t * Real.smoothTransition (1 + (2 / ε) * t) * Real.smoothTransition (N + 1 - t) +
              N * (1 - Real.smoothTransition (N + 1 - t))))

theorem moserExactBase_ne_zero
    {ε N : ℝ} (hε : 0 < ε) (hN : 0 ≤ N) :
    ∀ t : ℝ, ε + moserExactInput ε N t ≠ 0 := by
  intro t
  have hbase_lb : ε / 2 ≤ ε + moserExactInput ε N t := by
    have hinput_lb := moserExactInput_lower_bound (ε := ε) (N := N) hε hN (t := t)
    linarith
  have hbase_pos : 0 < ε + moserExactInput ε N t := by
    have : 0 < ε / 2 := by positivity
    exact lt_of_lt_of_le this hbase_lb
  exact hbase_pos.ne'

theorem moserExactRegPow_contDiff
    {ε N p : ℝ} (hε : 0 < ε) (hN : 0 ≤ N) :
    ContDiff ℝ (⊤ : ℕ∞) (moserExactRegPow ε N p) := by
  have hbase : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ => ε + moserExactInput ε N t) := by
    exact contDiff_const.add (moserExactInput_contDiff (ε := ε) (N := N) hε)
  simpa [moserExactRegPow] using
    (hbase.rpow_const_of_ne (moserExactBase_ne_zero (ε := ε) (N := N) hε hN)).sub contDiff_const

theorem moserExactRegTestPow_contDiff
    {ε N p : ℝ} (hε : 0 < ε) (hN : 0 ≤ N) :
    ContDiff ℝ (⊤ : ℕ∞) (moserExactRegTestPow ε N p) := by
  have hbase : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ => ε + moserExactInput ε N t) := by
    exact contDiff_const.add (moserExactInput_contDiff (ε := ε) (N := N) hε)
  simpa [moserExactRegTestPow] using
    (hbase.rpow_const_of_ne (moserExactBase_ne_zero (ε := ε) (N := N) hε hN)).sub contDiff_const

theorem moserExactRegPow_deriv_bounded
    {ε N p : ℝ} (hε : 0 < ε) (hN : 0 ≤ N) :
    ∃ M, ∀ t, |deriv (moserExactRegPow ε N p) t| ≤ M := by
  have h1 : ContDiff ℝ 1 (moserExactRegPow ε N p) :=
    (moserExactRegPow_contDiff (ε := ε) (N := N) (p := p) hε hN).of_le (by simp)
  have hcont : Continuous (deriv (moserExactRegPow ε N p)) := h1.continuous_deriv_one
  obtain ⟨M, -, hM_max⟩ := (isCompact_Icc (a := (-ε / 2 : ℝ)) (b := N + 1)).exists_isMaxOn
    (Set.nonempty_Icc.2 (by linarith : (-ε / 2 : ℝ) ≤ N + 1)) hcont.norm.continuousOn
  have hbound : ∀ t : ℝ, ‖deriv (moserExactRegPow ε N p) t‖ ≤ ‖deriv (moserExactRegPow ε N p) M‖ := by
    intro t
    by_cases ht0 : t < -ε / 2
    · have hloc : moserExactRegPow ε N p =ᶠ[nhds t] fun _ => (0 : ℝ) := by
        filter_upwards [Iio_mem_nhds ht0] with y hy
        have hσL : moserExactLeftTransition ε y = 0 := by
          apply Real.smoothTransition.zero_of_nonpos
          dsimp [moserExactLeftTransition]
          have : 1 + (2 / ε) * y ≤ 0 := by
            have hcoeff_nonneg : 0 ≤ 2 / ε := by positivity
            have hmul : (2 / ε) * y ≤ (2 / ε) * (-ε / 2) :=
              mul_le_mul_of_nonneg_left hy.le hcoeff_nonneg
            have hEq : (2 / ε) * (-ε / 2) = (-1 : ℝ) := by
              field_simp [hε.ne']
            linarith [hmul, hEq]
          exact this
        have hσR : Real.smoothTransition (N + 1 - y) = 1 := by
          apply Real.smoothTransition.one_of_one_le
          have hy_lt : y < -ε / 2 := hy
          have hy_le0 : y ≤ 0 := by linarith
          have : 1 ≤ N + 1 - y := by linarith
          exact this
        simp [moserExactRegPow, moserExactInput, hσL, hσR]
      rw [hloc.deriv_eq, deriv_const, norm_zero]
      exact norm_nonneg _
    · by_cases ht1 : N + 1 < t
      · have hconst :
            moserExactRegPow ε N p =ᶠ[nhds t]
              fun _ => (ε + N) ^ (p / 2) - ε ^ (p / 2) := by
          filter_upwards [Ioi_mem_nhds ht1] with y hy
          rw [moserExactRegPow, moserExactInput_eq_top_of_top_le (ε := ε) (N := N) hy.le]
        rw [hconst.deriv_eq, deriv_const, norm_zero]
        exact norm_nonneg _
      · push_neg at ht0 ht1
        exact Filter.eventually_principal.mp hM_max t (Set.mem_Icc.2 ⟨ht0, ht1⟩)
  refine ⟨‖deriv (moserExactRegPow ε N p) M‖, ?_⟩
  intro t
  exact (Real.norm_eq_abs _).ge.trans (hbound t)

theorem moserExactRegTestPow_deriv_bounded
    {ε N p : ℝ} (hε : 0 < ε) (hN : 0 ≤ N) :
    ∃ M, ∀ t, |deriv (moserExactRegTestPow ε N p) t| ≤ M := by
  have h1 : ContDiff ℝ 1 (moserExactRegTestPow ε N p) :=
    (moserExactRegTestPow_contDiff (ε := ε) (N := N) (p := p) hε hN).of_le (by simp)
  have hcont : Continuous (deriv (moserExactRegTestPow ε N p)) := h1.continuous_deriv_one
  obtain ⟨M, -, hM_max⟩ := (isCompact_Icc (a := (-ε / 2 : ℝ)) (b := N + 1)).exists_isMaxOn
    (Set.nonempty_Icc.2 (by linarith : (-ε / 2 : ℝ) ≤ N + 1)) hcont.norm.continuousOn
  have hbound : ∀ t : ℝ, ‖deriv (moserExactRegTestPow ε N p) t‖ ≤ ‖deriv (moserExactRegTestPow ε N p) M‖ := by
    intro t
    by_cases ht0 : t < -ε / 2
    · have hloc : moserExactRegTestPow ε N p =ᶠ[nhds t] fun _ => (0 : ℝ) := by
        filter_upwards [Iio_mem_nhds ht0] with y hy
        have hσL : moserExactLeftTransition ε y = 0 := by
          apply Real.smoothTransition.zero_of_nonpos
          dsimp [moserExactLeftTransition]
          have : 1 + (2 / ε) * y ≤ 0 := by
            have hcoeff_nonneg : 0 ≤ 2 / ε := by positivity
            have hmul : (2 / ε) * y ≤ (2 / ε) * (-ε / 2) :=
              mul_le_mul_of_nonneg_left hy.le hcoeff_nonneg
            have hEq : (2 / ε) * (-ε / 2) = (-1 : ℝ) := by
              field_simp [hε.ne']
            linarith [hmul, hEq]
          exact this
        have hσR : Real.smoothTransition (N + 1 - y) = 1 := by
          apply Real.smoothTransition.one_of_one_le
          have hy_lt : y < -ε / 2 := hy
          have hy_le0 : y ≤ 0 := by linarith
          have : 1 ≤ N + 1 - y := by linarith
          exact this
        simp [moserExactRegTestPow, moserExactInput, hσL, hσR]
      rw [hloc.deriv_eq, deriv_const, norm_zero]
      exact norm_nonneg _
    · by_cases ht1 : N + 1 < t
      · have hconst :
            moserExactRegTestPow ε N p =ᶠ[nhds t]
              fun _ => (ε + N) ^ (p - 1) - ε ^ (p - 1) := by
          filter_upwards [Ioi_mem_nhds ht1] with y hy
          rw [moserExactRegTestPow, moserExactInput_eq_top_of_top_le (ε := ε) (N := N) hy.le]
        rw [hconst.deriv_eq, deriv_const, norm_zero]
        exact norm_nonneg _
      · push_neg at ht0 ht1
        exact Filter.eventually_principal.mp hM_max t (Set.mem_Icc.2 ⟨ht0, ht1⟩)
  refine ⟨‖deriv (moserExactRegTestPow ε N p) M‖, ?_⟩
  intro t
  exact (Real.norm_eq_abs _).ge.trans (hbound t)


end DeGiorgi
