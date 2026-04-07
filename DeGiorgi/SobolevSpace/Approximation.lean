import DeGiorgi.SobolevSpace.Witnesses

/-!
# Chapter 02: Sobolev Approximation Layer

This module packages cutoffs, zero-extension, convolution smoothing, and the
whole-space approximation results used downstream.
-/

noncomputable section

open MeasureTheory Metric Filter Topology Set Function Matrix
open scoped ENNReal NNReal Convolution Pointwise

namespace DeGiorgi

variable {d : ℕ} [NeZero d]

local notation "E" => EuclideanSpace ℝ (Fin d)

omit [NeZero d] in
private lemma exists_smooth_cutoff
    {K Ω : Set E}
    (hK : IsCompact K) (hΩ : IsOpen Ω) (hKΩ : K ⊆ Ω) :
    ∃ η : E → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) η ∧
      HasCompactSupport η ∧
      Set.range η ⊆ Set.Icc (0 : ℝ) 1 ∧
      (∀ x ∈ K, η x = 1) ∧
      tsupport η ⊆ Ω := by
  obtain ⟨δ, hδ_pos, hδΩ⟩ := hK.exists_cthickening_subset_open hΩ hKΩ
  rcases exists_contMDiff_support_eq_eq_one_iff
      (I := modelWithCornersSelf ℝ E) (s := Metric.thickening δ K) (t := K)
      isOpen_thickening hK.isClosed (self_subset_thickening hδ_pos K) with
    ⟨η, hη_smooth, hη_range, hη_support, hη_one_iff⟩
  refine ⟨η, contMDiff_iff_contDiff.mp hη_smooth, ?_, hη_range, ?_, ?_⟩
  · apply HasCompactSupport.intro' (K := Metric.cthickening δ K)
    · exact hK.cthickening (r := δ)
    · simpa using (isClosed_cthickening : IsClosed (Metric.cthickening δ K))
    · intro x hx
      have hxt : x ∉ tsupport η := by
        intro hxt
        have hx_closure : x ∈ closure (Metric.thickening δ K) := by
          rw [tsupport, hη_support] at hxt
          exact hxt
        exact hx ((Metric.closure_thickening_subset_cthickening δ K) hx_closure)
      exact image_eq_zero_of_notMem_tsupport hxt
  · intro x hx
    exact (hη_one_iff x).1 hx
  · rw [tsupport, hη_support]
    exact Metric.closure_thickening_subset_cthickening δ K |>.trans hδΩ

private lemma memW01p_of_global_approx_supported
    {Ω : Set E} {p : ℝ≥0∞} {u : E → ℝ}
    (hw : MemW1pWitness p u Ω)
    (φ : ℕ → E → ℝ)
    (hφ_smooth : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (φ n))
    (hφ_compact : ∀ n, HasCompactSupport (φ n))
    (hφ_sub : ∀ n, tsupport (φ n) ⊆ Ω)
    (hφ_fun :
      Tendsto (fun n => eLpNorm (fun x => φ n x - u x) p (volume.restrict Ω))
        atTop (nhds 0))
    (hφ_grad :
      ∀ i : Fin d, Tendsto (fun n => eLpNorm
        (fun x => (fderiv ℝ (φ n) x) (EuclideanSpace.single i 1) - hw.weakGrad x i)
        p (volume.restrict Ω)) atTop (nhds 0)) :
    MemW01p p u Ω := by
  let _ := (inferInstance : NeZero d)
  exact ⟨hw.memW1p, hw, φ, hφ_smooth, hφ_compact, hφ_sub, hφ_fun, hφ_grad⟩

omit [NeZero d] in
theorem zero_outside_of_tsupport_subset
    {Ω : Set E} {f : E → ℝ}
    (hsub : tsupport f ⊆ Ω) {x : E} (hx : x ∉ Ω) :
    f x = 0 := by
  by_cases hfx : f x = 0
  · exact hfx
  · exfalso
    exact hx (hsub (subset_tsupport f (mem_support.mpr hfx)))

theorem fderiv_apply_zero_outside_of_tsupport_subset
    {Ω : Set E} {f : E → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hsub : tsupport f ⊆ Ω) {x : E} (hx : x ∉ Ω) (i : Fin d) :
    (fderiv ℝ f x) (EuclideanSpace.single i 1) = 0 := by
  let _ := (inferInstance : NeZero d)
  let _ := hf
  apply zero_outside_of_tsupport_subset
    (Ω := Ω)
    (f := fun y => (fderiv ℝ f y) (EuclideanSpace.single i 1))
  · exact (tsupport_fderiv_apply_subset ℝ (EuclideanSpace.single i (1 : ℝ))).trans hsub
  · exact hx

/-- Zero-extension of a compactly supported local `W^{1,p}` witness to all of
`ℝ^d`, using the `MemW01p` approximation sequence on the source open set. -/
noncomputable def zeroExtend_memW1pWitness_p
    {Ω : Set E} (hΩ : IsOpen Ω)
    {p : ℝ} (hp : 1 < p)
    {v : E → ℝ}
    (hv : MemW01p (ENNReal.ofReal p) v Ω)
    (hw : MemW1pWitness (ENNReal.ofReal p) v Ω) :
    MemW1pWitness (ENNReal.ofReal p) (Ω.indicator v) Set.univ := by
  classical
  have hΩ_meas : MeasurableSet Ω := hΩ.measurableSet
  let hw₀ : MemW1pWitness (ENNReal.ofReal p) v Ω := Classical.choose hv.2
  let hExφ := Classical.choose_spec hv.2
  let φ : ℕ → E → ℝ := Classical.choose hExφ
  have hφspec := Classical.choose_spec hExφ
  have hφ_smooth : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (φ n) := hφspec.1
  have hφ_compact : ∀ n, HasCompactSupport (φ n) := hφspec.2.1
  have hφ_sub : ∀ n, tsupport (φ n) ⊆ Ω := hφspec.2.2.1
  have hφ_fun :
      Tendsto
        (fun n => eLpNorm (fun x => φ n x - v x) (ENNReal.ofReal p) (volume.restrict Ω))
        atTop (nhds 0) := hφspec.2.2.2.1
  have hφ_grad :
      ∀ i : Fin d,
        Tendsto
          (fun n =>
            eLpNorm
              (fun x => (fderiv ℝ (φ n) x) (EuclideanSpace.single i 1) - hw₀.weakGrad x i)
              (ENNReal.ofReal p) (volume.restrict Ω))
          atTop (nhds 0) := hφspec.2.2.2.2
  let G : E → E := fun x =>
    WithLp.toLp 2 fun i => Ω.indicator (fun y => hw.weakGrad y i) x
  refine
    { memLp := ?_
      weakGrad := G
      weakGrad_component_memLp := ?_
      isWeakGrad := ?_ }
  · simpa using
      (MeasureTheory.memLp_indicator_iff_restrict
        (μ := volume) (s := Ω) (f := v) (p := ENNReal.ofReal p) hΩ_meas).2 hw.memLp
  · intro i
    simpa [G, PiLp.toLp_apply] using
      (MeasureTheory.memLp_indicator_iff_restrict
        (μ := volume) (s := Ω) (f := fun y => hw.weakGrad y i) (p := ENNReal.ofReal p) hΩ_meas).2
        (hw.weakGrad_component_memLp i)
  · intro i
    have hp_le : 1 ≤ p := le_of_lt hp
    have hcompΩ :
        (fun x => hw₀.weakGrad x i) =ᵐ[volume.restrict Ω] (fun x => hw.weakGrad x i) := by
      exact HasWeakPartialDeriv.ae_eq hΩ (hw₀.isWeakGrad i) (hw.isWeakGrad i)
        ((hw₀.weakGrad_component_memLp i).locallyIntegrable (by
          simpa using (ENNReal.ofReal_le_ofReal hp_le : ENNReal.ofReal (1 : ℝ) ≤ ENNReal.ofReal p)))
        ((hw.weakGrad_component_memLp i).locallyIntegrable (by
          simpa using (ENNReal.ofReal_le_ofReal hp_le : ENNReal.ofReal (1 : ℝ) ≤ ENNReal.ofReal p)))
    refine HasWeakPartialDeriv.of_eLpNormApprox_p
      (d := d) (Ω := Set.univ) (p := p) (hΩ := isOpen_univ) (hp := hp)
      (i := i) (f := Ω.indicator v) (g := fun x => G x i)
      (ψ := φ)
      (gψ := fun n x => (fderiv ℝ (φ n) x) (EuclideanSpace.single i 1))
      ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · rw [Measure.restrict_univ]
      simpa using
        (MeasureTheory.memLp_indicator_iff_restrict
          (μ := volume) (s := Ω) (f := v) (p := ENNReal.ofReal p) hΩ_meas).2 hw.memLp
    · rw [Measure.restrict_univ]
      simpa [G, PiLp.toLp_apply] using
        (MeasureTheory.memLp_indicator_iff_restrict
          (μ := volume) (s := Ω) (f := fun y => hw.weakGrad y i) (p := ENNReal.ofReal p) hΩ_meas).2
          (hw.weakGrad_component_memLp i)
    · intro n
      simpa using
        HasWeakPartialDeriv.of_contDiff (Ω := Set.univ) (i := i) (f := φ n)
          isOpen_univ ((hφ_smooth n).of_le (by norm_cast))
    · intro n
      have hφ_memLp :
          MemLp (φ n) (ENNReal.ofReal p) (volume.restrict Ω) :=
        ((hφ_smooth n).continuous.memLp_of_hasCompactSupport (hφ_compact n)).restrict Ω
      have hEq :
          (fun x => φ n x - Ω.indicator v x) =
            Ω.indicator (fun x => φ n x - v x) := by
        ext x
        by_cases hx : x ∈ Ω
        · simp [hx]
        · have hφx : φ n x = 0 := zero_outside_of_tsupport_subset (Ω := Ω) (hφ_sub n) hx
          simp [hx, hφx]
      rw [Measure.restrict_univ, hEq,
        MeasureTheory.memLp_indicator_iff_restrict (μ := volume) (s := Ω)
          (p := ENNReal.ofReal p) hΩ_meas]
      exact hφ_memLp.sub hw.memLp
    · have hEq :
          (fun n => eLpNorm (fun x => φ n x - Ω.indicator v x) (ENNReal.ofReal p) volume) =
            fun n => eLpNorm (fun x => φ n x - v x) (ENNReal.ofReal p) (volume.restrict Ω) := by
        funext n
        have hFn :
            (fun x => φ n x - Ω.indicator v x) =
              Ω.indicator (fun x => φ n x - v x) := by
          ext x
          by_cases hx : x ∈ Ω
          · simp [hx]
          · have hφx : φ n x = 0 := zero_outside_of_tsupport_subset (Ω := Ω) (hφ_sub n) hx
            simp [hx, hφx]
        rw [hFn, MeasureTheory.eLpNorm_indicator_eq_eLpNorm_restrict
          (μ := volume) (s := Ω) (p := ENNReal.ofReal p) hΩ_meas]
      rw [Measure.restrict_univ, hEq]
      simpa using hφ_fun
    · intro n
      let ei : E := EuclideanSpace.single i (1 : ℝ)
      have hderiv_smooth :
          ContDiff ℝ (⊤ : ℕ∞) (fun x => (fderiv ℝ (φ n) x) ei) :=
        (hφ_smooth n).fderiv_right (m := (⊤ : ℕ∞)) (by norm_cast)
          |>.clm_apply contDiff_const
      have hderiv_memLp :
          MemLp (fun x => (fderiv ℝ (φ n) x) ei) (ENNReal.ofReal p) (volume.restrict Ω) :=
        (hderiv_smooth.continuous.memLp_of_hasCompactSupport
          ((hφ_compact n).fderiv_apply (𝕜 := ℝ) _)).restrict Ω
      have hEq :
          (fun x => (fderiv ℝ (φ n) x) ei - G x i) =
            Ω.indicator (fun x => (fderiv ℝ (φ n) x) ei - hw.weakGrad x i) := by
        ext x
        by_cases hx : x ∈ Ω
        · simp [G, hx]
        · have hdx :
              (fderiv ℝ (φ n) x) ei = 0 := by
            simpa [ei] using
              fderiv_apply_zero_outside_of_tsupport_subset (Ω := Ω) (hf := hφ_smooth n)
                (hsub := hφ_sub n) hx i
          simp [G, hx, hdx]
      rw [Measure.restrict_univ, hEq,
        MeasureTheory.memLp_indicator_iff_restrict (μ := volume) (s := Ω)
          (p := ENNReal.ofReal p) hΩ_meas]
      exact hderiv_memLp.sub (hw.weakGrad_component_memLp i)
    · have hEq :
          (fun n =>
            eLpNorm
              (fun x => (fderiv ℝ (φ n) x) (EuclideanSpace.single i 1) - G x i)
              (ENNReal.ofReal p) volume) =
            fun n =>
              eLpNorm
                (fun x => (fderiv ℝ (φ n) x) (EuclideanSpace.single i 1) - hw.weakGrad x i)
                (ENNReal.ofReal p) (volume.restrict Ω) := by
        funext n
        have hFn :
            (fun x => (fderiv ℝ (φ n) x) (EuclideanSpace.single i 1) - G x i) =
              Ω.indicator
                (fun x => (fderiv ℝ (φ n) x) (EuclideanSpace.single i 1) - hw.weakGrad x i) := by
          ext x
          by_cases hx : x ∈ Ω
          · simp [G, hx]
          · have hdx :
                (fderiv ℝ (φ n) x) (EuclideanSpace.single i 1) = 0 := by
              exact fderiv_apply_zero_outside_of_tsupport_subset (Ω := Ω) (hf := hφ_smooth n)
                (hsub := hφ_sub n) hx i
            simp [G, hx, hdx]
        rw [hFn, MeasureTheory.eLpNorm_indicator_eq_eLpNorm_restrict
          (μ := volume) (s := Ω) (p := ENNReal.ofReal p) hΩ_meas]
      rw [Measure.restrict_univ, hEq]
      have hEqSeq :
          (fun n =>
            eLpNorm
              (fun x => (fderiv ℝ (φ n) x) (EuclideanSpace.single i 1) - hw.weakGrad x i)
              (ENNReal.ofReal p) (volume.restrict Ω)) =
            (fun n =>
              eLpNorm
                (fun x => (fderiv ℝ (φ n) x) (EuclideanSpace.single i 1) - hw₀.weakGrad x i)
                (ENNReal.ofReal p) (volume.restrict Ω)) := by
        funext n
        have hDiffAe :
            (fun x => (fderiv ℝ (φ n) x) (EuclideanSpace.single i 1) - hw.weakGrad x i)
              =ᵐ[volume.restrict Ω]
            (fun x => (fderiv ℝ (φ n) x) (EuclideanSpace.single i 1) - hw₀.weakGrad x i) := by
          filter_upwards [hcompΩ] with x hx
          simp [hx]
        exact eLpNorm_congr_ae hDiffAe
      rw [hEqSeq]
      simpa using hφ_grad i

omit [NeZero d] in
private lemma tsupport_convolution_subset_cthickening
    {κ u : E → ℝ} {r : ℝ}
    (hκ : Function.support κ ⊆ Metric.closedBall (0 : E) r)
    (hu : HasCompactSupport u) :
    tsupport (κ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] u)
      ⊆ Metric.cthickening r (tsupport u) := by
  let _ := hu
  have hsupport :
      Function.support (κ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] u)
        ⊆ Function.support κ + Function.support u :=
    support_convolution_subset (L := ContinuousLinearMap.lsmul ℝ ℝ) (μ := volume)
  have hsum :
      Function.support κ + Function.support u ⊆ Metric.cthickening r (tsupport u) := by
    intro x hx
    rcases Set.mem_add.mp hx with ⟨a, ha, b, hb, rfl⟩
    have ha_ball : a ∈ Metric.closedBall (0 : E) r := hκ ha
    have hb_tsupport : b ∈ tsupport u := subset_tsupport u hb
    refine Metric.mem_cthickening_of_dist_le (x := a + b) (y := b) (δ := r)
      (tsupport u) hb_tsupport ?_
    simpa [Metric.mem_closedBall, dist_eq_norm, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
      using ha_ball
  simpa [tsupport] using
    closure_minimal (hsupport.trans hsum) isClosed_cthickening

omit [NeZero d] in
private lemma tsupport_normed_convolution_subset_cthickening
    (φ : ContDiffBump (0 : E)) {u : E → ℝ}
    (hu : HasCompactSupport u) :
    tsupport ((φ.normed volume) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] u)
      ⊆ Metric.cthickening φ.rOut (tsupport u) :=
  tsupport_convolution_subset_cthickening
    (r := φ.rOut)
    (fun x hx => (Metric.mem_ball.1 ((by simpa [φ.support_normed_eq] using hx))).le)
    hu

private noncomputable def shrinkingBump (n : ℕ) : ContDiffBump (0 : E) where
  rIn := (((n : ℝ) + 1)⁻¹) / 2
  rOut := ((n : ℝ) + 1)⁻¹
  rIn_pos := by positivity
  rIn_lt_rOut := by
    have hr_pos : 0 < (((n : ℝ) + 1)⁻¹ : ℝ) := by positivity
    nlinarith

omit [NeZero d] in
private lemma tendsto_shrinkingBump_rOut :
    Tendsto (fun n => (shrinkingBump (d := d) n).rOut) atTop (nhds 0) := by
  have h :
      Tendsto (fun n : ℕ => (((n : ℝ) + 1) : ℝ)⁻¹) atTop (nhds (0 : ℝ)) :=
    by simpa [one_div] using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  simpa [shrinkingBump] using h

omit [NeZero d] in
private theorem eLpNorm_normedConvolution_le
    (φ : ContDiffBump (0 : E))
    {p : ℝ} (hp : 1 ≤ p) {f : E → ℝ}
    (hf : MemLp f (ENNReal.ofReal p) volume) :
    eLpNorm ((φ.normed volume) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f)
      (ENNReal.ofReal p) volume ≤
    eLpNorm f (ENNReal.ofReal p) volume := by
  let ψ : E → ℝ := φ.normed volume
  let ρ : E → ℝ≥0∞ := fun y => ENNReal.ofReal (ψ y)
  let ν : Measure E := volume.withDensity ρ
  have hp_pos : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hp0 : ENNReal.ofReal p ≠ 0 := by
    exact ne_of_gt (ENNReal.ofReal_pos.mpr hp_pos)
  have hp_toReal : (ENNReal.ofReal p).toReal = p := by
    simp [hp_pos.le]
  have hρ_meas : Measurable ρ := by
    exact φ.continuous_normed.measurable.ennreal_ofReal
  have hρ_lt_top : ∀ᵐ y ∂volume, ρ y < ∞ := by
    filter_upwards with y
    simp [ρ]
  have hρ_ne_top : ∀ᵐ y ∂volume, ρ y ≠ ∞ := by
    filter_upwards [hρ_lt_top] with y hy
    exact hy.ne
  have hν_prob : IsProbabilityMeasure ν := by
    refine ⟨?_⟩
    rw [show ν = volume.withDensity ρ by rfl, withDensity_apply _ MeasurableSet.univ]
    rw [Measure.restrict_univ]
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal
      φ.integrable_normed (Filter.Eventually.of_forall φ.nonneg_normed)]
    simpa [ρ, ψ] using φ.integral_normed (μ := volume)
  have hf_loc : LocallyIntegrable f volume := by
    exact hf.locallyIntegrable (by simpa using (ENNReal.ofReal_le_ofReal hp : ENNReal.ofReal (1 : ℝ) ≤ ENNReal.ofReal p))
  have hh_int : Integrable (fun x => ‖f x‖ ^ p) volume := by
    simpa [hp_toReal] using hf.integrable_norm_rpow hp0 ENNReal.ofReal_ne_top
  have hψ_int : Integrable ψ volume := by
    simpa [ψ] using φ.integrable_normed
  have hψ_cont : Continuous ψ := by
    simpa [ψ] using φ.continuous_normed
  have hψ_cpt : HasCompactSupport ψ := by
    simpa [ψ] using φ.hasCompactSupport_normed (μ := volume)
  have hconv_cont :
      Continuous (((φ.normed volume) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) : E → ℝ) := by
    exact hψ_cpt.continuous_convolution_left (L := ContinuousLinearMap.lsmul ℝ ℝ) hψ_cont hf_loc
  have hpointwise :
      ∀ x : E,
        ‖((ψ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) x)‖ ^ p ≤
          (ψ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (fun y => ‖f y‖ ^ p)) x := by
    intro x
    have hce_f :
        ConvolutionExistsAt ψ f x (ContinuousLinearMap.lsmul ℝ ℝ) volume := by
      exact (hψ_cpt.convolutionExists_left (L := ContinuousLinearMap.lsmul ℝ ℝ) hψ_cont hf_loc) x
    have hce_h :
        ConvolutionExistsAt ψ (fun y => ‖f y‖ ^ p) x (ContinuousLinearMap.lsmul ℝ ℝ) volume := by
      exact (hψ_cpt.convolutionExists_left
        (L := ContinuousLinearMap.lsmul ℝ ℝ) hψ_cont hh_int.locallyIntegrable) x
    have hconv_ν :
        ((ψ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) x) = ∫ y, f (x - y) ∂ν := by
      rw [show ν = volume.withDensity ρ by rfl]
      rw [integral_withDensity_eq_integral_toReal_smul hρ_meas hρ_lt_top]
      rw [MeasureTheory.convolution_def]
      refine integral_congr_ae ?_
      filter_upwards with y
      simp [ρ, ψ, ContinuousLinearMap.lsmul_apply, smul_eq_mul, φ.nonneg_normed y, mul_comm]
    have h_int_norm_vol :
        Integrable (fun y => (ρ y).toReal * ‖f (x - y)‖) volume := by
      refine hce_f.integrable.norm.congr ?_
      filter_upwards with y
      simp [ρ, ψ, ContinuousLinearMap.lsmul_apply, smul_eq_mul, φ.nonneg_normed y]
    have h_int_norm :
        Integrable (fun y => ‖f (x - y)‖) ν := by
      exact (MeasureTheory.integrable_withDensity_iff_integrable_smul' hρ_meas hρ_lt_top).2 <| by
        simpa [ρ, ψ, φ.nonneg_normed] using h_int_norm_vol
    have h_int_rpow_vol :
        Integrable (fun y => (ρ y).toReal * ‖f (x - y)‖ ^ p) volume := by
      refine hce_h.integrable.congr ?_
      filter_upwards with y
      simp [ρ, ψ, ContinuousLinearMap.lsmul_apply, smul_eq_mul, φ.nonneg_normed y, mul_comm]
    have h_int_rpow :
        Integrable (fun y => ‖f (x - y)‖ ^ p) ν := by
      exact (MeasureTheory.integrable_withDensity_iff_integrable_smul' hρ_meas hρ_lt_top).2 <| by
        simpa [ρ, ψ, φ.nonneg_normed] using h_int_rpow_vol
    have hnorm_le : ‖((ψ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) x)‖ ≤ ∫ y, ‖f (x - y)‖ ∂ν := by
      rw [hconv_ν]
      exact MeasureTheory.norm_integral_le_integral_norm _
    have hJensen :
        (∫ y, ‖f (x - y)‖ ∂ν) ^ p ≤ ∫ y, ‖f (x - y)‖ ^ p ∂ν := by
      have hconv : ConvexOn ℝ (Set.Ici 0) (fun t : ℝ => t ^ p) := convexOn_rpow hp
      have hcont : ContinuousOn (fun t : ℝ => t ^ p) (Set.Ici (0 : ℝ)) := by
        exact continuousOn_id.rpow_const (by
          intro t ht
          exact Or.inr hp_pos.le)
      have hmem : ∀ᵐ y ∂ν, ‖f (x - y)‖ ∈ Set.Ici (0 : ℝ) := by
        filter_upwards with y
        exact norm_nonneg _
      exact hconv.map_integral_le hcont isClosed_Ici hmem h_int_norm h_int_rpow
    calc
      ‖((ψ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) x)‖ ^ p
          ≤ (∫ y, ‖f (x - y)‖ ∂ν) ^ p := by
            exact Real.rpow_le_rpow (norm_nonneg _) hnorm_le hp_pos.le
      _ ≤ ∫ y, ‖f (x - y)‖ ^ p ∂ν := hJensen
      _ = ∫ y, ψ y * ‖f (x - y)‖ ^ p ∂volume := by
            rw [show ν = volume.withDensity ρ by rfl]
            rw [integral_withDensity_eq_integral_toReal_smul hρ_meas hρ_lt_top]
            refine integral_congr_ae ?_
            filter_upwards with y
            simp [ρ, ψ, φ.nonneg_normed y, mul_comm]
      _ = (ψ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (fun y => ‖f y‖ ^ p)) x := by
            simp [MeasureTheory.convolution_def, ContinuousLinearMap.lsmul_apply, mul_comm]
  have hconv_h_int :
      Integrable (ψ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (fun y => ‖f y‖ ^ p)) volume := by
    exact hψ_int.integrable_convolution (L := ContinuousLinearMap.lsmul ℝ ℝ) hh_int
  have hpow_int :
      Integrable (fun x =>
        ‖((ψ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) x)‖ ^ p) volume := by
    refine Integrable.mono' hconv_h_int ?_ ?_
    · exact (hconv_cont.norm.rpow_const (by intro x; exact Or.inr hp_pos.le)).aestronglyMeasurable
    · filter_upwards with x
      have hnonneg : 0 ≤ |((ψ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) x)| ^ p := by
        positivity
      simpa [Real.norm_eq_abs, abs_of_nonneg hnonneg] using hpointwise x
  have h_int_le :
      ∫ x, ‖((ψ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) x)‖ ^ p ∂volume ≤
        ∫ x, (ψ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (fun y => ‖f y‖ ^ p)) x ∂volume := by
    refine integral_mono_ae hpow_int hconv_h_int ?_
    filter_upwards with x
    exact hpointwise x
  have h_conv_eq :
      ∫ x, (ψ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (fun y => ‖f y‖ ^ p)) x ∂volume =
        ∫ x, ‖f x‖ ^ p ∂volume := by
    calc
      ∫ x, (ψ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (fun y => ‖f y‖ ^ p)) x ∂volume
          = (∫ x, ψ x ∂volume) * (∫ x, ‖f x‖ ^ p ∂volume) := by
              simpa [ContinuousLinearMap.lsmul_apply, mul_comm, mul_left_comm, mul_assoc] using
                (MeasureTheory.integral_convolution
                  (L := ContinuousLinearMap.lsmul ℝ ℝ)
                  (μ := volume) (ν := volume) hψ_int hh_int)
      _ = ∫ x, ‖f x‖ ^ p ∂volume := by
            simp [ψ, φ.integral_normed (μ := volume)]
  have hconv_memLp :
      MemLp ((ψ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) : E → ℝ)
        (ENNReal.ofReal p) volume := by
    exact (MeasureTheory.integrable_norm_rpow_iff
      hconv_cont.aestronglyMeasurable hp0 ENNReal.ofReal_ne_top).1 <| by
        simpa [hp_toReal] using hpow_int
  calc
    eLpNorm ((ψ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) : E → ℝ)
        (ENNReal.ofReal p) volume
      = ENNReal.ofReal ((∫ x, ‖((ψ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) x)‖ ^ p ∂volume) ^ p⁻¹) := by
          simpa [hp_toReal] using
            hconv_memLp.eLpNorm_eq_integral_rpow_norm hp0 ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal ((∫ x, ‖f x‖ ^ p ∂volume) ^ p⁻¹) := by
          apply ENNReal.ofReal_le_ofReal
          refine Real.rpow_le_rpow ?_ (h_int_le.trans_eq h_conv_eq) ?_
          · exact integral_nonneg fun _ => by positivity
          · exact inv_nonneg.mpr hp_pos.le
    _ = eLpNorm f (ENNReal.ofReal p) volume := by
          symm
          simpa [hp_toReal] using hf.eLpNorm_eq_integral_rpow_norm hp0 ENNReal.ofReal_ne_top

omit [NeZero d] in
private theorem normedConvolution_sub_eq
    (φ : ContDiffBump (0 : E)) {f g : E → ℝ}
    (hf_loc : LocallyIntegrable f volume) (hg_loc : LocallyIntegrable g volume) :
    (fun x =>
      ((φ.normed volume) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) x -
        ((φ.normed volume) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x) =
    (fun x =>
      ((φ.normed volume) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] fun y => f y - g y) x) := by
  ext x
  have hce_f := (φ.hasCompactSupport_normed (μ := volume)).convolutionExists_left
    (L := ContinuousLinearMap.lsmul ℝ ℝ) φ.continuous_normed hf_loc
  have hce_g := (φ.hasCompactSupport_normed (μ := volume)).convolutionExists_left
    (L := ContinuousLinearMap.lsmul ℝ ℝ) φ.continuous_normed hg_loc
  have hf_int :
      Integrable (fun t => φ.normed volume t * f (x - t)) volume := by
    exact (hce_f x).congr <| Eventually.of_forall fun t => by
      simp [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  have hg_int :
      Integrable (fun t => φ.normed volume t * g (x - t)) volume := by
    exact (hce_g x).congr <| Eventually.of_forall fun t => by
      simp [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  simp only [MeasureTheory.convolution_def, ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  rw [← integral_sub hf_int hg_int]
  congr 1
  ext t
  ring

omit [NeZero d] in
private theorem eLpNorm_normedConvolution_sub_le
    (φ : ContDiffBump (0 : E))
    {p : ℝ} (hp : 1 ≤ p) {f g : E → ℝ}
    (hf : MemLp f (ENNReal.ofReal p) volume)
    (hg : MemLp g (ENNReal.ofReal p) volume) :
    eLpNorm
      (fun x =>
        ((φ.normed volume) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) x -
          ((φ.normed volume) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x)
      (ENNReal.ofReal p) volume ≤
      eLpNorm (fun x => f x - g x) (ENNReal.ofReal p) volume := by
  rw [normedConvolution_sub_eq (d := d) φ
    (hf.locallyIntegrable (by
      simpa using (ENNReal.ofReal_le_ofReal hp : ENNReal.ofReal (1 : ℝ) ≤ ENNReal.ofReal p)))
    (hg.locallyIntegrable (by
      simpa using (ENNReal.ofReal_le_ofReal hp : ENNReal.ofReal (1 : ℝ) ≤ ENNReal.ofReal p)))]
  exact eLpNorm_normedConvolution_le (d := d) φ hp (hf.sub hg)

omit [NeZero d] in
private theorem tendsto_eLpNorm_normedConvolution_sub_of_continuous
    {p : ℝ} (hp : 1 ≤ p) {g : E → ℝ}
    (hg_cont : Continuous g) (hg_comp : HasCompactSupport g) :
    Tendsto
      (fun n =>
        eLpNorm
          (fun x =>
            ((shrinkingBump (d := d) n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x -
              g x)
          (ENNReal.ofReal p) volume)
      atTop (nhds 0) := by
  let _ := hp
  let S : Set E := Metric.cthickening 1 (tsupport g)
  let T : Set E := Metric.cthickening (1 + 1) (tsupport g)
  have hS_comp : IsCompact S := hg_comp.isCompact.cthickening (r := 1)
  have hT_comp : IsCompact T := hg_comp.isCompact.cthickening (r := 1 + 1)
  have hS_meas : MeasurableSet S := hS_comp.measurableSet
  have hS_finite : volume S < ∞ := hS_comp.measure_lt_top
  have hS_sub_T : S ⊆ T := by
    simpa [S, T] using (cthickening_mono (show (1 : ℝ) ≤ 1 + 1 by norm_num) (tsupport g))
  have hg_support_sub : Function.support g ⊆ S := by
    intro x hx
    exact Metric.mem_cthickening_of_dist_le (x := x) (y := x) (δ := 1)
      (tsupport g) (subset_tsupport g hx) (by simp)
  have huc : UniformContinuousOn g T := hT_comp.uniformContinuousOn_of_continuous hg_cont.continuousOn
  refine ENNReal.tendsto_nhds_zero.2 ?_
  intro ε hε
  by_cases hε_top : ε = ∞
  · filter_upwards with n
    simp [hε_top]
  let εr : ℝ := ε.toReal
  have hεr_pos : 0 < εr := ENNReal.toReal_pos hε.ne' hε_top
  let M : ℝ≥0∞ := volume S ^ ((1 : ℝ) / (ENNReal.ofReal p).toReal)
  have hM_top : M ≠ ∞ := by
    simp [M, hS_finite.ne]
  let C : ℝ := M.toReal + 1
  have hC_pos : 0 < C := by
    have hM_nonneg : 0 ≤ M.toReal := ENNReal.toReal_nonneg
    dsimp [C]
    linarith
  let ε0 : ℝ := εr / C
  have hε0_pos : 0 < ε0 := by
    dsimp [ε0]
    positivity
  rcases Metric.uniformContinuousOn_iff.mp huc ε0 hε0_pos with ⟨δ0, hδ0_pos, hδ0⟩
  let δ : ℝ := min δ0 1
  have hδ_pos : 0 < δ := by
    dsimp [δ]
    exact lt_min hδ0_pos zero_lt_one
  have hsmall :
      ∀ᶠ n in atTop, (shrinkingBump (d := d) n).rOut < δ := by
    exact (tendsto_order.1 tendsto_shrinkingBump_rOut).2 _ hδ_pos
  filter_upwards [hsmall] with n hn
  have hrOut_le_one : (shrinkingBump (d := d) n).rOut ≤ 1 := by
    exact le_trans hn.le (min_le_right _ _)
  have hconv_support_sub :
      Function.support
          (((shrinkingBump (d := d) n).normed volume) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g)
        ⊆ S := by
    intro x hx
    have hts :
        tsupport
            (((shrinkingBump (d := d) n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g))
          ⊆ S := by
      refine (tsupport_normed_convolution_subset_cthickening (d := d) (shrinkingBump (d := d) n) hg_comp).trans ?_
      simpa [S] using cthickening_mono hrOut_le_one (tsupport g)
    exact hts (subset_tsupport _ hx)
  have hdist :
      ∀ x : E,
        dist
            (((shrinkingBump (d := d) n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x)
            (g x) ≤ ε0 := by
    intro x
    by_cases hx : x ∈ S
    · have hxT : x ∈ T := hS_sub_T hx
      refine (shrinkingBump (d := d) n).dist_normed_convolution_le hg_cont.aestronglyMeasurable ?_
      intro y hy
      have hyT : y ∈ T := by
        have hyS :
            y ∈ Metric.cthickening 1 S := by
          refine Metric.mem_cthickening_of_dist_le (x := y) (y := x) (δ := 1) S hx ?_
          exact le_trans hy.le hrOut_le_one
        have hyT' : y ∈ Metric.cthickening 1 (Metric.cthickening 1 (tsupport g)) := by
          simpa [S] using hyS
        have hyT'' : y ∈ Metric.cthickening (1 + 1) (tsupport g) := by
          simpa [S, cthickening_cthickening (show (0 : ℝ) ≤ 1 by positivity)
            (show (0 : ℝ) ≤ 1 by positivity) (tsupport g)] using hyT'
        simpa [T] using hyT''
      exact (hδ0 y hyT x hxT (lt_of_lt_of_le hy (le_trans hn.le (min_le_left _ _)))).le
    · have hconvx :
          (((shrinkingBump (d := d) n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x) = 0 := by
        exact zero_outside_of_tsupport_subset
          (Ω := S)
          ((tsupport_normed_convolution_subset_cthickening (d := d) (shrinkingBump (d := d) n) hg_comp).trans
            (by simpa [S] using cthickening_mono hrOut_le_one (tsupport g)))
          hx
      have hgx : g x = 0 := zero_outside_of_tsupport_subset (Ω := S)
        (show tsupport g ⊆ S by
          intro y hy
          exact Metric.mem_cthickening_of_dist_le (x := y) (y := y) (δ := 1)
            (tsupport g) hy (by simp))
        hx
      simp [hconvx, hgx, hε0_pos.le]
  have hbound :
      eLpNorm
        (fun x =>
          ((shrinkingBump (d := d) n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x -
            g x)
        (ENNReal.ofReal p) volume ≤ ENNReal.ofReal ε0 * M := by
    refine eLpNorm_sub_le_of_dist_bdd
      (μ := volume) (p := ENNReal.ofReal p) (s := S) (hp := by simp) hS_meas hε0_pos.le hdist ?_ ?_
    · intro x hx
      exact hconv_support_sub hx
    · exact hg_support_sub
  have hfinal :
      ENNReal.ofReal ε0 * M < ε := by
    have hM_eq : M = ENNReal.ofReal (M.toReal) := by
      exact (ENNReal.ofReal_toReal hM_top).symm
    have hlt_real : ε0 * M.toReal < εr := by
      dsimp [ε0, C]
      have hfrac_lt_one : M.toReal / (M.toReal + 1) < 1 := by
        have hM_nonneg : 0 ≤ M.toReal := ENNReal.toReal_nonneg
        have hden_pos : 0 < M.toReal + 1 := by linarith
        have hnum_lt : M.toReal < M.toReal + 1 := by linarith
        exact (div_lt_one hden_pos).2 hnum_lt
      have hmul_lt : εr * (M.toReal / (M.toReal + 1)) < εr := by
        simpa [mul_comm, mul_left_comm, mul_assoc] using
          (mul_lt_mul_of_pos_left hfrac_lt_one hεr_pos)
      have hcalc :
          εr / (M.toReal + 1) * M.toReal = εr * (M.toReal / (M.toReal + 1)) := by
        field_simp [show M.toReal + 1 ≠ 0 by linarith]
      simpa [hcalc] using hmul_lt
    have hlt_ofReal :
        ENNReal.ofReal ε0 * M < ENNReal.ofReal εr := by
      rw [hM_eq, ← ENNReal.ofReal_mul (show 0 ≤ ε0 by positivity),
        ENNReal.ofReal_lt_ofReal_iff hεr_pos]
      exact hlt_real
    simpa [εr, hε_top] using hlt_ofReal
  exact hbound.trans hfinal.le

omit [NeZero d] in
private theorem tendsto_eLpNorm_normedConvolution_sub
    {p : ℝ} (hp : 1 ≤ p) {f : E → ℝ}
    (hf : MemLp f (ENNReal.ofReal p) volume) :
    Tendsto
      (fun n =>
        eLpNorm
          (fun x =>
            ((shrinkingBump (d := d) n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) x -
              f x)
          (ENNReal.ofReal p) volume)
      atTop (nhds 0) := by
  refine ENNReal.tendsto_nhds_zero.2 ?_
  intro ε hε
  by_cases hε_top : ε = ∞
  · filter_upwards with n
    simp [hε_top]
  let εr : ℝ := ε.toReal
  have hεr_pos : 0 < εr := ENNReal.toReal_pos hε.ne' hε_top
  have hε3_pos : 0 < εr / 3 := by positivity
  obtain ⟨g, hg_comp, hg_smooth, hfg⟩ :=
    hf.exist_eLpNorm_sub_le (by simp) (by
      simpa using (ENNReal.ofReal_le_ofReal hp : ENNReal.ofReal (1 : ℝ) ≤ ENNReal.ofReal p))
      hε3_pos
  have hg_memLp : MemLp g (ENNReal.ofReal p) volume :=
    hg_smooth.continuous.memLp_of_hasCompactSupport hg_comp
  have hmid :
      Tendsto
        (fun n =>
          eLpNorm
            (fun x =>
              ((shrinkingBump (d := d) n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x -
                g x)
            (ENNReal.ofReal p) volume)
        atTop (nhds 0) :=
    tendsto_eLpNorm_normedConvolution_sub_of_continuous (d := d) hp hg_smooth.continuous hg_comp
  have hconv_diff :
      ∀ n,
        eLpNorm
          (fun x =>
            ((shrinkingBump (d := d) n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) x -
              ((shrinkingBump (d := d) n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x)
          (ENNReal.ofReal p) volume ≤
          eLpNorm (fun x => f x - g x) (ENNReal.ofReal p) volume := by
    intro n
    exact eLpNorm_normedConvolution_sub_le (d := d) (shrinkingBump (d := d) n) hp hf hg_memLp
  filter_upwards [ENNReal.tendsto_nhds_zero.1 hmid (ENNReal.ofReal (εr / 3))
      (ENNReal.ofReal_pos.mpr hε3_pos)] with n hn
  have hp_enn : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    simpa using (ENNReal.ofReal_le_ofReal hp : ENNReal.ofReal (1 : ℝ) ≤ ENNReal.ofReal p)
  have hA_cont :
      Continuous
        (fun x =>
          ((shrinkingBump (d := d) n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
              (fun y => f y - g y)) x) := by
    exact (shrinkingBump (d := d) n).hasCompactSupport_normed.continuous_convolution_left
      (L := ContinuousLinearMap.lsmul ℝ ℝ)
      (shrinkingBump (d := d) n).continuous_normed ((hf.sub hg_memLp).locallyIntegrable hp_enn)
  have hB_cont :
      Continuous
        (fun x =>
          ((shrinkingBump (d := d) n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x) := by
    exact (shrinkingBump (d := d) n).hasCompactSupport_normed.continuous_convolution_left
      (L := ContinuousLinearMap.lsmul ℝ ℝ)
      (shrinkingBump (d := d) n).continuous_normed (hg_memLp.locallyIntegrable hp_enn)
  have hF_cont :
      Continuous
        (fun x =>
          ((shrinkingBump (d := d) n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) x) := by
    exact (shrinkingBump (d := d) n).hasCompactSupport_normed.continuous_convolution_left
      (L := ContinuousLinearMap.lsmul ℝ ℝ)
      (shrinkingBump (d := d) n).continuous_normed (hf.locallyIntegrable hp_enn)
  have hA_sm :
      AEStronglyMeasurable
        (fun x =>
          ((shrinkingBump (d := d) n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
              (fun y => f y - g y)) x)
        volume := hA_cont.aestronglyMeasurable
  have hFG_sm :
      AEStronglyMeasurable
        (fun x =>
          ((shrinkingBump (d := d) n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) x -
            ((shrinkingBump (d := d) n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x)
        volume := hF_cont.aestronglyMeasurable.sub hB_cont.aestronglyMeasurable
  have hB_sm :
      AEStronglyMeasurable
        (fun x =>
          ((shrinkingBump (d := d) n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x -
            g x)
        volume := hB_cont.aestronglyMeasurable.sub hg_memLp.aestronglyMeasurable
  have hC_sm :
      AEStronglyMeasurable (fun x => g x - f x) volume :=
    hg_memLp.aestronglyMeasurable.sub hf.aestronglyMeasurable
  have htri :
      eLpNorm
        (fun x =>
          ((shrinkingBump (d := d) n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) x -
            f x)
        (ENNReal.ofReal p) volume ≤
      eLpNorm
        (fun x =>
          ((shrinkingBump (d := d) n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) x -
            ((shrinkingBump (d := d) n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x)
        (ENNReal.ofReal p) volume +
      eLpNorm
        (fun x =>
          ((shrinkingBump (d := d) n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x -
            g x)
        (ENNReal.ofReal p) volume +
      eLpNorm (fun x => g x - f x) (ENNReal.ofReal p) volume := by
    have hdecomp :
        (fun x =>
          ((shrinkingBump (d := d) n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) x -
            f x) =
        (fun x =>
          ((shrinkingBump (d := d) n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) x -
            ((shrinkingBump (d := d) n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x) +
        (fun x =>
          ((shrinkingBump (d := d) n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x -
            g x) +
        (fun x => g x - f x) := by
      ext x
      simp [sub_eq_add_neg, add_assoc, add_comm]
      ring
    rw [hdecomp]
    calc
      eLpNorm
          ((fun x =>
            ((shrinkingBump (d := d) n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) x -
              ((shrinkingBump (d := d) n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x) +
            (fun x =>
              ((shrinkingBump (d := d) n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x -
                g x) +
            (fun x => g x - f x))
          (ENNReal.ofReal p) volume
          ≤
        eLpNorm
            ((fun x =>
              ((shrinkingBump (d := d) n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) x -
                ((shrinkingBump (d := d) n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x) +
            (fun x =>
              ((shrinkingBump (d := d) n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x -
                g x))
            (ENNReal.ofReal p) volume +
          eLpNorm (fun x => g x - f x) (ENNReal.ofReal p) volume := by
            exact eLpNorm_add_le (hFG_sm.add hB_sm) hC_sm hp_enn
      _ ≤
        eLpNorm
          (fun x =>
            ((shrinkingBump (d := d) n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) x -
              ((shrinkingBump (d := d) n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x)
          (ENNReal.ofReal p) volume +
        eLpNorm
          (fun x =>
            ((shrinkingBump (d := d) n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x -
              g x)
          (ENNReal.ofReal p) volume +
        eLpNorm (fun x => g x - f x) (ENNReal.ofReal p) volume := by
          gcongr
          exact eLpNorm_add_le hFG_sm hB_sm hp_enn
  have houter :
      eLpNorm
          (fun x =>
            ((shrinkingBump (d := d) n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) x -
              ((shrinkingBump (d := d) n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x)
          (ENNReal.ofReal p) volume +
        eLpNorm
          (fun x =>
            ((shrinkingBump (d := d) n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x -
              g x)
          (ENNReal.ofReal p) volume +
        eLpNorm (fun x => g x - f x) (ENNReal.ofReal p) volume ≤
      (ENNReal.ofReal (εr / 3) + ENNReal.ofReal (εr / 3)) + ENNReal.ofReal (εr / 3) := by
    have hfg' : eLpNorm (fun x => f x - g x) (ENNReal.ofReal p) volume ≤ ENNReal.ofReal (εr / 3) := by
      simpa [sub_eq_add_neg, add_comm] using hfg
    have hgf' : eLpNorm (fun x => g x - f x) (ENNReal.ofReal p) volume ≤ ENNReal.ofReal (εr / 3) := by
      have hEq :
          eLpNorm (fun x => f x - g x) (ENNReal.ofReal p) volume =
            eLpNorm (fun x => g x - f x) (ENNReal.ofReal p) volume := by
        simpa [sub_eq_add_neg] using
          (eLpNorm_sub_comm (fun x => f x) (fun x => g x) (ENNReal.ofReal p) volume)
      rw [← hEq]
      exact hfg'
    have hfirst_le :
        eLpNorm
            (fun x =>
              ((shrinkingBump (d := d) n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) x -
                ((shrinkingBump (d := d) n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x)
            (ENNReal.ofReal p) volume ≤
          ENNReal.ofReal (εr / 3) := (hconv_diff n).trans hfg'
    calc
      eLpNorm
          (fun x =>
            ((shrinkingBump (d := d) n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) x -
              ((shrinkingBump (d := d) n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x)
          (ENNReal.ofReal p) volume +
        eLpNorm
          (fun x =>
            ((shrinkingBump (d := d) n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x -
              g x)
          (ENNReal.ofReal p) volume +
        eLpNorm (fun x => g x - f x) (ENNReal.ofReal p) volume
          ≤
        ENNReal.ofReal (εr / 3) +
          eLpNorm
            (fun x =>
              ((shrinkingBump (d := d) n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x -
                g x)
            (ENNReal.ofReal p) volume +
          eLpNorm (fun x => g x - f x) (ENNReal.ofReal p) volume := by
            gcongr
      _ ≤ ENNReal.ofReal (εr / 3) + ENNReal.ofReal (εr / 3) +
            eLpNorm (fun x => g x - f x) (ENNReal.ofReal p) volume := by
            gcongr
      _ ≤ ENNReal.ofReal (εr / 3) + ENNReal.ofReal (εr / 3) +
            ENNReal.ofReal (εr / 3) := by
            gcongr
      _ = (ENNReal.ofReal (εr / 3) + ENNReal.ofReal (εr / 3)) +
            ENNReal.ofReal (εr / 3) := by ac_rfl
  calc
    eLpNorm
      (fun x =>
        ((shrinkingBump (d := d) n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) x -
          f x)
      (ENNReal.ofReal p) volume
        ≤
      eLpNorm
        (fun x =>
          ((shrinkingBump (d := d) n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) x -
            ((shrinkingBump (d := d) n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x)
        (ENNReal.ofReal p) volume +
      eLpNorm
        (fun x =>
          ((shrinkingBump (d := d) n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x -
            g x)
        (ENNReal.ofReal p) volume +
      eLpNorm (fun x => g x - f x) (ENNReal.ofReal p) volume := htri
    _ ≤ (ENNReal.ofReal (εr / 3) + ENNReal.ofReal (εr / 3)) + ENNReal.ofReal (εr / 3) := houter
    _ ≤ ε := by
        have hsum : (εr / 3 + εr / 3) + εr / 3 = εr := by ring
        rw [← ENNReal.ofReal_add (by positivity : 0 ≤ εr / 3) (by positivity : 0 ≤ εr / 3),
          ← ENNReal.ofReal_add (by positivity : 0 ≤ εr / 3 + εr / 3) (by positivity : 0 ≤ εr / 3)]
        simp [hsum, εr, hε_top]

/-- Weak gradients of the same `W^{1,p}` function agree a.e. on the source open
set. -/
theorem MemW1pWitness.ae_eq_p
    {Ω : Set E} (hΩ : IsOpen Ω) {p : ℝ} (hp : 1 ≤ p) {f : E → ℝ}
    (hw₁ hw₂ : MemW1pWitness (ENNReal.ofReal p) f Ω) :
    hw₁.weakGrad =ᵐ[volume.restrict Ω] hw₂.weakGrad := by
  let _ := (inferInstance : NeZero d)
  have hp_enn : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    simpa using (ENNReal.ofReal_le_ofReal hp : ENNReal.ofReal (1 : ℝ) ≤ ENNReal.ofReal p)
  have hcomp :
      ∀ i : Fin d,
        (fun x => hw₁.weakGrad x i) =ᵐ[volume.restrict Ω] (fun x => hw₂.weakGrad x i) := by
    intro i
    exact HasWeakPartialDeriv.ae_eq hΩ (hw₁.isWeakGrad i) (hw₂.isWeakGrad i)
      ((hw₁.weakGrad_component_memLp i).locallyIntegrable hp_enn)
      ((hw₂.weakGrad_component_memLp i).locallyIntegrable hp_enn)
  filter_upwards [ae_all_iff.2 hcomp] with x hx
  ext i
  exact hx i

/-- Two `W^{1,2}` witnesses on an open set have a.e.-equal gradients. -/
theorem MemW1pWitness.ae_eq
    {Ω : Set E} (hΩ : IsOpen Ω) {f : E → ℝ}
    (hw₁ hw₂ : MemW1pWitness 2 f Ω) :
    hw₁.weakGrad =ᵐ[volume.restrict Ω] hw₂.weakGrad := by
  let _ := (inferInstance : NeZero d)
  have hp2 : (1 : ENNReal) ≤ 2 := by
    norm_num
  have hcomp :
      ∀ i : Fin d,
        (fun x => hw₁.weakGrad x i) =ᵐ[volume.restrict Ω] (fun x => hw₂.weakGrad x i) := by
    intro i
    exact HasWeakPartialDeriv.ae_eq hΩ (hw₁.isWeakGrad i) (hw₂.isWeakGrad i)
      ((hw₁.weakGrad_component_memLp i).locallyIntegrable hp2)
      ((hw₂.weakGrad_component_memLp i).locallyIntegrable hp2)
  filter_upwards [ae_all_iff.2 hcomp] with x hx
  ext i
  exact hx i

omit [NeZero d] in
private theorem convolution_fderiv_eq_convolution_weakPartial_univ
    {u g φ : E → ℝ} {i : Fin d}
    (hweak : HasWeakPartialDeriv i g u Set.univ)
    (hφ_smooth : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφ_compact : HasCompactSupport φ) :
    ∀ x,
      ((fun y => (fderiv ℝ φ y) (EuclideanSpace.single i 1))
          ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] u) x =
        (φ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x := by
  intro x
  let T : Homeomorph E E := (Homeomorph.neg E).trans (Homeomorph.addLeft x)
  let ψ : E → ℝ := φ ∘ T
  have hψ_smooth : ContDiff ℝ (⊤ : ℕ∞) ψ := by
    simpa [ψ, T, Function.comp, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
      hφ_smooth.comp (contDiff_const.add contDiff_id.neg)
  have hψ_compact : HasCompactSupport ψ := by
    simpa [ψ, T, Function.comp] using hφ_compact.comp_homeomorph T
  have key := hweak ψ hψ_smooth hψ_compact (by simp)
  have hderiv :
      ∀ t,
        (fderiv ℝ ψ t) (EuclideanSpace.single i 1) =
          - (fderiv ℝ φ (x + -t)) (EuclideanSpace.single i 1) := by
    intro t
    have hfd :
        HasFDerivAt ψ
          (((fderiv ℝ φ (x + -t)).comp ((0 : E →L[ℝ] E) - 1)) : E →L[ℝ] ℝ) t := by
      simpa [ψ, T, Function.comp, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
        ((hφ_smooth.differentiable
            (show (((⊤ : ℕ∞) : WithTop ℕ∞)) ≠ 0 by simp) (x + -t)).hasFDerivAt.comp t
          ((hasFDerivAt_const x t).add (hasFDerivAt_id t).neg))
    calc
      (fderiv ℝ ψ t) (EuclideanSpace.single i 1)
        = (((fderiv ℝ φ (x + -t)).comp ((0 : E →L[ℝ] E) - 1))
            (EuclideanSpace.single i 1)) := by
              rw [hfd.fderiv]
      _ = (fderiv ℝ φ (x + -t))
            (((0 : E →L[ℝ] E) - 1) (EuclideanSpace.single i 1)) := by
              rfl
      _ = (fderiv ℝ φ (x + -t)) (- EuclideanSpace.single i 1) := by
            simp
      _ = - (fderiv ℝ φ (x + -t)) (EuclideanSpace.single i 1) := by
            simp
  have hkey :
      ∫ t, g t * ψ t ∂volume =
        ∫ t, u t * (fderiv ℝ φ (x + -t)) (EuclideanSpace.single i 1) ∂volume := by
    have hkey' :
        ∫ t, u t * (fderiv ℝ ψ t) (EuclideanSpace.single i 1) ∂volume =
          -∫ t, g t * ψ t ∂volume := by
      simpa [Measure.restrict_univ] using key
    have hderiv_int :
        ∫ t, u t * (fderiv ℝ ψ t) (EuclideanSpace.single i 1) ∂volume =
          -∫ t, u t * (fderiv ℝ φ (x + -t)) (EuclideanSpace.single i 1) ∂volume := by
      calc
        ∫ t, u t * (fderiv ℝ ψ t) (EuclideanSpace.single i 1) ∂volume
          = ∫ t, -(u t * (fderiv ℝ φ (x + -t)) (EuclideanSpace.single i 1)) ∂volume := by
              refine integral_congr_ae ?_
              filter_upwards with t
              rw [hderiv t]
              ring
        _ = -∫ t, u t * (fderiv ℝ φ (x + -t)) (EuclideanSpace.single i 1) ∂volume := by
              rw [integral_neg]
    linarith
  calc
      ((fun y => (fderiv ℝ φ y) (EuclideanSpace.single i 1))
        ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] u) x
      = ∫ t, u t * (fderiv ℝ φ (x - t)) (EuclideanSpace.single i 1) ∂volume := by
          simpa [smul_eq_mul, mul_comm] using
            (MeasureTheory.convolution_lsmul_swap
              (f := fun y => (fderiv ℝ φ y) (EuclideanSpace.single i 1)) (g := u) (x := x)
              (μ := volume))
    _ = ∫ t, g t * ψ t ∂volume := hkey.symm
    _ = (φ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x := by
          simpa [ψ, T, Function.comp, sub_eq_add_neg, add_comm, add_left_comm, add_assoc,
            smul_eq_mul, mul_comm] using
            (MeasureTheory.convolution_lsmul_swap (f := φ) (g := g) (x := x) (μ := volume)).symm

/-- Global smooth compactly supported approximation of a compactly supported
`W^{1,p}` function on `ℝ^d`, in the finite-`p` regime. -/
theorem exists_smooth_compactSupport_W1p_approx_univ
    {p : ℝ} (hp : 1 < p)
    {u : E → ℝ}
    (hw : MemW1pWitness (ENNReal.ofReal p) u Set.univ)
    (hu_compact : HasCompactSupport u) :
    ∃ φ : ℕ → E → ℝ,
      (∀ n, ContDiff ℝ (⊤ : ℕ∞) (φ n)) ∧
      (∀ n, HasCompactSupport (φ n)) ∧
      (∀ n,
        tsupport (φ n) ⊆
          Metric.cthickening (shrinkingBump (d := d) n).rOut (tsupport u)) ∧
      Tendsto
        (fun n => eLpNorm (fun x => φ n x - u x) (ENNReal.ofReal p) volume)
        atTop (nhds 0) ∧
      (∀ i : Fin d,
        Tendsto
          (fun n =>
            eLpNorm
              (fun x => (fderiv ℝ (φ n) x) (EuclideanSpace.single i 1) - hw.weakGrad x i)
              (ENNReal.ofReal p) volume)
          atTop (nhds 0)) := by
  let _ := (inferInstance : NeZero d)
  have hp_le : 1 ≤ p := le_of_lt hp
  have hp_enn : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    simpa using (ENNReal.ofReal_le_ofReal hp_le : ENNReal.ofReal (1 : ℝ) ≤ ENNReal.ofReal p)
  have hu_memLp : MemLp u (ENNReal.ofReal p) volume := by
    simpa [Measure.restrict_univ] using hw.memLp
  let φ : ℕ → E → ℝ := fun n =>
    ((shrinkingBump (d := d) n).normed volume
      ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] u)
  refine ⟨φ, ?_, ?_, ?_, ?_, ?_⟩
  · intro n
    exact (shrinkingBump (d := d) n).hasCompactSupport_normed.contDiff_convolution_left
      (L := ContinuousLinearMap.lsmul ℝ ℝ)
      ((shrinkingBump (d := d) n).contDiff_normed)
      (hu_memLp.locallyIntegrable hp_enn)
  · intro n
    apply HasCompactSupport.intro'
      (K := Metric.cthickening (shrinkingBump (d := d) n).rOut (tsupport u))
      (hu_compact.isCompact.cthickening (r := (shrinkingBump (d := d) n).rOut))
      (hu_compact.isCompact.cthickening (r := (shrinkingBump (d := d) n).rOut)).isClosed
    intro x hx
    exact zero_outside_of_tsupport_subset
      (Ω := Metric.cthickening (shrinkingBump (d := d) n).rOut (tsupport u))
      (tsupport_normed_convolution_subset_cthickening
        (d := d) (shrinkingBump (d := d) n) hu_compact)
      hx
  · intro n
    exact tsupport_normed_convolution_subset_cthickening
      (d := d) (shrinkingBump (d := d) n) hu_compact
  · simpa [φ] using
      tendsto_eLpNorm_normedConvolution_sub (d := d) hp_le hu_memLp
  · intro i
    have hGi_memLp : MemLp (fun y => hw.weakGrad y i) (ENNReal.ofReal p) volume := by
      simpa [Measure.restrict_univ] using hw.weakGrad_component_memLp i
    have hEq :
        (fun n =>
          eLpNorm
            (fun x => (fderiv ℝ (φ n) x) (EuclideanSpace.single i 1) - hw.weakGrad x i)
            (ENNReal.ofReal p) volume) =
          fun n =>
            eLpNorm
              (fun x =>
                ((shrinkingBump (d := d) n).normed volume
                  ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (fun y => hw.weakGrad y i)) x -
                  hw.weakGrad x i)
              (ENNReal.ofReal p) volume := by
      funext n
      refine eLpNorm_congr_ae ?_
      filter_upwards with x
      let bump : E → ℝ := (shrinkingBump (d := d) n).normed volume
      let Dbump : E → E →L[ℝ] ℝ := fderiv ℝ bump
      let ei : E := EuclideanSpace.single i 1
      have hbump1 : ContDiff ℝ 1 bump := by
        simpa [bump] using
          ((shrinkingBump (d := d) n).contDiff_normed : ContDiff ℝ 1 ((shrinkingBump (d := d) n).normed volume))
      have hfd :=
        (shrinkingBump (d := d) n).hasCompactSupport_normed.hasFDerivAt_convolution_left
          (L := ContinuousLinearMap.lsmul ℝ ℝ)
          hbump1
          (hu_memLp.locallyIntegrable hp_enn) x
      have hDbump_cont : Continuous Dbump := by
        simpa [Dbump, bump] using hbump1.continuous_fderiv one_ne_zero
      have hDbump_compact : HasCompactSupport Dbump := by
        simpa [Dbump, bump] using ((shrinkingBump (d := d) n).hasCompactSupport_normed.fderiv (𝕜 := ℝ))
      have hfd' :
          (fderiv ℝ (φ n) x) ei =
            (((Dbump ⋆[
                ContinuousLinearMap.precompL E (ContinuousLinearMap.lsmul ℝ ℝ), volume] u) x)
                ei) := by
        simpa [φ, bump, Dbump, ei] using
          congrArg (fun A : E →L[ℝ] ℝ => A ei) hfd.fderiv
      have hconv_apply :
          (((Dbump ⋆[
              ContinuousLinearMap.precompL E (ContinuousLinearMap.lsmul ℝ ℝ), volume] u) x) ei) =
            (((fun y => (fderiv ℝ bump y) ei)
              ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] u) x) := by
        calc
          (((Dbump ⋆[
              ContinuousLinearMap.precompL E (ContinuousLinearMap.lsmul ℝ ℝ), volume] u) x) ei)
              =
            ((u ⋆[
              ContinuousLinearMap.precompR E (ContinuousLinearMap.lsmul ℝ ℝ).flip, volume] Dbump) x) ei := by
                simpa [ContinuousLinearMap.precompL, Dbump] using
                  congrArg (fun F => F x ei)
                    (MeasureTheory.convolution_flip
                      (L := ContinuousLinearMap.precompR E (ContinuousLinearMap.lsmul ℝ ℝ).flip)
                      (μ := volume) (f := u) (g := Dbump))
          _ = (u ⋆[(ContinuousLinearMap.lsmul ℝ ℝ).flip, volume] (fun y => Dbump y ei)) x := by
                simpa [Dbump, bump] using
                  (MeasureTheory.convolution_precompR_apply
                    (L := (ContinuousLinearMap.lsmul ℝ ℝ).flip)
                    (μ := volume) (f := u) (g := Dbump)
                    (hf := hu_memLp.locallyIntegrable hp_enn)
                    (hcg := hDbump_compact) (hg := hDbump_cont) (x₀ := x) (x := ei))
          _ = (((fun y => Dbump y ei) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] u) x) := by
                simpa [smul_eq_mul, mul_comm] using
                  congrArg (fun F => F x)
                    ((MeasureTheory.convolution_flip
                      (L := (ContinuousLinearMap.lsmul ℝ ℝ).flip)
                      (μ := volume) (f := u) (g := fun y => Dbump y ei)).symm)
      calc
        (fderiv ℝ (φ n) x) ei - hw.weakGrad x i
          = (((Dbump ⋆[
                ContinuousLinearMap.precompL E (ContinuousLinearMap.lsmul ℝ ℝ), volume] u) x)
                ei) - hw.weakGrad x i := by
                  rw [hfd']
        _ = (((fun y =>
              (fderiv ℝ bump y) ei)
                ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] u) x) - hw.weakGrad x i := by
                  rw [hconv_apply]
        _ = ((bump)
              ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (fun y => hw.weakGrad y i)) x -
                hw.weakGrad x i := by
                  simpa [ei] using
                    congrArg (fun z => z - hw.weakGrad x i)
                      (convolution_fderiv_eq_convolution_weakPartial_univ
                        (d := d) (i := i) (u := u) (g := fun y => hw.weakGrad y i)
                        (φ := bump)
                        (hw.isWeakGrad i)
                        (by
                          simpa [bump] using
                            ((shrinkingBump (d := d) n).contDiff_normed :
                              ContDiff ℝ (⊤ : ℕ∞) ((shrinkingBump (d := d) n).normed volume)))
                        ((shrinkingBump (d := d) n).hasCompactSupport_normed) x)
    exact hEq ▸ tendsto_eLpNorm_normedConvolution_sub (d := d) hp_le hGi_memLp

omit [NeZero d] in
private lemma fderiv_apply_eq_zero_of_eq_one_on_cthickening
    {K : Set E} {δ : ℝ} (hδ : 0 < δ)
    {η : E → ℝ}
    (hη_one : ∀ x ∈ Metric.cthickening δ K, η x = 1)
    {x : E} (hx : x ∈ K) (i : Fin d) :
    (fderiv ℝ η x) (EuclideanSpace.single i 1) = 0 := by
  have hη_eq : η =ᶠ[𝓝 x] fun _ => (1 : ℝ) := by
    refine Filter.mem_of_superset (Metric.ball_mem_nhds x (by linarith : 0 < δ / 2)) ?_
    intro y hy
    rw [Metric.mem_ball] at hy
    have hy_closed : y ∈ Metric.closedBall x (δ / 2) := by
      rw [Metric.mem_closedBall]
      exact le_of_lt hy
    have hy_cthick_half : y ∈ Metric.cthickening (δ / 2) K :=
      Metric.closedBall_subset_cthickening hx (δ / 2) hy_closed
    have hy_cthick : y ∈ Metric.cthickening δ K :=
      Metric.cthickening_mono (by linarith : δ / 2 ≤ δ) K hy_cthick_half
    exact hη_one y hy_cthick
  rw [Filter.EventuallyEq.fderiv_eq hη_eq]
  simp

omit [NeZero d] in
private theorem tsupport_mul_smooth_bounded_p_weakGrad_component_subset
    {p : ℝ≥0∞} (hp : 1 ≤ p)
    {Ω : Set E} (hΩ : IsOpen Ω)
    {u η : E → ℝ} (hw : MemW1pWitness p u Ω)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    {C₀ C₁ : ℝ}
    (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁)
    (hη_bound : ∀ x, |η x| ≤ C₀)
    (hη_grad_bound : ∀ x, ‖fderiv ℝ η x‖ ≤ C₁)
    (i : Fin d) :
    tsupport
        (fun x =>
          (MemW1pWitness.mul_smooth_bounded_p
            (d := d) (p := p) hp hΩ hw hη hC₀ hC₁ hη_bound hη_grad_bound).weakGrad x i) ⊆
      tsupport η := by
  have hfirst :
      tsupport (fun x => η x * hw.weakGrad x i) ⊆ tsupport η :=
    tsupport_mul_subset_left
  have hsecond :
      tsupport (fun x => (fderiv ℝ η x) (EuclideanSpace.single i 1) * u x) ⊆ tsupport η :=
    (tsupport_mul_subset_left :
      tsupport (fun x => (fderiv ℝ η x) (EuclideanSpace.single i 1) * u x) ⊆
        tsupport (fun x => (fderiv ℝ η x) (EuclideanSpace.single i 1))).trans <|
      (tsupport_fderiv_apply_subset ℝ (EuclideanSpace.single i 1)).trans subset_rfl
  simpa [MemW1pWitness.mul_smooth_bounded_p, PiLp.toLp_apply, smul_eq_mul] using
    (tsupport_add
      (fun x => η x * hw.weakGrad x i)
      (fun x => (fderiv ℝ η x) (EuclideanSpace.single i 1) * u x)).trans
      (union_subset hfirst hsecond)

-- Global smooth approximation for a local witness whose function and weak
-- gradient are already supported in a compact set inside the open domain.
set_option maxHeartbeats 1000000 in
theorem exists_smooth_W1p_approx_of_supportedWitness
    {Ω K : Set E} (hΩ : IsOpen Ω)
    {p : ℝ} (hp : 1 < p)
    {u : E → ℝ}
    (hw : MemW1pWitness (ENNReal.ofReal p) u Ω)
    (hK_compact : IsCompact K) (hKΩ : K ⊆ Ω)
    (hu_sub : tsupport u ⊆ K)
    (hgrad_sub : ∀ i : Fin d, tsupport (fun x => hw.weakGrad x i) ⊆ K) :
    ∃ φ : ℕ → E → ℝ,
      (∀ n, ContDiff ℝ (⊤ : ℕ∞) (φ n)) ∧
      (∀ n, HasCompactSupport (φ n)) ∧
      (∀ n, tsupport (φ n) ⊆ Ω) ∧
      Tendsto
        (fun n => eLpNorm (fun x => φ n x - u x) (ENNReal.ofReal p) (volume.restrict Ω))
        atTop (nhds 0) ∧
      (∀ i : Fin d,
        Tendsto
          (fun n =>
            eLpNorm
              (fun x => (fderiv ℝ (φ n) x) (EuclideanSpace.single i 1) - hw.weakGrad x i)
              (ENNReal.ofReal p) (volume.restrict Ω))
          atTop (nhds 0)) := by
  have hp_le : 1 ≤ p := le_of_lt hp
  have hK_compact_u : HasCompactSupport u := by
    apply HasCompactSupport.intro' (K := K) hK_compact hK_compact.isClosed
    intro x hx
    exact zero_outside_of_tsupport_subset (Ω := K) hu_sub hx
  obtain ⟨δ, hδ_pos, hδΩ⟩ := hK_compact.exists_cthickening_subset_open hΩ hKΩ
  let K' : Set E := Metric.cthickening δ K
  have hK'_compact : IsCompact K' := hK_compact.cthickening (r := δ)
  have hK'_Ω : K' ⊆ Ω := hδΩ
  obtain ⟨χ, hχ_smooth, hχ_compact, _hχ_range, hχ_one, hχ_sub⟩ :=
    exists_smooth_cutoff (d := d) hK'_compact hΩ hK'_Ω
  have hu_memLp_univ : MemLp u (ENNReal.ofReal p) volume := by
    have hu_eq_ind : Ω.indicator u = u := by
      ext x
      by_cases hx : x ∈ Ω
      · simp [hx]
      · simp [hx, zero_outside_of_tsupport_subset (Ω := Ω) (hu_sub.trans hKΩ) hx]
    rw [← hu_eq_ind]
    exact (MeasureTheory.memLp_indicator_iff_restrict
      (μ := volume) (s := Ω) (f := u) (p := ENNReal.ofReal p) hΩ.measurableSet).2 hw.memLp
  have hgrad_memLp_univ :
      ∀ i : Fin d, MemLp (fun x => hw.weakGrad x i) (ENNReal.ofReal p) volume := by
    intro i
    have hgi_eq_ind : Ω.indicator (fun x => hw.weakGrad x i) = fun x => hw.weakGrad x i := by
      ext x
      by_cases hx : x ∈ Ω
      · simp [hx]
      · simp [hx, zero_outside_of_tsupport_subset (Ω := Ω) (hgrad_sub i |>.trans hKΩ) hx]
    rw [← hgi_eq_ind]
    exact (MeasureTheory.memLp_indicator_iff_restrict
      (μ := volume) (s := Ω) (f := fun x => hw.weakGrad x i) (p := ENNReal.ofReal p)
      hΩ.measurableSet).2 (hw.weakGrad_component_memLp i)
  let hwUniv : MemW1pWitness (ENNReal.ofReal p) u Set.univ := by
    refine
      { memLp := by simpa [Measure.restrict_univ] using hu_memLp_univ
        weakGrad := hw.weakGrad
        weakGrad_component_memLp := by
          intro i
          simpa [Measure.restrict_univ] using hgrad_memLp_univ i
        isWeakGrad := ?_ }
    ·
      intro i φ hφ_smooth hφ_compact _hφ_sub
      let ψ : E → ℝ := fun x => χ x * φ x
      have hψ_smooth : ContDiff ℝ (⊤ : ℕ∞) ψ := hχ_smooth.mul hφ_smooth
      have hψ_compact : HasCompactSupport ψ := by
        simpa [ψ] using hχ_compact.mul_right (f' := φ)
      have hψ_sub : tsupport ψ ⊆ Ω := (tsupport_smul_subset_left χ φ).trans hχ_sub
      have key := hw.isWeakGrad i ψ hψ_smooth hψ_compact hψ_sub
      let ei : E := EuclideanSpace.single i 1
      have hχ_deriv_zero :
          ∀ x ∈ K, (fderiv ℝ χ x) ei = 0 := by
        intro x hx
        exact fderiv_apply_eq_zero_of_eq_one_on_cthickening
          (d := d) hδ_pos hχ_one hx i
      have hleft_pt :
          ∀ x,
            u x * (fderiv ℝ ψ x) ei =
              u x * (fderiv ℝ φ x) ei := by
        intro x
        by_cases hx : x ∈ K
        · have hχx : χ x = 1 := hχ_one x (Metric.self_subset_cthickening K hx)
          have hdχx : (fderiv ℝ χ x) ei = 0 := hχ_deriv_zero x hx
          have hχ_diff : Differentiable ℝ χ := hχ_smooth.differentiable (by simp)
          have hφ_diff : Differentiable ℝ φ := hφ_smooth.differentiable (by simp)
          rw [fderiv_fun_mul hχ_diff.differentiableAt hφ_diff.differentiableAt]
          simp [ei, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
            smul_eq_mul, hχx, hdχx]
        · have hux : u x = 0 := zero_outside_of_tsupport_subset (Ω := K) hu_sub hx
          simp [hux]
      have hright_pt :
          ∀ x,
            hw.weakGrad x i * ψ x =
              hw.weakGrad x i * φ x := by
        intro x
        by_cases hx : x ∈ K
        · have hχx : χ x = 1 := hχ_one x (Metric.self_subset_cthickening K hx)
          simp [ψ, hχx]
        · have hgx : hw.weakGrad x i = 0 :=
            zero_outside_of_tsupport_subset (Ω := K) (hgrad_sub i) hx
          simp [ψ, hgx]
      have hψ_deriv_sub : tsupport (fun x => (fderiv ℝ ψ x) ei) ⊆ Ω :=
        (tsupport_fderiv_apply_subset ℝ ei).trans hψ_sub
      have hleft_zero : ∀ x, x ∉ Ω → u x * (fderiv ℝ ψ x) ei = 0 := by
        intro x hx
        have hderivx : (fderiv ℝ ψ x) ei = 0 :=
          image_eq_zero_of_notMem_tsupport
            (f := fun y => (fderiv ℝ ψ y) ei) (fun h => hx (hψ_deriv_sub h))
        simp [hderivx]
      have hright_zero : ∀ x, x ∉ Ω → hw.weakGrad x i * ψ x = 0 := by
        intro x hx
        have hψx : ψ x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hψ_sub h))
        simp [hψx]
      have key_global :
          ∫ x, u x * (fderiv ℝ ψ x) ei ∂volume =
            -∫ x, hw.weakGrad x i * ψ x ∂volume := by
        rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hleft_zero,
          ← setIntegral_eq_integral_of_forall_compl_eq_zero hright_zero]
        simpa [Measure.restrict_univ] using key
      have hleft_global :
          ∫ x, u x * (fderiv ℝ ψ x) ei ∂volume =
            ∫ x, u x * (fderiv ℝ φ x) ei ∂volume := by
        refine integral_congr_ae ?_
        filter_upwards with x
        exact hleft_pt x
      have hright_global :
          ∫ x, hw.weakGrad x i * ψ x ∂volume =
            ∫ x, hw.weakGrad x i * φ x ∂volume := by
        refine integral_congr_ae ?_
        filter_upwards with x
        exact hright_pt x
      rw [hleft_global, hright_global] at key_global
      simpa [Measure.restrict_univ] using key_global
  rcases exists_smooth_compactSupport_W1p_approx_univ (d := d) hp hwUniv hK_compact_u with
    ⟨φ, hφ_smooth, hφ_compact, hφ_sup, hφ_fun, hφ_grad⟩
  have hsmall_lt :
      ∀ᶠ n in atTop, (shrinkingBump (d := d) n).rOut < δ := by
    exact (tendsto_order.1 (tendsto_shrinkingBump_rOut (d := d))).2 _ hδ_pos
  have hsmall :
      ∀ᶠ n in atTop, (shrinkingBump (d := d) n).rOut ≤ δ := by
    exact hsmall_lt.mono fun _ hn => hn.le
  rcases Filter.eventually_atTop.1 hsmall with ⟨N, hN⟩
  let ψ : ℕ → E → ℝ := fun n => φ (n + N)
  refine ⟨ψ, ?_, ?_, ?_, ?_, ?_⟩
  · intro n
    exact hφ_smooth (n + N)
  · intro n
    exact hφ_compact (n + N)
  · intro n
    have hle : (shrinkingBump (d := d) (n + N)).rOut ≤ δ := hN (n + N) (Nat.le_add_left _ _)
    exact (hφ_sup (n + N)).trans <|
      (Metric.cthickening_subset_of_subset (shrinkingBump (d := d) (n + N)).rOut hu_sub).trans <|
        (Metric.cthickening_mono hle K).trans hδΩ
  ·
    have hψ_fun_global :
        Tendsto
          (fun n => eLpNorm (fun x => ψ n x - u x) (ENNReal.ofReal p) volume)
          atTop (nhds 0) := by
      simpa [ψ] using hφ_fun.comp (tendsto_add_atTop_nat N)
    have hψ_fun_nonneg :
        ∀ n,
          (0 : ℝ≥0∞) ≤ eLpNorm (fun x => ψ n x - u x) (ENNReal.ofReal p) (volume.restrict Ω) :=
      fun n => zero_le _
    have hψ_fun_bound :
        ∀ n,
          eLpNorm (fun x => ψ n x - u x) (ENNReal.ofReal p) (volume.restrict Ω) ≤
            eLpNorm (fun x => ψ n x - u x) (ENNReal.ofReal p) volume :=
      fun n =>
        eLpNorm_mono_measure (f := fun x => ψ n x - u x) Measure.restrict_le_self
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds hψ_fun_global hψ_fun_nonneg hψ_fun_bound
  · intro i
    have hψ_grad_global :
        Tendsto
          (fun n =>
            eLpNorm
              (fun x => (fderiv ℝ (ψ n) x) (EuclideanSpace.single i 1) - hw.weakGrad x i)
              (ENNReal.ofReal p) volume)
          atTop (nhds 0) := by
      simpa [ψ] using (hφ_grad i).comp (tendsto_add_atTop_nat N)
    have hψ_grad_nonneg :
        ∀ n,
          (0 : ℝ≥0∞) ≤
            eLpNorm
              (fun x => (fderiv ℝ (ψ n) x) (EuclideanSpace.single i 1) - hw.weakGrad x i)
              (ENNReal.ofReal p) (volume.restrict Ω) :=
      fun n => zero_le _
    have hψ_grad_bound :
        ∀ n,
          eLpNorm
              (fun x => (fderiv ℝ (ψ n) x) (EuclideanSpace.single i 1) - hw.weakGrad x i)
              (ENNReal.ofReal p) (volume.restrict Ω) ≤
            eLpNorm
              (fun x => (fderiv ℝ (ψ n) x) (EuclideanSpace.single i 1) - hw.weakGrad x i)
              (ENNReal.ofReal p) volume :=
      fun n =>
        eLpNorm_mono_measure
          (f := fun x => (fderiv ℝ (ψ n) x) (EuclideanSpace.single i 1) - hw.weakGrad x i)
          Measure.restrict_le_self
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds hψ_grad_global hψ_grad_nonneg hψ_grad_bound

/-- Localization by compact support: a finite-`p` Sobolev function whose
support is compactly contained in an open set belongs to `W₀^{1,p}`. -/
theorem memW01p_of_memW1p_of_tsupport_subset
    {Ω : Set E} (hΩ : IsOpen Ω)
    {p : ℝ} (hp : 1 < p) {u : E → ℝ}
    (hu : MemW1p (ENNReal.ofReal p) u Ω)
    (hu_compact : HasCompactSupport u)
    (hu_sub : tsupport u ⊆ Ω) :
    MemW01p (ENNReal.ofReal p) u Ω := by
  have hp_enn : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    simpa using (ENNReal.ofReal_le_ofReal (le_of_lt hp) : ENNReal.ofReal (1 : ℝ) ≤ ENNReal.ofReal p)
  rcases hu with ⟨hu_memLp, hu_grad⟩
  choose g hg_memLp hg_weak using hu_grad
  let G : E → E := fun x => WithLp.toLp 2 fun i => g i x
  let hw : MemW1pWitness (ENNReal.ofReal p) u Ω :=
    { memLp := hu_memLp
      weakGrad := G
      weakGrad_component_memLp := hg_memLp
      isWeakGrad := hg_weak }
  obtain ⟨δ, hδ_pos, hδΩ⟩ := hu_compact.isCompact.exists_cthickening_subset_open hΩ hu_sub
  let K : Set E := Metric.cthickening δ (tsupport u)
  have hK_compact : IsCompact K := hu_compact.isCompact.cthickening (r := δ)
  have hKΩ : K ⊆ Ω := hδΩ
  obtain ⟨η, hη_smooth, hη_compact, hη_range, hη_one, hη_sub⟩ :=
    exists_smooth_cutoff (d := d) hK_compact hΩ hKΩ
  have hη_bound : ∀ x, |η x| ≤ 1 := by
    intro x
    rcases hη_range ⟨x, rfl⟩ with ⟨hx0, hx1⟩
    rw [abs_of_nonneg hx0]
    exact hx1
  have hη_fderiv_compact : HasCompactSupport (fderiv ℝ η) := hη_compact.fderiv (𝕜 := ℝ)
  obtain ⟨Cη, hCη⟩ := hη_fderiv_compact.isCompact.exists_bound_of_continuousOn
    ((hη_smooth.continuous_fderiv (by simp)).continuousOn)
  let C₁ : ℝ := max Cη 0
  have hC₁_nonneg : 0 ≤ C₁ := le_max_right _ _
  have hη_grad_bound : ∀ x, ‖fderiv ℝ η x‖ ≤ C₁ := by
    intro x
    by_cases hx : x ∈ tsupport (fderiv ℝ η)
    · exact (hCη x hx).trans (le_max_left _ _)
    · have hzero : fderiv ℝ η x = 0 := image_eq_zero_of_notMem_tsupport hx
      simp [C₁, hzero]
  let v : E → ℝ := fun x => η x * u x
  let hwCut :=
    MemW1pWitness.mul_smooth_bounded_p
      (d := d) (p := ENNReal.ofReal p) hp_enn hΩ hw hη_smooth
      zero_le_one hC₁_nonneg hη_bound hη_grad_bound
  have hv_eq_u : v = u := by
    funext x
    by_cases hx : x ∈ tsupport u
    · have hηx : η x = 1 := hη_one x (Metric.self_subset_cthickening (tsupport u) hx)
      simp [v, hηx]
    · have hux : u x = 0 := image_eq_zero_of_notMem_tsupport hx
      simp [v, hux]
  have hv_sub : tsupport v ⊆ tsupport η := tsupport_smul_subset_left η u
  have hgrad_sub :
      ∀ i : Fin d, tsupport (fun x => hwCut.weakGrad x i) ⊆ tsupport η := by
    intro i
    exact tsupport_mul_smooth_bounded_p_weakGrad_component_subset
      (d := d) (p := ENNReal.ofReal p) hp_enn hΩ hw hη_smooth zero_le_one hC₁_nonneg hη_bound
      hη_grad_bound i
  rcases exists_smooth_W1p_approx_of_supportedWitness
      (d := d) (Ω := Ω) (K := tsupport η) hΩ hp hwCut
      hη_compact.isCompact hη_sub hv_sub hgrad_sub with
    ⟨φ, hφ_smooth, hφ_compact, hφ_sub, hφ_fun, hφ_grad⟩
  simpa [v, hv_eq_u] using
    memW01p_of_global_approx_supported hwCut φ hφ_smooth hφ_compact hφ_sub hφ_fun hφ_grad

/-- Whole-space Sobolev inequality specialized to the `MemW₀^{1,p}` data
already stored in the `MemW₀^{1,p}` witness predicate. -/
theorem sobolev_of_memW01p_univ
    {p : ℝ} (hp : 1 ≤ p) (hpd : p < (d : ℝ))
    {u : E → ℝ}
    (hu : MemW01p (ENNReal.ofReal p) u Set.univ volume) :
    ∃ hw : MemW1pWitness (ENNReal.ofReal p) u Set.univ volume,
      eLpNorm u (ENNReal.ofReal ((d : ℝ) * p / ((d : ℝ) - p))) volume ≤
        ENNReal.ofReal (C_gns d p) *
          eLpNorm (fun x => ‖hw.weakGrad x‖) (ENNReal.ofReal p) volume := by
  rcases hu with ⟨_, hw, φ, hφ_smooth, hφ_cpt, _hφ_sub, hφ_fun, hφ_grad⟩
  refine ⟨hw, ?_⟩
  have hu_aesm : AEStronglyMeasurable u volume := by
    simpa using hw.memLp.aestronglyMeasurable
  have hG_comp_aesm : ∀ i : Fin d,
      AEStronglyMeasurable (fun x => hw.weakGrad x i) volume := by
    intro i
    simpa using (hw.weakGrad_component_memLp i).aestronglyMeasurable
  have hφ_fun_univ :
      Tendsto (fun n => eLpNorm (fun x => φ n x - u x) (ENNReal.ofReal p) volume)
        atTop (nhds 0) := by
    simpa using hφ_fun
  have hφ_grad_univ : ∀ i : Fin d, Tendsto
      (fun n => eLpNorm
        (fun x => (fderiv ℝ (φ n) x) (EuclideanSpace.single i 1) - hw.weakGrad x i)
        (ENNReal.ofReal p) volume)
      atTop (nhds 0) := by
    intro i
    simpa using hφ_grad i
  simpa [eLpNorm_norm] using
    sobolev_of_approx hp hpd hu_aesm hG_comp_aesm φ
      hφ_smooth hφ_cpt hφ_fun_univ hφ_grad_univ


end DeGiorgi
