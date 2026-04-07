import DeGiorgi.DeGiorgiIteration.Energy

/-!
# De Giorgi Iteration: Pre-Iteration

This module contains the PDE-facing pre-iteration stage that sits between the
energy estimates and the recurrence / Linfty assembly.
-/

noncomputable section

open MeasureTheory Metric Filter Topology Set Function Matrix
open scoped ENNReal NNReal

namespace DeGiorgi

section PreiterationPDE

variable {d : ℕ} [NeZero d]

local notation "E" => AmbientSpace d

omit [NeZero d] in
private lemma exists_fderiv_bound_of_contDiff_hasCompactSupport
    {η : E → ℝ}
    (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hη_comp : HasCompactSupport η) :
    ∃ Cη : ℝ, 0 ≤ Cη ∧ ∀ x, ‖fderiv ℝ η x‖ ≤ Cη := by
  obtain ⟨Cη, hCη⟩ :=
    (hη_comp.fderiv (𝕜 := ℝ)).exists_bound_of_continuous
      (hη.continuous_fderiv (by simp : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0))
  refine ⟨max Cη 0, le_max_right _ _, ?_⟩
  intro x
  exact le_trans (hCη x) (le_max_left _ _)

/-- PDE-facing De Giorgi pre-iteration wrapper on concentric balls.

This theorem packages the bookkeeping step that combines:

- a localized De Giorgi energy estimate at level `θ`,
- a Sobolev/Hölder interpolation input for level `λ`,
- and the Chebyshev bound already proved in this chapter.

The local Sobolev/Hölder interpolation theorem is kept as an explicit
hypothesis `hsob`; it can be discharged by a dedicated local Sobolev theorem
without changing the statement itself. -/
theorem deGiorgi_preiter_of_ballSobolev_on_concentricBalls_of_ballPosPart
    {u η : E → ℝ} {x₀ : E} {r s θ lam Csob Cη : ℝ}
    (hd : 0 < (d : ℝ))
    (A : EllipticCoeff d (Metric.ball x₀ s))
    (hr : 0 < r) (hrs : r < s)
    (hθl : θ < lam)
    (hCsob : 0 ≤ Csob)
    (hsub : IsSubsolution A u)
    (hu : MemW1pWitness 2 u (Metric.ball x₀ s))
    (hwθ : MemW1pWitness 2 (positivePartSub u θ) (Metric.ball x₀ s))
    (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hη_nonneg : ∀ x, 0 ≤ η x)
    (hη_eq_one : ∀ x ∈ Metric.ball x₀ r, η x = 1)
    (hη_bound : ∀ x, |η x| ≤ 1)
    (hCη : 0 ≤ Cη)
    (hη_grad_bound : ∀ x, ‖fderiv ℝ η x‖ ≤ Cη)
    (hη_sub_ball : tsupport η ⊆ Metric.ball x₀ s)
    (hsob :
      ∫ x in Metric.ball x₀ r, |positivePartSub u lam x| ^ 2 ∂volume ≤
        Csob * (∫ x in Metric.ball x₀ r, ‖hwθ.weakGrad x‖ ^ 2 ∂volume) *
          ((volume.restrict (Metric.ball x₀ s)).real {x | lam < u x}) ^ (2 / (d : ℝ))) :
    ∫ x in Metric.ball x₀ r, |positivePartSub u lam x| ^ 2 ∂volume ≤
      Csob * (4 * ellipticityRatio A * Cη ^ 2) *
        ((((lam - θ) ^ 2)⁻¹ *
            ∫ x in Metric.ball x₀ s, |positivePartSub u θ x| ^ 2 ∂volume) ^ (2 / (d : ℝ))) *
          ∫ x in Metric.ball x₀ s, |positivePartSub u θ x| ^ 2 ∂volume := by
  haveI : IsFiniteMeasure (volume.restrict (Metric.ball x₀ s)) := by
    rw [isFiniteMeasure_restrict]
    exact measure_ball_lt_top.ne
  have hθ_int :
      Integrable (fun x => |positivePartSub u θ x| ^ 2)
        (volume.restrict (Metric.ball x₀ s)) := by
    simpa [pow_two] using hwθ.memLp.integrable_sq
  have hIθ_nonneg :
      0 ≤ ∫ x in Metric.ball x₀ s, |positivePartSub u θ x| ^ 2 ∂volume := by
    refine integral_nonneg ?_
    intro x
    positivity
  have henergy :
      ∫ x in Metric.ball x₀ r, ‖hwθ.weakGrad x‖ ^ 2 ∂volume ≤
        (4 * ellipticityRatio A * Cη ^ 2) *
          ∫ x in Metric.ball x₀ s, |positivePartSub u θ x| ^ 2 ∂volume := by
    simpa using
      deGiorgi_energy_estimate_on_concentricBalls_of_ballPosPart
        A hr hrs hsub hu hwθ hη hη_nonneg hη_eq_one hη_bound hCη
        hη_grad_bound hη_sub_ball
  exact
    deGiorgi_preiter_of_energy
      (μ := volume.restrict (Metric.ball x₀ s))
      hd hθl hCsob
      (by
        have hRatio_nonneg : 0 ≤ ellipticityRatio A := A.ellipticityRatio_nonneg
        have hCη_sq_nonneg : 0 ≤ Cη ^ 2 := sq_nonneg Cη
        nlinarith)
      hIθ_nonneg hθ_int
      hsob henergy
      (by rfl)

/-- De Giorgi pre-iteration on concentric balls using the concrete
positive-part witness constructor on the outer ball. -/
theorem deGiorgi_preiter_of_ballSobolev_on_concentricBalls_of_posPartApprox
    {u η : E → ℝ} {x₀ : E} {r s θ lam Csob Cη : ℝ}
    (hd : 0 < (d : ℝ))
    (A : EllipticCoeff d (Metric.ball x₀ s))
    (hs : 0 < s) (hr : 0 < r) (hrs : r < s)
    (hθl : θ < lam)
    (hCsob : 0 ≤ Csob)
    (hsub : IsSubsolution A u)
    (hu : MemW1pWitness 2 u (Metric.ball x₀ s))
    (happroxBallTheta :
      ∃ ψ : ℕ → E → ℝ,
        (∀ n, ContDiff ℝ 1 (ψ n)) ∧
        (∀ n, HasCompactSupport (ψ n)) ∧
        Tendsto
          (fun n =>
            eLpNorm (fun x => ψ n x - (u x - θ)) 2
              (volume.restrict (Metric.ball x₀ s)))
          atTop (nhds 0) ∧
        (∀ i : Fin d,
          Tendsto
            (fun n =>
              eLpNorm
                (fun x =>
                  (fderiv ℝ (ψ n) x) (EuclideanSpace.single i 1) - hu.weakGrad x i)
                2 (volume.restrict (Metric.ball x₀ s)))
            atTop (nhds 0)))
    (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hη_nonneg : ∀ x, 0 ≤ η x)
    (hη_eq_one : ∀ x ∈ Metric.ball x₀ r, η x = 1)
    (hη_bound : ∀ x, |η x| ≤ 1)
    (hCη : 0 ≤ Cη)
    (hη_grad_bound : ∀ x, ‖fderiv ℝ η x‖ ≤ Cη)
    (hη_sub_ball : tsupport η ⊆ Metric.ball x₀ s)
    (hsob :
      ∫ x in Metric.ball x₀ r, |positivePartSub u lam x| ^ 2 ∂volume ≤
        Csob *
          (∫ x in Metric.ball x₀ r,
            ‖(positivePartSub_memW1pWitness_on_ball hs hu θ happroxBallTheta).weakGrad x‖ ^ 2
              ∂volume) *
          ((volume.restrict (Metric.ball x₀ s)).real {x | lam < u x}) ^ (2 / (d : ℝ))) :
    ∫ x in Metric.ball x₀ r, |positivePartSub u lam x| ^ 2 ∂volume ≤
      Csob * (4 * ellipticityRatio A * Cη ^ 2) *
        ((((lam - θ) ^ 2)⁻¹ *
            ∫ x in Metric.ball x₀ s, |positivePartSub u θ x| ^ 2 ∂volume) ^ (2 / (d : ℝ))) *
          ∫ x in Metric.ball x₀ s, |positivePartSub u θ x| ^ 2 ∂volume := by
  haveI : IsFiniteMeasure (volume.restrict (Metric.ball x₀ s)) := by
    rw [isFiniteMeasure_restrict]
    exact measure_ball_lt_top.ne
  let hwTheta : MemW1pWitness 2 (positivePartSub u θ) (Metric.ball x₀ s) :=
    positivePartSub_memW1pWitness_on_ball hs hu θ happroxBallTheta
  have hθ_int :
      Integrable (fun x => |positivePartSub u θ x| ^ 2)
        (volume.restrict (Metric.ball x₀ s)) := by
    simpa [pow_two] using hwTheta.memLp.integrable_sq
  have hIθ_nonneg :
      0 ≤ ∫ x in Metric.ball x₀ s, |positivePartSub u θ x| ^ 2 ∂volume := by
    refine integral_nonneg ?_
    intro x
    positivity
  have henergy :
      ∫ x in Metric.ball x₀ r, ‖hwTheta.weakGrad x‖ ^ 2 ∂volume ≤
        (4 * ellipticityRatio A * Cη ^ 2) *
          ∫ x in Metric.ball x₀ s, |positivePartSub u θ x| ^ 2 ∂volume := by
    change
      ∫ x in Metric.ball x₀ r, ‖hwTheta.weakGrad x‖ ^ 2 ∂volume ≤
        (4 * ellipticityRatio A * Cη ^ 2) *
          ∫ x in Metric.ball x₀ s, |positivePartSub u θ x| ^ 2 ∂volume
    exact
      deGiorgi_energy_estimate_on_concentricBalls_of_posPartApprox
        A hs hr hrs hsub hu happroxBallTheta hη hη_nonneg hη_eq_one
        hη_bound hCη hη_grad_bound hη_sub_ball
  have hsob' :
      ∫ x in Metric.ball x₀ r, |positivePartSub u lam x| ^ 2 ∂volume ≤
        Csob * (∫ x in Metric.ball x₀ r, ‖hwTheta.weakGrad x‖ ^ 2 ∂volume) *
          ((volume.restrict (Metric.ball x₀ s)).real {x | lam < u x}) ^ (2 / (d : ℝ)) := by
    change
      ∫ x in Metric.ball x₀ r, |positivePartSub u lam x| ^ 2 ∂volume ≤
        Csob * (∫ x in Metric.ball x₀ r, ‖hwTheta.weakGrad x‖ ^ 2 ∂volume) *
          ((volume.restrict (Metric.ball x₀ s)).real {x | lam < u x}) ^ (2 / (d : ℝ))
    exact hsob
  exact
    deGiorgi_preiter_of_energy
      (μ := volume.restrict (Metric.ball x₀ s))
      hd hθl hCsob
      (by
        have hRatio_nonneg : 0 ≤ ellipticityRatio A := A.ellipticityRatio_nonneg
        have hCη_sq_nonneg : 0 ≤ Cη ^ 2 := sq_nonneg Cη
        nlinarith)
      hIθ_nonneg hθ_int
      hsob' henergy
      (by rfl)

private theorem deGiorgi_cutoffSobolev_prepare
    {u η : E → ℝ} {x₀ : E} {s θ : ℝ}
    (hd : 2 < (d : ℝ))
    (_hs : 0 < s)
    (_hu : MemW1pWitness 2 u (Metric.ball x₀ s))
    (_hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (_hη_bound : ∀ x, |η x| ≤ 1)
    (hη_sub_ball : tsupport η ⊆ Metric.ball x₀ s)
    (hvW01 :
      MemW01p 2 (deGiorgiCutoffTestGeneral η u θ) (Metric.ball x₀ s)) :
    ∃ hwηθ_real :
      MemW1pWitness (ENNReal.ofReal (2 : ℝ))
        (deGiorgiCutoffTestGeneral η u θ) (Metric.ball x₀ s),
      eLpNorm (deGiorgiCutoffTestGeneral η u θ)
          (ENNReal.ofReal ((d : ℝ) * 2 / ((d : ℝ) - 2)))
          (volume.restrict (Metric.ball x₀ s)) ≤
        ENNReal.ofReal (C_gns d 2) *
          eLpNorm (fun x => ‖hwηθ_real.weakGrad x‖) 2
            (volume.restrict (Metric.ball x₀ s)) := by
  classical
  let Ω : Set E := Metric.ball x₀ s
  let μ : Measure E := volume.restrict Ω
  let v : E → ℝ := deGiorgiCutoffTestGeneral η u θ
  have hΩ_open : IsOpen Ω := isOpen_ball
  have hΩ_meas : MeasurableSet Ω := measurableSet_ball
  haveI : IsFiniteMeasure μ := by
    dsimp [μ, Ω]
    rw [isFiniteMeasure_restrict]
    exact measure_ball_lt_top.ne
  have hη_comp : HasCompactSupport η :=
    hasCompactSupport_of_tsupport_subset_ball hη_sub_ball
  let hwηθ : MemW1pWitness 2 v Ω := Classical.choose hvW01.2
  have hv_tsupport : tsupport v ⊆ Ω :=
    deGiorgiCutoffTestGeneral_tsupport_subset hη_sub_ball
  have hv_comp : HasCompactSupport v :=
    deGiorgiCutoffTestGeneral_hasCompactSupport hη_comp
  have hv_indicator_eq : Ω.indicator v = v := by
    ext x
    by_cases hx : x ∈ Ω
    · simp [hx]
    · have hvx0 : v x = 0 := by
        apply eq_zero_of_not_mem_tsupport
        intro hxt
        exact hx (hv_tsupport hxt)
      simp [hx, hvx0]
  have hvW01_real : MemW01p (ENNReal.ofReal (2 : ℝ)) v Ω := by
    simpa using hvW01
  have hwηθ_real : MemW1pWitness (ENNReal.ofReal (2 : ℝ)) v Ω := by
    simpa using hwηθ
  let hwηθ_univ_raw :
      MemW1pWitness (ENNReal.ofReal (2 : ℝ)) (Ω.indicator v) Set.univ :=
    zeroExtend_memW1pWitness_p (d := d) hΩ_open (p := 2) (by norm_num) hvW01_real hwηθ_real
  let hwηθ_univ : MemW1pWitness (ENNReal.ofReal (2 : ℝ)) v Set.univ :=
    { memLp := by
        simpa [hv_indicator_eq] using hwηθ_univ_raw.memLp
      weakGrad := hwηθ_univ_raw.weakGrad
      weakGrad_component_memLp := hwηθ_univ_raw.weakGrad_component_memLp
      isWeakGrad := by
        simpa [hv_indicator_eq] using hwηθ_univ_raw.isWeakGrad }
  have hvW01_univ : MemW01p (ENNReal.ofReal (2 : ℝ)) v Set.univ := by
    simpa [hv_indicator_eq] using
      zeroExtend_memW01p_p (d := d) hΩ_open (p := 2) (by norm_num) hvW01_real
  let q : ℝ≥0∞ := ENNReal.ofReal ((d : ℝ) * 2 / ((d : ℝ) - 2))
  obtain ⟨hwSob, hSob⟩ :=
    sobolev_of_memW01p_univ (d := d) (p := 2) (u := v) (by norm_num) hd hvW01_univ
  have hae_grad :
      hwSob.weakGrad =ᵐ[volume] hwηθ_univ.weakGrad := by
    simpa [Measure.restrict_univ] using
      MemW1pWitness.ae_eq_p (d := d) isOpen_univ (p := 2) (by norm_num) hwSob hwηθ_univ
  have hSob' :
      eLpNorm v q volume ≤
        ENNReal.ofReal (C_gns d 2) *
          eLpNorm (fun x => ‖hwηθ_univ.weakGrad x‖) 2 volume := by
    calc
      eLpNorm v q volume
          ≤ ENNReal.ofReal (C_gns d 2) *
              eLpNorm (fun x => ‖hwSob.weakGrad x‖) 2 volume := by
                simpa [q] using hSob
      _ = ENNReal.ofReal (C_gns d 2) *
            eLpNorm (fun x => ‖hwηθ_univ.weakGrad x‖) 2 volume := by
          congr 1
          exact eLpNorm_congr_ae (hae_grad.fun_comp (‖·‖))
  have hgrad_ext_vec :
      hwηθ_univ.weakGrad = Ω.indicator hwηθ_real.weakGrad := by
    ext x i
    by_cases hx : x ∈ Ω
    · simp [hwηθ_univ, hwηθ_univ_raw, zeroExtend_memW1pWitness_p, hx]
    · simp [hwηθ_univ, hwηθ_univ_raw, zeroExtend_memW1pWitness_p, hx]
  have hgrad_ext :
      (fun x => ‖hwηθ_univ.weakGrad x‖) = Ω.indicator (fun x => ‖hwηθ_real.weakGrad x‖) := by
    ext x
    by_cases hx : x ∈ Ω
    · simp [hgrad_ext_vec, hx]
    · simp [hgrad_ext_vec, hx]
  have hgrad_restrict :
      eLpNorm (fun x => ‖hwηθ_univ.weakGrad x‖) 2 volume =
        eLpNorm (fun x => ‖hwηθ_real.weakGrad x‖) 2 μ := by
    rw [hgrad_ext, MeasureTheory.eLpNorm_indicator_eq_eLpNorm_restrict hΩ_meas]
  have hv_support : Function.support v ⊆ Ω := by
    intro x hx
    exact hv_tsupport (subset_tsupport _ hx)
  have hv_restrict :
      eLpNorm v q μ = eLpNorm v q volume := by
    simpa [μ] using
      (MeasureTheory.eLpNorm_restrict_eq_of_support_subset (μ := volume) (p := q) hv_support)
  have hSob'' :
      eLpNorm v q μ ≤
        ENNReal.ofReal (C_gns d 2) * eLpNorm (fun x => ‖hwηθ_real.weakGrad x‖) 2 μ := by
    calc
      eLpNorm v q μ = eLpNorm v q volume := hv_restrict
      _ ≤ ENNReal.ofReal (C_gns d 2) *
            eLpNorm (fun x => ‖hwηθ_univ.weakGrad x‖) 2 volume := hSob'
      _ = ENNReal.ofReal (C_gns d 2) * eLpNorm (fun x => ‖hwηθ_real.weakGrad x‖) 2 μ := by
            rw [hgrad_restrict]
  exact ⟨hwηθ_real, hSob''⟩

private theorem deGiorgi_cutoffSobolev_superlevelStep
    {u η : E → ℝ} {x₀ : E} {r s θ lam : ℝ}
    (hd : 2 < (d : ℝ))
    (_hr : 0 < r) (hrs : r < s)
    (hu : MemW1pWitness 2 u (Metric.ball x₀ s))
    (hwθ : MemW1pWitness 2 (positivePartSub u θ) (Metric.ball x₀ s))
    (hθl : θ < lam)
    (hη_eq_one : ∀ x ∈ Metric.ball x₀ r, η x = 1)
    (hwηθ_real :
      MemW1pWitness (ENNReal.ofReal (2 : ℝ))
        (deGiorgiCutoffTestGeneral η u θ) (Metric.ball x₀ s))
    (hSob'' :
      eLpNorm (deGiorgiCutoffTestGeneral η u θ)
          (ENNReal.ofReal ((d : ℝ) * 2 / ((d : ℝ) - 2)))
          (volume.restrict (Metric.ball x₀ s)) ≤
        ENNReal.ofReal (C_gns d 2) *
          eLpNorm (fun x => ‖hwηθ_real.weakGrad x‖) 2
            (volume.restrict (Metric.ball x₀ s))) :
    ∫ x in Metric.ball x₀ r, |positivePartSub u lam x| ^ 2 ∂volume ≤
      (C_gns d 2) ^ 2 *
        (∫ x in Metric.ball x₀ s, ‖hwηθ_real.weakGrad x‖ ^ 2 ∂volume) *
        ((volume.restrict (Metric.ball x₀ s)).real {x | lam < u x}) ^ (2 / (d : ℝ)) := by
  classical
  let Ω : Set E := Metric.ball x₀ s
  let B : Set E := Metric.ball x₀ r
  let μ : Measure E := volume.restrict Ω
  let S : Set E := {x | lam < u x}
  let T : Set E := toMeasurable μ S
  let v : E → ℝ := deGiorgiCutoffTestGeneral η u θ
  let q : ℝ≥0∞ := ENNReal.ofReal ((d : ℝ) * 2 / ((d : ℝ) - 2))
  have hB_meas : MeasurableSet B := measurableSet_ball
  have hBsubΩ : B ⊆ Ω := Metric.ball_subset_ball (le_of_lt hrs)
  haveI : IsFiniteMeasure μ := by
    dsimp [μ, Ω]
    rw [isFiniteMeasure_restrict]
    exact measure_ball_lt_top.ne
  have hT_meas : MeasurableSet T := measurableSet_toMeasurable μ S
  have hSsubT : S ⊆ T := subset_toMeasurable μ S
  let g : E → ℝ := fun x => |v x| ^ 2
  have hwηθ_memLp2 : MemLp v 2 μ := by
    simpa using hwηθ_real.memLp
  have hgrad_memLp2 : MemLp (fun x => ‖hwηθ_real.weakGrad x‖) 2 μ := by
    simpa using hwηθ_real.weakGrad_norm_memLp
  have hθ_int_B :
      IntegrableOn (fun x => |positivePartSub u θ x| ^ 2) B volume := by
    simpa [B, pow_two] using (hwθ.restrict isOpen_ball hBsubΩ).memLp.integrable_sq
  have hlam_sq_aesm :
      AEStronglyMeasurable (fun x => |positivePartSub u lam x| ^ 2) (volume.restrict B) := by
    have huB_meas :
        AEMeasurable u (volume.restrict B) := by
      exact (hu.restrict isOpen_ball hBsubΩ).memLp.aestronglyMeasurable.aemeasurable
    have hlam_meas :
        AEMeasurable (fun x => positivePartSub u lam x) (volume.restrict B) := by
      simpa [positivePartSub] using
        (huB_meas.sub_const lam).max measurable_const.aemeasurable
    simpa [Real.norm_eq_abs] using (hlam_meas.norm.pow_const (2 : ℕ)).aestronglyMeasurable
  have hleft_int :
      IntegrableOn (fun x => |positivePartSub u lam x| ^ 2) B volume := by
    refine Integrable.mono' hθ_int_B hlam_sq_aesm ?_
    filter_upwards with x
    have hmono : positivePartSub u lam x ≤ positivePartSub u θ x := by
      dsimp [positivePartSub]
      exact max_le_max (by linarith) le_rfl
    have hlam_nonneg : 0 ≤ positivePartSub u lam x := positivePartSub_nonneg
    have hθ_nonneg : 0 ≤ positivePartSub u θ x := positivePartSub_nonneg
    have hsq :
        |positivePartSub u lam x| ^ 2 ≤ |positivePartSub u θ x| ^ 2 := by
      rw [abs_of_nonneg hlam_nonneg, abs_of_nonneg hθ_nonneg]
      nlinarith
    have hlam_sq_nonneg : 0 ≤ |positivePartSub u lam x| ^ 2 := by positivity
    simpa [Real.norm_eq_abs, abs_of_nonneg hlam_sq_nonneg] using hsq
  have hg_int :
      IntegrableOn g Ω volume := by
    simpa [g, pow_two] using hwηθ_memLp2.integrable_sq
  have hgT_int :
      IntegrableOn (T.indicator g) Ω volume := hg_int.indicator hT_meas
  have hpoint :
      ∀ x ∈ B, |positivePartSub u lam x| ^ 2 ≤ T.indicator g x := by
    intro x hxB
    by_cases hxl : lam < u x
    · have hxT : x ∈ T := hSsubT hxl
      have hηx : η x = 1 := hη_eq_one x hxB
      have hvx : v x = positivePartSub u θ x := by
        simp [v, deGiorgiCutoffTestGeneral, hηx]
      have hmono : positivePartSub u lam x ≤ positivePartSub u θ x := by
        dsimp [positivePartSub]
        gcongr
      have hlam_nonneg : 0 ≤ positivePartSub u lam x := positivePartSub_nonneg
      have hθ_nonneg : 0 ≤ positivePartSub u θ x := positivePartSub_nonneg
      have hsq :
          |positivePartSub u lam x| ^ 2 ≤ |v x| ^ 2 := by
        rw [hvx, abs_of_nonneg hlam_nonneg, abs_of_nonneg hθ_nonneg]
        nlinarith [hmono]
      simpa [g, hxT] using hsq
    · have hzero : positivePartSub u lam x = 0 := by
        have hux : u x - lam ≤ 0 := by linarith
        simp [positivePartSub, max_eq_right hux]
      by_cases hxT : x ∈ T
      · simp [g, hxT, hzero]
        exact sq_nonneg (v x)
      · simp [g, hxT, hzero]
  have hT_nonneg : ∀ x, 0 ≤ T.indicator g x := by
    intro x
    by_cases hxT : x ∈ T
    · simp [g, hxT]
      exact sq_nonneg (v x)
    · simp [g, hxT]
  have hleft_le_T :
      ∫ x in B, |positivePartSub u lam x| ^ 2 ∂volume ≤
        ∫ x in Ω, T.indicator g x ∂volume := by
    have hmonoB :
        ∫ x in B, |positivePartSub u lam x| ^ 2 ∂volume ≤
          ∫ x in B, T.indicator g x ∂volume := by
      refine integral_mono_ae hleft_int (hgT_int.mono_set hBsubΩ) ?_
      refine (ae_restrict_iff' (μ := volume) hB_meas).2 ?_
      filter_upwards with x hx
      exact hpoint x hx
    calc
      ∫ x in B, |positivePartSub u lam x| ^ 2 ∂volume ≤
          ∫ x in B, T.indicator g x ∂volume := hmonoB
      _ ≤ ∫ x in Ω, T.indicator g x ∂volume :=
        setIntegral_mono_set hgT_int (ae_of_all _ hT_nonneg) (ae_of_all _ hBsubΩ)
  have hμT_real :
      (μ.restrict T).real Set.univ = μ.real S := by
    rw [measureReal_restrict_apply_univ]
    exact (measureReal_eq_measureReal_iff (μ := μ) (ν := μ) (s := T) (t := S)).2
      (measure_toMeasurable (μ := μ) S)
  have hq_gt_two : 2 < (d : ℝ) * 2 / ((d : ℝ) - 2) := by
    have hd' : 0 < (d : ℝ) - 2 := by linarith
    have hd0 : 0 < (d : ℝ) := by linarith
    field_simp [hd0.ne', hd'.ne]
    nlinarith
  have htwo_le_q : (2 : ℝ≥0∞) ≤ q := by
    simpa [q] using
      (ENNReal.ofReal_le_ofReal (le_of_lt hq_gt_two) :
        ENNReal.ofReal (2 : ℝ) ≤ ENNReal.ofReal ((d : ℝ) * 2 / ((d : ℝ) - 2)))
  have hq_nonneg : 0 ≤ (d : ℝ) * 2 / ((d : ℝ) - 2) := by
    linarith
  have hq_toReal : q.toReal = (d : ℝ) * 2 / ((d : ℝ) - 2) := by
    simpa [q] using ENNReal.toReal_ofReal hq_nonneg
  have hexp :
      (1 / (2 : ℝ)) - 1 / q.toReal = 1 / (d : ℝ) := by
    rw [hq_toReal]
    have hd0 : (d : ℝ) ≠ 0 := by linarith
    have hd2 : (d : ℝ) - 2 ≠ 0 := by linarith
    field_simp [hd0, hd2]
    ring
  have hv_memLp_q :
      MemLp v q μ := by
    refine ⟨hwηθ_real.memLp.aestronglyMeasurable, ?_⟩
    have hgrad_lt_top :
        eLpNorm (fun x => ‖hwηθ_real.weakGrad x‖) 2 μ < ∞ :=
      hgrad_memLp2.eLpNorm_lt_top
    have hrhs_lt_top :
        ENNReal.ofReal (C_gns d 2) *
          eLpNorm (fun x => ‖hwηθ_real.weakGrad x‖) 2 μ < ∞ := by
      rw [ENNReal.mul_lt_top_iff]
      exact Or.inl ⟨by simp, hgrad_lt_top⟩
    exact lt_of_le_of_lt hSob'' hrhs_lt_top
  have hv_memLp_q_T :
      MemLp v q (μ.restrict T) := hv_memLp_q.mono_measure Measure.restrict_le_self
  have hv_memLp2_T :
      MemLp v 2 (μ.restrict T) := hwηθ_memLp2.mono_measure Measure.restrict_le_self
  have hcompare_real :
      MeasureTheory.lpNorm v 2 (μ.restrict T) ≤
        MeasureTheory.lpNorm v q (μ.restrict T) *
          ((μ.restrict T).real Set.univ) ^ ((1 / (2 : ℝ)) - 1 / q.toReal) := by
    have hcompare :=
      MeasureTheory.eLpNorm_le_eLpNorm_mul_rpow_measure_univ
        (μ := μ.restrict T) (f := v) htwo_le_q
        hwηθ_real.memLp.aestronglyMeasurable.restrict
    have hexp_nonneg : 0 ≤ (1 / (2 : ℝ)) - 1 / q.toReal := by
      rw [hexp]
      positivity
    have hfactor_ne_top :
        (μ.restrict T) Set.univ ^ ((1 / (2 : ℝ)) - 1 / q.toReal) ≠ ∞ := by
      exact (ENNReal.rpow_lt_top_of_nonneg hexp_nonneg (by finiteness)).ne
    have hrhs_ne_top :
        eLpNorm v q (μ.restrict T) *
            (μ.restrict T) Set.univ ^ ((1 / (2 : ℝ)) - 1 / q.toReal) ≠ ∞ := by
      exact ENNReal.mul_ne_top hv_memLp_q_T.eLpNorm_ne_top hfactor_ne_top
    have hcompare_toReal :
        (eLpNorm v 2 (μ.restrict T)).toReal ≤
          (eLpNorm v q (μ.restrict T) *
            (μ.restrict T) Set.univ ^ ((1 / (2 : ℝ)) - 1 / q.toReal)).toReal :=
      (ENNReal.toReal_le_toReal hv_memLp2_T.eLpNorm_ne_top hrhs_ne_top).2 hcompare
    have hrpow_toReal :
        ((μ.restrict T) Set.univ ^ ((1 / (2 : ℝ)) - 1 / q.toReal)).toReal =
          ((μ.restrict T).real Set.univ) ^ ((1 / (2 : ℝ)) - 1 / q.toReal) := by
      rw [← ENNReal.toReal_rpow]
      rfl
    have hcompare_toReal' := hcompare_toReal
    rw [MeasureTheory.toReal_eLpNorm hv_memLp2_T.aestronglyMeasurable,
      ENNReal.toReal_mul, MeasureTheory.toReal_eLpNorm hv_memLp_q_T.aestronglyMeasurable,
      hrpow_toReal] at hcompare_toReal'
    exact hcompare_toReal'
  have hq_mono_real :
      MeasureTheory.lpNorm v q (μ.restrict T) ≤ MeasureTheory.lpNorm v q μ := by
    rw [← MeasureTheory.toReal_eLpNorm hv_memLp_q_T.aestronglyMeasurable,
      ← MeasureTheory.toReal_eLpNorm hv_memLp_q.aestronglyMeasurable]
    exact ENNReal.toReal_mono hv_memLp_q.eLpNorm_ne_top
      (MeasureTheory.eLpNorm_mono_measure v Measure.restrict_le_self)
  have hgrad_lp :
      MeasureTheory.lpNorm (fun x => ‖hwηθ_real.weakGrad x‖) 2 μ =
        (∫ x in Ω, ‖hwηθ_real.weakGrad x‖ ^ 2 ∂volume) ^ (1 / (2 : ℝ)) := by
    simpa [μ] using
      (MeasureTheory.lpNorm_eq_integral_norm_rpow_toReal
        (μ := μ) (f := fun x => ‖hwηθ_real.weakGrad x‖)
        two_ne_zero ENNReal.ofNat_ne_top hwηθ_real.weakGrad_norm_memLp.aestronglyMeasurable)
  have hSob_real :
      MeasureTheory.lpNorm v q μ ≤
        (C_gns d 2) * MeasureTheory.lpNorm (fun x => ‖hwηθ_real.weakGrad x‖) 2 μ := by
    have hgrad_ne_top :
        eLpNorm (fun x => ‖hwηθ_real.weakGrad x‖) 2 μ ≠ ∞ :=
      hgrad_memLp2.eLpNorm_ne_top
    have hrhs_ne_top :
        ENNReal.ofReal (C_gns d 2) *
            eLpNorm (fun x => ‖hwηθ_real.weakGrad x‖) 2 μ ≠ ∞ :=
      ENNReal.mul_ne_top (by simp) hgrad_ne_top
    have hSob_toReal :
        (eLpNorm v q μ).toReal ≤
          (ENNReal.ofReal (C_gns d 2) *
            eLpNorm (fun x => ‖hwηθ_real.weakGrad x‖) 2 μ).toReal :=
      (ENNReal.toReal_le_toReal hv_memLp_q.eLpNorm_ne_top hrhs_ne_top).2 hSob''
    have hC_toReal : (ENNReal.ofReal (C_gns d 2)).toReal = C_gns d 2 :=
      ENNReal.toReal_ofReal (C_gns_nonneg d 2)
    have hSob_toReal' := hSob_toReal
    rw [MeasureTheory.toReal_eLpNorm hv_memLp_q.aestronglyMeasurable,
      ENNReal.toReal_mul, MeasureTheory.toReal_eLpNorm hgrad_memLp2.aestronglyMeasurable,
      hC_toReal] at hSob_toReal'
    exact hSob_toReal'
  have hT_lp_sq :
      ∫ x in T, |v x| ^ 2 ∂μ = (MeasureTheory.lpNorm v 2 (μ.restrict T)) ^ 2 := by
    rw [MeasureTheory.lpNorm_eq_integral_norm_rpow_toReal
      (μ := μ.restrict T) (f := v) two_ne_zero ENNReal.ofNat_ne_top
      hv_memLp2_T.aestronglyMeasurable]
    norm_num
    have hnonneg : 0 ≤ ∫ x in T, v x ^ 2 ∂μ := by
      refine integral_nonneg ?_
      intro x
      exact sq_nonneg (v x)
    have hsqrt :
        (∫ x in T, v x ^ 2 ∂μ) ^ (1 / (2 : ℝ)) =
          Real.sqrt (∫ x in T, v x ^ 2 ∂μ) := by
      rw [Real.sqrt_eq_rpow]
    rw [hsqrt, Real.sq_sqrt hnonneg]
  have hgrad_sq :
      (MeasureTheory.lpNorm (fun x => ‖hwηθ_real.weakGrad x‖) 2 μ) ^ 2 =
        ∫ x in Ω, ‖hwηθ_real.weakGrad x‖ ^ 2 ∂volume := by
    rw [hgrad_lp]
    have hnonneg :
        0 ≤ ∫ x in Ω, ‖hwηθ_real.weakGrad x‖ ^ 2 ∂volume := by
      refine integral_nonneg ?_
      intro x
      positivity
    have hsqrt :
        (∫ x in Ω, ‖hwηθ_real.weakGrad x‖ ^ 2 ∂volume) ^ (1 / (2 : ℝ)) =
          Real.sqrt (∫ x in Ω, ‖hwηθ_real.weakGrad x‖ ^ 2 ∂volume) := by
      rw [Real.sqrt_eq_rpow]
    rw [hsqrt, Real.sq_sqrt hnonneg]
  have hmain_lp :
      MeasureTheory.lpNorm v 2 (μ.restrict T) ≤
        (C_gns d 2) * MeasureTheory.lpNorm (fun x => ‖hwηθ_real.weakGrad x‖) 2 μ *
          (μ.real S) ^ (1 / (d : ℝ)) := by
    calc
      MeasureTheory.lpNorm v 2 (μ.restrict T)
          ≤ MeasureTheory.lpNorm v q (μ.restrict T) *
              ((μ.restrict T).real Set.univ) ^ ((1 / (2 : ℝ)) - 1 / q.toReal) :=
        hcompare_real
      _ = MeasureTheory.lpNorm v q (μ.restrict T) * (μ.real S) ^ (1 / (d : ℝ)) := by
        rw [hμT_real, hexp]
      _ ≤ MeasureTheory.lpNorm v q μ * (μ.real S) ^ (1 / (d : ℝ)) := by
        gcongr
      _ ≤ ((C_gns d 2) * MeasureTheory.lpNorm (fun x => ‖hwηθ_real.weakGrad x‖) 2 μ) *
            (μ.real S) ^ (1 / (d : ℝ)) := by
        gcongr
      _ = (C_gns d 2) * MeasureTheory.lpNorm (fun x => ‖hwηθ_real.weakGrad x‖) 2 μ *
            (μ.real S) ^ (1 / (d : ℝ)) := by ring
  have hmain_sq :
      ∫ x in T, |v x| ^ 2 ∂μ ≤
        (C_gns d 2) ^ 2 *
          (∫ x in Ω, ‖hwηθ_real.weakGrad x‖ ^ 2 ∂volume) *
          (μ.real S) ^ (2 / (d : ℝ)) := by
    have hμ_nonneg : 0 ≤ μ.real S := measureReal_nonneg
    have hnonneg_left : 0 ≤ MeasureTheory.lpNorm v 2 (μ.restrict T) := MeasureTheory.lpNorm_nonneg
    have hnonneg_right :
        0 ≤ (C_gns d 2) * MeasureTheory.lpNorm (fun x => ‖hwηθ_real.weakGrad x‖) 2 μ *
          (μ.real S) ^ (1 / (d : ℝ)) := by
      have hpow_nonneg : 0 ≤ (μ.real S) ^ (1 / (d : ℝ)) := Real.rpow_nonneg hμ_nonneg _
      exact mul_nonneg (mul_nonneg (C_gns_nonneg d 2) MeasureTheory.lpNorm_nonneg) hpow_nonneg
    have hsq :
        (MeasureTheory.lpNorm v 2 (μ.restrict T)) ^ 2 ≤
          ((C_gns d 2) * MeasureTheory.lpNorm (fun x => ‖hwηθ_real.weakGrad x‖) 2 μ *
            (μ.real S) ^ (1 / (d : ℝ))) ^ 2 := by
      nlinarith [hmain_lp]
    calc
      ∫ x in T, |v x| ^ 2 ∂μ = (MeasureTheory.lpNorm v 2 (μ.restrict T)) ^ 2 := hT_lp_sq
      _ ≤ ((C_gns d 2) * MeasureTheory.lpNorm (fun x => ‖hwηθ_real.weakGrad x‖) 2 μ *
                (μ.real S) ^ (1 / (d : ℝ))) ^ 2 := hsq
      _ = (C_gns d 2) ^ 2 *
            (∫ x in Ω, ‖hwηθ_real.weakGrad x‖ ^ 2 ∂volume) *
            (μ.real S) ^ (2 / (d : ℝ)) := by
          have hpow :
              ((μ.real S) ^ (1 / (d : ℝ))) ^ 2 =
                (μ.real S) ^ (2 / (d : ℝ)) := by
            rw [pow_two, ← Real.rpow_add' hμ_nonneg]
            · ring_nf
            · positivity
          calc
            ((C_gns d 2) * MeasureTheory.lpNorm (fun x => ‖hwηθ_real.weakGrad x‖) 2 μ *
                (μ.real S) ^ (1 / (d : ℝ))) ^ 2
                = (C_gns d 2) ^ 2 *
                    (MeasureTheory.lpNorm (fun x => ‖hwηθ_real.weakGrad x‖) 2 μ) ^ 2 *
                    ((μ.real S) ^ (1 / (d : ℝ))) ^ 2 := by
                    ring
            _ = (C_gns d 2) ^ 2 *
                  (∫ x in Ω, ‖hwηθ_real.weakGrad x‖ ^ 2 ∂volume) *
                  ((μ.real S) ^ (1 / (d : ℝ))) ^ 2 := by
                  rw [hgrad_sq]
            _ = (C_gns d 2) ^ 2 *
                  (∫ x in Ω, ‖hwηθ_real.weakGrad x‖ ^ 2 ∂volume) *
                  (μ.real S) ^ (2 / (d : ℝ)) := by
                  rw [hpow]
  calc
    ∫ x in B, |positivePartSub u lam x| ^ 2 ∂volume
        ≤ ∫ x in Ω, T.indicator g x ∂volume := hleft_le_T
    _ = ∫ x in T, |v x| ^ 2 ∂μ := by
      rw [show ∫ x in Ω, T.indicator g x ∂volume = ∫ x, T.indicator g x ∂μ by rfl,
        MeasureTheory.integral_indicator hT_meas]
    _ ≤ (C_gns d 2) ^ 2 *
          (∫ x in Ω, ‖hwηθ_real.weakGrad x‖ ^ 2 ∂volume) *
          (μ.real S) ^ (2 / (d : ℝ)) := hmain_sq
    _ = (C_gns d 2) ^ 2 *
          (∫ x in Metric.ball x₀ s, ‖hwηθ_real.weakGrad x‖ ^ 2 ∂volume) *
          ((volume.restrict (Metric.ball x₀ s)).real {x | lam < u x}) ^ (2 / (d : ℝ)) := by
      simp [Ω, μ, S]

/-- Sobolev/Hölder step for De Giorgi pre-iteration on concentric balls.

The argument passes through a zero-trace cutoff witness for
`η² (u - θ)₊`. The originally intended statement with only the bare
`θ`-truncation gradient on the right-hand side is false, e.g. for constant
superlevel functions. The proof here records the actual Chapter 05 mechanism:

1. build a `W₀^{1,2}` witness for `η² (u - θ)₊`,
2. zero-extend it to the whole space,
3. apply whole-space Sobolev, and
4. combine it with the `L²`-to-`L^{2d/(d-2)}` restriction estimate on
   `{x | λ < u x}`. -/
theorem deGiorgi_cutoffSobolev_on_concentricBalls_of_ballPosPart
    {u η : E → ℝ} {x₀ : E} {r s θ lam : ℝ}
    (hd : 2 < (d : ℝ))
    (hr : 0 < r) (hrs : r < s)
    (hu : MemW1pWitness 2 u (Metric.ball x₀ s))
    (hwθ : MemW1pWitness 2 (positivePartSub u θ) (Metric.ball x₀ s))
    (hθl : θ < lam)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (_hη_nonneg : ∀ x, 0 ≤ η x)
    (hη_eq_one : ∀ x ∈ Metric.ball x₀ r, η x = 1)
    (hη_bound : ∀ x, |η x| ≤ 1)
    (hη_sub_ball : tsupport η ⊆ Metric.ball x₀ s) :
    ∃ hwηθ : MemW1pWitness 2 (deGiorgiCutoffTestGeneral η u θ) (Metric.ball x₀ s),
      ∫ x in Metric.ball x₀ r, |positivePartSub u lam x| ^ 2 ∂volume ≤
        (C_gns d 2) ^ 2 *
          (∫ x in Metric.ball x₀ s, ‖hwηθ.weakGrad x‖ ^ 2 ∂volume) *
          ((volume.restrict (Metric.ball x₀ s)).real {x | lam < u x}) ^ (2 / (d : ℝ)) := by
  have hs : 0 < s := lt_trans hr hrs
  let v : E → ℝ := deGiorgiCutoffTestGeneral η u θ
  haveI : IsFiniteMeasure (volume.restrict (Metric.ball x₀ s)) := by
    rw [isFiniteMeasure_restrict]
    exact measure_ball_lt_top.ne
  have hη_comp : HasCompactSupport η :=
    hasCompactSupport_of_tsupport_subset_ball hη_sub_ball
  obtain ⟨Cη, hCη, hη_grad_bound⟩ :=
    exists_fderiv_bound_of_contDiff_hasCompactSupport hη hη_comp
  have hvW01 :
      MemW01p 2 (deGiorgiCutoffTestGeneral η u θ) (Metric.ball x₀ s) :=
    deGiorgiCutoffTest_memW01p_of_truncWitness
      isOpen_ball hwθ hη (by norm_num) hCη hη_bound hη_grad_bound hη_comp hη_sub_ball
  obtain ⟨hwηθ_real, hSob''⟩ :=
    deGiorgi_cutoffSobolev_prepare (d := d) hd hs hu hη hη_bound hη_sub_ball hvW01
  let hwηθ : MemW1pWitness 2 v (Metric.ball x₀ s) :=
    { memLp := by
        simpa [v] using hwηθ_real.memLp
      weakGrad := hwηθ_real.weakGrad
      weakGrad_component_memLp := by
        simpa using hwηθ_real.weakGrad_component_memLp
      isWeakGrad := by
        simpa [v] using hwηθ_real.isWeakGrad }
  refine ⟨hwηθ, ?_⟩
  simpa [v, hwηθ] using
    deGiorgi_cutoffSobolev_superlevelStep (d := d) hd hr hrs hu hwθ hθl hη_eq_one
      hwηθ_real hSob''

/-- Sobolev/Hölder step for De Giorgi pre-iteration on concentric balls,
using the concrete positive-part approximation input. -/
theorem deGiorgi_cutoffSobolev_on_concentricBalls_of_posPartApprox
    {u η : E → ℝ} {x₀ : E} {r s θ lam : ℝ}
    (hd : 2 < (d : ℝ))
    (hs : 0 < s) (hr : 0 < r) (hrs : r < s)
    (hu : MemW1pWitness 2 u (Metric.ball x₀ s))
    (happroxBallTheta :
      ∃ ψ : ℕ → E → ℝ,
        (∀ n, ContDiff ℝ 1 (ψ n)) ∧
        (∀ n, HasCompactSupport (ψ n)) ∧
        Tendsto
          (fun n =>
            eLpNorm (fun x => ψ n x - (u x - θ)) 2
              (volume.restrict (Metric.ball x₀ s)))
          atTop (nhds 0) ∧
        (∀ i : Fin d,
          Tendsto
            (fun n =>
              eLpNorm
                (fun x =>
                  (fderiv ℝ (ψ n) x) (EuclideanSpace.single i 1) - hu.weakGrad x i)
                2 (volume.restrict (Metric.ball x₀ s)))
            atTop (nhds 0)))
    (hθl : θ < lam)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (_hη_nonneg : ∀ x, 0 ≤ η x)
    (hη_eq_one : ∀ x ∈ Metric.ball x₀ r, η x = 1)
    (hη_bound : ∀ x, |η x| ≤ 1)
    (hη_sub_ball : tsupport η ⊆ Metric.ball x₀ s) :
    ∃ hwηθ : MemW1pWitness 2 (deGiorgiCutoffTestGeneral η u θ) (Metric.ball x₀ s),
      ∫ x in Metric.ball x₀ r, |positivePartSub u lam x| ^ 2 ∂volume ≤
        (C_gns d 2) ^ 2 *
          (∫ x in Metric.ball x₀ s, ‖hwηθ.weakGrad x‖ ^ 2 ∂volume) *
          ((volume.restrict (Metric.ball x₀ s)).real {x | lam < u x}) ^ (2 / (d : ℝ)) := by
  let v : E → ℝ := deGiorgiCutoffTestGeneral η u θ
  have hη_comp : HasCompactSupport η :=
    hasCompactSupport_of_tsupport_subset_ball hη_sub_ball
  obtain ⟨Cη, hCη, hη_grad_bound⟩ :=
    exists_fderiv_bound_of_contDiff_hasCompactSupport hη hη_comp
  have hvW01 :
      MemW01p 2 (deGiorgiCutoffTestGeneral η u θ) (Metric.ball x₀ s) :=
    deGiorgiCutoffTest_memW01p_on_ball_of_ballPosPartApprox
      hs hu hη hη_bound hCη hη_grad_bound hη_sub_ball θ happroxBallTheta
  obtain ⟨hwηθ_real, hSob''⟩ :=
    deGiorgi_cutoffSobolev_prepare (d := d) hd hs hu hη hη_bound hη_sub_ball hvW01
  let hwηθ : MemW1pWitness 2 v (Metric.ball x₀ s) :=
    { memLp := by
        simpa [v] using hwηθ_real.memLp
      weakGrad := hwηθ_real.weakGrad
      weakGrad_component_memLp := by
        simpa using hwηθ_real.weakGrad_component_memLp
      isWeakGrad := by
        simpa [v] using hwηθ_real.isWeakGrad }
  let hwθ : MemW1pWitness 2 (positivePartSub u θ) (Metric.ball x₀ s) :=
    positivePartSub_memW1pWitness_on_ball hs hu θ happroxBallTheta
  refine ⟨hwηθ, ?_⟩
  simpa [v, hwηθ, hwθ] using
    deGiorgi_cutoffSobolev_superlevelStep (d := d) hd hr hrs hu hwθ hθl hη_eq_one
      hwηθ_real hSob''

lemma deGiorgi_cutoff_gradient_bound_of_weighted
    {u η : E → ℝ} {x₀ : E} {s k Cη Cw : ℝ}
    (hCw : 0 ≤ Cw)
    (hw_trunc : MemW1pWitness 2 (positivePartSub u k) (Metric.ball x₀ s))
    (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hη_nonneg : ∀ x, 0 ≤ η x)
    (hη_bound : ∀ x, |η x| ≤ 1)
    (hCη : 0 ≤ Cη)
    (hη_grad_bound : ∀ x, ‖fderiv ℝ η x‖ ≤ Cη)
    (hweighted :
      ∫ x in Metric.ball x₀ s, η x ^ 2 * ‖hw_trunc.weakGrad x‖ ^ 2 ∂volume ≤
        4 * Cw *
          ∫ x in Metric.ball x₀ s,
            ‖fderiv ℝ η x‖ ^ 2 * |positivePartSub u k x| ^ 2 ∂volume) :
    let hwφ : MemW1pWitness 2 (deGiorgiCutoffTestGeneral η u k) (Metric.ball x₀ s) :=
      deGiorgiCutoffTestWitnessWeighted
        isOpen_ball hw_trunc hη (by norm_num) hCη hη_bound hη_grad_bound
    ∫ x in Metric.ball x₀ s, ‖hwφ.weakGrad x‖ ^ 2 ∂volume ≤
      (8 * (Cw + 1) * Cη ^ 2) *
        ∫ x in Metric.ball x₀ s, |positivePartSub u k x| ^ 2 ∂volume := by
  dsimp
  let hwφ : MemW1pWitness 2 (deGiorgiCutoffTestGeneral η u k) (Metric.ball x₀ s) :=
    deGiorgiCutoffTestWitnessWeighted
      isOpen_ball hw_trunc hη (by norm_num) hCη hη_bound hη_grad_bound
  have hhwφ_int :
      Integrable (fun x => ‖hwφ.weakGrad x‖ ^ 2)
        (volume.restrict (Metric.ball x₀ s)) := by
    simpa [pow_two] using hwφ.weakGrad_norm_memLp.integrable_sq
  have htrunc_sq_int :
      Integrable (fun x => ‖hw_trunc.weakGrad x‖ ^ 2)
        (volume.restrict (Metric.ball x₀ s)) := by
    simpa [pow_two] using hw_trunc.weakGrad_norm_memLp.integrable_sq
  have hpos_sq_int :
      Integrable (fun x => |positivePartSub u k x| ^ 2)
        (volume.restrict (Metric.ball x₀ s)) := by
    simpa [pow_two] using hw_trunc.memLp.integrable_sq
  have hweighted_int :
      Integrable (fun x => η x ^ 2 * ‖hw_trunc.weakGrad x‖ ^ 2)
        (volume.restrict (Metric.ball x₀ s)) := by
    refine Integrable.mono' htrunc_sq_int ?_ ?_
    · exact
        (((hη.continuous.pow 2).aemeasurable).mul
          htrunc_sq_int.aestronglyMeasurable.aemeasurable).aestronglyMeasurable
    · filter_upwards with x
      have hηx_nonneg : 0 ≤ η x := hη_nonneg x
      have hηx_le_one : η x ≤ 1 := by
        simpa [abs_of_nonneg hηx_nonneg] using hη_bound x
      have hηx_sq_le_one : η x ^ 2 ≤ 1 := by nlinarith
      have hgw_nonneg : 0 ≤ ‖hw_trunc.weakGrad x‖ ^ 2 := by positivity
      have hprod_nonneg : 0 ≤ η x ^ 2 * ‖hw_trunc.weakGrad x‖ ^ 2 := by positivity
      have hle : η x ^ 2 * ‖hw_trunc.weakGrad x‖ ^ 2 ≤ ‖hw_trunc.weakGrad x‖ ^ 2 := by
        nlinarith
      simpa [Real.norm_eq_abs, abs_of_nonneg hprod_nonneg, abs_of_nonneg hgw_nonneg] using hle
  have hgrad_term_int :
      Integrable (fun x => ‖fderiv ℝ η x‖ ^ 2 * |positivePartSub u k x| ^ 2)
        (volume.restrict (Metric.ball x₀ s)) := by
    refine Integrable.mono' (hpos_sq_int.const_mul (Cη ^ 2)) ?_ ?_
    · exact
        ((((hη.continuous_fderiv (by simp : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0)).norm.pow 2).aemeasurable).mul
          hpos_sq_int.aestronglyMeasurable.aemeasurable).aestronglyMeasurable
    · filter_upwards with x
      have hfd_sq_le : ‖fderiv ℝ η x‖ ^ 2 ≤ Cη ^ 2 := by
        exact sq_le_sq.mpr (by
          simpa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg hCη] using hη_grad_bound x)
      have hpos_nonneg : 0 ≤ |positivePartSub u k x| ^ 2 := by positivity
      have hterm_nonneg :
          0 ≤ ‖fderiv ℝ η x‖ ^ 2 * |positivePartSub u k x| ^ 2 := by positivity
      have hle :
          ‖fderiv ℝ η x‖ ^ 2 * |positivePartSub u k x| ^ 2 ≤
            Cη ^ 2 * |positivePartSub u k x| ^ 2 :=
        mul_le_mul_of_nonneg_right hfd_sq_le hpos_nonneg
      simpa [Real.norm_eq_abs, abs_of_nonneg hterm_nonneg] using hle
  have hgrad_term_bound :
      ∫ x in Metric.ball x₀ s, ‖fderiv ℝ η x‖ ^ 2 * |positivePartSub u k x| ^ 2 ∂volume ≤
        Cη ^ 2 * ∫ x in Metric.ball x₀ s, |positivePartSub u k x| ^ 2 ∂volume := by
    calc
      ∫ x in Metric.ball x₀ s, ‖fderiv ℝ η x‖ ^ 2 * |positivePartSub u k x| ^ 2 ∂volume
          ≤ ∫ x in Metric.ball x₀ s, Cη ^ 2 * |positivePartSub u k x| ^ 2 ∂volume := by
            refine integral_mono_ae hgrad_term_int (hpos_sq_int.const_mul (Cη ^ 2)) ?_
            refine (ae_restrict_iff' (μ := volume) isOpen_ball.measurableSet).2 ?_
            filter_upwards with x hx
            have hfd_sq_le : ‖fderiv ℝ η x‖ ^ 2 ≤ Cη ^ 2 := by
              exact sq_le_sq.mpr (by
                simpa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg hCη] using hη_grad_bound x)
            have hpos_nonneg : 0 ≤ |positivePartSub u k x| ^ 2 := by positivity
            exact mul_le_mul_of_nonneg_right hfd_sq_le hpos_nonneg
      _ = Cη ^ 2 * ∫ x in Metric.ball x₀ s, |positivePartSub u k x| ^ 2 ∂volume := by
            rw [integral_const_mul]
  have hpointwise :
      ∀ x,
        ‖hwφ.weakGrad x‖ ^ 2 ≤
          2 * (η x ^ 2 * ‖hw_trunc.weakGrad x‖ ^ 2) +
            8 * Cη ^ 2 * |positivePartSub u k x| ^ 2 := by
    intro x
    let a : E := η x ^ 2 • hw_trunc.weakGrad x
    let b : E := (2 * η x * positivePartSub u k x) • deGiorgiFderivVec η x
    have hdecomp : hwφ.weakGrad x = a + b := by
      simp [hwφ, a, b, deGiorgiCutoffTestWitnessWeighted_grad]
    have hnorm_sq :
        ‖hwφ.weakGrad x‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
      rw [hdecomp]
      calc
        ‖a + b‖ ^ 2 ≤ (‖a‖ + ‖b‖) ^ 2 := by
          exact sq_le_sq.mpr (by
            have hsum_nonneg : 0 ≤ ‖a‖ + ‖b‖ := by positivity
            simpa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg hsum_nonneg] using norm_add_le a b)
        _ ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
          nlinarith [sq_nonneg (‖a‖ - ‖b‖)]
    have hηx_nonneg : 0 ≤ η x := hη_nonneg x
    have hηx_le_one : η x ≤ 1 := by
      simpa [abs_of_nonneg hηx_nonneg] using hη_bound x
    have hηx_sq_le_one : η x ^ 2 ≤ 1 := by nlinarith
    have htrunc_nonneg : 0 ≤ positivePartSub u k x := positivePartSub_nonneg
    have ha_sq :
        ‖a‖ ^ 2 ≤ η x ^ 2 * ‖hw_trunc.weakGrad x‖ ^ 2 := by
      calc
        ‖a‖ ^ 2 = (η x ^ 2) ^ 2 * ‖hw_trunc.weakGrad x‖ ^ 2 := by
          dsimp [a]
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (η x))]
          ring
        _ ≤ η x ^ 2 * ‖hw_trunc.weakGrad x‖ ^ 2 := by
          have hη_four_le : (η x ^ 2) ^ 2 ≤ η x ^ 2 := by nlinarith
          have hgw_nonneg : 0 ≤ ‖hw_trunc.weakGrad x‖ ^ 2 := by positivity
          exact mul_le_mul_of_nonneg_right hη_four_le hgw_nonneg
    have hb_sq :
        ‖b‖ ^ 2 ≤ 4 * Cη ^ 2 * |positivePartSub u k x| ^ 2 := by
      calc
        ‖b‖ ^ 2
            = (2 * η x * positivePartSub u k x) ^ 2 * ‖deGiorgiFderivVec η x‖ ^ 2 := by
                dsimp [b]
                rw [norm_smul, Real.norm_eq_abs]
                have hcoeff_nonneg : 0 ≤ 2 * η x * positivePartSub u k x := by positivity
                rw [abs_of_nonneg hcoeff_nonneg]
                ring
        _ ≤ (2 * η x * positivePartSub u k x) ^ 2 * Cη ^ 2 := by
              have hnorm_sq_le : ‖deGiorgiFderivVec η x‖ ^ 2 ≤ Cη ^ 2 := by
                rw [deGiorgi_norm_fderivVec_eq_norm_fderiv]
                exact sq_le_sq.mpr (by
                  simpa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg hCη] using hη_grad_bound x)
              have hcoeff_nonneg : 0 ≤ (2 * η x * positivePartSub u k x) ^ 2 := by positivity
              exact mul_le_mul_of_nonneg_left hnorm_sq_le hcoeff_nonneg
        _ ≤ 4 * Cη ^ 2 * |positivePartSub u k x| ^ 2 := by
              have hcoeff_le :
                  (2 * η x * positivePartSub u k x) ^ 2 ≤ 4 * (positivePartSub u k x) ^ 2 := by
                nlinarith
              have hCη_sq_nonneg : 0 ≤ Cη ^ 2 := sq_nonneg Cη
              calc
                (2 * η x * positivePartSub u k x) ^ 2 * Cη ^ 2
                    ≤ (4 * (positivePartSub u k x) ^ 2) * Cη ^ 2 :=
                      mul_le_mul_of_nonneg_right hcoeff_le hCη_sq_nonneg
                _ = 4 * Cη ^ 2 * |positivePartSub u k x| ^ 2 := by
                      rw [abs_of_nonneg htrunc_nonneg]
                      ring
    nlinarith
  have hupper_int :
      Integrable
        (fun x =>
          2 * (η x ^ 2 * ‖hw_trunc.weakGrad x‖ ^ 2) +
            8 * Cη ^ 2 * |positivePartSub u k x| ^ 2)
        (volume.restrict (Metric.ball x₀ s)) := by
    exact (hweighted_int.const_mul 2).add (hpos_sq_int.const_mul (8 * Cη ^ 2))
  have hmain :
      ∫ x in Metric.ball x₀ s, ‖hwφ.weakGrad x‖ ^ 2 ∂volume ≤
        ∫ x in Metric.ball x₀ s,
          2 * (η x ^ 2 * ‖hw_trunc.weakGrad x‖ ^ 2) +
            8 * Cη ^ 2 * |positivePartSub u k x| ^ 2 ∂volume := by
    refine integral_mono_ae hhwφ_int hupper_int ?_
    refine (ae_restrict_iff' (μ := volume) isOpen_ball.measurableSet).2 ?_
    filter_upwards with x hx
    exact hpointwise x
  have hweighted' :
      2 * ∫ x in Metric.ball x₀ s, η x ^ 2 * ‖hw_trunc.weakGrad x‖ ^ 2 ∂volume ≤
        8 * Cw * Cη ^ 2 *
          ∫ x in Metric.ball x₀ s, |positivePartSub u k x| ^ 2 ∂volume := by
    calc
      2 * ∫ x in Metric.ball x₀ s, η x ^ 2 * ‖hw_trunc.weakGrad x‖ ^ 2 ∂volume
          ≤ 2 * (4 * Cw *
              ∫ x in Metric.ball x₀ s, ‖fderiv ℝ η x‖ ^ 2 * |positivePartSub u k x| ^ 2 ∂volume) := by
                gcongr
      _ = 8 * Cw *
            ∫ x in Metric.ball x₀ s, ‖fderiv ℝ η x‖ ^ 2 * |positivePartSub u k x| ^ 2 ∂volume := by
              ring
      _ ≤ 8 * Cw * (Cη ^ 2 *
            ∫ x in Metric.ball x₀ s, |positivePartSub u k x| ^ 2 ∂volume) := by
              gcongr
      _ = 8 * Cw * Cη ^ 2 *
            ∫ x in Metric.ball x₀ s, |positivePartSub u k x| ^ 2 ∂volume := by
              ring
  calc
    ∫ x in Metric.ball x₀ s, ‖hwφ.weakGrad x‖ ^ 2 ∂volume
        ≤ ∫ x in Metric.ball x₀ s,
            2 * (η x ^ 2 * ‖hw_trunc.weakGrad x‖ ^ 2) +
              8 * Cη ^ 2 * |positivePartSub u k x| ^ 2 ∂volume := hmain
    _ = 2 * ∫ x in Metric.ball x₀ s, η x ^ 2 * ‖hw_trunc.weakGrad x‖ ^ 2 ∂volume +
          8 * Cη ^ 2 *
            ∫ x in Metric.ball x₀ s, |positivePartSub u k x| ^ 2 ∂volume := by
            rw [integral_add (hweighted_int.const_mul 2) (hpos_sq_int.const_mul (8 * Cη ^ 2))]
            rw [integral_const_mul, integral_const_mul]
    _ ≤ 8 * Cw * Cη ^ 2 *
          ∫ x in Metric.ball x₀ s, |positivePartSub u k x| ^ 2 ∂volume +
        8 * Cη ^ 2 *
          ∫ x in Metric.ball x₀ s, |positivePartSub u k x| ^ 2 ∂volume := by
            gcongr
    _ = (8 * (Cw + 1) * Cη ^ 2) *
          ∫ x in Metric.ball x₀ s, |positivePartSub u k x| ^ 2 ∂volume := by
            ring

/-- PDE-facing De Giorgi pre-iteration theorem on concentric balls.

This now factors through the explicit cutoff-Sobolev bridge
`deGiorgi_cutoffSobolev_on_concentricBalls_of_ballPosPart` instead of keeping
the local Sobolev argument bundled into one monolithic proof. -/
theorem deGiorgi_preiter_on_concentricBalls_of_ballPosPart
    {u η : E → ℝ} {x₀ : E} {r s θ lam Cη : ℝ}
    (hd : 2 < (d : ℝ))
    (A : EllipticCoeff d (Metric.ball x₀ s))
    (hr : 0 < r) (hrs : r < s)
    (hsub : IsSubsolution A u)
    (hu : MemW1pWitness 2 u (Metric.ball x₀ s))
    (hwθ : MemW1pWitness 2 (positivePartSub u θ) (Metric.ball x₀ s))
    (hθl : θ < lam)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hη_nonneg : ∀ x, 0 ≤ η x)
    (hη_eq_one : ∀ x ∈ Metric.ball x₀ r, η x = 1)
    (hη_bound : ∀ x, |η x| ≤ 1)
    (hCη : 0 ≤ Cη)
    (hη_grad_bound : ∀ x, ‖fderiv ℝ η x‖ ≤ Cη)
    (hη_sub_ball : tsupport η ⊆ Metric.ball x₀ s) :
    ∫ x in Metric.ball x₀ r, |positivePartSub u lam x| ^ 2 ∂volume ≤
      (C_gns d 2) ^ 2 * (8 * (ellipticityRatio A + 1) * Cη ^ 2) *
        ((((lam - θ) ^ 2)⁻¹ *
            ∫ x in Metric.ball x₀ s, |positivePartSub u θ x| ^ 2 ∂volume) ^ (2 / (d : ℝ))) *
          ∫ x in Metric.ball x₀ s, |positivePartSub u θ x| ^ 2 ∂volume := by
  have hs : 0 < s := lt_trans hr hrs
  have hd_pos : 0 < (d : ℝ) := by
    linarith
  have hRatio_nonneg : 0 ≤ ellipticityRatio A := A.ellipticityRatio_nonneg
  have hCenergy_nonneg : 0 ≤ 8 * (ellipticityRatio A + 1) * Cη ^ 2 := by
    have hCη_sq_nonneg : 0 ≤ Cη ^ 2 := sq_nonneg Cη
    nlinarith
  have hθ_int :
      Integrable (fun x => |positivePartSub u θ x| ^ 2)
        (volume.restrict (Metric.ball x₀ s)) := by
    simpa [pow_two] using hwθ.memLp.integrable_sq
  have hIθ_nonneg :
      0 ≤ ∫ x in Metric.ball x₀ s, |positivePartSub u θ x| ^ 2 ∂volume := by
    refine integral_nonneg ?_
    intro x
    positivity
  obtain ⟨hwηθ, hsob⟩ :=
    deGiorgi_cutoffSobolev_on_concentricBalls_of_ballPosPart
      (d := d) hd hr hrs hu hwθ hθl hη hη_nonneg hη_eq_one hη_bound hη_sub_ball
  let hwφ : MemW1pWitness 2 (deGiorgiCutoffTestGeneral η u θ) (Metric.ball x₀ s) :=
    deGiorgiCutoffTestWitnessWeighted
      isOpen_ball hwθ hη (by norm_num) hCη hη_bound hη_grad_bound
  have hweighted :
      ∫ x in Metric.ball x₀ s, η x ^ 2 * ‖hwθ.weakGrad x‖ ^ 2 ∂volume ≤
        (4 * ellipticityRatio A) *
          ∫ x in Metric.ball x₀ s, ‖fderiv ℝ η x‖ ^ 2 * |positivePartSub u θ x| ^ 2
            ∂volume := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      caccioppoli_weighted_on_ball_of_ballPosPart
        A hs hsub hu hwθ hη hη_nonneg hη_bound hCη hη_grad_bound hη_sub_ball
  have hgrad_bound_phi :
      ∫ x in Metric.ball x₀ s, ‖hwφ.weakGrad x‖ ^ 2 ∂volume ≤
        (8 * (ellipticityRatio A + 1) * Cη ^ 2) *
          ∫ x in Metric.ball x₀ s, |positivePartSub u θ x| ^ 2 ∂volume := by
    simpa [hwφ] using
      deGiorgi_cutoff_gradient_bound_of_weighted
        (x₀ := x₀) (s := s) (u := u) (η := η) (k := θ)
        (Cη := Cη) (Cw := ellipticityRatio A)
        hRatio_nonneg hwθ hη hη_nonneg hη_bound hCη hη_grad_bound hweighted
  have hgrad_ae :
      hwηθ.weakGrad =ᵐ[volume.restrict (Metric.ball x₀ s)] hwφ.weakGrad :=
    MemW1pWitness.ae_eq isOpen_ball hwηθ hwφ
  have hgrad_eq :
      ∫ x in Metric.ball x₀ s, ‖hwηθ.weakGrad x‖ ^ 2 ∂volume =
        ∫ x in Metric.ball x₀ s, ‖hwφ.weakGrad x‖ ^ 2 ∂volume := by
    refine integral_congr_ae ?_
    filter_upwards [hgrad_ae] with x hx
    simp [hx]
  have henergy :
      ∫ x in Metric.ball x₀ s, ‖hwηθ.weakGrad x‖ ^ 2 ∂volume ≤
        (8 * (ellipticityRatio A + 1) * Cη ^ 2) *
          ∫ x in Metric.ball x₀ s, |positivePartSub u θ x| ^ 2 ∂volume := by
    rw [hgrad_eq]
    exact hgrad_bound_phi
  haveI : IsFiniteMeasure (volume.restrict (Metric.ball x₀ s)) := by
    rw [isFiniteMeasure_restrict]
    exact measure_ball_lt_top.ne
  simpa [mul_assoc, mul_left_comm, mul_comm] using
    deGiorgi_preiter_of_energy
      (μ := volume.restrict (Metric.ball x₀ s))
      (d := d) hd_pos (u := u) (θ := θ) (lam := lam)
      (Ilam := ∫ x in Metric.ball x₀ r, |positivePartSub u lam x| ^ 2 ∂volume)
      (Iθ := ∫ x in Metric.ball x₀ s, |positivePartSub u θ x| ^ 2 ∂volume)
      (G := ∫ x in Metric.ball x₀ s, ‖hwηθ.weakGrad x‖ ^ 2 ∂volume)
      (Csob := (C_gns d 2) ^ 2)
      (Cenergy := 8 * (ellipticityRatio A + 1) * Cη ^ 2)
      hθl
      (sq_nonneg _)
      hCenergy_nonneg
      hIθ_nonneg
      hθ_int
      hsob
      henergy
      (by rfl)

/-- Approximation-based version of the PDE-facing De Giorgi pre-iteration
theorem.

This is the approximation-driven counterpart of
`deGiorgi_preiter_on_concentricBalls_of_ballPosPart`: instead of taking a
pre-built witness for `(u - θ)_+` or a generic positive-part closure axiom, it
uses the outer-ball smooth approximation package for `u - θ`. The analytic
proof still runs through the same weighted-Caccioppoli and ball-Sobolev layer. -/
theorem deGiorgi_preiter_on_concentricBalls_of_posPartApprox
    {u η : E → ℝ} {x₀ : E} {r s θ lam Cη : ℝ}
    (hd : 2 < (d : ℝ))
    (A : EllipticCoeff d (Metric.ball x₀ s))
    (hs : 0 < s) (hr : 0 < r) (hrs : r < s)
    (hsub : IsSubsolution A u)
    (hu : MemW1pWitness 2 u (Metric.ball x₀ s))
    (happroxBallTheta :
      ∃ ψ : ℕ → E → ℝ,
        (∀ n, ContDiff ℝ 1 (ψ n)) ∧
        (∀ n, HasCompactSupport (ψ n)) ∧
        Tendsto
          (fun n =>
            eLpNorm (fun x => ψ n x - (u x - θ)) 2
              (volume.restrict (Metric.ball x₀ s)))
          atTop (nhds 0) ∧
        (∀ i : Fin d,
          Tendsto
            (fun n =>
              eLpNorm
                (fun x =>
                  (fderiv ℝ (ψ n) x) (EuclideanSpace.single i 1) - hu.weakGrad x i)
                2 (volume.restrict (Metric.ball x₀ s)))
            atTop (nhds 0)))
    (hθl : θ < lam)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hη_nonneg : ∀ x, 0 ≤ η x)
    (hη_eq_one : ∀ x ∈ Metric.ball x₀ r, η x = 1)
    (hη_bound : ∀ x, |η x| ≤ 1)
    (hCη : 0 ≤ Cη)
    (hη_grad_bound : ∀ x, ‖fderiv ℝ η x‖ ≤ Cη)
    (hη_sub_ball : tsupport η ⊆ Metric.ball x₀ s) :
    ∫ x in Metric.ball x₀ r, |positivePartSub u lam x| ^ 2 ∂volume ≤
      (C_gns d 2) ^ 2 * (8 * (ellipticityRatio A + 1) * Cη ^ 2) *
        ((((lam - θ) ^ 2)⁻¹ *
            ∫ x in Metric.ball x₀ s, |positivePartSub u θ x| ^ 2 ∂volume) ^ (2 / (d : ℝ))) *
          ∫ x in Metric.ball x₀ s, |positivePartSub u θ x| ^ 2 ∂volume := by
  let hwθ : MemW1pWitness 2 (positivePartSub u θ) (Metric.ball x₀ s) :=
    positivePartSub_memW1pWitness_on_ball hs hu θ happroxBallTheta
  change
    ∫ x in Metric.ball x₀ r, |positivePartSub u lam x| ^ 2 ∂volume ≤
      (C_gns d 2) ^ 2 * (8 * (ellipticityRatio A + 1) * Cη ^ 2) *
        ((((lam - θ) ^ 2)⁻¹ *
            ∫ x in Metric.ball x₀ s, |positivePartSub u θ x| ^ 2 ∂volume) ^ (2 / (d : ℝ))) *
          ∫ x in Metric.ball x₀ s, |positivePartSub u θ x| ^ 2 ∂volume
  exact
    deGiorgi_preiter_on_concentricBalls_of_ballPosPart
      (d := d) hd A hr hrs hsub hu hwθ hθl hη hη_nonneg hη_eq_one hη_bound
      hCη hη_grad_bound hη_sub_ball

end PreiterationPDE

end DeGiorgi
