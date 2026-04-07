import DeGiorgi.MoserIteration.Sequences
import Mathlib.Topology.MetricSpace.Thickening

/-!
# Moser Cutoff Preparation Basics

This module contains the basic cutoff, derivative, Sobolev-preparation, and local support lemmas for the Chapter 06 Moser iteration.
-/

noncomputable section

open MeasureTheory Filter

namespace DeGiorgi

variable {d : ℕ} [NeZero d]

local notation "E" => AmbientSpace d

/-- Powered cutoff used in the Moser pre-estimate:
`η · (u_+)^{p/2}`. -/
noncomputable def moserPowerCutoff
    (η u : E → ℝ) (p : ℝ) : E → ℝ :=
  fun x => η x * |max (u x) 0| ^ (p / 2)

omit [NeZero d] in
theorem moserPowerCutoff_tsupport_subset
    {u η : E → ℝ} {p s : ℝ}
    (hη_sub_ball : tsupport η ⊆ Metric.ball (0 : E) s) :
    tsupport (moserPowerCutoff (d := d) η u p) ⊆ Metric.ball (0 : E) s := by
  exact (tsupport_mul_subset_left
    (f := η) (g := fun x => |max (u x) 0| ^ (p / 2))).trans hη_sub_ball

noncomputable def moserFderivVec
    (η : E → ℝ) (x : E) : E :=
  (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ η x)

omit [NeZero d] in
lemma moserFderivVec_apply
    {η : E → ℝ} {x : E} (i : Fin d) :
    moserFderivVec η x i = (fderiv ℝ η x) (EuclideanSpace.single i 1) := by
  calc
    moserFderivVec η x i = inner ℝ (moserFderivVec η x) (EuclideanSpace.single i (1 : ℝ)) := by
      simpa using
        (EuclideanSpace.inner_single_right (i := i) (a := (1 : ℝ)) (moserFderivVec η x)).symm
    _ = ((InnerProductSpace.toDual ℝ E) (moserFderivVec η x)) (EuclideanSpace.single i (1 : ℝ)) := by
      rw [InnerProductSpace.toDual_apply_apply]
    _ = (fderiv ℝ η x) (EuclideanSpace.single i 1) := by
      simp [moserFderivVec]

omit [NeZero d] in
lemma moser_norm_fderivVec_eq_norm_fderiv
    {η : E → ℝ} {x : E} :
    ‖moserFderivVec η x‖ = ‖fderiv ℝ η x‖ := by
  dsimp [moserFderivVec]
  exact ((InnerProductSpace.toDual ℝ E).symm.norm_map (fderiv ℝ η x))

theorem moser_fderiv_norm_zero_outside_tsupport
    {f : E → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    {x : E} (hx : x ∉ tsupport f) :
    ‖fderiv ℝ f x‖ = 0 := by
  have hvec_zero : moserFderivVec f x = 0 := by
    ext i
    rw [moserFderivVec_apply]
    exact fderiv_apply_zero_outside_of_tsupport_subset
      (Ω := tsupport f) (hf := hf) (hsub := subset_rfl) hx i
  rw [← moser_norm_fderivVec_eq_norm_fderiv (η := f) (x := x), hvec_zero, norm_zero]

theorem moser_aestronglyMeasurable_matMulE
    {Ω : Set E}
    (A : EllipticCoeff d Ω)
    {G : E → E}
    (hG : AEStronglyMeasurable G (volume.restrict Ω)) :
    AEStronglyMeasurable (fun x => matMulE (A.a x) (G x)) (volume.restrict Ω) := by
  have hG_ofLp_cont : Continuous (fun y : E => (WithLp.ofLp y : Fin d → ℝ)) := by
    simpa using (PiLp.continuous_ofLp 2 (fun _ : Fin d => ℝ))
  have hG_ofLp :
      AEStronglyMeasurable (fun x => (G x).ofLp) (volume.restrict Ω) :=
    hG_ofLp_cont.comp_aestronglyMeasurable hG
  have hmulVec :
      AEMeasurable (fun x => Matrix.mulVec (A.a x) (G x).ofLp) (volume.restrict Ω) := by
    refine aemeasurable_pi_lambda _ ?_
    intro i
    have hmeas_sum :
        AEMeasurable
          (∑ j : Fin d, fun x => A.a x i j * (G x).ofLp j)
          (volume.restrict Ω) := by
      refine Finset.aemeasurable_sum (s := (Finset.univ : Finset (Fin d)))
        (f := fun j x => A.a x i j * (G x).ofLp j) ?_
      intro j _
      have hGj : AEMeasurable (fun x => (G x).ofLp j) (volume.restrict Ω) := by
        simpa using
          (Continuous.comp_aestronglyMeasurable (continuous_apply j) hG_ofLp).aemeasurable
      exact (A.measurable_apply i j).aemeasurable.mul hGj
    convert hmeas_sum using 1
    ext x
    simp [Matrix.mulVec, dotProduct]
  exact (PiLp.continuous_toLp 2 (fun _ : Fin d => ℝ)).comp_aestronglyMeasurable
    hmulVec.aestronglyMeasurable

omit [NeZero d] in
theorem moser_tendsto_eLpNorm_zero_of_dominated
    {μ : Measure E}
    {F : ℕ → E → ℝ} {H : E → ℝ}
    (hH_memLp : MemLp H 2 μ)
    (hF_meas : ∀ n, AEStronglyMeasurable (F n) μ)
    (hdom : ∀ n, ∀ᵐ x ∂μ, |F n x| ≤ H x)
    (hF_ae : ∀ᵐ x ∂μ, Tendsto (fun n => F n x) atTop (nhds 0)) :
    Tendsto (fun n => eLpNorm (F n) 2 μ) atTop (nhds 0) := by
  have huiH : UnifIntegrable (fun _ : ℕ => H) 2 μ := by
    simpa using
      (MeasureTheory.unifIntegrable_const (p := (2 : ENNReal))
        (by norm_num) (by simp) hH_memLp)
  have huiF : UnifIntegrable F 2 μ := by
    intro ε hε
    obtain ⟨δ, hδ, hδ'⟩ := huiH hε
    refine ⟨δ, hδ, fun n s hs hμs => ?_⟩
    calc
      eLpNorm (s.indicator (F n)) 2 μ ≤ eLpNorm (s.indicator H) 2 μ := by
        refine eLpNorm_mono_ae_real ?_
        filter_upwards [hdom n] with x hx
        by_cases hxs : x ∈ s
        · simpa [Set.indicator_of_mem, hxs] using hx
        · simp [Set.indicator_of_notMem, hxs]
      _ ≤ ENNReal.ofReal ε := hδ' 0 s hs hμs
  have hutH : UnifTight (fun _ : ℕ => H) 2 μ := by
    exact MeasureTheory.unifTight_const (p := (2 : ENNReal)) (by simp) hH_memLp
  have hutF : UnifTight F 2 μ := by
    intro ε hε
    obtain ⟨s, hμs, hs'⟩ := hutH hε
    refine ⟨s, hμs, fun n => ?_⟩
    calc
      eLpNorm (sᶜ.indicator (F n)) 2 μ ≤ eLpNorm (sᶜ.indicator H) 2 μ := by
        refine eLpNorm_mono_ae_real ?_
        filter_upwards [hdom n] with x hx
        by_cases hxs : x ∈ sᶜ
        · simpa [Set.indicator_of_mem, hxs] using hx
        · simp [Set.indicator_of_notMem, hxs]
      _ ≤ ε := hs' 0
  have hLpF0 :
      Tendsto (fun n => eLpNorm (F n - fun _ => (0 : ℝ)) 2 μ) atTop (nhds 0) := by
    exact
      MeasureTheory.tendsto_Lp_of_tendsto_ae
        (μ := μ) (p := (2 : ENNReal)) (hp := by norm_num) (hp' := by simp)
        (haef := hF_meas) (hg' := MeasureTheory.MemLp.zero' (p := (2 : ENNReal)) (μ := μ))
        huiF hutF hF_ae
  have hEq0 :
      (fun n => eLpNorm (F n - fun _ => (0 : ℝ)) 2 μ) =
        (fun n => eLpNorm (F n) 2 μ) := by
    funext n
    congr 1
    ext x
    simp
  rw [hEq0] at hLpF0
  exact hLpF0

theorem one_add_rpow_le_two_rpow_mul_one_add_rpow
    {t p : ℝ} (ht : 0 ≤ t) (hp : 1 ≤ p) :
    (1 + t) ^ p ≤ (2 : ℝ) ^ p * (1 + t ^ p) := by
  by_cases ht1 : t ≤ 1
  · have hbase : 1 + t ≤ 2 := by linarith
    have hpow : (1 + t) ^ p ≤ (2 : ℝ) ^ p := by
      exact Real.rpow_le_rpow (by positivity) hbase (by linarith)
    have hfac : (2 : ℝ) ^ p ≤ (2 : ℝ) ^ p * (1 + t ^ p) := by
      have htp_nonneg : 0 ≤ t ^ p := Real.rpow_nonneg ht p
      nlinarith [Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ 2) p]
    exact le_trans hpow hfac
  · have ht1' : 1 < t := by linarith
    have hbase : 1 + t ≤ 2 * t := by linarith
    calc
      (1 + t) ^ p ≤ (2 * t) ^ p := by
        exact Real.rpow_le_rpow (by positivity) hbase (by linarith)
      _ = (2 : ℝ) ^ p * t ^ p := by
        rw [Real.mul_rpow (by positivity : (0 : ℝ) ≤ 2) ht]
      _ ≤ (2 : ℝ) ^ p * (1 + t ^ p) := by
        have htp_nonneg : 0 ≤ t ^ p := Real.rpow_nonneg ht p
        have h2_nonneg : 0 ≤ (2 : ℝ) ^ p := Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ 2) p
        gcongr
        linarith

/-- Generic local Sobolev preparation on a ball: zero-extend a `W₀^{1,2}` ball
witness to the whole space, apply Sobolev, then restrict back. This is the
Chapter 06 analogue of the private Chapter 05 helper for cutoff functions. -/
theorem sobolev_prepare_on_ball
    {x₀ : E} {s : ℝ} {v : E → ℝ}
    (hd : 2 < (d : ℝ))
    (_hs : 0 < s)
    (hvW01 : MemW01p 2 v (Metric.ball x₀ s))
    (hv_support : tsupport v ⊆ Metric.ball x₀ s) :
    ∃ hwv_real :
      MemW1pWitness (ENNReal.ofReal (2 : ℝ)) v (Metric.ball x₀ s),
      eLpNorm v
          (ENNReal.ofReal ((d : ℝ) * 2 / ((d : ℝ) - 2)))
          (volume.restrict (Metric.ball x₀ s)) ≤
        ENNReal.ofReal (C_gns d 2) *
          eLpNorm (fun x => ‖hwv_real.weakGrad x‖) 2
            (volume.restrict (Metric.ball x₀ s)) := by
  classical
  let Ω : Set E := Metric.ball x₀ s
  let μ : Measure E := volume.restrict Ω
  have hΩ_open : IsOpen Ω := by
    simp [Ω]
  have hΩ_meas : MeasurableSet Ω := measurableSet_ball
  haveI : IsFiniteMeasure μ := by
    dsimp [μ, Ω]
    rw [isFiniteMeasure_restrict]
    exact measure_ball_lt_top.ne
  let hwv : MemW1pWitness 2 v Ω := Classical.choose hvW01.2
  have hv_indicator_eq : Ω.indicator v = v := by
    ext x
    by_cases hx : x ∈ Ω
    · simp [hx]
    · have hvx0 : v x = 0 := by
        exact image_eq_zero_of_notMem_tsupport (fun hxt => hx (hv_support hxt))
      simp [hx, hvx0]
  have hvW01_real : MemW01p (ENNReal.ofReal (2 : ℝ)) v Ω := by
    simpa using hvW01
  have hwv_real : MemW1pWitness (ENNReal.ofReal (2 : ℝ)) v Ω := by
    simpa using hwv
  let hwv_univ_raw :
      MemW1pWitness (ENNReal.ofReal (2 : ℝ)) (Ω.indicator v) Set.univ :=
    zeroExtend_memW1pWitness_p (d := d) hΩ_open (p := 2) (by norm_num) hvW01_real hwv_real
  let hwv_univ : MemW1pWitness (ENNReal.ofReal (2 : ℝ)) v Set.univ :=
    { memLp := by
        simpa [hv_indicator_eq] using hwv_univ_raw.memLp
      weakGrad := hwv_univ_raw.weakGrad
      weakGrad_component_memLp := hwv_univ_raw.weakGrad_component_memLp
      isWeakGrad := by
        simpa [hv_indicator_eq] using hwv_univ_raw.isWeakGrad }
  have hvW01_univ : MemW01p (ENNReal.ofReal (2 : ℝ)) v Set.univ := by
    simpa [hv_indicator_eq] using
      zeroExtend_memW01p_p (d := d) hΩ_open (p := 2) (by norm_num) hvW01_real
  let qexp := ENNReal.ofReal ((d : ℝ) * 2 / ((d : ℝ) - 2))
  obtain ⟨hwSob, hSob⟩ :=
    sobolev_of_memW01p_univ (d := d) (p := 2) (u := v) (by norm_num) hd hvW01_univ
  have hae_grad :
      hwSob.weakGrad =ᵐ[volume] hwv_univ.weakGrad := by
    simpa [Measure.restrict_univ] using
      MemW1pWitness.ae_eq_p (d := d) isOpen_univ (p := 2) (by norm_num) hwSob hwv_univ
  have hSob' :
      eLpNorm v qexp volume ≤
        ENNReal.ofReal (C_gns d 2) *
          eLpNorm (fun x => ‖hwv_univ.weakGrad x‖) 2 volume := by
    calc
      eLpNorm v qexp volume
          ≤ ENNReal.ofReal (C_gns d 2) *
              eLpNorm (fun x => ‖hwSob.weakGrad x‖) 2 volume := by
                simpa [qexp] using hSob
      _ = ENNReal.ofReal (C_gns d 2) *
            eLpNorm (fun x => ‖hwv_univ.weakGrad x‖) 2 volume := by
          congr 1
          exact eLpNorm_congr_ae (hae_grad.fun_comp (‖·‖))
  have hgrad_ext_vec :
      hwv_univ.weakGrad = Ω.indicator hwv_real.weakGrad := by
    ext x i
    by_cases hx : x ∈ Ω
    · simp [hwv_univ, hwv_univ_raw, zeroExtend_memW1pWitness_p, hx]
    · simp [hwv_univ, hwv_univ_raw, zeroExtend_memW1pWitness_p, hx]
  have hgrad_ext :
      (fun x => ‖hwv_univ.weakGrad x‖) = Ω.indicator (fun x => ‖hwv_real.weakGrad x‖) := by
    ext x
    by_cases hx : x ∈ Ω
    · simp [hgrad_ext_vec, hx]
    · simp [hgrad_ext_vec, hx]
  have hgrad_restrict :
      eLpNorm (fun x => ‖hwv_univ.weakGrad x‖) 2 volume =
        eLpNorm (fun x => ‖hwv_real.weakGrad x‖) 2 μ := by
    rw [hgrad_ext, MeasureTheory.eLpNorm_indicator_eq_eLpNorm_restrict hΩ_meas]
  have hv_support_fun : Function.support v ⊆ Ω := by
    intro x hx
    exact hv_support (subset_tsupport _ hx)
  have hv_restrict :
      eLpNorm v qexp μ = eLpNorm v qexp volume := by
    simpa [μ] using
      (MeasureTheory.eLpNorm_restrict_eq_of_support_subset
        (μ := volume) (p := qexp) hv_support_fun)
  have hSob'' :
      eLpNorm v qexp μ ≤
        ENNReal.ofReal (C_gns d 2) * eLpNorm (fun x => ‖hwv_real.weakGrad x‖) 2 μ := by
    calc
      eLpNorm v qexp μ = eLpNorm v qexp volume := hv_restrict
      _ ≤ ENNReal.ofReal (C_gns d 2) *
            eLpNorm (fun x => ‖hwv_univ.weakGrad x‖) 2 volume := hSob'
      _ = ENNReal.ofReal (C_gns d 2) * eLpNorm (fun x => ‖hwv_real.weakGrad x‖) 2 μ := by
            rw [hgrad_restrict]
  exact ⟨hwv_real, hSob''⟩

theorem isSubsolution_restrict_ball
    {Ω : Set E} (hΩ : IsOpen Ω)
    {c : E} {r : ℝ} (hr : 0 < r)
    {A : EllipticCoeff d Ω} {u : E → ℝ}
    (hsub : Metric.closedBall c r ⊆ Ω)
    (hu : IsSubsolution A u) :
    IsSubsolution (A.restrict (Metric.ball_subset_closedBall.trans hsub)) u := by
  rcases hu with ⟨hu_mem, hu_sub⟩
  let huw : MemW1pWitness 2 u Ω := MemW1p.someWitness hu_mem
  refine ⟨(huw.restrict Metric.isOpen_ball (Metric.ball_subset_closedBall.trans hsub)).memW1p, ?_⟩
  intro hu' φ hφ0 hφ hφ_nonneg
  have hφ0_big :
      MemH01 ((Metric.ball c r).indicator φ) Ω :=
    memH01_indicator_ball_of_closedBall_subset (d := d) hΩ hr hsub hφ0
  let hφBig : MemW1pWitness 2 ((Metric.ball c r).indicator φ) Ω :=
    ballIndicatorWitnessOn (d := d) hΩ hφ0 hφ
  have hbig :
      bilinFormOfCoeff A huw hφBig ≤ 0 := by
    exact hu_sub huw _ hφ0_big hφBig (by
      intro x
      by_cases hx : x ∈ Metric.ball c r
      · simpa [hx] using hφ_nonneg x
      · simp [hx])
  calc
    bilinFormOfCoeff (A.restrict (Metric.ball_subset_closedBall.trans hsub)) hu' hφ
      = bilinFormOfCoeff (A.restrict (Metric.ball_subset_closedBall.trans hsub))
          (huw.restrict Metric.isOpen_ball (Metric.ball_subset_closedBall.trans hsub)) hφ := by
            exact bilinFormOfCoeff_eq_left Metric.isOpen_ball
              (A.restrict (Metric.ball_subset_closedBall.trans hsub)) hu'
              (huw.restrict Metric.isOpen_ball (Metric.ball_subset_closedBall.trans hsub)) hφ
    _ = bilinFormOfCoeff A huw (ballIndicatorWitnessOn (d := d) hΩ hφ0 hφ) := by
          exact bilinForm_ball_restrict_eq_zeroExtend (d := d) hΩ A hr hsub huw hφ0 hφ
    _ ≤ 0 := hbig

omit [NeZero d] in
lemma affine_preimage_ball_radius
    {x₀ : E} {R ρ : ℝ} (hR : 0 < R) :
    (fun z : E => x₀ + R • z) ⁻¹' Metric.ball x₀ (R * ρ) =
      Metric.ball (0 : E) ρ := by
  ext z
  simp only [Set.mem_preimage, Metric.mem_ball, dist_eq_norm]
  have hsub : x₀ + R • z - x₀ = R • z := by
    abel
  rw [hsub, norm_smul, Real.norm_of_nonneg hR.le]
  constructor
  · intro hz
    have : ‖z‖ < ρ := by
      nlinarith
    simpa [sub_zero] using this
  · intro hz
    have hz' : ‖z‖ < ρ := by
      simpa [sub_zero] using hz
    have : R * ‖z‖ < R * ρ := by
      exact mul_lt_mul_of_pos_left hz' hR
    simpa [sub_zero] using this

omit [NeZero d] in
lemma affine_map_volume
    {x₀ : E} {R : ℝ} (hR : 0 < R) :
    Measure.map (fun z : E => x₀ + R • z) (volume : Measure E) =
      ENNReal.ofReal (|R ^ Module.finrank ℝ E|⁻¹) • (volume : Measure E) := by
  rw [show (fun z : E => x₀ + R • z) = (fun z : E => x₀ + z) ∘ (fun z : E => R • z) from rfl]
  rw [← Measure.map_map (measurable_const_add x₀) (measurable_const_smul R)]
  rw [Measure.map_addHaar_smul volume hR.ne']
  rw [Measure.map_smul, (measurePreserving_add_left volume x₀).map_eq, abs_inv]

omit [NeZero d] in
lemma affine_map_restrict_ball_radius
    {x₀ : E} {R ρ : ℝ} (hR : 0 < R) :
    Measure.map (fun z : E => x₀ + R • z) (volume.restrict (Metric.ball (0 : E) ρ)) =
      ENNReal.ofReal (|R ^ Module.finrank ℝ E|⁻¹) •
        (volume.restrict (Metric.ball x₀ (R * ρ))) := by
  have hmeas : Measurable (fun z : E => x₀ + R • z) :=
    (measurable_const_add x₀).comp (measurable_const_smul R)
  calc
    Measure.map (fun z : E => x₀ + R • z) (volume.restrict (Metric.ball (0 : E) ρ))
        = Measure.map (fun z : E => x₀ + R • z)
            (volume.restrict ((fun z : E => x₀ + R • z) ⁻¹' Metric.ball x₀ (R * ρ))) := by
              rw [affine_preimage_ball_radius (d := d) (x₀ := x₀) (R := R) (ρ := ρ) hR]
    _ = (Measure.map (fun z : E => x₀ + R • z) volume).restrict (Metric.ball x₀ (R * ρ)) := by
          rw [Measure.restrict_map hmeas measurableSet_ball]
    _ = (ENNReal.ofReal (|R ^ Module.finrank ℝ E|⁻¹) • (volume : Measure E)).restrict
          (Metric.ball x₀ (R * ρ)) := by
            rw [affine_map_volume (d := d) (x₀ := x₀) hR]
    _ = ENNReal.ofReal (|R ^ Module.finrank ℝ E|⁻¹) •
          (volume.restrict (Metric.ball x₀ (R * ρ))) := by
            rw [Measure.restrict_smul]

omit [NeZero d] in
lemma affine_scale_measure_ne_zero
    {R : ℝ} (hR : 0 < R) :
    ENNReal.ofReal (|R ^ Module.finrank ℝ E|⁻¹) ≠ 0 := by
  rw [ENNReal.ofReal_ne_zero_iff]
  have hpow_ne : R ^ Module.finrank ℝ E ≠ 0 := by
    exact pow_ne_zero _ hR.ne'
  have habs_pos : 0 < |R ^ Module.finrank ℝ E| := by
    exact abs_pos.mpr hpow_ne
  exact inv_pos.mpr habs_pos

theorem local_ae_bound_on_halfBall_of_subsolution
    (hd : 2 < (d : ℝ))
    (A : NormalizedEllipticCoeff d (Metric.ball (0 : E) 1))
    {u : E → ℝ} {x₀ : E} {R : ℝ}
    (hR : 0 < R)
    (hball_sub : Metric.closedBall x₀ R ⊆ Metric.ball (0 : E) 1)
    (hsub : IsSubsolution A.1 u)
    (hu1 : MemW1pWitness 2 u (Metric.ball (0 : E) 1)) :
    ∃ lamStar : ℝ, 0 < lamStar ∧
      ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ (R / 2))), max (u x) 0 ≤ lamStar := by
  let Aball : NormalizedEllipticCoeff d (Metric.ball x₀ R) :=
    ⟨A.1.restrict (Metric.ball_subset_closedBall.trans hball_sub), A.2⟩
  have hsub_ball : IsSubsolution Aball.1 u := by
    simpa [Aball] using
      isSubsolution_restrict_ball (d := d) (Ω := Metric.ball (0 : E) 1)
        Metric.isOpen_ball (c := x₀) (r := R) hR hball_sub hsub
  let huBall : MemW1pWitness 2 u (Metric.ball x₀ R) :=
    hu1.restrict Metric.isOpen_ball (Metric.ball_subset_closedBall.trans hball_sub)
  let huR := huBall.rescale_to_unitBall (d := d) (x₀ := x₀) (R := R) hR
  have hposInt_scaled :
      IntegrableOn
        (fun z => |max (rescaleToUnitBall (d := d) (x₀ := x₀) (R := R) u z) 0| ^ 2)
        (Metric.ball (0 : E) 1) volume := by
    simpa [huR, rescaleToUnitBall, pow_two] using huR.memLp.pos_part.integrable_sq
  have hsub_scaled :
      IsSubsolution
        (rescaleNormalizedCoeffToUnitBall (d := d) (x₀ := x₀) (R := R) hR Aball).1
        (rescaleToUnitBall (d := d) (x₀ := x₀) (R := R) u) := by
    simpa [Aball] using
      rescaleToUnitBall_isSubsolution (d := d) (x₀ := x₀) (R := R) hR Aball.1 hsub_ball
  obtain ⟨lamStar, hlam_pos, -, hbound_unit⟩ :=
    linfty_subsolution_DeGiorgi_exists_threshold (d := d) hd
      (rescaleNormalizedCoeffToUnitBall (d := d) (x₀ := x₀) (R := R) hR Aball).1
      (u := rescaleToUnitBall (d := d) (x₀ := x₀) (R := R) u)
      hsub_scaled hposInt_scaled
  let T : E → E := fun z => x₀ + R • z
  let hT : E ≃ₜ E :=
    (Homeomorph.smulOfNeZero R hR.ne').trans (Homeomorph.addRight x₀)
  have hT_emb : MeasurableEmbedding T := by
    convert hT.toMeasurableEquiv.measurableEmbedding using 1
    ext z
    simp [hT, T, add_comm]
  have hbound_map :
      ∀ᵐ y ∂ Measure.map T (volume.restrict (Metric.ball (0 : E) (1 / 2 : ℝ))),
        max (u y) 0 ≤ lamStar := by
    exact (hT_emb.ae_map_iff).2 (by simpa [T, rescaleToUnitBall] using hbound_unit)
  have hmap_half :
      Measure.map T (volume.restrict (Metric.ball (0 : E) (1 / 2 : ℝ))) =
        ENNReal.ofReal (|R ^ Module.finrank ℝ E|⁻¹) •
          (volume.restrict (Metric.ball x₀ (R / 2))) := by
    simpa [T, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      affine_map_restrict_ball_radius (d := d) (x₀ := x₀) (R := R) (ρ := (1 / 2 : ℝ)) hR
  rw [hmap_half] at hbound_map
  exact ⟨lamStar, hlam_pos,
    (Measure.ae_ennreal_smul_measure_iff
      (affine_scale_measure_ne_zero (d := d) (R := R) hR)).1 hbound_map⟩

theorem qualitative_bound_on_tsupport_of_subsolution
    (hd : 2 < (d : ℝ))
    (A : NormalizedEllipticCoeff d (Metric.ball (0 : E) 1))
    {u η : E → ℝ} {s : ℝ}
    (_hs : 0 < s) (hs1 : s ≤ 1)
    (hsub : IsSubsolution A.1 u)
    (hu1 : MemW1pWitness 2 u (Metric.ball (0 : E) 1))
    (hη_sub_ball : tsupport η ⊆ Metric.ball (0 : E) s) :
    ∃ N0 : ℝ, 0 < N0 ∧
      ∀ᵐ x ∂(volume.restrict (Metric.ball (0 : E) s)),
        x ∈ tsupport η → max (u x) 0 ≤ N0 := by
  classical
  let K : Set E := tsupport η
  have hη_comp : HasCompactSupport η :=
    hasCompactSupport_of_tsupport_subset_ball (f := η) hη_sub_ball
  have hK_compact : IsCompact K := by
    simpa [K] using hη_comp.isCompact
  obtain ⟨δ, hδ_pos, hδ_sub⟩ :=
    hK_compact.exists_cthickening_subset_open Metric.isOpen_ball hη_sub_ball
  let U : K → Set E := fun y => Metric.ball (y : E) (δ / 2)
  have hU_open : ∀ y : K, IsOpen (U y) := by
    intro y
    exact Metric.isOpen_ball
  have hU_cover : K ⊆ ⋃ y : K, U y := by
    intro x hx
    exact Set.mem_iUnion.2 ⟨⟨x, hx⟩, by
      change x ∈ Metric.ball x (δ / 2)
      exact Metric.mem_ball_self (show 0 < δ / 2 by positivity)⟩
  obtain ⟨t, ht_cover⟩ := hK_compact.elim_finite_subcover U hU_open hU_cover
  have houter_sub (y : K) : Metric.closedBall (y : E) δ ⊆ Metric.ball (0 : E) 1 := by
    exact (Metric.closedBall_subset_cthickening y.2 δ).trans
      (hδ_sub.trans (Metric.ball_subset_ball hs1))
  have hlocal :
      ∀ y : K,
        ∃ lamStar : ℝ, 0 < lamStar ∧
          ∀ᵐ x ∂(volume.restrict (Metric.ball (y : E) (δ / 2))),
            max (u x) 0 ≤ lamStar := by
    intro y
    exact
      local_ae_bound_on_halfBall_of_subsolution (d := d) hd A
        (u := u) (x₀ := (y : E)) (R := δ) hδ_pos (houter_sub y) hsub hu1
  choose lam hlam_pos hlam_ae using hlocal
  have hall_aux :
      ∀ t' : Finset K,
        ∀ᵐ x ∂(volume.restrict (Metric.ball (0 : E) s)),
          ∀ y ∈ t', x ∈ Metric.ball (y : E) (δ / 2) → max (u x) 0 ≤ lam y := by
    intro t'
    classical
    induction t' using Finset.induction_on with
    | empty =>
        exact Filter.Eventually.of_forall fun _ y hy => False.elim (by simp at hy)
    | @insert y t hy ih =>
        have hy_sub_ball : Metric.ball (y : E) (δ / 2) ⊆ Metric.ball (0 : E) s := by
          have hhalf_le : δ / 2 ≤ δ := by linarith
          exact (Metric.ball_subset_closedBall.trans
            (Metric.closedBall_subset_cthickening y.2 (δ / 2))).trans
              ((Metric.cthickening_mono hhalf_le K).trans hδ_sub)
        have hy_on_Ω :
            ∀ᵐ x ∂(volume.restrict (Metric.ball (0 : E) s)),
              x ∈ Metric.ball (y : E) (δ / 2) → max (u x) 0 ≤ lam y := by
          have hy_restrict :
              ∀ᵐ x ∂(volume.restrict (Metric.ball (0 : E) s)).restrict
                  (Metric.ball (y : E) (δ / 2)),
                max (u x) 0 ≤ lam y := by
            simpa [Measure.restrict_restrict_of_subset hy_sub_ball] using hlam_ae y
          exact (ae_restrict_iff' measurableSet_ball).1 hy_restrict
        filter_upwards [hy_on_Ω, ih] with x hx_y hx_t z hz hzmem
        by_cases hzy : z = y
        · subst hzy
          exact hx_y hzmem
        · exact hx_t z (by simpa [hzy] using hz) hzmem
  let N0 : ℝ := 1 + t.sum fun y => lam y
  have hall :
      ∀ᵐ x ∂(volume.restrict (Metric.ball (0 : E) s)),
        ∀ y ∈ t, x ∈ Metric.ball (y : E) (δ / 2) → max (u x) 0 ≤ lam y :=
    hall_aux t
  refine ⟨N0, by
    dsimp [N0]
    have hsum_nonneg : 0 ≤ t.sum fun y => lam y := by
      exact Finset.sum_nonneg fun y _ => (hlam_pos y).le
    linarith, ?_⟩
  filter_upwards [hall] with x hx_all hxK
  have hx_cover : x ∈ ⋃ y ∈ t, Metric.ball (y : E) (δ / 2) := ht_cover hxK
  rw [Set.mem_iUnion] at hx_cover
  obtain ⟨y, hx_cover⟩ := hx_cover
  rw [Set.mem_iUnion] at hx_cover
  obtain ⟨hy_mem, hxy⟩ := hx_cover
  have hxy_bound : max (u x) 0 ≤ lam y := hx_all y hy_mem hxy
  have hsum_ge : lam y ≤ t.sum fun z => lam z := by
    exact Finset.single_le_sum (fun z _ => (hlam_pos z).le) hy_mem
  have hN0_ge : lam y ≤ N0 := by
    dsimp [N0]
    linarith
  exact hxy_bound.trans hN0_ge

omit [NeZero d] in
theorem exists_lt_one_ball_of_tsupport_subset_ball
    {η : E → ℝ} {s : ℝ}
    (hs : 0 < s)
    (_hs1 : s ≤ 1)
    (hη_sub_ball : tsupport η ⊆ Metric.ball (0 : E) s) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < s ∧ tsupport η ⊆ Metric.ball (0 : E) ρ := by
  classical
  let K : Set E := tsupport η
  by_cases hK_empty : K = ∅
  · refine ⟨s / 2, by positivity, by linarith, ?_⟩
    simp [K, hK_empty]
  · have hK_compact : IsCompact K := by
      simpa [K] using (hasCompactSupport_of_tsupport_subset_ball (f := η) hη_sub_ball).isCompact
    have hK_nonempty : K.Nonempty := Set.nonempty_iff_ne_empty.mpr hK_empty
    let S : Set ℝ := (fun x : E => ‖x‖) '' K
    have hS_compact : IsCompact S := by
      simpa [S] using hK_compact.image_of_continuousOn continuous_norm.continuousOn
    have hS_nonempty : S.Nonempty := by
      rcases hK_nonempty with ⟨x, hx⟩
      exact ⟨‖x‖, ⟨x, hx, rfl⟩⟩
    obtain ⟨M, hMgreatest⟩ := hS_compact.exists_isGreatest hS_nonempty
    obtain ⟨xM, hxMK, hxMnorm⟩ := hMgreatest.1
    have hM_lt_s : M < s := by
      have hxM_ball : xM ∈ Metric.ball (0 : E) s := hη_sub_ball hxMK
      simpa [hxMnorm, Metric.mem_ball, dist_zero_right] using hxM_ball
    let ρ : ℝ := (M + s) / 2
    refine ⟨ρ, ?_, ?_, ?_⟩
    · dsimp [ρ]
      have hM_nonneg : 0 ≤ M := by
        rcases hK_nonempty with ⟨x, hx⟩
        have hxS : ‖x‖ ∈ S := ⟨x, hx, rfl⟩
        exact le_trans (norm_nonneg _) (hMgreatest.2 hxS)
      linarith
    · dsimp [ρ]
      linarith
    · intro x hxK
      have hxS : ‖x‖ ∈ S := ⟨x, hxK, rfl⟩
      have hnorm_le : ‖x‖ ≤ M := hMgreatest.2 hxS
      have hnorm_lt_ρ : ‖x‖ < ρ := by
        dsimp [ρ]
        linarith
      simpa [Metric.mem_ball, dist_zero_right] using hnorm_lt_ρ

theorem moser_comp_abs_le_linear
    {Φ : ℝ → ℝ}
    (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (hΦ0 : Φ 0 = 0)
    (hΦ'_bdd : ∃ M, ∀ t, |deriv Φ t| ≤ M) :
    ∃ M, 0 ≤ M ∧ ∀ t, |Φ t| ≤ M * |t| := by
  obtain ⟨M, hM⟩ := hΦ'_bdd
  have hM_nonneg : 0 ≤ M := le_trans (abs_nonneg _) (hM 0)
  have hΦ_lip : LipschitzWith ⟨M, hM_nonneg⟩ Φ :=
    lipschitzWith_of_nnnorm_deriv_le (hΦ.differentiable (by simp)) (fun t => by
      simp only [← NNReal.coe_le_coe, NNReal.coe_mk, coe_nnnorm]
      exact (Real.norm_eq_abs _).symm ▸ hM t)
  refine ⟨M, hM_nonneg, ?_⟩
  intro t
  have ht := hΦ_lip.dist_le_mul t 0
  simpa [Real.dist_eq, hΦ0, Real.norm_eq_abs] using ht

/-- Smooth bounded-derivative composition helper for Chapter 06.

This keeps the nonlinear Moser work inside Chapter 06 from having to rebuild
the generic chain-rule packaging every time we introduce a regularized power or
test function. -/
noncomputable def MemW1pWitness.comp_smooth_bounded
    {Ω : Set E} (hΩ : IsOpen Ω)
    {u : E → ℝ} (hu : MemW1pWitness 2 u Ω)
    (Φ : ℝ → ℝ) (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (hΦ0 : Φ 0 = 0)
    (hΦ'_bdd : ∃ M, ∀ t, |deriv Φ t| ≤ M) :
    MemW1pWitness 2 (fun x => Φ (u x)) Ω := by
  classical
  let M : ℝ := Classical.choose hΦ'_bdd
  have hM : ∀ t, |deriv Φ t| ≤ M := Classical.choose_spec hΦ'_bdd
  have hM_nonneg : 0 ≤ M := le_trans (abs_nonneg _) (hM 0)
  have hΦ_lip : LipschitzWith ⟨M, hM_nonneg⟩ Φ :=
    lipschitzWith_of_nnnorm_deriv_le (hΦ.differentiable (by simp)) (fun t => by
      simp only [← NNReal.coe_le_coe, NNReal.coe_mk, coe_nnnorm]
      exact (Real.norm_eq_abs _).symm ▸ hM t)
  have hΦ_abs_le : ∀ t, |Φ t| ≤ M * |t| := by
    intro t
    have ht := hΦ_lip.dist_le_mul t 0
    simpa [Real.dist_eq, hΦ0, Real.norm_eq_abs] using ht
  have hcomp_memLp :
      MemLp (fun x => Φ (u x)) 2 (volume.restrict Ω) := by
    refine MemLp.of_le_mul (g := u) (c := M) hu.memLp ?_ ?_
    · exact hΦ.continuous.comp_aestronglyMeasurable hu.memLp.aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs]
        simpa [Real.norm_eq_abs, abs_mul, abs_of_nonneg hM_nonneg] using hΦ_abs_le (u x)
  exact
    { memLp := hcomp_memLp
      weakGrad := fun x => WithLp.toLp 2 fun i => deriv Φ (u x) * hu.weakGrad x i
      weakGrad_component_memLp := by
        intro i
        refine MemLp.of_le_mul (g := fun x => hu.weakGrad x i) (c := M)
          (hu.weakGrad_component_memLp i) ?_ ?_
        · exact
            (((hΦ.continuous_deriv (by simp)).comp_aestronglyMeasurable
              hu.memLp.aestronglyMeasurable).mul
              (hu.weakGrad_component_memLp i).aestronglyMeasurable)
        · exact Filter.Eventually.of_forall fun x => by
            calc
              ‖deriv Φ (u x) * hu.weakGrad x i‖
                  = |deriv Φ (u x)| * ‖hu.weakGrad x i‖ := by
                      rw [norm_mul, Real.norm_eq_abs]
              _ ≤ M * ‖hu.weakGrad x i‖ := by
                    gcongr
                    exact hM (u x)
      isWeakGrad := by
        intro i
        simpa [HasWeakPartialDeriv, HasWeakPartialDeriv'] using
          (sobolev_chain_rule (d := d) hΩ
            (hwd := hu.isWeakGrad i) (hu := hu.memW1p)
            (hg_Lp := hu.weakGrad_component_memLp i)
            (Φ := Φ) hΦ hΦ0 hΦ'_bdd) }

theorem moser_shiftApprox_on_ball_of_unitBall
    {u : E → ℝ} {s θ : ℝ}
    (_hs : 0 < s) (hs1 : s ≤ 1)
    (hu1 : MemW1pWitness 2 u (Metric.ball (0 : E) 1)) :
    ∃ ψ : ℕ → E → ℝ,
      (∀ n, ContDiff ℝ 1 (ψ n)) ∧
      (∀ n, HasCompactSupport (ψ n)) ∧
      Filter.Tendsto
        (fun n =>
          eLpNorm (fun x => ψ n x - (u x - θ)) 2
            (volume.restrict (Metric.ball (0 : E) s)))
        Filter.atTop (nhds 0) ∧
      (∀ i : Fin d,
        Filter.Tendsto
          (fun n =>
            eLpNorm
              (fun x =>
                (fderiv ℝ (ψ n) x) (EuclideanSpace.single i 1) -
                  (hu1.restrict Metric.isOpen_ball (Metric.ball_subset_ball hs1)).weakGrad x i)
              2 (volume.restrict (Metric.ball (0 : E) s)))
          Filter.atTop (nhds 0)) := by
  haveI : IsFiniteMeasure (volume.restrict (Metric.ball (0 : E) 1)) := by
    rw [isFiniteMeasure_restrict]
    exact measure_ball_lt_top.ne
  let huShift : MemW1pWitness 2 (fun x => u x - θ) (Metric.ball (0 : E) 1) :=
    hu1.sub_const Metric.isOpen_ball θ
  rcases exists_smooth_W12_approx_on_unitBall (d := d) huShift with
    ⟨ψ, hψ_smooth, hψ_compact, hψ_fun, hψ_grad⟩
  refine ⟨ψ, ?_, hψ_compact, ?_, ?_⟩
  · intro n
    exact (hψ_smooth n).of_le (by norm_num)
  · refine ENNReal.tendsto_nhds_zero.2 ?_
    intro ε hε
    filter_upwards [ENNReal.tendsto_nhds_zero.1 hψ_fun ε hε] with m hm
    exact le_trans
      (eLpNorm_mono_measure (fun x => ψ m x - (u x - θ))
        (Measure.restrict_mono_set volume (Metric.ball_subset_ball hs1)))
      hm
  · intro i
    refine ENNReal.tendsto_nhds_zero.2 ?_
    intro ε hε
    filter_upwards [ENNReal.tendsto_nhds_zero.1 (hψ_grad i) ε hε] with m hm
    have hmono :
        eLpNorm
          (fun x =>
            (fderiv ℝ (ψ m) x) (EuclideanSpace.single i 1) -
              (hu1.restrict Metric.isOpen_ball (Metric.ball_subset_ball hs1)).weakGrad x i)
          2 (volume.restrict (Metric.ball (0 : E) s)) ≤
          eLpNorm
            (fun x =>
              (fderiv ℝ (ψ m) x) (EuclideanSpace.single i 1) - hu1.weakGrad x i)
            2 (volume.restrict (Metric.ball (0 : E) 1)) := by
      simpa [MemW1pWitness.restrict] using
        (eLpNorm_mono_measure
          (fun x =>
            (fderiv ℝ (ψ m) x) (EuclideanSpace.single i 1) - hu1.weakGrad x i)
          (Measure.restrict_mono_set volume (Metric.ball_subset_ball hs1)))
    exact le_trans hmono hm

omit [NeZero d] in
theorem positivePartSub_sub_positivePartSub_eq_min_posPart
    {u : E → ℝ} {N : ℝ} (hN : 0 ≤ N) :
    (fun x => positivePartSub u 0 x - positivePartSub u N x) =
      fun x => min (max (u x) 0) N := by
  funext x
  by_cases hx0 : u x ≤ 0
  · have hsub0 : positivePartSub u 0 x = 0 := by
      simp [positivePartSub, hx0]
    have hsubN : positivePartSub u N x = 0 := by
      have hxN : u x - N ≤ 0 := by linarith
      simp [positivePartSub, hxN]
    have hmin : min (max (u x) 0) N = 0 := by
      simp [hx0, hN]
    simp [hsub0, hsubN, hmin]
  · have hx0' : 0 < u x := lt_of_not_ge hx0
    by_cases hxN : u x ≤ N
    · have hsub0 : positivePartSub u 0 x = u x := by
        simp [positivePartSub, hx0'.le]
      have hsubN : positivePartSub u N x = 0 := by
        have hxN' : u x - N ≤ 0 := by linarith
        simp [positivePartSub, hxN']
      have hmin : min (max (u x) 0) N = u x := by
        rw [show max (u x) 0 = u x by simp [hx0'.le]]
        exact min_eq_left hxN
      linarith
    · have hxN' : N < u x := lt_of_not_ge hxN
      have hsub0 : positivePartSub u 0 x = u x := by
        simp [positivePartSub, hx0'.le]
      have hsubN : positivePartSub u N x = u x - N := by
        have hxN0 : 0 ≤ u x - N := by linarith
        simp [positivePartSub, hxN0]
      have hmin : min (max (u x) 0) N = N := by
        rw [show max (u x) 0 = u x by simp [hx0'.le]]
        exact min_eq_right hxN'.le
      linarith

noncomputable def moserClippedPosPartWitness
    {u : E → ℝ} {s N : ℝ}
    (hs : 0 < s) (hs1 : s ≤ 1) (hN : 0 ≤ N)
    (hu1 : MemW1pWitness 2 u (Metric.ball (0 : E) 1)) :
    MemW1pWitness 2 (fun x => min (max (u x) 0) N) (Metric.ball (0 : E) s) := by
  let huS : MemW1pWitness 2 u (Metric.ball (0 : E) s) :=
    hu1.restrict Metric.isOpen_ball (Metric.ball_subset_ball hs1)
  have happrox0 :=
    moser_shiftApprox_on_ball_of_unitBall (d := d) (u := u) (s := s) (θ := 0) hs hs1 hu1
  have happroxN :=
    moser_shiftApprox_on_ball_of_unitBall (d := d) (u := u) (s := s) (θ := N) hs hs1 hu1
  let hw0 : MemW1pWitness 2 (positivePartSub u 0) (Metric.ball (0 : E) s) :=
    positivePartSub_memW1pWitness_on_ball (d := d) (x₀ := (0 : E)) (s := s)
      hs huS 0 happrox0
  let hwN : MemW1pWitness 2 (positivePartSub u N) (Metric.ball (0 : E) s) :=
    positivePartSub_memW1pWitness_on_ball (d := d) (x₀ := (0 : E)) (s := s)
      hs huS N happroxN
  let hwClip :
      MemW1pWitness 2
        (fun x => positivePartSub u 0 x + ((-1 : ℝ) * positivePartSub u N x))
        (Metric.ball (0 : E) s) :=
    hw0.add (hwN.smul (-1))
  have hEq :
      (fun x => min (max (u x) 0) N) =
        (fun x => positivePartSub u 0 x + ((-1 : ℝ) * positivePartSub u N x)) := by
    simpa [sub_eq_add_neg] using
      (positivePartSub_sub_positivePartSub_eq_min_posPart (u := u) hN).symm
  refine
    { memLp := by
        rw [hEq]
        simpa using hwClip.memLp
      weakGrad := hwClip.weakGrad
      weakGrad_component_memLp := hwClip.weakGrad_component_memLp
      isWeakGrad := by
        rw [hEq]
        simpa using hwClip.isWeakGrad }

lemma positivePartSub_grad_eq_on_superlevel
    {Ω : Set E}
    [IsFiniteMeasure (volume.restrict Ω)]
    (hΩ : IsOpen Ω)
    {u : E → ℝ} {k : ℝ}
    (hu : MemW1pWitness 2 u Ω)
    (hw_trunc : MemW1pWitness 2 (positivePartSub u k) Ω) :
    ∀ᵐ x ∂(volume.restrict Ω), k < u x → hu.weakGrad x = hw_trunc.weakGrad x := by
  let w : E → ℝ := positivePartSub u k
  let hw_shift : MemW1pWitness 2 (fun x => u x - k) Ω := hu.sub_const hΩ k
  let hw_diff :
      MemW1pWitness 2 (fun x => u x - k + (-1 : ℝ) * w x) Ω :=
    hw_shift.add (hw_trunc.smul (-1))
  have hcomp :
      ∀ i : Fin d, ∀ᵐ x ∂(volume.restrict Ω), k < u x → hu.weakGrad x i = hw_trunc.weakGrad x i := by
    intro i
    have hz := hw_diff.weakGrad_ae_eq_zero_on_zeroSet hΩ i
    filter_upwards [hz] with x hx hku
    have hfun : (u x - k + (-1 : ℝ) * w x) = 0 := by
      have huxk : 0 ≤ u x - k := le_of_lt (sub_pos.mpr hku)
      simp [w, positivePartSub, max_eq_left huxk]
    have hgrad0 : hw_diff.weakGrad x i = 0 := hx hfun
    have hgrad0' :
        (hu.weakGrad x).ofLp i - (hw_trunc.weakGrad x).ofLp i = 0 := by
      simpa [hw_diff, hw_shift, w, MemW1pWitness.add, MemW1pWitness.smul,
        MemW1pWitness.sub_const, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        using hgrad0
    exact sub_eq_zero.mp hgrad0'
  filter_upwards [ae_all_iff.2 hcomp] with x hx hku
  ext i
  exact hx i hku

lemma positivePartSub_grad_zero_on_sublevel
    {Ω : Set E}
    (hΩ : IsOpen Ω)
    {u : E → ℝ} {k : ℝ}
    (hw_trunc : MemW1pWitness 2 (positivePartSub u k) Ω) :
    ∀ᵐ x ∂(volume.restrict Ω), u x ≤ k → hw_trunc.weakGrad x = 0 := by
  let w : E → ℝ := positivePartSub u k
  have hcomp :
      ∀ i : Fin d, ∀ᵐ x ∂(volume.restrict Ω), u x ≤ k → hw_trunc.weakGrad x i = 0 := by
    intro i
    have hz := hw_trunc.weakGrad_ae_eq_zero_on_zeroSet hΩ i
    filter_upwards [hz] with x hx huk
    have hwx : w x = 0 := by
      have huxk : u x - k ≤ 0 := by linarith
      simp [w, positivePartSub, max_eq_right huxk]
    exact hx hwx
  filter_upwards [ae_all_iff.2 hcomp] with x hx huk
  ext i
  exact hx i huk

lemma moserClippedPosPartWitness_grad_eq_on_midrange
    {u : E → ℝ} {s N : ℝ}
    (hs : 0 < s) (hs1 : s ≤ 1) (hN : 0 ≤ N)
    (hu1 : MemW1pWitness 2 u (Metric.ball (0 : E) 1)) :
    ∀ᵐ x ∂(volume.restrict (Metric.ball (0 : E) s)),
      0 < u x → u x < N →
        (moserClippedPosPartWitness (d := d) (u := u) (s := s) (N := N) hs hs1 hN hu1).weakGrad x =
          (hu1.restrict Metric.isOpen_ball (Metric.ball_subset_ball hs1)).weakGrad x := by
  let Ω := Metric.ball (0 : E) s
  letI : IsFiniteMeasure (volume.restrict Ω) := by
    dsimp [Ω]
    rw [isFiniteMeasure_restrict]
    exact measure_ball_lt_top.ne
  let huS : MemW1pWitness 2 u Ω :=
    hu1.restrict Metric.isOpen_ball (Metric.ball_subset_ball hs1)
  let hw0 : MemW1pWitness 2 (positivePartSub u 0) Ω :=
    positivePartSub_memW1pWitness_on_ball (d := d) (x₀ := (0 : E)) (s := s)
      hs huS 0 (moser_shiftApprox_on_ball_of_unitBall (d := d) (u := u) (s := s) (θ := 0) hs hs1 hu1)
  let hwN : MemW1pWitness 2 (positivePartSub u N) Ω :=
    positivePartSub_memW1pWitness_on_ball (d := d) (x₀ := (0 : E)) (s := s)
      hs huS N (moser_shiftApprox_on_ball_of_unitBall (d := d) (u := u) (s := s) (θ := N) hs hs1 hu1)
  have h0_eq := positivePartSub_grad_eq_on_superlevel (d := d) Metric.isOpen_ball huS hw0
  have hN_zero := positivePartSub_grad_zero_on_sublevel (d := d) Metric.isOpen_ball hwN
  filter_upwards [h0_eq, hN_zero] with x hx0 hxN hu_pos hu_ltN
  have hxN_le : u x ≤ N := hu_ltN.le
  ext i
  have h0i : huS.weakGrad x i = hw0.weakGrad x i := by
    exact congrArg (fun ξ : E => ξ i) (hx0 hu_pos)
  have hNi : hwN.weakGrad x i = 0 := by
    exact congrArg (fun ξ : E => ξ i) (hxN hxN_le)
  simp [moserClippedPosPartWitness, huS, hw0, hwN, MemW1pWitness.add,
    MemW1pWitness.smul, h0i, hNi]

lemma moserClippedPosPartWitness_grad_zero_on_nonpos
    {u : E → ℝ} {s N : ℝ}
    (hs : 0 < s) (hs1 : s ≤ 1) (hN : 0 ≤ N)
    (hu1 : MemW1pWitness 2 u (Metric.ball (0 : E) 1)) :
    ∀ᵐ x ∂(volume.restrict (Metric.ball (0 : E) s)),
      u x ≤ 0 →
        (moserClippedPosPartWitness (d := d) (u := u) (s := s) (N := N) hs hs1 hN hu1).weakGrad x = 0 := by
  let Ω := Metric.ball (0 : E) s
  let huS : MemW1pWitness 2 u Ω :=
    hu1.restrict Metric.isOpen_ball (Metric.ball_subset_ball hs1)
  let hw0 : MemW1pWitness 2 (positivePartSub u 0) Ω :=
    positivePartSub_memW1pWitness_on_ball (d := d) (x₀ := (0 : E)) (s := s)
      hs huS 0 (moser_shiftApprox_on_ball_of_unitBall (d := d) (u := u) (s := s) (θ := 0) hs hs1 hu1)
  let hwN : MemW1pWitness 2 (positivePartSub u N) Ω :=
    positivePartSub_memW1pWitness_on_ball (d := d) (x₀ := (0 : E)) (s := s)
      hs huS N (moser_shiftApprox_on_ball_of_unitBall (d := d) (u := u) (s := s) (θ := N) hs hs1 hu1)
  have h0_zero := positivePartSub_grad_zero_on_sublevel (d := d) Metric.isOpen_ball hw0
  have hN_zero := positivePartSub_grad_zero_on_sublevel (d := d) Metric.isOpen_ball hwN
  filter_upwards [h0_zero, hN_zero] with x hx0 hxN hu_nonpos
  have hN_le : u x ≤ N := by linarith
  ext i
  have h0i : hw0.weakGrad x i = 0 := by
    exact congrArg (fun ξ : E => ξ i) (hx0 hu_nonpos)
  have hNi : hwN.weakGrad x i = 0 := by
    exact congrArg (fun ξ : E => ξ i) (hxN hN_le)
  simp [moserClippedPosPartWitness, huS, hw0, hwN, MemW1pWitness.add,
    MemW1pWitness.smul, h0i, hNi]

lemma moserClippedPosPartWitness_grad_zero_on_toplevel
    {u : E → ℝ} {s N : ℝ}
    (hs : 0 < s) (hs1 : s ≤ 1) (hN : 0 ≤ N)
    (hu1 : MemW1pWitness 2 u (Metric.ball (0 : E) 1)) :
    ∀ᵐ x ∂(volume.restrict (Metric.ball (0 : E) s)),
      N ≤ u x →
        (moserClippedPosPartWitness (d := d) (u := u) (s := s) (N := N) hs hs1 hN hu1).weakGrad x = 0 := by
  let Ω := Metric.ball (0 : E) s
  letI : IsFiniteMeasure (volume.restrict Ω) := by
    dsimp [Ω]
    rw [isFiniteMeasure_restrict]
    exact measure_ball_lt_top.ne
  let huS : MemW1pWitness 2 u Ω :=
    hu1.restrict Metric.isOpen_ball (Metric.ball_subset_ball hs1)
  let huSN : MemW1pWitness 2 (fun x => u x - N) Ω := huS.sub_const Metric.isOpen_ball N
  let hw0 : MemW1pWitness 2 (positivePartSub u 0) Ω :=
    positivePartSub_memW1pWitness_on_ball (d := d) (x₀ := (0 : E)) (s := s)
      hs huS 0 (moser_shiftApprox_on_ball_of_unitBall (d := d) (u := u) (s := s) (θ := 0) hs hs1 hu1)
  let hwN : MemW1pWitness 2 (positivePartSub u N) Ω :=
    positivePartSub_memW1pWitness_on_ball (d := d) (x₀ := (0 : E)) (s := s)
      hs huS N (moser_shiftApprox_on_ball_of_unitBall (d := d) (u := u) (s := s) (θ := N) hs hs1 hu1)
  have h0_eq := positivePartSub_grad_eq_on_superlevel (d := d) Metric.isOpen_ball huS hw0
  have h0_zero := positivePartSub_grad_zero_on_sublevel (d := d) Metric.isOpen_ball hw0
  have hN_eq := positivePartSub_grad_eq_on_superlevel (d := d) Metric.isOpen_ball huS hwN
  have hN_zero := positivePartSub_grad_zero_on_sublevel (d := d) Metric.isOpen_ball hwN
  have hzN := huSN.weakGrad_ae_eq_zero_on_zeroSet Metric.isOpen_ball
  filter_upwards [h0_eq, h0_zero, hN_eq, hN_zero, ae_all_iff.2 hzN] with x hx0eq hx0zero hxNeq hxNzero hz hNu
  by_cases hlt : N < u x
  · have hu_pos : 0 < u x := by linarith
    ext i
    have h0i : huS.weakGrad x i = hw0.weakGrad x i := by
      exact congrArg (fun ξ : E => ξ i) (hx0eq hu_pos)
    have hNi : huS.weakGrad x i = hwN.weakGrad x i := by
      exact congrArg (fun ξ : E => ξ i) (hxNeq hlt)
    calc
      ((moserClippedPosPartWitness (d := d) (u := u) (s := s) (N := N) hs hs1 hN hu1).weakGrad x) i
          = hw0.weakGrad x i + (-1 : ℝ) * hwN.weakGrad x i := by
              simp [moserClippedPosPartWitness, huS, hw0, hwN, MemW1pWitness.add,
                MemW1pWitness.smul]
      _ = huS.weakGrad x i + (-1 : ℝ) * huS.weakGrad x i := by rw [← h0i, ← hNi]
      _ = 0 := by ring
  · have heq : u x = N := le_antisymm (not_lt.mp hlt) hNu
    ext i
    have huSi_zero : huS.weakGrad x i = 0 := by
      have hshift_zero : huSN.weakGrad x i = 0 := by
        exact hz i (by linarith [heq])
      simpa [huSN, MemW1pWitness.sub_const] using hshift_zero
    have hNi : hwN.weakGrad x i = 0 := by
      have hxNarg : u x ≤ N := by
        rw [heq]
      exact congrArg (fun ξ : E => ξ i) (hxNzero hxNarg)
    have h0i : hw0.weakGrad x i = 0 := by
      by_cases hN0 : N = 0
      · subst hN0
        have hu_nonpos : u x ≤ 0 := by simpa using heq.le
        exact congrArg (fun ξ : E => ξ i) (hx0zero hu_nonpos)
      · have hN_pos : 0 < N := lt_of_le_of_ne hN (by simpa [eq_comm] using hN0)
        have hu_pos : 0 < u x := by linarith [heq, hN_pos]
        have h0eqi : huS.weakGrad x i = hw0.weakGrad x i := by
          exact congrArg (fun ξ : E => ξ i) (hx0eq hu_pos)
        linarith
    calc
      ((moserClippedPosPartWitness (d := d) (u := u) (s := s) (N := N) hs hs1 hN hu1).weakGrad x) i
          = hw0.weakGrad x i + (-1 : ℝ) * hwN.weakGrad x i := by
              simp [moserClippedPosPartWitness, huS, hw0, hwN, MemW1pWitness.add,
                MemW1pWitness.smul]
      _ = 0 + (-1 : ℝ) * 0 := by rw [h0i, hNi]
      _ = 0 := by ring


end DeGiorgi
