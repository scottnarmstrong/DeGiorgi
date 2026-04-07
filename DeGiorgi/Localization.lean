import DeGiorgi.BallScaling
import DeGiorgi.BallExtension
import DeGiorgi.PositivePart

/-!
# Chapter 06: Localization Helpers

This file exposes reusable local restriction and simple transport lemmas for
subsolutions, supersolutions, and solutions on balls. These results are used
throughout the Harnack and Holder arguments.
-/

noncomputable section

open MeasureTheory

namespace DeGiorgi

variable {d : ℕ} [NeZero d]

local notation "E" => AmbientSpace d

namespace EllipticCoeff

/-- Restrict an elliptic coefficient field to a smaller domain by keeping the
same coefficient matrix and constants and shrinking the a.e. coercivity domain.
-/
noncomputable def restrict
    {Ω Ω' : Set E} (A : EllipticCoeff d Ω) (hsub : Ω' ⊆ Ω) :
    EllipticCoeff d Ω' where
  a := A.a
  lam := A.lam
  Λ := A.Λ
  measurable_comp := A.measurable_comp
  hlam := A.hlam
  hΛ := A.hΛ
  coercive := ae_restrict_of_ae_restrict_of_subset hsub A.coercive
  coercive_inv := ae_restrict_of_ae_restrict_of_subset hsub A.coercive_inv

@[simp] theorem restrict_a
    {Ω Ω' : Set E} (A : EllipticCoeff d Ω) (hsub : Ω' ⊆ Ω) :
    (A.restrict hsub).a = A.a := rfl

@[simp] theorem restrict_lam
    {Ω Ω' : Set E} (A : EllipticCoeff d Ω) (hsub : Ω' ⊆ Ω) :
    (A.restrict hsub).lam = A.lam := rfl

@[simp] theorem restrict_Λ
    {Ω Ω' : Set E} (A : EllipticCoeff d Ω) (hsub : Ω' ⊆ Ω) :
    (A.restrict hsub).Λ = A.Λ := rfl

end EllipticCoeff

namespace NormalizedEllipticCoeff

/-- Restrict a normalized elliptic coefficient field to a smaller domain. -/
  noncomputable def restrict
    {Ω Ω' : Set E} (A : NormalizedEllipticCoeff d Ω) (hsub : Ω' ⊆ Ω) :
    NormalizedEllipticCoeff d Ω' := by
  refine ⟨A.1.restrict hsub, by simp⟩

end NormalizedEllipticCoeff

omit [NeZero d] in
theorem affine_preimage_ball_mul
    {x₀ : E} {R ρ : ℝ} (hR : 0 < R) :
    (fun z : E => x₀ + R • z) ⁻¹' Metric.ball x₀ (R * ρ) = Metric.ball (0 : E) ρ := by
  ext z
  simp only [Set.mem_preimage, Metric.mem_ball, dist_eq_norm]
  constructor
  · intro hz
    have hsub : x₀ + R • z - x₀ = R • z := by
      abel
    rw [hsub, norm_smul, Real.norm_of_nonneg hR.le] at hz
    have hiff : R * ‖z‖ < R * ρ ↔ ‖z‖ < ρ := by
      constructor
      · intro hh
        nlinarith
      · intro hh
        nlinarith
    simpa [sub_zero] using hiff.mp hz
  · intro hz
    have hsub : x₀ + R • z - x₀ = R • z := by
      abel
    rw [hsub, norm_smul, Real.norm_of_nonneg hR.le]
    have hiff : R * ‖z‖ < R * ρ ↔ ‖z‖ < ρ := by
      constructor
      · intro hh
        nlinarith
      · intro hh
        nlinarith
    have hz' : ‖z‖ < ρ := by
      simpa [sub_zero] using hz
    exact hiff.mpr hz'

omit [NeZero d] in
private theorem affine_map_restrict_ball_mul
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
              rw [affine_preimage_ball_mul (d := d) (x₀ := x₀) (R := R) (ρ := ρ) hR]
    _ = (Measure.map (fun z : E => x₀ + R • z) volume).restrict (Metric.ball x₀ (R * ρ)) := by
          rw [Measure.restrict_map hmeas measurableSet_ball]
    _ = (ENNReal.ofReal (|R ^ Module.finrank ℝ E|⁻¹) • (volume : Measure E)).restrict
          (Metric.ball x₀ (R * ρ)) := by
            rw [show (fun z : E => x₀ + R • z) = (fun z => x₀ + z) ∘ (fun z => R • z) from rfl]
            rw [← Measure.map_map (measurable_const_add x₀) (measurable_const_smul R)]
            rw [Measure.map_addHaar_smul volume hR.ne']
            rw [Measure.map_smul, (measurePreserving_add_left volume x₀).map_eq, abs_inv]
    _ = ENNReal.ofReal (|R ^ Module.finrank ℝ E|⁻¹) •
          (volume.restrict (Metric.ball x₀ (R * ρ))) := by
            rw [Measure.restrict_smul]

omit [NeZero d] in
private theorem affine_scale_measure_ne_zero
    {R : ℝ} (hR : 0 < R) :
    ENNReal.ofReal (|R ^ Module.finrank ℝ E|⁻¹) ≠ 0 := by
  rw [ENNReal.ofReal_ne_zero_iff]
  have hpow_ne : R ^ Module.finrank ℝ E ≠ 0 := by
    exact pow_ne_zero _ hR.ne'
  have habs_pos : 0 < |R ^ Module.finrank ℝ E| := by
    exact abs_pos.mpr hpow_ne
  exact inv_pos.mpr habs_pos

private noncomputable def affineMeasurableEmbedding
    {x₀ : E} {R : ℝ} (hR : 0 < R) :
    MeasurableEmbedding (fun z : E => x₀ + R • z) :=
  ((MeasurableEquiv.addLeft x₀).measurableEmbedding).comp
    ((Homeomorph.smulOfNeZero R hR.ne').toMeasurableEquiv.measurableEmbedding)

omit [NeZero d] in
set_option maxHeartbeats 5000000 in
theorem essSup_rescale_halfBall
    {x₀ : E} {R : ℝ} (hR : 0 < R) {u : E → ℝ} :
    essSup (fun z : E => u (x₀ + R • z))
        (volume.restrict (Metric.ball (0 : E) (1 / 2 : ℝ))) =
      essSup u (volume.restrict (Metric.ball x₀ (R / 2 : ℝ))) := by
  let μsrc : Measure E := volume.restrict (Metric.ball (0 : E) (1 / 2 : ℝ))
  let μdst : Measure E := volume.restrict (Metric.ball x₀ (R / 2 : ℝ))
  let T : E → E := fun z => x₀ + R • z
  have hmap :
      Measure.map T μsrc =
        ENNReal.ofReal (|R ^ Module.finrank ℝ E|⁻¹) • μdst := by
    simpa [μsrc, μdst, T, show R * (1 / 2 : ℝ) = R / 2 by ring] using
      affine_map_restrict_ball_mul (d := d) (x₀ := x₀) (R := R) (ρ := (1 / 2 : ℝ)) hR
  have hiff :
      ∀ a : ℝ,
        (∀ᵐ z ∂μsrc, u (T z) ≤ a) ↔ ∀ᵐ x ∂μdst, u x ≤ a := by
    intro a
    constructor
    · intro h
      have hmap_ae : ∀ᵐ x ∂ Measure.map T μsrc, u x ≤ a :=
        (affineMeasurableEmbedding (d := d) (x₀ := x₀) (R := R) hR).ae_map_iff.2 h
      rw [hmap, Measure.ae_ennreal_smul_measure_eq
        (affine_scale_measure_ne_zero (d := d) hR)] at hmap_ae
      exact hmap_ae
    · intro h
      have hmap_ae : ∀ᵐ x ∂ Measure.map T μsrc, u x ≤ a := by
        rw [hmap]
        rw [Measure.ae_ennreal_smul_measure_eq
          (affine_scale_measure_ne_zero (d := d) hR)]
        exact h
      exact (affineMeasurableEmbedding (d := d) (x₀ := x₀) (R := R) hR).ae_map_iff.1 hmap_ae
  rw [essSup_eq_sInf, essSup_eq_sInf]
  congr 1
  ext a
  simpa [μsrc, μdst, T, ae_iff, not_le] using hiff a

omit [NeZero d] in
set_option maxHeartbeats 5000000 in
theorem essInf_rescale_halfBall
    {x₀ : E} {R : ℝ} (hR : 0 < R) {u : E → ℝ} :
    essInf (fun z : E => u (x₀ + R • z))
        (volume.restrict (Metric.ball (0 : E) (1 / 2 : ℝ))) =
      essInf u (volume.restrict (Metric.ball x₀ (R / 2 : ℝ))) := by
  let μsrc : Measure E := volume.restrict (Metric.ball (0 : E) (1 / 2 : ℝ))
  let μdst : Measure E := volume.restrict (Metric.ball x₀ (R / 2 : ℝ))
  let T : E → E := fun z => x₀ + R • z
  have hmap :
      Measure.map T μsrc =
        ENNReal.ofReal (|R ^ Module.finrank ℝ E|⁻¹) • μdst := by
    simpa [μsrc, μdst, T, show R * (1 / 2 : ℝ) = R / 2 by ring] using
      affine_map_restrict_ball_mul (d := d) (x₀ := x₀) (R := R) (ρ := (1 / 2 : ℝ)) hR
  have hiff :
      ∀ a : ℝ,
        (∀ᵐ z ∂μsrc, a ≤ u (T z)) ↔ ∀ᵐ x ∂μdst, a ≤ u x := by
    intro a
    constructor
    · intro h
      have hmap_ae : ∀ᵐ x ∂ Measure.map T μsrc, a ≤ u x :=
        (affineMeasurableEmbedding (d := d) (x₀ := x₀) (R := R) hR).ae_map_iff.2 h
      rw [hmap, Measure.ae_ennreal_smul_measure_eq
        (affine_scale_measure_ne_zero (d := d) hR)] at hmap_ae
      exact hmap_ae
    · intro h
      have hmap_ae : ∀ᵐ x ∂ Measure.map T μsrc, a ≤ u x := by
        rw [hmap]
        rw [Measure.ae_ennreal_smul_measure_eq
          (affine_scale_measure_ne_zero (d := d) hR)]
        exact h
      exact (affineMeasurableEmbedding (d := d) (x₀ := x₀) (R := R) hR).ae_map_iff.1 hmap_ae
  rw [essInf_eq_sSup, essInf_eq_sSup]
  congr 1
  ext a
  simpa [μsrc, μdst, T, ae_iff, not_le] using hiff a

omit [NeZero d] in
private lemma ball_indicator_support_subset_closedBall
    {c : E} {r : ℝ} {φ : E → ℝ} :
    Function.support ((Metric.ball c r).indicator φ) ⊆ Metric.closedBall c r := by
  intro x hx
  by_contra hx_closed
  have hxball : x ∉ Metric.ball c r := by
    intro hxball
    exact hx_closed (Metric.mem_closedBall.2 (le_of_lt (Metric.mem_ball.1 hxball)))
  have hzero : (Metric.ball c r).indicator φ x = 0 := by
    simp [hxball]
  exact hx hzero

omit [NeZero d] in
private lemma ball_indicator_tsupport_subset_closedBall
    {c : E} {r : ℝ} {φ : E → ℝ} :
    tsupport ((Metric.ball c r).indicator φ) ⊆ Metric.closedBall c r := by
  calc
    tsupport ((Metric.ball c r).indicator φ)
        ⊆ closure (Function.support ((Metric.ball c r).indicator φ)) := by
          simp [tsupport]
    _ ⊆ closure (Metric.closedBall c r) := by
          exact closure_mono
            (ball_indicator_support_subset_closedBall (c := c) (r := r) (φ := φ))
    _ = Metric.closedBall c r := by
          rw [(Metric.isClosed_closedBall : IsClosed (Metric.closedBall c r)).closure_eq]

theorem memH01_indicator_ball_of_closedBall_subset
    {Ω : Set E} (hΩ : IsOpen Ω)
    {c : E} {r : ℝ} (_hr : 0 < r)
    (hsub : Metric.closedBall c r ⊆ Ω)
    {φ : E → ℝ} (hφ0 : MemH01 φ (Metric.ball c r)) :
    MemH01 ((Metric.ball c r).indicator φ) Ω := by
  let hφ0_real : MemW01p (ENNReal.ofReal (2 : ℝ)) φ (Metric.ball c r) := by
    simpa using hφ0
  have hball0 : MemW01p 2 ((Metric.ball c r).indicator φ) Set.univ := by
    simpa using
      (zeroExtend_memW01p_p (d := d) Metric.isOpen_ball
        (p := 2) (by norm_num : (1 : ℝ) < 2) hφ0_real)
  let hballw : MemW1pWitness 2 ((Metric.ball c r).indicator φ) Set.univ :=
    MemW1p.someWitness (MemW01p.memW1p hball0)
  have hball_memW1p_Ω :
      MemW1p (ENNReal.ofReal (2 : ℝ)) ((Metric.ball c r).indicator φ) Ω := by
    simpa using (hballw.restrict hΩ (by intro x hx; simp)).memW1p
  have hcompact :
      HasCompactSupport ((Metric.ball c r).indicator φ) := by
    refine HasCompactSupport.intro'
      (isCompact_closedBall c r) Metric.isClosed_closedBall ?_
    intro x hx
    have hxball : x ∉ Metric.ball c r := by
      intro hxball
      exact hx (Metric.mem_closedBall.2 (le_of_lt (Metric.mem_ball.1 hxball)))
    simp [hxball]
  have htsub : tsupport ((Metric.ball c r).indicator φ) ⊆ Ω := by
    exact (ball_indicator_tsupport_subset_closedBall (c := c) (r := r) (φ := φ)).trans hsub
  simpa using
    (memW01p_of_memW1p_of_tsupport_subset
      (d := d) hΩ (by norm_num : (1 : ℝ) < 2) hball_memW1p_Ω hcompact htsub)

noncomputable def ballIndicatorWitnessOn
    {Ω : Set E} (hΩ : IsOpen Ω)
    {c : E} {r : ℝ} {φ : E → ℝ}
    (hφ0 : MemH01 φ (Metric.ball c r))
    (hφ : MemW1pWitness 2 φ (Metric.ball c r)) :
    MemW1pWitness 2 ((Metric.ball c r).indicator φ) Ω := by
  let hφ0_real : MemW01p (ENNReal.ofReal (2 : ℝ)) φ (Metric.ball c r) := by
    simpa using hφ0
  let hφ_real : MemW1pWitness (ENNReal.ofReal (2 : ℝ)) φ (Metric.ball c r) := by
    refine
      { memLp := ?_
        weakGrad := hφ.weakGrad
        weakGrad_component_memLp := ?_
        isWeakGrad := hφ.isWeakGrad }
    · simpa using hφ.memLp
    · intro i
      simpa using hφ.weakGrad_component_memLp i
  let hφExtUniv : MemW1pWitness (ENNReal.ofReal (2 : ℝ)) ((Metric.ball c r).indicator φ) Set.univ :=
    zeroExtend_memW1pWitness_p (d := d) Metric.isOpen_ball
      (p := 2) (by norm_num : (1 : ℝ) < 2) hφ0_real hφ_real
  have htwo : ENNReal.ofReal (2 : ℝ) = (2 : ENNReal) := by
    norm_num
  simpa [htwo] using hφExtUniv.restrict hΩ (by intro x hx; simp)

omit [NeZero d] in
@[simp] private lemma cast_MemW1pWitness_weakGrad
    {p q : ENNReal} {Ω : Set E} {f : E → ℝ}
    (hpq : p = q) (h : MemW1pWitness p f Ω) :
    (Eq.mp (by cases hpq; rfl : MemW1pWitness p f Ω = MemW1pWitness q f Ω) h).weakGrad =
      h.weakGrad := by
  cases hpq
  rfl

@[simp] private lemma ballIndicatorWitnessOn_weakGrad_apply
    {Ω : Set E} (hΩ : IsOpen Ω)
    {c : E} {r : ℝ} {φ : E → ℝ}
    (hφ0 : MemH01 φ (Metric.ball c r))
    (hφ : MemW1pWitness 2 φ (Metric.ball c r))
    (x : E) (i : Fin d) :
    (ballIndicatorWitnessOn (d := d) hΩ hφ0 hφ).weakGrad x i =
      (Metric.ball c r).indicator (fun y => hφ.weakGrad y i) x := by
  let hφ0_real : MemW01p (ENNReal.ofReal (2 : ℝ)) φ (Metric.ball c r) := by
    simpa using hφ0
  let hφ_real : MemW1pWitness (ENNReal.ofReal (2 : ℝ)) φ (Metric.ball c r) := by
    refine
      { memLp := ?_
        weakGrad := hφ.weakGrad
        weakGrad_component_memLp := ?_
        isWeakGrad := hφ.isWeakGrad }
    · simpa using hφ.memLp
    · intro j
      simpa using hφ.weakGrad_component_memLp j
  have htwo : ENNReal.ofReal (2 : ℝ) = (2 : ENNReal) := by
    norm_num
  let hφExtUniv : MemW1pWitness (ENNReal.ofReal (2 : ℝ)) ((Metric.ball c r).indicator φ) Set.univ :=
    zeroExtend_memW1pWitness_p (d := d) Metric.isOpen_ball
      (p := 2) (by norm_num : (1 : ℝ) < 2) hφ0_real hφ_real
  let hφExt : MemW1pWitness (ENNReal.ofReal (2 : ℝ)) ((Metric.ball c r).indicator φ) Ω :=
    hφExtUniv.restrict hΩ (by intro y hy; simp)
  have hcast :
      (ballIndicatorWitnessOn (d := d) hΩ hφ0 hφ).weakGrad = hφExt.weakGrad := by
    unfold ballIndicatorWitnessOn
    simpa [htwo, hφExtUniv, hφExt] using
      cast_MemW1pWitness_weakGrad htwo hφExt
  have hraw :
      hφExt.weakGrad x i = (Metric.ball c r).indicator (fun y => hφ.weakGrad y i) x := by
    simp [hφExt, hφExtUniv, zeroExtend_memW1pWitness_p, MemW1pWitness.restrict, hφ_real]
  simpa [hcast] using hraw

set_option maxHeartbeats 50000 in
theorem bilinForm_ball_restrict_eq_zeroExtend
    {Ω : Set E} (hΩ : IsOpen Ω)
    (A : EllipticCoeff d Ω)
    {c : E} {r : ℝ} (_hr : 0 < r)
    (hsub : Metric.closedBall c r ⊆ Ω)
    {u : E → ℝ}
    (hu : MemW1pWitness 2 u Ω)
    {φ : E → ℝ}
    (hφ0 : MemH01 φ (Metric.ball c r))
    (hφ : MemW1pWitness 2 φ (Metric.ball c r)) :
    bilinFormOfCoeff (A.restrict (Metric.ball_subset_closedBall.trans hsub))
        (hu.restrict Metric.isOpen_ball (Metric.ball_subset_closedBall.trans hsub)) hφ =
      bilinFormOfCoeff A hu (ballIndicatorWitnessOn (d := d) hΩ hφ0 hφ) := by
  let hφExt : MemW1pWitness 2 ((Metric.ball c r).indicator φ) Ω :=
    ballIndicatorWitnessOn (d := d) hΩ hφ0 hφ
  let A' : EllipticCoeff d (Metric.ball c r) :=
    A.restrict (Metric.ball_subset_closedBall.trans hsub)
  let hu' : MemW1pWitness 2 u (Metric.ball c r) :=
    hu.restrict Metric.isOpen_ball (Metric.ball_subset_closedBall.trans hsub)
  let fsmall : E → ℝ := fun x => bilinFormIntegrandOfCoeff A' hu' hφ x
  have hball_sub : Metric.ball c r ⊆ Ω := by
    intro x hx
    exact hsub (Metric.mem_closedBall.2 (le_of_lt (Metric.mem_ball.1 hx)))
  have hEq_ae :
      (fun x => (Metric.ball c r).indicator fsmall x) =ᵐ[volume.restrict Ω]
        fun x => bilinFormIntegrandOfCoeff A hu hφExt x := by
    filter_upwards with x
    by_cases hx : x ∈ Metric.ball c r
    · have hgradφ : hφExt.weakGrad x = hφ.weakGrad x := by
        apply PiLp.ext
        intro i
        simp [hφExt, ballIndicatorWitnessOn_weakGrad_apply, hx]
      simp [A', hu', fsmall, hφExt, hgradφ, EllipticCoeff.restrict,
        MemW1pWitness.restrict, hx, bilinFormIntegrandOfCoeff]
    · have hgradφ : hφExt.weakGrad x = 0 := by
        apply PiLp.ext
        intro i
        simp [hφExt, ballIndicatorWitnessOn_weakGrad_apply, hx]
      simp [A', hu', fsmall, hφExt, hgradφ, EllipticCoeff.restrict,
        MemW1pWitness.restrict, hx, bilinFormIntegrandOfCoeff]
  calc
    bilinFormOfCoeff A' hu' hφ
      = ∫ x in Metric.ball c r, fsmall x ∂(volume.restrict Ω) := by
          simp [bilinFormOfCoeff, fsmall, Measure.restrict_restrict_of_subset hball_sub]
    _ = ∫ x, (Metric.ball c r).indicator fsmall x ∂(volume.restrict Ω) := by
          symm
          exact integral_indicator measurableSet_ball
    _ = ∫ x, bilinFormIntegrandOfCoeff A hu hφExt x ∂(volume.restrict Ω) := by
          exact integral_congr_ae hEq_ae
    _ = bilinFormOfCoeff A hu hφExt := by
          rfl

noncomputable def MemW1pWitness.of_ae_eq
    {Ω : Set E} {f g : E → ℝ}
    (hfg : f =ᵐ[volume.restrict Ω] g)
    (hw : MemW1pWitness 2 f Ω) :
    MemW1pWitness 2 g Ω := by
  refine
    { memLp := (memLp_congr_ae hfg).1 hw.memLp
      weakGrad := hw.weakGrad
      weakGrad_component_memLp := hw.weakGrad_component_memLp
      isWeakGrad := ?_ }
  intro i φ hφ hφ_supp hφ_sub
  have hweak := hw.isWeakGrad i φ hφ hφ_supp hφ_sub
  have hcongr :
      (fun x => g x * (fderiv ℝ φ x) (EuclideanSpace.single i 1)) =ᵐ[volume.restrict Ω]
        (fun x => f x * (fderiv ℝ φ x) (EuclideanSpace.single i 1)) := by
    filter_upwards [hfg] with x hx
    simp [hx]
  calc
    ∫ x in Ω, g x * (fderiv ℝ φ x) (EuclideanSpace.single i 1)
        = ∫ x in Ω, f x * (fderiv ℝ φ x) (EuclideanSpace.single i 1) := by
            exact integral_congr_ae hcongr
    _ = -∫ x in Ω, hw.weakGrad x i * φ x := hweak

theorem IsSubsolution.congr_ae
    {Ω : Set E} {A : EllipticCoeff d Ω} {u v : E → ℝ}
    (huv : u =ᵐ[volume.restrict Ω] v)
    (hsub : IsSubsolution A u) :
    IsSubsolution A v := by
  refine ⟨(MemW1pWitness.of_ae_eq huv (MemW1p.someWitness hsub.1)).memW1p, ?_⟩
  intro hv φ hφ hφw hφ_nonneg
  let hu : MemW1pWitness 2 u Ω := MemW1pWitness.of_ae_eq huv.symm hv
  have hineq : bilinFormOfCoeff A hu hφw ≤ 0 := hsub.2 hu φ hφ hφw hφ_nonneg
  simpa [hu, MemW1pWitness.of_ae_eq] using hineq

theorem IsSupersolution.congr_ae
    {Ω : Set E} {A : EllipticCoeff d Ω} {u v : E → ℝ}
    (huv : u =ᵐ[volume.restrict Ω] v)
    (hsuper : IsSupersolution A u) :
    IsSupersolution A v := by
  refine ⟨(MemW1pWitness.of_ae_eq huv (MemW1p.someWitness hsuper.1)).memW1p, ?_⟩
  intro hv φ hφ hφw hφ_nonneg
  let hu : MemW1pWitness 2 u Ω := MemW1pWitness.of_ae_eq huv.symm hv
  have hineq : 0 ≤ bilinFormOfCoeff A hu hφw := hsuper.2 hu φ hφ hφw hφ_nonneg
  simpa [hu, MemW1pWitness.of_ae_eq] using hineq

theorem IsSolution.congr_ae
    {Ω : Set E} {A : EllipticCoeff d Ω} {u v : E → ℝ}
    (huv : u =ᵐ[volume.restrict Ω] v)
    (hsol : IsSolution A u) :
    IsSolution A v := by
  exact ⟨hsol.1.congr_ae huv, hsol.2.congr_ae huv⟩

theorem IsSubsolution.restrict_ball
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
    _ = bilinFormOfCoeff A huw
          (ballIndicatorWitnessOn (d := d) hΩ hφ0 hφ) := by
          exact bilinForm_ball_restrict_eq_zeroExtend (d := d) hΩ A hr hsub huw hφ0 hφ
    _ ≤ 0 := hbig

theorem IsSupersolution.restrict_ball
    {Ω : Set E} (hΩ : IsOpen Ω)
    {c : E} {r : ℝ} (hr : 0 < r)
    {A : EllipticCoeff d Ω} {u : E → ℝ}
    (hsub : Metric.closedBall c r ⊆ Ω)
    (hu : IsSupersolution A u) :
    IsSupersolution (A.restrict (Metric.ball_subset_closedBall.trans hsub)) u := by
  rcases hu with ⟨hu_mem, hu_super⟩
  let huw : MemW1pWitness 2 u Ω := MemW1p.someWitness hu_mem
  refine ⟨(huw.restrict Metric.isOpen_ball (Metric.ball_subset_closedBall.trans hsub)).memW1p, ?_⟩
  intro hu' φ hφ0 hφ hφ_nonneg
  have hφ0_big :
      MemH01 ((Metric.ball c r).indicator φ) Ω :=
    memH01_indicator_ball_of_closedBall_subset (d := d) hΩ hr hsub hφ0
  let hφBig : MemW1pWitness 2 ((Metric.ball c r).indicator φ) Ω :=
    ballIndicatorWitnessOn (d := d) hΩ hφ0 hφ
  have hbig :
      0 ≤ bilinFormOfCoeff A huw hφBig := by
    exact hu_super huw _ hφ0_big hφBig (by
      intro x
      by_cases hx : x ∈ Metric.ball c r
      · simpa [hx] using hφ_nonneg x
      · simp [hx])
  calc
    0 ≤ bilinFormOfCoeff A huw
          (ballIndicatorWitnessOn (d := d) hΩ hφ0 hφ) := by
          exact hbig
    _ = bilinFormOfCoeff (A.restrict (Metric.ball_subset_closedBall.trans hsub))
          (huw.restrict Metric.isOpen_ball (Metric.ball_subset_closedBall.trans hsub)) hφ := by
          symm
          exact bilinForm_ball_restrict_eq_zeroExtend (d := d) hΩ A hr hsub huw hφ0 hφ
    _ = bilinFormOfCoeff (A.restrict (Metric.ball_subset_closedBall.trans hsub)) hu' hφ := by
          symm
          exact bilinFormOfCoeff_eq_left Metric.isOpen_ball
            (A.restrict (Metric.ball_subset_closedBall.trans hsub))
            hu' (huw.restrict Metric.isOpen_ball (Metric.ball_subset_closedBall.trans hsub)) hφ

theorem IsSolution.restrict_ball
    {Ω : Set E} (hΩ : IsOpen Ω)
    {c : E} {r : ℝ} (hr : 0 < r)
    {A : EllipticCoeff d Ω} {u : E → ℝ}
    (hsub : Metric.closedBall c r ⊆ Ω)
    (hu : IsSolution A u) :
    IsSolution (A.restrict (Metric.ball_subset_closedBall.trans hsub)) u := by
  exact ⟨hu.1.restrict_ball (d := d) hΩ hr hsub, hu.2.restrict_ball (d := d) hΩ hr hsub⟩

theorem IsSubsolution.sub_const_ball
    {c : E} {r : ℝ} (_hr : 0 < r)
    {A : EllipticCoeff d (Metric.ball c r)} {u : E → ℝ}
    (hsub : IsSubsolution A u) (k : ℝ) :
    IsSubsolution A (fun x => u x - k) := by
  haveI : IsFiniteMeasure (volume.restrict (Metric.ball c r)) := by
    rw [MeasureTheory.isFiniteMeasure_iff]
    simpa using (measure_ball_lt_top (μ := volume) (x := c) (r := r))
  let hu : MemW1pWitness 2 u (Metric.ball c r) := MemW1p.someWitness hsub.1
  let huShift : MemW1pWitness 2 (fun x => u x - k) (Metric.ball c r) :=
    hu.sub_const Metric.isOpen_ball k
  refine ⟨huShift.memW1p, ?_⟩
  intro hv φ hφ0 hφ hφ_nonneg
  let huBackRaw : MemW1pWitness 2 (fun x => (u x - k) - (-k)) (Metric.ball c r) :=
    hv.sub_const Metric.isOpen_ball (-k)
  let huBack : MemW1pWitness 2 u (Metric.ball c r) :=
    MemW1pWitness.of_ae_eq (Ω := Metric.ball c r)
      (Filter.Eventually.of_forall fun x => by ring) huBackRaw
  have hineq : bilinFormOfCoeff A huBack hφ ≤ 0 := hsub.2 huBack φ hφ0 hφ hφ_nonneg
  simpa [huBack, huBackRaw, MemW1pWitness.of_ae_eq, MemW1pWitness.sub_const,
    sub_eq_add_neg, add_assoc] using hineq

theorem IsSupersolution.sub_const_ball
    {c : E} {r : ℝ} (_hr : 0 < r)
    {A : EllipticCoeff d (Metric.ball c r)} {u : E → ℝ}
    (hsuper : IsSupersolution A u) (k : ℝ) :
    IsSupersolution A (fun x => u x - k) := by
  haveI : IsFiniteMeasure (volume.restrict (Metric.ball c r)) := by
    rw [MeasureTheory.isFiniteMeasure_iff]
    simpa using (measure_ball_lt_top (μ := volume) (x := c) (r := r))
  let hu : MemW1pWitness 2 u (Metric.ball c r) := MemW1p.someWitness hsuper.1
  let huShift : MemW1pWitness 2 (fun x => u x - k) (Metric.ball c r) :=
    hu.sub_const Metric.isOpen_ball k
  refine ⟨huShift.memW1p, ?_⟩
  intro hv φ hφ0 hφ hφ_nonneg
  let huBackRaw : MemW1pWitness 2 (fun x => (u x - k) - (-k)) (Metric.ball c r) :=
    hv.sub_const Metric.isOpen_ball (-k)
  let huBack : MemW1pWitness 2 u (Metric.ball c r) :=
    MemW1pWitness.of_ae_eq (Ω := Metric.ball c r)
      (Filter.Eventually.of_forall fun x => by ring) huBackRaw
  have hineq : 0 ≤ bilinFormOfCoeff A huBack hφ := hsuper.2 huBack φ hφ0 hφ hφ_nonneg
  simpa [huBack, huBackRaw, MemW1pWitness.of_ae_eq, MemW1pWitness.sub_const,
    sub_eq_add_neg, add_assoc] using hineq

theorem IsSolution.sub_const_ball
    {c : E} {r : ℝ} (hr : 0 < r)
    {A : EllipticCoeff d (Metric.ball c r)} {u : E → ℝ}
    (hsol : IsSolution A u) (k : ℝ) :
    IsSolution A (fun x => u x - k) := by
  exact ⟨hsol.1.sub_const_ball (d := d) hr k, hsol.2.sub_const_ball (d := d) hr k⟩

theorem IsSubsolution.neg_ball
    {c : E} {r : ℝ} (_hr : 0 < r)
    {A : EllipticCoeff d (Metric.ball c r)} {u : E → ℝ}
    (hsub : IsSubsolution A u) :
    IsSupersolution A (fun x => -u x) := by
  let hu : MemW1pWitness 2 u (Metric.ball c r) := MemW1p.someWitness hsub.1
  let hneg : MemW1pWitness 2 (fun x => -u x) (Metric.ball c r) := by
    simpa using hu.smul (-1)
  refine ⟨hneg.memW1p, ?_⟩
  intro hv φ hφ0 hφ hφ_nonneg
  let huBackRaw : MemW1pWitness 2 (fun x => (-1 : ℝ) * (-u x)) (Metric.ball c r) := hv.smul (-1)
  let huBack : MemW1pWitness 2 u (Metric.ball c r) :=
    MemW1pWitness.of_ae_eq (Ω := Metric.ball c r)
      (Filter.Eventually.of_forall fun x => by ring) huBackRaw
  have hineq : bilinFormOfCoeff A huBack hφ ≤ 0 := hsub.2 huBack φ hφ0 hφ hφ_nonneg
  have hsmul : bilinFormOfCoeff A huBack hφ = -bilinFormOfCoeff A hv hφ := by
    simpa [huBack, huBackRaw, MemW1pWitness.of_ae_eq] using
      (bilinFormOfCoeff_smul_left (-1) A hv hφ)
  rw [hsmul] at hineq
  linarith

theorem IsSupersolution.neg_ball
    {c : E} {r : ℝ} (_hr : 0 < r)
    {A : EllipticCoeff d (Metric.ball c r)} {u : E → ℝ}
    (hsuper : IsSupersolution A u) :
    IsSubsolution A (fun x => -u x) := by
  let hu : MemW1pWitness 2 u (Metric.ball c r) := MemW1p.someWitness hsuper.1
  let hneg : MemW1pWitness 2 (fun x => -u x) (Metric.ball c r) := by
    simpa using hu.smul (-1)
  refine ⟨hneg.memW1p, ?_⟩
  intro hv φ hφ0 hφ hφ_nonneg
  let huBackRaw : MemW1pWitness 2 (fun x => (-1 : ℝ) * (-u x)) (Metric.ball c r) := hv.smul (-1)
  let huBack : MemW1pWitness 2 u (Metric.ball c r) :=
    MemW1pWitness.of_ae_eq (Ω := Metric.ball c r)
      (Filter.Eventually.of_forall fun x => by ring) huBackRaw
  have hineq : 0 ≤ bilinFormOfCoeff A huBack hφ := hsuper.2 huBack φ hφ0 hφ hφ_nonneg
  have hsmul : bilinFormOfCoeff A huBack hφ = -bilinFormOfCoeff A hv hφ := by
    simpa [huBack, huBackRaw, MemW1pWitness.of_ae_eq] using
      (bilinFormOfCoeff_smul_left (-1) A hv hφ)
  rw [hsmul] at hineq
  linarith

theorem IsSolution.neg_ball
    {c : E} {r : ℝ} (hr : 0 < r)
    {A : EllipticCoeff d (Metric.ball c r)} {u : E → ℝ}
    (hsol : IsSolution A u) :
    IsSolution A (fun x => -u x) := by
  exact ⟨hsol.2.neg_ball (d := d) hr, hsol.1.neg_ball (d := d) hr⟩

end DeGiorgi
