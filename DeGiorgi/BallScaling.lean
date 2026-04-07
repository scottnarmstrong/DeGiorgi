import DeGiorgi.UnitBallApproximation
import DeGiorgi.WeakFormulation

/-!
# Chapter 04: Scaling

This module packages the affine ball-to-unit-ball transport lemmas for the
weak-solution predicates introduced in `WeakFormulation`.

Its main role in the De Giorgi chain is to let the Harnack and Holder
arguments reapply unit-ball results on smaller balls without duplicating
scaling logic downstream.
-/

noncomputable section

open MeasureTheory
open scoped InnerProductSpace

namespace DeGiorgi

variable {d : ℕ} [NeZero d]

local notation "E" => AmbientSpace d

omit [NeZero d] in
private lemma affine_preimage_ball
    {x₀ : E} {R : ℝ} (hR : 0 < R) :
    (fun z : E => x₀ + R • z) ⁻¹' Metric.ball x₀ R = Metric.ball (0 : E) 1 := by
  ext z
  simp only [Set.mem_preimage, Metric.mem_ball, dist_eq_norm]
  constructor
  · intro hz
    have hsub : x₀ + R • z - x₀ = R • z := by
      abel
    rw [hsub, norm_smul, Real.norm_of_nonneg hR.le] at hz
    have hiff : R * ‖z‖ < R ↔ ‖z‖ < 1 := by
      constructor <;> intro hh <;> nlinarith
    simpa [sub_zero] using hiff.mp hz
  · intro hz
    have hsub : x₀ + R • z - x₀ = R • z := by
      abel
    rw [hsub, norm_smul, Real.norm_of_nonneg hR.le]
    have hiff : R * ‖z‖ < R ↔ ‖z‖ < 1 := by
      constructor <;> intro hh <;> nlinarith
    have hz0 : ‖z‖ < 1 := by
      simpa [sub_zero] using hz
    exact hiff.mpr hz0

omit [NeZero d] in
private lemma affine_map_volume
    {x₀ : E} {R : ℝ} (hR : 0 < R) :
    Measure.map (fun z : E => x₀ + R • z) (volume : Measure E) =
      ENNReal.ofReal (|R ^ Module.finrank ℝ E|⁻¹) • (volume : Measure E) := by
  rw [show (fun z : E => x₀ + R • z) = (fun z : E => x₀ + z) ∘ (fun z : E => R • z) from rfl]
  rw [← Measure.map_map (measurable_const_add x₀) (measurable_const_smul R)]
  rw [Measure.map_addHaar_smul volume hR.ne']
  rw [Measure.map_smul, (measurePreserving_add_left volume x₀).map_eq, abs_inv]

omit [NeZero d] in
private lemma affine_map_restrict_unitBall
    {x₀ : E} {R : ℝ} (hR : 0 < R) :
    Measure.map (fun z : E => x₀ + R • z) (volume.restrict (Metric.ball (0 : E) 1)) =
      ENNReal.ofReal (|R ^ Module.finrank ℝ E|⁻¹) •
        (volume.restrict (Metric.ball x₀ R)) := by
  have hmeas : Measurable (fun z : E => x₀ + R • z) :=
    (measurable_const_add x₀).comp (measurable_const_smul R)
  calc
    Measure.map (fun z : E => x₀ + R • z) (volume.restrict (Metric.ball (0 : E) 1))
        = Measure.map (fun z : E => x₀ + R • z)
            (volume.restrict ((fun z : E => x₀ + R • z) ⁻¹' Metric.ball x₀ R)) := by
              rw [affine_preimage_ball (d := d) hR]
    _ = (Measure.map (fun z : E => x₀ + R • z) volume).restrict (Metric.ball x₀ R) := by
          rw [Measure.restrict_map hmeas measurableSet_ball]
    _ = (ENNReal.ofReal (|R ^ Module.finrank ℝ E|⁻¹) • (volume : Measure E)).restrict
          (Metric.ball x₀ R) := by
            rw [affine_map_volume (d := d) (x₀ := x₀) hR]
    _ = ENNReal.ofReal (|R ^ Module.finrank ℝ E|⁻¹) •
          (volume.restrict (Metric.ball x₀ R)) := by
            rw [Measure.restrict_smul]

omit [NeZero d] in
private lemma affine_scale_measure_ne_zero
    {R : ℝ} (hR : 0 < R) :
    ENNReal.ofReal (|R ^ Module.finrank ℝ E|⁻¹) ≠ 0 := by
  rw [ENNReal.ofReal_ne_zero_iff]
  have hpow_ne : R ^ Module.finrank ℝ E ≠ 0 := by
    exact pow_ne_zero _ hR.ne'
  have habs_pos : 0 < |R ^ Module.finrank ℝ E| := by
    exact abs_pos.mpr hpow_ne
  exact inv_pos.mpr habs_pos

/-- Affine pullback along `z ↦ x₀ + R • z`, intended to transport functions
from `B(x₀, R)` to the unit ball. -/
noncomputable def rescaleToUnitBall
    {x₀ : E} {R : ℝ} (u : E → ℝ) : E → ℝ :=
  fun z => u (x₀ + R • z)

/-- Pull back an elliptic coefficient from `B(x₀, R)` to the unit ball. -/
noncomputable def rescaleCoeffToUnitBall
    {x₀ : E} {R : ℝ} (hR : 0 < R)
    (A : EllipticCoeff d (Metric.ball x₀ R)) :
    EllipticCoeff d (Metric.ball (0 : E) 1) := by
  refine
    { a := fun z => A.a (x₀ + R • z)
      lam := A.lam
      Λ := A.Λ
      measurable_comp := ?_
      hlam := A.hlam
      hΛ := A.hΛ
      coercive := ?_
      coercive_inv := ?_ }
  · intro i j
    let T : E → E := fun z => x₀ + R • z
    change Measurable ((fun x => A.a x i j) ∘ T)
    exact (A.measurable_comp i j).comp ((measurable_const_add x₀).comp (measurable_const_smul R))
  · let T : E → E := fun z => x₀ + R • z
    let P : E → Prop := fun x ↦
      ∀ ξ : E, (A.lam * ‖ξ‖ ^ (2 : ℕ) ≤ ⟪ξ, matMulE (A.a x) ξ⟫_ℝ)
    have hmap :
        Measure.map T (volume.restrict (Metric.ball (0 : E) 1)) =
          ENNReal.ofReal (|R ^ Module.finrank ℝ E|⁻¹) •
            (volume.restrict (Metric.ball x₀ R)) :=
      affine_map_restrict_unitBall (d := d) (x₀ := x₀) hR
    have hcoer_map :
        ∀ᵐ x ∂ Measure.map T (volume.restrict (Metric.ball (0 : E) 1)), P x := by
      rw [hmap]
      have hscale_pos : 0 < |R ^ Module.finrank ℝ E|⁻¹ := by
        have hpow_ne : R ^ Module.finrank ℝ E ≠ 0 := by
          exact pow_ne_zero _ hR.ne'
        exact inv_pos.mpr (abs_pos.mpr hpow_ne)
      have hsmul :
          (∀ᵐ x ∂ (ENNReal.ofReal (|R ^ Module.finrank ℝ E|⁻¹) •
              volume.restrict (Metric.ball x₀ R)), P x) ↔
            ∀ᵐ x ∂ volume.restrict (Metric.ball x₀ R), P x :=
        by
          simp [ae_iff]
          intro hbad
          exfalso
          exact (not_le_of_gt (pow_pos (abs_pos.mpr hR.ne') d)) hbad
      exact hsmul.2 A.coercive
    have hpull :
        ∀ᵐ z ∂ volume.restrict (Metric.ball (0 : E) 1), P (T z) :=
      ae_of_ae_map (((measurable_const_add x₀).comp (measurable_const_smul R)).aemeasurable)
        hcoer_map
    simpa [P, T] using hpull
  · let T : E → E := fun z => x₀ + R • z
    let P : E → Prop := fun x ↦
      ∀ ξ : E, (A.Λ⁻¹ * ‖ξ‖ ^ (2 : ℕ) ≤ ⟪ξ, matMulE ((A.a x)⁻¹) ξ⟫_ℝ)
    have hmap :
        Measure.map T (volume.restrict (Metric.ball (0 : E) 1)) =
          ENNReal.ofReal (|R ^ Module.finrank ℝ E|⁻¹) •
            (volume.restrict (Metric.ball x₀ R)) :=
      affine_map_restrict_unitBall (d := d) (x₀ := x₀) hR
    have hcoer_map :
        ∀ᵐ x ∂ Measure.map T (volume.restrict (Metric.ball (0 : E) 1)), P x := by
      rw [hmap]
      have hscale_pos : 0 < |R ^ Module.finrank ℝ E|⁻¹ := by
        have hpow_ne : R ^ Module.finrank ℝ E ≠ 0 := by
          exact pow_ne_zero _ hR.ne'
        exact inv_pos.mpr (abs_pos.mpr hpow_ne)
      have hsmul :
          (∀ᵐ x ∂ (ENNReal.ofReal (|R ^ Module.finrank ℝ E|⁻¹) •
              volume.restrict (Metric.ball x₀ R)), P x) ↔
            ∀ᵐ x ∂ volume.restrict (Metric.ball x₀ R), P x :=
        by
          simp [ae_iff]
          intro hbad
          exfalso
          exact (not_le_of_gt (pow_pos (abs_pos.mpr hR.ne') d)) hbad
      exact hsmul.2 A.coercive_inv
    have hpull :
        ∀ᵐ z ∂ volume.restrict (Metric.ball (0 : E) 1), P (T z) :=
      ae_of_ae_map (((measurable_const_add x₀).comp (measurable_const_smul R)).aemeasurable)
        hcoer_map
    simpa [P, T] using hpull

/-- Pull back a normalized elliptic coefficient from `B(x₀, R)` to the unit
ball. -/
noncomputable def rescaleNormalizedCoeffToUnitBall
    {x₀ : E} {R : ℝ} (hR : 0 < R)
    (A : NormalizedEllipticCoeff d (Metric.ball x₀ R)) :
    NormalizedEllipticCoeff d (Metric.ball (0 : E) 1) := by
  refine ⟨rescaleCoeffToUnitBall (d := d) (x₀ := x₀) (R := R) hR A.1, by
    simp [rescaleCoeffToUnitBall]⟩

/-- Affine pushforward from the unit ball to `B(x₀, R)`. -/
noncomputable def transportFromUnitBall
    {x₀ : E} {R : ℝ} (u : E → ℝ) : E → ℝ :=
  fun x => u (R⁻¹ • (x - x₀))

omit [NeZero d] in
theorem rescaleToUnitBall_transportFromUnitBall
    {x₀ : E} {R : ℝ} (hR : 0 < R) (u : E → ℝ) :
    rescaleToUnitBall (d := d) (x₀ := x₀) (R := R)
      (transportFromUnitBall (d := d) (x₀ := x₀) (R := R) u) = u := by
  ext z
  have hsub : x₀ + R • z - x₀ = R • z := by
    abel
  simp [rescaleToUnitBall, transportFromUnitBall, hsub, smul_smul, inv_mul_cancel₀ hR.ne']

attribute [simp] rescaleToUnitBall_transportFromUnitBall

omit [NeZero d] in
private lemma inverse_affine_preimage_unitBall
    {x₀ : E} {R : ℝ} (hR : 0 < R) :
    (fun x : E => R⁻¹ • (x - x₀)) ⁻¹' Metric.ball (0 : E) 1 = Metric.ball x₀ R := by
  ext x
  rw [Set.mem_preimage, Metric.mem_ball, dist_eq_norm, Metric.mem_ball, dist_eq_norm]
  simp only [sub_zero]
  rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hR.le)]
  constructor
  · intro hx
    rwa [inv_mul_lt_iff₀ hR, mul_one] at hx
  · intro hx
    exact (inv_mul_lt_iff₀ hR).2 (by simpa using hx)

omit [NeZero d] in
private lemma inverse_affine_map_restrict_ball
    {x₀ : E} {R : ℝ} (hR : 0 < R) :
    Measure.map (fun x : E => R⁻¹ • (x - x₀)) (volume.restrict (Metric.ball x₀ R)) =
      ENNReal.ofReal (|R⁻¹ ^ Module.finrank ℝ E|⁻¹) •
        (volume.restrict (Metric.ball (0 : E) 1)) := by
  let S : E → E := fun x => R⁻¹ • (x - x₀)
  have hmeas : Measurable S :=
    (measurable_const_smul R⁻¹).comp (measurable_id.sub measurable_const)
  have hrestrict :
      Measure.map S (volume.restrict (Metric.ball x₀ R)) =
        (Measure.map S volume).restrict (Metric.ball (0 : E) 1) := by
    simpa [S, inverse_affine_preimage_unitBall (d := d) (x₀ := x₀) hR] using
      (Measure.restrict_map (μ := volume) (f := S) hmeas
        (s := Metric.ball (0 : E) 1) measurableSet_ball).symm
  calc
    Measure.map S (volume.restrict (Metric.ball x₀ R))
        = (Measure.map S volume).restrict (Metric.ball (0 : E) 1) := hrestrict
    _ = (ENNReal.ofReal (|R⁻¹ ^ Module.finrank ℝ E|⁻¹) • (volume : Measure E)).restrict
          (Metric.ball (0 : E) 1) := by
            have hmap :
                Measure.map S (volume : Measure E) =
                  ENNReal.ofReal (|R⁻¹ ^ Module.finrank ℝ E|⁻¹) • (volume : Measure E) := by
              rw [show S = (fun z : E => R⁻¹ • z) ∘ (fun z : E => (-x₀) + z) from by
                  ext z
                  simp [S, sub_eq_add_neg, add_comm]]
              rw [← Measure.map_map (measurable_const_smul R⁻¹) (measurable_const_add (-x₀))]
              rw [(measurePreserving_add_left volume (-x₀)).map_eq]
              simpa [abs_inv] using
                (Measure.map_addHaar_smul (μ := (volume : Measure E))
                  (r := R⁻¹) (inv_ne_zero hR.ne'))
            rw [hmap]
    _ = ENNReal.ofReal (|R⁻¹ ^ Module.finrank ℝ E|⁻¹) •
          (volume.restrict (Metric.ball (0 : E) 1)) := by
            rw [Measure.restrict_smul]

omit [NeZero d] in
private lemma transportFromUnitBall_memLp
    {p : ENNReal} {x₀ : E} {R : ℝ} {u : E → ℝ}
    (hR : 0 < R)
    (hu : MemLp u p (volume.restrict (Metric.ball (0 : E) 1))) :
    MemLp (transportFromUnitBall (d := d) (x₀ := x₀) (R := R) u) p
      (volume.restrict (Metric.ball x₀ R)) := by
  let S : E → E := fun x => R⁻¹ • (x - x₀)
  let h : E ≃ₜ E := (Homeomorph.addRight (-x₀)).trans
    (Homeomorph.smulOfNeZero R⁻¹ (inv_ne_zero hR.ne'))
  have hS_emb : MeasurableEmbedding S := by
    convert h.toMeasurableEquiv.measurableEmbedding using 1
  have hmap :
      Measure.map S (volume.restrict (Metric.ball x₀ R)) =
        ENNReal.ofReal (|R⁻¹ ^ Module.finrank ℝ E|⁻¹) •
          (volume.restrict (Metric.ball (0 : E) 1)) :=
    inverse_affine_map_restrict_ball (d := d) (x₀ := x₀) hR
  have hu_map :
      MemLp u p (Measure.map S (volume.restrict (Metric.ball x₀ R))) := by
    rw [hmap]
    exact hu.smul_measure ENNReal.ofReal_ne_top
  change MemLp (u ∘ S) p (volume.restrict (Metric.ball x₀ R))
  simpa [Function.comp] using (hS_emb.memLp_map_measure_iff).1 hu_map

omit [NeZero d] in
private lemma affine_cov_helper
    {x₀ : E} {R : ℝ} (hR : 0 < R) (f : E → ℝ) :
    ∫ z in Metric.ball (0 : E) 1, f (x₀ + R • z) =
      (R ^ Module.finrank ℝ E)⁻¹ * ∫ x in Metric.ball x₀ R, f x := by
  open scoped Pointwise in
  have hscale := Measure.setIntegral_comp_smul_of_pos volume (fun x => f (x₀ + x))
    (Metric.ball (0 : E) 1) hR
  open scoped Pointwise in
  rw [show R • Metric.ball (0 : E) 1 = Metric.ball (0 : E) R from by
    rw [smul_unitBall hR.ne']
    simp [Real.norm_of_nonneg hR.le]] at hscale
  rw [hscale]
  congr 1
  rw [show Metric.ball x₀ R = (x₀ + ·) '' Metric.ball (0 : E) R from by simp]
  exact ((measurePreserving_add_left volume x₀).setIntegral_image_emb
    (MeasurableEquiv.addLeft x₀).measurableEmbedding f (Metric.ball (0 : E) R)).symm

omit [NeZero d] in
private lemma fderiv_transportFromUnitBall_apply
    {x₀ : E} {R : ℝ} (_hR : 0 < R)
    {u : E → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u) (i : Fin d) :
    ∀ x : E,
      (fderiv ℝ (transportFromUnitBall (d := d) (x₀ := x₀) (R := R) u) x)
          (EuclideanSpace.single i 1) =
        R⁻¹ * (fderiv ℝ u (R⁻¹ • (x - x₀))) (EuclideanSpace.single i 1) := by
  intro x
  let S : E → E := fun y => R⁻¹ • (y - x₀)
  have hS_fd : HasFDerivAt S (R⁻¹ • ContinuousLinearMap.id ℝ E) x := by
    have h := (hasFDerivAt_id (𝕜 := ℝ) x).sub
      (hasFDerivAt_const (𝕜 := ℝ) x₀ x)
    simp only [sub_zero] at h
    simpa [S] using h.const_smul R⁻¹
  have hu_at : HasFDerivAt u (fderiv ℝ u (S x)) (S x) :=
    ((hu.differentiable (by simp)).differentiableAt (x := S x)).hasFDerivAt
  have hcomp := hu_at.comp x hS_fd
  rw [show transportFromUnitBall (d := d) (x₀ := x₀) (R := R) u = u ∘ S from rfl, hcomp.fderiv]
  simp [S, ContinuousLinearMap.smul_apply, smul_eq_mul]

omit [NeZero d] in
private lemma weakPartialDeriv_transportFromUnitBall
    {i : Fin d} {x₀ : E} {R : ℝ} {u g : E → ℝ}
    (hR : 0 < R)
    (hg_weak : HasWeakPartialDeriv i g u (Metric.ball (0 : E) 1)) :
    HasWeakPartialDeriv i
      (fun x => R⁻¹ * g (R⁻¹ • (x - x₀)))
      (transportFromUnitBall (d := d) (x₀ := x₀) (R := R) u)
      (Metric.ball x₀ R) := by
  intro φ hφ_smooth hφ_supp hφ_sub
  set ψ : E → ℝ := fun z => φ (x₀ + R • z)
  have hψ_smooth : ContDiff ℝ (⊤ : ℕ∞) ψ := by
    simpa [ψ] using
      hφ_smooth.comp (contDiff_const.add (contDiff_const_smul R))
  have hψ_supp : HasCompactSupport ψ := by
    set h : E ≃ₜ E := (Homeomorph.smulOfNeZero R hR.ne').trans (Homeomorph.addLeft x₀)
    exact (show ψ = φ ∘ h from by
      ext z
      simp [ψ, h, Homeomorph.smulOfNeZero, Homeomorph.addLeft]) ▸
      hφ_supp.comp_homeomorph h
  have hψ_tsub : tsupport ψ ⊆ Metric.ball (0 : E) 1 := by
    intro z hz
    have hcont : Continuous (fun z : E => x₀ + R • z) :=
      (continuous_const_add x₀).comp (continuous_const_smul R)
    have hz' := hφ_sub ((tsupport_comp_subset_preimage _ hcont) hz)
    rw [Metric.mem_ball, dist_eq_norm] at hz' ⊢
    have hsub : x₀ + R • z - x₀ = R • z := by
      abel
    rw [hsub, norm_smul, Real.norm_of_nonneg hR.le] at hz'
    have hiff : R * ‖z‖ < R ↔ ‖z‖ < 1 := by
      constructor <;> intro hh <;> nlinarith
    simpa [sub_zero] using hiff.mp hz'
  have key := hg_weak ψ hψ_smooth hψ_supp hψ_tsub
  set ei : E := EuclideanSpace.single i (1 : ℝ)
  have hfderiv_rel :
      ∀ z : E, (fderiv ℝ ψ z) ei = R * (fderiv ℝ φ (x₀ + R • z)) ei := by
    intro z
    have hS_fd : HasFDerivAt (fun y : E => x₀ + R • y) (R • ContinuousLinearMap.id ℝ E) z := by
      simpa using ((hasFDerivAt_id (𝕜 := ℝ) z).const_smul R).const_add x₀
    have hφ_at : HasFDerivAt φ (fderiv ℝ φ (x₀ + R • z)) (x₀ + R • z) :=
      ((hφ_smooth.differentiable (by simp)).differentiableAt (x := x₀ + R • z)).hasFDerivAt
    have hcomp := hφ_at.comp z hS_fd
    rw [show ψ = φ ∘ (fun y : E => x₀ + R • y) from rfl, hcomp.fderiv]
    simp [ei, ContinuousLinearMap.smul_apply, smul_eq_mul]
  set Aint : ℝ := ∫ x in Metric.ball x₀ R,
      transportFromUnitBall (d := d) (x₀ := x₀) (R := R) u x * (fderiv ℝ φ x) ei
  set Bint : ℝ := ∫ x in Metric.ball x₀ R,
      g (R⁻¹ • (x - x₀)) * φ x
  have lhs_eq :
      ∫ z in Metric.ball (0 : E) 1, u z * (fderiv ℝ ψ z) ei =
        R * ((R ^ Module.finrank ℝ E)⁻¹ * Aint) := by
    simp_rw [hfderiv_rel]
    have hmul :
        (fun z : E => u z * (R * (fderiv ℝ φ (x₀ + R • z)) ei)) =
          (fun z : E => R * (u z * (fderiv ℝ φ (x₀ + R • z)) ei)) := by
      ext z
      ring
    rw [hmul, integral_const_mul]
    congr 1
    simpa [Aint, transportFromUnitBall, mul_assoc, smul_smul, inv_mul_cancel₀ hR.ne',
      sub_eq_add_neg] using
      affine_cov_helper (d := d) (x₀ := x₀) (R := R) hR
        (fun x => transportFromUnitBall (d := d) (x₀ := x₀) (R := R) u x * (fderiv ℝ φ x) ei)
  have rhs_eq :
      -∫ z in Metric.ball (0 : E) 1, g z * ψ z =
        -((R ^ Module.finrank ℝ E)⁻¹ * Bint) := by
    congr 1
    simpa [ψ, Bint, smul_smul, inv_mul_cancel₀ hR.ne', sub_eq_add_neg] using
      affine_cov_helper (d := d) (x₀ := x₀) (R := R) hR
        (fun x => g (R⁻¹ • (x - x₀)) * φ x)
  rw [lhs_eq, rhs_eq] at key
  have hpow_ne : (R ^ Module.finrank ℝ E) ≠ 0 := by
    exact pow_ne_zero _ hR.ne'
  have hpowinv_ne : ((R ^ Module.finrank ℝ E)⁻¹ : ℝ) ≠ 0 := by
    exact inv_ne_zero hpow_ne
  have key' : (R ^ Module.finrank ℝ E)⁻¹ * (R * Aint) =
      (R ^ Module.finrank ℝ E)⁻¹ * (-Bint) := by
    calc
      (R ^ Module.finrank ℝ E)⁻¹ * (R * Aint)
          = R * ((R ^ Module.finrank ℝ E)⁻¹ * Aint) := by ring
      _ = -((R ^ Module.finrank ℝ E)⁻¹ * Bint) := key
      _ = (R ^ Module.finrank ℝ E)⁻¹ * (-Bint) := by ring
  have key'' : R * Aint = -Bint := by
    exact mul_left_cancel₀ hpowinv_ne key'
  have hmain : Aint = -(R⁻¹ * Bint) := by
    calc
      Aint = R⁻¹ * (R * Aint) := by
              field_simp [hR.ne']
      _ = R⁻¹ * (-Bint) := by rw [key'']
      _ = -(R⁻¹ * Bint) := by ring
  have hconst :
      ∫ x in Metric.ball x₀ R, R⁻¹ * g (R⁻¹ • (x - x₀)) * φ x =
        R⁻¹ * Bint := by
    simp [Bint, integral_const_mul, mul_assoc]
  calc
    ∫ x in Metric.ball x₀ R,
        transportFromUnitBall (d := d) (x₀ := x₀) (R := R) u x * (fderiv ℝ φ x) ei = Aint := by
          rfl
    _ = -(R⁻¹ * Bint) := hmain
    _ = -∫ x in Metric.ball x₀ R, R⁻¹ * g (R⁻¹ • (x - x₀)) * φ x := by
          rw [hconst]

/-- Rescaling a unit-ball witness to a witness on `B(x₀, R)`. -/
noncomputable def MemW1pWitness.transportFromUnitBall
    {p : ENNReal} {x₀ : E} {R : ℝ} {u : E → ℝ}
    (hR : 0 < R)
    (hw : MemW1pWitness p u (Metric.ball (0 : E) 1)) :
    MemW1pWitness p (transportFromUnitBall (d := d) (x₀ := x₀) (R := R) u)
      (Metric.ball x₀ R) where
  memLp := transportFromUnitBall_memLp (d := d) (x₀ := x₀) (R := R) hR hw.memLp
  weakGrad := fun x => R⁻¹ • hw.weakGrad (R⁻¹ • (x - x₀))
  weakGrad_component_memLp := by
    intro i
    simpa [DeGiorgi.transportFromUnitBall, Pi.smul_apply, smul_eq_mul, sub_eq_add_neg] using
      (transportFromUnitBall_memLp (d := d) (x₀ := x₀) (R := R) hR
        (hw.weakGrad_component_memLp i)).const_mul R⁻¹
  isWeakGrad := by
    intro i
    simpa [DeGiorgi.transportFromUnitBall, Pi.smul_apply, smul_eq_mul, sub_eq_add_neg] using
      weakPartialDeriv_transportFromUnitBall (d := d) (i := i)
        (x₀ := x₀) (R := R) (u := u) (g := fun x => hw.weakGrad x i) hR (hw.isWeakGrad i)

omit [NeZero d] in
private theorem eLpNorm_transportFromUnitBall
    {p : ENNReal} {x₀ : E} {R : ℝ} {f : E → ℝ}
    (hR : 0 < R) (_hp : p ≠ 0) (hp' : p ≠ ⊤) :
    eLpNorm (DeGiorgi.transportFromUnitBall (d := d) (x₀ := x₀) (R := R) f) p
      (volume.restrict (Metric.ball x₀ R)) =
      ENNReal.ofReal (R ^ (d / p.toReal)) *
        eLpNorm f p (volume.restrict (Metric.ball (0 : E) 1)) := by
  let S : E → E := fun x => R⁻¹ • (x - x₀)
  let h : E ≃ₜ E := (Homeomorph.addRight (-x₀)).trans
    (Homeomorph.smulOfNeZero R⁻¹ (inv_ne_zero hR.ne'))
  have hS_emb : MeasurableEmbedding S := by
    convert h.toMeasurableEquiv.measurableEmbedding using 1
  rw [show DeGiorgi.transportFromUnitBall (d := d) (x₀ := x₀) (R := R) f = f ∘ S from rfl,
    ← hS_emb.eLpNorm_map_measure]
  rw [inverse_affine_map_restrict_ball (d := d) (x₀ := x₀) hR,
    eLpNorm_smul_measure_of_ne_top hp']
  simp only [smul_eq_mul]
  congr 1
  have hfin : Module.finrank ℝ E = d := by
    simp
  rw [hfin]
  have hRd_pos : (0 : ℝ) < R ^ d := pow_pos hR d
  have hRinv_pow_abs :
      |R⁻¹ ^ d|⁻¹ = R ^ d := by
    rw [abs_of_nonneg (pow_nonneg (inv_nonneg.mpr hR.le) d)]
    rw [show R⁻¹ ^ d = (R ^ d)⁻¹ from (inv_pow R d)]
    simp
  rw [hRinv_pow_abs]
  rw [ENNReal.ofReal_rpow_of_nonneg (pow_nonneg hR.le d) ENNReal.toReal_nonneg]
  congr 1
  rw [← Real.rpow_natCast R d, ← Real.rpow_mul hR.le]
  congr 1
  rw [ENNReal.toReal_div, ENNReal.toReal_one]
  ring

/-- Transport zero-trace Sobolev test functions from the unit ball to
`B(x₀, R)`. -/
private theorem MemW01p.transportFromUnitBall
    {x₀ : E} {R : ℝ} {u : E → ℝ}
    (hR : 0 < R)
    (hu : MemW01p 2 u (Metric.ball (0 : E) 1)) :
    MemW01p 2 (DeGiorgi.transportFromUnitBall (d := d) (x₀ := x₀) (R := R) u)
      (Metric.ball x₀ R) := by
  let _ := (inferInstance : NeZero d)
  rcases hu with ⟨_, hw, φ, hφ_smooth, hφ_compact, hφ_sub, hφ_fun, hφ_grad⟩
  let ψ : ℕ → E → ℝ := fun n =>
    DeGiorgi.transportFromUnitBall (d := d) (x₀ := x₀) (R := R) (φ n)
  refine ⟨(hw.transportFromUnitBall (d := d) (x₀ := x₀) (R := R) hR).memW1p,
    hw.transportFromUnitBall (d := d) (x₀ := x₀) (R := R) hR, ψ, ?_, ?_, ?_, ?_, ?_⟩
  · intro n
    simpa [ψ] using
      (hφ_smooth n).comp ((contDiff_const_smul R⁻¹).comp (contDiff_id.sub contDiff_const))
  · intro n
    let h : E ≃ₜ E := (Homeomorph.addRight (-x₀)).trans
      (Homeomorph.smulOfNeZero R⁻¹ (inv_ne_zero hR.ne'))
    exact (show ψ n = φ n ∘ h from by
      ext x
      have hx : h x = R⁻¹ • (x - x₀) := by
        ext i
        simp [h, Homeomorph.addRight, Homeomorph.smulOfNeZero, sub_eq_add_neg, smul_add]
      simpa [ψ, DeGiorgi.transportFromUnitBall] using congrArg (φ n) hx.symm) ▸
      (hφ_compact n).comp_homeomorph h
  · intro n x hx
    have hcont : Continuous (fun x : E => R⁻¹ • (x - x₀)) :=
      (continuous_const_smul R⁻¹).comp (continuous_id.sub continuous_const)
    have hx' := hφ_sub n ((tsupport_comp_subset_preimage _ hcont) hx)
    have : x ∈ (fun x : E => R⁻¹ • (x - x₀)) ⁻¹' Metric.ball (0 : E) 1 := hx'
    simpa [inverse_affine_preimage_unitBall (d := d) (x₀ := x₀) hR] using this
  ·
    let C : ENNReal := ENNReal.ofReal (R ^ (d / (2 : ENNReal).toReal))
    have hEq :
        (fun n =>
          eLpNorm (fun x => ψ n x -
              DeGiorgi.transportFromUnitBall (d := d) (x₀ := x₀) (R := R) u x) 2
            (volume.restrict (Metric.ball x₀ R))) =
          (fun n =>
            C * eLpNorm (fun x => φ n x - u x) 2
              (volume.restrict (Metric.ball (0 : E) 1))) := by
      funext n
      have hfun :
          (fun x => ψ n x -
              DeGiorgi.transportFromUnitBall (d := d) (x₀ := x₀) (R := R) u x) =
            DeGiorgi.transportFromUnitBall (d := d) (x₀ := x₀) (R := R)
              (fun x => φ n x - u x) := by
        ext x
        simp [ψ, DeGiorgi.transportFromUnitBall]
      rw [hfun, eLpNorm_transportFromUnitBall (d := d) (x₀ := x₀) (R := R)
        (f := fun x => φ n x - u x) hR (by norm_num) (by norm_num)]
    rw [hEq]
    have hscaled :
        Filter.Tendsto
          (fun n =>
            C * eLpNorm (fun x => φ n x - u x) 2
              (volume.restrict (Metric.ball (0 : E) 1)))
          Filter.atTop (nhds (C * 0)) :=
      ENNReal.Tendsto.const_mul hφ_fun (Or.inr ENNReal.coe_ne_top)
    simpa using hscaled
  · intro i
    let C : ENNReal := ENNReal.ofReal (R ^ (d / (2 : ENNReal).toReal))
    let C' : ENNReal := ‖R⁻¹‖ₑ
    have hEq :
        (fun n =>
          eLpNorm
            (fun x =>
              (fderiv ℝ (ψ n) x) (EuclideanSpace.single i 1) -
                (hw.transportFromUnitBall (d := d) (x₀ := x₀) (R := R) hR).weakGrad x i)
            2 (volume.restrict (Metric.ball x₀ R))) =
          (fun n =>
            C' * (C * eLpNorm
              (fun x =>
                (fderiv ℝ (φ n) x) (EuclideanSpace.single i 1) - hw.weakGrad x i)
              2 (volume.restrict (Metric.ball (0 : E) 1)))) := by
      funext n
      have hfun :
          (fun x =>
            (fderiv ℝ (ψ n) x) (EuclideanSpace.single i 1) -
              (hw.transportFromUnitBall (d := d) (x₀ := x₀) (R := R) hR).weakGrad x i) =
            R⁻¹ •
              DeGiorgi.transportFromUnitBall (d := d) (x₀ := x₀) (R := R)
                (fun x =>
                  (fderiv ℝ (φ n) x) (EuclideanSpace.single i 1) - hw.weakGrad x i) := by
        ext x
        rw [fderiv_transportFromUnitBall_apply (d := d) (x₀ := x₀) (R := R)
          (u := φ n) hR (hφ_smooth n) i x]
        simp [MemW1pWitness.transportFromUnitBall, DeGiorgi.transportFromUnitBall,
          Pi.smul_apply, smul_eq_mul]
        ring
      rw [hfun, eLpNorm_const_smul]
      rw [eLpNorm_transportFromUnitBall (d := d) (x₀ := x₀) (R := R)
        (f := fun x =>
          (fderiv ℝ (φ n) x) (EuclideanSpace.single i 1) - hw.weakGrad x i)
        hR (by norm_num) (by norm_num)]
    rw [hEq]
    have hscaled :
        Filter.Tendsto
          (fun n =>
            C' * (C * eLpNorm
              (fun x =>
                (fderiv ℝ (φ n) x) (EuclideanSpace.single i 1) - hw.weakGrad x i)
              2 (volume.restrict (Metric.ball (0 : E) 1))))
          Filter.atTop (nhds (C' * (C * 0))) :=
      ENNReal.Tendsto.const_mul
        (ENNReal.Tendsto.const_mul (hφ_grad i) (Or.inr ENNReal.coe_ne_top))
        (Or.inr ENNReal.coe_ne_top)
    simpa [mul_assoc] using hscaled

private lemma bilinForm_rescaleToUnitBall
    {x₀ : E} {R : ℝ} (hR : 0 < R)
    (A : EllipticCoeff d (Metric.ball x₀ R))
    {u φ : E → ℝ}
    (hu : MemW1pWitness 2 u (Metric.ball x₀ R))
    (hφ : MemW1pWitness 2 φ (Metric.ball (0 : E) 1)) :
    bilinFormOfCoeff (rescaleCoeffToUnitBall (d := d) (x₀ := x₀) (R := R) hR A)
      (hu.rescale_to_unitBall (d := d) (x₀ := x₀) (R := R) hR) hφ =
      ((R ^ Module.finrank ℝ E)⁻¹ * R ^ (2 : ℕ)) *
        bilinFormOfCoeff A hu
          (hφ.transportFromUnitBall (d := d) (x₀ := x₀) (R := R) hR) := by
  let huR := hu.rescale_to_unitBall (d := d) (x₀ := x₀) (R := R) hR
  let hφB := hφ.transportFromUnitBall (d := d) (x₀ := x₀) (R := R) hR
  have hpoint :
      ∀ z : E,
        bilinFormIntegrandOfCoeff
            (rescaleCoeffToUnitBall (d := d) (x₀ := x₀) (R := R) hR A) huR hφ z =
          R ^ (2 : ℕ) *
            bilinFormIntegrandOfCoeff A hu hφB (x₀ + R • z) := by
    intro z
    have hmat :
        matMulE (A.a (x₀ + R • z)) (R • hu.weakGrad (x₀ + R • z)) =
          R • matMulE (A.a (x₀ + R • z)) (hu.weakGrad (x₀ + R • z)) := by
      ext i
      simp [matMulE_apply, Matrix.mulVec_smul, Pi.smul_apply]
    have hgrad :
        hφ.weakGrad z = R • hφB.weakGrad (x₀ + R • z) := by
      ext i
      simp [hφB, MemW1pWitness.transportFromUnitBall, smul_eq_mul, sub_eq_add_neg,
        smul_smul, inv_mul_cancel₀ hR.ne']
      rw [mul_inv_cancel₀ hR.ne', one_mul]
    calc
      bilinFormIntegrandOfCoeff
          (rescaleCoeffToUnitBall (d := d) (x₀ := x₀) (R := R) hR A) huR hφ z
          = ⟪matMulE (A.a (x₀ + R • z)) (R • hu.weakGrad (x₀ + R • z)),
              hφ.weakGrad z⟫_ℝ := by
                simp [bilinFormIntegrandOfCoeff, huR, rescaleCoeffToUnitBall,
                  MemW1pWitness.rescale_to_unitBall]
      _ = ⟪R • matMulE (A.a (x₀ + R • z)) (hu.weakGrad (x₀ + R • z)),
            R • hφB.weakGrad (x₀ + R • z)⟫_ℝ := by rw [hmat, hgrad]
      _ = R ^ (2 : ℕ) *
            bilinFormIntegrandOfCoeff A hu hφB (x₀ + R • z) := by
            simp [bilinFormIntegrandOfCoeff, hφB, inner_smul_left, inner_smul_right,
              pow_two, mul_assoc]
  unfold bilinFormOfCoeff
  calc
    ∫ z in Metric.ball (0 : E) 1,
        bilinFormIntegrandOfCoeff
          (rescaleCoeffToUnitBall (d := d) (x₀ := x₀) (R := R) hR A) huR hφ z
        = ∫ z in Metric.ball (0 : E) 1,
            R ^ (2 : ℕ) * bilinFormIntegrandOfCoeff A hu hφB (x₀ + R • z) := by
              apply integral_congr_ae
              filter_upwards with z
              exact hpoint z
    _ = R ^ (2 : ℕ) * ∫ z in Metric.ball (0 : E) 1,
          bilinFormIntegrandOfCoeff A hu hφB (x₀ + R • z) := by
            rw [integral_const_mul]
    _ = R ^ (2 : ℕ) *
          ((R ^ Module.finrank ℝ E)⁻¹ *
            ∫ x in Metric.ball x₀ R, bilinFormIntegrandOfCoeff A hu hφB x) := by
              rw [affine_cov_helper (d := d) (x₀ := x₀) (R := R) hR
                (fun x => bilinFormIntegrandOfCoeff A hu hφB x)]
    _ = ((R ^ Module.finrank ℝ E)⁻¹ * R ^ (2 : ℕ)) *
          ∫ x in Metric.ball x₀ R, bilinFormIntegrandOfCoeff A hu hφB x := by
            ring
    _ = ((R ^ Module.finrank ℝ E)⁻¹ * R ^ (2 : ℕ)) *
          bilinFormOfCoeff A hu hφB := by
            rfl

/-- Transport subsolutions on `B(x₀, R)` to the unit ball via affine pullback. -/
theorem rescaleToUnitBall_isSubsolution
    {x₀ : E} {R : ℝ} (hR : 0 < R)
    (A : EllipticCoeff d (Metric.ball x₀ R))
    {u : E → ℝ}
    (hsub : IsSubsolution A u) :
    IsSubsolution (rescaleCoeffToUnitBall (d := d) hR A)
      (rescaleToUnitBall (d := d) (x₀ := x₀) (R := R) u) := by
  rcases hsub with ⟨hu_mem, hsub_ineq⟩
  let hu : MemW1pWitness 2 u (Metric.ball x₀ R) := DeGiorgi.MemW1p.someWitness hu_mem
  let huR := hu.rescale_to_unitBall (d := d) (x₀ := x₀) (R := R) hR
  refine ⟨huR.memW1p, ?_⟩
  intro hu' φ hφ0 hφ hφ_nonneg
  let hφB := hφ.transportFromUnitBall (d := d) (x₀ := x₀) (R := R) hR
  have hφB0 :
      MemH01 (DeGiorgi.transportFromUnitBall (d := d) (x₀ := x₀) (R := R) φ)
        (Metric.ball x₀ R) :=
    MemW01p.transportFromUnitBall (d := d) (x₀ := x₀) (R := R) hR hφ0
  have hball : bilinFormOfCoeff A hu hφB ≤ 0 := by
    exact hsub_ineq hu _ hφB0 hφB (by
      intro x
      exact hφ_nonneg (R⁻¹ • (x - x₀)))
  have hconst_nonneg : 0 ≤ ((R ^ Module.finrank ℝ E)⁻¹ * R ^ (2 : ℕ) : ℝ) := by
    positivity
  calc
    bilinFormOfCoeff (rescaleCoeffToUnitBall (d := d) (x₀ := x₀) (R := R) hR A) hu' hφ
        = bilinFormOfCoeff (rescaleCoeffToUnitBall (d := d) (x₀ := x₀) (R := R) hR A) huR hφ := by
            exact bilinFormOfCoeff_eq_left Metric.isOpen_ball _ hu' huR hφ
    _ = ((R ^ Module.finrank ℝ E)⁻¹ * R ^ (2 : ℕ)) * bilinFormOfCoeff A hu hφB := by
          simpa [huR, hφB] using bilinForm_rescaleToUnitBall (d := d) (x₀ := x₀) (R := R) hR A hu hφ
    _ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hconst_nonneg hball

/-- Transport supersolutions on `B(x₀, R)` to the unit ball via affine
pullback. -/
theorem rescaleToUnitBall_isSupersolution
    {x₀ : E} {R : ℝ} (hR : 0 < R)
    (A : EllipticCoeff d (Metric.ball x₀ R))
    {u : E → ℝ}
    (hsuper : IsSupersolution A u) :
    IsSupersolution (rescaleCoeffToUnitBall (d := d) hR A)
      (rescaleToUnitBall (d := d) (x₀ := x₀) (R := R) u) := by
  rcases hsuper with ⟨hu_mem, hsuper_ineq⟩
  let hu : MemW1pWitness 2 u (Metric.ball x₀ R) := DeGiorgi.MemW1p.someWitness hu_mem
  let huR := hu.rescale_to_unitBall (d := d) (x₀ := x₀) (R := R) hR
  refine ⟨huR.memW1p, ?_⟩
  intro hu' φ hφ0 hφ hφ_nonneg
  let hφB := hφ.transportFromUnitBall (d := d) (x₀ := x₀) (R := R) hR
  have hφB0 :
      MemH01 (DeGiorgi.transportFromUnitBall (d := d) (x₀ := x₀) (R := R) φ)
        (Metric.ball x₀ R) :=
    MemW01p.transportFromUnitBall (d := d) (x₀ := x₀) (R := R) hR hφ0
  have hball : 0 ≤ bilinFormOfCoeff A hu hφB := by
    exact hsuper_ineq hu _ hφB0 hφB (by
      intro x
      exact hφ_nonneg (R⁻¹ • (x - x₀)))
  have hconst_nonneg : 0 ≤ ((R ^ Module.finrank ℝ E)⁻¹ * R ^ (2 : ℕ) : ℝ) := by
    positivity
  calc
    0 ≤ ((R ^ Module.finrank ℝ E)⁻¹ * R ^ (2 : ℕ)) * bilinFormOfCoeff A hu hφB :=
      mul_nonneg hconst_nonneg hball
    _ = bilinFormOfCoeff (rescaleCoeffToUnitBall (d := d) (x₀ := x₀) (R := R) hR A) huR hφ := by
          symm
          simpa [huR, hφB] using bilinForm_rescaleToUnitBall (d := d) (x₀ := x₀) (R := R) hR A hu hφ
    _ = bilinFormOfCoeff (rescaleCoeffToUnitBall (d := d) (x₀ := x₀) (R := R) hR A) hu' hφ := by
          symm
          exact bilinFormOfCoeff_eq_left Metric.isOpen_ball _ hu' huR hφ

/-- Transport solutions on `B(x₀, R)` to the unit ball via affine pullback. -/
theorem rescaleToUnitBall_isSolution
    {x₀ : E} {R : ℝ} (hR : 0 < R)
    (A : EllipticCoeff d (Metric.ball x₀ R))
    {u : E → ℝ}
    (hsol : IsSolution A u) :
    IsSolution (rescaleCoeffToUnitBall (d := d) hR A)
      (rescaleToUnitBall (d := d) (x₀ := x₀) (R := R) u) := by
  exact ⟨rescaleToUnitBall_isSubsolution (d := d) (x₀ := x₀) (R := R) hR A hsol.1,
    rescaleToUnitBall_isSupersolution (d := d) (x₀ := x₀) (R := R) hR A hsol.2⟩

/-- Transport homogeneous weak solutions on `B(x₀, R)` to the unit ball via
affine pullback. -/
theorem rescaleToUnitBall_isHomogeneousWeakSolution
    {x₀ : E} {R : ℝ} (hR : 0 < R)
    (A : EllipticCoeff d (Metric.ball x₀ R))
    {u : E → ℝ}
    (hweak : IsHomogeneousWeakSolution A u) :
    IsHomogeneousWeakSolution (rescaleCoeffToUnitBall (d := d) hR A)
      (rescaleToUnitBall (d := d) (x₀ := x₀) (R := R) u) := by
  rcases hweak with ⟨hu_mem, hweak_eq⟩
  let hu : MemW1pWitness 2 u (Metric.ball x₀ R) := DeGiorgi.MemW1p.someWitness hu_mem
  let huR := hu.rescale_to_unitBall (d := d) (x₀ := x₀) (R := R) hR
  refine ⟨huR.memW1p, ?_⟩
  intro hu' φ hφ0 hφ
  let hφB := hφ.transportFromUnitBall (d := d) (x₀ := x₀) (R := R) hR
  have hφB0 :
      MemH01 (DeGiorgi.transportFromUnitBall (d := d) (x₀ := x₀) (R := R) φ)
        (Metric.ball x₀ R) :=
    MemW01p.transportFromUnitBall (d := d) (x₀ := x₀) (R := R) hR hφ0
  have hball : bilinFormOfCoeff A hu hφB = 0 :=
    hweak_eq hu _ hφB0 hφB
  calc
    bilinFormOfCoeff (rescaleCoeffToUnitBall (d := d) (x₀ := x₀) (R := R) hR A) hu' hφ
        = bilinFormOfCoeff (rescaleCoeffToUnitBall (d := d) (x₀ := x₀) (R := R) hR A) huR hφ := by
            exact bilinFormOfCoeff_eq_left Metric.isOpen_ball _ hu' huR hφ
    _ = ((R ^ Module.finrank ℝ E)⁻¹ * R ^ (2 : ℕ)) * bilinFormOfCoeff A hu hφB := by
          simpa [huR, hφB] using bilinForm_rescaleToUnitBall (d := d) (x₀ := x₀) (R := R) hR A hu hφ
    _ = 0 := by rw [hball]; ring

end DeGiorgi
