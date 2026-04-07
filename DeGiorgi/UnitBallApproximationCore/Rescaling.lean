import DeGiorgi.UnitBallApproximationCore.Profiles

/-!
# Chapter 02: Unit-Ball Rescaling Layer

This module packages the rescaling of Sobolev witnesses to the unit ball.
-/

noncomputable section

open MeasureTheory Metric Filter Topology Set Function Matrix
open scoped ENNReal NNReal

namespace DeGiorgi

variable {d : ℕ} [NeZero d]

local notation "E" => EuclideanSpace ℝ (Fin d)

/-- The dilation used in the star-shaped approximation argument. -/
def unitBallDilate (lam : ℝ) (u : E → ℝ) : E → ℝ :=
  fun x => u (lam⁻¹ • x)


omit [NeZero d] in
lemma unitBallDilate_apply (lam : ℝ) (u : E → ℝ) (x : E) :
    unitBallDilate (d := d) lam u x = u (lam⁻¹ • x) := rfl

omit [NeZero d] in
lemma smul_inv_mem_unitBall {lam : ℝ} (hlam : 1 < lam) {x : E}
    (hx : x ∈ Metric.ball (0 : E) 1) :
    lam⁻¹ • x ∈ Metric.ball (0 : E) 1 := by
  rw [Metric.mem_ball, dist_zero_right] at hx ⊢
  have hlam_pos : 0 < lam := lt_trans zero_lt_one hlam
  rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hlam_pos.le)]
  have hinv_lt_one : lam⁻¹ < 1 := by
    exact inv_lt_one_of_one_lt₀ hlam
  have hmul : lam⁻¹ * ‖x‖ ≤ ‖x‖ := by
    exact mul_le_of_le_one_left (norm_nonneg x) hinv_lt_one.le
  exact lt_of_le_of_lt hmul hx

omit [NeZero d] in
private lemma rescale_memLp_helper {p : ℝ≥0∞} {x₀ : E} {R : ℝ} {f : E → ℝ}
    (hR : 0 < R) (hf : MemLp f p (volume.restrict (Metric.ball x₀ R))) :
    MemLp (fun z => f (x₀ + R • z)) p (volume.restrict (Metric.ball (0 : E) 1)) := by
  set T := fun z : E => x₀ + R • z
  have hT_emb : MeasurableEmbedding T :=
    ((MeasurableEquiv.addLeft x₀).measurableEmbedding).comp
      ((Homeomorph.smul (isUnit_iff_ne_zero.2 hR.ne').unit).toMeasurableEquiv.measurableEmbedding)
  have hpre : T ⁻¹' (Metric.ball x₀ R) = Metric.ball (0 : E) 1 := by
    ext z
    simp only [T, mem_preimage, Metric.mem_ball, dist_comm, dist_eq_norm]
    constructor
    · intro h
      have : x₀ - (x₀ + R • z) = -(R • z) := by abel
      rw [this, norm_neg, norm_smul, Real.norm_of_nonneg hR.le] at h
      simp only [sub_zero]
      rwa [show R * ‖z‖ < R ↔ ‖z‖ < 1 from by constructor <;> intro hh <;> nlinarith] at h
    · intro h
      simp only [sub_zero] at h
      have : x₀ - (x₀ + R • z) = -(R • z) := by abel
      rw [this, norm_neg, norm_smul, Real.norm_of_nonneg hR.le]
      nlinarith
  rw [show (fun z => f (x₀ + R • z)) = f ∘ T from rfl, ← hpre,
    ← hT_emb.memLp_map_measure_iff, ← hT_emb.restrict_map,
    show Measure.map T volume =
        ENNReal.ofReal (|R ^ Module.finrank ℝ E|⁻¹) • (volume : Measure E) from by
          rw [show T = (fun z => x₀ + z) ∘ (fun z => R • z) from rfl,
            ← Measure.map_map (measurable_const_add x₀) (measurable_const_smul R),
            Measure.map_addHaar_smul volume hR.ne', Measure.map_smul,
            (measurePreserving_add_left volume x₀).map_eq, abs_inv],
    Measure.restrict_smul]
  exact hf.smul_measure ENNReal.ofReal_ne_top

omit [NeZero d] in
private lemma rescale_cov_helper {x₀ : E} {R : ℝ} (hR : 0 < R) (f : E → ℝ) :
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
private lemma weakPartialDeriv_rescale_to_unitBall
    {i : Fin d} {x₀ : E} {R : ℝ} {u g : E → ℝ}
    (hR : 0 < R)
    (hg_weak : HasWeakPartialDeriv i g u (Metric.ball x₀ R)) :
    HasWeakPartialDeriv i (fun z => R * g (x₀ + R • z)) (fun z => u (x₀ + R • z))
      (Metric.ball (0 : E) 1) := by
  intro φ hφ_smooth hφ_supp hφ_sub
  set ψ : E → ℝ := fun x => φ (R⁻¹ • (x - x₀))
  have hψ_smooth : ContDiff ℝ (⊤ : ℕ∞) ψ :=
    hφ_smooth.comp ((contDiff_const_smul R⁻¹).comp (contDiff_id.sub contDiff_const))
  have hψ_supp : HasCompactSupport ψ := by
    set h : E ≃ₜ E := (Homeomorph.addRight (-x₀)).trans
      (Homeomorph.smulOfNeZero R⁻¹ (inv_ne_zero hR.ne'))
    exact (show ψ = φ ∘ h from by
      ext x
      simp [ψ, h, Homeomorph.addRight, Homeomorph.smulOfNeZero, sub_eq_add_neg]) ▸
      hφ_supp.comp_homeomorph h
  have hψ_tsub : tsupport ψ ⊆ Metric.ball x₀ R := by
    intro x hx
    have hcont : Continuous (fun x : E => R⁻¹ • (x - x₀)) :=
      (continuous_const_smul R⁻¹).comp (continuous_id.sub continuous_const)
    have h2 := hφ_sub ((tsupport_comp_subset_preimage _ hcont) hx)
    rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hR.le)] at h2
    rw [Metric.mem_ball, dist_eq_norm]
    rwa [inv_mul_lt_iff₀ hR, mul_one] at h2
  have key := hg_weak ψ hψ_smooth hψ_supp hψ_tsub
  have hψ_at_T : ∀ z : E, ψ (x₀ + R • z) = φ z := fun z => by
    show φ (R⁻¹ • ((x₀ + R • z) - x₀)) = φ z
    simp [smul_smul, inv_mul_cancel₀ hR.ne']
  have hfderiv_rel : ∀ z : E, (fderiv ℝ φ z) (EuclideanSpace.single i 1) =
      R * (fderiv ℝ ψ (x₀ + R • z)) (EuclideanSpace.single i 1) := by
    intro z
    set S := fun x : E => R⁻¹ • (x - x₀)
    have harg : S (x₀ + R • z) = z := by
      simp [S, smul_smul, inv_mul_cancel₀ hR.ne']
    have hS_fd : HasFDerivAt S (R⁻¹ • ContinuousLinearMap.id ℝ E) (x₀ + R • z) := by
      have h3 := (hasFDerivAt_id (𝕜 := ℝ) (x₀ + R • z)).sub
        (hasFDerivAt_const (𝕜 := ℝ) x₀ (x₀ + R • z))
      simp only [sub_zero] at h3
      exact h3.const_smul R⁻¹
    have hφ_at : HasFDerivAt φ (fderiv ℝ φ z) z :=
      ((hφ_smooth.differentiable (by simp)).differentiableAt (x := z)).hasFDerivAt
    rw [← harg] at hφ_at
    have h_comp := hφ_at.comp (x₀ + R • z) hS_fd
    rw [harg] at h_comp
    rw [show ψ = φ ∘ S from rfl, h_comp.fderiv]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.id_apply, map_smul, smul_eq_mul]
    rw [← mul_assoc, mul_inv_cancel₀ hR.ne', one_mul]
  set c := (R ^ Module.finrank ℝ E)⁻¹
  have lhs_eq :
      ∫ z in Metric.ball (0 : E) 1, u (x₀ + R • z) * (fderiv ℝ φ z) (EuclideanSpace.single i 1) =
        R * (c * ∫ x in Metric.ball x₀ R, u x * (fderiv ℝ ψ x) (EuclideanSpace.single i 1)) := by
    simp_rw [hfderiv_rel, show ∀ z : E,
      u (x₀ + R • z) * (R * (fderiv ℝ ψ (x₀ + R • z)) (EuclideanSpace.single i 1)) =
        R * (u (x₀ + R • z) * (fderiv ℝ ψ (x₀ + R • z)) (EuclideanSpace.single i 1))
      from fun z => by ring]
    rw [integral_const_mul]
    congr 1
    exact rescale_cov_helper hR
      (fun x => u x * (fderiv ℝ ψ x) (EuclideanSpace.single i 1))
  have rhs_eq :
      -∫ z in Metric.ball (0 : E) 1, R * g (x₀ + R • z) * φ z =
        -(R * (c * ∫ x in Metric.ball x₀ R, g x * ψ x)) := by
    simp_rw [show ∀ z, R * g (x₀ + R • z) * φ z =
      R * (g (x₀ + R • z) * ψ (x₀ + R • z)) from
      fun z => by rw [hψ_at_T]; ring]
    rw [integral_const_mul]
    congr 1
    congr 1
    exact rescale_cov_helper hR (fun x => g x * ψ x)
  rw [lhs_eq, rhs_eq, key]
  ring

/-- Rescaling a witness on `B_R(x₀)` to a witness on the unit ball. -/
noncomputable def MemW1pWitness.rescale_to_unitBall
    {p : ℝ≥0∞} {x₀ : E} {R : ℝ} {u : E → ℝ}
    (hR : 0 < R)
    (hw : MemW1pWitness p u (Metric.ball x₀ R)) :
    MemW1pWitness p (fun z => u (x₀ + R • z)) (Metric.ball (0 : E) 1) where
  memLp := by
    exact rescale_memLp_helper hR hw.memLp
  weakGrad := fun z => R • hw.weakGrad (x₀ + R • z)
  weakGrad_component_memLp := by
    intro i
    simpa [Pi.smul_apply, smul_eq_mul] using
      (rescale_memLp_helper (x₀ := x₀) (R := R) hR (hw.weakGrad_component_memLp i)).const_mul R
  isWeakGrad := by
    intro i
    simpa [Pi.smul_apply, smul_eq_mul] using
      weakPartialDeriv_rescale_to_unitBall (x₀ := x₀) (R := R) (u := u)
        (g := fun x => hw.weakGrad x i) hR (hw.isWeakGrad i)

omit [NeZero d] in
theorem eLpNorm_rescale_to_unitBall
    {p : ℝ≥0∞} {x₀ : E} {R : ℝ} {f : E → ℝ}
    (hR : 0 < R) (_hp : p ≠ 0) (hp' : p ≠ ⊤) :
    eLpNorm (fun z => f (x₀ + R • z)) p (volume.restrict (Metric.ball (0 : E) 1)) =
      ENNReal.ofReal (R⁻¹ ^ (d / p.toReal)) *
        eLpNorm f p (volume.restrict (Metric.ball x₀ R)) := by
  set T := fun z : E => x₀ + R • z with hT_def
  have hR' : R ≠ 0 := hR.ne'
  have hT_emb : MeasurableEmbedding T :=
    ((MeasurableEquiv.addLeft x₀).measurableEmbedding).comp
      ((Homeomorph.smul (isUnit_iff_ne_zero.2 hR').unit).toMeasurableEquiv.measurableEmbedding)
  rw [show (fun z => f (x₀ + R • z)) = f ∘ T from rfl, ← hT_emb.eLpNorm_map_measure]
  have hpreimage : T ⁻¹' (Metric.ball x₀ R) = Metric.ball (0 : E) 1 := by
    ext z
    simp only [T, mem_preimage, Metric.mem_ball, dist_comm, dist_eq_norm]
    constructor
    · intro h
      have : x₀ - (x₀ + R • z) = -(R • z) := by abel
      rw [this, norm_neg, norm_smul, Real.norm_of_nonneg hR.le] at h
      simp only [sub_zero]
      rwa [show R * ‖z‖ < R ↔ ‖z‖ < 1 from by constructor <;> intro hh <;> nlinarith] at h
    · intro h
      simp only [sub_zero] at h
      have : x₀ - (x₀ + R • z) = -(R • z) := by abel
      rw [this, norm_neg, norm_smul, Real.norm_of_nonneg hR.le]
      nlinarith
  conv_lhs => rw [show Metric.ball (0 : E) 1 = T ⁻¹' Metric.ball x₀ R from hpreimage.symm]
  rw [← Measure.restrict_map hT_emb.measurable measurableSet_ball]
  have hmap : Measure.map T (volume : Measure E) =
      ENNReal.ofReal (|R ^ Module.finrank ℝ E|⁻¹) • volume := by
    rw [show T = (fun z => x₀ + z) ∘ (fun z => R • z) from rfl]
    rw [← Measure.map_map (measurable_const_add x₀) (measurable_const_smul R)]
    rw [Measure.map_addHaar_smul volume hR']
    rw [Measure.map_smul, (measurePreserving_add_left volume x₀).map_eq, abs_inv]
  rw [hmap, Measure.restrict_smul, eLpNorm_smul_measure_of_ne_top hp']
  simp only [smul_eq_mul]
  congr 1
  have hfin : Module.finrank ℝ E = d := by simp
  rw [hfin]
  have hRd_pos : (0 : ℝ) < R ^ d := pow_pos hR d
  rw [abs_of_pos hRd_pos]
  rw [show (R ^ d)⁻¹ = R⁻¹ ^ d from (inv_pow R d).symm]
  have hRinv_nonneg : (0 : ℝ) ≤ R⁻¹ := inv_nonneg.mpr hR.le
  rw [ENNReal.ofReal_rpow_of_nonneg (pow_nonneg hRinv_nonneg d) ENNReal.toReal_nonneg]
  congr 1
  rw [← Real.rpow_natCast (R⁻¹) d, ← Real.rpow_mul hRinv_nonneg]
  congr 1
  rw [ENNReal.toReal_div, ENNReal.toReal_one]
  ring


end DeGiorgi
