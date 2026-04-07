import DeGiorgi.SobolevSpace
import DeGiorgi.Poincare
import DeGiorgi.EllipticCoefficients

/-!
# Weak Formulation: Bilinear Form And Right-Hand Sides

This module develops the coefficient bilinear form and the divergence-form
right-hand-side functionals used throughout the variational theory.
-/

noncomputable section

open MeasureTheory Filter
open scoped InnerProductSpace

namespace DeGiorgi

variable {d : ℕ} [NeZero d]

local notation "E" => AmbientSpace d

/-- Pointwise bilinear-form integrand associated to an elliptic coefficient
field and two Sobolev witnesses. -/
def bilinFormIntegrandOfCoeff {Ω : Set E} {u v : E → ℝ}
    (A : EllipticCoeff d Ω)
    (hu : MemW1pWitness 2 u Ω) (hv : MemW1pWitness 2 v Ω) : E → ℝ :=
  fun x => ⟪matMulE (A.a x) (hu.weakGrad x), hv.weakGrad x⟫_ℝ

/-- The weak bilinear form `a_A(u,v) = ∫_Ω ⟪A∇u, ∇v⟫`. -/
noncomputable def bilinFormOfCoeff {Ω : Set E} {u v : E → ℝ}
    (A : EllipticCoeff d Ω)
    (hu : MemW1pWitness 2 u Ω) (hv : MemW1pWitness 2 v Ω) : ℝ :=
  ∫ x in Ω, bilinFormIntegrandOfCoeff A hu hv x

/-- The bilinear-form integrand is a.e. strongly measurable on `Ω`. -/
theorem aestronglyMeasurable_bilinFormIntegrandOfCoeff
    {Ω : Set E} {u v : E → ℝ}
    (A : EllipticCoeff d Ω)
    (hu : MemW1pWitness 2 u Ω) (hv : MemW1pWitness 2 v Ω) :
    AEStronglyMeasurable (bilinFormIntegrandOfCoeff A hu hv) (volume.restrict Ω) := by
  have hF_aemeas :
      AEMeasurable
        (fun x => ∑ i : Fin d, (∑ j : Fin d, A.a x i j * hu.weakGrad x j) * hv.weakGrad x i)
        (volume.restrict Ω) := by
    have hsum :
        AEMeasurable
          (∑ i : Fin d, fun x => (∑ j : Fin d, A.a x i j * hu.weakGrad x j) * hv.weakGrad x i)
          (volume.restrict Ω) := by
      refine Finset.aemeasurable_sum (s := (Finset.univ : Finset (Fin d)))
        (f := fun i x => (∑ j : Fin d, A.a x i j * hu.weakGrad x j) * hv.weakGrad x i) ?_
      intro i _
      have hrow :
          AEMeasurable (fun x => ∑ j : Fin d, A.a x i j * hu.weakGrad x j)
            (volume.restrict Ω) := by
        have hrow_sum :
            AEMeasurable (∑ j : Fin d, fun x => A.a x i j * hu.weakGrad x j)
              (volume.restrict Ω) := by
          refine Finset.aemeasurable_sum (s := (Finset.univ : Finset (Fin d)))
            (f := fun j x => A.a x i j * hu.weakGrad x j) ?_
          intro j _
          exact (A.measurable_apply i j).aemeasurable.mul
            (hu.weakGrad_component_memLp j).aemeasurable
        convert hrow_sum using 1
        ext x
        simp
      exact hrow.mul (hv.weakGrad_component_memLp i).aemeasurable
    convert hsum using 1
    ext x
    simp
  have hscalar : ∀ a b : ℝ, ⟪a, b⟫_ℝ = a * b := by
    intro a b
    simpa using (RCLike.inner_apply' a b)
  refine hF_aemeas.aestronglyMeasurable.congr ?_
  filter_upwards with x
  simp [bilinFormIntegrandOfCoeff, PiLp.inner_apply, matMulE_apply, Matrix.mulVec,
    dotProduct, hscalar]

/-- The bilinear-form integrand is integrable on `Ω`. -/
theorem integrable_bilinFormIntegrandOfCoeff
    {Ω : Set E} {u v : E → ℝ}
    (A : EllipticCoeff d Ω)
    (hu : MemW1pWitness 2 u Ω) (hv : MemW1pWitness 2 v Ω) :
    Integrable (bilinFormIntegrandOfCoeff A hu hv) (volume.restrict Ω) := by
  let μ : Measure E := volume.restrict Ω
  have hprod_memLp :
      MemLp (fun x => ‖hu.weakGrad x‖ * ‖hv.weakGrad x‖) 1 μ := by
    simpa using (hv.weakGrad_memLp.norm.mul hu.weakGrad_memLp.norm)
  have hdom_int :
      Integrable (fun x => A.Λ * (‖hu.weakGrad x‖ * ‖hv.weakGrad x‖)) μ := by
    rw [← memLp_one_iff_integrable]
    exact hprod_memLp.const_mul A.Λ
  have hbound :
      ∀ᵐ x ∂μ, ‖bilinFormIntegrandOfCoeff A hu hv x‖ ≤
        A.Λ * (‖hu.weakGrad x‖ * ‖hv.weakGrad x‖) := by
    filter_upwards [A.mixed_bound] with x hx
    simpa [bilinFormIntegrandOfCoeff, real_inner_comm, mul_assoc, mul_comm, mul_left_comm] using
      hx (hu.weakGrad x) (hv.weakGrad x)
  exact Integrable.mono' hdom_int
    (aestronglyMeasurable_bilinFormIntegrandOfCoeff A hu hv)
    hbound

/-- The weak bilinear form is continuous with respect to the `L²` gradient
seminorms. -/
theorem bilinForm_bound
    {Ω : Set E} {u v : E → ℝ}
    (A : EllipticCoeff d Ω)
    (hu : MemW1pWitness 2 u Ω) (hv : MemW1pWitness 2 v Ω) :
    |bilinFormOfCoeff A hu hv| ≤
      A.Λ * (∫ x, ‖hu.weakGrad x‖ ^ (2 : ℝ) ∂(volume.restrict Ω)) ^ (1 / (2 : ℝ)) *
        (∫ x, ‖hv.weakGrad x‖ ^ (2 : ℝ) ∂(volume.restrict Ω)) ^ (1 / (2 : ℝ)) := by
  let μ : Measure E := volume.restrict Ω
  have hint_int := integrable_bilinFormIntegrandOfCoeff A hu hv
  have hdom_int :
      Integrable (fun x => A.Λ * (‖hu.weakGrad x‖ * ‖hv.weakGrad x‖)) μ := by
    rw [← memLp_one_iff_integrable]
    have hprod_memLp :
        MemLp (fun x => ‖hu.weakGrad x‖ * ‖hv.weakGrad x‖) 1 μ := by
      simpa using (hv.weakGrad_memLp.norm.mul hu.weakGrad_memLp.norm)
    exact hprod_memLp.const_mul A.Λ
  have hpointwise :
      ∀ᵐ x ∂μ, ‖bilinFormIntegrandOfCoeff A hu hv x‖ ≤
        A.Λ * (‖hu.weakGrad x‖ * ‖hv.weakGrad x‖) := by
    filter_upwards [A.mixed_bound] with x hx
    simpa [bilinFormIntegrandOfCoeff, real_inner_comm, mul_assoc, mul_comm, mul_left_comm] using
      hx (hu.weakGrad x) (hv.weakGrad x)
  have hnorm_le :
      ∫ x, ‖bilinFormIntegrandOfCoeff A hu hv x‖ ∂μ ≤
        ∫ x, A.Λ * (‖hu.weakGrad x‖ * ‖hv.weakGrad x‖) ∂μ := by
    exact integral_mono_ae hint_int.norm hdom_int hpointwise
  have hholder :
      ∫ x, ‖hu.weakGrad x‖ * ‖hv.weakGrad x‖ ∂μ ≤
        (∫ x, ‖hu.weakGrad x‖ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) *
          (∫ x, ‖hv.weakGrad x‖ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) := by
    have hhu_memLp : MemLp hu.weakGrad (ENNReal.ofReal (2 : ℝ)) μ := by
      simpa using hu.weakGrad_memLp
    have hhv_memLp : MemLp hv.weakGrad (ENNReal.ofReal (2 : ℝ)) μ := by
      simpa using hv.weakGrad_memLp
    exact
      integral_mul_norm_le_Lp_mul_Lq (μ := μ) (f := hu.weakGrad) (g := hv.weakGrad)
        Real.HolderConjugate.two_two hhu_memLp hhv_memLp
  simpa [μ, mul_assoc] using
    (calc
      |bilinFormOfCoeff A hu hv| = ‖∫ x, bilinFormIntegrandOfCoeff A hu hv x ∂μ‖ := by
        simp [bilinFormOfCoeff, μ]
      _ ≤ ∫ x, ‖bilinFormIntegrandOfCoeff A hu hv x‖ ∂μ :=
        norm_integral_le_integral_norm _
      _ ≤ ∫ x, A.Λ * (‖hu.weakGrad x‖ * ‖hv.weakGrad x‖) ∂μ := hnorm_le
      _ = A.Λ * ∫ x, ‖hu.weakGrad x‖ * ‖hv.weakGrad x‖ ∂μ := by
        rw [integral_const_mul]
      _ ≤ A.Λ *
          ((∫ x, ‖hu.weakGrad x‖ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) *
            (∫ x, ‖hv.weakGrad x‖ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ))) := by
        exact mul_le_mul_of_nonneg_left hholder A.Λ_nonneg
      _ = A.Λ * (∫ x, ‖hu.weakGrad x‖ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) *
          (∫ x, ‖hv.weakGrad x‖ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) := by
        ring)

/-- The weak bilinear form is coercive with respect to the `L²` gradient
seminorm. -/
theorem bilinForm_coercive
    {Ω : Set E} {u : E → ℝ}
    (A : EllipticCoeff d Ω)
    (hu : MemW1pWitness 2 u Ω) :
    A.lam * ∫ x, ‖hu.weakGrad x‖ ^ (2 : ℕ) ∂(volume.restrict Ω) ≤
      bilinFormOfCoeff A hu hu := by
  let μ : Measure E := volume.restrict Ω
  have hint_int := integrable_bilinFormIntegrandOfCoeff A hu hu
  have hsq_int : Integrable (fun x => ‖hu.weakGrad x‖ ^ (2 : ℕ)) μ := by
    simpa using
      (MeasureTheory.MemLp.integrable_norm_pow (f := hu.weakGrad) (μ := μ)
        hu.weakGrad_memLp (by norm_num : (2 : ℕ) ≠ 0))
  have hleft_int : Integrable (fun x => A.lam * ‖hu.weakGrad x‖ ^ (2 : ℕ)) μ := by
    simpa using hsq_int.const_mul A.lam
  have hcoercive_ae :
      ∀ᵐ x ∂μ, A.lam * ‖hu.weakGrad x‖ ^ (2 : ℕ) ≤
        bilinFormIntegrandOfCoeff A hu hu x := by
    filter_upwards [A.coercive] with x hx
    simpa [bilinFormIntegrandOfCoeff, real_inner_comm] using hx (hu.weakGrad x)
  have hmono :
      ∫ x, A.lam * ‖hu.weakGrad x‖ ^ (2 : ℕ) ∂μ ≤
        ∫ x, bilinFormIntegrandOfCoeff A hu hu x ∂μ := by
    exact integral_mono_ae hleft_int hint_int hcoercive_ae
  simpa [μ] using
    (calc
      A.lam * ∫ x, ‖hu.weakGrad x‖ ^ (2 : ℕ) ∂μ
          = ∫ x, A.lam * ‖hu.weakGrad x‖ ^ (2 : ℕ) ∂μ := by
            rw [integral_const_mul]
      _ ≤ ∫ x, bilinFormIntegrandOfCoeff A hu hu x ∂μ := hmono
      _ = bilinFormOfCoeff A hu hu := by
            simp [bilinFormOfCoeff, μ])

/-- The bilinear form does not depend on the chosen `W^{1,2}` witness in the
left slot. -/
theorem bilinFormOfCoeff_eq_left
    {Ω : Set E} (hΩ : IsOpen Ω)
    (A : EllipticCoeff d Ω)
    {u v : E → ℝ}
    (hu₁ hu₂ : MemW1pWitness 2 u Ω)
    (hv : MemW1pWitness 2 v Ω) :
    bilinFormOfCoeff A hu₁ hv = bilinFormOfCoeff A hu₂ hv := by
  have hgrad_ae : hu₁.weakGrad =ᵐ[volume.restrict Ω] hu₂.weakGrad :=
    MemW1pWitness.ae_eq hΩ hu₁ hu₂
  unfold bilinFormOfCoeff
  apply integral_congr_ae
  filter_upwards [hgrad_ae] with x hx
  simp [bilinFormIntegrandOfCoeff, hx]

/-- The bilinear form does not depend on the chosen `W^{1,2}` witness in the
right slot. -/
theorem bilinFormOfCoeff_eq_right
    {Ω : Set E} (hΩ : IsOpen Ω)
    (A : EllipticCoeff d Ω)
    {u v : E → ℝ}
    (hu : MemW1pWitness 2 u Ω)
    (hv₁ hv₂ : MemW1pWitness 2 v Ω) :
    bilinFormOfCoeff A hu hv₁ = bilinFormOfCoeff A hu hv₂ := by
  have hgrad_ae : hv₁.weakGrad =ᵐ[volume.restrict Ω] hv₂.weakGrad :=
    MemW1pWitness.ae_eq hΩ hv₁ hv₂
  unfold bilinFormOfCoeff
  apply integral_congr_ae
  filter_upwards [hgrad_ae] with x hx
  simp [bilinFormIntegrandOfCoeff, hx]

/-- The bilinear-form integrand is additive in the left slot. -/
theorem bilinFormIntegrandOfCoeff_add_left
    {Ω : Set E} {u₁ u₂ v : E → ℝ}
    (A : EllipticCoeff d Ω)
    (hu₁ : MemW1pWitness 2 u₁ Ω)
    (hu₂ : MemW1pWitness 2 u₂ Ω)
    (hv : MemW1pWitness 2 v Ω) :
    bilinFormIntegrandOfCoeff A (hu₁.add hu₂) hv =
      fun x => bilinFormIntegrandOfCoeff A hu₁ hv x + bilinFormIntegrandOfCoeff A hu₂ hv x := by
  ext x
  have hmat :
      matMulE (A.a x) ((hu₁.add hu₂).weakGrad x) =
        matMulE (A.a x) (hu₁.weakGrad x) + matMulE (A.a x) (hu₂.weakGrad x) := by
    ext i
    simp [MemW1pWitness.add, matMulE_apply, Matrix.mulVec_add, Pi.add_apply]
  simp [bilinFormIntegrandOfCoeff, hmat, inner_add_left]

/-- The bilinear form is additive in the left slot. -/
theorem bilinFormOfCoeff_add_left
    {Ω : Set E} {u₁ u₂ v : E → ℝ}
    (A : EllipticCoeff d Ω)
    (hu₁ : MemW1pWitness 2 u₁ Ω)
    (hu₂ : MemW1pWitness 2 u₂ Ω)
    (hv : MemW1pWitness 2 v Ω) :
    bilinFormOfCoeff A (hu₁.add hu₂) hv =
      bilinFormOfCoeff A hu₁ hv + bilinFormOfCoeff A hu₂ hv := by
  rw [bilinFormOfCoeff, bilinFormOfCoeff, bilinFormOfCoeff,
    bilinFormIntegrandOfCoeff_add_left]
  exact
    integral_add
      (integrable_bilinFormIntegrandOfCoeff A hu₁ hv)
      (integrable_bilinFormIntegrandOfCoeff A hu₂ hv)

/-- The bilinear-form integrand is homogeneous in the left slot. -/
theorem bilinFormIntegrandOfCoeff_smul_left
    {Ω : Set E} {u v : E → ℝ} (c : ℝ)
    (A : EllipticCoeff d Ω)
    (hu : MemW1pWitness 2 u Ω)
    (hv : MemW1pWitness 2 v Ω) :
    bilinFormIntegrandOfCoeff A (hu.smul c) hv =
      fun x => c * bilinFormIntegrandOfCoeff A hu hv x := by
  ext x
  have hmat :
      matMulE (A.a x) ((hu.smul c).weakGrad x) =
        c • matMulE (A.a x) (hu.weakGrad x) := by
    ext i
    simp [MemW1pWitness.smul, matMulE_apply, Matrix.mulVec_smul, Pi.smul_apply,
      smul_eq_mul]
  simp [bilinFormIntegrandOfCoeff, hmat, inner_smul_left]

/-- The bilinear form is homogeneous in the left slot. -/
theorem bilinFormOfCoeff_smul_left
    {Ω : Set E} {u v : E → ℝ} (c : ℝ)
    (A : EllipticCoeff d Ω)
    (hu : MemW1pWitness 2 u Ω)
    (hv : MemW1pWitness 2 v Ω) :
    bilinFormOfCoeff A (hu.smul c) hv = c * bilinFormOfCoeff A hu hv := by
  rw [bilinFormOfCoeff, bilinFormIntegrandOfCoeff_smul_left, integral_const_mul, bilinFormOfCoeff]

/-- The bilinear-form integrand is additive in the right slot. -/
theorem bilinFormIntegrandOfCoeff_add_right
    {Ω : Set E} {u v₁ v₂ : E → ℝ}
    (A : EllipticCoeff d Ω)
    (hu : MemW1pWitness 2 u Ω)
    (hv₁ : MemW1pWitness 2 v₁ Ω)
    (hv₂ : MemW1pWitness 2 v₂ Ω) :
    bilinFormIntegrandOfCoeff A hu (hv₁.add hv₂) =
      fun x => bilinFormIntegrandOfCoeff A hu hv₁ x + bilinFormIntegrandOfCoeff A hu hv₂ x := by
  ext x
  have hgrad :
      (hv₁.add hv₂).weakGrad x = hv₁.weakGrad x + hv₂.weakGrad x := by
    simp [MemW1pWitness.add]
  simp [bilinFormIntegrandOfCoeff, hgrad, inner_add_right]

/-- The bilinear form is additive in the right slot. -/
theorem bilinFormOfCoeff_add_right
    {Ω : Set E} {u v₁ v₂ : E → ℝ}
    (A : EllipticCoeff d Ω)
    (hu : MemW1pWitness 2 u Ω)
    (hv₁ : MemW1pWitness 2 v₁ Ω)
    (hv₂ : MemW1pWitness 2 v₂ Ω) :
    bilinFormOfCoeff A hu (hv₁.add hv₂) =
      bilinFormOfCoeff A hu hv₁ + bilinFormOfCoeff A hu hv₂ := by
  rw [bilinFormOfCoeff, bilinFormOfCoeff, bilinFormOfCoeff,
    bilinFormIntegrandOfCoeff_add_right]
  exact
    integral_add
      (integrable_bilinFormIntegrandOfCoeff A hu hv₁)
      (integrable_bilinFormIntegrandOfCoeff A hu hv₂)

/-- The bilinear-form integrand is homogeneous in the right slot. -/
theorem bilinFormIntegrandOfCoeff_smul_right
    {Ω : Set E} {u v : E → ℝ} (c : ℝ)
    (A : EllipticCoeff d Ω)
    (hu : MemW1pWitness 2 u Ω)
    (hv : MemW1pWitness 2 v Ω) :
    bilinFormIntegrandOfCoeff A hu (hv.smul c) =
      fun x => c * bilinFormIntegrandOfCoeff A hu hv x := by
  ext x
  simp [bilinFormIntegrandOfCoeff, MemW1pWitness.smul, inner_smul_right]

/-- The bilinear form is homogeneous in the right slot. -/
theorem bilinFormOfCoeff_smul_right
    {Ω : Set E} {u v : E → ℝ} (c : ℝ)
    (A : EllipticCoeff d Ω)
    (hu : MemW1pWitness 2 u Ω)
    (hv : MemW1pWitness 2 v Ω) :
    bilinFormOfCoeff A hu (hv.smul c) = c * bilinFormOfCoeff A hu hv := by
  rw [bilinFormOfCoeff, bilinFormIntegrandOfCoeff_smul_right, integral_const_mul, bilinFormOfCoeff]

/-- Pointwise divergence-form RHS integrand `⟪F, ∇v⟫`. -/
def divergenceRHSIntegrandOfField {Ω : Set E} {v : E → ℝ}
    (F : E → E) (hv : MemW1pWitness 2 v Ω) : E → ℝ :=
  fun x => ⟪F x, hv.weakGrad x⟫_ℝ

/-- The divergence-form RHS functional `v ↦ -∫_Ω ⟪F, ∇v⟫`. -/
noncomputable def divergenceRHSOfField {Ω : Set E} {v : E → ℝ}
    (F : E → E) (hv : MemW1pWitness 2 v Ω) : ℝ :=
  -∫ x in Ω, divergenceRHSIntegrandOfField F hv x

omit [NeZero d] in
/-- The divergence-form RHS integrand is a.e. strongly measurable on `Ω`. -/
theorem aestronglyMeasurable_divergenceRHSIntegrandOfField
    {Ω : Set E} {F : E → E} (hF : MemLp F 2 (volume.restrict Ω))
    {v : E → ℝ} (hv : MemW1pWitness 2 v Ω) :
    AEStronglyMeasurable (divergenceRHSIntegrandOfField F hv) (volume.restrict Ω) := by
  have hF_ofLp_cont : Continuous (fun y : E => (WithLp.ofLp y : Fin d → ℝ)) := by
    simpa using (PiLp.continuous_ofLp 2 (fun _ : Fin d => ℝ))
  have hF_ofLp :
      AEStronglyMeasurable (fun x => (WithLp.ofLp (F x) : Fin d → ℝ)) (volume.restrict Ω) :=
    hF_ofLp_cont.comp_aestronglyMeasurable hF.aestronglyMeasurable
  have hsum :
      AEMeasurable
        (∑ i : Fin d, fun x => F x i * hv.weakGrad x i)
        (volume.restrict Ω) := by
    refine Finset.aemeasurable_sum (s := (Finset.univ : Finset (Fin d)))
      (f := fun i x => F x i * hv.weakGrad x i) ?_
    intro i _hi
    have hFi : AEMeasurable (fun x => F x i) (volume.restrict Ω) := by
      simpa using
        (Continuous.comp_aestronglyMeasurable (continuous_apply i) hF_ofLp).aemeasurable
    exact hFi.mul (hv.weakGrad_component_memLp i).aemeasurable
  have hscalar : ∀ a b : ℝ, ⟪a, b⟫_ℝ = a * b := by
    intro a b
    simpa using (RCLike.inner_apply' a b)
  refine hsum.aestronglyMeasurable.congr ?_
  filter_upwards with x
  simp [divergenceRHSIntegrandOfField, PiLp.inner_apply, hscalar]

/-- The divergence-form RHS integrand is integrable on `Ω`. -/
theorem integrable_divergenceRHSIntegrandOfField
    {Ω : Set E} {F : E → E} (hF : MemLp F 2 (volume.restrict Ω))
    {v : E → ℝ} (hv : MemW1pWitness 2 v Ω) :
    Integrable (divergenceRHSIntegrandOfField F hv) (volume.restrict Ω) := by
  let _ := (inferInstance : NeZero d)
  let μ : Measure E := volume.restrict Ω
  have hdom_int :
      Integrable (fun x => ‖F x‖ * ‖hv.weakGrad x‖) μ := by
    simpa [mul_comm] using (hv.weakGrad_memLp.norm.integrable_mul hF.norm)
  have hbound :
      ∀ᵐ x ∂μ, ‖divergenceRHSIntegrandOfField F hv x‖ ≤ ‖F x‖ * ‖hv.weakGrad x‖ := by
    filter_upwards with x
    simpa [divergenceRHSIntegrandOfField] using abs_real_inner_le_norm (F x) (hv.weakGrad x)
  exact Integrable.mono' hdom_int
    (aestronglyMeasurable_divergenceRHSIntegrandOfField hF hv)
    hbound

/-- The divergence-form RHS is bounded with respect to the `L²` gradient
seminorm. -/
theorem divergenceRHSOfField_bound
    {Ω : Set E} {F : E → E} (hF : MemLp F 2 (volume.restrict Ω))
    {v : E → ℝ} (hv : MemW1pWitness 2 v Ω) :
    |divergenceRHSOfField F hv| ≤
      (∫ x, ‖F x‖ ^ (2 : ℝ) ∂(volume.restrict Ω)) ^ (1 / (2 : ℝ)) *
        (∫ x, ‖hv.weakGrad x‖ ^ (2 : ℝ) ∂(volume.restrict Ω)) ^ (1 / (2 : ℝ)) := by
  let μ : Measure E := volume.restrict Ω
  have hint_int := integrable_divergenceRHSIntegrandOfField hF hv
  have hpointwise :
      ∀ᵐ x ∂μ, ‖divergenceRHSIntegrandOfField F hv x‖ ≤ ‖F x‖ * ‖hv.weakGrad x‖ := by
    filter_upwards with x
    simpa [divergenceRHSIntegrandOfField] using abs_real_inner_le_norm (F x) (hv.weakGrad x)
  have hnorm_le :
      ∫ x, ‖divergenceRHSIntegrandOfField F hv x‖ ∂μ ≤
        ∫ x, ‖F x‖ * ‖hv.weakGrad x‖ ∂μ := by
    have hdom_int : Integrable (fun x => ‖F x‖ * ‖hv.weakGrad x‖) μ := by
      simpa [mul_comm] using (hv.weakGrad_memLp.norm.integrable_mul hF.norm)
    exact integral_mono_ae hint_int.norm hdom_int hpointwise
  have hF_memLp : MemLp F (ENNReal.ofReal (2 : ℝ)) μ := by
    simpa using hF
  have hholder :
      ∫ x, ‖F x‖ * ‖hv.weakGrad x‖ ∂μ ≤
        (∫ x, ‖F x‖ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) *
          (∫ x, ‖hv.weakGrad x‖ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) := by
    have hhv_memLp : MemLp hv.weakGrad (ENNReal.ofReal (2 : ℝ)) μ := by
      simpa using hv.weakGrad_memLp
    exact
      integral_mul_norm_le_Lp_mul_Lq (μ := μ) (f := F) (g := hv.weakGrad)
        Real.HolderConjugate.two_two hF_memLp hhv_memLp
  simpa [divergenceRHSOfField, μ] using
    (calc
      |divergenceRHSOfField F hv| = ‖∫ x, divergenceRHSIntegrandOfField F hv x ∂μ‖ := by
        simp [divergenceRHSOfField, μ]
      _ ≤ ∫ x, ‖divergenceRHSIntegrandOfField F hv x‖ ∂μ :=
        norm_integral_le_integral_norm _
      _ ≤ ∫ x, ‖F x‖ * ‖hv.weakGrad x‖ ∂μ := hnorm_le
      _ ≤
        (∫ x, ‖F x‖ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) *
          (∫ x, ‖hv.weakGrad x‖ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) := hholder)

omit [NeZero d] in
/-- The divergence-form RHS integrand is additive in the test slot. -/
theorem divergenceRHSIntegrandOfField_add
    {Ω : Set E} {F : E → E} {v₁ v₂ : E → ℝ}
    (hv₁ : MemW1pWitness 2 v₁ Ω)
    (hv₂ : MemW1pWitness 2 v₂ Ω) :
    divergenceRHSIntegrandOfField F (hv₁.add hv₂) =
      fun x => divergenceRHSIntegrandOfField F hv₁ x + divergenceRHSIntegrandOfField F hv₂ x := by
  ext x
  have hgrad :
      (hv₁.add hv₂).weakGrad x = hv₁.weakGrad x + hv₂.weakGrad x := by
    simp [MemW1pWitness.add]
  simp [divergenceRHSIntegrandOfField, hgrad, inner_add_right]

/-- The divergence-form RHS is additive in the test slot. -/
theorem divergenceRHSOfField_add
    {Ω : Set E} {F : E → E} (hF : MemLp F 2 (volume.restrict Ω))
    {v₁ v₂ : E → ℝ}
    (hv₁ : MemW1pWitness 2 v₁ Ω)
    (hv₂ : MemW1pWitness 2 v₂ Ω) :
    divergenceRHSOfField F (hv₁.add hv₂) =
      divergenceRHSOfField F hv₁ + divergenceRHSOfField F hv₂ := by
  rw [divergenceRHSOfField, divergenceRHSOfField, divergenceRHSOfField,
    divergenceRHSIntegrandOfField_add]
  rw [integral_add
    (integrable_divergenceRHSIntegrandOfField hF hv₁)
    (integrable_divergenceRHSIntegrandOfField hF hv₂)]
  ring

omit [NeZero d] in
/-- The divergence-form RHS integrand is homogeneous in the test slot. -/
theorem divergenceRHSIntegrandOfField_smul
    {Ω : Set E} {F : E → E} (c : ℝ) {v : E → ℝ}
    (hv : MemW1pWitness 2 v Ω) :
    divergenceRHSIntegrandOfField F (hv.smul c) =
      fun x => c * divergenceRHSIntegrandOfField F hv x := by
  ext x
  simp [divergenceRHSIntegrandOfField, MemW1pWitness.smul, inner_smul_right]

omit [NeZero d] in
/-- The divergence-form RHS is homogeneous in the test slot. -/
theorem divergenceRHSOfField_smul
    {Ω : Set E} {F : E → E} (c : ℝ) {v : E → ℝ}
    (hv : MemW1pWitness 2 v Ω) :
    divergenceRHSOfField F (hv.smul c) = c * divergenceRHSOfField F hv := by
  rw [divergenceRHSOfField, divergenceRHSIntegrandOfField_smul, integral_const_mul,
    divergenceRHSOfField]
  ring

/-- A witness-independent RHS on raw functions obtained by choosing a witness
when `v ∈ H₀¹(Ω)` and returning `0` otherwise. -/
noncomputable def weakProblemRHSOfField {Ω : Set E}
    (F : E → E) : (E → ℝ) → ℝ := by
  classical
  intro v
  exact
    if hv0 : MemH01 v Ω then
      divergenceRHSOfField F (DeGiorgi.MemW1p.someWitness (MemW01p.memW1p hv0))
    else
      0

/-- On `H₀¹(Ω)`, the raw-function RHS agrees with the witness-dependent
divergence-form functional. -/
theorem weakProblemRHSOfField_eq_of_memH01
    {Ω : Set E} (hΩ : IsOpen Ω) {F : E → E} {v : E → ℝ}
    (hv0 : MemH01 v Ω) (hv : MemW1pWitness 2 v Ω) :
    weakProblemRHSOfField (Ω := Ω) F v = divergenceRHSOfField F hv := by
  let _ := (inferInstance : NeZero d)
  rw [weakProblemRHSOfField, dif_pos hv0]
  let hw0 : MemW1pWitness 2 v Ω :=
    DeGiorgi.MemW1p.someWitness (MemW01p.memW1p hv0)
  have hgrad_ae : hw0.weakGrad =ᵐ[volume.restrict Ω] hv.weakGrad := by
    have hp2 : (1 : ENNReal) ≤ 2 := by
      norm_num
    have hcomp :
        ∀ i : Fin d,
          (fun x => hw0.weakGrad x i) =ᵐ[volume.restrict Ω] (fun x => hv.weakGrad x i) := by
      intro i
      exact HasWeakPartialDeriv.ae_eq hΩ (hw0.isWeakGrad i) (hv.isWeakGrad i)
        ((hw0.weakGrad_component_memLp i).locallyIntegrable hp2)
        ((hv.weakGrad_component_memLp i).locallyIntegrable hp2)
    filter_upwards [ae_all_iff.2 hcomp] with x hx
    ext i
    exact hx i
  have hintegral :
      ∫ x in Ω, divergenceRHSIntegrandOfField F hw0 x =
        ∫ x in Ω, divergenceRHSIntegrandOfField F hv x := by
    apply integral_congr_ae
    filter_upwards [hgrad_ae] with x hx
    simpa [divergenceRHSIntegrandOfField, hw0] using
      congrArg (fun g => ⟪F x, g⟫_ℝ) hx
  simpa [hw0, divergenceRHSOfField] using congrArg Neg.neg hintegral

/-- The chosen raw-function RHS is bounded on `H₀¹(Ω)` with respect to the
`L²` gradient seminorm. -/
theorem weakProblemRHSOfField_bound
    {Ω : Set E} (hΩ : IsOpen Ω) {F : E → E}
    (hF : MemLp F 2 (volume.restrict Ω))
    (v : E → ℝ) (hv0 : MemH01 v Ω) (hv : MemW1pWitness 2 v Ω) :
    |weakProblemRHSOfField (Ω := Ω) F v| ≤
      (∫ x, ‖F x‖ ^ (2 : ℝ) ∂(volume.restrict Ω)) ^ (1 / (2 : ℝ)) *
        (∫ x, ‖hv.weakGrad x‖ ^ (2 : ℝ) ∂(volume.restrict Ω)) ^ (1 / (2 : ℝ)) := by
  rw [weakProblemRHSOfField_eq_of_memH01 hΩ hv0 hv]
  exact divergenceRHSOfField_bound hF hv

/-- Raw-function RHS for the lifted Dirichlet problem with boundary datum
`u₀`. -/
noncomputable def weakProblemRHSOfFieldAndDatum {Ω : Set E}
    (A : EllipticCoeff d Ω) (F : E → E)
    {u₀ : E → ℝ} (hu₀ : MemW1pWitness 2 u₀ Ω) :
    (E → ℝ) → ℝ := by
  classical
  intro v
  exact
    if hv0 : MemH01 v Ω then
      let hv0w : MemW1pWitness 2 v Ω :=
        DeGiorgi.MemW1p.someWitness (MemW01p.memW1p hv0)
      divergenceRHSOfField F hv0w - bilinFormOfCoeff A hu₀ hv0w
    else
      0

/-- On `H₀¹(Ω)`, the shifted raw RHS agrees with the natural lifted
functional. -/
theorem weakProblemRHSOfFieldAndDatum_eq_of_memH01
    {Ω : Set E} (hΩ : IsOpen Ω)
    (A : EllipticCoeff d Ω)
    {F : E → E} {u₀ : E → ℝ} (hu₀ : MemW1pWitness 2 u₀ Ω)
    {v : E → ℝ} (hv0 : MemH01 v Ω) (hv : MemW1pWitness 2 v Ω) :
    weakProblemRHSOfFieldAndDatum (A := A) (Ω := Ω) F hu₀ v =
      divergenceRHSOfField F hv - bilinFormOfCoeff A hu₀ hv := by
  rw [weakProblemRHSOfFieldAndDatum, dif_pos hv0]
  let hw0 : MemW1pWitness 2 v Ω :=
    DeGiorgi.MemW1p.someWitness (MemW01p.memW1p hv0)
  have hdiv : divergenceRHSOfField F hw0 = divergenceRHSOfField F hv := by
    have hgrad_ae : hw0.weakGrad =ᵐ[volume.restrict Ω] hv.weakGrad :=
      MemW1pWitness.ae_eq hΩ hw0 hv
    unfold divergenceRHSOfField
    congr 1
    apply integral_congr_ae
    filter_upwards [hgrad_ae] with x hx
    simpa [divergenceRHSIntegrandOfField] using congrArg (fun g => ⟪F x, g⟫_ℝ) hx
  have hbilin : bilinFormOfCoeff A hu₀ hw0 = bilinFormOfCoeff A hu₀ hv := by
    exact bilinFormOfCoeff_eq_right hΩ A hu₀ hw0 hv
  change divergenceRHSOfField F hw0 - bilinFormOfCoeff A hu₀ hw0 =
    divergenceRHSOfField F hv - bilinFormOfCoeff A hu₀ hv
  rw [hdiv, hbilin]

/-- The shifted raw RHS is bounded on `H₀¹(Ω)` with respect to the `L²`
gradient seminorm. -/
theorem weakProblemRHSOfFieldAndDatum_bound
    {Ω : Set E} (hΩ : IsOpen Ω)
    (A : EllipticCoeff d Ω)
    {F : E → E} (hF : MemLp F 2 (volume.restrict Ω))
    {u₀ : E → ℝ} (hu₀ : MemW1pWitness 2 u₀ Ω)
    (v : E → ℝ) (hv0 : MemH01 v Ω) (hv : MemW1pWitness 2 v Ω) :
    |weakProblemRHSOfFieldAndDatum (A := A) (Ω := Ω) F hu₀ v| ≤
      ((∫ x, ‖F x‖ ^ (2 : ℝ) ∂(volume.restrict Ω)) ^ (1 / (2 : ℝ)) +
          A.Λ * (∫ x, ‖hu₀.weakGrad x‖ ^ (2 : ℝ) ∂(volume.restrict Ω)) ^ (1 / (2 : ℝ))) *
        (∫ x, ‖hv.weakGrad x‖ ^ (2 : ℝ) ∂(volume.restrict Ω)) ^ (1 / (2 : ℝ)) := by
  let CF : ℝ :=
    (∫ x, ‖F x‖ ^ (2 : ℝ) ∂(volume.restrict Ω)) ^ (1 / (2 : ℝ))
  let CU : ℝ :=
    A.Λ * (∫ x, ‖hu₀.weakGrad x‖ ^ (2 : ℝ) ∂(volume.restrict Ω)) ^ (1 / (2 : ℝ))
  let GV : ℝ :=
    (∫ x, ‖hv.weakGrad x‖ ^ (2 : ℝ) ∂(volume.restrict Ω)) ^ (1 / (2 : ℝ))
  rw [weakProblemRHSOfFieldAndDatum_eq_of_memH01 hΩ A hu₀ hv0 hv]
  have hdiv : |divergenceRHSOfField F hv| ≤ CF * GV := by
    simpa [CF, GV] using divergenceRHSOfField_bound hF hv
  have hbilin : |bilinFormOfCoeff A hu₀ hv| ≤ CU * GV := by
    simpa [CU, GV, mul_assoc] using bilinForm_bound A hu₀ hv
  calc
    |divergenceRHSOfField F hv - bilinFormOfCoeff A hu₀ hv|
      = |divergenceRHSOfField F hv + (-bilinFormOfCoeff A hu₀ hv)| := by ring_nf
    _ ≤ |divergenceRHSOfField F hv| + |-bilinFormOfCoeff A hu₀ hv| := abs_add_le _ _
    _ = |divergenceRHSOfField F hv| + |bilinFormOfCoeff A hu₀ hv| := by simp
    _ ≤ CF * GV + CU * GV := add_le_add hdiv hbilin
    _ = (CF + CU) * GV := by ring
    _ = ((∫ x, ‖F x‖ ^ (2 : ℝ) ∂(volume.restrict Ω)) ^ (1 / (2 : ℝ)) +
          A.Λ * (∫ x, ‖hu₀.weakGrad x‖ ^ (2 : ℝ) ∂(volume.restrict Ω)) ^ (1 / (2 : ℝ))) *
        (∫ x, ‖hv.weakGrad x‖ ^ (2 : ℝ) ∂(volume.restrict Ω)) ^ (1 / (2 : ℝ)) := by
      rfl

end DeGiorgi
