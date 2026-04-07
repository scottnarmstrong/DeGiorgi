import DeGiorgi.WeakFormulation.ExistenceTheory

/-!
# Weak Formulation: Weighted Estimates

This module collects the weighted bilinear-form expansion and integrability
estimates used in the Caccioppoli and Moser arguments.
-/

noncomputable section

open MeasureTheory Filter
open scoped InnerProductSpace

namespace DeGiorgi

variable {d : ℕ} [NeZero d]

local notation "E" => AmbientSpace d

/-! ### Bilinear form expansion for smooth-product witnesses

These lemmas expand `bilinFormOfCoeff A hu (η · hw)` into its two constituent
terms. This is the key tool for the Caccioppoli / Moser absorption argument:
the bilinear form against a product test function splits into a "principal" term
(involving `η · ⟪A∇u, ∇w⟫`) and a "cross" term (involving `w · ⟪A∇u, ∇η⟫`). -/

/-- Pointwise expansion of the bilinear-form integrand against a smooth-product
witness `η · w`.

The weak gradient of `η · w` is `η · ∇w + (∇η) · w` (from `mul_smooth_bounded_p`),
so the bilinear-form integrand is:
```
⟪A∇u, ∇(η·w)⟫ = η · ⟪A∇u, ∇w⟫ + w · ⟪A∇u, ∇η⟫
```
where `∇η` is encoded as the vector with components `(fderiv ℝ η x)(single i 1)`.

Note: this is an a.e. identity because `mul_smooth_bounded_p` produces
the gradient `η · ∇w + (∇η) · w` by construction. -/
theorem bilinFormIntegrand_mul_smooth_eq
    {Ω : Set E} (hΩ : IsOpen Ω)
    {u w η : E → ℝ}
    (A : EllipticCoeff d Ω)
    (hu : MemW1pWitness 2 u Ω)
    (hw : MemW1pWitness 2 w Ω)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    {C₀ C₁ : ℝ} (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁)
    (hη_bound : ∀ x, |η x| ≤ C₀)
    (hη_grad_bound : ∀ x, ‖fderiv ℝ η x‖ ≤ C₁)
    (hp : (1 : ENNReal) ≤ 2) :
    ∀ x, bilinFormIntegrandOfCoeff A hu
        (hw.mul_smooth_bounded_p (d := d) hp hΩ hη hC₀ hC₁ hη_bound hη_grad_bound) x =
      η x * bilinFormIntegrandOfCoeff A hu hw x +
      w x * ⟪matMulE (A.a x) (hu.weakGrad x),
        (WithLp.toLp 2 fun i =>
          (fderiv ℝ η x) (EuclideanSpace.single i 1) : E)⟫_ℝ := by
  intro x
  -- The weakGrad of mul_smooth_bounded_p at x is:
  --   η x • hw.weakGrad x + toLp 2 (fun i => fderiv ℝ η x (single i 1) * w x)
  -- The bilinear-form integrand ⟪A∇u, ∇(η·w)⟫ distributes over this sum
  -- by bilinearity of the inner product.
  simp only [bilinFormIntegrandOfCoeff, MemW1pWitness.mul_smooth_bounded_p,
    inner_add_right, inner_smul_right]
  congr 1
  -- Factor w(x) out: ⟪v, toLp(f_i * c)⟫ = c * ⟪v, toLp(f_i)⟫
  -- The goal is: Σᵢ ⟪row_i, f_i * w⟫ = (Σᵢ ⟪row_i, f_i⟫) * w
  -- where ⟪a, b⟫_ℝ = a * b, so ⟪a, f_i * w⟫ = a * (f_i * w) = (a * f_i) * w = ⟪a, f_i⟫ * w
  simp only [PiLp.inner_apply, matMulE, Matrix.mulVec]
  rw [Finset.mul_sum]
  congr 1
  ext i
  -- ⟪a, b * c⟫_ℝ = c * ⟪a, b⟫_ℝ for reals
  rw [show (fderiv ℝ η x) (EuclideanSpace.single i 1) * w x =
      w x • ((fderiv ℝ η x) (EuclideanSpace.single i 1)) from by rw [smul_eq_mul]; ring,
    inner_smul_right]

-- Standalone helpers for `bilinForm_weighted_cauchySchwarz`.

/-- Pointwise: `(f * ⟪Aξ,η⟫)² ≤ (f² * ⟪Aξ,ξ⟫) * (Λ * ‖η‖²)` when `‖Aξ‖² ≤ Λ⟪ξ,Aξ⟫`. -/
private theorem pointwise_weighted_cs_sq
    {f_val : ℝ} {bilin_uv bilin_uu : ℝ} {normAu normv : ℝ} {Λ : ℝ}
    (hbilin_uv : |bilin_uv| ≤ normAu * normv)
    (hAu_sq : normAu ^ 2 ≤ Λ * bilin_uu)
    (_hnormAu : 0 ≤ normAu) (_hnormv : 0 ≤ normv) (_hΛ : 0 ≤ Λ) :
    (f_val * bilin_uv) ^ 2 ≤ (f_val ^ 2 * bilin_uu) * (Λ * normv ^ 2) := by
  -- (f * bilin_uv)² = f² * bilin_uv²
  -- ≤ f² * (normAu * normv)²        [from hbilin_uv via sq_abs + sq_le_sq']
  -- = f² * normAu² * normv²
  -- ≤ f² * (Λ * bilin_uu) * normv²   [from hAu_sq]
  -- = (f² * bilin_uu) * (Λ * normv²)
  -- (f * bilin_uv)² ≤ f² * (normAu * normv)² ≤ f² * (Λ * bilin_uu) * normv²
  have h1 : (f_val * bilin_uv) ^ 2 ≤ f_val ^ 2 * (normAu * normv) ^ 2 := by
    have : (f_val * bilin_uv) ^ 2 = f_val ^ 2 * bilin_uv ^ 2 := by ring
    rw [this]
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
    exact sq_le_sq' (neg_le_of_abs_le hbilin_uv) (abs_le.mp hbilin_uv).2
  have h2 : (normAu * normv) ^ 2 = normAu ^ 2 * normv ^ 2 := by ring
  calc (f_val * bilin_uv) ^ 2
      ≤ f_val ^ 2 * (normAu ^ 2 * normv ^ 2) := by linarith
    _ ≤ f_val ^ 2 * (Λ * bilin_uu * normv ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
        apply mul_le_mul_of_nonneg_right hAu_sq (sq_nonneg _)
    _ = (f_val ^ 2 * bilin_uu) * (Λ * normv ^ 2) := by ring

/-- Squaring a bound of the form `c ≤ a^(1/2) * b^(1/2)` gives `c² ≤ a * b`. -/
private theorem sq_le_of_le_rpow_half_mul {a b c : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (h : c ≤ a ^ ((1 : ℝ) / 2) * b ^ ((1 : ℝ) / 2)) :
    c ^ (2 : ℕ) ≤ a * b := by
  have ha_sqrt : a ^ ((1 : ℝ) / 2) ≥ 0 := Real.rpow_nonneg ha _
  have hb_sqrt : b ^ ((1 : ℝ) / 2) ≥ 0 := Real.rpow_nonneg hb _
  have hrhs_nonneg : 0 ≤ a ^ ((1 : ℝ) / 2) * b ^ ((1 : ℝ) / 2) :=
    mul_nonneg ha_sqrt.le hb_sqrt.le
  have hsq : c ^ (2 : ℕ) ≤ (a ^ ((1 : ℝ) / 2) * b ^ ((1 : ℝ) / 2)) ^ (2 : ℕ) :=
    sq_le_sq' (by linarith) h
  have hexpand : (a ^ ((1 : ℝ) / 2) * b ^ ((1 : ℝ) / 2)) ^ (2 : ℕ) = a * b := by
    rw [mul_pow]
    have ha2 : (a ^ ((1 : ℝ) / 2)) ^ (2 : ℕ) = a := by
      rw [← Real.rpow_natCast (a ^ ((1 : ℝ) / 2)) 2]
      rw [← Real.rpow_mul ha]
      norm_num
    have hb2 : (b ^ ((1 : ℝ) / 2)) ^ (2 : ℕ) = b := by
      rw [← Real.rpow_natCast (b ^ ((1 : ℝ) / 2)) 2]
      rw [← Real.rpow_mul hb]
      norm_num
    rw [ha2, hb2]
  linarith

set_option maxHeartbeats 800000 in
/-- The norm of `matMulE (A.a x) ξ` is a.e. strongly measurable when composed with
a Sobolev weak gradient. -/
private theorem aestronglyMeasurable_norm_matMulE_weakGrad
    {Ω : Set E} {u : E → ℝ}
    (A : EllipticCoeff d Ω)
    (hu : MemW1pWitness 2 u Ω) :
    AEStronglyMeasurable (fun x => ‖matMulE (A.a x) (hu.weakGrad x)‖) (volume.restrict Ω) := by
  -- ‖A∇u(x)‖² = ∑ᵢ (∑ⱼ aᵢⱼ * ∂ⱼu)², so ‖A∇u(x)‖ is measurable
  -- via ⟪A∇u, A∇u⟫ = bilinFormIntegrandOfCoeff A' hu hu for suitable A'.
  -- More directly: ‖v‖ = √(⟪v,v⟫) and the inner product is measurable.
  -- We use that A∇u is AEStronglyMeasurable component-wise.
  have hcomp : ∀ i : Fin d, AEMeasurable (fun x =>
      ∑ j : Fin d, A.a x i j * hu.weakGrad x j) (volume.restrict Ω) := by
    intro i
    have hrow_sum :
        AEMeasurable (∑ j : Fin d, fun x => A.a x i j * hu.weakGrad x j)
          (volume.restrict Ω) := by
      refine Finset.aemeasurable_sum (s := (Finset.univ : Finset (Fin d)))
        (f := fun j x => A.a x i j * hu.weakGrad x j) ?_
      intro j _
      exact (A.measurable_comp i j).aemeasurable.mul
        (hu.weakGrad_component_memLp j).aemeasurable
    convert hrow_sum using 1
    ext x
    simp
  -- The norm squared ‖A∇u(x)‖² = ∑ᵢ (component i)²
  -- First show x ↦ ‖A∇u(x)‖² is measurable
  have hscalar : ∀ a b : ℝ, ⟪a, b⟫_ℝ = a * b := by
    intro a b
    simpa using (RCLike.inner_apply' a b)
  have hnorm_sq_eq : ∀ x, ‖matMulE (A.a x) (hu.weakGrad x)‖ ^ 2 =
      ∑ i : Fin d, (∑ j : Fin d, A.a x i j * hu.weakGrad x j) ^ 2 := by
    intro x
    rw [← real_inner_self_eq_norm_sq]
    simp only [PiLp.inner_apply, matMulE_apply, Matrix.mulVec, dotProduct, hscalar]
    congr 1; ext i; ring
  have hnorm_sq_meas : AEMeasurable (fun x =>
      ‖matMulE (A.a x) (hu.weakGrad x)‖ ^ 2) (volume.restrict Ω) := by
    have : (fun x => ‖matMulE (A.a x) (hu.weakGrad x)‖ ^ 2) =
        (fun x => ∑ i : Fin d, (∑ j : Fin d, A.a x i j * hu.weakGrad x j) ^ 2) := by
      ext x; exact hnorm_sq_eq x
    rw [this]
    have hsum_meas :
        AEMeasurable (∑ i : Fin d, fun x =>
          (∑ j : Fin d, A.a x i j * hu.weakGrad x j) ^ 2) (volume.restrict Ω) :=
      Finset.aemeasurable_sum Finset.univ fun i _ => (hcomp i).pow_const 2
    convert hsum_meas using 1
    ext x; simp
  -- ‖v‖ = √(‖v‖²), so measurability of ‖v‖² gives measurability of ‖v‖
  have hmeas_norm : AEMeasurable (fun x => ‖matMulE (A.a x) (hu.weakGrad x)‖)
      (volume.restrict Ω) := by
    have : (fun x => ‖matMulE (A.a x) (hu.weakGrad x)‖) =
        (fun x => Real.sqrt (‖matMulE (A.a x) (hu.weakGrad x)‖ ^ 2)) := by
      ext x; rw [Real.sqrt_sq (norm_nonneg _)]
    rw [this]
    exact hnorm_sq_meas.sqrt
  exact hmeas_norm.aestronglyMeasurable

set_option maxHeartbeats 800000 in
/-- MemLp of `|f| * ‖A∇u‖` at exponent 2, given integrability of `f² * ‖A∇u‖²`.
Extracted as a standalone helper to keep elaboration manageable. -/
private theorem memLp_abs_mul_norm_matMulE
    {Ω : Set E} {u : E → ℝ} {f : E → ℝ}
    (A : EllipticCoeff d Ω)
    (hu : MemW1pWitness 2 u Ω)
    (hf : AEStronglyMeasurable f (volume.restrict Ω))
    (hint : Integrable (fun x =>
        f x ^ 2 * ‖matMulE (A.a x) (hu.weakGrad x)‖ ^ 2) (volume.restrict Ω)) :
    MemLp (fun x => |f x| * ‖matMulE (A.a x) (hu.weakGrad x)‖)
      2 (volume.restrict Ω) := by
  have hg_meas := hf.norm.mul (aestronglyMeasurable_norm_matMulE_weakGrad A hu)
  -- g² = f² * ‖A∇u‖² is integrable ↔ g ∈ L²
  have hint' : Integrable (fun x =>
      ‖|f x| * ‖matMulE (A.a x) (hu.weakGrad x)‖‖ ^ ENNReal.toReal 2) (volume.restrict Ω) := by
    convert hint using 1; ext x
    rw [Real.norm_of_nonneg (mul_nonneg (abs_nonneg _) (norm_nonneg _))]
    have h2 : ENNReal.toReal 2 = (2 : ℝ) := by norm_num
    rw [h2, show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, Real.rpow_natCast, mul_pow, sq_abs]
  -- Use convert to handle MeasurableSpace instance diamond
  convert (integrable_norm_rpow_iff hg_meas two_ne_zero ENNReal.ofNat_ne_top).mp hint'

/-- Weighted Cauchy-Schwarz inequality for the bilinear form.

For any `f : E → ℝ` serving as a weight function:
```
|∫ f · ⟪A∇u, ∇v⟫| ≤ (∫ f² · ⟪A∇u, ∇u⟫)^{1/2} · (Λ · ∫ ‖∇v‖²)^{1/2}
```
This follows from the pointwise bound `|⟪Aξ, η⟫|² ≤ ⟪Aξ,ξ⟫ · ⟪Aη,η⟫ ≤ ⟪Aξ,ξ⟫ · Λ‖η‖²`
(the first inequality is Cauchy-Schwarz for the A-inner product, the second is the upper bound).

This is the key tool for the absorption argument in Moser iteration. -/
theorem bilinForm_weighted_cauchySchwarz
    {Ω : Set E}
    {u v : E → ℝ} {f : E → ℝ}
    (A : EllipticCoeff d Ω)
    (hu : MemW1pWitness 2 u Ω) (hv : MemW1pWitness 2 v Ω)
    (hf : AEStronglyMeasurable f (volume.restrict Ω))
    (hf_sq_int : Integrable (fun x => f x ^ 2 *
        bilinFormIntegrandOfCoeff A hu hu x) (volume.restrict Ω)) :
    (∫ x in Ω, f x * bilinFormIntegrandOfCoeff A hu hv x ∂volume) ^ 2 ≤
      (∫ x in Ω, f x ^ 2 * bilinFormIntegrandOfCoeff A hu hu x ∂volume) *
        (A.Λ * ∫ x in Ω, ‖hv.weakGrad x‖ ^ (2 : ℕ) ∂volume) := by
  let μ : Measure E := volume.restrict Ω
  -- Non-integrable case: integral = 0, so 0² = 0 ≤ RHS
  by_cases hint : Integrable (fun x => f x * bilinFormIntegrandOfCoeff A hu hv x) μ
  · -- Integrable case: use pointwise bound + Hölder
    have hpw_abs : ∀ᵐ x ∂μ, ‖f x * bilinFormIntegrandOfCoeff A hu hv x‖ ≤
        (|f x| * ‖matMulE (A.a x) (hu.weakGrad x)‖) * ‖hv.weakGrad x‖ := by
      filter_upwards with x
      rw [Real.norm_eq_abs, abs_mul, bilinFormIntegrandOfCoeff]
      calc |f x| * |⟪matMulE (A.a x) (hu.weakGrad x), hv.weakGrad x⟫_ℝ|
          ≤ |f x| * (‖matMulE (A.a x) (hu.weakGrad x)‖ * ‖hv.weakGrad x‖) :=
            mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _) (abs_nonneg _)
        _ = (|f x| * ‖matMulE (A.a x) (hu.weakGrad x)‖) * ‖hv.weakGrad x‖ := by ring
    have hdom : ∀ᵐ x ∂μ, f x ^ 2 * ‖matMulE (A.a x) (hu.weakGrad x)‖ ^ 2 ≤
        A.Λ * (f x ^ 2 * bilinFormIntegrandOfCoeff A hu hu x) := by
      filter_upwards [A.mulVec_sq_le] with x hx
      have hmvs := hx (hu.weakGrad x)
      calc f x ^ 2 * ‖matMulE (A.a x) (hu.weakGrad x)‖ ^ 2
          ≤ f x ^ 2 * (A.Λ * ⟪hu.weakGrad x, matMulE (A.a x) (hu.weakGrad x)⟫_ℝ) :=
            mul_le_mul_of_nonneg_left hmvs (sq_nonneg _)
        _ = A.Λ * (f x ^ 2 * ⟪hu.weakGrad x, matMulE (A.a x) (hu.weakGrad x)⟫_ℝ) := by ring
        _ = A.Λ * (f x ^ 2 * bilinFormIntegrandOfCoeff A hu hu x) := by
            rw [bilinFormIntegrandOfCoeff, real_inner_comm]
    have hg_meas : AEStronglyMeasurable (fun x => |f x| * ‖matMulE (A.a x) (hu.weakGrad x)‖) μ :=
      hf.norm.mul (aestronglyMeasurable_norm_matMulE_weakGrad A hu)
    have hfsq_normAu_int : Integrable (fun x =>
        f x ^ 2 * ‖matMulE (A.a x) (hu.weakGrad x)‖ ^ 2) μ := by
      refine Integrable.mono' (hf_sq_int.const_mul A.Λ) ?_ ?_
      · exact (hg_meas.mul hg_meas).congr (ae_of_all _ (fun x => by
          simp only [Pi.mul_apply]; rw [← sq_abs (f x)]; ring))
      · filter_upwards [hdom] with x hx
        rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
        exact hx
    -- g² = f² * ‖A∇u‖² is integrable, so g ∈ L²
    have hg_memLp : MemLp (fun x => |f x| * ‖matMulE (A.a x) (hu.weakGrad x)‖)
        (ENNReal.ofReal 2) μ := by
      rw [show (ENNReal.ofReal (2 : ℝ)) = (2 : ℕ∞) from by norm_num]
      exact memLp_abs_mul_norm_matMulE A hu hf hfsq_normAu_int
    -- h(x) = ‖∇v(x)‖
    have hh_memLp : MemLp (fun x => ‖hv.weakGrad x‖)
        (ENNReal.ofReal 2) μ := by
      rw [show (ENNReal.ofReal (2 : ℝ)) = (2 : ℕ∞) from by norm_num]
      exact hv.weakGrad_memLp.norm
    have hholder :=
      integral_mul_norm_le_Lp_mul_Lq (μ := μ)
        (f := fun x => |f x| * ‖matMulE (A.a x) (hu.weakGrad x)‖)
        (g := fun x => ‖hv.weakGrad x‖)
        Real.HolderConjugate.two_two hg_memLp hh_memLp
    simp only [Real.norm_of_nonneg (mul_nonneg (abs_nonneg _) (norm_nonneg _)),
      Real.norm_of_nonneg (norm_nonneg _)] at hholder
    -- |∫ f*bilin| ≤ ∫ |f*bilin| ≤ ∫ g*h ≤ (∫ g²)^(1/2) * (∫ h²)^(1/2)
    -- Need: g*h integrable for integral_mono_ae
    have hgh_int : Integrable (fun x =>
        (|f x| * ‖matMulE (A.a x) (hu.weakGrad x)‖) * ‖hv.weakGrad x‖) μ := by
      have hh2_int : Integrable (fun x => ‖hv.weakGrad x‖ ^ (2 : ℕ)) μ := by
        have := (integrable_norm_rpow_iff
          hv.weakGrad_memLp.aestronglyMeasurable.norm two_ne_zero ENNReal.ofNat_ne_top).mpr
          hv.weakGrad_memLp.norm
        convert this using 1; ext x
        rw [Real.norm_of_nonneg (norm_nonneg _)]
        have h2 : ENNReal.toReal 2 = (2 : ℝ) := by norm_num
        rw [h2, show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, Real.rpow_natCast]
      refine Integrable.mono'
        ((hfsq_normAu_int.add hh2_int).div_const 2)
        (hg_meas.mul hv.weakGrad_memLp.aestronglyMeasurable.norm)
        (ae_of_all _ (fun x => ?_))
      rw [Real.norm_of_nonneg (mul_nonneg (mul_nonneg (abs_nonneg _) (norm_nonneg _))
        (norm_nonneg _))]
      simp only [Pi.add_apply]
      have hg := mul_nonneg (abs_nonneg (f x)) (norm_nonneg (matMulE (A.a x) (hu.weakGrad x)))
      have hh := norm_nonneg (hv.weakGrad x)
      nlinarith [sq_nonneg (|f x| * ‖matMulE (A.a x) (hu.weakGrad x)‖ - ‖hv.weakGrad x‖),
        sq_abs (f x), mul_self_nonneg (‖matMulE (A.a x) (hu.weakGrad x)‖)]
    have habs_le : |∫ x, f x * bilinFormIntegrandOfCoeff A hu hv x ∂μ| ≤
        ∫ x, (|f x| * ‖matMulE (A.a x) (hu.weakGrad x)‖) * ‖hv.weakGrad x‖ ∂μ := by
      calc |∫ x, f x * bilinFormIntegrandOfCoeff A hu hv x ∂μ|
          = ‖∫ x, f x * bilinFormIntegrandOfCoeff A hu hv x ∂μ‖ := (Real.norm_eq_abs _).symm
        _ ≤ ∫ x, ‖f x * bilinFormIntegrandOfCoeff A hu hv x‖ ∂μ :=
            norm_integral_le_integral_norm _
        _ ≤ _ := integral_mono_ae hint.norm hgh_int hpw_abs
    have hle_rpow : |∫ x, f x * bilinFormIntegrandOfCoeff A hu hv x ∂μ| ≤
        (∫ x, (|f x| * ‖matMulE (A.a x) (hu.weakGrad x)‖) ^ (2 : ℝ) ∂μ) ^ ((1 : ℝ) / 2) *
        (∫ x, ‖hv.weakGrad x‖ ^ (2 : ℝ) ∂μ) ^ ((1 : ℝ) / 2) :=
      le_trans habs_le hholder
    have hsq : (∫ x, f x * bilinFormIntegrandOfCoeff A hu hv x ∂μ) ^ (2 : ℕ) ≤
        (∫ x, (|f x| * ‖matMulE (A.a x) (hu.weakGrad x)‖) ^ (2 : ℝ) ∂μ) *
        (∫ x, ‖hv.weakGrad x‖ ^ (2 : ℝ) ∂μ) := by
      have := sq_le_of_le_rpow_half_mul
        (integral_nonneg (fun x => by positivity))
        (integral_nonneg (fun x => by positivity))
        (abs_nonneg _) hle_rpow
      rwa [sq_abs] at this
    have hrpow_g : ∀ x, (|f x| * ‖matMulE (A.a x) (hu.weakGrad x)‖) ^ (2 : ℝ) =
        f x ^ 2 * ‖matMulE (A.a x) (hu.weakGrad x)‖ ^ 2 := by
      intro x
      rw [Real.mul_rpow (abs_nonneg _) (norm_nonneg _)]
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num]
      rw [Real.rpow_natCast, Real.rpow_natCast, sq_abs]
    have hrpow_h : ∀ x, ‖hv.weakGrad x‖ ^ (2 : ℝ) = (‖hv.weakGrad x‖ ^ (2 : ℕ) : ℝ) := by
      intro x
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, Real.rpow_natCast]
    simp_rw [hrpow_g, hrpow_h] at hsq
    have hint_dom : ∫ x, f x ^ 2 * ‖matMulE (A.a x) (hu.weakGrad x)‖ ^ 2 ∂μ ≤
        A.Λ * ∫ x, f x ^ 2 * bilinFormIntegrandOfCoeff A hu hu x ∂μ := by
      calc ∫ x, f x ^ 2 * ‖matMulE (A.a x) (hu.weakGrad x)‖ ^ 2 ∂μ
          ≤ ∫ x, A.Λ * (f x ^ 2 * bilinFormIntegrandOfCoeff A hu hu x) ∂μ :=
            integral_mono_ae hfsq_normAu_int (hf_sq_int.const_mul A.Λ) hdom
        _ = A.Λ * ∫ x, f x ^ 2 * bilinFormIntegrandOfCoeff A hu hu x ∂μ :=
            integral_const_mul _ _
    -- Final assembly
    calc (∫ x, f x * bilinFormIntegrandOfCoeff A hu hv x ∂μ) ^ 2
        ≤ (∫ x, f x ^ 2 * ‖matMulE (A.a x) (hu.weakGrad x)‖ ^ 2 ∂μ) *
          (∫ x, ‖hv.weakGrad x‖ ^ (2 : ℕ) ∂μ) := hsq
      _ ≤ (A.Λ * ∫ x, f x ^ 2 * bilinFormIntegrandOfCoeff A hu hu x ∂μ) *
          (∫ x, ‖hv.weakGrad x‖ ^ (2 : ℕ) ∂μ) :=
          mul_le_mul_of_nonneg_right hint_dom (integral_nonneg (fun x => by positivity))
      _ = (∫ x, f x ^ 2 * bilinFormIntegrandOfCoeff A hu hu x ∂μ) *
          (A.Λ * ∫ x, ‖hv.weakGrad x‖ ^ (2 : ℕ) ∂μ) := by ring
  · -- Non-integrable case
    have hlhs : ∫ x in Ω, f x * bilinFormIntegrandOfCoeff A hu hv x = 0 :=
      integral_undef hint
    rw [hlhs]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
    exact mul_nonneg
      (integral_nonneg_of_ae (by
        filter_upwards [A.coercive] with x hx
        have hbilin_nonneg : 0 ≤ bilinFormIntegrandOfCoeff A hu hu x := by
          simp only [bilinFormIntegrandOfCoeff]
          rw [real_inner_comm]
          exact le_trans (mul_nonneg A.lam_nonneg (sq_nonneg _)) (hx (hu.weakGrad x))
        exact mul_nonneg (sq_nonneg _) hbilin_nonneg))
      (mul_nonneg A.Λ_nonneg (integral_nonneg (fun x => by positivity)))

/-- Integrability of a bounded scalar times the bilinear-form integrand.

If `|f(x)| ≤ C` everywhere and the bilinear-form integrand `⟪A∇u,∇u⟫` is
integrable (which it always is for `u ∈ W^{1,2}`), then `f · ⟪A∇u,∇u⟫` is
integrable. This is a key API lemma for the Caccioppoli/Moser absorption argument.

Proved in a standalone context to keep elaboration manageable in the presence of
`WithLp`/`PiLp` coercions. -/
theorem integrable_bounded_mul_bilinFormIntegrand
    {Ω : Set E}
    {u : E → ℝ} {f : E → ℝ} {C : ℝ}
    (A : EllipticCoeff d Ω)
    (hu : MemW1pWitness 2 u Ω)
    (hf_meas : AEStronglyMeasurable f (volume.restrict Ω))
    (hf_bound : ∀ x, |f x| ≤ C) :
    Integrable (fun x => f x * bilinFormIntegrandOfCoeff A hu hu x) (volume.restrict Ω) := by
  have hbilin_int := integrable_bilinFormIntegrandOfCoeff A hu hu
  have hC_nonneg : 0 ≤ C := le_trans (abs_nonneg (f 0)) (hf_bound 0)
  -- Use: |f · g| ≤ C · |g|, and C · |g| is integrable since g is.
  apply Integrable.mono' ((hbilin_int.norm).const_mul C)
    (hf_meas.mul (aestronglyMeasurable_bilinFormIntegrandOfCoeff A hu hu))
  filter_upwards with x
  simp only [Pi.mul_apply, Real.norm_eq_abs]
  calc ‖f x * bilinFormIntegrandOfCoeff A hu hu x‖
      = |f x| * |bilinFormIntegrandOfCoeff A hu hu x| := by
        rw [Real.norm_eq_abs, abs_mul]
    _ ≤ C * |bilinFormIntegrandOfCoeff A hu hu x| :=
        mul_le_mul_of_nonneg_right (hf_bound x) (abs_nonneg _)
    _ = C * ‖bilinFormIntegrandOfCoeff A hu hu x‖ := by
        rw [Real.norm_eq_abs]

end DeGiorgi
