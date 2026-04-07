import DeGiorgi.Foundations

/-!
# Chapter 03: Coefficients

This chapter defines the elliptic coefficient structures used throughout the
development.

It uses a unified coefficient structure with measurable coefficients, lower
ellipticity on `a` and `a⁻¹`, and derived mixed and upper bounds recorded as
theorems rather than primitive fields.
-/

noncomputable section

open MeasureTheory
open scoped InnerProductSpace

namespace DeGiorgi

/-- The ambient Euclidean space used by the elliptic regularity development. -/
abbrev AmbientSpace (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- Matrix action on the ambient Euclidean space. -/
def matMulE {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) (ξ : AmbientSpace d) : AmbientSpace d :=
  WithLp.toLp 2 (Matrix.mulVec M ξ.ofLp)

@[simp] theorem matMulE_ofLp {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) (ξ : AmbientSpace d) :
    (matMulE M ξ).ofLp = Matrix.mulVec M ξ.ofLp :=
  rfl

@[simp] theorem matMulE_apply {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ)
    (ξ : AmbientSpace d) (i : Fin d) :
    matMulE M ξ i = Matrix.mulVec M ξ.ofLp i :=
  rfl

/-- Unified nonsymmetric elliptic coefficient field for the elliptic regularity
development.

It is designed to serve both:

- the variational / weak-solution branch, which needs measurability;
- the De Giorgi / Moser branch, which uses coercivity of `a⁻¹` to derive mixed
  and upper bounds.

The upper bounds are intentionally not primitive fields in this structure. -/
structure EllipticCoeff (d : ℕ) [NeZero d] (Ω : Set (AmbientSpace d)) where
  /-- Matrix-valued coefficient field. -/
  a : AmbientSpace d → Matrix (Fin d) (Fin d) ℝ
  /-- Lower ellipticity constant. -/
  lam : ℝ
  /-- Upper ellipticity constant. -/
  Λ : ℝ
  /-- Componentwise measurability of the coefficient field. -/
  measurable_comp : ∀ i j, Measurable (fun x => a x i j)
  /-- Positivity of the lower ellipticity constant. -/
  hlam : 0 < lam
  /-- Comparison of lower and upper ellipticity scales. -/
  hΛ : lam ≤ Λ
  /-- Coercivity on `a`, stated almost everywhere on `Ω`. -/
  coercive : ∀ᵐ x ∂(MeasureTheory.volume.restrict Ω), ∀ ξ : AmbientSpace d,
    lam * ‖ξ‖ ^ 2 ≤ ⟪ξ, matMulE (a x) ξ⟫_ℝ
  /-- Coercivity on `a⁻¹`, stated almost everywhere on `Ω`. -/
  coercive_inv : ∀ᵐ x ∂(MeasureTheory.volume.restrict Ω), ∀ ξ : AmbientSpace d,
    Λ⁻¹ * ‖ξ‖ ^ 2 ≤ ⟪ξ, matMulE ((a x)⁻¹) ξ⟫_ℝ

/-- The ellipticity ratio governing scale-invariant estimates. -/
def ellipticityRatio {d : ℕ} [NeZero d] {Ω : Set (AmbientSpace d)}
    (A : EllipticCoeff d Ω) : ℝ :=
  A.Λ / A.lam

/-- Optional normalized view of the unified coefficient structure. -/
abbrev NormalizedEllipticCoeff (d : ℕ) [NeZero d] (Ω : Set (AmbientSpace d)) :=
  {A : EllipticCoeff d Ω // A.lam = 1}

namespace EllipticCoeff

variable {d : ℕ} [NeZero d] {Ω : Set (AmbientSpace d)} (A : EllipticCoeff d Ω)

@[simp] theorem ellipticityRatio_def :
    ellipticityRatio A = A.Λ / A.lam := rfl

theorem lam_nonneg : 0 ≤ A.lam :=
  le_of_lt A.hlam

theorem Λ_pos : 0 < A.Λ :=
  lt_of_lt_of_le A.hlam A.hΛ

theorem Λ_nonneg : 0 ≤ A.Λ :=
  A.Λ_pos.le

theorem ellipticityRatio_pos : 0 < ellipticityRatio A := by
  dsimp [ellipticityRatio]
  exact div_pos A.Λ_pos A.hlam

theorem ellipticityRatio_nonneg : 0 ≤ ellipticityRatio A :=
  (A.ellipticityRatio_pos).le

theorem one_le_ellipticityRatio : 1 ≤ ellipticityRatio A := by
  simpa [ellipticityRatio] using (one_le_div A.hlam).2 A.hΛ

theorem ae_coercive_nonneg :
    ∀ᵐ x ∂(MeasureTheory.volume.restrict Ω), ∀ ξ : AmbientSpace d,
      0 ≤ ⟪ξ, matMulE (A.a x) ξ⟫_ℝ := by
  filter_upwards [A.coercive] with x hx
  intro ξ
  have hnonneg : 0 ≤ A.lam * ‖ξ‖ ^ 2 := by
    exact mul_nonneg A.lam_nonneg (sq_nonneg ‖ξ‖)
  exact le_trans hnonneg (hx ξ)

theorem ae_coercive_inv_nonneg :
    ∀ᵐ x ∂(MeasureTheory.volume.restrict Ω), ∀ ξ : AmbientSpace d,
      0 ≤ ⟪ξ, matMulE ((A.a x)⁻¹) ξ⟫_ℝ := by
  filter_upwards [A.coercive_inv] with x hx
  intro ξ
  have hnonneg : 0 ≤ A.Λ⁻¹ * ‖ξ‖ ^ 2 := by
    exact mul_nonneg (inv_nonneg.mpr A.Λ_nonneg) (sq_nonneg ‖ξ‖)
  exact le_trans hnonneg (hx ξ)

theorem measurable_apply (i j : Fin d) :
    Measurable (fun x => A.a x i j) :=
  A.measurable_comp i j

theorem det_ne_zero_of_coercive {x : AmbientSpace d}
    (hx : ∀ ξ : AmbientSpace d,
      A.lam * ‖ξ‖ ^ 2 ≤ ⟪ξ, matMulE (A.a x) ξ⟫_ℝ) :
    (A.a x).det ≠ 0 := by
  classical
  rw [ne_eq, ← Matrix.exists_mulVec_eq_zero_iff]
  intro hsing
  rcases hsing with ⟨v, hv_ne, hv_zero⟩
  let ξ : AmbientSpace d := WithLp.toLp 2 v
  have hξ_zero_action : matMulE (A.a x) ξ = 0 := by
    apply PiLp.ext
    intro i
    simp [matMulE, ξ, hv_zero]
  have hcoer : A.lam * ‖ξ‖ ^ 2 ≤ ⟪ξ, matMulE (A.a x) ξ⟫_ℝ := hx ξ
  have hmul_nonneg : 0 ≤ A.lam * ‖ξ‖ ^ 2 := by
    exact mul_nonneg A.lam_nonneg (sq_nonneg ‖ξ‖)
  have hmul_eq_zero : A.lam * ‖ξ‖ ^ 2 = 0 := by
    refine le_antisymm ?_ hmul_nonneg
    simpa [hξ_zero_action] using hcoer
  have hnorm_sq_eq_zero : ‖ξ‖ ^ 2 = 0 := by
    exact (mul_eq_zero.mp hmul_eq_zero).resolve_left (ne_of_gt A.hlam)
  have hnorm_eq_zero : ‖ξ‖ = 0 := by
    nlinarith [sq_nonneg ‖ξ‖, hnorm_sq_eq_zero]
  have hξ_zero' : ξ = 0 := norm_eq_zero.mp hnorm_eq_zero
  have hv_zero' : v = 0 := by
    have hcoords : ξ.ofLp = 0 := by
      simpa [ξ] using congrArg (fun η : AmbientSpace d => η.ofLp) hξ_zero'
    simpa [ξ] using hcoords
  exact hv_ne hv_zero'

theorem inv_matMulE_matMulE {x : AmbientSpace d}
    (hx : ∀ ξ : AmbientSpace d,
      A.lam * ‖ξ‖ ^ 2 ≤ ⟪ξ, matMulE (A.a x) ξ⟫_ℝ)
    (ξ : AmbientSpace d) :
    matMulE ((A.a x)⁻¹) (matMulE (A.a x) ξ) = ξ := by
  apply PiLp.ext
  intro i
  have hdet_unit : IsUnit (A.a x).det :=
    (isUnit_iff_ne_zero.2 <| A.det_ne_zero_of_coercive hx)
  simp [matMulE, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet_unit, Matrix.one_mulVec]

/-- Mixed quadratic bound derived from inverse coercivity. -/
theorem mulVec_sq_le :
    ∀ᵐ x ∂(MeasureTheory.volume.restrict Ω), ∀ ξ : AmbientSpace d,
      ‖matMulE (A.a x) ξ‖ ^ 2 ≤ A.Λ * ⟪ξ, matMulE (A.a x) ξ⟫_ℝ := by
  filter_upwards [A.coercive, A.coercive_inv] with x hx_coercive hx_inv
  intro ξ
  let η : AmbientSpace d := matMulE (A.a x) ξ
  have hscaled :
      ‖η‖ ^ 2 ≤ A.Λ * ⟪η, matMulE ((A.a x)⁻¹) η⟫_ℝ := by
    have h := mul_le_mul_of_nonneg_left (hx_inv η) A.Λ_nonneg
    have hΛ_ne : A.Λ ≠ 0 := ne_of_gt A.Λ_pos
    simpa [η, mul_assoc, hΛ_ne] using h
  calc
    ‖matMulE (A.a x) ξ‖ ^ 2 = ‖η‖ ^ 2 := by
      rfl
    _ ≤ A.Λ * ⟪η, matMulE ((A.a x)⁻¹) η⟫_ℝ := hscaled
    _ = A.Λ * ⟪η, ξ⟫_ℝ := by
      rw [A.inv_matMulE_matMulE hx_coercive ξ]
    _ = A.Λ * ⟪ξ, η⟫_ℝ := by
      rw [real_inner_comm]
    _ = A.Λ * ⟪ξ, matMulE (A.a x) ξ⟫_ℝ := by
      rfl

/-- Pointwise quadratic upper bound derived from the mixed bound. -/
theorem quadratic_upper :
    ∀ᵐ x ∂(MeasureTheory.volume.restrict Ω), ∀ ξ : AmbientSpace d,
      ⟪ξ, matMulE (A.a x) ξ⟫_ℝ ≤ A.Λ * ‖ξ‖ ^ 2 := by
  filter_upwards [A.coercive, A.mulVec_sq_le] with x hx_coercive hx_mul ξ
  let q : ℝ := ⟪ξ, matMulE (A.a x) ξ⟫_ℝ
  let m : ℝ := ‖matMulE (A.a x) ξ‖
  let n : ℝ := ‖ξ‖
  have hq_nonneg : 0 ≤ q := by
    exact le_trans (mul_nonneg A.lam_nonneg (sq_nonneg ‖ξ‖)) (by simpa [q] using hx_coercive ξ)
  have hq_le : q ≤ n * m := by
    simpa [q, m, n, abs_of_nonneg hq_nonneg, mul_comm] using
      (abs_real_inner_le_norm ξ (matMulE (A.a x) ξ))
  have hm_sq : m ^ 2 ≤ A.Λ * q := by
    simpa [m, q] using hx_mul ξ
  have hn_nonneg : 0 ≤ n := norm_nonneg ξ
  have hm_nonneg : 0 ≤ m := norm_nonneg (matMulE (A.a x) ξ)
  have hq_mul : q * q ≤ (A.Λ * n ^ 2) * q := by
    nlinarith [hq_le, hm_sq, hn_nonneg, hm_nonneg, A.Λ_nonneg]
  have hupper : q ≤ A.Λ * n ^ 2 := by
    by_cases hq_zero : q = 0
    · have hnonneg : 0 ≤ A.Λ * n ^ 2 := mul_nonneg A.Λ_nonneg (sq_nonneg n)
      simpa [hq_zero] using hnonneg
    · have hq_pos : 0 < q := lt_of_le_of_ne hq_nonneg (by simpa [eq_comm] using hq_zero)
      exact le_of_mul_le_mul_right
        (by simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using hq_mul)
        hq_pos
  simpa [q, n] using hupper

/-- Mixed bilinear bound needed by the variational branch. -/
theorem mixed_bound :
    ∀ᵐ x ∂(MeasureTheory.volume.restrict Ω), ∀ ξ ζ : AmbientSpace d,
      |⟪ζ, matMulE (A.a x) ξ⟫_ℝ| ≤ A.Λ * ‖ζ‖ * ‖ξ‖ := by
  filter_upwards [A.mulVec_sq_le, A.quadratic_upper] with x hx_mul hx_quad
  intro ξ ζ
  let m : ℝ := ‖matMulE (A.a x) ξ‖
  let nξ : ℝ := ‖ξ‖
  let nζ : ℝ := ‖ζ‖
  have habs : |⟪ζ, matMulE (A.a x) ξ⟫_ℝ| ≤ nζ * m := by
    simpa [m, nζ, mul_comm] using abs_real_inner_le_norm ζ (matMulE (A.a x) ξ)
  have hm_sq : m ^ 2 ≤ A.Λ * ⟪ξ, matMulE (A.a x) ξ⟫_ℝ := by
    simpa [m] using hx_mul ξ
  have hq_upper :
      ⟪ξ, matMulE (A.a x) ξ⟫_ℝ ≤ A.Λ * nξ ^ 2 := by
    simpa [nξ] using hx_quad ξ
  have hm_le : m ≤ A.Λ * nξ := by
    have hm_nonneg : 0 ≤ m := norm_nonneg (matMulE (A.a x) ξ)
    have hnξ_nonneg : 0 ≤ nξ := norm_nonneg ξ
    have hrhs_nonneg : 0 ≤ A.Λ * nξ := mul_nonneg A.Λ_nonneg hnξ_nonneg
    have hm_sq_upper : m ^ 2 ≤ (A.Λ * nξ) ^ 2 := by
      nlinarith [hm_sq, hq_upper, A.Λ_nonneg]
    exact (sq_le_sq₀ hm_nonneg hrhs_nonneg).1 hm_sq_upper
  have hnζ_nonneg : 0 ≤ nζ := norm_nonneg ζ
  calc
    |⟪ζ, matMulE (A.a x) ξ⟫_ℝ| ≤ nζ * m := habs
    _ ≤ nζ * (A.Λ * nξ) := by
      exact mul_le_mul_of_nonneg_left hm_le hnζ_nonneg
    _ = A.Λ * ‖ζ‖ * ‖ξ‖ := by
      ring

end EllipticCoeff

namespace NormalizedEllipticCoeff

variable {d : ℕ} [NeZero d] {Ω : Set (AmbientSpace d)}
  (A : NormalizedEllipticCoeff d Ω)

@[simp] theorem lam_eq_one : A.1.lam = 1 :=
  A.2

@[simp] theorem ellipticityRatio_eq_Λ :
    ellipticityRatio A.1 = A.1.Λ := by
  simp [ellipticityRatio]

end NormalizedEllipticCoeff

end DeGiorgi
