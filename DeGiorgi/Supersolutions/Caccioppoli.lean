import DeGiorgi.Supersolutions.TestFunctions

/-!
# Supersolutions Weighted Caccioppoli

This module contains the weighted Caccioppoli inequality used in the
supersolution iteration arguments.
-/

noncomputable section

open MeasureTheory Metric

namespace DeGiorgi

variable {d : ℕ} [NeZero d]

local notation "E" => AmbientSpace d
local notation "μhalf" => (volume.restrict (Metric.ball (0 : E) (1 / 2 : ℝ)))

/-! ### Weighted Caccioppoli inequality for supersolutions

The abstract tool for Moser-type energy bounds: if `u > 0` is a supersolution
and `Ψ : ℝ → ℝ` is a smooth nonneg function with `Ψ(0) = 0` and `Ψ' ≥ 0`,
then testing with `φ² Ψ(u)` gives:

  `∫ φ² Ψ'(u) ⟨A∇u,∇u⟩ ≤ 4 ∫ (Ψ(u)²/Ψ'(u)) ⟨A∇φ,∇φ⟩`

Proof: expand `bilinFormOfCoeff` via `bilinFormIntegrand_mul_smooth_eq`,
apply AM-GM to the cross term, absorb into the principal term. -/

set_option maxHeartbeats 800000 in
/-- Weighted Caccioppoli inequality for supersolutions.

For `u > 0` a supersolution on `Ω`, `Ψ` smooth with `Ψ(0) = 0`, bounded derivative,
and `Ψ(u) ≥ 0`, and `φ` a smooth cutoff with compact support in `Ω`:

  `∫ φ² Ψ'(u) ⟨A∇u,∇u⟩ ≤ 4Λ ∫ |∇φ|² Ψ(u)²/Ψ'(u)`

where the ratio `Ψ²/Ψ'` is understood to be 0 where `Ψ' = 0`.

The proof uses the supersolution inequality `0 ≤ ∫⟨A∇u, ∇(φ²Ψ(u))⟩`,
expanded via `bilinFormIntegrand_mul_smooth_eq` into principal + cross terms,
then the cross term is absorbed via AM-GM. -/
theorem weighted_caccioppoli_of_supersolution
    {Ω : Set E} (hΩ : IsOpen Ω)
    {u φ : E → ℝ}
    (A : NormalizedEllipticCoeff d Ω)
    (hu : MemW1pWitness 2 u Ω)
    (hsuper : IsSupersolution A.1 u)
    (Ψ : ℝ → ℝ) (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ) (hΨ_zero : Ψ 0 = 0)
    (hΨ_bdd : ∃ M, ∀ t, |deriv Ψ t| ≤ M)
    (hΨ_nonneg : ∀ x ∈ Ω, 0 ≤ Ψ (u x))
    (hΨ'_nonpos : ∀ x ∈ Ω, deriv Ψ (u x) ≤ 0)
    (hΨ_zero_of_deriv_zero : ∀ x ∈ Ω, deriv Ψ (u x) = 0 → Ψ (u x) = 0)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    {Cφ : ℝ} (hCφ : 0 ≤ Cφ)
    (hφ_bound : ∀ x, |φ x| ≤ 1)
    (hφ_grad_bound : ∀ x, ‖fderiv ℝ φ x‖ ≤ Cφ)
    (hφ_support : tsupport φ ⊆ Ω)
    (hratio_int :
      Integrable
        (fun x => ‖fderiv ℝ φ x‖ ^ 2 *
          (if deriv Ψ (u x) = 0 then 0
           else Ψ (u x) ^ 2 / (-deriv Ψ (u x))))
        (volume.restrict Ω))
    (hφ_memH01 : MemH01 (fun x => φ x ^ 2 * Ψ (u x)) Ω) :
    -- |Principal term| ≤ 4Λ · gradient term
    -- Here |Ψ'| = -Ψ' since Ψ' ≤ 0.
    ∫ x in Ω, φ x ^ 2 * (-deriv Ψ (u x)) *
        bilinFormIntegrandOfCoeff A.1 hu hu x ∂volume ≤
      4 * A.1.Λ * ∫ x in Ω, ‖fderiv ℝ φ x‖ ^ 2 *
        (if deriv Ψ (u x) = 0 then 0
         else Ψ (u x) ^ 2 / (-deriv Ψ (u x))) ∂volume := by
  let hwΨ : MemW1pWitness 2 (fun x => Ψ (u x)) Ω :=
    MemW1pWitness.comp_smooth_bounded (d := d) hΩ hu Ψ hΨ hΨ_zero hΨ_bdd
  let hwφΨ := hwΨ.mul_smooth_bounded_p (d := d)
    (by norm_num : (1 : ENNReal) ≤ 2) hΩ hφ (by norm_num : (0 : ℝ) ≤ 1) hCφ
    hφ_bound hφ_grad_bound
  let hwφ2Ψ := hwφΨ.mul_smooth_bounded_p (d := d)
    (by norm_num : (1 : ENNReal) ≤ 2) hΩ hφ (by norm_num : (0 : ℝ) ≤ 1) hCφ
    hφ_bound hφ_grad_bound
  -- φ(x) * (φ(x) * Ψ(u(x))) = φ(x)² * Ψ(u(x)) ≥ 0
  -- Need MemH01 for the product function. The function φ·(φ·Ψ(u)) = φ²·Ψ(u).
  have hφ2Ψ_eq : (fun x => φ x * (φ x * Ψ (u x))) = (fun x => φ x ^ 2 * Ψ (u x)) := by
    ext x; ring
  have hφ2Ψ_memH01 : MemH01 (fun x => φ x * (φ x * Ψ (u x))) Ω := by
    rwa [hφ2Ψ_eq]
  have hφ2Ψ_nonneg : ∀ x, 0 ≤ φ x * (φ x * Ψ (u x)) := by
    intro x
    rw [show φ x * (φ x * Ψ (u x)) = φ x ^ 2 * Ψ (u x) by ring]
    by_cases hx : x ∈ Ω
    · exact mul_nonneg (sq_nonneg _) (hΨ_nonneg x hx)
    · -- Outside Ω, φ has compact support in Ω, so φ(x) = 0
      have hφx : φ x = 0 := by
        by_contra h
        exact hx (hφ_support (subset_tsupport _ h))
      simp [hφx]
  have htest : 0 ≤ bilinFormOfCoeff A.1 hu hwφ2Ψ := by
    exact hsuper.2 hu _ hφ2Ψ_memH01 hwφ2Ψ hφ2Ψ_nonneg
  -- The inner expansion: ⟨A∇u, ∇(Ψ(u))⟩ = Ψ'(u)·⟨A∇u,∇u⟩
  -- (from comp_smooth_bounded: the gradient of Ψ(u) is Ψ'(u)·∇u)
  have hΨu_bilin : ∀ x, bilinFormIntegrandOfCoeff A.1 hu hwΨ x =
      deriv Ψ (u x) * bilinFormIntegrandOfCoeff A.1 hu hu x := by
    intro x
    -- `∇(Ψ ∘ u) = Ψ'(u) ∇u`, so the bilinear integrand factors by pulling
    -- the scalar `Ψ'(u)` out of the inner product.
    have hgrad_eq : hwΨ.weakGrad x = deriv Ψ (u x) • hu.weakGrad x := by
      ext i; simp [hwΨ, MemW1pWitness.comp_smooth_bounded, smul_eq_mul]
    rw [bilinFormIntegrandOfCoeff, hgrad_eq, inner_smul_right]
    simp [bilinFormIntegrandOfCoeff]
  -- The ⟨A∇u, ∇φ⟩ term from the expansion lemma
  let fderivφ_vec : E → E := fun x =>
    WithLp.toLp 2 fun i => (fderiv ℝ φ x) (EuclideanSpace.single i 1)
  let AuDφ : E → ℝ := fun x =>
    @inner ℝ E _ (matMulE (A.1.a x) (hu.weakGrad x)) (fderivφ_vec x)
  -- Expand the double product: ⟨A∇u, ∇(φ·(φΨ))⟩ = φ·⟨A∇u, ∇(φΨ)⟩ + φΨ·AuDφ
  -- and ⟨A∇u, ∇(φΨ)⟩ = φ·Ψ'·⟨A∇u,∇u⟩ + Ψ·AuDφ
  -- Combined: φ²Ψ'⟨A∇u,∇u⟩ + 2φΨ·AuDφ
  have hexpand_outer := bilinFormIntegrand_mul_smooth_eq (d := d) hΩ A.1 hu hwφΨ hφ
    (by norm_num : (0 : ℝ) ≤ 1) hCφ hφ_bound hφ_grad_bound (by norm_num : (1 : ENNReal) ≤ 2)
  have hexpand_inner := bilinFormIntegrand_mul_smooth_eq (d := d) hΩ A.1 hu hwΨ hφ
    (by norm_num : (0 : ℝ) ≤ 1) hCφ hφ_bound hφ_grad_bound (by norm_num : (1 : ENNReal) ≤ 2)
  -- Pointwise: integrand of bilinFormOfCoeff = φ²Ψ'⟨A∇u,∇u⟩ + 2φΨ·AuDφ
  let P_x : E → ℝ := fun x =>
    φ x ^ 2 * deriv Ψ (u x) * bilinFormIntegrandOfCoeff A.1 hu hu x
  let Q_x : E → ℝ := fun x => 2 * φ x * Ψ (u x) * AuDφ x
  have hPQ : ∀ x, bilinFormIntegrandOfCoeff A.1 hu hwφ2Ψ x = P_x x + Q_x x := by
    intro x
    rw [hexpand_outer x, hexpand_inner x, hΨu_bilin x]
    dsimp [P_x, Q_x, AuDφ]
    ring
  -- From htest: 0 ≤ ∫(P + Q). Since Ψ' ≤ 0, P_x ≤ 0.
  -- So 0 ≤ ∫P + ∫Q, with ∫P ≤ 0. Thus -∫P ≤ ∫Q, i.e., |∫P| ≤ ∫Q.
  -- Equivalently: ∫ φ²|Ψ'|⟨A∇u,∇u⟩ ≤ 2∫ φΨ·AuDφ.
  have hPQ_int : 0 ≤ ∫ x in Ω, (P_x x + Q_x x) ∂volume := by
    have heq : ∫ x in Ω, (P_x x + Q_x x) ∂volume =
        ∫ x in Ω, bilinFormIntegrandOfCoeff A.1 hu hwφ2Ψ x ∂volume :=
      setIntegral_congr_fun hΩ.measurableSet (fun x _ => (hPQ x).symm)
    rw [heq]; exact htest
  -- Define the key quantities as real numbers.
  let absP : ℝ := ∫ x in Ω, φ x ^ 2 * (-deriv Ψ (u x)) *
    bilinFormIntegrandOfCoeff A.1 hu hu x ∂volume
  let C : ℝ := ∫ x in Ω, φ x * Ψ (u x) * AuDφ x ∂volume
  let R : ℝ := ∫ x in Ω, ‖fderiv ℝ φ x‖ ^ 2 *
    (if deriv Ψ (u x) = 0 then 0 else Ψ (u x) ^ 2 / (-deriv Ψ (u x))) ∂volume
  -- (a) |P| ≥ 0 (integrand is nonneg: φ²·(-Ψ')·⟨A∇u,∇u⟩ ≥ 0)
  have habsP_nonneg : 0 ≤ absP := by
    dsimp [absP]
    -- Use setIntegral_nonneg with pointwise bound (need coercivity pointwise on Ω)
    -- The a.e. coercivity suffices since we can use ae_restrict.
    rw [show (∫ x in Ω, φ x ^ 2 * -deriv Ψ (u x) * bilinFormIntegrandOfCoeff A.1 hu hu x ∂volume)
      = ∫ x, φ x ^ 2 * -deriv Ψ (u x) * bilinFormIntegrandOfCoeff A.1 hu hu x
          ∂(volume.restrict Ω) from rfl]
    apply integral_nonneg_of_ae
    filter_upwards [A.1.ae_coercive_nonneg, ae_restrict_mem hΩ.measurableSet] with x hcoer hx
    apply mul_nonneg
    · exact mul_nonneg (sq_nonneg _) (neg_nonneg.mpr (hΨ'_nonpos x hx))
    · rw [bilinFormIntegrandOfCoeff, real_inner_comm]; exact hcoer (hu.weakGrad x)
  obtain ⟨M, hM⟩ := hΨ_bdd
  have hP_int : Integrable P_x (volume.restrict Ω) := by
    -- P_x = (φ²·Ψ'(u)) · bilinForm. Use integrable_bounded_mul_bilinFormIntegrand.
    have hfbound : ∀ x, |φ x ^ 2 * deriv Ψ (u x)| ≤ M := by
      intro x
      rw [abs_mul]
      calc |φ x ^ 2| * |deriv Ψ (u x)|
          ≤ 1 * M := by
            exact mul_le_mul
              (by rw [abs_of_nonneg (sq_nonneg _)]; exact (sq_le_one_iff_abs_le_one _).mpr (hφ_bound x))
              (hM (u x)) (abs_nonneg _) zero_le_one
        _ = M := one_mul M
    have hfmeas : AEStronglyMeasurable (fun x => φ x ^ 2 * deriv Ψ (u x))
        (volume.restrict Ω) :=
      (hφ.continuous.pow 2).aestronglyMeasurable.mul
        ((hΨ.continuous_deriv (by simp)).comp_aestronglyMeasurable
          hu.memLp.aestronglyMeasurable)
    simpa [P_x] using
      (integrable_bounded_mul_bilinFormIntegrand A.1 hu hfmeas hfbound)
  have hPQ_integrable : Integrable (fun x => P_x x + Q_x x) (volume.restrict Ω) := by
    have := integrable_bilinFormIntegrandOfCoeff A.1 hu hwφ2Ψ
    exact this.congr (ae_of_all _ fun x => hPQ x)
  have hQ_int : Integrable Q_x (volume.restrict Ω) := by
    exact (hPQ_integrable.sub hP_int).congr (ae_of_all _ fun x => by dsimp; ring)
  have hcross_int : Integrable (fun x => φ x * Ψ (u x) * AuDφ x) (volume.restrict Ω) := by
    refine (hQ_int.const_mul (1 / 2 : ℝ)).congr ?_
    exact ae_of_all _ fun x => by
      dsimp [Q_x, AuDφ]
      ring
  -- (b) From 0 ≤ ∫(P+Q): since P_x + Q_x = φ²Ψ'⟨A∇u,∇u⟩ + 2φΨ·AuDφ
  --   = -(φ²(-Ψ')⟨A∇u,∇u⟩) + 2(φΨ·AuDφ) = -absP_integrand + 2C_integrand
  -- So ∫(P+Q) = -absP + 2C. Combined with 0 ≤ ∫(P+Q): absP ≤ 2C.
  have habsP_le_2C : absP ≤ 2 * C := by
    -- Now split: ∫(P+Q) = ∫P + ∫Q
    have hsplit : ∫ x in Ω, (P_x x + Q_x x) ∂volume =
        ∫ x in Ω, P_x x ∂volume + ∫ x in Ω, Q_x x ∂volume :=
      integral_add hP_int hQ_int
    -- absP = -∫P and 2C = ∫Q
    have hP_neg : ∫ x in Ω, P_x x ∂volume = -absP := by
      dsimp [absP, P_x]
      rw [← integral_neg]; congr 1; ext x; ring
    have hQ_2C : ∫ x in Ω, Q_x x ∂volume = 2 * C := by
      dsimp [C, Q_x]
      rw [← integral_const_mul]; congr 1; ext x; ring
    linarith [hPQ_int, hsplit, hP_neg, hQ_2C]
  have hR_nonneg : 0 ≤ R := by
    dsimp [R]
    apply setIntegral_nonneg_ae hΩ.measurableSet
    filter_upwards with x hx
    apply mul_nonneg (sq_nonneg _)
    split_ifs with hder
    · positivity
    · exact div_nonneg (sq_nonneg _) (neg_nonneg.mpr (hΨ'_nonpos x hx))
  -- (c) Integral CS: C² ≤ Λ · absP · R
  have hF_sq_int :
      Integrable
        (fun x => φ x ^ 2 * (-deriv Ψ (u x)) *
          bilinFormIntegrandOfCoeff A.1 hu hu x)
        (volume.restrict Ω) := by
    refine hP_int.neg.congr ?_
    exact ae_of_all _ fun x => by
      dsimp [P_x]
      ring
  let μ : Measure E := volume.restrict Ω
  let F : E → ℝ := fun x =>
    Real.sqrt (φ x ^ 2 * (-deriv Ψ (u x)) *
      bilinFormIntegrandOfCoeff A.1 hu hu x)
  let G : E → ℝ := fun x =>
    Real.sqrt (A.1.Λ * (‖fderiv ℝ φ x‖ ^ 2 *
      (if deriv Ψ (u x) = 0 then 0
       else Ψ (u x) ^ 2 / (-deriv Ψ (u x)))))
  have hF_arg_nonneg :
      ∀ᵐ x ∂μ, 0 ≤ φ x ^ 2 * (-deriv Ψ (u x)) *
        bilinFormIntegrandOfCoeff A.1 hu hu x := by
    filter_upwards [A.1.ae_coercive_nonneg, ae_restrict_mem hΩ.measurableSet] with x hcoer hx
    apply mul_nonneg
    · exact mul_nonneg (sq_nonneg _) (neg_nonneg.mpr (hΨ'_nonpos x hx))
    · rw [bilinFormIntegrandOfCoeff, real_inner_comm]
      exact hcoer (hu.weakGrad x)
  have hF_sq_eq :
      (fun x => F x ^ 2) =ᵐ[μ]
        (fun x => φ x ^ 2 * (-deriv Ψ (u x)) *
          bilinFormIntegrandOfCoeff A.1 hu hu x) := by
    filter_upwards [hF_arg_nonneg] with x hx
    dsimp [F]
    rw [Real.sq_sqrt hx]
  have hG_sq_int :
      Integrable
        (fun x => A.1.Λ * (‖fderiv ℝ φ x‖ ^ 2 *
          (if deriv Ψ (u x) = 0 then 0
           else Ψ (u x) ^ 2 / (-deriv Ψ (u x)))))
        μ := by
    simpa [μ] using hratio_int.const_mul A.1.Λ
  have hG_arg_nonneg :
      ∀ᵐ x ∂μ, 0 ≤ A.1.Λ * (‖fderiv ℝ φ x‖ ^ 2 *
        (if deriv Ψ (u x) = 0 then 0
         else Ψ (u x) ^ 2 / (-deriv Ψ (u x)))) := by
    filter_upwards [ae_restrict_mem hΩ.measurableSet] with x hx
    apply mul_nonneg A.1.Λ_nonneg
    apply mul_nonneg (sq_nonneg _)
    split_ifs with hder
    · positivity
    · exact div_nonneg (sq_nonneg _) (neg_nonneg.mpr (hΨ'_nonpos x hx))
  have hG_sq_eq :
      (fun x => G x ^ 2) =ᵐ[μ]
        (fun x => A.1.Λ * (‖fderiv ℝ φ x‖ ^ 2 *
          (if deriv Ψ (u x) = 0 then 0
           else Ψ (u x) ^ 2 / (-deriv Ψ (u x))))) := by
    filter_upwards [hG_arg_nonneg] with x hx
    dsimp [G]
    rw [Real.sq_sqrt hx]
  have hF_meas : AEStronglyMeasurable F μ := by
    exact (hF_sq_int.aestronglyMeasurable.aemeasurable.sqrt).aestronglyMeasurable
  have hG_meas : AEStronglyMeasurable G μ := by
    exact (hG_sq_int.aestronglyMeasurable.aemeasurable.sqrt).aestronglyMeasurable
  have hF_memLp : MemLp F 2 μ := by
    refine (MeasureTheory.memLp_two_iff_integrable_sq hF_meas).2 ?_
    exact hF_sq_int.congr hF_sq_eq.symm
  have hG_memLp : MemLp G 2 μ := by
    refine (MeasureTheory.memLp_two_iff_integrable_sq hG_meas).2 ?_
    exact hG_sq_int.congr hG_sq_eq.symm
  have hFG_int : Integrable (fun x => F x * G x) μ := by
    rw [← memLp_one_iff_integrable]
    have hmem : MemLp (fun x => ‖F x‖ * ‖G x‖) 1 μ := by
      simpa [mul_comm] using (hF_memLp.norm.mul hG_memLp.norm)
    simpa [F, G, Real.norm_of_nonneg (Real.sqrt_nonneg _)] using hmem
  have hcross_bound :
      ∀ᵐ x ∂μ, |φ x * Ψ (u x) * AuDφ x| ≤ F x * G x := by
    filter_upwards [A.1.mulVec_sq_le, A.1.ae_coercive_nonneg,
      ae_restrict_mem hΩ.measurableSet] with x hmul hcoer hx
    have hbilin_nonneg : 0 ≤ bilinFormIntegrandOfCoeff A.1 hu hu x := by
      rw [bilinFormIntegrandOfCoeff, real_inner_comm]
      exact hcoer (hu.weakGrad x)
    have hder_nonpos : deriv Ψ (u x) ≤ 0 := hΨ'_nonpos x hx
    by_cases hder : deriv Ψ (u x) = 0
    · have hΨx : Ψ (u x) = 0 := hΨ_zero_of_deriv_zero x hx hder
      simp [F, G, hder, hΨx]
    · have hder_lt : deriv Ψ (u x) < 0 := by
        exact lt_of_le_of_ne hder_nonpos (by simpa using hder)
      have hneg : 0 < -deriv Ψ (u x) := by linarith
      have hAu_abs :
          |AuDφ x| ≤ ‖matMulE (A.1.a x) (hu.weakGrad x)‖ * ‖fderiv ℝ φ x‖ := by
        calc
          |AuDφ x|
              ≤ ‖matMulE (A.1.a x) (hu.weakGrad x)‖ *
                  ‖WithLp.toLp 2
                    (fun i => (fderiv ℝ φ x) (EuclideanSpace.single i 1))‖ := by
                dsimp [AuDφ]
                exact abs_real_inner_le_norm _ _
          _ = ‖matMulE (A.1.a x) (hu.weakGrad x)‖ * ‖fderiv ℝ φ x‖ := by
                rw [super_norm_fderiv_eq_norm_partials]
      have hAu_sq :
          |AuDφ x| ^ 2 ≤
            A.1.Λ * bilinFormIntegrandOfCoeff A.1 hu hu x * ‖fderiv ℝ φ x‖ ^ 2 := by
        have hsq₁ :
            |AuDφ x| ^ 2 ≤
              (‖matMulE (A.1.a x) (hu.weakGrad x)‖ * ‖fderiv ℝ φ x‖) ^ 2 := by
          exact sq_le_sq.mpr <| by
            simpa [abs_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))] using hAu_abs
        have hmul_sq :
            ‖matMulE (A.1.a x) (hu.weakGrad x)‖ ^ 2 ≤
              A.1.Λ * bilinFormIntegrandOfCoeff A.1 hu hu x := by
          simpa [bilinFormIntegrandOfCoeff, real_inner_comm] using hmul (hu.weakGrad x)
        calc
          |AuDφ x| ^ 2 ≤
              (‖matMulE (A.1.a x) (hu.weakGrad x)‖ * ‖fderiv ℝ φ x‖) ^ 2 := hsq₁
          _ = ‖matMulE (A.1.a x) (hu.weakGrad x)‖ ^ 2 * ‖fderiv ℝ φ x‖ ^ 2 := by
                ring
          _ ≤
              (A.1.Λ * bilinFormIntegrandOfCoeff A.1 hu hu x) * ‖fderiv ℝ φ x‖ ^ 2 := by
                exact mul_le_mul_of_nonneg_right hmul_sq (sq_nonneg _)
          _ = A.1.Λ * bilinFormIntegrandOfCoeff A.1 hu hu x * ‖fderiv ℝ φ x‖ ^ 2 := by
                ring
      have hFarg_nonneg :
          0 ≤ φ x ^ 2 * (-deriv Ψ (u x)) *
            bilinFormIntegrandOfCoeff A.1 hu hu x := by
        apply mul_nonneg
        · exact mul_nonneg (sq_nonneg _) hneg.le
        · exact hbilin_nonneg
      have hGarg_nonneg :
          0 ≤ A.1.Λ * (‖fderiv ℝ φ x‖ ^ 2 *
            (if deriv Ψ (u x) = 0 then 0
             else Ψ (u x) ^ 2 / (-deriv Ψ (u x)))) := by
        apply mul_nonneg A.1.Λ_nonneg
        apply mul_nonneg (sq_nonneg _)
        simp [hder, div_nonneg (sq_nonneg _) hneg.le]
      have hcross_sq :
          |φ x * Ψ (u x) * AuDφ x| ^ 2 ≤
            (φ x ^ 2 * (-deriv Ψ (u x)) *
              bilinFormIntegrandOfCoeff A.1 hu hu x) *
            (A.1.Λ * (‖fderiv ℝ φ x‖ ^ 2 *
              (if deriv Ψ (u x) = 0 then 0
               else Ψ (u x) ^ 2 / (-deriv Ψ (u x))))) := by
        calc
          |φ x * Ψ (u x) * AuDφ x| ^ 2
              = φ x ^ 2 * Ψ (u x) ^ 2 * |AuDφ x| ^ 2 := by
                  rw [abs_mul, abs_mul]
                  calc
                    (|φ x| * |Ψ (u x)| * |AuDφ x|) ^ 2
                        = |φ x| ^ 2 * |Ψ (u x)| ^ 2 * |AuDφ x| ^ 2 := by ring
                    _ = φ x ^ 2 * Ψ (u x) ^ 2 * |AuDφ x| ^ 2 := by
                        rw [sq_abs, sq_abs]
          _ ≤
              φ x ^ 2 * Ψ (u x) ^ 2 *
                (A.1.Λ * bilinFormIntegrandOfCoeff A.1 hu hu x *
                  ‖fderiv ℝ φ x‖ ^ 2) := by
                  exact mul_le_mul_of_nonneg_left hAu_sq
                    (mul_nonneg (sq_nonneg _) (sq_nonneg _))
          _ =
              (φ x ^ 2 * (-deriv Ψ (u x)) *
                bilinFormIntegrandOfCoeff A.1 hu hu x) *
              (A.1.Λ * (‖fderiv ℝ φ x‖ ^ 2 *
                (if deriv Ψ (u x) = 0 then 0
                 else Ψ (u x) ^ 2 / (-deriv Ψ (u x))))) := by
                  simp [hder]
                  field_simp [hneg.ne']
      exact (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).1 <|
        calc
          |φ x * Ψ (u x) * AuDφ x| ^ 2
              ≤
                (φ x ^ 2 * (-deriv Ψ (u x)) *
                  bilinFormIntegrandOfCoeff A.1 hu hu x) *
                (A.1.Λ * (‖fderiv ℝ φ x‖ ^ 2 *
                  (if deriv Ψ (u x) = 0 then 0
                   else Ψ (u x) ^ 2 / (-deriv Ψ (u x))))) := hcross_sq
          _ = (F x * G x) ^ 2 := by
                dsimp [F, G]
                rw [mul_pow, Real.sq_sqrt hFarg_nonneg, Real.sq_sqrt hGarg_nonneg]
  have habs_le :
      |C| ≤ ∫ x, F x * G x ∂μ := by
    calc
      |C| = |∫ x, φ x * Ψ (u x) * AuDφ x ∂μ| := by
              rfl
      _ = ‖∫ x, φ x * Ψ (u x) * AuDφ x ∂μ‖ := by
              rw [Real.norm_eq_abs]
      _ ≤ ∫ x, ‖φ x * Ψ (u x) * AuDφ x‖ ∂μ := norm_integral_le_integral_norm _
      _ = ∫ x, |φ x * Ψ (u x) * AuDφ x| ∂μ := by
              apply integral_congr_ae
              filter_upwards with x
              rw [Real.norm_eq_abs]
      _ ≤ ∫ x, F x * G x ∂μ := integral_mono_ae hcross_int.norm hFG_int hcross_bound
  have hF_memLp' : MemLp F (ENNReal.ofReal 2) μ := by
    simpa using hF_memLp
  have hG_memLp' : MemLp G (ENNReal.ofReal 2) μ := by
    simpa using hG_memLp
  have hholder :
      ∫ x, F x * G x ∂μ ≤
        (∫ x, F x ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) *
          (∫ x, G x ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) := by
    simpa [F, G, Real.norm_of_nonneg (Real.sqrt_nonneg _)] using
      integral_mul_norm_le_Lp_mul_Lq (μ := μ) (f := F) (g := G)
        Real.HolderConjugate.two_two hF_memLp' hG_memLp'
  have hF_int_eq : ∫ x, F x ^ (2 : ℝ) ∂μ = absP := by
    calc
      ∫ x, F x ^ (2 : ℝ) ∂μ = ∫ x, F x ^ (2 : ℕ) ∂μ := by
            congr 1
            ext x
            rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      _ = ∫ x, φ x ^ 2 * (-deriv Ψ (u x)) *
            bilinFormIntegrandOfCoeff A.1 hu hu x ∂μ := by
              apply integral_congr_ae
              exact hF_sq_eq
      _ = absP := by rfl
  have hG_int_eq : ∫ x, G x ^ (2 : ℝ) ∂μ = A.1.Λ * R := by
    calc
      ∫ x, G x ^ (2 : ℝ) ∂μ = ∫ x, G x ^ (2 : ℕ) ∂μ := by
            congr 1
            ext x
            rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      _ = ∫ x, A.1.Λ * (‖fderiv ℝ φ x‖ ^ 2 *
            (if deriv Ψ (u x) = 0 then 0
             else Ψ (u x) ^ 2 / (-deriv Ψ (u x)))) ∂μ := by
              apply integral_congr_ae
              exact hG_sq_eq
      _ = A.1.Λ * R := by
            dsimp [R, μ]
            rw [integral_const_mul]
  have hC_bound :
      |C| ≤ absP ^ ((1 : ℝ) / 2) * (A.1.Λ * R) ^ ((1 : ℝ) / 2) := by
    calc
      |C| ≤ ∫ x, F x * G x ∂μ := habs_le
      _ ≤ (∫ x, F x ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) *
            (∫ x, G x ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) := hholder
      _ = absP ^ ((1 : ℝ) / 2) * (A.1.Λ * R) ^ ((1 : ℝ) / 2) := by
            rw [hF_int_eq, hG_int_eq]
  have hCS : C ^ 2 ≤ A.1.Λ * absP * R := by
    have hAR_nonneg : 0 ≤ A.1.Λ * R := mul_nonneg A.1.Λ_nonneg hR_nonneg
    have hsq :=
      super_sq_le_of_le_rpow_half_mul habsP_nonneg hAR_nonneg (abs_nonneg C) hC_bound
    simpa [sq_abs, mul_assoc, mul_left_comm, mul_comm] using hsq
  -- Since `R` is defined using `‖∇φ‖²`, the upper ellipticity bound
  -- `⟨A∇φ, ∇φ⟩ ≤ Λ ‖∇φ‖²` contributes the factor `Λ` in the final estimate.
  show absP ≤ 4 * A.1.Λ * R
  by_cases habsP_zero : absP = 0
  · rw [habsP_zero]
    apply mul_nonneg (mul_nonneg (by positivity) A.1.Λ_nonneg)
    exact hR_nonneg
  · have habsP_pos : 0 < absP := lt_of_le_of_ne habsP_nonneg (Ne.symm habsP_zero)
    have h1 : absP ^ 2 ≤ (2 * C) ^ 2 := sq_le_sq' (by linarith) habsP_le_2C
    have h2 : (2 * C) ^ 2 = 4 * C ^ 2 := by ring
    nlinarith [h1, h2, hCS, habsP_pos, A.1.Λ_nonneg, hR_nonneg]

end DeGiorgi
