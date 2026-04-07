import DeGiorgi.Supersolutions.RegularizationSupport
import DeGiorgi.Supersolutions.Caccioppoli

/-!
# Supersolutions Inverse Energy

This module contains the inverse-power energy estimates for regularized
cutoffs, culminating in the core inverse energy bound.
-/

noncomputable section

open MeasureTheory Metric

namespace DeGiorgi

variable {d : ℕ} [NeZero d]

local notation "E" => AmbientSpace d
local notation "μhalf" => (volume.restrict (Metric.ball (0 : E) (1 / 2 : ℝ)))

set_option maxHeartbeats 1000000

/-- Regularized energy bound: for each `ε > 0`, the exact shifted-power cutoff
`η · (ε + u)^{-p/2}` lies in `W₀^{1,2}(B_s)` with the expected Caccioppoli
energy estimate. -/

theorem superPowerCutoff_energy_bound_reg
    (_hd : 2 < (d : ℝ))
    (A : NormalizedEllipticCoeff d (Metric.ball (0 : E) 1))
    {u η : E → ℝ} {p s Cη ε : ℝ}
    (hp : 0 < p)
    (hε : 0 < ε)
    (hs : 0 < s) (hs1 : s ≤ 1)
    (hu_pos : ∀ x ∈ Metric.ball (0 : E) 1, 0 < u x)
    (hsuper : IsSupersolution A.1 u)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hη_bound : ∀ x, |η x| ≤ 1)
    (hη_grad_bound : ∀ x, ‖fderiv ℝ η x‖ ≤ Cη)
    (hη_sub_ball : tsupport η ⊆ Metric.ball (0 : E) s) :
    ∃ hwv : MemW1pWitness 2
        (superExactPowerCutoff η u ε (-(p / 2))) (Metric.ball (0 : E) s),
      MemW01p 2 (superExactPowerCutoff η u ε (-(p / 2))) (Metric.ball (0 : E) s) ∧
      ∫ x in Metric.ball (0 : E) s, ‖hwv.weakGrad x‖ ^ 2 ∂volume ≤
        2 * Cη ^ 2 * (A.1.Λ * (p / (1 + p)) ^ 2 + 1) *
          ∫ x in Metric.ball (0 : E) s,
            superExactShiftPow ε (-p) (u x) ∂volume := by
  let Ω : Set E := Metric.ball (0 : E) s
  let Ω1 : Set E := Metric.ball (0 : E) 1
  let μ : Measure E := volume.restrict Ω
  let hu1 : MemW1pWitness 2 u Ω1 := DeGiorgi.MemW1p.someWitness hsuper.1
  let hu : MemW1pWitness 2 u Ω :=
    hu1.restrict Metric.isOpen_ball (Metric.ball_subset_ball hs1)
  have ha_pow : -(p / 2) < 1 := by linarith
  have ha_test : -(1 + p) < 1 := by linarith
  let hwvBig : MemW1pWitness 2 (superExactPowerCutoff η u ε (-(p / 2))) Ω1 :=
    superExactPowerCutoffWitness (d := d) (u := u) (η := η) (ε := ε) (a := -(p / 2))
      (s := s) (Cη := Cη) hε ha_pow hu1 hη hη_bound hη_grad_bound hη_sub_ball
  let hwv : MemW1pWitness 2 (superExactPowerCutoff η u ε (-(p / 2))) Ω :=
    hwvBig.restrict Metric.isOpen_ball (Metric.ball_subset_ball hs1)
  have hvW01 :
      MemW01p 2 (superExactPowerCutoff η u ε (-(p / 2))) Ω := by
    simpa [Ω] using
      superExactPowerCutoff_memW01_on_ball (d := d) (u := u) (η := η) (ε := ε)
        (a := -(p / 2)) (s := s) (Cη := Cη) hs hs1 hε ha_pow hu1 hη
        hη_bound hη_grad_bound hη_sub_ball
  let hwφ : MemW1pWitness 2 (superExactTestCutoff η u ε (-(1 + p))) Ω1 :=
    superExactTestCutoffWitness (d := d) (u := u) (η := η) (ε := ε) (a := -(1 + p))
      (s := s) (Cη := Cη) hε ha_test hu1 hη hη_bound hη_grad_bound hη_sub_ball
  have hφ0 : MemH01 (superExactTestCutoff η u ε (-(1 + p))) Ω1 := by
    simpa [Ω1] using
      superExactTestCutoff_memH01_on_unitBall (d := d) (u := u) (η := η) (ε := ε)
        (a := -(1 + p)) (s := s) (Cη := Cη) hs1 hε ha_test hu1 hη
        hη_bound hη_grad_bound hη_sub_ball
  have hsuper_test :
      0 ≤ bilinFormOfCoeff A.1 hu1 hwφ := by
    exact hsuper.2 hu1 _ hφ0 hwφ
      (superExactInv_testCutoff_nonneg_global (u := u) (η := η) (ε := ε) (p := p)
        (s := s) hε hs1 hu_pos hη_sub_ball)
  have hCη_nonneg : 0 ≤ Cη := by
    exact le_trans (norm_nonneg _) (hη_grad_bound (0 : E))
  have hΩ_sub_Ω1 : Ω ⊆ Ω1 := Metric.ball_subset_ball hs1
  let ψ : E → ℝ := fun x => superExactShiftPow ε (-(1 + p)) (u x)
  let ψd : E → ℝ := fun x => -(deriv (superExactShiftReg ε (-(1 + p))) (u x))
  let Equad : E → ℝ := bilinFormIntegrandOfCoeff A.1 hu1 hu1
  let gradEtaNorm : E → ℝ := fun x => ‖fderiv ℝ η x‖
  let fluxNorm : E → ℝ := fun x => ‖matMulE (A.1.a x) (hu1.weakGrad x)‖
  let leftTerm : E → ℝ := fun x => η x ^ 2 * ψd x * Equad x
  let boundTerm : E → ℝ := fun x =>
    gradEtaNorm x ^ 2 * (|ψ x| ^ 2 / ψd x)
  let crossInner : E → ℝ := fun x =>
    (2 * η x * ψ x) *
      inner ℝ (matMulE (A.1.a x) (hu1.weakGrad x)) (superFderivVec η x)
  let crossAbs : E → ℝ := fun x =>
    2 * |η x| * |ψ x| * gradEtaNorm x * |fluxNorm x|
  let termAfun : E → ℝ := fun x =>
    η x ^ 2 *
      (deriv (superExactShiftReg ε (-(p / 2))) (u x)) ^ 2 *
      ‖hu1.weakGrad x‖ ^ 2
  let termBfun : E → ℝ := fun x =>
    ‖fderiv ℝ η x‖ ^ 2 *
      (superExactShiftPow ε (-(p / 2)) (u x)) ^ 2
  let coreIntegrand : E → ℝ := fun x => -leftTerm x + crossInner x
  have hψ_aemeas : AEMeasurable ψ μ := by
    exact superExactShiftPow_comp_aemeasurable (Ω := Ω) (u := u) (ε := ε)
      (a := -(1 + p)) hε hu
  have hψd_aemeas : AEMeasurable ψd μ := by
    have h1 : ContDiff ℝ 1 (superExactShiftReg ε (-(1 + p))) :=
      (superExactShiftReg_contDiff (ε := ε) (a := -(1 + p)) hε).of_le (by simp)
    exact (h1.continuous_deriv_one.measurable.comp_aemeasurable
      hu.memLp.aestronglyMeasurable.aemeasurable).neg
  have hgradEtaNorm_aemeas : AEMeasurable gradEtaNorm μ := by
    exact (hη.continuous_fderiv (by simp : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0)).norm.aemeasurable
  have hfluxNorm_aemeas : AEMeasurable fluxNorm μ := by
    exact
      (((super_aestronglyMeasurable_matMulE A.1 hu1.weakGrad_memLp.aestronglyMeasurable).mono_measure
        (Measure.restrict_mono_set volume hΩ_sub_Ω1)).norm.aemeasurable)
  have hcore_eq :
      ∀ x, coreIntegrand x = bilinFormIntegrandOfCoeff A.1 hu1 hwφ x := by
    intro x
    simpa [coreIntegrand, leftTerm, ψd, Equad, crossInner, ψ, hwφ]
      using
        (superExactTestCutoff_core_eq (d := d) (A := A) (u := u) (η := η) (ε := ε)
          (a := -(1 + p)) (Cη := Cη) hε ha_test hu1 hη hη_bound
          hη_grad_bound ((show tsupport η ⊆ Metric.ball (0 : E) 1 from hη_sub_ball.trans hΩ_sub_Ω1))
          hu_pos x)
  have hcore_zero_outside :
      ∀ x, x ∉ Ω → coreIntegrand x = 0 := by
    intro x hx
    have hxt : x ∉ tsupport η := fun hxη => hx (hη_sub_ball hxη)
    have hηx : η x = 0 := image_eq_zero_of_notMem_tsupport hxt
    have hfd_zero : fderiv ℝ η x = 0 := by
      exact norm_eq_zero.mp <| by
        simpa [gradEtaNorm] using
          super_fderiv_norm_zero_outside_tsupport (d := d) (f := η) hη hxt
    have hfdv_zero : superFderivVec η x = 0 := by
      apply PiLp.ext
      intro i
      simp [superFderivVec_apply, hfd_zero]
    simp [coreIntegrand, leftTerm, crossInner, hηx, hfdv_zero]
  have hindicator :
      Set.indicator Ω1 coreIntegrand = Set.indicator Ω coreIntegrand := by
    ext x
    by_cases hx : x ∈ Ω
    · have hx1 : x ∈ Ω1 := hΩ_sub_Ω1 hx
      simp [hx, hx1]
    · by_cases hx1 : x ∈ Ω1
      · simp [hx, hx1, hcore_zero_outside x hx]
      · simp [hx, hx1]
  have hcore_integral_eq :
      ∫ x in Ω1, coreIntegrand x ∂volume = ∫ x in Ω, coreIntegrand x ∂volume := by
    rw [← integral_indicator Metric.isOpen_ball.measurableSet,
      hindicator, integral_indicator Metric.isOpen_ball.measurableSet]
  have hcore_int_big :
      Integrable (bilinFormIntegrandOfCoeff A.1 hu1 hwφ) (volume.restrict Ω1) :=
    integrable_bilinFormIntegrandOfCoeff A.1 hu1 hwφ
  have hcore_int :
      Integrable coreIntegrand μ := by
    exact (hcore_int_big.mono_measure (Measure.restrict_mono_set volume hΩ_sub_Ω1)).congr
      (ae_of_all _ fun x => (hcore_eq x).symm)
  have hweighted_grad_sq_int :
      Integrable (fun x => η x ^ 2 * ‖hu1.weakGrad x‖ ^ 2) μ := by
    have hbase : Integrable (fun x => ‖hu1.weakGrad x‖ ^ 2) μ := by
      simpa [μ, hu, MemW1pWitness.restrict] using hu.weakGrad_norm_memLp.integrable_sq
    refine Integrable.mono' hbase ?_ ?_
    · exact
        (((hη.continuous.pow 2).aemeasurable).mul hbase.aestronglyMeasurable.aemeasurable).aestronglyMeasurable
    · filter_upwards with x
      have hη_sq_le : η x ^ 2 ≤ 1 := by
        have hη_sq_le' : η x ^ 2 ≤ (1 : ℝ) ^ 2 := by
          exact sq_le_sq.mpr (by simpa using hη_bound x)
        simpa using hη_sq_le'
      have hgrad_nonneg : 0 ≤ ‖hu1.weakGrad x‖ ^ 2 := by positivity
      have hterm_nonneg : 0 ≤ η x ^ 2 * ‖hu1.weakGrad x‖ ^ 2 := by positivity
      have hle :
          η x ^ 2 * ‖hu1.weakGrad x‖ ^ 2 ≤ ‖hu1.weakGrad x‖ ^ 2 := by
        simpa [one_mul] using mul_le_mul_of_nonneg_right hη_sq_le hgrad_nonneg
      simpa [Real.norm_eq_abs, abs_of_nonneg hterm_nonneg] using hle
  obtain ⟨Mψd, hMψd⟩ :=
    superExactShiftReg_deriv_bounded (ε := ε) (a := -(1 + p)) hε (by linarith)
  let Kψd : ℝ := max 1 (|Mψd|)
  have hKψd_nonneg : 0 ≤ Kψd := by
    exact le_trans zero_le_one (le_max_left _ _)
  have hbound_aemeas :
      AEMeasurable boundTerm μ := by
    exact
      ((hgradEtaNorm_aemeas.pow aemeasurable_const).mul
        ((hψ_aemeas.norm.pow aemeasurable_const).div hψd_aemeas))
  have hbound_int :
      Integrable boundTerm μ := by
    have hpow_int :
        IntegrableOn (fun x => superExactShiftPow ε (-p) (u x)) Ω volume :=
      superExactInv_shiftPow_integrableOn_ball (u := u) (ε := ε) (p := p) (s := s)
        hε (by linarith) hs hu
    refine Integrable.mono' (hpow_int.const_mul (Cη ^ 2 / (1 + p))) hbound_aemeas.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx
    have hux : 0 < u x := hu_pos x (hΩ_sub_Ω1 hx)
    have hlhs_nonneg :
        0 ≤ boundTerm x := by
      have hψd_pos :
          0 < ψd x := by
        dsimp [ψd]
        exact superExactInv_test_deriv_neg_pos (ε := ε) (p := p) (t := u x) hε hp hux
      dsimp [boundTerm, gradEtaNorm, ψ, ψd]
      exact mul_nonneg (sq_nonneg _) (div_nonneg (sq_nonneg _) hψd_pos.le)
    have hrhs_nonneg :
        0 ≤ (Cη ^ 2 / (1 + p)) * superExactShiftPow ε (-p) (u x) := by
      exact mul_nonneg
        (div_nonneg (sq_nonneg _) (by linarith : 0 ≤ 1 + p))
        (superExactShiftPow_nonneg (ε := ε) (a := -p) hε)
    have hle :
        boundTerm x ≤ (Cη ^ 2 / (1 + p)) * superExactShiftPow ε (-p) (u x) := by
      have hderiv_neg : deriv (superExactShiftReg ε (-(1 + p))) (u x) < 0 := by
        have hpos :=
          superExactInv_test_deriv_neg_pos (ε := ε) (p := p) (t := u x) hε hp hux
        linarith
      dsimp [boundTerm, gradEtaNorm, ψ, ψd]
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm,
        abs_of_nonneg (superExactShiftPow_nonneg (ε := ε) (a := -(1 + p)) hε),
        abs_of_neg hderiv_neg]
        using
          (superExactInv_boundTerm_pointwise (u := u) (η := η) (ε := ε) (p := p)
            (Cη := Cη) (x := x) hε hp hCη_nonneg hη_grad_bound hux)
    rw [Real.norm_of_nonneg hlhs_nonneg]
    exact hle
  have hleft_int :
      Integrable leftTerm μ := by
    have hleft_meas :
        AEStronglyMeasurable leftTerm μ := by
      exact ((((hη.continuous.pow 2).aemeasurable).mul hψd_aemeas).mul
        ((aestronglyMeasurable_bilinFormIntegrandOfCoeff A.1 hu1 hu1).mono_measure
          (Measure.restrict_mono_set volume hΩ_sub_Ω1)).aemeasurable).aestronglyMeasurable
    refine Integrable.mono' (hweighted_grad_sq_int.const_mul (A.1.Λ * Kψd)) hleft_meas ?_
    have hquad :
        ∀ᵐ x ∂μ, Equad x ≤ A.1.Λ * ‖hu1.weakGrad x‖ ^ 2 := by
      exact ae_restrict_of_ae_restrict_of_subset hΩ_sub_Ω1 <| by
        filter_upwards [A.1.quadratic_upper] with x hx
        simpa [Equad, bilinFormIntegrandOfCoeff, real_inner_comm] using hx (hu1.weakGrad x)
    have hnonneg :
        ∀ᵐ x ∂μ, 0 ≤ Equad x := by
      exact ae_restrict_of_ae_restrict_of_subset hΩ_sub_Ω1 <| by
        filter_upwards [A.1.ae_coercive_nonneg] with x hx
        simpa [Equad, bilinFormIntegrandOfCoeff, real_inner_comm] using hx (hu1.weakGrad x)
    filter_upwards [hquad, hnonneg, ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hxq hxn hx
    have hux : 0 < u x := hu_pos x (hΩ_sub_Ω1 hx)
    have hψd_nonneg : 0 ≤ ψd x := by
      dsimp [ψd]
      exact (superExactInv_test_deriv_neg_pos (ε := ε) (p := p) (t := u x) hε hp hux).le
    have hψd_le : ψd x ≤ Kψd := by
      calc
        ψd x = |ψd x| := by rw [abs_of_nonneg hψd_nonneg]
        _ = |deriv (superExactShiftReg ε (-(1 + p))) (u x)| := by
              dsimp [ψd]
              rw [abs_neg]
        _ ≤ Mψd := hMψd (u x)
        _ ≤ |Mψd| := le_abs_self _
        _ ≤ Kψd := le_max_right _ _
    have hrhs_nonneg :
        0 ≤ (A.1.Λ * Kψd) * (η x ^ 2 * ‖hu1.weakGrad x‖ ^ 2) := by
      exact mul_nonneg (mul_nonneg A.1.Λ_nonneg hKψd_nonneg) (by positivity)
    have hpoint :
        ‖leftTerm x‖ ≤ (A.1.Λ * Kψd) * (η x ^ 2 * ‖hu1.weakGrad x‖ ^ 2) := by
      calc
        ‖leftTerm x‖ = leftTerm x := by
          rw [Real.norm_of_nonneg]
          exact mul_nonneg (mul_nonneg (sq_nonneg _) hψd_nonneg) hxn
        _ = η x ^ 2 * ψd x * Equad x := by
              simp [leftTerm]
        _ ≤ η x ^ 2 * Kψd * Equad x := by
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hψd_le (sq_nonneg _)) hxn
        _ ≤ η x ^ 2 * Kψd * (A.1.Λ * ‖hu1.weakGrad x‖ ^ 2) := by
              exact mul_le_mul_of_nonneg_left hxq (mul_nonneg (sq_nonneg _) hKψd_nonneg)
        _ = (A.1.Λ * Kψd) * (η x ^ 2 * ‖hu1.weakGrad x‖ ^ 2) := by ring
    simpa [Real.norm_eq_abs, abs_of_nonneg hrhs_nonneg] using hpoint
  have hcoeff :
      ∀ᵐ x ∂μ, |fluxNorm x| ^ 2 ≤ A.1.Λ * Equad x := by
    exact ae_restrict_of_ae_restrict_of_subset hΩ_sub_Ω1 <| by
      filter_upwards [A.1.mulVec_sq_le] with x hx
      simpa [fluxNorm, Equad, bilinFormIntegrandOfCoeff, real_inner_comm] using
        hx (hu1.weakGrad x)
  have hψd_pos :
      ∀ᵐ x ∂μ, 0 < ψd x := by
    filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx
    dsimp [ψd]
    exact superExactInv_test_deriv_neg_pos (ε := ε) (p := p) (t := u x) hε hp
      (hu_pos x (hΩ_sub_Ω1 hx))
  have hcross_upper_pt :
      ∀ᵐ x ∂μ,
        crossAbs x ≤
          (1 / 2 : ℝ) * leftTerm x + 2 * A.1.Λ * boundTerm x := by
    filter_upwards [hcoeff, hψd_pos] with x hx hψx
    have hpt :=
      weighted_pointwise_core (Λ := A.1.Λ) (η := |η x|) (ζ := gradEtaNorm x)
        (ψ := ψ x) (ψd := ψd x) (Q := Equad x) (M := fluxNorm x) A.1.Λ_pos hψx hx
    have hη_sq : |η x| ^ 2 = η x ^ 2 := by
      rw [pow_two, pow_two, abs_mul_abs_self]
    have hflux_abs : |fluxNorm x| = fluxNorm x := by
      exact abs_of_nonneg (norm_nonneg _)
    simpa [crossAbs, leftTerm, boundTerm, gradEtaNorm, ψ, ψd, fluxNorm, Equad,
      hη_sq, hflux_abs, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm,
      add_assoc, add_left_comm, add_comm]
      using hpt
  have hcross_upper_int :
      Integrable (fun x => (1 / 2 : ℝ) * leftTerm x + 2 * A.1.Λ * boundTerm x) μ := by
    have htmp :
        Integrable (fun x => 2 * (A.1.Λ * boundTerm x) + (1 / 2 : ℝ) * leftTerm x) μ := by
      simpa [mul_assoc] using
        (hbound_int.const_mul (2 * A.1.Λ)).add (hleft_int.const_mul (1 / 2 : ℝ))
    simpa [mul_assoc, add_comm, add_left_comm, add_assoc] using htmp
  have hcrossAbs_int :
      Integrable crossAbs μ := by
    refine Integrable.mono' hcross_upper_int ?_ ?_
    · exact
        (by
          simpa [crossAbs, gradEtaNorm, fluxNorm, mul_assoc, mul_left_comm, mul_comm] using
            (((((hη.continuous.norm.aemeasurable).mul hψ_aemeas.norm).mul hgradEtaNorm_aemeas).mul
              hfluxNorm_aemeas.norm).const_mul (2 : ℝ)).aestronglyMeasurable)
    · filter_upwards [hcross_upper_pt] with x hx
      have hcross_nonneg : 0 ≤ crossAbs x := by
        dsimp [crossAbs, gradEtaNorm, fluxNorm]
        exact mul_nonneg
          (mul_nonneg (mul_nonneg (mul_nonneg (by positivity) (abs_nonneg _)) (abs_nonneg _))
            (norm_nonneg _))
          (abs_nonneg _)
      rw [Real.norm_of_nonneg hcross_nonneg]
      exact hx
  have hcrossInner_int :
      Integrable crossInner μ := by
    convert hcore_int.add hleft_int using 1
    ext x
    simp [coreIntegrand]
  have hcrossInner_abs_le :
      ∀ᵐ x ∂μ, |crossInner x| ≤ crossAbs x := by
    filter_upwards with x
    have hψ_nonneg : 0 ≤ ψ x := superExactShiftPow_nonneg (ε := ε) (a := -(1 + p)) hε
    have hinner :
        |inner ℝ (matMulE (A.1.a x) (hu1.weakGrad x)) (superFderivVec η x)| ≤
          fluxNorm x * gradEtaNorm x := by
      have := abs_real_inner_le_norm (matMulE (A.1.a x) (hu1.weakGrad x)) (superFderivVec η x)
      change
        |inner ℝ (matMulE (A.1.a x) (hu1.weakGrad x)) (superFderivVec η x)| ≤
          ‖matMulE (A.1.a x) (hu1.weakGrad x)‖ * ‖fderiv ℝ η x‖
      simpa [fluxNorm, gradEtaNorm, super_norm_fderivVec_eq_norm_fderiv (d := d) (η := η) (x := x),
        mul_comm] using this
    have hflux_nonneg : 0 ≤ fluxNorm x := by simp [fluxNorm]
    dsimp [crossInner, crossAbs, gradEtaNorm, fluxNorm]
    calc
      |(2 * η x * ψ x) *
          inner ℝ (matMulE (A.1.a x) (hu1.weakGrad x)) (superFderivVec η x)|
          = (2 * |η x| * |ψ x|) *
            |inner ℝ (matMulE (A.1.a x) (hu1.weakGrad x)) (superFderivVec η x)| := by
              rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hψ_nonneg]
              ring
      _ ≤ (2 * |η x| * |ψ x|) * (fluxNorm x * gradEtaNorm x) := by
            exact mul_le_mul_of_nonneg_left hinner (by positivity)
      _ = 2 * |η x| * |ψ x| * gradEtaNorm x * |fluxNorm x| := by
            rw [abs_of_nonneg hψ_nonneg, abs_of_nonneg hflux_nonneg]
            ring
  have hcrossInner_le :
      ∀ᵐ x ∂μ, crossInner x ≤ crossAbs x := by
    filter_upwards [hcrossInner_abs_le] with x hx
    exact (abs_le.mp hx).2
  have hcore_nonneg :
      0 ≤ ∫ x in Ω, coreIntegrand x ∂volume := by
    have hbilin_eq :
        bilinFormOfCoeff A.1 hu1 hwφ = ∫ x in Ω, coreIntegrand x ∂volume := by
      unfold bilinFormOfCoeff
      calc
        ∫ x in Ω1, bilinFormIntegrandOfCoeff A.1 hu1 hwφ x ∂volume
            = ∫ x in Ω1, coreIntegrand x ∂volume := by
                exact setIntegral_congr_fun Metric.isOpen_ball.measurableSet fun x _ => (hcore_eq x).symm
        _ = ∫ x in Ω, coreIntegrand x ∂volume := hcore_integral_eq
    rw [← hbilin_eq]
    exact hsuper_test
  have hcore_split :
      ∫ x in Ω, coreIntegrand x ∂volume =
        -∫ x in Ω, leftTerm x ∂volume + ∫ x in Ω, crossInner x ∂volume := by
    change ∫ x, coreIntegrand x ∂μ = -∫ x, leftTerm x ∂μ + ∫ x, crossInner x ∂μ
    rw [show coreIntegrand = fun x => -leftTerm x + crossInner x by
          funext x
          simp [coreIntegrand]]
    change ∫ x, (-leftTerm x + crossInner x) ∂μ = -∫ x, leftTerm x ∂μ + ∫ x, crossInner x ∂μ
    calc
      ∫ x, (-leftTerm x + crossInner x) ∂μ
          = ∫ x, -leftTerm x ∂μ + ∫ x, crossInner x ∂μ := by
              simpa using integral_add hleft_int.neg hcrossInner_int
      _ = -∫ x, leftTerm x ∂μ + ∫ x, crossInner x ∂μ := by
            rw [integral_neg]
  have hleft_le_cross :
      ∫ x in Ω, leftTerm x ∂volume ≤ ∫ x in Ω, crossAbs x ∂volume := by
    have hcrossInner_le_int :
        ∫ x in Ω, crossInner x ∂volume ≤ ∫ x in Ω, crossAbs x ∂volume := by
      exact integral_mono_ae hcrossInner_int hcrossAbs_int hcrossInner_le
    linarith [hcore_nonneg, hcore_split, hcrossInner_le_int]
  have hleft_bound :
      ∫ x in Ω, leftTerm x ∂volume ≤ 4 * A.1.Λ * ∫ x in Ω, boundTerm x ∂volume := by
    exact weighted_absorb (μ := μ) (Quad := Equad) (M := fluxNorm) (η := η)
      (ζ := gradEtaNorm) (ψ := ψ) (ψd := ψd) (Λ := A.1.Λ) A.1.Λ_pos
      (by simpa [μ] using hleft_le_cross) hcoeff hψd_pos hleft_int hcrossAbs_int hbound_int
  have hTermA_pt :
      ∀ᵐ x ∂μ, termAfun x ≤ (p ^ 2 / (4 * (1 + p))) * leftTerm x := by
    have hcoer :
        ∀ᵐ x ∂μ, ‖hu1.weakGrad x‖ ^ 2 ≤ Equad x := by
      exact ae_restrict_of_ae_restrict_of_subset hΩ_sub_Ω1 <| by
        filter_upwards [A.1.coercive] with x hx
        simpa [Equad, bilinFormIntegrandOfCoeff, real_inner_comm, A.2] using hx (hu1.weakGrad x)
    filter_upwards [hcoer, ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hxcoer hx
    have hux : 0 < u x := hu_pos x (hΩ_sub_Ω1 hx)
    have hψd_nonneg : 0 ≤ ψd x := by
      dsimp [ψd]
      exact (superExactInv_test_deriv_neg_pos (ε := ε) (p := p) (t := u x) hε hp hux).le
    have hα :
        (deriv (superExactShiftReg ε (-(p / 2))) (u x)) ^ 2 =
          (p ^ 2 / (4 * (1 + p))) * ψd x := by
      dsimp [ψd]
      simpa using superExactInv_power_deriv_sq (ε := ε) (p := p) (t := u x) hε hp hux
    have hconst_nonneg : 0 ≤ p ^ 2 / (4 * (1 + p)) := by
      positivity
    have hscaled :
        η x ^ 2 * ψd x * ‖hu1.weakGrad x‖ ^ 2 ≤ leftTerm x := by
      dsimp [leftTerm]
      exact mul_le_mul_of_nonneg_left hxcoer (mul_nonneg (sq_nonneg _) hψd_nonneg)
    calc
      termAfun x
          = (p ^ 2 / (4 * (1 + p))) * (η x ^ 2 * ψd x * ‖hu1.weakGrad x‖ ^ 2) := by
              dsimp [termAfun, leftTerm]
              rw [hα]
              ring
      _ ≤ (p ^ 2 / (4 * (1 + p))) * leftTerm x := by
            exact mul_le_mul_of_nonneg_left hscaled hconst_nonneg
  have hTermA_int :
      Integrable termAfun μ := by
    refine Integrable.mono' (hleft_int.const_mul (p ^ 2 / (4 * (1 + p)))) ?_ ?_
    · have hα_aemeas :
          AEMeasurable (fun x => deriv (superExactShiftReg ε (-(p / 2))) (u x)) μ := by
        have h1 : ContDiff ℝ 1 (superExactShiftReg ε (-(p / 2))) :=
          (superExactShiftReg_contDiff (ε := ε) (a := -(p / 2)) hε).of_le (by simp)
        exact h1.continuous_deriv_one.measurable.comp_aemeasurable
          hu.memLp.aestronglyMeasurable.aemeasurable
      exact ((((hη.continuous.pow 2).aemeasurable).mul (hα_aemeas.pow aemeasurable_const)).mul
        (hu.weakGrad_memLp.aestronglyMeasurable.aemeasurable.norm.pow aemeasurable_const)).aestronglyMeasurable
    · filter_upwards [hTermA_pt] with x hx
      have hterm_nonneg : 0 ≤ termAfun x := by
        dsimp [termAfun]
        exact mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (sq_nonneg _)
      have hrhs_nonneg : 0 ≤ (p ^ 2 / (4 * (1 + p))) * leftTerm x := by
        exact le_trans hterm_nonneg hx
      simpa [Real.norm_eq_abs, abs_of_nonneg hterm_nonneg, abs_of_nonneg hrhs_nonneg] using hx
  have hbound_est :
      ∫ x in Ω, boundTerm x ∂volume ≤
        (Cη ^ 2 / (1 + p)) * ∫ x in Ω, superExactShiftPow ε (-p) (u x) ∂volume := by
    simpa [Ω, μ, boundTerm, gradEtaNorm, ψ, ψd] using
      superExactInv_boundTerm_bound_on_ball (d := d) (u := u) (η := η) (ε := ε) (p := p)
        (s := s) (Cη := Cη) hε hp hs (fun x hx => hu_pos x (hΩ_sub_Ω1 hx)) hu hη
        hCη_nonneg hη_grad_bound
  have hTermA :
      ∫ x in Ω, termAfun x ∂volume ≤
        A.1.Λ * (p / (1 + p)) ^ 2 * Cη ^ 2 *
          ∫ x in Ω, superExactShiftPow ε (-p) (u x) ∂volume := by
    have hcoreA :
        ∫ x in Ω, termAfun x ∂volume ≤
          (p ^ 2 / (4 * (1 + p))) * ∫ x, leftTerm x ∂μ := by
      have hmono :
          ∫ x, termAfun x ∂μ ≤
            ∫ x, (p ^ 2 / (4 * (1 + p))) * leftTerm x ∂μ := by
        exact integral_mono_ae hTermA_int (hleft_int.const_mul (p ^ 2 / (4 * (1 + p)))) hTermA_pt
      simpa [μ, integral_const_mul] using hmono
    calc
      ∫ x in Ω, termAfun x ∂volume
          ≤ (p ^ 2 / (4 * (1 + p))) * ∫ x, leftTerm x ∂μ := hcoreA
      _ ≤ (p ^ 2 / (4 * (1 + p))) * (4 * A.1.Λ * ∫ x, boundTerm x ∂μ) := by
            have hconst_nonneg : 0 ≤ p ^ 2 / (4 * (1 + p)) := by positivity
            exact mul_le_mul_of_nonneg_left hleft_bound hconst_nonneg
      _ ≤ (p ^ 2 / (4 * (1 + p))) *
            (4 * A.1.Λ *
              ((Cη ^ 2 / (1 + p)) * ∫ x in Ω, superExactShiftPow ε (-p) (u x) ∂volume)) := by
            have hconst_nonneg : 0 ≤ p ^ 2 / (4 * (1 + p)) := by positivity
            have hΛ_nonneg : 0 ≤ 4 * A.1.Λ := by nlinarith [A.1.Λ_pos]
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hbound_est hΛ_nonneg) hconst_nonneg
      _ = A.1.Λ * (p / (1 + p)) ^ 2 * Cη ^ 2 *
            ∫ x in Ω, superExactShiftPow ε (-p) (u x) ∂volume := by
            have hp1 : 1 + p ≠ 0 := by linarith
            field_simp [hp1]
  have hTermB_int :
      Integrable termBfun μ := by
    have hpow_int :
        IntegrableOn (fun x => superExactShiftPow ε (-p) (u x)) Ω volume :=
      superExactInv_shiftPow_integrableOn_ball (u := u) (ε := ε) (p := p) (s := s)
        hε (by linarith) hs hu
    refine Integrable.mono' (hpow_int.const_mul (Cη ^ 2)) ?_ ?_
    · exact
        (((hη.continuous_fderiv (by simp : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0)).norm.aemeasurable.pow
          aemeasurable_const).mul
          ((superExactShiftPow_comp_aemeasurable (Ω := Ω) (u := u) (ε := ε)
            (a := -(p / 2)) hε hu).pow aemeasurable_const)).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx
      have hux : 0 < u x := hu_pos x (hΩ_sub_Ω1 hx)
      have hlhs_nonneg : 0 ≤ termBfun x := by positivity
      have hrhs_nonneg :
          0 ≤ Cη ^ 2 * superExactShiftPow ε (-p) (u x) := by
        exact mul_nonneg (sq_nonneg _) (superExactShiftPow_nonneg (ε := ε) (a := -p) hε)
      have hle :=
        superExactInv_termB_pointwise (u := u) (η := η) (ε := ε) (p := p) (Cη := Cη)
          (x := x) hε hCη_nonneg hη_grad_bound hux
      rw [Real.norm_of_nonneg hlhs_nonneg]
      change ‖fderiv ℝ η x‖ ^ 2 * (superExactShiftPow ε (-(p / 2)) (u x)) ^ 2 ≤
        Cη ^ 2 * superExactShiftPow ε (-p) (u x)
      exact hle
  have hTermB :
      ∫ x in Ω, termBfun x ∂volume ≤
        Cη ^ 2 * ∫ x in Ω, superExactShiftPow ε (-p) (u x) ∂volume := by
    simpa [Ω, termBfun] using
      superExactInv_termB_bound_on_ball (d := d) (u := u) (η := η) (ε := ε) (p := p)
        (s := s) (Cη := Cη) hε hp hs (fun x hx => hu_pos x (hΩ_sub_Ω1 hx)) hu hη
        hCη_nonneg hη_grad_bound
  have hgrad_split :
      ∫ x in Ω, ‖hwv.weakGrad x‖ ^ 2 ∂volume ≤
        2 * ∫ x in Ω, termAfun x ∂volume +
          2 * ∫ x in Ω, termBfun x ∂volume := by
    have hupper_int :
        Integrable (fun x => 2 * termAfun x + 2 * termBfun x) μ := by
      convert (hTermA_int.const_mul (2 : ℝ)).add (hTermB_int.const_mul (2 : ℝ)) using 1
    have hmono :
        ∫ x, ‖hwv.weakGrad x‖ ^ 2 ∂μ ≤
          ∫ x, 2 * termAfun x + 2 * termBfun x ∂μ := by
      refine integral_mono_ae ?_ hupper_int ?_
      · simpa [pow_two, μ] using hwv.weakGrad_norm_memLp.integrable_sq
      · filter_upwards with x
        simpa [μ, hwv, hwvBig, termAfun, termBfun, add_assoc, add_left_comm, add_comm,
          mul_assoc, MemW1pWitness.restrict] using
          (superExactPowerCutoffWitness_norm_sq_le (d := d) (u := u) (η := η) (ε := ε)
            (a := -(p / 2)) (s := s) (Cη := Cη) hε ha_pow hu1 hη hη_bound
            hη_grad_bound hη_sub_ball x)
    calc
      ∫ x in Ω, ‖hwv.weakGrad x‖ ^ 2 ∂volume = ∫ x, ‖hwv.weakGrad x‖ ^ 2 ∂μ := by
            rfl
      _ ≤ ∫ x, 2 * termAfun x + 2 * termBfun x ∂μ := hmono
      _ = 2 * ∫ x in Ω, termAfun x ∂volume +
            2 * ∫ x in Ω, termBfun x ∂volume := by
            rw [integral_add (hTermA_int.const_mul (2 : ℝ)) (hTermB_int.const_mul (2 : ℝ)),
              integral_const_mul, integral_const_mul]
  refine ⟨hwv, hvW01, ?_⟩
  have hI_nonneg :
      0 ≤ ∫ x in Ω, superExactShiftPow ε (-p) (u x) ∂volume := by
    apply setIntegral_nonneg_ae Metric.isOpen_ball.measurableSet
    filter_upwards with x hx
    exact superExactShiftPow_nonneg (ε := ε) (a := -p) hε
  calc
    ∫ x in Ω, ‖hwv.weakGrad x‖ ^ 2 ∂volume
        ≤ 2 * ∫ x in Ω, termAfun x ∂volume +
            2 * ∫ x in Ω, termBfun x ∂volume := hgrad_split
    _ ≤ 2 * (A.1.Λ * (p / (1 + p)) ^ 2 * Cη ^ 2 *
            ∫ x in Ω, superExactShiftPow ε (-p) (u x) ∂volume) +
          2 * (Cη ^ 2 * ∫ x in Ω, superExactShiftPow ε (-p) (u x) ∂volume) := by
            exact add_le_add
              (mul_le_mul_of_nonneg_left hTermA (by positivity))
              (mul_le_mul_of_nonneg_left hTermB (by positivity))
    _ = 2 * Cη ^ 2 * (A.1.Λ * (p / (1 + p)) ^ 2 + 1) *
          ∫ x in Ω, superExactShiftPow ε (-p) (u x) ∂volume := by
            ring


theorem superExactInv_energy_mainBall
    (hd : 2 < (d : ℝ))
    (A : NormalizedEllipticCoeff d (Metric.ball (0 : E) 1))
    {u η : E → ℝ} {p s Cη : ℝ}
    (hp : 0 < p)
    (hs : 0 < s) (hs1 : s ≤ 1)
    (hu_pos : ∀ x ∈ Metric.ball (0 : E) 1, 0 < u x)
    (hsuper : IsSupersolution A.1 u)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hη_bound : ∀ x, |η x| ≤ 1)
    (hη_grad_bound : ∀ x, ‖fderiv ℝ η x‖ ≤ Cη)
    (hη_sub_ball : tsupport η ⊆ Metric.ball (0 : E) s) :
    ∀ n,
      let hwvBig : MemW1pWitness 2
          (superExactPowerCutoff η u (superEpsSeq n) (-(p / 2)))
          (Metric.ball (0 : E) 1) :=
        superExactPowerCutoffWitness (d := d) (u := u) (η := η)
          (ε := superEpsSeq n) (a := -(p / 2)) (s := s) (Cη := Cη)
          (superEpsSeq_pos n) (by linarith) (hsuper.1.someWitness)
          hη hη_bound hη_grad_bound hη_sub_ball
      let hwv : MemW1pWitness 2
          (superExactPowerCutoff η u (superEpsSeq n) (-(p / 2)))
          (Metric.ball (0 : E) s) :=
        hwvBig.restrict Metric.isOpen_ball (Metric.ball_subset_ball hs1)
      ∫ x in Metric.ball (0 : E) s, ‖hwv.weakGrad x‖ ^ 2 ∂volume ≤
        2 * Cη ^ 2 * (A.1.Λ * (p / (1 + p)) ^ 2 + 1) *
          ∫ x in Metric.ball (0 : E) s,
            superExactShiftPow (superEpsSeq n) (-p) (u x) ∂volume := by
  intro n
  let Ω : Set E := Metric.ball (0 : E) s
  let μ : Measure E := volume.restrict Ω
  let hu1 : MemW1pWitness 2 u (Metric.ball (0 : E) 1) := hsuper.1.someWitness
  let hwvBig : MemW1pWitness 2
      (superExactPowerCutoff η u (superEpsSeq n) (-(p / 2)))
      (Metric.ball (0 : E) 1) :=
    superExactPowerCutoffWitness (d := d) (u := u) (η := η)
      (ε := superEpsSeq n) (a := -(p / 2)) (s := s) (Cη := Cη)
      (superEpsSeq_pos n) (by linarith) hu1 hη hη_bound hη_grad_bound hη_sub_ball
  let hwv : MemW1pWitness 2
      (superExactPowerCutoff η u (superEpsSeq n) (-(p / 2)))
      Ω :=
    hwvBig.restrict Metric.isOpen_ball (Metric.ball_subset_ball hs1)
  obtain ⟨hwvReg, -, henergyReg⟩ :=
    superPowerCutoff_energy_bound_reg (d := d) hd A
      (u := u) (η := η) (p := p) (s := s) (Cη := Cη) (ε := superEpsSeq n)
      hp (superEpsSeq_pos n) hs hs1 hu_pos hsuper hη hη_bound hη_grad_bound hη_sub_ball
  have hae_grad :
      hwvReg.weakGrad =ᵐ[μ] hwv.weakGrad := by
    simpa [μ, Ω, hwv] using
      (MemW1pWitness.ae_eq (d := d) Metric.isOpen_ball hwvReg hwv)
  have hgrad_sq_eq :
      ∫ x in Ω, ‖hwvReg.weakGrad x‖ ^ 2 ∂volume =
        ∫ x in Ω, ‖hwv.weakGrad x‖ ^ 2 ∂volume := by
    exact integral_congr_ae (hae_grad.fun_comp (fun z => ‖z‖ ^ 2))
  calc
    ∫ x in Ω, ‖hwv.weakGrad x‖ ^ 2 ∂volume
        = ∫ x in Ω, ‖hwvReg.weakGrad x‖ ^ 2 ∂volume := by
            symm
            exact hgrad_sq_eq
    _ ≤ 2 * Cη ^ 2 * (A.1.Λ * (p / (1 + p)) ^ 2 + 1) *
          ∫ x in Ω, superExactShiftPow (superEpsSeq n) (-p) (u x) ∂volume := henergyReg

set_option maxHeartbeats 1000000 in
theorem superPowerCutoff_memW1p_energy_of_supersolution_core
    (hd : 2 < (d : ℝ))
    (A : NormalizedEllipticCoeff d (Metric.ball (0 : E) 1))
    {u η : E → ℝ} {p s Cη : ℝ}
    (hp : 0 < p)
    (hs : 0 < s) (hs1 : s ≤ 1)
    (hu_pos : ∀ x ∈ Metric.ball (0 : E) 1, 0 < u x)
    (hsuper : IsSupersolution A.1 u)
    (hpInt :
      IntegrableOn (fun x => |(u x)⁻¹| ^ p)
        (Metric.ball (0 : E) s) volume)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hη_bound : ∀ x, |η x| ≤ 1)
    (hη_grad_bound : ∀ x, ‖fderiv ℝ η x‖ ≤ Cη)
    (hη_sub_ball : tsupport η ⊆ Metric.ball (0 : E) s) :
    ∃ hwv : MemW1pWitness 2 (superPowerCutoff (d := d) η u p) (Metric.ball (0 : E) s),
      ∫ x in Metric.ball (0 : E) s, ‖hwv.weakGrad x‖ ^ 2 ∂volume ≤
        2 * Cη ^ 2 * (A.1.Λ * (p / (1 + p)) ^ 2 + 1) *
          ∫ x in Metric.ball (0 : E) s, |(u x)⁻¹| ^ p ∂volume := by
  classical
  let Ω : Set E := Metric.ball (0 : E) s
  let μ : Measure E := volume.restrict Ω
  let hu1 : MemW1pWitness 2 u (Metric.ball (0 : E) 1) :=
    DeGiorgi.MemW1p.someWitness hsuper.1
  let hu : MemW1pWitness 2 u Ω :=
    hu1.restrict Metric.isOpen_ball (Metric.ball_subset_ball hs1)
  let f : E → ℝ := superPowerCutoff (d := d) η u p
  let fn : ℕ → E → ℝ :=
    fun n => superExactPowerCutoff η u (superEpsSeq n) (-(p / 2))
  have ha_pow : -(p / 2) < 1 := by linarith
  let wfnBig : ∀ n : ℕ, MemW1pWitness 2 (fun x => fn n x) (Metric.ball (0 : E) 1) := fun n => by
    dsimp [fn]
    exact
      superExactPowerCutoffWitness
        (d := d) (u := u) (η := η) (ε := superEpsSeq n) (a := -(p / 2))
        (s := s) (Cη := Cη) (superEpsSeq_pos n) ha_pow hu1 hη hη_bound hη_grad_bound
        hη_sub_ball
  let wfn : ∀ n : ℕ, MemW1pWitness 2 (fun x => fn n x) Ω := fun n =>
    (wfnBig n).restrict Metric.isOpen_ball (Metric.ball_subset_ball hs1)
  let Hhalf : E → ℝ := fun x => |(u x)⁻¹| ^ (p / 2)
  let I : ℝ := ∫ x in Ω, |(u x)⁻¹| ^ p ∂volume
  have hΩ_sub : Ω ⊆ Metric.ball (0 : E) 1 := Metric.ball_subset_ball hs1
  have hCη_nonneg : 0 ≤ Cη := by
    exact le_trans (norm_nonneg _) (hη_grad_bound (0 : E))
  have hI_nonneg : 0 ≤ I := by
    dsimp [I]
    exact integral_nonneg fun _ => Real.rpow_nonneg (abs_nonneg _) _
  have hHhalf_memLp : MemLp Hhalf 2 μ := by
    simpa [Hhalf, μ, Ω] using
      (invPower_half_memLp_of_integrableOn (Ω := Ω) (u := u) (p := p)
        (by linarith) hu (by simpa [Ω] using hpInt))
  have hf_memLp : MemLp f 2 μ := by
    refine hHhalf_memLp.of_le ?_ ?_
    · have hpow_meas : AEStronglyMeasurable Hhalf μ := hHhalf_memLp.aestronglyMeasurable
      change AEStronglyMeasurable (fun x => η x * Hhalf x) μ
      simpa using hη.continuous.aestronglyMeasurable.mul hpow_meas
    · filter_upwards with x
      calc
        ‖f x‖ = |η x| * ‖Hhalf x‖ := by
          simp [f, Hhalf, superPowerCutoff, norm_mul]
        _ ≤ 1 * ‖Hhalf x‖ := by
          exact mul_le_mul_of_nonneg_right (hη_bound x) (norm_nonneg _)
        _ = ‖Hhalf x‖ := by ring
  have hfn_tendsto_ae :
      ∀ᵐ x ∂μ, Filter.Tendsto (fun n => fn n x) Filter.atTop (nhds (f x)) := by
    filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx
    exact
      superExactPowerCutoff_tendsto_powerCutoff_of_pos (d := d) (u := u) (η := η)
        (p := p) (x := x) (hu_pos x (hΩ_sub hx))
  have hfn_fun_memLp :
      ∀ n, MemLp (fun x => fn n x - f x) 2 μ := by
    intro n
    exact (wfn n).memLp.sub hf_memLp
  have hfn_meas : ∀ n, AEStronglyMeasurable (fun x => fn n x - f x) μ := by
    intro n
    exact (hfn_fun_memLp n).aestronglyMeasurable
  have htwo_Hhalf_memLp : MemLp (fun x => 2 * Hhalf x) 2 μ := by
    simpa [Hhalf, mul_assoc, mul_left_comm, mul_comm] using hHhalf_memLp.const_mul (2 : ℝ)
  have hfn_dom :
      ∀ n, ∀ᵐ x ∂μ, |fn n x - f x| ≤ 2 * Hhalf x := by
    intro n
    filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx
    have hux : 0 < u x := hu_pos x (hΩ_sub hx)
    have hshift_nonneg :
        0 ≤ superExactShiftPow (superEpsSeq n) (-(p / 2)) (u x) :=
      superExactShiftPow_nonneg (ε := superEpsSeq n) (a := -(p / 2)) (superEpsSeq_pos n)
    have hhalf_nonneg : 0 ≤ Hhalf x := Real.rpow_nonneg (abs_nonneg _) _
    have hshift_le :
        superExactShiftPow (superEpsSeq n) (-(p / 2)) (u x) ≤ Hhalf x := by
      simpa [Hhalf] using
        superExactShiftPow_le_inv_rpow_of_pos
          (ε := superEpsSeq n) (q := p / 2) (t := u x)
          (superEpsSeq_pos n) (by linarith) hux
    have hshift_norm_le : ‖superExactShiftPow (superEpsSeq n) (-(p / 2)) (u x)‖ ≤ ‖Hhalf x‖ := by
      rw [Real.norm_of_nonneg hshift_nonneg, Real.norm_of_nonneg hhalf_nonneg]
      exact hshift_le
    have hfn_bound : ‖fn n x‖ ≤ ‖Hhalf x‖ := by
      calc
        ‖fn n x‖
            = |η x| * ‖superExactShiftPow (superEpsSeq n) (-(p / 2)) (u x)‖ := by
                simp [fn, superExactPowerCutoff_eq_mul_shiftPow, norm_mul]
        _ ≤ |η x| * ‖Hhalf x‖ := by
            exact mul_le_mul_of_nonneg_left hshift_norm_le (abs_nonneg _)
        _ ≤ 1 * ‖Hhalf x‖ := by
            exact mul_le_mul_of_nonneg_right (hη_bound x) (norm_nonneg _)
        _ = ‖Hhalf x‖ := by ring
    have hf_bound : ‖f x‖ ≤ ‖Hhalf x‖ := by
      calc
        ‖f x‖ = |η x| * ‖Hhalf x‖ := by
          simp [f, Hhalf, superPowerCutoff, norm_mul]
        _ ≤ 1 * ‖Hhalf x‖ := by
          exact mul_le_mul_of_nonneg_right (hη_bound x) (norm_nonneg _)
        _ = ‖Hhalf x‖ := by ring
    calc
      |fn n x - f x| ≤ ‖fn n x‖ + ‖f x‖ := by
        simpa [Real.norm_eq_abs] using norm_sub_le (fn n x) (f x)
      _ ≤ 2 * ‖Hhalf x‖ := by
        linarith
      _ = 2 * Hhalf x := by
        rw [Real.norm_of_nonneg hhalf_nonneg]
  have hfn_tendsto :
      Filter.Tendsto (fun n => eLpNorm (fun x => fn n x - f x) 2 μ) Filter.atTop (nhds 0) := by
    exact super_tendsto_eLpNorm_zero_of_dominated htwo_Hhalf_memLp hfn_meas hfn_dom <| by
      filter_upwards [hfn_tendsto_ae] with x hx
      have hconst : Filter.Tendsto (fun _ : ℕ => f x) Filter.atTop (nhds (f x)) :=
        tendsto_const_nhds
      simpa using hx.sub hconst
  let Bn : ℕ → Fin d → E → ℝ := fun n i x =>
    (fderiv ℝ η x) (EuclideanSpace.single i 1) *
      superExactShiftPow (superEpsSeq n) (-(p / 2)) (u x)
  let B : Fin d → E → ℝ := fun i x =>
    (fderiv ℝ η x) (EuclideanSpace.single i 1) * Hhalf x
  have hCHhalf_memLp : MemLp (fun x => Cη * Hhalf x) 2 μ := by
    simpa [Hhalf, mul_assoc, mul_left_comm, mul_comm] using hHhalf_memLp.const_mul Cη
  have htwo_CHhalf_memLp : MemLp (fun x => (2 * Cη) * Hhalf x) 2 μ := by
    simpa [Hhalf, mul_assoc, mul_left_comm, mul_comm] using hHhalf_memLp.const_mul (2 * Cη)
  have hB_memLp :
      ∀ i : Fin d, MemLp (B i) 2 μ := by
    intro i
    refine hCHhalf_memLp.of_le ?_ ?_
    · have hcoord_meas :
        AEStronglyMeasurable
          (fun x => (fderiv ℝ η x) (EuclideanSpace.single i 1)) μ := by
        simpa using
          (((hη.continuous_fderiv (by simp : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0)).clm_apply
            continuous_const).aestronglyMeasurable)
      simpa [B] using hcoord_meas.mul hHhalf_memLp.aestronglyMeasurable
    · filter_upwards with x
      have hhalf_nonneg : 0 ≤ Hhalf x := Real.rpow_nonneg (abs_nonneg _) _
      have hcoord_le :
          |(fderiv ℝ η x) (EuclideanSpace.single i 1)| ≤ Cη := by
        exact le_trans
          (abs_fderiv_apply_le_norm_fderiv (d := d) (f := η) (x := x) i)
          (hη_grad_bound x)
      have hcoord_norm_le :
          ‖(fderiv ℝ η x) (EuclideanSpace.single i 1)‖ ≤ Cη := by
        simpa [Real.norm_eq_abs] using hcoord_le
      calc
        ‖B i x‖ = ‖(fderiv ℝ η x) (EuclideanSpace.single i 1)‖ * ‖Hhalf x‖ := by
          simp [B, norm_mul]
        _ ≤ Cη * ‖Hhalf x‖ := by
          exact mul_le_mul hcoord_norm_le le_rfl (norm_nonneg _) hCη_nonneg
        _ = ‖Cη * Hhalf x‖ := by
          rw [norm_mul, Real.norm_of_nonneg hCη_nonneg]
  have hB_tendsto_ae :
      ∀ i : Fin d, ∀ᵐ x ∂μ, Filter.Tendsto (fun n => Bn n i x) Filter.atTop (nhds (B i x)) := by
    intro i
    filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx
    have hux : 0 < u x := hu_pos x (hΩ_sub hx)
    have hpow :=
      superExactShiftPow_tendsto_rpow_of_pos (a := -(p / 2)) (t := u x) hux
    have hpow_eq :
        (u x) ^ (-(p / 2)) = Hhalf x := by
      dsimp [Hhalf]
      rw [abs_of_pos (inv_pos.mpr hux)]
      rw [show (-(p / 2) : ℝ) = -(p / 2) by ring, Real.rpow_neg hux.le]
      rw [Real.inv_rpow hux.le]
    simpa [Bn, B, hpow_eq, Hhalf, mul_assoc, mul_left_comm, mul_comm] using
      Filter.Tendsto.const_mul ((fderiv ℝ η x) (EuclideanSpace.single i 1)) hpow
  have hBn_memLp :
      ∀ n i, MemLp (Bn n i) 2 μ := by
    intro n i
    refine hCHhalf_memLp.of_le ?_ ?_
    · have hcoord_meas :
        AEStronglyMeasurable
          (fun x => (fderiv ℝ η x) (EuclideanSpace.single i 1)) μ := by
        simpa using
          (((hη.continuous_fderiv (by simp : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0)).clm_apply
            continuous_const).aestronglyMeasurable)
      have hshift_meas :
          AEStronglyMeasurable
            (fun x => superExactShiftPow (superEpsSeq n) (-(p / 2)) (u x)) μ := by
        exact
          (superExactShiftPow_comp_aemeasurable
            (Ω := Ω) (u := u) (ε := superEpsSeq n) (a := -(p / 2))
            (superEpsSeq_pos n) hu).aestronglyMeasurable
      simpa [Bn] using hcoord_meas.mul hshift_meas
    · filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx
      have hux : 0 < u x := hu_pos x (hΩ_sub hx)
      have hshift_nonneg :
          0 ≤ superExactShiftPow (superEpsSeq n) (-(p / 2)) (u x) :=
        superExactShiftPow_nonneg (ε := superEpsSeq n) (a := -(p / 2)) (superEpsSeq_pos n)
      have hhalf_nonneg : 0 ≤ Hhalf x := Real.rpow_nonneg (abs_nonneg _) _
      have hshift_le :
          superExactShiftPow (superEpsSeq n) (-(p / 2)) (u x) ≤ Hhalf x := by
        simpa [Hhalf] using
          superExactShiftPow_le_inv_rpow_of_pos
            (ε := superEpsSeq n) (q := p / 2) (t := u x)
            (superEpsSeq_pos n) (by linarith) hux
      have hshift_norm_le :
          ‖superExactShiftPow (superEpsSeq n) (-(p / 2)) (u x)‖ ≤ ‖Hhalf x‖ := by
        rw [Real.norm_of_nonneg hshift_nonneg, Real.norm_of_nonneg hhalf_nonneg]
        exact hshift_le
      have hcoord_le :
          |(fderiv ℝ η x) (EuclideanSpace.single i 1)| ≤ Cη := by
        exact le_trans
          (abs_fderiv_apply_le_norm_fderiv (d := d) (f := η) (x := x) i)
          (hη_grad_bound x)
      have hcoord_norm_le :
          ‖(fderiv ℝ η x) (EuclideanSpace.single i 1)‖ ≤ Cη := by
        simpa [Real.norm_eq_abs] using hcoord_le
      calc
        ‖Bn n i x‖
            = ‖(fderiv ℝ η x) (EuclideanSpace.single i 1)‖ *
                ‖superExactShiftPow (superEpsSeq n) (-(p / 2)) (u x)‖ := by
                  simp [Bn, norm_mul]
        _ ≤ Cη * ‖Hhalf x‖ := by
            exact
              (mul_le_mul hcoord_norm_le hshift_norm_le (norm_nonneg _) hCη_nonneg)
        _ = ‖Cη * Hhalf x‖ := by
            rw [norm_mul, Real.norm_of_nonneg hCη_nonneg]
  have hBn_fun_memLp :
      ∀ n i, MemLp (fun x => Bn n i x - B i x) 2 μ := by
    intro n i
    exact (hBn_memLp n i).sub (hB_memLp i)
  have hBn_tendsto :
      ∀ i : Fin d,
        Filter.Tendsto (fun n => eLpNorm (fun x => Bn n i x - B i x) 2 μ) Filter.atTop (nhds 0) := by
    intro i
    have hdom :
        ∀ n, ∀ᵐ x ∂μ, |Bn n i x - B i x| ≤ (2 * Cη) * Hhalf x := by
      intro n
      filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx
      have hux : 0 < u x := hu_pos x (hΩ_sub hx)
      have hhalf_nonneg : 0 ≤ Hhalf x := Real.rpow_nonneg (abs_nonneg _) _
      have hcoord_le :
          |(fderiv ℝ η x) (EuclideanSpace.single i 1)| ≤ Cη := by
        exact le_trans
          (abs_fderiv_apply_le_norm_fderiv (d := d) (f := η) (x := x) i)
          (hη_grad_bound x)
      have hcoord_norm_le :
          ‖(fderiv ℝ η x) (EuclideanSpace.single i 1)‖ ≤ Cη := by
        simpa [Real.norm_eq_abs] using hcoord_le
      have hshift_nonneg :
          0 ≤ superExactShiftPow (superEpsSeq n) (-(p / 2)) (u x) :=
        superExactShiftPow_nonneg (ε := superEpsSeq n) (a := -(p / 2)) (superEpsSeq_pos n)
      have hshift_le :
          superExactShiftPow (superEpsSeq n) (-(p / 2)) (u x) ≤ Hhalf x := by
        simpa [Hhalf] using
          superExactShiftPow_le_inv_rpow_of_pos
            (ε := superEpsSeq n) (q := p / 2) (t := u x)
            (superEpsSeq_pos n) (by linarith) hux
      have hshift_norm_le :
          ‖superExactShiftPow (superEpsSeq n) (-(p / 2)) (u x)‖ ≤ ‖Hhalf x‖ := by
        rw [Real.norm_of_nonneg hshift_nonneg, Real.norm_of_nonneg hhalf_nonneg]
        exact hshift_le
      have hBn_bound : ‖Bn n i x‖ ≤ Cη * ‖Hhalf x‖ := by
        calc
          ‖Bn n i x‖
              = ‖(fderiv ℝ η x) (EuclideanSpace.single i 1)‖ *
                  ‖superExactShiftPow (superEpsSeq n) (-(p / 2)) (u x)‖ := by
                    simp [Bn, norm_mul]
          _ ≤ Cη * ‖Hhalf x‖ := by
              exact mul_le_mul hcoord_norm_le hshift_norm_le (norm_nonneg _) hCη_nonneg
      have hB_bound : ‖B i x‖ ≤ Cη * ‖Hhalf x‖ := by
        calc
          ‖B i x‖ = ‖(fderiv ℝ η x) (EuclideanSpace.single i 1)‖ * ‖Hhalf x‖ := by
            simp [B, norm_mul]
          _ ≤ Cη * ‖Hhalf x‖ := by
            exact mul_le_mul hcoord_norm_le le_rfl (norm_nonneg _) hCη_nonneg
      calc
        |Bn n i x - B i x| ≤ ‖Bn n i x‖ + ‖B i x‖ := by
          simpa [Real.norm_eq_abs] using norm_sub_le (Bn n i x) (B i x)
        _ ≤ 2 * (Cη * ‖Hhalf x‖) := by
          linarith
        _ = (2 * Cη) * Hhalf x := by
          rw [Real.norm_of_nonneg hhalf_nonneg]
          ring
    exact super_tendsto_eLpNorm_zero_of_dominated htwo_CHhalf_memLp
      (fun n => (hBn_fun_memLp n i).aestronglyMeasurable) hdom <| by
        filter_upwards [hB_tendsto_ae i] with x hx
        have hconst : Filter.Tendsto (fun _ : ℕ => B i x) Filter.atTop (nhds (B i x)) :=
          tendsto_const_nhds
        simpa using hx.sub hconst
  let Gn : ℕ → Fin d → E → ℝ := fun n i x => (wfn n).weakGrad x i
  let AsingSeq : ℕ → Fin d → E → ℝ := fun n i x => Gn n i x - Bn n i x
  let Asing : Fin d → E → ℝ := fun i x =>
    η x * ((-(p / 2)) * |(u x)⁻¹| ^ (p / 2 + 1)) * hu.weakGrad x i
  have hAsingSeq_memLp :
      ∀ n i, MemLp (AsingSeq n i) 2 μ := by
    intro n i
    simpa [AsingSeq, Gn] using ((wfn n).weakGrad_component_memLp i).sub (hBn_memLp n i)
  have hAsingSeq_formula :
      ∀ n i x,
        AsingSeq n i x =
          η x * deriv (superExactShiftReg (superEpsSeq n) (-(p / 2))) (u x) *
            hu.weakGrad x i := by
    intro n i x
    dsimp [AsingSeq, Gn, Bn, wfn, wfnBig, hu]
    simp [MemW1pWitness.restrict]
    rw [superExactPowerCutoffWitness_grad
      (d := d) (u := u) (η := η) (ε := superEpsSeq n) (a := -(p / 2))
      (s := s) (Cη := Cη) (superEpsSeq_pos n) ha_pow hu1 hη hη_bound hη_grad_bound
      hη_sub_ball x i]
    ring
  have hAsing_tendsto_ae :
      ∀ i : Fin d, ∀ᵐ x ∂μ, Filter.Tendsto (fun n => AsingSeq n i x) Filter.atTop
        (nhds (Asing i x)) := by
    intro i
    filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx
    have hux : 0 < u x := hu_pos x (hΩ_sub hx)
    have hderiv := superExactInv_deriv_tendsto (u := u) (p := p) (x := x) hux
    have hmul :
        Filter.Tendsto
          (fun n =>
            (η x * hu.weakGrad x i) *
              deriv (superExactShiftReg (superEpsSeq n) (-(p / 2))) (u x))
          Filter.atTop
          (nhds
            ((η x * hu.weakGrad x i) *
              ((-(p / 2)) * |(u x)⁻¹| ^ (p / 2 + 1)))) := by
      exact Filter.Tendsto.const_mul (η x * hu.weakGrad x i) hderiv
    have hEq :
        (fun n => AsingSeq n i x) =
          (fun n =>
            (η x * hu.weakGrad x i) *
              deriv (superExactShiftReg (superEpsSeq n) (-(p / 2))) (u x)) := by
      funext n
      rw [hAsingSeq_formula n i x]
      ring
    rw [hEq]
    simpa [Asing, mul_assoc, mul_left_comm, mul_comm] using hmul
  have hAsing_aestrong :
      ∀ i : Fin d, AEStronglyMeasurable (Asing i) μ := by
    intro i
    exact aestronglyMeasurable_of_tendsto_ae Filter.atTop
      (fun n => (hAsingSeq_memLp n i).aestronglyMeasurable) (hAsing_tendsto_ae i)
  let CE : ℝ := 2 * Cη ^ 2 * (A.1.Λ * (p / (1 + p)) ^ 2 + 1)
  have hCE_nonneg : 0 ≤ CE := by
    dsimp [CE]
    have hterm_nonneg : 0 ≤ A.1.Λ * (p / (1 + p)) ^ 2 + 1 := by
      exact add_nonneg (mul_nonneg A.1.Λ_nonneg (sq_nonneg _)) zero_le_one
    exact mul_nonneg (mul_nonneg (by positivity) (sq_nonneg _)) hterm_nonneg
  have hRhs_int :
      ∀ n, Integrable (fun x => superExactShiftPow (superEpsSeq n) (-p) (u x)) μ := by
    intro n
    simpa [μ, Ω] using
      (superExactInv_shiftPow_integrableOn_ball (u := u) (ε := superEpsSeq n) (p := p)
        (s := s) (superEpsSeq_pos n) (by linarith) hs hu)
  have hpIntΩ : Integrable (fun x => |(u x)⁻¹| ^ p) μ := by
    simpa [μ, Ω] using hpInt
  have hRhs_le :
      ∀ n,
        ∫ x in Ω, superExactShiftPow (superEpsSeq n) (-p) (u x) ∂volume ≤ I := by
    intro n
    have hpt :
        ∀ᵐ x ∂μ, superExactShiftPow (superEpsSeq n) (-p) (u x) ≤ |(u x)⁻¹| ^ p := by
      filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx
      have hux : 0 < u x := hu_pos x (hΩ_sub hx)
      simpa using
        superExactShiftPow_le_inv_rpow_of_pos
          (ε := superEpsSeq n) (q := p) (t := u x) (superEpsSeq_pos n) (by linarith) hux
    dsimp [I]
    exact integral_mono_ae (hRhs_int n) hpIntΩ hpt
  have hGn_energy :
      ∀ n,
        ∫ x in Ω, ‖(wfn n).weakGrad x‖ ^ 2 ∂volume ≤ CE * I := by
    intro n
    calc
      ∫ x in Ω, ‖(wfn n).weakGrad x‖ ^ 2 ∂volume
          ≤ CE * ∫ x in Ω, superExactShiftPow (superEpsSeq n) (-p) (u x) ∂volume := by
              simpa [CE, I, Ω] using
                (superExactInv_energy_mainBall
                  (d := d) hd A (u := u) (η := η) (p := p) (s := s) (Cη := Cη)
                  hp hs hs1 hu_pos hsuper hη hη_bound hη_grad_bound hη_sub_ball n)
      _ ≤ CE * I := by
          exact mul_le_mul_of_nonneg_left (hRhs_le n) hCE_nonneg
  have hBn_sq_bound :
      ∀ n i, ∫ x in Ω, (Bn n i x) ^ 2 ∂volume ≤ Cη ^ 2 * I := by
    intro n i
    have hBn_sq_int : Integrable (fun x => (Bn n i x) ^ 2) μ := by
      simpa [pow_two] using (hBn_memLp n i).integrable_sq
    have hBn_rhs_int :
        Integrable (fun x => Cη ^ 2 * superExactShiftPow (superEpsSeq n) (-p) (u x)) μ := by
      exact (hRhs_int n).const_mul (Cη ^ 2)
    have hBn_pt :
        ∀ᵐ x ∂μ, (Bn n i x) ^ 2 ≤ Cη ^ 2 * superExactShiftPow (superEpsSeq n) (-p) (u x) := by
      filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx
      have hux : 0 < u x := hu_pos x (hΩ_sub hx)
      have hcoord_sq_le :
          ((fderiv ℝ η x) (EuclideanSpace.single i 1)) ^ 2 ≤ Cη ^ 2 := by
        exact sq_le_sq.mpr (by
          simpa [abs_of_nonneg hCη_nonneg] using
            (le_trans
              (abs_fderiv_apply_le_norm_fderiv (d := d) (f := η) (x := x) i)
              (hη_grad_bound x)))
      have hpow_sq_eq :
          (superExactShiftPow (superEpsSeq n) (-(p / 2)) (u x)) ^ 2 =
            superExactShiftPow (superEpsSeq n) (-p) (u x) := by
        exact superExactInv_power_sq_of_pos
          (u := u) (ε := superEpsSeq n) (p := p) (x := x) (superEpsSeq_pos n) hux
      have hpow_nonneg :
          0 ≤ superExactShiftPow (superEpsSeq n) (-p) (u x) :=
        superExactShiftPow_nonneg (ε := superEpsSeq n) (a := -p) (superEpsSeq_pos n)
      calc
        (Bn n i x) ^ 2
            = ((fderiv ℝ η x) (EuclideanSpace.single i 1)) ^ 2 *
                superExactShiftPow (superEpsSeq n) (-p) (u x) := by
                  dsimp [Bn]
                  calc
                    ((fderiv ℝ η x) (EuclideanSpace.single i 1) *
                        superExactShiftPow (superEpsSeq n) (-(p / 2)) (u x)) ^ 2
                        = ((fderiv ℝ η x) (EuclideanSpace.single i 1)) ^ 2 *
                            (superExactShiftPow (superEpsSeq n) (-(p / 2)) (u x)) ^ 2 := by
                              ring
                    _ = ((fderiv ℝ η x) (EuclideanSpace.single i 1)) ^ 2 *
                          superExactShiftPow (superEpsSeq n) (-p) (u x) := by
                            rw [hpow_sq_eq]
        _ ≤ Cη ^ 2 * superExactShiftPow (superEpsSeq n) (-p) (u x) := by
            exact mul_le_mul_of_nonneg_right hcoord_sq_le hpow_nonneg
    have hmain :
        ∫ x in Ω, (Bn n i x) ^ 2 ∂volume ≤
          ∫ x in Ω, Cη ^ 2 * superExactShiftPow (superEpsSeq n) (-p) (u x) ∂volume := by
      simpa [μ] using integral_mono_ae hBn_sq_int hBn_rhs_int hBn_pt
    calc
      ∫ x in Ω, (Bn n i x) ^ 2 ∂volume
          ≤ ∫ x in Ω, Cη ^ 2 * superExactShiftPow (superEpsSeq n) (-p) (u x) ∂volume := hmain
      _ = Cη ^ 2 * ∫ x in Ω, superExactShiftPow (superEpsSeq n) (-p) (u x) ∂volume := by
            rw [integral_const_mul]
      _ ≤ Cη ^ 2 * I := by
            exact mul_le_mul_of_nonneg_left (hRhs_le n) (sq_nonneg _)
  have hAsingSeq_sq_bound :
      ∀ n i, ∫ x in Ω, (AsingSeq n i x) ^ 2 ∂volume ≤ 2 * (CE * I) + 2 * (Cη ^ 2 * I) := by
    intro n i
    have hpt :
        ∀ᵐ x ∂μ, (AsingSeq n i x) ^ 2 ≤ 2 * ‖(wfn n).weakGrad x‖ ^ 2 + 2 * (Bn n i x) ^ 2 := by
      filter_upwards with x
      have haux :
          (AsingSeq n i x) ^ 2 ≤ 2 * ((wfn n).weakGrad x i) ^ 2 + 2 * (Bn n i x) ^ 2 := by
        dsimp [AsingSeq, Gn]
        nlinarith [sq_nonneg ((wfn n).weakGrad x i + Bn n i x)]
      have hcoord_le :
          |(wfn n).weakGrad x i| ≤ ‖(wfn n).weakGrad x‖ := by
        simpa [Real.norm_eq_abs] using PiLp.norm_apply_le ((wfn n).weakGrad x) i
      have hcoord_sq_le :
          ((wfn n).weakGrad x i) ^ 2 ≤ ‖(wfn n).weakGrad x‖ ^ 2 := by
        exact sq_le_sq.mpr (by
          have hnorm_nonneg : 0 ≤ ‖(wfn n).weakGrad x‖ := norm_nonneg _
          simpa [Real.norm_eq_abs, abs_of_nonneg hnorm_nonneg] using hcoord_le)
      calc
        (AsingSeq n i x) ^ 2 ≤ 2 * ((wfn n).weakGrad x i) ^ 2 + 2 * (Bn n i x) ^ 2 := haux
        _ ≤ 2 * ‖(wfn n).weakGrad x‖ ^ 2 + 2 * (Bn n i x) ^ 2 := by
            have htwice :
                2 * ((wfn n).weakGrad x i) ^ 2 ≤ 2 * ‖(wfn n).weakGrad x‖ ^ 2 := by
              exact mul_le_mul_of_nonneg_left hcoord_sq_le (by positivity)
            simpa [add_comm, add_left_comm, add_assoc] using
              add_le_add_right htwice (2 * (Bn n i x) ^ 2)
    have hintL : Integrable (fun x => (AsingSeq n i x) ^ 2) μ := by
      simpa [pow_two] using (hAsingSeq_memLp n i).integrable_sq
    have hintR :
        Integrable (fun x => 2 * ‖(wfn n).weakGrad x‖ ^ 2 + 2 * (Bn n i x) ^ 2) μ := by
      simpa [pow_two, μ] using
        ((wfn n).weakGrad_norm_memLp.integrable_sq.const_mul (2 : ℝ)).add
          ((hBn_memLp n i).integrable_sq.const_mul (2 : ℝ))
    calc
      ∫ x in Ω, (AsingSeq n i x) ^ 2 ∂volume
          = ∫ x, (AsingSeq n i x) ^ 2 ∂μ := by simp [μ]
      _ ≤ ∫ x, (2 * ‖(wfn n).weakGrad x‖ ^ 2 + 2 * (Bn n i x) ^ 2) ∂μ := by
            exact integral_mono_ae hintL hintR hpt
      _ = 2 * ∫ x in Ω, ‖(wfn n).weakGrad x‖ ^ 2 ∂volume +
            2 * ∫ x in Ω, (Bn n i x) ^ 2 ∂volume := by
            simp [μ, integral_add,
              ((wfn n).weakGrad_norm_memLp.integrable_sq.const_mul (2 : ℝ)),
              ((hBn_memLp n i).integrable_sq.const_mul (2 : ℝ)), integral_const_mul]
      _ ≤ 2 * (CE * I) + 2 * (Cη ^ 2 * I) := by
            gcongr
            · exact hGn_energy n
            · exact hBn_sq_bound n i
  have hAsing_memLp :
      ∀ i : Fin d, MemLp (Asing i) 2 μ := by
    intro i
    have hFatou :
        ∫⁻ x, ENNReal.ofReal ((Asing i x) ^ 2) ∂μ ≤
          Filter.liminf (fun n => ∫⁻ x, ENNReal.ofReal ((AsingSeq n i x) ^ 2) ∂μ) Filter.atTop := by
      have hmeas :
          ∀ n, AEMeasurable (fun x => ENNReal.ofReal ((AsingSeq n i x) ^ 2)) μ := by
        intro n
        exact (((hAsingSeq_memLp n i).aestronglyMeasurable.aemeasurable.pow_const 2).ennreal_ofReal)
      have hleft := MeasureTheory.lintegral_liminf_le' (μ := μ) hmeas
      have hlim :
          (fun x =>
            Filter.liminf (fun n => ENNReal.ofReal ((AsingSeq n i x) ^ 2)) Filter.atTop) =ᵐ[μ]
            (fun x => ENNReal.ofReal ((Asing i x) ^ 2)) := by
        filter_upwards [hAsing_tendsto_ae i] with x hx
        have hsq :
            Filter.Tendsto (fun n => ENNReal.ofReal ((AsingSeq n i x) ^ 2)) Filter.atTop
              (nhds (ENNReal.ofReal ((Asing i x) ^ 2))) := by
          exact (ENNReal.continuous_ofReal.tendsto _
            |>.comp (((continuous_pow 2).tendsto (Asing i x)).comp hx))
        simp [hsq.liminf_eq]
      calc
        ∫⁻ x, ENNReal.ofReal ((Asing i x) ^ 2) ∂μ
            = ∫⁻ x, Filter.liminf (fun n => ENNReal.ofReal ((AsingSeq n i x) ^ 2)) Filter.atTop ∂μ := by
                exact lintegral_congr_ae hlim.symm
        _ ≤ Filter.liminf (fun n => ∫⁻ x, ENNReal.ofReal ((AsingSeq n i x) ^ 2) ∂μ) Filter.atTop := hleft
    have hBound_ne_top :
        Filter.liminf (fun n => ∫⁻ x, ENNReal.ofReal ((AsingSeq n i x) ^ 2) ∂μ) Filter.atTop ≠ ⊤ := by
      apply ne_of_lt
      have htop : ENNReal.ofReal (2 * (CE * I) + 2 * (Cη ^ 2 * I)) < ⊤ := by simp
      have hle :
          Filter.liminf (fun n => ∫⁻ x, ENNReal.ofReal ((AsingSeq n i x) ^ 2) ∂μ) Filter.atTop ≤
            ENNReal.ofReal (2 * (CE * I) + 2 * (Cη ^ 2 * I)) := by
        refine Filter.liminf_le_of_frequently_le' (Filter.Frequently.of_forall fun n => ?_)
        have hEq :
            ∫⁻ x, ENNReal.ofReal ((AsingSeq n i x) ^ 2) ∂μ =
              ENNReal.ofReal (∫ x in Ω, (AsingSeq n i x) ^ 2 ∂volume) := by
          change
            ∫⁻ x, ENNReal.ofReal ((AsingSeq n i x) ^ 2) ∂μ =
              ENNReal.ofReal (∫ x, (AsingSeq n i x) ^ 2 ∂μ)
          exact
            (MeasureTheory.ofReal_integral_eq_lintegral_ofReal
              (μ := μ) (f := fun x => (AsingSeq n i x) ^ 2)
              ((hAsingSeq_memLp n i).integrable_sq)
              (ae_of_all _ fun _ => sq_nonneg _)).symm
        rw [hEq]
        exact ENNReal.ofReal_le_ofReal (hAsingSeq_sq_bound n i)
      exact lt_of_le_of_lt hle htop
    have hAsing_sq_int :
        Integrable (fun x => (Asing i x) ^ 2) μ := by
      have hlin_top :
          ∫⁻ x, ENNReal.ofReal ((Asing i x) ^ 2) ∂μ ≠ ⊤ := by
        exact ne_of_lt (lt_of_le_of_lt hFatou (lt_top_iff_ne_top.mpr hBound_ne_top))
      have hInt :=
        integrable_toReal_of_lintegral_ne_top
          (((hAsing_aestrong i).aemeasurable.pow_const 2).ennreal_ofReal) hlin_top
      simpa [ENNReal.toReal_ofReal, sq_nonneg] using hInt
    exact (MeasureTheory.memLp_two_iff_integrable_sq (hAsing_aestrong i)).2 hAsing_sq_int
  have hAsing_fun_memLp :
      ∀ n i, MemLp (fun x => AsingSeq n i x - Asing i x) 2 μ := by
    intro n i
    exact (hAsingSeq_memLp n i).sub (hAsing_memLp i)
  have hAsing_tendsto :
      ∀ i : Fin d,
        Filter.Tendsto (fun n => eLpNorm (fun x => AsingSeq n i x - Asing i x) 2 μ)
          Filter.atTop (nhds 0) := by
    intro i
    have htwo_Asing_memLp : MemLp (fun x => 2 * |Asing i x|) 2 μ := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using ((hAsing_memLp i).norm.const_mul (2 : ℝ))
    have hdom :
        ∀ n, ∀ᵐ x ∂μ, |AsingSeq n i x - Asing i x| ≤ 2 * |Asing i x| := by
      intro n
      filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx
      have hux : 0 < u x := hu_pos x (hΩ_sub hx)
      have hpow_nonneg : 0 ≤ |(u x)⁻¹| ^ (p / 2 + 1) := Real.rpow_nonneg (abs_nonneg _) _
      have hseq_abs_le : |AsingSeq n i x| ≤ |Asing i x| := by
        have hderiv_le :=
          superExactShiftReg_deriv_abs_le_inv_rpow_of_pos
            (ε := superEpsSeq n) (q := p / 2) (t := u x)
            (superEpsSeq_pos n) (by linarith) hux
        have hlimit_abs :
            |((-(p / 2)) * |(u x)⁻¹| ^ (p / 2 + 1))| =
              (p / 2) * |(u x)⁻¹| ^ (p / 2 + 1) := by
          rw [abs_mul, abs_of_neg (by linarith : (-(p / 2) : ℝ) < 0),
            abs_of_nonneg hpow_nonneg]
          ring
        calc
          |AsingSeq n i x|
              = |η x| *
                  |deriv (superExactShiftReg (superEpsSeq n) (-(p / 2))) (u x)| *
                  |hu.weakGrad x i| := by
                    rw [hAsingSeq_formula n i x]
                    simp [abs_mul]
          _ ≤ |η x| * ((p / 2) * |(u x)⁻¹| ^ (p / 2 + 1)) * |hu.weakGrad x i| := by
              gcongr
          _ = |Asing i x| := by
              symm
              dsimp [Asing]
              rw [abs_mul, abs_mul, hlimit_abs]
      calc
        |AsingSeq n i x - Asing i x| ≤ |AsingSeq n i x| + |Asing i x| := by
          simpa [Real.norm_eq_abs] using norm_sub_le (AsingSeq n i x) (Asing i x)
        _ ≤ 2 * |Asing i x| := by linarith
    exact super_tendsto_eLpNorm_zero_of_dominated htwo_Asing_memLp
      (fun n => (hAsing_fun_memLp n i).aestronglyMeasurable) hdom <| by
        filter_upwards [hAsing_tendsto_ae i] with x hx
        have hconst : Filter.Tendsto (fun _ : ℕ => Asing i x) Filter.atTop (nhds (Asing i x)) :=
          tendsto_const_nhds
        simpa using hx.sub hconst
  let gComp : Fin d → E → ℝ := fun i x => Asing i x + B i x
  have hGn_fun_memLp :
      ∀ n i, MemLp (fun x => Gn n i x - gComp i x) 2 μ := by
    intro n i
    have hEq :
        (fun x => Gn n i x - gComp i x) =
          (fun x => (AsingSeq n i x - Asing i x) + (Bn n i x - B i x)) := by
      ext x
      dsimp [Gn, gComp, AsingSeq]
      ring
    rw [hEq]
    simpa using (hAsing_fun_memLp n i).add (hBn_fun_memLp n i)
  have hGn_tendsto :
      ∀ i : Fin d,
        Filter.Tendsto (fun n => eLpNorm (fun x => Gn n i x - gComp i x) 2 μ)
          Filter.atTop (nhds 0) := by
    intro i
    let rhs : ℕ → ENNReal := fun n =>
      eLpNorm (fun x => AsingSeq n i x - Asing i x) 2 μ +
        eLpNorm (fun x => Bn n i x - B i x) 2 μ
    have hbound :
        ∀ n,
          eLpNorm (fun x => Gn n i x - gComp i x) 2 μ ≤ rhs n := by
      intro n
      have hEq :
          (fun x => Gn n i x - gComp i x) =
            (fun x => (AsingSeq n i x - Asing i x) + (Bn n i x - B i x)) := by
        ext x
        dsimp [Gn, gComp, AsingSeq]
        ring
      rw [hEq]
      simpa [rhs] using eLpNorm_add_le
        (hAsing_fun_memLp n i).aestronglyMeasurable
        (hBn_fun_memLp n i).aestronglyMeasurable (by norm_num)
    have hsum_tendsto :
        Filter.Tendsto rhs Filter.atTop (nhds 0) := by
      simpa [rhs] using (hAsing_tendsto i).add (hBn_tendsto i)
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum_tendsto
      (fun _ => zero_le _) hbound
  have hWeakComp :
      ∀ i : Fin d, HasWeakPartialDeriv i (gComp i) f Ω := by
    intro i
    have hf_memLp' : MemLp f (ENNReal.ofReal (2 : ℝ)) μ := by
      simpa using hf_memLp
    have hgComp_memLp' : MemLp (gComp i) (ENNReal.ofReal (2 : ℝ)) μ := by
      have hEq :
          gComp i = fun x => Asing i x + B i x := by
        funext x
        simp [gComp]
      rw [hEq]
      simpa using (hAsing_memLp i).add (hB_memLp i)
    have hGn_isWeak : ∀ n, HasWeakPartialDeriv i (Gn n i) (fn n) Ω := by
      intro n
      simpa [Gn] using (wfn n).isWeakGrad i
    have hfn_fun_memLp' :
        ∀ n, MemLp (fun x => fn n x - f x) (ENNReal.ofReal (2 : ℝ)) μ := by
      intro n
      simpa using hfn_fun_memLp n
    have hfn_tendsto' :
        Filter.Tendsto
          (fun n => eLpNorm (fun x => fn n x - f x) (ENNReal.ofReal (2 : ℝ)) μ)
          Filter.atTop (nhds 0) := by
      simpa using hfn_tendsto
    have hGn_fun_memLp' :
        ∀ n, MemLp (fun x => Gn n i x - gComp i x) (ENNReal.ofReal (2 : ℝ)) μ := by
      intro n
      simpa using hGn_fun_memLp n i
    have hGn_tendsto' :
        Filter.Tendsto
          (fun n => eLpNorm (fun x => Gn n i x - gComp i x) (ENNReal.ofReal (2 : ℝ)) μ)
          Filter.atTop (nhds 0) := by
      simpa using hGn_tendsto i
    refine HasWeakPartialDeriv.of_eLpNormApprox_p
      (d := d) (Ω := Ω) (p := 2) (hΩ := Metric.isOpen_ball) (hp := by norm_num)
      (i := i) (f := f) (g := gComp i) (ψ := fn) (gψ := fun n => Gn n i)
      hf_memLp' hgComp_memLp' hGn_isWeak
      hfn_fun_memLp' hfn_tendsto' hGn_fun_memLp' hGn_tendsto'
  let G : E → E := fun x => WithLp.toLp 2 fun i => gComp i x
  let hwv : MemW1pWitness 2 f Ω := {
    memLp := hf_memLp
    weakGrad := G
    weakGrad_component_memLp := by
      intro i
      have hEq : (fun x => G x i) = gComp i := by
        funext x
        simp [G]
      rw [hEq]
      have hgComp_memLp :
          MemLp (gComp i) 2 μ := by
        have hEq' :
            gComp i = fun x => Asing i x + B i x := by
          funext x
          simp [gComp]
        rw [hEq']
        simpa using (hAsing_memLp i).add (hB_memLp i)
      simpa using hgComp_memLp
    isWeakGrad := by
      intro i
      have hEq : (fun x => G x i) = gComp i := by
        funext x
        simp [G]
      rw [hEq]
      exact hWeakComp i }
  have hGn_comp_tendsto_ae :
      ∀ i : Fin d, ∀ᵐ x ∂μ, Filter.Tendsto (fun n => Gn n i x) Filter.atTop
        (nhds (gComp i x)) := by
    intro i
    filter_upwards [hAsing_tendsto_ae i, hB_tendsto_ae i] with x hA hB
    have hEq :
        (fun n => Gn n i x) = (fun n => AsingSeq n i x + Bn n i x) := by
      funext n
      dsimp [AsingSeq, Gn]
      ring
    rw [hEq]
    have hsum :
        Filter.Tendsto (fun n => AsingSeq n i x + Bn n i x) Filter.atTop
          (nhds (Asing i x + B i x)) := hA.add hB
    simpa [gComp] using hsum
  have hGn_vec_tendsto_ae :
      ∀ᵐ x ∂μ, Filter.Tendsto (fun n => (wfn n).weakGrad x) Filter.atTop
        (nhds (hwv.weakGrad x)) := by
    have hcoords :
        ∀ᵐ x ∂μ, ∀ i : Fin d, Filter.Tendsto (fun n => Gn n i x) Filter.atTop
          (nhds (gComp i x)) := by
      rw [ae_all_iff]
      intro i
      exact hGn_comp_tendsto_ae i
    filter_upwards [hcoords] with x hx
    have hpi :
        Filter.Tendsto (fun n : ℕ => fun i : Fin d => Gn n i x) Filter.atTop
          (nhds fun i : Fin d => gComp i x) := by
      rw [tendsto_pi_nhds]
      intro i
      exact hx i
    have htoLp :
        Filter.Tendsto (fun y : Fin d → ℝ => WithLp.toLp 2 y) (nhds fun i : Fin d => gComp i x)
          (nhds (WithLp.toLp 2 fun i : Fin d => gComp i x)) :=
      (PiLp.continuous_toLp 2 (fun _ : Fin d => ℝ)).tendsto (fun i : Fin d => gComp i x)
    simpa [G, hwv, Gn] using htoLp.comp hpi
  have hFatou :
      ∫⁻ x, ENNReal.ofReal (‖hwv.weakGrad x‖ ^ 2) ∂μ ≤
        Filter.liminf (fun n => ∫⁻ x, ENNReal.ofReal (‖(wfn n).weakGrad x‖ ^ 2) ∂μ) Filter.atTop := by
    have hmeas :
        ∀ n, AEMeasurable (fun x => ENNReal.ofReal (‖(wfn n).weakGrad x‖ ^ 2)) μ := by
      intro n
      have hsq_meas :
          AEMeasurable (fun x => ‖(wfn n).weakGrad x‖ ^ 2) μ := by
        exact (wfn n).weakGrad_norm_memLp.aestronglyMeasurable.aemeasurable.pow_const 2
      exact hsq_meas.ennreal_ofReal
    have hleft := MeasureTheory.lintegral_liminf_le' (μ := μ) hmeas
    have hlim :
        (fun x =>
          Filter.liminf (fun n => ENNReal.ofReal (‖(wfn n).weakGrad x‖ ^ 2)) Filter.atTop) =ᵐ[μ]
            (fun x => ENNReal.ofReal (‖hwv.weakGrad x‖ ^ 2)) := by
      filter_upwards [hGn_vec_tendsto_ae] with x hx
      have hsq :
          Filter.Tendsto (fun n => ENNReal.ofReal (‖(wfn n).weakGrad x‖ ^ 2)) Filter.atTop
            (nhds (ENNReal.ofReal (‖hwv.weakGrad x‖ ^ 2))) := by
        exact ((ENNReal.continuous_ofReal.comp (continuous_norm.pow 2)).tendsto _).comp hx
      exact hsq.liminf_eq
    calc
      ∫⁻ x, ENNReal.ofReal (‖hwv.weakGrad x‖ ^ 2) ∂μ
          = ∫⁻ x, Filter.liminf (fun n => ENNReal.ofReal (‖(wfn n).weakGrad x‖ ^ 2)) Filter.atTop ∂μ := by
              exact lintegral_congr_ae hlim.symm
      _ ≤ Filter.liminf (fun n => ∫⁻ x, ENNReal.ofReal (‖(wfn n).weakGrad x‖ ^ 2) ∂μ) Filter.atTop := hleft
  have hRhs_meas :
      ∀ n, AEStronglyMeasurable (fun x => superExactShiftPow (superEpsSeq n) (-p) (u x)) μ := by
    intro n
    exact
      (superExactShiftPow_comp_aemeasurable
        (Ω := Ω) (u := u) (ε := superEpsSeq n) (a := -p) (superEpsSeq_pos n)
        hu).aestronglyMeasurable
  have hRhs_dom :
      ∀ n, ∀ᵐ x ∂μ, |superExactShiftPow (superEpsSeq n) (-p) (u x)| ≤ |(u x)⁻¹| ^ p := by
    intro n
    filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx
    have hux : 0 < u x := hu_pos x (hΩ_sub hx)
    have hpow_nonneg :
        0 ≤ superExactShiftPow (superEpsSeq n) (-p) (u x) :=
      superExactShiftPow_nonneg (ε := superEpsSeq n) (a := -p) (superEpsSeq_pos n)
    simpa [abs_of_nonneg hpow_nonneg] using
      superExactShiftPow_le_inv_rpow_of_pos
        (ε := superEpsSeq n) (q := p) (t := u x) (superEpsSeq_pos n) (by linarith) hux
  have hRhs_tendsto :
      Filter.Tendsto
        (fun n => ∫ x in Ω, superExactShiftPow (superEpsSeq n) (-p) (u x) ∂volume)
        Filter.atTop (nhds I) := by
    have hpt :
        ∀ᵐ x ∂μ, Filter.Tendsto (fun n => superExactShiftPow (superEpsSeq n) (-p) (u x))
          Filter.atTop
          (nhds (|(u x)⁻¹| ^ p)) := by
      filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx
      exact superExactInv_rhs_tendsto (u := u) (p := p) (x := x) (hu_pos x (hΩ_sub hx))
    have hmain :=
      MeasureTheory.tendsto_integral_of_dominated_convergence
        (fun x => |(u x)⁻¹| ^ p) hRhs_meas hpIntΩ hRhs_dom hpt
    simpa [μ, I] using hmain
  have hleft_eq :
      ∫⁻ x, ENNReal.ofReal (‖hwv.weakGrad x‖ ^ 2) ∂μ =
        ENNReal.ofReal (∫ x in Ω, ‖hwv.weakGrad x‖ ^ 2 ∂volume) := by
    change
      ∫⁻ x, ENNReal.ofReal (‖hwv.weakGrad x‖ ^ 2) ∂μ =
        ENNReal.ofReal (∫ x, ‖hwv.weakGrad x‖ ^ 2 ∂μ)
    exact
      (MeasureTheory.ofReal_integral_eq_lintegral_ofReal
        (μ := μ) (f := fun x => ‖hwv.weakGrad x‖ ^ 2)
        hwv.weakGrad_norm_memLp.integrable_sq
        (ae_of_all _ fun _ => sq_nonneg _)).symm
  have hright_eq :
      ∀ n,
        ∫⁻ x, ENNReal.ofReal (‖(wfn n).weakGrad x‖ ^ 2) ∂μ =
          ENNReal.ofReal (∫ x in Ω, ‖(wfn n).weakGrad x‖ ^ 2 ∂volume) := by
    intro n
    change
      ∫⁻ x, ENNReal.ofReal (‖(wfn n).weakGrad x‖ ^ 2) ∂μ =
        ENNReal.ofReal (∫ x, ‖(wfn n).weakGrad x‖ ^ 2 ∂μ)
    exact
      (MeasureTheory.ofReal_integral_eq_lintegral_ofReal
        (μ := μ) (f := fun x => ‖(wfn n).weakGrad x‖ ^ 2)
        (wfn n).weakGrad_norm_memLp.integrable_sq
        (ae_of_all _ fun _ => sq_nonneg _)).symm
  have hmain_enn :
      ENNReal.ofReal (∫ x in Ω, ‖hwv.weakGrad x‖ ^ 2 ∂volume) ≤ ENNReal.ofReal (CE * I) := by
    rw [← hleft_eq]
    refine le_trans hFatou ?_
    rw [Filter.liminf_congr (Filter.Eventually.of_forall hright_eq)]
    have hliminf_le :
        Filter.liminf (fun n => ENNReal.ofReal (∫ x in Ω, ‖(wfn n).weakGrad x‖ ^ 2 ∂volume))
          Filter.atTop ≤ ENNReal.ofReal (CE * I) := by
      refine Filter.liminf_le_of_frequently_le' (Filter.Frequently.of_forall fun n => ?_)
      exact ENNReal.ofReal_le_ofReal (hGn_energy n)
    exact hliminf_le
  have hmain_real :
      ∫ x in Ω, ‖hwv.weakGrad x‖ ^ 2 ∂volume ≤ CE * I := by
    exact (ENNReal.ofReal_le_ofReal_iff (by exact mul_nonneg hCE_nonneg hI_nonneg)).mp hmain_enn
  refine ⟨hwv, ?_⟩
  simpa [CE, I] using hmain_real

theorem superPowerCutoff_energy_bound
    (hd : 2 < (d : ℝ))
    (A : NormalizedEllipticCoeff d (Metric.ball (0 : E) 1))
    {u η : E → ℝ} {p s Cη : ℝ}
    (hp : 0 < p)
    (hs : 0 < s) (hs1 : s ≤ 1)
    (hu_pos : ∀ x ∈ Metric.ball (0 : E) 1, 0 < u x)
    (hsuper : IsSupersolution A.1 u)
    (hpInt :
      IntegrableOn (fun x => |(u x)⁻¹| ^ p)
        (Metric.ball (0 : E) s) volume)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hη_bound : ∀ x, |η x| ≤ 1)
    (hη_grad_bound : ∀ x, ‖fderiv ℝ η x‖ ≤ Cη)
    (hη_sub_ball : tsupport η ⊆ Metric.ball (0 : E) s) :
    ∃ hwv : MemW1pWitness 2 (superPowerCutoff (d := d) η u p) (Metric.ball (0 : E) s),
      MemW01p 2 (superPowerCutoff (d := d) η u p) (Metric.ball (0 : E) s) ∧
      ∫ x in Metric.ball (0 : E) s, ‖hwv.weakGrad x‖ ^ 2 ∂volume ≤
        2 * Cη ^ 2 * (A.1.Λ * (p / (1 + p)) ^ 2 + 1) *
          ∫ x in Metric.ball (0 : E) s, |(u x)⁻¹| ^ p ∂volume := by
  let Ω : Set E := Metric.ball (0 : E) s
  let v : E → ℝ := superPowerCutoff (d := d) η u p
  have hv_support : tsupport v ⊆ Ω :=
    superPowerCutoff_tsupport_subset (d := d) (u := u) (η := η) (p := p) hη_sub_ball
  obtain ⟨hwv, henergy⟩ :=
    superPowerCutoff_memW1p_energy_of_supersolution_core
      (d := d) hd A (u := u) (η := η) (p := p) (s := s) (Cη := Cη)
      hp hs hs1 hu_pos hsuper hpInt hη hη_bound hη_grad_bound hη_sub_ball
  have hv_compact : HasCompactSupport v :=
    hasCompactSupport_of_tsupport_subset_ball hv_support
  have hv_memW1p_real : MemW1p (ENNReal.ofReal (2 : ℝ)) v Ω := by
    simpa [Ω] using hwv.memW1p
  have hvW01_real : MemW01p (ENNReal.ofReal (2 : ℝ)) v Ω := by
    exact memW01p_of_memW1p_of_tsupport_subset
      (d := d) Metric.isOpen_ball (p := (2 : ℝ)) (by norm_num)
      hv_memW1p_real hv_compact hv_support
  have hvW01 : MemW01p 2 v Ω := by
    simpa [Ω] using hvW01_real
  exact ⟨hwv, hvW01, henergy⟩

end DeGiorgi
