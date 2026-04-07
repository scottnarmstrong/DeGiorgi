import DeGiorgi.Harnack
import DeGiorgi.Support.MeasureBounds
import DeGiorgi.Support.IterationConstants
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Algebra.Order.Group.OrderIso
import Mathlib.Topology.Order.Lattice

/-!
# Holder Local Bounds

Local dyadic-radius setup, local Moser bounds, and positivity packaging used in
the Holder endpoint.
-/

noncomputable section

open MeasureTheory Filter

namespace DeGiorgi

variable {d : ℕ} [NeZero d]

local notation "E" => AmbientSpace d
local notation "μ1" => volume.restrict (Metric.ball (0 : E) 1)
local notation "μhalf" => volume.restrict (Metric.ball (0 : E) (1 / 2 : ℝ))

noncomputable def moserDyadicRadius (n : ℕ) : ℝ :=
  (1 / 4 : ℝ) / (2 : ℝ) ^ n

noncomputable def ballMeasure (x : E) (r : ℝ) : Measure E :=
  volume.restrict (Metric.ball x r)

noncomputable def moserDyadicEssSup
    (u : E → ℝ) (x : E) (n : ℕ) : ℝ :=
  essSup u (ballMeasure x (moserDyadicRadius n))

noncomputable def moserDyadicEssInf
    (u : E → ℝ) (x : E) (n : ℕ) : ℝ :=
  essInf u (ballMeasure x (moserDyadicRadius n))

noncomputable def moserHolderNorm
    (A : NormalizedEllipticCoeff d (Metric.ball (0 : E) 1))
    (u : E → ℝ) (p₀ : ℝ) : ℝ :=
  A.1.Λ ^ ((d : ℝ) / (2 * p₀)) *
    (p₀ / (p₀ - 1)) ^ ((d : ℝ) / p₀) *
    (∫ z in Metric.ball (0 : E) 1, |u z| ^ p₀ ∂volume) ^ ((1 : ℝ) / p₀)

noncomputable def localMoserPrefactor (p₀ : ℝ) : ℝ :=
  (C_Moser d * (2 : ℝ) ^ (d : ℝ)) ^ ((1 : ℝ) / p₀)

theorem le_of_forall_pos_add_bound {a b : ℝ}
    (h : ∀ ε > 0, a ≤ b + ε) :
    a ≤ b := by
  by_contra hab
  have hε : 0 < (a - b) / 2 := by linarith
  have hbad := h ((a - b) / 2) hε
  linarith

theorem moserDyadicRadius_pos (n : ℕ) :
    0 < moserDyadicRadius n := by
  unfold moserDyadicRadius
  positivity

theorem moserDyadicRadius_le_quarter (n : ℕ) :
    moserDyadicRadius n ≤ (1 / 4 : ℝ) := by
  unfold moserDyadicRadius
  exact div_le_self (by positivity) (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))

theorem moserDyadicRadius_succ (n : ℕ) :
    moserDyadicRadius (n + 1) = moserDyadicRadius n / 2 := by
  unfold moserDyadicRadius
  rw [pow_succ]
  ring

theorem moserDyadicRadius_eq_half_pow (n : ℕ) :
    moserDyadicRadius n = (1 / 4 : ℝ) * (1 / 2 : ℝ) ^ n := by
  simp [moserDyadicRadius, div_eq_mul_inv, inv_pow]

theorem one_le_localMoserPrefactor_base :
    1 ≤ C_Moser d * (2 : ℝ) ^ (d : ℝ) := by
  have hpow : 1 ≤ (2 : ℝ) ^ (d : ℝ) := by
    exact Real.one_le_rpow (by norm_num) (by positivity)
  exact one_le_mul_of_one_le_of_one_le (one_le_C_Moser (d := d)) hpow

theorem localMoserPrefactor_le_holderConstant
    {p₀ : ℝ} (hp₀ : 1 < p₀) :
    localMoserPrefactor (d := d) p₀ ≤ C_holder_Moser d / 64 := by
  let B : ℝ := C_Moser d * (2 : ℝ) ^ (d : ℝ)
  have hp₀_pos : 0 < p₀ := lt_trans zero_lt_one hp₀
  have hB_one : 1 ≤ B := one_le_localMoserPrefactor_base (d := d)
  have hroot_le : B ^ ((1 : ℝ) / p₀) ≤ B := by
    refine Real.rpow_le_self_of_one_le hB_one ?_
    have hp₀_ge : 1 ≤ p₀ := le_of_lt hp₀
    have hp₀_ne : p₀ ≠ 0 := hp₀_pos.ne'
    field_simp [hp₀_ne]
    linarith
  have hB_nonneg : 0 ≤ B := by
    exact le_trans (by norm_num : (0 : ℝ) ≤ 1) hB_one
  have hB_le : B ≤ C_holder_Moser d / 64 := by
    unfold C_holder_Moser B
    have hlocal_nonneg : 0 ≤ C_Moser d * (((d : ℝ) - 1) ^ (d : ℝ)) * ((4 : ℝ) ^ (d : ℝ)) := by
      exact localMoserBase_nonneg (d := d)
    have hweak_nonneg : 0 ≤ C_weakHarnack_of d * (d : ℝ) ^ (d : ℝ) := by
      refine mul_nonneg ?_ ?_
      · exact le_trans (by norm_num : (0 : ℝ) ≤ 1) (one_le_C_weakHarnack_of (d := d))
      · exact Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ d) _
    nlinarith [abs_nonneg (C_harnack d), hlocal_nonneg, hB_nonneg, hweak_nonneg]
  simpa [localMoserPrefactor, B] using hroot_le.trans hB_le

theorem moserHolderNorm_nonneg
    (A : NormalizedEllipticCoeff d (Metric.ball (0 : E) 1))
    {u : E → ℝ} {p₀ : ℝ} (hp₀ : 1 < p₀) :
    0 ≤ moserHolderNorm A u p₀ := by
  have hp₀_pos : 0 < p₀ := lt_trans zero_lt_one hp₀
  have hden_pos : 0 < p₀ - 1 := by
    linarith
  unfold moserHolderNorm
  refine mul_nonneg (mul_nonneg ?_ ?_) ?_
  · exact Real.rpow_nonneg A.1.Λ_nonneg _
  · have hratio_nonneg : 0 ≤ p₀ / (p₀ - 1) := by
      exact div_nonneg hp₀_pos.le hden_pos.le
    exact Real.rpow_nonneg hratio_nonneg _
  · refine Real.rpow_nonneg ?_ _
    refine integral_nonneg ?_
    intro z
    exact Real.rpow_nonneg (abs_nonneg _) _

omit [NeZero d] in
theorem ball_half_subset_unitBall
    {x : E} (hx : x ∈ Metric.ball (0 : E) (1 / 2 : ℝ)) :
    Metric.ball x (1 / 2 : ℝ) ⊆ Metric.ball (0 : E) 1 := by
  intro y hy
  refine Metric.mem_ball.2 ?_
  have hx' : dist x (0 : E) < 1 / 2 := by simpa using hx
  have hy' : dist y x < 1 / 2 := by simpa using hy
  calc
    dist y (0 : E) ≤ dist y x + dist x (0 : E) := dist_triangle _ _ _
    _ < 1 / 2 + 1 / 2 := by linarith
    _ = 1 := by norm_num

omit [NeZero d] in
theorem closedBall_quarter_subset_unitBall
    {x : E} (hx : x ∈ Metric.ball (0 : E) (1 / 2 : ℝ)) :
    Metric.closedBall x (1 / 4 : ℝ) ⊆ Metric.ball (0 : E) 1 := by
  intro y hy
  refine Metric.mem_ball.2 ?_
  have hx' : dist x (0 : E) < 1 / 2 := by simpa using hx
  have hy' : dist y x ≤ 1 / 4 := by simpa using hy
  calc
    dist y (0 : E) ≤ dist y x + dist x (0 : E) := dist_triangle _ _ _
    _ < 1 / 4 + 1 / 2 := by linarith
    _ = 3 / 4 := by norm_num
    _ < 1 := by norm_num

omit [NeZero d] in
theorem closedBall_half_subset_unitBall
    {x : E} (hx : x ∈ Metric.ball (0 : E) (1 / 2 : ℝ)) :
    Metric.closedBall x (1 / 2 : ℝ) ⊆ Metric.ball (0 : E) 1 := by
  intro y hy
  refine Metric.mem_ball.2 ?_
  have hx' : dist x (0 : E) < 1 / 2 := by simpa using hx
  have hy' : dist y x ≤ 1 / 2 := by simpa using hy
  calc
    dist y (0 : E) ≤ dist y x + dist x (0 : E) := dist_triangle _ _ _
    _ < 1 / 2 + 1 / 2 := by linarith
    _ = 1 := by norm_num

theorem harnack_on_ball
    (hd : 2 < (d : ℝ))
    {x₀ : E} {R : ℝ} (hR : 0 < R)
    (A : NormalizedEllipticCoeff d (Metric.ball x₀ R))
    {u : E → ℝ}
    (hu_pos : ∀ x ∈ Metric.ball x₀ R, 0 < u x)
    (hsol : IsSolution A.1 u) :
    essSup u (ballMeasure x₀ (R / 2 : ℝ)) ≤
      Real.exp (C_harnack d * A.1.Λ ^ ((1 : ℝ) / 2)) *
        essInf u (ballMeasure x₀ (R / 2 : ℝ)) := by
  let uR : E → ℝ := rescaleToUnitBall (d := d) (x₀ := x₀) (R := R) u
  let AR : NormalizedEllipticCoeff d (Metric.ball (0 : E) 1) :=
    rescaleNormalizedCoeffToUnitBall (d := d) (x₀ := x₀) (R := R) hR A
  have hu_posR : ∀ z ∈ Metric.ball (0 : E) 1, 0 < uR z := by
    intro z hz
    have hz_ball :
        x₀ + R • z ∈ Metric.ball x₀ R := by
      have hz' :
          z ∈ (fun y : E => x₀ + R • y) ⁻¹' Metric.ball x₀ (R * (1 : ℝ)) := by
        rw [affine_preimage_ball_mul (d := d) (x₀ := x₀) (R := R) (ρ := (1 : ℝ)) hR]
        exact hz
      simpa using hz'
    exact hu_pos (x₀ + R • z) hz_ball
  have hsolR : IsSolution AR.1 uR := by
    change IsSolution
      (rescaleCoeffToUnitBall (d := d) (x₀ := x₀) (R := R) hR A.1)
      (rescaleToUnitBall (d := d) (x₀ := x₀) (R := R) u)
    exact rescaleToUnitBall_isSolution (d := d) (x₀ := x₀) (R := R) hR A.1 hsol
  have hbase := harnack (d := d) hd AR hu_posR hsolR
  change
    essSup (fun z : E => u (x₀ + R • z))
        (volume.restrict (Metric.ball (0 : E) (1 / 2 : ℝ))) ≤
      Real.exp (C_harnack d * A.1.Λ ^ ((1 : ℝ) / 2)) *
        essInf (fun z : E => u (x₀ + R • z))
          (volume.restrict (Metric.ball (0 : E) (1 / 2 : ℝ))) at hbase
  rw [essSup_rescale_halfBall (d := d) (x₀ := x₀) (R := R) hR,
    essInf_rescale_halfBall (d := d) (x₀ := x₀) (R := R) hR] at hbase
  simpa [ballMeasure] using hbase

noncomputable def positiveBallRepresentative
    (u : E → ℝ) (x₀ : E) (R δ : ℝ) : E → ℝ := by
  classical
  exact fun x =>
    if x ∈ Metric.ball x₀ R ∧ u x ≤ 0 then
      δ
    else
      u x

omit [NeZero d] in
theorem positiveBallRepresentative_ae_eq
    {x₀ : E} {R δ : ℝ} {u : E → ℝ}
    (hpos : ∀ᵐ x ∂ ballMeasure x₀ R, 0 < u x) :
    positiveBallRepresentative u x₀ R δ =ᵐ[ballMeasure x₀ R] u := by
  filter_upwards [hpos] with x hx
  by_cases hball : x ∈ Metric.ball x₀ R
  · have hux : ¬ u x ≤ 0 := by linarith
    simp [positiveBallRepresentative, hball, hux]
  · simp [positiveBallRepresentative, hball]

omit [NeZero d] in
theorem positiveBallRepresentative_pos
    {x₀ : E} {R δ : ℝ} {u : E → ℝ} (hδ : 0 < δ) :
    ∀ x ∈ Metric.ball x₀ R, 0 < positiveBallRepresentative u x₀ R δ x := by
  intro x hx
  by_cases hux : u x ≤ 0
  · simp [positiveBallRepresentative, hx, hux, hδ]
  · have hx_pos : 0 < u x := lt_of_not_ge hux
    simp [positiveBallRepresentative, hx, hux, hx_pos]

theorem harnack_on_ball_ae_pos
    (hd : 2 < (d : ℝ))
    {x₀ : E} {R : ℝ} (hR : 0 < R)
    (A : NormalizedEllipticCoeff d (Metric.ball x₀ R))
    {u : E → ℝ}
    (hu_pos : ∀ᵐ x ∂ ballMeasure x₀ R, 0 < u x)
    (hsol : IsSolution A.1 u) :
    essSup u (ballMeasure x₀ (R / 2 : ℝ)) ≤
      Real.exp (C_harnack d * A.1.Λ ^ ((1 : ℝ) / 2)) *
        essInf u (ballMeasure x₀ (R / 2 : ℝ)) := by
  let v : E → ℝ := positiveBallRepresentative u x₀ R 1
  have hv_ae_ball : v =ᵐ[ballMeasure x₀ R] u :=
    positiveBallRepresentative_ae_eq (x₀ := x₀) (R := R) (δ := 1) hu_pos
  have hv_pos : ∀ x ∈ Metric.ball x₀ R, 0 < v x :=
    positiveBallRepresentative_pos (x₀ := x₀) (R := R) (δ := 1) zero_lt_one
  have hv_sol : IsSolution A.1 v := hsol.congr_ae hv_ae_ball.symm
  have hhalf_sub : Metric.ball x₀ (R / 2 : ℝ) ⊆ Metric.ball x₀ R := by
    exact Metric.ball_subset_ball (by linarith)
  have hv_ae_half : v =ᵐ[ballMeasure x₀ (R / 2 : ℝ)] u :=
    ae_restrict_of_ae_restrict_of_subset hhalf_sub hv_ae_ball
  have hbase := harnack_on_ball (d := d) hd hR A hv_pos hv_sol
  rw [essSup_congr_ae hv_ae_half, essInf_congr_ae hv_ae_half] at hbase
  exact hbase

theorem solution_aestronglyMeasurable_on
    (A : NormalizedEllipticCoeff d (Metric.ball (0 : E) 1))
    {u : E → ℝ} (hsol : IsSolution A.1 u)
    {s : Set E} (hs : s ⊆ Metric.ball (0 : E) 1) :
    AEStronglyMeasurable u (volume.restrict s) := by
  let hu : MemW1pWitness 2 u (Metric.ball (0 : E) 1) := MemW1p.someWitness hsol.1.1
  exact (hu.memLp.mono_measure (Measure.restrict_mono hs le_rfl)).aestronglyMeasurable

omit [NeZero d] in
theorem abs_posPart_rpow_le_abs_rpow
    {u : E → ℝ} {p₀ : ℝ} (hp₀ : 0 < p₀) (x : E) :
    |max (u x) 0| ^ p₀ ≤ |u x| ^ p₀ := by
  have hmax_le : |max (u x) 0| ≤ |u x| := by
    by_cases hux : 0 ≤ u x
    · simp [max_eq_left hux, abs_of_nonneg hux]
    · simp [max_eq_right (le_of_not_ge hux)]
  exact Real.rpow_le_rpow (abs_nonneg _) hmax_le hp₀.le

omit [NeZero d] in
theorem integrableOn_posPart_pow_of_integrableOn_abs_pow
    {s : Set E} {u : E → ℝ} {p₀ : ℝ} (hp₀ : 0 < p₀)
    (hu_aesm : AEStronglyMeasurable u (volume.restrict s))
    (hInt : IntegrableOn (fun z => |u z| ^ p₀) s volume) :
    IntegrableOn (fun z => |max (u z) 0| ^ p₀) s volume := by
  rw [IntegrableOn] at hInt ⊢
  refine Integrable.mono' hInt ?_ ?_
  · exact
      (continuous_id.rpow_const (fun x : ℝ => Or.inr hp₀.le)).comp_aestronglyMeasurable <|
        (continuous_max.comp_aestronglyMeasurable (hu_aesm.prodMk aestronglyMeasurable_const)).norm
  · filter_upwards with x
    simpa [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)] using
      abs_posPart_rpow_le_abs_rpow (u := u) hp₀ x

omit [NeZero d] in
theorem halfBallVolumeFactor_eq :
    ((1 / 2 : ℝ) ^ Module.finrank ℝ E)⁻¹ = (2 : ℝ) ^ (d : ℝ) := by
  have h₁ : (2 : ℝ) ^ Module.finrank ℝ E = (2 : ℝ) ^ (d : ℝ) := by
    simp [AmbientSpace, Real.rpow_natCast]
  rw [show (1 / 2 : ℝ) = ((2 : ℝ)⁻¹) by norm_num, inv_pow, h₁]
  simp

theorem localMoserBoundPow_eq
    (A : NormalizedEllipticCoeff d (Metric.ball (0 : E) 1))
    {u : E → ℝ} {p₀ : ℝ} (hp₀ : 1 < p₀) :
    (localMoserPrefactor (d := d) p₀ * moserHolderNorm A u p₀) ^ p₀ =
      C_Moser d * (2 : ℝ) ^ (d : ℝ) *
        A.1.Λ ^ ((d : ℝ) / 2) *
        (p₀ / (p₀ - 1)) ^ (d : ℝ) *
        (∫ z in Metric.ball (0 : E) 1, |u z| ^ p₀ ∂volume) := by
  let B : ℝ := C_Moser d * (2 : ℝ) ^ (d : ℝ)
  let L : ℝ := A.1.Λ ^ ((d : ℝ) / (2 * p₀))
  let P : ℝ := (p₀ / (p₀ - 1)) ^ ((d : ℝ) / p₀)
  let I : ℝ := ∫ z in Metric.ball (0 : E) 1, |u z| ^ p₀ ∂volume
  have hp₀_pos : 0 < p₀ := lt_trans zero_lt_one hp₀
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    refine mul_nonneg ?_ ?_
    · exact le_trans (by norm_num : (0 : ℝ) ≤ 1) (one_le_C_Moser (d := d))
    · exact Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _
  have hL_nonneg : 0 ≤ L := by
    dsimp [L]
    exact Real.rpow_nonneg A.1.Λ_nonneg _
  have hratio_nonneg : 0 ≤ p₀ / (p₀ - 1) := by
    have hden_pos : 0 < p₀ - 1 := by
      linarith
    exact div_nonneg hp₀_pos.le hden_pos.le
  have hP_nonneg : 0 ≤ P := by
    dsimp [P]
    exact Real.rpow_nonneg hratio_nonneg _
  have hI_nonneg : 0 ≤ I := by
    dsimp [I]
    refine integral_nonneg ?_
    intro z
    exact Real.rpow_nonneg (abs_nonneg _) _
  have hBpow : (B ^ ((1 : ℝ) / p₀)) ^ p₀ = B := by
    rw [← Real.rpow_mul hB_nonneg]
    have hmul : ((1 : ℝ) / p₀) * p₀ = 1 := by
      field_simp [hp₀_pos.ne']
    rw [hmul, Real.rpow_one]
  have hLpow : L ^ p₀ = A.1.Λ ^ ((d : ℝ) / 2) := by
    dsimp [L]
    rw [← Real.rpow_mul A.1.Λ_nonneg]
    have hmul : ((d : ℝ) / (2 * p₀)) * p₀ = (d : ℝ) / 2 := by
      field_simp [hp₀_pos.ne']
    rw [hmul]
  have hPpow : P ^ p₀ = (p₀ / (p₀ - 1)) ^ (d : ℝ) := by
    dsimp [P]
    rw [← Real.rpow_mul hratio_nonneg]
    have hmul : ((d : ℝ) / p₀) * p₀ = (d : ℝ) := by
      field_simp [hp₀_pos.ne']
    rw [hmul]
  have hIpow : (I ^ ((1 : ℝ) / p₀)) ^ p₀ = I := by
    rw [← Real.rpow_mul hI_nonneg]
    have hmul : ((1 : ℝ) / p₀) * p₀ = 1 := by
      field_simp [hp₀_pos.ne']
    rw [hmul, Real.rpow_one]
  calc
    (localMoserPrefactor (d := d) p₀ * moserHolderNorm A u p₀) ^ p₀
        = ((B ^ ((1 : ℝ) / p₀)) * ((L * P) * I ^ ((1 : ℝ) / p₀))) ^ p₀ := by
            simp [localMoserPrefactor, moserHolderNorm, B, L, P, I,
              mul_assoc, mul_left_comm, mul_comm]
    _ = (B ^ ((1 : ℝ) / p₀)) ^ p₀ * (((L * P) * I ^ ((1 : ℝ) / p₀)) ^ p₀) := by
          rw [Real.mul_rpow (Real.rpow_nonneg hB_nonneg _)
            (mul_nonneg (mul_nonneg hL_nonneg hP_nonneg) (Real.rpow_nonneg hI_nonneg _))]
    _ = B * (((L * P) * I ^ ((1 : ℝ) / p₀)) ^ p₀) := by
          rw [hBpow]
    _ = B * ((L * P) ^ p₀ * (I ^ ((1 : ℝ) / p₀)) ^ p₀) := by
          rw [Real.mul_rpow (mul_nonneg hL_nonneg hP_nonneg) (Real.rpow_nonneg hI_nonneg _)]
    _ = B * (L ^ p₀ * P ^ p₀ * (I ^ ((1 : ℝ) / p₀)) ^ p₀) := by
          rw [Real.mul_rpow hL_nonneg hP_nonneg]
    _ = B * (A.1.Λ ^ ((d : ℝ) / 2) * (p₀ / (p₀ - 1)) ^ (d : ℝ) * I) := by
          rw [hLpow, hPpow, hIpow]
    _ = C_Moser d * (2 : ℝ) ^ (d : ℝ) *
          A.1.Λ ^ ((d : ℝ) / 2) *
          (p₀ / (p₀ - 1)) ^ (d : ℝ) *
          (∫ z in Metric.ball (0 : E) 1, |u z| ^ p₀ ∂volume) := by
          simp [B, I, mul_assoc, mul_left_comm, mul_comm]

omit [NeZero d] in
theorem posPartIntegral_le_absIntegral
    {s : Set E} {u : E → ℝ} {p₀ : ℝ} (hp₀ : 1 < p₀)
    (hu_aesm : AEStronglyMeasurable u (volume.restrict s))
    (hInt : IntegrableOn (fun z => |u z| ^ p₀) s volume) :
    ∫ z in s, |max (u z) 0| ^ p₀ ∂volume ≤
      ∫ z in s, |u z| ^ p₀ ∂volume := by
  have hleft :
      IntegrableOn (fun z => |max (u z) 0| ^ p₀) s volume :=
    integrableOn_posPart_pow_of_integrableOn_abs_pow
      (u := u) (s := s) (p₀ := p₀) (lt_trans zero_lt_one hp₀) hu_aesm hInt
  have hmono :
      ∀ᵐ z ∂ volume.restrict s, |max (u z) 0| ^ p₀ ≤ |u z| ^ p₀ := by
    filter_upwards with z
    exact abs_posPart_rpow_le_abs_rpow (u := u) (lt_trans zero_lt_one hp₀) z
  exact integral_mono_ae hleft hInt hmono

theorem ae_posPart_le_localMoserBound_on_quarterBall
    (hd : 2 < (d : ℝ))
    (A : NormalizedEllipticCoeff d (Metric.ball (0 : E) 1))
    {u : E → ℝ} {p₀ : ℝ} (hp₀ : 1 < p₀)
    (hsol : IsSolution A.1 u)
    (hInt : IntegrableOn (fun z => |u z| ^ p₀) (Metric.ball (0 : E) 1) volume)
    {x : E} (hx : x ∈ Metric.ball (0 : E) (1 / 2 : ℝ)) :
    ∀ᵐ z ∂ ballMeasure x (1 / 4 : ℝ),
      max (u z) 0 ≤ localMoserPrefactor (d := d) p₀ * moserHolderNorm A u p₀ := by
  have hhalf_closed : Metric.closedBall x (1 / 2 : ℝ) ⊆ Metric.ball (0 : E) 1 :=
    closedBall_half_subset_unitBall (d := d) hx
  have hhalf_ball : Metric.ball x (1 / 2 : ℝ) ⊆ Metric.ball (0 : E) 1 :=
    Metric.ball_subset_closedBall.trans hhalf_closed
  let Ahalf : NormalizedEllipticCoeff d (Metric.ball x (1 / 2 : ℝ)) :=
    NormalizedEllipticCoeff.restrict A hhalf_ball
  have hsubHalf : IsSubsolution Ahalf.1 u := by
    change IsSubsolution ((A.1).restrict (Metric.ball_subset_closedBall.trans hhalf_closed)) u
    exact hsol.1.restrict_ball (d := d) Metric.isOpen_ball (by norm_num) hhalf_closed
  have hu_aesm_half :
      AEStronglyMeasurable u (volume.restrict (Metric.ball x (1 / 2 : ℝ))) := by
    exact solution_aestronglyMeasurable_on (d := d) A hsol hhalf_ball
  have hInt_half_abs :
      IntegrableOn (fun z => |u z| ^ p₀) (Metric.ball x (1 / 2 : ℝ)) volume := by
    exact hInt.mono_set hhalf_ball
  have hInt_half_pos :
      IntegrableOn (fun z => |max (u z) 0| ^ p₀) (Metric.ball x (1 / 2 : ℝ)) volume := by
    exact integrableOn_posPart_pow_of_integrableOn_abs_pow
      (u := u) (s := Metric.ball x (1 / 2 : ℝ))
      (p₀ := p₀) (lt_trans zero_lt_one hp₀) hu_aesm_half hInt_half_abs
  have hlinfty_raw :=
    linfty_subsolution_Moser_on_ball (d := d) hd
      (x₀ := x) (R := (1 / 2 : ℝ)) (by norm_num)
      Ahalf (p₀ := p₀) hp₀ hsubHalf hInt_half_pos
  have hlinfty :
      ∀ᵐ z ∂ ballMeasure x (1 / 4 : ℝ),
        |max (u z) 0| ^ p₀ ≤
          C_Moser d * A.1.Λ ^ ((d : ℝ) / 2) *
            (p₀ / (p₀ - 1)) ^ (d : ℝ) *
            (((1 / 2 : ℝ) ^ Module.finrank ℝ E)⁻¹ *
              ∫ z in Metric.ball x (1 / 2 : ℝ), |max (u z) 0| ^ p₀ ∂volume) := by
    convert hlinfty_raw using 1
    · simp [ballMeasure, div_eq_mul_inv]
      norm_num
  have hhalf_pos_le_abs :
      ∫ z in Metric.ball x (1 / 2 : ℝ), |max (u z) 0| ^ p₀ ∂volume ≤
        ∫ z in Metric.ball x (1 / 2 : ℝ), |u z| ^ p₀ ∂volume := by
    exact posPartIntegral_le_absIntegral
      (u := u) (s := Metric.ball x (1 / 2 : ℝ)) (p₀ := p₀) hp₀ hu_aesm_half hInt_half_abs
  have hhalf_abs_le :
      ∫ z in Metric.ball x (1 / 2 : ℝ), |u z| ^ p₀ ∂volume ≤
        ∫ z in Metric.ball (0 : E) 1, |u z| ^ p₀ ∂volume := by
    exact setIntegral_mono_set hInt
      (ae_of_all _ (by intro z; exact Real.rpow_nonneg (abs_nonneg _) _))
      (ae_of_all _ hhalf_ball)
  have hcoeff_nonneg :
      0 ≤ C_Moser d * A.1.Λ ^ ((d : ℝ) / 2) * (p₀ / (p₀ - 1)) ^ (d : ℝ) := by
    refine mul_nonneg (mul_nonneg ?_ ?_) ?_
    · exact le_trans (by norm_num : (0 : ℝ) ≤ 1) (one_le_C_Moser (d := d))
    · exact Real.rpow_nonneg A.1.Λ_nonneg _
    · have hp₀_pos : 0 < p₀ := lt_trans zero_lt_one hp₀
      have hden_pos : 0 < p₀ - 1 := by
        linarith
      have hratio_nonneg : 0 ≤ p₀ / (p₀ - 1) := by
        exact div_nonneg hp₀_pos.le hden_pos.le
      exact Real.rpow_nonneg hratio_nonneg _
  have hscale_nonneg : 0 ≤ (2 : ℝ) ^ (d : ℝ) := by
    exact Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _
  have hrhs_le :
      C_Moser d * A.1.Λ ^ ((d : ℝ) / 2) *
          (p₀ / (p₀ - 1)) ^ (d : ℝ) *
          (((1 / 2 : ℝ) ^ Module.finrank ℝ E)⁻¹ *
            ∫ z in Metric.ball x (1 / 2 : ℝ), |max (u z) 0| ^ p₀ ∂volume) ≤
        (localMoserPrefactor (d := d) p₀ * moserHolderNorm A u p₀) ^ p₀ := by
    rw [halfBallVolumeFactor_eq, localMoserBoundPow_eq (d := d) (A := A) (u := u) hp₀]
    have hint_le :
        (2 : ℝ) ^ (d : ℝ) *
            ∫ z in Metric.ball x (1 / 2 : ℝ), |max (u z) 0| ^ p₀ ∂volume ≤
          (2 : ℝ) ^ (d : ℝ) *
            ∫ z in Metric.ball (0 : E) 1, |u z| ^ p₀ ∂volume := by
      exact mul_le_mul_of_nonneg_left (le_trans hhalf_pos_le_abs hhalf_abs_le) hscale_nonneg
    exact
      by
        simpa [mul_assoc, mul_left_comm, mul_comm] using
          (mul_le_mul_of_nonneg_left hint_le hcoeff_nonneg)
  filter_upwards [hlinfty] with z hz
  have hz_nonneg : 0 ≤ max (u z) 0 := le_max_right _ _
  have hp₀_pos : 0 < p₀ := lt_trans zero_lt_one hp₀
  have hpref_nonneg : 0 ≤ localMoserPrefactor (d := d) p₀ := by
    unfold localMoserPrefactor
    refine Real.rpow_nonneg ?_ _
    refine mul_nonneg ?_ ?_
    · exact le_trans (by norm_num : (0 : ℝ) ≤ 1) (one_le_C_Moser (d := d))
    · exact Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _
  have hbound_nonneg :
      0 ≤ localMoserPrefactor (d := d) p₀ * moserHolderNorm A u p₀ := by
    exact mul_nonneg hpref_nonneg (moserHolderNorm_nonneg (d := d) A hp₀)
  have hpow_le :
      (max (u z) 0) ^ p₀ ≤
        (localMoserPrefactor (d := d) p₀ * moserHolderNorm A u p₀) ^ p₀ := by
    simpa [abs_of_nonneg hz_nonneg] using le_trans hz hrhs_le
  exact (Real.rpow_le_rpow_iff hz_nonneg hbound_nonneg hp₀_pos).1 hpow_le


theorem ae_abs_le_moserHolderNorm_on_quarterBall
    (hd : 2 < (d : ℝ))
    (A : NormalizedEllipticCoeff d (Metric.ball (0 : E) 1))
    {u : E → ℝ} {p₀ : ℝ} (hp₀ : 1 < p₀)
    (hsol : IsSolution A.1 u)
    (hInt : IntegrableOn (fun z => |u z| ^ p₀) (Metric.ball (0 : E) 1) volume)
    {x : E} (hx : x ∈ Metric.ball (0 : E) (1 / 2 : ℝ)) :
    ∀ᵐ z ∂ ballMeasure x (1 / 4 : ℝ),
      |u z| ≤ (C_holder_Moser d / 64) * moserHolderNorm A u p₀ := by
  have hpos :
      ∀ᵐ z ∂ ballMeasure x (1 / 4 : ℝ),
        max (u z) 0 ≤ localMoserPrefactor (d := d) p₀ * moserHolderNorm A u p₀ :=
    ae_posPart_le_localMoserBound_on_quarterBall
      (d := d) hd A hp₀ hsol hInt hx
  have hnegsol : IsSolution A.1 (fun z => -u z) := by
    simpa using hsol.neg_ball (d := d) (c := (0 : E)) (r := 1) (by norm_num)
  have hnegInt :
      IntegrableOn (fun z => |(-u z)| ^ p₀) (Metric.ball (0 : E) 1) volume := by
    simpa using hInt
  have hneg :
      ∀ᵐ z ∂ ballMeasure x (1 / 4 : ℝ),
        max (-u z) 0 ≤ localMoserPrefactor (d := d) p₀ * moserHolderNorm A u p₀ := by
    simpa [moserHolderNorm, mul_assoc, mul_left_comm, mul_comm] using
      (ae_posPart_le_localMoserBound_on_quarterBall
        (d := d) hd A (u := fun z => -u z) (p₀ := p₀) hp₀ hnegsol hnegInt hx)
  have hbound_nonneg :
      0 ≤ localMoserPrefactor (d := d) p₀ * moserHolderNorm A u p₀ := by
    have hpref_nonneg : 0 ≤ localMoserPrefactor (d := d) p₀ := by
      unfold localMoserPrefactor
      refine Real.rpow_nonneg ?_ _
      refine mul_nonneg ?_ ?_
      · exact le_trans (by norm_num : (0 : ℝ) ≤ 1) (one_le_C_Moser (d := d))
      · exact Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _
    exact mul_nonneg hpref_nonneg (moserHolderNorm_nonneg (d := d) A hp₀)
  have hpref_le :
      localMoserPrefactor (d := d) p₀ * moserHolderNorm A u p₀ ≤
        (C_holder_Moser d / 64) * moserHolderNorm A u p₀ := by
    exact mul_le_mul_of_nonneg_right
      (localMoserPrefactor_le_holderConstant (d := d) (p₀ := p₀) hp₀)
      (moserHolderNorm_nonneg (d := d) A hp₀)
  filter_upwards [hpos, hneg] with z hz_pos hz_neg
  have hz_upper :
      u z ≤ localMoserPrefactor (d := d) p₀ * moserHolderNorm A u p₀ := by
    exact le_trans (le_max_left _ _) hz_pos
  have hz_lower :
      -(localMoserPrefactor (d := d) p₀ * moserHolderNorm A u p₀) ≤ u z := by
    have hneg_upper : -u z ≤ localMoserPrefactor (d := d) p₀ * moserHolderNorm A u p₀ := by
      exact le_trans (le_max_left _ _) hz_neg
    linarith
  have habs :
      |u z| ≤ localMoserPrefactor (d := d) p₀ * moserHolderNorm A u p₀ := by
    exact abs_le.mpr ⟨hz_lower, hz_upper⟩
  exact le_trans habs hpref_le


end DeGiorgi
