import DeGiorgi.Supersolutions.ForwardIteration
import DeGiorgi.Supersolutions.InverseIteration

/-!
# Supersolutions Stage-One Theorems

This module contains the two stage-one weak Harnack theorems for positive
supersolutions, assembled from the inverse and forward iteration layers.
-/

noncomputable section

open MeasureTheory Metric

namespace DeGiorgi

variable {d : ℕ} [NeZero d]

local notation "E" => AmbientSpace d
local notation "μhalf" => (volume.restrict (Metric.ball (0 : E) (1 / 2 : ℝ)))

/-! ### Main theorems -/

set_option maxHeartbeats 5000000 in
/-- First stage of weak Harnack: inverse-power iteration for positive
supersolutions.

For `u > 0` a supersolution on `B₁` and every `p₀ > 0`:
```
(Λ p₀² + 1)^{-d/2} · (∫_{B₁} |u⁻¹|^{p₀})⁻¹ ≤ C · (inf_{B_{1/2}} u)^{p₀}
```
Proof: the Moser iteration (Steps 1-2 above) gives an a.e. `L^∞` bound on
`u⁻¹` over `B_{1/2}`. Since `u > 0` pointwise, this converts to a lower
bound on `inf u`, which we rearrange to get the stated inequality. -/
theorem weak_harnack_stage_one_inverse
    (hd : 2 < (d : ℝ))
    (A : NormalizedEllipticCoeff d (Metric.ball (0 : E) 1))
    {u : E → ℝ} {p₀ : ℝ} (hp₀ : 0 < p₀)
    (hu_pos : ∀ x ∈ Metric.ball (0 : E) 1, 0 < u x)
    (hsuper : IsSupersolution A.1 u) :
    (A.1.Λ * p₀ ^ 2 + 1) ^ (-(d : ℝ) / 2) *
        (∫ x in Metric.ball (0 : E) 1, |(u x)⁻¹| ^ p₀ ∂volume)⁻¹ ≤
      C_weakHarnack0 d *
        (essInf u μhalf) ^ p₀ := by
  let I : ℝ := ∫ x in Metric.ball (0 : E) 1, |(u x)⁻¹| ^ p₀ ∂volume
  let L : ℝ := A.1.Λ * p₀ ^ 2 + 1
  have hC_nonneg : 0 ≤ C_weakHarnack0 d := by
    exact le_trans (by norm_num : (0 : ℝ) ≤ 1) (one_le_C_weakHarnack0 (d := d))
  have hL_pos : 0 < L := by
    dsimp [L]
    nlinarith [A.1.Λ_nonneg, sq_nonneg p₀]
  have hL_nonneg : 0 ≤ L := hL_pos.le
  have hhalf_nonneg : ∀ᵐ x ∂μhalf, 0 ≤ u x := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    exact (hu_pos x ((Metric.ball_subset_ball (by norm_num : (1 / 2 : ℝ) ≤ 1)) hx)).le
  have hessInf_nonneg : 0 ≤ essInf u μhalf := by
    exact
      le_essInf_real_of_ae_le
        (d := d)
        (restrict_ball_ne_zero (c := (0 : E)) (r := (1 / 2 : ℝ)) (by norm_num))
        hhalf_nonneg
  by_cases hpInt : IntegrableOn (fun x => |(u x)⁻¹| ^ p₀) (Metric.ball (0 : E) 1) volume
  · let c0 : ℝ := C_weakHarnack0 d * L ^ ((d : ℝ) / 2) * I
    have hI_nonneg : 0 ≤ I := by
      dsimp [I]
      exact integral_nonneg fun x => by positivity
    have hI_pos : 0 < I := by
      have hnonneg :
          0 ≤ᵐ[volume.restrict (Metric.ball (0 : E) 1)] fun x => |(u x)⁻¹| ^ p₀ := by
        filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
        positivity
      have hI_ne_zero : I ≠ 0 := by
        intro hI_zero
        have hzero_ae :
            (fun x => |(u x)⁻¹| ^ p₀) =ᵐ[volume.restrict (Metric.ball (0 : E) 1)] 0 := by
          rw [← sub_eq_zero] at hI_zero
          rwa [sub_zero, setIntegral_eq_zero_iff_of_nonneg_ae hnonneg hpInt] at hI_zero
        have hpos_ae :
            ∀ᵐ x ∂(volume.restrict (Metric.ball (0 : E) 1)), |(u x)⁻¹| ^ p₀ ≠ 0 := by
          filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
          have hux_pos : 0 < u x := hu_pos x hx
          have hpow_pos : 0 < |(u x)⁻¹| ^ p₀ := by
            rw [abs_of_pos (inv_pos.mpr hux_pos)]
            exact Real.rpow_pos_of_pos (inv_pos.mpr hux_pos) p₀
          exact hpow_pos.ne'
        have hfalse : ∀ᵐ x ∂(volume.restrict (Metric.ball (0 : E) 1)), False := by
          filter_upwards [hzero_ae, hpos_ae] with x hx0 hxpos
          exact hxpos hx0
        rw [ae_iff] at hfalse
        have hball_zero : volume (Metric.ball (0 : E) 1) = 0 := by
          simpa [Measure.restrict_apply_univ] using hfalse
        exact (Metric.measure_ball_pos volume (0 : E) (by norm_num : (0 : ℝ) < 1)).ne'
          hball_zero
      exact lt_of_le_of_ne hI_nonneg (Ne.symm hI_ne_zero)
    have hc0_pos : 0 < c0 := by
      dsimp [c0]
      exact mul_pos (mul_pos (lt_of_lt_of_le zero_lt_one (one_le_C_weakHarnack0 (d := d)))
        (Real.rpow_pos_of_pos hL_pos _)) hI_pos
    have hc0_nonneg : 0 ≤ c0 := hc0_pos.le
    have hclose := supersolution_ae_closeout_inv (d := d) hd A hp₀ hu_pos hsuper hpInt
    have hroot_ae :
        ∀ᵐ x ∂μhalf, (c0⁻¹) ^ (1 / p₀) ≤ u x := by
      filter_upwards [hclose, ae_restrict_mem measurableSet_ball] with x hxclose hxhalf
      have hux_pos : 0 < u x := hu_pos x ((Metric.ball_subset_ball (by norm_num : (1 / 2 : ℝ) ≤ 1)) hxhalf)
      have hupow_pos : 0 < u x ^ p₀ := Real.rpow_pos_of_pos hux_pos p₀
      have hpow_inv : (u x ^ p₀)⁻¹ ≤ c0 := by
        calc
          (u x ^ p₀)⁻¹ = ((u x)⁻¹) ^ p₀ := by
            rw [Real.inv_rpow hux_pos.le]
          _ = |(u x)⁻¹| ^ p₀ := by
            rw [abs_of_pos (inv_pos.mpr hux_pos)]
          _ ≤ c0 := hxclose
      have hpow_lower : c0⁻¹ ≤ u x ^ p₀ := by
        have htmp :
            c0⁻¹ ≤ ((u x ^ p₀)⁻¹)⁻¹ := (inv_le_inv₀ hc0_pos (inv_pos.mpr hupow_pos)).2 hpow_inv
        simpa [hupow_pos.ne'] using htmp
      have hroot :=
        Real.rpow_le_rpow (inv_nonneg.mpr hc0_nonneg) hpow_lower (by positivity : 0 ≤ 1 / p₀)
      have hux_root : (u x ^ p₀) ^ (1 / p₀) = u x := by
        rw [← Real.rpow_mul hux_pos.le]
        field_simp [hp₀.ne']
        rw [Real.rpow_one]
      calc
        (c0⁻¹) ^ (1 / p₀) ≤ (u x ^ p₀) ^ (1 / p₀) := hroot
        _ = u x := hux_root
    have hc_le_ess : (c0⁻¹) ^ (1 / p₀) ≤ essInf u μhalf := by
      exact
        le_essInf_real_of_ae_le
          (d := d)
          (restrict_ball_ne_zero (c := (0 : E)) (r := (1 / 2 : ℝ)) (by norm_num))
          hroot_ae
    have hpow_ess :
        c0⁻¹ ≤ (essInf u μhalf) ^ p₀ := by
      have hpow :=
        Real.rpow_le_rpow
          (Real.rpow_nonneg (inv_nonneg.mpr hc0_nonneg) _)
          hc_le_ess hp₀.le
      have hleft : ((c0⁻¹) ^ (1 / p₀)) ^ p₀ = c0⁻¹ := by
        calc
          ((c0⁻¹) ^ (1 / p₀)) ^ p₀ = (c0⁻¹) ^ ((1 / p₀) * p₀) := by
            rw [← Real.rpow_mul (inv_nonneg.mpr hc0_nonneg)]
          _ = (c0⁻¹) ^ (1 : ℝ) := by
            congr 1
            field_simp [hp₀.ne']
          _ = c0⁻¹ := by rw [Real.rpow_one]
      calc
        c0⁻¹ = ((c0⁻¹) ^ (1 / p₀)) ^ p₀ := hleft.symm
        _ ≤ (essInf u μhalf) ^ p₀ := hpow
    have hC_pos : 0 < C_weakHarnack0 d :=
      lt_of_lt_of_le zero_lt_one (one_le_C_weakHarnack0 (d := d))
    have hLpow_ne : L ^ ((d : ℝ) / 2) ≠ 0 := (Real.rpow_pos_of_pos hL_pos _).ne'
    have hLneg : L ^ (-(d : ℝ) / 2) = (L ^ ((d : ℝ) / 2))⁻¹ := by
      rw [show (-(d : ℝ) / 2) = -((d : ℝ) / 2) by ring, Real.rpow_neg hL_pos.le]
    calc
      L ^ (-(d : ℝ) / 2) * I⁻¹
          = C_weakHarnack0 d * c0⁻¹ := by
              dsimp [c0]
              rw [hLneg]
              field_simp [hC_pos.ne', hLpow_ne, hI_pos.ne']
      _ ≤ C_weakHarnack0 d * (essInf u μhalf) ^ p₀ := by
            exact mul_le_mul_of_nonneg_left hpow_ess hC_nonneg
  · have hrhs_nonneg : 0 ≤ C_weakHarnack0 d * (essInf u μhalf) ^ p₀ := by
      exact mul_nonneg hC_nonneg (Real.rpow_nonneg hessInf_nonneg _)
    have hI_zero :
        ∫ x in Metric.ball (0 : E) 1, |(u x)⁻¹| ^ p₀ ∂volume = 0 := by
      simpa using (integral_undef hpInt :
        ∫ x in Metric.ball (0 : E) 1, |(u x)⁻¹| ^ p₀ ∂volume = 0)
    calc
      (A.1.Λ * p₀ ^ 2 + 1) ^ (-(d : ℝ) / 2) *
          (∫ x in Metric.ball (0 : E) 1, |(u x)⁻¹| ^ p₀ ∂volume)⁻¹
          = 0 := by rw [hI_zero]; simp
      _ ≤ C_weakHarnack0 d * (essInf u μhalf) ^ p₀ := hrhs_nonneg

private theorem superIterNormFwd_zero
    {u : E → ℝ} {p₀ : ℝ} :
    superIterNormFwd (d := d) (u := u) p₀ 0 =
      (∫ x in Metric.ball (0 : E) 1, |u x| ^ p₀ ∂volume) ^ (1 / p₀) := by
  simp [superIterNormFwd, superIterIntegralFwd, moserExponentSeq_zero, moserRadius_zero]

private theorem moserExponentSeq_forward_target_eq
    (hd : 2 < (d : ℝ))
    {q : ℝ} {m : ℕ} :
    moserExponentSeq d (q * (moserChi d)⁻¹ ^ m) (m + 1) = q * moserChi d := by
  rw [moserExponentSeq]
  have hχ_ne : moserChi d ≠ 0 := (moserChi_pos (d := d) hd).ne'
  have hχpow_ne : moserChi d ^ m ≠ 0 := pow_ne_zero m hχ_ne
  calc
    q * (moserChi d)⁻¹ ^ m * moserChi d ^ (m + 1)
        = q * ((moserChi d ^ m)⁻¹ * moserChi d ^ (m + 1)) := by
            rw [inv_pow]
            ring
    _ = q * moserChi d := by
          congr 1
          calc
            (moserChi d ^ m)⁻¹ * moserChi d ^ (m + 1)
                = (moserChi d ^ m)⁻¹ * (moserChi d ^ m * moserChi d) := by
                    rw [pow_succ]
            _ = moserChi d := by
                  field_simp [hχpow_ne]

private theorem superIterNormFwd_target
    (hd : 2 < (d : ℝ))
    {u : E → ℝ} {q : ℝ} {m : ℕ} :
    let p₀ := q * (moserChi d)⁻¹ ^ m
    superIterNormFwd (d := d) (u := u) p₀ (m + 1) =
      (∫ x in Metric.ball (0 : E) (moserRadius (m + 1)),
          |u x| ^ (q * moserChi d) ∂volume) ^ (1 / (q * moserChi d)) := by
  intro p₀
  rw [superIterNormFwd, superIterIntegralFwd,
    moserExponentSeq_forward_target_eq (d := d) hd (q := q) (m := m)]

private noncomputable def weakHarnackForwardUpgradeLHS
    (A : NormalizedEllipticCoeff d (Metric.ball (0 : E) 1))
    (u : E → ℝ) (p q p₀ : ℝ) : ℝ :=
  (((C_weakHarnack0 d *
        (A.1.Λ * p₀ ^ 2 / (1 - q) ^ 2 + 1) ^ ((d : ℝ) / 2)) ^
          (1 / p₀)) *
      (∫ x in Metric.ball (0 : E) 1, |u x| ^ p₀ ∂volume) ^
        (1 / p₀)) ^ p

private noncomputable def weakHarnackForwardUpgradeRHS
    (hd : 2 < (d : ℝ))
    (A : NormalizedEllipticCoeff d (Metric.ball (0 : E) 1))
    (u : E → ℝ) (p q : ℝ) : ℝ :=
  C_weakHarnack0Forward (d := d) hd *
    (A.1.Λ * p ^ 2 / (1 - q) ^ 2 + 1) ^ (((d : ℝ) * moserChi d) / 2) *
    ∫ x in Metric.ball (0 : E) 1, |u x| ^ p ∂volume

private theorem weak_harnack_stage_one_forward_power_upgrade
    (hd : 2 < (d : ℝ))
    (A : NormalizedEllipticCoeff d (Metric.ball (0 : E) 1))
    {u : E → ℝ} {p q p₀ : ℝ}
    (hp₀ : 0 < p₀) (hp : 0 < p)
    (hp1 : p < 1)
    (hp₀_lt_p : p₀ < p)
    (hp_le : p ≤ moserChi d * p₀)
    (_hq1 : q < 1)
    (hsuper : IsSupersolution A.1 u)
    (_hp₀Int :
      IntegrableOn (fun x => |u x| ^ p₀)
        (Metric.ball (0 : E) 1) volume) :
    weakHarnackForwardUpgradeLHS (d := d) A u p q p₀ ≤
      weakHarnackForwardUpgradeRHS (d := d) hd A u p q := by
  let μ : Measure E := volume.restrict (Metric.ball (0 : E) 1)
  haveI : IsFiniteMeasure μ := by
    dsimp [μ]
    rw [isFiniteMeasure_restrict]
    exact measure_ne_top_of_subset Metric.ball_subset_closedBall
      (isCompact_closedBall (0 : E) (1 : ℝ)).measure_lt_top.ne
  let hu : MemW1pWitness 2 u (Metric.ball (0 : E) 1) := hsuper.1.someWitness
  let V : ℝ := volume.real (Metric.ball (0 : E) 1)
  let χ : ℝ := moserChi d
  let X₀ : ℝ := A.1.Λ * p₀ ^ 2 / (1 - q) ^ 2 + 1
  let X : ℝ := A.1.Λ * p ^ 2 / (1 - q) ^ 2 + 1
  let β : ℝ := ((d : ℝ) * χ) / 2
  have hχ_pos : 0 < χ := by
    dsimp [χ]
    exact moserChi_pos (d := d) hd
  have hp₀_le_two : p₀ ≤ 2 := by linarith
  have hp_le_two : p ≤ 2 := by linarith
  have hu_memLp_p₀ : MemLp u (ENNReal.ofReal p₀) μ := by
    exact hu.memLp.mono_exponent <| by
      simpa using (ENNReal.ofReal_le_ofReal hp₀_le_two)
  have hu_memLp_p : MemLp u (ENNReal.ofReal p) μ := by
    exact hu.memLp.mono_exponent <| by
      simpa using (ENNReal.ofReal_le_ofReal hp_le_two)
  have hratio_le : p / p₀ ≤ χ := by
    dsimp [χ]
    rw [div_le_iff₀ hp₀]
    simpa [mul_comm] using hp_le
  have hratio_nonneg : 0 ≤ p / p₀ := by positivity
  have hvol_pos : 0 < V := by
    dsimp [V]
    exact ENNReal.toReal_pos
      (measure_ball_pos volume (0 : E) (by norm_num : (0 : ℝ) < 1)).ne'
      measure_ball_lt_top.ne
  have hvol_nonneg : 0 ≤ V := hvol_pos.le
  have hexp_nonneg : 0 ≤ 1 / p₀ - 1 / p := by
    have hrecip : 1 / p < 1 / p₀ := by
      exact div_lt_div_of_pos_left one_pos hp₀ hp₀_lt_p
    linarith
  have hcompare_enn :
      eLpNorm u (ENNReal.ofReal p₀) μ ≤
        eLpNorm u (ENNReal.ofReal p) μ * μ Set.univ ^ (1 / p₀ - 1 / p) := by
    simpa [ENNReal.toReal_ofReal hp₀.le, ENNReal.toReal_ofReal hp.le] using
      (eLpNorm_le_eLpNorm_mul_rpow_measure_univ
        (μ := μ) (f := u)
        (p := ENNReal.ofReal p₀) (q := ENNReal.ofReal p)
        (by exact ENNReal.ofReal_le_ofReal (le_of_lt hp₀_lt_p))
        hu_memLp_p.aestronglyMeasurable)
  have hμ_ne_top : μ Set.univ ≠ ⊤ := by
    dsimp [μ]
    rw [Measure.restrict_apply_univ]
    exact measure_ball_lt_top.ne
  have hrpow_ne_top : μ Set.univ ^ (1 / p₀ - 1 / p) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg hexp_nonneg hμ_ne_top
  have hrhs_ne_top :
      eLpNorm u (ENNReal.ofReal p) μ * μ Set.univ ^ (1 / p₀ - 1 / p) ≠ ⊤ :=
    ENNReal.mul_ne_top hu_memLp_p.eLpNorm_ne_top hrpow_ne_top
  have hcompare_real :
      MeasureTheory.lpNorm u (ENNReal.ofReal p₀) μ ≤
        MeasureTheory.lpNorm u (ENNReal.ofReal p) μ * V ^ (1 / p₀ - 1 / p) := by
    have htoReal :=
      (ENNReal.toReal_le_toReal hu_memLp_p₀.eLpNorm_ne_top hrhs_ne_top).2 hcompare_enn
    simpa [MeasureTheory.toReal_eLpNorm hu_memLp_p₀.aestronglyMeasurable,
      MeasureTheory.toReal_eLpNorm hu_memLp_p.aestronglyMeasurable,
      V, μ, measureReal_def, Measure.restrict_apply_univ,
      ENNReal.toReal_mul, ENNReal.toReal_rpow,
      mul_comm, mul_left_comm, mul_assoc] using htoReal
  have hLp_p₀ :
      MeasureTheory.lpNorm u (ENNReal.ofReal p₀) μ =
        (∫ x in Metric.ball (0 : E) 1, |u x| ^ p₀ ∂volume) ^ (1 / p₀) := by
    simpa [μ, ENNReal.toReal_ofReal hp₀.le, Real.norm_eq_abs] using
      (MeasureTheory.lpNorm_eq_integral_norm_rpow_toReal
        (μ := μ) (f := u) (p := ENNReal.ofReal p₀)
        (by positivity) ENNReal.ofReal_ne_top hu_memLp_p₀.aestronglyMeasurable)
  have hLp_p :
      MeasureTheory.lpNorm u (ENNReal.ofReal p) μ =
        (∫ x in Metric.ball (0 : E) 1, |u x| ^ p ∂volume) ^ (1 / p) := by
    simpa [μ, ENNReal.toReal_ofReal hp.le, Real.norm_eq_abs] using
      (MeasureTheory.lpNorm_eq_integral_norm_rpow_toReal
        (μ := μ) (f := u) (p := ENNReal.ofReal p)
        (by positivity) ENNReal.ofReal_ne_top hu_memLp_p.aestronglyMeasurable)
  have hInt_compare :
      (∫ x in Metric.ball (0 : E) 1, |u x| ^ p₀ ∂volume) ^ (1 / p₀) ≤
        (∫ x in Metric.ball (0 : E) 1, |u x| ^ p ∂volume) ^ (1 / p) *
          V ^ (1 / p₀ - 1 / p) := by
    simpa [hLp_p₀, hLp_p, mul_comm, mul_left_comm, mul_assoc] using hcompare_real
  have hI₀_nonneg :
      0 ≤ ∫ x in Metric.ball (0 : E) 1, |u x| ^ p₀ ∂volume := by
    exact integral_nonneg fun x => by positivity
  have hI_nonneg :
      0 ≤ ∫ x in Metric.ball (0 : E) 1, |u x| ^ p ∂volume := by
    exact integral_nonneg fun x => by positivity
  have hvol_pow_compare :
      V ^ (p / p₀ - 1) ≤ (V + 1) ^ χ := by
    have hpow_nonneg : 0 ≤ p / p₀ - 1 := by
      have hratio_ge_one : 1 ≤ p / p₀ := by
        rw [one_le_div hp₀]
        linarith
      linarith
    have hpow_le : p / p₀ - 1 ≤ χ := by
      linarith [hratio_le]
    have hV1_ge_one : 1 ≤ V + 1 := by linarith
    calc
      V ^ (p / p₀ - 1) ≤ (V + 1) ^ (p / p₀ - 1) := by
        exact Real.rpow_le_rpow hvol_nonneg (by linarith) hpow_nonneg
      _ ≤ (V + 1) ^ χ := by
        exact Real.rpow_le_rpow_of_exponent_le hV1_ge_one hpow_le
  have hInt_pow_compare :
      (∫ x in Metric.ball (0 : E) 1, |u x| ^ p₀ ∂volume) ^ (p / p₀) ≤
        (V + 1) ^ χ * ∫ x in Metric.ball (0 : E) 1, |u x| ^ p ∂volume := by
    have hbase :=
      Real.rpow_le_rpow (by positivity) hInt_compare hp.le
    have hstep :
        (∫ x in Metric.ball (0 : E) 1, |u x| ^ p₀ ∂volume) ^ (p / p₀) ≤
          V ^ (p / p₀ - 1) * ∫ x in Metric.ball (0 : E) 1, |u x| ^ p ∂volume := by
      calc
        (∫ x in Metric.ball (0 : E) 1, |u x| ^ p₀ ∂volume) ^ (p / p₀)
            = (((∫ x in Metric.ball (0 : E) 1, |u x| ^ p₀ ∂volume) ^ (1 / p₀)) ^ p) := by
                rw [← Real.rpow_mul hI₀_nonneg]
                field_simp [hp₀.ne']
        _ ≤
            (((∫ x in Metric.ball (0 : E) 1, |u x| ^ p ∂volume) ^ (1 / p) *
                V ^ (1 / p₀ - 1 / p)) ^ p) := hbase
        _ =
            (∫ x in Metric.ball (0 : E) 1, |u x| ^ p ∂volume) *
              V ^ (p / p₀ - 1) := by
                rw [Real.mul_rpow
                  (Real.rpow_nonneg hI_nonneg _)
                  (Real.rpow_nonneg hvol_nonneg _)]
                rw [← Real.rpow_mul hI_nonneg, ← Real.rpow_mul hvol_nonneg]
                have hp_mul : (1 / p) * p = 1 := by
                  field_simp [hp.ne']
                have hp₀_mul : (1 / p₀ - 1 / p) * p = p / p₀ - 1 := by
                  field_simp [hp.ne', hp₀.ne']
                rw [hp_mul, hp₀_mul, Real.rpow_one]
        _ = V ^ (p / p₀ - 1) *
              ∫ x in Metric.ball (0 : E) 1, |u x| ^ p ∂volume := by ring
    exact hstep.trans <|
      mul_le_mul_of_nonneg_right hvol_pow_compare hI_nonneg
  have hp₀_sq_le_p_sq : p₀ ^ 2 ≤ p ^ 2 := by
    nlinarith [le_of_lt hp₀_lt_p]
  have hX₀_le_X : X₀ ≤ X := by
    dsimp [X₀, X]
    have hdiv :
        A.1.Λ * p₀ ^ 2 / (1 - q) ^ 2 ≤
          A.1.Λ * p ^ 2 / (1 - q) ^ 2 := by
      have hmul :
          A.1.Λ * p₀ ^ 2 ≤ A.1.Λ * p ^ 2 := by
        exact mul_le_mul_of_nonneg_left hp₀_sq_le_p_sq A.1.Λ_pos.le
      exact div_le_div_of_nonneg_right hmul (by positivity)
    linarith
  have hX₀_nonneg : 0 ≤ X₀ := by
    dsimp [X₀]
    have hfrac_nonneg :
        0 ≤ A.1.Λ * p₀ ^ 2 / (1 - q) ^ 2 := by
      exact div_nonneg (mul_nonneg A.1.Λ_pos.le (sq_nonneg p₀))
        (sq_nonneg (1 - q))
    linarith
  have hX_ge_one : 1 ≤ X := by
    dsimp [X]
    have hfrac_nonneg :
        0 ≤ A.1.Λ * p ^ 2 / (1 - q) ^ 2 := by
      exact div_nonneg (mul_nonneg A.1.Λ_pos.le (sq_nonneg p))
        (sq_nonneg (1 - q))
    linarith
  have hCX_compare :
      (C_weakHarnack0 d * X₀ ^ ((d : ℝ) / 2)) ^ (p / p₀) ≤
        (C_weakHarnack0 d) ^ χ * X ^ β := by
    have hC_nonneg : 0 ≤ C_weakHarnack0 d := by
      exact le_trans (by norm_num : (0 : ℝ) ≤ 1) (one_le_C_weakHarnack0 (d := d))
    have hCpow :
        (C_weakHarnack0 d) ^ (p / p₀) ≤ (C_weakHarnack0 d) ^ χ := by
      exact Real.rpow_le_rpow_of_exponent_le
        (one_le_C_weakHarnack0 (d := d)) hratio_le
    have hXpow :
        X₀ ^ (((d : ℝ) / 2) * (p / p₀)) ≤ X ^ β := by
      have hexp_nonneg' : 0 ≤ ((d : ℝ) / 2) * (p / p₀) := by positivity
      have hexp_le' : ((d : ℝ) / 2) * (p / p₀) ≤ β := by
        dsimp [β]
        nlinarith [hratio_le]
      calc
        X₀ ^ (((d : ℝ) / 2) * (p / p₀))
            ≤ X ^ (((d : ℝ) / 2) * (p / p₀)) := by
                exact Real.rpow_le_rpow hX₀_nonneg hX₀_le_X hexp_nonneg'
        _ ≤ X ^ β := by
              exact Real.rpow_le_rpow_of_exponent_le hX_ge_one hexp_le'
    calc
      (C_weakHarnack0 d * X₀ ^ ((d : ℝ) / 2)) ^ (p / p₀)
          = (C_weakHarnack0 d) ^ (p / p₀) *
              X₀ ^ (((d : ℝ) / 2) * (p / p₀)) := by
                rw [Real.mul_rpow hC_nonneg (Real.rpow_nonneg hX₀_nonneg _),
                  ← Real.rpow_mul hX₀_nonneg]
      _ ≤ (C_weakHarnack0 d) ^ χ * X ^ β := by
            exact mul_le_mul hCpow hXpow (by positivity) (by positivity)
  have hlhs_eq :
      weakHarnackForwardUpgradeLHS (d := d) A u p q p₀ =
        (C_weakHarnack0 d * X₀ ^ ((d : ℝ) / 2)) ^ (p / p₀) *
          (∫ x in Metric.ball (0 : E) 1, |u x| ^ p₀ ∂volume) ^ (p / p₀) := by
    dsimp [weakHarnackForwardUpgradeLHS, X₀]
    have hCX_nonneg : 0 ≤
        (C_weakHarnack0 d * X₀ ^ ((d : ℝ) / 2)) ^ (1 / p₀) := by
      exact Real.rpow_nonneg
        (mul_nonneg
          (le_trans (by norm_num : (0 : ℝ) ≤ 1) (one_le_C_weakHarnack0 (d := d)))
          (Real.rpow_nonneg hX₀_nonneg _)) _
    rw [Real.mul_rpow hCX_nonneg (Real.rpow_nonneg hI₀_nonneg _)]
    congr 1
    · rw [← Real.rpow_mul
          (mul_nonneg
            (le_trans (by norm_num : (0 : ℝ) ≤ 1) (one_le_C_weakHarnack0 (d := d)))
            (Real.rpow_nonneg hX₀_nonneg _))]
      have hp_mul : (1 / p₀) * p = p / p₀ := by
        field_simp [hp₀.ne']
      rw [hp_mul]
    · rw [← Real.rpow_mul hI₀_nonneg]
      field_simp [hp₀.ne']
  calc
    weakHarnackForwardUpgradeLHS (d := d) A u p q p₀
        = (C_weakHarnack0 d * X₀ ^ ((d : ℝ) / 2)) ^ (p / p₀) *
            (∫ x in Metric.ball (0 : E) 1, |u x| ^ p₀ ∂volume) ^ (p / p₀) := hlhs_eq
    _ ≤ ((C_weakHarnack0 d) ^ χ * X ^ β) *
          ((V + 1) ^ χ * ∫ x in Metric.ball (0 : E) 1, |u x| ^ p ∂volume) := by
            exact mul_le_mul hCX_compare hInt_pow_compare
              (Real.rpow_nonneg hI₀_nonneg _)
              (mul_nonneg
                (Real.rpow_nonneg
                  (le_trans (by norm_num : (0 : ℝ) ≤ 1) (one_le_C_weakHarnack0 (d := d))) _)
                (Real.rpow_nonneg (le_trans zero_le_one hX_ge_one) _))
    _ = ((C_weakHarnack0 d) ^ χ * (V + 1) ^ χ) * X ^ β *
          ∫ x in Metric.ball (0 : E) 1, |u x| ^ p ∂volume := by
          ring
    _ = ((C_weakHarnack0 d) * (V + 1)) ^ χ * X ^ β *
          ∫ x in Metric.ball (0 : E) 1, |u x| ^ p ∂volume := by
          rw [← Real.mul_rpow
            (by exact le_trans (by norm_num : (0 : ℝ) ≤ 1) (one_le_C_weakHarnack0 (d := d)))
            (by positivity)]
    _ = weakHarnackForwardUpgradeRHS (d := d) hd A u p q := by
          dsimp [weakHarnackForwardUpgradeRHS, C_weakHarnack0Forward, V, χ, X, β]

set_option maxHeartbeats 5000000 in
/-- Second stage of weak Harnack: forward low-power iteration for positive
supersolutions.

For `u > 0` a supersolution on `B₁` and `0 < p < q < 1`:
```
‖u‖_{L^{qd/(d-2)}(B_{1/2})}^p ≤
  C_fwd(d) (Λp²/(1-q)² + 1)^{dχ/2} ‖u‖_{Lᵖ(B₁)}^p
```
The theorem is stated for arbitrary `0 < p < q < 1`, with the nonlinear factor
raised to `dχ/2`.

Proof: choose `m` large enough that `p₀ = q χ^{-m} ≤ p`, then apply the
finite forward iteration to get `‖u‖_{L^{qχ}(B_{r_{m+1}})} ≤ C · ‖u‖_{L^{p₀}(B₁)}`,
use `B_{1/2} ⊂ B_{r_{m+1}}` and `p₀ ≤ p` to convert, raise to the `p`-th power,
and apply the geometric majorant bound. -/
theorem weak_harnack_stage_one_forward
    (hd : 2 < (d : ℝ))
    (A : NormalizedEllipticCoeff d (Metric.ball (0 : E) 1))
    {u : E → ℝ} {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hpq : p < q) (hq1 : q < 1)
    (hu_pos : ∀ x ∈ Metric.ball (0 : E) 1, 0 < u x)
    (hsuper : IsSupersolution A.1 u) :
    (∫ x in Metric.ball (0 : E) (1 / 2 : ℝ),
        |u x| ^ (q * (d : ℝ) / ((d : ℝ) - 2)) ∂volume) ^
          (p * (((d : ℝ) - 2) / (q * (d : ℝ)))) ≤
      C_weakHarnack0Forward (d := d) hd *
        (A.1.Λ * p ^ 2 / (1 - q) ^ 2 + 1) ^ (((d : ℝ) * moserChi d) / 2) *
        ∫ x in Metric.ball (0 : E) 1, |u x| ^ p ∂volume := by
  have hq : 0 < q := lt_trans hp hpq
  let qχ : ℝ := q * moserChi d
  have hqχ_pos : 0 < qχ := mul_pos hq (moserChi_pos (d := d) hd)
  have hqχ_ne : qχ ≠ 0 := hqχ_pos.ne'
  rcases exists_forward_iteration_depth (d := d) hd hp hpq with
    ⟨m, hm_lt, hm_le⟩
  let p₀ : ℝ := q * (moserChi d)⁻¹ ^ m
  have hp₀ : 0 < p₀ := by
    dsimp [p₀]
    exact mul_pos hq (pow_pos (inv_pos.mpr (moserChi_pos (d := d) hd)) m)
  have hp₀_lt_p : p₀ < p := by
    simpa [p₀] using hm_lt
  have hp_le_chi_p₀ : p ≤ moserChi d * p₀ := by
    simpa [p₀] using hm_le
  have hp₀_le_two : p₀ ≤ 2 := by
    have hp₀_lt_one : p₀ < 1 := lt_trans hp₀_lt_p hp1
    linarith
  have hp₀Int :
      IntegrableOn (fun x => |u x| ^ p₀)
        (Metric.ball (0 : E) 1) volume := by
    exact supersolution_integrableOn_ball_one_rpow
      (d := d) A hp₀ hp₀_le_two hsuper
  have hiter :=
    supersolution_iteration_forward (d := d) hd A (u := u) (q := q) (m := m)
      hq hq1 hu_pos hsuper
  have hstep := hiter hp₀Int (m + 1) le_rfl
  have hgeom :=
    supersolution_geometric_majorant_fwd (d := d) hd A (q := q) (m := m) hq hq1
  have htarget_int :
      IntegrableOn (fun x => |u x| ^ qχ)
        (Metric.ball (0 : E) (moserRadius (m + 1))) volume := by
    have hstep_int := hstep.1
    rw [moserExponentSeq_forward_target_eq (d := d) hd (q := q) (m := m)] at hstep_int
    simpa [qχ] using hstep_int
  have htarget_norm :
      (∫ x in Metric.ball (0 : E) (moserRadius (m + 1)),
          |u x| ^ qχ ∂volume) ^ (1 / qχ) ≤
        ((C_weakHarnack0 d *
              (A.1.Λ * p₀ ^ 2 / (1 - q) ^ 2 + 1) ^ ((d : ℝ) / 2)) ^
            (1 / p₀)) *
          (∫ x in Metric.ball (0 : E) 1, |u x| ^ p₀ ∂volume) ^ (1 / p₀) := by
    have hbound_step :
        superIterNormFwd (d := d) (u := u) p₀ (m + 1) ≤
          (∏ i ∈ Finset.range (m + 1), superStepConstFwd (d := d) A p₀ i) *
            superIterNormFwd (d := d) (u := u) p₀ 0 := by
      simpa [p₀] using hstep.2
    calc
      (∫ x in Metric.ball (0 : E) (moserRadius (m + 1)),
          |u x| ^ qχ ∂volume) ^ (1 / qχ)
          = superIterNormFwd (d := d) (u := u) p₀ (m + 1) := by
              simpa [qχ, p₀] using
                (superIterNormFwd_target (d := d) hd (u := u) (q := q) (m := m)).symm
      _ ≤ (∏ i ∈ Finset.range (m + 1), superStepConstFwd (d := d) A p₀ i) *
            superIterNormFwd (d := d) (u := u) p₀ 0 := by
              exact hbound_step
      _ ≤ ((C_weakHarnack0 d *
              (A.1.Λ * p₀ ^ 2 / (1 - q) ^ 2 + 1) ^ ((d : ℝ) / 2)) ^
            (1 / p₀)) *
          superIterNormFwd (d := d) (u := u) p₀ 0 := by
            exact mul_le_mul_of_nonneg_right (by simpa [p₀] using hgeom)
              (Real.rpow_nonneg (integral_nonneg fun x => by positivity) _)
      _ = ((C_weakHarnack0 d *
              (A.1.Λ * p₀ ^ 2 / (1 - q) ^ 2 + 1) ^ ((d : ℝ) / 2)) ^
            (1 / p₀)) *
          (∫ x in Metric.ball (0 : E) 1, |u x| ^ p₀ ∂volume) ^ (1 / p₀) := by
            rw [superIterNormFwd_zero]
  have hhalf_sub :
      Metric.ball (0 : E) (1 / 2 : ℝ) ⊆ Metric.ball (0 : E) (moserRadius (m + 1)) := by
    exact Metric.ball_subset_ball (le_of_lt (moserRadius_gt_half (m + 1)))
  have hhalf_int :
      IntegrableOn (fun x => |u x| ^ qχ)
        (Metric.ball (0 : E) (1 / 2 : ℝ)) volume := by
    exact htarget_int.mono_set hhalf_sub
  have hhalf_integral_le :
      ∫ x in Metric.ball (0 : E) (1 / 2 : ℝ), |u x| ^ qχ ∂volume ≤
        ∫ x in Metric.ball (0 : E) (moserRadius (m + 1)), |u x| ^ qχ ∂volume := by
    exact setIntegral_mono_set htarget_int
      (ae_of_all _ (by intro x; positivity))
      (Filter.Eventually.of_forall hhalf_sub)
  have hhalf_norm_le :
      (∫ x in Metric.ball (0 : E) (1 / 2 : ℝ), |u x| ^ qχ ∂volume) ^ (1 / qχ) ≤
        ((C_weakHarnack0 d *
              (A.1.Λ * p₀ ^ 2 / (1 - q) ^ 2 + 1) ^ ((d : ℝ) / 2)) ^
            (1 / p₀)) *
          (∫ x in Metric.ball (0 : E) 1, |u x| ^ p₀ ∂volume) ^ (1 / p₀) := by
    exact
      (Real.rpow_le_rpow (by positivity) hhalf_integral_le (by positivity)).trans
        htarget_norm
  have hmain_pow :
      (∫ x in Metric.ball (0 : E) (1 / 2 : ℝ), |u x| ^ qχ ∂volume) ^ (p / qχ) ≤
        weakHarnackForwardUpgradeLHS (d := d) A u p q p₀ := by
    calc
      (∫ x in Metric.ball (0 : E) (1 / 2 : ℝ), |u x| ^ qχ ∂volume) ^ (p / qχ)
          = ((∫ x in Metric.ball (0 : E) (1 / 2 : ℝ), |u x| ^ qχ ∂volume) ^
              (1 / qχ)) ^ p := by
                rw [← Real.rpow_mul (integral_nonneg fun x => by positivity)]
                field_simp [hqχ_ne]
      _ ≤ weakHarnackForwardUpgradeLHS (d := d) A u p q p₀ := by
            exact Real.rpow_le_rpow (by positivity) hhalf_norm_le hp.le
  have hupgrade :=
    weak_harnack_stage_one_forward_power_upgrade
      (d := d) hd A (u := u) hp₀ hp hp1 hp₀_lt_p hp_le_chi_p₀ hq1 hsuper hp₀Int
  have hqχ_eq : q * (d : ℝ) / ((d : ℝ) - 2) = qχ := by
    dsimp [qχ]
    rw [moserChi]
    ring
  have hexp_eq : p * (((d : ℝ) - 2) / (q * (d : ℝ))) = p / qχ := by
    dsimp [qχ]
    rw [moserChi]
    field_simp [hq.ne']
  calc
    (∫ x in Metric.ball (0 : E) (1 / 2 : ℝ),
        |u x| ^ (q * (d : ℝ) / ((d : ℝ) - 2)) ∂volume) ^
          (p * (((d : ℝ) - 2) / (q * (d : ℝ))))
        = (∫ x in Metric.ball (0 : E) (1 / 2 : ℝ), |u x| ^ qχ ∂volume) ^
            (p / qχ) := by
              rw [hqχ_eq, hexp_eq]
    _ ≤ weakHarnackForwardUpgradeLHS (d := d) A u p q p₀ := hmain_pow
    _ ≤ weakHarnackForwardUpgradeRHS (d := d) hd A u p q := hupgrade
    _ = C_weakHarnack0Forward (d := d) hd *
          (A.1.Λ * p ^ 2 / (1 - q) ^ 2 + 1) ^ (((d : ℝ) * moserChi d) / 2) *
          ∫ x in Metric.ball (0 : E) 1, |u x| ^ p ∂volume := rfl

end DeGiorgi
