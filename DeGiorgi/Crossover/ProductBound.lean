import DeGiorgi.Crossover.ExponentialIntegrability

/-!
# Crossover Product Bound Layer

Public product-bound consequences of the exponential-integrability machinery.
-/

noncomputable section

open MeasureTheory Metric Filter Set
open scoped ENNReal NNReal Topology RealInnerProductSpace

namespace DeGiorgi

variable {d : ℕ} [NeZero d]

local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "Cmo" =>
  ((volume.real (Metric.ball (0 : E) 1)) ^ (-(1 / 2 : ℝ)) * C_poinc_val d)

private theorem regularized_crossover_product_bound
    (A : NormalizedEllipticCoeff d (Metric.ball (0 : E) 1))
    {u : E → ℝ}
    (hu_pos : ∀ x ∈ Metric.ball (0 : E) 1, 0 < u x)
    (hsuper : IsSupersolution A.1 u)
    {ε : ℝ} (hε : 0 < ε) :
    let p := c_crossover' d / A.1.Λ ^ ((1 : ℝ) / 2)
    (⨍ x in Metric.ball (0 : E) (1 / 2 : ℝ), (u x + ε) ^ p ∂volume) *
      (⨍ x in Metric.ball (0 : E) (1 / 2 : ℝ), (u x + ε) ^ (-p) ∂volume) ≤
        (crossoverJNKhalf d) ^ 2 := by
  intro p
  let Bhalf : Set E := Metric.ball (0 : E) (1 / 2 : ℝ)
  let v : E → ℝ := regularizedLogMeasurable (A := A) hu_pos hsuper hε
  let a : ℝ := ⨍ z in Metric.ball (0 : E) (1 / 48 : ℝ), v z ∂volume
  let δ : ℝ := 24 * (2 : ℝ) ^ (d + 1) *
    (c_crossover_bmo_scale d * A.1.Λ ^ ((1 : ℝ) / 2))
  let Kloc : ℝ := Real.exp (p * δ) * (1 + C_JN d)
  let Khalf : ℝ := (Nat.ceil ((97 : ℝ) ^ d) : ℝ) * Kloc
  let Fabs : E → ℝ := fun x => Real.exp (p * |v x - a|)
  let Fplus : E → ℝ := fun x => Real.exp (-p * (v x - a))
  let Fminus : E → ℝ := fun x => Real.exp (p * (v x - a))
  have hBsub : Bhalf ⊆ Metric.ball (0 : E) 1 := Metric.ball_subset_ball (by norm_num)
  have hu_pos_half : ∀ x ∈ Bhalf, 0 < u x := by
    intro x hx
    exact hu_pos x (hBsub hx)
  have hΛsqrt_pos : 0 < A.1.Λ ^ ((1 : ℝ) / 2) := by
    have hΛge : 1 ≤ A.1.Λ := by
      have hΛ := A.1.hΛ
      rw [A.2] at hΛ
      simpa using hΛ
    exact Real.rpow_pos_of_pos (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hΛge) _
  have hp_pos : 0 < p := by
    exact div_pos (crossoverC'_pos (d := d)) hΛsqrt_pos
  have hpd :
      p * δ = crossoverJNTheta d := by
    dsimp [p, δ, crossoverJNTheta]
    field_simp [hΛsqrt_pos.ne']
  have hKhalf_eq : Khalf = crossoverJNKhalf d := by
    dsimp [Khalf, Kloc, crossoverJNKhalf, crossoverJNKloc]
    rw [hpd]
  have hbase :=
    regularizedLog_halfBall_exp_average_to_origin_le (d := d) (A := A)
      hu_pos hsuper hε
  have hFabs_int : IntegrableOn Fabs Bhalf volume := by
    simpa [Bhalf, v, p, a, Fabs] using hbase.1
  have hFabs_avg : (⨍ x in Bhalf, Fabs x ∂volume) ≤ crossoverJNKhalf d := by
    have htmp : (⨍ x in Bhalf, Fabs x ∂volume) ≤ Khalf := by
      simpa [Bhalf, v, p, a, δ, Kloc, Khalf, Fabs] using hbase.2
    rw [hKhalf_eq] at htmp
    exact htmp
  have hFplus_nonneg : ∀ x, 0 ≤ Fplus x := by
    intro x
    exact le_of_lt (Real.exp_pos _)
  have hFminus_nonneg : ∀ x, 0 ≤ Fminus x := by
    intro x
    exact le_of_lt (Real.exp_pos _)
  have hFplus_le :
      ∀ᵐ x ∂(volume.restrict Bhalf), Fplus x ≤ Fabs x := by
    filter_upwards with x
    have hle : -(v x - a) ≤ |v x - a| := by
      exact neg_le_abs (v x - a)
    have hmul : -p * (v x - a) ≤ p * |v x - a| := by
      have hmul' : p * (a - v x) ≤ p * |v x - a| := by
        simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
          (mul_le_mul_of_nonneg_left hle hp_pos.le)
      ring_nf at hmul' ⊢
      exact hmul'
    exact Real.exp_le_exp.mpr hmul
  have hFminus_le :
      ∀ᵐ x ∂(volume.restrict Bhalf), Fminus x ≤ Fabs x := by
    filter_upwards with x
    have hle : v x - a ≤ |v x - a| := by
      exact le_abs_self (v x - a)
    have hmul : p * (v x - a) ≤ p * |v x - a| := by
      exact mul_le_mul_of_nonneg_left hle hp_pos.le
    exact Real.exp_le_exp.mpr hmul
  have hFplus_avg :
      (⨍ x in Bhalf, Fplus x ∂volume) ≤ crossoverJNKhalf d := by
    exact le_trans
      (setAverage_mono_of_nonneg_local (d := d) hFplus_nonneg hFabs_int hFplus_le)
      hFabs_avg
  have hFminus_avg :
      (⨍ x in Bhalf, Fminus x ∂volume) ≤ crossoverJNKhalf d := by
    exact le_trans
      (setAverage_mono_of_nonneg_local (d := d) hFminus_nonneg hFabs_int hFminus_le)
      hFabs_avg
  have hFplus_avg_nonneg : 0 ≤ ⨍ x in Bhalf, Fplus x ∂volume := by
    rw [MeasureTheory.setAverage_eq, smul_eq_mul]
    refine mul_nonneg ?_ ?_
    · positivity
    · exact MeasureTheory.setIntegral_nonneg measurableSet_ball fun x hx => hFplus_nonneg x
  have hFminus_avg_nonneg : 0 ≤ ⨍ x in Bhalf, Fminus x ∂volume := by
    rw [MeasureTheory.setAverage_eq, smul_eq_mul]
    refine mul_nonneg ?_ ?_
    · positivity
    · exact MeasureTheory.setIntegral_nonneg measurableSet_ball fun x hx => hFminus_nonneg x
  have hExact_restrict :
      v =ᵐ[volume.restrict Bhalf] fun x => -Real.log (u x + ε) + Real.log ε := by
    have hball1 :
        v =ᵐ[volume.restrict (Metric.ball (0 : E) 1)]
          fun x => -Real.log (u x + ε) + Real.log ε := by
      exact (regularizedLogMeasurable_ae_eq (d := d) (A := A) hu_pos hsuper hε).symm.trans
        (regularizedLogFun_eq_ae (d := d) (Ω := Metric.ball (0 : E) 1)
          Metric.isOpen_ball hu_pos hε)
    exact ae_mono (Measure.restrict_mono hBsub le_rfl) hball1
  have hExact_ball :
      ∀ᵐ x ∂volume, x ∈ Bhalf → v x = -Real.log (u x + ε) + Real.log ε := by
    rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_ball] at hExact_restrict
    exact hExact_restrict
  have hpow_pos_eq :
      ∀ᵐ x ∂volume, x ∈ Bhalf →
        (u x + ε) ^ p = Real.exp (p * (Real.log ε - a)) * Fplus x := by
    filter_upwards [hExact_ball] with x hx hxmem
    have hux : 0 < u x := hu_pos_half x hxmem
    have huxε : 0 < u x + ε := by linarith
    dsimp [Fplus]
    have hx' := hx hxmem
    rw [hx', Real.rpow_def_of_pos huxε]
    rw [← Real.exp_add]
    congr 1
    ring
  have hpow_neg_eq :
      ∀ᵐ x ∂volume, x ∈ Bhalf →
        (u x + ε) ^ (-p) = Real.exp (p * (a - Real.log ε)) * Fminus x := by
    filter_upwards [hExact_ball] with x hx hxmem
    have hux : 0 < u x := hu_pos_half x hxmem
    have huxε : 0 < u x + ε := by linarith
    dsimp [Fminus]
    have hx' := hx hxmem
    rw [hx', Real.rpow_def_of_pos huxε]
    rw [← Real.exp_add]
    congr 1
    ring
  have havg_pos :
      (⨍ x in Bhalf, (u x + ε) ^ p ∂volume) =
        Real.exp (p * (Real.log ε - a)) * (⨍ x in Bhalf, Fplus x ∂volume) := by
    calc
      (⨍ x in Bhalf, (u x + ε) ^ p ∂volume)
          = ⨍ x in Bhalf, Real.exp (p * (Real.log ε - a)) * Fplus x ∂volume := by
              exact MeasureTheory.setAverage_congr_fun measurableSet_ball hpow_pos_eq
      _ = Real.exp (p * (Real.log ε - a)) * (⨍ x in Bhalf, Fplus x ∂volume) := by
            rw [MeasureTheory.setAverage_eq, MeasureTheory.setAverage_eq, smul_eq_mul, smul_eq_mul,
              integral_const_mul]
            ring
  have havg_neg :
      (⨍ x in Bhalf, (u x + ε) ^ (-p) ∂volume) =
        Real.exp (p * (a - Real.log ε)) * (⨍ x in Bhalf, Fminus x ∂volume) := by
    calc
      (⨍ x in Bhalf, (u x + ε) ^ (-p) ∂volume)
          = ⨍ x in Bhalf, Real.exp (p * (a - Real.log ε)) * Fminus x ∂volume := by
              exact MeasureTheory.setAverage_congr_fun measurableSet_ball hpow_neg_eq
      _ = Real.exp (p * (a - Real.log ε)) * (⨍ x in Bhalf, Fminus x ∂volume) := by
            rw [MeasureTheory.setAverage_eq, MeasureTheory.setAverage_eq, smul_eq_mul, smul_eq_mul,
              integral_const_mul]
            ring
  have hcancel :
      Real.exp (p * (Real.log ε - a)) * Real.exp (p * (a - Real.log ε)) = 1 := by
    rw [← Real.exp_add]
    have hsum : p * (Real.log ε - a) + p * (a - Real.log ε) = 0 := by ring
    simp [hsum]
  rw [havg_pos, havg_neg]
  calc
    (Real.exp (p * (Real.log ε - a)) * ⨍ x in Bhalf, Fplus x ∂volume) *
        (Real.exp (p * (a - Real.log ε)) * ⨍ x in Bhalf, Fminus x ∂volume)
        = (Real.exp (p * (Real.log ε - a)) * Real.exp (p * (a - Real.log ε))) *
            ((⨍ x in Bhalf, Fplus x ∂volume) * (⨍ x in Bhalf, Fminus x ∂volume)) := by
              ring
    _ = (⨍ x in Bhalf, Fplus x ∂volume) * (⨍ x in Bhalf, Fminus x ∂volume) := by
          rw [hcancel]
          ring
    _ ≤ (crossoverJNKhalf d) ^ 2 := by
          nlinarith [hFplus_avg, hFminus_avg, hFplus_avg_nonneg, hFminus_avg_nonneg]

/-- The crossover product is bounded by a dimension-only constant.
This is the master existence theorem powering `crossover_estimate`. -/
theorem crossover_product_bound_exists :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (_hd : 2 < (d : ℝ))
        (A : NormalizedEllipticCoeff d (Metric.ball (0 : E) 1))
        {u : E → ℝ}
        (_hu_pos : ∀ x ∈ Metric.ball (0 : E) 1, 0 < u x)
        (_hsuper : IsSupersolution A.1 u),
        (⨍ x in Metric.ball (0 : E) (1 / 2 : ℝ),
            |u x| ^ (c_crossover' d / A.1.Λ ^ ((1 : ℝ) / 2)) ∂volume) *
          (⨍ x in Metric.ball (0 : E) (1 / 2 : ℝ),
            |u x| ^ (-(c_crossover' d / A.1.Λ ^ ((1 : ℝ) / 2))) ∂volume) ≤ C := by
  let C : ℝ := max 1 ((crossoverJNKhalf d) ^ 2)
  refine ⟨C, le_max_left _ _, ?_⟩
  intro hd A u hu_pos hsuper
  let Bhalf : Set E := Metric.ball (0 : E) (1 / 2 : ℝ)
  let μ : Measure E := volume.restrict Bhalf
  let p : ℝ := c_crossover' d / A.1.Λ ^ ((1 : ℝ) / 2)
  let Aavg : ℝ := ⨍ x in Bhalf, |u x| ^ p ∂volume
  let K : ℝ := (crossoverJNKhalf d) ^ 2
  let M : ℝ := K / Aavg
  let εn : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  let g : ℕ → E → ℝ := fun n x => |(u x + εn n)⁻¹| ^ p
  let g0 : E → ℝ := fun x => |(u x)⁻¹| ^ p
  haveI : IsFiniteMeasure μ := by
    refine ⟨by
      simpa [μ, Bhalf] using
        (measure_ball_lt_top (μ := volume) (x := (0 : E)) (r := (1 / 2 : ℝ)))⟩
  have hBsub : Bhalf ⊆ Metric.ball (0 : E) 1 := Metric.ball_subset_ball (by norm_num)
  have hu_pos_half : ∀ x ∈ Bhalf, 0 < u x := by
    intro x hx
    exact hu_pos x (hBsub hx)
  have hμ_eq : μ.real Set.univ = volume.real Bhalf := by
    simp [μ, Bhalf]
  have hμ_pos : 0 < μ.real Set.univ := by
    rw [hμ_eq]
    exact ENNReal.toReal_pos
      (measure_ball_pos (μ := volume) (0 : E) (by norm_num : (0 : ℝ) < 1 / 2)).ne'
      (measure_ball_lt_top (μ := volume) (x := (0 : E)) (r := (1 / 2 : ℝ))).ne
  have hΛsqrt_pos : 0 < A.1.Λ ^ ((1 : ℝ) / 2) := by
    have hΛge : 1 ≤ A.1.Λ := by
      have hΛ := A.1.hΛ
      rw [A.2] at hΛ
      simpa using hΛ
    exact Real.rpow_pos_of_pos (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hΛge) _
  have hΛsqrt_ge_one : 1 ≤ A.1.Λ ^ ((1 : ℝ) / 2) := by
    have hΛge : 1 ≤ A.1.Λ := by
      have hΛ := A.1.hΛ
      rw [A.2] at hΛ
      simpa using hΛ
    exact Real.one_le_rpow hΛge (by positivity : 0 ≤ (1 : ℝ) / 2)
  have hp_pos : 0 < p := by
    exact div_pos (crossoverC'_pos (d := d)) hΛsqrt_pos
  have hp_nonneg : 0 ≤ p := hp_pos.le
  have hp_le_one : p ≤ 1 := by
    have hinv_le_one : (A.1.Λ ^ ((1 : ℝ) / 2))⁻¹ ≤ 1 := by
      exact inv_le_one_of_one_le₀ hΛsqrt_ge_one
    have hp_le_cc :
        p ≤ c_crossover' d := by
      dsimp [p]
      rw [div_eq_mul_inv]
      have hcc_nonneg : 0 ≤ c_crossover' d := (crossoverC'_pos (d := d)).le
      calc
        c_crossover' d * (A.1.Λ ^ ((1 : ℝ) / 2))⁻¹
            ≤ c_crossover' d * 1 := by
              exact mul_le_mul_of_nonneg_left hinv_le_one hcc_nonneg
        _ = c_crossover' d := by ring
    exact hp_le_cc.trans (c_crossover'_le_one (d := d))
  have hp_le_two : p ≤ 2 := by linarith
  let hw_u : MemW1pWitness 2 u (Metric.ball (0 : E) 1) :=
    (isSupersolution_memW1p hsuper).someWitness
  let hw_u_half : MemW1pWitness 2 u Bhalf :=
    hw_u.restrict Metric.isOpen_ball hBsub
  have hu_aestrong : AEStronglyMeasurable u μ := by
    simpa [μ, Bhalf] using hw_u_half.memLp.aestronglyMeasurable
  have hu_sq_int : Integrable (fun x => |u x| ^ (2 : ℝ)) μ := by
    simpa [μ, Bhalf, Real.rpow_natCast] using hw_u_half.memLp.integrable_norm_pow'
  have hpow_meas : AEStronglyMeasurable (fun x => |u x| ^ p) μ := by
    exact
      ((Real.continuous_rpow_const hp_nonneg).measurable.comp_aemeasurable
        ((continuous_abs.measurable).comp_aemeasurable hu_aestrong.aemeasurable)).aestronglyMeasurable
  have hpow_nonneg : ∀ x, 0 ≤ |u x| ^ p := by
    intro x
    exact Real.rpow_nonneg (abs_nonneg _) _
  have hpow_int : Integrable (fun x => |u x| ^ p) μ := by
    have hdom_int : Integrable (fun x => (1 : ℝ) + |u x| ^ (2 : ℝ)) μ := by
      exact (integrable_const (1 : ℝ)).add hu_sq_int
    refine Integrable.mono' hdom_int hpow_meas ?_
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    have habs_nonneg : 0 ≤ |u x| := abs_nonneg _
    have hpow_nonneg' : 0 ≤ |u x| ^ p := hpow_nonneg x
    have hbound : |u x| ^ p ≤ 1 + |u x| ^ (2 : ℝ) := by
      by_cases hsmall : |u x| ≤ 1
      · have hle_one : |u x| ^ p ≤ 1 := by
          exact Real.rpow_le_one habs_nonneg hsmall hp_nonneg
        linarith [show 0 ≤ |u x| ^ (2 : ℝ) by positivity]
      · have hge_one : 1 ≤ |u x| := le_of_not_ge hsmall
        have hle_two : |u x| ^ p ≤ |u x| ^ (2 : ℝ) := by
          exact Real.rpow_le_rpow_of_exponent_le hge_one hp_le_two
        linarith
    rw [Real.norm_eq_abs, abs_of_nonneg hpow_nonneg']
    exact hbound
  have hpow_support :
      Bhalf ⊆ Function.support (fun x => |u x| ^ p) := by
    intro x hx
    have hux : 0 < u x := hu_pos_half x hx
    have hpow_pos : 0 < |u x| ^ p := by
      rw [abs_of_pos hux]
      exact Real.rpow_pos_of_pos hux _
    exact Function.mem_support.mpr (ne_of_gt hpow_pos)
  have hsupport_pos : 0 < μ (Function.support (fun x => |u x| ^ p)) := by
    have hμ_ball_pos : 0 < μ Bhalf := by
      simpa [μ, Bhalf] using
        (measure_ball_pos (μ := volume) (0 : E) (by norm_num : (0 : ℝ) < 1 / 2))
    exact lt_of_lt_of_le hμ_ball_pos (measure_mono hpow_support)
  have hIpos_pos : 0 < ∫ x, |u x| ^ p ∂μ := by
    rw [integral_pos_iff_support_of_nonneg hpow_nonneg hpow_int]
    exact hsupport_pos
  have hAavg_pos : 0 < Aavg := by
    dsimp [Aavg]
    rw [MeasureTheory.setAverage_eq, smul_eq_mul]
    rw [show ∫ x in Bhalf, |u x| ^ p ∂volume = ∫ x, |u x| ^ p ∂μ by
          simp [μ, Bhalf]]
    rw [← hμ_eq]
    exact mul_pos (inv_pos.mpr hμ_pos) hIpos_pos
  have hεn_pos : ∀ n, 0 < εn n := by
    intro n
    dsimp [εn]
    positivity
  have hεn_le_one : ∀ n, εn n ≤ 1 := by
    intro n
    dsimp [εn]
    have hden_ge : (1 : ℝ) ≤ (n : ℝ) + 1 := by
      nlinarith
    simpa using (one_div_le_one_div_of_le (by positivity : (0 : ℝ) < 1) hden_ge)
  have hshift_pos_meas :
      ∀ n, AEStronglyMeasurable (fun x => (u x + εn n) ^ p) μ := by
    intro n
    exact
      ((Real.continuous_rpow_const hp_nonneg).measurable.comp_aemeasurable
        (hu_aestrong.aemeasurable.add measurable_const.aemeasurable)).aestronglyMeasurable
  have hshift_pos_int :
      ∀ n, Integrable (fun x => (u x + εn n) ^ p) μ := by
    intro n
    have hdom_int : Integrable (fun x => (1 : ℝ) + |u x| ^ p) μ := by
      exact (integrable_const (1 : ℝ)).add hpow_int
    refine Integrable.mono' hdom_int (hshift_pos_meas n) ?_
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    have hux_pos : 0 < u x := hu_pos_half x hx
    have hux_nonneg : 0 ≤ u x := hux_pos.le
    have huxε_nonneg : 0 ≤ u x + εn n := by
      linarith [hux_pos, hεn_pos n]
    have hsubadd :
        (u x + εn n) ^ p ≤ u x ^ p + (εn n) ^ p := by
      simpa [add_comm] using
        (Real.rpow_add_le_add_rpow (hεn_pos n).le hux_nonneg hp_nonneg hp_le_one)
    have hεpow_le_one : (εn n) ^ p ≤ 1 := by
      exact Real.rpow_le_one (hεn_pos n).le (hεn_le_one n) hp_nonneg
    have hpow_nonneg' : 0 ≤ (u x + εn n) ^ p := by
      exact Real.rpow_nonneg huxε_nonneg _
    calc
      ‖(u x + εn n) ^ p‖ = (u x + εn n) ^ p := by
        rw [Real.norm_eq_abs, abs_of_nonneg hpow_nonneg']
      _ ≤ u x ^ p + (εn n) ^ p := hsubadd
      _ ≤ u x ^ p + 1 := by linarith
      _ = 1 + |u x| ^ p := by
        rw [abs_of_pos hux_pos]
        ring
  have hAavg_le_shift :
      ∀ n, Aavg ≤ ⨍ x in Bhalf, (u x + εn n) ^ p ∂volume := by
    intro n
    dsimp [Aavg]
    refine setAverage_mono_of_nonneg_local (d := d) hpow_nonneg ?_ ?_
    · simpa [IntegrableOn, μ, Bhalf] using hshift_pos_int n
    · filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
      have hux_pos : 0 < u x := hu_pos_half x hx
      have hux_nonneg : 0 ≤ u x := hux_pos.le
      have hle_add : u x ≤ u x + εn n := by
        linarith [hεn_pos n]
      rw [abs_of_pos hux_pos]
      exact Real.rpow_le_rpow hux_nonneg hle_add hp_nonneg
  have hg_meas : ∀ n, AEStronglyMeasurable (g n) μ := by
    intro n
    dsimp [g]
    exact
      ((Real.continuous_rpow_const hp_nonneg).measurable.comp_aemeasurable
        ((continuous_abs.measurable).comp_aemeasurable
          ((hu_aestrong.aemeasurable.add measurable_const.aemeasurable).inv))).aestronglyMeasurable
  have hg0_meas : AEStronglyMeasurable g0 μ := by
    dsimp [g0]
    exact
      ((Real.continuous_rpow_const hp_nonneg).measurable.comp_aemeasurable
        ((continuous_abs.measurable).comp_aemeasurable
          (hu_aestrong.aemeasurable.inv))).aestronglyMeasurable
  have hg_nonneg : ∀ n, 0 ≤ᵐ[μ] g n := by
    intro n
    exact Filter.Eventually.of_forall fun x => by
      dsimp [g]
      positivity
  have hg0_nonneg : 0 ≤ᵐ[μ] g0 := by
    exact Filter.Eventually.of_forall fun x => by
      dsimp [g0]
      positivity
  have hg_int : ∀ n, Integrable (g n) μ := by
    intro n
    have hconst_int : Integrable (fun _ : E => ((εn n)⁻¹) ^ p) μ := by
      exact integrable_const (((εn n)⁻¹) ^ p)
    refine Integrable.mono' hconst_int (hg_meas n) ?_
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    have hux_pos : 0 < u x := hu_pos_half x hx
    have huxε_pos : 0 < u x + εn n := by
      linarith [hux_pos, hεn_pos n]
    have hε_le : εn n ≤ u x + εn n := by
      linarith [hux_pos, hεn_pos n]
    have hle_inv : (u x + εn n)⁻¹ ≤ (εn n)⁻¹ := by
      rw [inv_le_inv₀ huxε_pos (hεn_pos n)]
      exact hε_le
    have hpow_nonneg' : 0 ≤ |(u x + εn n)⁻¹| ^ p := by
      positivity
    calc
      ‖g n x‖ = ‖|(u x + εn n)⁻¹| ^ p‖ := by
        dsimp [g]
      _ = |(u x + εn n)⁻¹| ^ p := by
        rw [Real.norm_eq_abs, abs_of_nonneg hpow_nonneg']
      _ = ((u x + εn n)⁻¹) ^ p := by
        rw [abs_of_pos (inv_pos.mpr huxε_pos)]
      _ ≤ ((εn n)⁻¹) ^ p := by
        exact Real.rpow_le_rpow (inv_nonneg.mpr huxε_pos.le) hle_inv hp_nonneg
  have hshift_neg_eq :
      ∀ n,
        (⨍ x in Bhalf, (u x + εn n) ^ (-p) ∂volume) =
          ⨍ x in Bhalf, g n x ∂volume := by
    intro n
    exact MeasureTheory.setAverage_congr_fun measurableSet_ball <| by
      filter_upwards with x
      intro hx
      have huxε_pos : 0 < u x + εn n := by
        linarith [hu_pos_half x hx, hεn_pos n]
      calc
        (u x + εn n) ^ (-p) = |u x + εn n| ^ (-p) := by
          rw [abs_of_pos huxε_pos]
        _ = g n x := by
          dsimp [g]
          exact crossover_abs_rpow_neg_eq_abs_inv_rpow huxε_pos
  have hreg_n :
      ∀ n,
        (⨍ x in Bhalf, (u x + εn n) ^ p ∂volume) *
            (⨍ x in Bhalf, g n x ∂volume) ≤ K := by
    intro n
    have hreg :=
      regularized_crossover_product_bound (d := d) (A := A)
        hu_pos hsuper (hε := hεn_pos n)
    have hshift_neg_eq' :
        (⨍ x in Metric.ball (0 : E) (1 / 2 : ℝ), (u x + εn n) ^ (-p) ∂volume) =
          ⨍ x in Metric.ball (0 : E) (1 / 2 : ℝ), g n x ∂volume := by
      simpa [Bhalf] using hshift_neg_eq n
    have hregp :
        (⨍ x in Metric.ball (0 : E) (1 / 2 : ℝ), (u x + εn n) ^ p ∂volume) *
            (⨍ x in Metric.ball (0 : E) (1 / 2 : ℝ), (u x + εn n) ^ (-p) ∂volume) ≤
          crossoverJNKhalf d ^ 2 := by
      simpa [p] using hreg
    have hreg' :
        (⨍ x in Metric.ball (0 : E) (1 / 2 : ℝ), (u x + εn n) ^ p ∂volume) *
            (⨍ x in Metric.ball (0 : E) (1 / 2 : ℝ), g n x ∂volume) ≤
          crossoverJNKhalf d ^ 2 := by
      calc
        (⨍ x in Metric.ball (0 : E) (1 / 2 : ℝ), (u x + εn n) ^ p ∂volume) *
            (⨍ x in Metric.ball (0 : E) (1 / 2 : ℝ), g n x ∂volume)
            =
              (⨍ x in Metric.ball (0 : E) (1 / 2 : ℝ), (u x + εn n) ^ p ∂volume) *
                (⨍ x in Metric.ball (0 : E) (1 / 2 : ℝ), (u x + εn n) ^ (-p) ∂volume) := by
                  rw [hshift_neg_eq']
        _ ≤ crossoverJNKhalf d ^ 2 := hregp
    simpa [Bhalf, p, K] using hreg'
  have hgavg_nonneg :
      ∀ n, 0 ≤ ⨍ x in Bhalf, g n x ∂volume := by
    intro n
    rw [MeasureTheory.setAverage_eq, smul_eq_mul]
    refine mul_nonneg ?_ ?_
    · positivity
    · exact integral_nonneg fun x => by
        dsimp [g]
        positivity
  have hgavg_bound :
      ∀ n, ⨍ x in Bhalf, g n x ∂volume ≤ M := by
    intro n
    have hmul :
        Aavg * (⨍ x in Bhalf, g n x ∂volume) ≤ K := by
      have hleft :
          Aavg * (⨍ x in Bhalf, g n x ∂volume) ≤
            (⨍ x in Bhalf, (u x + εn n) ^ p ∂volume) *
              (⨍ x in Bhalf, g n x ∂volume) := by
        exact mul_le_mul_of_nonneg_right (hAavg_le_shift n) (hgavg_nonneg n)
      exact le_trans hleft (hreg_n n)
    exact (le_div_iff₀ hAavg_pos).2 (by simpa [M, mul_comm, mul_left_comm, mul_assoc] using hmul)
  have hg_int_bound :
      ∀ n, ∫ x, g n x ∂μ ≤ μ.real Set.univ * M := by
    intro n
    have havg := hgavg_bound n
    rw [MeasureTheory.setAverage_eq, smul_eq_mul] at havg
    rw [show ∫ x in Bhalf, g n x ∂volume = ∫ x, g n x ∂μ by
          simp [μ, Bhalf]] at havg
    rw [← hμ_eq] at havg
    rw [show (μ.real Set.univ)⁻¹ * ∫ x, g n x ∂μ =
        (∫ x, g n x ∂μ) / μ.real Set.univ by
          field_simp [hμ_pos.ne']] at havg
    have hmul : ∫ x, g n x ∂μ ≤ M * μ.real Set.univ := by
      exact (div_le_iff₀ hμ_pos).mp havg
    simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
  have hright_eq :
      ∀ n,
        ∫⁻ x, ENNReal.ofReal (g n x) ∂μ =
          ENNReal.ofReal (∫ x, g n x ∂μ) := by
    intro n
    exact
      (MeasureTheory.ofReal_integral_eq_lintegral_ofReal
        (μ := μ) (f := g n) (hg_int n) (hg_nonneg n)).symm
  have hFatou :
      ∫⁻ x, ENNReal.ofReal (g0 x) ∂μ ≤
        atTop.liminf (fun n => ∫⁻ x, ENNReal.ofReal (g n x) ∂μ) := by
    have hmeas :
        ∀ n, AEMeasurable (fun x => ENNReal.ofReal (g n x)) μ := by
      intro n
      exact (hg_meas n).aemeasurable.ennreal_ofReal
    have hleft := MeasureTheory.lintegral_liminf_le' (μ := μ) hmeas
    have hlim :
        (fun x => Filter.liminf (fun n => ENNReal.ofReal (g n x)) atTop) =ᵐ[μ]
          fun x => ENNReal.ofReal (g0 x) := by
      filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
      have hux_pos : 0 < u x := hu_pos_half x hx
      have hshift_tend :
          Filter.Tendsto (fun n => u x + εn n) atTop (nhds (u x)) := by
        simpa [εn, add_comm, one_div] using
          (tendsto_one_div_add_atTop_nhds_zero_nat.const_add (u x))
      have hinv_tend :
          Filter.Tendsto (fun n => (u x + εn n)⁻¹) atTop (nhds ((u x)⁻¹)) := by
        have hdiv :
            Filter.Tendsto (fun n : ℕ => (1 : ℝ) / (u x + εn n)) atTop
              (nhds ((1 : ℝ) / u x)) := by
          exact Tendsto.div tendsto_const_nhds hshift_tend hux_pos.ne'
        simpa [one_div] using hdiv
      have hreal_tend :
          Filter.Tendsto (fun n => g n x) atTop (nhds (g0 x)) := by
        dsimp [g, g0]
        exact ((Real.continuous_rpow_const hp_nonneg).continuousAt.tendsto.comp
          (continuous_abs.continuousAt.tendsto.comp hinv_tend))
      have henn_tend :
          Filter.Tendsto (fun n => ENNReal.ofReal (g n x)) atTop
            (nhds (ENNReal.ofReal (g0 x))) := by
        exact (ENNReal.continuous_ofReal.tendsto _).comp hreal_tend
      exact henn_tend.liminf_eq
    calc
      ∫⁻ x, ENNReal.ofReal (g0 x) ∂μ
          = ∫⁻ x, Filter.liminf (fun n => ENNReal.ofReal (g n x)) atTop ∂μ := by
              exact lintegral_congr_ae hlim.symm
      _ ≤ atTop.liminf (fun n => ∫⁻ x, ENNReal.ofReal (g n x) ∂μ) := hleft
  have hliminf_le :
      atTop.liminf (fun n => ∫⁻ x, ENNReal.ofReal (g n x) ∂μ) ≤
        ENNReal.ofReal (μ.real Set.univ * M) := by
    rw [Filter.liminf_congr (Eventually.of_forall hright_eq)]
    refine Filter.liminf_le_of_frequently_le' (Frequently.of_forall fun n => ?_)
    exact ENNReal.ofReal_le_ofReal (hg_int_bound n)
  have hmain_enn :
      ∫⁻ x, ENNReal.ofReal (g0 x) ∂μ ≤ ENNReal.ofReal (μ.real Set.univ * M) := by
    exact le_trans hFatou hliminf_le
  have hM_nonneg : 0 ≤ M := by
    dsimp [M, K]
    exact div_nonneg (by positivity) hAavg_pos.le
  have hg0_int : Integrable g0 μ := by
    have hlin_top : ∫⁻ x, ENNReal.ofReal (g0 x) ∂μ ≠ ⊤ := by
      exact ne_of_lt (lt_of_le_of_lt hmain_enn ENNReal.ofReal_lt_top)
    have hInt :=
      integrable_toReal_of_lintegral_ne_top
        (hg0_meas.aemeasurable.ennreal_ofReal) hlin_top
    refine hInt.congr ?_
    filter_upwards with x
    have hg0x_nonneg : 0 ≤ g0 x := by
      dsimp [g0]
      positivity
    rw [ENNReal.toReal_ofReal hg0x_nonneg]
  have hg0_int_bound :
      ∫ x, g0 x ∂μ ≤ μ.real Set.univ * M := by
    calc
      ∫ x, g0 x ∂μ = ENNReal.toReal (∫⁻ x, ENNReal.ofReal (g0 x) ∂μ) := by
            exact MeasureTheory.integral_eq_lintegral_of_nonneg_ae hg0_nonneg hg0_meas
      _ ≤ ENNReal.toReal (ENNReal.ofReal (μ.real Set.univ * M)) := by
            have hleft_ne_top : ∫⁻ x, ENNReal.ofReal (g0 x) ∂μ ≠ ⊤ := by
              exact ne_of_lt (lt_of_le_of_lt hmain_enn ENNReal.ofReal_lt_top)
            have hright_ne_top : ENNReal.ofReal (μ.real Set.univ * M) ≠ ⊤ := by
              exact ne_of_lt ENNReal.ofReal_lt_top
            exact (ENNReal.toReal_le_toReal hleft_ne_top hright_ne_top).2 hmain_enn
      _ = μ.real Set.univ * M := by
            rw [ENNReal.toReal_ofReal (mul_nonneg hμ_pos.le hM_nonneg)]
  have hg0_avg_bound :
      (⨍ x in Bhalf, g0 x ∂volume) ≤ M := by
    rw [MeasureTheory.setAverage_eq, smul_eq_mul, ← hμ_eq]
    rw [show (μ.real Set.univ)⁻¹ * ∫ x, g0 x ∂μ =
        (∫ x, g0 x ∂μ) / μ.real Set.univ by
          field_simp [hμ_pos.ne']]
    exact (div_le_iff₀ hμ_pos).2 (by simpa [mul_comm, mul_left_comm, mul_assoc] using hg0_int_bound)
  have hneg_target_eq :
      (⨍ x in Bhalf, |u x| ^ (-p) ∂volume) = ⨍ x in Bhalf, g0 x ∂volume := by
    exact MeasureTheory.setAverage_congr_fun measurableSet_ball <| by
      filter_upwards with x
      intro hx
      have hux_pos : 0 < u x := hu_pos_half x hx
      dsimp [g0]
      exact crossover_abs_rpow_neg_eq_abs_inv_rpow hux_pos
  rw [hneg_target_eq]
  calc
    (⨍ x in Bhalf, |u x| ^ p ∂volume) * (⨍ x in Bhalf, g0 x ∂volume)
        ≤ Aavg * M := by
          exact mul_le_mul_of_nonneg_left hg0_avg_bound hAavg_pos.le
    _ = K := by
          dsimp [M]
          field_simp [hAavg_pos.ne']
    _ ≤ C := by
          dsimp [C]
          exact le_max_right _ _

/-- The constant `C(d)` bounding the crossover product `⨍ u^c · ⨍ u^{-c} ≤ C`.
Defined via `Classical.choose` from the crossover existence proof. -/
noncomputable def C_crossover' (d : ℕ) [NeZero d] : ℝ :=
  Classical.choose (crossover_product_bound_exists (d := d))

theorem C_crossover'_spec :
    1 ≤ C_crossover' (d := d) ∧
    ∀ (_hd : 2 < (d : ℝ))
      (A : NormalizedEllipticCoeff d (Metric.ball (0 : E) 1))
      {u : E → ℝ}
      (_hu_pos : ∀ x ∈ Metric.ball (0 : E) 1, 0 < u x)
      (_hsuper : IsSupersolution A.1 u),
      (⨍ x in Metric.ball (0 : E) (1 / 2 : ℝ),
          |u x| ^ (c_crossover' d / A.1.Λ ^ ((1 : ℝ) / 2)) ∂volume) *
        (⨍ x in Metric.ball (0 : E) (1 / 2 : ℝ),
          |u x| ^ (-(c_crossover' d / A.1.Λ ^ ((1 : ℝ) / 2))) ∂volume) ≤ C_crossover' d :=
  Classical.choose_spec (crossover_product_bound_exists (d := d))

theorem one_le_C_crossover' : 1 ≤ C_crossover' (d := d) :=
  (Classical.choose_spec (crossover_product_bound_exists (d := d))).1

end DeGiorgi
