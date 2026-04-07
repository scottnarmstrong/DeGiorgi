import DeGiorgi.Oscillation.BMO

/-!
# Chapter 02: Local John-Nirenberg Theory

This module contains the selected-ball decay machinery and the local
John-Nirenberg inequality.
-/

noncomputable section

open MeasureTheory Metric Filter Set
open scoped ENNReal NNReal Topology

namespace DeGiorgi

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)

/-- Geometric decay of selected John-Nirenberg bad-ball unions from the local half-measure step. -/
theorem john_nirenberg_level_set_decay
    {x₀ : E} {r : ℝ} {E_lam E_lam_A : Set E}
    {ι : Type*} [Countable ι] (B : ι → JNBall x₀ r)
    (_hE_lam_meas : MeasurableSet E_lam)
    (hE_lam_A_meas : MeasurableSet E_lam_A)
    (hE_lam_fin : volume E_lam ≠ ⊤)
    (hE_lam_A_sub : E_lam_A ⊆ E_lam)
    (hcover : E_lam ⊆ ⋃ i, (B i).fivefold)
    (hU_sub_E_lam : (⋃ i, (B i).carrier) ⊆ E_lam)
    (hdisj : ∀ i j, i ≠ j → Disjoint ((B i).carrier) ((B j).carrier))
    (hmain : ∀ i,
      volume (E_lam_A ∩ (B i).carrier) ≤ ENNReal.ofReal (1 / 2) * volume ((B i).carrier)) :
    volume.real E_lam_A ≤ (1 - 1 / (2 * 5 ^ d)) * volume.real E_lam := by
  -- Finiteness of derived sets
  have hE_lam_A_fin : volume E_lam_A ≠ ⊤ := measure_ne_top_of_subset hE_lam_A_sub hE_lam_fin
  -- Set up U = ⋃ i, (B i).carrier
  set U := ⋃ i, (B i).carrier with hU_def
  have hU_meas : MeasurableSet U :=
    MeasurableSet.iUnion (fun i => (B i).measurableSet_carrier)
  have hU_fin : volume U ≠ ⊤ := measure_ne_top_of_subset hU_sub_E_lam hE_lam_fin
  -- Carrier finiteness
  have hcarrier_fin : ∀ i, volume ((B i).carrier) ≠ ⊤ :=
    fun i => measure_ne_top_of_subset (subset_iUnion (fun i => (B i).carrier) i) hU_fin
  -- Pairwise disjointness in Pairwise form
  have hdisj_pw : Pairwise (Function.onFun Disjoint fun i => (B i).carrier) :=
    fun i j hij => hdisj i j hij
  have hvolU : volume U = ∑' i, volume ((B i).carrier) :=
    measure_iUnion hdisj_pw (fun i => (B i).measurableSet_carrier)
  have hE_lam_le : volume.real E_lam ≤ (5 : ℝ) ^ d * volume.real U := by
    have h1 : volume E_lam ≤ volume (⋃ i, (B i).fivefold) := measure_mono hcover
    have h2 : volume (⋃ i, (B i).fivefold) ≤ ∑' i, volume ((B i).fivefold) :=
      measure_iUnion_le _
    have h3 : ∀ i, volume ((B i).fivefold) = ENNReal.ofReal ((5 : ℝ) ^ d) * volume ((B i).carrier) :=
      fun i => (B i).volume_fivefold
    have h4 : ∑' i, volume ((B i).fivefold) = ∑' i, (ENNReal.ofReal ((5 : ℝ) ^ d) * volume ((B i).carrier)) :=
      tsum_congr (fun i => h3 i)
    have h5 : ∑' i, (ENNReal.ofReal ((5 : ℝ) ^ d) * volume ((B i).carrier)) =
        ENNReal.ofReal ((5 : ℝ) ^ d) * ∑' i, volume ((B i).carrier) :=
      ENNReal.tsum_mul_left
    rw [h4, h5, ← hvolU] at h2
    have hfive_ne_top : ENNReal.ofReal ((5 : ℝ) ^ d) * volume U ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hU_fin
    have hle := ENNReal.toReal_mono hfive_ne_top (h1.trans h2)
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity : (0:ℝ) ≤ (5:ℝ) ^ d)] at hle
  have hA_inter_U : volume.real (E_lam_A ∩ U) ≤ 1 / 2 * volume.real U := by
    -- Work in ENNReal: volume (E_lam_A ∩ U) ≤ ENNReal.ofReal (1/2) * volume U
    have hinter_eq : E_lam_A ∩ U = ⋃ i, (E_lam_A ∩ (B i).carrier) := by
      simp [hU_def, inter_iUnion]
    have hdisj_inter : Pairwise (Function.onFun Disjoint fun i => E_lam_A ∩ (B i).carrier) := by
      intro i j hij
      exact Disjoint.mono inter_subset_right inter_subset_right (hdisj_pw hij)
    have hmeas_inter : ∀ i, MeasurableSet (E_lam_A ∩ (B i).carrier) :=
      fun i => hE_lam_A_meas.inter (B i).measurableSet_carrier
    have hvol_inter : volume (E_lam_A ∩ U) = ∑' i, volume (E_lam_A ∩ (B i).carrier) := by
      rw [hinter_eq, measure_iUnion hdisj_inter hmeas_inter]
    have henn_le : volume (E_lam_A ∩ U) ≤ ENNReal.ofReal (1 / 2) * volume U := by
      rw [hvol_inter, hvolU]
      calc ∑' i, volume (E_lam_A ∩ (B i).carrier)
          ≤ ∑' i, (ENNReal.ofReal (1 / 2) * volume ((B i).carrier)) :=
            ENNReal.tsum_le_tsum (fun i => hmain i)
        _ = ENNReal.ofReal (1 / 2) * ∑' i, volume ((B i).carrier) :=
            ENNReal.tsum_mul_left
    have hfin : ENNReal.ofReal (1 / 2) * volume U ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hU_fin
    have := ENNReal.toReal_mono hfin henn_le
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by norm_num : (0:ℝ) ≤ 1/2)] at this
  have hAdiffU_sub : E_lam_A \ U ⊆ E_lam \ U :=
    diff_subset_diff_left hE_lam_A_sub
  -- volume.real E_lam_A = volume.real (E_lam_A ∩ U) + volume.real (E_lam_A \ U)
  have hE_lam_A_split : volume.real E_lam_A =
      volume.real (E_lam_A ∩ U) + volume.real (E_lam_A \ U) := by
    rw [← measureReal_inter_add_diff hU_meas hE_lam_A_fin]
  -- volume.real (E_lam \ U) = volume.real E_lam - volume.real U
  have hE_lam_diff : volume.real (E_lam \ U) = volume.real E_lam - volume.real U :=
    measureReal_diff hU_sub_E_lam hU_meas hE_lam_fin
  -- volume.real (E_lam_A \ U) ≤ volume.real (E_lam \ U)
  have hAdiffU_le : volume.real (E_lam_A \ U) ≤ volume.real (E_lam \ U) := by
    exact measureReal_mono hAdiffU_sub
      (ne_top_of_le_ne_top hE_lam_fin (measure_mono diff_subset))
  have hU_lower : 1 / (5 : ℝ) ^ d * volume.real E_lam ≤ volume.real U := by
    by_cases h5d : (5 : ℝ) ^ d = 0
    · simp [h5d]
    · rw [div_mul_eq_mul_div, one_mul]
      exact div_le_of_le_mul₀ (by positivity) measureReal_nonneg (by linarith [hE_lam_le])
  -- Now combine: volume.real E_lam_A ≤ 1/2 * volume.real U + (volume.real E_lam - volume.real U)
  --                                    = volume.real E_lam - 1/2 * volume.real U
  --                                    ≤ volume.real E_lam - 1/2 * 1/5^d * volume.real E_lam
  --                                    = (1 - 1/(2*5^d)) * volume.real E_lam
  have hU_real_le : volume.real U ≤ volume.real E_lam :=
    measureReal_mono hU_sub_E_lam hE_lam_fin
  calc volume.real E_lam_A
      = volume.real (E_lam_A ∩ U) + volume.real (E_lam_A \ U) := hE_lam_A_split
    _ ≤ 1 / 2 * volume.real U + volume.real (E_lam \ U) := by
        linarith [hA_inter_U, hAdiffU_le]
    _ = 1 / 2 * volume.real U + (volume.real E_lam - volume.real U) := by
        rw [hE_lam_diff]
    _ = volume.real E_lam - 1 / 2 * volume.real U := by ring
    _ ≤ volume.real E_lam - 1 / 2 * (1 / (5 : ℝ) ^ d * volume.real E_lam) := by
        linarith [hU_lower]
    _ = (1 - 1 / (2 * 5 ^ d)) * volume.real E_lam := by ring

/-! ## Auxiliary Lemmas for Local John-Nirenberg -/

/-- The five-fold enlargement of a JNBall stays inside the five-fold enlargement
of the ambient ball. -/
lemma JNBall.fivefold_subset_sixBall {x₀ : E} {R : ℝ} (b : JNBall x₀ R) :
    Metric.ball b.center (5 * b.radius) ⊆ Metric.ball x₀ (6 * R) := by
  intro y hy
  have h1 : dist y b.center < 5 * b.radius := Metric.mem_ball.1 hy
  have hcR : dist b.center x₀ < R := Metric.mem_ball.1 b.center_mem
  have hdy : dist y x₀ < 5 * b.radius + R :=
    calc dist y x₀ ≤ dist y b.center + dist b.center x₀ := dist_triangle _ _ _
      _ < 5 * b.radius + R := by linarith
  have h6 : 5 * b.radius + R ≤ 6 * R := by linarith [b.radius_le]
  exact Metric.mem_ball.2 (lt_of_lt_of_le hdy h6)

lemma JNBall.closedBall_fivefold_subset_sixBall {x₀ : E} {R : ℝ} (b : JNBall x₀ R) :
    Metric.closedBall b.center (5 * b.radius) ⊆ Metric.ball x₀ (6 * R) := by
  intro y hy
  have h1 : dist y b.center ≤ 5 * b.radius := Metric.mem_closedBall.1 hy
  have hcR : dist b.center x₀ < R := Metric.mem_ball.1 b.center_mem
  have hdy : dist y x₀ < 5 * b.radius + R :=
    calc dist y x₀ ≤ dist y b.center + dist b.center x₀ := dist_triangle _ _ _
      _ < 5 * b.radius + R := by linarith
  have h6 : 5 * b.radius + R ≤ 6 * R := by linarith [b.radius_le]
  exact Metric.mem_ball.2 (lt_of_lt_of_le hdy h6)

/-- Convert a volume.real inequality to an ENNReal inequality. -/
lemma volume_real_le_to_ennreal {s t : Set E}
    (hs_fin : volume s ≠ ⊤) (ht_fin : volume t ≠ ⊤)
    {θ : ℝ} (hθ : 0 ≤ θ)
    (h : volume.real s ≤ θ * volume.real t) :
    volume s ≤ ENNReal.ofReal θ * volume t := by
  rw [measureReal_def, measureReal_def] at h
  rwa [← ENNReal.toReal_le_toReal hs_fin (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ht_fin),
    ENNReal.toReal_mul, ENNReal.toReal_ofReal hθ]

/-- The absolute value function `|u - c|` has BMO seminorm at most `2M`
whenever `u` has BMO seminorm at most `M`. Uses the reverse triangle inequality
`||a| - |b|| ≤ |a - b|`. -/
lemma abs_sub_const_bmo_le_two
    {M : ℝ} {u : E → ℝ} {c : ℝ} {z : E} {s : ℝ} (hs : 0 < s)
    (hu_int : IntegrableOn u (Metric.ball z s) volume)
    (hu_bmo : (⨍ x in Metric.ball z s,
      ‖u x - ⨍ y in Metric.ball z s, u y ∂volume‖ ∂volume) ≤ M) :
    (⨍ x in Metric.ball z s,
      ‖ |u x - c| - ⨍ y in Metric.ball z s, |u y - c| ∂volume‖ ∂volume) ≤ 2 * M := by
  -- Abbreviations
  set B := Metric.ball z s with hB_def
  set avg_u := ⨍ y in B, u y ∂volume with havg_u_def
  set w : E → ℝ := fun x => |u x - c| with hw_def
  set avg_w := ⨍ y in B, w y ∂volume with havg_w_def
  -- Measure facts
  have hB_vol_pos : 0 < volume B := measure_ball_pos volume z hs
  have hB_vol_ne_zero : volume B ≠ 0 := hB_vol_pos.ne'
  have hB_vol_ne_top : volume B ≠ ⊤ := measure_ball_lt_top.ne
  haveI : IsFiniteMeasure (volume.restrict B) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hB_vol_ne_top.lt_top⟩
  have hvolR_pos : 0 < volume.real B :=
    ENNReal.toReal_pos hB_vol_ne_zero hB_vol_ne_top
  have hvolR_ne_zero : volume.real B ≠ 0 := hvolR_pos.ne'
  -- Integrability facts
  have hw_int : IntegrableOn w B volume := (hu_int.sub integrableOn_const).norm
  have hu_sub_avg_int : IntegrableOn (fun x => u x - avg_u) B volume :=
    hu_int.sub integrableOn_const
  have hw_sub_avg_int : IntegrableOn (fun x => w x - avg_w) B volume :=
    hw_int.sub integrableOn_const
  have hnorm_w_sub_avg_int : IntegrableOn (fun x => ‖w x - avg_w‖) B volume :=
    hw_sub_avg_int.norm
  -- Key constant: a = |avg_u - c|
  set a := |avg_u - c| with ha_def
  have hrev_tri : ∀ x, ‖w x - a‖ ≤ ‖u x - avg_u‖ := by
    intro x
    simp only [hw_def, ha_def]
    rw [show u x - avg_u = (u x - c) - (avg_u - c) from by ring]
    exact norm_abs_sub_abs (u x - c) (avg_u - c)
  -- Reverse triangle in the other direction (for Jensen step)
  have hrev_tri' : ∀ y, ‖a - w y‖ ≤ ‖u y - avg_u‖ := by
    intro y
    rw [norm_sub_rev]
    exact hrev_tri y
  -- Proof: ‖a - avg_w‖ ≤ ⨍ ‖a - w y‖ ≤ ⨍ ‖u y - avg_u‖
  have hJensen : ‖a - avg_w‖ ≤ ⨍ y in B, ‖u y - avg_u‖ ∂volume := by
    -- First bound: ‖a - avg_w‖ = ‖(volR B)⁻¹ • (volR B • a - ∫ w)‖
    -- = (volR B)⁻¹ * ‖∫ (a - w)‖ ≤ (volR B)⁻¹ * ∫ ‖a - w‖ ≤ (volR B)⁻¹ * ∫ ‖u - avg_u‖
    rw [havg_w_def, setAverage_eq]
    -- ‖a - (volR B)⁻¹ • ∫ w‖
    have hsub_eq : a - (volume.real B)⁻¹ • ∫ y in B, w y ∂volume =
        (volume.real B)⁻¹ • (∫ y in B, (a - w y) ∂volume) := by
      rw [integral_sub (integrable_const a) hw_int, integral_const,
        measureReal_restrict_apply_univ, smul_sub]
      simp only [smul_eq_mul, measureReal_def]
      have hvR : (volume B).toReal ≠ 0 :=
        ENNReal.toReal_ne_zero.mpr ⟨hB_vol_ne_zero, hB_vol_ne_top⟩
      field_simp [hvR]
    rw [hsub_eq, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hvolR_pos.le)]
    -- Now: (volR B)⁻¹ * ‖∫ (a - w)‖ ≤ (volR B)⁻¹ * ∫ ‖a - w‖ ≤ (volR B)⁻¹ * ∫ ‖u - avg_u‖
    rw [setAverage_eq]
    apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hvolR_pos.le)
    calc ‖∫ y in B, (a - w y) ∂volume‖
        ≤ ∫ y in B, ‖a - w y‖ ∂volume := norm_integral_le_integral_norm _
      _ ≤ ∫ y in B, ‖u y - avg_u‖ ∂volume := by
          apply setIntegral_mono ((integrable_const a).sub hw_int).norm hu_sub_avg_int.norm
          exact fun y => hrev_tri' y
  -- ‖w x - avg_w‖ ≤ ‖w x - a‖ + ‖a - avg_w‖ ≤ ‖u x - avg_u‖ + ⨍ ‖u - avg_u‖
  have hpointwise : ∀ x, ‖w x - avg_w‖ ≤
      ‖u x - avg_u‖ + ⨍ y in B, ‖u y - avg_u‖ ∂volume := by
    intro x
    calc ‖w x - avg_w‖
        = ‖(w x - a) + (a - avg_w)‖ := by congr 1; ring
      _ ≤ ‖w x - a‖ + ‖a - avg_w‖ := norm_add_le _ _
      _ ≤ ‖u x - avg_u‖ + ⨍ y in B, ‖u y - avg_u‖ ∂volume :=
          add_le_add (hrev_tri x) hJensen
  -- ⨍ ‖w - avg_w‖ ≤ ⨍ (‖u - avg_u‖ + const) = ⨍ ‖u - avg_u‖ + const ≤ M + M = 2M
  have hint_le : ∫ x in B, ‖w x - avg_w‖ ∂volume ≤
      ∫ x in B, (‖u x - avg_u‖ + ⨍ y in B, ‖u y - avg_u‖ ∂volume) ∂volume :=
    setIntegral_mono hnorm_w_sub_avg_int
      (hu_sub_avg_int.norm.add integrableOn_const) (fun x => hpointwise x)
  have hint_split : ∫ x in B, (‖u x - avg_u‖ + ⨍ y in B, ‖u y - avg_u‖ ∂volume) ∂volume =
      (∫ x in B, ‖u x - avg_u‖ ∂volume) +
      (⨍ y in B, ‖u y - avg_u‖ ∂volume) * volume.real B := by
    rw [integral_add hu_sub_avg_int.norm (integrable_const _),
      integral_const, measureReal_restrict_apply_univ,
      smul_eq_mul, mul_comm, measureReal_def]
  -- Convert to averages: ⨍ ‖w - avg_w‖ ≤ ⨍ ‖u - avg_u‖ + ⨍ ‖u - avg_u‖
  set osc_u := ⨍ y in B, ‖u y - avg_u‖ ∂volume with hosc_u_def
  have hfinal : ⨍ x in B, ‖w x - avg_w‖ ∂volume ≤ osc_u + osc_u := by
    -- All averages are (volR B)⁻¹ • ∫
    -- From hint_le + hint_split:
    -- ∫ ‖w - avg_w‖ ≤ ∫ ‖u - avg_u‖ + osc_u * volR B
    -- So ⨍ ‖w - avg_w‖ = (volR B)⁻¹ * ∫ ‖w - avg_w‖
    --    ≤ (volR B)⁻¹ * (∫ ‖u - avg_u‖ + osc_u * volR B)
    --    = (volR B)⁻¹ * ∫ ‖u - avg_u‖ + osc_u
    --    = ⨍ ‖u - avg_u‖ + osc_u = osc_u + osc_u
    have hle_int : ∫ x in B, ‖w x - avg_w‖ ∂volume ≤
        (∫ x in B, ‖u x - avg_u‖ ∂volume) + osc_u * volume.real B := by
      linarith [hint_le, hint_split]
    -- osc_u * volume.real B = ∫ ‖u - avg_u‖
    have hosc_vol : osc_u * volume.real B = ∫ x in B, ‖u x - avg_u‖ ∂volume := by
      rw [hosc_u_def, setAverage_eq, smul_eq_mul, mul_comm (volume.real B)⁻¹,
        mul_assoc, inv_mul_cancel₀ hvolR_ne_zero, mul_one]
    -- So ∫ ‖w - avg_w‖ ≤ 2 * ∫ ‖u - avg_u‖
    have hle_int2 : ∫ x in B, ‖w x - avg_w‖ ∂volume ≤
        2 * ∫ x in B, ‖u x - avg_u‖ ∂volume := by linarith [hosc_vol]
    -- Divide by volume.real B
    show ⨍ x in B, ‖w x - avg_w‖ ∂volume ≤ osc_u + osc_u
    rw [hosc_u_def, setAverage_eq, setAverage_eq, smul_eq_mul, smul_eq_mul]
    calc (volume.real B)⁻¹ * ∫ x in B, ‖w x - avg_w‖ ∂volume
        ≤ (volume.real B)⁻¹ * (2 * ∫ x in B, ‖u x - avg_u‖ ∂volume) :=
          mul_le_mul_of_nonneg_left hle_int2 (inv_nonneg.mpr hvolR_pos.le)
      _ = 2 * ((volume.real B)⁻¹ * ∫ x in B, ‖u x - avg_u‖ ∂volume) := by ring
      _ = (volume.real B)⁻¹ * ∫ x in B, ‖u x - avg_u‖ ∂volume +
          (volume.real B)⁻¹ * ∫ x in B, ‖u x - avg_u‖ ∂volume := by ring
  calc ⨍ x in B, ‖w x - avg_w‖ ∂volume
      ≤ osc_u + osc_u := hfinal
    _ ≤ M + M := by linarith [hu_bmo]
    _ = 2 * M := by ring

/-- The average on a sub-ball differs from the average on a larger ball by at most
the volume ratio times the mean oscillation on the larger ball. -/
lemma abs_subballAverage_sub_ballAverage_le
    {u : E → ℝ} {x c : E} {r s : ℝ}
    (hr : 0 < r) (hs : 0 < s)
    (hsub : Metric.ball c s ⊆ Metric.ball x r)
    (hu_int : IntegrableOn u (Metric.ball x r) volume) :
    |⨍ z in Metric.ball c s, u z ∂volume - ⨍ z in Metric.ball x r, u z ∂volume| ≤
      (r / s) ^ d * (⨍ z in Metric.ball x r, ‖u z - ⨍ w in Metric.ball x r, u w ∂volume‖ ∂volume) := by
  let S : Set E := Metric.ball c s
  let B : Set E := Metric.ball x r
  let avg : ℝ := ⨍ w in B, u w ∂volume
  have hSfin : volume S ≠ ∞ := measure_ball_lt_top.ne
  have hBfin : volume B ≠ ∞ := measure_ball_lt_top.ne
  have hS0 : volume S ≠ 0 := (measure_ball_pos volume c hs).ne'
  have hB0 : volume B ≠ 0 := (measure_ball_pos volume x hr).ne'
  have hSreal0 : volume.real S ≠ 0 := (MeasureTheory.measureReal_ne_zero_iff hSfin).2 hS0
  have hBreal0 : volume.real B ≠ 0 := (MeasureTheory.measureReal_ne_zero_iff hBfin).2 hB0
  have hSreal_pos : 0 < volume.real S := by
    rwa [lt_iff_le_and_ne, and_iff_right MeasureTheory.measureReal_nonneg, ne_eq, eq_comm]
  have huS_int : IntegrableOn u S volume := hu_int.mono_set hsub
  have hdiff :
      (⨍ z in S, u z ∂volume) - avg = ⨍ z in S, (u z - avg) ∂volume := by
    rw [MeasureTheory.setAverage_eq (μ := volume) (f := u) (s := S),
      MeasureTheory.setAverage_eq (μ := volume) (f := fun z => u z - avg) (s := S)]
    rw [integral_sub huS_int (integrableOn_const hSfin),
      MeasureTheory.setIntegral_const avg]
    simp [smul_eq_mul]
    field_simp [hSreal0]
  have hnorm :
      |⨍ z in S, (u z - avg) ∂volume|
        ≤ ⨍ z in S, |u z - avg| ∂volume := by
    have hnorm' :
        |∫ z in S, (u z - avg) ∂volume| ≤ ∫ z in S, |u z - avg| ∂volume := by
      simpa [Real.norm_eq_abs, avg] using
        (norm_integral_le_integral_norm (fun z => u z - avg) :
          ‖∫ z in S, (u z - avg) ∂volume‖ ≤ ∫ z in S, ‖u z - avg‖ ∂volume)
    have hSreal_inv_nonneg : 0 ≤ (volume.real S)⁻¹ := by positivity
    have hnorm'' := mul_le_mul_of_nonneg_left hnorm' hSreal_inv_nonneg
    calc
      |⨍ z in S, (u z - avg) ∂volume|
          = (volume.real S)⁻¹ * |∫ z in S, (u z - avg) ∂volume| := by
              rw [MeasureTheory.setAverage_eq, smul_eq_mul, abs_mul, abs_inv,
                abs_of_nonneg MeasureTheory.measureReal_nonneg]
      _ ≤ (volume.real S)⁻¹ * ∫ z in S, |u z - avg| ∂volume := hnorm''
      _ = ⨍ z in S, |u z - avg| ∂volume := by
            rw [MeasureTheory.setAverage_eq, smul_eq_mul]
  have habsB_int : IntegrableOn (fun z => |u z - avg|) B volume := by
    simpa [Real.norm_eq_abs, avg] using (hu_int.sub (integrableOn_const hBfin)).norm
  have hmono :
      ∫ z in S, |u z - avg| ∂volume ≤ ∫ z in B, |u z - avg| ∂volume := by
    exact MeasureTheory.setIntegral_mono_set habsB_int
      (Filter.Eventually.of_forall fun z => abs_nonneg (u z - avg))
      (Filter.Eventually.of_forall hsub)
  have hvol :
      volume.real B = (r / s) ^ d * volume.real S := by
    rw [show B = Metric.ball x r by rfl, show S = Metric.ball c s by rfl]
    rw [volumeReal_ball_eq x hr, volumeReal_ball_eq c hs]
    rw [div_pow]
    field_simp [pow_ne_zero _ (ne_of_gt hs)]
  calc
    |⨍ z in S, u z ∂volume - avg|
        = |⨍ z in S, (u z - avg) ∂volume| := by rw [hdiff]
    _ ≤ ⨍ z in S, |u z - avg| ∂volume := hnorm
    _ = (volume.real S)⁻¹ * ∫ z in S, |u z - avg| ∂volume := by
      rw [MeasureTheory.setAverage_eq (μ := volume) (f := fun z => |u z - avg|) (s := S), smul_eq_mul]
    _ ≤ (volume.real S)⁻¹ * ∫ z in B, |u z - avg| ∂volume := by
      gcongr
    _ = (r / s) ^ d * ⨍ z in Metric.ball x r, ‖u z - ⨍ w in Metric.ball x r, u w ∂volume‖ ∂volume := by
      have havg_eq : ⨍ z in Metric.ball x r, ‖u z - ⨍ w in Metric.ball x r, u w ∂volume‖ ∂volume =
        (volume.real B)⁻¹ * ∫ z in B, |u z - avg| ∂volume := by
        rw [MeasureTheory.setAverage_eq, smul_eq_mul]
        congr 1 with z
      rw [havg_eq, hvol, mul_inv]
      have hrs : (r / s) ^ d ≠ 0 := pow_ne_zero d (div_ne_zero (ne_of_gt hr) (ne_of_gt hs))
      field_simp [hSreal0, hrs]

/-- The average shift estimate: `|(u)_B - (u)_{6B}| ≤ 6^d * M`. -/
lemma abs_ballAverage_sub_sixBallAverage_le
    {u : E → ℝ} {x₀ : E} {r M : ℝ} (hr : 0 < r)
    (hu_int : IntegrableOn u (Metric.ball x₀ (6 * r)) volume)
    (hu_bmo : (⨍ x in Metric.ball x₀ (6 * r),
      ‖u x - ⨍ y in Metric.ball x₀ (6 * r), u y ∂volume‖ ∂volume) ≤ M) :
    |⨍ x in Metric.ball x₀ r, u x ∂volume -
      ⨍ x in Metric.ball x₀ (6 * r), u x ∂volume| ≤ 6 ^ d * M := by
  have h6r : 0 < 6 * r := by linarith
  have hsub : Metric.ball x₀ r ⊆ Metric.ball x₀ (6 * r) :=
    Metric.ball_subset_ball (by linarith)
  have hle := abs_subballAverage_sub_ballAverage_le h6r hr hsub (hu_int)
  have hratio : (6 * r / r) ^ d = (6 : ℝ) ^ d := by
    rw [mul_div_cancel_of_imp]
    exact fun h => absurd h (ne_of_gt hr)
  calc |⨍ x in Metric.ball x₀ r, u x ∂volume - ⨍ x in Metric.ball x₀ (6 * r), u x ∂volume|
        ≤ (6 * r / r) ^ d * (⨍ z in Metric.ball x₀ (6 * r), ‖u z - ⨍ w in Metric.ball x₀ (6 * r), u w ∂volume‖ ∂volume) := hle
      _ = 6 ^ d * (⨍ z in Metric.ball x₀ (6 * r), ‖u z - ⨍ w in Metric.ball x₀ (6 * r), u w ∂volume‖ ∂volume) := by rw [hratio]
      _ ≤ 6 ^ d * M := by exact mul_le_mul_of_nonneg_left hu_bmo (by positivity)

/-- Base-scale control: if `lam ≥ 4 * 6^d * M`, then the average of `‖u - avg‖` on every radius
`R` ball centered in `ball(x₀, R)` is at most `lam`. -/
private lemma base_ball_average_le
    {u : E → ℝ} {x₀ : E} {R M lam : ℝ}
    (hR : 0 < R) (hM : 0 < M)
    (hlam_ge : 4 * 6 ^ (d : ℕ) * M ≤ lam)
    (hu_int : IntegrableOn u (Metric.ball x₀ (6 * R)) volume)
    (hu_bmo : ∀ (z : E) (s : ℝ), 0 < s →
      Metric.closedBall z s ⊆ Metric.ball x₀ (6 * R) →
      (⨍ x in Metric.ball z s, ‖u x - ⨍ y in Metric.ball z s, u y ∂volume‖ ∂volume) ≤ M) :
    ∀ x ∈ Metric.ball x₀ R,
      ⨍ y in Metric.ball x R,
        ‖u y - ⨍ z in Metric.ball x₀ R, u z ∂volume‖ ∂volume ≤ lam := by
  set avg := ⨍ z in Metric.ball x₀ R, u z ∂volume
  intro x hx
  have hdx : dist x x₀ < R := Metric.mem_ball.mp hx
  have hcb_xR : Metric.closedBall x R ⊆ Metric.ball x₀ (6 * R) := by
    intro z hz
    rw [Metric.mem_closedBall] at hz
    rw [Metric.mem_ball]
    calc dist z x₀ ≤ dist z x + dist x x₀ := dist_triangle _ _ _
      _ < R + R := by linarith
      _ ≤ 6 * R := by linarith
  have hcb_x2R : Metric.closedBall x (2 * R) ⊆ Metric.ball x₀ (6 * R) := by
    intro z hz
    rw [Metric.mem_closedBall] at hz
    rw [Metric.mem_ball]
    calc dist z x₀ ≤ dist z x + dist x x₀ := dist_triangle _ _ _
      _ < 2 * R + R := by linarith
      _ ≤ 6 * R := by linarith
  have hb_x0R_x2R : Metric.ball x₀ R ⊆ Metric.ball x (2 * R) := by
    intro z hz
    rw [Metric.mem_ball] at hz ⊢
    calc dist z x ≤ dist z x₀ + dist x₀ x := dist_triangle _ _ _
      _ = dist z x₀ + dist x x₀ := by rw [dist_comm x₀ x]
      _ < R + R := by linarith
      _ = 2 * R := by ring
  have hb_xR_x2R : Metric.ball x R ⊆ Metric.ball x (2 * R) :=
    Metric.ball_subset_ball (by linarith)
  have h2R_pos : 0 < 2 * R := by linarith
  have hb_x2R_6R : Metric.ball x (2 * R) ⊆ Metric.ball x₀ (6 * R) :=
    Metric.ball_subset_closedBall.trans hcb_x2R
  have hu_int_x2R : IntegrableOn u (Metric.ball x (2 * R)) volume :=
    hu_int.mono_set hb_x2R_6R
  set avg_x2R := ⨍ z in Metric.ball x (2 * R), u z ∂volume
  set avg_xR := ⨍ z in Metric.ball x R, u z ∂volume
  have hratio : (2 * R / R) ^ d = (2 : ℝ) ^ d := by
    rw [mul_div_cancel_of_imp]
    exact fun h => absurd h (ne_of_gt hR)
  have havg_diff_R : |avg - avg_x2R| ≤ (2 : ℝ) ^ d * M := by
    calc |avg - avg_x2R|
        ≤ (2 * R / R) ^ d * (⨍ z in Metric.ball x (2 * R),
            ‖u z - avg_x2R‖ ∂volume) :=
          abs_subballAverage_sub_ballAverage_le h2R_pos hR hb_x0R_x2R hu_int_x2R
      _ = (2 : ℝ) ^ d * (⨍ z in Metric.ball x (2 * R),
            ‖u z - avg_x2R‖ ∂volume) := by rw [hratio]
      _ ≤ (2 : ℝ) ^ d * M := by
          gcongr
          exact hu_bmo x (2 * R) h2R_pos hcb_x2R
  have havg_diff_xR : |avg_xR - avg_x2R| ≤ (2 : ℝ) ^ d * M := by
    calc |avg_xR - avg_x2R|
        ≤ (2 * R / R) ^ d * (⨍ z in Metric.ball x (2 * R),
            ‖u z - avg_x2R‖ ∂volume) :=
          abs_subballAverage_sub_ballAverage_le h2R_pos hR hb_xR_x2R hu_int_x2R
      _ = (2 : ℝ) ^ d * (⨍ z in Metric.ball x (2 * R),
            ‖u z - avg_x2R‖ ∂volume) := by rw [hratio]
      _ ≤ (2 : ℝ) ^ d * M := by
          gcongr
          exact hu_bmo x (2 * R) h2R_pos hcb_x2R
  have havg_shift : |avg_xR - avg| ≤ (2 : ℝ) ^ d * M + (2 : ℝ) ^ d * M := by
    have htri : |avg_xR - avg| ≤ |avg_xR - avg_x2R| + |avg_x2R - avg| := by
      have : avg_xR - avg = (avg_xR - avg_x2R) + (avg_x2R - avg) := by ring
      calc |avg_xR - avg| = |(avg_xR - avg_x2R) + (avg_x2R - avg)| := by rw [this]
        _ ≤ |avg_xR - avg_x2R| + |avg_x2R - avg| := abs_add_le _ _
    have h2 : |avg_x2R - avg| ≤ (2 : ℝ) ^ d * M := by
      rw [abs_sub_comm]
      exact havg_diff_R
    linarith
  have hu_int_xR : IntegrableOn u (Metric.ball x R) volume :=
    hu_int.mono_set (Metric.ball_subset_closedBall.trans hcb_xR)
  have hfin_xR : volume (Metric.ball x R) ≠ ⊤ := measure_ball_lt_top.ne
  have hne_xR : volume (Metric.ball x R) ≠ 0 := (measure_ball_pos volume x hR).ne'
  have hvolR_pos' : 0 < volume.real (Metric.ball x R) :=
    ENNReal.toReal_pos hne_xR hfin_xR
  have hvolR_ne' : volume.real (Metric.ball x R) ≠ 0 := ne_of_gt hvolR_pos'
  have hint_sub : IntegrableOn (fun y => u y - avg) (Metric.ball x R) volume :=
    hu_int_xR.sub integrableOn_const
  have hint_sub_xR : IntegrableOn (fun y => u y - avg_xR) (Metric.ball x R) volume :=
    hu_int_xR.sub integrableOn_const
  have hint_norm : ∫ y in Metric.ball x R, ‖u y - avg‖ ∂volume ≤
      (∫ y in Metric.ball x R, ‖u y - avg_xR‖ ∂volume) +
      |avg_xR - avg| * volume.real (Metric.ball x R) := by
    have hpw : ∀ y, ‖u y - avg‖ ≤ ‖u y - avg_xR‖ + |avg_xR - avg| := by
      intro y
      have : u y - avg = (u y - avg_xR) + (avg_xR - avg) := by ring
      calc ‖u y - avg‖ = ‖(u y - avg_xR) + (avg_xR - avg)‖ := by rw [this]
        _ ≤ ‖u y - avg_xR‖ + ‖avg_xR - avg‖ := norm_add_le _ _
        _ = ‖u y - avg_xR‖ + |avg_xR - avg| := by simp only [Real.norm_eq_abs]
    have h1 : ∫ y in Metric.ball x R, ‖u y - avg‖ ∂volume ≤
        ∫ y in Metric.ball x R, (‖u y - avg_xR‖ + |avg_xR - avg|) ∂volume :=
      MeasureTheory.setIntegral_mono hint_sub.norm
        (hint_sub_xR.norm.add integrableOn_const) hpw
    have h2 : ∫ y in Metric.ball x R, (‖u y - avg_xR‖ + |avg_xR - avg|) ∂volume =
        (∫ y in Metric.ball x R, ‖u y - avg_xR‖ ∂volume) +
        |avg_xR - avg| * volume.real (Metric.ball x R) := by
      rw [integral_add hint_sub_xR.norm integrableOn_const,
        integral_const, measureReal_restrict_apply_univ, smul_eq_mul, mul_comm]
    linarith
  rw [MeasureTheory.setAverage_eq, smul_eq_mul]
  calc (volume.real (Metric.ball x R))⁻¹ * ∫ y in Metric.ball x R, ‖u y - avg‖ ∂volume
      ≤ (volume.real (Metric.ball x R))⁻¹ *
        ((∫ y in Metric.ball x R, ‖u y - avg_xR‖ ∂volume) +
         |avg_xR - avg| * volume.real (Metric.ball x R)) := by
          apply mul_le_mul_of_nonneg_left hint_norm (inv_nonneg.mpr hvolR_pos'.le)
    _ = (⨍ y in Metric.ball x R, ‖u y - avg_xR‖ ∂volume) + |avg_xR - avg| := by
        rw [mul_add, MeasureTheory.setAverage_eq, smul_eq_mul]
        congr 1
        field_simp [hvolR_ne']
    _ ≤ M + ((2 : ℝ) ^ d * M + (2 : ℝ) ^ d * M) := by
        gcongr
        exact hu_bmo x R hR hcb_xR
    _ ≤ 4 * (6 : ℝ) ^ d * M := by
        have h2le6 : (2 : ℝ) ^ d ≤ (6 : ℝ) ^ d :=
          pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) (show (2 : ℝ) ≤ 6 by norm_num) d
        have h1le : (1 : ℝ) ≤ (6 : ℝ) ^ d :=
          one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 6)
        nlinarith
    _ ≤ lam := hlam_ge

private def JNBadCenterSet
    (w : E → ℝ) (x₀ : E) (R lam : ℝ) : Set E :=
  {x ∈ Metric.ball x₀ R | ∃ r, 0 < r ∧ r ≤ R ∧
    lam < ⨍ y in Metric.ball x r, w y ∂volume}

/-- A raw bad witness ball for the John-Nirenberg Calderón-Zygmund decomposition. -/
private structure JNBadWitness
    (w : E → ℝ) (x₀ : E) (R lam : ℝ) where
  center : E
  witnessRadius : ℝ
  center_mem : center ∈ Metric.ball x₀ R
  radius_pos : 0 < witnessRadius
  radius_le : witnessRadius ≤ R
  bad : lam < ⨍ y in Metric.ball center witnessRadius, w y ∂volume

private lemma JNBadWitness.mem_badCenterSet
    {w : E → ℝ} {x₀ : E} {R lam : ℝ}
    (p : JNBadWitness w x₀ R lam) :
    p.center ∈ JNBadCenterSet w x₀ R lam := by
  refine ⟨p.center_mem, p.witnessRadius, p.radius_pos, p.radius_le, p.bad⟩

private noncomputable def weakenBadWitness
    {w : E → ℝ} {x₀ : E} {R lam₁ lam₂ : ℝ}
    (hlam : lam₁ ≤ lam₂) (p : JNBadWitness w x₀ R lam₂) :
    JNBadWitness w x₀ R lam₁ where
  center := p.center
  witnessRadius := p.witnessRadius
  center_mem := p.center_mem
  radius_pos := p.radius_pos
  radius_le := p.radius_le
  bad := lt_of_le_of_lt hlam p.bad

private noncomputable def witnessStepRadius
    {w : E → ℝ} {x₀ : E} {R lam : ℝ}
    (p : JNBadWitness w x₀ R lam) (n : ℕ) : ℝ :=
  min (((n + 1 : ℕ) : ℝ) * p.witnessRadius) R

private lemma witnessStepRadius_zero
    {w : E → ℝ} {x₀ : E} {R lam : ℝ}
    (p : JNBadWitness w x₀ R lam) :
    witnessStepRadius p 0 = p.witnessRadius := by
  simp [witnessStepRadius, p.radius_le]

private lemma witnessStepRadius_pos
    {w : E → ℝ} {x₀ : E} {R lam : ℝ}
    (hR : 0 < R) (p : JNBadWitness w x₀ R lam) (n : ℕ) :
    0 < witnessStepRadius p n := by
  dsimp [witnessStepRadius]
  refine lt_min ?_ hR
  have hsucc : 0 < (((n + 1 : ℕ) : ℝ)) := by
    exact_mod_cast (Nat.succ_pos n)
  exact mul_pos hsucc p.radius_pos

private lemma witnessStepRadius_le_R
    {w : E → ℝ} {x₀ : E} {R lam : ℝ}
    (p : JNBadWitness w x₀ R lam) (n : ℕ) :
    witnessStepRadius p n ≤ R := by
  dsimp [witnessStepRadius]
  exact min_le_right _ _

private lemma witnessStepRadius_mono
    {w : E → ℝ} {x₀ : E} {R lam : ℝ}
    (p : JNBadWitness w x₀ R lam) {n m : ℕ} (hnm : n ≤ m) :
    witnessStepRadius p n ≤ witnessStepRadius p m := by
  dsimp [witnessStepRadius]
  apply min_le_min
  · have hnm' : (((n + 1 : ℕ) : ℝ)) ≤ (((m + 1 : ℕ) : ℝ)) := by
      exact_mod_cast (Nat.succ_le_succ hnm)
    exact mul_le_mul_of_nonneg_right hnm' p.radius_pos.le
  · exact le_rfl

private lemma witnessStepRadius_succ_le_double
    {w : E → ℝ} {x₀ : E} {R lam : ℝ}
    (hR : 0 < R) (p : JNBadWitness w x₀ R lam) (n : ℕ) :
    witnessStepRadius p (n + 1) ≤ 2 * witnessStepRadius p n := by
  by_cases hstep : (((n + 1 : ℕ) : ℝ) * p.witnessRadius) ≤ R
  · have hcurr :
        witnessStepRadius p n = ((n + 1 : ℕ) : ℝ) * p.witnessRadius := by
      rw [witnessStepRadius, min_eq_left hstep]
    calc
      witnessStepRadius p (n + 1) ≤ (((n + 2 : ℕ) : ℝ) * p.witnessRadius) := by
        dsimp [witnessStepRadius]
        exact min_le_left _ _
      _ ≤ 2 * (((n + 1 : ℕ) : ℝ) * p.witnessRadius) := by
        have hcoeff_nat : n + 2 ≤ 2 * (n + 1) := by
          omega
        have hcoeff : (((n + 2 : ℕ) : ℝ)) ≤ 2 * (((n + 1 : ℕ) : ℝ)) := by
          exact_mod_cast hcoeff_nat
        calc
          (((n + 2 : ℕ) : ℝ) * p.witnessRadius)
              ≤ (2 * (((n + 1 : ℕ) : ℝ))) * p.witnessRadius := by
                exact mul_le_mul_of_nonneg_right hcoeff p.radius_pos.le
          _ = 2 * (((n + 1 : ℕ) : ℝ) * p.witnessRadius) := by ring
      _ = 2 * witnessStepRadius p n := by rw [hcurr]
  · have hcurr : witnessStepRadius p n = R := by
      rw [witnessStepRadius, min_eq_right (le_of_not_ge hstep)]
    calc
      witnessStepRadius p (n + 1) ≤ R := witnessStepRadius_le_R p (n + 1)
      _ = witnessStepRadius p n := by rw [hcurr]
      _ ≤ 2 * witnessStepRadius p n := by
          nlinarith [witnessStepRadius_pos hR p n]

private lemma exists_nonbad_stepIndex
    {w : E → ℝ} {x₀ : E} {R lam : ℝ}
    (_hR : 0 < R)
    (p : JNBadWitness w x₀ R lam)
    (havg_base : ∀ x ∈ Metric.ball x₀ R,
      ⨍ y in Metric.ball x R, w y ∂volume ≤ lam) :
    ∃ n : ℕ,
      ⨍ y in Metric.ball p.center (witnessStepRadius p n), w y ∂volume ≤ lam := by
  let N : ℕ := Nat.ceil (R / p.witnessRadius)
  have hRN : R ≤ ((N : ℕ) : ℝ) * p.witnessRadius := by
    exact (div_le_iff₀ p.radius_pos).mp (Nat.le_ceil (R / p.witnessRadius))
  have hstepN : witnessStepRadius p N = R := by
    rw [witnessStepRadius, min_eq_right]
    have hNsucc : (((N + 1 : ℕ) : ℝ) * p.witnessRadius) ≥ ((N : ℕ) : ℝ) * p.witnessRadius := by
      have hsucc : ((N : ℕ) : ℝ) ≤ (((N + 1 : ℕ) : ℝ)) := by
        exact_mod_cast (Nat.le_succ N)
      exact mul_le_mul_of_nonneg_right hsucc p.radius_pos.le
    exact le_trans hRN hNsucc
  refine ⟨N, ?_⟩
  rw [hstepN]
  exact havg_base p.center p.center_mem

private noncomputable def stoppingIndexBad
    {w : E → ℝ} {x₀ : E} {R lam : ℝ}
    (hR : 0 < R)
    (havg_base : ∀ x ∈ Metric.ball x₀ R,
      ⨍ y in Metric.ball x R, w y ∂volume ≤ lam)
    (p : JNBadWitness w x₀ R lam) : ℕ :=
  Nat.find (exists_nonbad_stepIndex hR p havg_base)

private lemma stoppingIndexBad_spec
    {w : E → ℝ} {x₀ : E} {R lam : ℝ}
    (hR : 0 < R)
    (havg_base : ∀ x ∈ Metric.ball x₀ R,
      ⨍ y in Metric.ball x R, w y ∂volume ≤ lam)
    (p : JNBadWitness w x₀ R lam) :
    ⨍ y in Metric.ball p.center (witnessStepRadius p (stoppingIndexBad hR havg_base p)),
      w y ∂volume ≤ lam := by
  exact Nat.find_spec (exists_nonbad_stepIndex hR p havg_base)

private lemma stoppingIndexBad_pos
    {w : E → ℝ} {x₀ : E} {R lam : ℝ}
    (hR : 0 < R)
    (havg_base : ∀ x ∈ Metric.ball x₀ R,
      ⨍ y in Metric.ball x R, w y ∂volume ≤ lam)
    (p : JNBadWitness w x₀ R lam) :
    1 ≤ stoppingIndexBad hR havg_base p := by
  have hspec := stoppingIndexBad_spec hR havg_base p
  have hneq : stoppingIndexBad hR havg_base p ≠ 0 := by
    intro hzero
    rw [hzero, witnessStepRadius_zero p] at hspec
    linarith [p.bad]
  exact Nat.succ_le_of_lt (Nat.pos_of_ne_zero hneq)

private lemma stoppingIndexBad_prev_bad
    {w : E → ℝ} {x₀ : E} {R lam : ℝ}
    (hR : 0 < R)
    (havg_base : ∀ x ∈ Metric.ball x₀ R,
      ⨍ y in Metric.ball x R, w y ∂volume ≤ lam)
    (p : JNBadWitness w x₀ R lam) (m : ℕ)
    (hm : m < stoppingIndexBad hR havg_base p) :
    lam <
      ⨍ y in Metric.ball p.center (witnessStepRadius p m), w y ∂volume := by
  exact not_le.mp (Nat.find_min (exists_nonbad_stepIndex hR p havg_base) hm)

private noncomputable def stoppingRadiusBad
    {w : E → ℝ} {x₀ : E} {R lam : ℝ}
    (hR : 0 < R)
    (havg_base : ∀ x ∈ Metric.ball x₀ R,
      ⨍ y in Metric.ball x R, w y ∂volume ≤ lam)
    (p : JNBadWitness w x₀ R lam) : ℝ :=
  witnessStepRadius p (stoppingIndexBad hR havg_base p - 1)

private noncomputable def stoppingParentRadiusBad
    {w : E → ℝ} {x₀ : E} {R lam : ℝ}
    (hR : 0 < R)
    (havg_base : ∀ x ∈ Metric.ball x₀ R,
      ⨍ y in Metric.ball x R, w y ∂volume ≤ lam)
    (p : JNBadWitness w x₀ R lam) : ℝ :=
  witnessStepRadius p (stoppingIndexBad hR havg_base p)

private lemma stoppingRadiusBad_pos
    {w : E → ℝ} {x₀ : E} {R lam : ℝ}
    (hR : 0 < R)
    (havg_base : ∀ x ∈ Metric.ball x₀ R,
      ⨍ y in Metric.ball x R, w y ∂volume ≤ lam)
    (p : JNBadWitness w x₀ R lam) :
    0 < stoppingRadiusBad hR havg_base p := by
  dsimp [stoppingRadiusBad]
  exact witnessStepRadius_pos hR p _

private lemma stoppingRadiusBad_le_R
    {w : E → ℝ} {x₀ : E} {R lam : ℝ}
    (hR : 0 < R)
    (havg_base : ∀ x ∈ Metric.ball x₀ R,
      ⨍ y in Metric.ball x R, w y ∂volume ≤ lam)
    (p : JNBadWitness w x₀ R lam) :
    stoppingRadiusBad hR havg_base p ≤ R := by
  dsimp [stoppingRadiusBad]
  exact witnessStepRadius_le_R p _

private lemma stoppingRadiusBad_bad
    {w : E → ℝ} {x₀ : E} {R lam : ℝ}
    (hR : 0 < R)
    (havg_base : ∀ x ∈ Metric.ball x₀ R,
      ⨍ y in Metric.ball x R, w y ∂volume ≤ lam)
    (p : JNBadWitness w x₀ R lam) :
    lam <
      ⨍ y in Metric.ball p.center (stoppingRadiusBad hR havg_base p), w y ∂volume := by
  dsimp [stoppingRadiusBad]
  exact stoppingIndexBad_prev_bad hR havg_base p
    (stoppingIndexBad hR havg_base p - 1) (by
      have hpos := stoppingIndexBad_pos hR havg_base p
      omega)

private lemma stoppingParentRadiusBad_le
    {w : E → ℝ} {x₀ : E} {R lam : ℝ}
    (hR : 0 < R)
    (havg_base : ∀ x ∈ Metric.ball x₀ R,
      ⨍ y in Metric.ball x R, w y ∂volume ≤ lam)
    (p : JNBadWitness w x₀ R lam) :
    ⨍ y in Metric.ball p.center (stoppingParentRadiusBad hR havg_base p), w y ∂volume ≤ lam := by
  exact stoppingIndexBad_spec hR havg_base p

private lemma stoppingParentRadiusBad_pos
    {w : E → ℝ} {x₀ : E} {R lam : ℝ}
    (hR : 0 < R)
    (havg_base : ∀ x ∈ Metric.ball x₀ R,
      ⨍ y in Metric.ball x R, w y ∂volume ≤ lam)
    (p : JNBadWitness w x₀ R lam) :
    0 < stoppingParentRadiusBad hR havg_base p := by
  dsimp [stoppingParentRadiusBad]
  exact witnessStepRadius_pos hR p _

private lemma stoppingRadiusBad_le_parent
    {w : E → ℝ} {x₀ : E} {R lam : ℝ}
    (hR : 0 < R)
    (havg_base : ∀ x ∈ Metric.ball x₀ R,
      ⨍ y in Metric.ball x R, w y ∂volume ≤ lam)
    (p : JNBadWitness w x₀ R lam) :
    stoppingRadiusBad hR havg_base p ≤
      stoppingParentRadiusBad hR havg_base p := by
  have hidx :
      stoppingIndexBad hR havg_base p - 1 ≤
        stoppingIndexBad hR havg_base p := by
    omega
  dsimp [stoppingRadiusBad, stoppingParentRadiusBad]
  exact witnessStepRadius_mono p hidx

private lemma stoppingParentRadiusBad_le_double
    {w : E → ℝ} {x₀ : E} {R lam : ℝ}
    (hR : 0 < R)
    (havg_base : ∀ x ∈ Metric.ball x₀ R,
      ⨍ y in Metric.ball x R, w y ∂volume ≤ lam)
    (p : JNBadWitness w x₀ R lam) :
    stoppingParentRadiusBad hR havg_base p ≤
      2 * stoppingRadiusBad hR havg_base p := by
  have hpos := stoppingIndexBad_pos hR havg_base p
  have hstep :=
    witnessStepRadius_succ_le_double hR p (stoppingIndexBad hR havg_base p - 1)
  have hidx :
      stoppingIndexBad hR havg_base p =
        (stoppingIndexBad hR havg_base p - 1) + 1 := by
    omega
  dsimp [stoppingParentRadiusBad, stoppingRadiusBad]
  rw [hidx]
  exact hstep

private lemma stoppingRadiusBad_mono
    {w : E → ℝ} {x₀ : E} {R lam₁ lam₂ : ℝ}
    (hR : 0 < R)
    (havg_base₁ : ∀ x ∈ Metric.ball x₀ R,
      ⨍ y in Metric.ball x R, w y ∂volume ≤ lam₁)
    (havg_base₂ : ∀ x ∈ Metric.ball x₀ R,
      ⨍ y in Metric.ball x R, w y ∂volume ≤ lam₂)
    (hlam : lam₁ ≤ lam₂)
    (p₂ : JNBadWitness w x₀ R lam₂) :
    stoppingRadiusBad hR havg_base₂ p₂ ≤
      stoppingRadiusBad hR havg_base₁ (weakenBadWitness hlam p₂) := by
  let p₁ : JNBadWitness w x₀ R lam₁ := weakenBadWitness hlam p₂
  have hidx :
      stoppingIndexBad hR havg_base₂ p₂ ≤
        stoppingIndexBad hR havg_base₁ p₁ := by
    have hspec₁ := stoppingIndexBad_spec hR havg_base₁ p₁
    exact Nat.find_min' (exists_nonbad_stepIndex hR p₂ havg_base₂) (le_trans hspec₁ hlam)
  have hpos₂ := stoppingIndexBad_pos hR havg_base₂ p₂
  have hpos₁ := stoppingIndexBad_pos hR havg_base₁ p₁
  dsimp [stoppingRadiusBad]
  exact witnessStepRadius_mono p₁ (by
    have : stoppingIndexBad hR havg_base₂ p₂ - 1 ≤
        stoppingIndexBad hR havg_base₁ p₁ - 1 := by
      omega
    exact this)

/-- **John-Nirenberg iteration from a base level.**

This is a variant of `john_nirenberg` (and `john_nirenberg_iteration`) where the
one-step decay hypothesis `h_decay` is only assumed for `lam ≥ A` (instead of for
all `lam > 0`). The exponential decay conclusion holds for all `t > 0`, with a
slightly larger constant prefactor `1/θ²` to absorb the base case `t ≤ A`.

**Proof sketch (pure math)**:
- For `t > A`: decompose `t = A + k·A + r` with `0 < r ≤ A`. Iterate h_decay
  `k` times from level `A + r` to get `vol(E_t) ≤ θ^k · vol(E_{A+r}) ≤ θ^k · vol(B)`.
  The exponential bound follows from `θ^k ≤ (1/θ²) · exp(-t · (-log θ / A))`.
- For `t ≤ A`: `vol(E_t) ≤ vol(B)` trivially, and the RHS is at least
  `(1/θ²) · vol(B) · exp(-A · (-log θ / A)) = (1/θ²) · vol(B) · θ ≥ vol(B)/θ ≥ vol(B)`. -/
theorem john_nirenberg_from_base
    {u : E → ℝ} {x₀ : E} {r : ℝ} {A θ : ℝ}
    (_hr : 0 < r) (hu_meas : Measurable u)
    (hA : 0 < A) (hθ_pos : 0 < θ) (hθ_lt : θ < 1)
    (h_decay : ∀ lam : ℝ, A ≤ lam →
      volume ({x ∈ Metric.ball x₀ r |
        ‖u x - ⨍ y in Metric.ball x₀ r, u y ∂volume‖ > lam + A}) ≤
        ENNReal.ofReal θ *
          volume ({x ∈ Metric.ball x₀ r |
            ‖u x - ⨍ y in Metric.ball x₀ r, u y ∂volume‖ > lam}))
    (t : ℝ) (_ht : 0 < t) :
    volume ({x ∈ Metric.ball x₀ r |
      ‖u x - ⨍ y in Metric.ball x₀ r, u y ∂volume‖ > t}) ≤
    ENNReal.ofReal (1 / θ ^ 2) * volume (Metric.ball x₀ r) *
      ENNReal.ofReal (Real.exp (-t * (-Real.log θ / A))) := by
  -- This is a purely mathematical iteration argument (no CZ covering involved).
  -- The proof decomposes t into base + iterated steps, applies h_decay iteratively,
  -- and bounds the resulting geometric series by the exponential.
  set avg := ⨍ y in Metric.ball x₀ r, u y ∂volume
  set B := Metric.ball x₀ r with hB_def
  set F : ℝ → Set E := fun s => {x ∈ B | ‖u x - avg‖ > s + A} with hF_def
  have hB_meas : MeasurableSet B := by
    simpa [hB_def] using (measurableSet_ball : MeasurableSet (Metric.ball x₀ r))
  have hF_sub : ∀ s, F s ⊆ B := by
    intro s x hx
    exact hx.1
  have hF_meas : ∀ s, MeasurableSet (F s) := by
    intro s
    refine hB_meas.inter ?_
    exact measurableSet_lt measurable_const ((hu_meas.sub_const avg).norm)
  have hF_anti : ∀ s₁ s₂, s₁ ≤ s₂ → F s₂ ⊆ F s₁ := by
    intro s₁ s₂ hs x hx
    refine ⟨hx.1, ?_⟩
    have hs' : s₁ + A ≤ s₂ + A := by linarith
    exact lt_of_le_of_lt hs' hx.2
  have h_decayF : ∀ s : ℝ, 0 < s →
      volume (F (s + A)) ≤ ENNReal.ofReal θ * volume (F s) := by
    intro s hs
    have hsA : A ≤ s + A := by linarith
    simpa [F, add_assoc, avg, B] using h_decay (s + A) hsA
  have h_iter :=
    john_nirenberg_iteration hB_meas
      (measure_ball_lt_top (μ := volume) (x := x₀) (r := r)).ne
      hF_sub hF_meas hF_anti hA hθ_pos hθ_lt h_decayF
  have hAdiv : A * (-Real.log θ / A) = -Real.log θ := by
    field_simp [hA.ne']
  have hexpA : Real.exp (-A * (-Real.log θ / A)) = θ := by
    have hexp_arg : -A * (-Real.log θ / A) = Real.log θ := by
      calc
        -A * (-Real.log θ / A) = -(A * (-Real.log θ / A)) := by ring
        _ = -(-Real.log θ) := by rw [hAdiv]
        _ = Real.log θ := by ring
    rw [hexp_arg, Real.exp_log hθ_pos]
  by_cases htA : A < t
  · have hs_pos : 0 < t - A := by linarith
    have hmain :
        volume ({x ∈ Metric.ball x₀ r | ‖u x - avg‖ > t}) ≤
          ENNReal.ofReal (1 / θ) * volume (Metric.ball x₀ r) *
            ENNReal.ofReal (Real.exp (-(t - A) * (-Real.log θ / A))) := by
      simpa [F, hB_def, avg, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
        h_iter (t - A) hs_pos
    have hexp_shift :
        Real.exp (-(t - A) * (-Real.log θ / A)) =
          (1 / θ) * Real.exp (-t * (-Real.log θ / A)) := by
      have h_inv : (1 / θ : ℝ) = Real.exp (-Real.log θ) := by
        rw [Real.exp_neg, Real.exp_log hθ_pos, one_div]
      rw [h_inv, ← Real.exp_add]
      congr 1
      calc
        -(t - A) * (-Real.log θ / A)
            = -t * (-Real.log θ / A) + A * (-Real.log θ / A) := by ring
        _ = -t * (-Real.log θ / A) + (-Real.log θ) := by rw [hAdiv]
        _ = -Real.log θ + -t * (-Real.log θ / A) := by ring
    calc
      volume ({x ∈ Metric.ball x₀ r | ‖u x - avg‖ > t})
          ≤ ENNReal.ofReal (1 / θ) * volume (Metric.ball x₀ r) *
              ENNReal.ofReal (Real.exp (-(t - A) * (-Real.log θ / A))) := hmain
      _ = ENNReal.ofReal (1 / θ ^ 2) * volume (Metric.ball x₀ r) *
            ENNReal.ofReal (Real.exp (-t * (-Real.log θ / A))) := by
        rw [hexp_shift, ENNReal.ofReal_mul (by positivity)]
        calc
          ENNReal.ofReal (1 / θ) * volume (Metric.ball x₀ r) *
              (ENNReal.ofReal (1 / θ) * ENNReal.ofReal (Real.exp (-t * (-Real.log θ / A))))
              =
              (ENNReal.ofReal (1 / θ) * ENNReal.ofReal (1 / θ)) * volume (Metric.ball x₀ r) *
                ENNReal.ofReal (Real.exp (-t * (-Real.log θ / A))) := by
                ring
          _ = ENNReal.ofReal ((1 / θ) * (1 / θ)) * volume (Metric.ball x₀ r) *
                ENNReal.ofReal (Real.exp (-t * (-Real.log θ / A))) := by
                rw [← ENNReal.ofReal_mul (by positivity)]
          _ = ENNReal.ofReal (1 / θ ^ 2) * volume (Metric.ball x₀ r) *
                ENNReal.ofReal (Real.exp (-t * (-Real.log θ / A))) := by
                congr 1
                field_simp [pow_two, hθ_pos.ne']
  · have ht_le_A : t ≤ A := le_of_not_gt htA
    have hsub :
        {x ∈ Metric.ball x₀ r | ‖u x - avg‖ > t} ⊆ Metric.ball x₀ r := by
      intro x hx
      exact hx.1
    have hrate_pos : 0 < -Real.log θ / A := by
      have hlog_neg : Real.log θ < 0 := Real.log_neg hθ_pos hθ_lt
      exact div_pos (by linarith) hA
    have hexp_lower : θ ≤ Real.exp (-t * (-Real.log θ / A)) := by
      have hArg : -A * (-Real.log θ / A) ≤ -t * (-Real.log θ / A) := by
        nlinarith [ht_le_A, le_of_lt hrate_pos]
      calc
        θ = Real.exp (-A * (-Real.log θ / A)) := by rw [hexpA]
        _ ≤ Real.exp (-t * (-Real.log θ / A)) := Real.exp_le_exp.2 hArg
    have hmul : 1 ≤ (1 / θ ^ 2) * θ := by
      have hθ_ne : θ ≠ 0 := hθ_pos.ne'
      rw [pow_two]
      field_simp [hθ_ne]
      linarith
    have hcoeff : 1 ≤ (1 / θ ^ 2) * Real.exp (-t * (-Real.log θ / A)) := by
      calc
        1 ≤ (1 / θ ^ 2) * θ := hmul
        _ ≤ (1 / θ ^ 2) * Real.exp (-t * (-Real.log θ / A)) := by
            gcongr
    calc
      volume ({x ∈ Metric.ball x₀ r | ‖u x - avg‖ > t})
          ≤ volume (Metric.ball x₀ r) := measure_mono hsub
      _ = ENNReal.ofReal 1 * volume (Metric.ball x₀ r) := by simp
      _ ≤ ENNReal.ofReal ((1 / θ ^ 2) * Real.exp (-t * (-Real.log θ / A))) *
            volume (Metric.ball x₀ r) := by
            have hcoeff' :
                ENNReal.ofReal (1 : ℝ) ≤
                  ENNReal.ofReal ((1 / θ ^ 2) * Real.exp (-t * (-Real.log θ / A))) :=
              ENNReal.ofReal_le_ofReal hcoeff
            exact mul_le_mul_of_nonneg_right hcoeff' (by positivity)
      _ = ENNReal.ofReal (1 / θ ^ 2) * volume (Metric.ball x₀ r) *
            ENNReal.ofReal (Real.exp (-t * (-Real.log θ / A))) := by
            rw [ENNReal.ofReal_mul (by positivity)]
            ring

/-- A set-family John-Nirenberg tail decay theorem from a base-level one-step
decay hypothesis.

This is the reusable set-family analogue of `john_nirenberg_from_base`. It
iterates one-step decay starting from the base level `A` for an arbitrary
antitone measurable family `E_lam`, and is useful when the Calderon-Zygmund /
stopping-time work has already been packaged into such a family and one wants the final
exponential tail bound without rebuilding the iteration argument. -/
theorem level_set_family_from_base
    {B : Set E} {E_lam : ℝ → Set E} {A θ : ℝ}
    (hB_meas : MeasurableSet B) (hB_fin : volume B ≠ ⊤)
    (hE_sub : ∀ lam, E_lam lam ⊆ B)
    (hE_meas : ∀ lam, MeasurableSet (E_lam lam))
    (hE_anti : ∀ lam₁ lam₂, lam₁ ≤ lam₂ → E_lam lam₂ ⊆ E_lam lam₁)
    (hA : 0 < A) (hθ_pos : 0 < θ) (hθ_lt : θ < 1)
    (h_decay : ∀ lam : ℝ, A ≤ lam →
      volume (E_lam (lam + A)) ≤ ENNReal.ofReal θ * volume (E_lam lam))
    (t : ℝ) (_ht : 0 < t) :
    volume (E_lam t) ≤
      ENNReal.ofReal (1 / θ ^ 2) * volume B *
        ENNReal.ofReal (Real.exp (-t * (-Real.log θ / A))) := by
  have h_decayF : ∀ s : ℝ, 0 < s →
      volume (E_lam (s + A + A)) ≤ ENNReal.ofReal θ * volume (E_lam (s + A)) := by
    intro s hs
    have hsA : A ≤ s + A := by linarith
    simpa [add_assoc] using h_decay (s + A) hsA
  set F : ℝ → Set E := fun s => E_lam (s + A) with hF_def
  have hF_sub : ∀ s, F s ⊆ B := by
    intro s
    simpa [F] using hE_sub (s + A)
  have hF_meas : ∀ s, MeasurableSet (F s) := by
    intro s
    simpa [F] using hE_meas (s + A)
  have hF_anti : ∀ s₁ s₂, s₁ ≤ s₂ → F s₂ ⊆ F s₁ := by
    intro s₁ s₂ hs
    simpa [F] using hE_anti (s₁ + A) (s₂ + A) (by linarith)
  have h_iter :=
    john_nirenberg_iteration hB_meas hB_fin hF_sub hF_meas hF_anti hA hθ_pos hθ_lt
      (by
        intro s hs
        simpa [F, add_assoc] using h_decayF s hs)
  have hAdiv : A * (-Real.log θ / A) = -Real.log θ := by
    field_simp [hA.ne']
  have hexpA : Real.exp (-A * (-Real.log θ / A)) = θ := by
    have hexp_arg : -A * (-Real.log θ / A) = Real.log θ := by
      calc
        -A * (-Real.log θ / A) = -(A * (-Real.log θ / A)) := by ring
        _ = -(-Real.log θ) := by rw [hAdiv]
        _ = Real.log θ := by ring
    rw [hexp_arg, Real.exp_log hθ_pos]
  by_cases htA : A < t
  · have hs_pos : 0 < t - A := by linarith
    have hmain :
        volume (E_lam t) ≤
          ENNReal.ofReal (1 / θ) * volume B *
            ENNReal.ofReal (Real.exp (-(t - A) * (-Real.log θ / A))) := by
      simpa [F, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
        h_iter (t - A) hs_pos
    have hexp_shift :
        Real.exp (-(t - A) * (-Real.log θ / A)) =
          (1 / θ) * Real.exp (-t * (-Real.log θ / A)) := by
      have h_inv : (1 / θ : ℝ) = Real.exp (-Real.log θ) := by
        rw [Real.exp_neg, Real.exp_log hθ_pos, one_div]
      rw [h_inv, ← Real.exp_add]
      congr 1
      calc
        -(t - A) * (-Real.log θ / A)
            = -t * (-Real.log θ / A) + A * (-Real.log θ / A) := by ring
        _ = -t * (-Real.log θ / A) + (-Real.log θ) := by rw [hAdiv]
        _ = -Real.log θ + -t * (-Real.log θ / A) := by ring
    calc
      volume (E_lam t)
          ≤ ENNReal.ofReal (1 / θ) * volume B *
              ENNReal.ofReal (Real.exp (-(t - A) * (-Real.log θ / A))) := hmain
      _ = ENNReal.ofReal (1 / θ ^ 2) * volume B *
            ENNReal.ofReal (Real.exp (-t * (-Real.log θ / A))) := by
        rw [hexp_shift, ENNReal.ofReal_mul (by positivity)]
        calc
          ENNReal.ofReal (1 / θ) * volume B *
              (ENNReal.ofReal (1 / θ) * ENNReal.ofReal (Real.exp (-t * (-Real.log θ / A))))
              =
              (ENNReal.ofReal (1 / θ) * ENNReal.ofReal (1 / θ)) * volume B *
                ENNReal.ofReal (Real.exp (-t * (-Real.log θ / A))) := by
                ring
          _ = ENNReal.ofReal ((1 / θ) * (1 / θ)) * volume B *
                ENNReal.ofReal (Real.exp (-t * (-Real.log θ / A))) := by
                rw [← ENNReal.ofReal_mul (by positivity)]
          _ = ENNReal.ofReal (1 / θ ^ 2) * volume B *
                ENNReal.ofReal (Real.exp (-t * (-Real.log θ / A))) := by
                congr 1
                field_simp [pow_two, hθ_pos.ne']
  · have ht_le_A : t ≤ A := le_of_not_gt htA
    have hsub : E_lam t ⊆ B := hE_sub t
    have hrate_pos : 0 < -Real.log θ / A := by
      have hlog_neg : Real.log θ < 0 := Real.log_neg hθ_pos hθ_lt
      exact div_pos (by linarith) hA
    have hexp_lower : θ ≤ Real.exp (-t * (-Real.log θ / A)) := by
      have hArg : -A * (-Real.log θ / A) ≤ -t * (-Real.log θ / A) := by
        nlinarith [ht_le_A, le_of_lt hrate_pos]
      calc
        θ = Real.exp (-A * (-Real.log θ / A)) := by rw [hexpA]
        _ ≤ Real.exp (-t * (-Real.log θ / A)) := Real.exp_le_exp.2 hArg
    have hmul : 1 ≤ (1 / θ ^ 2) * θ := by
      have hθ_ne : θ ≠ 0 := hθ_pos.ne'
      rw [pow_two]
      field_simp [hθ_ne]
      linarith
    have hcoeff : 1 ≤ (1 / θ ^ 2) * Real.exp (-t * (-Real.log θ / A)) := by
      calc
        1 ≤ (1 / θ ^ 2) * θ := hmul
        _ ≤ (1 / θ ^ 2) * Real.exp (-t * (-Real.log θ / A)) := by
            gcongr
    calc
      volume (E_lam t) ≤ volume B := measure_mono hsub
      _ = ENNReal.ofReal 1 * volume B := by simp
      _ ≤ ENNReal.ofReal ((1 / θ ^ 2) * Real.exp (-t * (-Real.log θ / A))) * volume B := by
          have hcoeff' :
              ENNReal.ofReal (1 : ℝ) ≤
                ENNReal.ofReal ((1 / θ ^ 2) * Real.exp (-t * (-Real.log θ / A))) :=
            ENNReal.ofReal_le_ofReal hcoeff
          exact mul_le_mul_of_nonneg_right hcoeff' (by positivity)
      _ = ENNReal.ofReal (1 / θ ^ 2) * volume B *
            ENNReal.ofReal (Real.exp (-t * (-Real.log θ / A))) := by
          rw [ENNReal.ofReal_mul (by positivity)]
          ring

private lemma fivefold_cover_real_le
    {x₀ : E} {R : ℝ} {S : Set E}
    (hS_sub : S ⊆ Metric.ball x₀ (6 * R))
    {ι : Type*} [Countable ι]
    (B : ι → JNBall x₀ R)
    (hcover : S ⊆ ⋃ i : ι, (B i).fivefold)
    (hdisj : ∀ i j : ι, i ≠ j → Disjoint ((B i).carrier) ((B j).carrier)) :
    volume.real S ≤ (5 : ℝ) ^ d * volume.real (⋃ i : ι, (B i).carrier) := by
  let U : Set E := ⋃ i : ι, (B i).carrier
  have hU_sub : U ⊆ Metric.ball x₀ (6 * R) := by
    intro x hx
    rcases Set.mem_iUnion.1 hx with ⟨i, hi⟩
    exact (B i).fivefold_subset_sixBall
      ((Metric.ball_subset_ball (by linarith [(B i).radius_pos])) hi)
  have hS_fin : volume S ≠ ⊤ :=
    measure_ne_top_of_subset hS_sub
      (measure_ball_lt_top (μ := volume) (x := x₀) (r := 6 * R)).ne
  have hU_fin : volume U ≠ ⊤ :=
    measure_ne_top_of_subset hU_sub
      (measure_ball_lt_top (μ := volume) (x := x₀) (r := 6 * R)).ne
  have hU_vol : volume U = ∑' i : ι, volume ((B i).carrier) := by
    exact measure_iUnion hdisj (fun i => (B i).measurableSet_carrier)
  have h1 : volume S ≤ volume (⋃ i : ι, (B i).fivefold) := measure_mono hcover
  have h2 : volume (⋃ i : ι, (B i).fivefold) ≤ ∑' i : ι, volume ((B i).fivefold) :=
    measure_iUnion_le _
  have h3 : ∀ i : ι, volume ((B i).fivefold) =
      ENNReal.ofReal ((5 : ℝ) ^ d) * volume ((B i).carrier) := fun i => (B i).volume_fivefold
  have h4 :
      ∑' i : ι, volume ((B i).fivefold) =
        ENNReal.ofReal ((5 : ℝ) ^ d) * ∑' i : ι, volume ((B i).carrier) := by
    rw [tsum_congr h3, ENNReal.tsum_mul_left]
  rw [h4, ← hU_vol] at h2
  have hmul_fin : ENNReal.ofReal ((5 : ℝ) ^ d) * volume U ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hU_fin
  have hreal := ENNReal.toReal_mono hmul_fin (h1.trans h2)
  rw [ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ (5 : ℝ) ^ d)] at hreal
  simpa [U] using hreal

set_option maxHeartbeats 1000000 in
private lemma assigned_union_half_measure_real
    {u : E → ℝ} {x₀ : E} {R M lam μ A C5 avgR : ℝ}
    (_hR : 0 < R) (_hM : 0 < M)
    (hμ_eq : μ = lam + A)
    (hA_sub_C5_pos : 0 < A - C5)
    (hlocal_coeff :
      2 * M * 5 ^ d / (A - C5) ≤ 1 / (2 * 5 ^ d))
    (hu_int : IntegrableOn u (Metric.ball x₀ (6 * R)) volume)
    (hu_bmo : ∀ (z : E) (s : ℝ), 0 < s →
      Metric.closedBall z s ⊆ Metric.ball x₀ (6 * R) →
      (⨍ x in Metric.ball z s, ‖u x - ⨍ y in Metric.ball z s, u y ∂volume‖ ∂volume) ≤ M)
    (w : E → ℝ) (hw_def : w = fun x => ‖u x - avgR‖)
    {SLam : Type*} {SMu : Type*} [Countable SLam] [Countable SMu]
    (BLam : SLam → JNBall x₀ R) (BMu : SMu → JNBall x₀ R)
    (hBLam_disj : ∀ i j : SLam, i ≠ j → Disjoint ((BLam i).carrier) ((BLam j).carrier))
    (hBMu_disj : ∀ i j : SMu, i ≠ j → Disjoint ((BMu i).carrier) ((BMu j).carrier))
    (assign : SMu → SLam)
    (hassign_sub : ∀ p : SMu, (BMu p).carrier ⊆ (BLam (assign p)).fivefold)
    (havg5_le : ∀ q : SLam, ⨍ x in (BLam q).fivefold, w x ∂volume ≤ lam + C5)
    (hlarge : ∀ p : SMu, μ < ⨍ x in (BMu p).carrier, w x ∂volume) :
    volume.real (⋃ p : SMu, (BMu p).carrier) ≤
      (1 / (2 * 5 ^ d)) * volume.real (⋃ q : SLam, (BLam q).carrier) := by
  have hw_int : IntegrableOn w (Metric.ball x₀ (6 * R)) volume := by
    simpa [hw_def] using (hu_int.sub integrableOn_const).norm
  let V : SLam → Set E := fun q => ⋃ p : {p : SMu // assign p = q}, (BMu p.1).carrier
  have hV_sub : ∀ q : SLam, V q ⊆ (BLam q).fivefold := by
    intro q x hx
    rcases Set.mem_iUnion.1 hx with ⟨p, hp⟩
    have : assign p.1 = q := p.2
    simpa [V, this] using hassign_sub p.1 hp
  have hV_meas : ∀ q : SLam, MeasurableSet (V q) := by
    intro q
    dsimp [V]
    exact (isOpen_iUnion fun _ => isOpen_ball).measurableSet
  have hV_half : ∀ q : SLam,
      volume.real (V q) ≤ (1 / (2 * 5 ^ d)) * volume.real ((BLam q).carrier) := by
    intro q
    let b := BLam q
    let Vq := V q
    let avg5 := ⨍ x in b.fivefold, w x ∂volume
    have hV_sub_five : Vq ⊆ b.fivefold := hV_sub q
    have hV_fin : volume Vq ≠ ⊤ :=
      measure_ne_top_of_subset hV_sub_five measure_ball_lt_top.ne
    have hV_int : IntegrableOn w Vq volume :=
      hw_int.mono_set (fun x hx => b.fivefold_subset_sixBall (hV_sub_five hx))
    have hcomp_disj :
        Pairwise (Function.onFun Disjoint fun p : {p : SMu // assign p = q} =>
          (BMu p.1).carrier) := by
      intro p₁ p₂ hp
      exact hBMu_disj p₁.1 p₂.1 (fun h => hp (Subtype.ext h))
    have hHasSum_vol :
        HasSum (fun p : {p : SMu // assign p = q} =>
            volume.real ((BMu p.1).carrier)) (volume.real Vq) := by
      simpa [Vq, V, MeasureTheory.setIntegral_const] using
        (MeasureTheory.hasSum_integral_iUnion
          (s := fun p : {p : SMu // assign p = q} => (BMu p.1).carrier)
          (f := fun _ => (1 : ℝ))
          (hm := fun p => (BMu p.1).measurableSet_carrier) hcomp_disj
          (hfi := integrableOn_const hV_fin))
    have hHasSum_int :
        HasSum (fun p : {p : SMu // assign p = q} =>
            ∫ x in (BMu p.1).carrier, w x ∂volume) (∫ x in Vq, w x ∂volume) := by
      simpa [Vq, V] using
        (MeasureTheory.hasSum_integral_iUnion
          (s := fun p : {p : SMu // assign p = q} => (BMu p.1).carrier)
          (f := w) (hm := fun p => (BMu p.1).measurableSet_carrier) hcomp_disj hV_int)
    have hV_real_sum :
        volume.real Vq =
          ∑' p : {p : SMu // assign p = q}, volume.real ((BMu p.1).carrier) := by
      simpa using hHasSum_vol.tsum_eq.symm
    have hV_int_sum :
        ∫ x in Vq, w x ∂volume =
          ∑' p : {p : SMu // assign p = q}, ∫ x in (BMu p.1).carrier, w x ∂volume := by
      simpa using hHasSum_int.tsum_eq.symm
    have hlarge_int :
        ∀ p : {p : SMu // assign p = q},
          μ * volume.real ((BMu p.1).carrier) <
            ∫ x in (BMu p.1).carrier, w x ∂volume := by
      intro p
      have hlarge_p : μ < ⨍ x in (BMu p.1).carrier, w x ∂volume := hlarge p.1
      have hvol_pos : 0 < volume.real ((BMu p.1).carrier) :=
        ENNReal.toReal_pos (measure_ball_pos volume _ (BMu p.1).radius_pos).ne'
          measure_ball_lt_top.ne
      have hvol_ne : volume.real ((BMu p.1).carrier) ≠ 0 := ne_of_gt hvol_pos
      have hmul := mul_lt_mul_of_pos_right hlarge_p hvol_pos
      rw [MeasureTheory.setAverage_eq, smul_eq_mul] at hmul
      have hcancel :
          (volume.real ((BMu p.1).carrier))⁻¹ *
              (∫ x in (BMu p.1).carrier, w x ∂volume) *
            volume.real ((BMu p.1).carrier) =
            ∫ x in (BMu p.1).carrier, w x ∂volume := by
        field_simp [hvol_ne]
      simpa [mul_assoc, hcancel] using hmul
    have hsumm_vol := hHasSum_vol.summable
    have hsumm_int := hHasSum_int.summable
    have hsum_lower : μ * volume.real Vq ≤ ∫ x in Vq, w x ∂volume := by
      rw [hV_real_sum, hV_int_sum]
      calc
        μ * ∑' p : {p : SMu // assign p = q}, volume.real ((BMu p.1).carrier)
            = ∑' p : {p : SMu // assign p = q},
                μ * volume.real ((BMu p.1).carrier) := by
                rw [← tsum_mul_left]
        _ ≤ ∑' p : {p : SMu // assign p = q}, ∫ x in (BMu p.1).carrier, w x ∂volume := by
            refine Summable.tsum_le_tsum (fun p => le_of_lt (hlarge_int p)) ?_ hsumm_int
            exact hsumm_vol.mul_left μ
    have havg5_nonneg : 0 ≤ avg5 := by
      dsimp [avg5]
      rw [MeasureTheory.setAverage_eq, smul_eq_mul]
      have hfive_vol_nonneg :
          0 ≤ (volume.real b.fivefold)⁻¹ := by
        have hfive_vol_pos : 0 < volume.real b.fivefold :=
          ENNReal.toReal_pos (measure_ball_pos volume _ (mul_pos (by positivity) b.radius_pos)).ne'
            measure_ball_lt_top.ne
        exact inv_nonneg.mpr hfive_vol_pos.le
      have hnonneg :
          0 ≤ ∫ x in b.fivefold, w x ∂volume :=
        MeasureTheory.integral_nonneg_of_ae
          (Filter.Eventually.of_forall fun x => by
            simp [hw_def])
      exact mul_nonneg hfive_vol_nonneg hnonneg
    have hV_shift_int : IntegrableOn (fun x => w x - avg5) Vq volume :=
      hV_int.sub (integrableOn_const hV_fin)
    have hV_rhs_int :
        IntegrableOn (fun x => ‖w x - avg5‖ + avg5) Vq volume :=
      hV_shift_int.norm.add (integrableOn_const hV_fin)
    have hpw : ∀ x, w x ≤ ‖w x - avg5‖ + avg5 := by
      intro x
      have hw_nonneg : 0 ≤ w x := by
        simp [hw_def]
      calc
        w x = ‖w x‖ := by simp [Real.norm_eq_abs, abs_of_nonneg hw_nonneg]
        _ = ‖(w x - avg5) + avg5‖ := by congr 1; ring
        _ ≤ ‖w x - avg5‖ + ‖avg5‖ := norm_add_le _ _
        _ = ‖w x - avg5‖ + avg5 := by
            simp [Real.norm_eq_abs, abs_of_nonneg havg5_nonneg]
    have hupper0 :
        ∫ x in Vq, w x ∂volume ≤
          ∫ x in Vq, (‖w x - avg5‖ + avg5) ∂volume := by
      exact MeasureTheory.setIntegral_mono hV_int hV_rhs_int hpw
    have hosc_five_int :
        IntegrableOn (fun x => ‖w x - avg5‖) b.fivefold volume := by
      exact (hw_int.mono_set b.fivefold_subset_sixBall).sub
        (integrableOn_const measure_ball_lt_top.ne) |>.norm
    have hosc_V_le :
        ∫ x in Vq, ‖w x - avg5‖ ∂volume ≤
          ∫ x in b.fivefold, ‖w x - avg5‖ ∂volume := by
      exact MeasureTheory.setIntegral_mono_set hosc_five_int
        (Filter.Eventually.of_forall fun x => norm_nonneg (w x - avg5))
        (Filter.Eventually.of_forall hV_sub_five)
    have hosc_avg :
        (⨍ x in b.fivefold, ‖w x - avg5‖ ∂volume) ≤ 2 * M := by
      have h5r_pos : 0 < 5 * b.radius := by
        exact mul_pos (by positivity) b.radius_pos
      have hu_bmo_five :=
        hu_bmo b.center (5 * b.radius) h5r_pos b.closedBall_fivefold_subset_sixBall
      simpa [hw_def, avg5] using
        (abs_sub_const_bmo_le_two (M := M) (u := u) (c := avgR) (z := b.center)
          (s := 5 * b.radius) h5r_pos
          (hu_int := hu_int.mono_set b.fivefold_subset_sixBall)
          (hu_bmo := hu_bmo_five))
    have hfive_vol_pos : 0 < volume.real b.fivefold :=
      ENNReal.toReal_pos (measure_ball_pos volume _ (mul_pos (by positivity) b.radius_pos)).ne'
        measure_ball_lt_top.ne
    have hfive_vol_ne : volume.real b.fivefold ≠ 0 := ne_of_gt hfive_vol_pos
    have hosc_int_le :
        ∫ x in b.fivefold, ‖w x - avg5‖ ∂volume ≤
          2 * M * volume.real b.fivefold := by
      have hEq :
          ∫ x in b.fivefold, ‖w x - avg5‖ ∂volume =
            volume.real b.fivefold *
              (⨍ x in b.fivefold, ‖w x - avg5‖ ∂volume) := by
        rw [MeasureTheory.setAverage_eq, smul_eq_mul]
        field_simp [hfive_vol_ne]
      calc
        ∫ x in b.fivefold, ‖w x - avg5‖ ∂volume
            = volume.real b.fivefold *
                (⨍ x in b.fivefold, ‖w x - avg5‖ ∂volume) := hEq
        _ ≤ volume.real b.fivefold * (2 * M) := by
            exact mul_le_mul_of_nonneg_left hosc_avg hfive_vol_pos.le
        _ = 2 * M * volume.real b.fivefold := by ring
    have hupper :
        ∫ x in Vq, w x ∂volume ≤
          2 * M * volume.real b.fivefold + avg5 * volume.real Vq := by
      calc
        ∫ x in Vq, w x ∂volume
            ≤ ∫ x in Vq, (‖w x - avg5‖ + avg5) ∂volume := hupper0
        _ = ∫ x in Vq, ‖w x - avg5‖ ∂volume + avg5 * volume.real Vq := by
            rw [integral_add hV_shift_int.norm (integrableOn_const hV_fin),
              MeasureTheory.setIntegral_const, smul_eq_mul]
            ring
        _ ≤ ∫ x in b.fivefold, ‖w x - avg5‖ ∂volume + avg5 * volume.real Vq := by
            linarith [hosc_V_le]
        _ ≤ 2 * M * volume.real b.fivefold + avg5 * volume.real Vq := by
            linarith [hosc_int_le]
    have hmain :
        (A - C5) * volume.real Vq ≤ 2 * M * volume.real b.fivefold := by
      have havg5q : avg5 ≤ lam + C5 := by
        simpa [b, avg5] using havg5_le q
      have hupper' :
          ∫ x in Vq, w x ∂volume ≤
            2 * M * volume.real b.fivefold + (lam + C5) * volume.real Vq := by
        have hmul_avg :
            avg5 * volume.real Vq ≤ (lam + C5) * volume.real Vq :=
          mul_le_mul_of_nonneg_right havg5q measureReal_nonneg
        linarith [hupper, hmul_avg]
      have hmain' :
          μ * volume.real Vq ≤
            2 * M * volume.real b.fivefold + (lam + C5) * volume.real Vq := by
        exact le_trans hsum_lower hupper'
      have hmain'' :
          (lam + A) * volume.real Vq ≤
            2 * M * volume.real b.fivefold + (lam + C5) * volume.real Vq := by
        simpa [hμ_eq] using hmain'
      have hVq_nonneg : 0 ≤ volume.real Vq := measureReal_nonneg
      linarith [hmain'', hVq_nonneg]
    have hdiv :
        volume.real Vq ≤ (2 * M * volume.real b.fivefold) / (A - C5) := by
      rw [le_div_iff₀ hA_sub_C5_pos]
      linarith
    calc
      volume.real Vq ≤ (2 * M * volume.real b.fivefold) / (A - C5) := hdiv
      _ = (2 * M / (A - C5)) * volume.real b.fivefold := by ring
      _ = (2 * M * 5 ^ d / (A - C5)) * volume.real b.carrier := by
          rw [b.volumeReal_fivefold]
          ring
      _ ≤ (1 / (2 * 5 ^ d)) * volume.real b.carrier := by
          exact mul_le_mul_of_nonneg_right hlocal_coeff measureReal_nonneg
  let UMu : Set E := ⋃ p : SMu, (BMu p).carrier
  let ULam : Set E := ⋃ q : SLam, (BLam q).carrier
  have hUMu_eq : UMu = ⋃ q : SLam, V q := by
    ext x
    constructor
    · intro hx
      rcases Set.mem_iUnion.1 hx with ⟨p, hp⟩
      exact Set.mem_iUnion.2 ⟨assign p, Set.mem_iUnion.2 ⟨⟨p, rfl⟩, hp⟩⟩
    · intro hx
      rcases Set.mem_iUnion.1 hx with ⟨q, hxq⟩
      rcases Set.mem_iUnion.1 hxq with ⟨p, hp⟩
      exact Set.mem_iUnion.2 ⟨p.1, hp⟩
  have hV_pairwise :
      Pairwise (Function.onFun Disjoint fun q : SLam => V q) := by
    intro q₁ q₂ hq
    refine disjoint_iff_inter_eq_empty.2 ?_
    ext x
    constructor
    · intro hx
      rcases hx with ⟨hx₁, hx₂⟩
      rcases Set.mem_iUnion.1 hx₁ with ⟨p₁, hp₁⟩
      rcases Set.mem_iUnion.1 hx₂ with ⟨p₂, hp₂⟩
      by_cases hp : p₁.1 = p₂.1
      · have : q₁ = q₂ := by
          calc
            q₁ = assign p₁.1 := by simpa using p₁.2.symm
            _ = assign p₂.1 := by simp [hp]
            _ = q₂ := p₂.2
        exact False.elim (hq this)
      · have hxempty :
            x ∈ (∅ : Set E) := by
          exact (hBMu_disj p₁.1 p₂.1 hp).le_bot ⟨hp₁, hp₂⟩
        simp at hxempty
    · intro hx
      simp at hx
  have hUMu_fin : volume UMu ≠ ⊤ := by
    refine measure_ne_top_of_subset ?_
      (measure_ball_lt_top (μ := volume) (x := x₀) (r := 6 * R)).ne
    intro x hx
    rcases Set.mem_iUnion.1 hx with ⟨p, hp⟩
    exact (BMu p).fivefold_subset_sixBall
      ((Metric.ball_subset_ball (by linarith [(BMu p).radius_pos])) hp)
  have hULam_fin : volume ULam ≠ ⊤ := by
    refine measure_ne_top_of_subset ?_
      (measure_ball_lt_top (μ := volume) (x := x₀) (r := 6 * R)).ne
    intro x hx
    rcases Set.mem_iUnion.1 hx with ⟨q, hq⟩
    exact (BLam q).fivefold_subset_sixBall
      ((Metric.ball_subset_ball (by linarith [(BLam q).radius_pos])) hq)
  have hUMu_volV : volume UMu = ∑' q : SLam, volume (V q) := by
    rw [hUMu_eq]
    exact measure_iUnion hV_pairwise hV_meas
  have hULam_vol : volume ULam = ∑' q : SLam, volume ((BLam q).carrier) := by
    exact measure_iUnion (fun p q hpq => hBLam_disj p q hpq)
      (fun q => (BLam q).measurableSet_carrier)
  have hV_fin_each : ∀ q : SLam, volume (V q) ≠ ⊤ := by
    intro q
    exact measure_ne_top_of_subset (hV_sub q) measure_ball_lt_top.ne
  have hV_half_enn :
      ∀ q : SLam,
        volume (V q) ≤
          ENNReal.ofReal (1 / (2 * 5 ^ d)) * volume ((BLam q).carrier) := by
    intro q
    exact volume_real_le_to_ennreal (hV_fin_each q) measure_ball_lt_top.ne
      (by positivity : (0 : ℝ) ≤ 1 / (2 * 5 ^ d)) (hV_half q)
  have henn :
      volume UMu ≤ ENNReal.ofReal (1 / (2 * 5 ^ d)) * volume ULam := by
    rw [hUMu_volV, hULam_vol]
    calc
      ∑' q : SLam, volume (V q)
          ≤ ∑' q : SLam,
              ENNReal.ofReal (1 / (2 * 5 ^ d)) * volume ((BLam q).carrier) :=
            ENNReal.tsum_le_tsum hV_half_enn
      _ = ENNReal.ofReal (1 / (2 * 5 ^ d)) *
            ∑' q : SLam, volume ((BLam q).carrier) := by
              rw [ENNReal.tsum_mul_left]
  have hfin :
      ENNReal.ofReal (1 / (2 * 5 ^ d)) * volume ULam ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hULam_fin
  have hreal := ENNReal.toReal_mono hfin henn
  rw [ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ 1 / (2 * 5 ^ d))] at hreal
  simpa [UMu, ULam] using hreal

private lemma closedBall_ae_eq_ball_of_pos_aux (x : E) {r : ℝ} (hr : 0 < r) :
    Metric.closedBall x r =ᵐ[volume] Metric.ball x r := by
  by_cases hd : d = 0
  · subst hd
    have hball : Metric.ball x r = Set.univ := by
      ext y
      have hyx : y = x := Subsingleton.elim _ _
      simp [Metric.mem_ball, hyx, hr]
    have hclosed : Metric.closedBall x r = Set.univ := by
      ext y
      have hyx : y = x := Subsingleton.elim _ _
      simp [Metric.mem_closedBall, hyx, hr.le]
    simp [hball, hclosed]
  · have hdpos : 0 < d := Nat.pos_of_ne_zero hd
    haveI : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) (M := E) <| by
      simpa [finrank_euclideanSpace] using hdpos
    refine (ae_eq_of_subset_of_measure_ge Metric.ball_subset_closedBall ?_
      measurableSet_ball.nullMeasurableSet measure_closedBall_lt_top.ne).symm
    simpa using le_of_eq (Measure.addHaar_closedBall_eq_addHaar_ball (μ := volume) x r)

private lemma setAverage_closedBall_eq_ball_of_pos_aux
    {u : E → ℝ} (x : E) {r : ℝ} (hr : 0 < r) :
    ⨍ z in Metric.closedBall x r, u z ∂volume =
      ⨍ z in Metric.ball x r, u z ∂volume := by
  exact MeasureTheory.setAverage_congr (closedBall_ae_eq_ball_of_pos_aux x hr)

private lemma tendsto_dyadic_radius_nhdsWithin_zero_aux {ρ : ℝ} (hρ : 0 < ρ) :
    Tendsto (fun n : ℕ => ρ / (2 : ℝ) ^ n) atTop (𝓝[>] 0) := by
  refine (tendsto_nhdsWithin_iff).2 ?_
  refine ⟨?_, Eventually.of_forall ?_⟩
  · have hpow :
        Tendsto (fun n : ℕ => ((1 / 2 : ℝ) ^ n)) atTop (𝓝 (0 : ℝ)) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    simpa [div_eq_mul_inv, one_div, inv_pow, mul_assoc, mul_left_comm, mul_comm] using
      hpow.const_mul ρ
  · intro n
    show ρ / (2 : ℝ) ^ n ∈ Set.Ioi (0 : ℝ)
    simpa [Set.mem_Ioi] using (show 0 < ρ / (2 : ℝ) ^ n by positivity)

private lemma closedBall_subset_ball_of_mem_ball_half_aux
    {x₀ x : E} {R r : ℝ}
    (hx : x ∈ Metric.ball x₀ (R / 2)) (_hr : 0 ≤ r) (hrR : r ≤ R / 2) :
    Metric.closedBall x r ⊆ Metric.ball x₀ R := by
  intro z hz
  have hx' : dist x x₀ < R / 2 := by simpa using hx
  have hz' : dist z x ≤ r := by simpa using hz
  refine Metric.mem_ball.mpr ?_
  calc
    dist z x₀ ≤ dist z x + dist x x₀ := dist_triangle _ _ _
    _ < r + R / 2 := by linarith
    _ ≤ R := by linarith

set_option maxHeartbeats 1600000 in
private lemma ae_pointwise_gt_subset_badCenter
    {w : E → ℝ} {x₀ : E} {R lam : ℝ}
    (hR : 0 < R)
    (hw_int : IntegrableOn w (Metric.ball x₀ (6 * R)) volume) :
    {x ∈ Metric.ball x₀ R | w x > lam} ≤ᵐ[volume] JNBadCenterSet w x₀ R lam := by
  let B : Set E := Metric.ball x₀ R
  let outer : Set E := Metric.ball x₀ (6 * R)
  let ρ : ℝ := R / 2
  let f : E → ℝ := outer.indicator w
  have hρ : 0 < ρ := by
    dsimp [ρ]
    positivity
  have hB_meas : MeasurableSet B := measurableSet_ball
  have hB_sub_outer : B ⊆ outer := by
    simpa [B, outer] using
      (Metric.ball_subset_ball (show R ≤ 6 * R by linarith) :
        Metric.ball x₀ R ⊆ Metric.ball x₀ (6 * R))
  have hf_int : Integrable f volume := by
    exact hw_int.integrable_indicator measurableSet_ball
  have hdiff_ae :
      ∀ᵐ x ∂volume,
        Tendsto (fun n : ℕ => ⨍ y in Metric.closedBall x (ρ / (2 : ℝ) ^ n), f y ∂volume)
          atTop (𝓝 (f x)) := by
    filter_upwards
        [((IsUnifLocDoublingMeasure.vitaliFamily (μ := volume) (K := 0)).ae_tendsto_average
          hf_int.locallyIntegrable)] with x hdx
    exact Tendsto.comp hdx <|
      IsUnifLocDoublingMeasure.tendsto_closedBall_filterAt (μ := volume) (K := 0)
        (fun _ : ℕ => x) (fun n : ℕ => ρ / (2 : ℝ) ^ n)
        (tendsto_dyadic_radius_nhdsWithin_zero_aux hρ)
        (Eventually.of_forall fun n => by
          exact Metric.mem_closedBall_self (x := x)
            (by positivity : 0 ≤ 0 * (ρ / (2 : ℝ) ^ n)))
  filter_upwards [hdiff_ae] with x hdx
  intro hx_point
  rcases hx_point with ⟨hxB, hx_gt⟩
  have hx_outer : x ∈ outer := hB_sub_outer hxB
  have hclosed_to_w :
      Tendsto (fun n : ℕ => ⨍ y in Metric.closedBall x (ρ / (2 : ℝ) ^ n), f y ∂volume)
        atTop (𝓝 (w x)) := by
    simpa [f, outer, hx_outer] using hdx
  have hevent :
      ∀ᶠ n : ℕ in atTop,
        lam < ⨍ y in Metric.closedBall x (ρ / (2 : ℝ) ^ n), f y ∂volume := by
    exact hclosed_to_w.eventually (Ioi_mem_nhds hx_gt)
  rcases hevent.exists with ⟨n, hn⟩
  let r : ℝ := ρ / (2 : ℝ) ^ n
  have hr_pos : 0 < r := by
    dsimp [r]
    positivity
  have hr_le_R : r ≤ R := by
    calc
      r ≤ ρ := by
        dsimp [r]
        exact div_le_self hρ.le (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))
      _ = R / 2 := by rfl
      _ ≤ R := by linarith
  have hx_threeR : x ∈ Metric.ball x₀ ((6 * R) / 2) := by
    rw [Metric.mem_ball] at hxB ⊢
    linarith
  have hr_threeR : r ≤ (6 * R) / 2 := by
    have hRhalf : R / 2 ≤ (6 * R) / 2 := by linarith
    calc
      r ≤ R / 2 := by
        calc
          r ≤ ρ := by
            dsimp [r]
            exact div_le_self hρ.le (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))
          _ = R / 2 := by rfl
      _ ≤ (6 * R) / 2 := hRhalf
  have hclosedsub : Metric.closedBall x r ⊆ outer :=
    closedBall_subset_ball_of_mem_ball_half_aux hx_threeR (by positivity) hr_threeR
  have havg_eq :
      ⨍ y in Metric.closedBall x r, f y ∂volume =
        ⨍ y in Metric.ball x r, w y ∂volume := by
    calc
      ⨍ y in Metric.closedBall x r, f y ∂volume
          = ⨍ y in Metric.closedBall x r, w y ∂volume := by
              apply MeasureTheory.setAverage_congr_fun Metric.isClosed_closedBall.measurableSet
              exact Eventually.of_forall fun z hz => by
                simp [f, outer, hclosedsub hz]
      _ = ⨍ y in Metric.ball x r, w y ∂volume := by
            exact setAverage_closedBall_eq_ball_of_pos_aux x hr_pos
  refine ⟨hxB, r, hr_pos, hr_le_R, ?_⟩
  simpa [r] using hn.trans_eq havg_eq

set_option maxHeartbeats 1000000 in
/-- The full local John-Nirenberg inequality: if `u` has BMO seminorm at most `M`
on all sub-balls of `ball(x₀, 6R)`, then the level sets of `|u - (u)_B|` on `B = ball(x₀, R)`
decay exponentially. -/
theorem john_nirenberg_local
    {u : E → ℝ} {x₀ : E} {R M : ℝ}
    (hR : 0 < R) (hM : 0 < M)
    (_hu_meas : Measurable u)
    (hu_int : IntegrableOn u (Metric.ball x₀ (6 * R)) volume)
    (hu_bmo : ∀ (z : E) (s : ℝ), 0 < s →
      Metric.closedBall z s ⊆ Metric.ball x₀ (6 * R) →
      (⨍ x in Metric.ball z s, ‖u x - ⨍ y in Metric.ball z s, u y ∂volume‖ ∂volume) ≤ M)
    {t : ℝ} (ht : 0 < t) :
    volume ({x ∈ Metric.ball x₀ R |
      ‖u x - ⨍ y in Metric.ball x₀ R, u y ∂volume‖ > t}) ≤
    ENNReal.ofReal (C_JN d) * volume (Metric.ball x₀ R) *
      ENNReal.ofReal (Real.exp (-t / (C_JN d * M))) := by
  classical
  set B := Metric.ball x₀ R with hB_def
  set sixB := Metric.ball x₀ (6 * R) with hsixB_def
  set avgR := ⨍ y in B, u y ∂volume with havgR_def
  set w : E → ℝ := fun x => ‖u x - avgR‖ with hw_def
  set θ : ℝ := 1 / 2 with hθ_def
  set A : ℝ := 8 * 25 ^ d * M with hA_def
  set C5 : ℝ := 2 * 5 ^ d * M with hC5_def
  set F : ℝ → Type := fun lam => JNBadWitness w x₀ R lam with hF_def
  have hB_sub_six : B ⊆ sixB := by
    intro x hx
    rw [hB_def, Metric.mem_ball] at hx
    rw [hsixB_def, Metric.mem_ball]
    linarith
  have hw_int : IntegrableOn w sixB volume := by
    simpa [w, hw_def, sixB, hsixB_def] using (hu_int.sub integrableOn_const).norm
  have hθ_pos : 0 < θ := by simp [hθ_def]
  have hθ_lt : θ < 1 := by
    rw [hθ_def]
    norm_num
  have hA_pos : 0 < A := by
    rw [hA_def]
    positivity
  have hC5_nonneg : 0 ≤ C5 := by
    rw [hC5_def]
    positivity
  have hC5_le : C5 ≤ 4 * 25 ^ d * M := by
    rw [hC5_def]
    have hpow : (5 : ℝ) ^ d ≤ 25 ^ d :=
      pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 5)
        (by norm_num : (5 : ℝ) ≤ 25) d
    nlinarith [hpow, hM]
  have hA_sub_C5_pos : 0 < A - C5 := by
    rw [hA_def]
    linarith [hC5_le, hM]
  have hA_ge_base : 4 * 6 ^ (d : ℕ) * M ≤ A := by
    rw [hA_def]
    have hpow : (6 : ℝ) ^ d ≤ 25 ^ d :=
      pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 6) (by norm_num : (6 : ℝ) ≤ 25) d
    nlinarith [hpow, hM]
  have hlocal_coeff :
      2 * M * 5 ^ d / (A - C5) ≤ 1 / (2 * 5 ^ d) := by
    have hden_lower : 4 * 25 ^ d * M ≤ A - C5 := by
      rw [hA_def]
      linarith [hC5_le]
    calc
      2 * M * 5 ^ d / (A - C5) ≤ 2 * M * 5 ^ d / (4 * 25 ^ d * M) := by
        apply div_le_div_of_nonneg_left
        · positivity
        · positivity
        · exact hden_lower
      _ = 1 / (2 * 5 ^ d) := by
        rw [show (25 : ℝ) ^ d = (5 : ℝ) ^ d * (5 : ℝ) ^ d by
          rw [show (25 : ℝ) = 5 * 5 by norm_num, mul_pow]]
        field_simp [hM.ne', show (5 : ℝ) ^ d ≠ 0 by positivity]
        ring
  have havg_base : ∀ lam : ℝ, A ≤ lam →
      ∀ x ∈ Metric.ball x₀ R, ⨍ y in Metric.ball x R, w y ∂volume ≤ lam := by
    intro lam hlamA
    simpa [w, hw_def, avgR, hB_def] using
      (base_ball_average_le (u := u) (x₀ := x₀) (R := R) (M := M) (lam := lam)
        hR hM (le_trans hA_ge_base hlamA) hu_int hu_bmo)
  let stopR : ∀ lam : ℝ, A ≤ lam → F lam → ℝ := fun lam hlamA =>
    stoppingRadiusBad hR (havg_base lam hlamA)
  let stopParentR : ∀ lam : ℝ, A ≤ lam → F lam → ℝ := fun lam hlamA =>
    stoppingParentRadiusBad hR (havg_base lam hlamA)
  let Ebad : ℝ → Set E := fun lam =>
    if hlamA : A ≤ lam then
      ⋃ p : F lam, Metric.ball p.center (stopR lam hlamA p)
    else
      sixB
  have hEbad_sub : ∀ lam : ℝ, Ebad lam ⊆ sixB := by
    intro lam
    by_cases hlamA : A ≤ lam
    · intro x hx
      dsimp [Ebad] at hx
      rw [dif_pos hlamA] at hx
      rcases Set.mem_iUnion.1 hx with ⟨p, hp⟩
      have hcenter : p.center ∈ B := p.center_mem
      have hrad_le : stopR lam hlamA p ≤ R := by
        dsimp [stopR]
        exact stoppingRadiusBad_le_R hR (havg_base lam hlamA) p
      have hball : dist x p.center < stopR lam hlamA p := Metric.mem_ball.mp hp
      have hcenter_ball : dist p.center x₀ < R := by
        simpa [hB_def] using hcenter
      rw [hsixB_def, Metric.mem_ball]
      calc
        dist x x₀ ≤ dist x p.center + dist p.center x₀ := dist_triangle _ _ _
        _ < stopR lam hlamA p + R := by linarith
        _ ≤ 6 * R := by linarith [hrad_le, hR]
    · simp [Ebad, hlamA]
  have hEbad_meas : ∀ lam : ℝ, MeasurableSet (Ebad lam) := by
    intro lam
    by_cases hlamA : A ≤ lam
    · dsimp [Ebad]
      rw [dif_pos hlamA]
      exact ((isOpen_iUnion fun _ : F lam => isOpen_ball).measurableSet)
    · dsimp [Ebad]
      rw [dif_neg hlamA]
      simpa [hsixB_def] using
        (measurableSet_ball : MeasurableSet (Metric.ball x₀ (6 * R)))
  have hEbad_anti : ∀ lam₁ lam₂ : ℝ, lam₁ ≤ lam₂ → Ebad lam₂ ⊆ Ebad lam₁ := by
    intro lam₁ lam₂ h12
    by_cases h₁ : A ≤ lam₁
    · have h₂ : A ≤ lam₂ := le_trans h₁ h12
      intro x hx
      dsimp [Ebad] at hx
      rw [dif_pos h₂] at hx
      rcases Set.mem_iUnion.1 hx with ⟨p₂, hp₂⟩
      let p₁ : F lam₁ := weakenBadWitness h12 p₂
      have hrad :
          stopR lam₂ h₂ p₂ ≤ stopR lam₁ h₁ p₁ := by
        dsimp [stopR, p₁]
        exact stoppingRadiusBad_mono hR
          (havg_base lam₁ h₁) (havg_base lam₂ h₂) h12 p₂
      dsimp [Ebad]
      rw [dif_pos h₁]
      exact Set.mem_iUnion.2 ⟨p₁, Metric.ball_subset_ball hrad hp₂⟩
    · intro x hx
      dsimp [Ebad]
      rw [dif_neg h₁]
      exact hEbad_sub lam₂ hx
  have h_point_subset_ae : ∀ s : ℝ, {x ∈ B | w x > s} ≤ᵐ[volume] Ebad s := by
    intro s
    by_cases hsA : A ≤ s
    · have hbad_ae :
          {x ∈ B | w x > s} ≤ᵐ[volume] JNBadCenterSet w x₀ R s :=
        ae_pointwise_gt_subset_badCenter (w := w) (x₀ := x₀) (R := R) hR hw_int
      filter_upwards [hbad_ae] with y hy
      intro hy_point
      rcases hy hy_point with ⟨hyB, r, hr_pos, hr_le, hbad⟩
      let p : F s :=
        { center := y
          witnessRadius := r
          center_mem := hyB
          radius_pos := hr_pos
          radius_le := hr_le
          bad := hbad }
      dsimp [Ebad]
      rw [dif_pos hsA]
      exact Set.mem_iUnion.2 ⟨p, by
        simpa [p] using
          (Metric.mem_ball_self (stoppingRadiusBad_pos hR (havg_base s hsA) p) :
            p.center ∈ Metric.ball p.center (stopR s hsA p))⟩
    · exact Filter.Eventually.of_forall fun y hy => by
        dsimp [Ebad]
        rw [dif_neg hsA]
        exact hB_sub_six hy.1
  have h_decay_bad : ∀ lam : ℝ, A ≤ lam →
      volume (Ebad (lam + A)) ≤ ENNReal.ofReal θ * volume (Ebad lam) := by
    intro lam hlamA
    let μ : ℝ := lam + A
    have hμA : A ≤ μ := by
      dsimp [μ]
      linarith
    have hlamμ : lam ≤ μ := by
      dsimp [μ]
      linarith
    by_cases hFμ_nonempty : Nonempty (F μ)
    · have hFlam_nonempty : Nonempty (F lam) := by
        rcases hFμ_nonempty with ⟨p⟩
        exact ⟨weakenBadWitness hlamμ p⟩
      let rLam : F lam → ℝ := stopR lam hlamA
      let rMu : F μ → ℝ := stopR μ hμA
      let parentLam : F lam → ℝ := stopParentR lam hlamA
      have hrLam_pos : ∀ p : F lam, 0 < rLam p := by
        intro p
        dsimp [rLam, stopR]
        exact stoppingRadiusBad_pos hR (havg_base lam hlamA) p
      have hrMu_pos : ∀ p : F μ, 0 < rMu p := by
        intro p
        dsimp [rMu, stopR]
        exact stoppingRadiusBad_pos hR (havg_base μ hμA) p
      have hrLam_bdd : BddAbove (Set.range rLam) := by
        refine ⟨R, ?_⟩
        rintro r ⟨p, rfl⟩
        dsimp [rLam, stopR]
        exact stoppingRadiusBad_le_R hR (havg_base lam hlamA) p
      have hrMu_bdd : BddAbove (Set.range rMu) := by
        refine ⟨R, ?_⟩
        rintro r ⟨p, rfl⟩
        dsimp [rMu, stopR]
        exact stoppingRadiusBad_le_R hR (havg_base μ hμA) p
      have hrawLam_nonempty : (⋃ p : F lam, Metric.ball p.center (rLam p)).Nonempty := by
        rcases hFlam_nonempty with ⟨p⟩
        refine ⟨p.center, Set.mem_iUnion.2 ?_⟩
        exact ⟨p, by simpa using (Metric.mem_ball_self (hrLam_pos p) : p.center ∈ Metric.ball p.center (rLam p))⟩
      have hrawMu_nonempty : (⋃ p : F μ, Metric.ball p.center (rMu p)).Nonempty := by
        rcases hFμ_nonempty with ⟨p⟩
        refine ⟨p.center, Set.mem_iUnion.2 ?_⟩
        exact ⟨p, by simpa using (Metric.mem_ball_self (hrMu_pos p) : p.center ∈ Metric.ball p.center (rMu p))⟩
      obtain ⟨SLam, hSLam_count, hSLam_disj, hSLam_hit, hSLam_cover⟩ :=
        vitali_covering_lemma (ι := F lam) (x := fun p => p.center) (r := rLam)
          hrLam_pos hrLam_bdd hrawLam_nonempty
      obtain ⟨SMu, hSMu_count, hSMu_disj, hSMu_hit, hSMu_cover⟩ :=
        vitali_covering_lemma (ι := F μ) (x := fun p => p.center) (r := rMu)
          hrMu_pos hrMu_bdd hrawMu_nonempty
      haveI : Countable SLam := hSLam_count.to_subtype
      haveI : Countable SMu := hSMu_count.to_subtype
      let BLam : SLam → JNBall x₀ R := fun q =>
        { center := q.1.center
          radius := rLam q.1
          radius_pos := hrLam_pos q.1
          radius_le := by
            dsimp [rLam, stopR]
            exact stoppingRadiusBad_le_R hR (havg_base lam hlamA) q.1
          center_mem := q.1.center_mem }
      let BMu : SMu → JNBall x₀ R := fun q =>
        { center := q.1.center
          radius := rMu q.1
          radius_pos := hrMu_pos q.1
          radius_le := by
            dsimp [rMu, stopR]
            exact stoppingRadiusBad_le_R hR (havg_base μ hμA) q.1
          center_mem := q.1.center_mem }
      have hBLam_disj : ∀ i j : SLam, i ≠ j → Disjoint ((BLam i).carrier) ((BLam j).carrier) := by
        intro i j hij
        exact hSLam_disj i.1 i.2 j.1 j.2 (fun h => hij (Subtype.ext h))
      have hBMu_disj : ∀ i j : SMu, i ≠ j → Disjoint ((BMu i).carrier) ((BMu j).carrier) := by
        intro i j hij
        exact hSMu_disj i.1 i.2 j.1 j.2 (fun h => hij (Subtype.ext h))
      have hBMu_cover : Ebad μ ⊆ ⋃ q : SMu, (BMu q).fivefold := by
        simpa [Ebad, hμA, BMu, rMu] using hSMu_cover
      have hULam_sub : (⋃ q : SLam, (BLam q).carrier) ⊆ Ebad lam := by
        intro x hx
        dsimp [Ebad]
        rw [dif_pos hlamA]
        rcases Set.mem_iUnion.1 hx with ⟨q, hq⟩
        exact Set.mem_iUnion.2 ⟨q.1, by simpa [BLam, rLam] using hq⟩
      have hUMu_sub : (⋃ q : SMu, (BMu q).carrier) ⊆ Ebad μ := by
        intro x hx
        dsimp [Ebad]
        rw [dif_pos hμA]
        rcases Set.mem_iUnion.1 hx with ⟨q, hq⟩
        exact Set.mem_iUnion.2 ⟨q.1, by simpa [BMu, rMu] using hq⟩
      let toLow : SMu → F lam := fun p => weakenBadWitness hlamμ p.1
      let assign : SMu → SLam := fun p =>
        ⟨Classical.choose (hSLam_hit (toLow p)), (Classical.choose_spec (hSLam_hit (toLow p))).1⟩
      have hassign_hit : ∀ p : SMu,
          (Metric.ball (toLow p).center (rLam (toLow p)) ∩ (BLam (assign p)).carrier).Nonempty := by
        intro p
        exact (Classical.choose_spec (hSLam_hit (toLow p))).2.1
      have hassign_rad : ∀ p : SMu, rLam (toLow p) ≤ 2 * (BLam (assign p)).radius := by
        intro p
        exact (Classical.choose_spec (hSLam_hit (toLow p))).2.2
      have hrMu_le_low : ∀ p : SMu, rMu p.1 ≤ rLam (toLow p) := by
        intro p
        dsimp [rMu, rLam, toLow, stopR]
        exact stoppingRadiusBad_mono hR
          (havg_base lam hlamA) (havg_base μ hμA) hlamμ p.1
      have hassign_sub : ∀ p : SMu, (BMu p).carrier ⊆ (BLam (assign p)).fivefold := by
        intro p
        apply ball_subset_fivefold_of_inter_nonempty
        · exact Metric.ball_subset_ball (hrMu_le_low p)
        · exact hassign_hit p
        · exact hassign_rad p
      let V : SLam → Set E := fun q => ⋃ p : {p : SMu // assign p = q}, (BMu p.1).carrier
      have hV_sub : ∀ q : SLam, V q ⊆ (BLam q).fivefold := by
        intro q x hx
        rcases Set.mem_iUnion.1 hx with ⟨p, hp⟩
        have : assign p.1 = q := p.2
        simpa [V, this] using hassign_sub p.1 hp
      have hV_meas : ∀ q : SLam, MeasurableSet (V q) := by
        intro q
        dsimp [V]
        exact (isOpen_iUnion fun _ => isOpen_ball).measurableSet
      have havg5_le : ∀ q : SLam,
          ⨍ x in (BLam q).fivefold, w x ∂volume ≤ lam + C5 := by
        intro q
        let b := BLam q
        let parent := parentLam q.1
        let avg5 := ⨍ x in b.fivefold, w x ∂volume
        let avgParent := ⨍ x in Metric.ball b.center parent, w x ∂volume
        have h5r_pos : 0 < 5 * b.radius := by
          nlinarith [b.radius_pos]
        have hparent_pos : 0 < parent := by
          dsimp [parent, parentLam, stopParentR]
          exact stoppingParentRadiusBad_pos hR (havg_base lam hlamA) q.1
        have hparent_le : parent ≤ 2 * b.radius := by
          dsimp [parent, b, BLam, parentLam, stopParentR, rLam, stopR]
          exact stoppingParentRadiusBad_le_double hR (havg_base lam hlamA) q.1
        have hrad_le_parent : b.radius ≤ parent := by
          dsimp [parent, b, BLam, parentLam, stopParentR, rLam, stopR]
          exact stoppingRadiusBad_le_parent hR (havg_base lam hlamA) q.1
        have hw_int_five : IntegrableOn w b.fivefold volume :=
          hw_int.mono_set b.fivefold_subset_sixBall
        have hw_bmo_five :
            (⨍ x in b.fivefold, ‖w x - avg5‖ ∂volume) ≤ 2 * M := by
          have hu_bmo_five :=
            hu_bmo b.center (5 * b.radius) h5r_pos b.closedBall_fivefold_subset_sixBall
          simpa [w, hw_def, avg5] using
            (abs_sub_const_bmo_le_two (M := M) (u := u) (c := avgR) (z := b.center)
              (s := 5 * b.radius) h5r_pos
              (hu_int := hu_int.mono_set b.fivefold_subset_sixBall)
              (hu_bmo := hu_bmo_five))
        have hsub_parent_5 :
            Metric.ball b.center parent ⊆ b.fivefold :=
          Metric.ball_subset_ball (by linarith [hparent_le, b.radius_pos])
        have hratio_le :
            ((5 * b.radius) / parent) ^ d ≤ (5 : ℝ) ^ d := by
          have hfrac_le : (5 * b.radius) / parent ≤ (5 : ℝ) := by
            exact (div_le_iff₀ hparent_pos).2 (by nlinarith [hrad_le_parent])
          exact pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (5 * b.radius) / parent)
            hfrac_le d
        have hdiff :
            |avgParent - avg5| ≤
              ((5 * b.radius) / parent) ^ d *
                (⨍ z in b.fivefold, ‖w z - avg5‖ ∂volume) := by
          simpa [avgParent, avg5, JNBall.fivefold] using
            (abs_subballAverage_sub_ballAverage_le (u := w)
              (x := b.center) (c := b.center) h5r_pos hparent_pos hsub_parent_5 hw_int_five)
        have havgParent_le : avgParent ≤ lam := by
          dsimp [avgParent, parent, parentLam, stopParentR]
          exact stoppingParentRadiusBad_le hR (havg_base lam hlamA) q.1
        have hnorm_nonneg : 0 ≤ ⨍ z in b.fivefold, ‖w z - avg5‖ ∂volume := by
          rw [MeasureTheory.setAverage_eq]
          exact smul_nonneg (by positivity) (MeasureTheory.integral_nonneg fun _ => norm_nonneg _)
        have hdiff' : |avgParent - avg5| ≤ (5 : ℝ) ^ d * (2 * M) := by
          calc
            |avgParent - avg5| ≤
                ((5 * b.radius) / parent) ^ d *
                  (⨍ z in b.fivefold, ‖w z - avg5‖ ∂volume) := hdiff
            _ ≤ (5 : ℝ) ^ d * (⨍ z in b.fivefold, ‖w z - avg5‖ ∂volume) := by
                exact mul_le_mul_of_nonneg_right hratio_le hnorm_nonneg
            _ ≤ (5 : ℝ) ^ d * (2 * M) := by
                exact mul_le_mul_of_nonneg_left hw_bmo_five (by positivity)
        have hdiff_upper : avg5 - avgParent ≤ C5 := by
          rw [hC5_def]
          have hpair := abs_le.mp hdiff'
          linarith
        linarith [havgParent_le, hdiff_upper]
      have hlarge : ∀ p : SMu, μ < ⨍ x in (BMu p).carrier, w x ∂volume := by
        intro p
        dsimp [BMu, rMu, stopR]
        exact stoppingRadiusBad_bad hR (havg_base μ hμA) p.1
      let UMu : Set E := ⋃ p : SMu, (BMu p).carrier
      let ULam : Set E := ⋃ p : SLam, (BLam p).carrier
      have hUMu_le_ULam :
          volume.real UMu ≤ (1 / (2 * 5 ^ d)) * volume.real ULam := by
        simpa [UMu, ULam] using
          assigned_union_half_measure_real
            (d := d) (_hR := hR) (_hM := hM) (hμ_eq := by rfl)
            (hA_sub_C5_pos := hA_sub_C5_pos) (hlocal_coeff := hlocal_coeff)
            (hu_int := hu_int) (hu_bmo := hu_bmo) (w := w) (hw_def := hw_def)
            (BLam := BLam) (BMu := BMu) (hBLam_disj := hBLam_disj)
            (hBMu_disj := hBMu_disj) (assign := assign) (hassign_sub := hassign_sub)
            (havg5_le := havg5_le) (hlarge := hlarge)
      have hEbadMu_real :
          volume.real (Ebad μ) ≤ (5 : ℝ) ^ d * volume.real UMu := by
        simpa [UMu] using
          fivefold_cover_real_le
            (d := d) (x₀ := x₀) (R := R) (S := Ebad μ)
            (hS_sub := by simpa [sixB, hsixB_def] using hEbad_sub μ)
            (B := BMu) (hcover := hBMu_cover) (hdisj := hBMu_disj)
      have hEbadLam_fin : volume (Ebad lam) ≠ ⊤ :=
        measure_ne_top_of_subset (hEbad_sub lam)
          (measure_ball_lt_top (μ := volume) (x := x₀) (r := 6 * R)).ne
      have hULam_le_Ebad : volume.real ULam ≤ volume.real (Ebad lam) := by
        exact measureReal_mono hULam_sub hEbadLam_fin
      have hreal_decay :
          volume.real (Ebad μ) ≤ (1 / 2) * volume.real (Ebad lam) := by
        calc
          volume.real (Ebad μ) ≤ (5 : ℝ) ^ d * volume.real UMu := hEbadMu_real
          _ ≤ (5 : ℝ) ^ d * ((1 / (2 * 5 ^ d)) * volume.real ULam) := by
              exact mul_le_mul_of_nonneg_left hUMu_le_ULam (by positivity)
          _ = (1 / 2) * volume.real ULam := by
              rw [← mul_assoc, five_pow_half_factor]
          _ ≤ (1 / 2) * volume.real (Ebad lam) := by
              exact mul_le_mul_of_nonneg_left hULam_le_Ebad (by norm_num)
      have hEbadMu_fin : volume (Ebad μ) ≠ ⊤ :=
        measure_ne_top_of_subset (hEbad_sub μ)
          (measure_ball_lt_top (μ := volume) (x := x₀) (r := 6 * R)).ne
      have henn_decay :
          volume (Ebad μ) ≤ ENNReal.ofReal (1 / 2) * volume (Ebad lam) :=
        volume_real_le_to_ennreal hEbadMu_fin hEbadLam_fin (by norm_num) hreal_decay
      simpa [Ebad, hμA, θ, hθ_def, μ] using henn_decay
    · haveI : IsEmpty (F μ) := not_nonempty_iff.mp hFμ_nonempty
      have hEbadμ_empty : Ebad μ = ∅ := by
        simp [Ebad, hμA]
      simp [hEbadμ_empty, θ, μ]
  have h_exp_bad :=
    level_set_family_from_base
      (by simpa [hsixB_def] using (measurableSet_ball : MeasurableSet (Metric.ball x₀ (6 * R))))
      (measure_ball_lt_top (μ := volume) (x := x₀) (r := 6 * R)).ne
      hEbad_sub hEbad_meas hEbad_anti hA_pos hθ_pos hθ_lt h_decay_bad t ht
  have h_exp :
      volume ({x ∈ B | w x > t}) ≤
        ENNReal.ofReal 4 * volume sixB *
          ENNReal.ofReal (Real.exp (-t * (-Real.log θ / A))) := by
    have hmain :
        volume ({x ∈ B | w x > t}) ≤
          ENNReal.ofReal (1 / θ ^ 2) * volume sixB *
            ENNReal.ofReal (Real.exp (-t * (-Real.log θ / A))) := by
      calc
        volume ({x ∈ B | w x > t}) ≤ volume (Ebad t) := measure_mono_ae (h_point_subset_ae t)
        _ ≤ ENNReal.ofReal (1 / θ ^ 2) * volume sixB *
              ENNReal.ofReal (Real.exp (-t * (-Real.log θ / A))) := h_exp_bad
    have hθsq : (1 / θ ^ 2 : ℝ) = 4 := by
      rw [hθ_def]
      norm_num
    simpa [hθsq] using hmain
  have hsixB_vol :
      volume sixB = ENNReal.ofReal ((6 : ℝ) ^ d) * volume B := by
    have hleft : volume sixB ≠ ⊤ := measure_ball_lt_top.ne
    have hright : ENNReal.ofReal ((6 : ℝ) ^ d) * volume B ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top measure_ball_lt_top.ne
    rw [← ENNReal.toReal_eq_toReal_iff' hleft hright]
    rw [hsixB_def, hB_def, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ (6 : ℝ) ^ d)]
    change volume.real (Metric.ball x₀ (6 * R)) = (6 : ℝ) ^ d * volume.real (Metric.ball x₀ R)
    rw [volumeReal_ball_eq x₀ (show 0 < 6 * R by nlinarith), volumeReal_ball_eq x₀ hR]
    rw [mul_pow]
    ring
  have h_coeff_ball :
      ENNReal.ofReal 4 * volume sixB ≤ ENNReal.ofReal (C_JN d) * volume B := by
    rw [hsixB_vol]
    have hcoeff : 4 * (6 : ℝ) ^ d ≤ C_JN d := by
      rw [C_JN]
      have h36 : (6 : ℝ) ^ d ≤ 36 ^ d :=
        pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 6) (by norm_num : (6 : ℝ) ≤ 36) d
      calc
        4 * (6 : ℝ) ^ d ≤ 4 * 36 ^ d := by
          gcongr
        _ ≤ 16 * 36 ^ d := by
          have h36_nonneg : 0 ≤ (36 : ℝ) ^ d := by positivity
          nlinarith
    calc
      ENNReal.ofReal 4 * (ENNReal.ofReal ((6 : ℝ) ^ d) * volume B)
          = ENNReal.ofReal (4 * (6 : ℝ) ^ d) * volume B := by
              rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
      _ ≤ ENNReal.ofReal (C_JN d) * volume B := by
          exact mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal hcoeff) (by positivity)
  have h_const_exp : ∀ s : ℝ, 0 < s →
      -s * (-Real.log θ / A) ≤ -s / (C_JN d * M) := by
    intro s hs
    have hCJN_pos : 0 < C_JN d := C_JN_pos d
    have hCM_pos : 0 < C_JN d * M := mul_pos hCJN_pos hM
    suffices hkey : A ≤ C_JN d * M * (-Real.log θ) by
      have h_rate : 1 / (C_JN d * M) ≤ -Real.log θ / A := by
        rw [div_le_div_iff₀ hCM_pos hA_pos, one_mul]
        linarith [mul_comm (C_JN d * M) (-Real.log θ)]
      have := mul_le_mul_of_nonpos_left h_rate (neg_nonpos.mpr (le_of_lt hs))
      simp only [mul_div_assoc'] at this
      convert this using 1 <;> ring
    have hlog : Real.log θ ≤ θ - 1 := Real.log_le_sub_one_of_pos hθ_pos
    have hneg_log : (1 / 2 : ℝ) ≤ -Real.log θ := by
      rw [hθ_def] at hlog ⊢
      linarith
    calc
      A = 8 * 25 ^ d * M := hA_def
      _ ≤ 8 * 36 ^ d * M := by
          have hpow : (25 : ℝ) ^ d ≤ 36 ^ d :=
            pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 25) (by norm_num : (25 : ℝ) ≤ 36) d
          nlinarith [hpow, hM]
      _ = C_JN d * M * (1 / 2) := by
          rw [C_JN]
          ring
      _ ≤ C_JN d * M * (-Real.log θ) := by
          exact mul_le_mul_of_nonneg_left hneg_log (by positivity : 0 ≤ C_JN d * M)
  have hexp_bound :
      ENNReal.ofReal (Real.exp (-t * (-Real.log θ / A))) ≤
        ENNReal.ofReal (Real.exp (-t / (C_JN d * M))) := by
    exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (h_const_exp t ht))
  calc
    volume ({x ∈ Metric.ball x₀ R |
        ‖u x - ⨍ y in Metric.ball x₀ R, u y ∂volume‖ > t})
        = volume ({x ∈ B | w x > t}) := by
            simp [hB_def, w, avgR]
    _ ≤ ENNReal.ofReal 4 * volume sixB *
          ENNReal.ofReal (Real.exp (-t * (-Real.log θ / A))) := h_exp
    _ = (ENNReal.ofReal 4 * volume sixB) *
          ENNReal.ofReal (Real.exp (-t * (-Real.log θ / A))) := by
            rfl
    _ ≤ (ENNReal.ofReal (C_JN d) * volume B) *
          ENNReal.ofReal (Real.exp (-t * (-Real.log θ / A))) := by
            exact mul_le_mul_of_nonneg_right h_coeff_ball (by positivity)
    _ = ENNReal.ofReal (C_JN d) * volume B *
          ENNReal.ofReal (Real.exp (-t * (-Real.log θ / A))) := by
            rfl
    _ ≤ ENNReal.ofReal (C_JN d) * volume B *
          ENNReal.ofReal (Real.exp (-t / (C_JN d * M))) := by
            exact mul_le_mul_of_nonneg_left hexp_bound
              (by positivity : 0 ≤ ENNReal.ofReal (C_JN d) * volume B)


end DeGiorgi
