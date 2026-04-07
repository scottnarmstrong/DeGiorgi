import DeGiorgi.DeGiorgiIteration
import DeGiorgi.Localization
import DeGiorgi.WeakHarnack
import DeGiorgi.FiniteCover
import DeGiorgi.ScaledBallEstimates
import DeGiorgi.Support.MeasureBounds
import DeGiorgi.Support.IterationConstants
import Mathlib.MeasureTheory.Function.EssSup
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Topology.Compactness.Compact

/-!
# Chapter 07: Harnack Consequences

This module proves the Harnack inequality from the De Giorgi-Moser chain and
packages the constants used later in the Moser Holder theorem.

The focus here is the endpoint comparison argument on nested balls. Iteration
machinery belongs upstream in the De Giorgi, Moser, and weak Harnack modules.
-/

noncomputable section

open MeasureTheory

namespace DeGiorgi

variable {d : ℕ} [NeZero d]

local notation "E" => AmbientSpace d
local notation "μ1" => volume.restrict (Metric.ball (0 : E) 1)
local notation "μhalf" => volume.restrict (Metric.ball (0 : E) (1 / 2 : ℝ))

set_option maxHeartbeats 5000000

set_option maxHeartbeats 5000000 in
omit [NeZero d] in
/-- An a.e. upper bound on the half ball upgrades to an essential-supremum
bound on the half ball. -/
theorem essSup_halfBall_le_of_ae_bound
    {u : E → ℝ} {C : ℝ}
    (h_nonneg : ∀ᵐ x ∂μhalf, 0 ≤ u x)
    (hbound : ∀ᵐ x ∂μhalf, u x ≤ C) :
    essSup u μhalf ≤ C := by
  rw [essSup_eq_sInf]
  refine csInf_le ?_ ?_
  · refine ⟨0, ?_⟩
    intro b hb
    by_contra hb_nonneg
    have hb_neg : b < 0 := lt_of_not_ge hb_nonneg
    have hs : {x | b < u x} ∈ ae μhalf := by
      filter_upwards [h_nonneg] with x hx
      linarith
    have hs_compl : {x | b < u x}ᶜ ∈ ae μhalf := by
      exact compl_mem_ae_iff.mpr hb
    have hfalse : ∀ᵐ x ∂μhalf, False := by
      filter_upwards [hs, hs_compl] with x hx hx_compl
      exact hx_compl hx
    rw [ae_iff] at hfalse
    have hzero : μhalf Set.univ = 0 := by
      simpa using hfalse
    exact
      (restrict_ball_ne_zero (c := (0 : E)) (r := (1 / 2 : ℝ)) (by norm_num))
        (Measure.measure_univ_eq_zero.mp hzero)
  · simpa [not_le] using (ae_iff.mp hbound)

set_option maxHeartbeats 5000000 in
omit [NeZero d] in
/-- An a.e. lower bound on the half ball upgrades to an essential-infimum
bound on the half ball. -/
theorem le_essInf_halfBall_of_ae_bound
    {u : E → ℝ} {c C : ℝ}
    (hlow : ∀ᵐ x ∂μhalf, c ≤ u x)
    (hupp : ∀ᵐ x ∂μhalf, u x ≤ C) :
    c ≤ essInf u μhalf := by
  rw [essInf_eq_sSup]
  refine le_csSup ?_ ?_
  · refine ⟨C, ?_⟩
    intro a ha
    have ha_ae : ∀ᵐ x ∂μhalf, a ≤ u x := by
      rw [ae_iff]
      simpa [not_le] using ha
    have hconst : ∀ᵐ x ∂μhalf, a ≤ C := by
      filter_upwards [ha_ae, hupp] with x hax hxu
      linarith
    by_contra hAC
    have hfalse : ∀ᵐ x ∂μhalf, False := by
      filter_upwards [hconst] with x hx
      linarith
    rw [ae_iff] at hfalse
    have hzero : μhalf Set.univ = 0 := by
      simpa using hfalse
    exact
      (restrict_ball_ne_zero (c := (0 : E)) (r := (1 / 2 : ℝ)) (by norm_num))
        (Measure.measure_univ_eq_zero.mp hzero)
  · have hlow' := hlow
    rw [ae_iff] at hlow'
    simpa [not_le] using hlow'

/-- The low-power exponent used in the Chapter 07 Harnack proof. -/
noncomputable def harnack_q (d : ℕ) [NeZero d] : ℝ :=
  ((d : ℝ) - 1) / (d : ℝ)

/-- The corresponding `L^p` exponent in the Chapter 07 Harnack proof. -/
noncomputable def harnack_p (d : ℕ) [NeZero d] : ℝ :=
  ((d : ℝ) - 1) / ((d : ℝ) - 2)

omit [NeZero d] in
private theorem harnack_dim_ge_three (hd : 2 < (d : ℝ)) : 3 ≤ d := by
  have hd_nat : 2 < d := by
    exact_mod_cast hd
  exact Nat.succ_le_of_lt hd_nat

private theorem harnack_q_pos (hd : 2 < (d : ℝ)) :
    0 < harnack_q d := by
  unfold harnack_q
  have hd_pos : 0 < (d : ℝ) := by positivity
  have hnum_pos : 0 < (d : ℝ) - 1 := by linarith
  exact div_pos hnum_pos hd_pos

private theorem harnack_q_lt_one (hd : 2 < (d : ℝ)) :
    harnack_q d < 1 := by
  unfold harnack_q
  have hd_pos : 0 < (d : ℝ) := by positivity
  rw [div_lt_one hd_pos]
  linarith

private theorem one_sub_harnack_q (hd : 2 < (d : ℝ)) :
    1 - harnack_q d = ((d : ℝ))⁻¹ := by
  unfold harnack_q
  have hd_ne : (d : ℝ) ≠ 0 := by positivity
  field_simp [hd_ne]
  ring

private theorem harnack_p_eq_from_q :
    harnack_p d = harnack_q d * (d : ℝ) / ((d : ℝ) - 2) := by
  unfold harnack_p harnack_q
  have hd_pos : 0 < (d : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
  have hd_ne : (d : ℝ) ≠ 0 := ne_of_gt hd_pos
  by_cases hdm2 : (d : ℝ) - 2 = 0
  · have hd_eq : (d : ℝ) = 2 := by linarith
    norm_num [hd_eq]
  · field_simp [hd_ne, hdm2]

private theorem harnack_p_gt_one (hd : 2 < (d : ℝ)) :
    1 < harnack_p d := by
  unfold harnack_p
  have hden_pos : 0 < (d : ℝ) - 2 := by linarith
  exact (one_lt_div hden_pos).2 (by linarith)

private theorem harnack_p_le_two (hd : 2 < (d : ℝ)) :
    harnack_p d ≤ 2 := by
  have hd_three : 3 ≤ d := harnack_dim_ge_three hd
  have hd_three' : (3 : ℝ) ≤ d := by exact_mod_cast hd_three
  unfold harnack_p
  have hden_pos : 0 < (d : ℝ) - 2 := by linarith
  rw [div_le_iff₀ hden_pos]
  linarith

private theorem harnack_p_div_sub_eq (hd : 2 < (d : ℝ)) :
    harnack_p d / (harnack_p d - 1) = (d : ℝ) - 1 := by
  unfold harnack_p
  have hden_pos : 0 < (d : ℝ) - 2 := by linarith
  have hden_ne : (d : ℝ) - 2 ≠ 0 := ne_of_gt hden_pos
  field_simp [hden_ne]
  ring

private theorem harnack_p_inv_eq (hd : 2 < (d : ℝ)) :
    (harnack_p d)⁻¹ = ((d : ℝ) - 2) / ((d : ℝ) - 1) := by
  unfold harnack_p
  have hnum_pos : 0 < (d : ℝ) - 1 := by linarith
  have hnum_ne : (d : ℝ) - 1 ≠ 0 := ne_of_gt hnum_pos
  field_simp [hnum_ne]

private theorem harnack_outerExponent_eq (hd : 2 < (d : ℝ)) :
    ((d : ℝ) - 2) / (harnack_q d * (d : ℝ)) = (harnack_p d)⁻¹ := by
  rw [harnack_p_inv_eq (d := d) hd]
  unfold harnack_q
  have hd_ne : (d : ℝ) ≠ 0 := by positivity
  field_simp [hd_ne]

private theorem halfBall_power_factor_eq (hd : 2 < (d : ℝ)) :
    (1 / (1 - harnack_q d)) ^ (d : ℝ) = (d : ℝ) ^ (d : ℝ) := by
  have hone_sub : 1 - harnack_q d = ((d : ℝ))⁻¹ := one_sub_harnack_q (d := d) hd
  rw [hone_sub]
  simp

omit [NeZero d] in
private theorem ball_subset_unitBall_of_mem_closedBall_half
    {c : E} (hc : c ∈ Metric.closedBall (0 : E) (1 / 2 : ℝ))
    {r : ℝ} (_hr_nonneg : 0 ≤ r) (hr_half : r ≤ (1 / 2 : ℝ)) :
    Metric.ball c r ⊆ Metric.ball (0 : E) 1 := by
  intro x hx
  have hc' : dist c (0 : E) ≤ 1 / 2 := by simpa using hc
  have hx' : dist x c < r := by simpa using hx
  refine Metric.mem_ball.2 ?_
  have hlt : dist x (0 : E) < r + 1 / 2 := by
    calc
      dist x (0 : E) ≤ dist x c + dist c (0 : E) := dist_triangle _ _ _
      _ < r + 1 / 2 := by linarith
  exact lt_of_lt_of_le hlt (by linarith)

omit [NeZero d] in
private theorem closedBall_subset_unitBall_of_mem_ball_half
    {c : E} (hc : c ∈ Metric.ball (0 : E) (1 / 2 : ℝ))
    {r : ℝ} (_hr_nonneg : 0 ≤ r) (hr_half : r ≤ (1 / 2 : ℝ)) :
    Metric.closedBall c r ⊆ Metric.ball (0 : E) 1 := by
  intro x hx
  have hc' : dist c (0 : E) < 1 / 2 := by simpa using hc
  have hx' : dist x c ≤ r := by simpa using hx
  refine Metric.mem_ball.2 ?_
  have hlt : dist x (0 : E) < r + 1 / 2 := by
    calc
      dist x (0 : E) ≤ dist x c + dist c (0 : E) := dist_triangle _ _ _
      _ < r + 1 / 2 := by linarith
  exact lt_of_lt_of_le hlt (by linarith)

omit [NeZero d] in
private lemma affine_map_restrict_ball_mul
    {x₀ : E} {R ρ : ℝ} (hR : 0 < R) :
    Measure.map (fun z : E => x₀ + R • z) (volume.restrict (Metric.ball (0 : E) ρ)) =
      ENNReal.ofReal (|R ^ Module.finrank ℝ E|⁻¹) •
        (volume.restrict (Metric.ball x₀ (R * ρ))) := by
  have hmeas : Measurable (fun z : E => x₀ + R • z) :=
    (measurable_const_add x₀).comp (measurable_const_smul R)
  calc
    Measure.map (fun z : E => x₀ + R • z) (volume.restrict (Metric.ball (0 : E) ρ))
        = Measure.map (fun z : E => x₀ + R • z)
            (volume.restrict ((fun z : E => x₀ + R • z) ⁻¹' Metric.ball x₀ (R * ρ))) := by
              rw [affine_preimage_ball_mul (d := d) (x₀ := x₀) (R := R) (ρ := ρ) hR]
    _ = (Measure.map (fun z : E => x₀ + R • z) volume).restrict (Metric.ball x₀ (R * ρ)) := by
          rw [Measure.restrict_map hmeas measurableSet_ball]
    _ = (ENNReal.ofReal (|R ^ Module.finrank ℝ E|⁻¹) • (volume : Measure E)).restrict
          (Metric.ball x₀ (R * ρ)) := by
            rw [show (fun z : E => x₀ + R • z) = (fun z => x₀ + z) ∘ (fun z => R • z) from rfl]
            rw [← Measure.map_map (measurable_const_add x₀) (measurable_const_smul R)]
            rw [Measure.map_addHaar_smul volume hR.ne']
            rw [Measure.map_smul, (measurePreserving_add_left volume x₀).map_eq, abs_inv]
    _ = ENNReal.ofReal (|R ^ Module.finrank ℝ E|⁻¹) •
          (volume.restrict (Metric.ball x₀ (R * ρ))) := by
            rw [Measure.restrict_smul]

/-- Quantitative constant used to absorb the local-ball Harnack chain into the
final exponential form. -/
noncomputable def C_harnack (d : ℕ) [NeZero d] : ℝ :=
  17 *
    (((d : ℝ) - 2) / ((d : ℝ) - 1) *
        Real.log
          (C_Moser d * (((d : ℝ) - 1) ^ (d : ℝ)) * ((4 : ℝ) ^ (d : ℝ))) +
      (d : ℝ) +
      Real.log (C_weakHarnack_of d * ((d : ℝ) ^ (weak_harnack_decay_exp d))))

/-- Quantitative constant for the Moser Hölder theorem. -/
noncomputable def C_holder_Moser (d : ℕ) [NeZero d] : ℝ :=
  (256 : ℝ) *
    (|C_harnack d| +
      C_Moser d * (((d : ℝ) - 1) ^ (d : ℝ)) * ((4 : ℝ) ^ (d : ℝ)) +
      C_Moser d * ((2 : ℝ) ^ (d : ℝ)) +
      C_weakHarnack_of d * ((d : ℝ) ^ (d : ℝ)) + 8)

private noncomputable def quarterBallInf
    (u : E → ℝ) (c : E) : ℝ :=
  essInf (fun z : E => u (c + (1 / 2 : ℝ) • z))
    (volume.restrict (Metric.ball (0 : E) (1 / 4 : ℝ)))

private noncomputable def localHarnackConstant
    (A : NormalizedEllipticCoeff d (Metric.ball (0 : E) 1)) : ℝ :=
  (localMoserBase d * A.1.Λ ^ ((d : ℝ) / 2)) ^ ((harnack_p d)⁻¹) *
    localWeakHarnackBase d ^ (A.1.Λ ^ ((1 : ℝ) / 2))

private theorem localHarnackConstant_pos
    (hd : 2 < (d : ℝ))
    (A : NormalizedEllipticCoeff d (Metric.ball (0 : E) 1)) :
    0 < localHarnackConstant (d := d) A := by
  unfold localHarnackConstant
  refine mul_pos ?_ ?_
  · exact Real.rpow_pos_of_pos (mul_pos (localMoserBase_pos (d := d) hd)
      (Real.rpow_pos_of_pos A.1.Λ_pos _)) _
  · exact Real.rpow_pos_of_pos (localWeakHarnackBase_pos (d := d)) _

private theorem localMoserBase_eq (hd : 2 < (d : ℝ)) :
    C_Moser d * (harnack_p d / (harnack_p d - 1)) ^ (d : ℝ) * (4 : ℝ) ^ (d : ℝ) =
      localMoserBase d := by
  rw [harnack_p_div_sub_eq (d := d) hd, localMoserBase]

private theorem localWeakHarnackBase_eq (hd : 2 < (d : ℝ)) :
    C_weakHarnack d hd / (1 - harnack_q d) ^ (weak_harnack_decay_exp d) =
      localWeakHarnackBase d := by
  have hone_sub : 1 - harnack_q d = ((d : ℝ))⁻¹ := one_sub_harnack_q (d := d) hd
  have hd_pos : 0 < (d : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
  rw [hone_sub, div_eq_mul_inv, Real.inv_rpow hd_pos.le, inv_inv]
  unfold localWeakHarnackBase
  rw [show C_weakHarnack_of d = C_weakHarnack d hd from C_weakHarnack_of_eq hd]

omit [NeZero d] in
private theorem quarterBallInf_eq_essInf_eighthBall
    {u : E → ℝ} {c : E}
    (hu_ae : AEMeasurable u (volume.restrict (Metric.ball c (1 / 8 : ℝ)))) :
    quarterBallInf u c = essInf u (volume.restrict (Metric.ball c (1 / 8 : ℝ))) := by
  let T : E → E := fun z => c + (1 / 2 : ℝ) • z
  let μquarter : Measure E := volume.restrict (Metric.ball (0 : E) (1 / 4 : ℝ))
  let ν : Measure E := volume.restrict (Metric.ball c (1 / 8 : ℝ))
  let g : E → ℝ := hu_ae.mk u
  have hg_meas : Measurable g := hu_ae.measurable_mk
  have hg_ae : g =ᵐ[ν] u := hu_ae.ae_eq_mk.symm
  have hT_emb : MeasurableEmbedding T := by
    dsimp [T]
    exact ((MeasurableEquiv.addLeft c).measurableEmbedding).comp
      ((Homeomorph.smulOfNeZero (1 / 2 : ℝ) (by norm_num)).toMeasurableEquiv.measurableEmbedding)
  have hmap :
      Measure.map T μquarter =
        ENNReal.ofReal (|((1 / 2 : ℝ) ^ Module.finrank ℝ E)|⁻¹) •
          volume.restrict (Metric.ball c (1 / 8 : ℝ)) := by
    convert
      affine_map_restrict_ball_mul (d := d) (x₀ := c) (R := (1 / 2 : ℝ)) (ρ := (1 / 4 : ℝ))
        (by norm_num) using 1
    · simp
      norm_num
  have hscale_ne :
      ENNReal.ofReal (|((1 / 2 : ℝ) ^ Module.finrank ℝ E)|⁻¹) ≠ 0 := by
    exact affine_scale_measure_ne_zero (d := d) (R := (1 / 2 : ℝ)) (by norm_num)
  have hg_ae_map : g =ᵐ[Measure.map T μquarter] u := by
    rw [hmap, Measure.ae_ennreal_smul_measure_eq hscale_ne]
    exact hg_ae
  have hg_comp_ae : g ∘ T =ᵐ[μquarter] u ∘ T := by
    exact ae_of_ae_map hT_emb.measurable.aemeasurable hg_ae_map
  calc
    quarterBallInf u c = essInf (g ∘ T) μquarter := by
      unfold quarterBallInf
      exact essInf_congr_ae hg_comp_ae.symm
    _ = essInf g (Measure.map T μquarter) := by
      exact essInf_comp_measurableEmbedding_eq hT_emb hg_meas
    _ = essInf g ν := by
      rw [hmap]
      simpa [ν] using
        (essInf_measurable_ennreal_smul_measure (μ := ν) (c := ENNReal.ofReal
          (|((1 / 2 : ℝ) ^ Module.finrank ℝ E)|⁻¹)) hscale_ne (f := g) hg_meas)
    _ = essInf u ν := by
      exact essInf_congr_ae hg_ae

omit [NeZero d] in
private theorem quarterBallInf_le_ae
    {u : E → ℝ} {c : E}
    (hu_ae : AEMeasurable u (volume.restrict (Metric.ball c (1 / 8 : ℝ))))
    (hu_nonneg : ∀ z ∈ Metric.ball c (1 / 8 : ℝ), 0 ≤ u z) :
    ∀ᵐ z ∂(volume.restrict (Metric.ball c (1 / 8 : ℝ))),
      quarterBallInf u c ≤ u z := by
  rw [quarterBallInf_eq_essInf_eighthBall (u := u) (c := c) hu_ae]
  have hu_nonneg_ae :
      ∀ᵐ z ∂(volume.restrict (Metric.ball c (1 / 8 : ℝ))), 0 ≤ u z := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
    exact hu_nonneg z hz
  exact ae_essInf_le (μ := volume.restrict (Metric.ball c (1 / 8 : ℝ))) (f := u)
    ⟨0, by simpa using hu_nonneg_ae⟩

private theorem aemeasurable_on_ball_of_isSolution
    (A : NormalizedEllipticCoeff d (Metric.ball (0 : E) 1))
    {u : E → ℝ} (hsol : IsSolution A.1 u)
    {c : E} {r : ℝ}
    (hsub : Metric.ball c r ⊆ Metric.ball (0 : E) 1) :
    AEMeasurable u (volume.restrict (Metric.ball c r)) := by
  let huw : MemW1pWitness 2 u (Metric.ball (0 : E) 1) := MemW1p.someWitness hsol.1.1
  exact (huw.restrict Metric.isOpen_ball hsub).memLp.aestronglyMeasurable.aemeasurable

set_option maxHeartbeats 5000000 in
private theorem ae_le_localHarnack_on_eighthBall
    (hd : 2 < (d : ℝ))
    (A : NormalizedEllipticCoeff d (Metric.ball (0 : E) 1))
    {u : E → ℝ}
    (hu_pos : ∀ x ∈ Metric.ball (0 : E) 1, 0 < u x)
    (hsol : IsSolution A.1 u)
    {c : E} (hc : c ∈ Metric.ball (0 : E) (1 / 2 : ℝ)) :
    ∀ᵐ x ∂(volume.restrict (Metric.ball c (1 / 16 : ℝ))),
      u x ≤ localHarnackConstant (d := d) A * quarterBallInf u c := by
  have hsubHalfClosed :
      Metric.closedBall c (1 / 2 : ℝ) ⊆ Metric.ball (0 : E) 1 :=
    closedBall_subset_unitBall_of_mem_ball_half (d := d) hc (by positivity) le_rfl
  have hsubEighthClosed :
      Metric.closedBall c (1 / 8 : ℝ) ⊆ Metric.ball (0 : E) 1 :=
    closedBall_subset_unitBall_of_mem_ball_half (d := d) hc (by positivity) (by norm_num)
  have hsubHalfBall : Metric.ball c (1 / 2 : ℝ) ⊆ Metric.ball (0 : E) 1 :=
    Metric.ball_subset_closedBall.trans hsubHalfClosed
  have hsubEighthBall : Metric.ball c (1 / 8 : ℝ) ⊆ Metric.ball (0 : E) 1 :=
    Metric.ball_subset_closedBall.trans hsubEighthClosed
  let Ahalf : NormalizedEllipticCoeff d (Metric.ball c (1 / 2 : ℝ)) :=
    NormalizedEllipticCoeff.restrict A hsubHalfBall
  let Aeighth : NormalizedEllipticCoeff d (Metric.ball c (1 / 8 : ℝ)) :=
    NormalizedEllipticCoeff.restrict A hsubEighthBall
  have hsolHalf : IsSolution Ahalf.1 u := by
    change IsSolution ((A.1).restrict (Metric.ball_subset_closedBall.trans hsubHalfClosed)) u
    exact hsol.restrict_ball (d := d) Metric.isOpen_ball (by norm_num) hsubHalfClosed
  have hsolEighth : IsSolution Aeighth.1 u := by
    change IsSolution ((A.1).restrict (Metric.ball_subset_closedBall.trans hsubEighthClosed)) u
    exact hsol.restrict_ball (d := d) Metric.isOpen_ball (by norm_num) hsubEighthClosed
  have hu_posHalf : ∀ x ∈ Metric.ball c (1 / 2 : ℝ), 0 < u x := by
    intro x hx
    exact hu_pos x (hsubHalfBall hx)
  let huEighth : MemW1pWitness 2 u (Metric.ball c (1 / 8 : ℝ)) :=
    MemW1p.someWitness hsolEighth.1.1
  have hfin : Module.finrank ℝ E = d := by simp [AmbientSpace]
  haveI : IsFiniteMeasure (volume.restrict (Metric.ball c (1 / 8 : ℝ))) := by
    rw [MeasureTheory.isFiniteMeasure_iff]
    simpa using (measure_ball_lt_top (μ := volume) (x := c) (r := (1 / 8 : ℝ)))
  have hu_memLp_p :
      MemLp u (ENNReal.ofReal (harnack_p d))
        (volume.restrict (Metric.ball c (1 / 8 : ℝ))) := by
    exact huEighth.memLp.mono_exponent <| by
      exact_mod_cast harnack_p_le_two (d := d) hd
  have hp_pos : 0 < harnack_p d := lt_trans zero_lt_one (harnack_p_gt_one (d := d) hd)
  have hu_abs_int :
      IntegrableOn (fun x => |u x| ^ harnack_p d) (Metric.ball c (1 / 8 : ℝ)) volume := by
    have hint :
        Integrable (fun x => ‖u x‖ ^ harnack_p d)
          (volume.restrict (Metric.ball c (1 / 8 : ℝ))) := by
      have hint' :=
        hu_memLp_p.integrable_norm_rpow (ENNReal.ofReal_pos.mpr hp_pos).ne' ENNReal.ofReal_ne_top
      simpa [ENNReal.toReal_ofReal hp_pos.le] using hint'
    simpa [IntegrableOn] using hint
  have hu_posInt :
      IntegrableOn (fun x => |max (u x) 0| ^ harnack_p d)
        (Metric.ball c (1 / 8 : ℝ)) volume := by
    refine hu_abs_int.congr_fun ?_ measurableSet_ball
    intro x hx
    have hux_pos : 0 < u x := hu_pos x (hsubEighthBall hx)
    have hux_nonneg : 0 ≤ u x := hux_pos.le
    simp [max_eq_left hux_nonneg, abs_of_nonneg hux_nonneg]
  have hlinfty_raw :=
    linfty_subsolution_Moser_on_ball (d := d) hd
      (x₀ := c) (R := (1 / 8 : ℝ)) (by norm_num)
      Aeighth (p₀ := harnack_p d) (harnack_p_gt_one (d := d) hd)
      hsolEighth.1 hu_posInt
  have hlinfty :
      ∀ᵐ x ∂(volume.restrict (Metric.ball c (1 / 16 : ℝ))),
        |max (u x) 0| ^ harnack_p d ≤
          C_Moser d * Aeighth.1.Λ ^ ((d : ℝ) / 2) *
            (harnack_p d / (harnack_p d - 1)) ^ (d : ℝ) *
            (((1 / 8 : ℝ) ^ Module.finrank ℝ E)⁻¹ *
              ∫ x in Metric.ball c (1 / 8 : ℝ), |max (u x) 0| ^ harnack_p d ∂volume) := by
    convert hlinfty_raw using 1
    · simp
      norm_num
  have hweak :
      ((((1 / 2 : ℝ) ^ Module.finrank ℝ E)⁻¹ *
          ∫ x in Metric.ball c (1 / 8 : ℝ), |u x| ^ harnack_p d ∂volume) ^
          ((harnack_p d)⁻¹)) ≤
        localWeakHarnackBase d ^ (A.1.Λ ^ ((1 : ℝ) / 2)) * quarterBallInf u c := by
    have hweak_raw :=
      weak_harnack_on_ball (d := d) hd
        (x₀ := c) (R := (1 / 2 : ℝ)) (by norm_num)
        Ahalf (q := harnack_q d)
        (harnack_q_pos (d := d) hd) (harnack_q_lt_one (d := d) hd)
        hu_posHalf hsolHalf.2
    have hweak_raw' := hweak_raw
    dsimp [Ahalf] at hweak_raw'
    rw [← harnack_p_eq_from_q (d := d), harnack_outerExponent_eq (d := d) hd,
      localWeakHarnackBase_eq (d := d) hd] at hweak_raw'
    convert hweak_raw' using 1
    norm_num
  have hscale :
      ((1 / 8 : ℝ) ^ Module.finrank ℝ E)⁻¹ =
        ((4 : ℝ) ^ (d : ℝ)) * (((1 / 2 : ℝ) ^ Module.finrank ℝ E)⁻¹) := by
    have hscale_nat :
        ((1 / 8 : ℝ) ^ d)⁻¹ = ((4 : ℝ) ^ d) * (((1 / 2 : ℝ) ^ d)⁻¹) := by
      calc
        ((1 / 8 : ℝ) ^ d)⁻¹ = (8 : ℝ) ^ d := by
          rw [show (1 / 8 : ℝ) = (8 : ℝ)⁻¹ by norm_num, inv_pow]
          norm_num
        _ = (4 : ℝ) ^ d * (2 : ℝ) ^ d := by
          rw [show (8 : ℝ) = (4 : ℝ) * 2 by norm_num, mul_pow]
        _ = (4 : ℝ) ^ d * (((1 / 2 : ℝ) ^ d)⁻¹) := by
          congr 1
          rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num, inv_pow]
          norm_num
    simpa [hfin] using hscale_nat
  have hweak_factor_pos :
      0 < localWeakHarnackBase d ^ (A.1.Λ ^ ((1 : ℝ) / 2)) := by
    exact Real.rpow_pos_of_pos (localWeakHarnackBase_pos (d := d)) _
  have hu_ae_eighth :
      AEMeasurable u (volume.restrict (Metric.ball c (1 / 8 : ℝ))) := by
    exact aemeasurable_on_ball_of_isSolution (d := d) A hsol hsubEighthBall
  have hquarterBallInf_lower :
      ∀ᵐ z ∂(volume.restrict (Metric.ball c (1 / 8 : ℝ))),
        quarterBallInf u c ≤ u z := by
    exact quarterBallInf_le_ae (c := c) hu_ae_eighth (fun z hz => (hu_pos z (hsubEighthBall hz)).le)
  have hquarterBallInf_nonneg : 0 ≤ quarterBallInf u c := by
    have hu_nonneg_ae :
        ∀ᵐ z ∂(volume.restrict (Metric.ball c (1 / 8 : ℝ))), 0 ≤ u z := by
      filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
      exact (hu_pos z (hsubEighthBall hz)).le
    rw [quarterBallInf_eq_essInf_eighthBall (u := u) (c := c) hu_ae_eighth]
    have hμ_eighth_ne_zero :
        volume.restrict (Metric.ball c (1 / 8 : ℝ)) ≠ 0 := by
      intro hzero
      have hball_zero : volume (Metric.ball c (1 / 8 : ℝ)) = 0 := by
        simpa [Measure.restrict_apply_univ] using
          congrArg (fun μ : Measure E => μ Set.univ) hzero
      exact (Metric.measure_ball_pos volume c (by norm_num : 0 < (1 / 8 : ℝ))).ne' hball_zero
    exact le_essInf_real_of_ae_le
      (μ := volume.restrict (Metric.ball c (1 / 8 : ℝ)))
      hμ_eighth_ne_zero
      (by simpa using hu_nonneg_ae)
  let T : ℝ := localWeakHarnackBase d ^ (A.1.Λ ^ ((1 : ℝ) / 2)) * quarterBallInf u c
  have hT_nonneg : 0 ≤ T := by
    exact mul_nonneg
      (Real.rpow_nonneg (localWeakHarnackBase_pos (d := d)).le _)
      hquarterBallInf_nonneg
  have hweak_pow :
      (((1 / 2 : ℝ) ^ Module.finrank ℝ E)⁻¹ *
          ∫ x in Metric.ball c (1 / 8 : ℝ), |u x| ^ harnack_p d ∂volume) ≤
        T ^ harnack_p d := by
    let L : ℝ :=
      ((1 / 2 : ℝ) ^ Module.finrank ℝ E)⁻¹ *
        ∫ x in Metric.ball c (1 / 8 : ℝ), |u x| ^ harnack_p d ∂volume
    have hL_nonneg : 0 ≤ L := by
      dsimp [L]
      positivity
    have hweak' : L ^ ((harnack_p d)⁻¹) ≤ T := by
      simpa [L, T] using hweak
    have hpow :=
      Real.rpow_le_rpow (Real.rpow_nonneg hL_nonneg _) hweak' hp_pos.le
    have hp_ne : harnack_p d ≠ 0 := ne_of_gt hp_pos
    have hmul : (harnack_p d)⁻¹ * harnack_p d = 1 := by
      field_simp [hp_ne]
    have hL :
        (L ^ ((harnack_p d)⁻¹)) ^ harnack_p d = L := by
      rw [← Real.rpow_mul hL_nonneg, hmul, Real.rpow_one]
    rw [hL] at hpow
    simpa [L, T] using hpow
  filter_upwards [hlinfty, ae_restrict_mem measurableSet_ball] with x hx_raw hx_ball
  have hx_ball' : x ∈ Metric.ball c (1 / 16 : ℝ) := by
    simpa using hx_ball
  have hx_eighth : x ∈ Metric.ball c (1 / 8 : ℝ) :=
    Metric.ball_subset_ball (by norm_num : (1 / 16 : ℝ) ≤ 1 / 8) hx_ball'
  have hux_pos : 0 < u x := hu_pos _ (hsubEighthBall hx_eighth)
  have hux_nonneg : 0 ≤ u x := hux_pos.le
  have hx_to_u :
      |max (u x) 0| ^ harnack_p d = u x ^ harnack_p d := by
    simp [max_eq_left hux_nonneg, abs_of_nonneg hux_nonneg]
  have hint_eq :
      ∫ x in Metric.ball c (1 / 8 : ℝ), |max (u x) 0| ^ harnack_p d ∂volume =
        ∫ x in Metric.ball c (1 / 8 : ℝ), |u x| ^ harnack_p d ∂volume := by
    apply setIntegral_congr_fun measurableSet_ball
    intro y hy
    have huy_pos : 0 < u y := hu_pos _ (hsubEighthBall hy)
    have huy_nonneg : 0 ≤ u y := huy_pos.le
    simp [max_eq_left huy_nonneg, abs_of_nonneg huy_nonneg]
  have hx_bound :
      u x ^ harnack_p d ≤
        localMoserBase d * A.1.Λ ^ ((d : ℝ) / 2) * T ^ harnack_p d := by
    have hx0 :
        u x ^ harnack_p d ≤
          C_Moser d * A.1.Λ ^ ((d : ℝ) / 2) *
            (harnack_p d / (harnack_p d - 1)) ^ (d : ℝ) *
            (((1 / 8 : ℝ) ^ Module.finrank ℝ E)⁻¹ *
              ∫ x in Metric.ball c (1 / 8 : ℝ), |max (u x) 0| ^ harnack_p d ∂volume) := by
      calc
        u x ^ harnack_p d ≤
            C_Moser d * Aeighth.1.Λ ^ ((d : ℝ) / 2) *
              (harnack_p d / (harnack_p d - 1)) ^ (d : ℝ) *
              (((1 / 8 : ℝ) ^ Module.finrank ℝ E)⁻¹ *
                ∫ x in Metric.ball c (1 / 8 : ℝ), |max (u x) 0| ^ harnack_p d ∂volume) := by
              simpa [hfin, Real.rpow_natCast,
                show (1 / 8 : ℝ) / 2 = (1 / 16 : ℝ) by norm_num,
                hx_to_u, mul_assoc, mul_left_comm, mul_comm] using hx_raw
        _ = C_Moser d * A.1.Λ ^ ((d : ℝ) / 2) *
              (harnack_p d / (harnack_p d - 1)) ^ (d : ℝ) *
              (((1 / 8 : ℝ) ^ Module.finrank ℝ E)⁻¹ *
                ∫ x in Metric.ball c (1 / 8 : ℝ), |max (u x) 0| ^ harnack_p d ∂volume) := by
              rw [show Aeighth.1.Λ = A.1.Λ by
                    simp [Aeighth, NormalizedEllipticCoeff.restrict, EllipticCoeff.restrict_Λ]]
    have hx :
        u x ^ harnack_p d ≤
          C_Moser d * A.1.Λ ^ ((d : ℝ) / 2) * (((d : ℝ) - 1) ^ (d : ℝ)) *
            (((1 / 8 : ℝ) ^ Module.finrank ℝ E)⁻¹ *
              ∫ x in Metric.ball c (1 / 8 : ℝ), |max (u x) 0| ^ harnack_p d ∂volume) := by
      have hratio :
          (harnack_p d / (harnack_p d - 1)) ^ (d : ℝ) = ((d : ℝ) - 1) ^ (d : ℝ) := by
        rw [harnack_p_div_sub_eq (d := d) hd]
      simpa [hratio, mul_assoc, mul_left_comm, mul_comm] using hx0
    have hconst :
        C_Moser d * A.1.Λ ^ ((d : ℝ) / 2) * (((d : ℝ) - 1) ^ (d : ℝ)) *
            (((1 / 8 : ℝ) ^ Module.finrank ℝ E)⁻¹ *
          ∫ x in Metric.ball c (1 / 8 : ℝ), |max (u x) 0| ^ harnack_p d ∂volume) ≤
          C_Moser d * A.1.Λ ^ ((d : ℝ) / 2) * (((d : ℝ) - 1) ^ (d : ℝ)) *
            (((4 : ℝ) ^ (d : ℝ)) * T ^ harnack_p d) := by
      rw [hint_eq, hscale]
      have hpref_nonneg :
          0 ≤ C_Moser d * A.1.Λ ^ ((d : ℝ) / 2) * (((d : ℝ) - 1) ^ (d : ℝ)) := by
        refine mul_nonneg (mul_nonneg ?_ ?_) ?_
        · exact le_trans (by norm_num : (0 : ℝ) ≤ 1) (one_le_C_Moser (d := d))
        · exact Real.rpow_nonneg A.1.Λ_nonneg _
        · have hdm1_nonneg : 0 ≤ (d : ℝ) - 1 := by
            have hd_pos : 0 < (d : ℝ) := by
              exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
            linarith
          exact Real.rpow_nonneg hdm1_nonneg _
      have hweak_pow' :
          ((4 : ℝ) ^ (d : ℝ)) *
              (((1 / 2 : ℝ) ^ Module.finrank ℝ E)⁻¹ *
                ∫ x in Metric.ball c (1 / 8 : ℝ), |u x| ^ harnack_p d ∂volume) ≤
            ((4 : ℝ) ^ (d : ℝ)) * T ^ harnack_p d := by
        exact mul_le_mul_of_nonneg_left hweak_pow (by positivity)
      have hweak_pow'' :
          ((4 : ℝ) ^ (d : ℝ) *
              (((1 / 2 : ℝ) ^ Module.finrank ℝ E)⁻¹ *
                ∫ x in Metric.ball c (1 / 8 : ℝ), |u x| ^ harnack_p d ∂volume)) ≤
            ((4 : ℝ) ^ (d : ℝ) * T ^ harnack_p d) := by
        simpa [mul_assoc] using hweak_pow'
      exact mul_le_mul_of_nonneg_left (by simpa [mul_assoc] using hweak_pow'') hpref_nonneg
    have hx' := le_trans hx hconst
    simpa [localMoserBase, T, mul_assoc, mul_left_comm, mul_comm] using hx'
  have hbase_nonneg : 0 ≤ localMoserBase d * A.1.Λ ^ ((d : ℝ) / 2) := by
    exact mul_nonneg (localMoserBase_nonneg (d := d)) (Real.rpow_nonneg A.1.Λ_nonneg _)
  have hroot :
      u x ≤ localHarnackConstant (d := d) A * quarterBallInf u c := by
    have hroot0 :
        u x ≤
          (localMoserBase d * A.1.Λ ^ ((d : ℝ) / 2) * T ^ harnack_p d) ^
            ((harnack_p d)⁻¹) := by
      have hright_nonneg :
          0 ≤
            (localMoserBase d * A.1.Λ ^ ((d : ℝ) / 2) * T ^ harnack_p d) ^
              ((harnack_p d)⁻¹) := by
        positivity
      rw [← Real.rpow_le_rpow_iff hux_nonneg hright_nonneg hp_pos]
      have hp_ne : harnack_p d ≠ 0 := ne_of_gt hp_pos
      have hmul :
          (harnack_p d)⁻¹ * harnack_p d = 1 := by
        field_simp [hp_ne]
      rw [← Real.rpow_mul (mul_nonneg hbase_nonneg (Real.rpow_nonneg hT_nonneg _)), hmul,
        Real.rpow_one]
      exact hx_bound
    have hp_ne : harnack_p d ≠ 0 := ne_of_gt hp_pos
    have hmul :
        harnack_p d * (harnack_p d)⁻¹ = 1 := by
      field_simp [hp_ne]
    have hT :
        (T ^ harnack_p d) ^ (harnack_p d)⁻¹ = T := by
      rw [← Real.rpow_mul hT_nonneg, hmul, Real.rpow_one]
    have hright :
        (localMoserBase d * A.1.Λ ^ ((d : ℝ) / 2) * T ^ harnack_p d) ^ (harnack_p d)⁻¹ =
          (localMoserBase d * A.1.Λ ^ ((d : ℝ) / 2)) ^ (harnack_p d)⁻¹ * T := by
      rw [show localMoserBase d * A.1.Λ ^ ((d : ℝ) / 2) * T ^ harnack_p d =
          (localMoserBase d * A.1.Λ ^ ((d : ℝ) / 2)) * T ^ harnack_p d by ring]
      rw [Real.mul_rpow hbase_nonneg (Real.rpow_nonneg hT_nonneg _), hT]
    calc
      u x ≤ (localMoserBase d * A.1.Λ ^ ((d : ℝ) / 2) * T ^ harnack_p d) ^ (harnack_p d)⁻¹ := hroot0
      _ = (localMoserBase d * A.1.Λ ^ ((d : ℝ) / 2)) ^ (harnack_p d)⁻¹ * T := hright
      _ = localHarnackConstant (d := d) A * quarterBallInf u c := by
            simp [T, localHarnackConstant, mul_assoc]
  exact hroot

omit [NeZero d] in
private theorem const_le_of_ae_const_le {μ : Measure E} (hμ : μ ≠ 0) {a b : ℝ}
    (h : ∀ᵐ _z ∂ μ, a ≤ b) :
    a ≤ b := by
  by_contra hab
  have hfalse : ∀ᵐ z ∂ μ, False := by
    simpa [hab] using h
  rw [ae_iff] at hfalse
  have hzero : μ Set.univ = 0 := by
    simpa using hfalse
  exact hμ (Measure.measure_univ_eq_zero.mp hzero)

omit [NeZero d] in
private theorem ball_oneSixteenth_subset_eighth
    {c₁ c₂ : E} (hcenters : dist c₁ c₂ ≤ (1 / 16 : ℝ)) :
    Metric.ball c₂ (1 / 16 : ℝ) ⊆ Metric.ball c₁ (1 / 8 : ℝ) := by
  intro z hz
  rw [Metric.mem_ball] at hz ⊢
  have hcenters' : dist c₂ c₁ ≤ (1 / 16 : ℝ) := by
    simpa [dist_comm] using hcenters
  have hsum : dist z c₂ + dist c₂ c₁ < 1 / 8 := by
    linarith
  exact lt_of_le_of_lt (dist_triangle _ _ _) hsum

private theorem quarterBallInf_step
    (hd : 2 < (d : ℝ))
    (A : NormalizedEllipticCoeff d (Metric.ball (0 : E) 1))
    {u : E → ℝ}
    (hu_pos : ∀ x ∈ Metric.ball (0 : E) 1, 0 < u x)
    (hsol : IsSolution A.1 u)
    {c₁ c₂ : E}
    (hc₂ : c₂ ∈ Metric.ball (0 : E) (1 / 2 : ℝ))
    (hcenters : dist c₁ c₂ ≤ (1 / 16 : ℝ)) :
    quarterBallInf u c₁ ≤
      localHarnackConstant (d := d) A * quarterBallInf u c₂ := by
  have hlocal :=
    ae_le_localHarnack_on_eighthBall (d := d) hd A hu_pos hsol hc₂
  have hnonneg_c₁ : ∀ w ∈ Metric.ball c₁ (1 / 8 : ℝ), 0 ≤ u w := by
    intro w hw
    have hc₂' : dist c₂ (0 : E) < 1 / 2 := by simpa using hc₂
    have hcenters' : dist c₁ c₂ ≤ 1 / 16 := by simpa [dist_comm] using hcenters
    have hw_unit : w ∈ Metric.ball (0 : E) 1 := by
      refine Metric.mem_ball.2 ?_
      have hw' : dist w c₁ < 1 / 8 := by simpa using hw
      calc
        dist w (0 : E) ≤ dist w c₁ + dist c₁ (0 : E) := dist_triangle _ _ _
        _ ≤ dist w c₁ + (dist c₁ c₂ + dist c₂ (0 : E)) := by
              gcongr
              exact dist_triangle _ _ _
        _ < 1 / 8 + (1 / 16 + 1 / 2) := by linarith
        _ = 11 / 16 := by norm_num
        _ < 1 := by norm_num
    exact (hu_pos _ hw_unit).le
  have hu_ae_c₁ :
      AEMeasurable u (volume.restrict (Metric.ball c₁ (1 / 8 : ℝ))) := by
    have hsub_c₁ : Metric.ball c₁ (1 / 8 : ℝ) ⊆ Metric.ball (0 : E) 1 := by
      intro z hz
      refine Metric.mem_ball.2 ?_
      have hz' : dist z c₁ < 1 / 8 := by simpa using hz
      have hc₂' : dist c₂ (0 : E) < 1 / 2 := by simpa using hc₂
      have hcenters' : dist c₁ c₂ ≤ 1 / 16 := by simpa [dist_comm] using hcenters
      calc
        dist z (0 : E) ≤ dist z c₁ + dist c₁ (0 : E) := dist_triangle _ _ _
        _ ≤ dist z c₁ + (dist c₁ c₂ + dist c₂ (0 : E)) := by
              gcongr
              exact dist_triangle _ _ _
        _ < 1 / 8 + (1 / 16 + 1 / 2) := by linarith
        _ = 11 / 16 := by norm_num
        _ < 1 := by norm_num
    exact aemeasurable_on_ball_of_isSolution (d := d) A hsol hsub_c₁
  have hquarter :
      ∀ᵐ z ∂ volume.restrict (Metric.ball c₂ (1 / 16 : ℝ)),
        quarterBallInf u c₁ ≤ u z := by
    refine ae_restrict_of_ae_restrict_of_subset
      (ball_oneSixteenth_subset_eighth hcenters) ?_
    exact quarterBallInf_le_ae (c := c₁) hu_ae_c₁ hnonneg_c₁
  have hpoint :
      ∀ᵐ z ∂ volume.restrict (Metric.ball c₂ (1 / 16 : ℝ)),
        quarterBallInf u c₁ ≤
          localHarnackConstant (d := d) A * quarterBallInf u c₂ := by
    filter_upwards [hquarter, hlocal] with z hzquarter hz
    exact le_trans hzquarter hz
  exact const_le_of_ae_const_le
    (restrict_ball_ne_zero (d := d) (c := c₂) (by norm_num))
    hpoint

private noncomputable def harnackChainCenter (c y : E) (n : ℕ) : E :=
  AffineMap.lineMap c y ((n : ℝ) / 16)

omit [NeZero d] in
@[simp] private theorem harnackChainCenter_zero (c y : E) :
    harnackChainCenter c y 0 = c := by
  simp [harnackChainCenter]

omit [NeZero d] in
@[simp] private theorem harnackChainCenter_sixteen (c y : E) :
    harnackChainCenter c y 16 = y := by
  simp [harnackChainCenter]

omit [NeZero d] in
private theorem harnackChainCenter_mem_ball
    {c y : E}
    (hc : c ∈ Metric.ball (0 : E) (1 / 2 : ℝ))
    (hy : y ∈ Metric.ball (0 : E) (1 / 2 : ℝ))
    {n : ℕ} (hn : n ≤ 16) :
    harnackChainCenter c y n ∈ Metric.ball (0 : E) (1 / 2 : ℝ) := by
  have ht : ((n : ℝ) / 16 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
    refine ⟨by positivity, ?_⟩
    have hn' : (n : ℝ) ≤ 16 := by exact_mod_cast hn
    nlinarith
  exact (convex_ball (0 : E) (1 / 2 : ℝ)).lineMap_mem hc hy ht

omit [NeZero d] in
private theorem harnackChainCenter_dist_succ_le
    {c y : E}
    (hc : c ∈ Metric.ball (0 : E) (1 / 2 : ℝ))
    (hy : y ∈ Metric.ball (0 : E) (1 / 2 : ℝ))
    {n : ℕ} (_hn : n < 16) :
    dist (harnackChainCenter c y n) (harnackChainCenter c y (n + 1)) ≤ (1 / 16 : ℝ) := by
  have hc' : dist c (0 : E) < 1 / 2 := by simpa using hc
  have hy' : dist y (0 : E) < 1 / 2 := by simpa using hy
  have hcy : dist c y ≤ 1 := by
    calc
      dist c y ≤ dist c (0 : E) + dist y (0 : E) := by
        simpa [dist_comm] using (dist_triangle c (0 : E) y)
      _ ≤ 1 / 2 + 1 / 2 := by linarith
      _ = 1 := by norm_num
  rw [harnackChainCenter, harnackChainCenter, dist_lineMap_lineMap]
  have hcoeff : dist ((n : ℝ) / 16) (((n + 1 : ℕ) : ℝ) / 16 : ℝ) = (1 / 16 : ℝ) := by
    rw [Real.dist_eq]
    have hstep_num : (n : ℝ) / 16 ≤ (((n + 1 : ℕ) : ℝ) / 16 : ℝ) := by
      have hn_le : (n : ℝ) ≤ (((n + 1 : ℕ) : ℝ) : ℝ) := by
        exact_mod_cast Nat.le_succ n
      exact div_le_div_of_nonneg_right hn_le (by positivity)
    have hneg : (n : ℝ) / 16 - (((n + 1 : ℕ) : ℝ) / 16 : ℝ) ≤ 0 := by
      linarith
    have hdiff : (((n + 1 : ℕ) : ℝ) / 16 : ℝ) - (n : ℝ) / 16 = (1 / 16 : ℝ) := by
      rw [Nat.cast_add, Nat.cast_one]
      ring
    rw [abs_of_nonpos hneg]
    linarith
  rw [hcoeff]
  nlinarith

private theorem quarterBallInf_chain_le
    (hd : 2 < (d : ℝ))
    (A : NormalizedEllipticCoeff d (Metric.ball (0 : E) 1))
    {u : E → ℝ}
    (hu_pos : ∀ x ∈ Metric.ball (0 : E) 1, 0 < u x)
    (hsol : IsSolution A.1 u)
    {c y : E}
    (hc : c ∈ Metric.ball (0 : E) (1 / 2 : ℝ))
    (hy : y ∈ Metric.ball (0 : E) (1 / 2 : ℝ)) :
    quarterBallInf u c ≤
      localHarnackConstant (d := d) A ^ 16 * quarterBallInf u y := by
  let K : ℝ := localHarnackConstant (d := d) A
  have hK_nonneg : 0 ≤ K := (localHarnackConstant_pos (d := d) hd A).le
  have hstep :
      ∀ n < 16,
        quarterBallInf u (harnackChainCenter c y n) ≤
          K * quarterBallInf u (harnackChainCenter c y (n + 1)) := by
    intro n hn
    have hc_succ :
        harnackChainCenter c y (n + 1) ∈ Metric.ball (0 : E) (1 / 2 : ℝ) :=
      harnackChainCenter_mem_ball hc hy (Nat.succ_le_of_lt hn)
    have hdist :
        dist (harnackChainCenter c y n) (harnackChainCenter c y (n + 1)) ≤ (1 / 16 : ℝ) :=
      harnackChainCenter_dist_succ_le hc hy hn
    simpa [K] using
      quarterBallInf_step (d := d) hd A hu_pos hsol hc_succ hdist
  have hiter :
      ∀ n ≤ 16,
        quarterBallInf u c ≤
          K ^ n * quarterBallInf u (harnackChainCenter c y n) := by
    intro n hn
    induction n with
    | zero =>
        simp [harnackChainCenter, K]
    | succ n ih =>
        have hn' : n ≤ 16 := Nat.le_of_succ_le hn
        have hn_lt : n < 16 := Nat.lt_of_succ_le hn
        calc
          quarterBallInf u c ≤ K ^ n * quarterBallInf u (harnackChainCenter c y n) := ih hn'
          _ ≤ K ^ n * (K * quarterBallInf u (harnackChainCenter c y (n + 1))) := by
                exact mul_le_mul_of_nonneg_left (hstep n hn_lt) (pow_nonneg hK_nonneg _)
          _ = K ^ (n + 1) * quarterBallInf u (harnackChainCenter c y (n + 1)) := by
                rw [pow_succ']
                ring
  calc
    quarterBallInf u c ≤ K ^ 16 * quarterBallInf u (harnackChainCenter c y 16) := hiter 16 le_rfl
    _ = K ^ 16 * quarterBallInf u y := by simp [harnackChainCenter]

private theorem localHarnackConstant_pow_seventeen_le_exp
    (hd : 2 < (d : ℝ))
    (A : NormalizedEllipticCoeff d (Metric.ball (0 : E) 1)) :
    localHarnackConstant (d := d) A ^ 17 ≤
      Real.exp (C_harnack d * A.1.Λ ^ ((1 : ℝ) / 2)) := by
  let K : ℝ := localHarnackConstant (d := d) A
  let s : ℝ := A.1.Λ ^ ((1 : ℝ) / 2)
  let M : ℝ := localMoserBase d
  let W : ℝ := localWeakHarnackBase d
  have hK_pos : 0 < K := localHarnackConstant_pos (d := d) hd A
  have hs_pos : 0 < s := by
    exact Real.rpow_pos_of_pos A.1.Λ_pos _
  have hM_pos : 0 < M := by
    simpa [M] using localMoserBase_pos (d := d) hd
  have hW_pos : 0 < W := by
    simpa [W] using localWeakHarnackBase_pos (d := d)
  have hs_ge_one : 1 ≤ s := by
    have hΛ_one : 1 ≤ A.1.Λ := by
      simpa [A.2] using A.1.hΛ
    unfold s
    exact Real.one_le_rpow hΛ_one (by positivity : 0 ≤ (1 / 2 : ℝ))
  have hlogM_nonneg : 0 ≤ Real.log (localMoserBase d) := by
    exact Real.log_nonneg (one_le_localMoserBase (d := d) hd)
  have hlogW_nonneg : 0 ≤ Real.log (localWeakHarnackBase d) := by
    exact Real.log_nonneg (one_le_localWeakHarnackBase (d := d) hd)
  have hΛ_one : 1 ≤ A.1.Λ := by
    simpa [A.2] using A.1.hΛ
  have hlogΛ_nonneg : 0 ≤ Real.log A.1.Λ := by
    exact Real.log_nonneg hΛ_one
  have hlogΛ_le : Real.log A.1.Λ ≤ 2 * s := by
    have hsq : s ^ (2 : ℝ) = A.1.Λ := by
      unfold s
      rw [← Real.rpow_mul A.1.Λ_nonneg]
      norm_num
    calc
      Real.log A.1.Λ = 2 * Real.log s := by
        rw [← hsq, Real.log_rpow hs_pos]
      _ ≤ 2 * s := by
        gcongr
        exact Real.log_le_self hs_pos.le
  have hlogK :
      Real.log K =
        (harnack_p d)⁻¹ *
          (Real.log M + ((d : ℝ) / 2) * Real.log A.1.Λ) +
        s * Real.log W := by
    unfold K localHarnackConstant s M W
    have hMΛ_pos : 0 < localMoserBase d * A.1.Λ ^ ((d : ℝ) / 2) := by
      refine mul_pos (localMoserBase_pos (d := d) hd) ?_
      exact Real.rpow_pos_of_pos A.1.Λ_pos _
    rw [Real.log_mul]
    · rw [Real.log_rpow hMΛ_pos]
      rw [Real.log_mul (localMoserBase_pos (d := d) hd).ne'
        (Real.rpow_pos_of_pos A.1.Λ_pos _).ne']
      rw [Real.log_rpow A.1.Λ_pos, Real.log_rpow hW_pos]
    · exact (Real.rpow_pos_of_pos hMΛ_pos _).ne'
    · exact (Real.rpow_pos_of_pos hW_pos _).ne'
  have hp_pos : 0 < harnack_p d := lt_trans zero_lt_one (harnack_p_gt_one (d := d) hd)
  have hinvp_nonneg : 0 ≤ (harnack_p d)⁻¹ := by
    exact inv_nonneg.mpr hp_pos.le
  have hinvp_le_one : (harnack_p d)⁻¹ ≤ 1 := by
    rw [harnack_p_inv_eq (d := d) hd]
    have hden_pos : 0 < (d : ℝ) - 1 := by
      linarith
    exact (div_le_one hden_pos).2 (by linarith)
  have htermM :
      (harnack_p d)⁻¹ * Real.log M ≤
        ((harnack_p d)⁻¹ * Real.log M) * s := by
    have hcoeff_nonneg : 0 ≤ (harnack_p d)⁻¹ * Real.log M :=
      mul_nonneg hinvp_nonneg hlogM_nonneg
    have hmult :
        ((harnack_p d)⁻¹ * Real.log M) * 1 ≤
          ((harnack_p d)⁻¹ * Real.log M) * s := by
      exact mul_le_mul_of_nonneg_left hs_ge_one hcoeff_nonneg
    simpa using hmult
  have htermA :
      (harnack_p d)⁻¹ * (((d : ℝ) / 2) * Real.log A.1.Λ) ≤ (d : ℝ) * s := by
    have hmid_nonneg : 0 ≤ ((d : ℝ) / 2) * Real.log A.1.Λ := by
      positivity
    have hmid_le : ((d : ℝ) / 2) * Real.log A.1.Λ ≤ (d : ℝ) * s := by
      calc
        ((d : ℝ) / 2) * Real.log A.1.Λ ≤ ((d : ℝ) / 2) * (2 * s) := by
          gcongr
        _ = (d : ℝ) * s := by
          ring
    have hle_mid : (harnack_p d)⁻¹ * (((d : ℝ) / 2) * Real.log A.1.Λ) ≤
        ((d : ℝ) / 2) * Real.log A.1.Λ := by
      have htmp :
          (harnack_p d)⁻¹ * (((d : ℝ) / 2) * Real.log A.1.Λ) ≤
            1 * (((d : ℝ) / 2) * Real.log A.1.Λ) := by
        exact mul_le_mul_of_nonneg_right hinvp_le_one hmid_nonneg
      simpa using htmp
    exact hle_mid.trans hmid_le
  have hlogK_le :
      Real.log K ≤
        (((d : ℝ) - 2) / ((d : ℝ) - 1) * Real.log M +
            (d : ℝ) + Real.log W) * s := by
    rw [hlogK]
    have hsplit :
        (((d : ℝ) - 2) / ((d : ℝ) - 1) * Real.log M +
            (d : ℝ) + Real.log W) * s
          =
        (((d : ℝ) - 2) / ((d : ℝ) - 1) * Real.log M) * s +
          (d : ℝ) * s +
          s * Real.log W := by
      ring
    have hleft_split :
        (harnack_p d)⁻¹ * (Real.log M + ((d : ℝ) / 2) * Real.log A.1.Λ) +
            s * Real.log W
          =
        (harnack_p d)⁻¹ * Real.log M +
          (harnack_p d)⁻¹ * (((d : ℝ) / 2) * Real.log A.1.Λ) +
          s * Real.log W := by
      ring
    rw [hsplit]
    rw [hleft_split]
    have hmain :
        (harnack_p d)⁻¹ * Real.log M +
            (harnack_p d)⁻¹ * (((d : ℝ) / 2) * Real.log A.1.Λ) ≤
          (((d : ℝ) - 2) / ((d : ℝ) - 1) * Real.log M) * s +
            (d : ℝ) * s := by
      have htermM' :
          (harnack_p d)⁻¹ * Real.log M ≤
            (((d : ℝ) - 2) / ((d : ℝ) - 1) * Real.log M) * s := by
        simpa [harnack_p_inv_eq (d := d) hd] using htermM
      exact add_le_add htermM' htermA
    simpa [add_assoc, add_left_comm, add_comm] using
      add_le_add_right hmain (s * Real.log W)
  have hlogKpow :
      Real.log (K ^ 17) ≤ C_harnack d * s := by
    rw [Real.log_pow, C_harnack]
    have hscaled : 17 * Real.log K ≤
        17 *
          ((((d : ℝ) - 2) / ((d : ℝ) - 1) * Real.log M +
              (d : ℝ) + Real.log W) * s) := by
      exact mul_le_mul_of_nonneg_left hlogK_le (by norm_num)
    simpa [M, W, localMoserBase, localWeakHarnackBase,
      mul_assoc, mul_left_comm, mul_comm] using hscaled
  exact (Real.log_le_iff_le_exp (pow_pos hK_pos 17)).mp hlogKpow

/-- Positive weak solutions satisfy Harnack on the unit ball.
-/
theorem harnack
    (hd : 2 < (d : ℝ))
    (A : NormalizedEllipticCoeff d (Metric.ball (0 : E) 1))
    {u : E → ℝ}
    (hu_pos : ∀ x ∈ Metric.ball (0 : E) 1, 0 < u x)
    (hsol : IsSolution A.1 u) :
    essSup u μhalf ≤
      Real.exp (C_harnack d * A.1.Λ ^ ((1 : ℝ) / 2)) *
        essInf u μhalf := by
  let K : ℝ := localHarnackConstant (d := d) A
  have hK_pos : 0 < K := localHarnackConstant_pos (d := d) hd A
  let centerOf : E → E := fun x => (15 / 16 : ℝ) • x
  have hcenter_mem :
      ∀ x ∈ Metric.closedBall (0 : E) (1 / 2 : ℝ),
        centerOf x ∈ Metric.ball (0 : E) (1 / 2 : ℝ) := by
    intro x hx
    rw [Metric.mem_ball, dist_eq_norm, sub_zero]
    have hxnorm : ‖x‖ ≤ 1 / 2 := by simpa [dist_eq_norm] using hx
    dsimp [centerOf]
    rw [norm_smul, Real.norm_of_nonneg (by positivity)]
    calc
      (15 / 16 : ℝ) * ‖x‖ ≤ (15 / 16 : ℝ) * (1 / 2 : ℝ) := by gcongr
      _ = 15 / 32 := by norm_num
      _ < 1 / 2 := by norm_num
  have hmem_cover_ball :
      ∀ x ∈ Metric.closedBall (0 : E) (1 / 2 : ℝ),
        x ∈ Metric.ball (centerOf x) (1 / 16 : ℝ) := by
    intro x hx
    rw [Metric.mem_ball, dist_eq_norm]
    have hxnorm : ‖x‖ ≤ 1 / 2 := by simpa [dist_eq_norm] using hx
    have hrepr : x - centerOf x = (1 / 16 : ℝ) • x := by
      dsimp [centerOf]
      calc
        x - (15 / 16 : ℝ) • x = (1 : ℝ) • x - (15 / 16 : ℝ) • x := by simp
        _ = ((1 : ℝ) - 15 / 16) • x := by rw [sub_smul]
        _ = (1 / 16 : ℝ) • x := by norm_num
    rw [hrepr, norm_smul, Real.norm_of_nonneg (by positivity)]
    calc
      (1 / 16 : ℝ) * ‖x‖ ≤ (1 / 16 : ℝ) * (1 / 2 : ℝ) := by gcongr
      _ = 1 / 32 := by norm_num
      _ < 1 / 16 := by norm_num
  obtain ⟨t, ht_mem, hcover⟩ :=
    (isCompact_closedBall (0 : E) (1 / 2 : ℝ)).elim_nhds_subcover
      (fun x : E => Metric.ball (centerOf x) (1 / 16 : ℝ))
      (fun x hx => IsOpen.mem_nhds Metric.isOpen_ball (hmem_cover_ball x hx))
  have hzero_mem : (0 : E) ∈ Metric.ball (0 : E) (1 / 2 : ℝ) := by
    exact Metric.mem_ball_self (by norm_num)
  have hsubset_cover :
      Metric.ball (0 : E) (1 / 2 : ℝ) ⊆ ⋃ x ∈ t, Metric.ball (centerOf x) (1 / 16 : ℝ) := by
    exact Metric.ball_subset_closedBall.trans hcover
  have hnonneg_half_ae : ∀ᵐ x ∂ μhalf, 0 ≤ u x := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    exact (hu_pos x (Metric.ball_subset_ball (by norm_num : (1 / 2 : ℝ) ≤ 1) hx)).le
  have hnonneg_on_eighthBall :
      ∀ {c z : E},
        c ∈ Metric.ball (0 : E) (1 / 2 : ℝ) →
        z ∈ Metric.ball c (1 / 8 : ℝ) →
        0 ≤ u z := by
    intro c z hc hz
    have hc_closed : c ∈ Metric.closedBall (0 : E) (1 / 2 : ℝ) := by
      exact Metric.mem_closedBall.2 (le_of_lt (Metric.mem_ball.1 hc))
    have hz_unit : z ∈ Metric.ball (0 : E) 1 :=
      ball_subset_unitBall_of_mem_closedBall_half (d := d) hc_closed (by positivity) (by norm_num) hz
    exact (hu_pos z hz_unit).le
  have hupper0 :
      ∀ᵐ x ∂ μhalf, u x ≤ K ^ 17 * quarterBallInf u 0 := by
    refine ae_on_set_of_ae_on_finite_cover (μ := volume)
      (s := Metric.ball (0 : E) (1 / 2 : ℝ))
      (U := fun x : E => Metric.ball (centerOf x) (1 / 16 : ℝ))
      hsubset_cover ?_
    intro x hx
    let c : E := centerOf x
    have hc_ball : c ∈ Metric.ball (0 : E) (1 / 2 : ℝ) := hcenter_mem x (ht_mem x hx)
    have hchain :
        quarterBallInf u c ≤ K ^ 16 * quarterBallInf u 0 := by
      simpa [K] using
        quarterBallInf_chain_le (d := d) hd A hu_pos hsol hc_ball hzero_mem
    filter_upwards [ae_le_localHarnack_on_eighthBall (d := d) hd A hu_pos hsol hc_ball] with x hx
    calc
      u x ≤ K * quarterBallInf u c := by simpa [K] using hx
      _ ≤ K * (K ^ 16 * quarterBallInf u 0) := by
            gcongr
      _ = K ^ 17 * quarterBallInf u 0 := by
            rw [pow_succ']
            ring
  have hcore :
      essSup u μhalf ≤ K ^ 17 * essInf u μhalf := by
    have hcenter_bound :
        ∀ {y : E}, y ∈ Metric.ball (0 : E) (1 / 2 : ℝ) →
          essSup u μhalf ≤ K ^ 17 * quarterBallInf u y := by
      intro y hy
      have hhalf :
          ∀ᵐ x ∂ μhalf, u x ≤ K ^ 17 * quarterBallInf u y := by
        refine ae_on_set_of_ae_on_finite_cover (μ := volume)
          (s := Metric.ball (0 : E) (1 / 2 : ℝ))
          (U := fun x : E => Metric.ball (centerOf x) (1 / 16 : ℝ))
          hsubset_cover ?_
        intro x hx
        let c : E := centerOf x
        have hc_ball : c ∈ Metric.ball (0 : E) (1 / 2 : ℝ) := hcenter_mem x (ht_mem x hx)
        have hchain :
            quarterBallInf u c ≤ K ^ 16 * quarterBallInf u y := by
          simpa [K] using
            quarterBallInf_chain_le (d := d) hd A hu_pos hsol hc_ball hy
        filter_upwards [ae_le_localHarnack_on_eighthBall (d := d) hd A hu_pos hsol hc_ball] with x hx
        calc
          u x ≤ K * quarterBallInf u c := by simpa [K] using hx
          _ ≤ K * (K ^ 16 * quarterBallInf u y) := by
                gcongr
          _ = K ^ 17 * quarterBallInf u y := by
                rw [pow_succ']
                ring
      exact essSup_halfBall_le_of_ae_bound hnonneg_half_ae hhalf
    have hlow_ae :
        ∀ᵐ y ∂ μhalf, essSup u μhalf / K ^ 17 ≤ u y := by
      refine ae_on_set_of_ae_on_finite_cover (μ := volume)
        (s := Metric.ball (0 : E) (1 / 2 : ℝ))
        (U := fun x : E => Metric.ball (centerOf x) (1 / 16 : ℝ))
        hsubset_cover ?_
      intro x hx
      let c : E := centerOf x
      have hc_ball : c ∈ Metric.ball (0 : E) (1 / 2 : ℝ) := hcenter_mem x (ht_mem x hx)
      have hcenter_div :
          essSup u μhalf / K ^ 17 ≤ quarterBallInf u c := by
        exact (div_le_iff₀ (pow_pos hK_pos 17)).2
          (by simpa [mul_comm, mul_left_comm, mul_assoc] using hcenter_bound hc_ball)
      have hu_ae_c :
          AEMeasurable u (volume.restrict (Metric.ball c (1 / 8 : ℝ))) := by
        have hsub_c : Metric.ball c (1 / 8 : ℝ) ⊆ Metric.ball (0 : E) 1 := by
          intro z hz
          have hc_closed : c ∈ Metric.closedBall (0 : E) (1 / 2 : ℝ) := by
            exact Metric.mem_closedBall.2 (le_of_lt (Metric.mem_ball.1 hc_ball))
          exact ball_subset_unitBall_of_mem_closedBall_half
            (d := d) hc_closed (by positivity) (by norm_num) hz
        exact aemeasurable_on_ball_of_isSolution (d := d) A hsol hsub_c
      have hquarter_small :
          ∀ᵐ z ∂ volume.restrict (Metric.ball c (1 / 16 : ℝ)),
            quarterBallInf u c ≤ u z := by
        refine ae_restrict_of_ae_restrict_of_subset
          (Metric.ball_subset_ball (by norm_num : (1 / 16 : ℝ) ≤ 1 / 8)) ?_
        exact quarterBallInf_le_ae (c := c) hu_ae_c (fun z hz => hnonneg_on_eighthBall hc_ball hz)
      filter_upwards [hquarter_small] with z hz
      exact le_trans hcenter_div hz
    have hlow :
        essSup u μhalf / K ^ 17 ≤ essInf u μhalf :=
      le_essInf_halfBall_of_ae_bound hlow_ae hupper0
    have hmul : essSup u μhalf ≤ essInf u μhalf * K ^ 17 :=
      (div_le_iff₀ (pow_pos hK_pos 17)).mp hlow
    simpa [mul_comm, mul_left_comm, mul_assoc, K] using hmul
  have hessInf_nonneg : 0 ≤ essInf u μhalf := by
    exact
      le_essInf_real_of_ae_le
        (μ := μhalf)
        (restrict_ball_ne_zero (c := (0 : E)) (r := (1 / 2 : ℝ)) (by norm_num))
        (by simpa using hnonneg_half_ae)
  have hKexp :
      K ^ 17 ≤ Real.exp (C_harnack d * A.1.Λ ^ ((1 : ℝ) / 2)) := by
    simpa [K] using localHarnackConstant_pow_seventeen_le_exp (d := d) hd A
  calc
    essSup u μhalf ≤ K ^ 17 * essInf u μhalf := hcore
    _ ≤ Real.exp (C_harnack d * A.1.Λ ^ ((1 : ℝ) / 2)) * essInf u μhalf := by
          exact mul_le_mul_of_nonneg_right hKexp hessInf_nonneg

/-- Harnack, packaged directly for the equality-form local weak-solution
interface from Chapter 04. -/
theorem harnack_of_homogeneousWeakSolution
    (hd : 2 < (d : ℝ))
    (A : NormalizedEllipticCoeff d (Metric.ball (0 : E) 1))
    {u : E → ℝ}
    (hu_pos : ∀ x ∈ Metric.ball (0 : E) 1, 0 < u x)
    (hweak : IsHomogeneousWeakSolution A.1 u) :
    essSup u μhalf ≤
      Real.exp (C_harnack d * A.1.Λ ^ ((1 : ℝ) / 2)) *
        essInf u μhalf := by
  exact harnack hd A hu_pos (isHomogeneousWeakSolution_isSolution hweak)

end DeGiorgi
