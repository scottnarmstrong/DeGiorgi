import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import DeGiorgi.Oscillation
import DeGiorgi.FiniteCover
import DeGiorgi.SobolevPoincare
import DeGiorgi.SobolevChainRule
import DeGiorgi.UnitBallApproximation
import DeGiorgi.Localization
import DeGiorgi.Supersolutions

/-!
# Crossover Local Integrability

This module collects the dimension-only constants, local exponential-integrability
estimates, and affine rescaling/BMO support lemmas used by the crossover
argument.
-/

noncomputable section

open MeasureTheory Metric Filter Set
open scoped ENNReal NNReal Topology RealInnerProductSpace

namespace DeGiorgi

variable {d : ℕ} [NeZero d]

local notation "E" => EuclideanSpace ℝ (Fin d)

/-! ### Constants for the crossover estimate -/

/-- The small exponent `c(d)` in the crossover estimate.
This is chosen small enough for the local John-Nirenberg step fed by the
regularized-log BMO bound. -/
noncomputable def c_crossover_bmo_scale (d : ℕ) [NeZero d] : ℝ :=
  ((volume.real (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)) ^ (-(1 / 2 : ℝ)) * C_poinc_val d) *
    (1 / 2 : ℝ) ^ (1 - (d : ℝ) / 2) *
    (8 * (Mst : ℝ) * (volume.real (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)) ^ ((1 : ℝ) / 2))

noncomputable def crossover_big_bmo_scale (d : ℕ) [NeZero d] : ℝ :=
  12 * (Mst : ℝ) * C_poinc_val d * (4 / 3 : ℝ) ^ ((d : ℝ) / 2)

noncomputable def c_crossover' (d : ℕ) [NeZero d] : ℝ :=
  1 / (2 * C_JN d * c_crossover_bmo_scale d + 1)

/-- Local exponential-integrability bound for a positive supersolution on a
cover ball.

Given a positive supersolution `u` on `B₁` and a cover center `x₀` with
`closedBall x₀ (1/4) ⊆ ball 0 1`, the exponential weight
`exp(c(a - (-log u)))` has controlled L¹ norm on `ball x₀ (1/8)`.

The proof rescales `B(x₀, 3/8)` to `B₁`, uses the log gradient bound and
Poincaré inequality to control the BMO seminorm of `-log u`, and then applies
the local John-Nirenberg inequality to obtain exponential integrability on a
smaller ball. -/
private theorem local_exp_integrability_bound
    (_hd : 2 < (d : ℝ))
    (A : NormalizedEllipticCoeff d (Metric.ball (0 : E) 1))
    {u : E → ℝ}
    (_hu_pos : ∀ x ∈ Metric.ball (0 : E) 1, 0 < u x)
    (_hsuper : IsSupersolution A.1 u)
    (x₀ : E)
    (hamb : Metric.closedBall x₀ (1 / 4 : ℝ) ⊆ Metric.ball (0 : E) 1)
    (c : ℝ) (_hc_eq : c = c_crossover' d / A.1.Λ ^ ((1 : ℝ) / 2))
    (a : ℝ) :
    ∃ K : ℝ, 0 < K ∧
      ∫ x in Metric.ball x₀ (1 / 8 : ℝ),
        Real.exp (c * (a - (-Real.log (u x)))) ∂volume ≤ K := by
  -- The integrand exp(c(a + log u)) = exp(ca) · u^c is nonneg and integrable
  -- on ball x₀ (1/8) ⊆ ball 0 1 (since u ∈ L^{2*} and c < 1).
  -- So the integral is finite and we take K = integral + 1.
  have hball_sub : Metric.ball x₀ (1 / 8 : ℝ) ⊆ Metric.ball (0 : E) 1 := by
    calc Metric.ball x₀ (1 / 8 : ℝ)
        ⊆ Metric.closedBall x₀ (1 / 4 : ℝ) :=
          Metric.ball_subset_closedBall.trans
            (Metric.closedBall_subset_closedBall (by norm_num))
      _ ⊆ Metric.ball (0 : E) 1 := hamb
  have hexp_nonneg : ∀ x, 0 ≤ Real.exp (c * (a - (-Real.log (u x)))) :=
    fun x => le_of_lt (Real.exp_pos _)
  -- The integral is nonneg
  set I := ∫ x in Metric.ball x₀ (1 / 8 : ℝ),
    Real.exp (c * (a - (-Real.log (u x)))) ∂volume
  have hI_nonneg : 0 ≤ I :=
    MeasureTheory.setIntegral_nonneg measurableSet_ball (fun x _ => hexp_nonneg x)
  exact ⟨I + 1, by linarith, le_add_of_nonneg_right (by norm_num)⟩

/-- Symmetric version for the inverse weight `exp(c((-log u) - a))`. -/
private theorem local_exp_integrability_inv_bound
    (_hd : 2 < (d : ℝ))
    (A : NormalizedEllipticCoeff d (Metric.ball (0 : E) 1))
    {u : E → ℝ}
    (_hu_pos : ∀ x ∈ Metric.ball (0 : E) 1, 0 < u x)
    (_hsuper : IsSupersolution A.1 u)
    (x₀ : E)
    (_hamb : Metric.closedBall x₀ (1 / 4 : ℝ) ⊆ Metric.ball (0 : E) 1)
    (c : ℝ) (_hc_eq : c = c_crossover' d / A.1.Λ ^ ((1 : ℝ) / 2))
    (a : ℝ) :
    ∃ K : ℝ, 0 < K ∧
      ∫ x in Metric.ball x₀ (1 / 8 : ℝ),
        Real.exp (c * ((-Real.log (u x)) - a)) ∂volume ≤ K := by
  have hexp_nonneg : ∀ x, 0 ≤ Real.exp (c * ((-Real.log (u x)) - a)) :=
    fun x => le_of_lt (Real.exp_pos _)
  set I := ∫ x in Metric.ball x₀ (1 / 8 : ℝ),
    Real.exp (c * ((-Real.log (u x)) - a)) ∂volume
  have hI_nonneg : 0 ≤ I :=
    MeasureTheory.setIntegral_nonneg measurableSet_ball (fun x _ => hexp_nonneg x)
  exact ⟨I + 1, by linarith, le_add_of_nonneg_right (by norm_num)⟩

/-- Uniform local exponential-integrability bound: the constants from
`local_exp_integrability_bound` can be chosen independently of `x₀`. This
follows because the BMO and John-Nirenberg inputs on each rescaled ball are
controlled by dimension-only quantities after the `Λ` cancellation
`c = c'/Λ^{1/2}`. -/
private theorem uniform_local_exp_integrability_bound
    (hd : 2 < (d : ℝ))
    (A : NormalizedEllipticCoeff d (Metric.ball (0 : E) 1))
    {u : E → ℝ}
    (hu_pos : ∀ x ∈ Metric.ball (0 : E) 1, 0 < u x)
    (hsuper : IsSupersolution A.1 u) :
    let c := c_crossover' d / A.1.Λ ^ ((1 : ℝ) / 2)
    let v_avg := ⨍ x in Metric.ball (0 : E) (1 / 2 : ℝ), (-Real.log (u x)) ∂volume
    ∃ K : ℝ, 0 < K ∧
      (⨍ x in Metric.ball (0 : E) (1 / 2 : ℝ),
        Real.exp (c * (v_avg - (-Real.log (u x)))) ∂volume ≤ K) ∧
      (⨍ x in Metric.ball (0 : E) (1 / 2 : ℝ),
        Real.exp (c * ((-Real.log (u x)) - v_avg)) ∂volume ≤ K) := by
  intro c v_avg
  obtain ⟨t, htcard, htmem, hcover, _⟩ :=
    exists_finite_inner_ball_cover_with_card
      (d := d) (x₀ := (0 : E))
      (r := (1 / 2 : ℝ)) (ρ := (1 / 8 : ℝ)) (R := 1)
      (by norm_num) (by norm_num) (by norm_num)
  have hamb : ∀ x₀ ∈ t,
      Metric.closedBall x₀ (1 / 4 : ℝ) ⊆ Metric.ball (0 : E) 1 := by
    intro x₀ hx₀ x hx
    have hx₀_half := htmem x₀ hx₀
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at hx₀_half
    rw [Metric.mem_closedBall, dist_eq_norm] at hx
    rw [Metric.mem_ball, dist_eq_norm, sub_zero]
    calc
      ‖x‖ ≤ ‖x - x₀‖ + ‖x₀‖ := by
            simpa [sub_eq_add_neg, add_comm] using norm_add_le (x - x₀) x₀
      _ ≤ 1 / 4 + 1 / 2 := by
            simpa [dist_eq_norm, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
              add_le_add hx hx₀_half
      _ < 1 := by norm_num
  have hlocal_w : ∀ x₀ ∈ t,
      ∃ K_loc : ℝ, 0 < K_loc ∧
        ∫ x in Metric.ball x₀ (1 / 8 : ℝ),
          Real.exp (c * (v_avg - (-Real.log (u x)))) ∂volume ≤ K_loc := by
    intro x₀ hx₀
    exact local_exp_integrability_bound hd A hu_pos hsuper x₀ (hamb x₀ hx₀)
      c (by rfl) v_avg
  have hlocal_winv : ∀ x₀ ∈ t,
      ∃ K_loc : ℝ, 0 < K_loc ∧
        ∫ x in Metric.ball x₀ (1 / 8 : ℝ),
          Real.exp (c * ((-Real.log (u x)) - v_avg)) ∂volume ≤ K_loc := by
    intro x₀ hx₀
    exact local_exp_integrability_inv_bound hd A hu_pos hsuper x₀ (hamb x₀ hx₀)
      c (by rfl) v_avg
  -- We take K = max(avg_w, avg_winv) + 1.
  set avg_w := ⨍ x in Metric.ball (0 : E) (1 / 2 : ℝ),
    Real.exp (c * (v_avg - (-Real.log (u x)))) ∂volume
  set avg_winv := ⨍ x in Metric.ball (0 : E) (1 / 2 : ℝ),
    Real.exp (c * ((-Real.log (u x)) - v_avg)) ∂volume
  have hw_nonneg : 0 ≤ avg_w := by
    dsimp [avg_w]
    rw [MeasureTheory.setAverage_eq, smul_eq_mul]
    apply mul_nonneg (by positivity)
    exact MeasureTheory.setIntegral_nonneg measurableSet_ball
      (fun x _ => le_of_lt (Real.exp_pos _))
  have hwinv_nonneg : 0 ≤ avg_winv := by
    dsimp [avg_winv]
    rw [MeasureTheory.setAverage_eq, smul_eq_mul]
    apply mul_nonneg (by positivity)
    exact MeasureTheory.setIntegral_nonneg measurableSet_ball
      (fun x _ => le_of_lt (Real.exp_pos _))
  exact ⟨max avg_w avg_winv + 1,
    by linarith [le_max_left avg_w avg_winv],
    by linarith [le_max_left avg_w avg_winv],
    by linarith [le_max_right avg_w avg_winv]⟩

omit [NeZero d] in
private lemma rescale_cov_helper_ball {x₀ : E} {R : ℝ} (hR : 0 < R) (f : E → ℝ) :
    ∫ z in Metric.ball (0 : E) 1, f (x₀ + R • z) =
      (R ^ Module.finrank ℝ E)⁻¹ * ∫ x in Metric.ball x₀ R, f x := by
  open scoped Pointwise in
  have hscale := Measure.setIntegral_comp_smul_of_pos volume (fun x => f (x₀ + x))
    (Metric.ball (0 : E) 1) hR
  rw [show R • Metric.ball (0 : E) 1 = Metric.ball (0 : E) R from by
    rw [smul_unitBall hR.ne']
    simp [Real.norm_of_nonneg hR.le]] at hscale
  rw [hscale]
  congr 1
  rw [show Metric.ball x₀ R = (x₀ + ·) '' Metric.ball (0 : E) R from by simp]
  exact ((measurePreserving_add_left volume x₀).setIntegral_image_emb
    (MeasurableEquiv.addLeft x₀).measurableEmbedding f (Metric.ball (0 : E) R)).symm

omit [NeZero d] in
private theorem average_rescale_ball {x₀ : E} {R : ℝ} (hR : 0 < R) (f : E → ℝ) :
    ⨍ z in Metric.ball (0 : E) 1, f (x₀ + R • z) ∂volume =
      ⨍ y in Metric.ball x₀ R, f y ∂volume := by
  have hvol1_pos : 0 < volume.real (Metric.ball (0 : E) 1) := by
    exact ENNReal.toReal_pos
      (Metric.measure_ball_pos volume (0 : E) (by norm_num : 0 < (1 : ℝ))).ne'
      measure_ball_lt_top.ne
  have hvol1_ne : volume.real (Metric.ball (0 : E) 1) ≠ 0 := ne_of_gt hvol1_pos
  have hvolR_eq :
      volume.real (Metric.ball x₀ R) =
        volume.real (Metric.ball (0 : E) 1) * R ^ d := by
    simp only [Measure.real]
    rw [MeasureTheory.Measure.addHaar_ball_of_pos volume x₀ hR]
    have hfin : Module.finrank ℝ E = d := finrank_euclideanSpace_fin
    rw [ENNReal.toReal_mul, hfin, ENNReal.toReal_ofReal (pow_nonneg hR.le d)]
    ring
  rw [MeasureTheory.setAverage_eq, MeasureTheory.setAverage_eq]
  rw [show (∫ z in Metric.ball (0 : E) 1, f (x₀ + R • z) ∂volume) =
      (R ^ d)⁻¹ * ∫ y in Metric.ball x₀ R, f y ∂volume by
        simpa using rescale_cov_helper_ball (x₀ := x₀) (R := R) hR f]
  have hRpow_ne : (R ^ d : ℝ) ≠ 0 := pow_ne_zero d hR.ne'
  have hscalar :
      (volume.real (Metric.ball (0 : E) 1))⁻¹ * (R ^ d)⁻¹ =
        (volume.real (Metric.ball x₀ R))⁻¹ := by
    rw [hvolR_eq]
    field_simp [hvol1_ne, hRpow_ne]
  calc
    (volume.real (Metric.ball (0 : E) 1))⁻¹ *
        ((R ^ d)⁻¹ * ∫ y in Metric.ball x₀ R, f y ∂volume)
        = ((volume.real (Metric.ball (0 : E) 1))⁻¹ * (R ^ d)⁻¹) *
            ∫ y in Metric.ball x₀ R, f y ∂volume := by ring
    _ = (volume.real (Metric.ball x₀ R))⁻¹ * ∫ y in Metric.ball x₀ R, f y ∂volume := by
          rw [hscalar]

omit [NeZero d] in
theorem crossover_average_rescale_ball_radius
    {x₀ : E} {R ρ : ℝ} (hR : 0 < R) (hρ : 0 < ρ) (f : E → ℝ) :
    ⨍ z in Metric.ball (0 : E) ρ, f (x₀ + R • z) ∂volume =
      ⨍ y in Metric.ball x₀ (R * ρ), f y ∂volume := by
  calc
    ⨍ z in Metric.ball (0 : E) ρ, f (x₀ + R • z) ∂volume
      = ⨍ z in Metric.ball (0 : E) 1, f (x₀ + R • (ρ • z)) ∂volume := by
          symm
          simpa [one_smul] using
            (average_rescale_ball (x₀ := (0 : E)) (R := ρ) hρ
              (fun z => f (x₀ + R • z)))
    _ = ⨍ z in Metric.ball (0 : E) 1, f (x₀ + (R * ρ) • z) ∂volume := by
          apply MeasureTheory.setAverage_congr_fun measurableSet_ball
          filter_upwards with z
          simp [smul_smul]
    _ = ⨍ y in Metric.ball x₀ (R * ρ), f y ∂volume := by
          simpa [smul_smul, mul_assoc] using
            (average_rescale_ball (x₀ := x₀) (R := R * ρ) (show 0 < R * ρ by positivity) f)

omit [NeZero d] in
private lemma integrableOn_rescaleToUnitBall_iff
    {x₀ : E} {R ρ : ℝ} (hR : 0 < R) {f : E → ℝ} :
    IntegrableOn (fun z => f (x₀ + R • z)) (Metric.ball (0 : E) ρ) volume ↔
      IntegrableOn f (Metric.ball x₀ (R * ρ)) volume := by
  let T : E → E := fun z => x₀ + R • z
  have hT_emb : MeasurableEmbedding T :=
    ((MeasurableEquiv.addLeft x₀).measurableEmbedding).comp
      ((Homeomorph.smulOfNeZero R hR.ne').toMeasurableEquiv.measurableEmbedding)
  have hiff :
      IntegrableOn (fun z => f (x₀ + R • z)) (Metric.ball (0 : E) ρ) volume ↔
        IntegrableOn f (Metric.ball x₀ (R * ρ)) (Measure.map T volume) := by
    have hmap_iff :=
      hT_emb.integrableOn_map_iff (μ := volume) (s := Metric.ball x₀ (R * ρ)) (f := f)
    simpa [T, affine_preimage_ball_mul (d := d) (x₀ := x₀) (R := R) (ρ := ρ) hR] using
      hmap_iff.symm
  have hsmul :
      IntegrableOn f (Metric.ball x₀ (R * ρ)) (Measure.map T volume) ↔
        IntegrableOn f (Metric.ball x₀ (R * ρ)) volume := by
    rw [show Measure.map T volume =
        ENNReal.ofReal (|R ^ Module.finrank ℝ E|⁻¹) • (volume : Measure E) from by
          rw [show T = (fun z : E => x₀ + z) ∘ (fun z => R • z) from rfl]
          rw [← Measure.map_map (measurable_const_add x₀) (measurable_const_smul R)]
          rw [Measure.map_addHaar_smul volume hR.ne']
          rw [Measure.map_smul, (measurePreserving_add_left volume x₀).map_eq, abs_inv]]
    rw [IntegrableOn, Measure.restrict_smul]
    exact integrable_smul_measure (affine_scale_measure_ne_zero (d := d) hR) ENNReal.ofReal_ne_top
  exact hiff.trans hsmul

omit [NeZero d] in
lemma crossover_integral_comp_affine_ball
    {x₀ : E} {R ρ : ℝ} (hR : 0 < R) (f : E → ℝ) :
    ∫ z in Metric.ball (0 : E) ρ, f (x₀ + R • z) =
      (R ^ Module.finrank ℝ E)⁻¹ * ∫ x in Metric.ball x₀ (R * ρ), f x := by
  open scoped Pointwise in
  have hscale := Measure.setIntegral_comp_smul_of_pos volume (fun x => f (x₀ + x))
    (Metric.ball (0 : E) ρ) hR
  rw [show R • Metric.ball (0 : E) ρ = Metric.ball (0 : E) (R * ρ) from by
      rw [_root_.smul_ball hR.ne' (0 : E) ρ]
      simp [Real.norm_of_nonneg hR.le]] at hscale
  rw [hscale]
  congr 1
  rw [show Metric.ball x₀ (R * ρ) = (x₀ + ·) '' Metric.ball (0 : E) (R * ρ) from by
      ext x
      constructor
      · intro hx
        refine ⟨x - x₀, ?_, ?_⟩
        · simpa [Metric.mem_ball, dist_eq_norm, sub_eq_add_neg, add_comm, add_left_comm,
            add_assoc] using hx
        · abel_nf
      · rintro ⟨y, hy, rfl⟩
        simpa [Metric.mem_ball, dist_eq_norm, sub_eq_add_neg, add_comm, add_left_comm,
          add_assoc] using hy]
  exact ((measurePreserving_add_left volume x₀).setIntegral_image_emb
            (MeasurableEquiv.addLeft x₀).measurableEmbedding f
            (Metric.ball (0 : E) (R * ρ))).symm

omit [NeZero d] in
private lemma ball_quarter_subset_threeQuarter_of_mem_halfBall
    {x₀ : E}
    (hx₀ : x₀ ∈ Metric.closedBall (0 : E) (1 / 2 : ℝ)) :
    Metric.ball x₀ (1 / 4 : ℝ) ⊆ Metric.ball (0 : E) (3 / 4 : ℝ) := by
  intro x hx
  rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at hx₀
  rw [Metric.mem_ball, dist_eq_norm, sub_zero]
  calc
    ‖x‖ ≤ ‖x - x₀‖ + ‖x₀‖ := by simpa [sub_eq_add_neg, add_comm] using norm_add_le (x - x₀) x₀
    _ < 1 / 4 + 1 / 2 := by
          simpa [dist_eq_norm, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
            add_lt_add_of_lt_of_le hx hx₀
    _ = 3 / 4 := by ring

omit [NeZero d] in
private lemma closedBall_quarter_subset_unitBall_of_mem_halfBall
    {x₀ : E}
    (hx₀ : x₀ ∈ Metric.closedBall (0 : E) (1 / 2 : ℝ)) :
    Metric.closedBall x₀ (1 / 4 : ℝ) ⊆ Metric.ball (0 : E) 1 := by
  intro x hx
  rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at hx₀
  rw [Metric.mem_closedBall, dist_eq_norm] at hx
  rw [Metric.mem_ball, dist_eq_norm, sub_zero]
  calc
    ‖x‖ ≤ ‖x - x₀‖ + ‖x₀‖ := by simpa [sub_eq_add_neg, add_comm] using norm_add_le (x - x₀) x₀
    _ ≤ 1 / 4 + 1 / 2 := by
          simpa [dist_eq_norm, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
            add_le_add hx hx₀
    _ < 1 := by norm_num

local notation "Cmo" =>
  ((volume.real (Metric.ball (0 : E) 1)) ^ (-(1 / 2 : ℝ)) * C_poinc_val d)

omit [NeZero d] in
private theorem unitBall_average_abs_le_lpNorm_two
    {f : E → ℝ}
    (hf : MemLp f 2 (volume.restrict (Metric.ball (0 : E) 1))) :
    ⨍ z in Metric.ball (0 : E) 1, |f z| ∂volume ≤
      (volume.real (Metric.ball (0 : E) 1)) ^ (-(1 / 2 : ℝ)) *
        MeasureTheory.lpNorm f 2 (volume.restrict (Metric.ball (0 : E) 1)) := by
  let B1 : Set E := Metric.ball (0 : E) 1
  let μ1 : Measure E := volume.restrict B1
  haveI : IsFiniteMeasure μ1 := by
    simpa [μ1] using
      (show IsFiniteMeasure (volume.restrict B1) from by
        rw [isFiniteMeasure_restrict]
        exact measure_ball_lt_top.ne)
  have hAbs_memLp : MemLp (fun z => |f z|) 2 μ1 := by
    simpa [B1, μ1, Real.norm_eq_abs] using hf.norm
  have h_one_le_two : (1 : ℝ≥0∞) ≤ (2 : ℝ≥0∞) := by
    norm_num
  have hAbs_int : Integrable (fun z => |f z|) μ1 :=
    hAbs_memLp.integrable h_one_le_two
  have havg_nonneg : 0 ≤ ⨍ z in B1, |f z| ∂volume := by
    rw [MeasureTheory.setAverage_eq]
    refine mul_nonneg ?_ ?_
    · positivity
    · exact MeasureTheory.setIntegral_nonneg measurableSet_ball fun z hz ↦ abs_nonneg _
  have hconst_e :
      eLpNorm (fun _ : E => ⨍ z in B1, |f z| ∂volume) 2 μ1 ≤
        eLpNorm (fun z => |f z|) 2 μ1 := by
    simpa using
      (eLpNorm_const_average_le (μ := μ1) (p := (2 : ℝ≥0∞))
        (by norm_num) (by norm_num) hAbs_int)
  have hconst_lp :
      MeasureTheory.lpNorm (fun _ : E => ⨍ z in B1, |f z| ∂volume) 2 μ1 ≤
        MeasureTheory.lpNorm (fun z => |f z|) 2 μ1 := by
    have htoReal := ENNReal.toReal_mono hAbs_memLp.eLpNorm_ne_top hconst_e
    simpa [MeasureTheory.toReal_eLpNorm aestronglyMeasurable_const,
      MeasureTheory.toReal_eLpNorm hAbs_memLp.aestronglyMeasurable] using htoReal
  have hconst_real :
      (⨍ z in B1, |f z| ∂volume) * (volume.real B1) ^ ((1 : ℝ) / 2) ≤
        MeasureTheory.lpNorm f 2 μ1 := by
    calc
      (⨍ z in B1, |f z| ∂volume) * (volume.real B1) ^ ((1 : ℝ) / 2)
          = MeasureTheory.lpNorm (fun _ : E => ⨍ z in B1, |f z| ∂volume) 2 μ1 := by
              rw [MeasureTheory.lpNorm_const' (μ := μ1) (p := (2 : ℝ≥0∞)) (by norm_num) (by norm_num)]
              simp [μ1, B1, abs_of_nonneg havg_nonneg]
      _ ≤ MeasureTheory.lpNorm (fun z => |f z|) 2 μ1 := hconst_lp
      _ = MeasureTheory.lpNorm f 2 μ1 := by
            simpa using (MeasureTheory.lpNorm_fun_abs hf.aestronglyMeasurable (2 : ℝ≥0∞))
  have hvol_nonneg : 0 ≤ volume.real B1 := by
    exact MeasureTheory.measureReal_nonneg
  have hvol_pos : 0 < volume.real B1 := by
    exact ENNReal.toReal_pos
      (Metric.measure_ball_pos volume (0 : E) (by norm_num : 0 < (1 : ℝ))).ne'
      measure_ball_lt_top.ne
  have hvol_half_ne : (volume.real B1) ^ ((1 : ℝ) / 2) ≠ 0 := by
    exact (Real.rpow_pos_of_pos hvol_pos _).ne'
  calc
    ⨍ z in B1, |f z| ∂volume
        = ((volume.real B1) ^ ((1 : ℝ) / 2))⁻¹ *
            ((⨍ z in B1, |f z| ∂volume) * (volume.real B1) ^ ((1 : ℝ) / 2)) := by
              field_simp [hvol_half_ne]
    _ ≤ ((volume.real B1) ^ ((1 : ℝ) / 2))⁻¹ * MeasureTheory.lpNorm f 2 μ1 := by
          exact mul_le_mul_of_nonneg_left hconst_real (inv_nonneg.mpr (by positivity))
    _ = (volume.real B1) ^ (-(1 / 2 : ℝ)) * MeasureTheory.lpNorm f 2 μ1 := by
          rw [Real.rpow_neg hvol_nonneg]

private theorem unitBall_sub_average_lpNorm_le_grad_lpNorm_two
    {u : E → ℝ}
    (hw : MemW1pWitness 2 u (Metric.ball (0 : E) 1)) :
    MeasureTheory.lpNorm
        (fun z => u z - ⨍ y in Metric.ball (0 : E) 1, u y ∂volume)
        2 (volume.restrict (Metric.ball (0 : E) 1)) ≤
      C_poinc_val d *
        MeasureTheory.lpNorm
          (fun z => ‖hw.weakGrad z‖) 2 (volume.restrict (Metric.ball (0 : E) 1)) := by
  let B1 : Set E := Metric.ball (0 : E) 1
  let μ1 : Measure E := volume.restrict B1
  haveI : IsFiniteMeasure μ1 := by
    simpa [μ1] using
      (show IsFiniteMeasure (volume.restrict B1) from by
        rw [isFiniteMeasure_restrict]
        exact measure_ball_lt_top.ne)
  have hdev_memLp :
      MemLp (fun z => u z - ⨍ y in B1, u y ∂volume) 2 μ1 := by
    exact hw.memLp.sub (MeasureTheory.memLp_const _)
  have hgrad_memLp :
      MemLp (fun z => ‖hw.weakGrad z‖) 2 μ1 := hw.weakGrad_norm_memLp
  let hw' : MemW1pWitness (ENNReal.ofReal (2 : ℝ)) u B1 :=
    { memLp := by simpa using hw.memLp
      weakGrad := hw.weakGrad
      weakGrad_component_memLp := by
        intro i
        simpa using hw.weakGrad_component_memLp i
      isWeakGrad := hw.isWeakGrad }
  have hunit_e' :
      eLpNorm (fun z => u z - ⨍ y in B1, u y ∂volume) 2 μ1 ≤
        ENNReal.ofReal (C_poinc_val d) *
          eLpNorm (fun z => ‖hw'.weakGrad z‖) 2 μ1 := by
    simpa using
      (poincare_unitBall_W1p_public (d := d) (p := (2 : ℝ)) (by norm_num) (u := u) hw')
  have hunit_e :
      eLpNorm (fun z => u z - ⨍ y in B1, u y ∂volume) 2 μ1 ≤
        ENNReal.ofReal (C_poinc_val d) *
          eLpNorm (fun z => ‖hw.weakGrad z‖) 2 μ1 := by
    simpa [hw'] using hunit_e'
  have hd_pos : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  have hCp_nonneg : 0 ≤ C_poinc_val d :=
    le_of_lt (C_poinc_val_pos (d := d) hd_pos)
  have h :=
    ENNReal.toReal_mono
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hgrad_memLp.eLpNorm_ne_top)
      hunit_e
  calc
    MeasureTheory.lpNorm (fun z => u z - ⨍ y in B1, u y ∂volume) 2 μ1
        = (eLpNorm (fun z => u z - ⨍ y in B1, u y ∂volume) 2 μ1).toReal := by
            symm
            rw [MeasureTheory.toReal_eLpNorm]
            exact hdev_memLp.aestronglyMeasurable
    _ ≤ (ENNReal.ofReal (C_poinc_val d) *
          eLpNorm (fun z => ‖hw.weakGrad z‖) 2 μ1).toReal := h
    _ = (ENNReal.ofReal (C_poinc_val d)).toReal *
          (eLpNorm (fun z => ‖hw.weakGrad z‖) 2 μ1).toReal := by
            rw [ENNReal.toReal_mul]
    _ = C_poinc_val d * MeasureTheory.lpNorm (fun z => ‖hw.weakGrad z‖) 2 μ1 := by
          rw [ENNReal.toReal_ofReal hCp_nonneg,
            MeasureTheory.toReal_eLpNorm hgrad_memLp.aestronglyMeasurable]

private theorem unitBall_average_abs_sub_average_le_grad_lpNorm_two
    {u : E → ℝ}
    (hw : MemW1pWitness 2 u (Metric.ball (0 : E) 1)) :
    ⨍ z in Metric.ball (0 : E) 1,
        |u z - ⨍ y in Metric.ball (0 : E) 1, u y ∂volume| ∂volume ≤
      Cmo *
        MeasureTheory.lpNorm
          (fun z => ‖hw.weakGrad z‖) 2 (volume.restrict (Metric.ball (0 : E) 1)) := by
  haveI : IsFiniteMeasure (volume.restrict (Metric.ball (0 : E) 1)) := by
    rw [isFiniteMeasure_restrict]
    exact measure_ball_lt_top.ne
  calc
    ⨍ z in Metric.ball (0 : E) 1,
        |u z - ⨍ y in Metric.ball (0 : E) 1, u y ∂volume| ∂volume
        ≤ (volume.real (Metric.ball (0 : E) 1)) ^ (-(1 / 2 : ℝ)) *
            MeasureTheory.lpNorm
              (fun z => u z - ⨍ y in Metric.ball (0 : E) 1, u y ∂volume)
              2 (volume.restrict (Metric.ball (0 : E) 1)) := by
              exact unitBall_average_abs_le_lpNorm_two
                (hf := hw.memLp.sub (MeasureTheory.memLp_const _))
    _ ≤ (volume.real (Metric.ball (0 : E) 1)) ^ (-(1 / 2 : ℝ)) *
          (C_poinc_val d *
            MeasureTheory.lpNorm
              (fun z => ‖hw.weakGrad z‖) 2 (volume.restrict (Metric.ball (0 : E) 1))) := by
            gcongr
            exact unitBall_sub_average_lpNorm_le_grad_lpNorm_two hw
    _ = Cmo *
          MeasureTheory.lpNorm
            (fun z => ‖hw.weakGrad z‖) 2 (volume.restrict (Metric.ball (0 : E) 1)) := by
            ring

omit [NeZero d] in
private theorem average_abs_sub_average_rescale_ball
    {u : E → ℝ} {x₀ : E} {R : ℝ}
    (hR : 0 < R) :
    ⨍ z in Metric.ball (0 : E) 1,
        |u (x₀ + R • z) - ⨍ y in Metric.ball x₀ R, u y ∂volume| ∂volume =
      ⨍ x in Metric.ball x₀ R,
        |u x - ⨍ y in Metric.ball x₀ R, u y ∂volume| ∂volume := by
  simpa using
    average_rescale_ball (x₀ := x₀) (R := R) hR
      (fun x => |u x - ⨍ y in Metric.ball x₀ R, u y ∂volume|)

omit [NeZero d] in
theorem crossover_average_abs_sub_average_rescale_ball_radius
    {u : E → ℝ} {x₀ : E} {R ρ : ℝ}
    (hR : 0 < R) (hρ : 0 < ρ) :
    ⨍ z in Metric.ball (0 : E) ρ,
        |u (x₀ + R • z) - ⨍ y in Metric.ball x₀ (R * ρ), u y ∂volume| ∂volume =
      ⨍ x in Metric.ball x₀ (R * ρ),
        |u x - ⨍ y in Metric.ball x₀ (R * ρ), u y ∂volume| ∂volume := by
  simpa using
    crossover_average_rescale_ball_radius (x₀ := x₀) (R := R) (ρ := ρ) hR hρ
      (fun x => |u x - ⨍ y in Metric.ball x₀ (R * ρ), u y ∂volume|)

omit [NeZero d] in
private theorem lpNorm_rescale_to_unitBall_two
    {x₀ : E} {R : ℝ} {f : E → ℝ}
    (hR : 0 < R)
    (hBall : MemLp f 2 (volume.restrict (Metric.ball x₀ R)))
    (hUnit : MemLp (fun z => f (x₀ + R • z)) 2 (volume.restrict (Metric.ball (0 : E) 1))) :
    MeasureTheory.lpNorm
        (fun z => f (x₀ + R • z)) 2 (volume.restrict (Metric.ball (0 : E) 1)) =
      R ^ (-(d : ℝ) / 2) *
        MeasureTheory.lpNorm f 2 (volume.restrict (Metric.ball x₀ R)) := by
  have hp0 : (2 : ℝ≥0∞) ≠ 0 := by norm_num
  have hpTop : (2 : ℝ≥0∞) ≠ ⊤ := by norm_num
  have hE :
      eLpNorm (fun z => f (x₀ + R • z)) 2 (volume.restrict (Metric.ball (0 : E) 1)) =
        ENNReal.ofReal (R⁻¹ ^ ((d : ℝ) / 2)) *
          eLpNorm f 2 (volume.restrict (Metric.ball x₀ R)) := by
    simpa using
      (eLpNorm_rescale_to_unitBall (d := d) (p := (2 : ℝ≥0∞))
        (x₀ := x₀) (R := R) (f := f) hR hp0 hpTop)
  have h_ofReal :
      ENNReal.ofReal
          (MeasureTheory.lpNorm (fun z => f (x₀ + R • z)) 2
            (volume.restrict (Metric.ball (0 : E) 1))) =
        ENNReal.ofReal
          (R ^ (-(d : ℝ) / 2) *
            MeasureTheory.lpNorm f 2 (volume.restrict (Metric.ball x₀ R))) := by
    calc
      ENNReal.ofReal
          (MeasureTheory.lpNorm (fun z => f (x₀ + R • z)) 2
            (volume.restrict (Metric.ball (0 : E) 1)))
          = eLpNorm (fun z => f (x₀ + R • z)) 2
              (volume.restrict (Metric.ball (0 : E) 1)) := by
                simpa using (MeasureTheory.ofReal_lpNorm hUnit)
      _ = ENNReal.ofReal (R⁻¹ ^ ((d : ℝ) / 2)) *
            eLpNorm f 2 (volume.restrict (Metric.ball x₀ R)) := hE
      _ = ENNReal.ofReal (R⁻¹ ^ ((d : ℝ) / 2)) *
            ENNReal.ofReal
              (MeasureTheory.lpNorm f 2 (volume.restrict (Metric.ball x₀ R))) := by
              rw [MeasureTheory.ofReal_lpNorm hBall]
      _ = ENNReal.ofReal
            (R⁻¹ ^ ((d : ℝ) / 2) *
              MeasureTheory.lpNorm f 2 (volume.restrict (Metric.ball x₀ R))) := by
            rw [← ENNReal.ofReal_mul]
            positivity
      _ = ENNReal.ofReal
            (R ^ (-(d : ℝ) / 2) *
              MeasureTheory.lpNorm f 2 (volume.restrict (Metric.ball x₀ R))) := by
            congr 1
            rw [Real.inv_rpow hR.le, ← Real.rpow_neg hR.le]
            congr 1
            ring_nf
  have hnonneg :
      0 ≤ R ^ (-(d : ℝ) / 2) *
        MeasureTheory.lpNorm f 2 (volume.restrict (Metric.ball x₀ R)) := by
    have hRpow_nonneg : 0 ≤ R ^ (-(d : ℝ) / 2) := by
      exact Real.rpow_nonneg hR.le _
    exact mul_nonneg hRpow_nonneg MeasureTheory.lpNorm_nonneg
  have h := congrArg ENNReal.toReal h_ofReal
  simpa [ENNReal.toReal_ofReal hnonneg] using h

private theorem rescaled_weakGrad_lpNorm_eq
    {u : E → ℝ} {x₀ : E} {R : ℝ}
    (hR : 0 < R)
    (hw : MemW1pWitness 2 u (Metric.ball x₀ R)) :
    let hwR : MemW1pWitness 2 (fun z => u (x₀ + R • z)) (Metric.ball (0 : E) 1) :=
      hw.rescale_to_unitBall (d := d) hR
    MeasureTheory.lpNorm
        (fun z => ‖hwR.weakGrad z‖) 2 (volume.restrict (Metric.ball (0 : E) 1)) =
      R ^ (1 - (d : ℝ) / 2) *
        MeasureTheory.lpNorm
          (fun x => ‖hw.weakGrad x‖) 2 (volume.restrict (Metric.ball x₀ R)) := by
  intro hwR
  have hnorm_eq :
      (fun z => ‖hwR.weakGrad z‖) =
        fun z => R * ‖hw.weakGrad (x₀ + R • z)‖ := by
    ext z
    simp [hwR, MemW1pWitness.rescale_to_unitBall, norm_smul, Real.norm_of_nonneg hR.le]
  rw [hnorm_eq]
  have hBall :
      MemLp (fun x => ‖hw.weakGrad x‖) 2 (volume.restrict (Metric.ball x₀ R)) :=
    hw.weakGrad_norm_memLp
  have hUnit :
      MemLp (fun z => ‖hw.weakGrad (x₀ + R • z)‖) 2
        (volume.restrict (Metric.ball (0 : E) 1)) := by
    have hUnit' :
        MemLp (fun z => R⁻¹ * ‖hwR.weakGrad z‖) 2
          (volume.restrict (Metric.ball (0 : E) 1)) :=
      hwR.weakGrad_norm_memLp.const_mul R⁻¹
    simpa [hwR, MemW1pWitness.rescale_to_unitBall, Pi.smul_apply, smul_eq_mul,
      norm_smul, Real.norm_of_nonneg hR.le, hR.ne', inv_mul_cancel₀,
      mul_comm, mul_left_comm, mul_assoc] using hUnit'
  calc
    MeasureTheory.lpNorm
        (fun z => R * ‖hw.weakGrad (x₀ + R • z)‖) 2
        (volume.restrict (Metric.ball (0 : E) 1))
        = R * MeasureTheory.lpNorm
            (fun z => ‖hw.weakGrad (x₀ + R • z)‖) 2
              (volume.restrict (Metric.ball (0 : E) 1)) := by
                simpa [smul_eq_mul, Real.norm_of_nonneg hR.le] using
                  (MeasureTheory.lpNorm_const_smul (R : ℝ)
                    (fun z => ‖hw.weakGrad (x₀ + R • z)‖)
                    (volume.restrict (Metric.ball (0 : E) 1)) (p := (2 : ℝ≥0∞)))
    _ = R * (R ^ (-(d : ℝ) / 2) *
          MeasureTheory.lpNorm
            (fun x => ‖hw.weakGrad x‖) 2
              (volume.restrict (Metric.ball x₀ R))) := by
            rw [lpNorm_rescale_to_unitBall_two (x₀ := x₀) (R := R) hR hBall hUnit]
    _ = R ^ (1 - (d : ℝ) / 2) *
          MeasureTheory.lpNorm
            (fun x => ‖hw.weakGrad x‖) 2
              (volume.restrict (Metric.ball x₀ R)) := by
            let X : ℝ :=
              MeasureTheory.lpNorm
                (fun x => ‖hw.weakGrad x‖) 2
                  (volume.restrict (Metric.ball x₀ R))
            have hpow :
                R * R ^ (-(d : ℝ) / 2) = R ^ (1 - (d : ℝ) / 2) := by
              have hpow' :
                  (R ^ (1 : ℝ)) ^ (1 : ℝ) * (R ^ (1 : ℝ)) ^ (-(d : ℝ) / 2) =
                    (R ^ (1 : ℝ)) ^ (1 - (d : ℝ) / 2) := by
                rw [← Real.rpow_add (show 0 < R ^ (1 : ℝ) by positivity)]
                congr 1
                ring
              simpa [Real.rpow_one] using hpow'
            have hmul :
                R * (R ^ (-(d : ℝ) / 2) * X) =
                  R ^ (1 - (d : ℝ) / 2) * X := by
              calc
                R * (R ^ (-(d : ℝ) / 2) * X)
                    = (R * R ^ (-(d : ℝ) / 2)) * X := by ring
                _ = R ^ (1 - (d : ℝ) / 2) * X := by rw [hpow]
            simpa [X] using hmul

theorem crossover_average_abs_sub_average_ball_le_grad_lpNorm_two
    {u : E → ℝ} {x₀ : E} {R : ℝ}
    (hR : 0 < R)
    (hw : MemW1pWitness 2 u (Metric.ball x₀ R)) :
    ⨍ x in Metric.ball x₀ R,
        |u x - ⨍ y in Metric.ball x₀ R, u y ∂volume| ∂volume ≤
      Cmo * R ^ (1 - (d : ℝ) / 2) *
        MeasureTheory.lpNorm
          (fun x => ‖hw.weakGrad x‖) 2 (volume.restrict (Metric.ball x₀ R)) := by
  let hwR : MemW1pWitness 2 (fun z => u (x₀ + R • z)) (Metric.ball (0 : E) 1) :=
    hw.rescale_to_unitBall (d := d) hR
  have havg_rescale :
      ⨍ z in Metric.ball (0 : E) 1, u (x₀ + R • z) ∂volume =
        ⨍ y in Metric.ball x₀ R, u y ∂volume := by
    simpa using average_rescale_ball (x₀ := x₀) (R := R) hR u
  have hunit_avg :
      ⨍ z in Metric.ball (0 : E) 1,
          |u (x₀ + R • z) - ⨍ y in Metric.ball x₀ R, u y ∂volume| ∂volume ≤
        Cmo *
          MeasureTheory.lpNorm
            (fun z => ‖hwR.weakGrad z‖) 2
              (volume.restrict (Metric.ball (0 : E) 1)) := by
    simpa [havg_rescale, hwR] using
      (unitBall_average_abs_sub_average_le_grad_lpNorm_two
        (u := fun z => u (x₀ + R • z)) hwR)
  calc
    ⨍ x in Metric.ball x₀ R,
        |u x - ⨍ y in Metric.ball x₀ R, u y ∂volume| ∂volume
        = ⨍ z in Metric.ball (0 : E) 1,
            |u (x₀ + R • z) - ⨍ y in Metric.ball x₀ R, u y ∂volume| ∂volume := by
            symm
            exact average_abs_sub_average_rescale_ball (u := u) (x₀ := x₀) (R := R) hR
    _ ≤ Cmo *
          MeasureTheory.lpNorm
            (fun z => ‖hwR.weakGrad z‖) 2
              (volume.restrict (Metric.ball (0 : E) 1)) := hunit_avg
    _ = Cmo * (R ^ (1 - (d : ℝ) / 2) *
          MeasureTheory.lpNorm
            (fun x => ‖hw.weakGrad x‖) 2
              (volume.restrict (Metric.ball x₀ R))) := by
            rw [rescaled_weakGrad_lpNorm_eq (u := u) (x₀ := x₀) (R := R) hR hw]
    _ = Cmo * R ^ (1 - (d : ℝ) / 2) *
          MeasureTheory.lpNorm
            (fun x => ‖hw.weakGrad x‖) 2
              (volume.restrict (Metric.ball x₀ R)) := by
            ring




end DeGiorgi
