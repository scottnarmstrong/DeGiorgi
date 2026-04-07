import Mathlib.Topology.Algebra.Order.LiminfLimsup
import DeGiorgi.MoserIteration
import DeGiorgi.Support.MeasureBounds

/-!
# Chapter 06: Supersolution Estimates

This module develops the Moser iteration estimates for positive
supersolutions.

## Proof structure

The proof has three steps:

1. **Test function computation**: test the supersolution
   inequality with `φ² u^{-(1+p)}` to get the one-step Sobolev gain estimates
   for inverse powers (`p > 0`) and forward low powers (`p ∈ (0,1)`).

2. **Inverse-power iteration**: iterate the inverse-power
   one-step bound along the geometric exponent sequence `pₙ = p₀ χⁿ` to get
   the `L^∞` bound on `u⁻¹`.

3. **Forward low-power iteration**: iterate the forward low-power
   one-step bound along `pₙ = q χ^{n-m}` (a finite iteration) to get
   the forward stage estimate.

## Main results

- `weak_harnack_stage_one_inverse`: estimate `e.weakHarnack1`
- `weak_harnack_stage_one_forward`: estimate `e.weakHarnack2`

-/

noncomputable section

open MeasureTheory Metric

namespace DeGiorgi

variable {d : ℕ} [NeZero d]

local notation "E" => AmbientSpace d
local notation "μhalf" => (volume.restrict (Metric.ball (0 : E) (1 / 2 : ℝ)))

/-- The weakened forward-stage constant that honestly absorbs the finite-measure
`L^p` to `L^{p₀}` upgrade on the unit ball. -/
noncomputable def C_weakHarnack0Forward
    (d : ℕ) [NeZero d] (_hd : 2 < (d : ℝ)) : ℝ :=
  (C_weakHarnack0 d * (volume.real (Metric.ball (0 : AmbientSpace d) 1) + 1)) ^
    (moserChi d)

theorem one_le_C_weakHarnack0Forward
    (hd : 2 < (d : ℝ)) :
    1 ≤ C_weakHarnack0Forward (d := d) hd := by
  unfold C_weakHarnack0Forward
  have hbase : 1 ≤
      C_weakHarnack0 d * (volume.real (Metric.ball (0 : E) 1) + 1) := by
    have hC : 1 ≤ C_weakHarnack0 d := one_le_C_weakHarnack0 (d := d)
    have hV : 1 ≤ volume.real (Metric.ball (0 : E) 1) + 1 := by
      have hV_nonneg : 0 ≤ volume.real (Metric.ball (0 : E) 1) := by
        exact measureReal_nonneg
      linarith
    calc
      (1 : ℝ) = 1 * 1 := by ring
      _ ≤ C_weakHarnack0 d * (volume.real (Metric.ball (0 : E) 1) + 1) := by
          exact mul_le_mul hC hV (by positivity) (by positivity)
  exact Real.one_le_rpow hbase (moserChi_pos (d := d) hd).le


-- Moser sequence lemmas (moserChi_pos, moserRadius_pos, moserExponentSeq_pos,
-- etc.) are imported from `MoserIteration` and used directly below.

/-! ### One-Step Sobolev Gain for Supersolutions

These are the analogues of `moser_preMoser` from the subsolution theory.
The key difference: the test function is `φ² u^{-(1+p)}` instead of
`φ² u^{p-1}`, and the Caccioppoli inequality produces
`∫ |∇(φ u^{-p/2})|² ≤ C(Λp²/(1+p)² + 1) ∫ |∇φ|² u^{-p}`
for the weighted cutoff.

The proof is decomposed into three sub-results:
1. `superPowerCutoff_energy_bound`: W^{1,2} witness + energy bound for
   `η · u^{-p/2}` (the Caccioppoli inequality)
2. `supersolution_preMoser_inverse`: wire up energy bound + Sobolev → Lp gain
3. `supersolution_preMoser_forward`: the `p ∈ (0,1)` variant
-/

/-- Inverse-power cutoff used in the supersolution pre-estimate: `η · u^{-p/2}`.
This is the supersolution analogue of `moserPowerCutoff` (which uses `u₊^{p/2}`). -/
noncomputable def superPowerCutoff
    (η u : E → ℝ) (p : ℝ) : E → ℝ :=
  fun x => η x * |(u x)⁻¹| ^ (p / 2)

omit [NeZero d] in
theorem superPowerCutoff_tsupport_subset
    {u η : E → ℝ} {p s : ℝ}
    (hη_sub_ball : tsupport η ⊆ Metric.ball (0 : E) s) :
    tsupport (superPowerCutoff (d := d) η u p) ⊆ Metric.ball (0 : E) s :=
  (tsupport_mul_subset_left
    (f := η) (g := fun x => |(u x)⁻¹| ^ (p / 2))).trans hη_sub_ball

noncomputable def superFderivVec
    (η : E → ℝ) (x : E) : E :=
  (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ η x)

omit [NeZero d] in
lemma superFderivVec_apply
    {η : E → ℝ} {x : E} (i : Fin d) :
    superFderivVec η x i = (fderiv ℝ η x) (EuclideanSpace.single i 1) := by
  calc
    superFderivVec η x i = inner ℝ (superFderivVec η x) (EuclideanSpace.single i (1 : ℝ)) := by
      simpa using
        (EuclideanSpace.inner_single_right (i := i) (a := (1 : ℝ)) (superFderivVec η x)).symm
    _ = ((InnerProductSpace.toDual ℝ E) (superFderivVec η x)) (EuclideanSpace.single i (1 : ℝ)) := by
      rw [InnerProductSpace.toDual_apply_apply]
    _ = (fderiv ℝ η x) (EuclideanSpace.single i 1) := by
      simp [superFderivVec]

omit [NeZero d] in
lemma super_norm_fderivVec_eq_norm_fderiv
    {η : E → ℝ} {x : E} :
    ‖superFderivVec η x‖ = ‖fderiv ℝ η x‖ := by
  dsimp [superFderivVec]
  exact ((InnerProductSpace.toDual ℝ E).symm.norm_map (fderiv ℝ η x))

theorem super_fderiv_norm_zero_outside_tsupport
    {f : E → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    {x : E} (hx : x ∉ tsupport f) :
    ‖fderiv ℝ f x‖ = 0 := by
  have hvec_zero : superFderivVec f x = 0 := by
    ext i
    rw [superFderivVec_apply]
    exact fderiv_apply_zero_outside_of_tsupport_subset
      (Ω := tsupport f) (hf := hf) (hsub := subset_rfl) hx i
  rw [← super_norm_fderivVec_eq_norm_fderiv (η := f) (x := x), hvec_zero, norm_zero]

theorem super_aestronglyMeasurable_matMulE
    {Ω : Set E}
    (A : EllipticCoeff d Ω)
    {G : E → E}
    (hG : AEStronglyMeasurable G (volume.restrict Ω)) :
    AEStronglyMeasurable (fun x => matMulE (A.a x) (G x)) (volume.restrict Ω) := by
  have hG_ofLp_cont : Continuous (fun y : E => (WithLp.ofLp y : Fin d → ℝ)) := by
    simpa using (PiLp.continuous_ofLp 2 (fun _ : Fin d => ℝ))
  have hG_ofLp :
      AEStronglyMeasurable (fun x => (G x).ofLp) (volume.restrict Ω) :=
    hG_ofLp_cont.comp_aestronglyMeasurable hG
  have hmulVec :
      AEMeasurable (fun x => Matrix.mulVec (A.a x) (G x).ofLp) (volume.restrict Ω) := by
    refine aemeasurable_pi_lambda _ ?_
    intro i
    have hmeas_sum :
        AEMeasurable
          (∑ j : Fin d, fun x => A.a x i j * (G x).ofLp j)
          (volume.restrict Ω) := by
      refine Finset.aemeasurable_sum (s := (Finset.univ : Finset (Fin d)))
        (f := fun j x => A.a x i j * (G x).ofLp j) ?_
      intro j _
      have hGj : AEMeasurable (fun x => (G x).ofLp j) (volume.restrict Ω) := by
        simpa using
          (Continuous.comp_aestronglyMeasurable (continuous_apply j) hG_ofLp).aemeasurable
      exact (A.measurable_apply i j).aemeasurable.mul hGj
    convert hmeas_sum using 1
    ext x
    simp [Matrix.mulVec, dotProduct]
  exact (PiLp.continuous_toLp 2 (fun _ : Fin d => ℝ)).comp_aestronglyMeasurable
    hmulVec.aestronglyMeasurable

omit [NeZero d] in
theorem super_tendsto_eLpNorm_zero_of_dominated
    {μ : Measure E}
    {F : ℕ → E → ℝ} {H : E → ℝ}
    (hH_memLp : MemLp H 2 μ)
    (hF_meas : ∀ n, AEStronglyMeasurable (F n) μ)
    (hdom : ∀ n, ∀ᵐ x ∂μ, |F n x| ≤ H x)
    (hF_ae : ∀ᵐ x ∂μ, Filter.Tendsto (fun n => F n x) Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n => eLpNorm (F n) 2 μ) Filter.atTop (nhds 0) := by
  have huiH : UnifIntegrable (fun _ : ℕ => H) 2 μ := by
    simpa using
      (MeasureTheory.unifIntegrable_const (p := (2 : ENNReal))
        (by norm_num) (by simp) hH_memLp)
  have huiF : UnifIntegrable F 2 μ := by
    intro ε hε
    obtain ⟨δ, hδ, hδ'⟩ := huiH hε
    refine ⟨δ, hδ, fun n s hs hμs => ?_⟩
    calc
      eLpNorm (s.indicator (F n)) 2 μ ≤ eLpNorm (s.indicator H) 2 μ := by
        refine eLpNorm_mono_ae_real ?_
        filter_upwards [hdom n] with x hx
        by_cases hxs : x ∈ s
        · simpa [Set.indicator_of_mem, hxs] using hx
        · simp [Set.indicator_of_notMem, hxs]
      _ ≤ ENNReal.ofReal ε := hδ' 0 s hs hμs
  have hutH : UnifTight (fun _ : ℕ => H) 2 μ := by
    exact MeasureTheory.unifTight_const (p := (2 : ENNReal)) (by simp) hH_memLp
  have hutF : UnifTight F 2 μ := by
    intro ε hε
    obtain ⟨s, hμs, hs'⟩ := hutH hε
    refine ⟨s, hμs, fun n => ?_⟩
    calc
      eLpNorm (sᶜ.indicator (F n)) 2 μ ≤ eLpNorm (sᶜ.indicator H) 2 μ := by
        refine eLpNorm_mono_ae_real ?_
        filter_upwards [hdom n] with x hx
        by_cases hxs : x ∈ sᶜ
        · simpa [Set.indicator_of_mem, hxs] using hx
        · simp [Set.indicator_of_notMem, hxs]
      _ ≤ ε := hs' 0
  have hLpF0 :
      Filter.Tendsto (fun n => eLpNorm (F n - fun _ => (0 : ℝ)) 2 μ)
        Filter.atTop (nhds 0) := by
    exact
      MeasureTheory.tendsto_Lp_of_tendsto_ae
        (μ := μ) (p := (2 : ENNReal)) (hp := by norm_num) (hp' := by simp)
        (haef := hF_meas) (hg' := MeasureTheory.MemLp.zero' (p := (2 : ENNReal)) (μ := μ))
        huiF hutF hF_ae
  exact hLpF0.congr' (Filter.Eventually.of_forall fun n => by
    congr 1
    funext x
    simp)

theorem weighted_pointwise_core
    {Λ η ζ ψ ψd Q M : ℝ}
    (hΛ : 0 < Λ) (hψd : 0 < ψd)
    (hcoeff : |M| ^ 2 ≤ Λ * Q) :
    2 * η * |ψ| * ζ * |M| ≤
      (1 / 2 : ℝ) * η ^ 2 * ψd * Q + 2 * Λ * ζ ^ 2 * (|ψ| ^ 2 / ψd) := by
  let a : ℝ := η * |M| * Real.sqrt ψd / Real.sqrt (2 * Λ)
  let b : ℝ := Real.sqrt (2 * Λ) * ζ * |ψ| / Real.sqrt ψd
  have hyoung : 2 * a * b ≤ a ^ 2 + b ^ 2 := by
    nlinarith [sq_nonneg (a - b)]
  have hsqrtΛ_pos : 0 < Real.sqrt (2 * Λ) := by
    apply Real.sqrt_pos.2
    positivity
  have hsqrtΛ_ne : Real.sqrt (2 * Λ) ≠ 0 := hsqrtΛ_pos.ne'
  have hsqrtψd_pos : 0 < Real.sqrt ψd := Real.sqrt_pos.2 hψd
  have hsqrtψd_ne : Real.sqrt ψd ≠ 0 := hsqrtψd_pos.ne'
  have hsqrtΛ_sq : (Real.sqrt (2 * Λ)) ^ 2 = 2 * Λ := by
    rw [Real.sq_sqrt]
    positivity
  have hsqrtψd_sq : (Real.sqrt ψd) ^ 2 = ψd := by
    rw [Real.sq_sqrt hψd.le]
  have ha_sq :
      a ^ 2 = η ^ 2 * |M| ^ 2 * ψd / (2 * Λ) := by
    dsimp [a]
    rw [div_pow, mul_pow, mul_pow, hsqrtψd_sq, hsqrtΛ_sq]
  have hb_sq :
      b ^ 2 = 2 * Λ * ζ ^ 2 * (|ψ| ^ 2 / ψd) := by
    dsimp [b]
    rw [div_pow, mul_pow, mul_pow, hsqrtΛ_sq, hsqrtψd_sq]
    ring
  have hcoeff' :
      η ^ 2 * |M| ^ 2 * ψd / (2 * Λ) ≤ (1 / 2 : ℝ) * η ^ 2 * ψd * Q := by
    have hmul :
        (η ^ 2 * ψd / (2 * Λ)) * (|M| ^ 2) ≤
          (η ^ 2 * ψd / (2 * Λ)) * (Λ * Q) := by
      refine mul_le_mul_of_nonneg_left hcoeff ?_
      positivity
    have hfac :
        (η ^ 2 * ψd / (2 * Λ)) * (Λ * Q) =
          (1 / 2 : ℝ) * η ^ 2 * ψd * Q := by
      field_simp [hΛ.ne']
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hmul.trans_eq hfac
  have hmain :
      2 * η * |ψ| * ζ * |M| ≤
        η ^ 2 * |M| ^ 2 * ψd / (2 * Λ) + 2 * Λ * ζ ^ 2 * (|ψ| ^ 2 / ψd) := by
    have hconv : 2 * a * b = 2 * η * |ψ| * ζ * |M| := by
      dsimp [a, b]
      field_simp [hsqrtΛ_ne, hsqrtψd_ne]
    rwa [hconv, ha_sq, hb_sq] at hyoung
  have hsum :
      η ^ 2 * |M| ^ 2 * ψd / (2 * Λ) + 2 * Λ * ζ ^ 2 * (|ψ| ^ 2 / ψd) ≤
        (1 / 2 : ℝ) * η ^ 2 * ψd * Q + 2 * Λ * ζ ^ 2 * (|ψ| ^ 2 / ψd) := by
    nlinarith [hcoeff']
  exact hmain.trans hsum

theorem weighted_absorb
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {Quad M η ζ ψ ψd : α → ℝ} {Λ : ℝ}
    (hΛ : 0 < Λ)
    (hcore :
      ∫ x, η x ^ 2 * ψd x * Quad x ∂μ ≤
        ∫ x, 2 * |η x| * |ψ x| * ζ x * |M x| ∂μ)
    (hcoeff : ∀ᵐ x ∂μ, |M x| ^ 2 ≤ Λ * Quad x)
    (hψd_pos : ∀ᵐ x ∂μ, 0 < ψd x)
    (hleft_int : Integrable (fun x => η x ^ 2 * ψd x * Quad x) μ)
    (hcross_int : Integrable (fun x => 2 * |η x| * |ψ x| * ζ x * |M x|) μ)
    (hbound_int : Integrable (fun x => ζ x ^ 2 * (|ψ x| ^ 2 / ψd x)) μ) :
    ∫ x, η x ^ 2 * ψd x * Quad x ∂μ ≤
      4 * Λ * ∫ x, ζ x ^ 2 * (|ψ x| ^ 2 / ψd x) ∂μ := by
  have hupper_pt :
      ∀ᵐ x ∂μ,
        2 * |η x| * |ψ x| * ζ x * |M x| ≤
          (1 / 2 : ℝ) * η x ^ 2 * ψd x * Quad x +
            2 * Λ * ζ x ^ 2 * (|ψ x| ^ 2 / ψd x) := by
    filter_upwards [hcoeff, hψd_pos] with x hx hψx
    simpa using weighted_pointwise_core (η := |η x|) hΛ hψx hx
  have hupper_int :
      Integrable
        (fun x =>
          (1 / 2 : ℝ) * η x ^ 2 * ψd x * Quad x +
            2 * Λ * ζ x ^ 2 * (|ψ x| ^ 2 / ψd x)) μ := by
    simpa [mul_assoc, add_comm, add_left_comm, add_assoc] using
      (hleft_int.const_mul (1 / 2 : ℝ)).add (hbound_int.const_mul (2 * Λ))
  have hcross_bound :
      ∫ x, 2 * |η x| * |ψ x| * ζ x * |M x| ∂μ ≤
        ∫ x, (1 / 2 : ℝ) * η x ^ 2 * ψd x * Quad x +
          2 * Λ * ζ x ^ 2 * (|ψ x| ^ 2 / ψd x) ∂μ := by
    exact integral_mono_ae hcross_int hupper_int hupper_pt
  have hsplit :
      ∫ x, (1 / 2 : ℝ) * η x ^ 2 * ψd x * Quad x +
          2 * Λ * ζ x ^ 2 * (|ψ x| ^ 2 / ψd x) ∂μ =
        (1 / 2 : ℝ) * ∫ x, η x ^ 2 * ψd x * Quad x ∂μ +
          2 * Λ * ∫ x, ζ x ^ 2 * (|ψ x| ^ 2 / ψd x) ∂μ := by
    have hrewrite :
        (fun x =>
          (1 / 2 : ℝ) * η x ^ 2 * ψd x * Quad x +
            2 * Λ * ζ x ^ 2 * (|ψ x| ^ 2 / ψd x)) =
          (fun x =>
            ((1 / 2 : ℝ) * (η x ^ 2 * ψd x * Quad x)) +
              ((2 * Λ) * (ζ x ^ 2 * (|ψ x| ^ 2 / ψd x)))) := by
      funext x
      ring
    rw [hrewrite,
      integral_add (hleft_int.const_mul (1 / 2 : ℝ)) (hbound_int.const_mul (2 * Λ))]
    rw [integral_const_mul, integral_const_mul]
  have hmain :
      ∫ x, η x ^ 2 * ψd x * Quad x ∂μ ≤
        (1 / 2 : ℝ) * ∫ x, η x ^ 2 * ψd x * Quad x ∂μ +
          2 * Λ * ∫ x, ζ x ^ 2 * (|ψ x| ^ 2 / ψd x) ∂μ := by
    calc
      ∫ x, η x ^ 2 * ψd x * Quad x ∂μ
          ≤ ∫ x, 2 * |η x| * |ψ x| * ζ x * |M x| ∂μ := hcore
      _ ≤ ∫ x, (1 / 2 : ℝ) * η x ^ 2 * ψd x * Quad x +
            2 * Λ * ζ x ^ 2 * (|ψ x| ^ 2 / ψd x) ∂μ := hcross_bound
      _ = (1 / 2 : ℝ) * ∫ x, η x ^ 2 * ψd x * Quad x ∂μ +
            2 * Λ * ∫ x, ζ x ^ 2 * (|ψ x| ^ 2 / ψd x) ∂μ := hsplit
  linarith

-- **Caccioppoli-Sobolev energy bound for `η · u^{-p/2}`** (supersolutions).
--
-- This is the core PDE sub-lemma: if `u > 0` is a supersolution, `η` is a smooth
-- cutoff with `|η| ≤ 1` and `‖∇η‖ ≤ Cη`, then the function `v = η · u^{-p/2}`
-- lies in `W₀^{1,2}(Bₛ)` and satisfies
--   ∫_{Bₛ} |∇v|² ≤ 2 Cη² (Λp²/(1+p)² + 1) ∫_{Bₛ} u^{-p}
-- for the weighted cutoff.
--
-- Proof: regularize via `regInvPow ε p`, prove energy bound for each ε,
-- then send ε → 0.

/-- Regularized inverse power: `Φ_ε(t) = (max t 0 + ε)^{-p/2} - ε^{-p/2}`.

This is smooth on all of `ℝ` (since `t + ε > ε/2 > 0` for `t > -ε/2`),
vanishes at 0, and has bounded derivative. It approximates `t^{-p/2}` as `ε → 0`
for `t > 0`. -/
noncomputable def regInvPow (ε p : ℝ) : ℝ → ℝ :=
  fun t => (Real.sqrt (t ^ 2 + ε ^ 2)) ^ (-(p / 2)) - ε ^ (-(p / 2))

lemma regInvPow_zero {ε p : ℝ} (hε : 0 < ε) : regInvPow ε p 0 = 0 := by
  simp [regInvPow, Real.sqrt_sq (le_of_lt hε)]

lemma regInvPow_contDiff {ε p : ℝ} (hε : 0 < ε) :
    ContDiff ℝ (⊤ : ℕ∞) (regInvPow ε p) := by
  unfold regInvPow
  apply ContDiff.sub
  · apply ContDiff.rpow
    · exact (contDiff_id.pow 2 |>.add contDiff_const).sqrt (fun t => by positivity)
    · exact contDiff_const
    · intro t
      exact ne_of_gt (Real.sqrt_pos.mpr (by positivity))
  · exact contDiff_const

lemma regInvPow_deriv_bounded {ε p : ℝ} (hε : 0 < ε) (hp : 0 < p) :
    ∃ M : ℝ, ∀ t, |deriv (regInvPow ε p) t| ≤ M := by
  refine ⟨(p / 2) * ε ^ (-(p / 2) - 1), fun t => ?_⟩
  -- Compute HasDerivAt for f(t) = (√(t²+ε²))^{-(p/2)} - ε^{-(p/2)}
  have hpos : 0 < t ^ 2 + ε ^ 2 := by positivity
  have hsqrt_pos : 0 < Real.sqrt (t ^ 2 + ε ^ 2) := Real.sqrt_pos.mpr hpos
  have hsqrt_ne : Real.sqrt (t ^ 2 + ε ^ 2) ≠ 0 := ne_of_gt hsqrt_pos
  -- d/dt[t² + ε²] = 2t
  have hd_sum : HasDerivAt (fun t => t ^ 2 + ε ^ 2) (2 * t) t := by
    convert (hasDerivAt_pow 2 t).add (hasDerivAt_const t (ε ^ 2)) using 1; ring
  -- d/dt[√(t²+ε²)] = t/√(t²+ε²)
  have hd_sqrt : HasDerivAt (fun t => Real.sqrt (t ^ 2 + ε ^ 2))
      (t / Real.sqrt (t ^ 2 + ε ^ 2)) t := by
    have := hd_sum.sqrt (ne_of_gt hpos)
    convert this using 1; field_simp
  -- d/dt[(√(t²+ε²))^α] = α · (√(t²+ε²))^{α-1} · t/√(t²+ε²)
  let α : ℝ := -(p / 2)
  have hd_rpow : HasDerivAt (fun t => (Real.sqrt (t ^ 2 + ε ^ 2)) ^ α)
      (α * (Real.sqrt (t ^ 2 + ε ^ 2)) ^ (α - 1) *
        (t / Real.sqrt (t ^ 2 + ε ^ 2))) t := by
    have h := hd_sqrt.rpow_const (p := α) (Or.inl hsqrt_ne)
    convert h using 1; ring
  -- d/dt[regInvPow ε p t] = α · (√(t²+ε²))^{α-1} · t/√(t²+ε²)
  have hd_f : HasDerivAt (regInvPow ε p)
      (α * (Real.sqrt (t ^ 2 + ε ^ 2)) ^ (α - 1) *
        (t / Real.sqrt (t ^ 2 + ε ^ 2))) t := by
    have := hd_rpow.sub (hasDerivAt_const t (ε ^ α))
    simp only [sub_zero] at this
    exact this
  rw [hd_f.deriv]
  -- Now bound: |α · (√(t²+ε²))^{α-1} · t/√(t²+ε²)|
  -- = (p/2) · |t/√(t²+ε²)| · (√(t²+ε²))^{-(p/2)-1}
  -- ≤ (p/2) · 1 · ε^{-(p/2)-1}
  have habs_ratio : |t / Real.sqrt (t ^ 2 + ε ^ 2)| ≤ 1 := by
    rw [abs_div, abs_of_nonneg hsqrt_pos.le]
    exact (div_le_one hsqrt_pos).mpr (Real.abs_le_sqrt (by linarith [sq_nonneg ε]))
  have hsqrt_ge_eps : ε ≤ Real.sqrt (t ^ 2 + ε ^ 2) := by
    calc ε = Real.sqrt (ε ^ 2) := (Real.sqrt_sq hε.le).symm
      _ ≤ Real.sqrt (t ^ 2 + ε ^ 2) := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg t])
  have hrpow_bound : (Real.sqrt (t ^ 2 + ε ^ 2)) ^ (α - 1) ≤ ε ^ (α - 1) := by
    exact Real.rpow_le_rpow_of_nonpos hε hsqrt_ge_eps (by dsimp [α]; linarith)
  -- |α| = p/2
  have hα_abs : |α| = p / 2 := by dsimp [α]; rw [abs_neg]; exact abs_of_pos (by linarith)
  calc |α * (Real.sqrt (t ^ 2 + ε ^ 2)) ^ (α - 1) *
          (t / Real.sqrt (t ^ 2 + ε ^ 2))|
      = |α| * |(Real.sqrt (t ^ 2 + ε ^ 2)) ^ (α - 1)| *
          |t / Real.sqrt (t ^ 2 + ε ^ 2)| := by
        rw [abs_mul, abs_mul]
    _ ≤ (p / 2) * (Real.sqrt (t ^ 2 + ε ^ 2)) ^ (α - 1) *  1 := by
        rw [hα_abs, abs_of_nonneg (Real.rpow_nonneg hsqrt_pos.le _)]
        exact mul_le_mul_of_nonneg_left habs_ratio
          (mul_nonneg (by linarith) (Real.rpow_nonneg hsqrt_pos.le _))
    _ = (p / 2) * (Real.sqrt (t ^ 2 + ε ^ 2)) ^ (α - 1) := by ring
    _ ≤ (p / 2) * ε ^ (α - 1) := by
        exact mul_le_mul_of_nonneg_left hrpow_bound (by linarith)
    _ = (p / 2) * ε ^ (-(p / 2) - 1) := by dsimp [α]

/-- Smooth left transition used to extend shifted powers below `0` while
keeping them exact on `[0, ∞)`. -/
noncomputable def superExactLeftTransition (ε : ℝ) : ℝ → ℝ :=
  fun t => Real.smoothTransition (1 + (2 / ε) * t)

/-- Smooth input which agrees with the identity on `[0, ∞)` and is constant
`0` below `-ε/2`. -/
noncomputable def superExactInput (ε : ℝ) : ℝ → ℝ :=
  fun t => t * superExactLeftTransition ε t

theorem superExactLeftTransition_eq_one_of_nonneg
    {ε t : ℝ} (hε : 0 < ε) (ht : 0 ≤ t) :
    superExactLeftTransition ε t = 1 := by
  apply Real.smoothTransition.one_of_one_le
  dsimp [superExactLeftTransition]
  have : 0 ≤ (2 / ε) * t := by positivity
  linarith

theorem superExactInput_eq_self_of_nonneg
    {ε t : ℝ} (hε : 0 < ε) (ht : 0 ≤ t) :
    superExactInput ε t = t := by
  rw [superExactInput, superExactLeftTransition_eq_one_of_nonneg hε ht]
  ring

theorem superExactInput_eq_zero_of_le_neg_half
    {ε t : ℝ} (hε : 0 < ε) (ht : t ≤ -ε / 2) :
    superExactInput ε t = 0 := by
  have hσ : superExactLeftTransition ε t = 0 := by
    apply Real.smoothTransition.zero_of_nonpos
    dsimp [superExactLeftTransition]
    have hcoeff_nonneg : 0 ≤ 2 / ε := by positivity
    have hmul : (2 / ε) * t ≤ (2 / ε) * (-ε / 2) :=
      mul_le_mul_of_nonneg_left ht hcoeff_nonneg
    have hEq : (2 / ε) * (-ε / 2) = (-1 : ℝ) := by
      field_simp [hε.ne']
    linarith [hmul, hEq]
  simp [superExactInput, hσ]

theorem superExactInput_lower_bound
    {ε t : ℝ} (hε : 0 < ε) :
    -ε / 2 ≤ superExactInput ε t := by
  by_cases hlow : t ≤ -ε / 2
  · rw [superExactInput_eq_zero_of_le_neg_half hε hlow]
    linarith
  · have hlow' : -ε / 2 < t := lt_of_not_ge hlow
    by_cases hnonneg : 0 ≤ t
    · rw [superExactInput_eq_self_of_nonneg hε hnonneg]
      linarith
    · have ht_neg : t < 0 := lt_of_not_ge hnonneg
      have hσ_nonneg : 0 ≤ superExactLeftTransition ε t := Real.smoothTransition.nonneg _
      have hσ_le : superExactLeftTransition ε t ≤ 1 := Real.smoothTransition.le_one _
      have hmul : t ≤ t * superExactLeftTransition ε t := by
        have := mul_le_mul_of_nonpos_left hσ_le ht_neg.le
        simpa [one_mul] using this
      dsimp [superExactInput]
      linarith

theorem superExactLeftTransition_contDiff
    {ε : ℝ} (_hε : 0 < ε) :
    ContDiff ℝ (⊤ : ℕ∞) (superExactLeftTransition ε) := by
  have hlin : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ => (2 / ε) * t + 1) := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      ((contDiff_const : ContDiff ℝ (⊤ : ℕ∞) fun _ : ℝ => 2 / ε).mul contDiff_id).add
        contDiff_const
  simpa [superExactLeftTransition, add_comm, add_left_comm, add_assoc] using
    Real.smoothTransition.contDiff.comp hlin

theorem superExactInput_contDiff
    {ε : ℝ} (hε : 0 < ε) :
    ContDiff ℝ (⊤ : ℕ∞) (superExactInput ε) := by
  simpa [superExactInput] using
    (contDiff_id.mul (superExactLeftTransition_contDiff (ε := ε) hε))

theorem superExactBase_ne_zero
    {ε : ℝ} (hε : 0 < ε) :
    ∀ t : ℝ, ε + superExactInput ε t ≠ 0 := by
  intro t
  have hbase_lb : ε / 2 ≤ ε + superExactInput ε t := by
    have hinput_lb := superExactInput_lower_bound (ε := ε) hε (t := t)
    linarith
  have hbase_pos : 0 < ε + superExactInput ε t := by
    have : 0 < ε / 2 := by positivity
    exact lt_of_lt_of_le this hbase_lb
  exact hbase_pos.ne'

/-- Exact shifted power using `superExactInput`; this agrees with
`t ↦ (ε + t)^a` on `[0, ∞)`. -/
noncomputable def superExactShiftPow (ε a : ℝ) : ℝ → ℝ :=
  fun t => (ε + superExactInput ε t) ^ a

/-- Zero-vanishing exact shifted power profile. -/
noncomputable def superExactShiftReg (ε a : ℝ) : ℝ → ℝ :=
  fun t => superExactShiftPow ε a t - ε ^ a

theorem superExactShiftPow_contDiff
    {ε a : ℝ} (hε : 0 < ε) :
    ContDiff ℝ (⊤ : ℕ∞) (superExactShiftPow ε a) := by
  have hbase : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ => ε + superExactInput ε t) := by
    exact contDiff_const.add (superExactInput_contDiff (ε := ε) hε)
  simpa [superExactShiftPow] using
    hbase.rpow_const_of_ne (superExactBase_ne_zero (ε := ε) hε)

theorem superExactShiftReg_contDiff
    {ε a : ℝ} (hε : 0 < ε) :
    ContDiff ℝ (⊤ : ℕ∞) (superExactShiftReg ε a) := by
  simpa [superExactShiftReg] using
    (superExactShiftPow_contDiff (ε := ε) (a := a) hε).sub contDiff_const

theorem superExactShiftPow_eq_shifted_of_nonneg
    {ε a t : ℝ} (hε : 0 < ε) (ht : 0 ≤ t) :
    superExactShiftPow ε a t = (ε + t) ^ a := by
  rw [superExactShiftPow, superExactInput_eq_self_of_nonneg hε ht]

theorem superExactShiftReg_eq_shifted_of_nonneg
    {ε a t : ℝ} (hε : 0 < ε) (ht : 0 ≤ t) :
    superExactShiftReg ε a t = (ε + t) ^ a - ε ^ a := by
  rw [superExactShiftReg, superExactShiftPow_eq_shifted_of_nonneg hε ht]

theorem superExactShiftPow_eq_const_of_le_neg_half
    {ε a t : ℝ} (hε : 0 < ε) (ht : t ≤ -ε / 2) :
    superExactShiftPow ε a t = ε ^ a := by
  rw [superExactShiftPow, superExactInput_eq_zero_of_le_neg_half hε ht]
  simp

theorem superExactShiftReg_eq_zero_of_le_neg_half
    {ε a t : ℝ} (hε : 0 < ε) (ht : t ≤ -ε / 2) :
    superExactShiftReg ε a t = 0 := by
  rw [superExactShiftReg, superExactShiftPow_eq_const_of_le_neg_half hε ht]
  ring

theorem superExactShiftReg_zero
    {ε a : ℝ} (hε : 0 < ε) :
    superExactShiftReg ε a 0 = 0 := by
  rw [superExactShiftReg_eq_shifted_of_nonneg (ε := ε) (a := a) hε (by positivity)]
  ring_nf

theorem superExactShiftReg_hasDerivAt_shifted
    {ε a t : ℝ} (hε : 0 < ε) (ht : 0 < t) :
    HasDerivAt (superExactShiftReg ε a)
      (a * (ε + t) ^ (a - 1)) t := by
  have hloc :
      superExactShiftReg ε a =ᶠ[nhds t]
        fun y : ℝ => (ε + y) ^ a - ε ^ a := by
    filter_upwards [Ioi_mem_nhds ht] with y hy
    rw [superExactShiftReg_eq_shifted_of_nonneg (ε := ε) (a := a) hε hy.le]
  have hbase :
      HasDerivAt (fun y : ℝ => (ε + y) ^ a - ε ^ a)
        (a * (ε + t) ^ (a - 1)) t := by
    have hpow :
        HasDerivAt (fun y : ℝ => (ε + y) ^ a)
          (a * (ε + t) ^ (a - 1)) t := by
      simpa using
        (((hasDerivAt_id t).const_add ε).rpow_const
          (p := a) (Or.inl (by linarith : ε + t ≠ 0)))
    simpa using hpow.sub_const (ε ^ a)
  exact hbase.congr_of_eventuallyEq hloc

theorem superExactShiftReg_deriv_eq_shifted
    {ε a t : ℝ} (hε : 0 < ε) (ht : 0 < t) :
    deriv (superExactShiftReg ε a) t = a * (ε + t) ^ (a - 1) :=
  (superExactShiftReg_hasDerivAt_shifted (ε := ε) (a := a) hε ht).deriv

theorem superExactShiftReg_deriv_bounded
    {ε a : ℝ} (hε : 0 < ε) (ha : a < 1) :
    ∃ M : ℝ, ∀ t, |deriv (superExactShiftReg ε a) t| ≤ M := by
  have h1 : ContDiff ℝ 1 (superExactShiftReg ε a) :=
    (superExactShiftReg_contDiff (ε := ε) (a := a) hε).of_le (by simp)
  have hcont : Continuous (deriv (superExactShiftReg ε a)) := h1.continuous_deriv_one
  obtain ⟨Mmid, -, hMmid_max⟩ := (isCompact_Icc (a := -ε / 2) (b := (0 : ℝ))).exists_isMaxOn
    (Set.nonempty_Icc.2 (by linarith : -ε / 2 ≤ (0 : ℝ))) hcont.norm.continuousOn
  let M : ℝ := max ‖deriv (superExactShiftReg ε a) Mmid‖ (|a| * ε ^ (a - 1))
  refine ⟨M, ?_⟩
  intro t
  by_cases hlow : t < -ε / 2
  · have hloc : superExactShiftReg ε a =ᶠ[nhds t] fun _ => (0 : ℝ) := by
      filter_upwards [Iio_mem_nhds hlow] with y hy
      exact superExactShiftReg_eq_zero_of_le_neg_half (ε := ε) (a := a) hε hy.le
    rw [hloc.deriv_eq, deriv_const, abs_zero]
    have hMnonneg : 0 ≤ M := by
      change (0 : ℝ) ≤ max ‖deriv (superExactShiftReg ε a) Mmid‖ (|a| * ε ^ (a - 1))
      exact le_trans (norm_nonneg _) (le_max_left _ _)
    exact hMnonneg
  · push_neg at hlow
    by_cases hnonpos : t ≤ 0
    · have hbound :
          ‖deriv (superExactShiftReg ε a) t‖ ≤ ‖deriv (superExactShiftReg ε a) Mmid‖ :=
        Filter.eventually_principal.mp hMmid_max t (Set.mem_Icc.2 ⟨hlow, hnonpos⟩)
      calc
        |deriv (superExactShiftReg ε a) t|
            = ‖deriv (superExactShiftReg ε a) t‖ := by rw [Real.norm_eq_abs]
        _ ≤ ‖deriv (superExactShiftReg ε a) Mmid‖ := hbound
        _ ≤ M := le_max_left _ _
    · have ht : 0 < t := lt_of_not_ge hnonpos
      have hpow_nonneg : 0 ≤ (ε + t) ^ (a - 1) := Real.rpow_nonneg (by linarith) _
      have hpow_le : (ε + t) ^ (a - 1) ≤ ε ^ (a - 1) := by
        exact Real.rpow_le_rpow_of_nonpos hε (by linarith : ε ≤ ε + t) (by linarith)
      calc
        |deriv (superExactShiftReg ε a) t|
            = |a * (ε + t) ^ (a - 1)| := by
                rw [superExactShiftReg_deriv_eq_shifted (ε := ε) (a := a) hε ht]
        _ = |a| * (ε + t) ^ (a - 1) := by
              rw [abs_mul, abs_of_nonneg hpow_nonneg]
        _ ≤ |a| * ε ^ (a - 1) := by
              exact mul_le_mul_of_nonneg_left hpow_le (abs_nonneg _)
        _ ≤ M := le_max_right _ _

noncomputable def superExactPowerCutoff
    (η u : E → ℝ) (ε a : ℝ) : E → ℝ :=
  fun x => η x * superExactShiftReg ε a (u x) + ε ^ a * η x

noncomputable def superExactPowerCutoffReg
    (η u : E → ℝ) (ε a : ℝ) : E → ℝ :=
  fun x => η x * superExactShiftReg ε a (u x)

noncomputable def superExactTestCutoff
    (η u : E → ℝ) (ε a : ℝ) : E → ℝ :=
  fun x => η x * superExactPowerCutoff η u ε a x

noncomputable def superExactTestCutoffReg
    (η u : E → ℝ) (ε a : ℝ) : E → ℝ :=
  fun x => η x * (η x * superExactShiftReg ε a (u x))

omit [NeZero d] in
@[simp] lemma superExactPowerCutoff_eq_mul_shiftPow
    {u η : E → ℝ} {ε a : ℝ} {x : E} :
    superExactPowerCutoff η u ε a x =
      η x * superExactShiftPow ε a (u x) := by
  simp [superExactPowerCutoff, superExactShiftReg]
  ring

noncomputable def superExactPowerCutoffRegWitness
    {u η : E → ℝ} {ε a Cη : ℝ}
    (hε : 0 < ε) (ha : a < 1)
    (hu1 : MemW1pWitness 2 u (Metric.ball (0 : E) 1))
    (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hη_bound : ∀ x, |η x| ≤ 1)
    (hη_grad_bound : ∀ x, ‖fderiv ℝ η x‖ ≤ Cη) :
    MemW1pWitness 2
      (superExactPowerCutoffReg η u ε a)
      (Metric.ball (0 : E) 1) := by
  let hwReg :
      MemW1pWitness 2
        (fun x => superExactShiftReg ε a (u x))
        (Metric.ball (0 : E) 1) :=
    MemW1pWitness.comp_smooth_bounded (d := d) Metric.isOpen_ball hu1
      (superExactShiftReg ε a)
      (superExactShiftReg_contDiff (ε := ε) (a := a) hε)
      (superExactShiftReg_zero (ε := ε) (a := a) hε)
      (superExactShiftReg_deriv_bounded (ε := ε) (a := a) hε ha)
  have hCη_nonneg : 0 ≤ Cη := by
    exact le_trans (norm_nonneg _) (hη_grad_bound (0 : E))
  exact hwReg.mul_smooth_bounded Metric.isOpen_ball hη
    (C₀ := 1) (C₁ := Cη) (by norm_num) hCη_nonneg hη_bound hη_grad_bound

noncomputable def superExactTestCutoffRegWitness
    {u η : E → ℝ} {ε a Cη : ℝ}
    (hε : 0 < ε) (ha : a < 1)
    (hu1 : MemW1pWitness 2 u (Metric.ball (0 : E) 1))
    (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hη_bound : ∀ x, |η x| ≤ 1)
    (hη_grad_bound : ∀ x, ‖fderiv ℝ η x‖ ≤ Cη) :
    MemW1pWitness 2
      (superExactTestCutoffReg η u ε a)
      (Metric.ball (0 : E) 1) := by
  let hwReg :
      MemW1pWitness 2
        (fun x => superExactShiftReg ε a (u x))
        (Metric.ball (0 : E) 1) :=
    MemW1pWitness.comp_smooth_bounded (d := d) Metric.isOpen_ball hu1
      (superExactShiftReg ε a)
      (superExactShiftReg_contDiff (ε := ε) (a := a) hε)
      (superExactShiftReg_zero (ε := ε) (a := a) hε)
      (superExactShiftReg_deriv_bounded (ε := ε) (a := a) hε ha)
  have hCη_nonneg : 0 ≤ Cη := by
    exact le_trans (norm_nonneg _) (hη_grad_bound (0 : E))
  let hwηReg :=
    hwReg.mul_smooth_bounded Metric.isOpen_ball hη
      (C₀ := 1) (C₁ := Cη) (by norm_num) hCη_nonneg hη_bound hη_grad_bound
  exact hwηReg.mul_smooth_bounded Metric.isOpen_ball hη
    (C₀ := 1) (C₁ := Cη) (by norm_num) hCη_nonneg hη_bound hη_grad_bound

lemma superExactPowerCutoffRegWitness_grad
    {u η : E → ℝ} {ε a Cη : ℝ}
    (hε : 0 < ε) (ha : a < 1)
    (hu1 : MemW1pWitness 2 u (Metric.ball (0 : E) 1))
    (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hη_bound : ∀ x, |η x| ≤ 1)
    (hη_grad_bound : ∀ x, ‖fderiv ℝ η x‖ ≤ Cη)
    (x : E) (i : Fin d) :
    (superExactPowerCutoffRegWitness (d := d) (u := u) (η := η) (ε := ε) (a := a)
      (Cη := Cη) hε ha hu1 hη hη_bound hη_grad_bound).weakGrad x i =
      η x * deriv (superExactShiftReg ε a) (u x) * hu1.weakGrad x i +
        (fderiv ℝ η x) (EuclideanSpace.single i 1) * superExactShiftReg ε a (u x) := by
  simp only [superExactPowerCutoffRegWitness,
    MemW1pWitness.mul_smooth_bounded, MemW1pWitness.comp_smooth_bounded,
    WithLp.ofLp_add, WithLp.ofLp_smul, smul_eq_mul, Pi.add_apply, Pi.smul_apply]
  ring

lemma superExactTestCutoffRegWitness_grad
    {u η : E → ℝ} {ε a Cη : ℝ}
    (hε : 0 < ε) (ha : a < 1)
    (hu1 : MemW1pWitness 2 u (Metric.ball (0 : E) 1))
    (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hη_bound : ∀ x, |η x| ≤ 1)
    (hη_grad_bound : ∀ x, ‖fderiv ℝ η x‖ ≤ Cη)
    (x : E) (i : Fin d) :
    (superExactTestCutoffRegWitness (d := d) (u := u) (η := η) (ε := ε) (a := a)
      (Cη := Cη) hε ha hu1 hη hη_bound hη_grad_bound).weakGrad x i =
      2 * η x * (fderiv ℝ η x) (EuclideanSpace.single i 1) *
        superExactShiftReg ε a (u x) +
      η x ^ 2 * deriv (superExactShiftReg ε a) (u x) * hu1.weakGrad x i := by
  simp only [superExactTestCutoffRegWitness,
    MemW1pWitness.mul_smooth_bounded, MemW1pWitness.comp_smooth_bounded,
    WithLp.ofLp_add, WithLp.ofLp_smul, smul_eq_mul, Pi.add_apply, Pi.smul_apply]
  ring

noncomputable def superEtaWitness
    {η : E → ℝ} {s : ℝ}
    (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hη_sub_ball : tsupport η ⊆ Metric.ball (0 : E) s) :
    MemW1pWitness 2 η (Metric.ball (0 : E) 1) := by
  let hwUniv : MemW1pWitness 2 η Set.univ :=
    MemW1pWitness.of_contDiff_hasCompactSupport (p := 2) hη
      (hasCompactSupport_of_tsupport_subset_ball (f := η) hη_sub_ball)
  exact hwUniv.restrict Metric.isOpen_ball (by intro x hx; simp)

omit [NeZero d] in
lemma superEtaWitness_grad
    {η : E → ℝ} {s : ℝ}
    (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hη_sub_ball : tsupport η ⊆ Metric.ball (0 : E) s)
    (x : E) (i : Fin d) :
    (superEtaWitness (d := d) (η := η) (s := s) hη hη_sub_ball).weakGrad x i =
      (fderiv ℝ η x) (EuclideanSpace.single i 1) := by
  change
    (WithLp.toLp 2
      (fun j => (fderiv ℝ η x) (EuclideanSpace.single j 1))) i =
      (fderiv ℝ η x) (EuclideanSpace.single i 1)
  simp

noncomputable def superExactPowerCutoffWitness
    {u η : E → ℝ} {ε a s Cη : ℝ}
    (hε : 0 < ε) (ha : a < 1)
    (hu1 : MemW1pWitness 2 u (Metric.ball (0 : E) 1))
    (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hη_bound : ∀ x, |η x| ≤ 1)
    (hη_grad_bound : ∀ x, ‖fderiv ℝ η x‖ ≤ Cη)
    (hη_sub_ball : tsupport η ⊆ Metric.ball (0 : E) s) :
    MemW1pWitness 2
      (superExactPowerCutoff η u ε a)
      (Metric.ball (0 : E) 1) := by
  let hwReg :=
    superExactPowerCutoffRegWitness (d := d) (u := u) (η := η) (ε := ε) (a := a)
      (Cη := Cη) hε ha hu1 hη hη_bound hη_grad_bound
  let hwη := superEtaWitness (d := d) (η := η) (s := s) hη hη_sub_ball
  simpa [superExactPowerCutoff] using hwReg.add (hwη.smul (ε ^ a))

lemma superExactPowerCutoffWitness_grad
    {u η : E → ℝ} {ε a s Cη : ℝ}
    (hε : 0 < ε) (ha : a < 1)
    (hu1 : MemW1pWitness 2 u (Metric.ball (0 : E) 1))
    (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hη_bound : ∀ x, |η x| ≤ 1)
    (hη_grad_bound : ∀ x, ‖fderiv ℝ η x‖ ≤ Cη)
    (hη_sub_ball : tsupport η ⊆ Metric.ball (0 : E) s)
    (x : E) (i : Fin d) :
    (superExactPowerCutoffWitness (d := d) (u := u) (η := η) (ε := ε) (a := a)
      (s := s) (Cη := Cη) hε ha hu1 hη hη_bound hη_grad_bound hη_sub_ball).weakGrad x i =
      η x * deriv (superExactShiftReg ε a) (u x) * hu1.weakGrad x i +
        (fderiv ℝ η x) (EuclideanSpace.single i 1) * superExactShiftPow ε a (u x) := by
  rw [show
      (superExactPowerCutoffWitness (d := d) (u := u) (η := η) (ε := ε) (a := a)
        (s := s) (Cη := Cη) hε ha hu1 hη hη_bound hη_grad_bound hη_sub_ball).weakGrad x i =
      (superExactPowerCutoffRegWitness (d := d) (u := u) (η := η) (ε := ε) (a := a)
        (Cη := Cη) hε ha hu1 hη hη_bound hη_grad_bound).weakGrad x i +
        ε ^ a * (superEtaWitness (d := d) (η := η) (s := s) hη hη_sub_ball).weakGrad x i by
      simp [superExactPowerCutoffWitness, MemW1pWitness.add, MemW1pWitness.smul,
        smul_eq_mul],
    superExactPowerCutoffRegWitness_grad (d := d) (u := u) (η := η) (ε := ε) (a := a)
      (Cη := Cη) hε ha hu1 hη hη_bound hη_grad_bound x i,
    superEtaWitness_grad (d := d) (η := η) (s := s) hη hη_sub_ball x i]
  simp [superExactShiftPow, superExactShiftReg]
  ring

noncomputable def superExactTestCutoffWitness
    {u η : E → ℝ} {ε a s Cη : ℝ}
    (hε : 0 < ε) (ha : a < 1)
    (hu1 : MemW1pWitness 2 u (Metric.ball (0 : E) 1))
    (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hη_bound : ∀ x, |η x| ≤ 1)
    (hη_grad_bound : ∀ x, ‖fderiv ℝ η x‖ ≤ Cη)
    (hη_sub_ball : tsupport η ⊆ Metric.ball (0 : E) s) :
    MemW1pWitness 2
      (superExactTestCutoff η u ε a)
      (Metric.ball (0 : E) 1) := by
  let hwPow :=
    superExactPowerCutoffWitness (d := d) (u := u) (η := η) (ε := ε) (a := a)
      (s := s) (Cη := Cη) hε ha hu1 hη hη_bound hη_grad_bound hη_sub_ball
  have hCη_nonneg : 0 ≤ Cη := by
    exact le_trans (norm_nonneg _) (hη_grad_bound (0 : E))
  change MemW1pWitness 2
    (fun x => η x * superExactPowerCutoff η u ε a x)
    (Metric.ball (0 : E) 1)
  exact hwPow.mul_smooth_bounded (η := η) Metric.isOpen_ball hη
      (C₀ := 1) (C₁ := Cη) (by norm_num) hCη_nonneg hη_bound hη_grad_bound

lemma superExactTestCutoffWitness_grad
    {u η : E → ℝ} {ε a s Cη : ℝ}
    (hε : 0 < ε) (ha : a < 1)
    (hu1 : MemW1pWitness 2 u (Metric.ball (0 : E) 1))
    (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hη_bound : ∀ x, |η x| ≤ 1)
    (hη_grad_bound : ∀ x, ‖fderiv ℝ η x‖ ≤ Cη)
    (hη_sub_ball : tsupport η ⊆ Metric.ball (0 : E) s)
    (x : E) (i : Fin d) :
    (superExactTestCutoffWitness (d := d) (u := u) (η := η) (ε := ε) (a := a)
      (s := s) (Cη := Cη) hε ha hu1 hη hη_bound hη_grad_bound hη_sub_ball).weakGrad x i =
      2 * η x * (fderiv ℝ η x) (EuclideanSpace.single i 1) *
        superExactShiftPow ε a (u x) +
      η x ^ 2 * deriv (superExactShiftReg ε a) (u x) * hu1.weakGrad x i := by
  rw [show
      (superExactTestCutoffWitness (d := d) (u := u) (η := η) (ε := ε) (a := a)
        (s := s) (Cη := Cη) hε ha hu1 hη hη_bound hη_grad_bound hη_sub_ball).weakGrad x i =
      η x *
        (superExactPowerCutoffWitness (d := d) (u := u) (η := η) (ε := ε) (a := a)
          (s := s) (Cη := Cη) hε ha hu1 hη hη_bound hη_grad_bound hη_sub_ball).weakGrad x i +
        (fderiv ℝ η x) (EuclideanSpace.single i 1) * superExactPowerCutoff η u ε a x by
      simp [superExactTestCutoffWitness,
        MemW1pWitness.mul_smooth_bounded, smul_eq_mul],
    superExactPowerCutoffWitness_grad (d := d) (u := u) (η := η) (ε := ε) (a := a)
      (s := s) (Cη := Cη) hε ha hu1 hη hη_bound hη_grad_bound hη_sub_ball x i]
  rw [superExactPowerCutoff_eq_mul_shiftPow (u := u) (η := η) (ε := ε) (a := a) (x := x)]
  simp
  ring

omit [NeZero d] in
theorem superExactPowerCutoff_tsupport_subset
    {u η : E → ℝ} {ε a s : ℝ}
    (hη_sub_ball : tsupport η ⊆ Metric.ball (0 : E) s) :
    tsupport (superExactPowerCutoff η u ε a) ⊆ Metric.ball (0 : E) s :=
by
  let g : E → ℝ := fun x => η x * superExactShiftPow ε a (u x)
  have hEq : superExactPowerCutoff η u ε a = g := by
    funext x
    simp [g, superExactPowerCutoff_eq_mul_shiftPow]
  simpa [hEq, g] using
    (tsupport_mul_subset_left
      (f := η) (g := fun x => superExactShiftPow ε a (u x))).trans hη_sub_ball

omit [NeZero d] in
theorem superExactTestCutoff_tsupport_subset
    {u η : E → ℝ} {ε a s : ℝ}
    (hη_sub_ball : tsupport η ⊆ Metric.ball (0 : E) s) :
    tsupport (superExactTestCutoff η u ε a) ⊆ Metric.ball (0 : E) s :=
by
  change
    tsupport (fun x => η x * superExactPowerCutoff η u ε a x) ⊆ Metric.ball (0 : E) s
  exact
    (tsupport_mul_subset_left
      (f := η) (g := fun x => superExactPowerCutoff η u ε a x)).trans hη_sub_ball

theorem superExactPowerCutoff_memW01_on_ball
    {u η : E → ℝ} {ε a s Cη : ℝ}
    (_hs : 0 < s) (hs1 : s ≤ 1)
    (hε : 0 < ε) (ha : a < 1)
    (hu1 : MemW1pWitness 2 u (Metric.ball (0 : E) 1))
    (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hη_bound : ∀ x, |η x| ≤ 1)
    (hη_grad_bound : ∀ x, ‖fderiv ℝ η x‖ ≤ Cη)
    (hη_sub_ball : tsupport η ⊆ Metric.ball (0 : E) s) :
    MemW01p 2 (superExactPowerCutoff η u ε a) (Metric.ball (0 : E) s) := by
  let Ω : Set E := Metric.ball (0 : E) s
  let hwBig : MemW1pWitness 2 (superExactPowerCutoff η u ε a) (Metric.ball (0 : E) 1) :=
    superExactPowerCutoffWitness (d := d) (u := u) (η := η) (ε := ε) (a := a)
      (s := s) (Cη := Cη) hε ha hu1 hη hη_bound hη_grad_bound hη_sub_ball
  let hw : MemW1pWitness 2 (superExactPowerCutoff η u ε a) Ω :=
    hwBig.restrict Metric.isOpen_ball (Metric.ball_subset_ball hs1)
  have hv_support : tsupport (superExactPowerCutoff η u ε a) ⊆ Ω := by
    exact
      superExactPowerCutoff_tsupport_subset (d := d) (u := u) (η := η) (ε := ε) (a := a)
        hη_sub_ball
  have hv_compact : HasCompactSupport (superExactPowerCutoff η u ε a) :=
    hasCompactSupport_of_tsupport_subset_ball hv_support
  have hvW1 : MemW1p (ENNReal.ofReal (2 : ℝ))
      (superExactPowerCutoff η u ε a) Ω := by
    simpa [Ω] using hw.memW1p
  have hvW01_real : MemW01p (ENNReal.ofReal (2 : ℝ))
      (superExactPowerCutoff η u ε a) Ω := by
    exact
      memW01p_of_memW1p_of_tsupport_subset
        (d := d) Metric.isOpen_ball (p := (2 : ℝ)) (by norm_num)
        hvW1 hv_compact hv_support
  simpa [Ω] using hvW01_real

theorem superExactTestCutoff_memH01_on_ball
    {u η : E → ℝ} {ε a s Cη : ℝ}
    (_hs : 0 < s) (hs1 : s ≤ 1)
    (hε : 0 < ε) (ha : a < 1)
    (hu1 : MemW1pWitness 2 u (Metric.ball (0 : E) 1))
    (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hη_bound : ∀ x, |η x| ≤ 1)
    (hη_grad_bound : ∀ x, ‖fderiv ℝ η x‖ ≤ Cη)
    (hη_sub_ball : tsupport η ⊆ Metric.ball (0 : E) s) :
    MemH01 (superExactTestCutoff η u ε a) (Metric.ball (0 : E) s) := by
  let Ω : Set E := Metric.ball (0 : E) s
  let hwBig : MemW1pWitness 2 (superExactTestCutoff η u ε a) (Metric.ball (0 : E) 1) :=
    superExactTestCutoffWitness (d := d) (u := u) (η := η) (ε := ε) (a := a)
      (s := s) (Cη := Cη) hε ha hu1 hη hη_bound hη_grad_bound hη_sub_ball
  let hw : MemW1pWitness 2 (superExactTestCutoff η u ε a) Ω :=
    hwBig.restrict Metric.isOpen_ball (Metric.ball_subset_ball hs1)
  have hv_support : tsupport (superExactTestCutoff η u ε a) ⊆ Ω := by
    exact
      superExactTestCutoff_tsupport_subset (d := d) (u := u) (η := η) (ε := ε) (a := a)
        hη_sub_ball
  have hv_compact : HasCompactSupport (superExactTestCutoff η u ε a) :=
    hasCompactSupport_of_tsupport_subset_ball hv_support
  have hvW1 : MemW1p (ENNReal.ofReal (2 : ℝ))
      (superExactTestCutoff η u ε a) Ω := by
    simpa [Ω] using hw.memW1p
  have hvW01_real : MemW01p (ENNReal.ofReal (2 : ℝ))
      (superExactTestCutoff η u ε a) Ω := by
    exact
      memW01p_of_memW1p_of_tsupport_subset
        (d := d) Metric.isOpen_ball (p := (2 : ℝ)) (by norm_num)
        hvW1 hv_compact hv_support
  simpa [Ω] using hvW01_real

theorem superExactTestCutoff_memH01_on_unitBall
    {u η : E → ℝ} {ε a s Cη : ℝ}
    (hs1 : s ≤ 1)
    (hε : 0 < ε) (ha : a < 1)
    (hu1 : MemW1pWitness 2 u (Metric.ball (0 : E) 1))
    (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hη_bound : ∀ x, |η x| ≤ 1)
    (hη_grad_bound : ∀ x, ‖fderiv ℝ η x‖ ≤ Cη)
    (hη_sub_ball : tsupport η ⊆ Metric.ball (0 : E) s) :
    MemH01 (superExactTestCutoff η u ε a) (Metric.ball (0 : E) 1) := by
  let Ω : Set E := Metric.ball (0 : E) 1
  let hw : MemW1pWitness 2 (superExactTestCutoff η u ε a) Ω :=
    superExactTestCutoffWitness (d := d) (u := u) (η := η) (ε := ε) (a := a)
      (s := s) (Cη := Cη) hε ha hu1 hη hη_bound hη_grad_bound hη_sub_ball
  have hv_support : tsupport (superExactTestCutoff η u ε a) ⊆ Ω := by
    exact
      (superExactTestCutoff_tsupport_subset (d := d) (u := u) (η := η) (ε := ε) (a := a)
        hη_sub_ball).trans (Metric.ball_subset_ball hs1)
  have hv_compact : HasCompactSupport (superExactTestCutoff η u ε a) :=
    hasCompactSupport_of_tsupport_subset_ball hv_support
  have hvW1 : MemW1p (ENNReal.ofReal (2 : ℝ))
      (superExactTestCutoff η u ε a) Ω := by
    simpa [Ω] using hw.memW1p
  have hvW01_real : MemW01p (ENNReal.ofReal (2 : ℝ))
      (superExactTestCutoff η u ε a) Ω := by
    exact
      memW01p_of_memW1p_of_tsupport_subset
        (d := d) Metric.isOpen_ball (p := (2 : ℝ)) (by norm_num)
        hvW1 hv_compact hv_support
  simpa [Ω] using hvW01_real

omit [NeZero d] in
theorem superExactInv_testCutoff_nonneg_global
    {u η : E → ℝ} {ε p s : ℝ}
    (hε : 0 < ε) (hs1 : s ≤ 1)
    (hu_pos : ∀ x ∈ Metric.ball (0 : E) 1, 0 < u x)
    (hη_sub_ball : tsupport η ⊆ Metric.ball (0 : E) s) :
    ∀ x, 0 ≤ superExactTestCutoff η u ε (-(1 + p)) x := by
  intro x
  by_cases hx : x ∈ tsupport η
  · have hux_pos : 0 < u x := hu_pos x ((Metric.ball_subset_ball hs1) (hη_sub_ball hx))
    have hpow_pos : 0 < superExactShiftPow ε (-1 - p) (u x) := by
      rw [superExactShiftPow_eq_shifted_of_nonneg (ε := ε) (a := -1 - p) hε hux_pos.le]
      exact Real.rpow_pos_of_pos (by positivity) _
    have hterm_nonneg :
        0 ≤ η x ^ 2 * superExactShiftPow ε (-1 - p) (u x) := by
      exact mul_nonneg (sq_nonneg _) hpow_pos.le
    rw [superExactTestCutoff, superExactPowerCutoff_eq_mul_shiftPow (u := u) (η := η)
      (ε := ε) (a := -(1 + p)) (x := x)]
    ring_nf
    exact hterm_nonneg
  · have hηx : η x = 0 := image_eq_zero_of_notMem_tsupport hx
    simp [superExactTestCutoff, superExactPowerCutoff_eq_mul_shiftPow, hηx]

theorem superExactTestCutoff_core_eq
    (A : NormalizedEllipticCoeff d (Metric.ball (0 : E) 1))
    {u η : E → ℝ} {ε a Cη : ℝ}
    (hε : 0 < ε) (ha : a < 1)
    (hu1 : MemW1pWitness 2 u (Metric.ball (0 : E) 1))
    (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hη_bound : ∀ x, |η x| ≤ 1)
    (hη_grad_bound : ∀ x, ‖fderiv ℝ η x‖ ≤ Cη)
    (hη_support_unit : tsupport η ⊆ Metric.ball (0 : E) 1)
    (hu_pos : ∀ x ∈ Metric.ball (0 : E) 1, 0 < u x) :
    let hwφ := superExactTestCutoffWitness (d := d) (u := u) (η := η) (ε := ε) (a := a)
      (s := 1) (Cη := Cη) hε ha hu1 hη hη_bound hη_grad_bound hη_support_unit
    let ψ := fun x => superExactShiftPow ε a (u x)
    let Equad := bilinFormIntegrandOfCoeff A.1 hu1 hu1
    let crossInner : E → ℝ := fun x =>
      (2 * η x * ψ x) *
        inner ℝ (matMulE (A.1.a x) (hu1.weakGrad x)) (superFderivVec η x)
    let coreIntegrand : E → ℝ := fun x =>
      η x ^ 2 * deriv (superExactShiftReg ε a) (u x) * Equad x + crossInner x
    ∀ x, coreIntegrand x = bilinFormIntegrandOfCoeff A.1 hu1 hwφ x := by
  intro hwφ ψ Equad crossInner coreIntegrand x
  by_cases hx : x ∈ tsupport η
  · have hux_pos : 0 < u x := hu_pos x (hη_support_unit hx)
    have hφformula :
        hwφ.weakGrad x =
          (2 * η x * ψ x) • superFderivVec η x +
            (η x ^ 2 * deriv (superExactShiftReg ε a) (u x)) • hu1.weakGrad x := by
      apply PiLp.ext
      intro i
      change
        (superExactTestCutoffWitness (d := d) (u := u) (η := η) (ε := ε) (a := a)
          (s := 1) (Cη := Cη) hε ha hu1 hη hη_bound hη_grad_bound hη_support_unit).weakGrad x i =
          (2 * η x * ψ x) * superFderivVec η x i +
            (η x ^ 2 * deriv (superExactShiftReg ε a) (u x)) * hu1.weakGrad x i
      simpa [ψ, superFderivVec_apply, mul_assoc, mul_left_comm, mul_comm] using
        (superExactTestCutoffWitness_grad (d := d) (u := u) (η := η) (ε := ε) (a := a)
          (s := 1) (Cη := Cη) hε ha hu1 hη hη_bound hη_grad_bound hη_support_unit x i)
    calc
      coreIntegrand x
          = η x ^ 2 * deriv (superExactShiftReg ε a) (u x) * Equad x + crossInner x := by
              rfl
      _ = bilinFormIntegrandOfCoeff A.1 hu1 hwφ x := by
            dsimp [crossInner, Equad, ψ]
            change
              η x ^ 2 * deriv (superExactShiftReg ε a) (u x) *
                  inner ℝ (matMulE (A.1.a x) (hu1.weakGrad x)) (hu1.weakGrad x) +
                (2 * η x * superExactShiftPow ε a (u x)) *
                  inner ℝ (matMulE (A.1.a x) (hu1.weakGrad x)) (superFderivVec η x) =
              inner ℝ (matMulE (A.1.a x) (hu1.weakGrad x)) (hwφ.weakGrad x)
            rw [hφformula, inner_add_right, inner_smul_right, inner_smul_right]
            ring
  · have hηx : η x = 0 := image_eq_zero_of_notMem_tsupport hx
    have hφgrad_zero : hwφ.weakGrad x = 0 := by
      apply PiLp.ext
      intro i
      have hformula :
          hwφ.weakGrad x i =
            2 * η x * (fderiv ℝ η x) (EuclideanSpace.single i 1) *
              superExactShiftPow ε a (u x) +
            η x ^ 2 * deriv (superExactShiftReg ε a) (u x) * hu1.weakGrad x i := by
        simpa [hwφ, mul_assoc, mul_left_comm, mul_comm] using
          (superExactTestCutoffWitness_grad (d := d) (u := u) (η := η) (ε := ε) (a := a)
            (s := 1) (Cη := Cη) hε ha hu1 hη hη_bound hη_grad_bound hη_support_unit x i)
      rw [hformula]
      have hfdi_zero :
          (fderiv ℝ η x) (EuclideanSpace.single i 1) = 0 := by
        exact fderiv_apply_zero_outside_of_tsupport_subset
          (Ω := tsupport η) (hf := hη) (hsub := subset_rfl) hx i
      simp [hηx, hfdi_zero]
    calc
      coreIntegrand x = 0 := by
        dsimp [coreIntegrand, crossInner, Equad]
        rw [hηx]
        ring
      _ = bilinFormIntegrandOfCoeff A.1 hu1 hwφ x := by
            rw [bilinFormIntegrandOfCoeff, hφgrad_zero]
            simp

theorem superExactShiftPow_deriv_eq_shifted
    {ε a t : ℝ} (hε : 0 < ε) (ht : 0 < t) :
    deriv (superExactShiftPow ε a) t = a * (ε + t) ^ (a - 1) := by
  have hbase :
      HasDerivAt (superExactShiftPow ε a) (a * (ε + t) ^ (a - 1)) t := by
    have hreg :=
      superExactShiftReg_hasDerivAt_shifted (ε := ε) (a := a) hε ht
    have hpow :
        HasDerivAt (fun y => superExactShiftReg ε a y + ε ^ a)
          (a * (ε + t) ^ (a - 1)) t := by
      simpa [superExactShiftReg, superExactShiftPow] using hreg.add_const (ε ^ a)
    simpa [superExactShiftReg, superExactShiftPow] using hpow
  exact hbase.deriv

lemma superExactShiftPow_nonneg
    {ε a t : ℝ} (hε : 0 < ε) :
    0 ≤ superExactShiftPow ε a t := by
  dsimp [superExactShiftPow]
  have hbase_nonneg : 0 ≤ ε + superExactInput ε t := by
    have hinput_lb := superExactInput_lower_bound (ε := ε) hε (t := t)
    linarith
  exact Real.rpow_nonneg hbase_nonneg _

lemma superExactInv_test_ratio
    {ε p t : ℝ} (hε : 0 < ε) (hp : 0 < p) (ht : 0 < t) :
    |superExactShiftPow ε (-(1 + p)) t| ^ 2 /
        (-(deriv (superExactShiftReg ε (-(1 + p))) t)) =
      (ε + t) ^ (-p) / (1 + p) := by
  have hbase_pos : 0 < ε + t := by positivity
  have hpow_eq :
      superExactShiftPow ε (-(1 + p)) t = (ε + t) ^ (-(1 + p)) := by
    rw [superExactShiftPow_eq_shifted_of_nonneg (ε := ε) (a := -(1 + p)) hε ht.le]
  have hderiv_eq :
      -(deriv (superExactShiftReg ε (-(1 + p))) t) =
        (1 + p) * (ε + t) ^ (-(2 + p)) := by
    rw [superExactShiftReg_deriv_eq_shifted (ε := ε) (a := -(1 + p)) hε ht]
    ring_nf
  have hpow_pos : 0 < superExactShiftPow ε (-(1 + p)) t := by
    rw [hpow_eq]
    exact Real.rpow_pos_of_pos hbase_pos _
  have hnegpow :
      (ε + t) ^ (-(2 + p)) = ((ε + t) ^ (2 + p))⁻¹ := by
    rw [Real.rpow_neg hbase_pos.le]
  calc
    |superExactShiftPow ε (-(1 + p)) t| ^ 2 /
        (-(deriv (superExactShiftReg ε (-(1 + p))) t))
        = (((ε + t) ^ (-(1 + p))) ^ 2) /
            ((1 + p) * (ε + t) ^ (-(2 + p))) := by
              rw [hpow_eq, hderiv_eq]
              congr 1
              rw [abs_of_pos (Real.rpow_pos_of_pos hbase_pos _)]
    _ = (((ε + t) ^ (-(1 + p))) ^ 2) /
          ((1 + p) * ((ε + t) ^ (2 + p))⁻¹) := by
            rw [hnegpow]
    _ = ((((ε + t) ^ (-(1 + p))) ^ 2) *
          (ε + t) ^ (2 + p)) / (1 + p) := by
            field_simp [show (1 + p : ℝ) ≠ 0 by linarith,
              show (ε + t) ^ (2 + p) ≠ 0 by
                exact (Real.rpow_pos_of_pos hbase_pos _).ne']
    _ = (ε + t) ^ (-p) / (1 + p) := by
          congr 1
          calc
            (((ε + t) ^ (-(1 + p))) ^ 2) * (ε + t) ^ (2 + p)
                = ((ε + t) ^ (-(1 + p)) * (ε + t) ^ (-(1 + p))) *
                    (ε + t) ^ (2 + p) := by
                    rw [pow_two]
            _ = (ε + t) ^ (-(1 + p) + (-(1 + p))) * (ε + t) ^ (2 + p) := by
                  rw [← Real.rpow_add hbase_pos]
            _ = (ε + t) ^ ((-(1 + p) + (-(1 + p))) + (2 + p)) := by
                  rw [← Real.rpow_add hbase_pos]
            _ = (ε + t) ^ (-p) := by ring_nf

omit [NeZero d] in
lemma superExactInv_test_ratio_of_pos
    {u : E → ℝ} {ε p : ℝ} {x : E}
    (hε : 0 < ε) (hp : 0 < p) (hux : 0 < u x) :
    |superExactShiftPow ε (-(1 + p)) (u x)| ^ 2 /
        (-(deriv (superExactShiftReg ε (-(1 + p))) (u x))) =
      superExactShiftPow ε (-p) (u x) / (1 + p) := by
  have hbase :=
    superExactInv_test_ratio (ε := ε) (p := p) (t := u x) hε hp hux
  have hpow_eq :
      (ε + u x) ^ (-p) = superExactShiftPow ε (-p) (u x) := by
    symm
    rw [superExactShiftPow_eq_shifted_of_nonneg (ε := ε) (a := -p) hε hux.le]
  simpa [hpow_eq] using hbase

lemma superExactInv_test_deriv_neg_pos
    {ε p t : ℝ} (hε : 0 < ε) (hp : 0 < p) (ht : 0 < t) :
    0 < -(deriv (superExactShiftReg ε (-(1 + p))) t) := by
  rw [superExactShiftReg_deriv_eq_shifted (ε := ε) (a := -(1 + p)) hε ht]
  have hp1 : 0 < 1 + p := by linarith
  have hbase_pos : 0 < ε + t := by linarith
  have hpos : 0 < (1 + p) * (ε + t) ^ (-(1 + p) - 1) := by
    exact mul_pos hp1 (Real.rpow_pos_of_pos hbase_pos _)
  nlinarith

lemma superExactInv_power_deriv_sq
    {ε p t : ℝ} (hε : 0 < ε) (hp : 0 < p) (ht : 0 < t) :
    (deriv (superExactShiftReg ε (-(p / 2))) t) ^ 2 =
      (p ^ 2 / (4 * (1 + p))) *
        (-(deriv (superExactShiftReg ε (-(1 + p))) t)) := by
  have hbase_pos : 0 < ε + t := by positivity
  have hderiv_pow :
      deriv (superExactShiftReg ε (-(p / 2))) t =
        (-(p / 2)) * (ε + t) ^ (-(p / 2) - 1) := by
    rw [superExactShiftReg_deriv_eq_shifted (ε := ε) (a := -(p / 2)) hε ht]
  have hderiv_test :
      -(deriv (superExactShiftReg ε (-(1 + p))) t) =
        (1 + p) * (ε + t) ^ (-(2 + p)) := by
    rw [superExactShiftReg_deriv_eq_shifted (ε := ε) (a := -(1 + p)) hε ht]
    ring_nf
  calc
    (deriv (superExactShiftReg ε (-(p / 2))) t) ^ 2
        = ((p / 2) ^ 2) * (ε + t) ^ (-(2 + p)) := by
            rw [hderiv_pow]
            calc
              ((-(p / 2)) * (ε + t) ^ (-(p / 2) - 1)) ^ 2
                  = (p / 2) ^ 2 *
                      ((ε + t) ^ (-(p / 2) - 1) * (ε + t) ^ (-(p / 2) - 1)) := by
                      ring_nf
              _ = (p / 2) ^ 2 * ((ε + t) ^ ((-(p / 2) - 1) + (-(p / 2) - 1))) := by
                    congr 1
                    rw [← Real.rpow_add hbase_pos]
              _ = (p / 2) ^ 2 * (ε + t) ^ (-(2 + p)) := by
                    congr 2
                    ring_nf
    _ = (p ^ 2 / (4 * (1 + p))) *
          ((1 + p) * (ε + t) ^ (-(2 + p))) := by
            field_simp [show (1 + p : ℝ) ≠ 0 by linarith]
            ring
    _ = (p ^ 2 / (4 * (1 + p))) *
          (-(deriv (superExactShiftReg ε (-(1 + p))) t)) := by
            rw [hderiv_test]

lemma superExactInv_power_sq
    {ε p t : ℝ} (hε : 0 < ε) (ht : 0 < t) :
    (superExactShiftPow ε (-(p / 2)) t) ^ 2 =
      superExactShiftPow ε (-p) t := by
  have hbase_pos : 0 < ε + t := by positivity
  rw [superExactShiftPow_eq_shifted_of_nonneg (ε := ε) (a := -(p / 2)) hε ht.le,
    superExactShiftPow_eq_shifted_of_nonneg (ε := ε) (a := -p) hε ht.le]
  calc
    ((ε + t) ^ (-(p / 2))) ^ 2
        = (ε + t) ^ (-(p / 2) + -(p / 2)) := by
            rw [pow_two, ← Real.rpow_add hbase_pos]
    _ = (ε + t) ^ (-p) := by ring_nf

omit [NeZero d] in
lemma superExactInv_power_sq_of_pos
    {u : E → ℝ} {ε p : ℝ} {x : E}
    (hε : 0 < ε) (hux : 0 < u x) :
    (superExactShiftPow ε (-(p / 2)) (u x)) ^ 2 =
      superExactShiftPow ε (-p) (u x) := by
  exact superExactInv_power_sq (ε := ε) (p := p) (t := u x) hε hux

lemma superExactFwd_test_ratio
    {ε p t : ℝ} (hε : 0 < ε) (_hp : 0 < p) (hp1 : p < 1) (ht : 0 < t) :
    |superExactShiftPow ε (p - 1) t| ^ 2 /
        (-(deriv (superExactShiftReg ε (p - 1)) t)) =
      superExactShiftPow ε p t / (1 - p) := by
  have hbase_pos : 0 < ε + t := by positivity
  have hpow_eq :
      superExactShiftPow ε (p - 1) t = (ε + t) ^ (p - 1) := by
    rw [superExactShiftPow_eq_shifted_of_nonneg (ε := ε) (a := p - 1) hε ht.le]
  have hpow_p_eq :
      superExactShiftPow ε p t = (ε + t) ^ p := by
    rw [superExactShiftPow_eq_shifted_of_nonneg (ε := ε) (a := p) hε ht.le]
  have hpow_pos : 0 < superExactShiftPow ε (p - 1) t := by
    rw [hpow_eq]
    exact Real.rpow_pos_of_pos hbase_pos _
  have habs :
      |superExactShiftPow ε (p - 1) t| = (ε + t) ^ (p - 1) := by
    rw [hpow_eq, abs_of_pos (Real.rpow_pos_of_pos hbase_pos _)]
  have hderiv :
      deriv (superExactShiftReg ε (p - 1)) t =
        (p - 1) * (ε + t) ^ (p - 2) := by
    rw [superExactShiftReg_deriv_eq_shifted (ε := ε) (a := p - 1) hε ht]
    congr 2
    ring_nf
  have hderiv_neg :
      -(deriv (superExactShiftReg ε (p - 1)) t) =
        (1 - p) * (ε + t) ^ (p - 2) := by
    rw [hderiv]
    ring
  have hpow_term_ne : (ε + t) ^ (p - 2) ≠ 0 := by
    exact (Real.rpow_pos_of_pos hbase_pos _).ne'
  calc
    |superExactShiftPow ε (p - 1) t| ^ 2 /
        (-(deriv (superExactShiftReg ε (p - 1)) t))
        = (((ε + t) ^ (p - 1)) ^ 2) /
            ((1 - p) * (ε + t) ^ (p - 2)) := by
              rw [habs, hderiv_neg]
    _ = (((ε + t) ^ (p - 1)) ^ 2 * ((ε + t) ^ (p - 2))⁻¹) / (1 - p) := by
          field_simp [show (1 - p : ℝ) ≠ 0 by linarith, hpow_term_ne]
    _ = ((ε + t) ^ p) / (1 - p) := by
          congr 1
          calc
            ((ε + t) ^ (p - 1)) ^ 2 * ((ε + t) ^ (p - 2))⁻¹
                = ((ε + t) ^ (p - 1 + (p - 1))) * ((ε + t) ^ (-(p - 2))) := by
                    rw [pow_two, ← Real.rpow_add hbase_pos]
                    rw [show ((ε + t) ^ (p - 2))⁻¹ = (ε + t) ^ (-(p - 2)) by
                      rw [Real.rpow_neg hbase_pos.le]]
            _ = (ε + t) ^ ((p - 1 + (p - 1)) + (-(p - 2))) := by
                  rw [← Real.rpow_add hbase_pos]
            _ = (ε + t) ^ p := by ring_nf
    _ = superExactShiftPow ε p t / (1 - p) := by
          rw [hpow_p_eq]

omit [NeZero d] in
lemma superExactFwd_test_ratio_of_pos
    {u : E → ℝ} {ε p : ℝ} {x : E}
    (hε : 0 < ε) (hp : 0 < p) (hp1 : p < 1) (hux : 0 < u x) :
    |superExactShiftPow ε (p - 1) (u x)| ^ 2 /
        (-(deriv (superExactShiftReg ε (p - 1)) (u x))) =
      superExactShiftPow ε p (u x) / (1 - p) := by
  exact superExactFwd_test_ratio (ε := ε) (p := p) (t := u x) hε hp hp1 hux

lemma superExactFwd_test_deriv_neg_pos
    {ε p t : ℝ} (hε : 0 < ε) (_hp : 0 < p) (hp1 : p < 1) (ht : 0 < t) :
    0 < -(deriv (superExactShiftReg ε (p - 1)) t) := by
  have hgap : 0 < 1 - p := by linarith
  have hbase_pos : 0 < ε + t := by positivity
  have hpos : 0 < (1 - p) * (ε + t) ^ (p - 2) := by
    exact mul_pos hgap (Real.rpow_pos_of_pos hbase_pos _)
  have hderiv_neg :
      -(deriv (superExactShiftReg ε (p - 1)) t) =
        (1 - p) * (ε + t) ^ (p - 2) := by
    rw [superExactShiftReg_deriv_eq_shifted (ε := ε) (a := p - 1) hε ht]
    ring_nf
  rw [hderiv_neg]
  exact hpos

lemma superExactFwd_power_deriv_sq
    {ε p t : ℝ} (hε : 0 < ε) (hp : 0 < p) (hp1 : p < 1) (ht : 0 < t) :
    (deriv (superExactShiftReg ε (p / 2)) t) ^ 2 =
      (p ^ 2 / (4 * (1 - p))) *
        (-(deriv (superExactShiftReg ε (p - 1)) t)) := by
  have hbase_pos : 0 < ε + t := by positivity
  have hderiv_pow :
      deriv (superExactShiftReg ε (p / 2)) t =
        (p / 2) * (ε + t) ^ (p / 2 - 1) := by
    rw [superExactShiftReg_deriv_eq_shifted (ε := ε) (a := p / 2) hε ht]
  have hderiv_test :
      -(deriv (superExactShiftReg ε (p - 1)) t) =
        (1 - p) * (ε + t) ^ (p - 2) := by
    rw [superExactShiftReg_deriv_eq_shifted (ε := ε) (a := p - 1) hε ht]
    ring_nf
  calc
    (deriv (superExactShiftReg ε (p / 2)) t) ^ 2
        = ((p / 2) ^ 2) * (ε + t) ^ (p - 2) := by
            rw [hderiv_pow]
            calc
              ((p / 2) * (ε + t) ^ (p / 2 - 1)) ^ 2
                  = (p / 2) ^ 2 *
                      ((ε + t) ^ (p / 2 - 1) * (ε + t) ^ (p / 2 - 1)) := by
                      ring_nf
              _ = (p / 2) ^ 2 * ((ε + t) ^ ((p / 2 - 1) + (p / 2 - 1))) := by
                    congr 1
                    rw [← Real.rpow_add hbase_pos]
              _ = (p / 2) ^ 2 * (ε + t) ^ (p - 2) := by
                    congr 2
                    ring_nf
    _ = (p ^ 2 / (4 * (1 - p))) * ((1 - p) * (ε + t) ^ (p - 2)) := by
            field_simp [show (1 - p : ℝ) ≠ 0 by linarith]
            ring
    _ = (p ^ 2 / (4 * (1 - p))) *
          (-(deriv (superExactShiftReg ε (p - 1)) t)) := by
            rw [hderiv_test]

lemma superExactFwd_power_sq
    {ε p t : ℝ} (hε : 0 < ε) (ht : 0 < t) :
    (superExactShiftPow ε (p / 2) t) ^ 2 =
      superExactShiftPow ε p t := by
  have hbase_pos : 0 < ε + t := by positivity
  rw [superExactShiftPow_eq_shifted_of_nonneg (ε := ε) (a := p / 2) hε ht.le,
    superExactShiftPow_eq_shifted_of_nonneg (ε := ε) (a := p) hε ht.le]
  calc
    ((ε + t) ^ (p / 2)) ^ 2 = (ε + t) ^ (p / 2 + p / 2) := by
      rw [pow_two, ← Real.rpow_add hbase_pos]
    _ = (ε + t) ^ p := by ring_nf

omit [NeZero d] in
lemma superExactFwd_power_sq_of_pos
    {u : E → ℝ} {ε p : ℝ} {x : E}
    (hε : 0 < ε) (hux : 0 < u x) :
    (superExactShiftPow ε (p / 2) (u x)) ^ 2 =
      superExactShiftPow ε p (u x) := by
  exact superExactFwd_power_sq (ε := ε) (p := p) (t := u x) hε hux

lemma superExactInv_pow_abs_le_global
    {ε p t : ℝ} (hε : 0 < ε) (hp : 0 ≤ p) :
    |superExactShiftPow ε (-p) t| ≤ (ε / 2) ^ (-p) := by
  dsimp [superExactShiftPow]
  have hinput_lb : -ε / 2 ≤ superExactInput ε t := by
    exact superExactInput_lower_bound (ε := ε) hε (t := t)
  have hbase_lb : ε / 2 ≤ ε + superExactInput ε t := by
    linarith
  have hbase_nonneg : 0 ≤ ε + superExactInput ε t := by
    linarith
  rw [abs_of_nonneg (Real.rpow_nonneg hbase_nonneg _)]
  exact Real.rpow_le_rpow_of_nonpos (by positivity : 0 < ε / 2) hbase_lb (by linarith)

omit [NeZero d] in
theorem superExactShiftPow_comp_aemeasurable
    {Ω : Set E} {u : E → ℝ} {ε a : ℝ}
    (hε : 0 < ε) (hu : MemW1pWitness 2 u Ω) :
    AEMeasurable (fun x => superExactShiftPow ε a (u x)) (volume.restrict Ω) := by
  exact
    ((superExactShiftPow_contDiff (ε := ε) (a := a) hε).continuous.measurable).comp_aemeasurable
      hu.memLp.aestronglyMeasurable.aemeasurable

omit [NeZero d] in
theorem superExactInv_shiftPow_integrableOn_ball
    {u : E → ℝ} {ε p s : ℝ}
    (hε : 0 < ε) (hp : 0 ≤ p) (_hs : 0 < s)
    (hu : MemW1pWitness 2 u (Metric.ball (0 : E) s)) :
    IntegrableOn (fun x => superExactShiftPow ε (-p) (u x))
      (Metric.ball (0 : E) s) volume := by
  have h_int :
      IntegrableOn (fun x => superExactShiftPow ε (-p) (u x))
        Set.univ (volume.restrict (Metric.ball (0 : E) s)) := by
    apply Measure.integrableOn_of_bounded (M := (ε / 2) ^ (-p))
    · simpa using (measure_ball_lt_top (μ := volume) (x := (0 : E)) (r := s)).ne
    · exact
        (superExactShiftPow_comp_aemeasurable
          (Ω := Metric.ball (0 : E) s) (u := u) (ε := ε) (a := -p) hε hu).aestronglyMeasurable
    · filter_upwards with x
      have hbound :=
        superExactInv_pow_abs_le_global (ε := ε) (p := p) (t := u x) hε hp
      have hfx_nonneg : 0 ≤ superExactShiftPow ε (-p) (u x) :=
        superExactShiftPow_nonneg (ε := ε) (a := -p) hε
      have hM_nonneg : 0 ≤ (ε / 2) ^ (-p) := by
        exact Real.rpow_nonneg (by positivity) _
      simpa [Real.norm_eq_abs, abs_of_nonneg hfx_nonneg, abs_of_nonneg hM_nonneg] using hbound
  simpa [IntegrableOn] using h_int

omit [NeZero d] in
theorem superExactFwd_shiftPow_integrableOn_ball
    {u : E → ℝ} {ε p s : ℝ}
    (hε : 0 < ε) (hp : 0 < p) (hp1 : p < 1) (_hs : 0 < s)
    (hu_pos : ∀ x ∈ Metric.ball (0 : E) s, 0 < u x)
    (hu : MemW1pWitness 2 u (Metric.ball (0 : E) s))
    (hpInt : IntegrableOn (fun x => |u x| ^ p) (Metric.ball (0 : E) s) volume) :
    IntegrableOn (fun x => superExactShiftPow ε p (u x))
      (Metric.ball (0 : E) s) volume := by
  let Ω : Set E := Metric.ball (0 : E) s
  have hconst_int : IntegrableOn (fun _ : E => ε ^ p) Ω volume := by
    exact integrableOn_const (measure_ball_lt_top (μ := volume) (x := (0 : E)) (r := s)).ne
  have hsum_int :
      Integrable (fun x => ε ^ p + |u x| ^ p) (volume.restrict Ω) := by
    simpa [Ω, IntegrableOn] using hconst_int.add hpInt
  refine Integrable.mono' hsum_int ?_ ?_
  · exact
      (superExactShiftPow_comp_aemeasurable
        (Ω := Ω) (u := u) (ε := ε) (a := p) hε hu).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx
    have hux : 0 < u x := hu_pos x hx
    have hfx_nonneg : 0 ≤ superExactShiftPow ε p (u x) :=
      superExactShiftPow_nonneg (ε := ε) (a := p) hε
    have hrhs_nonneg : 0 ≤ ε ^ p + |u x| ^ p := by
      exact add_nonneg (Real.rpow_nonneg hε.le _) (Real.rpow_nonneg (abs_nonneg _) _)
    have hbound :
        superExactShiftPow ε p (u x) ≤ ε ^ p + |u x| ^ p := by
      rw [superExactShiftPow_eq_shifted_of_nonneg (ε := ε) (a := p) hε hux.le]
      have hsubadd :=
        Real.rpow_add_le_add_rpow hε.le hux.le hp.le hp1.le
      simpa [abs_of_pos hux] using hsubadd
    simpa [Real.norm_eq_abs, abs_of_nonneg hfx_nonneg, abs_of_nonneg hrhs_nonneg] using hbound

omit [NeZero d] in
lemma superExactInv_termB_pointwise
    {u η : E → ℝ} {ε p Cη : ℝ} {x : E}
    (hε : 0 < ε)
    (hCη_nonneg : 0 ≤ Cη)
    (hη_grad_bound : ∀ x, ‖fderiv ℝ η x‖ ≤ Cη)
    (hux : 0 < u x) :
    ‖fderiv ℝ η x‖ ^ 2 * (superExactShiftPow ε (-(p / 2)) (u x)) ^ 2 ≤
      Cη ^ 2 * superExactShiftPow ε (-p) (u x) := by
  have hgrad_sq_le : ‖fderiv ℝ η x‖ ^ 2 ≤ Cη ^ 2 := by
    exact sq_le_sq.mpr (by
      simp [abs_of_nonneg (norm_nonneg _), abs_of_nonneg hCη_nonneg, hη_grad_bound x])
  have hpow_sq_eq :
      (superExactShiftPow ε (-(p / 2)) (u x)) ^ 2 = superExactShiftPow ε (-p) (u x) := by
    exact superExactInv_power_sq_of_pos (u := u) (ε := ε) (p := p) (x := x) hε hux
  have hpow_nonneg : 0 ≤ superExactShiftPow ε (-p) (u x) :=
    superExactShiftPow_nonneg (ε := ε) (a := -p) hε
  rw [hpow_sq_eq]
  exact mul_le_mul_of_nonneg_right hgrad_sq_le hpow_nonneg

omit [NeZero d] in
lemma superExactFwd_termB_pointwise
    {u η : E → ℝ} {ε p Cη : ℝ} {x : E}
    (hε : 0 < ε) (hCη_nonneg : 0 ≤ Cη)
    (hη_grad_bound : ∀ x, ‖fderiv ℝ η x‖ ≤ Cη)
    (hux : 0 < u x) :
    ‖fderiv ℝ η x‖ ^ 2 * (superExactShiftPow ε (p / 2) (u x)) ^ 2 ≤
      Cη ^ 2 * superExactShiftPow ε p (u x) := by
  have hgrad_sq_le : ‖fderiv ℝ η x‖ ^ 2 ≤ Cη ^ 2 := by
    exact sq_le_sq.mpr (by
      simp [abs_of_nonneg (norm_nonneg _), abs_of_nonneg hCη_nonneg, hη_grad_bound x])
  have hpow_sq_eq :
      (superExactShiftPow ε (p / 2) (u x)) ^ 2 = superExactShiftPow ε p (u x) := by
    exact superExactFwd_power_sq_of_pos (u := u) (ε := ε) (p := p) (x := x) hε hux
  have hpow_nonneg : 0 ≤ superExactShiftPow ε p (u x) :=
    superExactShiftPow_nonneg (ε := ε) (a := p) hε
  calc
    ‖fderiv ℝ η x‖ ^ 2 * (superExactShiftPow ε (p / 2) (u x)) ^ 2
        = ‖fderiv ℝ η x‖ ^ 2 * superExactShiftPow ε p (u x) := by
            rw [hpow_sq_eq]
    _ ≤ Cη ^ 2 * superExactShiftPow ε p (u x) := by
          exact mul_le_mul_of_nonneg_right hgrad_sq_le hpow_nonneg

omit [NeZero d] in
lemma superExactFwd_boundTerm_pointwise
    {u η : E → ℝ} {ε p Cη : ℝ} {x : E}
    (hε : 0 < ε) (hp : 0 < p) (hp1 : p < 1)
    (hCη_nonneg : 0 ≤ Cη)
    (hη_grad_bound : ∀ x, ‖fderiv ℝ η x‖ ≤ Cη)
    (hux : 0 < u x) :
    ‖fderiv ℝ η x‖ ^ 2 *
        (|superExactShiftPow ε (p - 1) (u x)| ^ 2 /
          (-(deriv (superExactShiftReg ε (p - 1)) (u x)))) ≤
      (Cη ^ 2 / (1 - p)) * superExactShiftPow ε p (u x) := by
  have hgrad_sq_le : ‖fderiv ℝ η x‖ ^ 2 ≤ Cη ^ 2 := by
    exact sq_le_sq.mpr (by
      simp [abs_of_nonneg (norm_nonneg _), abs_of_nonneg hCη_nonneg, hη_grad_bound x])
  have hratio :
      |superExactShiftPow ε (p - 1) (u x)| ^ 2 /
          (-(deriv (superExactShiftReg ε (p - 1)) (u x))) =
        superExactShiftPow ε p (u x) / (1 - p) := by
    exact superExactFwd_test_ratio_of_pos (u := u) (ε := ε) (p := p) (x := x) hε hp hp1 hux
  have hpow_nonneg : 0 ≤ superExactShiftPow ε p (u x) :=
    superExactShiftPow_nonneg (ε := ε) (a := p) hε
  rw [hratio]
  have hdiv_nonneg : 0 ≤ superExactShiftPow ε p (u x) / (1 - p) := by
    exact div_nonneg hpow_nonneg (by linarith : 0 ≤ 1 - p)
  have hle :
      ‖fderiv ℝ η x‖ ^ 2 * (superExactShiftPow ε p (u x) / (1 - p)) ≤
        Cη ^ 2 * (superExactShiftPow ε p (u x) / (1 - p)) := by
    exact mul_le_mul_of_nonneg_right hgrad_sq_le hdiv_nonneg
  simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hle

omit [NeZero d] in
theorem superExactInv_termB_bound_on_ball
    {u η : E → ℝ} {ε p s Cη : ℝ}
    (hε : 0 < ε) (hp : 0 < p) (hs : 0 < s)
    (hu_pos : ∀ x ∈ Metric.ball (0 : E) s, 0 < u x)
    (hu : MemW1pWitness 2 u (Metric.ball (0 : E) s))
    (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hCη_nonneg : 0 ≤ Cη)
    (hη_grad_bound : ∀ x, ‖fderiv ℝ η x‖ ≤ Cη) :
    ∫ x in Metric.ball (0 : E) s,
        ‖fderiv ℝ η x‖ ^ 2 * (superExactShiftPow ε (-(p / 2)) (u x)) ^ 2 ∂volume ≤
      Cη ^ 2 * ∫ x in Metric.ball (0 : E) s, superExactShiftPow ε (-p) (u x) ∂volume := by
  let Ω : Set E := Metric.ball (0 : E) s
  have hpow_int :
      IntegrableOn (fun x => superExactShiftPow ε (-p) (u x)) Ω volume :=
    superExactInv_shiftPow_integrableOn_ball (u := u) (ε := ε) (p := p) (s := s)
      hε (by linarith) hs hu
  have hlhs_aemeas :
      AEMeasurable
        (fun x => ‖fderiv ℝ η x‖ ^ 2 * (superExactShiftPow ε (-(p / 2)) (u x)) ^ 2)
        (volume.restrict Ω) := by
    have hgrad_aemeas :
        AEMeasurable (fun x => ‖fderiv ℝ η x‖) (volume.restrict Ω) := by
      exact (hη.continuous_fderiv (by simp : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0)).norm.aemeasurable
    have hpow_aemeas :
        AEMeasurable (fun x => superExactShiftPow ε (-(p / 2)) (u x)) (volume.restrict Ω) := by
      exact
        superExactShiftPow_comp_aemeasurable
          (Ω := Ω) (u := u) (ε := ε) (a := -(p / 2)) hε hu
    exact ((hgrad_aemeas.pow aemeasurable_const).mul (hpow_aemeas.pow aemeasurable_const))
  have hlhs_int :
      Integrable
        (fun x => ‖fderiv ℝ η x‖ ^ 2 * (superExactShiftPow ε (-(p / 2)) (u x)) ^ 2)
        (volume.restrict Ω) := by
    refine Integrable.mono' (hpow_int.const_mul (Cη ^ 2)) hlhs_aemeas.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx
    have hux : 0 < u x := hu_pos x hx
    have hle :=
      superExactInv_termB_pointwise
        (u := u) (η := η) (ε := ε) (p := p) (Cη := Cη) (x := x)
        hε hCη_nonneg hη_grad_bound hux
    have hlhs_nonneg :
        0 ≤ ‖fderiv ℝ η x‖ ^ 2 * (superExactShiftPow ε (-(p / 2)) (u x)) ^ 2 := by
      positivity
    have hrhs_nonneg :
        0 ≤ Cη ^ 2 * superExactShiftPow ε (-p) (u x) := by
      exact mul_nonneg (sq_nonneg _) (superExactShiftPow_nonneg (ε := ε) (a := -p) hε)
    simpa [Real.norm_eq_abs, abs_of_nonneg hlhs_nonneg, abs_of_nonneg hrhs_nonneg] using hle
  have hmono :
      ∫ x, ‖fderiv ℝ η x‖ ^ 2 * (superExactShiftPow ε (-(p / 2)) (u x)) ^ 2 ∂(volume.restrict Ω) ≤
        ∫ x, Cη ^ 2 * superExactShiftPow ε (-p) (u x) ∂(volume.restrict Ω) := by
    refine integral_mono_ae hlhs_int (hpow_int.const_mul (Cη ^ 2)) ?_
    filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx
    exact
      superExactInv_termB_pointwise
        (u := u) (η := η) (ε := ε) (p := p) (Cη := Cη) (x := x)
        hε hCη_nonneg hη_grad_bound (hu_pos x hx)
  calc
    ∫ x in Ω, ‖fderiv ℝ η x‖ ^ 2 * (superExactShiftPow ε (-(p / 2)) (u x)) ^ 2 ∂volume
        = ∫ x, ‖fderiv ℝ η x‖ ^ 2 * (superExactShiftPow ε (-(p / 2)) (u x)) ^ 2
            ∂(volume.restrict Ω) := by
            rfl
    _ ≤ ∫ x, Cη ^ 2 * superExactShiftPow ε (-p) (u x) ∂(volume.restrict Ω) := hmono
    _ = Cη ^ 2 * ∫ x in Ω, superExactShiftPow ε (-p) (u x) ∂volume := by
          simp [Ω, integral_const_mul]

omit [NeZero d] in
lemma superExactInv_boundTerm_pointwise
    {u η : E → ℝ} {ε p Cη : ℝ} {x : E}
    (hε : 0 < ε) (hp : 0 < p)
    (hCη_nonneg : 0 ≤ Cη)
    (hη_grad_bound : ∀ x, ‖fderiv ℝ η x‖ ≤ Cη)
    (hux : 0 < u x) :
    ‖fderiv ℝ η x‖ ^ 2 *
        (|superExactShiftPow ε (-(1 + p)) (u x)| ^ 2 /
          (-(deriv (superExactShiftReg ε (-(1 + p))) (u x)))) ≤
      Cη ^ 2 * (superExactShiftPow ε (-p) (u x) / (1 + p)) := by
  have hgrad_sq_le : ‖fderiv ℝ η x‖ ^ 2 ≤ Cη ^ 2 := by
    exact sq_le_sq.mpr (by
      simp [abs_of_nonneg (norm_nonneg _), abs_of_nonneg hCη_nonneg, hη_grad_bound x])
  have hratio :
      |superExactShiftPow ε (-(1 + p)) (u x)| ^ 2 /
          (-(deriv (superExactShiftReg ε (-(1 + p))) (u x))) =
        superExactShiftPow ε (-p) (u x) / (1 + p) := by
    exact superExactInv_test_ratio_of_pos (u := u) (ε := ε) (p := p) (x := x) hε hp hux
  have hpow_nonneg : 0 ≤ superExactShiftPow ε (-p) (u x) :=
    superExactShiftPow_nonneg (ε := ε) (a := -p) hε
  rw [hratio]
  exact mul_le_mul_of_nonneg_right hgrad_sq_le
    (div_nonneg hpow_nonneg (by linarith : 0 ≤ 1 + p))

omit [NeZero d] in
theorem superExactInv_boundTerm_bound_on_ball
    {u η : E → ℝ} {ε p s Cη : ℝ}
    (hε : 0 < ε) (hp : 0 < p) (hs : 0 < s)
    (hu_pos : ∀ x ∈ Metric.ball (0 : E) s, 0 < u x)
    (hu : MemW1pWitness 2 u (Metric.ball (0 : E) s))
    (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hCη_nonneg : 0 ≤ Cη)
    (hη_grad_bound : ∀ x, ‖fderiv ℝ η x‖ ≤ Cη) :
    ∫ x in Metric.ball (0 : E) s,
        ‖fderiv ℝ η x‖ ^ 2 *
          (|superExactShiftPow ε (-(1 + p)) (u x)| ^ 2 /
            (-(deriv (superExactShiftReg ε (-(1 + p))) (u x)))) ∂volume ≤
      (Cη ^ 2 / (1 + p)) * ∫ x in Metric.ball (0 : E) s,
        superExactShiftPow ε (-p) (u x) ∂volume := by
  let Ω : Set E := Metric.ball (0 : E) s
  have hpow_int :
      IntegrableOn (fun x => superExactShiftPow ε (-p) (u x)) Ω volume :=
    superExactInv_shiftPow_integrableOn_ball (u := u) (ε := ε) (p := p) (s := s)
      hε (by linarith) hs hu
  have hlhs_aemeas :
      AEMeasurable
        (fun x => ‖fderiv ℝ η x‖ ^ 2 *
          (|superExactShiftPow ε (-(1 + p)) (u x)| ^ 2 /
            (-(deriv (superExactShiftReg ε (-(1 + p))) (u x)))))
        (volume.restrict Ω) := by
    have hgrad_aemeas :
        AEMeasurable (fun x => ‖fderiv ℝ η x‖) (volume.restrict Ω) := by
      exact (hη.continuous_fderiv (by simp : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0)).norm.aemeasurable
    have hpow_aemeas :
        AEMeasurable (fun x => superExactShiftPow ε (-(1 + p)) (u x)) (volume.restrict Ω) := by
      exact
        superExactShiftPow_comp_aemeasurable
          (Ω := Ω) (u := u) (ε := ε) (a := -(1 + p)) hε hu
    have hderiv_aemeas :
        AEMeasurable
          (fun x => deriv (superExactShiftReg ε (-(1 + p))) (u x))
          (volume.restrict Ω) := by
      have h1 : ContDiff ℝ 1 (superExactShiftReg ε (-(1 + p))) :=
        (superExactShiftReg_contDiff (ε := ε) (a := -(1 + p)) hε).of_le (by simp)
      exact
        h1.continuous_deriv_one.measurable.comp_aemeasurable
          hu.memLp.aestronglyMeasurable.aemeasurable
    exact
      (hgrad_aemeas.pow aemeasurable_const).mul
        ((hpow_aemeas.norm.pow aemeasurable_const).div (hderiv_aemeas.neg))
  have hlhs_int :
      Integrable
        (fun x => ‖fderiv ℝ η x‖ ^ 2 *
          (|superExactShiftPow ε (-(1 + p)) (u x)| ^ 2 /
            (-(deriv (superExactShiftReg ε (-(1 + p))) (u x)))))
        (volume.restrict Ω) := by
    refine Integrable.mono' (hpow_int.const_mul (Cη ^ 2 / (1 + p))) hlhs_aemeas.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx
    have hux : 0 < u x := hu_pos x hx
    have hle :=
      superExactInv_boundTerm_pointwise
        (u := u) (η := η) (ε := ε) (p := p) (Cη := Cη) (x := x)
        hε hp hCη_nonneg hη_grad_bound hux
    have hlhs_nonneg :
        0 ≤ ‖fderiv ℝ η x‖ ^ 2 *
          (|superExactShiftPow ε (-(1 + p)) (u x)| ^ 2 /
            (-(deriv (superExactShiftReg ε (-(1 + p))) (u x)))) := by
      have hψd_pos :
          0 < -(deriv (superExactShiftReg ε (-(1 + p))) (u x)) :=
        superExactInv_test_deriv_neg_pos (ε := ε) (p := p) (t := u x) hε hp hux
      exact mul_nonneg (sq_nonneg _) (div_nonneg (sq_nonneg _) hψd_pos.le)
    have hrhs_nonneg :
        0 ≤ (Cη ^ 2 / (1 + p)) * superExactShiftPow ε (-p) (u x) := by
      exact mul_nonneg
        (div_nonneg (sq_nonneg _) (by linarith : 0 ≤ 1 + p))
        (superExactShiftPow_nonneg (ε := ε) (a := -p) hε)
    have hle' :
        ‖fderiv ℝ η x‖ ^ 2 *
            (|superExactShiftPow ε (-(1 + p)) (u x)| ^ 2 /
              (-(deriv (superExactShiftReg ε (-(1 + p))) (u x)))) ≤
          (Cη ^ 2 / (1 + p)) * superExactShiftPow ε (-p) (u x) := by
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hle
    have hle_norm :
        ‖‖fderiv ℝ η x‖ ^ 2 *
            (|superExactShiftPow ε (-(1 + p)) (u x)| ^ 2 /
              (-(deriv (superExactShiftReg ε (-(1 + p))) (u x))))‖ ≤
          (Cη ^ 2 / (1 + p)) * superExactShiftPow ε (-p) (u x) := by
      rw [Real.norm_of_nonneg hlhs_nonneg]
      exact hle'
    exact hle_norm
  have hmono :
      ∫ x, ‖fderiv ℝ η x‖ ^ 2 *
          (|superExactShiftPow ε (-(1 + p)) (u x)| ^ 2 /
            (-(deriv (superExactShiftReg ε (-(1 + p))) (u x))))
          ∂(volume.restrict Ω) ≤
        ∫ x, (Cη ^ 2 / (1 + p)) * superExactShiftPow ε (-p) (u x)
          ∂(volume.restrict Ω) := by
    refine integral_mono_ae hlhs_int (hpow_int.const_mul (Cη ^ 2 / (1 + p))) ?_
    filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx
    have hux : 0 < u x := hu_pos x hx
    have hψd_pos :
        0 < -(deriv (superExactShiftReg ε (-(1 + p))) (u x)) :=
      superExactInv_test_deriv_neg_pos (ε := ε) (p := p) (t := u x) hε hp hux
    have hder_neg : deriv (superExactShiftReg ε (-(1 + p))) (u x) < 0 := by
      linarith
    have hpow_nonneg :
        0 ≤ superExactShiftPow ε (-(1 + p)) (u x) :=
      superExactShiftPow_nonneg (ε := ε) (a := -(1 + p)) hε
    simpa [abs_of_nonneg hpow_nonneg, abs_of_neg hder_neg,
      div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
      (superExactInv_boundTerm_pointwise
        (u := u) (η := η) (ε := ε) (p := p) (Cη := Cη) (x := x)
        hε hp hCη_nonneg hη_grad_bound hux)
  calc
    ∫ x in Ω, ‖fderiv ℝ η x‖ ^ 2 *
        (|superExactShiftPow ε (-(1 + p)) (u x)| ^ 2 /
          (-(deriv (superExactShiftReg ε (-(1 + p))) (u x)))) ∂volume
        = ∫ x, ‖fderiv ℝ η x‖ ^ 2 *
            (|superExactShiftPow ε (-(1 + p)) (u x)| ^ 2 /
              (-(deriv (superExactShiftReg ε (-(1 + p))) (u x))))
            ∂(volume.restrict Ω) := by
            rfl
    _ ≤ ∫ x, (Cη ^ 2 / (1 + p)) * superExactShiftPow ε (-p) (u x)
          ∂(volume.restrict Ω) := hmono
    _ = (Cη ^ 2 / (1 + p)) * ∫ x in Ω, superExactShiftPow ε (-p) (u x) ∂volume := by
          simp [Ω, integral_const_mul]

omit [NeZero d] in
theorem superExactFwd_boundTerm_bound_on_ball
    {u η : E → ℝ} {ε p s Cη : ℝ}
    (hε : 0 < ε) (hp : 0 < p) (hp1 : p < 1) (hs : 0 < s)
    (hu_pos : ∀ x ∈ Metric.ball (0 : E) s, 0 < u x)
    (hu : MemW1pWitness 2 u (Metric.ball (0 : E) s))
    (hpInt : IntegrableOn (fun x => |u x| ^ p) (Metric.ball (0 : E) s) volume)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hCη_nonneg : 0 ≤ Cη)
    (hη_grad_bound : ∀ x, ‖fderiv ℝ η x‖ ≤ Cη) :
    ∫ x in Metric.ball (0 : E) s,
        ‖fderiv ℝ η x‖ ^ 2 *
          (|superExactShiftPow ε (p - 1) (u x)| ^ 2 /
            (-(deriv (superExactShiftReg ε (p - 1)) (u x)))) ∂volume ≤
      (Cη ^ 2 / (1 - p)) * ∫ x in Metric.ball (0 : E) s,
        superExactShiftPow ε p (u x) ∂volume := by
  let Ω : Set E := Metric.ball (0 : E) s
  have hpow_int :
      IntegrableOn (fun x => superExactShiftPow ε p (u x)) Ω volume :=
    superExactFwd_shiftPow_integrableOn_ball (u := u) (ε := ε) (p := p) (s := s)
      hε hp hp1 hs hu_pos hu hpInt
  have hlhs_aemeas :
      AEMeasurable
        (fun x => ‖fderiv ℝ η x‖ ^ 2 *
          (|superExactShiftPow ε (p - 1) (u x)| ^ 2 /
            (-(deriv (superExactShiftReg ε (p - 1)) (u x)))))
        (volume.restrict Ω) := by
    have hgrad_aemeas :
        AEMeasurable (fun x => ‖fderiv ℝ η x‖) (volume.restrict Ω) := by
      exact (hη.continuous_fderiv (by simp : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0)).norm.aemeasurable
    have hpow_aemeas :
        AEMeasurable (fun x => superExactShiftPow ε (p - 1) (u x)) (volume.restrict Ω) := by
      exact
        superExactShiftPow_comp_aemeasurable
          (Ω := Ω) (u := u) (ε := ε) (a := p - 1) hε hu
    have hderiv_aemeas :
        AEMeasurable
          (fun x => deriv (superExactShiftReg ε (p - 1)) (u x))
          (volume.restrict Ω) := by
      have h1 : ContDiff ℝ 1 (superExactShiftReg ε (p - 1)) :=
        (superExactShiftReg_contDiff (ε := ε) (a := p - 1) hε).of_le (by simp)
      exact
        h1.continuous_deriv_one.measurable.comp_aemeasurable
          hu.memLp.aestronglyMeasurable.aemeasurable
    exact
      (hgrad_aemeas.pow aemeasurable_const).mul
        ((hpow_aemeas.norm.pow aemeasurable_const).div (hderiv_aemeas.neg))
  have hlhs_int :
      Integrable
        (fun x => ‖fderiv ℝ η x‖ ^ 2 *
          (|superExactShiftPow ε (p - 1) (u x)| ^ 2 /
            (-(deriv (superExactShiftReg ε (p - 1)) (u x)))))
        (volume.restrict Ω) := by
    refine Integrable.mono' (hpow_int.const_mul (Cη ^ 2 / (1 - p))) hlhs_aemeas.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx
    have hux : 0 < u x := hu_pos x hx
    have hle :=
      superExactFwd_boundTerm_pointwise
        (u := u) (η := η) (ε := ε) (p := p) (Cη := Cη) (x := x)
        hε hp hp1 hCη_nonneg hη_grad_bound hux
    have hlhs_nonneg :
        0 ≤ ‖fderiv ℝ η x‖ ^ 2 *
          (|superExactShiftPow ε (p - 1) (u x)| ^ 2 /
            (-(deriv (superExactShiftReg ε (p - 1)) (u x)))) := by
      have hψd_pos :
          0 < -(deriv (superExactShiftReg ε (p - 1)) (u x)) :=
        superExactFwd_test_deriv_neg_pos (ε := ε) (p := p) hε hp hp1 hux
      exact mul_nonneg (sq_nonneg _) (div_nonneg (sq_nonneg _) hψd_pos.le)
    have hrhs_nonneg :
        0 ≤ (Cη ^ 2 / (1 - p)) * superExactShiftPow ε p (u x) := by
      exact mul_nonneg
        (div_nonneg (sq_nonneg _) (by linarith : 0 ≤ 1 - p))
        (superExactShiftPow_nonneg (ε := ε) (a := p) hε)
    have hle_norm :
        ‖‖fderiv ℝ η x‖ ^ 2 *
            (|superExactShiftPow ε (p - 1) (u x)| ^ 2 /
              (-(deriv (superExactShiftReg ε (p - 1)) (u x))))‖ ≤
          (Cη ^ 2 / (1 - p)) * superExactShiftPow ε p (u x) := by
      rw [Real.norm_of_nonneg hlhs_nonneg]
      exact hle
    exact hle_norm
  have hmono :
      ∫ x, ‖fderiv ℝ η x‖ ^ 2 *
          (|superExactShiftPow ε (p - 1) (u x)| ^ 2 /
            (-(deriv (superExactShiftReg ε (p - 1)) (u x))))
          ∂(volume.restrict Ω) ≤
        ∫ x, (Cη ^ 2 / (1 - p)) * superExactShiftPow ε p (u x)
          ∂(volume.restrict Ω) := by
    refine integral_mono_ae hlhs_int (hpow_int.const_mul (Cη ^ 2 / (1 - p))) ?_
    filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx
    have hux : 0 < u x := hu_pos x hx
    have hψd_pos :
        0 < -(deriv (superExactShiftReg ε (p - 1)) (u x)) :=
      superExactFwd_test_deriv_neg_pos (ε := ε) (p := p) hε hp hp1 hux
    have hpow_nonneg :
        0 ≤ superExactShiftPow ε (p - 1) (u x) :=
      superExactShiftPow_nonneg (ε := ε) (a := p - 1) hε
    simpa [abs_of_nonneg hpow_nonneg, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
      using
        (superExactFwd_boundTerm_pointwise
          (u := u) (η := η) (ε := ε) (p := p) (Cη := Cη) (x := x)
          hε hp hp1 hCη_nonneg hη_grad_bound hux)
  calc
    ∫ x in Ω, ‖fderiv ℝ η x‖ ^ 2 *
        (|superExactShiftPow ε (p - 1) (u x)| ^ 2 /
          (-(deriv (superExactShiftReg ε (p - 1)) (u x)))) ∂volume
        = ∫ x, ‖fderiv ℝ η x‖ ^ 2 *
            (|superExactShiftPow ε (p - 1) (u x)| ^ 2 /
              (-(deriv (superExactShiftReg ε (p - 1)) (u x))))
            ∂(volume.restrict Ω) := by
            rfl
    _ ≤ ∫ x, (Cη ^ 2 / (1 - p)) * superExactShiftPow ε p (u x)
          ∂(volume.restrict Ω) := hmono
    _ = (Cη ^ 2 / (1 - p)) * ∫ x in Ω, superExactShiftPow ε p (u x) ∂volume := by
          simp [Ω, integral_const_mul]

omit [NeZero d] in
theorem superExactFwd_termB_bound_on_ball
    {u η : E → ℝ} {ε p s Cη : ℝ}
    (hε : 0 < ε) (hp : 0 < p) (hp1 : p < 1) (hs : 0 < s)
    (hu_pos : ∀ x ∈ Metric.ball (0 : E) s, 0 < u x)
    (hu : MemW1pWitness 2 u (Metric.ball (0 : E) s))
    (hpInt : IntegrableOn (fun x => |u x| ^ p) (Metric.ball (0 : E) s) volume)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hCη_nonneg : 0 ≤ Cη)
    (hη_grad_bound : ∀ x, ‖fderiv ℝ η x‖ ≤ Cη) :
    ∫ x in Metric.ball (0 : E) s, ‖fderiv ℝ η x‖ ^ 2 *
        (superExactShiftPow ε (p / 2) (u x)) ^ 2 ∂volume ≤
      Cη ^ 2 * ∫ x in Metric.ball (0 : E) s, superExactShiftPow ε p (u x) ∂volume := by
  let Ω : Set E := Metric.ball (0 : E) s
  have hpow_int :
      IntegrableOn (fun x => superExactShiftPow ε p (u x)) Ω volume :=
    superExactFwd_shiftPow_integrableOn_ball (u := u) (ε := ε) (p := p) (s := s)
      hε hp hp1 hs hu_pos hu hpInt
  have hlhs_int :
      IntegrableOn
        (fun x => ‖fderiv ℝ η x‖ ^ 2 * (superExactShiftPow ε (p / 2) (u x)) ^ 2)
        Ω volume := by
    refine Integrable.mono' (hpow_int.const_mul (Cη ^ 2)) ?_ ?_
    · exact
        (((hη.continuous_fderiv (by simp : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0)).norm.aemeasurable.pow
          aemeasurable_const).mul
          ((superExactShiftPow_comp_aemeasurable (Ω := Ω) (u := u) (ε := ε)
            (a := p / 2) hε hu).pow aemeasurable_const)).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx
      have hux : 0 < u x := hu_pos x hx
      have hlhs_nonneg :
          0 ≤ ‖fderiv ℝ η x‖ ^ 2 * (superExactShiftPow ε (p / 2) (u x)) ^ 2 := by
        positivity
      have hrhs_nonneg :
          0 ≤ Cη ^ 2 * superExactShiftPow ε p (u x) := by
        exact mul_nonneg (sq_nonneg _) (superExactShiftPow_nonneg (ε := ε) (a := p) hε)
      have hle :=
        superExactFwd_termB_pointwise (u := u) (η := η) (ε := ε) (p := p) (Cη := Cη)
          (x := x) hε hCη_nonneg hη_grad_bound hux
      rw [Real.norm_of_nonneg hlhs_nonneg]
      exact hle
  have hmono :
      ∫ x in Ω, ‖fderiv ℝ η x‖ ^ 2 *
          (superExactShiftPow ε (p / 2) (u x)) ^ 2 ∂volume ≤
        ∫ x in Ω, Cη ^ 2 * superExactShiftPow ε p (u x) ∂volume := by
    simpa [Ω] using
      integral_mono_ae (by simpa [IntegrableOn] using hlhs_int)
        (hpow_int.const_mul (Cη ^ 2)) (by
          filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx
          have hux : 0 < u x := hu_pos x hx
          exact superExactFwd_termB_pointwise
            (u := u) (η := η) (ε := ε) (p := p) (Cη := Cη) (x := x)
            hε hCη_nonneg hη_grad_bound hux)
  have hbound :
      ∫ x in Ω, ‖fderiv ℝ η x‖ ^ 2 *
          (superExactShiftPow ε (p / 2) (u x)) ^ 2 ∂volume ≤
        Cη ^ 2 * ∫ x in Ω, superExactShiftPow ε p (u x) ∂volume := by
    calc
      ∫ x in Ω, ‖fderiv ℝ η x‖ ^ 2 *
          (superExactShiftPow ε (p / 2) (u x)) ^ 2 ∂volume
          ≤ ∫ x in Ω, Cη ^ 2 * superExactShiftPow ε p (u x) ∂volume := hmono
      _ = Cη ^ 2 * ∫ x in Ω, superExactShiftPow ε p (u x) ∂volume := by
          rw [integral_const_mul]
  simpa [Ω] using hbound

omit [NeZero d] in
theorem super_norm_fderiv_eq_norm_partials
    {f : E → ℝ} {x : E} :
    ‖fderiv ℝ f x‖ =
      ‖WithLp.toLp 2
        (fun i => (fderiv ℝ f x) (EuclideanSpace.single i 1))‖ := by
  let v : E := (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ f x)
  have hv :
      v = WithLp.toLp 2
        (fun i => (fderiv ℝ f x) (EuclideanSpace.single i 1)) := by
    have hv_map : (InnerProductSpace.toDual ℝ E) v = fderiv ℝ f x := by
      simp [v]
    ext i
    calc
      v i = inner ℝ v (EuclideanSpace.single i (1 : ℝ)) := by
        simpa using
          (EuclideanSpace.inner_single_right (i := i) (a := (1 : ℝ)) v).symm
      _ = ((InnerProductSpace.toDual ℝ E) v) (EuclideanSpace.single i (1 : ℝ)) := by
        rw [InnerProductSpace.toDual_apply_apply]
      _ = (fderiv ℝ f x) (EuclideanSpace.single i (1 : ℝ)) := by
        rw [hv_map]
      _ = (WithLp.toLp 2
            (fun j => (fderiv ℝ f x) (EuclideanSpace.single j 1))) i := by
        rfl
  calc
    ‖fderiv ℝ f x‖ = ‖v‖ := by
      change ‖fderiv ℝ f x‖ = ‖(InnerProductSpace.toDual ℝ E).symm (fderiv ℝ f x)‖
      exact (((InnerProductSpace.toDual ℝ E).symm.norm_map (fderiv ℝ f x))).symm
    _ = ‖WithLp.toLp 2
        (fun i => (fderiv ℝ f x) (EuclideanSpace.single i 1))‖ := by
          rw [hv]

lemma superExactPowerCutoffWitness_norm_sq_le
    {u η : E → ℝ} {ε a s Cη : ℝ}
    (hε : 0 < ε) (ha : a < 1)
    (hu1 : MemW1pWitness 2 u (Metric.ball (0 : E) 1))
    (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hη_bound : ∀ x, |η x| ≤ 1)
    (hη_grad_bound : ∀ x, ‖fderiv ℝ η x‖ ≤ Cη)
    (hη_sub_ball : tsupport η ⊆ Metric.ball (0 : E) s)
    (x : E) :
    ‖(superExactPowerCutoffWitness (d := d) (u := u) (η := η) (ε := ε) (a := a)
      (s := s) (Cη := Cη) hε ha hu1 hη hη_bound hη_grad_bound hη_sub_ball).weakGrad x‖ ^ 2 ≤
      2 * (η x ^ 2 * (deriv (superExactShiftReg ε a) (u x)) ^ 2 * ‖hu1.weakGrad x‖ ^ 2) +
      2 * (‖fderiv ℝ η x‖ ^ 2 * (superExactShiftPow ε a (u x)) ^ 2) := by
  have hterm : ∀ i : Fin d,
      (superExactPowerCutoffWitness (d := d) (u := u) (η := η) (ε := ε) (a := a)
        (s := s) (Cη := Cη) hε ha hu1 hη hη_bound hη_grad_bound hη_sub_ball).weakGrad x i ^ 2 ≤
      2 * (η x * deriv (superExactShiftReg ε a) (u x) * hu1.weakGrad x i) ^ 2 +
      2 * ((fderiv ℝ η x) (EuclideanSpace.single i 1) *
        superExactShiftPow ε a (u x)) ^ 2 := by
    intro i
    rw [superExactPowerCutoffWitness_grad (d := d) (u := u) (η := η) (ε := ε) (a := a)
      (s := s) (Cη := Cη) hε ha hu1 hη hη_bound hη_grad_bound hη_sub_ball x i]
    nlinarith [sq_nonneg
      (η x * deriv (superExactShiftReg ε a) (u x) * hu1.weakGrad x i -
        (fderiv ℝ η x) (EuclideanSpace.single i 1) * superExactShiftPow ε a (u x))]
  rw [EuclideanSpace.norm_eq (𝕜 := ℝ),
    Real.sq_sqrt (Finset.sum_nonneg fun i _ => by positivity)]
  simp_rw [Real.norm_eq_abs, sq_abs]
  rw [EuclideanSpace.norm_eq (𝕜 := ℝ) (hu1.weakGrad x),
    Real.sq_sqrt (Finset.sum_nonneg fun i _ => by positivity)]
  simp_rw [Real.norm_eq_abs, sq_abs]
  rw [show ‖fderiv ℝ η x‖ ^ 2 = ∑ i : Fin d,
      ((fderiv ℝ η x) (EuclideanSpace.single i 1)) ^ 2 by
    rw [super_norm_fderiv_eq_norm_partials (d := d) (f := η) (x := x),
      EuclideanSpace.norm_eq (𝕜 := ℝ),
      Real.sq_sqrt (Finset.sum_nonneg fun i _ => by positivity)]
    simp_rw [Real.norm_eq_abs, sq_abs]]
  calc
    ∑ i,
        (superExactPowerCutoffWitness (d := d) (u := u) (η := η) (ε := ε) (a := a)
          (s := s) (Cη := Cη) hε ha hu1 hη hη_bound hη_grad_bound hη_sub_ball).weakGrad x i ^ 2
        ≤ ∑ i,
            (2 * (η x * deriv (superExactShiftReg ε a) (u x) * hu1.weakGrad x i) ^ 2 +
              2 * ((fderiv ℝ η x) (EuclideanSpace.single i 1) *
                superExactShiftPow ε a (u x)) ^ 2) := by
            exact Finset.sum_le_sum fun i _ => hterm i
    _ =
        2 * (η x ^ 2 * deriv (superExactShiftReg ε a) (u x) ^ 2 *
          ∑ i, hu1.weakGrad x i ^ 2) +
        2 * ((∑ i, ((fderiv ℝ η x) (EuclideanSpace.single i 1)) ^ 2) *
          superExactShiftPow ε a (u x) ^ 2) := by
          have hring : ∀ i : Fin d,
              2 * (η x * deriv (superExactShiftReg ε a) (u x) * hu1.weakGrad x i) ^ 2 +
                2 * ((fderiv ℝ η x) (EuclideanSpace.single i 1) *
                  superExactShiftPow ε a (u x)) ^ 2 =
              2 * (η x ^ 2 * deriv (superExactShiftReg ε a) (u x) ^ 2 *
                (hu1.weakGrad x i ^ 2)) +
                2 * (((fderiv ℝ η x) (EuclideanSpace.single i 1)) ^ 2 *
                  superExactShiftPow ε a (u x) ^ 2) := by
            intro i
            ring
          simp_rw [hring, Finset.sum_add_distrib, ← Finset.mul_sum]
          simp [mul_comm, mul_left_comm, mul_assoc, ← Finset.mul_sum]

/-- Squaring a bound of the form `c ≤ a^(1/2) * b^(1/2)` gives `c² ≤ a * b`. -/
theorem super_sq_le_of_le_rpow_half_mul {a b c : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (h : c ≤ a ^ ((1 : ℝ) / 2) * b ^ ((1 : ℝ) / 2)) :
    c ^ (2 : ℕ) ≤ a * b := by
  have ha_sqrt : 0 ≤ a ^ ((1 : ℝ) / 2) := Real.rpow_nonneg ha _
  have hb_sqrt : 0 ≤ b ^ ((1 : ℝ) / 2) := Real.rpow_nonneg hb _
  have hrhs_nonneg : 0 ≤ a ^ ((1 : ℝ) / 2) * b ^ ((1 : ℝ) / 2) :=
    mul_nonneg ha_sqrt hb_sqrt
  have hsq :
      c ^ (2 : ℕ) ≤ (a ^ ((1 : ℝ) / 2) * b ^ ((1 : ℝ) / 2)) ^ (2 : ℕ) :=
    sq_le_sq' (by linarith) h
  have ha2 : (a ^ ((1 : ℝ) / 2)) ^ (2 : ℕ) = a := by
    rw [← Real.rpow_natCast (a ^ ((1 : ℝ) / 2)) 2]
    rw [← Real.rpow_mul ha]
    norm_num
  have hb2 : (b ^ ((1 : ℝ) / 2)) ^ (2 : ℕ) = b := by
    rw [← Real.rpow_natCast (b ^ ((1 : ℝ) / 2)) 2]
    rw [← Real.rpow_mul hb]
    norm_num
  calc
    c ^ (2 : ℕ) ≤ (a ^ ((1 : ℝ) / 2) * b ^ ((1 : ℝ) / 2)) ^ (2 : ℕ) := hsq
    _ = a * b := by rw [mul_pow, ha2, hb2]


end DeGiorgi
