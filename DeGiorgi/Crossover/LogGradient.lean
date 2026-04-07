import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import DeGiorgi.Crossover.LocalIntegrability
import DeGiorgi.Oscillation
import DeGiorgi.SobolevChainRule
import DeGiorgi.UnitBallApproximation
import DeGiorgi.Localization
import DeGiorgi.Supersolutions

/-!
# Chapter 06: Crossover Logarithmic Gradient Layer

This module proves the logarithmic gradient bound for positive supersolutions,
which is the PDE input for the crossover estimate.
-/

noncomputable section

open MeasureTheory Metric Filter Set
open scoped ENNReal NNReal Topology RealInnerProductSpace

namespace DeGiorgi

variable {d : ℕ} [NeZero d]

local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "Cmo" =>
  ((volume.real (Metric.ball (0 : E) 1)) ^ (-(1 / 2 : ℝ)) * C_poinc_val d)

/-! ### Logarithmic Gradient Bound for Supersolutions

The key PDE step for the crossover estimate: if `u > 0` is a supersolution
on `B₁`, then `v = -log u` satisfies the weighted gradient bound
`∫ φ² |∇v|² ≤ 4Λ ∫ |∇φ|²` for every smooth cutoff `φ ∈ H₀¹(B₁)`.

Proof strategy:
1. For `ε > 0`, define `Φ_ε(t) = 1/(t+ε) - 1/ε`. Note `Φ_ε(0) = 0` and
   `|Φ_ε'(t)| ≤ 1/ε²`, so the Sobolev chain rule applies.
2. `Φ_ε ∘ u ∈ W^{1,2}` with `∇(Φ_ε ∘ u) = -∇u/(u+ε)²`.
3. Form test function `ψ_ε = φ² · (1/(u+ε) - 1/ε) + φ²/ε = φ²/(u+ε)`.
   This is nonneg and in `H₀¹(B₁)` (smooth × Sobolev product rule).
4. Supersolution: `0 ≤ ∫ ⟨A∇u, ∇ψ_ε⟩ = -∫ φ² ⟨A∇v_ε, ∇v_ε⟩ + 2∫ φ⟨A∇v_ε, ∇φ⟩`
   where `v_ε = -log(u+ε)`.
5. By Cauchy-Schwarz on the A-inner product and `⟨∇φ, A∇φ⟩ ≤ Λ|∇φ|²`:
   `∫ φ² |∇v_ε|² ≤ 4Λ ∫ |∇φ|²`.
6. Send `ε → 0` (monotone convergence). -/

-- We use Φ_ε(t) = 1/(√(t²+ε²)) - 1/ε as the regularized reciprocal.
-- This is smooth on all of ℝ (no singularity), Φ_ε(0) = 0, and |Φ_ε'| ≤ 1/ε².
-- On the positive reals, Φ_ε(t) ≈ 1/(t+ε) - 1/ε for large t/ε.
-- The exact form doesn't matter much — we only need the chain rule hypotheses
-- and the ε → 0 convergence on {u > 0}.
--
-- For the proof, the key properties are:
--   (1) Φ_ε(0) = 0
--   (2) ContDiff ℝ ⊤ Φ_ε
--   (3) |Φ_ε'| ≤ M_ε for some M_ε
-- These feed into sobolev_chain_rule / MemW1pWitness.comp_smooth_bounded.

/-- Smooth regularized reciprocal for the chain rule.

For `ε > 0`, the function `Φ_ε(t) = 1/(t+ε) - 1/ε` is smooth on `(-ε, ∞)`,
vanishes at 0, and has derivative `-1/(t+ε)²` bounded by `1/ε²`.
To get a globally smooth function (required by `sobolev_chain_rule`),
we define `Φ_ε(t) = 1/√(t²+ε²) - 1/ε` which is `C^∞(ℝ)` since `t²+ε² > 0`.
On `(0, ∞)`, it agrees with the desired approximation up to controlled error. -/
private noncomputable def recipApprox (ε : ℝ) : ℝ → ℝ :=
  fun t => 1 / Real.sqrt (t ^ 2 + ε ^ 2) - 1 / ε

private lemma recipApprox_zero {ε : ℝ} (hε : 0 < ε) : recipApprox ε 0 = 0 := by
  simp only [recipApprox]
  have : (0 : ℝ) ^ 2 + ε ^ 2 = ε ^ 2 := by ring
  rw [this, Real.sqrt_sq (le_of_lt hε)]
  simp

private lemma recipApprox_contDiff {ε : ℝ} (hε : 0 < ε) :
    ContDiff ℝ (⊤ : ℕ∞) (recipApprox ε) := by
  unfold recipApprox
  apply ContDiff.sub
  · -- 1/√(t² + ε²) is smooth since t² + ε² > 0 everywhere
    apply ContDiff.div contDiff_const
    · exact (contDiff_id.pow 2 |>.add contDiff_const).sqrt
        (fun t => by positivity)
    · intro t; exact Real.sqrt_ne_zero'.mpr (by positivity)
  · exact contDiff_const

private lemma recipApprox_deriv_bounded {ε : ℝ} (hε : 0 < ε) :
    ∃ M : ℝ, ∀ t, |deriv (recipApprox ε) t| ≤ M := by
  -- |Φ_ε'(t)| = |t| / (t² + ε²)^{3/2} ≤ 1/ε² (by AM-GM or direct bound)
  refine ⟨1 / ε ^ 2, fun t => ?_⟩
  have hpos : 0 < t ^ 2 + ε ^ 2 := by positivity
  have hsqrt_pos : 0 < Real.sqrt (t ^ 2 + ε ^ 2) := Real.sqrt_pos.mpr hpos
  have hsqrt_ne : Real.sqrt (t ^ 2 + ε ^ 2) ≠ 0 := ne_of_gt hsqrt_pos
  have hd_sum : HasDerivAt (fun t => t ^ 2 + ε ^ 2) (2 * t) t := by
    convert (hasDerivAt_pow 2 t).add (hasDerivAt_const t (ε ^ 2)) using 1; ring
  have hd_sqrt : HasDerivAt (fun t => Real.sqrt (t ^ 2 + ε ^ 2))
      (t / Real.sqrt (t ^ 2 + ε ^ 2)) t := by
    have := hd_sum.sqrt (ne_of_gt hpos)
    convert this using 1; field_simp
  have hd_inv : HasDerivAt (fun t => 1 / Real.sqrt (t ^ 2 + ε ^ 2))
      (-(t / Real.sqrt (t ^ 2 + ε ^ 2)) / (Real.sqrt (t ^ 2 + ε ^ 2)) ^ 2) t := by
    have := (hasDerivAt_const t 1).div hd_sqrt hsqrt_ne
    convert this using 1; ring
  have hd_recip : HasDerivAt (recipApprox ε)
      (-(t / Real.sqrt (t ^ 2 + ε ^ 2)) / (Real.sqrt (t ^ 2 + ε ^ 2)) ^ 2) t := by
    have := hd_inv.sub (hasDerivAt_const t (1 / ε))
    simp only [sub_zero] at this; exact this
  rw [hd_recip.deriv]
  have hsq_eq : (Real.sqrt (t ^ 2 + ε ^ 2)) ^ 2 = t ^ 2 + ε ^ 2 :=
    Real.sq_sqrt (le_of_lt hpos)
  have h_abs_le : |t| ≤ Real.sqrt (t ^ 2 + ε ^ 2) :=
    Real.abs_le_sqrt (by linarith [sq_nonneg ε])
  have hval_eq : -(t / Real.sqrt (t ^ 2 + ε ^ 2)) / (Real.sqrt (t ^ 2 + ε ^ 2)) ^ 2 =
      -(t / (Real.sqrt (t ^ 2 + ε ^ 2) * (t ^ 2 + ε ^ 2))) := by
    rw [hsq_eq]; field_simp
  rw [hval_eq, abs_neg, abs_div, abs_mul, abs_of_nonneg (le_of_lt hsqrt_pos),
    abs_of_nonneg (le_of_lt hpos)]
  calc |t| / (Real.sqrt (t ^ 2 + ε ^ 2) * (t ^ 2 + ε ^ 2))
      ≤ Real.sqrt (t ^ 2 + ε ^ 2) / (Real.sqrt (t ^ 2 + ε ^ 2) * (t ^ 2 + ε ^ 2)) :=
        div_le_div_of_nonneg_right h_abs_le (by positivity)
    _ = 1 / (t ^ 2 + ε ^ 2) := by field_simp [hsqrt_ne, ne_of_gt hpos]
    _ ≤ 1 / ε ^ 2 :=
        div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith [sq_nonneg t])

/-- Smooth regularized logarithm agreeing with `-log (t + ε) + log ε` on `t ≥ 0`.

We splice the logarithm to the affine function `-t / ε` on `(-∞, -ε / 2]`
using the same smooth transition used for `exists_smooth_recipApprox`. This
gives a globally smooth chain-rule profile with bounded derivative. -/
private lemma exists_smooth_logApprox {ε : ℝ} (hε : 0 < ε) :
    ∃ (Ψ : ℝ → ℝ),
      Ψ 0 = 0 ∧
      ContDiff ℝ (⊤ : ℕ∞) Ψ ∧
      (∃ M, ∀ t, |deriv Ψ t| ≤ M) ∧
      (∀ t, 0 ≤ t → Ψ t = -Real.log (t + ε) + Real.log ε) ∧
      (∀ t, 0 < t → deriv Ψ t = -(1 / (t + ε))) := by
  let χ : ℝ → ℝ := fun t => Real.smoothTransition (1 + (2 / ε) * t)
  let g : ℝ → ℝ := fun t => -Real.log (t + ε) + Real.log ε
  let h : ℝ → ℝ := fun t => -(t / ε)
  let Ψ : ℝ → ℝ := fun t => χ t * g t + (1 - χ t) * h t
  have hχ_one : ∀ t, 0 ≤ t → χ t = 1 := by
    intro t ht
    simp only [χ]
    apply Real.smoothTransition.one_of_one_le
    have : 0 ≤ (2 / ε) * t := mul_nonneg (by positivity) ht
    linarith
  have hχ_zero : ∀ t, t ≤ -ε / 2 → χ t = 0 := by
    intro t ht
    simp only [χ]
    apply Real.smoothTransition.zero_of_nonpos
    have hmul : (2 / ε) * t ≤ (2 / ε) * (-ε / 2) :=
      mul_le_mul_of_nonneg_left ht (by positivity)
    have hval : (2 / ε) * (-ε / 2) = -1 := by
      field_simp [hε.ne']
    have : (2 / ε) * t ≤ -1 := by
      simpa [hval] using hmul
    linarith
  have hχ_smooth : ContDiff ℝ (⊤ : ℕ∞) χ := by
    have hlin : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ => 1 + (2 / ε) * t) :=
      contDiff_const.add (contDiff_const.mul contDiff_id)
    simpa [χ] using Real.smoothTransition.contDiff.comp hlin
  have hΨ0 : Ψ 0 = 0 := by
    simp [Ψ, g, h, hχ_one 0 le_rfl]
  have hΨ_smooth : ContDiff ℝ (⊤ : ℕ∞) Ψ := by
    rw [contDiff_iff_contDiffAt]
    intro t
    by_cases ht : t < -ε / 2
    · have harg_cont : ContinuousAt (fun s : ℝ => 1 + (2 / ε) * s) t :=
        continuousAt_const.add (continuousAt_const.mul continuousAt_id)
      have harg_neg : (1 + (2 / ε) * t) < 0 := by
        have hmul : (2 / ε) * t < (2 / ε) * (-ε / 2) :=
          mul_lt_mul_of_pos_left ht (by positivity)
        have hval : (2 / ε) * (-ε / 2) = -1 := by
          field_simp [hε.ne']
        have : (2 / ε) * t < -1 := by
          simpa [hval] using hmul
        linarith
      have hev : Ψ =ᶠ[nhds t] h := by
        filter_upwards [harg_cont.eventually (Iio_mem_nhds harg_neg)] with s hs
        have hχs : χ s = 0 := by
          simp only [χ]
          exact Real.smoothTransition.zero_of_nonpos hs.le
        simp [Ψ, h, hχs]
      have hh_smooth : ContDiff ℝ (⊤ : ℕ∞) h := by
        simpa [h, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
          ((contDiff_const.mul contDiff_id) : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ => (-(1 / ε : ℝ)) * t))
      have hconst : ContDiffAt ℝ (⊤ : ℕ∞) h t := hh_smooth.contDiffAt
      exact hconst.congr_of_eventuallyEq hev
    · have ht_ge : -ε / 2 ≤ t := le_of_not_gt ht
      have htε_pos : 0 < t + ε := by
        linarith
      have hg_at : ContDiffAt ℝ (⊤ : ℕ∞) g t := by
        have harg : ContDiffAt ℝ (⊤ : ℕ∞) (fun s : ℝ => s + ε) t := by
          simpa using
            (contDiffAt_id.add contDiffAt_const :
              ContDiffAt ℝ (⊤ : ℕ∞) (fun s : ℝ => s + ε) t)
        have hlog0 : ContDiffAt ℝ (⊤ : ℕ∞) Real.log (t + ε) :=
          (Real.contDiffAt_log).2 (by simpa using ne_of_gt htε_pos)
        have hlog : ContDiffAt ℝ (⊤ : ℕ∞) (fun s : ℝ => Real.log (s + ε)) t :=
          by simpa [Function.comp] using hlog0.comp t harg
        simpa [g] using hlog.neg.add contDiffAt_const
      have hh_at : ContDiffAt ℝ (⊤ : ℕ∞) h t := by
        have hh_smooth : ContDiff ℝ (⊤ : ℕ∞) h := by
          simpa [h, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
            ((contDiff_const.mul contDiff_id) : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ => (-(1 / ε : ℝ)) * t))
        exact hh_smooth.contDiffAt
      exact (hχ_smooth.contDiffAt.mul hg_at).add
        ((contDiff_const.sub hχ_smooth).contDiffAt.mul hh_at)
  have hΨ_deriv : ∀ t, 0 < t → deriv Ψ t = -(1 / (t + ε)) := by
    intro t ht
    have hev : Ψ =ᶠ[nhds t] g := by
      apply Filter.eventuallyEq_iff_exists_mem.mpr
      refine ⟨Set.Ioi 0, Ioi_mem_nhds ht, ?_⟩
      intro s hs
      simp [Ψ, g, hχ_one s (le_of_lt hs), h]
    rw [Filter.EventuallyEq.deriv_eq hev]
    have h1 : HasDerivAt (fun s : ℝ => ε + s) 1 t := by
      convert ((hasDerivAt_const t ε).add (hasDerivAt_id t)) using 1
      ring
    have hlog : HasDerivAt (fun s : ℝ => Real.log (ε + s)) ((ε + t)⁻¹) t := by
      simpa [one_div, add_comm] using h1.log (by simpa [add_comm] using ne_of_gt (by linarith : 0 < ε + t))
    have hg : HasDerivAt g (-(1 / (t + ε))) t := by
      convert (hlog.neg.add (hasDerivAt_const t (Real.log ε))) using 1
      · ext s
        simp [g, add_comm]
      · ring
    exact hg.deriv
  have hΨ_bdd : ∃ M, ∀ t, |deriv Ψ t| ≤ M := by
    have hderiv_cont : Continuous (deriv Ψ) := by
      exact hΨ_smooth.continuous_deriv (by simp)
    obtain ⟨Mmid, hMmid⟩ := isCompact_Icc.exists_bound_of_continuousOn
      (f := deriv Ψ) (s := Set.Icc (-ε / 2) 0) hderiv_cont.continuousOn
    refine ⟨max (1 / ε) Mmid, fun t => ?_⟩
    by_cases hneg : t < -ε / 2
    · have harg_cont : ContinuousAt (fun s : ℝ => 1 + (2 / ε) * s) t :=
        continuousAt_const.add (continuousAt_const.mul continuousAt_id)
      have harg_neg : (1 + (2 / ε) * t) < 0 := by
        have hmul : (2 / ε) * t < (2 / ε) * (-ε / 2) :=
          mul_lt_mul_of_pos_left hneg (by positivity)
        have hval : (2 / ε) * (-ε / 2) = -1 := by
          field_simp [hε.ne']
        have : (2 / ε) * t < -1 := by
          simpa [hval] using hmul
        linarith
      have hev : Ψ =ᶠ[nhds t] h := by
        filter_upwards [harg_cont.eventually (Iio_mem_nhds harg_neg)] with s hs
        have hχs : χ s = 0 := by
          simp only [χ]
          exact Real.smoothTransition.zero_of_nonpos hs.le
        simp [Ψ, h, hχs]
      have hconst : deriv Ψ t = deriv h t := by
        simpa using (Filter.EventuallyEq.deriv_eq hev)
      rw [hconst]
      have hh : deriv h t = -(1 / ε) := by
        have hhd : HasDerivAt h (-(1 / ε)) t := by
          simpa [h, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
            ((hasDerivAt_id t).const_mul (-(1 / ε : ℝ)))
        exact hhd.deriv
      rw [hh, abs_neg, abs_of_pos (by positivity)]
      exact le_max_left _ _
    · by_cases hpos : 0 < t
      · rw [hΨ_deriv t hpos, abs_neg]
        have hte : 0 < t + ε := by linarith
        have hbound : |1 / (t + ε)| ≤ 1 / ε := by
          rw [abs_of_pos (one_div_pos.mpr hte)]
          exact one_div_le_one_div_of_le hε (by linarith)
        exact le_trans hbound (le_max_left _ _)
      · have ht_mem : t ∈ Set.Icc (-ε / 2) 0 := by
          constructor
          · exact le_of_not_gt hneg
          · exact le_of_not_gt hpos
        have hmid := hMmid t ht_mem
        exact le_trans (by simpa [Real.norm_eq_abs] using hmid) (le_max_right _ _)
  refine ⟨Ψ, hΨ0, hΨ_smooth, hΨ_bdd, ?_, hΨ_deriv⟩
  intro t ht
  simp [Ψ, g, hχ_one t ht]

private noncomputable def smoothLogApprox {ε : ℝ} (hε : 0 < ε) : ℝ → ℝ :=
  Classical.choose (exists_smooth_logApprox hε)

private lemma smoothLogApprox_zero {ε : ℝ} (hε : 0 < ε) :
    smoothLogApprox hε 0 = 0 :=
  (Classical.choose_spec (exists_smooth_logApprox hε)).1

private lemma smoothLogApprox_smooth {ε : ℝ} (hε : 0 < ε) :
    ContDiff ℝ (⊤ : ℕ∞) (smoothLogApprox hε) :=
  (Classical.choose_spec (exists_smooth_logApprox hε)).2.1

private lemma smoothLogApprox_deriv_bdd {ε : ℝ} (hε : 0 < ε) :
    ∃ M, ∀ t, |deriv (smoothLogApprox hε) t| ≤ M :=
  (Classical.choose_spec (exists_smooth_logApprox hε)).2.2.1

private lemma smoothLogApprox_eq {ε : ℝ} (hε : 0 < ε) :
    ∀ t, 0 ≤ t → smoothLogApprox hε t = -Real.log (t + ε) + Real.log ε :=
  (Classical.choose_spec (exists_smooth_logApprox hε)).2.2.2.1

private lemma smoothLogApprox_deriv {ε : ℝ} (hε : 0 < ε) :
    ∀ t, 0 < t → deriv (smoothLogApprox hε) t = -(1 / (t + ε)) :=
  (Classical.choose_spec (exists_smooth_logApprox hε)).2.2.2.2

/-! #### Logarithmic gradient bound

If `u > 0` satisfies `-∇·(A∇u) ≥ 0` on `Ω`, then for every smooth cutoff
`φ` supported in `Ω`:
`∫_Ω φ² |∇u|²/u² ≤ 4Λ ∫_Ω |∇φ|²`.

Equivalently, setting `v = -log u`: `∫_Ω φ² |∇v|² ≤ 4Λ ∫_Ω |∇φ|²`.

-/

/-- A globally smooth extension of `t ↦ 1/(t+ε) - 1/ε` to all of `ℝ`,
agreeing with it on `(-ε/2, ∞)` (hence on the range of any `u > 0`).
This is obtained by multiplying by a smooth bump that's 1 on `[-ε/2, ∞)`.
The key properties: `Φ(0) = 0`, `ContDiff ℝ ⊤ Φ`, `|Φ'| ≤ M_ε`, and
on `{t > 0}`: `Φ(t) = 1/(t+ε) - 1/ε` and `Φ'(t) = -1/(t+ε)²`. -/
private lemma exists_smooth_recipApprox {ε : ℝ} (hε : 0 < ε) :
    ∃ (Φ : ℝ → ℝ),
      Φ 0 = 0 ∧
      ContDiff ℝ (⊤ : ℕ∞) Φ ∧
      (∃ M, ∀ t, |deriv Φ t| ≤ M) ∧
      (∀ t, 0 ≤ t → Φ t = 1 / (t + ε) - 1 / ε) ∧
      (∀ t, 0 < t → deriv Φ t = -(1 / (t + ε) ^ 2)) := by
  let χ : ℝ → ℝ := fun t => Real.smoothTransition (1 + (2 / ε) * t)
  let g : ℝ → ℝ := fun t => 1 / (t + ε) - 1 / ε
  let Φ : ℝ → ℝ := fun t => χ t * g t
  have hχ_one : ∀ t, 0 ≤ t → χ t = 1 := by
    intro t ht
    simp only [χ]
    apply Real.smoothTransition.one_of_one_le
    have : 0 ≤ (2 / ε) * t := mul_nonneg (by positivity) ht
    linarith
  have hχ_zero : ∀ t, t ≤ -ε / 2 → χ t = 0 := by
    intro t ht
    simp only [χ]
    apply Real.smoothTransition.zero_of_nonpos
    have hmul : (2 / ε) * t ≤ (2 / ε) * (-ε / 2) :=
      mul_le_mul_of_nonneg_left ht (by positivity)
    have hval : (2 / ε) * (-ε / 2) = -1 := by
      field_simp [hε.ne']
    have : (2 / ε) * t ≤ -1 := by
      simpa [hval] using hmul
    linarith
  have hχ_smooth : ContDiff ℝ (⊤ : ℕ∞) χ := by
    have hlin : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ => 1 + (2 / ε) * t) :=
      contDiff_const.add (contDiff_const.mul contDiff_id)
    simpa [χ] using Real.smoothTransition.contDiff.comp hlin
  have hΦ0 : Φ 0 = 0 := by
    simp [Φ, g, hχ_one 0 le_rfl]
  have hΦ_smooth : ContDiff ℝ (⊤ : ℕ∞) Φ := by
    rw [contDiff_iff_contDiffAt]
    intro t
    by_cases ht : t < -ε / 2
    · have harg_cont : ContinuousAt (fun s : ℝ => 1 + (2 / ε) * s) t :=
        continuousAt_const.add (continuousAt_const.mul continuousAt_id)
      have harg_neg : (1 + (2 / ε) * t) < 0 := by
        have hmul : (2 / ε) * t < (2 / ε) * (-ε / 2) :=
          mul_lt_mul_of_pos_left ht (by positivity)
        have hval : (2 / ε) * (-ε / 2) = -1 := by
          field_simp [hε.ne']
        have : (2 / ε) * t < -1 := by
          simpa [hval] using hmul
        linarith
      have hev : Φ =ᶠ[nhds t] fun _ : ℝ => 0 := by
        filter_upwards [harg_cont.eventually (Iio_mem_nhds harg_neg)] with s hs
        have hχs : χ s = 0 := by
          simp only [χ]
          exact Real.smoothTransition.zero_of_nonpos hs.le
        simp [Φ, hχs]
      have hconst : ContDiffAt ℝ (⊤ : ℕ∞) (fun _ : ℝ => (0 : ℝ)) t := contDiffAt_const
      exact hconst.congr_of_eventuallyEq hev
    · have ht_ge : -ε / 2 ≤ t := le_of_not_gt ht
      have htε_pos : 0 < t + ε := by
        linarith
      have hg_at : ContDiffAt ℝ (⊤ : ℕ∞) g t := by
        have harg : ContDiffAt ℝ (⊤ : ℕ∞) (fun s : ℝ => s + ε) t := by
          simpa using (contDiffAt_id.add contDiffAt_const : ContDiffAt ℝ (⊤ : ℕ∞) (fun s : ℝ => s + ε) t)
        have hInv : ContDiffAt ℝ (⊤ : ℕ∞) (fun s : ℝ => 1 / (s + ε)) t :=
          (contDiffAt_const.div harg (ne_of_gt htε_pos))
        simpa [g] using hInv.sub contDiffAt_const
      exact (hχ_smooth.contDiffAt.mul hg_at)
  have hΦ_deriv : ∀ t, 0 < t → deriv Φ t = -(1 / (t + ε) ^ 2) := by
    intro t ht
    have htε : t + ε ≠ 0 := ne_of_gt (by linarith)
    have hev : Φ =ᶠ[nhds t] g := by
      apply Filter.eventuallyEq_iff_exists_mem.mpr
      refine ⟨Set.Ioi 0, Ioi_mem_nhds ht, ?_⟩
      intro s hs
      simp [Φ, hχ_one s (le_of_lt hs)]
    rw [Filter.EventuallyEq.deriv_eq hev]
    have h1 : HasDerivAt (fun s : ℝ => ε + s) 1 t := by
      convert ((hasDerivAt_const t ε).add (hasDerivAt_id t)) using 1
      ring
    have h2 : HasDerivAt (fun s : ℝ => (ε + s)⁻¹) (-1 / (ε + t) ^ 2) t := by
      exact h1.inv (by simpa [add_comm] using htε)
    have hsub : HasDerivAt g (-1 / (ε + t) ^ 2) t := by
      convert (h2.sub (hasDerivAt_const t (1 / ε))) using 1
      · ext s
        simp [g, one_div, add_comm]
      · ring
    convert hsub.deriv using 1
    ring
  have hΦ_bdd : ∃ M, ∀ t, |deriv Φ t| ≤ M := by
    have hderiv_cont : Continuous (deriv Φ) := by
      exact hΦ_smooth.continuous_deriv (by simp)
    obtain ⟨Mmid, hMmid⟩ := isCompact_Icc.exists_bound_of_continuousOn
      (f := deriv Φ) (s := Set.Icc (-ε / 2) 0) hderiv_cont.continuousOn
    refine ⟨max (1 / ε ^ 2) Mmid, fun t => ?_⟩
    by_cases hneg : t < -ε / 2
    · have harg_cont : ContinuousAt (fun s : ℝ => 1 + (2 / ε) * s) t :=
        continuousAt_const.add (continuousAt_const.mul continuousAt_id)
      have harg_neg : (1 + (2 / ε) * t) < 0 := by
        have hmul : (2 / ε) * t < (2 / ε) * (-ε / 2) :=
          mul_lt_mul_of_pos_left hneg (by positivity)
        have hval : (2 / ε) * (-ε / 2) = -1 := by
          field_simp [hε.ne']
        have : (2 / ε) * t < -1 := by
          simpa [hval] using hmul
        linarith
      have hev : Φ =ᶠ[nhds t] fun _ : ℝ => 0 := by
        filter_upwards [harg_cont.eventually (Iio_mem_nhds harg_neg)] with s hs
        have hχs : χ s = 0 := by
          simp only [χ]
          exact Real.smoothTransition.zero_of_nonpos hs.le
        simp [Φ, hχs]
      have hzero : deriv Φ t = 0 := by
        have hEq : deriv Φ t = deriv (fun _ : ℝ => (0 : ℝ)) t := by
          simpa using (Filter.EventuallyEq.deriv_eq hev)
        simpa using hEq
      rw [hzero]
      simpa using le_trans (show 0 ≤ 1 / ε ^ 2 by positivity) (le_max_left _ _)
    · by_cases hpos : 0 < t
      · rw [hΦ_deriv t hpos, abs_neg]
        have habs : |1 / (t + ε) ^ 2| = 1 / (t + ε) ^ 2 := by
          apply abs_of_nonneg
          positivity
        rw [habs]
        have hsq_le : ε ^ 2 ≤ (t + ε) ^ 2 := by
          nlinarith
        have hεsq_pos : 0 < ε ^ 2 := by positivity
        exact le_trans (one_div_le_one_div_of_le hεsq_pos hsq_le) (le_max_left _ _)
      · have ht_mem : t ∈ Set.Icc (-ε / 2) 0 := by
          constructor
          · exact le_of_not_gt hneg
          · exact le_of_not_gt hpos
        have hmid := hMmid t ht_mem
        exact le_trans (by simpa [Real.norm_eq_abs] using hmid) (le_max_right _ _)
  refine ⟨Φ, hΦ0, hΦ_smooth, hΦ_bdd, ?_, hΦ_deriv⟩
  · intro t ht
    simp [Φ, g, hχ_one t ht, one_div]

/-- Sobolev chain rule packaged as a `MemW1pWitness`.

If `Φ : ℝ → ℝ` is smooth with `Φ(0) = 0` and bounded derivative, and
`u ∈ W^{1,2}(Ω)`, then `Φ ∘ u ∈ W^{1,2}(Ω)` with weak gradient
`Φ'(u) · ∇u`. -/
private noncomputable def comp_smooth_bounded_witness
    {Ω : Set E} (hΩ : IsOpen Ω)
    {u : E → ℝ} (hu : MemW1pWitness 2 u Ω)
    (Φ : ℝ → ℝ) (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (hΦ0 : Φ 0 = 0)
    (hΦ'_bdd : ∃ M, ∀ t, |deriv Φ t| ≤ M) :
    MemW1pWitness 2 (fun x => Φ (u x)) Ω := by
  classical
  let M : ℝ := Classical.choose hΦ'_bdd
  have hM : ∀ t, |deriv Φ t| ≤ M := Classical.choose_spec hΦ'_bdd
  have hM_nonneg : 0 ≤ M := le_trans (abs_nonneg _) (hM 0)
  have hΦ_lip : LipschitzWith ⟨M, hM_nonneg⟩ Φ :=
    lipschitzWith_of_nnnorm_deriv_le (hΦ.differentiable (by simp)) (fun t => by
      simp only [← NNReal.coe_le_coe, NNReal.coe_mk, coe_nnnorm]
      exact (Real.norm_eq_abs _).symm ▸ hM t)
  have hΦ_abs_le : ∀ t, |Φ t| ≤ M * |t| := by
    intro t; have ht := hΦ_lip.dist_le_mul t 0
    simpa [Real.dist_eq, hΦ0, Real.norm_eq_abs] using ht
  exact
    { memLp := by
        refine MemLp.of_le_mul (g := u) (c := M) hu.memLp ?_ ?_
        · exact hΦ.continuous.comp_aestronglyMeasurable hu.memLp.aestronglyMeasurable
        · exact .of_forall fun x => by
            rw [Real.norm_eq_abs]
            simpa [Real.norm_eq_abs, abs_mul, abs_of_nonneg hM_nonneg] using hΦ_abs_le (u x)
      weakGrad := fun x => WithLp.toLp 2 fun i => deriv Φ (u x) * hu.weakGrad x i
      weakGrad_component_memLp := by
        intro i
        refine MemLp.of_le_mul (g := fun x => hu.weakGrad x i) (c := M)
          (hu.weakGrad_component_memLp i) ?_ ?_
        · exact (((hΦ.continuous_deriv (by simp)).comp_aestronglyMeasurable
              hu.memLp.aestronglyMeasurable).mul
              (hu.weakGrad_component_memLp i).aestronglyMeasurable)
        · exact .of_forall fun x => by
            calc ‖deriv Φ (u x) * hu.weakGrad x i‖
                = |deriv Φ (u x)| * ‖hu.weakGrad x i‖ := by rw [norm_mul, Real.norm_eq_abs]
              _ ≤ M * ‖hu.weakGrad x i‖ := by gcongr; exact hM (u x)
      isWeakGrad := by
        intro i
        simpa [HasWeakPartialDeriv, HasWeakPartialDeriv'] using
          sobolev_chain_rule (d := d) hΩ
            (hwd := hu.isWeakGrad i) (hu := hu.memW1p)
            (hg_Lp := hu.weakGrad_component_memLp i)
            (Φ := Φ) hΦ hΦ0 hΦ'_bdd }

/-- The smooth chain-rule regularization used to represent
`-log (u + ε) + log ε` inside Sobolev arguments. -/
noncomputable def regularizedLogFun
    {u : E → ℝ} {ε : ℝ} (hε : 0 < ε) : E → ℝ :=
  fun x => smoothLogApprox hε (u x)

/-- The chain-rule witness for the regularized logarithm. -/
noncomputable def regularizedLogWitness
    {Ω : Set E} (hΩ : IsOpen Ω)
    {u : E → ℝ}
    (_hu_pos : ∀ x ∈ Ω, 0 < u x)
    (hw_u : MemW1pWitness 2 u Ω)
    {ε : ℝ} (hε : 0 < ε) :
    MemW1pWitness 2 (regularizedLogFun (u := u) hε) Ω :=
  comp_smooth_bounded_witness hΩ hw_u (smoothLogApprox hε)
    (smoothLogApprox_smooth hε) (smoothLogApprox_zero hε) (smoothLogApprox_deriv_bdd hε)

omit [NeZero d] in
theorem regularizedLogFun_eq_ae
    {Ω : Set E} (hΩ : IsOpen Ω)
    {u : E → ℝ}
    (hu_pos : ∀ x ∈ Ω, 0 < u x)
    {ε : ℝ} (hε : 0 < ε) :
    regularizedLogFun (u := u) hε =ᵐ[volume.restrict Ω]
      (fun x => -Real.log (u x + ε) + Real.log ε) := by
  filter_upwards [ae_restrict_mem hΩ.measurableSet] with x hx
  simp [regularizedLogFun, smoothLogApprox_eq hε (u x) (le_of_lt (hu_pos x hx))]

theorem regularizedLogWitness_grad_ae
    {Ω : Set E} (hΩ : IsOpen Ω)
    {u : E → ℝ}
    (hu_pos : ∀ x ∈ Ω, 0 < u x)
    (hw_u : MemW1pWitness 2 u Ω)
    {ε : ℝ} (hε : 0 < ε) :
    let hw_v := regularizedLogWitness (Ω := Ω) hΩ hu_pos hw_u hε
    ∀ᵐ x ∂(volume.restrict Ω), ∀ i : Fin d,
      hw_v.weakGrad x i = -(1 / (u x + ε)) * hw_u.weakGrad x i := by
  intro hw_v
  filter_upwards [ae_restrict_mem hΩ.measurableSet] with x hx
  intro i
  have hux : 0 < u x := hu_pos x hx
  subst hw_v
  calc
    (regularizedLogWitness (Ω := Ω) hΩ hu_pos hw_u hε).weakGrad x i =
        deriv (smoothLogApprox hε) (u x) * hw_u.weakGrad x i := by
      unfold regularizedLogWitness
      simp [comp_smooth_bounded_witness]
    _ = -(1 / (u x + ε)) * hw_u.weakGrad x i := by
      rw [smoothLogApprox_deriv hε (u x) hux]

theorem regularizedLogWitness_grad
    {Ω : Set E} (hΩ : IsOpen Ω)
    {u : E → ℝ}
    (hu_pos : ∀ x ∈ Ω, 0 < u x)
    (hw_u : MemW1pWitness 2 u Ω)
    {ε : ℝ} (hε : 0 < ε) :
    let hw_v := regularizedLogWitness (Ω := Ω) hΩ hu_pos hw_u hε
    ∀ x ∈ Ω, ∀ i : Fin d,
      hw_v.weakGrad x i = -(1 / (u x + ε)) * hw_u.weakGrad x i := by
  intro hw_v x hx i
  have hux : 0 < u x := hu_pos x hx
  subst hw_v
  calc
    (regularizedLogWitness (Ω := Ω) hΩ hu_pos hw_u hε).weakGrad x i =
        deriv (smoothLogApprox hε) (u x) * hw_u.weakGrad x i := by
      unfold regularizedLogWitness
      simp [comp_smooth_bounded_witness]
    _ = -(1 / (u x + ε)) * hw_u.weakGrad x i := by
      rw [smoothLogApprox_deriv hε (u x) hux]

private theorem build_test_function_eps
    {Ω : Set E} (hΩ : IsOpen Ω)
    {u : E → ℝ}
    (hu_pos : ∀ x ∈ Ω, 0 < u x)
    (hw_u : MemW1pWitness 2 u Ω)
    {φ : E → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφ_cs : HasCompactSupport φ) (hφ_sub : tsupport φ ⊆ Ω)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (ψ : E → ℝ) (hw_ψ : MemW1pWitness 2 ψ Ω),
      MemH01 ψ Ω ∧
      (∀ x, 0 ≤ ψ x) ∧
      (∀ᵐ x ∂(volume.restrict Ω), ∀ i : Fin d,
        hw_ψ.weakGrad x i =
          2 * φ x * (fderiv ℝ φ x) (EuclideanSpace.single i 1) / (u x + ε) -
          φ x ^ 2 * hw_u.weakGrad x i / (u x + ε) ^ 2) := by
  -- Get the smooth extension Φ with Φ(t) = 1/(t+ε) - 1/ε for t ≥ 0.
  obtain ⟨Φ, hΦ0, hΦ_smooth, hΦ'_bdd, hΦ_val, hΦ_deriv⟩ := exists_smooth_recipApprox hε
  let hw_Φu := comp_smooth_bounded_witness hΩ hw_u Φ hΦ_smooth hΦ0 hΦ'_bdd
  -- φ² is smooth, bounded (compact support), with bounded gradient.
  have hφsq : ContDiff ℝ (⊤ : ℕ∞) (fun x => φ x ^ 2) := hφ.pow 2
  -- φ² is bounded: |φ²(x)| ≤ C₀
  have hCφ_sq : ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ x, |φ x ^ 2| ≤ C₀ := by
    obtain ⟨Cφ, hCφ⟩ := hφ_cs.exists_bound_of_continuous hφ.continuous
    refine ⟨Cφ ^ 2, by positivity, fun x => ?_⟩
    rw [abs_of_nonneg (sq_nonneg _)]
    have h1 : |φ x| ≤ Cφ := (Real.norm_eq_abs (φ x)).symm ▸ hCφ x
    calc φ x ^ 2 = |φ x| ^ 2 := (sq_abs _).symm
      _ ≤ Cφ ^ 2 := by nlinarith [abs_nonneg (φ x)]
  obtain ⟨C₀, hC₀_nn, hC₀⟩ := hCφ_sq
  -- ‖∇(φ²)‖ bounded: ‖∇(φ²)(x)‖ ≤ C₁
  have hφsq_grad_bdd : ∃ C₁ : ℝ, 0 ≤ C₁ ∧ ∀ x, ‖fderiv ℝ (fun x => φ x ^ 2) x‖ ≤ C₁ := by
    obtain ⟨Cφ', hCφ'⟩ := hφ_cs.exists_bound_of_continuous hφ.continuous
    obtain ⟨Cg, hCg⟩ := (hφ_cs.fderiv (𝕜 := ℝ)).exists_bound_of_continuous
      (hφ.continuous_fderiv (by simp))
    have hCφ'_nn : 0 ≤ Cφ' := le_trans (norm_nonneg _) (hCφ' 0)
    have hCg_nn : 0 ≤ Cg := le_trans (norm_nonneg _) (hCg 0)
    refine ⟨2 * Cφ' * Cg, by positivity, fun x => ?_⟩
    -- ‖fderiv(φ²)(x)‖ ≤ 2|φ(x)|·‖fderiv(φ)(x)‖ ≤ 2·Cφ'·Cg
    have hφ_diff : Differentiable ℝ φ := hφ.differentiable (by simp)
    -- Get HasFDerivAt for the product φ·φ at x
    have hfd_x : HasFDerivAt φ (fderiv ℝ φ x) x := hφ_diff.differentiableAt.hasFDerivAt
    have hfd_mul : HasFDerivAt (fun y => φ y * φ y)
        (φ x • fderiv ℝ φ x + φ x • fderiv ℝ φ x) x := hfd_x.mul hfd_x
    have hsq_eq : (fun y => φ y ^ 2) = (fun y => φ y * φ y) := by ext; ring
    have hfderiv_sq : fderiv ℝ (fun x => φ x ^ 2) x =
        φ x • fderiv ℝ φ x + φ x • fderiv ℝ φ x := by
      rw [hsq_eq]; exact hfd_mul.fderiv
    rw [hfderiv_sq]
    calc ‖φ x • fderiv ℝ φ x + φ x • fderiv ℝ φ x‖
        ≤ ‖φ x • fderiv ℝ φ x‖ + ‖φ x • fderiv ℝ φ x‖ := norm_add_le _ _
      _ = 2 * (‖φ x‖ * ‖fderiv ℝ φ x‖) := by rw [norm_smul]; ring
      _ ≤ 2 * (Cφ' * Cg) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul (hCφ' x) (hCg x) (norm_nonneg _) hCφ'_nn) (by norm_num)
      _ = 2 * Cφ' * Cg := by ring
  obtain ⟨C₁, hC₁_nn, hC₁⟩ := hφsq_grad_bdd
  let hw_prod := hw_Φu.mul_smooth_bounded_p (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ
    hφsq hC₀_nn hC₁_nn hC₀ hC₁
  set f_scaled := fun x => (1 / ε) * φ x ^ 2
  have hf_smooth : ContDiff ℝ (⊤ : ℕ∞) f_scaled := contDiff_const.mul hφsq
  have hf_cs : HasCompactSupport f_scaled := by
    rw [HasCompactSupport] at hφ_cs ⊢
    exact hφ_cs.of_isClosed_subset isClosed_closure (closure_mono (fun x hx => by
      simp only [Function.mem_support, f_scaled] at hx
      exact Function.mem_support.mpr (fun h => by simp [h] at hx)))
  set ψ := fun x => φ x ^ 2 * Φ (u x) + f_scaled x
  -- On Ω: ψ(x) = φ(x)²·(1/(u(x)+ε) - 1/ε) + φ(x)²/ε = φ(x)²/(u(x)+ε).
  have hψ_eq : ∀ x ∈ Ω, ψ x = φ x ^ 2 / (u x + ε) := by
    intro x hx; simp only [ψ, f_scaled]
    rw [hΦ_val (u x) (le_of_lt (hu_pos x hx))]
    field_simp; ring
  -- Nonnegativity
  have hψ_nn : ∀ x, 0 ≤ ψ x := by
    intro x
    by_cases hx : x ∈ Ω
    · rw [hψ_eq x hx]; exact div_nonneg (sq_nonneg _) (by linarith [hu_pos x hx])
    · have hnt : x ∉ tsupport φ := fun h => hx (hφ_sub h)
      have hφ0 : φ x = 0 := by
        by_contra h
        exact hnt (subset_tsupport φ (Function.mem_support.mpr h))
      simp [ψ, f_scaled, hφ0]
  -- The combined MemW1pWitness and H₀¹ membership, plus gradient formula.
  -- hw_prod has gradient: φ²·(Φ'(u)·∇u_i) + (∂ᵢφ²)·Φ(u)
  -- hw_f has gradient: (1/ε)·∂ᵢ(φ²)
  -- Sum gradient: φ²·Φ'(u)·∇u_i + (∂ᵢφ²)·(Φ(u) + 1/ε)
  -- On Ω where u > 0: Φ'(u) = -1/(u+ε)², Φ(u) + 1/ε = 1/(u+ε).
  -- So: -φ²∇u_i/(u+ε)² + 2φ(∂ᵢφ)/(u+ε). ✓
  --
  -- H₀¹: both terms are H₀¹ (first from chain rule approx, second from smooth cs),
  -- sum is H₀¹ by MemW01p.add.
  have hφsq_sub : tsupport (fun x => φ x ^ 2) ⊆ Ω := by
    simpa [pow_two] using
      ((tsupport_mul_subset_left :
        tsupport (fun x => φ x * φ x) ⊆ tsupport φ).trans hφ_sub)
  have hf_sub : tsupport f_scaled ⊆ Ω := by
    dsimp [f_scaled]
    exact (tsupport_smul_subset_right (fun _ : E => 1 / ε) (fun x => φ x ^ 2)).trans hφsq_sub
  let hw_f_univ : MemW1pWitness 2 f_scaled Set.univ :=
    MemW1pWitness.of_contDiff_hasCompactSupport (p := 2) hf_smooth hf_cs
  let hw_f : MemW1pWitness 2 f_scaled Ω :=
    hw_f_univ.restrict hΩ (by intro x hx; simp)
  have hprod_cs : HasCompactSupport (fun x => φ x ^ 2 * Φ (u x)) := by
    simpa [pow_two, mul_assoc] using
      hφ_cs.mul_right (f' := fun x => φ x * Φ (u x))
  have hprod_sub : tsupport (fun x => φ x ^ 2 * Φ (u x)) ⊆ Ω := by
    exact (tsupport_mul_subset_left :
      tsupport (fun x => φ x ^ 2 * Φ (u x)) ⊆ tsupport (fun x => φ x ^ 2)).trans hφsq_sub
  have hprod_memH01 : MemH01 (fun x => φ x ^ 2 * Φ (u x)) Ω := by
    have hprod_memW1p : MemW1p (ENNReal.ofReal 2) (fun x => φ x ^ 2 * Φ (u x)) Ω := by
      simpa using hw_prod.memW1p
    simpa using
      (memW01p_of_memW1p_of_tsupport_subset
        (d := d) hΩ (p := 2) (by norm_num : (1 : ℝ) < 2)
        hprod_memW1p hprod_cs hprod_sub)
  have hf_memH01 : MemH01 f_scaled Ω := by
    exact memW01p_of_contDiff_hasCompactSupport_subset hΩ hf_smooth hf_cs hf_sub
  let hw_ψ : MemW1pWitness 2 ψ Ω := hw_prod.add hw_f
  have hψ_memH01 : MemH01 ψ Ω := by
    simpa [ψ] using MemW01p.add hprod_memH01 hf_memH01
  have hφ_diff : Differentiable ℝ φ := hφ.differentiable (by simp)
  have hφsq_deriv :
      ∀ x (i : Fin d),
        (fderiv ℝ (fun y => φ y ^ 2) x) (EuclideanSpace.single i 1) =
          2 * φ x * (fderiv ℝ φ x) (EuclideanSpace.single i 1) := by
    intro x i
    have hfd_x : HasFDerivAt φ (fderiv ℝ φ x) x := (hφ_diff x).hasFDerivAt
    have hfd_mul :
        HasFDerivAt (fun y => φ y * φ y)
          (φ x • fderiv ℝ φ x + φ x • fderiv ℝ φ x) x := hfd_x.mul hfd_x
    have hEq : (fun y => φ y ^ 2) = (fun y => φ y * φ y) := by
      ext y
      ring
    rw [hEq, hfd_mul.fderiv]
    simp [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    ring
  refine ⟨ψ, hw_ψ, hψ_memH01, hψ_nn, ?_⟩
  filter_upwards [ae_restrict_mem hΩ.measurableSet] with x hxΩ
  intro i
  have hu_posx : 0 < u x := hu_pos x hxΩ
  have hu_eps_ne : u x + ε ≠ 0 := by linarith
  have hprod_grad :
      hw_prod.weakGrad x i =
        φ x ^ 2 * (deriv Φ (u x) * hw_u.weakGrad x i) +
          (fderiv ℝ (fun y => φ y ^ 2) x) (EuclideanSpace.single i 1) * Φ (u x) := by
    simp [hw_prod, hw_Φu, MemW1pWitness.mul_smooth_bounded_p,
      comp_smooth_bounded_witness, smul_eq_mul,
      mul_left_comm, mul_comm]
  have hf_grad :
      hw_f.weakGrad x i =
        (fderiv ℝ f_scaled x) (EuclideanSpace.single i 1) := by
    simp [hw_f, hw_f_univ, MemW1pWitness.restrict,
      MemW1pWitness.of_contDiff_hasCompactSupport]
  have hf_scaled_deriv :
      (fderiv ℝ f_scaled x) (EuclideanSpace.single i 1) =
        (1 / ε) * (fderiv ℝ (fun y => φ y ^ 2) x) (EuclideanSpace.single i 1) := by
    have hfd_sq :
        HasFDerivAt (fun y => φ y ^ 2) (fderiv ℝ (fun y => φ y ^ 2) x) x :=
      (hφsq.differentiable (by simp) x).hasFDerivAt
    have hfd_scaled :
        HasFDerivAt f_scaled
          ((1 / ε) • fderiv ℝ (fun y => φ y ^ 2) x) x := by
      simpa [f_scaled] using (hasFDerivAt_const (1 / ε) x).mul hfd_sq
    rw [hfd_scaled.fderiv]
    simp [smul_eq_mul]
  calc
    hw_ψ.weakGrad x i = hw_prod.weakGrad x i + hw_f.weakGrad x i := by
      simp [hw_ψ, MemW1pWitness.add]
    _ = φ x ^ 2 * (deriv Φ (u x) * hw_u.weakGrad x i) +
          (fderiv ℝ (fun y => φ y ^ 2) x) (EuclideanSpace.single i 1) * Φ (u x) +
          (fderiv ℝ f_scaled x) (EuclideanSpace.single i 1) := by
            rw [hprod_grad, hf_grad]
    _ = φ x ^ 2 * (-(1 / (u x + ε) ^ 2) * hw_u.weakGrad x i) +
          (2 * φ x * (fderiv ℝ φ x) (EuclideanSpace.single i 1)) *
            (1 / (u x + ε) - 1 / ε) +
          (1 / ε) * (2 * φ x * (fderiv ℝ φ x) (EuclideanSpace.single i 1)) := by
            rw [hΦ_deriv (u x) hu_posx, hΦ_val (u x) (le_of_lt hu_posx),
              hφsq_deriv x i, hf_scaled_deriv, hφsq_deriv x i]
    _ = 2 * φ x * (fderiv ℝ φ x) (EuclideanSpace.single i 1) / (u x + ε) -
          φ x ^ 2 * hw_u.weakGrad x i / (u x + ε) ^ 2 := by
            field_simp [hε.ne', hu_eps_ne]
            ring

/-- **Step (b)**: Supersolution identity for the test function `φ²/(u+ε)`.

Testing the supersolution `0 ≤ ∫ ⟨A∇u, ∇ψ_ε⟩` and expanding gives `Q ≤ 2X`
where `Q = ∫ φ²/(u+ε)² ⟨∇u, A∇u⟩` and `X = ∫ φ/(u+ε) ⟨∇φ, A∇u⟩`. -/
private theorem supersolution_energy_identity_eps
    {Ω : Set E} (hΩ : IsOpen Ω)
    (A : EllipticCoeff d Ω)
    {u : E → ℝ}
    (hu_pos : ∀ x ∈ Ω, 0 < u x)
    (hsuper : IsSupersolution A u)
    (hw_u : MemW1pWitness 2 u Ω)
    {φ : E → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφ_cs : HasCompactSupport φ) (hφ_sub : tsupport φ ⊆ Ω)
    {ε : ℝ} (hε : 0 < ε) :
    -- Q ≤ 2X (supersolution + energy identity expansion)
    ∫ x in Ω, φ x ^ 2 / (u x + ε) ^ 2 *
      @inner ℝ E _ (hw_u.weakGrad x) (matMulE (A.a x) (hw_u.weakGrad x)) ≤
    2 * ∫ x in Ω, φ x / (u x + ε) *
      @inner ℝ E _ (WithLp.toLp 2
        (fun i => (fderiv ℝ φ x) (EuclideanSpace.single i 1)))
        (matMulE (A.a x) (hw_u.weakGrad x)) := by
  obtain ⟨ψ, hw_ψ, hψ_memH01, hψ_nn, hgrad_ψ⟩ :=
    build_test_function_eps hΩ hu_pos hw_u hφ hφ_cs hφ_sub hε
  let gradφ : E → E := fun x =>
    WithLp.toLp 2 fun i => (fderiv ℝ φ x) (EuclideanSpace.single i 1)
  have hgrad_vec :
      ∀ᵐ x ∂(volume.restrict Ω),
        hw_ψ.weakGrad x =
          (2 * φ x / (u x + ε)) • gradφ x +
            (-(φ x ^ 2 / (u x + ε) ^ 2)) • hw_u.weakGrad x := by
    filter_upwards [hgrad_ψ] with x hx
    ext i
    calc
      hw_ψ.weakGrad x i
          = 2 * φ x * (fderiv ℝ φ x) (EuclideanSpace.single i 1) / (u x + ε) -
              φ x ^ 2 * hw_u.weakGrad x i / (u x + ε) ^ 2 := hx i
      _ = (2 * φ x / (u x + ε)) * gradφ x i +
            (-(φ x ^ 2 / (u x + ε) ^ 2)) * hw_u.weakGrad x i := by
              simp [gradφ]
              ring
      _ = ((2 * φ x / (u x + ε)) • gradφ x +
            (-(φ x ^ 2 / (u x + ε) ^ 2)) • hw_u.weakGrad x) i := by
              simp [smul_eq_mul]
  have htest : 0 ≤ bilinFormOfCoeff A hw_u hw_ψ := by
    exact hsuper.2 hw_u ψ hψ_memH01 hw_ψ hψ_nn
  have hu_eps_aemeas : AEMeasurable (fun x => u x + ε) (volume.restrict Ω) := by
    exact ((continuous_id.add continuous_const).comp_aestronglyMeasurable
      hw_u.memLp.aestronglyMeasurable).aemeasurable
  have hweight_aemeas : AEMeasurable (fun x => φ x / (u x + ε)) (volume.restrict Ω) := by
    exact (hφ.continuous.aestronglyMeasurable.aemeasurable.div hu_eps_aemeas)
  obtain ⟨Cφ, hCφ⟩ := hφ_cs.exists_bound_of_continuous hφ.continuous
  have hCφ_nonneg : 0 ≤ Cφ := le_trans (norm_nonneg _) (hCφ (0 : E))
  have hweight_bound : ∀ x, |φ x / (u x + ε)| ≤ Cφ / ε := by
    intro x
    by_cases hx : x ∈ Ω
    · have hu_eps_pos : 0 < u x + ε := by linarith [hu_pos x hx, hε]
      have hnum : |φ x| ≤ Cφ := (Real.norm_eq_abs (φ x)).symm ▸ hCφ x
      rw [abs_div, abs_of_nonneg hu_eps_pos.le]
      have hε_le : ε ≤ u x + ε := by linarith [hu_pos x hx]
      have hgoal : |φ x| / (u x + ε) ≤ Cφ / ε := by
        refine le_trans ?_ (div_le_div_of_nonneg_right hnum hε.le)
        exact div_le_div_of_nonneg_left (abs_nonneg _) hε hε_le
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hgoal
    · have hφ0 : φ x = 0 := by
        by_contra h
        exact hx (hφ_sub (subset_tsupport φ (Function.mem_support.mpr h)))
      have hnonneg : 0 ≤ Cφ / ε := div_nonneg hCφ_nonneg hε.le
      simpa [hφ0] using hnonneg
  let hφ_test : IsSmoothTestOn Ω φ := ⟨hφ, hφ_cs, hφ_sub⟩
  let hw_φ : MemW1pWitness 2 φ Ω := smoothTestWitness hΩ hφ_test
  have hX0_int :
      Integrable (fun x => (φ x / (u x + ε)) *
        @inner ℝ E _ (gradφ x) (matMulE (A.a x) (hw_u.weakGrad x))) (volume.restrict Ω) := by
    have hbase :
        Integrable (fun x => φ x / (u x + ε) *
          bilinFormIntegrandOfCoeff A hw_u hw_φ x) (volume.restrict Ω) := by
      refine (integrable_bilinFormIntegrandOfCoeff A hw_u hw_φ).bdd_mul
        (c := Cφ / ε) hweight_aemeas.aestronglyMeasurable ?_
      exact Filter.Eventually.of_forall hweight_bound
    convert hbase using 1
    ext x
    rw [bilinFormIntegrandOfCoeff, real_inner_comm]
    simp [hw_φ, smoothTestWitness, smoothGradField, gradφ]
  have hX_int :
      Integrable (fun x => 2 * ((φ x / (u x + ε)) *
        @inner ℝ E _ (gradφ x) (matMulE (A.a x) (hw_u.weakGrad x)))) (volume.restrict Ω) := by
    exact hX0_int.const_mul 2
  have hweight_sq_meas :
      AEStronglyMeasurable (fun x => (φ x / (u x + ε)) ^ 2) (volume.restrict Ω) := by
    exact (hweight_aemeas.pow_const 2).aestronglyMeasurable
  have hweight_sq_bound : ∀ x, |(φ x / (u x + ε)) ^ 2| ≤ Cφ ^ 2 / ε ^ 2 := by
    intro x
    have hx := hweight_bound x
    have hnonneg : 0 ≤ Cφ / ε := div_nonneg hCφ_nonneg hε.le
    calc
      |(φ x / (u x + ε)) ^ 2| = |φ x / (u x + ε)| ^ 2 := by rw [abs_pow]
      _ ≤ (Cφ / ε) ^ 2 := by nlinarith [hx, abs_nonneg (φ x / (u x + ε)), hnonneg]
      _ = Cφ ^ 2 / ε ^ 2 := by ring
  have hQ_int :
      Integrable (fun x => φ x ^ 2 / (u x + ε) ^ 2 *
        @inner ℝ E _ (hw_u.weakGrad x) (matMulE (A.a x) (hw_u.weakGrad x))) (volume.restrict Ω) := by
    have hbase :=
      integrable_bounded_mul_bilinFormIntegrand A hw_u hweight_sq_meas hweight_sq_bound
    convert hbase using 1
    ext x
    rw [bilinFormIntegrandOfCoeff, real_inner_comm]
    rw [div_pow]
  have h_expand_ae :
      ∀ᵐ x ∂(volume.restrict Ω),
        bilinFormIntegrandOfCoeff A hw_u hw_ψ x =
          2 * (φ x / (u x + ε)) *
            @inner ℝ E _ (gradφ x) (matMulE (A.a x) (hw_u.weakGrad x)) -
          φ x ^ 2 / (u x + ε) ^ 2 *
            @inner ℝ E _ (hw_u.weakGrad x) (matMulE (A.a x) (hw_u.weakGrad x)) := by
    filter_upwards [hgrad_vec] with x hx
    rw [bilinFormIntegrandOfCoeff, hx, inner_add_right, inner_smul_right, inner_smul_right]
    rw [real_inner_comm (gradφ x) (matMulE (A.a x) (hw_u.weakGrad x))]
    rw [real_inner_comm (hw_u.weakGrad x) (matMulE (A.a x) (hw_u.weakGrad x))]
    ring
  have h_expand_ae' :
      ∀ᵐ x ∂(volume.restrict Ω),
        bilinFormIntegrandOfCoeff A hw_u hw_ψ x =
          2 * ((φ x / (u x + ε)) *
            @inner ℝ E _ (gradφ x) (matMulE (A.a x) (hw_u.weakGrad x))) -
          φ x ^ 2 / (u x + ε) ^ 2 *
            @inner ℝ E _ (hw_u.weakGrad x) (matMulE (A.a x) (hw_u.weakGrad x)) := by
    filter_upwards [h_expand_ae] with x hx
    simpa [mul_assoc] using hx
  have h_expand :
      bilinFormOfCoeff A hw_u hw_ψ =
        (2 * ∫ x in Ω, φ x / (u x + ε) *
          @inner ℝ E _ (gradφ x) (matMulE (A.a x) (hw_u.weakGrad x))) -
        ∫ x in Ω, φ x ^ 2 / (u x + ε) ^ 2 *
          @inner ℝ E _ (hw_u.weakGrad x) (matMulE (A.a x) (hw_u.weakGrad x)) := by
    rw [bilinFormOfCoeff]
    calc
      ∫ x in Ω, bilinFormIntegrandOfCoeff A hw_u hw_ψ x
          = ∫ x in Ω,
              (2 * ((φ x / (u x + ε)) *
                @inner ℝ E _ (gradφ x) (matMulE (A.a x) (hw_u.weakGrad x))) -
                φ x ^ 2 / (u x + ε) ^ 2 *
                  @inner ℝ E _ (hw_u.weakGrad x) (matMulE (A.a x) (hw_u.weakGrad x))) := by
              exact integral_congr_ae h_expand_ae'
      _ = (∫ x in Ω, 2 * ((φ x / (u x + ε)) *
                @inner ℝ E _ (gradφ x) (matMulE (A.a x) (hw_u.weakGrad x)))) -
          ∫ x in Ω, φ x ^ 2 / (u x + ε) ^ 2 *
            @inner ℝ E _ (hw_u.weakGrad x) (matMulE (A.a x) (hw_u.weakGrad x)) := by
              exact (integral_sub hX_int hQ_int)
      _ = (2 * ∫ x in Ω, φ x / (u x + ε) *
            @inner ℝ E _ (gradφ x) (matMulE (A.a x) (hw_u.weakGrad x))) -
          ∫ x in Ω, φ x ^ 2 / (u x + ε) ^ 2 *
            @inner ℝ E _ (hw_u.weakGrad x) (matMulE (A.a x) (hw_u.weakGrad x)) := by
              congr 1
              rw [integral_const_mul]
  have hnonneg_expr : 0 ≤
      (2 * ∫ x in Ω, φ x / (u x + ε) *
        @inner ℝ E _ (gradφ x) (matMulE (A.a x) (hw_u.weakGrad x))) -
      ∫ x in Ω, φ x ^ 2 / (u x + ε) ^ 2 *
        @inner ℝ E _ (hw_u.weakGrad x) (matMulE (A.a x) (hw_u.weakGrad x)) := by
    simpa [h_expand] using htest
  simpa [gradφ] using (sub_nonneg.mp hnonneg_expr)

/-- **Steps (c)+(d)**: Algebraic conclusion from `Q ≤ 2X` and the ellipticity bounds.

Given `Q ≤ 2X` where:
- `Q = ∫ φ²/(u+ε)² ⟨∇u, A∇u⟩ ≥ λ · ∫ φ²‖∇u‖²/(u+ε)²` (coercivity)
- `X² ≤ Q · P` (Cauchy-Schwarz on A-inner product)
- `P = ∫ ⟨∇φ, A∇φ⟩ ≤ Λ · ∫ ‖∇φ‖²` (upper bound)

We get `Q ≤ 4P` and hence `∫ φ²‖∇u‖²/(u+ε)² ≤ (4Λ/λ) · ∫ ‖∇φ‖²`.

This is a pure real-analysis/algebra step given the three integral bounds. -/
private theorem log_gradient_algebraic_conclusion
    {Q X P LHS RHS : ℝ}
    (hQ_nonneg : 0 ≤ Q)
    (hP_nonneg : 0 ≤ P)
    (hQ_le_2X : Q ≤ 2 * X)
    (hX_sq_le : X ^ 2 ≤ Q * P)
    (hLHS_le_Q : LHS ≤ Q)
    (hP_le_RHS : P ≤ RHS) :
    LHS ≤ 4 * RHS := by
  -- From Q ≤ 2X: Q² ≤ 4X² ≤ 4QP, so Q(Q - 4P) ≤ 0.
  -- Since Q ≥ 0, this gives Q ≤ 4P.
  -- Hence LHS ≤ Q ≤ 4P ≤ 4·RHS.
  by_cases hQ0 : Q = 0
  · nlinarith
  · have hQ_pos : 0 < Q := lt_of_le_of_ne hQ_nonneg (Ne.symm hQ0)
    -- From Q ≤ 2X and Q > 0, we get X > 0.
    have hX_pos : 0 < X := by linarith
    have hQP : Q ≤ 4 * P := by
      -- Q ≤ 2X, so Q² ≤ 4X² ≤ 4QP
      have h1 : Q ^ 2 ≤ (2 * X) ^ 2 := sq_le_sq' (by linarith) hQ_le_2X
      have h3 : Q ^ 2 ≤ 4 * (Q * P) := by nlinarith
      -- Q² ≤ 4QP → Q ≤ 4P (dividing by Q > 0)
      nlinarith [sq_nonneg (Q - 4 * P)]
    linarith

/-- Regularized logarithmic gradient bound: for fixed `ε > 0`,
`∫_Ω φ²|∇u|²/(u+ε)² ≤ 4Λ ∫_Ω |∇φ|²`.

This is the ε-level estimate that feeds into `log_gradient_bound_of_supersolution`
via `ε → 0`. -/
theorem log_gradient_bound_eps
    {Ω : Set E} (hΩ : IsOpen Ω)
    (A : EllipticCoeff d Ω)
    {u : E → ℝ}
    (hu_pos : ∀ x ∈ Ω, 0 < u x)
    (hsuper : IsSupersolution A u)
    {φ : E → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφ_cs : HasCompactSupport φ) (hφ_sub : tsupport φ ⊆ Ω)
    (hw_u : MemW1pWitness 2 u Ω)
    {ε : ℝ} (hε : 0 < ε) :
    ∫ x in Ω, φ x ^ 2 * ‖hw_u.weakGrad x‖ ^ 2 / (u x + ε) ^ 2 ≤
      4 * A.Λ / A.lam * ∫ x in Ω, ‖fderiv ℝ φ x‖ ^ 2 := by
  -- Define the key integrals.
  set LHS := ∫ x in Ω, φ x ^ 2 * ‖hw_u.weakGrad x‖ ^ 2 / (u x + ε) ^ 2
  -- Q := ∫ φ²/(u+ε)² ⟨∇u, A∇u⟩ (A-quadratic form weighted by φ²/(u+ε)²)
  set Q := ∫ x in Ω, φ x ^ 2 / (u x + ε) ^ 2 *
    @inner ℝ E _ (hw_u.weakGrad x) (matMulE (A.a x) (hw_u.weakGrad x))
  -- X := ∫ φ/(u+ε) ⟨∇φ, A∇u⟩ (mixed A-form)
  set gradφ : E → E := fun x => WithLp.toLp 2
    (fun i => (fderiv ℝ φ x) (EuclideanSpace.single i 1))
  set X := ∫ x in Ω, φ x / (u x + ε) *
    @inner ℝ E _ (gradφ x) (matMulE (A.a x) (hw_u.weakGrad x))
  -- Step (b): Q ≤ 2X (from supersolution with ψ_ε = φ²/(u+ε))
  have hQ_le_2X : Q ≤ 2 * X :=
    supersolution_energy_identity_eps hΩ A hu_pos hsuper hw_u hφ hφ_cs hφ_sub hε
  -- Q ≥ 0 (by coercivity: ⟨ξ, Aξ⟩ ≥ λ‖ξ‖² ≥ 0)
  have hQ_nonneg : 0 ≤ Q := by
    apply integral_nonneg_of_ae
    filter_upwards [A.ae_coercive_nonneg] with x hx
    exact mul_nonneg (div_nonneg (sq_nonneg _) (sq_nonneg _)) (hx (hw_u.weakGrad x))
  have hu_eps_aemeas : AEMeasurable (fun x => u x + ε) (volume.restrict Ω) := by
    exact ((continuous_id.add continuous_const).comp_aestronglyMeasurable
      hw_u.memLp.aestronglyMeasurable).aemeasurable
  have hweight_aemeas : AEMeasurable (fun x => φ x / (u x + ε)) (volume.restrict Ω) := by
    exact (hφ.continuous.aestronglyMeasurable.aemeasurable.div hu_eps_aemeas)
  have hweight_sq_meas :
      AEStronglyMeasurable (fun x => (φ x / (u x + ε)) ^ 2) (volume.restrict Ω) := by
    exact (hweight_aemeas.pow_const 2).aestronglyMeasurable
  obtain ⟨Cφ, hCφ⟩ := hφ_cs.exists_bound_of_continuous hφ.continuous
  have hCφ_nonneg : 0 ≤ Cφ := le_trans (norm_nonneg _) (hCφ (0 : E))
  have hweight_bound : ∀ x, |φ x / (u x + ε)| ≤ Cφ / ε := by
    intro x
    by_cases hx : x ∈ Ω
    · have hu_eps_pos : 0 < u x + ε := by linarith [hu_pos x hx, hε]
      have hnum : |φ x| ≤ Cφ := (Real.norm_eq_abs (φ x)).symm ▸ hCφ x
      rw [abs_div, abs_of_nonneg hu_eps_pos.le]
      have hε_le : ε ≤ u x + ε := by linarith [hu_pos x hx]
      have hgoal : |φ x| / (u x + ε) ≤ Cφ / ε := by
        refine le_trans ?_ (div_le_div_of_nonneg_right hnum hε.le)
        exact div_le_div_of_nonneg_left (abs_nonneg _) hε hε_le
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hgoal
    · have hφ0 : φ x = 0 := by
        by_contra h
        exact hx (hφ_sub (subset_tsupport φ (Function.mem_support.mpr h)))
      have hnonneg : 0 ≤ Cφ / ε := div_nonneg hCφ_nonneg hε.le
      simpa [hφ0] using hnonneg
  have hweight_sq_bound : ∀ x, |(φ x / (u x + ε)) ^ 2| ≤ Cφ ^ 2 / ε ^ 2 := by
    intro x
    have hx := hweight_bound x
    have hnonneg : 0 ≤ Cφ / ε := div_nonneg hCφ_nonneg hε.le
    calc
      |(φ x / (u x + ε)) ^ 2| = |φ x / (u x + ε)| ^ 2 := by rw [abs_pow]
      _ ≤ (Cφ / ε) ^ 2 := by nlinarith [hx, abs_nonneg (φ x / (u x + ε)), hnonneg]
      _ = Cφ ^ 2 / ε ^ 2 := by ring
  have hQ_int_weight :
      Integrable (fun x => (φ x / (u x + ε)) ^ 2 *
        bilinFormIntegrandOfCoeff A hw_u hw_u x) (volume.restrict Ω) := by
    exact integrable_bounded_mul_bilinFormIntegrand A hw_u hweight_sq_meas hweight_sq_bound
  have hQ_int :
      Integrable (fun x => φ x ^ 2 / (u x + ε) ^ 2 *
        bilinFormIntegrandOfCoeff A hw_u hw_u x) (volume.restrict Ω) := by
    convert hQ_int_weight using 1
    ext x
    rw [bilinFormIntegrandOfCoeff, real_inner_comm]
    rw [div_pow]
  have hQ_eq :
      ∫ x in Ω, φ x ^ 2 / (u x + ε) ^ 2 * bilinFormIntegrandOfCoeff A hw_u hw_u x = Q := by
    change ∫ x in Ω, φ x ^ 2 / (u x + ε) ^ 2 * bilinFormIntegrandOfCoeff A hw_u hw_u x =
      ∫ x in Ω, φ x ^ 2 / (u x + ε) ^ 2 *
        @inner ℝ E _ (hw_u.weakGrad x) (matMulE (A.a x) (hw_u.weakGrad x))
    refine integral_congr_ae ?_
    filter_upwards with x
    rw [bilinFormIntegrandOfCoeff, real_inner_comm]
  -- Coercivity: λ · LHS ≤ Q (pointwise ⟨ξ, Aξ⟩ ≥ λ‖ξ‖², integrate)
  have hLHS_le : A.lam * LHS ≤ Q := by
    let leftInt : E → ℝ := fun x =>
      A.lam * ((φ x / (u x + ε)) ^ 2 * ‖hw_u.weakGrad x‖ ^ 2)
    have hleft_aemeas : AEMeasurable leftInt (volume.restrict Ω) := by
      exact (((hweight_aemeas.pow_const 2).mul
        (hw_u.weakGrad_norm_memLp.aestronglyMeasurable.aemeasurable.pow_const 2)).const_mul A.lam)
    have hleft_meas : AEStronglyMeasurable leftInt (volume.restrict Ω) :=
      hleft_aemeas.aestronglyMeasurable
    have hleft_le_q :
        ∀ᵐ x ∂(volume.restrict Ω),
          leftInt x ≤ φ x ^ 2 / (u x + ε) ^ 2 *
            bilinFormIntegrandOfCoeff A hw_u hw_u x := by
      filter_upwards [A.coercive] with x hx
      have hnn : 0 ≤ (φ x / (u x + ε)) ^ 2 := sq_nonneg _
      calc
        leftInt x
            = (φ x / (u x + ε)) ^ 2 * (A.lam * ‖hw_u.weakGrad x‖ ^ 2) := by
                dsimp [leftInt]
                ring
        _ ≤ (φ x / (u x + ε)) ^ 2 *
              @inner ℝ E _ (hw_u.weakGrad x) (matMulE (A.a x) (hw_u.weakGrad x)) :=
            mul_le_mul_of_nonneg_left (hx (hw_u.weakGrad x)) hnn
        _ = φ x ^ 2 / (u x + ε) ^ 2 *
              bilinFormIntegrandOfCoeff A hw_u hw_u x := by
            rw [bilinFormIntegrandOfCoeff, real_inner_comm]
            rw [div_pow]
    have hleft_int : Integrable leftInt (volume.restrict Ω) := by
      refine Integrable.mono' hQ_int hleft_meas ?_
      filter_upwards [hleft_le_q] with x hx
      have hleft_nonneg : 0 ≤ leftInt x := by
        dsimp [leftInt]
        exact mul_nonneg A.lam_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))
      rw [Real.norm_of_nonneg hleft_nonneg]
      exact hx
    calc A.lam * LHS
        = ∫ x in Ω, A.lam * (φ x ^ 2 * ‖hw_u.weakGrad x‖ ^ 2 / (u x + ε) ^ 2) := by
          rw [integral_const_mul]
      _ = ∫ x in Ω, leftInt x := by
          refine integral_congr_ae ?_
          filter_upwards with x
          dsimp [leftInt]
          rw [div_pow]
          ring
      _ ≤ ∫ x in Ω, φ x ^ 2 / (u x + ε) ^ 2 * bilinFormIntegrandOfCoeff A hw_u hw_u x := by
          exact integral_mono_ae hleft_int hQ_int hleft_le_q
      _ = Q := hQ_eq
  have hφ_test : IsSmoothTestOn Ω φ := ⟨hφ, hφ_cs, hφ_sub⟩
  let hw_φ : MemW1pWitness 2 φ Ω := smoothTestWitness hΩ hφ_test
  have hX_sq_le :
      X ^ 2 ≤ Q * (A.Λ * ∫ x in Ω, ‖fderiv ℝ φ x‖ ^ 2) := by
    have hcs :=
      bilinForm_weighted_cauchySchwarz
        (A := A) (hu := hw_u) (hv := hw_φ)
        (f := fun x => φ x / (u x + ε))
        hweight_aemeas.aestronglyMeasurable hQ_int_weight
    have hX_eq :
        ∫ x in Ω, φ x / (u x + ε) *
          bilinFormIntegrandOfCoeff A hw_u hw_φ x = X := by
      change ∫ x in Ω, φ x / (u x + ε) * bilinFormIntegrandOfCoeff A hw_u hw_φ x =
        ∫ x in Ω, φ x / (u x + ε) *
          @inner ℝ E _ (gradφ x) (matMulE (A.a x) (hw_u.weakGrad x))
      refine integral_congr_ae ?_
      filter_upwards with x
      rw [bilinFormIntegrandOfCoeff, real_inner_comm]
      simp [gradφ, hw_φ, smoothTestWitness, smoothGradField]
    have hgrad_sq_eq :
        ∀ x, ‖hw_φ.weakGrad x‖ ^ (2 : ℕ) = ‖fderiv ℝ φ x‖ ^ 2 := by
      intro x
      have hnorm : ‖hw_φ.weakGrad x‖ = ‖fderiv ℝ φ x‖ := by
        simp [hw_φ, smoothTestWitness, smoothGradField, smoothGradNorm,
          norm_fderiv_eq_smoothGradNorm]
      rw [hnorm]
    have hP_eq :
        ∫ x in Ω, ‖hw_φ.weakGrad x‖ ^ (2 : ℕ) =
          ∫ x in Ω, ‖fderiv ℝ φ x‖ ^ 2 := by
      exact integral_congr_ae (Filter.Eventually.of_forall hgrad_sq_eq)
    calc
      X ^ 2 = (∫ x in Ω, φ x / (u x + ε) *
          bilinFormIntegrandOfCoeff A hw_u hw_φ x) ^ 2 := by
            rw [hX_eq.symm]
      _ ≤ (∫ x in Ω, (φ x / (u x + ε)) ^ 2 *
            bilinFormIntegrandOfCoeff A hw_u hw_u x) *
          (A.Λ * ∫ x in Ω, ‖hw_φ.weakGrad x‖ ^ (2 : ℕ)) := hcs
      _ = Q * (A.Λ * ∫ x in Ω, ‖fderiv ℝ φ x‖ ^ 2) := by
          rw [show ∫ x in Ω, (φ x / (u x + ε)) ^ 2 * bilinFormIntegrandOfCoeff A hw_u hw_u x =
              ∫ x in Ω, φ x ^ 2 / (u x + ε) ^ 2 * bilinFormIntegrandOfCoeff A hw_u hw_u x by
                refine integral_congr_ae ?_
                filter_upwards with x
                rw [div_pow],
            hQ_eq, hP_eq]
  have hR_nonneg : 0 ≤ A.Λ * ∫ x in Ω, ‖fderiv ℝ φ x‖ ^ 2 := by
    refine mul_nonneg A.Λ_nonneg ?_
    exact integral_nonneg (fun x => by positivity)
  have hlamLHS_le :
      A.lam * LHS ≤ 4 * (A.Λ * ∫ x in Ω, ‖fderiv ℝ φ x‖ ^ 2) := by
    exact
      log_gradient_algebraic_conclusion
        (Q := Q) (X := X) (P := A.Λ * ∫ x in Ω, ‖fderiv ℝ φ x‖ ^ 2)
        (LHS := A.lam * LHS) (RHS := A.Λ * ∫ x in Ω, ‖fderiv ℝ φ x‖ ^ 2)
        hQ_nonneg hR_nonneg hQ_le_2X hX_sq_le hLHS_le le_rfl
  calc
    LHS ≤ (4 * (A.Λ * ∫ x in Ω, ‖fderiv ℝ φ x‖ ^ 2)) / A.lam := by
      rw [le_div_iff₀ A.hlam]
      simpa [mul_comm] using hlamLHS_le
    _ = 4 * A.Λ / A.lam * ∫ x in Ω, ‖fderiv ℝ φ x‖ ^ 2 := by ring

/-- Logarithmic gradient bound for positive supersolutions.

If `u > 0` satisfies `-∇·(A∇u) ≥ 0` on `Ω`, then for every smooth cutoff
`φ` supported in `Ω`:
`∫_Ω φ² |∇u|²/u² ≤ 4Λ ∫_Ω |∇φ|²`.

Equivalently, setting `v = -log u`: `∫_Ω φ² |∇v|² ≤ 4Λ ∫_Ω |∇φ|²`.

Proof: apply `log_gradient_bound_eps` for each `ε > 0` to get
`∫ φ²|∇u|²/(u+ε)² ≤ 4Λ ∫ |∇φ|²`, then send `ε → 0`. Since
`u > 0` on `Ω`, the integrand `φ²|∇u|²/(u+ε)²` increases monotonically
to `φ²|∇u|²/u²` as `ε ↘ 0`. By monotone convergence, the limit integral
satisfies the same bound. -/
theorem log_gradient_bound_of_supersolution
    {Ω : Set E} (hΩ : IsOpen Ω)
    (A : EllipticCoeff d Ω)
    {u : E → ℝ}
    (hu_pos : ∀ x ∈ Ω, 0 < u x)
    (hsuper : IsSupersolution A u)
    {φ : E → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφ_cs : HasCompactSupport φ) (hφ_sub : tsupport φ ⊆ Ω)
    (hw_u : MemW1pWitness 2 u Ω) :
    ∫ x in Ω, φ x ^ 2 * ‖hw_u.weakGrad x‖ ^ 2 / (u x) ^ 2 ≤
      4 * A.Λ / A.lam * ∫ x in Ω, ‖fderiv ℝ φ x‖ ^ 2 := by
  -- The RHS is independent of ε, and for each ε > 0:
  --   ∫ φ²|∇u|²/(u+ε)² ≤ 4Λ ∫ |∇φ|² (by log_gradient_bound_eps).
  -- As ε ↘ 0, the LHS increases to ∫ φ²|∇u|²/u² (since u > 0 on Ω).
  -- Apply monotone convergence to pass the bound to the limit.
  suffices h : ∀ ε : ℝ, 0 < ε →
      ∫ x in Ω, φ x ^ 2 * ‖hw_u.weakGrad x‖ ^ 2 / (u x + ε) ^ 2 ≤
        4 * A.Λ / A.lam * ∫ x in Ω, ‖fderiv ℝ φ x‖ ^ 2 from by
    let μ : Measure E := volume.restrict Ω
    let εn : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
    let g : ℕ → E → ℝ := fun n x =>
      (φ x / (u x + εn n)) ^ 2 * ‖hw_u.weakGrad x‖ ^ 2
    let g0 : E → ℝ := fun x =>
      (φ x / u x) ^ 2 * ‖hw_u.weakGrad x‖ ^ 2
    set R := 4 * A.Λ / A.lam * ∫ x in Ω, ‖fderiv ℝ φ x‖ ^ 2
    obtain ⟨Cφ, hCφ⟩ := hφ_cs.exists_bound_of_continuous hφ.continuous
    have hCφ_nonneg : 0 ≤ Cφ := le_trans (norm_nonneg _) (hCφ (0 : E))
    have hεn_pos : ∀ n, 0 < εn n := by
      intro n
      dsimp [εn]
      positivity
    have hu_eps_aemeas : ∀ n, AEMeasurable (fun x => u x + εn n) μ := by
      intro n
      exact ((continuous_id.add continuous_const).comp_aestronglyMeasurable
        hw_u.memLp.aestronglyMeasurable).aemeasurable
    have hweight_sq_meas :
        ∀ n, AEStronglyMeasurable (fun x => (φ x / (u x + εn n)) ^ 2) μ := by
      intro n
      exact ((hφ.continuous.aestronglyMeasurable.aemeasurable.div
        (hu_eps_aemeas n)).pow_const 2).aestronglyMeasurable
    have hweight_sq_bound :
        ∀ n x, |(φ x / (u x + εn n)) ^ 2| ≤ Cφ ^ 2 / (εn n) ^ 2 := by
      intro n x
      by_cases hx : x ∈ Ω
      · have hu_eps_pos : 0 < u x + εn n := by linarith [hu_pos x hx, hεn_pos n]
        have hnum : |φ x| ≤ Cφ := (Real.norm_eq_abs (φ x)).symm ▸ hCφ x
        have hnonneg : 0 ≤ Cφ / εn n := div_nonneg hCφ_nonneg (hεn_pos n).le
        have hε_le : εn n ≤ u x + εn n := by linarith [hu_pos x hx]
        have hbound : |φ x / (u x + εn n)| ≤ Cφ / εn n := by
          rw [abs_div, abs_of_nonneg hu_eps_pos.le]
          refine le_trans ?_ (div_le_div_of_nonneg_right hnum (hεn_pos n).le)
          exact div_le_div_of_nonneg_left (abs_nonneg _) (hεn_pos n) hε_le
        calc
          |(φ x / (u x + εn n)) ^ 2| = |φ x / (u x + εn n)| ^ 2 := by rw [abs_pow]
          _ ≤ (Cφ / εn n) ^ 2 := by
              nlinarith [hbound, abs_nonneg (φ x / (u x + εn n)), hnonneg]
          _ = Cφ ^ 2 / (εn n) ^ 2 := by ring
      · have hφ0 : φ x = 0 := by
          by_contra hφx
          exact hx (hφ_sub (subset_tsupport φ (Function.mem_support.mpr hφx)))
        have hnonneg : 0 ≤ Cφ ^ 2 / (εn n) ^ 2 := by
          positivity
        simpa [hφ0] using hnonneg
    have hgrad_sq_meas : AEStronglyMeasurable (fun x => ‖hw_u.weakGrad x‖ ^ 2) μ := by
      exact (hw_u.weakGrad_norm_memLp.aestronglyMeasurable.aemeasurable.pow_const 2).aestronglyMeasurable
    have hg_meas : ∀ n, AEMeasurable (g n) μ := by
      intro n
      exact (hweight_sq_meas n).aemeasurable.mul hgrad_sq_meas.aemeasurable
    have hg0_meas : AEStronglyMeasurable g0 μ := by
      exact ((hφ.continuous.aestronglyMeasurable.aemeasurable.div
        hw_u.memLp.aestronglyMeasurable.aemeasurable).pow_const 2).aestronglyMeasurable.mul hgrad_sq_meas
    have hg_nonneg : ∀ n, 0 ≤ᵐ[μ] g n := by
      intro n
      exact Filter.Eventually.of_forall fun x => by
        dsimp [g]
        exact mul_nonneg (sq_nonneg _) (sq_nonneg _)
    have hg0_nonneg : 0 ≤ᵐ[μ] g0 := by
      exact Filter.Eventually.of_forall fun x => by
        dsimp [g0]
        exact mul_nonneg (sq_nonneg _) (sq_nonneg _)
    have hg_int : ∀ n, Integrable (g n) μ := by
      intro n
      exact (hw_u.weakGrad_norm_memLp.integrable_sq).bdd_mul
        (c := Cφ ^ 2 / (εn n) ^ 2) (hweight_sq_meas n)
        (Filter.Eventually.of_forall (hweight_sq_bound n))
    have hright_eq :
        ∀ n,
          ∫⁻ x, ENNReal.ofReal (g n x) ∂μ =
            ENNReal.ofReal (∫ x, g n x ∂μ) := by
      intro n
      exact
        (MeasureTheory.ofReal_integral_eq_lintegral_ofReal
          (μ := μ) (f := g n) (hg_int n) (hg_nonneg n)).symm
    have hfR : ∀ n, ∫ x, g n x ∂μ ≤ R := by
      intro n
      have hbound := h (εn n) (hεn_pos n)
      change ∫ x in Ω, g n x ∂volume ≤ R
      have hEq :
          ∫ x in Ω, g n x ∂volume =
            ∫ x in Ω, φ x ^ 2 * ‖hw_u.weakGrad x‖ ^ 2 / (u x + εn n) ^ 2 ∂volume := by
        refine integral_congr_ae ?_
        filter_upwards with x
        dsimp [g]
        rw [div_pow]
        ring
      rw [hEq]
      exact hbound
    have hFatou :
        ∫⁻ x, ENNReal.ofReal (g0 x) ∂μ ≤
          atTop.liminf (fun n => ∫⁻ x, ENNReal.ofReal (g n x) ∂μ) := by
      have hmeas :
          ∀ n, AEMeasurable (fun x => ENNReal.ofReal (g n x)) μ := by
        intro n
        exact (hg_meas n).ennreal_ofReal
      have hleft := MeasureTheory.lintegral_liminf_le' (μ := μ) hmeas
      have hlim :
          (fun x =>
            Filter.liminf (fun n => ENNReal.ofReal (g n x)) atTop) =ᵐ[μ]
              (fun x => ENNReal.ofReal (g0 x)) := by
        filter_upwards [ae_restrict_mem hΩ.measurableSet] with x hx
        have hu_posx : 0 < u x := hu_pos x hx
        have hden_tend : Tendsto (fun n => u x + εn n) atTop (nhds (u x)) := by
          simpa [εn, one_div] using
            (tendsto_one_div_add_atTop_nhds_zero_nat.const_add (u x))
        have hquot_tend :
            Tendsto (fun n => φ x / (u x + εn n)) atTop (nhds (φ x / u x)) := by
          exact Tendsto.div tendsto_const_nhds hden_tend hu_posx.ne'
        have hreal_tend : Tendsto (fun n => g n x) atTop (nhds (g0 x)) := by
          exact ((continuous_pow 2).tendsto (φ x / u x)).comp hquot_tend |>.mul tendsto_const_nhds
        have henn_tend :
            Tendsto (fun n => ENNReal.ofReal (g n x)) atTop
              (nhds (ENNReal.ofReal (g0 x))) := by
          exact (ENNReal.continuous_ofReal.tendsto _).comp hreal_tend
        exact henn_tend.liminf_eq
      calc
        ∫⁻ x, ENNReal.ofReal (g0 x) ∂μ
            = ∫⁻ x, Filter.liminf (fun n => ENNReal.ofReal (g n x)) atTop ∂μ := by
                exact lintegral_congr_ae hlim.symm
        _ ≤ atTop.liminf (fun n => ∫⁻ x, ENNReal.ofReal (g n x) ∂μ) := hleft
    have hliminf_le :
        atTop.liminf (fun n => ∫⁻ x, ENNReal.ofReal (g n x) ∂μ) ≤ ENNReal.ofReal R := by
      rw [Filter.liminf_congr (Eventually.of_forall hright_eq)]
      refine Filter.liminf_le_of_frequently_le' (Frequently.of_forall fun n => ?_)
      exact ENNReal.ofReal_le_ofReal (hfR n)
    have hmain_enn : ∫⁻ x, ENNReal.ofReal (g0 x) ∂μ ≤ ENNReal.ofReal R := by
      exact le_trans hFatou hliminf_le
    have hR_nonneg : 0 ≤ R := by
      dsimp [R]
      refine mul_nonneg ?_ (integral_nonneg (fun x => by positivity))
      · have hnum_nonneg : 0 ≤ 4 * A.Λ := by nlinarith [A.Λ_nonneg]
        exact div_nonneg hnum_nonneg A.hlam.le
    calc
      ∫ x in Ω, φ x ^ 2 * ‖hw_u.weakGrad x‖ ^ 2 / (u x) ^ 2
          = ∫ x, g0 x ∂μ := by
              refine integral_congr_ae ?_
              filter_upwards with x
              dsimp [g0]
              rw [div_pow]
              ring
      _ = ENNReal.toReal (∫⁻ x, ENNReal.ofReal (g0 x) ∂μ) := by
            exact MeasureTheory.integral_eq_lintegral_of_nonneg_ae hg0_nonneg hg0_meas
      _ ≤ ENNReal.toReal (ENNReal.ofReal R) := by
            have hleft_ne_top : ∫⁻ x, ENNReal.ofReal (g0 x) ∂μ ≠ ∞ := by
              exact ne_of_lt (lt_of_le_of_lt hmain_enn (by simp))
            exact (ENNReal.toReal_le_toReal hleft_ne_top (by simp)).2 hmain_enn
      _ = R := by rw [ENNReal.toReal_ofReal hR_nonneg]
      _ = 4 * A.Λ / A.lam * ∫ x in Ω, ‖fderiv ℝ φ x‖ ^ 2 := by
            rfl
  intro ε hε
  exact log_gradient_bound_eps hΩ A hu_pos hsuper hφ hφ_cs hφ_sub hw_u hε

end DeGiorgi
