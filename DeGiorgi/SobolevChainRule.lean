import DeGiorgi.UnitBallApproximation
import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# Chapter 02: Sobolev Chain Rule

If `u ∈ W^{1,2}(Ω)` with weak derivative `g` in direction `i`, and `Φ : ℝ → ℝ` is
smooth with bounded derivative and `Φ(0) = 0`, then `Φ ∘ u` has weak partial derivative
`Φ'(u) · g` in direction `i`.

## Proof

1. Fix a test function `φ` with compact support in `Ω`.
2. Find a ball `B ⊆ Ω` containing `tsupport φ`.
3. Restrict `u` to `B`, rescale to the unit ball.
4. Apply `exists_smooth_W12_approx_on_unitBall` to get smooth `ψ_n → u`.
5. Classical chain rule: `∫ Φ(ψ_n) · ∂ᵢφ = -∫ Φ'(ψ_n) · ∂ᵢψ_n · φ`.
6. Pass to the limit:
   - LHS: Φ is Lipschitz, so Φ(ψ_n) → Φ(u) in L².
   - RHS: split as Φ'(ψ_n)(∂ᵢψ_n - g) + (Φ'(ψ_n) - Φ'(u))g;
     first term → 0 by bounded × L² → L¹; second by dominated convergence.

This section isolates the Sobolev chain rule used by the Chapter 02
Stampacchia argument while keeping the proof independent of
`StampacchiaTruncation.lean`.
-/

noncomputable section

open MeasureTheory Metric Filter Topology Set Function
open scoped ENNReal NNReal Manifold

namespace DeGiorgi

variable {d : ℕ} [NeZero d]
local notation "E" => EuclideanSpace ℝ (Fin d)

/-! ## Classical chain rule for smooth functions

For smooth `f` and smooth `Φ`, the composition `Φ ∘ f` is smooth with
`∂ᵢ(Φ ∘ f)(x) = Φ'(f(x)) · ∂ᵢf(x)`. The IBP identity follows. -/

/-- If `f : E → ℝ` is smooth on an open set `Ω`, then `Φ ∘ f` satisfies
the weak derivative identity with derivative `Φ'(f) · ∂ᵢf`.
This is just the classical IBP for smooth functions + the classical chain rule. -/
private theorem chain_rule_smooth_ibp
    {Ω : Set E} (hΩ : IsOpen Ω) (i : Fin d)
    {f : E → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (_hf_cs : HasCompactSupport f)
    {Φ : ℝ → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (_hΦ0 : Φ 0 = 0) :
    ∀ φ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
    ∫ x in Ω, (Φ (f x)) * (fderiv ℝ φ x) (EuclideanSpace.single i 1) =
      -∫ x in Ω, (deriv Φ (f x) * (fderiv ℝ f x) (EuclideanSpace.single i 1)) * φ x := by
  let _ := (inferInstance : NeZero d)
  have hΦf : ContDiff ℝ (⊤ : ℕ∞) (Φ ∘ f) := hΦ.comp hf
  have hfderiv : ∀ x, fderiv ℝ (Φ ∘ f) x =
      (fderiv ℝ Φ (f x)).comp (fderiv ℝ f x) := by
    intro x
    exact (hΦ.differentiable (by simp) (f x)).hasFDerivAt.comp x
      (hf.differentiable (by simp) x).hasFDerivAt |>.fderiv
  have hweak := HasWeakPartialDeriv.of_contDiff (i := i) hΩ (hΦf.of_le (by simp))
  intro φ hφ hφ_cs hφ_supp
  have hkey := hweak φ hφ hφ_cs hφ_supp
  simp only [comp_apply] at hkey
  convert hkey using 2
  congr 1
  ext x
  rw [hfderiv x, ContinuousLinearMap.comp_apply]
  have hΦ_diff : DifferentiableAt ℝ Φ (f x) := hΦ.differentiable (by simp) (f x)
  rw [hΦ_diff.hasDerivAt.hasFDerivAt.fderiv]
  simp [smul_eq_mul, mul_comm]

/-! ## Limit passage lemmas -/

set_option maxHeartbeats 400000 in
omit [NeZero d] in
private theorem integral_mul_tendsto_of_eLpNorm_tendsto
    {S : Set E} (_hS : MeasurableSet S) (hS_fin : volume S < ⊤)
    {f : ℕ → E → ℝ} {g : E → ℝ}
    (hf_meas : ∀ n, AEStronglyMeasurable (f n) (volume.restrict S))
    (hg_meas : AEStronglyMeasurable g (volume.restrict S))
    (h_conv : Tendsto (fun n => eLpNorm (fun x => f n x - g x) 2
      (volume.restrict S)) atTop (nhds 0))
    {ψ : E → ℝ} (hψ_bdd : ∃ C, ∀ x, |ψ x| ≤ C)
    (hψ_meas : AEStronglyMeasurable ψ (volume.restrict S)) :
    Tendsto (fun n => ∫ x in S, f n x * ψ x) atTop
      (nhds (∫ x in S, g x * ψ x)) := by
  obtain ⟨C, hC⟩ := hψ_bdd
  set μ := volume.restrict S
  have hμ_fin : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr (ne_top_of_lt hS_fin)
  -- Pointwise bound: ‖(f n x - g x) * ψ x‖ₑ ≤ ‖C‖ₑ * ‖f n x - g x‖ₑ
  have h_ptwise : ∀ n x, ‖(f n x - g x) * ψ x‖ₑ ≤ ‖(C : ℝ)‖ₑ * ‖f n x - g x‖ₑ := by
    intro n x
    simp only [enorm_mul]
    calc ‖f n x - g x‖ₑ * ‖ψ x‖ₑ
        = ‖ψ x‖ₑ * ‖f n x - g x‖ₑ := mul_comm _ _
      _ ≤ ‖(C : ℝ)‖ₑ * ‖f n x - g x‖ₑ := by
          gcongr
          rw [enorm_le_iff_norm_le, Real.norm_eq_abs, Real.norm_eq_abs]
          exact (hC x).trans (le_abs_self C)
  -- ‖C‖ₑ is finite
  have hC_ne_top : ‖(C : ℝ)‖ₑ ≠ ⊤ := enorm_ne_top
  -- Bound lintegral: ∫⁻ ‖(f_n - g) * ψ‖ₑ ≤ ‖C‖ₑ * eLpNorm(f_n - g, 1, μ)
  have h_lintegral_bound : ∀ n, ∫⁻ x, ‖(f n x - g x) * ψ x‖ₑ ∂μ ≤
      ‖(C : ℝ)‖ₑ * eLpNorm (fun x => f n x - g x) 1 μ := by
    intro n
    calc ∫⁻ x, ‖(f n x - g x) * ψ x‖ₑ ∂μ
        ≤ ∫⁻ x, ‖(C : ℝ)‖ₑ * ‖f n x - g x‖ₑ ∂μ :=
          lintegral_mono (h_ptwise n)
      _ = ‖(C : ℝ)‖ₑ * ∫⁻ x, ‖f n x - g x‖ₑ ∂μ :=
          lintegral_const_mul' _ _ hC_ne_top
      _ = ‖(C : ℝ)‖ₑ * eLpNorm (fun x => f n x - g x) 1 μ := by
          rw [eLpNorm_one_eq_lintegral_enorm]
  -- L1 ≤ L2 * vol^{1/2}
  have h_L1_le_L2 : ∀ n, eLpNorm (fun x => f n x - g x) 1 μ ≤
      eLpNorm (fun x => f n x - g x) 2 μ * μ Set.univ ^ ((1 : ℝ) / 1 - 1 / 2) :=
    fun n => eLpNorm_le_eLpNorm_mul_rpow_measure_univ (by norm_num) ((hf_meas n).sub hg_meas)
  -- vol^{1/2} is finite
  have hV_ne_top : μ Set.univ ^ ((1 : ℝ) / 1 - 1 / 2) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (by norm_num) (measure_ne_top μ _)
  -- K := ‖C‖ₑ * vol^{1/2}
  set K : ℝ≥0∞ := ‖(C : ℝ)‖ₑ * μ Set.univ ^ ((1 : ℝ) / 1 - 1 / 2)
  have hK_ne_top : K ≠ ⊤ := ENNReal.mul_ne_top hC_ne_top hV_ne_top
  -- ∫⁻ ‖(f_n-g)*ψ‖ₑ ≤ K * eLpNorm(f_n-g, 2)
  have h_bound2 : ∀ n, ∫⁻ x, ‖(f n x - g x) * ψ x‖ₑ ∂μ ≤
      K * eLpNorm (fun x => f n x - g x) 2 μ := by
    intro n
    calc ∫⁻ x, ‖(f n x - g x) * ψ x‖ₑ ∂μ
        ≤ ‖(C : ℝ)‖ₑ * eLpNorm (fun x => f n x - g x) 1 μ := h_lintegral_bound n
      _ ≤ ‖(C : ℝ)‖ₑ * (eLpNorm (fun x => f n x - g x) 2 μ *
            μ Set.univ ^ ((1 : ℝ) / 1 - 1 / 2)) := by gcongr; exact h_L1_le_L2 n
      _ = K * eLpNorm (fun x => f n x - g x) 2 μ := by dsimp [K]; ring
  -- Squeeze: upper bound → 0
  have h_lintegral_tendsto : Tendsto (fun n => ∫⁻ x, ‖(f n x - g x) * ψ x‖ₑ ∂μ)
      atTop (nhds 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds _
      (Eventually.of_forall (fun _ => zero_le _)) (Eventually.of_forall h_bound2)
    rw [show (0 : ℝ≥0∞) = K * 0 from by simp]
    exact ENNReal.Tendsto.const_mul h_conv (Or.inr hK_ne_top)
  have h_diff_int : ∀ᶠ n in atTop,
      Integrable (fun x => (f n x - g x) * ψ x) μ := by
    have h_diff_memLp : ∀ᶠ n in atTop, MemLp (fun x => f n x - g x) 2 μ := by
      have := h_conv.eventually (gt_mem_nhds ENNReal.zero_lt_top)
      filter_upwards [this] with n hn
      exact ⟨(hf_meas n).sub hg_meas, hn⟩
    filter_upwards [h_diff_memLp] with n hn
    exact (memLp_one_iff_integrable.mp
      (hn.mono_exponent (by norm_num : (1 : ℝ≥0∞) ≤ 2))).mul_bdd
      hψ_meas (Eventually.of_forall (fun x => by rw [Real.norm_eq_abs]; exact hC x))
  -- ∫ (f_n - g) * ψ → 0
  have h_diff_integral : Tendsto (fun n => ∫ x, (f n x - g x) * ψ x ∂μ) atTop (nhds 0) := by
    rw [show (0 : ℝ) = ∫ _, (0 : ℝ) ∂μ from by simp]
    apply tendsto_integral_of_L1 (fun _ => (0 : ℝ)) (integrable_zero _ _ _)
    · filter_upwards [h_diff_int] with n hn; exact hn
    · simpa [sub_zero] using h_lintegral_tendsto
  by_cases hgψ_int : Integrable (fun x => g x * ψ x) μ
  · -- g * ψ integrable
    have h_fnψ_int : ∀ᶠ n in atTop, Integrable (fun x => f n x * ψ x) μ := by
      filter_upwards [h_diff_int] with n hn
      have heq : (fun x => f n x * ψ x) = (fun x => (f n x - g x) * ψ x + g x * ψ x) := by
        ext x; ring
      rw [heq]; exact hn.add hgψ_int
    -- The sequence ∫ f_n * ψ ∂μ - ∫ g * ψ ∂μ = ∫ (f_n - g) * ψ ∂μ → 0
    have h_sub_eq : ∀ᶠ n in atTop,
        ∫ x, f n x * ψ x ∂μ - ∫ x, g x * ψ x ∂μ =
        ∫ x, (f n x - g x) * ψ x ∂μ := by
      filter_upwards [h_fnψ_int] with n hn
      rw [← integral_sub hn hgψ_int]
      congr 1; ext x; ring
    have h_sub_tendsto : Tendsto
        (fun n => ∫ x, f n x * ψ x ∂μ - ∫ x, g x * ψ x ∂μ) atTop (nhds 0) :=
      h_diff_integral.congr' (h_sub_eq.mono fun n hn => hn.symm)
    exact tendsto_sub_nhds_zero_iff.mp h_sub_tendsto
  · -- g * ψ not integrable ⟹ f_n * ψ eventually not integrable
    have h_fnψ_not_int : ∀ᶠ n in atTop, ¬Integrable (fun x => f n x * ψ x) μ := by
      filter_upwards [h_diff_int] with n hn hfn
      exact hgψ_int (show Integrable (fun x => g x * ψ x) μ from by
        have heq : (fun x => g x * ψ x) = (fun x => f n x * ψ x - (f n x - g x) * ψ x) := by
          ext x; ring
        rw [heq]; exact hfn.sub hn)
    rw [show (∫ x in S, g x * ψ x) = ∫ x, g x * ψ x ∂μ from rfl,
        show (fun n => ∫ x in S, f n x * ψ x) = (fun n => ∫ x, f n x * ψ x ∂μ) from rfl,
        integral_undef hgψ_int]
    exact tendsto_nhds_of_eventually_eq (h_fnψ_not_int.mono fun n hn => integral_undef hn)

omit [NeZero d] in
private theorem integral_bdd_mul_L1_tendsto
    {S : Set E} (_hS : MeasurableSet S) (_hS_fin : volume S < ⊤)
    {h : ℕ → E → ℝ} {M : ℝ} (hM : 0 ≤ M) (hh_bdd : ∀ n x, |h n x| ≤ M)
    {g_diff : ℕ → E → ℝ}
    (hg_int : ∀ n, IntegrableOn (g_diff n) S volume)
    (hg_L1 : Tendsto (fun n => ∫ x in S, ‖g_diff n x‖) atTop (nhds 0))
    {ψ : E → ℝ} {C : ℝ} (hψ_bdd : ∀ x, |ψ x| ≤ C) :
    Tendsto (fun n => ∫ x in S, h n x * g_diff n x * ψ x) atTop (nhds 0) := by
  apply squeeze_zero_norm (a := fun n => M * |C| * ∫ x in S, ‖g_diff n x‖)
  · intro n
    -- Pointwise bound: ‖h n x * g_diff n x * ψ x‖ ≤ M * |C| * ‖g_diff n x‖
    have key : ∀ x, ‖h n x * g_diff n x * ψ x‖ ≤ M * |C| * ‖g_diff n x‖ := by
      intro x
      rw [Real.norm_eq_abs, abs_mul, abs_mul]
      calc |h n x| * |g_diff n x| * |ψ x|
          ≤ M * |g_diff n x| * |C| :=
          mul_le_mul (mul_le_mul_of_nonneg_right (hh_bdd n x) (abs_nonneg _))
            ((hψ_bdd x).trans (le_abs_self C)) (abs_nonneg _) (mul_nonneg hM (abs_nonneg _))
        _ = M * |C| * |g_diff n x| := by ring
        _ = M * |C| * ‖g_diff n x‖ := by rw [Real.norm_eq_abs]
    calc ‖∫ x in S, h n x * g_diff n x * ψ x‖
        ≤ ∫ x in S, M * |C| * ‖g_diff n x‖ :=
        norm_integral_le_of_norm_le
          ((hg_int n).norm.const_mul _)
          (Eventually.of_forall (fun x => key x))
      _ = M * |C| * ∫ x in S, ‖g_diff n x‖ := integral_const_mul _ _
  · -- M * |C| * ∫_S ‖g_n‖ → 0
    have : Tendsto (fun n => M * |C| * (∫ x in S, ‖g_diff n x‖)) atTop (nhds (M * |C| * 0)) :=
      hg_L1.const_mul (M * |C|)
    simp only [mul_zero] at this; exact this

omit [NeZero d] in
private theorem integral_dominated_convergence_term
    {S : Set E} (_hS : MeasurableSet S)
    {h : ℕ → E → ℝ} {M : ℝ} (hh_bdd : ∀ n x, |h n x| ≤ M)
    (hh_meas : ∀ n, AEStronglyMeasurable (fun x => h n x) (volume.restrict S))
    (hh_ae : ∀ᵐ x ∂(volume.restrict S), Tendsto (fun n => h n x) atTop (nhds 0))
    {w : E → ℝ} (hw_int : IntegrableOn w S volume) :
    Tendsto (fun n => ∫ x in S, h n x * w x) atTop (nhds 0) := by
  rw [show (0 : ℝ) = ∫ _ in S, (0 : ℝ) from by simp]
  apply tendsto_integral_of_dominated_convergence (fun x => |M| * ‖w x‖)
    (μ := volume.restrict S)
  · intro n; exact (hh_meas n).mul hw_int.aestronglyMeasurable
  · exact hw_int.norm.const_mul _
  · intro n; filter_upwards with x
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right ((hh_bdd n x).trans (le_abs_self M)) (abs_nonneg _)
  · filter_upwards [hh_ae] with x hx
    simpa using hx.mul_const _

/-! ## L² → L¹ and a.e. convergence extraction -/

omit [NeZero d] in
private theorem eLpNorm_one_tendsto_of_eLpNorm_two_tendsto
    {S : Set E} (hS_fin : volume S < ⊤)
    {f : ℕ → E → ℝ} {g : E → ℝ}
    (hf_meas : ∀ n, AEStronglyMeasurable (f n) (volume.restrict S))
    (hg_meas : AEStronglyMeasurable g (volume.restrict S))
    (h : Tendsto (fun n => eLpNorm (fun x => f n x - g x) 2
      (volume.restrict S)) atTop (nhds 0)) :
    Tendsto (fun n => ∫ x in S, ‖f n x - g x‖) atTop (nhds 0) := by
  set μ := volume.restrict S
  have hμ_fin : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr (ne_top_of_lt hS_fin)
  set K := μ Set.univ ^ ((1 : ℝ) / 1 - 1 / 2)
  have h_L1_le_L2 : ∀ n, eLpNorm (fun x => f n x - g x) 1 μ ≤
      eLpNorm (fun x => f n x - g x) 2 μ * K :=
    fun n => eLpNorm_le_eLpNorm_mul_rpow_measure_univ (by norm_num)
      ((hf_meas n).sub hg_meas)
  have h_L1_tendsto : Tendsto (fun n => eLpNorm (fun x => f n x - g x) 1 μ)
      atTop (nhds 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      (show Tendsto (fun n => eLpNorm (fun x => f n x - g x) 2 μ * K)
        atTop (nhds 0) from ?_)
      (Eventually.of_forall (fun _ => zero_le _))
      (Eventually.of_forall h_L1_le_L2)
    rw [show (0 : ℝ≥0∞) = 0 * K from by simp]
    exact ENNReal.Tendsto.mul_const h (Or.inr (by
      simp only [K]
      exact ENNReal.rpow_ne_top_of_nonneg (by norm_num) (measure_ne_top μ _)))
  have h_eq : ∀ n, ∫ x in S, ‖f n x - g x‖ =
      (eLpNorm (fun x => f n x - g x) 1 μ).toReal := by
    intro n
    rw [eLpNorm_one_eq_lintegral_enorm]
    exact integral_norm_eq_lintegral_enorm
      ((hf_meas n).sub hg_meas)
  rw [show (0 : ℝ) = (0 : ℝ≥0∞).toReal from by simp]
  exact (Filter.Tendsto.congr (fun n => (h_eq n).symm))
    ((ENNReal.tendsto_toReal (by simp : (0 : ℝ≥0∞) ≠ ⊤)).comp h_L1_tendsto)

omit [NeZero d] in
private theorem exists_ae_tendsto_of_eLpNorm_tendsto
    {S : Set E} (_hS : MeasurableSet S)
    {f : ℕ → E → ℝ} {g : E → ℝ}
    (hf_meas : ∀ n, AEStronglyMeasurable (f n) (volume.restrict S))
    (hg_meas : AEStronglyMeasurable g (volume.restrict S))
    (h : Tendsto (fun n => eLpNorm (fun x => f n x - g x) 2
      (volume.restrict S)) atTop (nhds 0)) :
    ∃ (ns : ℕ → ℕ), StrictMono ns ∧
      ∀ᵐ x ∂(volume.restrict S), Tendsto (fun k => f (ns k) x) atTop (nhds (g x)) := by
  have htim : TendstoInMeasure (volume.restrict S) f atTop g := by
    exact MeasureTheory.tendstoInMeasure_of_tendsto_eLpNorm
      (by norm_num : (2 : ℝ≥0∞) ≠ 0) hf_meas hg_meas h
  exact htim.exists_seq_tendsto_ae

/-! ## Main theorem: chain rule on the unit ball -/

set_option maxHeartbeats 800000 in
theorem sobolev_chain_rule_unitBall
    {u : E → ℝ}
    (hw : MemW1pWitness 2 u (Metric.ball (0 : E) 1))
    (i : Fin d)
    (Φ : ℝ → ℝ) (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (hΦ0 : Φ 0 = 0)
    (hΦ'_bdd : ∃ M, ∀ t, |deriv Φ t| ≤ M) :
    HasWeakPartialDeriv' (d := d) i
      (fun x => deriv Φ (u x) * hw.weakGrad x i)
      (fun x => Φ (u x))
      (Metric.ball (0 : E) 1) := by
  obtain ⟨M, hM⟩ := hΦ'_bdd
  have hM_pos : 0 ≤ M := le_trans (abs_nonneg _) (hM 0)
  have hB_fin : volume (Metric.ball (0 : E) 1) < ⊤ :=
    lt_of_le_of_lt (measure_mono ball_subset_closedBall)
      (isCompact_closedBall (0 : E) 1).measure_lt_top
  obtain ⟨ψ, hψ_smooth, hψ_cs, hψ_L2, hψ_grad⟩ :=
    exists_smooth_W12_approx_on_unitBall (d := d) hw
  obtain ⟨ns, hns_mono, hns_ae⟩ := exists_ae_tendsto_of_eLpNorm_tendsto
    measurableSet_ball
    (fun n => (hψ_smooth n).continuous.aestronglyMeasurable.restrict)
    hw.memLp.aestronglyMeasurable
    hψ_L2
  intro φ hφ hφ_cs hφ_supp
  have hIBP : ∀ n,
      ∫ x in Metric.ball (0 : E) 1, Φ (ψ (ns n) x) *
        (fderiv ℝ φ x) (EuclideanSpace.single i 1) =
      -∫ x in Metric.ball (0 : E) 1, (deriv Φ (ψ (ns n) x) *
        (fderiv ℝ (ψ (ns n)) x) (EuclideanSpace.single i 1)) * φ x := by
    intro n
    exact chain_rule_smooth_ibp isOpen_ball i (hψ_smooth (ns n)) (hψ_cs (ns n)) hΦ hΦ0
      φ hφ hφ_cs hφ_supp
  -- === hLHS ===
  have hLHS : Tendsto
      (fun n => ∫ x in Metric.ball (0 : E) 1, Φ (ψ (ns n) x) *
        (fderiv ℝ φ x) (EuclideanSpace.single i 1))
      atTop
      (nhds (∫ x in Metric.ball (0 : E) 1, Φ (u x) *
        (fderiv ℝ φ x) (EuclideanSpace.single i 1))) := by
    have hΦ_lip : LipschitzWith ⟨M, hM_pos⟩ Φ :=
      lipschitzWith_of_nnnorm_deriv_le (hΦ.differentiable (by simp)) (fun t => by
        simp only [← NNReal.coe_le_coe, NNReal.coe_mk, coe_nnnorm]
        exact (Real.norm_eq_abs _).symm ▸ hM t)
    have hΦ_ptwise : ∀ n x, ‖Φ (ψ (ns n) x) - Φ (u x)‖ ≤ M * ‖ψ (ns n) x - u x‖ := by
      intro n x
      have := hΦ_lip.dist_le_mul (ψ (ns n) x) (u x)
      rwa [Real.dist_eq, Real.dist_eq, NNReal.coe_mk] at this
    set μ := volume.restrict (Metric.ball (0 : E) 1)
    have hΦψ_L2 : Tendsto (fun n => eLpNorm (fun x => Φ (ψ (ns n) x) - Φ (u x)) 2 μ)
        atTop (nhds 0) := by
      have hψ_sub : Tendsto (fun n => eLpNorm (fun x => ψ (ns n) x - u x) 2 μ)
          atTop (nhds 0) := hψ_L2.comp hns_mono.tendsto_atTop
      apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
        (show Tendsto (fun n => ‖(M : ℝ)‖ₑ * eLpNorm (fun x => ψ (ns n) x - u x) 2 μ)
          atTop (nhds 0) from ?_)
        (Eventually.of_forall (fun _ => zero_le _))
        (Eventually.of_forall (fun n => ?_))
      · rw [show (0 : ℝ≥0∞) = ‖(M : ℝ)‖ₑ * 0 from by simp]
        exact ENNReal.Tendsto.const_mul hψ_sub (Or.inr enorm_ne_top)
      · calc eLpNorm (fun x => Φ (ψ (ns n) x) - Φ (u x)) 2 μ
            ≤ eLpNorm (fun x => M * (ψ (ns n) x - u x)) 2 μ := by
              apply eLpNorm_mono (fun x => ?_)
              calc ‖Φ (ψ (ns n) x) - Φ (u x)‖
                  ≤ M * ‖ψ (ns n) x - u x‖ := hΦ_ptwise n x
                _ = ‖M * (ψ (ns n) x - u x)‖ := by
                    simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg hM_pos]
          _ = ‖(M : ℝ)‖ₑ * eLpNorm (fun x => ψ (ns n) x - u x) 2 μ := by
              rw [show (fun x => M * (ψ (ns n) x - u x)) = M • (fun x => ψ (ns n) x - u x)
                from by ext; simp [smul_eq_mul]]
              exact eLpNorm_const_smul M _ _ _
    have hφ_deriv_cont : Continuous (fun x => (fderiv ℝ φ x) (EuclideanSpace.single i 1)) :=
      (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
    have hφ_bdd : ∃ C, ∀ x, |(fderiv ℝ φ x) (EuclideanSpace.single i 1)| ≤ C := by
      obtain ⟨C, hC⟩ := (hφ_cs.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single i 1)).exists_bound_of_continuous
        hφ_deriv_cont
      exact ⟨C, fun x => by rw [← Real.norm_eq_abs]; exact hC x⟩
    exact integral_mul_tendsto_of_eLpNorm_tendsto measurableSet_ball hB_fin
      (fun n => hΦ.continuous.comp_aestronglyMeasurable
        ((hψ_smooth (ns n)).continuous.aestronglyMeasurable.restrict))
      (hΦ.continuous.comp_aestronglyMeasurable hw.memLp.aestronglyMeasurable)
      hΦψ_L2 hφ_bdd hφ_deriv_cont.aestronglyMeasurable.restrict
  -- === hRHS ===
  have hRHS : Tendsto
      (fun n => ∫ x in Metric.ball (0 : E) 1, (deriv Φ (ψ (ns n) x) *
        (fderiv ℝ (ψ (ns n)) x) (EuclideanSpace.single i 1)) * φ x)
      atTop
      (nhds (∫ x in Metric.ball (0 : E) 1,
        (deriv Φ (u x) * hw.weakGrad x i) * φ x)) := by
    obtain ⟨C_φ, hC_φ⟩ : ∃ C, ∀ x, |φ x| ≤ C := by
      obtain ⟨C, hC⟩ := hφ_cs.exists_bound_of_continuous hφ.continuous
      exact ⟨C, fun x => by rw [← Real.norm_eq_abs]; exact hC x⟩
    have hgi_int : IntegrableOn (fun x => hw.weakGrad x i)
        (Metric.ball (0 : E) 1) volume := by
      haveI : IsFiniteMeasure (volume.restrict (Metric.ball (0 : E) 1)) :=
        isFiniteMeasure_restrict.mpr (ne_top_of_lt hB_fin)
      exact (hw.weakGrad_component_memLp i).integrable one_le_two
    -- Term 1: ∫ Φ'(ψ_n)·(∂ᵢψ_n - gi)·φ → 0
    have hT1 : Tendsto
        (fun n => ∫ x in Metric.ball (0 : E) 1, deriv Φ (ψ (ns n) x) *
          ((fderiv ℝ (ψ (ns n)) x) (EuclideanSpace.single i 1) - hw.weakGrad x i) * φ x)
        atTop (nhds 0) := by
      have hgrad_L1 : Tendsto
          (fun n => ∫ x in Metric.ball (0 : E) 1,
            ‖(fderiv ℝ (ψ (ns n)) x) (EuclideanSpace.single i 1) - hw.weakGrad x i‖)
          atTop (nhds 0) :=
        eLpNorm_one_tendsto_of_eLpNorm_two_tendsto hB_fin
          (fun n => ((hψ_smooth (ns n)).continuous_fderiv (by norm_cast)
            |>.clm_apply continuous_const).aestronglyMeasurable.restrict)
          (hw.weakGrad_component_memLp i).aestronglyMeasurable
          ((hψ_grad i).comp hns_mono.tendsto_atTop)
      exact integral_bdd_mul_L1_tendsto measurableSet_ball hB_fin
        hM_pos (fun n x => hM _)
        (fun n =>
          Integrable.sub
            (((hψ_smooth (ns n)).continuous_fderiv (by norm_cast)
              |>.clm_apply continuous_const).continuousOn.integrableOn_compact
                (isCompact_closedBall (0 : E) 1) |>.mono_set ball_subset_closedBall)
            hgi_int)
        hgrad_L1 hC_φ
    -- Term 2: ∫ (Φ'(ψ_n) - Φ'(u))·gi·φ → 0
    have hT2 : Tendsto
        (fun n => ∫ x in Metric.ball (0 : E) 1,
          (deriv Φ (ψ (ns n) x) - deriv Φ (u x)) * (hw.weakGrad x i * φ x))
        atTop (nhds 0) := by
      apply integral_dominated_convergence_term measurableSet_ball
      · intro n x
        have h1 : |deriv Φ (ψ (ns n) x) - deriv Φ (u x)| ≤
            |deriv Φ (ψ (ns n) x)| + |deriv Φ (u x)| := by
          rw [← Real.norm_eq_abs, ← Real.norm_eq_abs (deriv Φ (ψ _ _)),
              ← Real.norm_eq_abs (deriv Φ (u _))]
          exact norm_sub_le _ _
        exact h1.trans (add_le_add (hM _) (hM _))
      · intro n
        have hΦ'_cont : Continuous (deriv Φ) := hΦ.continuous_deriv (by simp)
        exact ((hΦ'_cont.comp (hψ_smooth (ns n)).continuous).aestronglyMeasurable.restrict.sub
          (hΦ'_cont.comp_aestronglyMeasurable hw.memLp.aestronglyMeasurable))
      · filter_upwards [hns_ae] with x hx
        have hΦ'_cont : Continuous (deriv Φ) := hΦ.continuous_deriv (by simp)
        -- Φ'(ψ_n(x)) → Φ'(u(x)) since ψ_n(x) → u(x) and Φ' is continuous
        have h1 : Tendsto (fun k => deriv Φ (ψ (ns k) x)) atTop
            (nhds (deriv Φ (u x))) :=
          (hΦ'_cont.tendsto (u x)).comp hx
        rw [show (0 : ℝ) = deriv Φ (u x) - deriv Φ (u x) from by ring]
        exact h1.sub tendsto_const_nhds
      · exact hgi_int.mul_bdd hφ.continuous.aestronglyMeasurable.restrict
          (Eventually.of_forall (fun x => by rw [Real.norm_eq_abs]; exact hC_φ x))
    -- Algebraic rearrangement + combine T1, T2
    -- Key identity: RHS_n(x) = target(x) + T1_integrand(x) + T2_integrand(x)
    have h_split : ∀ n,
        ∫ x in Metric.ball (0 : E) 1, (deriv Φ (ψ (ns n) x) *
          (fderiv ℝ (ψ (ns n)) x) (EuclideanSpace.single i 1)) * φ x =
        (∫ x in Metric.ball (0 : E) 1, (deriv Φ (u x) * hw.weakGrad x i) * φ x) +
        (∫ x in Metric.ball (0 : E) 1, deriv Φ (ψ (ns n) x) *
          ((fderiv ℝ (ψ (ns n)) x) (EuclideanSpace.single i 1) - hw.weakGrad x i) * φ x) +
        (∫ x in Metric.ball (0 : E) 1, (deriv Φ (ψ (ns n) x) - deriv Φ (u x)) * (hw.weakGrad x i * φ x)) := by
      intro n
      -- Integrability of the three summands (each is bounded × L¹ × bounded on finite measure)
      have hΦ'_cont : Continuous (deriv Φ) := hΦ.continuous_deriv (by simp)
      have hgiφ_int := hgi_int.mul_bdd hφ.continuous.aestronglyMeasurable.restrict
          (Eventually.of_forall (fun x => by rw [Real.norm_eq_abs]; exact hC_φ x))
      have hT2_int : IntegrableOn (fun x =>
          (deriv Φ (ψ (ns n) x) - deriv Φ (u x)) * (hw.weakGrad x i * φ x))
          (Metric.ball (0 : E) 1) volume :=
        hgiφ_int.bdd_mul
          (((hΦ'_cont.comp (hψ_smooth (ns n)).continuous).aestronglyMeasurable.restrict.sub
            (hΦ'_cont.comp_aestronglyMeasurable hw.memLp.aestronglyMeasurable)))
          (Eventually.of_forall (fun x => by
            rw [Real.norm_eq_abs]
            calc |deriv Φ (ψ (ns n) x) - deriv Φ (u x)|
                = ‖deriv Φ (ψ (ns n) x) - deriv Φ (u x)‖ := (Real.norm_eq_abs _).symm
              _ ≤ ‖deriv Φ (ψ (ns n) x)‖ + ‖deriv Φ (u x)‖ := norm_sub_le _ _
              _ ≤ M + M := by
                  rw [Real.norm_eq_abs, Real.norm_eq_abs]
                  exact add_le_add (hM _) (hM _)))
      have hTarget_int : IntegrableOn (fun x =>
          (deriv Φ (u x) * hw.weakGrad x i) * φ x) (Metric.ball (0 : E) 1) volume :=
        (hgi_int.bdd_mul
          (hΦ'_cont.comp_aestronglyMeasurable hw.memLp.aestronglyMeasurable)
          (Eventually.of_forall (fun x => by rw [Real.norm_eq_abs]; exact hM _))).mul_bdd
          hφ.continuous.aestronglyMeasurable.restrict
          (Eventually.of_forall (fun x => by rw [Real.norm_eq_abs]; exact hC_φ x))
      have hT1_int : IntegrableOn (fun x =>
          deriv Φ (ψ (ns n) x) *
            ((fderiv ℝ (ψ (ns n)) x) (EuclideanSpace.single i 1) - hw.weakGrad x i) * φ x)
          (Metric.ball (0 : E) 1) volume :=
        ((Integrable.sub
            (((hψ_smooth (ns n)).continuous_fderiv (by norm_cast)
              |>.clm_apply continuous_const).continuousOn.integrableOn_compact
                (isCompact_closedBall (0 : E) 1) |>.mono_set ball_subset_closedBall)
            hgi_int).bdd_mul
          ((hΦ'_cont.comp (hψ_smooth (ns n)).continuous).aestronglyMeasurable.restrict)
          (Eventually.of_forall (fun x => by rw [Real.norm_eq_abs]; exact hM _))).mul_bdd
          hφ.continuous.aestronglyMeasurable.restrict
          (Eventually.of_forall (fun x => by rw [Real.norm_eq_abs]; exact hC_φ x))
      -- Use linearity of integral + pointwise identity (as function-level equality)
      have h_eq : (fun x => (deriv Φ (ψ (ns n) x) *
          (fderiv ℝ (ψ (ns n)) x) (EuclideanSpace.single i 1)) * φ x) =
          ((fun x => (deriv Φ (u x) * hw.weakGrad x i) * φ x) +
          (fun x => deriv Φ (ψ (ns n) x) *
            ((fderiv ℝ (ψ (ns n)) x) (EuclideanSpace.single i 1) - hw.weakGrad x i) * φ x)) +
          (fun x => (deriv Φ (ψ (ns n) x) - deriv Φ (u x)) * (hw.weakGrad x i * φ x)) := by
        ext x; simp only [Pi.add_apply]; ring
      rw [h_eq, integral_add' (hTarget_int.add hT1_int) hT2_int,
          integral_add' hTarget_int hT1_int]
    -- RHS_n = target + T1_n + T2_n, and T1_n + T2_n → 0
    -- Use sub_tendsto: show ∫ RHS_n - ∫ target = T1_n + T2_n → 0
    apply tendsto_sub_nhds_zero_iff.mp
    have h_sub_eq : ∀ n,
        (∫ x in Metric.ball (0 : E) 1, (deriv Φ (ψ (ns n) x) *
          (fderiv ℝ (ψ (ns n)) x) (EuclideanSpace.single i 1)) * φ x) -
        (∫ x in Metric.ball (0 : E) 1, (deriv Φ (u x) * hw.weakGrad x i) * φ x) =
        (∫ x in Metric.ball (0 : E) 1, deriv Φ (ψ (ns n) x) *
          ((fderiv ℝ (ψ (ns n)) x) (EuclideanSpace.single i 1) - hw.weakGrad x i) * φ x) +
        (∫ x in Metric.ball (0 : E) 1, (deriv Φ (ψ (ns n) x) - deriv Φ (u x)) * (hw.weakGrad x i * φ x)) := by
      intro n; simp only [h_split n]; ring
    refine (Filter.Tendsto.congr (fun n => (h_sub_eq n).symm) ?_)
    rw [show (0 : ℝ) = 0 + 0 from by ring]
    exact hT1.add hT2
  -- Uniqueness of limits: hIBP says LHS_n = -RHS_n, so limit of LHS = -(limit of RHS)
  have hLHS2 : Tendsto
      (fun n => ∫ x in Metric.ball (0 : E) 1, Φ (ψ (ns n) x) *
        (fderiv ℝ φ x) (EuclideanSpace.single i 1))
      atTop (nhds (-∫ x in Metric.ball (0 : E) 1,
        (deriv Φ (u x) * hw.weakGrad x i) * φ x)) := by
    have hIBP' : (fun n => ∫ x in Metric.ball (0 : E) 1, Φ (ψ (ns n) x) *
        (fderiv ℝ φ x) (EuclideanSpace.single i 1)) =
      (fun n => -∫ x in Metric.ball (0 : E) 1, (deriv Φ (ψ (ns n) x) *
        (fderiv ℝ (ψ (ns n)) x) (EuclideanSpace.single i 1)) * φ x) := by
      ext n; exact hIBP n
    rw [hIBP']
    exact hRHS.neg
  exact tendsto_nhds_unique hLHS hLHS2

/-! ## Chain rule on an arbitrary ball -/

/-- Chain rule on an arbitrary ball `B(x₀, R)`. Proved by rescaling to the
unit ball and applying `sobolev_chain_rule_unitBall`. -/
private theorem sobolev_chain_rule_ball
    {x₀ : E} {R : ℝ} (hR : 0 < R)
    {u : E → ℝ}
    (hw : MemW1pWitness 2 u (Metric.ball x₀ R))
    {i : Fin d}
    (Φ : ℝ → ℝ) (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (hΦ0 : Φ 0 = 0)
    (hΦ'_bdd : ∃ M, ∀ t, |deriv Φ t| ≤ M) :
    HasWeakPartialDeriv' (d := d) i
      (fun x => deriv Φ (u x) * hw.weakGrad x i)
      (fun x => Φ (u x))
      (Metric.ball x₀ R) := by
  set hwU := hw.rescale_to_unitBall hR with hwU_def
  -- hwU is a witness for ũ(z) = u(x₀ + R·z) on ball(0,1),
  -- with hwU.weakGrad z i = R * hw.weakGrad (x₀ + R·z) i.
  have hUB := sobolev_chain_rule_unitBall hwU i Φ hΦ hΦ0 hΦ'_bdd
  -- hUB : HasWeakPartialDeriv' i
  --   (fun z => deriv Φ (u(x₀+R·z)) * hwU.weakGrad z i) (fun z => Φ(u(x₀+R·z))) (ball 0 1)
  have cov_helper : ∀ f : E → ℝ,
      ∫ z in Metric.ball (0 : E) 1, f (x₀ + R • z) =
        (R ^ Module.finrank ℝ E)⁻¹ * ∫ x in Metric.ball x₀ R, f x := by
    intro f
    open scoped Pointwise in
    have hscale := Measure.setIntegral_comp_smul_of_pos volume (fun x => f (x₀ + x))
      (Metric.ball (0 : E) 1) hR
    open scoped Pointwise in
    rw [show R • Metric.ball (0 : E) 1 = Metric.ball (0 : E) R from by
      rw [smul_unitBall hR.ne']
      simp [Real.norm_of_nonneg hR.le]] at hscale
    rw [hscale]
    congr 1
    rw [show Metric.ball x₀ R = (x₀ + ·) '' Metric.ball (0 : E) R from by simp]
    exact ((measurePreserving_add_left volume x₀).setIntegral_image_emb
      (MeasurableEquiv.addLeft x₀).measurableEmbedding f (Metric.ball (0 : E) R)).symm
  intro φ hφ hφ_cs hφ_supp
  set T := fun z : E => x₀ + R • z with hT_def
  set ψ : E → ℝ := fun z => φ (x₀ + R • z) with hψ_def
  have hψ_smooth : ContDiff ℝ (⊤ : ℕ∞) ψ :=
    hφ.comp (contDiff_const.add ((contDiff_const_smul R).comp contDiff_id))
  have hψ_cs : HasCompactSupport ψ := by
    set h : E ≃ₜ E := (Homeomorph.smulOfNeZero R (hR.ne')).trans (Homeomorph.addLeft x₀)
    exact (show ψ = φ ∘ h from by
      ext z; simp [ψ, h, Homeomorph.smulOfNeZero, Homeomorph.addLeft]) ▸
      hφ_cs.comp_homeomorph h
  have hψ_supp : tsupport ψ ⊆ Metric.ball (0 : E) 1 := by
    intro z hz
    have hcont : Continuous T := continuous_const.add (continuous_const_smul R)
    have h2 := hφ_supp ((tsupport_comp_subset_preimage φ hcont) hz)
    rw [Metric.mem_ball] at h2 ⊢
    rw [dist_zero_right]
    rw [dist_eq_norm] at h2
    have : x₀ + R • z - x₀ = R • z := by abel
    rw [this, norm_smul, Real.norm_of_nonneg hR.le] at h2
    rwa [show R * ‖z‖ < R ↔ ‖z‖ < 1 from by constructor <;> intro hh <;> nlinarith] at h2
  have hUB_applied := hUB ψ hψ_smooth hψ_cs hψ_supp
  -- hUB_applied :
  --   ∫ z in ball 0 1, Φ(u(x₀+R·z)) * (fderiv ℝ ψ z)(single i 1)
  --     = -∫ z in ball 0 1, (Φ'(u(x₀+R·z)) * hwU.weakGrad z i) * ψ z
  -- ψ = φ ∘ T where T z = x₀ + R·z, so fderiv ψ z = fderiv φ (T z) ∘ (R · id).
  -- Hence (fderiv ψ z)(single i 1) = R * (fderiv φ (T z))(single i 1).
  have hfderiv_ψ : ∀ z : E, (fderiv ℝ ψ z) (EuclideanSpace.single i 1) =
      R * (fderiv ℝ φ (x₀ + R • z)) (EuclideanSpace.single i 1) := by
    intro z
    have hT_fd : HasFDerivAt T (R • ContinuousLinearMap.id ℝ E) z := by
      have h1 := (hasFDerivAt_const (𝕜 := ℝ) x₀ z).add
        ((ContinuousLinearMap.id ℝ E).hasFDerivAt.const_smul R)
      simpa using h1
    have hφ_at : HasFDerivAt φ (fderiv ℝ φ (x₀ + R • z)) (x₀ + R • z) :=
      ((hφ.differentiable (by simp)).differentiableAt).hasFDerivAt
    have h_comp := hφ_at.comp z hT_fd
    rw [show ψ = φ ∘ T from rfl, h_comp.fderiv]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.id_apply, map_smul, smul_eq_mul]
  have hgrad_eq : ∀ z : E, hwU.weakGrad z i = R * hw.weakGrad (x₀ + R • z) i := by
    intro z
    simp [hwU_def, MemW1pWitness.rescale_to_unitBall, smul_eq_mul]
  -- LHS of hUB_applied becomes:
  --   ∫ z in B₁, Φ(u(T z)) * R * (fderiv ℝ φ (T z))(single i 1)
  -- = R * ∫ z in B₁, Φ(u(T z)) * (fderiv ℝ φ (T z))(single i 1)
  -- = R * (R^d)⁻¹ * ∫ x in B_R, Φ(u x) * (fderiv ℝ φ x)(single i 1)    [by cov_helper]
  set c := (R ^ Module.finrank ℝ E)⁻¹ with hc_def
  have lhs_eq :
      ∫ z in Metric.ball (0 : E) 1, Φ (u (x₀ + R • z)) *
        (fderiv ℝ ψ z) (EuclideanSpace.single i 1) =
      R * (c * ∫ x in Metric.ball x₀ R,
        Φ (u x) * (fderiv ℝ φ x) (EuclideanSpace.single i 1)) := by
    simp_rw [hfderiv_ψ, show ∀ z : E,
      Φ (u (x₀ + R • z)) * (R * (fderiv ℝ φ (x₀ + R • z)) (EuclideanSpace.single i 1)) =
        R * (Φ (u (x₀ + R • z)) * (fderiv ℝ φ (x₀ + R • z)) (EuclideanSpace.single i 1))
      from fun z => by ring]
    rw [integral_const_mul]
    congr 1
    exact cov_helper (fun x => Φ (u x) * (fderiv ℝ φ x) (EuclideanSpace.single i 1))
  -- RHS of hUB_applied becomes:
  --   -∫ z in B₁, (Φ'(u(T z)) * R * hw.weakGrad(T z) i) * φ(T z)
  -- = -(R * (R^d)⁻¹ * ∫ x in B_R, (Φ'(u x) * hw.weakGrad x i) * φ x)
  -- (where we factor out R from the inner product using hgrad_eq)
  have rhs_eq :
      -∫ z in Metric.ball (0 : E) 1, (deriv Φ (u (x₀ + R • z)) *
        hwU.weakGrad z i) * ψ z =
      -(R * (c * ∫ x in Metric.ball x₀ R,
        (deriv Φ (u x) * hw.weakGrad x i) * φ x)) := by
    simp_rw [hgrad_eq, hψ_def, show ∀ z : E,
      (deriv Φ (u (x₀ + R • z)) * (R * hw.weakGrad (x₀ + R • z) i)) * φ (x₀ + R • z) =
        R * ((deriv Φ (u (x₀ + R • z)) * hw.weakGrad (x₀ + R • z) i) * φ (x₀ + R • z))
      from fun z => by ring]
    rw [integral_const_mul]
    congr 1
    congr 1
    exact cov_helper (fun x => (deriv Φ (u x) * hw.weakGrad x i) * φ x)
  -- From hUB_applied: lhs_eq.lhs = rhs_eq.lhs
  -- So: R * c * ∫ B_R Φ(u) * ∂ᵢφ = -(R * c * ∫ B_R (Φ'u · gi) · φ)
  -- Since R > 0 and c = (R^d)⁻¹ > 0, we can cancel R * c.
  rw [lhs_eq, rhs_eq] at hUB_applied
  have hRc_pos : 0 < R * c := by
    apply mul_pos hR
    simp only [hc_def]; positivity
  -- hUB_applied : R * (c * LHS) = -(R * (c * RHS))
  -- Cancel R * c > 0.
  nlinarith

/-! ## Localization to general open sets -/

omit [NeZero d] in
/-- The integrals in the weak derivative definition depend only on the values of the
integrand on `tsupport φ`. When `tsupport φ ⊆ Ω' ⊆ Ω`, the set-integral over Ω
equals the set-integral over Ω'. -/
private theorem setIntegral_eq_of_tsupport_subset
    {Ω Ω' : Set E} (hΩ'_sub : Ω' ⊆ Ω)
    {φ : E → ℝ} (hφ_supp : tsupport φ ⊆ Ω')
    {f : E → ℝ} :
    ∫ x in Ω, f x * φ x = ∫ x in Ω', f x * φ x := by
  have h1 : ∀ x, x ∉ Ω' → f x * φ x = 0 := by
    intro x hx
    simp [image_eq_zero_of_notMem_tsupport (fun h => hx (hφ_supp h))]
  have h2 : ∀ x, x ∉ Ω → f x * φ x = 0 :=
    fun x hx => h1 x (fun h => hx (hΩ'_sub h))
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero h1,
      setIntegral_eq_integral_of_forall_compl_eq_zero h2]

omit [NeZero d] in
/-- The fderiv of φ vanishes outside tsupport φ.
If `x ∉ tsupport φ` then `φ =ᶠ[𝓝 x] 0`, so `fderiv ℝ φ x = 0`. -/
private theorem fderiv_eq_zero_of_notMem_tsupport
    {φ : E → ℝ} {x : E} (hx : x ∉ tsupport φ) :
    fderiv ℝ φ x = 0 := by
  have hev : φ =ᶠ[𝓝 x] 0 :=
    (isClosed_tsupport (f := φ)).isOpen_compl.eventually_mem hx |>.mono
      (fun y hy => image_eq_zero_of_notMem_tsupport hy)
  rw [Filter.EventuallyEq.fderiv_eq hev]
  simp

omit [NeZero d] in
private theorem setIntegral_fderiv_eq_of_tsupport_subset
    {Ω Ω' : Set E} (hΩ'_sub : Ω' ⊆ Ω)
    {φ : E → ℝ} (_hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφ_supp : tsupport φ ⊆ Ω')
    {f : E → ℝ} (i : Fin d) :
    ∫ x in Ω, f x * (fderiv ℝ φ x) (EuclideanSpace.single i 1) =
    ∫ x in Ω', f x * (fderiv ℝ φ x) (EuclideanSpace.single i 1) := by
  have h1 : ∀ x, x ∉ Ω' → f x * (fderiv ℝ φ x) (EuclideanSpace.single i 1) = 0 := by
    intro x hx
    have hx_notin : x ∉ tsupport φ := fun h => hx (hφ_supp h)
    have hφ_eq : φ =ᶠ[𝓝 x] 0 :=
      (isClosed_tsupport (f := φ)).isOpen_compl.eventually_mem hx_notin |>.mono
        (fun y hy => image_eq_zero_of_notMem_tsupport hy)
    rw [Filter.EventuallyEq.fderiv_eq hφ_eq]; simp
  have h2 : ∀ x, x ∉ Ω → f x * (fderiv ℝ φ x) (EuclideanSpace.single i 1) = 0 :=
    fun x hx => h1 x (fun h => hx (hΩ'_sub h))
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero h1,
      setIntegral_eq_integral_of_forall_compl_eq_zero h2]

omit [NeZero d] in
set_option maxHeartbeats 3200000 in
/-- Local-to-global for `HasWeakPartialDeriv'`: if the property holds on every
ball `B(x, r) ⊆ Ω` (with `x ∈ Ω`), then it holds on `Ω`.

The proof uses a smooth partition of unity to decompose a test function `φ`
(with `tsupport φ ⊆ Ω`) into finitely many pieces, each supported in a ball
`B ⊆ Ω`. The IBP identity is applied to each piece on its ball, converted to `Ω`
(since the integrands vanish outside the ball), then summed. -/
private theorem HasWeakPartialDeriv'_of_local
    {Ω : Set E} (hΩ : IsOpen Ω)
    {i : Fin d} {g f : E → ℝ}
    (hf_loc : LocallyIntegrable f (volume.restrict Ω))
    (hg_loc : LocallyIntegrable g (volume.restrict Ω))
    (hloc : ∀ x₀ ∈ Ω, ∀ r > 0, Metric.ball x₀ r ⊆ Ω →
      HasWeakPartialDeriv' (d := d) i g f (Metric.ball x₀ r)) :
    HasWeakPartialDeriv' (d := d) i g f Ω := by
  intro φ hφ hφ_cs hφ_supp
  set K := tsupport φ
  have hK_compact : IsCompact K := hφ_cs
  have hK_closed : IsClosed K := isClosed_tsupport φ
  -- For each x ∈ K ⊆ Ω, pick a ball in Ω
  have hR : ∀ (x : K), ∃ r, 0 < r ∧ Metric.ball (x : E) r ⊆ Ω := by
    intro ⟨x, hx⟩; exact Metric.isOpen_iff.mp hΩ x (hφ_supp hx)
  set U : K → Set E := fun x => Metric.ball (x : E) (hR x).choose
  have hU_pos : ∀ x : K, 0 < (hR x).choose := fun x => (hR x).choose_spec.1
  have hU_sub : ∀ x : K, U x ⊆ Ω := fun x => (hR x).choose_spec.2
  have hcover : K ⊆ ⋃ (x : K), U x :=
    fun x hx => mem_iUnion.mpr ⟨⟨x, hx⟩, Metric.mem_ball_self (hU_pos ⟨x, hx⟩)⟩
  -- Smooth partition of unity subordinate to {U x}
  obtain ⟨ρ, hρ_sub⟩ := SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ, E) hK_closed
    U (fun _ => isOpen_ball) hcover
  have hρ_fin_supp : ∀ x, (support (fun k => (ρ k : E → ℝ) x)).Finite :=
    fun x => ρ.locallyFinite.point_finite x
  have hρ_smooth : ∀ k, ContDiff ℝ (⊤ : ℕ∞) (ρ k : E → ℝ) :=
    fun k => contMDiff_iff_contDiff.mp (ρ k).contMDiff
  -- ψ_k := ρ_k * φ is smooth, compactly supported, with tsupport ⊆ ball_k
  have hψ_smooth : ∀ k, ContDiff ℝ (⊤ : ℕ∞) (fun x => (ρ k : E → ℝ) x * φ x) :=
    fun k => (hρ_smooth k).mul hφ
  have hψ_tsupp_ρ : ∀ k, tsupport (fun x => (ρ k : E → ℝ) x * φ x) ⊆ tsupport (ρ k : E → ℝ) := by
    intro k; apply closure_minimal _ (isClosed_tsupport _)
    intro x hx; simp only [mem_support] at hx
    exact subset_tsupport _ (left_ne_zero_of_mul hx)
  have hψ_supp_ball : ∀ k, tsupport (fun x => (ρ k : E → ℝ) x * φ x) ⊆ U k :=
    fun k => (hψ_tsupp_ρ k).trans (hρ_sub k)
  have hψ_cs : ∀ k, HasCompactSupport (fun x => (ρ k : E → ℝ) x * φ x) := by
    intro k
    apply IsCompact.of_isClosed_subset hK_compact (isClosed_tsupport _)
    apply closure_minimal _ (isClosed_tsupport φ)
    intro x hx; simp only [mem_support] at hx
    exact subset_tsupport φ (right_ne_zero_of_mul hx)
  -- φ = Σᶠ ρ_k · φ pointwise
  have hφ_sum : ∀ x, φ x = ∑ᶠ k, (ρ k : E → ℝ) x * φ x := by
    intro x
    by_cases hx : x ∈ K
    · conv_lhs => rw [show φ x = 1 * φ x from (one_mul _).symm, ← ρ.sum_eq_one hx]
      exact finsum_mul' (fun k => (ρ k : E → ℝ) x) (φ x) (hρ_fin_supp x)
    · simp [image_eq_zero_of_notMem_tsupport hx]
  -- For each k: IBP on ball_k, converted to Ω
  have hIBP_Ω : ∀ k : K,
      ∫ x in Ω, f x * (fderiv ℝ (fun x => (ρ k : E → ℝ) x * φ x) x) (EuclideanSpace.single i 1) =
        -∫ x in Ω, g x * ((ρ k : E → ℝ) x * φ x) := by
    intro k
    have hIBP_ball := hloc (k : E) (hU_sub k (Metric.mem_ball_self (hU_pos k)))
      (hR k).choose (hU_pos k) (hU_sub k)
      (fun x => (ρ k : E → ℝ) x * φ x) (hψ_smooth k) (hψ_cs k) (hψ_supp_ball k)
    rw [setIntegral_fderiv_eq_of_tsupport_subset (hU_sub k) (hψ_smooth k) (hψ_supp_ball k),
        setIntegral_eq_of_tsupport_subset (hU_sub k) (hψ_supp_ball k)]
    exact hIBP_ball
  -- Finite set S of active POU indices (those with support meeting K)
  have hS_fin : {k : K | (support (ρ k : E → ℝ) ∩ K).Nonempty}.Finite :=
    ρ.locallyFinite.finite_nonempty_inter_compact hK_compact
  set S := hS_fin.toFinset
  -- φ = Σ_{k ∈ S} ρ_k * φ (finite sum)
  have hfinsum_eq_finset : ∀ x,
      ∑ᶠ k, (ρ k : E → ℝ) x * φ x = ∑ k ∈ S, (ρ k : E → ℝ) x * φ x := by
    intro x
    refine finsum_eq_sum_of_support_subset _ (fun k hk => ?_)
    rw [mem_support] at hk
    show k ∈ S; rw [Finite.mem_toFinset]; show (support (ρ k : E → ℝ) ∩ K).Nonempty
    by_cases hx : x ∈ K
    · exact ⟨x, mem_support.mpr (left_ne_zero_of_mul hk), hx⟩
    · exact absurd (image_eq_zero_of_notMem_tsupport hx) (right_ne_zero_of_mul hk)
  have hφ_finsum : ∀ x, φ x = ∑ k ∈ S, (ρ k : E → ℝ) x * φ x :=
    fun x => (hφ_sum x).trans (hfinsum_eq_finset x)
  -- Decompose g·φ and f·∂ᵢφ as finite sums
  have hgφ_sum : ∀ x, g x * φ x = ∑ k ∈ S, g x * ((ρ k : E → ℝ) x * φ x) := by
    intro x; conv_lhs => rw [hφ_finsum x]; rw [Finset.mul_sum]
  have hfun_eq : (fun x => ∑ k ∈ S, (ρ k : E → ℝ) x * φ x) =
      ∑ k ∈ S, (fun x => (ρ k : E → ℝ) x * φ x) := by
    ext x; simp [Finset.sum_apply]
  have hfderiv_sum : ∀ x,
      (fderiv ℝ φ x) (EuclideanSpace.single i 1) =
      ∑ k ∈ S, (fderiv ℝ (fun x => (ρ k : E → ℝ) x * φ x) x) (EuclideanSpace.single i 1) := by
    intro x
    have heq : φ = fun x => ∑ k ∈ S, (ρ k : E → ℝ) x * φ x := funext hφ_finsum
    have hfd_sum : fderiv ℝ (fun x => ∑ k ∈ S, (ρ k : E → ℝ) x * φ x) x =
        ∑ k ∈ S, fderiv ℝ (fun x => (ρ k : E → ℝ) x * φ x) x := by
      rw [hfun_eq]; exact fderiv_sum (fun k _ => (hψ_smooth k).differentiable (by simp) x)
    conv_lhs => rw [show φ = fun x => ∑ k ∈ S, (ρ k : E → ℝ) x * φ x from heq]
    rw [hfd_sum, ContinuousLinearMap.sum_apply]
  have hf_dφ_sum : ∀ x,
      f x * (fderiv ℝ φ x) (EuclideanSpace.single i 1) =
      ∑ k ∈ S, f x * (fderiv ℝ (fun x => (ρ k : E → ℝ) x * φ x) x) (EuclideanSpace.single i 1) := by
    intro x; rw [hfderiv_sum x, Finset.mul_sum]
  -- Assembly: ∫_Ω f·∂ᵢφ = Σ_k ∫_Ω f·∂ᵢ(ρ_k·φ) = -Σ_k ∫_Ω g·(ρ_k·φ) = -∫_Ω g·φ
  calc ∫ x in Ω, f x * (fderiv ℝ φ x) (EuclideanSpace.single i 1)
      = ∫ x in Ω, ∑ k ∈ S, f x * (fderiv ℝ (fun x => (ρ k : E → ℝ) x * φ x) x) (EuclideanSpace.single i 1) := by
        congr 1; ext x; exact hf_dφ_sum x
    _ = ∑ k ∈ S, ∫ x in Ω, f x * (fderiv ℝ (fun x => (ρ k : E → ℝ) x * φ x) x) (EuclideanSpace.single i 1) := by
        rw [integral_finset_sum S (fun k _ => by
          let ψk : E → ℝ := fun x => (ρ k : E → ℝ) x * φ x
          have hψk_cont : Continuous (fun x =>
              (fderiv ℝ ψk x) (EuclideanSpace.single i 1)) :=
            ((hψ_smooth k).continuous_fderiv (by simp)).clm_apply continuous_const
          have hψk_cs : HasCompactSupport (fun x =>
              (fderiv ℝ ψk x) (EuclideanSpace.single i 1)) :=
            (hψ_cs k).fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single i 1)
          simpa [ψk, smul_eq_mul] using
            hf_loc.integrable_smul_right_of_hasCompactSupport hψk_cont hψk_cs)]
    _ = ∑ k ∈ S, -(∫ x in Ω, g x * ((ρ k : E → ℝ) x * φ x)) := by
        congr 1; ext k; exact hIBP_Ω k
    _ = -(∑ k ∈ S, ∫ x in Ω, g x * ((ρ k : E → ℝ) x * φ x)) :=
        by rw [Finset.sum_neg_distrib]
    _ = -(∫ x in Ω, ∑ k ∈ S, g x * ((ρ k : E → ℝ) x * φ x)) := by
        congr 1
        rw [integral_finset_sum S (fun k _ => by
          let ψk : E → ℝ := fun x => (ρ k : E → ℝ) x * φ x
          simpa [ψk, smul_eq_mul] using
            hg_loc.integrable_smul_right_of_hasCompactSupport
              (hψ_smooth k).continuous (hψ_cs k))]
    _ = -(∫ x in Ω, g x * φ x) := by
        congr 1; congr 1; ext x; exact (hgφ_sum x).symm

/-! ## Main localization theorem -/

/-- Build a `MemW1pWitness` from the propositional `MemW1p` using choice. -/
private noncomputable def MemW1p.toWitness
    {p : ℝ≥0∞} {f : E → ℝ} {Ω : Set E} (hu : MemW1p (d := d) p f Ω) :
    MemW1pWitness p f Ω where
  memLp := hu.1
  weakGrad := fun x => (WithLp.toLp 2 fun j => (hu.2 j).choose x : E)
  weakGrad_component_memLp := fun j => by
    show MemLp (fun x => (WithLp.toLp 2 fun j' => (hu.2 j').choose x : E) j) p _
    simpa using (hu.2 j).choose_spec.1
  isWeakGrad := fun j => by
    show HasWeakPartialDeriv (d := d) j
      (fun x => (WithLp.toLp 2 fun j' => (hu.2 j').choose x : E) j) f Ω
    simpa using (hu.2 j).choose_spec.2

set_option maxHeartbeats 400000 in
theorem sobolev_chain_rule
    {Ω : Set E} (hΩ : IsOpen Ω)
    {u : E → ℝ} {g : E → ℝ} {i : Fin d}
    (hwd : HasWeakPartialDeriv' (d := d) i g u Ω)
    (hu : MemW1p 2 u Ω)
    (hg_Lp : MemLp g 2 (volume.restrict Ω))
    (Φ : ℝ → ℝ) (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (hΦ0 : Φ 0 = 0)
    (hΦ'_bdd : ∃ M, ∀ t, |deriv Φ t| ≤ M) :
    HasWeakPartialDeriv' (d := d) i (fun x => deriv Φ (u x) * g x) (fun x => Φ (u x)) Ω := by
  set hw := hu.toWitness with hw_def
  set gi := fun x => hw.weakGrad x i with gi_def
  have hgi_Lp : MemLp gi 2 (volume.restrict Ω) := hw.weakGrad_component_memLp i
  have hgi_weak : HasWeakPartialDeriv (d := d) i gi u Ω := hw.isWeakGrad i
  -- Both are weak i-derivatives of u, both in L²(Ω) ⊆ L^1_loc(Ω).
  have hg_ae : g =ᵐ[volume.restrict Ω] gi := by
    exact HasWeakPartialDeriv.ae_eq hΩ
      (show HasWeakPartialDeriv (d := d) i g u Ω by
        simpa [HasWeakPartialDeriv, HasWeakPartialDeriv'] using hwd)
      hgi_weak
      (hg_Lp.locallyIntegrable (by norm_num : (1 : ℝ≥0∞) ≤ 2))
      (hgi_Lp.locallyIntegrable (by norm_num : (1 : ℝ≥0∞) ≤ 2))
  suffices h : HasWeakPartialDeriv' (d := d) i
      (fun x => deriv Φ (u x) * gi x) (fun x => Φ (u x)) Ω by
    intro φ hφ hφ_cs hφ_supp
    have key := h φ hφ hφ_cs hφ_supp
    -- Replace gi by g in the RHS using g =ᵐ gi.
    convert key using 2
    -- Goal: ∫_Ω (Φ'(u) * g) * φ = ∫_Ω (Φ'(u) * gi) * φ
    -- Use integral_congr_ae on the restricted measure.
    apply integral_congr_ae
    -- Goal: ∀ᵐ x ∂(volume.restrict Ω), (Φ'(u x) * g x) * φ x = (Φ'(u x) * gi x) * φ x
    filter_upwards [hg_ae] with x hx
    rw [hx]
  obtain ⟨M, hM⟩ := hΦ'_bdd
  have hM_pos : 0 ≤ M := le_trans (abs_nonneg _) (hM 0)
  -- Use HasWeakPartialDeriv'_of_local: prove on every ball, then extend to Ω.
  apply HasWeakPartialDeriv'_of_local hΩ
  · -- Φ ∘ u is locally integrable on Ω
    have hu_loc : LocallyIntegrable u (volume.restrict Ω) :=
      hw.memLp.locallyIntegrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    have hMu_loc : LocallyIntegrable (fun x => M * u x) (volume.restrict Ω) := by
      simpa [smul_eq_mul] using hu_loc.smul M
    have hΦ_lip : LipschitzWith ⟨M, hM_pos⟩ Φ :=
      lipschitzWith_of_nnnorm_deriv_le (hΦ.differentiable (by simp)) (fun t => by
        simp only [← NNReal.coe_le_coe, NNReal.coe_mk, coe_nnnorm]
        exact (Real.norm_eq_abs _).symm ▸ hM t)
    have hΦ_abs_le : ∀ t, |Φ t| ≤ M * |t| := by
      intro t
      have ht := hΦ_lip.dist_le_mul t 0
      simp [hΦ0, Real.norm_eq_abs] at ht
      exact ht
    exact hMu_loc.mono
      (hΦ.continuous.comp_aestronglyMeasurable hw.memLp.aestronglyMeasurable)
      (Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs]
        simpa [Real.norm_eq_abs, abs_mul, abs_of_nonneg hM_pos] using hΦ_abs_le (u x))
  · -- Φ'(u) · gi is locally integrable on Ω
    have hgi_loc : LocallyIntegrable gi (volume.restrict Ω) :=
      hgi_Lp.locallyIntegrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    have hMgi_loc : LocallyIntegrable (fun x => M * gi x) (volume.restrict Ω) := by
      simpa [smul_eq_mul] using hgi_loc.smul M
    exact hMgi_loc.mono
      (((hΦ.continuous_deriv (by simp)).comp_aestronglyMeasurable
        hw.memLp.aestronglyMeasurable).mul hgi_Lp.aestronglyMeasurable)
      (Eventually.of_forall fun x => by
        calc
          ‖deriv Φ (u x) * gi x‖ = |deriv Φ (u x)| * |gi x| := by
            rw [Real.norm_eq_abs, abs_mul]
          _ ≤ M * |gi x| := mul_le_mul_of_nonneg_right (hM (u x)) (abs_nonneg _)
          _ = ‖M * gi x‖ := by
            rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hM_pos])
  intro x₀ _hx₀ r hr hball
  -- On ball x₀ r ⊆ Ω, restrict the witness and apply sobolev_chain_rule_ball.
  let hw_ball := MemW1pWitness.restrict (d := d) isOpen_ball hball hw
  -- hw_ball.weakGrad = hw.weakGrad (same function, restricted domain)
  -- So hw_ball.weakGrad · i = gi
  -- Apply chain rule on the ball
  -- Apply chain rule on the ball.
  -- sobolev_chain_rule_ball gives:
  --   HasWeakPartialDeriv' i (fun x => deriv Φ (u x) * hw_ball.weakGrad x i) (Φ ∘ u) (ball x₀ r)
  -- Since hw_ball = MemW1pWitness.restrict isOpen_ball hball hw,
  -- hw_ball.weakGrad = hw.weakGrad, so hw_ball.weakGrad x i = gi x.
  -- We unfold to show the two functions are the same.
  exact sobolev_chain_rule_ball hr hw_ball (i := i) Φ hΦ hΦ0 ⟨M, hM⟩

end DeGiorgi
