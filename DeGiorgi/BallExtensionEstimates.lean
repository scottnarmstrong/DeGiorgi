import DeGiorgi.BallExtension
import DeGiorgi.LpFunctionToolkit

/-!
# Chapter 02: Ball Extension Estimates

This file contains the rough-input extension theorem and its supporting
Cauchy and convergence machinery. It builds on the extension results in
`BallExtension.lean` together with the bare-function `Lp` toolkit.
-/

noncomputable section

open MeasureTheory Metric Filter Topology Set Function Matrix
open scoped ENNReal NNReal RealInnerProductSpace

namespace DeGiorgi

variable {d : ℕ} [NeZero d]

local notation "E" => EuclideanSpace ℝ (Fin d)

-- Componentwise `L^p` Cauchy control produces a Euclidean-valued limit with
-- matching componentwise convergence.
omit [NeZero d] in
private theorem cauchy_Lp_component_limit
    {p : ℝ} (hp : 1 < p)
    {G : ℕ → E → E}
    (hG_comp_memLp : ∀ n i, MemLp (fun x => G n x i) (ENNReal.ofReal p) volume)
    -- COMPONENT-level Cauchy (from the mathematical Cauchy bound argument):
    (hG_comp_cauchy : ∀ i : Fin d, Tendsto (fun nm : ℕ × ℕ =>
      eLpNorm (fun x => G nm.1 x i - G nm.2 x i) (ENNReal.ofReal p) volume)
      atTop (nhds 0)) :
    ∃ Gext : E → E,
      (∀ i : Fin d, MemLp (fun x => Gext x i) (ENNReal.ofReal p) volume) ∧
      ∀ i : Fin d,
        Tendsto (fun n => eLpNorm (fun x => G n x i - Gext x i)
          (ENNReal.ofReal p) volume) atTop (nhds 0) := by
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    simpa using ENNReal.ofReal_le_ofReal hp.le
  have hcomp_limit : ∀ i : Fin d, ∃ g_i : E → ℝ,
      MemLp g_i (ENNReal.ofReal p) volume ∧
      Tendsto (fun n => eLpNorm (fun x => G n x i - g_i x) (ENNReal.ofReal p) volume)
        atTop (nhds 0) := by
    intro i
    exact BareFunction.scalar_cauchy_to_limit hp1 (by simp)
      (fun n => hG_comp_memLp n i) (hG_comp_cauchy i)
  choose g_i hg_i_memLp hg_i_tendsto using hcomp_limit
  -- Assemble vector limit: Gext x = (g_0 x, g_1 x, ..., g_{d-1} x) as EuclideanSpace
  refine ⟨fun x => EuclideanSpace.equiv (ι := Fin d) ℝ |>.symm (fun i => g_i i x),
    fun i => ?_, fun i => ?_⟩
  · convert hg_i_memLp i using 1
  · convert hg_i_tendsto i using 2

omit [NeZero d] in
private theorem aestronglyMeasurable_euclidean_of_components
    {μ : Measure E} {G : E → E}
    (hG_comp : ∀ i : Fin d, AEStronglyMeasurable (fun x => G x i) μ) :
    AEStronglyMeasurable G μ := by
  have h_ofLp : AEMeasurable (fun x => (WithLp.ofLp (G x) : Fin d → ℝ)) μ := by
    rw [aemeasurable_pi_iff]
    intro i
    simpa using (hG_comp i).aemeasurable
  have h_toLp_cont : Continuous (fun x : Fin d → ℝ => WithLp.toLp 2 x) := by
    simpa using (PiLp.continuous_toLp 2 (fun _ : Fin d => ℝ))
  have h_toLp_meas : Measurable (fun x : Fin d → ℝ => WithLp.toLp 2 x) :=
    h_toLp_cont.measurable
  have h_id : (fun x => WithLp.toLp 2 (WithLp.ofLp (G x))) = G := by
    funext x
    simp
  exact (h_toLp_meas.comp_aemeasurable h_ofLp).aestronglyMeasurable.congr <|
    EventuallyEq.of_eq h_id

omit [NeZero d] in
private theorem euclidean_eLpNorm_le_component_sum
    {μ : Measure E} {p : ℝ} (hp : 1 ≤ p) {F : E → E}
    (hF_comp_aesm : ∀ i : Fin d, AEStronglyMeasurable (fun x => F x i) μ) :
    eLpNorm F (ENNReal.ofReal p) μ ≤
      ∑ i : Fin d, eLpNorm (fun x => F x i) (ENNReal.ofReal p) μ := by
  let δ : Fin d → E → ℝ := fun i x => F x i
  have hPointwise :
      ∀ᵐ x ∂μ, ‖F x‖ ≤ ∑ i : Fin d, ‖δ i x‖ := by
    filter_upwards with x
    have hsplit : F x = ∑ i : Fin d, EuclideanSpace.single i (δ i x) := by
      ext i
      simp [δ, Finset.sum_apply]
    calc
      ‖F x‖ = ‖∑ i : Fin d, EuclideanSpace.single i (δ i x)‖ := by
          rw [hsplit]
      _ ≤ ∑ i : Fin d, ‖EuclideanSpace.single i (δ i x)‖ := by
          exact norm_sum_le _ _
      _ = ∑ i : Fin d, ‖δ i x‖ := by
          simp [δ]
  calc
    eLpNorm F (ENNReal.ofReal p) μ
        ≤ eLpNorm (fun x => ∑ i : Fin d, ‖δ i x‖) (ENNReal.ofReal p) μ := by
          exact eLpNorm_mono_ae_real hPointwise
    _ ≤ ∑ i : Fin d, eLpNorm (fun x => ‖δ i x‖) (ENNReal.ofReal p) μ := by
        have hp_enn : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
          rwa [← ENNReal.ofReal_one, ENNReal.ofReal_le_ofReal_iff (by linarith)]
        convert eLpNorm_sum_le (s := Finset.univ) (f := fun i => fun x => ‖δ i x‖)
          (fun i _ => (hF_comp_aesm i).norm) hp_enn using 1
        congr 1
        ext x
        simp [δ, Finset.sum_apply]
    _ = ∑ i : Fin d, eLpNorm (δ i) (ENNReal.ofReal p) μ := by
        congr 1
        ext i
        simpa [δ] using (eLpNorm_norm (f := δ i) (p := ENNReal.ofReal p) (μ := μ))
    _ = ∑ i : Fin d, eLpNorm (fun x => F x i) (ENNReal.ofReal p) μ := by
        simp [δ]

omit [NeZero d] in
private theorem memLp_euclidean_of_components
    {μ : Measure E} {p : ℝ} (hp : 1 ≤ p) {G : E → E}
    (hG_comp : ∀ i : Fin d, MemLp (fun x => G x i) (ENNReal.ofReal p) μ) :
    MemLp G (ENNReal.ofReal p) μ := by
  refine ⟨aestronglyMeasurable_euclidean_of_components (μ := μ)
      (fun i => (hG_comp i).aestronglyMeasurable), ?_⟩
  refine lt_of_le_of_lt
    (euclidean_eLpNorm_le_component_sum (d := d) (μ := μ) (p := p) hp
      (fun i => (hG_comp i).aestronglyMeasurable)) ?_
  have hsum :
      ∑ i : Fin d, eLpNorm (fun x => G x i) (ENNReal.ofReal p) μ < ∞ := by
    have hsum' :
        Finset.sum Finset.univ (fun i : Fin d => eLpNorm (fun x => G x i) (ENNReal.ofReal p) μ) < ∞ := by
      exact (ENNReal.sum_lt_top).2 (fun i _ => (hG_comp i).eLpNorm_lt_top)
    simpa using hsum'
  exact hsum

set_option maxHeartbeats 3200000 in
theorem exists_smooth_global_approx_of_unitBallExtension
    {p : ℝ} (hp : 1 < p) {u : E → ℝ}
    (hw : MemW1pWitness (ENNReal.ofReal p) u (Metric.ball (0 : E) 1)) :
    ∃ Gext : E → E,
      MemLp (unitBallExtension (d := d) u) (ENNReal.ofReal p) volume ∧
      (∀ i : Fin d, MemLp (fun x => Gext x i) (ENNReal.ofReal p) volume) ∧
      (∫⁻ x, (ENNReal.ofReal |unitBallExtension (d := d) u x|) ^ p ∂volume)
        ≤ C_unitBallExtensionFun d *
          ∫⁻ x in Metric.ball (0 : E) 1, (ENNReal.ofReal |u x|) ^ p ∂volume ∧
      (∫⁻ x, (ENNReal.ofReal ‖Gext x‖) ^ p ∂volume)
        ≤ (∫⁻ x in Metric.ball (0 : E) 1, (ENNReal.ofReal ‖hw.weakGrad x‖) ^ p ∂volume) +
          C_unitBallExtensionGrad d p *
            (∫⁻ x in Metric.ball (0 : E) 1, (ENNReal.ofReal |u x|) ^ p ∂volume +
             ∫⁻ x in Metric.ball (0 : E) 1, (ENNReal.ofReal ‖hw.weakGrad x‖) ^ p ∂volume) ∧
      ∃ Φ : ℕ → E → ℝ,
        (∀ n, ContDiff ℝ (⊤ : ℕ∞) (Φ n)) ∧
        (∀ n, HasCompactSupport (Φ n)) ∧
        Tendsto
          (fun n =>
            eLpNorm (fun x => Φ n x - unitBallExtension (d := d) u x)
              (ENNReal.ofReal p) volume)
          atTop (nhds 0) ∧
        ∀ i : Fin d,
          Tendsto
            (fun n =>
              eLpNorm
                (fun x => (fderiv ℝ (Φ n) x) (EuclideanSpace.single i 1) - Gext x i)
                (ENNReal.ofReal p) volume)
            atTop (nhds 0) := by
  rcases exists_smooth_W1p_approx_on_unitBall (d := d) (p := p) hp hw with
    ⟨ψ, hψ_smooth, hψ_cpt, hψ_fun, hψ_grad⟩
  let B : Set E := Metric.ball (0 : E) 1
  let μB : Measure E := volume.restrict B
  -- Apply Layer 3 to each ψ_n
  have h_step : ∀ n,
      ∃ Gψ : E → E,
        MemLp (unitBallExtension (d := d) (ψ n)) (ENNReal.ofReal p) volume ∧
        (∀ i : Fin d, MemLp (fun x => Gψ x i) (ENNReal.ofReal p) volume) ∧
        (∫⁻ x, (ENNReal.ofReal |unitBallExtension (d := d) (ψ n) x|) ^ p ∂volume)
          ≤ C_unitBallExtensionFun d *
            ∫⁻ x in B, (ENNReal.ofReal |ψ n x|) ^ p ∂volume ∧
        (∫⁻ x, (ENNReal.ofReal ‖Gψ x‖) ^ p ∂volume)
          ≤ (∫⁻ x in B, (ENNReal.ofReal ‖fderiv ℝ (ψ n) x‖) ^ p ∂volume) +
            C_unitBallExtensionGrad d p *
              (∫⁻ x in B, (ENNReal.ofReal |ψ n x|) ^ p ∂volume +
               ∫⁻ x in B, (ENNReal.ofReal ‖fderiv ℝ (ψ n) x‖) ^ p ∂volume) ∧
        ∃ Φ : ℕ → E → ℝ,
          (∀ m, ContDiff ℝ (⊤ : ℕ∞) (Φ m)) ∧
          (∀ m, HasCompactSupport (Φ m)) ∧
          Tendsto (fun m => eLpNorm (fun x => Φ m x - unitBallExtension (d := d) (ψ n) x)
            (ENNReal.ofReal p) volume) atTop (nhds 0) ∧
          ∀ i : Fin d,
            Tendsto (fun m => eLpNorm
              (fun x => (fderiv ℝ (Φ m) x) (EuclideanSpace.single i 1) - Gψ x i)
              (ENNReal.ofReal p) volume) atTop (nhds 0) :=
    fun n => smooth_input_unitBallExtension_smoothing (d := d) hp (hψ_smooth n) (hψ_cpt n)
  let G : ℕ → E → E := fun n => Classical.choose (h_step n)
  have hV_memLp : ∀ n, MemLp (unitBallExtension (d := d) (ψ n)) (ENNReal.ofReal p) volume :=
    fun n => (Classical.choose_spec (h_step n)).1
  have hG_comp_memLp : ∀ n i, MemLp (fun x => G n x i) (ENNReal.ofReal p) volume :=
    fun n i => (Classical.choose_spec (h_step n)).2.1 i
  have hG_bound : ∀ n,
      (∫⁻ x, (ENNReal.ofReal ‖G n x‖) ^ p ∂volume)
        ≤ (∫⁻ x in B, (ENNReal.ofReal ‖fderiv ℝ (ψ n) x‖) ^ p ∂volume) +
          C_unitBallExtensionGrad d p *
            (∫⁻ x in B, (ENNReal.ofReal |ψ n x|) ^ p ∂volume +
             ∫⁻ x in B, (ENNReal.ofReal ‖fderiv ℝ (ψ n) x‖) ^ p ∂volume) :=
    fun n => (Classical.choose_spec (h_step n)).2.2.2.1
  have h_step_approx : ∀ n, ∃ Φ : ℕ → E → ℝ,
      (∀ m, ContDiff ℝ (⊤ : ℕ∞) (Φ m)) ∧ (∀ m, HasCompactSupport (Φ m)) ∧
      Tendsto (fun m => eLpNorm (fun x => Φ m x - unitBallExtension (d := d) (ψ n) x)
        (ENNReal.ofReal p) volume) atTop (nhds 0) ∧
      ∀ i : Fin d, Tendsto (fun m => eLpNorm
        (fun x => (fderiv ℝ (Φ m) x) (EuclideanSpace.single i 1) - G n x i)
        (ENNReal.ofReal p) volume) atTop (nhds 0) :=
    fun n => (Classical.choose_spec (h_step n)).2.2.2.2
  have hV_wd : ∀ n i,
      HasWeakPartialDeriv i (fun x => G n x i)
        (unitBallExtension (d := d) (ψ n)) Set.univ := by
    intro n i
    rcases h_step_approx n with ⟨Φn, hΦn_smooth, hΦn_cpt, hΦn_fun, hΦn_grad⟩
    exact (hasWeakPartials_of_global_smoothApprox (d := d) hp
      (hV_memLp n) (fun j => hG_comp_memLp n j)
      hΦn_smooth hΦn_cpt hΦn_fun hΦn_grad) i
  letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨by simpa using ENNReal.ofReal_le_ofReal hp.le⟩
  -- Function energy bound (doesn't need MemLp)
  have huExt_fun_bound :
      (∫⁻ x, (ENNReal.ofReal |unitBallExtension (d := d) u x|) ^ p ∂volume)
        ≤ C_unitBallExtensionFun d *
          ∫⁻ x in B, (ENNReal.ofReal |u x|) ^ p ∂volume := by
    have h0 := lintegral_rpow_abs_unitBallExtension_sub_le_local (d := d) (p := p)
      (by linarith : 0 < p) (u := u) (v := fun _ => 0)
    simp only [unitBallExtension_zero, sub_zero] at h0
    exact h0
  -- V_n → unitBallExtension u in eLpNorm (doesn't need MemLp for uExt)
  have hV_fun :
      Tendsto (fun n => eLpNorm (fun x => unitBallExtension (d := d) (ψ n) x -
        unitBallExtension (d := d) u x) (ENNReal.ofReal p) volume) atTop (nhds 0) := by
    let K : ℝ≥0∞ := (1 + ENNReal.ofReal ((2 : ℝ) ^ (2 * d))) ^ (1 / p)
    have hbound : ∀ n,
        eLpNorm (fun x => unitBallExtension (d := d) (ψ n) x -
          unitBallExtension (d := d) u x) (ENNReal.ofReal p) volume
        ≤ K * eLpNorm (fun x => ψ n x - u x) (ENNReal.ofReal p) μB :=
      fun n => eLpNorm_unitBallExtension_sub_le_local (d := d) hp
    have hKψ : Tendsto (fun n => K * eLpNorm (fun x => ψ n x - u x)
        (ENNReal.ofReal p) μB) atTop (nhds 0) := by
      have h := ENNReal.Tendsto.const_mul hψ_fun (Or.inr (show K ≠ ⊤ by simp [K]))
      rwa [mul_zero] at h
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hKψ
      (fun _ => bot_le) hbound
  -- MemLp for unitBallExtension u: V_n Cauchy → Lp limit → ae_eq uExt → transfer
  have huExt_memLp : MemLp (unitBallExtension (d := d) u) (ENNReal.ofReal p) volume := by
    -- V_n is pair-Cauchy
    have hψ_memLp_restrict : ∀ n, MemLp (ψ n) (ENNReal.ofReal p) μB :=
      fun n => ((hψ_smooth n).continuous.memLp_of_hasCompactSupport (hψ_cpt n)).restrict B
    have hV_pair : Tendsto (fun nm : ℕ × ℕ =>
        eLpNorm (fun x => unitBallExtension (d := d) (ψ nm.1) x -
          unitBallExtension (d := d) (ψ nm.2) x) (ENNReal.ofReal p) volume)
        atTop (nhds 0) := by
      let K : ℝ≥0∞ := (1 + ENNReal.ofReal ((2 : ℝ) ^ (2 * d))) ^ (1 / p)
      have hKψ_fun : Tendsto (fun n =>
          K * eLpNorm (fun x => ψ n x - u x) (ENNReal.ofReal p) μB) atTop (nhds 0) := by
        have h := ENNReal.Tendsto.const_mul hψ_fun (Or.inr (show K ≠ ⊤ by simp [K]))
        rwa [mul_zero] at h
      refine tendsto_zero_of_le_pair_sum (fun nm => ?_) hKψ_fun
      calc eLpNorm (fun x => unitBallExtension (d := d) (ψ nm.1) x -
              unitBallExtension (d := d) (ψ nm.2) x) (ENNReal.ofReal p) volume
          ≤ K * eLpNorm (fun x => ψ nm.1 x - ψ nm.2 x) (ENNReal.ofReal p) μB :=
            eLpNorm_unitBallExtension_sub_le_local (d := d) hp
        _ ≤ K * (eLpNorm (fun x => ψ nm.1 x - u x) (ENNReal.ofReal p) μB +
              eLpNorm (fun x => ψ nm.2 x - u x) (ENNReal.ofReal p) μB) := by
            gcongr; rw [show (fun x => ψ nm.1 x - ψ nm.2 x) =
              (fun x => (ψ nm.1 x - u x) - (ψ nm.2 x - u x)) from by ext x; ring]
            exact eLpNorm_sub_le ((hψ_memLp_restrict nm.1).sub hw.memLp).aestronglyMeasurable
              ((hψ_memLp_restrict nm.2).sub hw.memLp).aestronglyMeasurable
              (by simpa using ENNReal.ofReal_le_ofReal hp.le)
        _ = K * eLpNorm (fun x => ψ nm.1 x - u x) (ENNReal.ofReal p) μB +
              K * eLpNorm (fun x => ψ nm.2 x - u x) (ENNReal.ofReal p) μB := by ring
    -- Extract Lp limit with MemLp
    obtain ⟨f_lim, hf_lim_memLp, hf_lim_tendsto⟩ :=
      BareFunction.scalar_cauchy_to_limit
        (by simpa using ENNReal.ofReal_le_ofReal hp.le) (by simp) hV_memLp hV_pair
    -- f_lim =ᵐ unitBallExtension u (both are eLpNorm limits of V_n)
    -- eLpNorm(V_n - f_lim) → 0 and eLpNorm(V_n - uExt) → 0, so eLpNorm(f_lim - uExt) = 0
    have hae : f_lim =ᵐ[volume] unitBallExtension (d := d) u := by
      have huExt_aesm : AEStronglyMeasurable (unitBallExtension (d := d) u) volume :=
        aestronglyMeasurable_unitBallExtension_of_memLp hw.memLp
      exact BareFunction.ae_eq_of_tendsto_eLpNorm_sub
        (by simpa using ENNReal.ofReal_le_ofReal hp.le)
        (fun n => (hV_memLp n).aestronglyMeasurable)
        hf_lim_memLp.aestronglyMeasurable huExt_aesm
        hf_lim_tendsto
        (by exact hV_fun)
    exact (memLp_congr_ae hae).mp hf_lim_memLp
  have hG_comp_cauchy : ∀ i : Fin d, Tendsto (fun nm : ℕ × ℕ =>
      eLpNorm (fun x => G nm.1 x i - G nm.2 x i) (ENNReal.ofReal p) volume)
      atTop (nhds 0) := by
    intro i
    -- ∫ |G nm.1 · i - G nm.2 · i|^p ≤ ∫ ‖exactGrad(ψ nm.1 - ψ nm.2)‖^p
    have hcomp_le : ∀ nm : ℕ × ℕ,
        ∫⁻ x, (ENNReal.ofReal |G nm.1 x i - G nm.2 x i|) ^ p ∂volume ≤
          ∫⁻ x, (ENNReal.ofReal ‖exactUnitBallExtensionGrad (d := d)
            (fun x => ψ nm.1 x - ψ nm.2 x) x‖) ^ p ∂volume :=
      fun nm => weakGrad_component_cauchy_bound (d := d) hp
        (hψ_smooth nm.1) (hψ_smooth nm.2) (hψ_cpt nm.1) (hψ_cpt nm.2)
        (hV_wd nm.1 i) (hV_wd nm.2 i) (hG_comp_memLp nm.1 i) (hG_comp_memLp nm.2 i)
    have hgrad_bound_nm : ∀ nm : ℕ × ℕ,
        ∫⁻ x, (ENNReal.ofReal ‖exactUnitBallExtensionGrad (d := d)
          (fun x => ψ nm.1 x - ψ nm.2 x) x‖) ^ p ∂volume ≤
          (∫⁻ x in B, (ENNReal.ofReal ‖fderiv ℝ (fun x => ψ nm.1 x - ψ nm.2 x) x‖) ^ p
            ∂volume) +
          C_unitBallExtensionGrad d p *
            (∫⁻ x in B, (ENNReal.ofReal |ψ nm.1 x - ψ nm.2 x|) ^ p ∂volume +
             ∫⁻ x in B, (ENNReal.ofReal ‖fderiv ℝ (fun x => ψ nm.1 x - ψ nm.2 x) x‖) ^ p
              ∂volume) :=
      fun nm => exactUnitBallExtensionGrad_bound (d := d) hp
        ((hψ_smooth nm.1).sub (hψ_smooth nm.2))
    have hfull_le : ∀ nm : ℕ × ℕ,
        ∫⁻ x, (ENNReal.ofReal |G nm.1 x i - G nm.2 x i|) ^ p ∂volume ≤
          (∫⁻ x in B, (ENNReal.ofReal ‖fderiv ℝ (fun x => ψ nm.1 x - ψ nm.2 x) x‖) ^ p
            ∂volume) +
          C_unitBallExtensionGrad d p *
            (∫⁻ x in B, (ENNReal.ofReal |ψ nm.1 x - ψ nm.2 x|) ^ p ∂volume +
             ∫⁻ x in B, (ENNReal.ofReal ‖fderiv ℝ (fun x => ψ nm.1 x - ψ nm.2 x) x‖) ^ p
              ∂volume) :=
      fun nm => le_trans (hcomp_le nm) (hgrad_bound_nm nm)
    have hp0 : (0 : ℝ) < p := by linarith
    -- Convert eLpNorm = (∫⁻ |·|^p)^(1/p)
    suffices hlint : Tendsto (fun nm : ℕ × ℕ =>
        ∫⁻ x, (ENNReal.ofReal |G nm.1 x i - G nm.2 x i|) ^ p ∂volume) atTop (nhds 0) by
      -- eLpNorm(f) = (∫⁻ |f|^p)^(1/p) conversion + Tendsto rpow
      have hconv : ∀ nm : ℕ × ℕ,
          eLpNorm (fun x => G nm.1 x i - G nm.2 x i) (ENNReal.ofReal p) volume =
            (∫⁻ x, (ENNReal.ofReal |G nm.1 x i - G nm.2 x i|) ^ p ∂volume) ^ (1 / p) := by
        intro nm
        have hp_enn_ne : (ENNReal.ofReal p) ≠ 0 := (ENNReal.ofReal_pos.mpr hp0).ne'
        simpa [ENNReal.toReal_ofReal hp0.le, Real.enorm_eq_ofReal_abs] using
          (MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal
            (μ := volume) (p := ENNReal.ofReal p) hp_enn_ne (by simp)
            (f := fun x => G nm.1 x i - G nm.2 x i))
      rw [show (0 : ℝ≥0∞) = (0 : ℝ≥0∞) ^ (1 / p) from by
        rw [ENNReal.zero_rpow_of_pos (by positivity : (0 : ℝ) < 1 / p)]]
      exact Filter.Tendsto.congr (fun nm => (hconv nm).symm)
        (hlint.ennrpow_const (1 / p))
    -- Auxiliary: ψ_n restricted to B is MemLp
    have hψ_memLp_restrict : ∀ n, MemLp (ψ n) (ENNReal.ofReal p) μB :=
      fun n => ((hψ_smooth n).continuous.memLp_of_hasCompactSupport (hψ_cpt n)).restrict B
    -- Function term: ∫_B |ψ nm.1 - ψ nm.2|^p → 0
    have hfun_pair : Tendsto (fun nm : ℕ × ℕ =>
        ∫⁻ x in B, (ENNReal.ofReal |ψ nm.1 x - ψ nm.2 x|) ^ p ∂volume) atTop (nhds 0) := by
      have hpair_eLpNorm : Tendsto (fun nm : ℕ × ℕ =>
          eLpNorm (fun x => ψ nm.1 x - ψ nm.2 x) (ENNReal.ofReal p) μB) atTop (nhds 0) := by
        refine tendsto_zero_of_le_pair_sum (fun nm => ?_) hψ_fun
        rw [show (fun x => ψ nm.1 x - ψ nm.2 x) =
          (fun x => (ψ nm.1 x - u x) - (ψ nm.2 x - u x)) from by ext x; ring]
        exact eLpNorm_sub_le ((hψ_memLp_restrict nm.1).sub hw.memLp).aestronglyMeasurable
          ((hψ_memLp_restrict nm.2).sub hw.memLp).aestronglyMeasurable
          (by simpa using ENNReal.ofReal_le_ofReal hp.le)
      have hconv_fun : ∀ nm : ℕ × ℕ,
          ∫⁻ x in B, (ENNReal.ofReal |ψ nm.1 x - ψ nm.2 x|) ^ p ∂volume =
            eLpNorm (fun x => ψ nm.1 x - ψ nm.2 x) (ENNReal.ofReal p) μB ^ p := by
        intro nm
        rw [← lintegral_rpow_norm_eq_eLpNorm_pow hp0]; congr 1
      simp_rw [hconv_fun]
      rw [show (0 : ℝ≥0∞) = (0 : ℝ≥0∞) ^ p from by rw [ENNReal.zero_rpow_of_pos hp0]]
      exact hpair_eLpNorm.ennrpow_const p
    -- Gradient term: ∫_B ‖∇(ψ nm.1 - ψ nm.2)‖^p → 0
    -- Strategy: ‖fderiv f x‖ = ‖(fun i => (fderiv f x)(e_i))‖_E by norm_fderiv_eq_norm_partials.
    -- For EuclideanSpace, ‖v‖^p ≤ d^(p/2) * ∑ᵢ |vᵢ|^p (norm-component bridge).
    -- Each component ∫_B |(fderiv(ψ₁-ψ₂))(e_i)|^p → 0 from hψ_grad via triangle.
    have hgrad_pair : Tendsto (fun nm : ℕ × ℕ =>
        ∫⁻ x in B, (ENNReal.ofReal ‖fderiv ℝ (fun x => ψ nm.1 x - ψ nm.2 x) x‖) ^ p
          ∂volume) atTop (nhds 0) := by
      -- Step A: Component-level pair Cauchy for each i.
      -- (fderiv(ψ₁-ψ₂))(eᵢ) = (fderiv ψ₁)(eᵢ) - (fderiv ψ₂)(eᵢ) by fderiv_sub.
      -- hψ_grad i says eLpNorm((fderiv ψ_n)(eᵢ) - weakGrad · i) → 0.
      -- By triangle: eLpNorm((fderiv ψ₁)(eᵢ) - (fderiv ψ₂)(eᵢ)) → 0 as pair.
      have hcomp_pair : ∀ j : Fin d, Tendsto (fun nm : ℕ × ℕ =>
          eLpNorm
            (fun x =>
              (fderiv ℝ (fun x => ψ nm.1 x - ψ nm.2 x) x)
                (EuclideanSpace.single j 1))
            (ENNReal.ofReal p) μB) atTop (nhds 0) := by
        intro j
        have hpair_comp_eLpNorm : Tendsto (fun nm : ℕ × ℕ =>
            eLpNorm (fun x => (fderiv ℝ (ψ nm.1) x) (EuclideanSpace.single j 1) -
              (fderiv ℝ (ψ nm.2) x) (EuclideanSpace.single j 1))
              (ENNReal.ofReal p) μB) atTop (nhds 0) := by
          refine tendsto_zero_of_le_pair_sum (fun nm => ?_) (hψ_grad j)
          rw [show (fun x => (fderiv ℝ (ψ nm.1) x) (EuclideanSpace.single j 1) -
              (fderiv ℝ (ψ nm.2) x) (EuclideanSpace.single j 1)) =
            (fun x => ((fderiv ℝ (ψ nm.1) x) (EuclideanSpace.single j 1) - hw.weakGrad x j) -
              ((fderiv ℝ (ψ nm.2) x) (EuclideanSpace.single j 1) - hw.weakGrad x j))
            from by ext x; ring]
          exact eLpNorm_sub_le
            (((((hψ_smooth nm.1).continuous_fderiv (by simp)).clm_apply
              continuous_const).memLp_of_hasCompactSupport
              ((hψ_cpt nm.1).fderiv_apply (𝕜 := ℝ) _)).restrict B |>.sub
              (hw.weakGrad_component_memLp j)).aestronglyMeasurable
            (((((hψ_smooth nm.2).continuous_fderiv (by simp)).clm_apply
              continuous_const).memLp_of_hasCompactSupport
              ((hψ_cpt nm.2).fderiv_apply (𝕜 := ℝ) _)).restrict B |>.sub
              (hw.weakGrad_component_memLp j)).aestronglyMeasurable
            (by simpa using ENNReal.ofReal_le_ofReal hp.le)
        refine (Filter.tendsto_congr fun nm => eLpNorm_congr_ae ?_).mpr hpair_comp_eLpNorm
        filter_upwards with x
        exact congrArg (fun L : E →L[ℝ] ℝ => L (EuclideanSpace.single j 1))
          (fderiv_sub ((hψ_smooth nm.1).differentiable (by simp)).differentiableAt
            ((hψ_smooth nm.2).differentiable (by simp)).differentiableAt)
      let H : (ℕ × ℕ) → E → E := fun nm x =>
        WithLp.toLp 2 fun j =>
          (fderiv ℝ (fun x => ψ nm.1 x - ψ nm.2 x) x)
            (EuclideanSpace.single j 1)
      have hH_pair : Tendsto (fun nm : ℕ × ℕ =>
          eLpNorm (H nm) (ENNReal.ofReal p) μB) atTop (nhds 0) := by
        have hle : ∀ nm : ℕ × ℕ,
            eLpNorm (H nm) (ENNReal.ofReal p) μB ≤
              ∑ j : Fin d, eLpNorm (fun x => H nm x j) (ENNReal.ofReal p) μB := by
          intro nm
          refine euclidean_eLpNorm_le_component_sum (d := d) (μ := μB) (p := p) hp.le ?_
          intro j
          have hmeas :
              Measurable (fun x =>
                (fderiv ℝ (fun x => ψ nm.1 x - ψ nm.2 x) x)
                  (EuclideanSpace.single j 1)) := by
            exact ((((hψ_smooth nm.1).sub (hψ_smooth nm.2)).continuous_fderiv
              (by simp)).clm_apply continuous_const).measurable
          simpa [H, PiLp.toLp_apply] using hmeas.aestronglyMeasurable
        have hsum : Tendsto (fun nm : ℕ × ℕ =>
            ∑ j : Fin d, eLpNorm (fun x => H nm x j) (ENNReal.ofReal p) μB)
            atTop (nhds 0) := by
          have h0 : (0 : ℝ≥0∞) = ∑ _j : Fin d, (0 : ℝ≥0∞) := by simp
          rw [h0]
          exact tendsto_finset_sum Finset.univ (fun j _ => by
            simpa [H, PiLp.toLp_apply] using hcomp_pair j)
        exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
          (fun _ => bot_le) hle
      have hconv : ∀ nm : ℕ × ℕ,
          ∫⁻ x in B, (ENNReal.ofReal ‖fderiv ℝ (fun x => ψ nm.1 x - ψ nm.2 x) x‖) ^ p
            ∂volume =
            eLpNorm (H nm) (ENNReal.ofReal p) μB ^ p := by
        intro nm
        calc
          ∫⁻ x in B, (ENNReal.ofReal ‖fderiv ℝ (fun x => ψ nm.1 x - ψ nm.2 x) x‖) ^ p
              ∂volume
              = ∫⁻ x in B, (ENNReal.ofReal ‖H nm x‖) ^ p ∂volume := by
                  congr 1
                  ext x
                  simp [H, norm_fderiv_eq_norm_partials_local (d := d)]
          _ = eLpNorm (H nm) (ENNReal.ofReal p) μB ^ p := by
                simpa [μB] using
                  (lintegral_rpow_norm_eq_eLpNorm_pow (μ := μB) hp0 (f := H nm))
      simp_rw [hconv]
      rw [show (0 : ℝ≥0∞) = (0 : ℝ≥0∞) ^ p from by
        rw [ENNReal.zero_rpow_of_pos hp0]]
      exact hH_pair.ennrpow_const p
    -- Combine: bound = grad_pair + C * (fun_pair + grad_pair), all → 0
    have hC_ne_top : C_unitBallExtensionGrad d p ≠ ⊤ := by
      unfold C_unitBallExtensionGrad
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.rpow_ne_top_of_nonneg (by linarith) (by simp))
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_
      (fun _ => bot_le) hfull_le
    have hsum := hfun_pair.add hgrad_pair
    rw [add_zero] at hsum
    have hCmul := ENNReal.Tendsto.const_mul hsum (Or.inr hC_ne_top)
    rw [mul_zero] at hCmul
    have hfinal := hgrad_pair.add hCmul
    rwa [add_zero] at hfinal
  obtain ⟨Gext, hGext_comp_memLp, hG_comp_tendsto⟩ :=
    cauchy_Lp_component_limit (d := d) hp hG_comp_memLp hG_comp_cauchy
  have hweak : ∀ i : Fin d,
      HasWeakPartialDeriv i (fun x => Gext x i)
        (unitBallExtension (d := d) u) Set.univ := by
    intro i
    exact HasWeakPartialDeriv.of_eLpNormApprox_p (d := d) (Ω := Set.univ) isOpen_univ hp
      (by rw [Measure.restrict_univ]; exact huExt_memLp)
      (by rw [Measure.restrict_univ]; exact hGext_comp_memLp i)
      (fun n => hV_wd n i)
      (fun n => by rw [Measure.restrict_univ]; exact (hV_memLp n).sub huExt_memLp)
      (by rw [Measure.restrict_univ]; exact hV_fun)
      (fun n => by rw [Measure.restrict_univ]; exact (hG_comp_memLp n i).sub (hGext_comp_memLp i))
      (by rw [Measure.restrict_univ]; exact hG_comp_tendsto i)
  let hwExt : MemW1pWitness (ENNReal.ofReal p)
      (unitBallExtension (d := d) u) Set.univ :=
    { memLp := by rw [Measure.restrict_univ]; exact huExt_memLp
      weakGrad := Gext
      weakGrad_component_memLp := by
        intro i; rw [Measure.restrict_univ]; exact hGext_comp_memLp i
      isWeakGrad := hweak }
  rcases exists_global_smooth_W1p_approx_of_localizedWitness
      (d := d) (Ω := Set.univ) isOpen_univ hp hwExt
      (unitBallExtension_hasCompactSupport (d := d) u) (Set.subset_univ _) with
    ⟨Φ, hΦ_smooth, hΦ_cpt, hΦ_fun, hΦ_grad⟩
  refine ⟨Gext, huExt_memLp, hGext_comp_memLp, huExt_fun_bound, ?_,
    Φ, hΦ_smooth, hΦ_cpt, hΦ_fun, ?_⟩
  · -- Gradient energy bound via semicontinuity
    -- Each G_n satisfies: ∫ ‖G_n‖^p ≤ bound(ψ_n).
    -- G_n → Gext in Lp (componentwise), so ∫ ‖Gext‖^p ≤ lim bound(ψ_n) = bound(u).
    --        (2) component eLpNorm ≤ vector eLpNorm (pre-compiled in geometry)
    -- This uses G n → Gext componentwise in Lp, hence a.e. along a subsequence,
    -- then Fatou's lemma on ‖·‖^p (or norm-equivalence + component Fatou).
    have hFatou : (∫⁻ x, (ENNReal.ofReal ‖Gext x‖) ^ p ∂volume) ≤
        atTop.liminf (fun n => ∫⁻ x, (ENNReal.ofReal ‖G n x‖) ^ p ∂volume) := by
      have hp0 : (0 : ℝ) < p := by linarith
      have hG_aesm : ∀ n, AEStronglyMeasurable (G n) volume := by
        intro n
        exact aestronglyMeasurable_euclidean_of_components (d := d) (μ := volume)
          (fun i => (hG_comp_memLp n i).aestronglyMeasurable)
      have hGext_aesm : AEStronglyMeasurable Gext volume :=
        aestronglyMeasurable_euclidean_of_components (d := d) (μ := volume)
          (fun i => (hGext_comp_memLp i).aestronglyMeasurable)
      have hGext_memLp_vec : MemLp Gext (ENNReal.ofReal p) volume :=
        memLp_euclidean_of_components (d := d) (μ := volume) hp.le
          (fun i => hGext_comp_memLp i)
      have hG_tendsto : Tendsto
          (fun n => eLpNorm (fun x => G n x - Gext x) (ENNReal.ofReal p) volume)
          atTop (nhds 0) := by
        have hle : ∀ n,
            eLpNorm (fun x => G n x - Gext x) (ENNReal.ofReal p) volume ≤
              ∑ i : Fin d, eLpNorm (fun x => G n x i - Gext x i) (ENNReal.ofReal p) volume := by
          intro n
          exact euclidean_eLpNorm_le_component_sum (d := d) (μ := volume) (p := p) hp.le
            (fun i =>
              ((hG_comp_memLp n i).aestronglyMeasurable.sub
                (hGext_comp_memLp i).aestronglyMeasurable))
        have hsum : Tendsto (fun n =>
            ∑ i : Fin d, eLpNorm (fun x => G n x i - Gext x i) (ENNReal.ofReal p) volume)
            atTop (nhds 0) := by
          have h0 : (0 : ℝ≥0∞) = ∑ _i : Fin d, (0 : ℝ≥0∞) := by simp
          rw [h0]
          exact tendsto_finset_sum Finset.univ (fun i _ => hG_comp_tendsto i)
        exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
          (fun _ => bot_le) hle
      have hGnorm_tendsto :
          Tendsto (fun n => eLpNorm (G n) (ENNReal.ofReal p) volume)
            atTop (nhds (eLpNorm Gext (ENNReal.ofReal p) volume)) := by
        have hle : ∀ n, eLpNorm (G n) (ENNReal.ofReal p) volume ≤
            eLpNorm (fun x => G n x - Gext x) (ENNReal.ofReal p) volume +
              eLpNorm Gext (ENNReal.ofReal p) volume := by
          intro n
          calc eLpNorm (G n) (ENNReal.ofReal p) volume
              = eLpNorm (fun x => (G n x - Gext x) + Gext x) (ENNReal.ofReal p) volume := by
                  congr 1
                  ext x
                  simp
            _ ≤ eLpNorm (fun x => G n x - Gext x) (ENNReal.ofReal p) volume +
                  eLpNorm Gext (ENNReal.ofReal p) volume :=
                eLpNorm_add_le ((hG_aesm n).sub hGext_aesm) hGext_aesm
                  (by simpa using ENNReal.ofReal_le_ofReal hp.le)
        have hge : ∀ n, eLpNorm Gext (ENNReal.ofReal p) volume ≤
            eLpNorm (fun x => G n x - Gext x) (ENNReal.ofReal p) volume +
              eLpNorm (G n) (ENNReal.ofReal p) volume := by
          intro n
          calc eLpNorm Gext (ENNReal.ofReal p) volume
              = eLpNorm (fun x => (Gext x - G n x) + G n x) (ENNReal.ofReal p) volume := by
                  congr 1
                  ext x
                  simp
            _ ≤ eLpNorm (fun x => Gext x - G n x) (ENNReal.ofReal p) volume +
                  eLpNorm (G n) (ENNReal.ofReal p) volume :=
                eLpNorm_add_le (hGext_aesm.sub (hG_aesm n)) (hG_aesm n)
                  (by simpa using ENNReal.ofReal_le_ofReal hp.le)
            _ = eLpNorm (fun x => G n x - Gext x) (ENNReal.ofReal p) volume +
                  eLpNorm (G n) (ENNReal.ofReal p) volume := by
                have hneg_eq :
                    eLpNorm (fun x => Gext x - G n x) (ENNReal.ofReal p) volume =
                      eLpNorm (fun x => G n x - Gext x) (ENNReal.ofReal p) volume := by
                  calc
                    eLpNorm (fun x => Gext x - G n x) (ENNReal.ofReal p) volume
                        = eLpNorm (fun x => -(G n x - Gext x)) (ENNReal.ofReal p) volume := by
                            congr 1
                            ext x
                            simp
                    _ = eLpNorm (fun x => G n x - Gext x) (ENNReal.ofReal p) volume := by
                          simpa only using
                            (eLpNorm_neg (f := fun x => G n x - Gext x)
                              (p := ENNReal.ofReal p) (μ := volume))
                simp [hneg_eq]
        refine tendsto_of_tendsto_of_tendsto_of_le_of_le ?_ ?_
          (fun n => tsub_le_iff_right.mpr (by simpa [add_comm] using hge n))
          (fun n => hle n)
        · have hsub :
              Tendsto
                (fun n =>
                  eLpNorm Gext (ENNReal.ofReal p) volume -
                    eLpNorm (fun x => G n x - Gext x) (ENNReal.ofReal p) volume)
                atTop (nhds (eLpNorm Gext (ENNReal.ofReal p) volume - 0)) := by
              simpa using
                (((ENNReal.continuous_sub_left hGext_memLp_vec.eLpNorm_ne_top).tendsto 0).comp
                  hG_tendsto)
          simpa using hsub
        · have hadd :
              Tendsto
                (fun n =>
                  eLpNorm (fun x => G n x - Gext x) (ENNReal.ofReal p) volume +
                    eLpNorm Gext (ENNReal.ofReal p) volume)
                atTop (nhds (0 + eLpNorm Gext (ENNReal.ofReal p) volume)) := by
              exact hG_tendsto.add tendsto_const_nhds
          rwa [zero_add] at hadd
      have hpow_tendsto : Tendsto
          (fun n => ∫⁻ x, (ENNReal.ofReal ‖G n x‖) ^ p ∂volume)
          atTop (nhds (∫⁻ x, (ENNReal.ofReal ‖Gext x‖) ^ p ∂volume)) := by
        have hEq : ∀ n,
            ∫⁻ x, (ENNReal.ofReal ‖G n x‖) ^ p ∂volume =
              eLpNorm (G n) (ENNReal.ofReal p) volume ^ p := by
          intro n
          simpa using (lintegral_rpow_norm_eq_eLpNorm_pow (μ := volume) hp0 (f := G n))
        have hEqLim :
            ∫⁻ x, (ENNReal.ofReal ‖Gext x‖) ^ p ∂volume =
              eLpNorm Gext (ENNReal.ofReal p) volume ^ p := by
          simpa using (lintegral_rpow_norm_eq_eLpNorm_pow (μ := volume) hp0 (f := Gext))
        simp_rw [hEq, hEqLim]
        exact hGnorm_tendsto.ennrpow_const p
      rw [hpow_tendsto.liminf_eq]
    -- Define the RHS as a function of n
    let RHS : ℕ → ℝ≥0∞ := fun n =>
      (∫⁻ x in B, (ENNReal.ofReal ‖fderiv ℝ (ψ n) x‖) ^ p ∂volume) +
        C_unitBallExtensionGrad d p *
          (∫⁻ x in B, (ENNReal.ofReal |ψ n x|) ^ p ∂volume +
           ∫⁻ x in B, (ENNReal.ofReal ‖fderiv ℝ (ψ n) x‖) ^ p ∂volume)
    let RHS_lim : ℝ≥0∞ :=
      (∫⁻ x in B, (ENNReal.ofReal ‖hw.weakGrad x‖) ^ p ∂volume) +
        C_unitBallExtensionGrad d p *
          (∫⁻ x in B, (ENNReal.ofReal |u x|) ^ p ∂volume +
           ∫⁻ x in B, (ENNReal.ofReal ‖hw.weakGrad x‖) ^ p ∂volume)
    -- bound(ψ n) → bound(u)
    have hRHS_tendsto : Tendsto RHS atTop (nhds RHS_lim) := by
      -- Abbreviations
      let Fn : ℕ → ℝ≥0∞ := fun n =>
        ∫⁻ x in B, (ENNReal.ofReal |ψ n x|) ^ p ∂volume
      let An : ℕ → ℝ≥0∞ := fun n =>
        ∫⁻ x in B, (ENNReal.ofReal ‖fderiv ℝ (ψ n) x‖) ^ p ∂volume
      let F_lim : ℝ≥0∞ := ∫⁻ x in B, (ENNReal.ofReal |u x|) ^ p ∂volume
      let A_lim : ℝ≥0∞ := ∫⁻ x in B, (ENNReal.ofReal ‖hw.weakGrad x‖) ^ p ∂volume
      have hp0 : (0 : ℝ) < p := by linarith
      have h1p : 1 ≤ ENNReal.ofReal p := by simpa using ENNReal.ofReal_le_ofReal hp.le
      -- Reverse triangle: eLpNorm(ψ n - u) → 0 ⟹ eLpNorm(ψ n) → eLpNorm(u).
      have hψ_memLp_B : ∀ n, MemLp (ψ n) (ENNReal.ofReal p) μB :=
        fun n => ((hψ_smooth n).continuous.memLp_of_hasCompactSupport (hψ_cpt n)).restrict B
      have heLpNorm_fun : Tendsto (fun n => eLpNorm (ψ n) (ENNReal.ofReal p) μB)
          atTop (nhds (eLpNorm u (ENNReal.ofReal p) μB)) := by
        -- Upper: eLpNorm(ψ n) ≤ eLpNorm(ψ n - u) + eLpNorm(u)
        have hle : ∀ n, eLpNorm (ψ n) (ENNReal.ofReal p) μB ≤
            eLpNorm (fun x => ψ n x - u x) (ENNReal.ofReal p) μB +
              eLpNorm u (ENNReal.ofReal p) μB := by
          intro n
          calc eLpNorm (ψ n) (ENNReal.ofReal p) μB
              = eLpNorm (fun x => (ψ n x - u x) + u x) (ENNReal.ofReal p) μB := by
                congr 1; ext x; simp
            _ ≤ eLpNorm (fun x => ψ n x - u x) (ENNReal.ofReal p) μB +
                  eLpNorm u (ENNReal.ofReal p) μB :=
                eLpNorm_add_le ((hψ_memLp_B n).sub hw.memLp).aestronglyMeasurable
                  hw.memLp.aestronglyMeasurable h1p
        -- Lower: eLpNorm(u) ≤ eLpNorm(ψ n - u) + eLpNorm(ψ n)
        have hge : ∀ n, eLpNorm u (ENNReal.ofReal p) μB ≤
            eLpNorm (fun x => ψ n x - u x) (ENNReal.ofReal p) μB +
              eLpNorm (ψ n) (ENNReal.ofReal p) μB := by
          intro n
          calc eLpNorm u (ENNReal.ofReal p) μB
              = eLpNorm (fun x => (u x - ψ n x) + ψ n x) (ENNReal.ofReal p) μB := by
                congr 1; ext x; simp
            _ ≤ eLpNorm (fun x => u x - ψ n x) (ENNReal.ofReal p) μB +
                  eLpNorm (ψ n) (ENNReal.ofReal p) μB :=
                eLpNorm_add_le (hw.memLp.sub (hψ_memLp_B n)).aestronglyMeasurable
                  (hψ_memLp_B n).aestronglyMeasurable h1p
            _ = eLpNorm (fun x => ψ n x - u x) (ENNReal.ofReal p) μB +
                  eLpNorm (ψ n) (ENNReal.ofReal p) μB := by
                have hneg_eq :
                    eLpNorm (fun x => u x - ψ n x) (ENNReal.ofReal p) μB =
                      eLpNorm (fun x => ψ n x - u x) (ENNReal.ofReal p) μB := by
                  calc
                    eLpNorm (fun x => u x - ψ n x) (ENNReal.ofReal p) μB
                        = eLpNorm (fun x => -(ψ n x - u x)) (ENNReal.ofReal p) μB := by
                            congr 1
                            ext x
                            ring
                    _ = eLpNorm (fun x => ψ n x - u x) (ENNReal.ofReal p) μB := by
                          simpa only using
                            (eLpNorm_neg (f := fun x => ψ n x - u x)
                              (p := ENNReal.ofReal p) (μ := μB))
                simp [hneg_eq]
        -- Squeeze: eLpNorm(u) - eLpNorm(ψ n - u) ≤ eLpNorm(ψ n) ≤ eLpNorm(ψ n - u) + eLpNorm(u)
        refine tendsto_of_tendsto_of_tendsto_of_le_of_le ?_ ?_
          (fun n => by
            have hge' : eLpNorm u (ENNReal.ofReal p) μB ≤
                eLpNorm (ψ n) (ENNReal.ofReal p) μB +
                  eLpNorm (fun x => ψ n x - u x) (ENNReal.ofReal p) μB := by
              simpa [add_comm] using hge n
            exact tsub_le_iff_right.mpr hge')
          (fun n => hle n)
        · have hsub :
              Tendsto
                (fun n =>
                  eLpNorm u (ENNReal.ofReal p) μB -
                    eLpNorm (fun x => ψ n x - u x) (ENNReal.ofReal p) μB)
                atTop (nhds (eLpNorm u (ENNReal.ofReal p) μB - 0)) := by
              simpa using
                (((ENNReal.continuous_sub_left hw.memLp.eLpNorm_ne_top).tendsto 0).comp hψ_fun)
          simpa using hsub
        · have hadd :
              Tendsto
                (fun n =>
                  eLpNorm (fun x => ψ n x - u x) (ENNReal.ofReal p) μB +
                    eLpNorm u (ENNReal.ofReal p) μB)
                atTop (nhds (0 + eLpNorm u (ENNReal.ofReal p) μB)) := by
              exact hψ_fun.add tendsto_const_nhds
          rwa [zero_add] at hadd
      -- Fn n = eLpNorm(ψ n)^p and F_lim = eLpNorm(u)^p
      have hFn_eq : ∀ n, Fn n = eLpNorm (ψ n) (ENNReal.ofReal p) μB ^ p := by
        intro n; rw [← lintegral_rpow_norm_eq_eLpNorm_pow hp0]; congr 1
      have hF_lim_eq : F_lim = eLpNorm u (ENNReal.ofReal p) μB ^ p := by
        rw [← lintegral_rpow_norm_eq_eLpNorm_pow hp0]; congr 1
      have hFn_tendsto : Tendsto Fn atTop (nhds F_lim) := by
        show Tendsto (fun n => Fn n) atTop (nhds F_lim)
        simp_rw [hFn_eq, hF_lim_eq]
        exact heLpNorm_fun.ennrpow_const p
      -- Component-level: eLpNorm(fderiv(ψ n)(eⱼ) - weakGrad · j) → 0 for each j.
      -- By reverse triangle, eLpNorm(fderiv(ψ n)(eⱼ)) → eLpNorm(weakGrad · j),
      -- hence ∫|comp_j(ψ n)|^p → ∫|comp_j(weakGrad)|^p for each j.
      -- Bridge: ∫‖fderiv(ψ n)‖^p ≈ ∑ⱼ ∫|comp_j(ψ n)|^p up to d^{p/2} (EuclideanSpace).
      -- Since all component integrals converge, the sandwich gives An n → A_lim.
      have hAn_tendsto : Tendsto An atTop (nhds A_lim) := by
        let gradVec : ℕ → E → E := fun n x =>
          WithLp.toLp 2 fun i =>
            (fderiv ℝ (ψ n) x) (EuclideanSpace.single i 1)
        have hgradVec_comp_aesm : ∀ n i, AEStronglyMeasurable (fun x => gradVec n x i) μB := by
          intro n i
          have hmeas :
              Measurable (fun x => (fderiv ℝ (ψ n) x) (EuclideanSpace.single i 1)) := by
            exact (((hψ_smooth n).continuous_fderiv (by simp)).clm_apply continuous_const).measurable
          simpa [gradVec, PiLp.toLp_apply] using hmeas.aestronglyMeasurable
        have hgradVec_aesm : ∀ n, AEStronglyMeasurable (gradVec n) μB := by
          intro n
          exact aestronglyMeasurable_euclidean_of_components (d := d) (μ := μB)
            (fun i => hgradVec_comp_aesm n i)
        have hweakGrad_aesm : AEStronglyMeasurable hw.weakGrad μB :=
          aestronglyMeasurable_euclidean_of_components (d := d) (μ := μB)
            (fun i => (hw.weakGrad_component_memLp i).aestronglyMeasurable)
        have hweakGrad_memLp_vec : MemLp hw.weakGrad (ENNReal.ofReal p) μB :=
          memLp_euclidean_of_components (d := d) (μ := μB) hp.le
            (fun i => hw.weakGrad_component_memLp i)
        have hgradVec_tendsto : Tendsto
            (fun n => eLpNorm (fun x => gradVec n x - hw.weakGrad x) (ENNReal.ofReal p) μB)
            atTop (nhds 0) := by
          have hle : ∀ n,
              eLpNorm (fun x => gradVec n x - hw.weakGrad x) (ENNReal.ofReal p) μB ≤
                ∑ i : Fin d,
                  eLpNorm (fun x => gradVec n x i - hw.weakGrad x i) (ENNReal.ofReal p) μB := by
            intro n
            exact euclidean_eLpNorm_le_component_sum (d := d) (μ := μB) (p := p) hp.le
              (fun i => (hgradVec_comp_aesm n i).sub
                (hw.weakGrad_component_memLp i).aestronglyMeasurable)
          have hsum : Tendsto (fun n =>
              ∑ i : Fin d,
                eLpNorm (fun x => gradVec n x i - hw.weakGrad x i) (ENNReal.ofReal p) μB)
              atTop (nhds 0) := by
            have h0 : (0 : ℝ≥0∞) = ∑ _i : Fin d, (0 : ℝ≥0∞) := by simp
            rw [h0]
            exact tendsto_finset_sum Finset.univ (fun i _ => by
              simpa [gradVec, PiLp.toLp_apply] using hψ_grad i)
          exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
            (fun _ => bot_le) hle
        have hgradVec_norm_tendsto :
            Tendsto (fun n => eLpNorm (gradVec n) (ENNReal.ofReal p) μB)
              atTop (nhds (eLpNorm hw.weakGrad (ENNReal.ofReal p) μB)) := by
          have hle : ∀ n, eLpNorm (gradVec n) (ENNReal.ofReal p) μB ≤
              eLpNorm (fun x => gradVec n x - hw.weakGrad x) (ENNReal.ofReal p) μB +
                eLpNorm hw.weakGrad (ENNReal.ofReal p) μB := by
            intro n
            calc eLpNorm (gradVec n) (ENNReal.ofReal p) μB
                = eLpNorm (fun x => (gradVec n x - hw.weakGrad x) + hw.weakGrad x)
                    (ENNReal.ofReal p) μB := by
                      congr 1
                      ext x
                      simp
              _ ≤ eLpNorm (fun x => gradVec n x - hw.weakGrad x) (ENNReal.ofReal p) μB +
                    eLpNorm hw.weakGrad (ENNReal.ofReal p) μB :=
                  eLpNorm_add_le ((hgradVec_aesm n).sub hweakGrad_aesm) hweakGrad_aesm h1p
          have hge : ∀ n, eLpNorm hw.weakGrad (ENNReal.ofReal p) μB ≤
              eLpNorm (fun x => gradVec n x - hw.weakGrad x) (ENNReal.ofReal p) μB +
                eLpNorm (gradVec n) (ENNReal.ofReal p) μB := by
            intro n
            calc eLpNorm hw.weakGrad (ENNReal.ofReal p) μB
                = eLpNorm (fun x => (hw.weakGrad x - gradVec n x) + gradVec n x)
                    (ENNReal.ofReal p) μB := by
                      congr 1
                      ext x
                      simp
              _ ≤ eLpNorm (fun x => hw.weakGrad x - gradVec n x) (ENNReal.ofReal p) μB +
                    eLpNorm (gradVec n) (ENNReal.ofReal p) μB :=
                  eLpNorm_add_le (hweakGrad_aesm.sub (hgradVec_aesm n)) (hgradVec_aesm n) h1p
              _ = eLpNorm (fun x => gradVec n x - hw.weakGrad x) (ENNReal.ofReal p) μB +
                    eLpNorm (gradVec n) (ENNReal.ofReal p) μB := by
                  have hneg_eq :
                      eLpNorm (fun x => hw.weakGrad x - gradVec n x) (ENNReal.ofReal p) μB =
                        eLpNorm (fun x => gradVec n x - hw.weakGrad x) (ENNReal.ofReal p) μB := by
                    calc
                      eLpNorm (fun x => hw.weakGrad x - gradVec n x) (ENNReal.ofReal p) μB
                          = eLpNorm (fun x => -(gradVec n x - hw.weakGrad x)) (ENNReal.ofReal p) μB := by
                              congr 1
                              ext x
                              simp
                      _ = eLpNorm (fun x => gradVec n x - hw.weakGrad x) (ENNReal.ofReal p) μB := by
                            simpa only using
                              (eLpNorm_neg (f := fun x => gradVec n x - hw.weakGrad x)
                                (p := ENNReal.ofReal p) (μ := μB))
                  simp [hneg_eq]
          refine tendsto_of_tendsto_of_tendsto_of_le_of_le ?_ ?_
            (fun n => by
              have hge' : eLpNorm hw.weakGrad (ENNReal.ofReal p) μB ≤
                  eLpNorm (gradVec n) (ENNReal.ofReal p) μB +
                    eLpNorm (fun x => gradVec n x - hw.weakGrad x) (ENNReal.ofReal p) μB := by
                simpa [add_comm] using hge n
              exact tsub_le_iff_right.mpr hge')
            (fun n => hle n)
          · have hsub :
                Tendsto
                  (fun n =>
                    eLpNorm hw.weakGrad (ENNReal.ofReal p) μB -
                      eLpNorm (fun x => gradVec n x - hw.weakGrad x) (ENNReal.ofReal p) μB)
                  atTop (nhds (eLpNorm hw.weakGrad (ENNReal.ofReal p) μB - 0)) := by
                simpa using
                  (((ENNReal.continuous_sub_left hweakGrad_memLp_vec.eLpNorm_ne_top).tendsto 0).comp
                    hgradVec_tendsto)
            simpa using hsub
          · have hadd :
                Tendsto
                  (fun n =>
                    eLpNorm (fun x => gradVec n x - hw.weakGrad x) (ENNReal.ofReal p) μB +
                      eLpNorm hw.weakGrad (ENNReal.ofReal p) μB)
                  atTop (nhds (0 + eLpNorm hw.weakGrad (ENNReal.ofReal p) μB)) := by
                exact hgradVec_tendsto.add tendsto_const_nhds
            rwa [zero_add] at hadd
        have hAn_eq : ∀ n, An n = eLpNorm (gradVec n) (ENNReal.ofReal p) μB ^ p := by
          intro n
          change
            (∫⁻ x in B, (ENNReal.ofReal ‖fderiv ℝ (ψ n) x‖) ^ p ∂volume) =
              eLpNorm (gradVec n) (ENNReal.ofReal p) μB ^ p
          calc
            ∫⁻ x in B, (ENNReal.ofReal ‖fderiv ℝ (ψ n) x‖) ^ p ∂volume
                = ∫⁻ x in B, (ENNReal.ofReal ‖gradVec n x‖) ^ p ∂volume := by
                    congr 1
                    ext x
                    simp [gradVec, norm_fderiv_eq_norm_partials_local (d := d)]
            _ = eLpNorm (gradVec n) (ENNReal.ofReal p) μB ^ p := by
                  simpa [μB] using
                    (lintegral_rpow_norm_eq_eLpNorm_pow (μ := μB) hp0 (f := gradVec n))
        have hA_lim_eq : A_lim = eLpNorm hw.weakGrad (ENNReal.ofReal p) μB ^ p := by
          change
            (∫⁻ x in B, (ENNReal.ofReal ‖hw.weakGrad x‖) ^ p ∂volume) =
              eLpNorm hw.weakGrad (ENNReal.ofReal p) μB ^ p
          simpa [μB] using
            (lintegral_rpow_norm_eq_eLpNorm_pow (μ := μB) hp0 (f := hw.weakGrad))
        rw [hA_lim_eq]
        convert hgradVec_norm_tendsto.ennrpow_const p using 1
        ext n
        exact hAn_eq n
      have hC_ne_top : C_unitBallExtensionGrad d p ≠ ⊤ := by
        unfold C_unitBallExtensionGrad
        exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.rpow_ne_top_of_nonneg (by linarith) (by simp))
      have hsum := hFn_tendsto.add hAn_tendsto
      have hCmul := ENNReal.Tendsto.const_mul hsum (Or.inr hC_ne_top)
      exact hAn_tendsto.add hCmul
    have hliminf_le : atTop.liminf (fun n => ∫⁻ x, (ENNReal.ofReal ‖G n x‖) ^ p ∂volume)
        ≤ RHS_lim := by
      calc atTop.liminf (fun n => ∫⁻ x, (ENNReal.ofReal ‖G n x‖) ^ p ∂volume)
          ≤ atTop.liminf RHS := by
            exact Filter.liminf_le_liminf (Eventually.of_forall hG_bound)
              (⟨0, Eventually.of_forall fun _ => bot_le⟩)
              (⟨⊤, fun _ _ => le_top⟩)
        _ = RHS_lim := hRHS_tendsto.liminf_eq
    exact le_trans hFatou hliminf_le
  · -- Gradient convergence: convert Set.univ.indicator to identity
    intro i
    refine (Filter.tendsto_congr fun n => eLpNorm_congr_ae ?_).mpr (hΦ_grad i)
    filter_upwards with x
    exact by
      simp [hwExt]

/-- Packaged explicit unit-ball `W^{1,p}` extension witness, assuming the single
global smoothing theorem above. -/
noncomputable def unitBallExtension_memW1pWitness
    {p : ℝ} (hp : 1 < p) {u : E → ℝ}
    (hw : MemW1pWitness (ENNReal.ofReal p) u (Metric.ball (0 : E) 1)) :
    MemW1pWitness (ENNReal.ofReal p) (unitBallExtension (d := d) u) Set.univ :=
  let h := exists_smooth_global_approx_of_unitBallExtension (d := d) hp hw
  let Gext := Classical.choose h
  let hspec := Classical.choose_spec h
  { memLp := by rw [Measure.restrict_univ]; exact hspec.1
    weakGrad := Gext
    weakGrad_component_memLp := by
      intro i; rw [Measure.restrict_univ]; exact hspec.2.1 i
    isWeakGrad := by
      have hΦ := hspec.2.2.2.2
      let Φ := Classical.choose hΦ
      have hΦspec := Classical.choose_spec hΦ
      exact hasWeakPartials_of_global_smoothApprox (d := d) hp
        hspec.1 hspec.2.1 hΦspec.1 hΦspec.2.1 hΦspec.2.2.1 hΦspec.2.2.2 }

theorem exists_unitBall_W1p_extension
    {p : ℝ} (hp : 1 < p) {u : E → ℝ}
    (hw : MemW1pWitness (ENNReal.ofReal p) u (Metric.ball (0 : E) 1)) :
    ∃ hwExt : MemW1pWitness (ENNReal.ofReal p) (unitBallExtension (d := d) u) Set.univ,
      HasCompactSupport (unitBallExtension (d := d) u) ∧
      (∀ x ∈ Metric.ball (0 : E) 1, unitBallExtension (d := d) u x = u x) ∧
      (∫⁻ x, (ENNReal.ofReal |unitBallExtension (d := d) u x|) ^ p ∂volume)
        ≤ C_unitBallExtensionFun d *
          ∫⁻ x in Metric.ball (0 : E) 1, (ENNReal.ofReal |u x|) ^ p ∂volume ∧
      (∫⁻ x, (ENNReal.ofReal ‖hwExt.weakGrad x‖) ^ p ∂volume)
        ≤ (∫⁻ x in Metric.ball (0 : E) 1, (ENNReal.ofReal ‖hw.weakGrad x‖) ^ p ∂volume) +
          C_unitBallExtensionGrad d p *
            (∫⁻ x in Metric.ball (0 : E) 1, (ENNReal.ofReal |u x|) ^ p ∂volume +
             ∫⁻ x in Metric.ball (0 : E) 1, (ENNReal.ofReal ‖hw.weakGrad x‖) ^ p ∂volume) := by
  -- Build the witness directly from exists_smooth_global_approx (single Classical.choose)
  rcases exists_smooth_global_approx_of_unitBallExtension (d := d) hp hw with
    ⟨Gext, huExt_memLp, hGext_comp_memLp, hfun_bound, hgrad_bound,
     Φ, hΦ_smooth, hΦ_cpt, hΦ_fun, hΦ_grad⟩
  let hwExt : MemW1pWitness (ENNReal.ofReal p) (unitBallExtension (d := d) u) Set.univ :=
    { memLp := by rw [Measure.restrict_univ]; exact huExt_memLp
      weakGrad := Gext
      weakGrad_component_memLp := by
        intro i; rw [Measure.restrict_univ]; exact hGext_comp_memLp i
      isWeakGrad :=
        hasWeakPartials_of_global_smoothApprox (d := d) hp
          huExt_memLp hGext_comp_memLp hΦ_smooth hΦ_cpt hΦ_fun hΦ_grad }
  exact ⟨hwExt,
    unitBallExtension_hasCompactSupport (d := d) u,
    fun x hx => unitBallExtension_eq_of_mem_ball (d := d) hx,
    hfun_bound, hgrad_bound⟩

theorem exists_unitBall_W1p_extension'
    {p : ℝ} (hp : 1 < p) {u : E → ℝ}
    (hw : MemW1pWitness (ENNReal.ofReal p) u (Metric.ball (0 : E) 1)) :
    ∃ uExt : E → ℝ, ∃ _ : MemW1pWitness (ENNReal.ofReal p) uExt Set.univ,
      HasCompactSupport uExt ∧
      (∀ x ∈ Metric.ball (0 : E) 1, uExt x = u x) := by
  rcases exists_unitBall_W1p_extension (d := d) hp hw with ⟨hwExt, hcpt, heq, _, _⟩
  exact ⟨_, hwExt, hcpt, heq⟩


end DeGiorgi
