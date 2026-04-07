import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.Analysis.Normed.Lp.PiLp

/-!
# Lp Bare-Function Toolkit

Lp completeness and convergence results that work entirely with **bare functions**
`α → E` and `eLpNorm`, without ever constructing elements of the `Lp E p μ` Banach
space type.

## Motivation

Lean 4's type class synthesis for `EuclideanSpace ℝ (Fin d)` — which unfolds through
`PiLp → WithLp → Pi` — causes exponential heartbeat blowup when converting between
bare functions and `Lp` elements via `MemLp.toLp` / `MemLp.coeFn_toLp`. A single
`coeFn_toLp` call can exceed 6.4M heartbeats even in standalone helpers.

This toolkit avoids the `Lp` type entirely. Instead of
```
bare function → toLp → Lp → CauchySeq → complete → Lp limit → coeFn → bare function
```
we use
```
bare function → Cauchy in eLpNorm → convergence in measure
  → a.e. convergent subsequence → a.e. limit (AEStronglyMeasurable)
  → MemLp (from eLpNorm bound) → bare function
```

Every step operates on bare functions. No `toLp`, no `coeFn_toLp`.

## Main results

* `BareFunction.exists_memLp_limit_of_cauchy_eLpNorm`: Cauchy in eLpNorm → limit exists
* `BareFunction.memLp_pi_component`: Pi-valued MemLp → component MemLp
* `BareFunction.eLpNorm_pi_component_le`: Component eLpNorm ≤ vector eLpNorm
* `BareFunction.tendsto_eLpNorm_pi_component`: Vector convergence → component convergence
* `BareFunction.exists_pi_limit_of_cauchy_eLpNorm`: Combined Cauchy → limit + components
-/

noncomputable section

open MeasureTheory Metric Filter Topology Set Function
open scoped ENNReal NNReal

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

namespace BareFunction

/-! ### MemLp from convergence -/

section General

variable {E : Type*} [NormedAddCommGroup E]

/-- If `f n → g` in eLpNorm and each `f n ∈ Lp`, then `g ∈ Lp`,
provided `g` is AEStronglyMeasurable. Avoids the `Lp` type entirely.

The key observation: `eLpNorm (f n - g) → 0` means `eLpNorm (f N - g) < 1` for
some `N`. Then `eLpNorm g ≤ eLpNorm (f N - g) + eLpNorm (f N) < ∞`. -/
theorem memLp_of_tendsto_eLpNorm
    {p : ℝ≥0∞} (hp : 1 ≤ p)
    {f : ℕ → α → E} {g : α → E}
    (hf_memLp : ∀ n, MemLp (f n) p μ)
    (hg_aesm : AEStronglyMeasurable g μ)
    (hfg : Tendsto (fun n => eLpNorm (f n - g) p μ) atTop (nhds 0)) :
    MemLp g p μ := by
  refine ⟨hg_aesm, ?_⟩
  -- Find N with eLpNorm (f N - g) < 1
  obtain ⟨N, hN⟩ := (hfg.eventually (gt_mem_nhds (by norm_num : (0 : ℝ≥0∞) < 1))).exists
  -- g = f N - (f N - g), so eLpNorm g ≤ eLpNorm (f N) + eLpNorm (f N - g)
  calc eLpNorm g p μ
      = eLpNorm (f N - (f N - g)) p μ := by congr 1; ext x; simp
    _ ≤ eLpNorm (f N) p μ + eLpNorm (f N - g) p μ :=
        eLpNorm_sub_le (hf_memLp N).aestronglyMeasurable
          ((hf_memLp N).aestronglyMeasurable.sub hg_aesm) hp
    _ < ⊤ := ENNReal.add_lt_top.mpr
        ⟨(hf_memLp N).eLpNorm_lt_top, lt_of_lt_of_le hN (by norm_num)⟩

/-- Lp limit uniqueness: if f_n → g₁ and f_n → g₂ in eLpNorm, then g₁ =ᵐ g₂. -/
theorem ae_eq_of_tendsto_eLpNorm_sub
    {p : ℝ≥0∞} (hp : 1 ≤ p)
    {f : ℕ → α → E} {g₁ g₂ : α → E}
    (hf_aesm : ∀ n, AEStronglyMeasurable (f n) μ)
    (hg₁ : AEStronglyMeasurable g₁ μ) (hg₂ : AEStronglyMeasurable g₂ μ)
    (h1 : Tendsto (fun n => eLpNorm (f n - g₁) p μ) atTop (nhds 0))
    (h2 : Tendsto (fun n => eLpNorm (f n - g₂) p μ) atTop (nhds 0)) :
    g₁ =ᵐ[μ] g₂ := by
  -- eLpNorm(g₁ - g₂) is constant, bounded by eLpNorm(g₁ - f n) + eLpNorm(f n - g₂) → 0
  have hzero : eLpNorm (g₁ - g₂) p μ = 0 := le_antisymm (by
    have hbound : ∀ n, eLpNorm (g₁ - g₂) p μ ≤
        eLpNorm (f n - g₁) p μ + eLpNorm (f n - g₂) p μ := by
      intro n
      calc eLpNorm (g₁ - g₂) p μ
          = eLpNorm ((g₁ - f n) + (f n - g₂)) p μ := by
            congr 1; ext x; simp [sub_add_sub_cancel]
        _ ≤ eLpNorm (g₁ - f n) p μ + eLpNorm (f n - g₂) p μ :=
            eLpNorm_add_le (hg₁.sub (hf_aesm n)) ((hf_aesm n).sub hg₂) hp
        _ = eLpNorm (f n - g₁) p μ + eLpNorm (f n - g₂) p μ := by
            congr 1
            rw [show g₁ - f n = -(f n - g₁) from by
                  ext x
                  simp [sub_eq_add_neg],
                eLpNorm_neg]
    -- Constant ≤ sum → 0, so constant = 0
    have hsum_tendsto : Tendsto (fun n => eLpNorm (f n - g₁) p μ + eLpNorm (f n - g₂) p μ)
        atTop (nhds 0) := by simpa [add_zero] using h1.add h2
    exact ge_of_tendsto hsum_tendsto (Filter.Eventually.of_forall hbound)) bot_le
  have hae_zero := (eLpNorm_eq_zero_iff (hg₁.sub hg₂)
    (ne_of_gt (lt_of_lt_of_le (by simp : (0 : ℝ≥0∞) < 1) hp))).mp hzero
  -- g₁ - g₂ =ᵐ 0 → g₁ =ᵐ g₂
  exact hae_zero.mono fun x hx => by simpa [sub_eq_zero] using hx

set_option maxHeartbeats 6400000 in
/-- **Scalar Cauchy → limit.** Generic over codomain E and domain α. -/
theorem scalar_cauchy_to_limit
    [SecondCountableTopology E] [CompleteSpace E]
    {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp_top : p ≠ ⊤)
    {f : ℕ → α → E}
    (hf_memLp : ∀ n, MemLp (f n) p μ)
    (hf_cauchy : Tendsto (fun nm : ℕ × ℕ =>
      eLpNorm (f nm.1 - f nm.2) p μ) atTop (nhds 0)) :
    ∃ g : α → E,
      MemLp g p μ ∧
      Tendsto (fun n => eLpNorm (f n - g) p μ) atTop (nhds 0) := by
  let _ := hp_top
  -- Same approach as exists_pi_limit_of_cauchy_eLpNorm:
  -- extract controlled Cauchy subsequence → cauchy_complete_eLpNorm → upgrade convergence
  have hp : p ≠ 0 := ne_of_gt (lt_of_lt_of_le (by simp : (0 : ℝ≥0∞) < 1) hp1)
  -- Step A: pair-Cauchy → controlled bound for each ε = (2⁻¹)^(k+1)
  have hpair : ∀ k : ℕ, ∃ M : ℕ, ∀ n m, M ≤ n → M ≤ m →
      eLpNorm (f n - f m) p μ ≤ (2⁻¹ : ℝ≥0∞) ^ (k + 1) := by
    intro k
    have hε : (0 : ℝ≥0∞) < (2⁻¹ : ℝ≥0∞) ^ (k + 1) := ENNReal.pow_pos (by norm_num) _
    obtain ⟨⟨N₁, N₂⟩, hNM⟩ := (ENNReal.tendsto_atTop_zero.mp hf_cauchy _ hε)
    exact ⟨max N₁ N₂, fun n m hn hm => hNM ⟨n, m⟩
      ⟨le_trans (le_max_left _ _) hn, le_trans (le_max_right _ _) hm⟩⟩
  -- Step B: Make bounds nondecreasing
  choose M_raw hM_raw using hpair
  let M : ℕ → ℕ := fun k => (Finset.range (k + 1)).sup M_raw
  have hM_ge : ∀ k, M_raw k ≤ M k :=
    fun k => Finset.le_sup (f := M_raw) (Finset.mem_range.mpr (Nat.lt_succ_of_le le_rfl))
  have hM_mono : Monotone M :=
    fun _ _ hab => Finset.sup_mono (Finset.range_mono (Nat.add_le_add_right hab 1))
  -- Step C: Controlled Cauchy bound
  let f_sub : ℕ → α → E := fun k => f (M k)
  have hf_sub_memLp : ∀ k, MemLp (f_sub k) p μ := fun k => hf_memLp (M k)
  have hf_sub_cau : ∀ K n m, K ≤ n → K ≤ m →
      eLpNorm (f_sub n - f_sub m) p μ < (2⁻¹ : ℝ≥0∞) ^ K := by
    intro K n m hn hm
    calc eLpNorm (f_sub n - f_sub m) p μ
        ≤ (2⁻¹ : ℝ≥0∞) ^ (K + 1) :=
          hM_raw K (M n) (M m) (le_trans (hM_ge K) (hM_mono hn))
            (le_trans (hM_ge K) (hM_mono hm))
      _ < (2⁻¹ : ℝ≥0∞) ^ K := by
          rw [pow_succ']
          calc (2⁻¹ : ℝ≥0∞) * (2⁻¹ : ℝ≥0∞) ^ K
              < 1 * (2⁻¹ : ℝ≥0∞) ^ K :=
                ENNReal.mul_lt_mul_left
                  (ENNReal.pow_pos (by norm_num : (0 : ℝ≥0∞) < 2⁻¹) K).ne'
                  (by simp : (2⁻¹ : ℝ≥0∞) ^ K ≠ ⊤)
                  (by norm_num : (2⁻¹ : ℝ≥0∞) < 1)
            _ = (2⁻¹ : ℝ≥0∞) ^ K := one_mul _
  -- Step D: Apply cauchy_complete_eLpNorm
  have hB_sum : ∑' k, (2⁻¹ : ℝ≥0∞) ^ k ≠ ⊤ := by
    simp
  have ⟨g_lim, hg_lim_memLp, hg_lim_tendsto_sub⟩ :=
    MeasureTheory.Lp.cauchy_complete_eLpNorm hp1 hf_sub_memLp hB_sum hf_sub_cau
  -- Step E: Full convergence (same as exists_pi_limit_of_cauchy_eLpNorm)
  refine ⟨g_lim, hg_lim_memLp, ?_⟩
  rw [ENNReal.tendsto_atTop_zero]
  intro ε hε
  obtain ⟨K₁, hK₁⟩ := ENNReal.tendsto_atTop_zero.mp hg_lim_tendsto_sub (ε / 2)
    (ENNReal.half_pos hε.ne')
  obtain ⟨K₂, hK₂⟩ := ENNReal.tendsto_atTop_zero.mp
    (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (2⁻¹ : ℝ≥0∞) < 1))
    (ε / 2) (ENNReal.half_pos hε.ne')
  let K := max K₁ K₂
  refine ⟨M K, fun n hn => ?_⟩
  have hn_ge : M_raw K ≤ n := le_trans (hM_ge K) hn
  have hMK_ge : M_raw K ≤ M K := hM_ge K
  calc eLpNorm (f n - g_lim) p μ
      = eLpNorm ((f n - f (M K)) + (f_sub K - g_lim)) p μ := by
        congr 1; ext x; simp [f_sub, sub_add_sub_cancel]
    _ ≤ eLpNorm (f n - f (M K)) p μ + eLpNorm (f_sub K - g_lim) p μ :=
        eLpNorm_add_le ((hf_memLp n).sub (hf_memLp (M K))).aestronglyMeasurable
          ((hf_sub_memLp K).sub hg_lim_memLp).aestronglyMeasurable
          hp1
    _ ≤ ε / 2 + ε / 2 := by
        gcongr
        · calc eLpNorm (f n - f (M K)) p μ
              ≤ (2⁻¹ : ℝ≥0∞) ^ (K + 1) := hM_raw K n (M K) hn_ge hMK_ge
            _ ≤ ε / 2 := hK₂ (K + 1) (Nat.le_add_right K₂ 1 |>.trans
                (Nat.add_le_add_right (le_max_right K₁ K₂) 1))
        · exact hK₁ K (le_max_left K₁ K₂)
    _ = ε := ENNReal.add_halves ε

end General

/-! ### Component-wise results for Pi-valued functions -/

section PiComponent

variable {d : ℕ}

/-- Pi sup norm ≤ sum of component norms (pointwise). -/
private theorem pi_norm_le_sum_norms (f : Fin d → ℝ) :
    ‖f‖ ≤ ∑ i : Fin d, ‖f i‖ := by
  refine (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun i _ => norm_nonneg _)).mpr ?_
  exact fun j => Finset.single_le_sum (fun i _ => norm_nonneg _) (Finset.mem_univ j)

set_option maxHeartbeats 3200000 in
/-- Vector eLpNorm ≤ sum of component eLpNorms for Pi-valued functions.
Uses `eLpNorm_mono_real` for the pointwise bound together with
`eLpNorm_sum_le` for ℝ-valued functions, avoiding Pi instance synthesis. -/
theorem eLpNorm_pi_le_sum_component
    {p : ℝ≥0∞} (hp1 : 1 ≤ p)
    {F : α → (Fin d → ℝ)}
    (hF_comp_aesm : ∀ i : Fin d, AEStronglyMeasurable (fun x => F x i) μ) :
    eLpNorm F p μ ≤ ∑ i : Fin d, eLpNorm (fun x => F x i) p μ := by
  calc eLpNorm F p μ
      ≤ eLpNorm (fun x => ∑ i : Fin d, ‖F x i‖) p μ :=
        eLpNorm_mono_real fun x => pi_norm_le_sum_norms (F x)
    _ ≤ ∑ i : Fin d, eLpNorm (fun x => ‖F x i‖) p μ := by
        let g : Fin d → α → ℝ := fun i x => ‖F x i‖
        have hg_aesm : ∀ i : Fin d, AEStronglyMeasurable (g i) μ :=
          fun i => (hF_comp_aesm i).norm
        suffices h : ∀ (s : Finset (Fin d)),
            eLpNorm (∑ i ∈ s, g i) p μ ≤ ∑ i ∈ s, eLpNorm (g i) p μ by
          have hg_eq : (fun x => ∑ i : Fin d, ‖F x i‖) = ∑ i : Fin d, g i := by
            ext x; simp [g, Finset.sum_apply]
          rw [hg_eq]; simp only [g]; exact h Finset.univ
        intro s
        induction s using Finset.cons_induction with
        | empty => simp [eLpNorm_zero]
        | cons a s has ih =>
          rw [Finset.sum_cons, Finset.sum_cons]
          calc eLpNorm (g a + ∑ i ∈ s, g i) p μ
              ≤ eLpNorm (g a) p μ + eLpNorm (∑ i ∈ s, g i) p μ :=
                eLpNorm_add_le (hg_aesm a)
                  (Finset.aestronglyMeasurable_sum s fun i _ => hg_aesm i) hp1
            _ ≤ eLpNorm (g a) p μ + ∑ i ∈ s, eLpNorm (g i) p μ := by gcongr
    _ = ∑ i : Fin d, eLpNorm (fun x => F x i) p μ := by
        congr 1; ext i; exact eLpNorm_norm _

/-- Each component of a Pi-valued AEStronglyMeasurable function is AEStronglyMeasurable.
For `Fin d → ℝ` (NOT `EuclideanSpace`), `continuous_apply` works directly. -/
theorem aestronglyMeasurable_pi_component
    {F : α → (Fin d → ℝ)} (hF : AEStronglyMeasurable F μ) (i : Fin d) :
    AEStronglyMeasurable (fun x => F x i) μ :=
  Continuous.comp_aestronglyMeasurable (continuous_apply i) hF

/-- AEStronglyMeasurable for a Pi-valued function from its components. -/
theorem aestronglyMeasurable_pi_of_components
    {F : α → (Fin d → ℝ)}
    (hF_comp : ∀ i : Fin d, AEStronglyMeasurable (fun x => F x i) μ) :
    AEStronglyMeasurable F μ :=
  (aemeasurable_pi_iff.mpr fun i => (hF_comp i).aemeasurable).aestronglyMeasurable

/-- Component eLpNorm ≤ vector eLpNorm for Pi types.
For `Fin d → ℝ` with the sup norm, `‖f i‖ ≤ ‖f‖` is `norm_le_pi_norm`. -/
theorem eLpNorm_pi_component_le
    {p : ℝ≥0∞} {F : α → (Fin d → ℝ)} (i : Fin d) :
    eLpNorm (fun x => F x i) p μ ≤ eLpNorm F p μ :=
  eLpNorm_mono fun x => norm_le_pi_norm (f := F x) i

/-- For `F : α → (Fin d → ℝ)` in Lp, each component is in Lp. -/
theorem memLp_pi_component
    {p : ℝ≥0∞} {F : α → (Fin d → ℝ)} (hF : MemLp F p μ) (i : Fin d) :
    MemLp (fun x => F x i) p μ :=
  ⟨aestronglyMeasurable_pi_component hF.aestronglyMeasurable i,
   lt_of_le_of_lt (eLpNorm_pi_component_le i) hF.eLpNorm_lt_top⟩

set_option maxHeartbeats 800000 in
/-- Vector eLpNorm convergence → component eLpNorm convergence.
Uses `eLpNorm_pi_component_le` via an explicit function equality to avoid
expensive defeq checks. -/
theorem tendsto_eLpNorm_pi_component
    {p : ℝ≥0∞}
    {G : ℕ → α → (Fin d → ℝ)} {Gext : α → (Fin d → ℝ)}
    (hG_tendsto : Tendsto (fun n => eLpNorm (fun x => G n x - Gext x) p μ) atTop (nhds 0))
    (i : Fin d) :
    Tendsto (fun n => eLpNorm (fun x => G n x i - Gext x i) p μ) atTop (nhds 0) := by
  -- Key: (fun x => G n x i - Gext x i) = (fun x => (G n x - Gext x) i)
  -- This is definitionally true for Fin d → ℝ (Pi subtraction), but we make it
  -- explicit to avoid expensive defeq checks inside tendsto_of_tendsto.
  have hle : ∀ n, eLpNorm (fun x => G n x i - Gext x i) p μ ≤
      eLpNorm (fun x => G n x - Gext x) p μ := by
    intro n
    -- Rewrite LHS to match eLpNorm_pi_component_le's input
    show eLpNorm (fun x => (G n - Gext) x i) p μ ≤ _
    exact eLpNorm_pi_component_le i
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hG_tendsto
    (fun _ => bot_le) hle

set_option maxHeartbeats 6400000 in
/-- **Combined Cauchy → limit + components for Pi-valued sequences.**
If G n is Cauchy in eLpNorm and each G n is in Lp, then there exists a bare
function Gext in Lp with vector and component convergence.
Reduces to scalar Lp ℝ completeness per component, then reassembles. -/
theorem exists_pi_limit_of_cauchy_eLpNorm
    {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp_top : p ≠ ⊤)
    {G : ℕ → α → (Fin d → ℝ)}
    (hG_memLp : ∀ n, MemLp (G n) p μ)
    (hG_cauchy : Tendsto (fun nm : ℕ × ℕ =>
      eLpNorm (fun x => G nm.1 x - G nm.2 x) p μ) atTop (nhds 0)) :
    ∃ Gext : α → (Fin d → ℝ),
      MemLp Gext p μ ∧
      (∀ i : Fin d, MemLp (fun x => Gext x i) p μ) ∧
      Tendsto (fun n => eLpNorm (fun x => G n x - Gext x) p μ) atTop (nhds 0) ∧
      ∀ i : Fin d,
        Tendsto (fun n => eLpNorm (fun x => G n x i - Gext x i) p μ)
          atTop (nhds 0) := by
  let _ := hp_top
  haveI : Fact (1 ≤ p) := ⟨hp1⟩
  have hp : p ≠ 0 := ne_of_gt (lt_of_lt_of_le (by simp : (0 : ℝ≥0∞) < 1) hp1)
  have hcomp_cauchy : ∀ i : Fin d,
      Tendsto (fun nm : ℕ × ℕ =>
        eLpNorm (fun x => G nm.1 x i - G nm.2 x i) p μ) atTop (nhds 0) := by
    intro i
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hG_cauchy
      (fun _ => bot_le) (fun nm => by
        show eLpNorm ((G nm.1 - G nm.2) · i) p μ ≤
          eLpNorm (fun x => G nm.1 x - G nm.2 x) p μ
        exact eLpNorm_pi_component_le i)
  have hcomp_memLp : ∀ n i, MemLp (fun x => G n x i) p μ :=
    fun n i => memLp_pi_component (hG_memLp n) i
  -- (Avoids the Lp type entirely — pure bare-function approach)
  have hcomp_limit : ∀ i : Fin d, ∃ g_i : α → ℝ,
      MemLp g_i p μ ∧
      Tendsto (fun n => eLpNorm (fun x => G n x i - g_i x) p μ) atTop (nhds 0) := by
    intro i
    -- Component sequence converges in measure (from eLpNorm convergence)
    -- Extract a.e. convergent subsequence, define limit, show convergence
    -- Riesz-Fischer via Mathlib's Lp.cauchy_complete_eLpNorm (bare functions, no Lp type).
    -- Step A: From pair-Cauchy, get controlled bound for each ε = (2⁻¹)^(k+1)
    have hcauchy_i := hcomp_cauchy i
    have hpair : ∀ k : ℕ, ∃ M : ℕ, ∀ n m, M ≤ n → M ≤ m →
        eLpNorm (fun x => G n x i - G m x i) p μ ≤ (2⁻¹ : ℝ≥0∞) ^ (k + 1) := by
      intro k
      have hε : (0 : ℝ≥0∞) < (2⁻¹ : ℝ≥0∞) ^ (k + 1) := ENNReal.pow_pos (by norm_num) _
      obtain ⟨⟨N₁, N₂⟩, hNM⟩ := (ENNReal.tendsto_atTop_zero.mp hcauchy_i _ hε)
      exact ⟨max N₁ N₂, fun n m hn hm => hNM ⟨n, m⟩
        ⟨le_trans (le_max_left _ _) hn, le_trans (le_max_right _ _) hm⟩⟩
    -- Step B: Make bounds nondecreasing
    choose M_raw hM_raw using hpair
    let M : ℕ → ℕ := fun k => (Finset.range (k + 1)).sup M_raw
    have hM_ge : ∀ k, M_raw k ≤ M k :=
      fun k => Finset.le_sup (f := M_raw) (Finset.mem_range.mpr (Nat.lt_succ_of_le le_rfl))
    have hM_mono : Monotone M :=
      fun _ _ hab => Finset.sup_mono (Finset.range_mono (Nat.add_le_add_right hab 1))
    -- Step C: Reindexed sequence f_sub k = G (M k) · i satisfies controlled Cauchy
    let f_sub : ℕ → α → ℝ := fun k x => G (M k) x i
    have hf_sub_memLp : ∀ k, MemLp (f_sub k) p μ := fun k => hcomp_memLp (M k) i
    have hf_sub_cau : ∀ K n m, K ≤ n → K ≤ m →
        eLpNorm (f_sub n - f_sub m) p μ < (2⁻¹ : ℝ≥0∞) ^ K := by
      intro K n m hn hm
      -- eLpNorm ≤ (2⁻¹)^(K+1) < (2⁻¹)^K
      calc eLpNorm (f_sub n - f_sub m) p μ
          ≤ (2⁻¹ : ℝ≥0∞) ^ (K + 1) :=
            hM_raw K (M n) (M m) (le_trans (hM_ge K) (hM_mono hn))
              (le_trans (hM_ge K) (hM_mono hm))
        _ < (2⁻¹ : ℝ≥0∞) ^ K := by
            rw [pow_succ']
            calc (2⁻¹ : ℝ≥0∞) * (2⁻¹ : ℝ≥0∞) ^ K
                < 1 * (2⁻¹ : ℝ≥0∞) ^ K :=
                  ENNReal.mul_lt_mul_left
                    (ENNReal.pow_pos (by norm_num : (0 : ℝ≥0∞) < 2⁻¹) K).ne'
                    (by simp : (2⁻¹ : ℝ≥0∞) ^ K ≠ ⊤)
                    (by norm_num : (2⁻¹ : ℝ≥0∞) < 1)
              _ = (2⁻¹ : ℝ≥0∞) ^ K := one_mul _
    -- Step D: Apply Mathlib's cauchy_complete_eLpNorm (bare-function Riesz-Fischer)
    have hB_sum : ∑' k, (2⁻¹ : ℝ≥0∞) ^ k ≠ ⊤ := by
      simp
    obtain ⟨g_lim, hg_lim_memLp, hg_lim_tendsto_sub⟩ :=
      MeasureTheory.Lp.cauchy_complete_eLpNorm (E := ℝ) hp1 hf_sub_memLp hB_sum hf_sub_cau
    -- Step E: Full sequence G n · i → g_lim (not just the subsequence)
    -- Key: for large K, ∀ n ≥ M K:
    --   eLpNorm(G n · i - g_lim) ≤ eLpNorm(G n · i - G (M K) · i) + eLpNorm(f_sub K - g_lim)
    --   where first term ≤ (2⁻¹)^(K+1) (from hM_raw) and second ≤ ε/2 (from hg_lim_tendsto_sub)
    refine ⟨g_lim, hg_lim_memLp, ?_⟩
    rw [ENNReal.tendsto_atTop_zero]
    intro ε hε
    -- Find K₁ with eLpNorm(f_sub k - g_lim) ≤ ε/2 for k ≥ K₁
    obtain ⟨K₁, hK₁⟩ := ENNReal.tendsto_atTop_zero.mp hg_lim_tendsto_sub (ε / 2)
      (ENNReal.half_pos hε.ne')
    -- Find K₂ with (2⁻¹)^(K₂+1) ≤ ε/2
    obtain ⟨K₂, hK₂⟩ := ENNReal.tendsto_atTop_zero.mp
      (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (2⁻¹ : ℝ≥0∞) < 1))
      (ε / 2) (ENNReal.half_pos hε.ne')
    -- Take K = max K₁ K₂, threshold = M K
    let K := max K₁ K₂
    refine ⟨M K, fun n hn => ?_⟩
    -- n ≥ M K ≥ M_raw K, and M K ≥ M_raw K, so both n and M K satisfy the Cauchy bound
    have hn_ge : M_raw K ≤ n := le_trans (hM_ge K) hn
    have hMK_ge : M_raw K ≤ M K := hM_ge K
    calc eLpNorm (fun x => G n x i - g_lim x) p μ
        = eLpNorm ((fun x => G n x i - G (M K) x i) + (fun x => G (M K) x i - g_lim x)) p μ := by
          congr 1; ext x; simp [sub_add_sub_cancel]
      _ ≤ eLpNorm (fun x => G n x i - G (M K) x i) p μ +
            eLpNorm (fun x => G (M K) x i - g_lim x) p μ :=
          eLpNorm_add_le ((hcomp_memLp n i).sub (hcomp_memLp (M K) i)).aestronglyMeasurable
            ((hcomp_memLp (M K) i).sub hg_lim_memLp).aestronglyMeasurable hp1
      _ ≤ ε / 2 + ε / 2 := by
          gcongr
          · -- First term: ≤ (2⁻¹)^(K+1) ≤ ε/2
            calc eLpNorm (fun x => G n x i - G (M K) x i) p μ
                ≤ (2⁻¹ : ℝ≥0∞) ^ (K + 1) := hM_raw K n (M K) hn_ge hMK_ge
              _ ≤ ε / 2 := hK₂ (K + 1) (Nat.le_add_right K₂ 1 |>.trans
                  (Nat.add_le_add_right (le_max_right K₁ K₂) 1))
          · -- Second term: eLpNorm(f_sub K - g_lim) ≤ ε/2
            exact hK₁ K (le_max_left K₁ K₂)
      _ = ε := ENNReal.add_halves ε
  choose g_i hg_i_memLp hg_i_tendsto using hcomp_limit
  let Gext : α → (Fin d → ℝ) := fun x i => g_i i x
  -- ‖G n x - Gext x‖_sup ≤ ∑ i |G n x i - g_i i x| (sup ≤ sum for nonneg)
  -- so eLpNorm (G n - Gext) ≤ ∑ i eLpNorm (G n · i - g_i i) → 0
  have hG_tendsto : Tendsto (fun n => eLpNorm (fun x => G n x - Gext x) p μ)
      atTop (nhds 0) := by
    have hle : ∀ n, eLpNorm (fun x => G n x - Gext x) p μ ≤
        ∑ i : Fin d, eLpNorm (fun x => G n x i - g_i i x) p μ := by
      intro n
      exact eLpNorm_pi_le_sum_component hp1
        (fun i => (hcomp_memLp n i).sub (hg_i_memLp i) |>.aestronglyMeasurable)
    have hsum : Tendsto (fun n => ∑ i : Fin d,
        eLpNorm (fun x => G n x i - g_i i x) p μ) atTop (nhds 0) := by
      have h0 : (0 : ℝ≥0∞) = ∑ _i : Fin d, (0 : ℝ≥0∞) := by simp
      rw [h0]; exact tendsto_finset_sum Finset.univ (fun i _ => hg_i_tendsto i)
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
      (fun _ => bot_le) hle
  have hGext_aesm : AEStronglyMeasurable Gext μ :=
    aestronglyMeasurable_pi_of_components fun i => (hg_i_memLp i).aestronglyMeasurable
  have hGext_memLp : MemLp Gext p μ :=
    memLp_of_tendsto_eLpNorm hp1 hG_memLp hGext_aesm hG_tendsto
  exact ⟨Gext, hGext_memLp,
    fun i => memLp_pi_component hGext_memLp i,
    hG_tendsto,
    fun i => tendsto_eLpNorm_pi_component hG_tendsto i⟩

end PiComponent

end BareFunction
