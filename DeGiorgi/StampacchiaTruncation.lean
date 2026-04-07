import DeGiorgi.Common
import DeGiorgi.SobolevChainRule

/-!
# Chapter 02: Stampacchia

This module proves the Stampacchia truncation lemma used in the Sobolev and
iteration machinery.

## Proof strategy

**1D case**: if `f : ℝ → ℝ` is differentiable a.e., then `f' = 0` a.e. on `{f = 0}`.
Key insight: at a point where `f(x) = 0` and `f'(x) ≠ 0`, `x` is an isolated zero.
But isolated points of any set in ℝ are countable (hence measure 0).
So `{f = 0 ∧ f' ≠ 0}` is contained in a countable set and has measure 0.

**d-dimensional case**: reduce to 1D via Fubini. The restriction of `u ∈ W^{1,2}(ℝ^d)`
to a.e. coordinate line is in `W^{1,1}` (hence AC) with the right derivative.
Apply the 1D result on each line, recombine by Fubini.
-/

noncomputable section

open MeasureTheory Metric Filter Topology Set Function intervalIntegral
open scoped ENNReal NNReal

namespace DeGiorgi

variable {d : ℕ} [NeZero d]
local notation "E" => EuclideanSpace ℝ (Fin d)

/-! ## Section 1: Pointwise 1D Stampacchia -/

/-- **Core lemma**: if `f` is differentiable at `x` with `f(x) = 0` and
`f'(x) ≠ 0`, then `f(x+h) ≠ 0` for all sufficiently small `h ≠ 0`.

Proof: the little-o condition gives `|f(x+h) - c·h| ≤ (|c|/2)·|h|` for small `h`.
Since `f(x) = 0`, triangle inequality gives `|f(x+h)| ≥ |c|·|h|/2 > 0`. -/
theorem deriv_ne_zero_implies_isolated_zero {f : ℝ → ℝ} {x : ℝ} {c : ℝ}
    (hf : HasDerivAt f c x) (hfx : f x = 0) (hc : c ≠ 0) :
    ∃ δ > 0, ∀ h, 0 < |h| → |h| < δ → f (x + h) ≠ 0 := by
  rw [hasDerivAt_iff_isLittleO_nhds_zero] at hf
  have hc_pos : 0 < |c| := abs_pos.mpr hc
  rw [Asymptotics.isLittleO_iff] at hf
  have hfilt := hf (half_pos hc_pos)
  rw [Filter.eventually_iff_exists_mem] at hfilt
  obtain ⟨S, hS_mem, hS⟩ := hfilt
  obtain ⟨δ, hδ_pos, hδ_sub⟩ := Metric.mem_nhds_iff.mp hS_mem
  refine ⟨δ, hδ_pos, fun h hh_pos hh_lt hf_eq => ?_⟩
  have hh_in : h ∈ S := hδ_sub (by simp; exact hh_lt)
  have h1 := hS h hh_in
  simp only [hfx, sub_zero, Real.norm_eq_abs, smul_eq_mul] at h1
  rw [hf_eq, zero_sub, abs_neg, abs_mul] at h1
  nlinarith

/-- Contrapositive: at a non-isolated zero where `f` is differentiable, `f'(x) = 0`. -/
theorem HasDerivAt.deriv_eq_zero_of_zero_and_not_isolated {f : ℝ → ℝ} {x c : ℝ}
    (hf : HasDerivAt f c x) (hfx : f x = 0)
    (hni : ∀ δ > 0, ∃ y, y ≠ x ∧ |y - x| < δ ∧ f y = 0) :
    c = 0 := by
  by_contra hc
  obtain ⟨δ, hδ_pos, hδ⟩ := deriv_ne_zero_implies_isolated_zero hf hfx hc
  obtain ⟨y, hy_ne, hy_lt, hy_zero⟩ := hni δ hδ_pos
  exact hδ (y - x) (by rwa [abs_pos, sub_ne_zero]) hy_lt (by rwa [add_sub_cancel])

/-! ## Section 2: Isolated points are countable → a.e. version -/

/-- In ℝ, the set of isolated points of any subset S is countable.

Proof: cover by ⋃_{p,q ∈ ℚ} {unique element of S in (p,q)}.
Each fiber has at most one element (uniqueness), and ℚ × ℚ is countable. -/
theorem countable_isolated (S : Set ℝ) :
    Set.Countable {x ∈ S | ∃ ε > 0, ∀ y ∈ S, dist y x < ε → y = x} := by
  set T := {x ∈ S | ∃ ε > 0, ∀ y ∈ S, dist y x < ε → y = x}
  apply Set.Countable.mono (show T ⊆
    ⋃ p : ℚ, ⋃ q : ℚ, {x ∈ S | (p : ℝ) < x ∧ x < q ∧ ∀ y ∈ S, (p : ℝ) < y → y < q → y = x}
    from ?_)
  · apply Set.countable_iUnion; intro p
    apply Set.countable_iUnion; intro q
    rcases Set.eq_empty_or_nonempty
      {x ∈ S | (p : ℝ) < x ∧ x < q ∧ ∀ y ∈ S, (p : ℝ) < y → y < q → y = x} with h | ⟨z, hz⟩
    · rw [h]; exact Set.countable_empty
    · apply (Set.countable_singleton z).mono
      intro y hy
      simp only [Set.mem_sep_iff] at hy hz
      exact hz.2.2.2 y hy.1 hy.2.1 hy.2.2.1
  · intro x ⟨hxS, ε, hε, hiso⟩
    simp only [Set.mem_iUnion, Set.mem_sep_iff]
    obtain ⟨p, hp1, hp2⟩ := exists_rat_btwn (show x - ε < x by linarith)
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show x < x + ε by linarith)
    exact ⟨p, q, hxS, hp2, hq1, fun y hyS hpy hyq => hiso y hyS (by
      rw [Real.dist_eq, abs_lt]; constructor <;> linarith)⟩

/-- **1D Stampacchia (a.e.)**: for `f` differentiable a.e., `f' = 0` a.e. on `{f = 0}`.

Proof: {f=0 ∧ f'≠0 ∧ f differentiable} ⊆ {isolated points of {f=0}}, which is
countable (hence measure 0). The remaining set {f not differentiable} has measure 0
by hypothesis. -/
theorem deriv_eq_zero_ae_on_zeroSet {f : ℝ → ℝ}
    (hf_diff : ∀ᵐ x, HasDerivAt f (deriv f x) x) :
    ∀ᵐ x, f x = 0 → deriv f x = 0 := by
  rw [ae_iff]
  have heq : {x | ¬(f x = 0 → deriv f x = 0)} = {x | f x = 0 ∧ deriv f x ≠ 0} := by
    ext x; simp only [mem_setOf_eq, Classical.not_imp, ne_eq]
  rw [heq]
  rw [ae_iff] at hf_diff
  apply le_antisymm _ (zero_le _)
  calc volume {x | f x = 0 ∧ deriv f x ≠ 0}
      ≤ volume ({x | f x = 0 ∧ deriv f x ≠ 0 ∧ HasDerivAt f (deriv f x) x} ∪
                {x | ¬HasDerivAt f (deriv f x) x}) := by
        apply measure_mono; intro x ⟨hfx, hdx⟩
        by_cases h : HasDerivAt f (deriv f x) x
        · left; exact ⟨hfx, hdx, h⟩
        · right; exact h
    _ ≤ volume {x | f x = 0 ∧ deriv f x ≠ 0 ∧ HasDerivAt f (deriv f x) x} +
        volume {x | ¬HasDerivAt f (deriv f x) x} := measure_union_le _ _
    _ ≤ volume {x | f x = 0 ∧ deriv f x ≠ 0 ∧ HasDerivAt f (deriv f x) x} + 0 := by
        gcongr; exact hf_diff.le
    _ = volume {x | f x = 0 ∧ deriv f x ≠ 0 ∧ HasDerivAt f (deriv f x) x} := add_zero _
    _ ≤ 0 := by
        -- Every such point is isolated in {f = 0}
        have hsub : {x | f x = 0 ∧ deriv f x ≠ 0 ∧ HasDerivAt f (deriv f x) x} ⊆
            {x ∈ {x | f x = 0} | ∃ ε > 0, ∀ y ∈ {x | f x = 0}, dist y x < ε → y = x} := by
          intro x ⟨hfx, hdx, hd⟩
          refine ⟨hfx, ?_⟩
          obtain ⟨δ, hδ, hiso⟩ := deriv_ne_zero_implies_isolated_zero hd hfx hdx
          exact ⟨δ, hδ, fun y hy hyd => by
            by_contra hne
            exact hiso (y - x) (by rwa [abs_pos, sub_ne_zero])
              (by rwa [Real.dist_eq] at hyd) (by rwa [add_sub_cancel])⟩
        calc volume _ ≤ volume _ := measure_mono hsub
          _ = 0 := (countable_isolated _).measure_zero _

/-! ## Section 3: 1D Sobolev → AC → Stampacchia

### Helper lemmas
-/

/-- Smooth (C^1) functions are absolutely continuous on intervals.
Proof: continuous derivative → bounded on compact [a,b] → Lipschitz → AC. -/
private theorem contDiff_ac {a b : ℝ} {φ : ℝ → ℝ} (hφ : ContDiff ℝ 1 φ) :
    AbsolutelyContinuousOnInterval φ a b := by
  obtain ⟨x₀, _, hx₀_max⟩ := isCompact_uIcc.exists_isMaxOn
    (nonempty_uIcc) ((hφ.continuous_deriv le_rfl).nnnorm.continuousOn)
  exact (Convex.lipschitzOnWith_of_nnnorm_hasDerivWithin_le (convex_uIcc a b)
    (fun x _ => (hφ.differentiable one_ne_zero).differentiableAt.hasDerivAt.hasDerivWithinAt)
    (fun x hx => hx₀_max hx)).absolutelyContinuousOnInterval

private lemma setIntegral_Ioo_eq_interval {a b : ℝ} (hab : a ≤ b) (f : ℝ → ℝ) :
    ∫ x in Ioo a b, f x = ∫ x in a..b, f x := by
  rw [intervalIntegral.integral_of_le hab]
  exact setIntegral_congr_set Ioo_ae_eq_Ioc

private lemma integrableOn_Ioo_intervalIntegrable {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : IntegrableOn f (Ioo a b) volume) :
    IntervalIntegrable f volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
  rwa [IntegrableOn, ← Measure.restrict_congr_set (μ := volume) Ioo_ae_eq_Ioc]

private theorem integrableOn_Icc_of_Ioo {g : ℝ → ℝ} {a b : ℝ}
    (hg : IntegrableOn g (Ioo a b) volume) :
    IntegrableOn g (Icc a b) volume := by
  rwa [IntegrableOn, ← Measure.restrict_congr_set Ioo_ae_eq_Icc]

private theorem integrable_primitive {a b : ℝ} (_hab : a < b) {g : ℝ → ℝ}
    (hg : IntegrableOn g (Ioo a b) volume) :
    IntegrableOn (fun x => ∫ t in a..x, g t) (Ioo a b) volume := by
  have hcont := intervalIntegral.continuousOn_primitive (μ := volume) (integrableOn_Icc_of_Ioo hg)
  have hcont' : ContinuousOn (fun x => ∫ t in a..x, g t) (Icc a b) :=
    hcont.congr (fun x hx => by simp only [intervalIntegral.integral_of_le hx.1])
  exact (hcont'.integrableOn_compact isCompact_Icc).mono_set Ioo_subset_Icc_self

/-- AC-IBP for the integral function: `∫ F·φ' = -∫ g·φ` where `F(x) = ∫_a^x g`
and `φ` is smooth with compact support in `(a,b)`. -/
private theorem ac_ibp_step {a b : ℝ} (hab : a < b) {g φ : ℝ → ℝ}
    (hg : IntegrableOn g (Ioo a b) volume)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφ_supp : tsupport φ ⊆ Ioo a b) :
    ∫ x in a..b, (∫ t in a..x, g t) * deriv φ x =
      -(∫ x in a..b, g x * φ x) := by
  have hg_ii : IntervalIntegrable g volume a b :=
    (uIcc_of_le hab.le ▸ integrableOn_Icc_of_Ioo hg).intervalIntegrable
  have hF_ac := hg_ii.absolutelyContinuousOnInterval_intervalIntegral (left_mem_uIcc)
  have ibp := hF_ac.integral_mul_deriv_eq_deriv_mul (contDiff_ac (hφ.of_le (by norm_cast)))
  have hFa : (∫ t in a..a, g t) = 0 := intervalIntegral.integral_same
  have hφb : φ b = 0 := by
    by_contra h; exact lt_irrefl b (hφ_supp (subset_tsupport φ h)).2
  have hφa : φ a = 0 := by
    by_contra h; exact lt_irrefl a (hφ_supp (subset_tsupport φ h)).1
  rw [ibp, hFa, hφb, hφa, mul_zero, zero_mul, sub_zero, zero_sub]
  congr 1
  apply intervalIntegral.integral_congr_ae
  filter_upwards [hg_ii.ae_hasDerivAt_integral] with x hx hx_mem
  rw [(hx (uIoc_subset_uIcc hx_mem) a left_mem_uIcc).deriv]

/-- The Evans antiderivative lemma: if η ∈ C_c^∞(a,b) has zero integral,
then η = φ' for some φ ∈ C_c^∞(a,b). Proof: φ(x) = ∫_a^x η is smooth
(η is smooth), vanishes for x ≤ a (η = 0 there), and vanishes for x ≥ b
(∫η = 0 means the antiderivative returns to 0). -/
private theorem exists_antideriv_of_zero_integral {a b : ℝ} (_hab : a < b)
    {η : ℝ → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hη_cs : HasCompactSupport η)
    (hη_supp : tsupport η ⊆ Ioo a b) (hη_int : ∫ x, η x = 0) :
    ∃ φ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ ∧ HasCompactSupport φ ∧
      tsupport φ ⊆ Ioo a b ∧ ∀ x, deriv φ x = η x := by
  let φ : ℝ → ℝ := fun x => ∫ t in a..x, η t
  have hη_cont : Continuous η := hη.continuous
  have hderiv : ∀ x, HasDerivAt φ (η x) x := fun x =>
    intervalIntegral.integral_hasDerivAt_right (hη_cont.intervalIntegrable _ _)
      hη_cont.aestronglyMeasurable.stronglyMeasurableAtFilter hη_cont.continuousAt
  have hderiv_eq : deriv φ = η := funext fun x => (hderiv x).deriv
  have hφ_diff : Differentiable ℝ φ := fun x => (hderiv x).differentiableAt
  have hη_zero : ∀ x, x ∉ Ioo a b → η x = 0 := fun x hx => by
    by_contra h; exact hx (hη_supp (subset_tsupport η (Function.mem_support.mpr h)))
  have hint_ab : ∫ t in a..b, η t = 0 := by
    rw [intervalIntegral.integral_eq_integral_of_support_subset
      ((subset_tsupport η).trans (hη_supp.trans Ioo_subset_Ioc_self)), hη_int]
  have hφ_zero_ge_b : ∀ x, x ≥ b → φ x = 0 := by
    intro x hx; show ∫ t in a..x, η t = 0
    rw [← intervalIntegral.integral_add_adjacent_intervals (μ := volume)
      (hη_cont.intervalIntegrable a b) (hη_cont.intervalIntegrable b x), hint_ab]
    rw [intervalIntegral.integral_congr (show EqOn η 0 (Set.uIcc b x) from fun t ht => by
      simp only [Pi.zero_apply]; exact hη_zero t (fun h => not_le.mpr h.2 (uIcc_of_le hx ▸ ht).1))]
    simp
  obtain ⟨ε, hε_pos, hε_thick⟩ :=
    hη_cs.isCompact.exists_cthickening_subset_open isOpen_Ioo hη_supp
  have hη_supp_Icc : tsupport η ⊆ Icc (a + ε) (b - ε) := by
    intro x hx; have hx_Ioo := hη_supp hx; constructor
    · by_contra h; push_neg at h
      exact lt_irrefl a (hε_thick (Metric.mem_cthickening_of_dist_le a x ε _ hx
        (by rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hx_Ioo.1.le)]; linarith))).1
    · by_contra h; push_neg at h
      exact lt_irrefl b (hε_thick (Metric.mem_cthickening_of_dist_le b x ε _ hx
        (by rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hx_Ioo.2.le)]; linarith))).2
  have hη_zero_lt : ∀ x, x < a + ε → η x = 0 := fun x hx => by
    by_contra h; exact not_lt.mpr (hη_supp_Icc (subset_tsupport η (Function.mem_support.mpr h))).1 hx
  have hη_zero_gt : ∀ x, x > b - ε → η x = 0 := fun x hx => by
    by_contra h; exact not_lt.mpr (hη_supp_Icc (subset_tsupport η (Function.mem_support.mpr h))).2 hx
  have hφ_zero_lt : ∀ x, x < a + ε → φ x = 0 := by
    intro x hx; show ∫ t in a..x, η t = 0
    rw [intervalIntegral.integral_congr (show EqOn η 0 (Set.uIcc a x) from fun t ht => by
      simp only [Pi.zero_apply]; apply hη_zero_lt
      rcases le_total a x with hax | hxa
      · rw [uIcc_of_le hax] at ht; linarith [ht.2]
      · rw [uIcc_of_ge hxa] at ht; linarith [ht.2])]
    exact intervalIntegral.integral_zero
  have hφ_zero_gt : ∀ x, x > b - ε → φ x = 0 := by
    intro x hx; show ∫ t in a..x, η t = 0
    rw [← intervalIntegral.integral_add_adjacent_intervals (μ := volume)
      (hη_cont.intervalIntegrable a b) (hη_cont.intervalIntegrable b x), hint_ab]
    rw [intervalIntegral.integral_congr (show EqOn η 0 (Set.uIcc b x) from fun t ht => by
      simp only [Pi.zero_apply]; apply hη_zero_gt
      rcases le_total b x with hbx | hxb
      · rw [uIcc_of_le hbx] at ht; linarith [ht.1]
      · rw [uIcc_of_ge hxb] at ht; linarith [ht.1, hx])]
    simp
  have hφ_supp_Icc : Function.support φ ⊆ Icc (a + ε) (b - ε) := by
    intro x hx; constructor
    · by_contra h; push_neg at h; exact Function.mem_support.mp hx (hφ_zero_lt x h)
    · by_contra h; push_neg at h; exact Function.mem_support.mp hx (hφ_zero_gt x h)
  exact ⟨φ,
    contDiff_infty_iff_deriv.mpr ⟨hφ_diff, hderiv_eq ▸ hη⟩,
    IsCompact.of_isClosed_subset isCompact_Icc isClosed_closure
      (closure_minimal hφ_supp_Icc isClosed_Icc),
    (closure_minimal hφ_supp_Icc isClosed_Icc).trans (fun x ⟨h1, h2⟩ => ⟨by linarith, by linarith⟩),
    fun x => by rw [hderiv_eq]⟩

/-- If ∫_{(a,b)} f·η = 0 for all smooth η with support in (a,b), then f = 0 a.e.
on (a,b), hence ∫_{(a,b)} f·ψ = 0 for any ψ. Uses Mathlib's
`IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero`. -/
private theorem smooth_cutoff_approximation {a b : ℝ} (_hab : a < b)
    {f : ℝ → ℝ} (hf : IntegrableOn f (Ioo a b) volume)
    {ψ : ℝ → ℝ} (_hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (_hψ_cs : HasCompactSupport ψ)
    (hmain : ∀ η : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) η → HasCompactSupport η →
      tsupport η ⊆ Ioo a b → ∫ x in Ioo a b, f x * η x = 0) :
    ∫ x in Ioo a b, f x * ψ x = 0 := by
  have hf_ae : ∀ᵐ x ∂volume, x ∈ Ioo a b → f x = 0 := by
    apply IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero isOpen_Ioo
    · exact hf.locallyIntegrableOn
    · intro η hη hη_cs hη_supp
      have hη_zero : ∀ x, x ∉ Ioo a b → η x = 0 :=
        fun x hx => by by_contra h; exact hx (hη_supp (subset_tsupport _ h))
      rw [← setIntegral_eq_integral_of_forall_compl_eq_zero
        (fun x hx => by simp [hη_zero x hx])]
      simp only [smul_eq_mul]
      rw [show (∫ x in Ioo a b, η x * f x) = (∫ x in Ioo a b, f x * η x) from by
        congr 1; ext x; ring]
      exact hmain η hη hη_cs hη_supp
  exact integral_eq_zero_of_ae ((ae_restrict_iff' measurableSet_Ioo).mpr
    (hf_ae.mono fun x hx hx_mem => by simp [hx hx_mem]))

private lemma integrable_of_smooth_cs {f : ℝ → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hf_cs : HasCompactSupport f) : Integrable f :=
  hf.continuous.integrable_of_hasCompactSupport hf_cs

private lemma integrableOn_mul_of_smooth_cs {a b : ℝ} {g f : ℝ → ℝ}
    (hg : IntegrableOn g (Ioo a b) volume)
    (hf_cont : Continuous f) (hf_cs : HasCompactSupport f) :
    IntegrableOn (fun x => g x * f x) (Ioo a b) volume := by
  obtain ⟨M, _, hM⟩ : ∃ M : ℝ, 0 ≤ M ∧ ∀ x, ‖f x‖ ≤ M := by
    have hb := hf_cont.norm.bddAbove_range_of_hasCompactSupport hf_cs.norm
    obtain ⟨C, hC⟩ := hb
    exact ⟨max C 0, le_max_right _ _, fun x => (hC ⟨x, rfl⟩).trans (le_max_left _ _)⟩
  exact (hg.norm.mul_const M).mono'
    (hg.aestronglyMeasurable.mul hf_cont.measurable.aestronglyMeasurable)
    (ae_of_all _ fun x => by
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]; exact mul_le_mul_of_nonneg_left (hM x) (abs_nonneg _))

private lemma support_sub_tsupport {f g : ℝ → ℝ} :
    support (f - g) ⊆ tsupport f ∪ tsupport g := by
  intro x hx; simp only [mem_support, Pi.sub_apply, sub_ne_zero] at hx
  by_contra h; simp only [mem_union, not_or] at h
  exact hx (by rw [image_eq_zero_of_notMem_tsupport h.1, image_eq_zero_of_notMem_tsupport h.2])

/-- **Du Bois-Reymond lemma**: if `g ∈ L^1(a,b)` and `∫ g · φ' = 0` for all
smooth compactly supported `φ` in `(a,b)`, then `g` is constant a.e.

Proof (Evans, Appendix C): fix `ψ₀ ∈ C_c^∞(a,b)` with `∫ψ₀ = 1`, set `c = ∫g·ψ₀`.
For any test `η`, decompose `η = [η - (∫η)·ψ₀] + (∫η)·ψ₀`. The first part has zero
integral, hence is `φ'` for some test `φ` (antiderivative lemma). The hypothesis gives
`∫g·φ' = 0`, so `∫g·η = c·∫η`. Then `∫(g-c)·η = 0` for all test `η`, and the
fundamental lemma (`ae_eq_zero_of_integral_contDiff_smul_eq_zero`) gives `g = c` a.e. -/
theorem du_bois_reymond
    {a b : ℝ} (hab : a < b)
    {g : ℝ → ℝ} (hg : IntegrableOn g (Ioo a b) volume)
    (htest : ∀ φ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo a b → ∫ x in Ioo a b, g x * deriv φ x = 0) :
    ∃ C : ℝ, g =ᵐ[volume.restrict (Ioo a b)] fun _ => C := by
  have ⟨ψ₀, hψ₀_smooth, hψ₀_cs, hψ₀_supp, hψ₀_int⟩ :
      ∃ ψ₀ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ₀ ∧ HasCompactSupport ψ₀ ∧
        tsupport ψ₀ ⊆ Ioo a b ∧ ∫ x, ψ₀ x = 1 := by
    set f : ContDiffBump ((a + b) / 2) :=
      ⟨(b - a) / 8, (b - a) / 4, by linarith, by linarith⟩
    refine ⟨f.normed volume, f.contDiff_normed, f.hasCompactSupport_normed, ?_,
      f.integral_normed⟩
    rw [f.tsupport_normed_eq]; intro x hx
    simp only [mem_closedBall, Real.dist_eq] at hx; rw [mem_Ioo]
    have := abs_le.mp (show |x - (a + b) / 2| ≤ (b - a) / 4 from hx)
    constructor <;> linarith
  set c := ∫ x in Ioo a b, g x * ψ₀ x
  have hmain : ∀ η : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) η → HasCompactSupport η →
      tsupport η ⊆ Ioo a b → ∫ x in Ioo a b, (g x - c) * η x = 0 := by
    intro η hη hη_cs hη_supp
    set α := ∫ x, η x
    set η₀ : ℝ → ℝ := fun x => η x - α * ψ₀ x with hη₀_def
    have hαψ₀_cs : HasCompactSupport (fun x => α * ψ₀ x) := by
      rw [hasCompactSupport_def]
      apply hψ₀_cs.isCompact.of_isClosed_subset isClosed_closure
      exact closure_mono (fun x hx => by
        simp only [mem_support] at hx ⊢; intro h; exact hx (by simp [h]))
    have hαψ₀_tsup : tsupport (fun x => α * ψ₀ x) ⊆ tsupport ψ₀ :=
      closure_mono (fun x hx => by simp only [mem_support] at hx ⊢; intro h; exact hx (by simp [h]))
    have hunion_closed : IsClosed (tsupport η ∪ tsupport (fun x => α * ψ₀ x)) :=
      isClosed_closure.union isClosed_closure
    have hη₀_smooth : ContDiff ℝ (⊤ : ℕ∞) η₀ := hη.sub (contDiff_const.mul hψ₀_smooth)
    have hη₀_cs : HasCompactSupport η₀ := by
      rw [hasCompactSupport_def]; exact (hη_cs.isCompact.union hαψ₀_cs.isCompact).of_isClosed_subset
        isClosed_closure (closure_minimal (show support η₀ ⊆ _ from hη₀_def ▸ support_sub_tsupport) hunion_closed)
    have hη₀_supp : tsupport η₀ ⊆ Ioo a b :=
      (closure_minimal (hη₀_def ▸ support_sub_tsupport) hunion_closed).trans
        (union_subset hη_supp (hαψ₀_tsup.trans hψ₀_supp))
    have hη₀_int : ∫ x, η₀ x = 0 := by
      have : ∫ x, η₀ x = (∫ x, η x) - ∫ x, α * ψ₀ x :=
        integral_sub (integrable_of_smooth_cs hη hη_cs)
          ((integrable_of_smooth_cs hψ₀_smooth hψ₀_cs).const_mul α)
      rw [this, MeasureTheory.integral_const_mul, hψ₀_int, mul_one, sub_self]
    obtain ⟨φ, hφ_smooth, hφ_cs, hφ_supp, hφ_deriv⟩ :=
      exists_antideriv_of_zero_integral hab hη₀_smooth hη₀_cs hη₀_supp hη₀_int
    have key : ∫ x in Ioo a b, g x * η₀ x = 0 := by
      rw [show (fun x => g x * η₀ x) = (fun x => g x * deriv φ x) from by ext x; rw [hφ_deriv]]
      exact htest φ hφ_smooth hφ_cs hφ_supp
    have hgη := integrableOn_mul_of_smooth_cs hg hη.continuous hη_cs
    have hgψ₀ := integrableOn_mul_of_smooth_cs hg hψ₀_smooth.continuous hψ₀_cs
    have gη_eq : ∫ x in Ioo a b, g x * η x = α * ∫ x in Ioo a b, g x * ψ₀ x := by
      have h_pw : ∀ x, g x * η₀ x = g x * η x - α * (g x * ψ₀ x) := by
        intro x; simp [hη₀_def, mul_sub, mul_comm α, mul_assoc]
      have h_sub : ∫ x in Ioo a b, g x * η₀ x =
          (∫ x in Ioo a b, g x * η x) - ∫ x in Ioo a b, α * (g x * ψ₀ x) := by
        simp_rw [h_pw]; exact integral_sub hgη (hgψ₀.const_mul α)
      have h_smul : ∫ x in Ioo a b, α * (g x * ψ₀ x) =
          α * ∫ x in Ioo a b, g x * ψ₀ x := by
        simp_rw [show ∀ x, α * (g x * ψ₀ x) = α • (g x * ψ₀ x) from
          fun x => (smul_eq_mul _ _).symm]; exact integral_smul α _
      linarith [key, h_sub, h_smul]
    have hcη : IntegrableOn (fun x => c * η x) (Ioo a b) :=
      ((integrable_of_smooth_cs hη hη_cs).integrableOn).const_mul c
    have hη_Ioo : ∫ x in Ioo a b, η x = α :=
      setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx =>
        image_eq_zero_of_notMem_tsupport (fun hmem => hx (hη_supp hmem)))
    have hcη_eq : ∫ x in Ioo a b, c * η x = c * α := by
      simp_rw [show ∀ x, c * η x = c • η x from fun x => (smul_eq_mul _ _).symm]
      rw [MeasureTheory.integral_smul, hη_Ioo, smul_eq_mul]
    simp_rw [fun x => show (g x - c) * η x = g x * η x - c * η x from by ring]
    rw [integral_sub hgη hcη, gη_eq, hcη_eq]; ring
  refine ⟨c, ?_⟩
  set h := (Ioo a b).indicator (fun x => g x - c)
  have hh_li : LocallyIntegrable h volume := by
    exact ((integrable_indicator_iff measurableSet_Ioo).mpr
      (hg.sub (integrableOn_const (hs := measure_Ioo_lt_top.ne)))).locallyIntegrable
  have hh_zero : ∀ ψ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      ∫ x, ψ x • h x = 0 := by
    intro ψ hψ hψ_cs
    simp only [smul_eq_mul]
    rw [show (fun x => ψ x * h x) = (Ioo a b).indicator (fun x => ψ x * (g x - c)) from by
      ext x; by_cases hx : x ∈ Ioo a b <;> simp [indicator, hx, h]]
    rw [MeasureTheory.integral_indicator measurableSet_Ioo,
        show (fun x => ψ x * (g x - c)) = (fun x => (g x - c) * ψ x) from by ext; ring]
    exact smooth_cutoff_approximation hab
      (hg.sub (integrableOn_const (hs := measure_Ioo_lt_top.ne))) hψ hψ_cs hmain
  have hae := ae_eq_zero_of_integral_contDiff_smul_eq_zero hh_li hh_zero
  rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Ioo]
  filter_upwards [hae] with x hx hx_mem
  simp only [h, indicator_of_mem hx_mem] at hx
  linarith

/-- For `u ∈ W^{1,1}(a,b)` with weak derivative `g`, `u` agrees a.e. with
`x ↦ C + ∫_a^x g(t) dt` for some constant `C`.

Proof: define `F(x) = ∫_a^x g`. By AC-IBP, `F` also has weak derivative `g` on `(a,b)`.
Then `u - F` has zero weak derivative. By `du_bois_reymond`, `u - F = D` a.e. -/
theorem w11_ae_eq_ac_representative
    {a b : ℝ} (hab : a < b) {u g : ℝ → ℝ}
    (hu : IntegrableOn u (Ioo a b) volume)
    (hg : IntegrableOn g (Ioo a b) volume)
    (hweak : ∀ φ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo a b →
      ∫ x in Ioo a b, u x * deriv φ x = -∫ x in Ioo a b, g x * φ x) :
    ∃ C : ℝ, u =ᵐ[volume.restrict (Ioo a b)]
      fun x => C + ∫ t in a..x, g t := by
  set F := fun x => ∫ t in a..x, g t
  have h_uF_test : ∀ φ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo a b →
      ∫ x in Ioo a b, (u x - F x) * deriv φ x = 0 := by
    intro φ hφ hφ_cs hφ_supp
    -- Convert set integral on Ioo to interval integral (they agree for volume)
    have conv := setIntegral_Ioo_eq_interval hab.le
    rw [conv]; simp_rw [sub_mul]
    -- Split ∫(u*φ' - F*φ') = ∫u*φ' - ∫F*φ'
    have hu_ii : IntervalIntegrable (fun x => u x * deriv φ x) volume a b :=
      integrableOn_Ioo_intervalIntegrable hab.le
        ((hu.bdd_mul (hφ.continuous_deriv (by norm_cast)).aestronglyMeasurable.restrict
          (ae_of_all _ fun x => (hφ_cs.deriv.exists_bound_of_continuous
            (hφ.continuous_deriv (by norm_cast))).choose_spec x)).congr
          (ae_of_all _ fun x => by ring))
    have hF_ii : IntervalIntegrable (fun x => (∫ t in a..x, g t) * deriv φ x) volume a b := by
      apply integrableOn_Ioo_intervalIntegrable hab.le
      have hcont := (intervalIntegral.continuousOn_primitive (μ := volume)
        (integrableOn_Icc_of_Ioo hg)).congr
        (fun x hx => by show ∫ t in a..x, g t = _; rw [intervalIntegral.integral_of_le hx.1])
      exact (hcont.mul (hφ.continuous_deriv (by norm_cast)).continuousOn).integrableOn_compact
        isCompact_Icc |>.mono_set Ioo_subset_Icc_self
    rw [intervalIntegral.integral_sub hu_ii hF_ii,
        ← conv, hweak φ hφ hφ_cs hφ_supp, conv, ac_ibp_step hab hg hφ hφ_supp]; ring
  obtain ⟨D, hD⟩ := du_bois_reymond hab
    (hu.sub (integrable_primitive hab hg))
    h_uF_test
  exact ⟨D, hD.mono (fun x hx => by simp at hx; linarith)⟩

/-- **1D Stampacchia for W^{1,1}**: the weak derivative `g` vanishes a.e. on `{u = 0}`.

Proof: replace `u` by its AC representative `F` (from `w11_ae_eq_ac_representative`).
Then `F' = g` a.e. by the FTC. Apply `deriv_eq_zero_ae_on_zeroSet` to `F`. -/
theorem stampacchia_1d {a b : ℝ} (hab : a < b) {u g : ℝ → ℝ}
    (hu : IntegrableOn u (Ioo a b) volume)
    (hg : IntegrableOn g (Ioo a b) volume)
    (hweak : ∀ φ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo a b →
      ∫ x in Ioo a b, u x * deriv φ x = -∫ x in Ioo a b, g x * φ x) :
    ∀ᵐ x ∂(volume.restrict (Ioo a b)), u x = 0 → g x = 0 := by
  obtain ⟨C, hC⟩ := w11_ae_eq_ac_representative hab hu hg hweak
  set F := fun x => C + ∫ t in a..x, g t
  -- We need global a.e. differentiability. Use g̃ = indicator (Ioo a b) g (globally integrable).
  -- F̃(x) = C + ∫_a^x g̃ agrees with F on (a,b) and is globally a.e. differentiable.
  set g' := (Ioo a b).indicator g
  have hg'_li : LocallyIntegrable g' volume :=
    ((integrable_indicator_iff measurableSet_Ioo).mpr hg).locallyIntegrable
  -- F̃ has derivative g̃ a.e. globally (by FTC for locally integrable functions)
  set F' := fun x => C + ∫ t in a..x, g' t
  have hF'_ae : ∀ᵐ x, HasDerivAt F' (g' x) x := by
    filter_upwards [LocallyIntegrable.ae_hasDerivAt_integral hg'_li] with x hx
    have := (hasDerivAt_const x C).add (hx a)
    simp only [zero_add] at this; exact this
  -- Apply deriv_eq_zero_ae_on_zeroSet to F'
  have hF'_deriv_ae : ∀ᵐ x, HasDerivAt F' (deriv F' x) x :=
    hF'_ae.mono fun x hx => by rwa [hx.deriv]
  have hF'_zero := deriv_eq_zero_ae_on_zeroSet hF'_deriv_ae
  -- On (a,b): g' = g, F' = F, so combine with hC and hF'_zero.
  have hint_eq : ∀ x ∈ Ioo a b,
      (∫ t in a..x, g' t) = ∫ t in a..x, g t := by
    intro x hx; apply intervalIntegral.integral_congr_ae; apply ae_of_all
    intro t ht; rw [uIoc_of_le hx.1.le] at ht
    exact indicator_of_mem (show t ∈ Ioo a b from ⟨ht.1, lt_of_le_of_lt ht.2 hx.2⟩) g
  filter_upwards [ae_restrict_of_ae (s := Ioo a b) hF'_ae,
                   ae_restrict_of_ae (s := Ioo a b) hF'_zero,
                   hC, ae_restrict_mem measurableSet_Ioo] with x hF'_d hF'_z hu_eq hx_mem
  intro hu_zero
  have hg'_eq : g' x = g x := indicator_of_mem hx_mem g
  have hF'_eq : F' x = C + ∫ t in a..x, g t := by
    change C + ∫ t in a..x, g' t = _; congr 1; exact hint_eq x hx_mem
  rw [← hg'_eq, ← hF'_d.deriv]
  exact hF'_z (by rw [hF'_eq]; show C + ∫ t in a..x, g t = 0; linarith [hu_eq])

/-! ## Section 4: d-dimensional Stampacchia via truncation

Instead of Fubini, we use the truncation approach: compose u with smooth
approximations Φ_ε of the sign function, apply the Sobolev chain rule to get
∫ Φ_ε(u)·∂ᵢψ = -∫ Φ_ε'(u)·Gᵢ·ψ, then take ε → 0.
-/

/-- For each ε > 0, there exists a smooth truncation Φ_ε with Φ_ε(0) = 0,
|Φ_ε| ≤ ε, |Φ_ε'| ≤ 1, and Φ_ε'(s) = 1 for |s| ≤ ε/2.

Construction: take β = ContDiffBump 0 with rIn = ε/2, rOut = ε.
Define Φ(s) = ∫₀ˢ β(t) dt. Then Φ' = β, giving all properties. -/
private theorem exists_smooth_trunc (ε : ℝ) (hε : 0 < ε) :
    ∃ Φ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) Φ ∧ Φ 0 = 0 ∧
      (∀ s, |Φ s| ≤ ε) ∧ (∀ s, |deriv Φ s| ≤ 1) ∧
      (∀ s, |s| ≤ ε / 2 → deriv Φ s = 1) ∧
      (∀ s, ε ≤ |s| → deriv Φ s = 0) := by
  set β : ContDiffBump (0 : ℝ) := ⟨ε / 2, ε, by linarith, by linarith⟩
  set Φ : ℝ → ℝ := fun s => ∫ t in (0 : ℝ)..s, β t
  have hβ_smooth : ContDiff ℝ (⊤ : ℕ∞) (β : ℝ → ℝ) := β.contDiff
  have hΦ_smooth : ContDiff ℝ (⊤ : ℕ∞) Φ := by
    rw [contDiff_infty_iff_deriv]; exact ⟨fun x =>
      (β.continuous.integral_hasStrictDerivAt 0 x).hasDerivAt.differentiableAt,
      (show deriv Φ = β from funext fun s => Continuous.deriv_integral _ β.continuous 0 s) ▸ hβ_smooth⟩
  have hderiv_eq : ∀ s, deriv Φ s = β s := fun s =>
    Continuous.deriv_integral _ β.continuous 0 s
  have hΦ_zero : Φ 0 = 0 := integral_same
  have hΦ_lip : LipschitzWith 1 Φ := by
    apply lipschitzWith_of_nnnorm_deriv_le (hΦ_smooth.differentiable (by norm_cast))
    intro x; simp only [← NNReal.coe_le_coe, coe_nnnorm, NNReal.coe_one, Real.norm_eq_abs, hderiv_eq]
    exact abs_le.mpr ⟨by linarith [β.nonneg' x], β.le_one⟩
  have hΦ_abs_le : ∀ s, |Φ s| ≤ |s| := fun s => by
    have := hΦ_lip.dist_le_mul s 0; simp [dist_eq_norm, hΦ_zero, Real.norm_eq_abs] at this; linarith
  have hderiv_vanish : ∀ s, ε ≤ |s| → deriv Φ s = 0 := fun s hs => by
    rw [hderiv_eq]; exact β.zero_of_le_dist (by simp; exact hs)
  have hΦ_const_pos : ∀ s, ε ≤ s → Φ s = Φ ε := by
    intro s hs; rcases eq_or_lt_of_le hs with rfl | hlt; · rfl
    exact constant_of_derivWithin_zero (hΦ_smooth.differentiable (by norm_cast)).differentiableOn
      (fun x ⟨hxl, _⟩ => by rw [DifferentiableAt.derivWithin _ (uniqueDiffOn_Icc hlt x ⟨hxl, by linarith⟩)]
                            · exact hderiv_vanish x (by rw [abs_of_nonneg (by linarith)]; exact hxl)
                            · exact (hΦ_smooth.differentiable (by norm_cast)) x)
      s (right_mem_Icc.mpr hs)
  have hΦ_const_neg : ∀ s, s ≤ -ε → Φ s = Φ (-ε) := by
    intro s hs; rcases eq_or_lt_of_le hs with rfl | hlt; · rfl
    have hdiff := (hΦ_smooth.differentiable (by simp : (↑(⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0))
    exact (constant_of_derivWithin_zero hdiff.differentiableOn
      (fun x hx => by
        rw [DifferentiableAt.derivWithin (hdiff x) (uniqueDiffOn_Icc hlt x ⟨hx.1, le_of_lt hx.2⟩)]
        exact hderiv_vanish x (by rw [abs_of_nonpos (by linarith [hx.2])]; linarith [hx.2]))
      (-ε) (right_mem_Icc.mpr hs)).symm
  refine ⟨Φ, hΦ_smooth, hΦ_zero, fun s => ?_, fun s => ?_, fun s hs => ?_, hderiv_vanish⟩
  · by_cases h : |s| ≤ ε
    · exact le_trans (hΦ_abs_le s) h
    · push_neg at h; cases le_or_gt 0 s with
      | inl hs => rw [hΦ_const_pos s (by linarith [abs_of_nonneg hs])]; exact le_trans (hΦ_abs_le ε) (by rw [abs_of_pos hε])
      | inr hs => rw [hΦ_const_neg s (by linarith [abs_of_neg hs])]; exact le_trans (hΦ_abs_le (-ε)) (by rw [abs_neg, abs_of_pos hε])
  · rw [hderiv_eq, abs_le]; exact ⟨by linarith [β.nonneg' s], β.le_one⟩
  · rw [hderiv_eq]; exact β.one_of_mem_closedBall (by simp [mem_closedBall]; exact hs)

/-- Enhanced smooth truncation: also includes vanishing for |s| ≥ ε. -/
private theorem exists_smooth_trunc' (ε : ℝ) (hε : 0 < ε) :
    ∃ Φ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) Φ ∧ Φ 0 = 0 ∧
      (∀ s, |Φ s| ≤ ε) ∧ (∀ s, |deriv Φ s| ≤ 1) ∧
      (∀ s, |s| ≤ ε / 2 → deriv Φ s = 1) ∧
      (∀ s, ε ≤ |s| → deriv Φ s = 0) := by
  obtain ⟨Φ, hΦ_smooth, hΦ_zero, hΦ_bdd, hΦ'_bdd, hΦ'_one, hΦ'_vanish⟩ :=
    exists_smooth_trunc ε hε
  exact ⟨Φ, hΦ_smooth, hΦ_zero, hΦ_bdd, hΦ'_bdd, hΦ'_one, hΦ'_vanish⟩

/-- **Stampacchia's Theorem**: the weak gradient of a W^{1,2}(Ω) function
vanishes a.e. on the zero set.

Proof: for ε > 0, let Φ_ε be the smooth truncation from `exists_smooth_trunc`.
By the chain rule, Φ_ε∘u has weak derivative Φ_ε'(u)·G_i. The IBP identity
∫ Φ_ε(u)·∂ᵢψ = -∫ Φ_ε'(u)·G_i·ψ gives, as ε → 0:
- LHS → 0 (since |Φ_ε(u)| ≤ ε → 0)
- RHS → -∫ 1_{u=0}·G_i·ψ (since Φ_ε'(u) → 1_{u=0} by the support condition)
Hence ∫ 1_{u=0}·G_i·ψ = 0 for all test ψ. By the fundamental lemma
(`IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero`), 1_{u=0}·G_i = 0 a.e. -/
-- Helper: the sequence of truncations and their properties
private theorem weakGrad_integral_test_eq_zero
    {Ω : Set E} (hΩ : IsOpen Ω) {u : E → ℝ}
    (hu : MemW1p 2 u Ω) (hu_meas : Measurable u)
    {G : E → E} (hG : ∀ i, HasWeakPartialDeriv' i (fun x => G x i) u Ω) (i : Fin d)
    (hGi_mem : MemLp (fun x => G x i) 2 (volume.restrict Ω))
    (ψ : E → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψ_cs : HasCompactSupport ψ)
    (hψ_supp : tsupport ψ ⊆ Ω) :
    ∫ x, ψ x • (fun x => if u x = 0 then G x i else 0) x = 0 := by
  have hGi_li_restrict : LocallyIntegrable (fun x => G x i) (volume.restrict Ω) := by
    exact hGi_mem.locallyIntegrable (by norm_num)
  have hGi_li : LocallyIntegrableOn (fun x => G x i) Ω := by
    exact locallyIntegrableOn_of_locallyIntegrable_restrict hGi_li_restrict
  have hΦ : ∀ n : ℕ, ∃ Φ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) Φ ∧ Φ 0 = 0 ∧
      (∀ s, |Φ s| ≤ 1 / ((n : ℝ) + 1)) ∧ (∀ s, |deriv Φ s| ≤ 1) ∧
      (∀ s, |s| ≤ 1 / ((n : ℝ) + 1) / 2 → deriv Φ s = 1) ∧
      (∀ s, 1 / ((n : ℝ) + 1) ≤ |s| → deriv Φ s = 0) :=
    fun n => exists_smooth_trunc' (1 / ((n : ℝ) + 1)) (by positivity)
  choose Φ hΦ_smooth hΦ_zero hΦ_bdd hΦ'_bdd hΦ'_one hΦ'_vanish using hΦ
  have hchain : ∀ n, HasWeakPartialDeriv' i (fun x => deriv (Φ n) (u x) * G x i)
      (fun x => Φ n (u x)) Ω :=
    fun n => DeGiorgi.sobolev_chain_rule hΩ (hG i) hu hGi_mem
      (Φ n) (hΦ_smooth n) (hΦ_zero n) ⟨1, hΦ'_bdd n⟩
  --   ∫_Ω Φ_n(u(x)) · ∂_iψ(x) = -∫_Ω (Φ_n'(u(x)) · G_i(x)) · ψ(x)
  have hIBP : ∀ n, ∫ x in Ω, Φ n (u x) * (fderiv ℝ ψ x) (EuclideanSpace.single i 1) =
      -(∫ x in Ω, (deriv (Φ n) (u x) * G x i) * ψ x) :=
    fun n => hchain n ψ hψ hψ_cs hψ_supp
  have hderiv_ptwise : ∀ x, Filter.Tendsto
      (fun n => deriv (Φ n) (u x))
      Filter.atTop (nhds (if u x = 0 then 1 else 0)) := by
    intro x
    by_cases hux : u x = 0
    · -- When u(x) = 0: Φ_n'(0) = 1 for all n
      simp only [hux, ite_true]
      apply tendsto_atTop_of_eventually_const (i₀ := 0)
      intro n _
      exact hΦ'_one n 0 (by rw [abs_zero]; positivity)
    · -- When u(x) ≠ 0: for large n, Φ_n'(u(x)) = 0
      simp only [hux, ite_false]
      have hux_pos : 0 < |u x| := abs_pos.mpr hux
      obtain ⟨N, hN⟩ := exists_nat_gt (1 / |u x|)
      apply tendsto_atTop_of_eventually_const (i₀ := N)
      intro n hn
      apply hΦ'_vanish n (u x)
      have hn_pos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      rw [div_le_iff₀ hn_pos]
      have hN' : 1 / |u x| < ↑n + 1 := by
        calc 1 / |u x| < ↑N := hN
          _ ≤ ↑n := by exact_mod_cast hn
          _ ≤ ↑n + 1 := le_add_of_nonneg_right (by positivity)
      linarith [(div_lt_iff₀ hux_pos).mp hN']
  -- Pointwise convergence of the full integrand
  have hptwise : ∀ x, Filter.Tendsto
      (fun n => (deriv (Φ n) (u x) * G x i) * ψ x)
      Filter.atTop (nhds ((if u x = 0 then G x i else 0) * ψ x)) := by
    intro x
    have key : Filter.Tendsto (fun n => deriv (Φ n) (u x) * G x i)
        Filter.atTop (nhds ((if u x = 0 then 1 else 0) * G x i)) :=
      (hderiv_ptwise x).mul (tendsto_const_nhds (x := G x i))
    have key2 : Filter.Tendsto (fun n => deriv (Φ n) (u x) * G x i * ψ x)
        Filter.atTop (nhds ((if u x = 0 then 1 else 0) * G x i * ψ x)) :=
      key.mul (tendsto_const_nhds (x := ψ x))
    have htarget : (if u x = 0 then G x i else 0) * ψ x =
        (if u x = 0 then 1 else 0) * G x i * ψ x := by split_ifs <;> ring
    rw [htarget]
    exact key2
  have hLHS_tendsto : Filter.Tendsto
      (fun n => ∫ x in Ω, Φ n (u x) *
        (fderiv ℝ ψ x) (EuclideanSpace.single i 1))
      Filter.atTop (nhds 0) := by
    -- diψ has compact support ⊆ tsupport ψ
    set diψ : E → ℝ := fun x => (fderiv ℝ ψ x) (EuclideanSpace.single i 1)
    have hdiψ_cs : HasCompactSupport diψ :=
      hψ_cs.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single i 1)
    have hdiψ_tsup : tsupport diψ ⊆ tsupport ψ :=
      tsupport_fderiv_apply_subset ℝ (EuclideanSpace.single i 1)
    -- ∫_Ω = ∫_{tsupport ψ} since integrand vanishes outside tsupport diψ ⊆ tsupport ψ ⊆ Ω
    have hK_meas := hψ_cs.isCompact.measure_lt_top (μ := volume)
    -- Get uniform bound M for ‖diψ‖
    have hdiψ_cont : Continuous diψ :=
      (hψ.continuous_fderiv (by norm_cast)).clm_apply continuous_const
    obtain ⟨M, hM_nn, hM⟩ : ∃ M : ℝ, 0 ≤ M ∧ ∀ x, ‖diψ x‖ ≤ M := by
      obtain ⟨C, hC⟩ := hdiψ_cont.norm.bddAbove_range_of_hasCompactSupport hdiψ_cs.norm
      exact ⟨max C 0, le_max_right _ _, fun x => (hC ⟨x, rfl⟩).trans (le_max_left _ _)⟩
    -- Rewrite ∫_Ω = ∫_{tsupport ψ}
    have heq : ∀ n, ∫ x in Ω, Φ n (u x) * diψ x =
        ∫ x in tsupport ψ, Φ n (u x) * diψ x := by
      intro n
      exact setIntegral_eq_of_subset_of_forall_diff_eq_zero hΩ.measurableSet hψ_supp
        (fun x ⟨_, hx_not⟩ => by simp [image_eq_zero_of_notMem_tsupport
          (show x ∉ tsupport diψ from fun h => hx_not (hdiψ_tsup h))])
    -- Bound: ‖∫ Φ_n(u) * diψ‖ ≤ (1/(n+1)) * M * μ(K)
    set C₀ := M * (volume (tsupport ψ)).toReal
    have hbound : ∀ n : ℕ, ‖∫ x in Ω, Φ n (u x) * diψ x‖ ≤
        1 / ((n : ℝ) + 1) * C₀ := by
      intro n; rw [heq]
      calc ‖∫ x in tsupport ψ, Φ n (u x) * diψ x‖
          ≤ 1 / ((n : ℝ) + 1) * M * (volume (tsupport ψ)).toReal := by
            apply norm_setIntegral_le_of_norm_le_const hK_meas
            intro x _; rw [norm_mul, Real.norm_eq_abs]
            exact mul_le_mul (hΦ_bdd n (u x)) (hM x) (norm_nonneg _) (by positivity)
        _ = _ := by ring
    -- 1/(n+1) → 0
    have h1n : Filter.Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1))
        Filter.atTop (nhds 0) := by
      have h1 : Filter.Tendsto (fun n : ℕ => ((n : ℝ) + 1)) Filter.atTop Filter.atTop :=
        tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
      exact (h1.inv_tendsto_atTop).congr (fun n => by simp [one_div])
    have h_tend := (h1n.mul_const C₀)
    rw [zero_mul] at h_tend
    exact squeeze_zero_norm hbound (h_tend.congr fun n => by simp [one_div])
  have hRHS_tendsto : Filter.Tendsto
      (fun n => ∫ x in Ω, (deriv (Φ n) (u x) * G x i) * ψ x)
      Filter.atTop (nhds (∫ x in Ω, (if u x = 0 then G x i else 0) * ψ x)) := by
    -- Dominated convergence with bound |G_i · ψ| (since |Φ_n'(u)| ≤ 1)
    -- G_i * ψ is integrable on Ω (G_i locally integrable, ψ bounded with compact support ⊆ Ω)
    have hGψ_int : IntegrableOn (fun x => G x i * ψ x) Ω := by
      -- G_i integrable on tsupport ψ (compact ⊆ Ω, G_i locally integrable on Ω)
      have hGi_int_K : IntegrableOn (fun x => G x i) (tsupport ψ) :=
        hGi_li.integrableOn_compact_subset hψ_supp hψ_cs.isCompact
      -- ψ is bounded
      obtain ⟨Mψ, hMψ⟩ := hψ.continuous.norm.bddAbove_range_of_hasCompactSupport hψ_cs.norm
      -- G_i * ψ integrable on tsupport ψ (G_i integrable, ψ bounded)
      have : IntegrableOn (fun x => G x i * ψ x) (tsupport ψ) := by
        apply Integrable.mono' (hGi_int_K.norm.mul_const Mψ)
        · exact hGi_int_K.aestronglyMeasurable.mul
            hψ.continuous.measurable.aestronglyMeasurable.restrict
        · exact ae_of_all _ fun x => by
            rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hMψ ⟨x, rfl⟩) (norm_nonneg _)
      -- Extend to Ω: outside tsupport ψ, ψ = 0 so G_i * ψ = 0
      exact this.of_ae_diff_eq_zero hΩ.measurableSet.nullMeasurableSet
        (ae_of_all _ fun x ⟨_, hx⟩ => by simp [image_eq_zero_of_notMem_tsupport hx])
    -- Apply dominated convergence
    show Filter.Tendsto (fun n => ∫ x, (deriv (Φ n) (u x) * G x i) * ψ x ∂volume.restrict Ω)
        Filter.atTop (nhds (∫ x, (if u x = 0 then G x i else 0) * ψ x ∂volume.restrict Ω))
    apply MeasureTheory.tendsto_integral_of_dominated_convergence
      (fun x => ‖G x i * ψ x‖)
    -- (1) AEStronglyMeasurable for each n: Φ_n' continuous, u arbitrary, G_i AE-meas, ψ meas
    · intro n
      have h1 : AEStronglyMeasurable (fun x => deriv (Φ n) (u x) * G x i)
          (volume.restrict Ω) := by
        exact (((hΦ_smooth n).continuous_deriv (by norm_cast)).measurable.comp hu_meas).aestronglyMeasurable.restrict.mul
          hGi_li.aestronglyMeasurable
      exact h1.mul hψ.continuous.measurable.aestronglyMeasurable.restrict
    -- (2) Dominator integrable
    · exact hGψ_int.norm
    -- (3) Norm bound
    · intro n
      exact ae_of_all _ fun x => by
        calc
          ‖(deriv (Φ n) (u x) * G x i) * ψ x‖
              = |deriv (Φ n) (u x)| * ‖G x i‖ * ‖ψ x‖ := by
                  simp [norm_mul, Real.norm_eq_abs, mul_assoc]
          _ ≤ 1 * ‖G x i‖ * ‖ψ x‖ := by
                gcongr
                exact hΦ'_bdd n (u x)
          _ = ‖G x i * ψ x‖ := by
                simp [norm_mul]
    -- (4) Pointwise convergence
    · exact ae_of_all _ fun x => hptwise x
  have hlim : ∫ x in Ω, (if u x = 0 then G x i else 0) * ψ x = 0 := by
    have hRHS_neg : Filter.Tendsto
        (fun n => -(∫ x in Ω, (deriv (Φ n) (u x) * G x i) * ψ x))
        Filter.atTop (nhds (-(∫ x in Ω, (if u x = 0 then G x i else 0) * ψ x))) :=
      hRHS_tendsto.neg
    have hseq : (fun n => -(∫ x in Ω, (deriv (Φ n) (u x) * G x i) * ψ x)) =
        (fun n => ∫ x in Ω, Φ n (u x) *
          (fderiv ℝ ψ x) (EuclideanSpace.single i 1)) :=
        funext fun n => (hIBP n).symm
    rw [hseq] at hRHS_neg
    have := tendsto_nhds_unique hRHS_neg hLHS_tendsto
    linarith
  -- Since tsupport ψ ⊆ Ω, the integrand vanishes outside Ω
  have hsupp_eq : (fun x => ψ x • (fun x => if u x = 0 then G x i else 0) x) =
      (fun x => (if u x = 0 then G x i else 0) * ψ x) := by
    ext x; simp [smul_eq_mul, mul_comm]
  rw [hsupp_eq, ← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ω)]
  · exact hlim
  · intro x hx
    have : ψ x = 0 := by
      by_contra hne
      exact hx (hψ_supp (subset_tsupport ψ hne))
    simp [this]

private theorem weakGrad_locallyIntegrableOn
    {Ω : Set E} (_hΩ : IsOpen Ω) {u : E → ℝ} (_hu : MemW1p 2 u Ω)
    {G : E → E} (_hG : ∀ i, HasWeakPartialDeriv' i (fun x => G x i) u Ω) (i : Fin d)
    (hGi_mem : MemLp (fun x => G x i) 2 (volume.restrict Ω))
    (hu_meas : Measurable u) :
    LocallyIntegrableOn (fun x => if u x = 0 then G x i else 0) Ω := by
  let _ := (inferInstance : NeZero d)
  have hGi_li_restrict : LocallyIntegrable (fun x => G x i) (volume.restrict Ω) := by
    exact hGi_mem.locallyIntegrable (by norm_num)
  have hGi_li : LocallyIntegrableOn (fun x => G x i) Ω := by
    exact locallyIntegrableOn_of_locallyIntegrable_restrict hGi_li_restrict
  -- For each x ∈ Ω, get a neighborhood where G_i is integrable, then the indicator is too
  intro x hxΩ
  obtain ⟨t, ht_mem, ht_int⟩ := hGi_li x hxΩ
  refine ⟨t, ht_mem, ?_⟩
  -- The indicator function is integrable on t (dominated by G_i on t)
  have heq : (fun x => if u x = 0 then G x i else 0) =
      (u ⁻¹' {0}).indicator (fun x => G x i) := by
    ext x; simp [Set.indicator, Set.mem_preimage, Set.mem_singleton_iff]
  rw [heq]
  exact ht_int.indicator (hu_meas (measurableSet_singleton 0))

theorem weakGrad_ae_eq_zero_on_zeroSet
    {Ω : Set E} (hΩ : IsOpen Ω) {u : E → ℝ}
    (hu : MemW1p 2 u Ω)
    {G : E → E} (hG : ∀ i, HasWeakPartialDeriv' i (fun x => G x i) u Ω) (i : Fin d)
    (hGi_mem : MemLp (fun x => G x i) 2 (volume.restrict Ω))
    (hu_meas : Measurable u) :
    ∀ᵐ x ∂(volume.restrict Ω), u x = 0 → G x i = 0 := by
  -- Define h(x) = indicator({u=0}) * G_i(x). We show h = 0 a.e. on Ω.
  set h : E → ℝ := fun x => if u x = 0 then G x i else 0 with hh_def
  -- It suffices to show h = 0 a.e. on Ω
  suffices hgoal : ∀ᵐ x ∂volume, x ∈ Ω → h x = 0 by
    rw [ae_restrict_iff' hΩ.measurableSet]
    filter_upwards [hgoal] with x hx hxΩ hux
    have := hx hxΩ
    simp only [hh_def, hux, ite_true] at this
    exact this
  -- Apply the fundamental lemma
  apply hΩ.ae_eq_zero_of_integral_contDiff_smul_eq_zero
  -- Sub-goal 1: h is locally integrable on Ω
  · exact weakGrad_locallyIntegrableOn hΩ hu hG i hGi_mem hu_meas
  -- Sub-goal 2: ∫ ψ • h = 0 for all smooth compactly supported ψ with supp ⊆ Ω
  · intro ψ hψ hψ_cs hψ_supp
    exact weakGrad_integral_test_eq_zero hΩ hu hu_meas hG i hGi_mem ψ hψ hψ_cs hψ_supp

end DeGiorgi
