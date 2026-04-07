import DeGiorgi.SobolevSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Chapter 02: Unit-Ball Approximation Profiles

This module contains the smooth cutoff profiles and the basic compact-support
approximation tool used in the unit-ball argument.
-/

noncomputable section

open MeasureTheory Metric Filter Topology Set Function Matrix
open scoped ENNReal NNReal

namespace DeGiorgi

variable {d : ℕ} [NeZero d]

local notation "E" => EuclideanSpace ℝ (Fin d)

open Real in
private lemma smoothTransition_differentiable' :
    Differentiable ℝ smoothTransition :=
  smoothTransition.contDiff.differentiable_one

open Real in
private lemma smoothTransition_deriv_continuous' :
    Continuous (deriv smoothTransition) := by
  exact smoothTransition.contDiff.continuous_deriv_one

open Real in
private lemma st_deriv_zero_neg {x : ℝ} (hx : x < 0) :
    deriv smoothTransition x = 0 := by
  have h : smoothTransition =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
    filter_upwards [Iio_mem_nhds hx] with y hy
    exact smoothTransition.zero_of_nonpos hy.le
  exact h.deriv_eq.trans (deriv_const x (0 : ℝ))

open Real in
private lemma st_deriv_zero_gt {x : ℝ} (hx : 1 < x) :
    deriv smoothTransition x = 0 := by
  have h : smoothTransition =ᶠ[𝓝 x] fun _ => (1 : ℝ) := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    exact smoothTransition.one_of_one_le hy.le
  exact h.deriv_eq.trans (deriv_const x (1 : ℝ))

open Real in
private lemma smoothTransition_nnnorm_deriv_bounded :
    ∃ C : ℝ≥0, ∀ x : ℝ, ‖deriv smoothTransition x‖₊ ≤ C := by
  have h1 : ContDiff ℝ 1 smoothTransition := smoothTransition.contDiff
  have h_cont : Continuous (deriv smoothTransition) := h1.continuous_deriv_one
  obtain ⟨M, -, hM_max⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_isMaxOn
    (nonempty_Icc.2 zero_le_one) h_cont.norm.continuousOn
  have hbound : ∀ x : ℝ, ‖deriv smoothTransition x‖ ≤ ‖deriv smoothTransition M‖ := by
    intro x
    by_cases hx0 : x < 0
    · rw [st_deriv_zero_neg hx0, norm_zero]
      exact norm_nonneg _
    · by_cases hx1 : 1 < x
      · rw [st_deriv_zero_gt hx1, norm_zero]
        exact norm_nonneg _
      · push_neg at hx0 hx1
        exact Filter.eventually_principal.mp hM_max x (Set.mem_Icc.2 ⟨hx0, hx1⟩)
  refine ⟨⟨‖deriv smoothTransition M‖, norm_nonneg _⟩, fun x => ?_⟩
  rw [← NNReal.coe_le_coe, NNReal.coe_mk, coe_nnnorm]
  exact hbound x

/-- Universal derivative bound for smooth cutoff profiles. -/
noncomputable def Mst : ℝ≥0 := smoothTransition_nnnorm_deriv_bounded.choose

open Real in
lemma smoothTransition_nnnorm_deriv_le :
    ∀ x : ℝ, ‖deriv smoothTransition x‖₊ ≤ Mst :=
  smoothTransition_nnnorm_deriv_bounded.choose_spec

open Real in
lemma smoothTransition_lipschitz : LipschitzWith Mst Real.smoothTransition :=
  lipschitzWith_of_nnnorm_deriv_le smoothTransition_differentiable'
    smoothTransition_nnnorm_deriv_le

def myCutoff (x₀ : E) (r R : ℝ) (x : E) : ℝ :=
  Real.smoothTransition ((R - ‖x - x₀‖) / (R - r))

omit [NeZero d] in
lemma myCutoff_nonneg (x₀ : E) (r R : ℝ) (x : E) : 0 ≤ myCutoff x₀ r R x :=
  Real.smoothTransition.nonneg _

omit [NeZero d] in
lemma myCutoff_le_one (x₀ : E) (r R : ℝ) (x : E) : myCutoff x₀ r R x ≤ 1 :=
  Real.smoothTransition.le_one _

omit [NeZero d] in
lemma myCutoff_eq_one {x₀ : E} {r R : ℝ} (hrR : r < R) {x : E}
    (hx : x ∈ Metric.ball x₀ r) : myCutoff x₀ r R x = 1 := by
  unfold myCutoff
  apply Real.smoothTransition.one_of_one_le
  rw [le_div_iff₀ (sub_pos.2 hrR)]
  have : ‖x - x₀‖ < r := by rwa [← dist_eq_norm, ← Metric.mem_ball]
  linarith

omit [NeZero d] in
lemma myCutoff_eq_zero {x₀ : E} {r R : ℝ} (hrR : r < R) {x : E}
    (hx : x ∉ Metric.closedBall x₀ R) : myCutoff x₀ r R x = 0 := by
  unfold myCutoff
  apply Real.smoothTransition.zero_of_nonpos
  have hx' : R < dist x x₀ := by
    rw [Metric.mem_closedBall, not_le] at hx
    exact hx
  have hx'' : R < ‖x - x₀‖ := by
    simpa [dist_eq_norm] using hx'
  exact div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)

omit [NeZero d] in
lemma myCutoff_support_subset (x₀ : E) {r R : ℝ} (hrR : r < R) :
    tsupport (myCutoff x₀ r R) ⊆ Metric.closedBall x₀ R := by
  apply closure_minimal (fun x hx => ?_) Metric.isClosed_closedBall
  contrapose! hx
  simp only [mem_support, ne_eq, not_not]
  exact myCutoff_eq_zero hrR hx

omit [NeZero d] in
lemma myCutoff_contDiff {x₀ : E} {r R : ℝ} (hr : 0 < r) (hrR : r < R) :
    ContDiff ℝ (⊤ : ℕ∞) (myCutoff x₀ r R) := by
  have hRr : (0 : ℝ) < R - r := sub_pos.2 hrR
  rw [contDiff_iff_contDiffAt]
  intro x
  unfold myCutoff
  rcases eq_or_ne (x - x₀) 0 with hx | hx
  · have hxx : x = x₀ := sub_eq_zero.mp hx
    subst x
    have harg : ContinuousAt (fun y : E => (R - ‖y - x₀‖) / (R - r)) x₀ := by
      apply ContinuousAt.div
      · exact continuousAt_const.sub (continuous_norm.continuousAt.comp
          (continuousAt_id.sub continuousAt_const))
      · exact continuousAt_const
      · exact hRr.ne'
    have hgt : 1 < (fun y : E => (R - ‖y - x₀‖) / (R - r)) x₀ := by
      simp
      rw [one_lt_div hRr]
      linarith
    have hge1 : ∀ᶠ y in 𝓝 x₀, 1 ≤ (R - ‖y - x₀‖) / (R - r) :=
      harg.eventually (Ioi_mem_nhds hgt) |>.mono fun y hy => le_of_lt hy
    have hconst : ContDiffAt ℝ (⊤ : ℕ∞) (fun _ : E => (1 : ℝ)) x₀ := contDiffAt_const
    exact hconst.congr_of_eventuallyEq
      (hge1.mono fun y hy => Real.smoothTransition.one_of_one_le hy)
  · have hnorm : ContDiffAt ℝ (⊤ : ℕ∞) (fun y : E => ‖y - x₀‖) x :=
      (contDiffAt_norm ℝ hx).comp x (contDiffAt_id.sub contDiffAt_const)
    have harg : ContDiffAt ℝ (⊤ : ℕ∞) (fun y : E => (R - ‖y - x₀‖) / (R - r)) x := by
      simpa only [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
        ((contDiffAt_const.sub hnorm).div contDiffAt_const hRr.ne')
    have hsmooth : ContDiffAt ℝ (⊤ : ℕ∞) Real.smoothTransition
        ((R - ‖x - x₀‖) / (R - r)) := Real.smoothTransition.contDiffAt
    exact ContDiffAt.comp
      (f := fun y : E => (R - ‖y - x₀‖) / (R - r))
      (g := Real.smoothTransition) x hsmooth harg

omit [NeZero d] in
private lemma radial_lipschitz (x₀ : E) {r R : ℝ} (hrR : r < R) :
    LipschitzWith ⟨(R - r)⁻¹, inv_nonneg.mpr (sub_pos.2 hrR).le⟩
      (fun x : E => (R - ‖x - x₀‖) / (R - r)) :=
  LipschitzWith.of_dist_le_mul fun x y => by
    simp only [NNReal.coe_mk, dist_eq_norm, Real.norm_eq_abs]
    have hpos : (0 : ℝ) < R - r := sub_pos.2 hrR
    have key : abs (‖y - x₀‖ - ‖x - x₀‖) ≤ ‖x - y‖ := calc
      abs (‖y - x₀‖ - ‖x - x₀‖) ≤ ‖(y - x₀) - (x - x₀)‖ := by
        exact abs_norm_sub_norm_le (y - x₀) (x - x₀)
      _ = ‖y - x‖ := by congr 1; abel
      _ = ‖x - y‖ := by exact norm_sub_rev y x
    have hsub : (R - ‖x - x₀‖) / (R - r) - (R - ‖y - x₀‖) / (R - r) =
        (‖y - x₀‖ - ‖x - x₀‖) / (R - r) := by ring
    rw [hsub, abs_div, abs_of_pos hpos, inv_mul_eq_div]
    exact div_le_div_of_nonneg_right key hpos.le

omit [NeZero d] in
lemma myCutoff_lipschitz (x₀ : E) {r R : ℝ} (hrR : r < R) :
    LipschitzWith (Mst * ⟨(R - r)⁻¹, inv_nonneg.mpr (sub_pos.2 hrR).le⟩)
      (myCutoff x₀ r R) :=
  smoothTransition_lipschitz.comp (radial_lipschitz x₀ hrR)

omit [NeZero d] in
lemma myCutoff_fderiv_bound (x₀ : E) {r R : ℝ} (hrR : r < R) (x : E) :
    ‖fderiv ℝ (myCutoff x₀ r R) x‖ ≤ ↑Mst * (R - r)⁻¹ := by
  have h : ‖fderiv ℝ (myCutoff x₀ r R) x‖ ≤
      ↑(Mst * ⟨(R - r)⁻¹, inv_nonneg.mpr (sub_nonneg.mpr hrR.le)⟩) :=
    norm_fderiv_le_of_lipschitz (𝕜 := ℝ) (x₀ := x) (myCutoff_lipschitz x₀ hrR)
  rwa [NNReal.coe_mul, NNReal.coe_mk] at h

structure Cutoff (x₀ : E) (r R : ℝ) where
  toFun : E → ℝ
  smooth : ContDiff ℝ (⊤ : ℕ∞) toFun
  nonneg : ∀ x, 0 ≤ toFun x
  le_one : ∀ x, toFun x ≤ 1
  eq_one : ∀ x ∈ Metric.ball x₀ r, toFun x = 1
  support_subset : tsupport toFun ⊆ Metric.closedBall x₀ R
  grad_bound : ∀ x, ‖fderiv ℝ toFun x‖ ≤ ↑Mst * (R - r)⁻¹

omit [NeZero d] in
theorem Cutoff.exists (x₀ : E) {r R : ℝ} (hr : 0 < r) (hR : r < R) :
    ∃ _η : Cutoff x₀ r R, True :=
  ⟨⟨myCutoff x₀ r R,
    by simpa using (myCutoff_contDiff (x₀ := x₀) hr hR),
    myCutoff_nonneg x₀ r R,
    myCutoff_le_one x₀ r R,
    fun x hx => myCutoff_eq_one (x₀ := x₀) hR hx,
    myCutoff_support_subset x₀ hR,
    fun x => myCutoff_fderiv_bound x₀ hR x⟩, trivial⟩

omit [NeZero d] in
theorem Lp_approx_by_continuous_compactly_supported
    {f : E → ℝ} {p : ℝ≥0∞}
    (hp : 1 ≤ p) (hp' : p ≠ ⊤)
    (hf : MemLp f p volume)
    {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∃ g : E → ℝ, Continuous g ∧ HasCompactSupport g ∧
      eLpNorm (f - g) p volume < δ := by
  obtain ⟨ε, hε_pos, hε_lt⟩ : ∃ ε : ℝ, 0 < ε ∧ ENNReal.ofReal ε < δ := by
    by_cases hδ_top : δ = ⊤
    · exact ⟨1, one_pos, hδ_top ▸ ENNReal.ofReal_lt_top⟩
    · have hδ_lt_top : δ < ⊤ := lt_top_iff_ne_top.mpr hδ_top
      refine ⟨(δ / 2).toReal,
        ENNReal.toReal_pos (ENNReal.div_pos hδ.ne' (by norm_num)).ne'
          (ENNReal.div_lt_top hδ_lt_top.ne (by norm_num)).ne, ?_⟩
      calc
        ENNReal.ofReal (δ / 2).toReal = δ / 2 :=
          ENNReal.ofReal_toReal (ENNReal.div_lt_top hδ_lt_top.ne (by norm_num)).ne
        _ < δ := ENNReal.half_lt_self hδ.ne' hδ_top
  obtain ⟨g, hg_supp, hg_smooth, hg_norm⟩ := hf.exist_eLpNorm_sub_le hp' hp hε_pos
  exact ⟨g, hg_smooth.continuous, hg_supp, lt_of_le_of_lt hg_norm hε_lt⟩


end DeGiorgi
