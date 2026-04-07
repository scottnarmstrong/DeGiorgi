import DeGiorgi.Foundations
import DeGiorgi.WholeSpaceSobolev
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Normed.Lp.SmoothApprox
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Chapter 02: Sobolev Weak-Derivative Layer

This module defines weak derivatives and proves their basic closure and
uniqueness properties.
-/

noncomputable section

open MeasureTheory Metric Filter Topology Set Function Matrix
open scoped ENNReal NNReal Convolution Pointwise

namespace DeGiorgi

variable {d : ℕ} [NeZero d]

local notation "E" => EuclideanSpace ℝ (Fin d)

/-- `HasWeakPartialDeriv i g f Ω` means that `g` is the weak partial derivative
of `f` with respect to coordinate `i` on `Ω`. -/
def HasWeakPartialDeriv (i : Fin d) (g f : E → ℝ) (Ω : Set E) : Prop :=
  ∀ φ : E → ℝ,
    ContDiff ℝ (⊤ : ℕ∞) φ →
    HasCompactSupport φ →
    tsupport φ ⊆ Ω →
    ∫ x in Ω, f x * (fderiv ℝ φ x) (EuclideanSpace.single i 1) =
      -∫ x in Ω, g x * φ x

/-- Alternate name for `HasWeakPartialDeriv`. -/
abbrev HasWeakPartialDeriv' (i : Fin d) (g f : E → ℝ) (Ω : Set E) : Prop :=
  HasWeakPartialDeriv (d := d) i g f Ω

/-- `HasWeakGrad G f Ω` means that `G` is the weak gradient of `f` on `Ω`. -/
def HasWeakGrad (G : E → E) (f : E → ℝ) (Ω : Set E) : Prop :=
  ∀ i : Fin d, HasWeakPartialDeriv i (fun x => G x i) f Ω

/-- `HasWeakDiv g F Ω` means that `g` is the weak divergence of `F` on `Ω`. -/
def HasWeakDiv (g : E → ℝ) (F : E → E) (Ω : Set E) : Prop :=
  ∀ φ : E → ℝ,
    ContDiff ℝ (⊤ : ℕ∞) φ →
    HasCompactSupport φ →
    tsupport φ ⊆ Ω →
    ∫ x in Ω, (∑ i, F x i * (fderiv ℝ φ x) (EuclideanSpace.single i 1)) =
      -∫ x in Ω, g x * φ x

omit [NeZero d] in
/-- A weak partial derivative on an open set is unique up to a.e. equality. -/
theorem HasWeakPartialDeriv.ae_eq {Ω : Set E} (hΩ : IsOpen Ω)
    {i : Fin d} {g₁ g₂ f : E → ℝ}
    (h1 : HasWeakPartialDeriv i g₁ f Ω) (h2 : HasWeakPartialDeriv i g₂ f Ω)
    (hg₁ : LocallyIntegrable g₁ (volume.restrict Ω))
    (hg₂ : LocallyIntegrable g₂ (volume.restrict Ω)) :
    g₁ =ᵐ[volume.restrict Ω] g₂ := by
  suffices h : ∀ᵐ x ∂(volume.restrict Ω), (g₁ - g₂) x = 0 by
    filter_upwards [h] with x hx
    simp [sub_eq_zero] at hx
    exact hx
  rw [ae_restrict_iff' hΩ.measurableSet]
  apply IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero hΩ
  · exact locallyIntegrableOn_of_locallyIntegrable_restrict (hg₁.sub hg₂)
  · intro φ hφ hφ_supp hφ_tsupport
    have eq1 := h1 φ hφ hφ_supp hφ_tsupport
    have eq2 := h2 φ hφ hφ_supp hφ_tsupport
    have h_eq : ∫ x in Ω, g₁ x * φ x = ∫ x in Ω, g₂ x * φ x := by
      linarith
    have h_zero : ∀ x, x ∉ Ω → φ x • (g₁ - g₂) x = 0 := by
      intro x hx
      have hφx : φ x = 0 := by
        by_contra h
        exact hx (hφ_tsupport (subset_tsupport _ h))
      simp [hφx]
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero h_zero]
    simp_rw [Pi.sub_apply, smul_eq_mul, mul_sub]
    rw [integral_sub]
    · simp_rw [mul_comm (φ _)]
      linarith
    ·
      have : Integrable (fun x => φ x • g₁ x) (volume.restrict Ω) :=
        hg₁.integrable_smul_left_of_hasCompactSupport hφ.continuous hφ_supp
      simpa [smul_eq_mul] using this
    ·
      have : Integrable (fun x => φ x • g₂ x) (volume.restrict Ω) :=
        hg₂.integrable_smul_left_of_hasCompactSupport hφ.continuous hφ_supp
      simpa [smul_eq_mul] using this

omit [NeZero d] in
/-- Classical `C¹` derivatives give weak derivatives on open sets. -/
theorem HasWeakPartialDeriv.of_contDiff {Ω : Set E} (hΩ : IsOpen Ω)
    {i : Fin d} {f : E → ℝ} (hf : ContDiff ℝ 1 f) :
    HasWeakPartialDeriv i (fun x => (fderiv ℝ f x) (EuclideanSpace.single i 1)) f Ω := by
  let _ := hΩ
  intro φ hφ hφ_supp hφ_sub
  let v := EuclideanSpace.single i (1 : ℝ)
  have h_fderiv_supp : tsupport (fun x => (fderiv ℝ φ x) v) ⊆ Ω :=
    (tsupport_fderiv_apply_subset ℝ v).trans hφ_sub
  have hf_diff : Differentiable ℝ f := hf.differentiable one_ne_zero
  have hφ_diff : Differentiable ℝ φ := hφ.differentiable (by simp)
  have hf_cont : Continuous f := hf_diff.continuous
  have hφ_cont : Continuous φ := hφ_diff.continuous
  have hfderiv_φ_cont : Continuous (fun x => (fderiv ℝ φ x) v) :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hfderiv_f_cont : Continuous (fun x => (fderiv ℝ f x) v) :=
    (hf.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hφ_fderiv_supp : HasCompactSupport (fun x => (fderiv ℝ φ x) v) :=
    hφ_supp.fderiv_apply (𝕜 := ℝ) v
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero, setIntegral_eq_integral_of_forall_compl_eq_zero]
  ·
    exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
      ((hfderiv_f_cont.mul hφ_cont).integrable_of_hasCompactSupport hφ_supp.mul_left)
      ((hf_cont.mul hfderiv_φ_cont).integrable_of_hasCompactSupport hφ_fderiv_supp.mul_left)
      ((hf_cont.mul hφ_cont).integrable_of_hasCompactSupport hφ_supp.mul_left)
      (fun x _ => hf_diff x) (fun x _ => hφ_diff x)
  ·
    intro x hx
    have : x ∉ tsupport φ := fun h => hx (hφ_sub h)
    simp only [mul_eq_zero]
    right
    by_contra hf'
    exact this (subset_tsupport φ (mem_support.mpr hf'))
  ·
    intro x hx
    have : x ∉ tsupport (fun x => (fderiv ℝ φ x) v) := fun h => hx (h_fderiv_supp h)
    simp only [mul_eq_zero]
    right
    by_contra hf'
    exact this (subset_tsupport _ (mem_support.mpr hf'))

omit [NeZero d] in
/-- Product rule for weak derivatives against a smooth scalar factor. -/
theorem HasWeakPartialDeriv.mul_smooth {Ω : Set E} (hΩ : IsOpen Ω)
    {i : Fin d} {g f η : E → ℝ}
    (hf : HasWeakPartialDeriv i g f Ω)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hf_int : LocallyIntegrable f (volume.restrict Ω))
    (hg_int : LocallyIntegrable g (volume.restrict Ω)) :
    HasWeakPartialDeriv i
      (fun x => η x * g x + (fderiv ℝ η x) (EuclideanSpace.single i 1) * f x)
      (fun x => η x * f x) Ω := by
  let _ := hΩ
  intro φ hφ_smooth hφ_supp hφ_sub
  have hηφ_smooth : ContDiff ℝ (⊤ : ℕ∞) (fun x => η x * φ x) := hη.mul hφ_smooth
  have hηφ_supp : HasCompactSupport (fun x => η x * φ x) := hφ_supp.mul_left
  have hηφ_tsub : tsupport (fun x => η x * φ x) ⊆ Ω :=
    (tsupport_smul_subset_right η φ).trans hφ_sub
  have hη_diff : Differentiable ℝ η := hη.differentiable (by simp)
  have hφ_diff : Differentiable ℝ φ := hφ_smooth.differentiable (by simp)
  let ei : E := EuclideanSpace.single i (1 : ℝ)
  have fderiv_prod : ∀ x : E, (fderiv ℝ (fun y => η y * φ y) x) ei =
      η x * (fderiv ℝ φ x) ei + φ x * (fderiv ℝ η x) ei := by
    intro x
    rw [fderiv_fun_mul hη_diff.differentiableAt hφ_diff.differentiableAt]
    simp [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  have key :
      ∫ x in Ω, f x * (η x * (fderiv ℝ φ x) ei + φ x * (fderiv ℝ η x) ei) =
        -∫ x in Ω, g x * (η x * φ x) := by
    simpa [fderiv_prod, ei] using hf (fun x => η x * φ x) hηφ_smooth hηφ_supp hηφ_tsub
  have hη_deriv_cont : Continuous (fun x => (fderiv ℝ η x) ei) :=
    (hη.continuous_fderiv (by simp)).clm_apply continuous_const
  have hφ_deriv_cont : Continuous (fun x => (fderiv ℝ φ x) ei) :=
    (hφ_smooth.continuous_fderiv (by simp)).clm_apply continuous_const
  have hφ_deriv_supp : HasCompactSupport (fun x => (fderiv ℝ φ x) ei) :=
    hφ_supp.fderiv_apply (𝕜 := ℝ) ei
  have int_f_φ_dη :
      Integrable (fun x => f x * (φ x * (fderiv ℝ η x) ei)) (volume.restrict Ω) := by
    have h := hf_int.integrable_smul_right_of_hasCompactSupport
      (hφ_smooth.continuous.mul hη_deriv_cont) hφ_supp.smul_right
    simpa [smul_eq_mul] using h
  have int_f_η_dφ :
      Integrable (fun x => f x * (η x * (fderiv ℝ φ x) ei)) (volume.restrict Ω) := by
    have h := hf_int.integrable_smul_right_of_hasCompactSupport
      (hη.continuous.mul hφ_deriv_cont) hφ_deriv_supp.mul_left
    simpa [smul_eq_mul] using h
  have int_g_ηφ : Integrable (fun x => g x * (η x * φ x)) (volume.restrict Ω) := by
    have h := hg_int.integrable_smul_right_of_hasCompactSupport
      (hη.continuous.mul hφ_smooth.continuous) hηφ_supp
    simpa [smul_eq_mul] using h
  have key2 :
      ∫ x in Ω, f x * (η x * (fderiv ℝ φ x) ei) + f x * (φ x * (fderiv ℝ η x) ei) =
        -∫ x in Ω, g x * (η x * φ x) := by
    simp_rw [← mul_add] at key ⊢
    exact key
  rw [integral_add int_f_η_dφ int_f_φ_dη] at key2
  show ∫ x in Ω, η x * f x * (fderiv ℝ φ x) ei =
    -∫ x in Ω, (η x * g x + (fderiv ℝ η x) ei * f x) * φ x
  have goal_rhs_conv :
      (fun x => (η x * g x + (fderiv ℝ η x) ei * f x) * φ x) =
        (fun x => g x * (η x * φ x) + f x * (φ x * (fderiv ℝ η x) ei)) := by
    ext x
    ring
  simp_rw [goal_rhs_conv]
  rw [integral_add int_g_ηφ int_f_φ_dη, neg_add]
  have goal_lhs_conv :
      (fun x => η x * f x * (fderiv ℝ φ x) ei) =
        (fun x => f x * (η x * (fderiv ℝ φ x) ei)) := by
    ext x
    ring
  simp_rw [goal_lhs_conv]
  linarith

omit [NeZero d] in
theorem HasWeakPartialDeriv.restrict {Ω Ω' : Set E}
    (hΩ' : IsOpen Ω') (h_sub : Ω' ⊆ Ω)
    {i : Fin d} {g f : E → ℝ}
    (hf : HasWeakPartialDeriv i g f Ω) :
    HasWeakPartialDeriv i g f Ω' := by
  let _ := hΩ'
  intro φ hφ_smooth hφ_compact hφ_supp
  have hφ_supp_Ω : tsupport φ ⊆ Ω := hφ_supp.trans h_sub
  have key := hf φ hφ_smooth hφ_compact hφ_supp_Ω
  have h1 : ∀ x, x ∉ Ω' → f x * (fderiv ℝ φ x) (EuclideanSpace.single i 1) = 0 := by
    intro x hx
    have hx_notin : x ∉ tsupport φ := fun h => hx (hφ_supp h)
    have hφ_eq : φ =ᶠ[𝓝 x] 0 :=
      (isClosed_tsupport (f := φ)).isOpen_compl.eventually_mem hx_notin |>.mono
        (fun y hy => image_eq_zero_of_notMem_tsupport hy)
    rw [Filter.EventuallyEq.fderiv_eq hφ_eq]
    simp
  have h2 : ∀ x, x ∉ Ω' → g x * φ x = 0 := by
    intro x hx
    simp [image_eq_zero_of_notMem_tsupport (fun h => hx (hφ_supp h))]
  have h3 : ∀ x, x ∉ Ω → f x * (fderiv ℝ φ x) (EuclideanSpace.single i 1) = 0 :=
    fun x hx => h1 x (fun h => hx (h_sub h))
  have h4 : ∀ x, x ∉ Ω → g x * φ x = 0 :=
    fun x hx => h2 x (fun h => hx (h_sub h))
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero h1,
    setIntegral_eq_integral_of_forall_compl_eq_zero h2,
    ← setIntegral_eq_integral_of_forall_compl_eq_zero h3,
    ← setIntegral_eq_integral_of_forall_compl_eq_zero h4,
    key]

omit [NeZero d] in
private lemma tendsto_integral_mul_of_eLpNorm_tendsto_zero_p
    {μ : Measure E} {f : E → ℝ} {g : ℕ → E → ℝ} {p q : ℝ}
    (hpq : p⁻¹ + q⁻¹ = 1) (hp : 1 < p) (hq : 1 < q)
    (hf : MemLp f (ENNReal.ofReal q) μ)
    (hg : ∀ n, MemLp (g n) (ENNReal.ofReal p) μ)
    (hlim : Tendsto (fun n => eLpNorm (g n) (ENNReal.ofReal p) μ) atTop (nhds 0)) :
    Tendsto (fun n => ∫ x, f x * g n x ∂μ) atTop (nhds 0) := by
  have hpqR : p.HolderConjugate q := Real.holderConjugate_iff.mpr ⟨hp, hpq⟩
  let C : ℝ := MeasureTheory.lpNorm f (ENNReal.ofReal q) μ
  have hlim' : Tendsto (fun n => MeasureTheory.lpNorm (g n) (ENNReal.ofReal p) μ) atTop (nhds 0) := by
    have hlim_toReal :
        Tendsto (fun n => (eLpNorm (g n) (ENNReal.ofReal p) μ).toReal) atTop (nhds 0) :=
      (ENNReal.tendsto_toReal_zero_iff (fun n => (hg n).eLpNorm_ne_top)).2 hlim
    have hEq :
        (fun n => (eLpNorm (g n) (ENNReal.ofReal p) μ).toReal) =
          (fun n => MeasureTheory.lpNorm (g n) (ENNReal.ofReal p) μ) := by
      funext n
      simpa using
        (MeasureTheory.toReal_eLpNorm
          (μ := μ) (p := ENNReal.ofReal p) (f := g n) (hg n).aestronglyMeasurable)
    simpa [hEq] using hlim_toReal
  have hbound :
      ∀ n, |∫ x, f x * g n x ∂μ| ≤ C * MeasureTheory.lpNorm (g n) (ENNReal.ofReal p) μ := by
    intro n
    have h_int :
        |∫ x, f x * g n x ∂μ| ≤ ∫ x, ‖f x‖ * ‖g n x‖ ∂μ := by
      calc
        |∫ x, f x * g n x ∂μ| = ‖∫ x, f x * g n x ∂μ‖ := by rw [Real.norm_eq_abs]
        _ ≤ ∫ x, ‖f x * g n x‖ ∂μ := by
          simpa using norm_integral_le_integral_norm (μ := μ) (f := fun x => f x * g n x)
        _ = ∫ x, ‖f x‖ * ‖g n x‖ ∂μ := by simp_rw [norm_mul]
    have h_holder :=
      MeasureTheory.integral_mul_norm_le_Lp_mul_Lq
        (μ := μ) (f := f) (g := g n) (p := q) (q := p) hpqR.symm hf (hg n)
    have hp0 : ENNReal.ofReal p ≠ 0 := by
      intro hp0'
      have : p ≤ 0 := by simpa [ENNReal.ofReal_eq_zero] using hp0'
      linarith
    have hq0 : ENNReal.ofReal q ≠ 0 := by
      intro hq0'
      have : q ≤ 0 := by simpa [ENNReal.ofReal_eq_zero] using hq0'
      linarith
    have h_f_lp :
        MeasureTheory.lpNorm f (ENNReal.ofReal q) μ =
          (∫ x, ‖f x‖ ^ q ∂μ) ^ q⁻¹ := by
      simpa [ENNReal.toReal_ofReal (by linarith : 0 ≤ q)] using
        (MeasureTheory.lpNorm_eq_integral_norm_rpow_toReal
          (μ := μ) (p := ENNReal.ofReal q) (f := f) hq0 (by simp) hf.aestronglyMeasurable)
    have h_g_lp :
        MeasureTheory.lpNorm (g n) (ENNReal.ofReal p) μ =
          (∫ x, ‖g n x‖ ^ p ∂μ) ^ p⁻¹ := by
      simpa [ENNReal.toReal_ofReal (by linarith : 0 ≤ p)] using
        (MeasureTheory.lpNorm_eq_integral_norm_rpow_toReal
          (μ := μ) (p := ENNReal.ofReal p) (f := g n) hp0 (by simp) (hg n).aestronglyMeasurable)
    calc
      |∫ x, f x * g n x ∂μ| ≤ ∫ x, ‖f x‖ * ‖g n x‖ ∂μ := h_int
      _ ≤ C * MeasureTheory.lpNorm (g n) (ENNReal.ofReal p) μ := by
        simpa [C, h_f_lp, h_g_lp, mul_comm, mul_left_comm, mul_assoc] using h_holder
  have h_upper :
      Tendsto (fun n => C * MeasureTheory.lpNorm (g n) (ENNReal.ofReal p) μ) atTop (nhds 0) := by
    simpa using Tendsto.const_mul C hlim'
  have h_abs :
      Tendsto (fun n => |∫ x, f x * g n x ∂μ|) atTop (nhds 0) :=
    squeeze_zero (fun n => abs_nonneg _) hbound h_upper
  exact (tendsto_zero_iff_abs_tendsto_zero _).2 h_abs

omit [NeZero d] in
/-- `L^p`-closure of weak partial derivatives on an open set, for `1 < p < ∞`. -/
theorem HasWeakPartialDeriv.of_eLpNormApprox_p
    {Ω : Set E} (hΩ : IsOpen Ω)
    {p : ℝ} (hp : 1 < p)
    {i : Fin d} {f g : E → ℝ} {ψ : ℕ → E → ℝ} {gψ : ℕ → E → ℝ}
    (hf_memLp : MemLp f (ENNReal.ofReal p) (volume.restrict Ω))
    (hg_memLp : MemLp g (ENNReal.ofReal p) (volume.restrict Ω))
    (hψ_wd : ∀ n, HasWeakPartialDeriv i (gψ n) (ψ n) Ω)
    (hψ_fun_memLp : ∀ n, MemLp (fun x => ψ n x - f x) (ENNReal.ofReal p) (volume.restrict Ω))
    (hψ_fun :
      Tendsto (fun n => eLpNorm (fun x => ψ n x - f x) (ENNReal.ofReal p) (volume.restrict Ω))
        atTop (nhds 0))
    (hψ_grad_memLp : ∀ n, MemLp (fun x => gψ n x - g x) (ENNReal.ofReal p) (volume.restrict Ω))
    (hψ_grad :
      Tendsto (fun n => eLpNorm (fun x => gψ n x - g x) (ENNReal.ofReal p) (volume.restrict Ω))
        atTop (nhds 0)) :
    HasWeakPartialDeriv i g f Ω := by
  let _ := hΩ
  intro φ hφ hφ_supp hφ_sub
  let μ : Measure E := volume.restrict Ω
  let dφ : E → ℝ := fun x => (fderiv ℝ φ x) (EuclideanSpace.single i 1)
  let q : ℝ := Real.conjExponent p
  have hpqR : p.HolderConjugate q := Real.HolderConjugate.conjExponent hp
  have hpq : p⁻¹ + q⁻¹ = 1 := (Real.holderConjugate_iff.mp hpqR).2
  have hq : 1 < q := (Real.holderConjugate_iff.mp hpqR.symm).1
  letI : (ENNReal.ofReal p).HolderTriple (ENNReal.ofReal q) 1 :=
    ENNReal.HolderConjugate.of_toReal <| by
      simpa [ENNReal.toReal_ofReal (by linarith : 0 ≤ p),
        ENNReal.toReal_ofReal (by linarith : 0 ≤ q)] using hpqR
  have hdφ_memLp : MemLp dφ (ENNReal.ofReal q) μ := by
    have hcont : Continuous dφ := by
      simpa [dφ] using
        ((hφ.continuous_fderiv (by simp : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0)).clm_apply
          continuous_const)
    have hcpt : HasCompactSupport dφ := by
      simpa [dφ] using hφ_supp.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single i 1)
    exact (hcont.memLp_of_hasCompactSupport hcpt).restrict _
  have hφ_memLp : MemLp φ (ENNReal.ofReal q) μ :=
    (hφ.continuous.memLp_of_hasCompactSupport hφ_supp).restrict _
  have h_fun_int :
      Tendsto (fun n => ∫ x, dφ x * (ψ n x - f x) ∂μ) atTop (nhds 0) :=
    tendsto_integral_mul_of_eLpNorm_tendsto_zero_p hpq hp hq hdφ_memLp hψ_fun_memLp hψ_fun
  have h_grad_int :
      Tendsto (fun n => ∫ x, φ x * (gψ n x - g x) ∂μ) atTop (nhds 0) :=
    tendsto_integral_mul_of_eLpNorm_tendsto_zero_p hpq hp hq hφ_memLp hψ_grad_memLp hψ_grad
  have h_lhs_tendsto :
      Tendsto (fun n => ∫ x in Ω, ψ n x * dφ x)
        atTop (nhds (∫ x in Ω, f x * dφ x)) := by
    have h_eq :
        (fun n => ∫ x in Ω, ψ n x * dφ x) =
          fun n => (∫ x in Ω, f x * dφ x) + ∫ x, dφ x * (ψ n x - f x) ∂μ := by
      funext n
      have hfi : Integrable (fun x => f x * dφ x) μ := by
        simpa [mul_comm] using hdφ_memLp.integrable_mul hf_memLp
      have hdi : Integrable (fun x => dφ x * (ψ n x - f x)) μ :=
        hdφ_memLp.integrable_mul (hψ_fun_memLp n)
      calc
        ∫ x in Ω, ψ n x * dφ x
            = ∫ x, (f x * dφ x) + dφ x * (ψ n x - f x) ∂μ := by
                congr with x
                ring
        _ = (∫ x, f x * dφ x ∂μ) + ∫ x, dφ x * (ψ n x - f x) ∂μ :=
              integral_add hfi hdi
    rw [h_eq]
    simpa [μ] using Tendsto.const_add _ h_fun_int
  have h_rhs_tendsto :
      Tendsto (fun n => -∫ x in Ω, gψ n x * φ x)
        atTop (nhds (-∫ x in Ω, g x * φ x)) := by
    have h_eq :
        (fun n => -∫ x in Ω, gψ n x * φ x) =
          fun n => -(∫ x in Ω, g x * φ x) - ∫ x, φ x * (gψ n x - g x) ∂μ := by
      funext n
      have hgi : Integrable (fun x => g x * φ x) μ := by
        simpa [mul_comm] using hφ_memLp.integrable_mul hg_memLp
      have hdi : Integrable (fun x => φ x * (gψ n x - g x)) μ :=
        hφ_memLp.integrable_mul (hψ_grad_memLp n)
      have : ∫ x, gψ n x * φ x ∂μ =
          (∫ x, g x * φ x ∂μ) + ∫ x, φ x * (gψ n x - g x) ∂μ := by
        calc
          ∫ x, gψ n x * φ x ∂μ
              = ∫ x, (g x * φ x) + φ x * (gψ n x - g x) ∂μ := by
                  congr with x
                  ring
          _ = (∫ x, g x * φ x ∂μ) + ∫ x, φ x * (gψ n x - g x) ∂μ :=
                integral_add hgi hdi
      linarith
    have h_aux :
        Tendsto
          (fun n => -(∫ x, g x * φ x ∂μ) - ∫ x, φ x * (gψ n x - g x) ∂μ)
          atTop (nhds (-(∫ x, g x * φ x ∂μ) - 0)) :=
      Tendsto.const_sub _ h_grad_int
    simpa [μ, h_eq] using h_aux
  have h_eq_n :
      ∀ n,
        ∫ x in Ω, ψ n x * dφ x = -∫ x in Ω, gψ n x * φ x := by
    intro n
    exact hψ_wd n φ hφ hφ_supp hφ_sub
  have h_eq_tendsto :
      Tendsto (fun n => ∫ x in Ω, ψ n x * dφ x)
        atTop (nhds (-∫ x in Ω, g x * φ x)) := by
    simpa [h_eq_n] using h_rhs_tendsto
  exact tendsto_nhds_unique h_lhs_tendsto h_eq_tendsto


end DeGiorgi
