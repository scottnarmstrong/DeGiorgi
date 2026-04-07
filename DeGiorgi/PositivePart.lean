import DeGiorgi.SobolevSpace
import DeGiorgi.StampacchiaTruncation

/-!
# Chapter 02: Positive-Part And Approximation Layer

This module develops the positive-part and approximation tools used by the
Sobolev and De Giorgi arguments:

- weak-derivative uniqueness and approximation transfer;
- the canonical indicator-difference convergence theorem;
- the smooth positive-part chain rule;
- the auxiliary positive-part witness constructor.

The emphasis here is on the approximation statements needed to pass from Sobolev
witness data to positive-part closures that can be reused later in the De
Giorgi iteration.
-/

noncomputable section

open MeasureTheory Metric Filter Topology Set Function Matrix
open scoped ENNReal NNReal

namespace DeGiorgi

variable {d : ℕ} [NeZero d]

local notation "E" => EuclideanSpace ℝ (Fin d)

/-! ## Weak-Derivative Uniqueness And Approximation Transfer -/

omit [NeZero d] in
private theorem HasWeakPartialDeriv.toStampacchia
    {Ω : Set E} {i : Fin d} {g f : E → ℝ}
    (h : HasWeakPartialDeriv i g f Ω) :
    HasWeakPartialDeriv' (d := d) i g f Ω := by
  simpa [HasWeakPartialDeriv, HasWeakPartialDeriv'] using h

omit [NeZero d] in
private theorem stampacchia_congr_ae
    {Ω : Set E} {i : Fin d} {g f f' : E → ℝ}
    (h : HasWeakPartialDeriv' (d := d) i g f Ω)
    (hff' : f =ᵐ[volume.restrict Ω] f') :
    HasWeakPartialDeriv' (d := d) i g f' Ω := by
  intro φ hφ hφ_cpt hφ_sub
  have hcongr :
      (fun x => f' x * (fderiv ℝ φ x) (EuclideanSpace.single i 1))
        =ᵐ[volume.restrict Ω]
      (fun x => f x * (fderiv ℝ φ x) (EuclideanSpace.single i 1)) := by
    filter_upwards [hff'] with x hx
    simp [hx]
  calc
    ∫ x in Ω, f' x * (fderiv ℝ φ x) (EuclideanSpace.single i 1) =
        ∫ x in Ω, f x * (fderiv ℝ φ x) (EuclideanSpace.single i 1) := by
          exact integral_congr_ae hcongr
    _ = -∫ x in Ω, g x * φ x := h φ hφ hφ_cpt hφ_sub

/-- Stampacchia's zero-set theorem for Sobolev witnesses: each weak-gradient
component vanishes a.e. on the zero set of the function. -/
theorem MemW1pWitness.weakGrad_ae_eq_zero_on_zeroSet
    {Ω : Set E} (hΩ : IsOpen Ω) {u : E → ℝ}
    (hw : MemW1pWitness 2 u Ω) :
    ∀ i : Fin d, ∀ᵐ x ∂(volume.restrict Ω), u x = 0 → hw.weakGrad x i = 0 := by
  intro i
  let uMk : E → ℝ := AEMeasurable.mk u hw.memLp.aemeasurable
  have hu_meas : Measurable uMk := hw.memLp.aemeasurable.measurable_mk
  have hu_ae : u =ᵐ[volume.restrict Ω] uMk := hw.memLp.aemeasurable.ae_eq_mk
  have hGMk :
      ∀ j : Fin d, HasWeakPartialDeriv' (d := d) j (fun x => hw.weakGrad x j) uMk Ω := by
    intro j
    exact stampacchia_congr_ae
      (HasWeakPartialDeriv.toStampacchia (hw.isWeakGrad j)) hu_ae
  have huMk_memW1p : MemW1p 2 uMk Ω := by
    refine ⟨hw.memLp.ae_eq hu_ae, ?_⟩
    intro j
    exact ⟨fun x => hw.weakGrad x j, hw.weakGrad_component_memLp j, by
      simpa [HasWeakPartialDeriv'] using hGMk j⟩
  have hzero_mk :
      ∀ᵐ x ∂(volume.restrict Ω), uMk x = 0 → hw.weakGrad x i = 0 :=
    DeGiorgi.weakGrad_ae_eq_zero_on_zeroSet hΩ huMk_memW1p hGMk i
      (hw.weakGrad_component_memLp i) hu_meas
  filter_upwards [hu_ae, hzero_mk] with x hx hzero hx_zero
  exact hzero (by simpa [hx] using hx_zero)

/-- Subtracting a constant preserves a `W^{1,2}` witness on finite-measure
domains. -/
noncomputable def MemW1pWitness.sub_const
    {Ω : Set E} [IsFiniteMeasure (volume.restrict Ω)]
    (hΩ : IsOpen Ω)
    {u : E → ℝ} (hw : MemW1pWitness 2 u Ω) (c : ℝ) :
    MemW1pWitness 2 (fun x => u x - c) Ω where
  memLp := hw.memLp.sub (memLp_const c)
  weakGrad := hw.weakGrad
  weakGrad_component_memLp := hw.weakGrad_component_memLp
  isWeakGrad := by
    intro i φ hφ hφ_supp hφ_sub
    let ei : EuclideanSpace ℝ (Fin d) := EuclideanSpace.single i (1 : ℝ)
    have hkey := hw.isWeakGrad i φ hφ hφ_supp hφ_sub
    have hconst :
        HasWeakPartialDeriv i (fun _ : E => (0 : ℝ)) (fun _ : E => c) Ω := by
      simpa [ei] using
        (HasWeakPartialDeriv.of_contDiff (Ω := Ω) (i := i)
          (f := fun _ : E => c) hΩ contDiff_const)
    have hconst_zero : ∫ x in Ω, c * (fderiv ℝ φ x) ei = 0 := by
      simpa using hconst φ hφ hφ_supp hφ_sub
    have hderiv_cont : Continuous (fun x => (fderiv ℝ φ x) ei) :=
      (hφ.continuous_fderiv (by simp : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0)).clm_apply
        continuous_const
    have hderiv_supp : HasCompactSupport (fun x => (fderiv ℝ φ x) ei) :=
      hφ_supp.fderiv_apply (𝕜 := ℝ) ei
    have hu_int : Integrable (fun x => u x * (fderiv ℝ φ x) ei) (volume.restrict Ω) := by
      have hu_loc : LocallyIntegrable u (volume.restrict Ω) :=
        hw.memLp.locallyIntegrable (by norm_num)
      simpa [smul_eq_mul] using
        hu_loc.integrable_smul_right_of_hasCompactSupport hderiv_cont hderiv_supp
    have hc_int : Integrable (fun x => c * (fderiv ℝ φ x) ei) (volume.restrict Ω) := by
      exact (hderiv_cont.integrable_of_hasCompactSupport hderiv_supp).const_mul c
    have hsub_fun :
        (fun x => (u x - c) * (fderiv ℝ φ x) ei) =
          (fun x => u x * (fderiv ℝ φ x) ei - c * (fderiv ℝ φ x) ei) := by
      ext x
      ring
    rw [hsub_fun, integral_sub hu_int hc_int, hkey, hconst_zero]
    simp

/-- Multiply a `W^{1,2}` witness by a bounded smooth scalar factor. -/
noncomputable def MemW1pWitness.mul_smooth_bounded
    {Ω : Set E} (hΩ : IsOpen Ω)
    {u η : E → ℝ} (hw : MemW1pWitness 2 u Ω)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    {C₀ C₁ : ℝ}
    (_hC₀ : 0 ≤ C₀) (_hC₁ : 0 ≤ C₁)
    (hη_bound : ∀ x, |η x| ≤ C₀)
    (hη_grad_bound : ∀ x, ‖fderiv ℝ η x‖ ≤ C₁) :
    MemW1pWitness 2 (fun x => η x * u x) Ω where
  memLp := by
    refine MemLp.of_le_mul (g := u) (c := C₀) hw.memLp ?_ ?_
    · exact hη.continuous.aestronglyMeasurable.mul hw.memLp.aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun x => by
        calc
          ‖η x * u x‖ = |η x| * ‖u x‖ := by
            rw [norm_mul, Real.norm_eq_abs]
          _ ≤ C₀ * ‖u x‖ := by
              gcongr
              exact hη_bound x
  weakGrad := fun x =>
    η x • hw.weakGrad x +
      (show E from WithLp.toLp 2 fun i => (fderiv ℝ η x) (EuclideanSpace.single i 1) * u x)
  weakGrad_component_memLp := by
    intro i
    have hfirst : MemLp (fun x => η x * hw.weakGrad x i) 2 (volume.restrict Ω) := by
      refine MemLp.of_le_mul (g := fun x => hw.weakGrad x i) (c := C₀)
        (hw.weakGrad_component_memLp i) ?_ ?_
      · exact hη.continuous.aestronglyMeasurable.mul
          (hw.weakGrad_component_memLp i).aestronglyMeasurable
      · exact Filter.Eventually.of_forall fun x => by
          calc
            ‖η x * hw.weakGrad x i‖ = |η x| * ‖hw.weakGrad x i‖ := by
              rw [norm_mul, Real.norm_eq_abs]
            _ ≤ C₀ * ‖hw.weakGrad x i‖ := by
                gcongr
                exact hη_bound x
    have hderiv_cont : Continuous (fun x => (fderiv ℝ η x) (EuclideanSpace.single i 1)) :=
      (hη.continuous_fderiv (by simp : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0)).clm_apply continuous_const
    have hsecond :
        MemLp (fun x => (fderiv ℝ η x) (EuclideanSpace.single i 1) * u x) 2
          (volume.restrict Ω) := by
      refine MemLp.of_le_mul (g := u) (c := C₁) hw.memLp ?_ ?_
      · exact hderiv_cont.aestronglyMeasurable.mul hw.memLp.aestronglyMeasurable
      · exact Filter.Eventually.of_forall fun x => by
          calc
            ‖(fderiv ℝ η x) (EuclideanSpace.single i 1) * u x‖
                = ‖(fderiv ℝ η x) (EuclideanSpace.single i 1)‖ * ‖u x‖ := by
                    rw [norm_mul]
            _ ≤ ‖fderiv ℝ η x‖ * ‖u x‖ := by
                  gcongr
                  simpa using (ContinuousLinearMap.le_opNorm (fderiv ℝ η x)
                    (EuclideanSpace.single i (1 : ℝ)))
            _ ≤ C₁ * ‖u x‖ := by
                  gcongr
                  exact hη_grad_bound x
    simpa using hfirst.add hsecond
  isWeakGrad := by
    intro i
    simpa using HasWeakPartialDeriv.mul_smooth hΩ
      (hf := hw.isWeakGrad i) hη
      (hw.memLp.locallyIntegrable (by norm_num))
      ((hw.weakGrad_component_memLp i).locallyIntegrable (by norm_num))

/-
A compactly supported `W₀^{1,2}` witness already contains the approximation
data needed by the positive-part closure arguments.
-/
omit [NeZero d] in
theorem smoothApproxData_of_memW01p
    {Ω : Set E} {u : E → ℝ}
    (hu : MemW01p 2 u Ω) :
    ∃ (hw : MemW1pWitness 2 u Ω) (φ : ℕ → E → ℝ),
      (∀ n, ContDiff ℝ (⊤ : ℕ∞) (φ n)) ∧
      (∀ n, HasCompactSupport (φ n)) ∧
      (∀ n, tsupport (φ n) ⊆ Ω) ∧
      Tendsto (fun n => eLpNorm (fun x => φ n x - u x) 2 (volume.restrict Ω))
        atTop (nhds 0) ∧
      ∀ i : Fin d,
        Tendsto (fun n => eLpNorm
          (fun x => (fderiv ℝ (φ n) x) (EuclideanSpace.single i 1) - hw.weakGrad x i)
          2 (volume.restrict Ω))
          atTop (nhds 0) := by
  simpa [MemW01p] using hu.2

omit [NeZero d] in
private lemma tendsto_integral_mul_of_eLpNorm_tendsto_zero
    {μ : Measure E} {f : E → ℝ} {g : ℕ → E → ℝ}
    (hf : MemLp f 2 μ)
    (hg : ∀ n, MemLp (g n) 2 μ)
    (hlim : Tendsto (fun n => eLpNorm (g n) 2 μ) atTop (nhds 0)) :
    Tendsto (fun n => ∫ x, f x * g n x ∂μ) atTop (nhds 0) := by
  have hpq : (2 : ℝ).HolderConjugate (2 : ℝ) := by
    exact Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩
  let C : ℝ := MeasureTheory.lpNorm f 2 μ
  have hlim' : Tendsto (fun n => MeasureTheory.lpNorm (g n) 2 μ) atTop (nhds 0) := by
    have hlim_toReal :
        Tendsto (fun n => (eLpNorm (g n) 2 μ).toReal) atTop (nhds 0) :=
      (ENNReal.tendsto_toReal_zero_iff (fun n => (hg n).eLpNorm_ne_top)).2 hlim
    have hEq :
        (fun n => (eLpNorm (g n) 2 μ).toReal) = (fun n => MeasureTheory.lpNorm (g n) 2 μ) := by
      funext n
      simpa using
        (MeasureTheory.toReal_eLpNorm
          (μ := μ) (p := (2 : ℝ≥0∞)) (f := g n) (hg n).aestronglyMeasurable)
    simpa [hEq] using hlim_toReal
  have hbound : ∀ n, |∫ x, f x * g n x ∂μ| ≤ C * MeasureTheory.lpNorm (g n) 2 μ := by
    intro n
    have h_int :
        |∫ x, f x * g n x ∂μ| ≤ ∫ x, ‖f x‖ * ‖g n x‖ ∂μ := by
      calc
        |∫ x, f x * g n x ∂μ| = ‖∫ x, f x * g n x ∂μ‖ := by rw [Real.norm_eq_abs]
        _ ≤ ∫ x, ‖f x * g n x‖ ∂μ := by
          simpa using norm_integral_le_integral_norm (μ := μ) (f := fun x => f x * g n x)
        _ = ∫ x, ‖f x‖ * ‖g n x‖ ∂μ := by simp_rw [norm_mul]
    have hf' : MemLp f (ENNReal.ofReal (2 : ℝ)) μ := by simpa using hf
    have hg' : MemLp (g n) (ENNReal.ofReal (2 : ℝ)) μ := by simpa using hg n
    have h_holder :=
      MeasureTheory.integral_mul_norm_le_Lp_mul_Lq
        (μ := μ) (f := f) (g := g n) (p := (2 : ℝ)) (q := (2 : ℝ)) hpq hf' hg'
    have h_f_lp :
        MeasureTheory.lpNorm f 2 μ = (∫ x, ‖f x‖ ^ (2 : ℝ) ∂μ) ^ ((2 : ℝ)⁻¹) := by
      simpa using
        (MeasureTheory.lpNorm_eq_integral_norm_rpow_toReal
          (μ := μ) (p := (2 : ℝ≥0∞)) (f := f) (by norm_num) (by simp)
          hf.aestronglyMeasurable)
    have h_g_lp :
        MeasureTheory.lpNorm (g n) 2 μ = (∫ x, ‖g n x‖ ^ (2 : ℝ) ∂μ) ^ ((2 : ℝ)⁻¹) := by
      simpa using
        (MeasureTheory.lpNorm_eq_integral_norm_rpow_toReal
          (μ := μ) (p := (2 : ℝ≥0∞)) (f := g n) (by norm_num) (by simp)
          (hg n).aestronglyMeasurable)
    calc
      |∫ x, f x * g n x ∂μ| ≤ ∫ x, ‖f x‖ * ‖g n x‖ ∂μ := h_int
      _ ≤ C * MeasureTheory.lpNorm (g n) 2 μ := by
        simpa [C, h_f_lp, h_g_lp, mul_comm, mul_left_comm, mul_assoc] using h_holder
  have h_upper : Tendsto (fun n => C * MeasureTheory.lpNorm (g n) 2 μ) atTop (nhds 0) := by
    simpa using Tendsto.const_mul C hlim'
  have h_abs : Tendsto (fun n => |∫ x, f x * g n x ∂μ|) atTop (nhds 0) :=
    squeeze_zero (fun n => abs_nonneg _) hbound h_upper
  exact (tendsto_zero_iff_abs_tendsto_zero _).2 h_abs

/-
Transfer weak derivatives from smooth compact-support approximants to the limit
function.
-/
omit [NeZero d] in
theorem HasWeakPartialDeriv.of_eLpNormApprox
    {Ω : Set E} (_hΩ : IsOpen Ω)
    {i : Fin d} {f g : E → ℝ} {ψ : ℕ → E → ℝ} {gψ : ℕ → E → ℝ}
    (hf_memLp : MemLp f 2 (volume.restrict Ω))
    (hg_memLp : MemLp g 2 (volume.restrict Ω))
    (hψ_wd : ∀ n, HasWeakPartialDeriv i (gψ n) (ψ n) Ω)
    (hψ_fun_memLp : ∀ n, MemLp (fun x => ψ n x - f x) 2 (volume.restrict Ω))
    (hψ_fun :
      Tendsto (fun n => eLpNorm (fun x => ψ n x - f x) 2 (volume.restrict Ω))
        atTop (nhds 0))
    (hψ_grad_memLp : ∀ n, MemLp (fun x => gψ n x - g x) 2 (volume.restrict Ω))
    (hψ_grad :
      Tendsto (fun n => eLpNorm (fun x => gψ n x - g x) 2 (volume.restrict Ω))
        atTop (nhds 0)) :
    HasWeakPartialDeriv i g f Ω := by
  intro φ hφ hφ_supp hφ_sub
  let μ : Measure E := volume.restrict Ω
  let dφ : E → ℝ := fun x => (fderiv ℝ φ x) (EuclideanSpace.single i 1)
  have hdφ_memLp : MemLp dφ 2 μ := by
    have hcont : Continuous dφ := by
      simpa [dφ] using
        ((hφ.continuous_fderiv (by simp : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0)).clm_apply
          continuous_const)
    have hcpt : HasCompactSupport dφ := by
      simpa [dφ] using hφ_supp.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single i 1)
    exact (hcont.memLp_of_hasCompactSupport hcpt).restrict _
  have hφ_memLp : MemLp φ 2 μ :=
    (hφ.continuous.memLp_of_hasCompactSupport hφ_supp).restrict _
  have h_fun_int :
      Tendsto (fun n => ∫ x, dφ x * (ψ n x - f x) ∂μ) atTop (nhds 0) :=
    tendsto_integral_mul_of_eLpNorm_tendsto_zero hdφ_memLp hψ_fun_memLp hψ_fun
  have h_grad_int :
      Tendsto (fun n => ∫ x, φ x * (gψ n x - g x) ∂μ) atTop (nhds 0) :=
    tendsto_integral_mul_of_eLpNorm_tendsto_zero hφ_memLp hψ_grad_memLp hψ_grad
  have h_lhs_tendsto :
      Tendsto (fun n => ∫ x in Ω, ψ n x * dφ x)
        atTop (nhds (∫ x in Ω, f x * dφ x)) := by
    have h_eq :
        ∀ n,
          ∫ x, ψ n x * dφ x ∂μ =
            (∫ x, f x * dφ x ∂μ) + ∫ x, dφ x * (ψ n x - f x) ∂μ := by
      intro n
      have hfi : Integrable (fun x => f x * dφ x) μ := hf_memLp.integrable_mul hdφ_memLp
      have hdi : Integrable (fun x => dφ x * (ψ n x - f x)) μ :=
        hdφ_memLp.integrable_mul (hψ_fun_memLp n)
      calc
        ∫ x, ψ n x * dφ x ∂μ
            = ∫ x, (f x * dφ x) + dφ x * (ψ n x - f x) ∂μ := by
                congr with x
                ring
        _ = (∫ x, f x * dφ x ∂μ) + ∫ x, dφ x * (ψ n x - f x) ∂μ :=
              integral_add hfi hdi
    have h_aux :
        Tendsto
          (fun n => (∫ x, f x * dφ x ∂μ) + ∫ x, dφ x * (ψ n x - f x) ∂μ)
          atTop (nhds ((∫ x, f x * dφ x ∂μ) + 0)) :=
      Tendsto.const_add _ h_fun_int
    simpa [μ, h_eq, add_comm, add_left_comm, add_assoc] using h_aux
  have h_rhs_tendsto :
      Tendsto (fun n => -∫ x in Ω, gψ n x * φ x)
        atTop (nhds (-∫ x in Ω, g x * φ x)) := by
    have h_eq :
        ∀ n,
          -(∫ x, gψ n x * φ x ∂μ) =
            -(∫ x, g x * φ x ∂μ) - ∫ x, φ x * (gψ n x - g x) ∂μ := by
      intro n
      have hgi : Integrable (fun x => g x * φ x) μ := hg_memLp.integrable_mul hφ_memLp
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
      ∀ n, ∫ x in Ω, ψ n x * dφ x = -∫ x in Ω, gψ n x * φ x := by
    intro n
    exact hψ_wd n φ hφ hφ_supp hφ_sub
  have h_eq_tendsto :
      Tendsto (fun n => ∫ x in Ω, ψ n x * dφ x)
        atTop (nhds (-∫ x in Ω, g x * φ x)) := by
    simpa [h_eq_n] using h_rhs_tendsto
  exact tendsto_nhds_unique h_lhs_tendsto h_eq_tendsto

/-! ## Indicator-Difference Convergence -/

theorem exists_subseq_tendsto_ae_of_tendsto_eLpNorm
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ} {ψ : ℕ → α → ℝ}
    (hψ_aemeas : ∀ n, AEStronglyMeasurable (ψ n) μ)
    (hf_aemeas : AEStronglyMeasurable f μ)
    (hψ :
      Tendsto (fun n => eLpNorm (fun x => ψ n x - f x) 2 μ) atTop (nhds 0)) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧
      ∀ᵐ x ∂μ, Tendsto (fun n => ψ (ns n) x) atTop (nhds (f x)) := by
  have htim : TendstoInMeasure μ ψ atTop f := by
    exact MeasureTheory.tendstoInMeasure_of_tendsto_eLpNorm
      (by norm_num : (2 : ℝ≥0∞) ≠ 0) hψ_aemeas hf_aemeas hψ
  exact htim.exists_seq_tendsto_ae

private lemma indicator_diff_mul_le_abs {a c d : ℝ} :
    |(if 0 < a then d else 0) - (if 0 < c then d else 0)| ≤ |d| := by
  by_cases ha : 0 < a <;> by_cases hc : 0 < c <;> simp [ha, hc]

private lemma tendsto_indicator_diff_mul_zero_of_tendsto
    {a : ℕ → ℝ} {u g : ℝ}
    (ha : Tendsto a atTop (nhds u)) (hg0 : u = 0 → g = 0) :
    Tendsto (fun n => (if 0 < a n then g else 0) - (if 0 < u then g else 0))
      atTop (nhds 0) := by
  by_cases hu0 : u = 0
  · have hg : g = 0 := hg0 hu0
    simp [hu0, hg]
  by_cases hu : 0 < u
  ·
    have hpos : ∀ᶠ n in atTop, 0 < a n := by
      have hnhds : {y : ℝ | u / 2 < y} ∈ 𝓝 u := Ioi_mem_nhds (by linarith)
      filter_upwards [ha hnhds] with n hn
      have hu_half : 0 < u / 2 := by linarith
      exact lt_trans hu_half hn
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hpos] with n hn
    simp [hn, hu]
  ·
    have hu_neg : u < 0 := by
      exact lt_of_le_of_ne (le_of_not_gt hu) (by simpa using hu0)
    have hneg : ∀ᶠ n in atTop, a n < u / 2 := by
      have hnhds : {y : ℝ | y < u / 2} ∈ 𝓝 u := Iio_mem_nhds (by linarith)
      filter_upwards [ha hnhds] with n hn
      exact hn
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hneg] with n hn
    have hna : ¬ 0 < a n := by linarith
    simp [hna, hu]

/-
Indicator-convergence theorem for the positive-part chain rule.
-/
omit [NeZero d] in
theorem tendsto_eLpNorm_indicator_diff_mul_of_tendsto_eLpNorm
    {μ : Measure E} {u G : E → ℝ} {ψ : ℕ → E → ℝ}
    (hψ_aestrong : ∀ n, AEStronglyMeasurable (ψ n) μ)
    (hu_aestrong : AEStronglyMeasurable u μ)
    (hG_memLp : MemLp G 2 μ)
    (hzero : ∀ᵐ x ∂μ, u x = 0 → G x = 0)
    (hψ :
      Tendsto (fun n => eLpNorm (fun x => ψ n x - u x) 2 μ) atTop (nhds 0)) :
    Tendsto (fun n => eLpNorm (fun x =>
      (if 0 < ψ n x then G x else 0) -
        (if 0 < u x then G x else 0))
      2 μ) atTop (nhds 0) := by
  let F : ℕ → E → ℝ := fun n x =>
    (if 0 < ψ n x then G x else 0) - (if 0 < u x then G x else 0)
  have hF_meas : ∀ n, AEStronglyMeasurable (F n) μ := by
    intro n
    have hψ_pos : NullMeasurableSet {x | 0 < ψ n x} μ := by
      exact AEStronglyMeasurable.nullMeasurableSet_lt
        (μ := μ) stronglyMeasurable_const.aestronglyMeasurable (hψ_aestrong n)
    have hu_pos : NullMeasurableSet {x | 0 < u x} μ := by
      exact AEStronglyMeasurable.nullMeasurableSet_lt
        (μ := μ) stronglyMeasurable_const.aestronglyMeasurable hu_aestrong
    simpa [F] using
      ((hG_memLp.aestronglyMeasurable.indicator₀ hψ_pos).sub
        (hG_memLp.aestronglyMeasurable.indicator₀ hu_pos))
  have hF_dom : ∀ n x, ‖F n x‖ ≤ ‖G x‖ := by
    intro n x
    exact indicator_diff_mul_le_abs (a := ψ n x) (c := u x) (d := G x)
  have huiG : UnifIntegrable (fun _ : ℕ => G) 2 μ := by
    exact MeasureTheory.unifIntegrable_const (p := (2 : ℝ≥0∞))
      (by norm_num) (by simp) hG_memLp
  have huiF : UnifIntegrable F 2 μ := by
    intro ε hε
    obtain ⟨δ, hδ, hδ'⟩ := huiG hε
    refine ⟨δ, hδ, fun n s hs hμs => ?_⟩
    calc
      eLpNorm (s.indicator (F n)) 2 μ ≤ eLpNorm (s.indicator G) 2 μ := by
        refine eLpNorm_mono ?_
        intro x
        by_cases hx : x ∈ s
        · simp [Set.indicator_of_mem, hx]
          exact hF_dom n x
        · simp [Set.indicator_of_notMem, hx]
      _ ≤ ENNReal.ofReal ε := hδ' 0 s hs hμs
  have hutG : UnifTight (fun _ : ℕ => G) 2 μ := by
    exact MeasureTheory.unifTight_const (p := (2 : ℝ≥0∞)) (by simp) hG_memLp
  have hutF : UnifTight F 2 μ := by
    intro ε hε
    obtain ⟨s, hμs, hs'⟩ := hutG hε
    refine ⟨s, hμs, fun n => ?_⟩
    calc
      eLpNorm (sᶜ.indicator (F n)) 2 μ ≤ eLpNorm (sᶜ.indicator G) 2 μ := by
        refine eLpNorm_mono ?_
        intro x
        by_cases hx : x ∈ sᶜ
        · simp [Set.indicator_of_mem, hx]
          exact hF_dom n x
        · simp [Set.indicator_of_notMem, hx]
      _ ≤ ε := hs' 0
  refine tendsto_of_subseq_tendsto ?_
  intro ns hns
  obtain ⟨ms, -, hms_ae⟩ :=
    exists_subseq_tendsto_ae_of_tendsto_eLpNorm
      (μ := μ) (f := u) (ψ := fun n => ψ (ns n))
      (fun n => hψ_aestrong (ns n)) hu_aestrong (hψ.comp hns)
  have hui_subseq : UnifIntegrable (fun n => F (ns (ms n))) 2 μ := by
    intro ε hε
    obtain ⟨δ, hδ, hδ'⟩ := huiF hε
    exact ⟨δ, hδ, fun n s hs hμs => hδ' (ns (ms n)) s hs hμs⟩
  have hut_subseq : UnifTight (fun n => F (ns (ms n))) 2 μ := by
    intro ε hε
    obtain ⟨s, hμs, hs'⟩ := hutF hε
    exact ⟨s, hμs, fun n => hs' (ns (ms n))⟩
  have hF_ae :
      ∀ᵐ x ∂μ, Tendsto (fun n => F (ns (ms n)) x) atTop (nhds 0) := by
    filter_upwards [hzero, hms_ae] with x hxzero hxt
    simpa [F] using
      tendsto_indicator_diff_mul_zero_of_tendsto
        (a := fun n => ψ (ns (ms n)) x) (u := u x) (g := G x) hxt hxzero
  refine ⟨ms, ?_⟩
  have hLpF :
      Tendsto (fun n => eLpNorm (F (ns (ms n))) 2 μ) atTop (nhds 0) := by
    have hLpF0 :
        Tendsto (fun n => eLpNorm (F (ns (ms n)) - fun _ => (0 : ℝ)) 2 μ) atTop (nhds 0) := by
      exact
        (MeasureTheory.tendsto_Lp_of_tendsto_ae (μ := μ) (p := (2 : ℝ≥0∞))
          (hp := by norm_num) (hp' := by simp)
          (haef := fun n => hF_meas (ns (ms n)))
          (hg' := (MeasureTheory.MemLp.zero' (p := (2 : ℝ≥0∞)) (μ := μ)))
          hui_subseq hut_subseq hF_ae)
    have hEq0 :
        (fun n => eLpNorm (F (ns (ms n)) - fun _ => (0 : ℝ)) 2 μ) =
          (fun n => eLpNorm (F (ns (ms n))) 2 μ) := by
      funext n
      congr 1
      ext x
      simp
    rw [hEq0] at hLpF0
    exact hLpF0
  simpa [F] using hLpF

/-! ## Positive-Part Chain Rule -/

omit [NeZero d] in
private lemma support_positivePart_subset_support (f : E → ℝ) :
    Function.support (fun x => max (f x) 0) ⊆ Function.support f := by
  intro x hx
  by_contra hfx
  have hfx0 : f x = 0 := by
    simpa [Function.support] using hfx
  have : max (f x) 0 = 0 := by
    simp [hfx0]
  exact hx this

omit [NeZero d] in
private lemma hasCompactSupport_positivePart {f : E → ℝ}
    (hf : HasCompactSupport f) :
    HasCompactSupport (fun x => max (f x) 0) :=
  hf.mono (support_positivePart_subset_support f)

omit [NeZero d] in
private lemma lineDeriv_positivePart_eq_of_contDiff
    {f : E → ℝ} (hf : ContDiff ℝ 1 f) (x v : E) :
    lineDeriv ℝ (fun y => max (f y) 0) x v =
      if 0 < f x then fderiv ℝ f x v else 0 := by
  have hfdiff : Differentiable ℝ f := hf.differentiable one_ne_zero
  by_cases hx : 0 < f x
  ·
    have hEq : (fun y => max (f y) 0) =ᶠ[𝓝 x] f := by
      have hpos : ∀ᶠ y in nhds x, 0 < f y :=
        (isOpen_lt continuous_const hf.continuous).mem_nhds hx
      filter_upwards [hpos] with y hy
      simp [max_eq_left hy.le]
    rw [hEq.lineDeriv_eq]
    simpa [hx] using (hfdiff x).lineDeriv_eq_fderiv (v := v)
  ·
    have hx_nonpos : f x ≤ 0 := le_of_not_gt hx
    by_cases hx_zero : f x = 0
    ·
      have hmin : IsLocalMin (fun y => max (f y) 0) x := by
        change ∀ᶠ y in nhds x, max (f x) 0 ≤ max (f y) 0
        filter_upwards [] with y
        simp [hx_zero]
      have hzero : lineDeriv ℝ (fun y => max (f y) 0) x v = 0 := by
        simpa using congrFun hmin.lineDeriv_eq_zero v
      simp [hx, hzero]
    ·
      have hx_neg : f x < 0 := lt_of_le_of_ne hx_nonpos hx_zero
      have hEq : (fun y => max (f y) 0) =ᶠ[nhds x] fun _ => (0 : ℝ) := by
        have hneg : ∀ᶠ y in nhds x, f y < 0 :=
          (isOpen_lt hf.continuous continuous_const).mem_nhds hx_neg
        filter_upwards [hneg] with y hy
        simp [max_eq_right hy.le]
      rw [hEq.lineDeriv_eq]
      have hconst : lineDeriv ℝ (fun _ : E => (0 : ℝ)) x v = 0 := by
        simpa using ((hasFDerivAt_const (0 : ℝ) x).hasLineDerivAt v).lineDeriv
      simp [hx, hconst]

omit [NeZero d] in
private theorem weakPartialDeriv_positivePart_of_contDiff
    {Ω : Set E} {i : Fin d} {f : E → ℝ}
    (hf : ContDiff ℝ 1 f) (hf_supp : HasCompactSupport f) :
    HasWeakPartialDeriv i
      (fun x => if 0 < f x then fderiv ℝ f x (EuclideanSpace.single i 1) else 0)
      (fun x => max (f x) 0) Ω := by
  intro φ hφ hφ_supp hφ_sub
  obtain ⟨Cf, hLip_f⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hf_supp hf one_ne_zero
  obtain ⟨Cφ, hLip_φ⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hφ_supp hφ (by simp)
  have hLip_pos : LipschitzWith Cf (fun y => max (f y) 0) := by
    simpa [Function.comp] using (MeasureTheory.Lp.lipschitzWith_pos_part.comp hLip_f)
  let ei : E := EuclideanSpace.single i (1 : ℝ)
  have hLineDeriv_f :
      ∀ x, lineDeriv ℝ (fun y => max (f y) 0) x ei =
        if 0 < f x then fderiv ℝ f x ei else 0 :=
    fun x => lineDeriv_positivePart_eq_of_contDiff hf x ei
  have hLineDeriv_φ :
      ∀ x, lineDeriv ℝ φ x (-ei) = -fderiv ℝ φ x ei := by
    intro x
    rw [(hφ.differentiable (by simp) x).lineDeriv_eq_fderiv]
    simp [ei]
  have hDeriv_φ_sub : tsupport (fun x => fderiv ℝ φ x ei) ⊆ Ω :=
    (tsupport_fderiv_apply_subset ℝ ei).trans hφ_sub
  have hIBP :=
    LipschitzWith.integral_lineDeriv_mul_eq
      (μ := volume) hLip_pos hLip_φ hφ_supp ei
  simp_rw [hLineDeriv_f, hLineDeriv_φ] at hIBP
  have hLHS_zero :
      ∀ x, x ∉ Ω →
        (if 0 < f x then fderiv ℝ f x ei else 0) * φ x = 0 := by
    intro x hx
    have hφx : φ x = 0 := by
      by_contra hφx
      exact hx (hφ_sub (subset_tsupport _ hφx))
    simp [hφx]
  have hRHS_zero :
      ∀ x, x ∉ Ω → (-fderiv ℝ φ x ei) * max (f x) 0 = 0 := by
    intro x hx
    have hderivx : fderiv ℝ φ x ei = 0 := by
      by_contra hderivx
      exact hx (hDeriv_φ_sub (subset_tsupport _ hderivx))
    rw [hderivx, neg_zero, zero_mul]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hLHS_zero,
      ← setIntegral_eq_integral_of_forall_compl_eq_zero hRHS_zero] at hIBP
  have hIBP' :
      ∫ x in Ω, (if 0 < f x then fderiv ℝ f x ei else 0) * φ x =
        -∫ x in Ω, max (f x) 0 * fderiv ℝ φ x ei := by
    rw [show (∫ x in Ω, -fderiv ℝ φ x ei * max (f x) 0) =
        -∫ x in Ω, max (f x) 0 * fderiv ℝ φ x ei by
        simp_rw [neg_mul, mul_comm]
        rw [integral_neg]] at hIBP
    exact hIBP
  have hneg := congrArg Neg.neg hIBP'
  simpa [neg_neg, ei] using hneg.symm

omit [NeZero d] in
private lemma positivePart_sub_abs_le {f g : E → ℝ} (x : E) :
    |max (f x) 0 - max (g x) 0| ≤ |f x - g x| := by
  have h := MeasureTheory.Lp.lipschitzWith_pos_part.dist_le_mul (f x) (g x)
  simpa [dist_eq_norm, Real.norm_eq_abs, mul_comm] using h

omit [NeZero d] in
private theorem eLpNorm_positivePart_sub_le
    {f g : E → ℝ} {μ : Measure E} :
    eLpNorm (fun x => max (f x) 0 - max (g x) 0) 2 μ ≤
      eLpNorm (fun x => f x - g x) 2 μ := by
  exact eLpNorm_mono_ae (Eventually.of_forall (positivePart_sub_abs_le (f := f) (g := g)))

omit [NeZero d] in
private theorem tendsto_eLpNorm_positivePart_sub
    {f : E → ℝ} {g : ℕ → E → ℝ} {μ : Measure E}
    (h :
      Tendsto (fun n => eLpNorm (fun x => g n x - f x) 2 μ) atTop (nhds 0)) :
    Tendsto (fun n => eLpNorm (fun x => max (g n x) 0 - max (f x) 0) 2 μ)
      atTop (nhds 0) := by
  have hbound :
      ∀ n, eLpNorm (fun x => max (g n x) 0 - max (f x) 0) 2 μ ≤
        eLpNorm (fun x => g n x - f x) 2 μ := by
    intro n
    exact eLpNorm_positivePart_sub_le (f := fun x => g n x) (g := fun x => f x)
  have hnonneg :
      ∀ n, 0 ≤ eLpNorm (fun x => max (g n x) 0 - max (f x) 0) 2 μ := by
    intro n
    positivity
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h hnonneg hbound

/-- Auxiliary positive-part witness constructor: this is the transportable core
assuming the zero-set vanishing input and the smooth approximation data are
already available. -/
noncomputable def MemW1pWitness.posPart_of_aux
    {Ω : Set E} [IsFiniteMeasure (volume.restrict Ω)]
    (hΩ : IsOpen Ω) {u : E → ℝ}
    (hw : MemW1pWitness 2 u Ω)
    (hzero :
      ∀ i : Fin d, ∀ᵐ x ∂(volume.restrict Ω), u x = 0 → hw.weakGrad x i = 0)
    (happrox :
      ∃ ψ : ℕ → E → ℝ,
        (∀ n, ContDiff ℝ 1 (ψ n)) ∧
        (∀ n, HasCompactSupport (ψ n)) ∧
        Tendsto (fun n => eLpNorm (fun x => ψ n x - u x) 2 (volume.restrict Ω))
          atTop (nhds 0) ∧
        (∀ i : Fin d,
          Tendsto (fun n => eLpNorm (fun x =>
            (fderiv ℝ (ψ n) x) (EuclideanSpace.single i 1) - hw.weakGrad x i)
            2 (volume.restrict Ω))
          atTop (nhds 0))) :
    MemW1pWitness 2 (fun x => max (u x) 0) Ω := by
  let ψ : ℕ → E → ℝ := Classical.choose happrox
  have hψspec := Classical.choose_spec happrox
  have hψ_smooth : ∀ n, ContDiff ℝ 1 (ψ n) := hψspec.1
  have hψspec' := hψspec.2
  have hψ_cpt : ∀ n, HasCompactSupport (ψ n) := hψspec'.1
  have hψspec'' := hψspec'.2
  have hψ_func :
      Tendsto (fun n => eLpNorm (fun x => ψ n x - u x) 2 (volume.restrict Ω))
        atTop (nhds 0) := hψspec''.1
  have hψ_grad :
      ∀ i : Fin d,
        Tendsto (fun n => eLpNorm (fun x =>
          (fderiv ℝ (ψ n) x) (EuclideanSpace.single i 1) - hw.weakGrad x i)
          2 (volume.restrict Ω))
        atTop (nhds 0) := hψspec''.2
  refine
    { memLp := by
        simpa using hw.memLp.pos_part
      weakGrad := fun x => if 0 < u x then hw.weakGrad x else 0
      weakGrad_component_memLp := ?_
      isWeakGrad := ?_ }
  ·
    intro i
    simpa using posPartGrad_component_memLp hw i
  ·
    intro i
    let μ : Measure E := volume.restrict Ω
    let g : E → ℝ := fun x => if 0 < u x then hw.weakGrad x i else 0
    let gψ : ℕ → E → ℝ := fun n x =>
      if 0 < ψ n x then (fderiv ℝ (ψ n) x) (EuclideanSpace.single i 1) else 0
    have hg_memLp : MemLp g 2 μ := by
      exact indicator_component_memLp hw.memLp.aemeasurable (hw.weakGrad_component_memLp i)
    have hψ_wd : ∀ n, HasWeakPartialDeriv i (gψ n) (fun x => max (ψ n x) 0) Ω := by
      intro n
      simpa [gψ] using
        weakPartialDeriv_positivePart_of_contDiff (Ω := Ω) (i := i) (hψ_smooth n) (hψ_cpt n)
    have hψ_fun_memLp : ∀ n, MemLp (fun x => max (ψ n x) 0 - max (u x) 0) 2 μ := by
      intro n
      have hfirst : MemLp (fun x => max (ψ n x) 0) 2 μ := by
        exact (((hψ_smooth n).continuous.max continuous_const).memLp_of_hasCompactSupport
          (hasCompactSupport_positivePart (hψ_cpt n))).restrict Ω
      exact hfirst.sub (by simpa using hw.memLp.pos_part)
    have hψ_fun :
        Tendsto (fun n => eLpNorm (fun x => max (ψ n x) 0 - max (u x) 0) 2 μ)
          atTop (nhds 0) :=
      tendsto_eLpNorm_positivePart_sub hψ_func
    have hψ_grad_memLp : ∀ n, MemLp (fun x => gψ n x - g x) 2 μ := by
      intro n
      have hderiv_cont : Continuous
          (fun x => (fderiv ℝ (ψ n) x) (EuclideanSpace.single i 1)) :=
        ((hψ_smooth n).fderiv_right (m := 0) (by norm_cast)).continuous.clm_apply
          continuous_const
      have hderiv_cpt : HasCompactSupport
          (fun x => (fderiv ℝ (ψ n) x) (EuclideanSpace.single i 1)) :=
        (hψ_cpt n).fderiv_apply (𝕜 := ℝ) _
      have hderiv_memLp : MemLp
          (fun x => (fderiv ℝ (ψ n) x) (EuclideanSpace.single i 1)) 2 μ :=
        (hderiv_cont.memLp_of_hasCompactSupport hderiv_cpt).restrict Ω
      have hfirst_raw : MemLp
          (fun x => (fderiv ℝ (ψ n) x) (EuclideanSpace.single i 1) - hw.weakGrad x i) 2 μ :=
        hderiv_memLp.sub (hw.weakGrad_component_memLp i)
      have hψ_meas : AEMeasurable (ψ n) μ :=
        ((hψ_smooth n).continuous.aemeasurable.restrict)
      have hfirst : MemLp
          (fun x => if 0 < ψ n x then
            (fderiv ℝ (ψ n) x) (EuclideanSpace.single i 1) - hw.weakGrad x i else 0)
          2 μ := indicator_component_memLp hψ_meas hfirst_raw
      have hsecond : MemLp
          (fun x => (if 0 < ψ n x then hw.weakGrad x i else 0) - g x) 2 μ := by
        have hleft : MemLp (fun x => if 0 < ψ n x then hw.weakGrad x i else 0) 2 μ :=
          indicator_component_memLp hψ_meas (hw.weakGrad_component_memLp i)
        exact hleft.sub hg_memLp
      have hEq :
          (fun x => gψ n x - g x) =
            (fun x =>
              (if 0 < ψ n x then
                (fderiv ℝ (ψ n) x) (EuclideanSpace.single i 1) - hw.weakGrad x i else 0) +
                ((if 0 < ψ n x then hw.weakGrad x i else 0) - g x)) := by
        funext x
        by_cases hxψ : 0 < ψ n x <;> by_cases hxu : 0 < u x <;> simp [gψ, g, hxψ, hxu]
      have hsum : MemLp
          (fun x =>
            (if 0 < ψ n x then
              (fderiv ℝ (ψ n) x) (EuclideanSpace.single i 1) - hw.weakGrad x i else 0) +
              ((if 0 < ψ n x then hw.weakGrad x i else 0) - g x))
          2 μ := ⟨hfirst.aestronglyMeasurable.add hsecond.aestronglyMeasurable,
            eLpNorm_add_lt_top hfirst hsecond⟩
      simpa [hEq] using hsum
    have hψ_grad_tendsto :
        Tendsto (fun n => eLpNorm (fun x => gψ n x - g x) 2 μ) atTop (nhds 0) := by
      have hfirst :
          Tendsto
            (fun n => eLpNorm
              (fun x => if 0 < ψ n x then
                (fderiv ℝ (ψ n) x) (EuclideanSpace.single i 1) - hw.weakGrad x i else 0)
              2 μ) atTop (nhds 0) := by
        have hbound :
            ∀ n,
              eLpNorm
                (fun x => if 0 < ψ n x then
                  (fderiv ℝ (ψ n) x) (EuclideanSpace.single i 1) - hw.weakGrad x i else 0)
                2 μ
              ≤ eLpNorm
                  (fun x => (fderiv ℝ (ψ n) x) (EuclideanSpace.single i 1) - hw.weakGrad x i)
                  2 μ := by
          intro n
          refine eLpNorm_mono ?_
          intro x
          by_cases hx : 0 < ψ n x <;> simp [hx]
        have hnonneg :
            ∀ n,
              0 ≤ eLpNorm
                (fun x => if 0 < ψ n x then
                  (fderiv ℝ (ψ n) x) (EuclideanSpace.single i 1) - hw.weakGrad x i else 0)
                2 μ := by
          intro n
          positivity
        exact tendsto_of_tendsto_of_tendsto_of_le_of_le
          tendsto_const_nhds (hψ_grad i) hnonneg hbound
      have hsecond :
          Tendsto
            (fun n => eLpNorm
              (fun x => (if 0 < ψ n x then hw.weakGrad x i else 0) - g x)
              2 μ) atTop (nhds 0) := by
        simpa [g] using
          tendsto_eLpNorm_indicator_diff_mul_of_tendsto_eLpNorm
            (μ := μ) (u := u) (G := fun x => hw.weakGrad x i) (ψ := ψ)
            (hψ_aestrong := fun n => (hψ_smooth n).continuous.aestronglyMeasurable.restrict)
            (hu_aestrong := hw.memLp.aestronglyMeasurable)
            (hG_memLp := hw.weakGrad_component_memLp i)
            (hzero := hzero i)
            (hψ := hψ_func)
      have hbound :
          ∀ n, eLpNorm (fun x => gψ n x - g x) 2 μ ≤
            eLpNorm
              (fun x => if 0 < ψ n x then
                (fderiv ℝ (ψ n) x) (EuclideanSpace.single i 1) - hw.weakGrad x i else 0)
              2 μ
            +
            eLpNorm
              (fun x => (if 0 < ψ n x then hw.weakGrad x i else 0) - g x)
              2 μ := by
        intro n
        have hψ_meas : AEMeasurable (ψ n) μ :=
          ((hψ_smooth n).continuous.aemeasurable.restrict)
        have hderiv_cont : Continuous
            (fun x => (fderiv ℝ (ψ n) x) (EuclideanSpace.single i 1)) :=
          ((hψ_smooth n).fderiv_right (m := 0) (by norm_cast)).continuous.clm_apply
            continuous_const
        have hderiv_cpt : HasCompactSupport
            (fun x => (fderiv ℝ (ψ n) x) (EuclideanSpace.single i 1)) :=
          (hψ_cpt n).fderiv_apply (𝕜 := ℝ) _
        have hderiv_memLp : MemLp
            (fun x => (fderiv ℝ (ψ n) x) (EuclideanSpace.single i 1)) 2 μ :=
          (hderiv_cont.memLp_of_hasCompactSupport hderiv_cpt).restrict Ω
        have hfirst_raw : MemLp
            (fun x => (fderiv ℝ (ψ n) x) (EuclideanSpace.single i 1) - hw.weakGrad x i) 2 μ :=
          hderiv_memLp.sub (hw.weakGrad_component_memLp i)
        have hfirst_mem : MemLp
            (fun x => if 0 < ψ n x then
              (fderiv ℝ (ψ n) x) (EuclideanSpace.single i 1) - hw.weakGrad x i else 0)
            2 μ := indicator_component_memLp hψ_meas hfirst_raw
        have hsecond_mem : MemLp
            (fun x => (if 0 < ψ n x then hw.weakGrad x i else 0) - g x)
            2 μ := by
          exact (indicator_component_memLp hψ_meas (hw.weakGrad_component_memLp i)).sub hg_memLp
        have hEq :
            (fun x => gψ n x - g x) =
              (fun x =>
                (if 0 < ψ n x then
                  (fderiv ℝ (ψ n) x) (EuclideanSpace.single i 1) - hw.weakGrad x i else 0) +
                  ((if 0 < ψ n x then hw.weakGrad x i else 0) - g x)) := by
          funext x
          by_cases hxψ : 0 < ψ n x <;> by_cases hxu : 0 < u x <;> simp [gψ, g, hxψ, hxu]
        rw [hEq]
        exact eLpNorm_add_le
          hfirst_mem.aestronglyMeasurable
          hsecond_mem.aestronglyMeasurable
          (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      have hnonneg : ∀ n, 0 ≤ eLpNorm (fun x => gψ n x - g x) 2 μ := by
        intro n
        positivity
      have hupper :
          Tendsto
            (fun n =>
              eLpNorm
                (fun x => if 0 < ψ n x then
                  (fderiv ℝ (ψ n) x) (EuclideanSpace.single i 1) - hw.weakGrad x i else 0)
                2 μ
              +
              eLpNorm
                (fun x => (if 0 < ψ n x then hw.weakGrad x i else 0) - g x)
                2 μ)
            atTop (nhds 0) := by
        simpa using hfirst.add hsecond
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper hnonneg hbound
    have hg_eq :
        (fun x => ((if 0 < u x then hw.weakGrad x else 0 : E) i)) = g := by
      funext x
      by_cases hx : 0 < u x <;> simp [g, hx]
    rw [hg_eq]
    exact
      HasWeakPartialDeriv.of_eLpNormApprox (d := d) hΩ
        (i := i) (f := fun x => max (u x) 0) (g := g)
        (ψ := fun n x => max (ψ n x) 0) (gψ := gψ)
        (by simpa using hw.memLp.pos_part)
        hg_memLp
        hψ_wd
        hψ_fun_memLp
        hψ_fun
        hψ_grad_memLp
        hψ_grad_tendsto

/-- Positive-part witness constructor with the Stampacchia zero-set input
supplied automatically from the imported Chapter 02 theorem. The remaining
explicit hypothesis is just the smooth approximation package. -/
noncomputable def MemW1pWitness.posPart
    {Ω : Set E} [IsFiniteMeasure (volume.restrict Ω)]
    (hΩ : IsOpen Ω) {u : E → ℝ}
    (hw : MemW1pWitness 2 u Ω)
    (happrox :
      ∃ ψ : ℕ → E → ℝ,
        (∀ n, ContDiff ℝ 1 (ψ n)) ∧
        (∀ n, HasCompactSupport (ψ n)) ∧
        Tendsto (fun n => eLpNorm (fun x => ψ n x - u x) 2 (volume.restrict Ω))
          atTop (nhds 0) ∧
        (∀ i : Fin d,
          Tendsto (fun n => eLpNorm (fun x =>
            (fderiv ℝ (ψ n) x) (EuclideanSpace.single i 1) - hw.weakGrad x i)
            2 (volume.restrict Ω))
          atTop (nhds 0))) :
    MemW1pWitness 2 (fun x => max (u x) 0) Ω :=
  MemW1pWitness.posPart_of_aux hΩ hw
    (hw.weakGrad_ae_eq_zero_on_zeroSet hΩ) happrox

end DeGiorgi
