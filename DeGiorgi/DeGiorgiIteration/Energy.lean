import DeGiorgi.DeGiorgiIteration.CutoffAdmissibility

/-!
# De Giorgi Iteration: Energy and Pre-Iteration

This module contains the weighted Caccioppoli layer, localized energy
estimates, and the abstract real-variable pre-iteration package used later
in the De Giorgi iteration.
-/

noncomputable section

open MeasureTheory Metric Filter Topology Set Function Matrix
open scoped ENNReal NNReal

namespace DeGiorgi

section WeightedPDE

variable {d : ℕ} [NeZero d]

local notation "E" => AmbientSpace d

omit [NeZero d] in
lemma deGiorgiCutoffTestGeneral_nonneg
    {η u : E → ℝ} {k : ℝ}
    (hη_nonneg : ∀ x, 0 ≤ η x) :
    ∀ x, 0 ≤ deGiorgiCutoffTestGeneral η u k x := by
  intro x
  have hpp : 0 ≤ positivePartSub u k x := positivePartSub_nonneg
  exact mul_nonneg (hη_nonneg x) (mul_nonneg (hη_nonneg x) hpp)

noncomputable def deGiorgiFderivVec
    (η : E → ℝ) (x : E) : E :=
  (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ η x)

omit [NeZero d] in
lemma deGiorgiFderivVec_apply
    {η : E → ℝ} {x : E} (i : Fin d) :
    deGiorgiFderivVec η x i = (fderiv ℝ η x) (EuclideanSpace.single i 1) := by
  calc
    deGiorgiFderivVec η x i = inner ℝ (deGiorgiFderivVec η x) (EuclideanSpace.single i (1 : ℝ)) := by
      simpa using
        (EuclideanSpace.inner_single_right (i := i) (a := (1 : ℝ)) (deGiorgiFderivVec η x)).symm
    _ = ((InnerProductSpace.toDual ℝ E) (deGiorgiFderivVec η x)) (EuclideanSpace.single i (1 : ℝ)) := by
      rw [InnerProductSpace.toDual_apply_apply]
    _ = (fderiv ℝ η x) (EuclideanSpace.single i 1) := by
      simp [deGiorgiFderivVec]

omit [NeZero d] in
private lemma fderiv_apply_eq_inner_fderivVec
    {η : E → ℝ} {x ξ : E} :
    (fderiv ℝ η x) ξ = inner ℝ (deGiorgiFderivVec η x) ξ := by
  dsimp [deGiorgiFderivVec]
  symm
  exact InnerProductSpace.toDual_symm_apply

omit [NeZero d] in
lemma deGiorgi_norm_fderivVec_eq_norm_fderiv
    {η : E → ℝ} {x : E} :
    ‖deGiorgiFderivVec η x‖ = ‖fderiv ℝ η x‖ := by
  dsimp [deGiorgiFderivVec]
  exact ((InnerProductSpace.toDual ℝ E).symm.norm_map (fderiv ℝ η x))

private noncomputable def MemW1pWitness.sub
    {Ω : Set E} {u v : E → ℝ}
    (hu : MemW1pWitness 2 u Ω)
    (hv : MemW1pWitness 2 v Ω) :
    MemW1pWitness 2 (fun x => u x - v x) Ω where
  memLp := hu.memLp.sub hv.memLp
  weakGrad := fun x => hu.weakGrad x - hv.weakGrad x
  weakGrad_component_memLp := by
    intro i
    simpa using (hu.weakGrad_component_memLp i).sub (hv.weakGrad_component_memLp i)
  isWeakGrad := by
    intro i φ hφ hφ_supp hφ_sub
    let ei : E := EuclideanSpace.single i (1 : ℝ)
    have hu_eq := hu.isWeakGrad i φ hφ hφ_supp hφ_sub
    have hv_eq := hv.isWeakGrad i φ hφ hφ_supp hφ_sub
    have hderiv_cont : Continuous (fun x => (fderiv ℝ φ x) ei) :=
      (hφ.continuous_fderiv (by simp : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0)).clm_apply
        continuous_const
    have hderiv_supp : HasCompactSupport (fun x => (fderiv ℝ φ x) ei) :=
      hφ_supp.fderiv_apply (𝕜 := ℝ) ei
    have hu_int : Integrable (fun x => u x * (fderiv ℝ φ x) ei) (volume.restrict Ω) := by
      have hu_loc : LocallyIntegrable u (volume.restrict Ω) :=
        hu.memLp.locallyIntegrable (by norm_num)
      simpa [smul_eq_mul] using
        hu_loc.integrable_smul_right_of_hasCompactSupport hderiv_cont hderiv_supp
    have hv_int : Integrable (fun x => v x * (fderiv ℝ φ x) ei) (volume.restrict Ω) := by
      have hv_loc : LocallyIntegrable v (volume.restrict Ω) :=
        hv.memLp.locallyIntegrable (by norm_num)
      simpa [smul_eq_mul] using
        hv_loc.integrable_smul_right_of_hasCompactSupport hderiv_cont hderiv_supp
    have hgu_int : Integrable (fun x => (hu.weakGrad x).ofLp i * φ x) (volume.restrict Ω) := by
      have hgu_loc : LocallyIntegrable (fun x => (hu.weakGrad x).ofLp i) (volume.restrict Ω) :=
        (hu.weakGrad_component_memLp i).locallyIntegrable (by norm_num)
      simpa [smul_eq_mul] using
        hgu_loc.integrable_smul_right_of_hasCompactSupport hφ.continuous hφ_supp
    have hgv_int : Integrable (fun x => (hv.weakGrad x).ofLp i * φ x) (volume.restrict Ω) := by
      have hgv_loc : LocallyIntegrable (fun x => (hv.weakGrad x).ofLp i) (volume.restrict Ω) :=
        (hv.weakGrad_component_memLp i).locallyIntegrable (by norm_num)
      simpa [smul_eq_mul] using
        hgv_loc.integrable_smul_right_of_hasCompactSupport hφ.continuous hφ_supp
    have hfun :
        (fun x => (u x - v x) * (fderiv ℝ φ x) ei) =
          (fun x => u x * (fderiv ℝ φ x) ei - v x * (fderiv ℝ φ x) ei) := by
      ext x
      ring
    have hgrad :
        (fun x => (((hu.weakGrad x - hv.weakGrad x)).ofLp i) * φ x) =
          (fun x => (hu.weakGrad x).ofLp i * φ x - (hv.weakGrad x).ofLp i * φ x) := by
      ext x
      simp [PiLp.sub_apply]
      ring
    rw [hfun, integral_sub hu_int hv_int, hu_eq, hv_eq, hgrad, integral_sub hgu_int hgv_int]
    ring

omit [NeZero d] in
@[simp] private lemma MemW1pWitness.sub_const_weakGrad
    {Ω : Set E} [IsFiniteMeasure (volume.restrict Ω)]
    (hΩ : IsOpen Ω)
    {u : E → ℝ} (hu : MemW1pWitness 2 u Ω)
    (c : ℝ) (x : E) :
    (hu.sub_const hΩ c).weakGrad x = hu.weakGrad x := rfl

omit [NeZero d] in
@[simp] private lemma MemW1pWitness.sub_weakGrad
    {Ω : Set E} {u v : E → ℝ}
    (hu : MemW1pWitness 2 u Ω)
    (hv : MemW1pWitness 2 v Ω)
    (x : E) :
    (hu.sub hv).weakGrad x = hu.weakGrad x - hv.weakGrad x := rfl

private theorem aestronglyMeasurable_matMulE
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

noncomputable def deGiorgiCutoffTestWitnessWeighted
    {Ω : Set E}
    (hΩ : IsOpen Ω)
    {u η : E → ℝ} {k C₀ C₁ : ℝ}
    (hw_trunc : MemW1pWitness 2 (positivePartSub u k) Ω)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁)
    (hη_bound : ∀ x, |η x| ≤ C₀)
    (hη_grad_bound : ∀ x, ‖fderiv ℝ η x‖ ≤ C₁) :
    MemW1pWitness 2 (deGiorgiCutoffTestGeneral η u k) Ω := by
  let hwη :=
    hw_trunc.mul_smooth_bounded hΩ hη
      (C₀ := C₀) (C₁ := C₁) hC₀ hC₁ hη_bound hη_grad_bound
  exact
    hwη.mul_smooth_bounded hΩ hη
      (C₀ := C₀) (C₁ := C₁) hC₀ hC₁ hη_bound hη_grad_bound

omit [NeZero d] in
lemma deGiorgiCutoffTestWitnessWeighted_grad
    {Ω : Set E}
    (hΩ : IsOpen Ω)
    {u η : E → ℝ} {k C₀ C₁ : ℝ}
    (hw_trunc : MemW1pWitness 2 (positivePartSub u k) Ω)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁)
    (hη_bound : ∀ x, |η x| ≤ C₀)
    (hη_grad_bound : ∀ x, ‖fderiv ℝ η x‖ ≤ C₁)
    (x : E) :
    (deGiorgiCutoffTestWitnessWeighted hΩ hw_trunc hη hC₀ hC₁ hη_bound hη_grad_bound).weakGrad x =
      η x ^ 2 • hw_trunc.weakGrad x +
        (2 * η x * positivePartSub u k x) • deGiorgiFderivVec η x := by
  ext i
  simp [deGiorgiCutoffTestWitnessWeighted, MemW1pWitness.mul_smooth_bounded,
    deGiorgiFderivVec_apply]
  ring

private lemma truncGrad_eq_on_superlevel
    {Ω : Set E}
    [IsFiniteMeasure (volume.restrict Ω)]
    (hΩ : IsOpen Ω)
    {u : E → ℝ} {k : ℝ}
    (hu : MemW1pWitness 2 u Ω)
    (hw_trunc : MemW1pWitness 2 (positivePartSub u k) Ω) :
    ∀ᵐ x ∂(volume.restrict Ω), k < u x → hu.weakGrad x = hw_trunc.weakGrad x := by
  let w : E → ℝ := positivePartSub u k
  let hw_shift : MemW1pWitness 2 (fun x => u x - k) Ω := hu.sub_const hΩ k
  let hw_diff : MemW1pWitness 2 (fun x => u x - k - w x) Ω := hw_shift.sub hw_trunc
  have hcomp :
      ∀ i : Fin d, ∀ᵐ x ∂(volume.restrict Ω), k < u x → hu.weakGrad x i = hw_trunc.weakGrad x i := by
    intro i
    have hz := hw_diff.weakGrad_ae_eq_zero_on_zeroSet hΩ i
    filter_upwards [hz] with x hx hku
    have hfun : (u x - k - w x) = 0 := by
      have huxk : 0 ≤ u x - k := le_of_lt (sub_pos.mpr hku)
      simp [w, positivePartSub, max_eq_left huxk]
    have hgrad0 : hw_diff.weakGrad x i = 0 := hx hfun
    have hgrad0' :
        (hu.weakGrad x).ofLp i - (hw_trunc.weakGrad x).ofLp i = 0 := by
      simpa [hw_diff, hw_shift, w, MemW1pWitness.sub, MemW1pWitness.sub_const] using hgrad0
    exact sub_eq_zero.mp hgrad0'
  filter_upwards [ae_all_iff.2 hcomp] with x hx hku
  ext i
  exact hx i hku

private lemma truncGrad_zero_on_sublevel
    {Ω : Set E}
    (hΩ : IsOpen Ω)
    {u : E → ℝ} {k : ℝ}
    (hw_trunc : MemW1pWitness 2 (positivePartSub u k) Ω) :
    ∀ᵐ x ∂(volume.restrict Ω), u x ≤ k → hw_trunc.weakGrad x = 0 := by
  let w : E → ℝ := positivePartSub u k
  have hcomp :
      ∀ i : Fin d, ∀ᵐ x ∂(volume.restrict Ω), u x ≤ k → hw_trunc.weakGrad x i = 0 := by
    intro i
    have hz := hw_trunc.weakGrad_ae_eq_zero_on_zeroSet hΩ i
    filter_upwards [hz] with x hx huk
    have hwx : w x = 0 := by
      have huxk : u x - k ≤ 0 := by linarith
      simp [w, positivePartSub, max_eq_right huxk]
    exact hx hwx
  filter_upwards [ae_all_iff.2 hcomp] with x hx huk
  ext i
  exact hx i huk

private lemma weighted_caccioppoli_pointwise_core
    {Λ η ζ Q M v : ℝ}
    (hΛ : 0 < Λ)
    (hcoeff : |M| ^ 2 ≤ Λ * Q) :
    2 * η * |v| * ζ * |M| ≤
      (1 / 2 : ℝ) * η ^ 2 * Q + 2 * Λ * ζ ^ 2 * |v| ^ 2 := by
  let s := Real.sqrt (2 * Λ)
  have hs_pos : 0 < s := by
    dsimp [s]
    apply Real.sqrt_pos.2
    positivity
  have hs_ne : s ≠ 0 := ne_of_gt hs_pos
  have hs_sq : s ^ 2 = 2 * Λ := by
    dsimp [s]
    rw [Real.sq_sqrt]
    positivity
  have hyoung :
      2 * (η * |M| / s) * (s * ζ * |v|) ≤
        (η * |M| / s) ^ 2 + (s * ζ * |v|) ^ 2 := by
    nlinarith [sq_nonneg ((η * |M| / s) - (s * ζ * |v|))]
  have hcoeff' : η ^ 2 * |M| ^ 2 / (2 * Λ) ≤ (1 / 2 : ℝ) * η ^ 2 * Q := by
    have hmul :
        (η ^ 2 / (2 * Λ)) * (|M| ^ 2) ≤ (η ^ 2 / (2 * Λ)) * (Λ * Q) := by
      refine mul_le_mul_of_nonneg_left hcoeff ?_
      positivity
    have hfac : (η ^ 2 / (2 * Λ)) * (Λ * Q) = (1 / 2 : ℝ) * η ^ 2 * Q := by
      field_simp [hΛ.ne']
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hmul.trans_eq hfac
  have hmain :
      2 * η * |v| * ζ * |M| ≤ η ^ 2 * |M| ^ 2 / (2 * Λ) + 2 * Λ * ζ ^ 2 * |v| ^ 2 := by
    have hconv :
        2 * (η * |M| / s) * (s * ζ * |v|) =
          2 * η * |v| * ζ * |M| := by
      field_simp [hs_ne]
    have hsq1 :
        (η * |M| / s) ^ 2 = η ^ 2 * |M| ^ 2 / (2 * Λ) := by
      rw [div_pow, hs_sq]
      field_simp [hΛ.ne']
    have hsq2 :
        (s * ζ * |v|) ^ 2 = 2 * Λ * ζ ^ 2 * |v| ^ 2 := by
      rw [mul_pow, mul_pow, hs_sq]
    rwa [hconv, hsq1, hsq2] at hyoung
  have hsum :
      η ^ 2 * |M| ^ 2 / (2 * Λ) + 2 * Λ * ζ ^ 2 * |v| ^ 2 ≤
        (1 / 2 : ℝ) * η ^ 2 * Q + 2 * Λ * ζ ^ 2 * |v| ^ 2 := by
    nlinarith [hcoeff']
  exact hmain.trans hsum

private theorem weighted_caccioppoli_absorb_core
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {Q M η ζ v : α → ℝ} {Λ : ℝ}
    (hΛ : 0 < Λ)
    (hcore :
      ∫ x, η x ^ 2 * Q x ∂μ ≤ ∫ x, 2 * η x * |v x| * ζ x * |M x| ∂μ)
    (hcoeff : ∀ᵐ x ∂μ, |M x| ^ 2 ≤ Λ * Q x)
    (hleft_int : Integrable (fun x => η x ^ 2 * Q x) μ)
    (hcross_int : Integrable (fun x => 2 * η x * |v x| * ζ x * |M x|) μ)
    (hbound_int : Integrable (fun x => ζ x ^ 2 * |v x| ^ 2) μ) :
    ∫ x, η x ^ 2 * Q x ∂μ ≤ 4 * Λ * ∫ x, ζ x ^ 2 * |v x| ^ 2 ∂μ := by
  have hupper_pt :
      ∀ᵐ x ∂μ,
        2 * η x * |v x| * ζ x * |M x| ≤
          (1 / 2 : ℝ) * η x ^ 2 * Q x + 2 * Λ * ζ x ^ 2 * |v x| ^ 2 := by
    filter_upwards [hcoeff] with x hx
    exact weighted_caccioppoli_pointwise_core hΛ hx
  have hupper_int :
      Integrable (fun x => (1 / 2 : ℝ) * η x ^ 2 * Q x + 2 * Λ * ζ x ^ 2 * |v x| ^ 2) μ := by
    simpa [mul_assoc, add_comm, add_left_comm, add_assoc] using
      (hleft_int.const_mul (1 / 2 : ℝ)).add (hbound_int.const_mul (2 * Λ))
  have hcross_bound :
      ∫ x, 2 * η x * |v x| * ζ x * |M x| ∂μ ≤
        ∫ x, (1 / 2 : ℝ) * η x ^ 2 * Q x + 2 * Λ * ζ x ^ 2 * |v x| ^ 2 ∂μ := by
    refine integral_mono_ae hcross_int hupper_int ?_
    exact hupper_pt
  have hsplit :
      ∫ x, (1 / 2 : ℝ) * η x ^ 2 * Q x + 2 * Λ * ζ x ^ 2 * |v x| ^ 2 ∂μ =
        (1 / 2 : ℝ) * ∫ x, η x ^ 2 * Q x ∂μ + 2 * Λ * ∫ x, ζ x ^ 2 * |v x| ^ 2 ∂μ := by
    have hrewrite :
        (fun x => (1 / 2 : ℝ) * η x ^ 2 * Q x + 2 * Λ * ζ x ^ 2 * |v x| ^ 2) =
          (fun x => ((1 / 2 : ℝ) * (η x ^ 2 * Q x)) + ((2 * Λ) * (ζ x ^ 2 * |v x| ^ 2))) := by
      funext x
      ring
    rw [hrewrite, integral_add (hleft_int.const_mul (1 / 2 : ℝ)) (hbound_int.const_mul (2 * Λ))]
    rw [integral_const_mul, integral_const_mul]
  have hmain :
      ∫ x, η x ^ 2 * Q x ∂μ ≤
        (1 / 2 : ℝ) * ∫ x, η x ^ 2 * Q x ∂μ + 2 * Λ * ∫ x, ζ x ^ 2 * |v x| ^ 2 ∂μ := by
    calc
      ∫ x, η x ^ 2 * Q x ∂μ ≤ ∫ x, 2 * η x * |v x| * ζ x * |M x| ∂μ := hcore
      _ ≤ ∫ x, (1 / 2 : ℝ) * η x ^ 2 * Q x + 2 * Λ * ζ x ^ 2 * |v x| ^ 2 ∂μ := hcross_bound
      _ = (1 / 2 : ℝ) * ∫ x, η x ^ 2 * Q x ∂μ + 2 * Λ * ∫ x, ζ x ^ 2 * |v x| ^ 2 ∂μ := hsplit
  linarith

/-- PDE-facing weighted Caccioppoli inequality for the truncated subsolution
test `η² (u-k)₊`. The analytic core of the argument is isolated here for
downstream reuse. -/
theorem caccioppoli_weighted_of_subsolution
    {Ω : Set E}
    [IsFiniteMeasure (volume.restrict Ω)]
    (hΩ : IsOpen Ω)
    (A : EllipticCoeff d Ω)
    {u η : E → ℝ} {k : ℝ}
    (hsub : IsSubsolution A u)
    (hu : MemW1pWitness 2 u Ω)
    (hw_trunc : MemW1pWitness 2 (positivePartSub u k) Ω)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hη_nonneg : ∀ x, 0 ≤ η x)
    {C₀ C₁ : ℝ}
    (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁)
    (hη_bound : ∀ x, |η x| ≤ C₀)
    (hη_grad_bound : ∀ x, ‖fderiv ℝ η x‖ ≤ C₁)
    (hη_admissible : MemW01p 2 (deGiorgiCutoffTestGeneral η u k) Ω) :
    ∫ x in Ω, η x ^ 2 * ‖hw_trunc.weakGrad x‖ ^ 2 ∂volume ≤
      4 * ellipticityRatio A *
        ∫ x in Ω, ‖fderiv ℝ η x‖ ^ 2 * |positivePartSub u k x| ^ 2 ∂volume := by
  let μ : Measure E := volume.restrict Ω
  let hwφ : MemW1pWitness 2 (deGiorgiCutoffTestGeneral η u k) Ω :=
    deGiorgiCutoffTestWitnessWeighted hΩ hw_trunc hη hC₀ hC₁ hη_bound hη_grad_bound
  let Equad : E → ℝ := bilinFormIntegrandOfCoeff A hw_trunc hw_trunc
  let leftTerm : E → ℝ := fun x => η x ^ 2 * Equad x
  let gradEtaNorm : E → ℝ := fun x => ‖fderiv ℝ η x‖
  let fluxNorm : E → ℝ := fun x => ‖matMulE (A.a x) (hw_trunc.weakGrad x)‖
  let crossAbs : E → ℝ :=
    fun x => 2 * η x * positivePartSub u k x * fluxNorm x * gradEtaNorm x
  let crossInner : E → ℝ :=
    fun x =>
      (2 * η x * positivePartSub u k x) *
        inner ℝ (matMulE (A.a x) (hw_trunc.weakGrad x)) (deGiorgiFderivVec η x)
  let coreIntegrand : E → ℝ := fun x => leftTerm x + crossInner x
  have hsub_test :
      bilinFormOfCoeff A hu hwφ ≤ 0 := by
    exact hsub.2 hu (deGiorgiCutoffTestGeneral η u k) hη_admissible hwφ
      (deGiorgiCutoffTestGeneral_nonneg hη_nonneg)
  have htrunc_sq_int :
      Integrable (fun x => ‖hw_trunc.weakGrad x‖ ^ 2) μ := by
    simpa [pow_two, μ] using hw_trunc.weakGrad_norm_memLp.integrable_sq
  have hweighted_grad_sq_int :
      Integrable (fun x => η x ^ 2 * ‖hw_trunc.weakGrad x‖ ^ 2) μ := by
    refine Integrable.mono' (htrunc_sq_int.const_mul (C₀ ^ 2)) ?_ ?_
    · exact
        (((hη.continuous.pow 2).aemeasurable).mul
          htrunc_sq_int.aestronglyMeasurable.aemeasurable).aestronglyMeasurable
    · filter_upwards with x
      have hη_sq_le : η x ^ 2 ≤ C₀ ^ 2 := by
        exact sq_le_sq.mpr (by simpa [abs_of_nonneg hC₀] using hη_bound x)
      have hgrad_nonneg : 0 ≤ ‖hw_trunc.weakGrad x‖ ^ 2 := by positivity
      have hterm_nonneg : 0 ≤ η x ^ 2 * ‖hw_trunc.weakGrad x‖ ^ 2 := by positivity
      have hle :
          η x ^ 2 * ‖hw_trunc.weakGrad x‖ ^ 2 ≤
            C₀ ^ 2 * ‖hw_trunc.weakGrad x‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hη_sq_le hgrad_nonneg
      simpa [Real.norm_eq_abs, abs_of_nonneg hterm_nonneg] using hle
  have hpos_sq_int :
      Integrable (fun x => |positivePartSub u k x| ^ 2) μ := by
    simpa [pow_two, μ] using hw_trunc.memLp.integrable_sq
  have hbound_int :
      Integrable (fun x => gradEtaNorm x ^ 2 * |positivePartSub u k x| ^ 2) μ := by
    refine Integrable.mono' (hpos_sq_int.const_mul (C₁ ^ 2)) ?_ ?_
    · exact
        ((((hη.continuous_fderiv (by simp : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0)).norm.pow 2).aemeasurable).mul
          hpos_sq_int.aestronglyMeasurable.aemeasurable).aestronglyMeasurable
    · filter_upwards with x
      have hfd_sq_le : gradEtaNorm x ^ 2 ≤ C₁ ^ 2 := by
        exact sq_le_sq.mpr (by
          simp [gradEtaNorm, abs_of_nonneg (norm_nonneg _), abs_of_nonneg hC₁, hη_grad_bound x])
      have hpos_nonneg : 0 ≤ |positivePartSub u k x| ^ 2 := by positivity
      have hterm_nonneg : 0 ≤ gradEtaNorm x ^ 2 * |positivePartSub u k x| ^ 2 := by positivity
      have hle :
          gradEtaNorm x ^ 2 * |positivePartSub u k x| ^ 2 ≤
            C₁ ^ 2 * |positivePartSub u k x| ^ 2 :=
        mul_le_mul_of_nonneg_right hfd_sq_le hpos_nonneg
      simpa [Real.norm_eq_abs, abs_of_nonneg hterm_nonneg] using hle
  have hE_nonneg :
      ∀ᵐ x ∂μ, 0 ≤ Equad x := by
    filter_upwards [A.ae_coercive_nonneg] with x hx
    simpa [Equad, bilinFormIntegrandOfCoeff, real_inner_comm] using hx (hw_trunc.weakGrad x)
  have hleft_int :
      Integrable leftTerm μ := by
    refine Integrable.mono' (hweighted_grad_sq_int.const_mul A.Λ) ?_ ?_
    · exact
        (((hη.continuous.pow 2).aemeasurable).mul
          (aestronglyMeasurable_bilinFormIntegrandOfCoeff A hw_trunc hw_trunc).aemeasurable).aestronglyMeasurable
    · filter_upwards [A.quadratic_upper, hE_nonneg] with x hx_quad hx_nonneg
      have hη_sq_nonneg : 0 ≤ η x ^ 2 := by positivity
      have hdom :
          η x ^ 2 * Equad x ≤ η x ^ 2 * (A.Λ * ‖hw_trunc.weakGrad x‖ ^ 2) :=
        mul_le_mul_of_nonneg_left
          (by simpa [Equad, bilinFormIntegrandOfCoeff, real_inner_comm] using
            hx_quad (hw_trunc.weakGrad x)) hη_sq_nonneg
      have hrhs_nonneg : 0 ≤ A.Λ * (η x ^ 2 * ‖hw_trunc.weakGrad x‖ ^ 2) := by
        exact mul_nonneg A.Λ_nonneg (by positivity)
      have hterm_nonneg : 0 ≤ leftTerm x := by
        exact mul_nonneg hη_sq_nonneg hx_nonneg
      have hnorm_rhs :
          ‖A.Λ * (η x ^ 2 * ‖hw_trunc.weakGrad x‖ ^ 2)‖ =
            A.Λ * (η x ^ 2 * ‖hw_trunc.weakGrad x‖ ^ 2) := by
        rw [Real.norm_eq_abs, abs_of_nonneg hrhs_nonneg]
      calc
        ‖leftTerm x‖ = leftTerm x := by rw [Real.norm_eq_abs, abs_of_nonneg hterm_nonneg]
        _ = η x ^ 2 * Equad x := by rfl
        _ ≤ η x ^ 2 * (A.Λ * ‖hw_trunc.weakGrad x‖ ^ 2) := hdom
        _ = A.Λ * (η x ^ 2 * ‖hw_trunc.weakGrad x‖ ^ 2) := by ring
  have hcoeff :
      ∀ᵐ x ∂μ, |fluxNorm x| ^ 2 ≤ A.Λ * Equad x := by
    filter_upwards [A.mulVec_sq_le] with x hx
    simpa [fluxNorm, Equad, bilinFormIntegrandOfCoeff, real_inner_comm] using
      hx (hw_trunc.weakGrad x)
  have hcross_upper_pt :
      ∀ᵐ x ∂μ,
        crossAbs x ≤
          (1 / 2 : ℝ) * leftTerm x + 2 * A.Λ * (gradEtaNorm x ^ 2 * |positivePartSub u k x| ^ 2) := by
    filter_upwards [hcoeff] with x hx
    have hx' :=
      weighted_caccioppoli_pointwise_core
        (Λ := A.Λ) (η := η x) (ζ := gradEtaNorm x) (Q := Equad x)
        (M := fluxNorm x) (v := positivePartSub u k x) A.Λ_pos hx
    simpa [crossAbs, leftTerm, gradEtaNorm, fluxNorm, Equad, abs_of_nonneg positivePartSub_nonneg,
      mul_assoc, mul_left_comm, mul_comm]
      using hx'
  have hcross_upper_int :
      Integrable
        (fun x =>
          (1 / 2 : ℝ) * leftTerm x + 2 * A.Λ * (gradEtaNorm x ^ 2 * |positivePartSub u k x| ^ 2)) μ := by
    simpa [mul_assoc, add_comm, add_left_comm, add_assoc] using
      (hleft_int.const_mul (1 / 2 : ℝ)).add (hbound_int.const_mul (2 * A.Λ))
  have hcrossAbs_int :
      Integrable crossAbs μ := by
    refine Integrable.mono' hcross_upper_int ?_ ?_
    · simpa [crossAbs, gradEtaNorm, fluxNorm, mul_assoc, mul_left_comm, mul_comm] using
        ((((hη.continuous.aestronglyMeasurable).mul
          hw_trunc.memLp.aestronglyMeasurable).mul
          ((hη.continuous_fderiv (by simp : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0)).norm.aestronglyMeasurable)).mul
          ((aestronglyMeasurable_matMulE A hw_trunc.weakGrad_memLp.aestronglyMeasurable).norm)).const_mul
          (2 : ℝ)
    · filter_upwards [hcross_upper_pt] with x hx
      have hcross_nonneg : 0 ≤ crossAbs x := by
        have hηx_nonneg : 0 ≤ η x := hη_nonneg x
        have hw_nonneg : 0 ≤ positivePartSub u k x := positivePartSub_nonneg
        have hflux_nonneg : 0 ≤ fluxNorm x := norm_nonneg _
        have hgrad_nonneg : 0 ≤ gradEtaNorm x := norm_nonneg _
        have hcoeff_nonneg : 0 ≤ 2 * η x * positivePartSub u k x := by
          nlinarith
        dsimp [crossAbs]
        exact mul_nonneg (mul_nonneg hcoeff_nonneg hflux_nonneg) hgrad_nonneg
      have hrhs_nonneg :
          0 ≤ (1 / 2 : ℝ) * leftTerm x + 2 * A.Λ * (gradEtaNorm x ^ 2 * |positivePartSub u k x| ^ 2) := by
        exact le_trans hcross_nonneg hx
      simpa [Real.norm_eq_abs, abs_of_nonneg hcross_nonneg, abs_of_nonneg hrhs_nonneg] using hx
  have hcore_eq_ae :
      coreIntegrand =ᵐ[μ] bilinFormIntegrandOfCoeff A hu hwφ := by
    have hsuper := truncGrad_eq_on_superlevel hΩ hu hw_trunc
    have hsublevel := truncGrad_zero_on_sublevel hΩ hw_trunc
    filter_upwards [hsuper, hsublevel] with x hsuperx hsublevelx
    by_cases hku : k < u x
    · have hgrad_eq : hu.weakGrad x = hw_trunc.weakGrad x := hsuperx hku
      simp [coreIntegrand, leftTerm, crossInner, Equad, hwφ, bilinFormIntegrandOfCoeff,
        deGiorgiCutoffTestWitnessWeighted_grad, hgrad_eq, inner_add_right,
        inner_smul_right, real_inner_comm, mul_assoc, mul_comm]
    · have huk : u x ≤ k := not_lt.mp hku
      have htrunc_zero : hw_trunc.weakGrad x = 0 := hsublevelx huk
      have hw_zero : positivePartSub u k x = 0 := by
        simp [positivePartSub, max_eq_right (sub_nonpos.mpr huk)]
      simp [coreIntegrand, leftTerm, crossInner, Equad, hwφ, bilinFormIntegrandOfCoeff,
        deGiorgiCutoffTestWitnessWeighted_grad, htrunc_zero, hw_zero]
  have hcore_int :
      Integrable coreIntegrand μ := by
    refine (integrable_bilinFormIntegrandOfCoeff A hu hwφ).congr ?_
    exact hcore_eq_ae.symm
  have hcrossInner_int :
      Integrable crossInner μ := by
    convert hcore_int.sub hleft_int using 1
    ext x
    simp [coreIntegrand]
  have hcrossInner_abs_le :
      ∀ᵐ x ∂μ, |crossInner x| ≤ crossAbs x := by
    filter_upwards with x
    have hηx_nonneg : 0 ≤ η x := hη_nonneg x
    have hw_nonneg : 0 ≤ positivePartSub u k x := positivePartSub_nonneg
    have hinner :
        |inner ℝ (matMulE (A.a x) (hw_trunc.weakGrad x)) (deGiorgiFderivVec η x)| ≤
          fluxNorm x * gradEtaNorm x := by
      have := abs_real_inner_le_norm (matMulE (A.a x) (hw_trunc.weakGrad x)) (deGiorgiFderivVec η x)
      have hfdv := deGiorgi_norm_fderivVec_eq_norm_fderiv (η := η) (x := x)
      change
        |inner ℝ (matMulE (A.a x) (hw_trunc.weakGrad x)) (deGiorgiFderivVec η x)| ≤
          ‖matMulE (A.a x) (hw_trunc.weakGrad x)‖ * ‖fderiv ℝ η x‖
      simpa [hfdv, mul_comm] using this
    have hcoeff_nonneg : 0 ≤ 2 * η x * positivePartSub u k x := by
      nlinarith
    change
      |2 * η x * positivePartSub u k x *
          inner ℝ (matMulE (A.a x) (hw_trunc.weakGrad x)) (deGiorgiFderivVec η x)| ≤
        2 * η x * positivePartSub u k x * fluxNorm x * gradEtaNorm x
    rw [abs_mul, abs_of_nonneg hcoeff_nonneg]
    calc
      (2 * η x * positivePartSub u k x) *
          |inner ℝ (matMulE (A.a x) (hw_trunc.weakGrad x)) (deGiorgiFderivVec η x)|
          ≤ (2 * η x * positivePartSub u k x) * (fluxNorm x * gradEtaNorm x) := by
            exact mul_le_mul_of_nonneg_left hinner hcoeff_nonneg
      _ = 2 * η x * positivePartSub u k x * fluxNorm x * gradEtaNorm x := by
            ring
  have hcross_lower :
      -∫ x, crossAbs x ∂μ ≤ ∫ x, crossInner x ∂μ := by
    have hneg :
        ∫ x, (-1 : ℝ) * crossAbs x ∂μ ≤ ∫ x, crossInner x ∂μ := by
      refine integral_mono_ae (hcrossAbs_int.const_mul (-1)) hcrossInner_int ?_
      filter_upwards [hcrossInner_abs_le] with x hx
      exact show (-1 : ℝ) * crossAbs x ≤ crossInner x by
        simpa using (abs_le.mp hx).1
    simpa [integral_neg] using hneg
  have hcore_integral :
      ∫ x, leftTerm x ∂μ ≤ ∫ x, crossAbs x ∂μ := by
    have hsub_test' :
        ∫ x, coreIntegrand x ∂μ ≤ 0 := by
      calc
        ∫ x, coreIntegrand x ∂μ = bilinFormOfCoeff A hu hwφ := by
          unfold bilinFormOfCoeff
          exact integral_congr_ae hcore_eq_ae
        _ ≤ 0 := hsub_test
    have hsplit :
        ∫ x, coreIntegrand x ∂μ = ∫ x, leftTerm x ∂μ + ∫ x, crossInner x ∂μ := by
      rw [show coreIntegrand = fun x => leftTerm x + crossInner x by
            funext x; simp [coreIntegrand]]
      exact integral_add hleft_int hcrossInner_int
    linarith
  have hleft_bound :
      ∫ x, leftTerm x ∂μ ≤ 4 * A.Λ * ∫ x, gradEtaNorm x ^ 2 * |positivePartSub u k x| ^ 2 ∂μ := by
    have hcore_absorb :
        ∫ x, η x ^ 2 * Equad x ∂μ ≤
          4 * A.Λ * ∫ x, gradEtaNorm x ^ 2 * |positivePartSub u k x| ^ 2 ∂μ := by
      have hcore' :
          ∫ x, η x ^ 2 * Equad x ∂μ ≤
            ∫ x, 2 * η x * |positivePartSub u k x| * gradEtaNorm x * |fluxNorm x| ∂μ := by
        simpa [crossAbs, fluxNorm, gradEtaNorm, abs_of_nonneg positivePartSub_nonneg,
          abs_of_nonneg (norm_nonneg _), mul_assoc, mul_left_comm, mul_comm]
          using hcore_integral
      have hcross_int' :
          Integrable (fun x => 2 * η x * |positivePartSub u k x| * gradEtaNorm x * |fluxNorm x|) μ := by
        simpa [crossAbs, fluxNorm, gradEtaNorm, abs_of_nonneg positivePartSub_nonneg,
          abs_of_nonneg (norm_nonneg _), mul_assoc, mul_left_comm, mul_comm]
          using hcrossAbs_int
      exact
        weighted_caccioppoli_absorb_core
          (μ := μ) (Q := Equad) (M := fluxNorm) (η := η)
          (ζ := gradEtaNorm) (v := positivePartSub u k) (Λ := A.Λ)
          A.Λ_pos hcore' hcoeff
          (by simpa [leftTerm] using hleft_int) hcross_int' hbound_int
    simpa [leftTerm] using hcore_absorb
  have hcoercive_weighted :
      A.lam * ∫ x in Ω, η x ^ 2 * ‖hw_trunc.weakGrad x‖ ^ 2 ∂volume ≤ ∫ x, leftTerm x ∂μ := by
    have hcoercive_ae :
        ∀ᵐ x ∂μ,
          A.lam * (η x ^ 2 * ‖hw_trunc.weakGrad x‖ ^ 2) ≤ leftTerm x := by
      filter_upwards [A.coercive] with x hx
      have hη_sq_nonneg : 0 ≤ η x ^ 2 := by positivity
      have := mul_le_mul_of_nonneg_left (hx (hw_trunc.weakGrad x)) hη_sq_nonneg
      simpa [leftTerm, Equad, bilinFormIntegrandOfCoeff, real_inner_comm,
        mul_assoc, mul_left_comm, mul_comm] using this
    have hleftSide_int :
        Integrable (fun x => A.lam * (η x ^ 2 * ‖hw_trunc.weakGrad x‖ ^ 2)) μ := by
      simpa [μ] using hweighted_grad_sq_int.const_mul A.lam
    calc
      A.lam * ∫ x in Ω, η x ^ 2 * ‖hw_trunc.weakGrad x‖ ^ 2 ∂volume
          = ∫ x, A.lam * (η x ^ 2 * ‖hw_trunc.weakGrad x‖ ^ 2) ∂μ := by
              simp [μ, integral_const_mul]
      _ ≤ ∫ x, leftTerm x ∂μ := by
            exact integral_mono_ae hleftSide_int hleft_int hcoercive_ae
  have hmain :
      A.lam * ∫ x in Ω, η x ^ 2 * ‖hw_trunc.weakGrad x‖ ^ 2 ∂volume ≤
        4 * A.Λ * ∫ x, gradEtaNorm x ^ 2 * |positivePartSub u k x| ^ 2 ∂μ := by
    exact hcoercive_weighted.trans hleft_bound
  have hlam_ne : A.lam ≠ 0 := ne_of_gt A.hlam
  have hdiv :
      ∫ x in Ω, η x ^ 2 * ‖hw_trunc.weakGrad x‖ ^ 2 ∂volume ≤
        (4 * A.Λ * ∫ x, gradEtaNorm x ^ 2 * |positivePartSub u k x| ^ 2 ∂μ) / A.lam := by
    refine (le_div_iff₀ A.hlam).2 ?_
    simpa [mul_assoc, mul_left_comm, mul_comm] using hmain
  calc
    ∫ x in Ω, η x ^ 2 * ‖hw_trunc.weakGrad x‖ ^ 2 ∂volume
        ≤ (4 * A.Λ * ∫ x, gradEtaNorm x ^ 2 * |positivePartSub u k x| ^ 2 ∂μ) / A.lam := hdiv
    _ = 4 * ellipticityRatio A *
          ∫ x in Ω, ‖fderiv ℝ η x‖ ^ 2 * |positivePartSub u k x| ^ 2 ∂volume := by
          simp [μ, ellipticityRatio, gradEtaNorm, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]

/-- Ball-specialized weighted Caccioppoli inequality, using the generalized
cutoff admissibility theorem from the previous section. -/
theorem caccioppoli_weighted_on_ball_of_ballPosPart
    {u η : E → ℝ} {x₀ : E} {s Cη k : ℝ}
    (A : EllipticCoeff d (Metric.ball x₀ s))
    (_hs : 0 < s)
    (hsub : IsSubsolution A u)
    (hu : MemW1pWitness 2 u (Metric.ball x₀ s))
    (hw_trunc : MemW1pWitness 2 (positivePartSub u k) (Metric.ball x₀ s))
    (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hη_nonneg : ∀ x, 0 ≤ η x)
    (hη_bound : ∀ x, |η x| ≤ 1)
    (hCη : 0 ≤ Cη)
    (hη_grad_bound : ∀ x, ‖fderiv ℝ η x‖ ≤ Cη)
    (hη_sub_ball : tsupport η ⊆ Metric.ball x₀ s) :
    ∫ x in Metric.ball x₀ s, η x ^ 2 * ‖hw_trunc.weakGrad x‖ ^ 2 ∂volume ≤
      4 * ellipticityRatio A *
        ∫ x in Metric.ball x₀ s, ‖fderiv ℝ η x‖ ^ 2 * |positivePartSub u k x| ^ 2 ∂volume := by
  haveI : IsFiniteMeasure (volume.restrict (Metric.ball x₀ s)) := by
    rw [isFiniteMeasure_restrict]
    exact measure_ball_lt_top.ne
  have hη_comp : HasCompactSupport η :=
    hasCompactSupport_of_tsupport_subset_ball hη_sub_ball
  have hη_admissible :
      MemW01p 2 (deGiorgiCutoffTestGeneral η u k) (Metric.ball x₀ s) :=
    deGiorgiCutoffTest_memW01p_of_truncWitness
      isOpen_ball hw_trunc hη (by norm_num) hCη hη_bound hη_grad_bound hη_comp hη_sub_ball
  exact caccioppoli_weighted_of_subsolution isOpen_ball A hsub hu hw_trunc hη hη_nonneg
    (by norm_num) hCη hη_bound hη_grad_bound hη_admissible

/-- Ball-specialized weighted Caccioppoli inequality with the truncation witness
constructed from the concrete Chapter 02 positive-part API. -/
theorem caccioppoli_weighted_on_ball_of_posPartApprox
    {u η : E → ℝ} {x₀ : E} {s Cη k : ℝ}
    (A : EllipticCoeff d (Metric.ball x₀ s))
    (hs : 0 < s)
    (hsub : IsSubsolution A u)
    (hu : MemW1pWitness 2 u (Metric.ball x₀ s))
    (happroxBallShift :
      ∃ ψ : ℕ → E → ℝ,
        (∀ n, ContDiff ℝ 1 (ψ n)) ∧
        (∀ n, HasCompactSupport (ψ n)) ∧
        Tendsto
          (fun n =>
            eLpNorm (fun x => ψ n x - (u x - k)) 2
              (volume.restrict (Metric.ball x₀ s)))
          atTop (nhds 0) ∧
        (∀ i : Fin d,
          Tendsto
            (fun n =>
              eLpNorm
                (fun x =>
                  (fderiv ℝ (ψ n) x) (EuclideanSpace.single i 1) - hu.weakGrad x i)
                2 (volume.restrict (Metric.ball x₀ s)))
            atTop (nhds 0)))
    (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hη_nonneg : ∀ x, 0 ≤ η x)
    (hη_bound : ∀ x, |η x| ≤ 1)
    (hCη : 0 ≤ Cη)
    (hη_grad_bound : ∀ x, ‖fderiv ℝ η x‖ ≤ Cη)
    (hη_sub_ball : tsupport η ⊆ Metric.ball x₀ s) :
    ∫ x in Metric.ball x₀ s, η x ^ 2 * ‖(positivePartSub_memW1pWitness_on_ball
        hs hu k happroxBallShift).weakGrad x‖ ^ 2 ∂volume ≤
      4 * ellipticityRatio A *
        ∫ x in Metric.ball x₀ s, ‖fderiv ℝ η x‖ ^ 2 * |positivePartSub u k x| ^ 2 ∂volume := by
  haveI : IsFiniteMeasure (volume.restrict (Metric.ball x₀ s)) := by
    rw [isFiniteMeasure_restrict]
    exact measure_ball_lt_top.ne
  let hw_trunc : MemW1pWitness 2 (positivePartSub u k) (Metric.ball x₀ s) :=
    positivePartSub_memW1pWitness_on_ball hs hu k happroxBallShift
  have hη_admissible :
      MemW01p 2 (deGiorgiCutoffTestGeneral η u k) (Metric.ball x₀ s) :=
    deGiorgiCutoffTest_memW01p_on_ball_of_ballPosPartApprox
      hs hu hη hη_bound hCη hη_grad_bound hη_sub_ball k happroxBallShift
  change
    ∫ x in Metric.ball x₀ s, η x ^ 2 * ‖hw_trunc.weakGrad x‖ ^ 2 ∂volume ≤
      4 * ellipticityRatio A *
        ∫ x in Metric.ball x₀ s, ‖fderiv ℝ η x‖ ^ 2 * |positivePartSub u k x| ^ 2 ∂volume
  exact caccioppoli_weighted_of_subsolution isOpen_ball A hsub hu hw_trunc hη hη_nonneg
    (by norm_num) hCη hη_bound hη_grad_bound hη_admissible

/-- Localized De Giorgi energy estimate on concentric balls. This packages the
weighted Caccioppoli inequality together with the localization step. -/
theorem deGiorgi_energy_estimate_on_concentricBalls_of_ballPosPart
    {u η : E → ℝ} {x₀ : E} {r s Cη k : ℝ}
    (A : EllipticCoeff d (Metric.ball x₀ s))
    (hr : 0 < r) (hrs : r < s)
    (hsub : IsSubsolution A u)
    (hu : MemW1pWitness 2 u (Metric.ball x₀ s))
    (hw_trunc : MemW1pWitness 2 (positivePartSub u k) (Metric.ball x₀ s))
    (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hη_nonneg : ∀ x, 0 ≤ η x)
    (hη_eq_one : ∀ x ∈ Metric.ball x₀ r, η x = 1)
    (hη_bound : ∀ x, |η x| ≤ 1)
    (hCη : 0 ≤ Cη)
    (hη_grad_bound : ∀ x, ‖fderiv ℝ η x‖ ≤ Cη)
    (hη_sub_ball : tsupport η ⊆ Metric.ball x₀ s) :
    ∫ x in Metric.ball x₀ r, ‖hw_trunc.weakGrad x‖ ^ 2 ∂volume ≤
      4 * ellipticityRatio A * Cη ^ 2 *
        ∫ x in Metric.ball x₀ s, |positivePartSub u k x| ^ 2 ∂volume := by
  have hs : 0 < s := lt_trans hr hrs
  have htrunc_sq_int :
      IntegrableOn (fun x => ‖hw_trunc.weakGrad x‖ ^ 2)
        (Metric.ball x₀ s) volume := by
    simpa [pow_two] using hw_trunc.weakGrad_norm_memLp.integrable_sq
  have hweighted_int :
      IntegrableOn (fun x => η x ^ 2 * ‖hw_trunc.weakGrad x‖ ^ 2)
        (Metric.ball x₀ s) volume := by
    refine Integrable.mono' htrunc_sq_int ?_ ?_
    · exact
        (((hη.continuous.pow 2).aemeasurable).mul
          htrunc_sq_int.aestronglyMeasurable.aemeasurable).aestronglyMeasurable
    · filter_upwards with x
      have hηx_nonneg : 0 ≤ η x := hη_nonneg x
      have hηx_le_one : η x ≤ 1 := by
        simpa [abs_of_nonneg hηx_nonneg] using hη_bound x
      have hηx_sq_le_one : η x ^ 2 ≤ 1 := by
        nlinarith
      have hgw_nonneg : 0 ≤ ‖hw_trunc.weakGrad x‖ ^ 2 := by positivity
      have hprod_nonneg : 0 ≤ η x ^ 2 * ‖hw_trunc.weakGrad x‖ ^ 2 := by positivity
      have hle : η x ^ 2 * ‖hw_trunc.weakGrad x‖ ^ 2 ≤ ‖hw_trunc.weakGrad x‖ ^ 2 := by
        nlinarith
      simpa [Real.norm_eq_abs, abs_of_nonneg hprod_nonneg, abs_of_nonneg hgw_nonneg] using hle
  have hpos_sq_int :
      IntegrableOn (fun x => |positivePartSub u k x| ^ 2)
        (Metric.ball x₀ s) volume := by
    simpa [pow_two] using hw_trunc.memLp.integrable_sq
  have hgrad_term_int :
      IntegrableOn (fun x => ‖fderiv ℝ η x‖ ^ 2 * |positivePartSub u k x| ^ 2)
        (Metric.ball x₀ s) volume := by
    refine Integrable.mono' (hpos_sq_int.const_mul (Cη ^ 2)) ?_ ?_
    · exact
        ((((hη.continuous_fderiv (by simp : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0)).norm.pow 2).aemeasurable).mul
          hpos_sq_int.aestronglyMeasurable.aemeasurable).aestronglyMeasurable
    · filter_upwards with x
      have hfd_sq_le : ‖fderiv ℝ η x‖ ^ 2 ≤ Cη ^ 2 := by
        exact sq_le_sq.mpr (by
          simpa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg hCη] using hη_grad_bound x)
      have hpos_nonneg : 0 ≤ |positivePartSub u k x| ^ 2 := by positivity
      have hterm_nonneg :
          0 ≤ ‖fderiv ℝ η x‖ ^ 2 * |positivePartSub u k x| ^ 2 := by positivity
      have hle :
          ‖fderiv ℝ η x‖ ^ 2 * |positivePartSub u k x| ^ 2 ≤
            Cη ^ 2 * |positivePartSub u k x| ^ 2 :=
        mul_le_mul_of_nonneg_right hfd_sq_le hpos_nonneg
      simpa [Real.norm_eq_abs, abs_of_nonneg hterm_nonneg] using hle
  have hweighted :
      ∫ x in Metric.ball x₀ s, η x ^ 2 * ‖hw_trunc.weakGrad x‖ ^ 2 ∂volume ≤
        (4 * ellipticityRatio A) *
          ∫ x in Metric.ball x₀ s, ‖fderiv ℝ η x‖ ^ 2 * |positivePartSub u k x| ^ 2
            ∂volume := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      caccioppoli_weighted_on_ball_of_ballPosPart
        A hs hsub hu hw_trunc hη hη_nonneg hη_bound hCη hη_grad_bound hη_sub_ball
  have hleft_eq :
      ∫ x in Metric.ball x₀ r, ‖hw_trunc.weakGrad x‖ ^ 2 ∂volume =
        ∫ x in Metric.ball x₀ r, η x ^ 2 * ‖hw_trunc.weakGrad x‖ ^ 2 ∂volume := by
    refine integral_congr_ae ?_
    refine (ae_restrict_iff' (μ := volume) measurableSet_ball).2 ?_
    filter_upwards with x hx
    simp [hη_eq_one x hx]
  have hweighted_nonneg :
      ∀ x, 0 ≤ η x ^ 2 * ‖hw_trunc.weakGrad x‖ ^ 2 := by
    intro x
    positivity
  have hleft_mono :
      ∫ x in Metric.ball x₀ r, η x ^ 2 * ‖hw_trunc.weakGrad x‖ ^ 2 ∂volume ≤
        ∫ x in Metric.ball x₀ s, η x ^ 2 * ‖hw_trunc.weakGrad x‖ ^ 2 ∂volume := by
    exact setIntegral_mono_set hweighted_int
      (ae_of_all _ hweighted_nonneg)
      (ae_of_all _ (Metric.ball_subset_ball (le_of_lt hrs)))
  have hgrad_bound :
      ∫ x in Metric.ball x₀ s, ‖fderiv ℝ η x‖ ^ 2 * |positivePartSub u k x| ^ 2 ∂volume ≤
        ∫ x in Metric.ball x₀ s, Cη ^ 2 * |positivePartSub u k x| ^ 2 ∂volume := by
    refine integral_mono_ae hgrad_term_int (hpos_sq_int.const_mul (Cη ^ 2)) ?_
    refine (ae_restrict_iff' (μ := volume) measurableSet_ball).2 ?_
    filter_upwards with x hx
    have hfd_sq_le : ‖fderiv ℝ η x‖ ^ 2 ≤ Cη ^ 2 := by
      exact sq_le_sq.mpr (by
        simpa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg hCη] using hη_grad_bound x)
    have hpos_nonneg : 0 ≤ |positivePartSub u k x| ^ 2 := by positivity
    exact mul_le_mul_of_nonneg_right hfd_sq_le hpos_nonneg
  have hcoeff_nonneg : 0 ≤ 4 * ellipticityRatio A := by
    have hRatio_nonneg : 0 ≤ ellipticityRatio A := A.ellipticityRatio_nonneg
    nlinarith
  calc
    ∫ x in Metric.ball x₀ r, ‖hw_trunc.weakGrad x‖ ^ 2 ∂volume
        = ∫ x in Metric.ball x₀ r, η x ^ 2 * ‖hw_trunc.weakGrad x‖ ^ 2 ∂volume := hleft_eq
    _ ≤ ∫ x in Metric.ball x₀ s, η x ^ 2 * ‖hw_trunc.weakGrad x‖ ^ 2 ∂volume := hleft_mono
    _ ≤ (4 * ellipticityRatio A) *
          ∫ x in Metric.ball x₀ s, ‖fderiv ℝ η x‖ ^ 2 * |positivePartSub u k x| ^ 2
            ∂volume := hweighted
    _ ≤ (4 * ellipticityRatio A) *
          ∫ x in Metric.ball x₀ s, Cη ^ 2 * |positivePartSub u k x| ^ 2 ∂volume := by
            exact mul_le_mul_of_nonneg_left hgrad_bound hcoeff_nonneg
    _ = 4 * ellipticityRatio A * Cη ^ 2 *
          ∫ x in Metric.ball x₀ s, |positivePartSub u k x| ^ 2 ∂volume := by
            rw [integral_const_mul]
            ring

/-- Localized De Giorgi energy estimate using the concrete Chapter 02
positive-part witness constructor on the outer ball. -/
theorem deGiorgi_energy_estimate_on_concentricBalls_of_posPartApprox
    {u η : E → ℝ} {x₀ : E} {r s Cη k : ℝ}
    (A : EllipticCoeff d (Metric.ball x₀ s))
    (hs : 0 < s) (hr : 0 < r) (hrs : r < s)
    (hsub : IsSubsolution A u)
    (hu : MemW1pWitness 2 u (Metric.ball x₀ s))
    (happroxBallShift :
      ∃ ψ : ℕ → E → ℝ,
        (∀ n, ContDiff ℝ 1 (ψ n)) ∧
        (∀ n, HasCompactSupport (ψ n)) ∧
        Tendsto
          (fun n =>
            eLpNorm (fun x => ψ n x - (u x - k)) 2
              (volume.restrict (Metric.ball x₀ s)))
          atTop (nhds 0) ∧
        (∀ i : Fin d,
          Tendsto
            (fun n =>
              eLpNorm
                (fun x =>
                  (fderiv ℝ (ψ n) x) (EuclideanSpace.single i 1) - hu.weakGrad x i)
                2 (volume.restrict (Metric.ball x₀ s)))
            atTop (nhds 0)))
    (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hη_nonneg : ∀ x, 0 ≤ η x)
    (hη_eq_one : ∀ x ∈ Metric.ball x₀ r, η x = 1)
    (hη_bound : ∀ x, |η x| ≤ 1)
    (hCη : 0 ≤ Cη)
    (hη_grad_bound : ∀ x, ‖fderiv ℝ η x‖ ≤ Cη)
    (hη_sub_ball : tsupport η ⊆ Metric.ball x₀ s) :
    ∫ x in Metric.ball x₀ r,
        ‖(positivePartSub_memW1pWitness_on_ball hs hu k happroxBallShift).weakGrad x‖ ^ 2
          ∂volume ≤
      4 * ellipticityRatio A * Cη ^ 2 *
        ∫ x in Metric.ball x₀ s, |positivePartSub u k x| ^ 2 ∂volume := by
  let hw_trunc : MemW1pWitness 2 (positivePartSub u k) (Metric.ball x₀ s) :=
    positivePartSub_memW1pWitness_on_ball hs hu k happroxBallShift
  change
    ∫ x in Metric.ball x₀ r, ‖hw_trunc.weakGrad x‖ ^ 2 ∂volume ≤
      4 * ellipticityRatio A * Cη ^ 2 *
        ∫ x in Metric.ball x₀ s, |positivePartSub u k x| ^ 2 ∂volume
  exact
    deGiorgi_energy_estimate_on_concentricBalls_of_ballPosPart
      A hr hrs hsub hu hw_trunc hη hη_nonneg hη_eq_one hη_bound hCη
      hη_grad_bound hη_sub_ball

end WeightedPDE

/-- Chebyshev bound for the superlevel set `{u > λ}` using `(u-θ)₊`. -/
theorem superlevel_measureReal_le_integral_posPart
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {u : α → ℝ} {θ lam : ℝ}
    (hθl : θ < lam)
    (hint : Integrable (fun x => |positivePartSub u θ x| ^ 2) μ) :
    μ.real {x | lam < u x} ≤
      ((lam - θ) ^ 2)⁻¹ * ∫ x, |positivePartSub u θ x| ^ 2 ∂μ := by
  let f : α → ℝ := fun x => |positivePartSub u θ x| ^ 2
  let ε : ℝ := (lam - θ) ^ 2
  have hε_pos : 0 < ε := by
    dsimp [ε]
    nlinarith
  have hf_nonneg : 0 ≤ᵐ[μ] f := by
    refine Filter.Eventually.of_forall ?_
    intro x
    dsimp [f]
    positivity
  have hmarkov :
      ε * μ.real {x | ε ≤ f x} ≤ ∫ x, f x ∂μ := by
    simpa [f, ε] using
      (MeasureTheory.mul_meas_ge_le_integral_of_nonneg (μ := μ) hf_nonneg hint ε)
  have hsubset : {x | lam < u x} ⊆ {x | ε ≤ f x} := by
    intro x hx
    dsimp [f, ε]
    exact positivePartSub_sq_ge_gap_sq_of_lt hθl hx
  have hmono : μ.real {x | lam < u x} ≤ μ.real {x | ε ≤ f x} := by
    exact measureReal_mono hsubset
  have hmain : ε * μ.real {x | lam < u x} ≤ ∫ x, f x ∂μ := by
    calc
      ε * μ.real {x | lam < u x} ≤ ε * μ.real {x | ε ≤ f x} := by
        gcongr
      _ ≤ ∫ x, f x ∂μ := hmarkov
  have hdiv : μ.real {x | lam < u x} ≤ (∫ x, f x ∂μ) / ε := by
    refine (le_div_iff₀ hε_pos).2 ?_
    simpa [mul_comm, mul_left_comm, mul_assoc] using hmain
  simpa [div_eq_mul_inv, f, ε, mul_comm, mul_left_comm, mul_assoc] using hdiv

private lemma weighted_caccioppoli_pointwise
    {Λ η ζ E M v : ℝ}
    (hΛ : 0 < Λ)
    (hcoeff : |M| ^ 2 ≤ Λ * E) :
    2 * η * |v| * ζ * |M| ≤
      (1 / 2 : ℝ) * η ^ 2 * E + 2 * Λ * ζ ^ 2 * |v| ^ 2 := by
  let s := Real.sqrt (2 * Λ)
  have hs_pos : 0 < s := by
    dsimp [s]
    apply Real.sqrt_pos.2
    positivity
  have hs_ne : s ≠ 0 := ne_of_gt hs_pos
  have hs_sq : s ^ 2 = 2 * Λ := by
    dsimp [s]
    rw [Real.sq_sqrt]
    positivity
  have hyoung :
      2 * (η * |M| / s) * (s * ζ * |v|) ≤
        (η * |M| / s) ^ 2 + (s * ζ * |v|) ^ 2 := by
    nlinarith [sq_nonneg ((η * |M| / s) - (s * ζ * |v|))]
  have hcoeff' : η ^ 2 * |M| ^ 2 / (2 * Λ) ≤ (1 / 2 : ℝ) * η ^ 2 * E := by
    have hmul :
        (η ^ 2 / (2 * Λ)) * (|M| ^ 2) ≤ (η ^ 2 / (2 * Λ)) * (Λ * E) := by
      refine mul_le_mul_of_nonneg_left hcoeff ?_
      positivity
    have hfac : (η ^ 2 / (2 * Λ)) * (Λ * E) = (1 / 2 : ℝ) * η ^ 2 * E := by
      field_simp [hΛ.ne']
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hmul.trans_eq hfac
  have hmain :
      2 * η * |v| * ζ * |M| ≤ η ^ 2 * |M| ^ 2 / (2 * Λ) + 2 * Λ * ζ ^ 2 * |v| ^ 2 := by
    have hconv :
        2 * (η * |M| / s) * (s * ζ * |v|) =
          2 * η * |v| * ζ * |M| := by
      field_simp [hs_ne]
    have hsq1 :
        (η * |M| / s) ^ 2 = η ^ 2 * |M| ^ 2 / (2 * Λ) := by
      rw [div_pow, hs_sq]
      field_simp [hΛ.ne']
    have hsq2 :
        (s * ζ * |v|) ^ 2 = 2 * Λ * ζ ^ 2 * |v| ^ 2 := by
      rw [mul_pow, mul_pow, hs_sq]
    rwa [hconv, hsq1, hsq2] at hyoung
  have hsum :
      η ^ 2 * |M| ^ 2 / (2 * Λ) + 2 * Λ * ζ ^ 2 * |v| ^ 2 ≤
        (1 / 2 : ℝ) * η ^ 2 * E + 2 * Λ * ζ ^ 2 * |v| ^ 2 := by
    nlinarith [hcoeff']
  exact hmain.trans hsum

/-- Abstract absorption step for weighted Caccioppoli. -/
theorem weighted_caccioppoli_absorb
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {E M η ζ v : α → ℝ} {Λ : ℝ}
    (hΛ : 0 < Λ)
    (hcore :
      ∫ x, η x ^ 2 * E x ∂μ ≤ ∫ x, 2 * η x * |v x| * ζ x * |M x| ∂μ)
    (hcoeff : ∀ᵐ x ∂μ, |M x| ^ 2 ≤ Λ * E x)
    (hleft_int : Integrable (fun x => η x ^ 2 * E x) μ)
    (hcross_int : Integrable (fun x => 2 * η x * |v x| * ζ x * |M x|) μ)
    (hbound_int : Integrable (fun x => ζ x ^ 2 * |v x| ^ 2) μ) :
    ∫ x, η x ^ 2 * E x ∂μ ≤ 4 * Λ * ∫ x, ζ x ^ 2 * |v x| ^ 2 ∂μ := by
  have hupper_pt :
      ∀ᵐ x ∂μ,
        2 * η x * |v x| * ζ x * |M x| ≤
          (1 / 2 : ℝ) * η x ^ 2 * E x + 2 * Λ * ζ x ^ 2 * |v x| ^ 2 := by
    filter_upwards [hcoeff] with x hx
    exact weighted_caccioppoli_pointwise hΛ hx
  have hupper_int :
      Integrable (fun x => (1 / 2 : ℝ) * η x ^ 2 * E x + 2 * Λ * ζ x ^ 2 * |v x| ^ 2) μ := by
    simpa [mul_assoc, add_comm, add_left_comm, add_assoc] using
      (hleft_int.const_mul (1 / 2 : ℝ)).add (hbound_int.const_mul (2 * Λ))
  have hcross_bound :
      ∫ x, 2 * η x * |v x| * ζ x * |M x| ∂μ ≤
        ∫ x, (1 / 2 : ℝ) * η x ^ 2 * E x + 2 * Λ * ζ x ^ 2 * |v x| ^ 2 ∂μ := by
    refine integral_mono_ae hcross_int hupper_int ?_
    exact hupper_pt
  have hsplit :
      ∫ x, (1 / 2 : ℝ) * η x ^ 2 * E x + 2 * Λ * ζ x ^ 2 * |v x| ^ 2 ∂μ =
        (1 / 2 : ℝ) * ∫ x, η x ^ 2 * E x ∂μ + 2 * Λ * ∫ x, ζ x ^ 2 * |v x| ^ 2 ∂μ := by
    have hrewrite :
        (fun x => (1 / 2 : ℝ) * η x ^ 2 * E x + 2 * Λ * ζ x ^ 2 * |v x| ^ 2) =
          (fun x => ((1 / 2 : ℝ) * (η x ^ 2 * E x)) + ((2 * Λ) * (ζ x ^ 2 * |v x| ^ 2))) := by
      funext x
      ring
    rw [hrewrite, integral_add (hleft_int.const_mul (1 / 2 : ℝ)) (hbound_int.const_mul (2 * Λ))]
    rw [integral_const_mul, integral_const_mul]
  have hmain :
      ∫ x, η x ^ 2 * E x ∂μ ≤
        (1 / 2 : ℝ) * ∫ x, η x ^ 2 * E x ∂μ + 2 * Λ * ∫ x, ζ x ^ 2 * |v x| ^ 2 ∂μ := by
    calc
      ∫ x, η x ^ 2 * E x ∂μ ≤ ∫ x, 2 * η x * |v x| * ζ x * |M x| ∂μ := hcore
      _ ≤ ∫ x, (1 / 2 : ℝ) * η x ^ 2 * E x + 2 * Λ * ζ x ^ 2 * |v x| ^ 2 ∂μ := hcross_bound
      _ = (1 / 2 : ℝ) * ∫ x, η x ^ 2 * E x ∂μ + 2 * Λ * ∫ x, ζ x ^ 2 * |v x| ^ 2 ∂μ := hsplit
  linarith

/-- Localization step for weighted Caccioppoli on nested sets. -/
theorem caccioppoli_localize_on_subset
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {s t : Set α} (hst : s ⊆ t)
    {G v η ζ : α → ℝ} {C_coeff C_grad : ℝ}
    (hs_meas : MeasurableSet s) (ht_meas : MeasurableSet t)
    (hη_eq_one : ∀ x ∈ s, η x = 1)
    (hC_coeff : 0 ≤ C_coeff) (hC_grad : 0 ≤ C_grad)
    (hζ_nonneg : ∀ x ∈ t, 0 ≤ ζ x)
    (hζ_bound : ∀ x ∈ t, ζ x ≤ C_grad)
    (h_weighted :
      ∫ x in t, η x ^ 2 * ‖G x‖ ^ 2 ∂μ ≤
        C_coeff * ∫ x in t, ζ x ^ 2 * |v x| ^ 2 ∂μ)
    (hweighted_int : IntegrableOn (fun x => η x ^ 2 * ‖G x‖ ^ 2) t μ)
    (hzv_int : IntegrableOn (fun x => ζ x ^ 2 * |v x| ^ 2) t μ)
    (hv_sq_int : IntegrableOn (fun x => |v x| ^ 2) t μ) :
    ∫ x in s, ‖G x‖ ^ 2 ∂μ ≤
      C_coeff * C_grad ^ 2 * ∫ x in t, |v x| ^ 2 ∂μ := by
  have hleft_eq :
      ∫ x in s, ‖G x‖ ^ 2 ∂μ = ∫ x in s, η x ^ 2 * ‖G x‖ ^ 2 ∂μ := by
    refine integral_congr_ae ?_
    refine (ae_restrict_iff' (μ := μ) ?_).2 ?_
    · exact hs_meas
    · filter_upwards with x hx
      simp [hη_eq_one x hx]
  have hweighted_nonneg : ∀ x, 0 ≤ η x ^ 2 * ‖G x‖ ^ 2 := by
    intro x
    positivity
  have hleft_mono :
      ∫ x in s, η x ^ 2 * ‖G x‖ ^ 2 ∂μ ≤ ∫ x in t, η x ^ 2 * ‖G x‖ ^ 2 ∂μ := by
    exact setIntegral_mono_set hweighted_int
      (ae_of_all _ hweighted_nonneg) (ae_of_all _ hst)
  have hgrad_pt :
      ∀ x ∈ t, ζ x ^ 2 * |v x| ^ 2 ≤ C_grad ^ 2 * |v x| ^ 2 := by
    intro x hx
    have hsq : ζ x ^ 2 ≤ C_grad ^ 2 := by
      nlinarith [hζ_nonneg x hx, hζ_bound x hx, hC_grad]
    apply mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
    exact hsq
  have hgrad_int :
      IntegrableOn (fun x => C_grad ^ 2 * |v x| ^ 2) t μ := by
    simpa using hv_sq_int.const_mul (C_grad ^ 2)
  have hgrad_bound :
      ∫ x in t, ζ x ^ 2 * |v x| ^ 2 ∂μ ≤ ∫ x in t, C_grad ^ 2 * |v x| ^ 2 ∂μ := by
    refine integral_mono_ae hzv_int hgrad_int ?_
    refine (ae_restrict_iff' (μ := μ) ?_).2 ?_
    · exact ht_meas
    · filter_upwards with x hx
      exact hgrad_pt x hx
  have hconst_mul :
      ∫ x in t, C_grad ^ 2 * |v x| ^ 2 ∂μ =
        C_grad ^ 2 * ∫ x in t, |v x| ^ 2 ∂μ := by
    rw [integral_const_mul]
  calc
    ∫ x in s, ‖G x‖ ^ 2 ∂μ = ∫ x in s, η x ^ 2 * ‖G x‖ ^ 2 ∂μ := hleft_eq
    _ ≤ ∫ x in t, η x ^ 2 * ‖G x‖ ^ 2 ∂μ := hleft_mono
    _ ≤ C_coeff * ∫ x in t, ζ x ^ 2 * |v x| ^ 2 ∂μ := h_weighted
    _ ≤ C_coeff * ∫ x in t, C_grad ^ 2 * |v x| ^ 2 ∂μ := by
      gcongr
    _ = C_coeff * C_grad ^ 2 * ∫ x in t, |v x| ^ 2 ∂μ := by
      rw [hconst_mul]
      ring

/-- Abstract real-variable combination step for De Giorgi pre-iteration. -/
theorem deGiorgi_preiter_abstract
    {d : ℕ} (hd : 0 < (d : ℝ))
    {Ilam Iθ G m Csob Cenergy θ lam : ℝ}
    (hCsob : 0 ≤ Csob) (hCenergy : 0 ≤ Cenergy)
    (hIθ : 0 ≤ Iθ) (hm : 0 ≤ m)
    (hsob : Ilam ≤ Csob * G * m ^ (2 / (d : ℝ)))
    (hmeasure : m ≤ ((lam - θ) ^ 2)⁻¹ * Iθ)
    (henergy : G ≤ Cenergy * Iθ) :
    Ilam ≤
      Csob * Cenergy * ((((lam - θ) ^ 2)⁻¹ * Iθ) ^ (2 / (d : ℝ))) * Iθ := by
  have hexp_nonneg : 0 ≤ 2 / (d : ℝ) := by positivity
  have hm_pow :
      m ^ (2 / (d : ℝ)) ≤ ((((lam - θ) ^ 2)⁻¹ * Iθ) ^ (2 / (d : ℝ))) := by
    exact Real.rpow_le_rpow hm hmeasure hexp_nonneg
  have hGI :
      G * m ^ (2 / (d : ℝ)) ≤
        (Cenergy * Iθ) * ((((lam - θ) ^ 2)⁻¹ * Iθ) ^ (2 / (d : ℝ))) := by
    exact mul_le_mul henergy hm_pow (by positivity) (by positivity)
  calc
    Ilam ≤ Csob * (G * m ^ (2 / (d : ℝ))) := by
      simpa [mul_assoc] using hsob
    _ ≤ Csob * ((Cenergy * Iθ) * ((((lam - θ) ^ 2)⁻¹ * Iθ) ^ (2 / (d : ℝ)))) := by
      exact mul_le_mul_of_nonneg_left hGI hCsob
    _ = Csob * Cenergy * ((((lam - θ) ^ 2)⁻¹ * Iθ) ^ (2 / (d : ℝ))) * Iθ := by
      ring

/-- Packaged pre-iteration step after Sobolev, energy, and Chebyshev inputs. -/
theorem deGiorgi_preiter_of_energy
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {d : ℕ} (hd : 0 < (d : ℝ))
    {u : α → ℝ} {θ lam : ℝ}
    {Ilam Iθ G Csob Cenergy : ℝ}
    (hθl : θ < lam)
    (hCsob : 0 ≤ Csob) (hCenergy : 0 ≤ Cenergy)
    (hIθ : 0 ≤ Iθ)
    (hint : Integrable (fun x => |positivePartSub u θ x| ^ 2) μ)
    (hsob :
      Ilam ≤ Csob * G * (μ.real {x | lam < u x}) ^ (2 / (d : ℝ)))
    (henergy :
      G ≤ Cenergy * Iθ)
    (hIθ_bound :
      ∫ x, |positivePartSub u θ x| ^ 2 ∂μ ≤ Iθ) :
    Ilam ≤
      Csob * Cenergy * ((((lam - θ) ^ 2)⁻¹ * Iθ) ^ (2 / (d : ℝ))) * Iθ := by
  have hm_nonneg : 0 ≤ μ.real {x | lam < u x} := measureReal_nonneg
  have hmeasure0 :
      μ.real {x | lam < u x} ≤
        ((lam - θ) ^ 2)⁻¹ * ∫ x, |positivePartSub u θ x| ^ 2 ∂μ :=
    superlevel_measureReal_le_integral_posPart hθl hint
  have hmeasure :
      μ.real {x | lam < u x} ≤ ((lam - θ) ^ 2)⁻¹ * Iθ := by
    calc
      μ.real {x | lam < u x}
          ≤ ((lam - θ) ^ 2)⁻¹ * ∫ x, |positivePartSub u θ x| ^ 2 ∂μ := hmeasure0
      _ ≤ ((lam - θ) ^ 2)⁻¹ * Iθ := by
        gcongr
  exact deGiorgi_preiter_abstract hd hCsob hCenergy hIθ hm_nonneg hsob hmeasure henergy

end DeGiorgi
