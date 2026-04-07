import DeGiorgi.SobolevSpace.WeakDerivatives

/-!
# Chapter 02: Sobolev Witness Layer

This module introduces `W^{1,p}` membership predicates, explicit witnesses, and
zero-trace witness operations.
-/

noncomputable section

open MeasureTheory Metric Filter Topology Set Function Matrix
open scoped ENNReal NNReal Convolution Pointwise

namespace DeGiorgi

variable {d : ℕ} [NeZero d]

local notation "E" => EuclideanSpace ℝ (Fin d)

/-- `MemW1p p f Ω μ` means `f ∈ W^{1,p}(Ω)` with respect to `μ`. -/
def MemW1p (p : ℝ≥0∞) (f : E → ℝ) (Ω : Set E)
    (μ : Measure E := volume) : Prop :=
  MemLp f p (μ.restrict Ω) ∧
  ∀ i : Fin d, ∃ g : E → ℝ,
    MemLp g p (μ.restrict Ω) ∧ HasWeakPartialDeriv i g f Ω

/-- An explicit `W^{1,p}` witness carrying the weak gradient. -/
structure MemW1pWitness (p : ℝ≥0∞) (f : E → ℝ) (Ω : Set E)
    (μ : Measure E := volume) where
  /-- The function itself lies in `L^p(Ω)`. -/
  memLp : MemLp f p (μ.restrict Ω)
  /-- The weak gradient field. -/
  weakGrad : E → E
  /-- Each weak-gradient component lies in `L^p(Ω)`. -/
  weakGrad_component_memLp : ∀ i : Fin d,
    MemLp (fun x => weakGrad x i) p (μ.restrict Ω)
  /-- The displayed gradient is indeed a weak gradient. -/
  isWeakGrad : HasWeakGrad weakGrad f Ω

/-- `H¹(Ω) = W^{1,2}(Ω)`. -/
abbrev MemH1 (f : E → ℝ) (Ω : Set E) (μ : Measure E := volume) :=
  MemW1p 2 f Ω μ

/-- `W₀^{1,p}(Ω)` defined via approximation by smooth compactly supported
functions with convergence in both the function and gradient `L^p` norms. -/
def MemW01p (p : ℝ≥0∞) (f : E → ℝ) (Ω : Set E)
    (μ : Measure E := volume) : Prop :=
  MemW1p p f Ω μ ∧
  ∃ (hw : MemW1pWitness p f Ω μ) (φ : ℕ → E → ℝ),
    (∀ n, ContDiff ℝ (⊤ : ℕ∞) (φ n)) ∧
    (∀ n, HasCompactSupport (φ n)) ∧
    (∀ n, tsupport (φ n) ⊆ Ω) ∧
    Tendsto (fun n => eLpNorm (fun x => φ n x - f x) p (μ.restrict Ω))
      atTop (nhds 0) ∧
    ∀ i : Fin d,
      Tendsto (fun n => eLpNorm
        (fun x => (fderiv ℝ (φ n) x) (EuclideanSpace.single i 1) - hw.weakGrad x i)
        p (μ.restrict Ω))
        atTop (nhds 0)

/-- `H₀¹(Ω) = W₀^{1,2}(Ω)`. -/
abbrev MemH01 (f : E → ℝ) (Ω : Set E) (μ : Measure E := volume) :=
  MemW01p 2 f Ω μ

/-- Choose an explicit weak-gradient witness from `W^{1,p}` membership. -/
noncomputable def MemW1p.someWitness
    {p : ℝ≥0∞} {Ω : Set E} {f : E → ℝ} {μ : Measure E}
    (hf : MemW1p p f Ω μ) :
    MemW1pWitness p f Ω μ := by
  rcases hf with ⟨hf_memLp, hf_grad⟩
  choose g hg_memLp hg_weak using hf_grad
  let G : E → E := fun x => WithLp.toLp 2 fun i => g i x
  exact
    { memLp := hf_memLp
      weakGrad := G
      weakGrad_component_memLp := hg_memLp
      isWeakGrad := hg_weak }

omit [NeZero d] in
/-- Forget the explicit gradient from a `W^{1,p}` witness. -/
theorem MemW1pWitness.memW1p
    {p : ℝ≥0∞} {Ω : Set E} {f : E → ℝ} {μ : Measure E}
    (hw : MemW1pWitness p f Ω μ) :
    MemW1p p f Ω μ := by
  refine ⟨hw.memLp, ?_⟩
  intro i
  exact ⟨fun x => hw.weakGrad x i, hw.weakGrad_component_memLp i, hw.isWeakGrad i⟩

/-- Add two `W^{1,2}` witnesses on the same domain. -/
noncomputable def MemW1pWitness.add
    {Ω : Set E} {u v : E → ℝ}
    (hu : MemW1pWitness 2 u Ω)
    (hv : MemW1pWitness 2 v Ω) :
    MemW1pWitness 2 (fun x => u x + v x) Ω where
  memLp := hu.memLp.add hv.memLp
  weakGrad := fun x => hu.weakGrad x + hv.weakGrad x
  weakGrad_component_memLp := by
    intro i
    simpa using (hu.weakGrad_component_memLp i).add (hv.weakGrad_component_memLp i)
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
    have hgu_int : Integrable (fun x => hu.weakGrad x i * φ x) (volume.restrict Ω) := by
      have hgu_loc : LocallyIntegrable (fun x => hu.weakGrad x i) (volume.restrict Ω) :=
        (hu.weakGrad_component_memLp i).locallyIntegrable (by norm_num)
      simpa [smul_eq_mul] using
        hgu_loc.integrable_smul_right_of_hasCompactSupport hφ.continuous hφ_supp
    have hgv_int : Integrable (fun x => hv.weakGrad x i * φ x) (volume.restrict Ω) := by
      have hgv_loc : LocallyIntegrable (fun x => hv.weakGrad x i) (volume.restrict Ω) :=
        (hv.weakGrad_component_memLp i).locallyIntegrable (by norm_num)
      simpa [smul_eq_mul] using
        hgv_loc.integrable_smul_right_of_hasCompactSupport hφ.continuous hφ_supp
    have hfun :
        (fun x => (u x + v x) * (fderiv ℝ φ x) ei) =
          (fun x => u x * (fderiv ℝ φ x) ei + v x * (fderiv ℝ φ x) ei) := by
      ext x
      ring
    have hgrad :
        (fun x => (hu.weakGrad x i + hv.weakGrad x i) * φ x) =
          (fun x => hu.weakGrad x i * φ x + hv.weakGrad x i * φ x) := by
      ext x
      ring
    calc
      ∫ x in Ω, (u x + v x) * (fderiv ℝ φ x) ei
          = (-∫ x in Ω, hu.weakGrad x i * φ x) + (-∫ x in Ω, hv.weakGrad x i * φ x) := by
            rw [hfun, integral_add hu_int hv_int, hu_eq, hv_eq]
      _ = -((∫ x in Ω, hu.weakGrad x i * φ x) + (∫ x in Ω, hv.weakGrad x i * φ x)) := by
            ring
      _ = -∫ x in Ω, (hu.weakGrad x i * φ x + hv.weakGrad x i * φ x) := by
            rw [integral_add hgu_int hgv_int]
      _ = -∫ x in Ω, ((fun x => hu.weakGrad x + hv.weakGrad x) x i * φ x) := by
            congr 2
            ext x
            simpa [Pi.add_apply] using (congrFun hgrad x).symm

noncomputable def MemW1pWitness.restrict
    {p : ℝ≥0∞} {Ω Ω' : Set E} {f : E → ℝ}
    (hΩ' : IsOpen Ω')
    (hsub : Ω' ⊆ Ω)
    (hw : MemW1pWitness p f Ω) :
    MemW1pWitness p f Ω' where
  memLp := hw.memLp.mono_measure (Measure.restrict_mono_set volume hsub)
  weakGrad := hw.weakGrad
  weakGrad_component_memLp := by
    intro i
    exact (hw.weakGrad_component_memLp i).mono_measure (Measure.restrict_mono_set volume hsub)
  isWeakGrad := by
    intro i
    exact HasWeakPartialDeriv.restrict hΩ' hsub (hw.isWeakGrad i)

/-- Multiply a `W^{1,2}` witness by a scalar. -/
noncomputable def MemW1pWitness.smul
    {Ω : Set E} {u : E → ℝ}
    (hu : MemW1pWitness 2 u Ω) (c : ℝ) :
    MemW1pWitness 2 (fun x => c * u x) Ω where
  memLp := hu.memLp.const_mul c
  weakGrad := fun x => c • hu.weakGrad x
  weakGrad_component_memLp := by
    intro i
    simpa [Pi.smul_apply, smul_eq_mul] using (hu.weakGrad_component_memLp i).const_mul c
  isWeakGrad := by
    intro i φ hφ hφ_supp hφ_sub
    let ei : E := EuclideanSpace.single i (1 : ℝ)
    have hu_eq := hu.isWeakGrad i φ hφ hφ_supp hφ_sub
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
    have hgu_int : Integrable (fun x => hu.weakGrad x i * φ x) (volume.restrict Ω) := by
      have hgu_loc : LocallyIntegrable (fun x => hu.weakGrad x i) (volume.restrict Ω) :=
        (hu.weakGrad_component_memLp i).locallyIntegrable (by norm_num)
      simpa [smul_eq_mul] using
        hgu_loc.integrable_smul_right_of_hasCompactSupport hφ.continuous hφ_supp
    calc
      ∫ x in Ω, (c * u x) * (fderiv ℝ φ x) ei
          = ∫ x in Ω, c * (u x * (fderiv ℝ φ x) ei) := by
              congr with x
              ring
      _ = c * ∫ x in Ω, u x * (fderiv ℝ φ x) ei := by
            rw [integral_const_mul]
      _ = c * (-∫ x in Ω, hu.weakGrad x i * φ x) := by rw [hu_eq]
      _ = -(c * ∫ x in Ω, hu.weakGrad x i * φ x) := by ring
      _ = -∫ x in Ω, c * (hu.weakGrad x i * φ x) := by
            rw [integral_const_mul]
      _ = -∫ x in Ω, (c * hu.weakGrad x i) * φ x := by
            congr 2
            ext x
            ring
      _ = -∫ x in Ω, ((fun x => c • hu.weakGrad x) x i * φ x) := by
            simp [smul_eq_mul]

/-- Multiply a `W^{1,p}` witness by a bounded smooth scalar factor. -/
noncomputable def MemW1pWitness.mul_smooth_bounded_p
    {p : ℝ≥0∞} (hp : 1 ≤ p)
    {Ω : Set E} (hΩ : IsOpen Ω)
    {u η : E → ℝ} (hw : MemW1pWitness p u Ω)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    {C₀ C₁ : ℝ}
    (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁)
    (hη_bound : ∀ x, |η x| ≤ C₀)
    (hη_grad_bound : ∀ x, ‖fderiv ℝ η x‖ ≤ C₁) :
    MemW1pWitness p (fun x => η x * u x) Ω where
  memLp := by
    let _ := hC₀
    let _ := hC₁
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
    have hfirst : MemLp (fun x => η x * hw.weakGrad x i) p (volume.restrict Ω) := by
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
        MemLp (fun x => (fderiv ℝ η x) (EuclideanSpace.single i 1) * u x) p
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
      (hw.memLp.locallyIntegrable hp)
      ((hw.weakGrad_component_memLp i).locallyIntegrable hp)

/-- A smooth compactly supported function on `ℝ^d` carries a canonical
`W^{1,p}` witness on the whole space. -/
noncomputable def MemW1pWitness.of_contDiff_hasCompactSupport
    {p : ℝ≥0∞} {f : E → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hf_supp : HasCompactSupport f) :
    MemW1pWitness p f Set.univ where
  memLp := hf.continuous.memLp_of_hasCompactSupport hf_supp
  weakGrad := fun x =>
    WithLp.toLp 2 fun i => (fderiv ℝ f x) (EuclideanSpace.single i 1)
  weakGrad_component_memLp := by
    intro i
    have hderiv_smooth : ContDiff ℝ (⊤ : ℕ∞)
        (fun x => (fderiv ℝ f x) (EuclideanSpace.single i 1)) :=
      (hf.fderiv_right (m := (⊤ : ℕ∞)) (by norm_cast)).clm_apply contDiff_const
    exact hderiv_smooth.continuous.memLp_of_hasCompactSupport (hf_supp.fderiv_apply (𝕜 := ℝ) _)
  isWeakGrad := by
    intro i
    simpa [PiLp.toLp_apply] using
      (HasWeakPartialDeriv.of_contDiff (Ω := Set.univ) (i := i)
        (f := f) isOpen_univ (hf.of_le (by norm_cast)))

omit [NeZero d] in
/-- The weak gradient field of a witness lies in `L^p(Ω)` as a Euclidean-space
valued map. -/
theorem MemW1pWitness.weakGrad_memLp
    {p : ℝ≥0∞} {Ω : Set E} {f : E → ℝ} {μ : Measure E}
    (hw : MemW1pWitness p f Ω μ) :
    MemLp hw.weakGrad p (μ.restrict Ω) := by
  refine MemLp.of_eval_piLp ?_
  intro i
  simpa using hw.weakGrad_component_memLp i

/-- The Euclidean norm of the weak gradient lies in `L^p(Ω)`. -/
theorem MemW1pWitness.weakGrad_norm_memLp
    {p : ℝ≥0∞} {Ω : Set E} {f : E → ℝ} {μ : Measure E}
    (hw : MemW1pWitness p f Ω μ) :
    MemLp (fun x => ‖hw.weakGrad x‖) p (μ.restrict Ω) := by
  let _ := (inferInstance : NeZero d)
  exact hw.weakGrad_memLp.norm

omit [NeZero d] in
/-- Forget the zero-trace approximation data from a `W₀^{1,p}` witness. -/
theorem MemW01p.memW1p
    {p : ℝ≥0∞} {Ω : Set E} {f : E → ℝ} {μ : Measure E}
    (hf : MemW01p p f Ω μ) :
    MemW1p p f Ω μ :=
  hf.1

/-- `H₀¹(Ω)` is closed under addition. -/
theorem MemW01p.add
    {Ω : Set E} {u v : E → ℝ}
    (hu : MemW01p 2 u Ω) (hv : MemW01p 2 v Ω) :
    MemW01p 2 (fun x => u x + v x) Ω := by
  let _ := (inferInstance : NeZero d)
  rcases hu with ⟨_, hwu, φu, hφu_smooth, hφu_compact, hφu_sub, hφu_fun, hφu_grad⟩
  rcases hv with ⟨_, hwv, φv, hφv_smooth, hφv_compact, hφv_sub, hφv_fun, hφv_grad⟩
  refine ⟨(hwu.add hwv).memW1p, hwu.add hwv, fun n x => φu n x + φv n x, ?_, ?_, ?_, ?_, ?_⟩
  · intro n
    exact (hφu_smooth n).add (hφv_smooth n)
  · intro n
    exact (hφu_compact n).add (hφv_compact n)
  · intro n
    exact (tsupport_add (φu n) (φv n)).trans <| union_subset (hφu_sub n) (hφv_sub n)
  ·
    have hupper :
        ∀ n,
          eLpNorm (fun x => (φu n x + φv n x) - (u x + v x)) 2 (volume.restrict Ω) ≤
            eLpNorm (fun x => φu n x - u x) 2 (volume.restrict Ω) +
              eLpNorm (fun x => φv n x - v x) 2 (volume.restrict Ω) := by
      intro n
      have hφu_mem : MemLp (φu n) 2 (volume.restrict Ω) :=
        ((hφu_smooth n).continuous.memLp_of_hasCompactSupport (hφu_compact n)).restrict Ω
      have hφv_mem : MemLp (φv n) 2 (volume.restrict Ω) :=
        ((hφv_smooth n).continuous.memLp_of_hasCompactSupport (hφv_compact n)).restrict Ω
      have hdu_mem : MemLp (fun x => φu n x - u x) 2 (volume.restrict Ω) :=
        hφu_mem.sub hwu.memLp
      have hdv_mem : MemLp (fun x => φv n x - v x) 2 (volume.restrict Ω) :=
        hφv_mem.sub hwv.memLp
      have hEq :
          (fun x => (φu n x + φv n x) - (u x + v x)) =
            (fun x => (φu n x - u x) + (φv n x - v x)) := by
        ext x
        ring
      rw [hEq]
      exact eLpNorm_add_le hdu_mem.aestronglyMeasurable hdv_mem.aestronglyMeasurable (by norm_num)
    have hsum :
        Tendsto
          (fun n =>
            eLpNorm (fun x => φu n x - u x) 2 (volume.restrict Ω) +
              eLpNorm (fun x => φv n x - v x) 2 (volume.restrict Ω))
          atTop (nhds (0 + 0)) :=
      hφu_fun.add hφv_fun
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_ (fun n => zero_le _) hupper
    simpa using hsum
  · intro i
    have hupper :
        ∀ n,
          eLpNorm
              (fun x =>
                (fderiv ℝ (fun y => φu n y + φv n y) x) (EuclideanSpace.single i 1) -
                  (hwu.add hwv).weakGrad x i)
              2 (volume.restrict Ω) ≤
            eLpNorm
                (fun x => (fderiv ℝ (φu n) x) (EuclideanSpace.single i 1) - hwu.weakGrad x i)
                2 (volume.restrict Ω) +
              eLpNorm
                (fun x => (fderiv ℝ (φv n) x) (EuclideanSpace.single i 1) - hwv.weakGrad x i)
                2 (volume.restrict Ω) := by
      intro n
      let ei : E := EuclideanSpace.single i (1 : ℝ)
      have hderiv_u_smooth : ContDiff ℝ (⊤ : ℕ∞)
          (fun x => (fderiv ℝ (φu n) x) ei) :=
        ((hφu_smooth n).fderiv_right (m := (⊤ : ℕ∞)) (by norm_cast)).clm_apply contDiff_const
      have hderiv_v_smooth : ContDiff ℝ (⊤ : ℕ∞)
          (fun x => (fderiv ℝ (φv n) x) ei) :=
        ((hφv_smooth n).fderiv_right (m := (⊤ : ℕ∞)) (by norm_cast)).clm_apply contDiff_const
      have hderiv_u_mem : MemLp (fun x => (fderiv ℝ (φu n) x) ei) 2 (volume.restrict Ω) :=
        (hderiv_u_smooth.continuous.memLp_of_hasCompactSupport ((hφu_compact n).fderiv_apply (𝕜 := ℝ) ei)).restrict Ω
      have hderiv_v_mem : MemLp (fun x => (fderiv ℝ (φv n) x) ei) 2 (volume.restrict Ω) :=
        (hderiv_v_smooth.continuous.memLp_of_hasCompactSupport ((hφv_compact n).fderiv_apply (𝕜 := ℝ) ei)).restrict Ω
      have hdu_mem :
          MemLp (fun x => (fderiv ℝ (φu n) x) ei - hwu.weakGrad x i) 2 (volume.restrict Ω) :=
        hderiv_u_mem.sub (hwu.weakGrad_component_memLp i)
      have hdv_mem :
          MemLp (fun x => (fderiv ℝ (φv n) x) ei - hwv.weakGrad x i) 2 (volume.restrict Ω) :=
        hderiv_v_mem.sub (hwv.weakGrad_component_memLp i)
      have hEq :
          (fun x =>
            (fderiv ℝ (fun y => φu n y + φv n y) x) ei - (hwu.add hwv).weakGrad x i) =
            (fun x =>
              ((fderiv ℝ (φu n) x) ei - hwu.weakGrad x i) +
                ((fderiv ℝ (φv n) x) ei - hwv.weakGrad x i)) := by
        ext x
        have hfd :
            fderiv ℝ (fun y => φu n y + φv n y) x =
              fderiv ℝ (φu n) x + fderiv ℝ (φv n) x := by
          have hu_diff : DifferentiableAt ℝ (φu n) x :=
            ((hφu_smooth n).contDiffAt).differentiableAt (by norm_num)
          have hv_diff : DifferentiableAt ℝ (φv n) x :=
            ((hφv_smooth n).contDiffAt).differentiableAt (by norm_num)
          exact fderiv_add hu_diff hv_diff
        simp [ei, MemW1pWitness.add, hfd]
        ring
      rw [hEq]
      exact eLpNorm_add_le hdu_mem.aestronglyMeasurable hdv_mem.aestronglyMeasurable (by norm_num)
    have hsum :
        Tendsto
          (fun n =>
            eLpNorm
                (fun x => (fderiv ℝ (φu n) x) (EuclideanSpace.single i 1) - hwu.weakGrad x i)
                2 (volume.restrict Ω) +
              eLpNorm
                (fun x => (fderiv ℝ (φv n) x) (EuclideanSpace.single i 1) - hwv.weakGrad x i)
                2 (volume.restrict Ω))
          atTop (nhds (0 + 0)) :=
      (hφu_grad i).add (hφv_grad i)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_ (fun n => zero_le _) hupper
    simpa using hsum

/-- `H₀¹(Ω)` is closed under scalar multiplication. -/
theorem MemW01p.smul
    {Ω : Set E} {u : E → ℝ} (c : ℝ)
    (hu : MemW01p 2 u Ω) :
    MemW01p 2 (fun x => c * u x) Ω := by
  let _ := (inferInstance : NeZero d)
  rcases hu with ⟨_, hwu, φ, hφ_smooth, hφ_compact, hφ_sub, hφ_fun, hφ_grad⟩
  refine ⟨(hwu.smul c).memW1p, hwu.smul c, fun n x => c * φ n x, ?_, ?_, ?_, ?_, ?_⟩
  · intro n
    simpa [smul_eq_mul] using (contDiff_const.mul (hφ_smooth n))
  · intro n
    simpa [Pi.smul_apply, smul_eq_mul] using (hφ_compact n).smul_left (f := fun _ : E => c)
  · intro n
    simpa [Pi.smul_apply, smul_eq_mul] using
      (tsupport_smul_subset_right (fun _ : E => c) (φ n)).trans (hφ_sub n)
  ·
    have hscaled :
        Tendsto
          (fun n =>
            ‖c‖ₑ * eLpNorm (fun x => φ n x - u x) 2 (volume.restrict Ω))
          atTop (nhds (‖c‖ₑ * 0)) :=
      ENNReal.Tendsto.const_mul hφ_fun (Or.inr ENNReal.coe_ne_top)
    have hEq :
        (fun n => eLpNorm (fun x => c * φ n x - c * u x) 2 (volume.restrict Ω)) =
          (fun n => ‖c‖ₑ * eLpNorm (fun x => φ n x - u x) 2 (volume.restrict Ω)) := by
      funext n
      have hfun :
          (fun x => c * φ n x - c * u x) = c • (fun x => φ n x - u x) := by
        ext x
        simp [Pi.smul_apply, smul_eq_mul]
        ring
      rw [hfun, eLpNorm_const_smul]
    rw [hEq]
    simpa using hscaled
  · intro i
    have hscaled :
        Tendsto
          (fun n =>
            ‖c‖ₑ *
              eLpNorm
                (fun x => (fderiv ℝ (φ n) x) (EuclideanSpace.single i 1) - hwu.weakGrad x i)
                2 (volume.restrict Ω))
          atTop (nhds (‖c‖ₑ * 0)) :=
      ENNReal.Tendsto.const_mul (hφ_grad i) (Or.inr ENNReal.coe_ne_top)
    have hEq :
        (fun n =>
          eLpNorm
            (fun x =>
              (fderiv ℝ (fun y => c * φ n y) x) (EuclideanSpace.single i 1) -
                (hwu.smul c).weakGrad x i)
            2 (volume.restrict Ω)) =
          (fun n =>
            ‖c‖ₑ *
              eLpNorm
                (fun x => (fderiv ℝ (φ n) x) (EuclideanSpace.single i 1) - hwu.weakGrad x i)
                2 (volume.restrict Ω)) := by
      funext n
      have hfun :
          (fun x =>
            (fderiv ℝ (fun y => c * φ n y) x) (EuclideanSpace.single i 1) -
              (hwu.smul c).weakGrad x i) =
            c • (fun x =>
              (fderiv ℝ (φ n) x) (EuclideanSpace.single i 1) - hwu.weakGrad x i) := by
        ext x
        have hfd : fderiv ℝ (fun y => c * φ n y) x = c • fderiv ℝ (φ n) x := by
          simpa [smul_eq_mul] using congrFun (fderiv_const_smul_field (𝕜 := ℝ) (f := φ n) c) x
        simp [MemW1pWitness.smul, Pi.smul_apply, smul_eq_mul, hfd]
        ring
      rw [hfun, eLpNorm_const_smul]
    rw [hEq]
    simpa using hscaled

/-- `H₀¹(Ω)` is closed under subtraction. -/
theorem MemW01p.sub
    {Ω : Set E} {u v : E → ℝ}
    (hu : MemW01p 2 u Ω) (hv : MemW01p 2 v Ω) :
    MemW01p 2 (fun x => u x - v x) Ω := by
  simpa [sub_eq_add_neg, Pi.smul_apply, smul_eq_mul] using hu.add (hv.smul (-1))

/-- A smooth compactly supported function belongs to `W₀^{1,p}(ℝ^d)`. -/
theorem memW01p_of_contDiff_hasCompactSupport
    {p : ℝ≥0∞} {f : E → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hf_supp : HasCompactSupport f) :
    MemW01p p f Set.univ := by
  let _ := (inferInstance : NeZero d)
  let hw : MemW1pWitness p f Set.univ :=
    MemW1pWitness.of_contDiff_hasCompactSupport (p := p) hf hf_supp
  refine ⟨hw.memW1p, hw, fun _ => f, ?_, ?_, ?_, ?_, ?_⟩
  · intro n
    exact hf
  · intro n
    exact hf_supp
  · intro n
    simp
  · simp
  · intro i
    simp [hw, MemW1pWitness.of_contDiff_hasCompactSupport]

/-- A smooth compactly supported function whose support is contained in an open
set belongs to `W₀^{1,p}` on that set. -/
theorem memW01p_of_contDiff_hasCompactSupport_subset
    {p : ℝ≥0∞} {Ω : Set E} (hΩ : IsOpen Ω) {f : E → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hf_supp : HasCompactSupport f)
    (hf_sub : tsupport f ⊆ Ω) :
    MemW01p p f Ω := by
  let _ := (inferInstance : NeZero d)
  let hw : MemW1pWitness p f Ω :=
    { memLp := (hf.continuous.memLp_of_hasCompactSupport hf_supp).restrict Ω
      weakGrad := fun x =>
        WithLp.toLp 2 fun i => (fderiv ℝ f x) (EuclideanSpace.single i 1)
      weakGrad_component_memLp := by
        intro i
        have hderiv_smooth : ContDiff ℝ (⊤ : ℕ∞)
            (fun x => (fderiv ℝ f x) (EuclideanSpace.single i 1)) :=
          (hf.fderiv_right (m := (⊤ : ℕ∞)) (by norm_cast)).clm_apply contDiff_const
        exact (hderiv_smooth.continuous.memLp_of_hasCompactSupport
          (hf_supp.fderiv_apply (𝕜 := ℝ) _)).restrict Ω
      isWeakGrad := by
        intro i
        simpa [PiLp.toLp_apply] using
          (HasWeakPartialDeriv.of_contDiff (Ω := Ω) (i := i)
            (f := f) hΩ (hf.of_le (by norm_cast))) }
  refine ⟨hw.memW1p, hw, fun _ => f, ?_, ?_, ?_, ?_, ?_⟩
  · intro n
    exact hf
  · intro n
    exact hf_supp
  · intro n
    exact hf_sub
  · simp
  · intro i
    simp [hw]

end DeGiorgi
