import DeGiorgi.WeakFormulation.SolutionInterfaces

/-!
# Weak Formulation: Smooth Test Functions

This module packages the smooth compactly supported test functions used to
bridge between classical gradients and the Sobolev weak-formulation layer.
-/

noncomputable section

open MeasureTheory Filter
open scoped InnerProductSpace

namespace DeGiorgi

variable {d : ℕ} [NeZero d]

local notation "E" => AmbientSpace d

/-! ## Smooth Test Functions And L² Coefficient Operator -/

/-- Smooth compactly supported test functions supported in `Ω`. -/
def IsSmoothTestOn (Ω : Set E) (u : E → ℝ) : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) u ∧ HasCompactSupport u ∧ tsupport u ⊆ Ω

omit [NeZero d] in
theorem IsSmoothTestOn.zero
    {Ω : Set E} :
    IsSmoothTestOn Ω (fun _ : E => (0 : ℝ)) := by
  refine ⟨by simpa using (contDiff_const : ContDiff ℝ (⊤ : ℕ∞) (fun _ : E => (0 : ℝ))),
    HasCompactSupport.zero, by simp⟩

omit [NeZero d] in
theorem IsSmoothTestOn.add
    {Ω : Set E} {u v : E → ℝ}
    (hu : IsSmoothTestOn Ω u) (hv : IsSmoothTestOn Ω v) :
    IsSmoothTestOn Ω (fun x => u x + v x) := by
  refine ⟨hu.1.add hv.1, hu.2.1.add hv.2.1, ?_⟩
  exact (tsupport_add u v).trans <| Set.union_subset hu.2.2 hv.2.2

omit [NeZero d] in
theorem IsSmoothTestOn.smul
    {Ω : Set E} (c : ℝ) {u : E → ℝ}
    (hu : IsSmoothTestOn Ω u) :
    IsSmoothTestOn Ω (fun x => c * u x) := by
  refine ⟨?_, ?_, ?_⟩
  · simpa [smul_eq_mul] using (contDiff_const.mul hu.1)
  · simpa [Pi.smul_apply, smul_eq_mul] using
      (hu.2.1.smul_left (f := fun _ : E => c))
  · simpa [Pi.smul_apply, smul_eq_mul] using
      (tsupport_smul_subset_right (fun _ : E => c) u).trans hu.2.2

omit [NeZero d] in
theorem IsSmoothTestOn.sub
    {Ω : Set E} {u v : E → ℝ}
    (hu : IsSmoothTestOn Ω u) (hv : IsSmoothTestOn Ω v) :
    IsSmoothTestOn Ω (fun x => u x - v x) := by
  simpa [sub_eq_add_neg, Pi.smul_apply, smul_eq_mul] using hu.add (hv.smul (-1))

/-- Classical gradient field of a smooth scalar function. -/
noncomputable def smoothGradField (u : E → ℝ) : E → E :=
  fun x => WithLp.toLp 2 fun i => (fderiv ℝ u x) (EuclideanSpace.single i 1)

omit [NeZero d] in
theorem norm_smoothGradField_eq_smoothGradNorm
    {u : E → ℝ} {x : E} :
    ‖smoothGradField u x‖ = smoothGradNorm u x := by
  rfl

omit [NeZero d] in
theorem smoothGradField_zero :
    smoothGradField (fun _ : E => (0 : ℝ)) = 0 := by
  ext x i
  simp [smoothGradField]

omit [NeZero d] in
theorem smoothGradField_add
    {u v : E → ℝ}
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) (hv : ContDiff ℝ (⊤ : ℕ∞) v) :
    smoothGradField (fun x => u x + v x) =
      fun x => smoothGradField u x + smoothGradField v x := by
  ext x i
  have hu_diff : DifferentiableAt ℝ u x :=
    (hu.contDiffAt).differentiableAt (by norm_num)
  have hv_diff : DifferentiableAt ℝ v x :=
    (hv.contDiffAt).differentiableAt (by norm_num)
  simpa [smoothGradField, PiLp.toLp_apply] using
    congrArg (fun L : E →L[ℝ] ℝ => L (EuclideanSpace.single i 1))
      (fderiv_add hu_diff hv_diff)

omit [NeZero d] in
theorem smoothGradField_smul
    (c : ℝ) {u : E → ℝ} :
    smoothGradField (fun x => c * u x) =
      fun x => c • smoothGradField u x := by
  ext x i
  have hfd : fderiv ℝ (fun y => c * u y) x = c • fderiv ℝ u x := by
    simpa [smul_eq_mul] using congrFun (fderiv_const_smul_field (𝕜 := ℝ) (f := u) c) x
  simpa [smoothGradField, PiLp.toLp_apply] using
    congrArg (fun L : E →L[ℝ] ℝ => L (EuclideanSpace.single i 1)) hfd

/-- Canonical `W^{1,2}` witness on `Ω` carried by a smooth compactly supported
test function supported in `Ω`. -/
noncomputable def smoothTestWitness
    {Ω : Set E} (hΩ : IsOpen Ω) {u : E → ℝ}
    (hu : IsSmoothTestOn Ω u) :
    MemW1pWitness 2 u Ω where
  memLp := (hu.1.continuous.memLp_of_hasCompactSupport hu.2.1).restrict Ω
  weakGrad := smoothGradField u
  weakGrad_component_memLp := by
    intro i
    have hderiv_smooth : ContDiff ℝ (⊤ : ℕ∞)
        (fun x => (fderiv ℝ u x) (EuclideanSpace.single i 1)) :=
      (hu.1.fderiv_right (m := (⊤ : ℕ∞)) (by norm_cast)).clm_apply contDiff_const
    exact
      (hderiv_smooth.continuous.memLp_of_hasCompactSupport
        (hu.2.1.fderiv_apply (𝕜 := ℝ) _)).restrict Ω
  isWeakGrad := by
    intro i
    simpa [smoothGradField, PiLp.toLp_apply] using
      (HasWeakPartialDeriv.of_contDiff (Ω := Ω) (i := i) (f := u) hΩ
        (hu.1.of_le (by norm_cast)))

theorem smoothTest_memH01
    {Ω : Set E} (hΩ : IsOpen Ω) {u : E → ℝ}
    (hu : IsSmoothTestOn Ω u) :
    MemH01 u Ω :=
  memW01p_of_contDiff_hasCompactSupport_subset hΩ hu.1 hu.2.1 hu.2.2

/-- The `L²` gradient class carried by a Sobolev witness. -/
noncomputable def gradLpOfWitness
    {Ω : Set E} {u : E → ℝ} (hu : MemW1pWitness 2 u Ω) :
    MeasureTheory.Lp E 2 (volume.restrict Ω) :=
  hu.weakGrad_memLp.toLp hu.weakGrad

theorem norm_gradLpOfWitness_eq
    {Ω : Set E} {u : E → ℝ} (hu : MemW1pWitness 2 u Ω) :
    ‖gradLpOfWitness hu‖ =
      (∫ x, ‖hu.weakGrad x‖ ^ (2 : ℝ) ∂(volume.restrict Ω)) ^ (1 / (2 : ℝ)) := by
  let _ := (inferInstance : NeZero d)
  rw [gradLpOfWitness, Lp.norm_toLp]
  rw [MeasureTheory.toReal_eLpNorm hu.weakGrad_memLp.aestronglyMeasurable]
  simpa using
    (MeasureTheory.lpNorm_eq_integral_norm_rpow_toReal
      (μ := volume.restrict Ω) (f := hu.weakGrad) (p := (2 : ENNReal))
      (by norm_num) (by simp) hu.weakGrad_memLp.aestronglyMeasurable)

/-- The `L²` class carried by a smooth test function on `Ω`. -/
noncomputable def smoothFunToLp
    {Ω : Set E} (hΩ : IsOpen Ω) {u : E → ℝ}
    (hu : IsSmoothTestOn Ω u) :
    MeasureTheory.Lp ℝ 2 (volume.restrict Ω) :=
  (smoothTestWitness hΩ hu).memLp.toLp u

theorem smoothFunToLp_zero
    {Ω : Set E} (hΩ : IsOpen Ω) :
    smoothFunToLp hΩ IsSmoothTestOn.zero = 0 := by
  let _ := (inferInstance : NeZero d)
  let hu0 := smoothTestWitness hΩ IsSmoothTestOn.zero
  let hu0Lp := hu0.memLp
  change hu0Lp.toLp (0 : E → ℝ) = 0
  exact hu0Lp.toLp_zero

theorem smoothFunToLp_add
    {Ω : Set E} (hΩ : IsOpen Ω) {u v : E → ℝ}
    (hu : IsSmoothTestOn Ω u) (hv : IsSmoothTestOn Ω v) :
    smoothFunToLp hΩ (hu.add hv) = smoothFunToLp hΩ hu + smoothFunToLp hΩ hv := by
  let _ := (inferInstance : NeZero d)
  let huLp := (smoothTestWitness hΩ hu).memLp
  let hvLp := (smoothTestWitness hΩ hv).memLp
  let huvLp := (smoothTestWitness hΩ (hu.add hv)).memLp
  change huvLp.toLp (fun x => u x + v x) = huLp.toLp u + hvLp.toLp v
  simpa using (MemLp.toLp_add huLp hvLp).symm

theorem smoothFunToLp_smul
    {Ω : Set E} (hΩ : IsOpen Ω) (c : ℝ) {u : E → ℝ}
    (hu : IsSmoothTestOn Ω u) :
    smoothFunToLp hΩ (hu.smul c) = c • smoothFunToLp hΩ hu := by
  let _ := (inferInstance : NeZero d)
  let huLp := (smoothTestWitness hΩ hu).memLp
  let hcuLp := (smoothTestWitness hΩ (hu.smul c)).memLp
  change hcuLp.toLp (fun x => c * u x) = c • huLp.toLp u
  simpa [Pi.smul_apply, smul_eq_mul] using (MemLp.toLp_const_smul c huLp).symm

theorem smoothFunToLp_sub
    {Ω : Set E} (hΩ : IsOpen Ω) {u v : E → ℝ}
    (hu : IsSmoothTestOn Ω u) (hv : IsSmoothTestOn Ω v) :
    smoothFunToLp hΩ (hu.sub hv) = smoothFunToLp hΩ hu - smoothFunToLp hΩ hv := by
  simpa [sub_eq_add_neg] using smoothFunToLp_add hΩ hu (hv.smul (-1))

/-- Norm of the `L²` class carried by a smooth test function. -/
theorem norm_smoothFunToLp_eq
    {Ω : Set E} (hΩ : IsOpen Ω) {u : E → ℝ}
    (hu : IsSmoothTestOn Ω u) :
    ‖smoothFunToLp hΩ hu‖ =
      (∫ x, ‖u x‖ ^ (2 : ℝ) ∂(volume.restrict Ω)) ^ (1 / (2 : ℝ)) := by
  let _ := (inferInstance : NeZero d)
  rw [smoothFunToLp, Lp.norm_toLp]
  rw [MeasureTheory.toReal_eLpNorm (smoothTestWitness hΩ hu).memLp.aestronglyMeasurable]
  simpa using
    (MeasureTheory.lpNorm_eq_integral_norm_rpow_toReal
      (μ := volume.restrict Ω) (f := u) (p := (2 : ENNReal))
      (by norm_num) (by simp) (smoothTestWitness hΩ hu).memLp.aestronglyMeasurable)

/-- The `L²` gradient class carried by a smooth test function on `Ω`. -/
noncomputable def smoothGradToLp
    {Ω : Set E} (hΩ : IsOpen Ω) {u : E → ℝ}
    (hu : IsSmoothTestOn Ω u) :
    MeasureTheory.Lp E 2 (volume.restrict Ω) :=
  gradLpOfWitness (smoothTestWitness hΩ hu)

theorem smoothGradToLp_zero
    {Ω : Set E} (hΩ : IsOpen Ω) :
    smoothGradToLp hΩ IsSmoothTestOn.zero = 0 := by
  let _ := (inferInstance : NeZero d)
  let hw0 := smoothTestWitness hΩ IsSmoothTestOn.zero
  let hzeroLp : MemLp (0 : E → E) 2 (volume.restrict Ω) :=
    MeasureTheory.MemLp.zero'
  have hcongr :
      hw0.weakGrad_memLp.toLp hw0.weakGrad = hzeroLp.toLp (0 : E → E) :=
    MemLp.toLp_congr hw0.weakGrad_memLp hzeroLp <|
      Filter.Eventually.of_forall fun x => by
        simpa [hw0, smoothTestWitness] using congrFun smoothGradField_zero x
  change hw0.weakGrad_memLp.toLp hw0.weakGrad = 0
  rw [hcongr]
  exact hzeroLp.toLp_zero

theorem smoothGradToLp_add
    {Ω : Set E} (hΩ : IsOpen Ω) {u v : E → ℝ}
    (hu : IsSmoothTestOn Ω u) (hv : IsSmoothTestOn Ω v) :
    smoothGradToLp hΩ (hu.add hv) = smoothGradToLp hΩ hu + smoothGradToLp hΩ hv := by
  let _ := (inferInstance : NeZero d)
  let hgu := (smoothTestWitness hΩ hu).weakGrad_memLp
  let hgv := (smoothTestWitness hΩ hv).weakGrad_memLp
  let hguv := (smoothTestWitness hΩ (hu.add hv)).weakGrad_memLp
  have hcongr :
      hguv.toLp (smoothGradField (fun x => u x + v x)) =
        (hgu.add hgv).toLp (fun x => smoothGradField u x + smoothGradField v x) :=
    MemLp.toLp_congr hguv (hgu.add hgv) <|
      Filter.Eventually.of_forall fun x => by
        simpa using congrFun (smoothGradField_add hu.1 hv.1) x
  change hguv.toLp (smoothGradField (fun x => u x + v x)) =
      hgu.toLp (smoothGradField u) + hgv.toLp (smoothGradField v)
  rw [hcongr]
  simpa using (MemLp.toLp_add hgu hgv)

theorem smoothGradToLp_smul
    {Ω : Set E} (hΩ : IsOpen Ω) (c : ℝ) {u : E → ℝ}
    (hu : IsSmoothTestOn Ω u) :
    smoothGradToLp hΩ (hu.smul c) = c • smoothGradToLp hΩ hu := by
  let _ := (inferInstance : NeZero d)
  let hgu := (smoothTestWitness hΩ hu).weakGrad_memLp
  let hgcu := (smoothTestWitness hΩ (hu.smul c)).weakGrad_memLp
  have hcongr :
      hgcu.toLp (smoothGradField (fun x => c * u x)) =
        (hgu.const_smul c).toLp (c • fun x => smoothGradField u x) :=
    MemLp.toLp_congr hgcu (hgu.const_smul c) <|
      Filter.Eventually.of_forall fun x => by
        simpa using congrFun (smoothGradField_smul c (u := u)) x
  change hgcu.toLp (smoothGradField (fun x => c * u x)) = c • hgu.toLp (smoothGradField u)
  rw [hcongr]
  simpa using (MemLp.toLp_const_smul c hgu)

theorem smoothGradToLp_sub
    {Ω : Set E} (hΩ : IsOpen Ω) {u v : E → ℝ}
    (hu : IsSmoothTestOn Ω u) (hv : IsSmoothTestOn Ω v) :
    smoothGradToLp hΩ (hu.sub hv) = smoothGradToLp hΩ hu - smoothGradToLp hΩ hv := by
  calc
    smoothGradToLp hΩ (hu.sub hv)
        = smoothGradToLp hΩ hu + smoothGradToLp hΩ (hv.smul (-1)) := by
            simpa [IsSmoothTestOn.sub] using smoothGradToLp_add hΩ hu (hv.smul (-1))
    _ = smoothGradToLp hΩ hu - smoothGradToLp hΩ hv := by
          rw [smoothGradToLp_smul hΩ (-1) hv]
          simp [sub_eq_add_neg]

/-- Norm of the `L²` gradient class carried by a smooth test function. -/
theorem norm_smoothGradToLp_eq
    {Ω : Set E} (hΩ : IsOpen Ω) {u : E → ℝ}
    (hu : IsSmoothTestOn Ω u) :
    ‖smoothGradToLp hΩ hu‖ =
      (∫ x, ‖smoothGradField u x‖ ^ (2 : ℝ) ∂(volume.restrict Ω)) ^ (1 / (2 : ℝ)) := by
  simpa [smoothGradToLp] using norm_gradLpOfWitness_eq (smoothTestWitness hΩ hu)

end DeGiorgi
