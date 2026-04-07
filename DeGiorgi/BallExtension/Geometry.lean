import DeGiorgi.BallExtension.Core

/-!
# Ball Extension Geometry

Shell, inversion, derivative, and decomposition lemmas for the explicit
unit-ball extension operator.
-/

noncomputable section

open MeasureTheory Metric Filter Topology Set Function Matrix
open scoped ENNReal NNReal RealInnerProductSpace

namespace DeGiorgi

variable {d : ℕ} [NeZero d]

local notation "E" => EuclideanSpace ℝ (Fin d)

/-- The outer shell on which the explicit unit-ball extension uses sphere inversion. -/
def unitBallOuterShell : Set E := {x : E | 1 < ‖x‖ ∧ ‖x‖ < 2}

/-- The inner shell that is the image of `unitBallOuterShell` under sphere inversion. -/
def unitBallInnerShell : Set E := {x : E | (1 / 2 : ℝ) < ‖x‖ ∧ ‖x‖ < 1}

omit [NeZero d] in
lemma measurableSet_unitBallOuterShell : MeasurableSet (unitBallOuterShell (d := d)) := by
  unfold unitBallOuterShell
  exact measurableSet_lt measurable_const measurable_norm
    |>.inter (measurableSet_lt measurable_norm measurable_const)

omit [NeZero d] in
lemma measurableSet_unitBallInnerShell : MeasurableSet (unitBallInnerShell (d := d)) := by
  unfold unitBallInnerShell
  exact measurableSet_lt measurable_const measurable_norm
    |>.inter (measurableSet_lt measurable_norm measurable_const)

omit [NeZero d] in
lemma mem_unitBallOuterShell {x : E} :
    x ∈ unitBallOuterShell (d := d) ↔ 1 < ‖x‖ ∧ ‖x‖ < 2 := Iff.rfl

omit [NeZero d] in
lemma mem_unitBallInnerShell {x : E} :
    x ∈ unitBallInnerShell (d := d) ↔ (1 / 2 : ℝ) < ‖x‖ ∧ ‖x‖ < 1 := Iff.rfl

omit [NeZero d] in
lemma unitBallRetraction_eq_inversion_of_mem_outerShell {x : E}
    (hx : x ∈ unitBallOuterShell (d := d)) :
    unitBallRetraction (d := d) x = EuclideanGeometry.inversion (0 : E) 1 x := by
  rcases hx with ⟨h1, h2⟩
  rw [unitBallRetraction_eq_smul_of_annulus (d := d) h1 h2, EuclideanGeometry.inversion]
  simp [dist_eq_norm, div_eq_mul_inv]

omit [NeZero d] in
lemma inversion_mem_unitBallInnerShell_of_mem_outerShell {x : E}
    (hx : x ∈ unitBallOuterShell (d := d)) :
    EuclideanGeometry.inversion (0 : E) 1 x ∈ unitBallInnerShell (d := d) := by
  rcases hx with ⟨h1, h2⟩
  rw [mem_unitBallInnerShell]
  constructor
  · have hxpos : 0 < ‖x‖ := lt_trans zero_lt_one h1
    rw [← dist_zero_right (EuclideanGeometry.inversion (0 : E) 1 x),
      EuclideanGeometry.dist_inversion_center (c := (0 : E)) (x := x) (R := (1 : ℝ)),
      dist_zero_right]
    field_simp [hxpos.ne']
    linarith
  · have hxpos : 0 < ‖x‖ := lt_trans zero_lt_one h1
    rw [← dist_zero_right (EuclideanGeometry.inversion (0 : E) 1 x),
      EuclideanGeometry.dist_inversion_center (c := (0 : E)) (x := x) (R := (1 : ℝ)),
      dist_zero_right]
    field_simp [hxpos.ne']
    linarith

omit [NeZero d] in
lemma inversion_mem_unitBallOuterShell_of_mem_innerShell {x : E}
    (hx : x ∈ unitBallInnerShell (d := d)) :
    EuclideanGeometry.inversion (0 : E) 1 x ∈ unitBallOuterShell (d := d) := by
  rcases hx with ⟨h1, h2⟩
  rw [mem_unitBallOuterShell]
  constructor
  · have hxpos : 0 < ‖x‖ := by linarith
    rw [← dist_zero_right (EuclideanGeometry.inversion (0 : E) 1 x),
      EuclideanGeometry.dist_inversion_center (c := (0 : E)) (x := x) (R := (1 : ℝ)),
      dist_zero_right]
    field_simp [hxpos.ne']
    linarith
  · have hxpos : 0 < ‖x‖ := by linarith
    rw [← dist_zero_right (EuclideanGeometry.inversion (0 : E) 1 x),
      EuclideanGeometry.dist_inversion_center (c := (0 : E)) (x := x) (R := (1 : ℝ)),
      dist_zero_right]
    field_simp [hxpos.ne']
    linarith

omit [NeZero d] in
lemma inversion_image_unitBallOuterShell :
    EuclideanGeometry.inversion (0 : E) 1 '' unitBallOuterShell (d := d) =
      unitBallInnerShell (d := d) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact inversion_mem_unitBallInnerShell_of_mem_outerShell (d := d) hx
  · intro hy
    refine ⟨EuclideanGeometry.inversion (0 : E) 1 y, ?_, ?_⟩
    · exact inversion_mem_unitBallOuterShell_of_mem_innerShell (d := d) hy
    · exact EuclideanGeometry.inversion_inversion (c := (0 : E)) (R := (1 : ℝ)) one_ne_zero y

omit [NeZero d] in
lemma inversion_image_unitBallInnerShell :
    EuclideanGeometry.inversion (0 : E) 1 '' unitBallInnerShell (d := d) =
      unitBallOuterShell (d := d) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact inversion_mem_unitBallOuterShell_of_mem_innerShell (d := d) hx
  · intro hy
    refine ⟨EuclideanGeometry.inversion (0 : E) 1 y, ?_, ?_⟩
    · exact inversion_mem_unitBallInnerShell_of_mem_outerShell (d := d) hy
    · exact EuclideanGeometry.inversion_inversion (c := (0 : E)) (R := (1 : ℝ)) one_ne_zero y

omit [NeZero d] in
lemma injOn_inversion_unitBallOuterShell :
    InjOn (EuclideanGeometry.inversion (0 : E) 1) (unitBallOuterShell (d := d)) := by
  exact (EuclideanGeometry.inversion_injective (c := (0 : E)) (R := (1 : ℝ)) one_ne_zero).injOn

omit [NeZero d] in
lemma injOn_inversion_unitBallInnerShell :
    InjOn (EuclideanGeometry.inversion (0 : E) 1) (unitBallInnerShell (d := d)) := by
  exact (EuclideanGeometry.inversion_injective (c := (0 : E)) (R := (1 : ℝ)) one_ne_zero).injOn

omit [NeZero d] in
lemma hasFDerivWithinAt_inversion_unitBallInnerShell {x : E}
    (hx : x ∈ unitBallInnerShell (d := d)) :
    HasFDerivWithinAt (EuclideanGeometry.inversion (0 : E) 1)
      (((1 / dist x (0 : E)) ^ 2) • ((ℝ ∙ x)ᗮ.reflection : E →L[ℝ] E))
      (unitBallInnerShell (d := d)) x := by
  have hx0 : x ≠ (0 : E) := by
    intro hx0
    rcases hx with ⟨h1, _h2⟩
    have : 0 < ‖x‖ := by linarith
    simp [hx0] at this
  simpa using
    (EuclideanGeometry.hasFDerivAt_inversion (c := (0 : E)) (R := (1 : ℝ)) hx0).hasFDerivWithinAt

omit [NeZero d] in
lemma abs_det_fderiv_inversion_zero_one' {x : E} (hx : x ≠ (0 : E)) :
    |(fderiv ℝ (EuclideanGeometry.inversion (0 : E) 1) x).det| =
      ((1 / dist x (0 : E)) ^ 2) ^ Module.finrank ℝ E := by
  have hfd :
      HasFDerivAt (EuclideanGeometry.inversion (0 : E) 1)
        (((1 / dist x (0 : E)) ^ 2) • ((ℝ ∙ x)ᗮ.reflection : E →L[ℝ] E)) x := by
    simpa using
      (EuclideanGeometry.hasFDerivAt_inversion (c := (0 : E)) (R := (1 : ℝ)) hx)
  have hreflect :
      ((((ℝ ∙ x)ᗮ.reflection : E →L[ℝ] E)).det : ℝ) = -1 := by
    rw [ContinuousLinearMap.det]
    calc
      LinearMap.det ((((ℝ ∙ x)ᗮ.reflection : E →L[ℝ] E)).toLinearMap)
          = (-1 : ℝ) ^ Module.finrank ℝ (((ℝ ∙ x)ᗮ)ᗮ : Submodule ℝ E) := by
              exact ((ℝ ∙ x)ᗮ).det_reflection
      _ = (-1 : ℝ) ^ Module.finrank ℝ (ℝ ∙ x : Submodule ℝ E) := by
            rw [Submodule.orthogonal_orthogonal]
      _ = (-1 : ℝ) ^ (1 : ℕ) := by
            rw [finrank_span_singleton hx]
      _ = -1 := by norm_num
  have hnn : 0 ≤ (((1 / dist x (0 : E)) ^ 2) ^ Module.finrank ℝ E : ℝ) := by
    positivity
  calc
    |(fderiv ℝ (EuclideanGeometry.inversion (0 : E) 1) x).det|
        = |((((1 / dist x (0 : E)) ^ 2) •
            ((ℝ ∙ x)ᗮ.reflection : E →L[ℝ] E)).det)| := by
              rw [hfd.fderiv]
    _ = |(((1 / dist x (0 : E)) ^ 2) ^ Module.finrank ℝ E) *
          ((((ℝ ∙ x)ᗮ.reflection : E →L[ℝ] E)).det)| := by
            simp [ContinuousLinearMap.det, LinearMap.det_smul]
    _ = |(((1 / dist x (0 : E)) ^ 2) ^ Module.finrank ℝ E)| *
          |((((ℝ ∙ x)ᗮ.reflection : E →L[ℝ] E)).det)| := by
            rw [abs_mul]
    _ = (((1 / dist x (0 : E)) ^ 2) ^ Module.finrank ℝ E) * 1 := by
          rw [abs_of_nonneg hnn, hreflect]
          norm_num
    _ = ((1 / dist x (0 : E)) ^ 2) ^ Module.finrank ℝ E := by ring

omit [NeZero d] in
lemma abs_det_fderiv_inversion_zero_one {x : E} (hx : x ≠ (0 : E)) :
    |(fderiv ℝ (EuclideanGeometry.inversion (0 : E) 1) x).det| =
      ((1 / ‖x‖) ^ 2) ^ d := by
  simpa [dist_zero_right, finrank_euclideanSpace_fin] using
    abs_det_fderiv_inversion_zero_one' (d := d) hx

omit [NeZero d] in
lemma abs_det_fderiv_inversion_zero_one_le_of_mem_innerShell {x : E}
    (hx : x ∈ unitBallInnerShell (d := d)) :
    |(fderiv ℝ (EuclideanGeometry.inversion (0 : E) 1) x).det| ≤ (2 : ℝ) ^ (2 * d) := by
  rcases hx with ⟨h1, _h2⟩
  have hx0 : x ≠ (0 : E) := by
    intro hx0
    have : 0 < ‖x‖ := by linarith
    simp [hx0] at this
  rw [abs_det_fderiv_inversion_zero_one (d := d) hx0]
  have hnorm_pos : 0 < ‖x‖ := by linarith
  have hbound : (1 / ‖x‖ : ℝ) ≤ 2 := by
    field_simp [hnorm_pos.ne']
    linarith
  calc
    ((1 / ‖x‖) ^ 2) ^ d ≤ (2 ^ 2 : ℝ) ^ d := by
      gcongr
    _ = (2 : ℝ) ^ (2 * d) := by rw [← pow_mul]

omit [NeZero d] in
lemma lintegral_outerShell_comp_inversion_le
    (Φ : E → ℝ≥0∞) :
    ∫⁻ y in unitBallOuterShell (d := d),
        Φ (EuclideanGeometry.inversion (0 : E) 1 y) ∂volume
      ≤ ENNReal.ofReal ((2 : ℝ) ^ (2 * d)) *
        ∫⁻ x in unitBallInnerShell (d := d), Φ x ∂volume := by
  let inv : E → E := EuclideanGeometry.inversion (0 : E) 1
  let f' : E → E →L[ℝ] E := fun x =>
    (((1 / dist x (0 : E)) ^ 2) • ((ℝ ∙ x)ᗮ.reflection : E →L[ℝ] E))
  have himage :
      inv '' unitBallInnerShell (d := d) = unitBallOuterShell (d := d) :=
    inversion_image_unitBallInnerShell (d := d)
  have hcov :=
    MeasureTheory.lintegral_image_eq_lintegral_abs_det_fderiv_mul
      (μ := volume) (s := unitBallInnerShell (d := d)) (f := inv) (f' := f')
      measurableSet_unitBallInnerShell
      (fun x hx => by
        simpa [inv, f'] using hasFDerivWithinAt_inversion_unitBallInnerShell (d := d) hx)
      injOn_inversion_unitBallInnerShell
      (fun y => Φ (inv y))
  rw [himage] at hcov
  calc
    ∫⁻ y in unitBallOuterShell (d := d), Φ (EuclideanGeometry.inversion (0 : E) 1 y) ∂volume
        = ∫⁻ x in unitBallInnerShell (d := d), ENNReal.ofReal |(f' x).det| * Φ (inv (inv x))
            ∂volume := by
              simpa [inv] using hcov
    _ ≤ ∫⁻ x in unitBallInnerShell (d := d),
          ENNReal.ofReal ((2 : ℝ) ^ (2 * d)) * Φ (inv (inv x)) ∂volume := by
            refine lintegral_mono_ae ?_
            rw [ae_restrict_iff' measurableSet_unitBallInnerShell]
            refine Filter.Eventually.of_forall ?_
            intro x hx
            have hweight :
                ENNReal.ofReal |(f' x).det| ≤ ENNReal.ofReal ((2 : ℝ) ^ (2 * d)) := by
              have hx0 : x ≠ (0 : E) := by
                intro hx0
                have : 0 < ‖x‖ := by
                  rcases hx with ⟨h1, _h2⟩
                  linarith
                simp [hx0] at this
              have hfderiv : f' x = fderiv ℝ (EuclideanGeometry.inversion (0 : E) 1) x := by
                have hfdx :
                    HasFDerivAt (EuclideanGeometry.inversion (0 : E) 1) (f' x) x := by
                  simpa [f'] using
                    (EuclideanGeometry.hasFDerivAt_inversion (c := (0 : E)) (R := (1 : ℝ)) hx0)
                exact hfdx.fderiv.symm
              exact ENNReal.ofReal_le_ofReal
                (by simpa [hfderiv] using
                  abs_det_fderiv_inversion_zero_one_le_of_mem_innerShell (d := d) hx)
            exact mul_le_mul' hweight le_rfl
    _ = ∫⁻ x in unitBallInnerShell (d := d),
          ENNReal.ofReal ((2 : ℝ) ^ (2 * d)) * Φ x ∂volume := by
            congr with x
            simp [inv, EuclideanGeometry.inversion_inversion, (by norm_num : (1 : ℝ) ≠ 0)]
    _ = ENNReal.ofReal ((2 : ℝ) ^ (2 * d)) *
          ∫⁻ x in unitBallInnerShell (d := d), Φ x ∂volume := by
            rw [lintegral_const_mul']
            simp

omit [NeZero d] in
lemma unitBallCutoff_eq_two_sub_norm_of_mem_outerShell {x : E}
    (hx : x ∈ unitBallOuterShell (d := d)) :
    unitBallCutoff (d := d) x = 2 - ‖x‖ := by
  rcases hx with ⟨h1, h2⟩
  unfold unitBallCutoff
  have hleft : 2 - ‖x‖ ≤ 1 := by linarith
  have hright : 0 ≤ 2 - ‖x‖ := by linarith
  rw [max_eq_left hright, min_eq_right hleft]

omit [NeZero d] in
lemma norm_fderiv_inversion_zero_one {x : E} (hx : x ≠ (0 : E)) :
    ‖fderiv ℝ (EuclideanGeometry.inversion (0 : E) 1) x‖ ≤ (1 / ‖x‖) ^ 2 := by
  have hfd :
      HasFDerivAt (EuclideanGeometry.inversion (0 : E) 1)
        (((1 / dist x (0 : E)) ^ 2) • ((ℝ ∙ x)ᗮ.reflection : E →L[ℝ] E)) x := by
    simpa using
      (EuclideanGeometry.hasFDerivAt_inversion (c := (0 : E)) (R := (1 : ℝ)) hx)
  have hreflect :
      ‖((ℝ ∙ x)ᗮ.reflection : E →L[ℝ] E)‖ ≤ 1 := by
    refine (ContinuousLinearMap.opNorm_le_iff
      (f := ((ℝ ∙ x)ᗮ.reflection : E →L[ℝ] E)) (M := 1) (by positivity)).2 ?_
    intro y
    simp [((ℝ ∙ x)ᗮ).reflection.norm_map y]
  calc
    ‖fderiv ℝ (EuclideanGeometry.inversion (0 : E) 1) x‖
        = ‖(((1 / dist x (0 : E)) ^ 2) • ((ℝ ∙ x)ᗮ.reflection : E →L[ℝ] E))‖ := by
            rw [hfd.fderiv]
    _ = |(1 / dist x (0 : E)) ^ 2| * ‖((ℝ ∙ x)ᗮ.reflection : E →L[ℝ] E)‖ := by
            rw [norm_smul, Real.norm_eq_abs]
    _ ≤ |(1 / dist x (0 : E)) ^ 2| * 1 := by
          gcongr
    _ = (1 / ‖x‖) ^ 2 := by
          rw [abs_of_nonneg]
          · simp [dist_zero_right]
          · positivity

omit [NeZero d] in
lemma norm_fderiv_inversion_le_one_of_mem_outerShell {x : E}
    (hx : x ∈ unitBallOuterShell (d := d)) :
    ‖fderiv ℝ (EuclideanGeometry.inversion (0 : E) 1) x‖ ≤ 1 := by
  rcases hx with ⟨h1, _h2⟩
  have hx0 : x ≠ (0 : E) := by
    intro hx0
    have : 0 < ‖x‖ := by linarith
    simp [hx0] at this
  have hnorm_ge_one : 1 ≤ ‖x‖ := by linarith
  have hle : (1 / ‖x‖ : ℝ) ≤ 1 := by
    simpa [one_div] using (inv_le_one_of_one_le₀ hnorm_ge_one)
  have hsq : (1 / ‖x‖ : ℝ) ^ 2 ≤ 1 := by
    have hnn : 0 ≤ (1 / ‖x‖ : ℝ) := by positivity
    have hsq' := mul_self_le_mul_self hnn hle
    simpa [sq] using hsq'
  exact (norm_fderiv_inversion_zero_one (d := d) hx0).trans hsq

omit [NeZero d] in
lemma isOpen_unitBallOuterShell : IsOpen (unitBallOuterShell (d := d)) := by
  unfold unitBallOuterShell
  exact isOpen_lt continuous_const continuous_norm |>.inter
    (isOpen_lt continuous_norm continuous_const)

omit [NeZero d] in
lemma hasFDerivAt_unitBallCutoff_of_mem_outerShell {x : E}
    (hx : x ∈ unitBallOuterShell (d := d)) :
    HasFDerivAt (unitBallCutoff (d := d)) (-(fderiv ℝ (fun y : E => ‖y‖) x)) x := by
  have hx0 : x ≠ (0 : E) := by
    intro hx0
    rcases hx with ⟨h1, _h2⟩
    have : 0 < ‖x‖ := by linarith
    simp [hx0] at this
  have hnorm : DifferentiableAt ℝ (fun y : E => ‖y‖) x :=
    differentiableAt_id.norm ℝ hx0
  have hfd_annulus :
      HasFDerivAt (fun y : E => 2 - ‖y‖) (-(fderiv ℝ (fun y : E => ‖y‖) x)) x := by
    simpa using hnorm.hasFDerivAt.const_sub (2 : ℝ)
  have heq :
      unitBallCutoff (d := d) =ᶠ[𝓝 x] fun y : E => 2 - ‖y‖ := by
    filter_upwards [isOpen_unitBallOuterShell (d := d) |>.mem_nhds hx] with y hy
    exact unitBallCutoff_eq_two_sub_norm_of_mem_outerShell (d := d) hy
  exact hfd_annulus.congr_of_eventuallyEq heq

lemma norm_fderiv_unitBallCutoff_of_mem_outerShell {x : E}
    (hx : x ∈ unitBallOuterShell (d := d)) :
    ‖fderiv ℝ (unitBallCutoff (d := d)) x‖ = 1 := by
  have hx0 : x ≠ (0 : E) := by
    intro hx0
    rcases hx with ⟨h1, _h2⟩
    have : 0 < ‖x‖ := by linarith
    simp [hx0] at this
  have hnorm : DifferentiableAt ℝ (fun y : E => ‖y‖) x :=
    differentiableAt_id.norm ℝ hx0
  have hfd_cutoff :=
    hasFDerivAt_unitBallCutoff_of_mem_outerShell (d := d) hx
  rw [hfd_cutoff.fderiv, norm_neg]
  simpa using norm_fderiv_norm hnorm

lemma norm_fderiv_unitBallExtension_le_of_mem_outerShell
    {u : E → ℝ} (hu : Differentiable ℝ u) {x : E}
    (hx : x ∈ unitBallOuterShell (d := d)) :
    ‖fderiv ℝ (unitBallExtension (d := d) u) x‖ ≤
      |u (EuclideanGeometry.inversion (0 : E) 1 x)| +
      ‖fderiv ℝ u (EuclideanGeometry.inversion (0 : E) 1 x)‖ := by
  let inv : E → E := EuclideanGeometry.inversion (0 : E) 1
  have hx0 : x ≠ (0 : E) := by
    intro hx0
    rcases hx with ⟨h1, _h2⟩
    have : 0 < ‖x‖ := by linarith
    simp [hx0] at this
  have hcutoff :
      HasFDerivAt (unitBallCutoff (d := d)) (fderiv ℝ (unitBallCutoff (d := d)) x) x := by
    simpa [(hasFDerivAt_unitBallCutoff_of_mem_outerShell (d := d) hx).fderiv] using
      (hasFDerivAt_unitBallCutoff_of_mem_outerShell (d := d) hx)
  have hinv :
      HasFDerivAt inv (fderiv ℝ inv x) x := by
    simpa [inv, (EuclideanGeometry.hasFDerivAt_inversion (c := (0 : E)) (R := (1 : ℝ)) hx0).fderiv] using
      (EuclideanGeometry.hasFDerivAt_inversion (c := (0 : E)) (R := (1 : ℝ)) hx0)
  have hcomp :
      HasFDerivAt (fun y : E => u (inv y))
        ((fderiv ℝ u (inv x)).comp (fderiv ℝ inv x)) x := by
    exact (hu (inv x)).hasFDerivAt.comp x hinv
  have hprod := hcutoff.mul hcomp
  have hext :
      unitBallExtension (d := d) u =ᶠ[𝓝 x] fun y : E => unitBallCutoff y * u (inv y) := by
    filter_upwards [isOpen_unitBallOuterShell (d := d) |>.mem_nhds hx] with y hy
    rw [unitBallExtension, unitBallRetraction_eq_inversion_of_mem_outerShell (d := d) hy]
  have hprod_ext :
      HasFDerivAt (unitBallExtension (d := d) u)
        (unitBallCutoff x • ((fderiv ℝ u (inv x)).comp (fderiv ℝ inv x)) +
          u (inv x) • fderiv ℝ (unitBallCutoff (d := d)) x) x := by
    simpa [mul_comm, add_comm, add_left_comm, add_assoc] using hprod.congr_of_eventuallyEq hext
  rw [hprod_ext.fderiv]
  calc
    ‖unitBallCutoff x • (fderiv ℝ u (inv x)).comp (fderiv ℝ inv x) +
        u (inv x) • fderiv ℝ (unitBallCutoff (d := d)) x‖
        ≤ ‖unitBallCutoff x • (fderiv ℝ u (inv x)).comp (fderiv ℝ inv x)‖ +
          ‖u (inv x) • fderiv ℝ (unitBallCutoff (d := d)) x‖ := norm_add_le _ _
    _ = |unitBallCutoff x| * ‖(fderiv ℝ u (inv x)).comp (fderiv ℝ inv x)‖ +
          |u (inv x)| * ‖fderiv ℝ (unitBallCutoff (d := d)) x‖ := by
            rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
    _ ≤ |unitBallCutoff x| * (‖fderiv ℝ u (inv x)‖ * ‖fderiv ℝ inv x‖) +
          |u (inv x)| * ‖fderiv ℝ (unitBallCutoff (d := d)) x‖ := by
            gcongr
            exact ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ |unitBallCutoff x| * ‖fderiv ℝ u (inv x)‖ + |u (inv x)| * 1 := by
          gcongr
          · exact mul_le_of_le_one_right (norm_nonneg _) <|
              norm_fderiv_inversion_le_one_of_mem_outerShell (d := d) hx
          · exact by
              rw [norm_fderiv_unitBallCutoff_of_mem_outerShell (d := d) hx]
    _ ≤ ‖fderiv ℝ u (inv x)‖ + |u (inv x)| := by
          have hcut : |unitBallCutoff x| ≤ 1 := by
            have hcut_nonneg : 0 ≤ unitBallCutoff x := by
              unfold unitBallCutoff
              exact le_min (by positivity) (le_max_right _ _)
            rw [abs_of_nonneg hcut_nonneg]
            have hcut_le : unitBallCutoff x ≤ 1 := by
              unfold unitBallCutoff
              exact min_le_left _ _
            exact hcut_le
          nlinarith [norm_nonneg (fderiv ℝ u (inv x)), abs_nonneg (u (inv x))]
    _ = |u (inv x)| + ‖fderiv ℝ u (inv x)‖ := by ring

omit [NeZero d] in
lemma unitBallInnerShell_subset_ball_zero_one :
    unitBallInnerShell (d := d) ⊆ Metric.ball (0 : E) 1 := by
  intro x hx
  rw [Metric.mem_ball, dist_zero_right]
  exact hx.2

omit [NeZero d] in
lemma unitBallOuterShell_subset_ball_zero_two :
    unitBallOuterShell (d := d) ⊆ Metric.ball (0 : E) 2 := by
  intro x hx
  rw [Metric.mem_ball, dist_zero_right]
  exact hx.2

omit [NeZero d] in
lemma ball_zero_two_eq_ball_zero_one_union_outerShell_union_sphere :
    Metric.ball (0 : E) 2 =
      Metric.ball (0 : E) 1 ∪ unitBallOuterShell (d := d) ∪ Metric.sphere (0 : E) 1 := by
  ext x
  constructor
  · intro hx
    rw [Metric.mem_ball, dist_zero_right] at hx
    by_cases h1 : ‖x‖ < 1
    · exact Or.inl <| Or.inl <| by simpa [Metric.mem_ball, dist_zero_right] using h1
    · have h1' : 1 ≤ ‖x‖ := by linarith
      by_cases h1eq : ‖x‖ = 1
      · exact Or.inr <| by simpa [Metric.mem_sphere, dist_zero_right] using h1eq
      · have h1lt : 1 < ‖x‖ := lt_of_le_of_ne h1' (by simpa [eq_comm] using h1eq)
        exact Or.inl <| Or.inr ⟨h1lt, hx⟩
  · rintro ((hx | hx) | hx)
    · rw [Metric.mem_ball, dist_zero_right] at hx ⊢
      exact lt_trans hx (by norm_num : (1 : ℝ) < 2)
    · rw [Metric.mem_ball, dist_zero_right]
      exact hx.2
    · have hsphere : ‖x‖ = 1 := by simpa [Metric.mem_sphere, dist_zero_right] using hx
      rw [Metric.mem_ball, dist_zero_right]
      linarith

omit [NeZero d] in
lemma disjoint_ball_zero_one_outerShell :
    Disjoint (Metric.ball (0 : E) 1) (unitBallOuterShell (d := d)) := by
  refine disjoint_left.2 ?_
  intro x hx1 hx2
  rw [Metric.mem_ball, dist_zero_right] at hx1
  exact (not_lt_of_ge (le_of_lt hx2.1)) hx1

omit [NeZero d] in
lemma disjoint_ball_zero_one_outerShell_union_sphere :
    Disjoint (Metric.ball (0 : E) 1 ∪ unitBallOuterShell (d := d)) (Metric.sphere (0 : E) 1) := by
  refine disjoint_left.2 ?_
  intro x hx hs
  rw [Metric.mem_sphere, dist_zero_right] at hs
  rcases hx with hx | hx
  · rw [Metric.mem_ball, dist_zero_right] at hx
    linarith
  · linarith [hx.1]

omit [NeZero d] in
lemma fderiv_unitBallExtension_eq_of_mem_ball
    {u : E → ℝ} {x : E} (hx : x ∈ Metric.ball (0 : E) 1) :
    fderiv ℝ (unitBallExtension (d := d) u) x = fderiv ℝ u x := by
  apply Filter.EventuallyEq.fderiv_eq
  filter_upwards [Metric.isOpen_ball.mem_nhds hx] with y hy
  exact unitBallExtension_eq_of_mem_ball (d := d) hy

end DeGiorgi