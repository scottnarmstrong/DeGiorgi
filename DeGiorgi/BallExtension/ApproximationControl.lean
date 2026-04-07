import DeGiorgi.BallExtension.SmoothCore

/-!
# Ball Extension Approximation Control

This file develops the shrinking-annulus control, exact gradient model, and
quantitative error bounds for the smooth approximants.
-/

noncomputable section

open MeasureTheory Metric Filter Topology Set Function Matrix
open scoped ENNReal NNReal RealInnerProductSpace

namespace DeGiorgi

variable {d : ℕ} [NeZero d]

local notation "E" => EuclideanSpace ℝ (Fin d)

namespace SmoothApproximationInternal

def unitBallApproxEps (n : ℕ) : ℝ :=
  ((n : ℝ) + 5)⁻¹

lemma unitBallApproxEps_pos (n : ℕ) :
    0 < unitBallApproxEps n := by
  unfold unitBallApproxEps
  exact inv_pos.mpr (by positivity : 0 < (n : ℝ) + 5)

lemma unitBallApproxEps_lt_one (n : ℕ) :
    unitBallApproxEps n < 1 := by
  unfold unitBallApproxEps
  have hpos : 0 < (n : ℝ) + 5 := by positivity
  field_simp [hpos.ne']
  linarith

omit [NeZero d] in
lemma measurableSet_unitBallBadAnnulusOne (ε : ℝ) :
    MeasurableSet (unitBallBadAnnulusOne (d := d) ε) := by
  unfold unitBallBadAnnulusOne
  exact measurableSet_lt measurable_const measurable_norm
    |>.inter (measurableSet_lt measurable_norm measurable_const)

omit [NeZero d] in
lemma measurableSet_unitBallBadAnnulusTwo (ε : ℝ) :
    MeasurableSet (unitBallBadAnnulusTwo (d := d) ε) := by
  unfold unitBallBadAnnulusTwo
  exact measurableSet_lt measurable_const measurable_norm
    |>.inter (measurableSet_lt measurable_norm measurable_const)

lemma tendsto_unitBallApproxEps :
    Tendsto (fun n => unitBallApproxEps n) atTop (nhds 0) := by
  unfold unitBallApproxEps
  have hbase : Tendsto (fun n : ℕ => n + 5) atTop atTop := tendsto_add_atTop_nat 5
  have h :=
    ((tendsto_inv_atTop_nhds_zero_nat : Tendsto (fun n : ℕ => ((n : ℝ))⁻¹) atTop (nhds 0)).comp hbase)
  refine h.congr' ?_
  exact Filter.Eventually.of_forall fun n => by
    change ((((n + 5 : ℕ) : ℝ))⁻¹) = (((n : ℝ) + 5)⁻¹)
    norm_num [Nat.cast_add]

lemma unitBallApproxEps_antitone : Antitone (unitBallApproxEps) := by
  intro m n hmn
  unfold unitBallApproxEps
  have hm : 0 < (((m + 5 : ℕ) : ℝ)) := by positivity
  have hle : (((m + 5 : ℕ) : ℝ)) ≤ (((n + 5 : ℕ) : ℝ)) := by
    exact_mod_cast Nat.add_le_add_right hmn 5
  simpa [Nat.cast_add, one_div, add_comm, add_left_comm, add_assoc] using
    (one_div_le_one_div_of_le hm hle)

omit [NeZero d] in
lemma unitBallBadAnnulusOne_antitone :
    Antitone (fun n : ℕ => unitBallBadAnnulusOne (d := d) (unitBallApproxEps n)) := by
  intro m n hmn x hx
  rcases hx with ⟨hx1, hx2⟩
  refine ⟨?_, ?_⟩
  · have hle := unitBallApproxEps_antitone hmn
    linarith
  · have hle := unitBallApproxEps_antitone hmn
    linarith

omit [NeZero d] in
lemma unitBallBadAnnulusTwo_antitone :
    Antitone (fun n : ℕ => unitBallBadAnnulusTwo (d := d) (unitBallApproxEps n)) := by
  intro m n hmn x hx
  rcases hx with ⟨hx1, hx2⟩
  refine ⟨?_, ?_⟩
  · have hle := unitBallApproxEps_antitone hmn
    linarith
  · have hle := unitBallApproxEps_antitone hmn
    linarith

def sphereOneControl : Set E :=
  {x : E | (3 / 4 : ℝ) ≤ ‖x‖ ∧ ‖x‖ ≤ 5 / 4}

def sphereTwoControl : Set E :=
  {x : E | (7 / 4 : ℝ) ≤ ‖x‖ ∧ ‖x‖ ≤ 9 / 4}

lemma unitBallApproxEps_le_one_fifth (n : ℕ) :
    unitBallApproxEps n ≤ (1 / 5 : ℝ) := by
  unfold unitBallApproxEps
  have hpos : 0 < (n : ℝ) + 5 := by positivity
  field_simp [hpos.ne']
  nlinarith

omit [NeZero d] in
lemma badAnnulusOne_subset_sphereOneControl (n : ℕ) :
    unitBallBadAnnulusOne (d := d) (unitBallApproxEps n) ⊆ sphereOneControl (d := d) := by
  intro x hx
  have hε : unitBallApproxEps n ≤ (1 / 5 : ℝ) := unitBallApproxEps_le_one_fifth n
  constructor
  · linarith [hx.1, hε]
  · linarith [hx.2, hε]

omit [NeZero d] in
lemma badAnnulusTwo_subset_sphereTwoControl (n : ℕ) :
    unitBallBadAnnulusTwo (d := d) (unitBallApproxEps n) ⊆ sphereTwoControl (d := d) := by
  intro x hx
  have hε : unitBallApproxEps n ≤ (1 / 5 : ℝ) := unitBallApproxEps_le_one_fifth n
  constructor
  · linarith [hx.1, hε]
  · linarith [hx.2, hε]

omit [NeZero d] in
lemma sphereOneControl_subset_closedBall :
    sphereOneControl (d := d) ⊆ Metric.closedBall (0 : E) (5 / 4 : ℝ) := by
  intro x hx
  rw [Metric.mem_closedBall, dist_zero_right]
  exact hx.2

omit [NeZero d] in
lemma sphereTwoControl_subset_closedBall :
    sphereTwoControl (d := d) ⊆ Metric.closedBall (0 : E) (9 / 4 : ℝ) := by
  intro x hx
  rw [Metric.mem_closedBall, dist_zero_right]
  exact hx.2

omit [NeZero d] in
lemma measure_unitBallBadAnnulusOne_lt_top (n : ℕ) :
    volume (unitBallBadAnnulusOne (d := d) (unitBallApproxEps n)) < ⊤ := by
  refine lt_of_le_of_lt
    (measure_mono (badAnnulusOne_subset_sphereOneControl (d := d) n |>.trans
      sphereOneControl_subset_closedBall)) ?_
  simpa using
    (measure_closedBall_lt_top (μ := (volume : Measure E)) (x := (0 : E)) (r := (5 / 4 : ℝ)))

omit [NeZero d] in
lemma measure_unitBallBadAnnulusTwo_lt_top (n : ℕ) :
    volume (unitBallBadAnnulusTwo (d := d) (unitBallApproxEps n)) < ⊤ := by
  refine lt_of_le_of_lt
    (measure_mono (badAnnulusTwo_subset_sphereTwoControl (d := d) n |>.trans
      sphereTwoControl_subset_closedBall)) ?_
  simpa using
    (measure_closedBall_lt_top (μ := (volume : Measure E)) (x := (0 : E)) (r := (9 / 4 : ℝ)))

omit [NeZero d] in
lemma iInter_unitBallBadAnnulusOne_eq_sphere :
    (⋂ n : ℕ, unitBallBadAnnulusOne (d := d) (unitBallApproxEps n)) =
      Metric.sphere (0 : E) 1 := by
  ext x
  constructor
  · intro hx
    rw [Metric.mem_sphere, dist_zero_right]
    by_cases hEq : ‖x‖ = 1
    · exact hEq
    · have hgap : 0 < |‖x‖ - 1| := abs_pos.mpr (sub_ne_zero.mpr hEq)
      have hev : ∀ᶠ n in atTop, unitBallApproxEps n < |‖x‖ - 1| :=
        tendsto_unitBallApproxEps (Iio_mem_nhds hgap)
      rcases (eventually_atTop.1 hev) with ⟨N, hN⟩
      have hxN := mem_iInter.1 hx N
      have hlt : unitBallApproxEps N < |‖x‖ - 1| := hN N le_rfl
      rcases hxN with ⟨hx1, hx2⟩
      have habs : |‖x‖ - 1| < unitBallApproxEps N := by
        rw [abs_sub_lt_iff]
        constructor <;> linarith
      linarith
  · intro hx
    rw [Metric.mem_sphere, dist_zero_right] at hx
    refine mem_iInter.2 ?_
    intro n
    constructor <;> simp [hx, unitBallApproxEps_pos n]

omit [NeZero d] in
lemma iInter_unitBallBadAnnulusTwo_eq_sphere :
    (⋂ n : ℕ, unitBallBadAnnulusTwo (d := d) (unitBallApproxEps n)) =
      Metric.sphere (0 : E) 2 := by
  ext x
  constructor
  · intro hx
    rw [Metric.mem_sphere, dist_zero_right]
    by_cases hEq : ‖x‖ = 2
    · exact hEq
    · have hgap : 0 < |‖x‖ - 2| := abs_pos.mpr (sub_ne_zero.mpr hEq)
      have hev : ∀ᶠ n in atTop, unitBallApproxEps n < |‖x‖ - 2| :=
        tendsto_unitBallApproxEps (Iio_mem_nhds hgap)
      rcases (eventually_atTop.1 hev) with ⟨N, hN⟩
      have hxN := mem_iInter.1 hx N
      have hlt : unitBallApproxEps N < |‖x‖ - 2| := hN N le_rfl
      rcases hxN with ⟨hx1, hx2⟩
      have habs : |‖x‖ - 2| < unitBallApproxEps N := by
        rw [abs_sub_lt_iff]
        constructor <;> linarith
      linarith
  · intro hx
    rw [Metric.mem_sphere, dist_zero_right] at hx
    refine mem_iInter.2 ?_
    intro n
    constructor <;> simp [hx, unitBallApproxEps_pos n]

lemma tendsto_measure_unitBallBadAnnulusOne :
    Tendsto (fun n => volume (unitBallBadAnnulusOne (d := d) (unitBallApproxEps n)))
      atTop (nhds 0) := by
  have h :=
    tendsto_measure_iInter_atTop
      (μ := volume)
      (s := fun n : ℕ => unitBallBadAnnulusOne (d := d) (unitBallApproxEps n))
      (fun n => (measurableSet_unitBallBadAnnulusOne (d := d) _).nullMeasurableSet)
      unitBallBadAnnulusOne_antitone
      ⟨0, (measure_unitBallBadAnnulusOne_lt_top (d := d) 0).ne⟩
  have hsphere_zero : volume (Metric.sphere (0 : E) 1) = 0 := by
    simpa using (Measure.addHaar_sphere (μ := (volume : Measure E)) (x := (0 : E)) 1)
  rw [iInter_unitBallBadAnnulusOne_eq_sphere (d := d), hsphere_zero] at h
  simpa using h

lemma tendsto_measure_unitBallBadAnnulusTwo :
    Tendsto (fun n => volume (unitBallBadAnnulusTwo (d := d) (unitBallApproxEps n)))
      atTop (nhds 0) := by
  have h :=
    tendsto_measure_iInter_atTop
      (μ := volume)
      (s := fun n : ℕ => unitBallBadAnnulusTwo (d := d) (unitBallApproxEps n))
      (fun n => (measurableSet_unitBallBadAnnulusTwo (d := d) _).nullMeasurableSet)
      unitBallBadAnnulusTwo_antitone
      ⟨0, (measure_unitBallBadAnnulusTwo_lt_top (d := d) 0).ne⟩
  have hsphere_zero : volume (Metric.sphere (0 : E) 2) = 0 := by
    simpa using (Measure.addHaar_sphere (μ := (volume : Measure E)) (x := (0 : E)) 2)
  rw [iInter_unitBallBadAnnulusTwo_eq_sphere (d := d), hsphere_zero] at h
  simpa using h

omit [NeZero d] in
lemma tendsto_smoothUnitBallExtensionApprox_pointwise
    {ψ : E → ℝ} {x : E}
    (hx1 : ‖x‖ ≠ 1) (hx2 : ‖x‖ ≠ 2) :
    Tendsto
      (fun n => smoothUnitBallExtensionApprox (d := d) (unitBallApproxEps n) ψ x)
      atTop (nhds (unitBallExtension (d := d) ψ x)) := by
  have hε := tendsto_unitBallApproxEps
  by_cases hlt1 : ‖x‖ < 1
  · have hgap : 0 < 1 - ‖x‖ := by linarith
    have hev :
        ∀ᶠ n in atTop, unitBallApproxEps n < 1 - ‖x‖ := hε (Iio_mem_nhds hgap)
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hev] with n hn
    have hxball : x ∈ Metric.ball (0 : E) (1 - unitBallApproxEps n) := by
      rw [Metric.mem_ball, dist_zero_right]
      linarith
    exact (smoothUnitBallExtensionApprox_eq_of_mem_innerCore (d := d)
      (unitBallApproxEps_pos n) hxball).symm
  · have hge1 : 1 ≤ ‖x‖ := by linarith
    by_cases hlt2 : ‖x‖ < 2
    · have hgt1 : 1 < ‖x‖ := by
        have hx1' : (1 : ℝ) ≠ ‖x‖ := by simpa [eq_comm] using hx1
        exact lt_of_le_of_ne hge1 hx1'
      let δ : ℝ := min (‖x‖ - 1) (2 - ‖x‖)
      have hδ : 0 < δ := by
        dsimp [δ]
        exact lt_min (by linarith) (by linarith)
      have hev : ∀ᶠ n in atTop, unitBallApproxEps n < δ := hε (Iio_mem_nhds hδ)
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [hev] with n hn
      have hxl : 1 + unitBallApproxEps n < ‖x‖ := by
        dsimp [δ] at hn
        have : unitBallApproxEps n < ‖x‖ - 1 := lt_of_lt_of_le hn (min_le_left _ _)
        linarith
      have hxr : ‖x‖ < 2 - unitBallApproxEps n := by
        dsimp [δ] at hn
        have : unitBallApproxEps n < 2 - ‖x‖ := lt_of_lt_of_le hn (min_le_right _ _)
        linarith
      exact (smoothUnitBallExtensionApprox_eq_of_mem_shellCore (d := d)
        (unitBallApproxEps_pos n) hxl hxr).symm
    · have hge2 : 2 ≤ ‖x‖ := by linarith
      have hgt2 : 2 < ‖x‖ := by
        have hx2' : (2 : ℝ) ≠ ‖x‖ := by simpa [eq_comm] using hx2
        exact lt_of_le_of_ne hge2 hx2'
      have hgap : 0 < ‖x‖ - 2 := by linarith
      have hev : ∀ᶠ n in atTop, unitBallApproxEps n < ‖x‖ - 2 := hε (Iio_mem_nhds hgap)
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [hev] with n hn
      have hxge : 2 + unitBallApproxEps n ≤ ‖x‖ := by linarith
      exact (smoothUnitBallExtensionApprox_eq_of_norm_ge (d := d)
        (unitBallApproxEps_pos n) hxge).symm

omit [NeZero d] in
lemma tendsto_fderiv_smoothUnitBallExtensionApprox_pointwise
    {ψ : E → ℝ} {x : E}
    (hx1 : ‖x‖ ≠ 1) (hx2 : ‖x‖ ≠ 2) :
    Tendsto
      (fun n => fderiv ℝ (smoothUnitBallExtensionApprox (d := d) (unitBallApproxEps n) ψ) x)
      atTop (nhds (fderiv ℝ (unitBallExtension (d := d) ψ) x)) := by
  have hε := tendsto_unitBallApproxEps
  by_cases hlt1 : ‖x‖ < 1
  · have hgap : 0 < 1 - ‖x‖ := by linarith
    have hev :
        ∀ᶠ n in atTop, unitBallApproxEps n < 1 - ‖x‖ := hε (Iio_mem_nhds hgap)
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hev] with n hn
    have hxball : x ∈ Metric.ball (0 : E) (1 - unitBallApproxEps n) := by
      rw [Metric.mem_ball, dist_zero_right]
      linarith
    have hEq :
        smoothUnitBallExtensionApprox (d := d) (unitBallApproxEps n) ψ =ᶠ[𝓝 x]
          unitBallExtension (d := d) ψ := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hxball] with y hy
      exact smoothUnitBallExtensionApprox_eq_of_mem_innerCore (d := d)
        (unitBallApproxEps_pos n) hy
    exact (Filter.EventuallyEq.fderiv_eq (𝕜 := ℝ) hEq).symm
  · have hge1 : 1 ≤ ‖x‖ := by linarith
    by_cases hlt2 : ‖x‖ < 2
    · have hgt1 : 1 < ‖x‖ := lt_of_le_of_ne hge1 hx1.symm
      let δ : ℝ := min (‖x‖ - 1) (2 - ‖x‖)
      have hδ : 0 < δ := by
        dsimp [δ]
        exact lt_min (by linarith) (by linarith)
      have hev : ∀ᶠ n in atTop, unitBallApproxEps n < δ := hε (Iio_mem_nhds hδ)
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [hev] with n hn
      have hxl : 1 + unitBallApproxEps n < ‖x‖ := by
        dsimp [δ] at hn
        have : unitBallApproxEps n < ‖x‖ - 1 := lt_of_lt_of_le hn (min_le_left _ _)
        linarith
      have hxr : ‖x‖ < 2 - unitBallApproxEps n := by
        dsimp [δ] at hn
        have : unitBallApproxEps n < 2 - ‖x‖ := lt_of_lt_of_le hn (min_le_right _ _)
        linarith
      have hxOuter : x ∈ unitBallOuterShell (d := d) := by constructor <;> linarith
      have hEq :
          smoothUnitBallExtensionApprox (d := d) (unitBallApproxEps n) ψ =ᶠ[𝓝 x]
            unitBallExtension (d := d) ψ := by
        have hLeft :
            {y : E | 1 + unitBallApproxEps n < ‖y‖} ∈ 𝓝 x :=
          (isOpen_lt continuous_const continuous_norm).mem_nhds hxl
        have hRight :
            {y : E | ‖y‖ < 2 - unitBallApproxEps n} ∈ 𝓝 x :=
          (isOpen_lt continuous_norm continuous_const).mem_nhds hxr
        filter_upwards [hLeft, hRight] with y hyL hyR
        exact smoothUnitBallExtensionApprox_eq_of_mem_shellCore (d := d)
          (unitBallApproxEps_pos n) hyL hyR
      have hShell :
          fderiv ℝ (unitBallExtension (d := d) ψ) x =
            fderiv ℝ (unitBallShellFormula (d := d) ψ) x :=
        fderiv_unitBallExtension_eq_shellFormula_of_mem_outerShell (d := d) hxOuter
      rw [hShell]
      have hEqShell :
          smoothUnitBallExtensionApprox (d := d) (unitBallApproxEps n) ψ =ᶠ[𝓝 x]
            unitBallShellFormula (d := d) ψ := by
        filter_upwards [hEq, isOpen_unitBallOuterShell (d := d) |>.mem_nhds hxOuter] with y hyEq hyOuter
        simpa [unitBallExtension_eq_shellFormula_of_mem_outerShell (d := d) hyOuter] using hyEq
      exact (Filter.EventuallyEq.fderiv_eq (𝕜 := ℝ) hEqShell).symm
    · have hge2 : 2 ≤ ‖x‖ := by linarith
      have hgt2 : 2 < ‖x‖ := lt_of_le_of_ne hge2 hx2.symm
      have hgap : 0 < ‖x‖ - 2 := by linarith
      have hev : ∀ᶠ n in atTop, unitBallApproxEps n < ‖x‖ - 2 := hε (Iio_mem_nhds hgap)
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [hev] with n hn
      have hxgt : 2 + unitBallApproxEps n < ‖x‖ := by linarith
      have hZeroEq :
          smoothUnitBallExtensionApprox (d := d) (unitBallApproxEps n) ψ =ᶠ[𝓝 x]
            unitBallExtension (d := d) ψ := by
        have hNhds :
            {y : E | 2 + unitBallApproxEps n < ‖y‖} ∈ 𝓝 x :=
          (isOpen_lt continuous_const continuous_norm).mem_nhds hxgt
        filter_upwards [hNhds] with y hy
        have hy1 : smoothUnitBallExtensionApprox (d := d) (unitBallApproxEps n) ψ y = 0 := by
          exact smoothUnitBallExtensionApprox_eq_zero_of_norm_ge (d := d)
            (unitBallApproxEps_pos n) (le_of_lt hy)
        have hy2 : unitBallExtension (d := d) ψ y = 0 := by
          have hy2' : 2 ≤ ‖y‖ := by
            have hεpos : 0 < unitBallApproxEps n := unitBallApproxEps_pos n
            linarith
          exact unitBallExtension_eq_zero_of_two_le_norm (d := d) hy2'
        simp [hy1, hy2]
      exact (Filter.EventuallyEq.fderiv_eq (𝕜 := ℝ) hZeroEq).symm

def unitBallBadSet (ε : ℝ) : Set E :=
  unitBallBadAnnulusOne (d := d) ε ∪ unitBallBadAnnulusTwo (d := d) ε

noncomputable def smoothUnitBallExtensionFDerivCandidate (ψ : E → ℝ) (x : E) :
    E →L[ℝ] ℝ := by
  classical
  exact
    if ‖x‖ < 1 then
      fderiv ℝ ψ x
    else if x ∈ unitBallOuterShell (d := d) then
      fderiv ℝ (unitBallShellFormula (d := d) ψ) x
    else
      0

noncomputable def smoothUnitBallExtensionGradCandidate (ψ : E → ℝ) : E → E := by
  classical
  exact fun x =>
    WithLp.toLp 2 fun i =>
      smoothUnitBallExtensionFDerivCandidate (d := d) ψ x (EuclideanSpace.single i 1)

omit [NeZero d] in
lemma fderiv_unitBallExtension_eq_zero_of_norm_gt_two
    {ψ : E → ℝ} {x : E} (hx : 2 < ‖x‖) :
    fderiv ℝ (unitBallExtension (d := d) ψ) x = 0 := by
  have hNhds : {y : E | 2 < ‖y‖} ∈ 𝓝 x :=
    (isOpen_lt continuous_const continuous_norm).mem_nhds hx
  have hEq : unitBallExtension (d := d) ψ =ᶠ[𝓝 x] fun _ : E => (0 : ℝ) := by
    filter_upwards [hNhds] with y hy
    exact unitBallExtension_eq_zero_of_two_le_norm (d := d) (le_of_lt hy)
  simpa using (hEq.symm.fderiv_eq).symm

omit [NeZero d] in
lemma smoothUnitBallExtensionGradCandidate_eq_grad_of_not_mem_spheres
    {ψ : E → ℝ} {x : E}
    (hx1 : x ∉ Metric.sphere (0 : E) 1)
    (hx2 : x ∉ Metric.sphere (0 : E) 2) :
    smoothUnitBallExtensionGradCandidate (d := d) ψ x =
      smoothUnitBallExtensionGrad (d := d) ψ x := by
  classical
  unfold smoothUnitBallExtensionGradCandidate smoothUnitBallExtensionGrad
  ext i
  by_cases hlt1 : ‖x‖ < 1
  · have hxball : x ∈ Metric.ball (0 : E) 1 := by
      rwa [Metric.mem_ball, dist_zero_right]
    simpa [smoothUnitBallExtensionFDerivCandidate, hlt1, PiLp.toLp_apply] using
      (congrArg (fun T : E →L[ℝ] ℝ => T (EuclideanSpace.single i 1))
        (fderiv_unitBallExtension_eq_of_mem_ball (d := d) hxball)).symm
  · have hge1 : 1 ≤ ‖x‖ := by linarith
    by_cases hlt2 : ‖x‖ < 2
    · have hgt1 : 1 < ‖x‖ := by
        rw [Metric.mem_sphere, dist_zero_right] at hx1
        have hx1' : (1 : ℝ) ≠ ‖x‖ := by simpa [eq_comm] using hx1
        exact lt_of_le_of_ne hge1 hx1'
      have hxShell : x ∈ unitBallOuterShell (d := d) := by
        constructor <;> linarith
      simpa [smoothUnitBallExtensionFDerivCandidate, hlt1, hxShell, PiLp.toLp_apply] using
        (congrArg (fun T : E →L[ℝ] ℝ => T (EuclideanSpace.single i 1))
          (fderiv_unitBallExtension_eq_shellFormula_of_mem_outerShell (d := d) hxShell)).symm
    · have hge2 : 2 ≤ ‖x‖ := by linarith
      have hgt2 : 2 < ‖x‖ := by
        rw [Metric.mem_sphere, dist_zero_right] at hx2
        have hx2' : (2 : ℝ) ≠ ‖x‖ := by simpa [eq_comm] using hx2
        exact lt_of_le_of_ne hge2 hx2'
      have hnotOuter : x ∉ unitBallOuterShell (d := d) := by
        intro hxOuter
        linarith [hxOuter.2, hge2]
      simpa [smoothUnitBallExtensionFDerivCandidate, hlt1, hnotOuter, PiLp.toLp_apply] using
        (congrArg (fun T : E →L[ℝ] ℝ => T (EuclideanSpace.single i 1))
          (fderiv_unitBallExtension_eq_zero_of_norm_gt_two (d := d) hgt2)).symm

lemma ae_eq_smoothUnitBallExtensionGradCandidate
    {ψ : E → ℝ} :
    smoothUnitBallExtensionGradCandidate (d := d) ψ =ᵐ[volume]
      smoothUnitBallExtensionGrad (d := d) ψ := by
  have hs1 : volume (Metric.sphere (0 : E) 1) = 0 := by
    simpa using (Measure.addHaar_sphere (μ := (volume : Measure E)) (x := (0 : E)) 1)
  have hs2 : volume (Metric.sphere (0 : E) 2) = 0 := by
    simpa using (Measure.addHaar_sphere (μ := (volume : Measure E)) (x := (0 : E)) 2)
  have hs1' : ∀ᵐ x ∂volume, x ∉ Metric.sphere (0 : E) 1 := by
    rw [ae_iff]
    simpa [Metric.sphere, dist_zero_right] using hs1
  have hs2' : ∀ᵐ x ∂volume, x ∉ Metric.sphere (0 : E) 2 := by
    rw [ae_iff]
    simpa [Metric.sphere, dist_zero_right] using hs2
  filter_upwards [hs1', hs2'] with x hx1 hx2
  exact smoothUnitBallExtensionGradCandidate_eq_grad_of_not_mem_spheres (d := d) hx1 hx2

noncomputable def exactUnitBallShellOrZero (ψ : E → ℝ) : E → ℝ := by
  classical
  exact (unitBallOuterShell (d := d)).piecewise (unitBallShellFormula (d := d) ψ) 0

noncomputable def exactUnitBallExtensionModel (ψ : E → ℝ) : E → ℝ := by
  classical
  exact (Metric.closedBall (0 : E) 1).piecewise ψ (exactUnitBallShellOrZero (d := d) ψ)

noncomputable def exactUnitBallShellGradApply (ψ : E → ℝ) (i : Fin d) : E → ℝ := by
  classical
  exact (unitBallOuterShell (d := d)).piecewise
    (fun x => (fderiv ℝ (unitBallShellFormula (d := d) ψ) x) (EuclideanSpace.single i 1))
    0

noncomputable def exactUnitBallExtensionGradApply (ψ : E → ℝ) (i : Fin d) : E → ℝ := by
  classical
  exact (Metric.ball (0 : E) 1).piecewise
    (fun x => (fderiv ℝ ψ x) (EuclideanSpace.single i 1))
    (exactUnitBallShellGradApply (d := d) ψ i)

noncomputable def exactUnitBallExtensionGrad (ψ : E → ℝ) : E → E := by
  classical
  exact fun x => WithLp.toLp 2 fun i => exactUnitBallExtensionGradApply (d := d) ψ i x

omit [NeZero d] in
lemma exactUnitBallShellOrZero_eq_unitBallExtension
    {ψ : E → ℝ} {x : E} (hx : x ∉ Metric.closedBall (0 : E) 1) :
    exactUnitBallShellOrZero (d := d) ψ x = unitBallExtension (d := d) ψ x := by
  classical
  by_cases hOuter : x ∈ unitBallOuterShell (d := d)
  · unfold exactUnitBallShellOrZero
    simp [hOuter, unitBallExtension_eq_shellFormula_of_mem_outerShell (d := d) hOuter]
  · unfold exactUnitBallShellOrZero
    simp [hOuter]
    have hgt1 : 1 < ‖x‖ := by
      rw [Metric.mem_closedBall, dist_zero_right] at hx
      linarith
    have hnorm : 2 ≤ ‖x‖ := by
      by_cases hlt2 : ‖x‖ < 2
      · exact False.elim (hOuter ⟨hgt1, hlt2⟩)
      · exact le_of_not_gt hlt2
    simpa using (unitBallExtension_eq_zero_of_two_le_norm (d := d) (u := ψ) hnorm).symm

omit [NeZero d] in
lemma exactUnitBallExtensionModel_eq_unitBallExtension
    {ψ : E → ℝ} :
    exactUnitBallExtensionModel (d := d) ψ = unitBallExtension (d := d) ψ := by
  classical
  funext x
  by_cases hx : x ∈ Metric.closedBall (0 : E) 1
  · have hnorm : ‖x‖ ≤ 1 := by
      rw [Metric.mem_closedBall, dist_zero_right] at hx
      exact hx
    have hret : unitBallRetraction (d := d) x = x :=
      unitBallRetraction_eq_self_of_norm_le_one (d := d) hnorm
    have hcut : unitBallCutoff (d := d) x = 1 := by
      unfold unitBallCutoff
      rw [max_eq_left (by linarith), min_eq_left (by linarith)]
    unfold exactUnitBallExtensionModel
    simp [hx, unitBallExtension, hret, hcut]
  · unfold exactUnitBallExtensionModel
    simp [hx, exactUnitBallShellOrZero_eq_unitBallExtension (d := d) hx]

omit [NeZero d] in
lemma continuousOn_unitBallShellFormula_outerShell
    {ψ : E → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) :
    ContinuousOn (unitBallShellFormula (d := d) ψ) (unitBallOuterShell (d := d)) := by
  intro x hx
  have hx0 : x ≠ (0 : E) := by
    have : 0 < ‖x‖ := by linarith [hx.1]
    intro hx0
    simpa [hx0] using this.ne'
  exact (contDiffAt_unitBallShellFormula (d := d) hψ hx0).continuousAt.continuousWithinAt

omit [NeZero d] in
lemma measurable_exactUnitBallShellOrZero
    {ψ : E → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) :
    Measurable (exactUnitBallShellOrZero (d := d) ψ) := by
  classical
  unfold exactUnitBallShellOrZero
  refine ContinuousOn.measurable_piecewise
    (hf := continuousOn_unitBallShellFormula_outerShell (d := d) hψ)
    (hg := continuousOn_const)
    measurableSet_unitBallOuterShell

omit [NeZero d] in
lemma measurable_exactUnitBallExtensionModel
    {ψ : E → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) :
    Measurable (exactUnitBallExtensionModel (d := d) ψ) := by
  classical
  unfold exactUnitBallExtensionModel
  exact Measurable.piecewise Metric.isClosed_closedBall.measurableSet
    hψ.continuous.measurable (measurable_exactUnitBallShellOrZero (d := d) hψ)

omit [NeZero d] in
lemma continuousOn_exactUnitBallShellGradApply
    {ψ : E → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (i : Fin d) :
    ContinuousOn
      (fun x => (fderiv ℝ (unitBallShellFormula (d := d) ψ) x) (EuclideanSpace.single i 1))
      (unitBallOuterShell (d := d)) := by
  intro x hx
  have hx0 : x ≠ (0 : E) := by
    have : 0 < ‖x‖ := by linarith [hx.1]
    intro hx0
    simpa [hx0] using this.ne'
  exact ((contDiffAt_unitBallShellFormula (d := d) hψ hx0).continuousAt_fderiv
      (by simp : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0)).clm_apply continuousAt_const |>.continuousWithinAt

omit [NeZero d] in
lemma measurable_exactUnitBallShellGradApply
    {ψ : E → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (i : Fin d) :
    Measurable (exactUnitBallShellGradApply (d := d) ψ i) := by
  classical
  unfold exactUnitBallShellGradApply
  refine ContinuousOn.measurable_piecewise
    (hf := continuousOn_exactUnitBallShellGradApply (d := d) hψ i)
    (hg := continuousOn_const)
    measurableSet_unitBallOuterShell

omit [NeZero d] in
lemma measurable_exactUnitBallExtensionGradApply
    {ψ : E → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (i : Fin d) :
    Measurable (exactUnitBallExtensionGradApply (d := d) ψ i) := by
  classical
  unfold exactUnitBallExtensionGradApply
  have hball :
      Measurable (fun x => (fderiv ℝ ψ x) (EuclideanSpace.single i 1)) := by
    exact ((hψ.continuous_fderiv (by simp : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0)).clm_apply
      continuous_const).measurable
  exact Measurable.piecewise Metric.isOpen_ball.measurableSet
    hball (measurable_exactUnitBallShellGradApply (d := d) hψ i)

omit [NeZero d] in
lemma exactUnitBallExtensionGradApply_eq_candidate
    {ψ : E → ℝ} (i : Fin d) :
    exactUnitBallExtensionGradApply (d := d) ψ i =
      fun x => smoothUnitBallExtensionGradCandidate (d := d) ψ x i := by
  classical
  funext x
  by_cases hxball : x ∈ Metric.ball (0 : E) 1
  · have hlt : ‖x‖ < 1 := by simpa [Metric.mem_ball, dist_zero_right] using hxball
    simp [exactUnitBallExtensionGradApply, smoothUnitBallExtensionGradCandidate,
      smoothUnitBallExtensionFDerivCandidate, hxball, hlt, PiLp.toLp_apply]
  · by_cases hOuter : x ∈ unitBallOuterShell (d := d)
    · have hnotlt : ¬ ‖x‖ < 1 := by
        intro hlt
        exact hxball (by simpa [Metric.mem_ball, dist_zero_right] using hlt)
      simp [exactUnitBallExtensionGradApply, exactUnitBallShellGradApply,
        smoothUnitBallExtensionGradCandidate, smoothUnitBallExtensionFDerivCandidate,
        hxball, hOuter, hnotlt, PiLp.toLp_apply]
    · have hnotlt : ¬ ‖x‖ < 1 := by
        intro hlt
        exact hxball (by simpa [Metric.mem_ball, dist_zero_right] using hlt)
      simp [exactUnitBallExtensionGradApply, exactUnitBallShellGradApply,
        smoothUnitBallExtensionGradCandidate, smoothUnitBallExtensionFDerivCandidate,
        hxball, hOuter, hnotlt, PiLp.toLp_apply]

lemma ae_eq_exactUnitBallExtensionGrad
    {ψ : E → ℝ} :
    exactUnitBallExtensionGrad (d := d) ψ =ᵐ[volume]
      smoothUnitBallExtensionGrad (d := d) ψ := by
  classical
  have hcomp : exactUnitBallExtensionGrad (d := d) ψ =ᵐ[volume]
      smoothUnitBallExtensionGradCandidate (d := d) ψ :=
    Filter.Eventually.of_forall fun x => by
      ext i
      simpa [exactUnitBallExtensionGrad] using
        congrFun (exactUnitBallExtensionGradApply_eq_candidate (d := d) (ψ := ψ) i) x
  exact hcomp.trans (ae_eq_smoothUnitBallExtensionGradCandidate (d := d) (ψ := ψ))

omit [NeZero d] in
lemma measurableSet_unitBallBadSet (ε : ℝ) :
    MeasurableSet (unitBallBadSet (d := d) ε) := by
  unfold unitBallBadSet
  exact (measurableSet_unitBallBadAnnulusOne (d := d) ε).union
    (measurableSet_unitBallBadAnnulusTwo (d := d) ε)

omit [NeZero d] in
lemma eventually_not_mem_unitBallBadSet {x : E}
    (hx1 : ‖x‖ ≠ 1) (hx2 : ‖x‖ ≠ 2) :
    ∀ᶠ n in atTop, x ∉ unitBallBadSet (d := d) (unitBallApproxEps n) := by
  by_cases hlt1 : ‖x‖ < 1
  · have hgap : 0 < 1 - ‖x‖ := by linarith
    have hev : ∀ᶠ n in atTop, unitBallApproxEps n < 1 - ‖x‖ :=
      tendsto_unitBallApproxEps (Iio_mem_nhds hgap)
    filter_upwards [hev] with n hn
    intro hxbad
    rcases hxbad with hxbad | hxbad
    · linarith [hxbad.1]
    · linarith [hxbad.1]
  · have hge1 : 1 ≤ ‖x‖ := by linarith
    by_cases hlt2 : ‖x‖ < 2
    · have hgt1 : 1 < ‖x‖ := by
        have hne1 : 1 ≠ ‖x‖ := by
          intro hEq
          exact hx1 (by simpa [Metric.mem_sphere, dist_zero_right, eq_comm] using hEq)
        exact lt_of_le_of_ne hge1 hne1
      let δ : ℝ := min (‖x‖ - 1) (2 - ‖x‖)
      have hδ : 0 < δ := by
        dsimp [δ]
        exact lt_min (sub_pos.mpr hgt1) (sub_pos.mpr hlt2)
      have hev : ∀ᶠ n in atTop, unitBallApproxEps n < δ :=
        tendsto_unitBallApproxEps (Iio_mem_nhds hδ)
      filter_upwards [hev] with n hn
      intro hxbad
      rcases hxbad with hxbad | hxbad
      · dsimp [δ] at hn
        have h1 : unitBallApproxEps n < ‖x‖ - 1 := lt_of_lt_of_le hn (min_le_left _ _)
        have h2 : unitBallApproxEps n < 2 - ‖x‖ := lt_of_lt_of_le hn (min_le_right _ _)
        linarith [hxbad.1, hxbad.2, h1, h2]
      · dsimp [δ] at hn
        have h2 : unitBallApproxEps n < 2 - ‖x‖ := lt_of_lt_of_le hn (min_le_right _ _)
        linarith [hxbad.1, h2]
    · have hge2 : 2 ≤ ‖x‖ := by linarith
      have hgt2 : 2 < ‖x‖ := by
        have hne2 : 2 ≠ ‖x‖ := by
          intro hEq
          exact hx2 (by simpa [Metric.mem_sphere, dist_zero_right, eq_comm] using hEq)
        exact lt_of_le_of_ne hge2 hne2
      have hgap : 0 < ‖x‖ - 2 := by linarith
      have hev : ∀ᶠ n in atTop, unitBallApproxEps n < ‖x‖ - 2 :=
        tendsto_unitBallApproxEps (Iio_mem_nhds hgap)
      filter_upwards [hev] with n hn
      intro hxbad
      rcases hxbad with hxbad | hxbad
      · linarith [hxbad.2, hn]
      · linarith [hxbad.2, hn]

lemma tendsto_measure_unitBallBadSet :
    Tendsto (fun n => volume (unitBallBadSet (d := d) (unitBallApproxEps n)))
      atTop (nhds 0) := by
  have hle :
      (fun n => volume (unitBallBadSet (d := d) (unitBallApproxEps n))) ≤
        fun n =>
          volume (unitBallBadAnnulusOne (d := d) (unitBallApproxEps n)) +
            volume (unitBallBadAnnulusTwo (d := d) (unitBallApproxEps n)) := by
    intro n
    exact measure_union_le _ _
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le
    (g := fun _ : ℕ => (0 : ℝ≥0∞))
    (h := fun n =>
      volume (unitBallBadAnnulusOne (d := d) (unitBallApproxEps n)) +
        volume (unitBallBadAnnulusTwo (d := d) (unitBallApproxEps n)))
    tendsto_const_nhds
    ?_
    (fun _ => bot_le)
    hle
  simpa [unitBallBadSet] using
    (tendsto_measure_unitBallBadAnnulusOne (d := d)).add
      (tendsto_measure_unitBallBadAnnulusTwo (d := d))

omit [NeZero d] in
lemma smoothUnitBallExtensionApprox_eq_unitBallExtension_of_not_mem_badSet
    {ψ : E → ℝ} {n : ℕ} {x : E}
    (hx : x ∉ unitBallBadSet (d := d) (unitBallApproxEps n)) :
    smoothUnitBallExtensionApprox (d := d) (unitBallApproxEps n) ψ x =
      unitBallExtension (d := d) ψ x := by
  let ε := unitBallApproxEps n
  have hε : 0 < unitBallApproxEps n := unitBallApproxEps_pos n
  have hx1 : x ∉ unitBallBadAnnulusOne (d := d) (unitBallApproxEps n) := by
    intro hx1
    exact hx (Or.inl hx1)
  have hx2 : x ∉ unitBallBadAnnulusTwo (d := d) (unitBallApproxEps n) := by
    intro hx2
    exact hx (Or.inr hx2)
  by_cases hinner : ‖x‖ ≤ 1 - ε
  · exact smoothUnitBallExtensionApprox_eq_of_norm_le_innerCore (d := d) hε hinner
  · by_cases hshell : 1 + ε ≤ ‖x‖ ∧ ‖x‖ ≤ 2 - ε
    · exact smoothUnitBallExtensionApprox_eq_of_shellCore_closed (d := d) hε hshell.1 hshell.2
    · have hnotInner : 1 - ε < ‖x‖ := lt_of_not_ge hinner
      have hnorm_ge : 2 + ε ≤ ‖x‖ := by
        by_contra hfar
        have hfar' : ‖x‖ < 2 + ε := by linarith
        by_cases hlt : ‖x‖ < 1 + ε
        · exact hx1 ⟨hnotInner, hlt⟩
        · have hge : 1 + ε ≤ ‖x‖ := le_of_not_gt hlt
          by_cases hmid : ‖x‖ ≤ 2 - ε
          · exact hshell ⟨hge, hmid⟩
          · exact hx2 ⟨lt_of_not_ge hmid, hfar'⟩
      exact smoothUnitBallExtensionApprox_eq_of_norm_ge (d := d) hε hnorm_ge

omit [NeZero d] in
lemma isCompact_sphereOneControl : IsCompact (sphereOneControl (d := d)) := by
  have hclosed : IsClosed (sphereOneControl (d := d)) := by
    unfold sphereOneControl
    exact (isClosed_le continuous_const continuous_norm).inter
      (isClosed_le continuous_norm continuous_const)
  refine (isCompact_closedBall (0 : E) (5 / 4 : ℝ)).of_isClosed_subset hclosed ?_
  intro x hx
  rw [Metric.mem_closedBall, dist_zero_right]
  exact hx.2

omit [NeZero d] in
lemma isCompact_sphereTwoControl : IsCompact (sphereTwoControl (d := d)) := by
  have hclosed : IsClosed (sphereTwoControl (d := d)) := by
    unfold sphereTwoControl
    exact (isClosed_le continuous_const continuous_norm).inter
      (isClosed_le continuous_norm continuous_const)
  refine (isCompact_closedBall (0 : E) (9 / 4 : ℝ)).of_isClosed_subset hclosed ?_
  intro x hx
  rw [Metric.mem_closedBall, dist_zero_right]
  exact hx.2

omit [NeZero d] in
theorem exists_fderiv_bound_on_compact
    {f : E → ℝ} {K U : Set E}
    (hK : IsCompact K) (hKU : K ⊆ U)
    (hcd : ∀ x ∈ U, ContDiffAt ℝ 1 f x) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ K, ‖fderiv ℝ f x‖ ≤ C := by
  have hcontU : ContinuousOn (fun x => fderiv ℝ f x) U := by
    intro x hx
    exact ((hcd x hx).continuousAt_fderiv (by simp : (1 : WithTop ℕ∞) ≠ 0)).continuousWithinAt
  rcases IsCompact.exists_bound_of_continuousOn hK (hcontU.mono hKU) with ⟨C, hC⟩
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro x hx
  exact (hC x hx).trans (le_max_left _ _)

omit [NeZero d] in
theorem exists_norm_bound_on_compact
    {f : E → ℝ} {K U : Set E}
    (hK : IsCompact K) (hKU : K ⊆ U)
    (hcont : ContinuousOn f U) :
    ∃ C : ℝ, ∀ x ∈ K, ‖f x‖ ≤ C := by
  rcases IsCompact.exists_bound_of_continuousOn hK (hcont.mono hKU) with ⟨C, hC⟩
  refine ⟨max C 0, ?_⟩
  intro x hx
  exact (hC x hx).trans (le_max_left _ _)

omit [NeZero d] in
lemma unitBallShellFormula_eq_on_sphereOne
    {ψ : E → ℝ} {x : E} (hx : x ∈ Metric.sphere (0 : E) 1) :
    unitBallShellFormula (d := d) ψ x = ψ x := by
  unfold unitBallShellFormula
  rw [EuclideanGeometry.inversion_of_mem_sphere hx]
  rw [Metric.mem_sphere, dist_zero_right] at hx
  simp [hx]
  ring

omit [NeZero d] in
lemma unitBallShellFormula_eq_zero_on_sphereTwo
    {ψ : E → ℝ} {x : E} (hx : x ∈ Metric.sphere (0 : E) 2) :
    unitBallShellFormula (d := d) ψ x = 0 := by
  unfold unitBallShellFormula
  rw [Metric.mem_sphere, dist_zero_right] at hx
  simp [hx]

omit [NeZero d] in
theorem exists_shellSubPsi_fderiv_bound
    {ψ : E → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ x ∈ sphereOneControl (d := d),
        ‖fderiv ℝ (fun y => unitBallShellFormula (d := d) ψ y - ψ y) x‖ ≤ C := by
  let f : E → ℝ := fun y => unitBallShellFormula (d := d) ψ y - ψ y
  have hsubset : sphereOneControl (d := d) ⊆ {x : E | x ≠ 0} := by
    intro x hx
    have : 0 < ‖x‖ := by linarith [hx.1]
    intro hx0
    simpa [hx0] using this.ne'
  rcases exists_fderiv_bound_on_compact (d := d)
      (f := f) (K := sphereOneControl (d := d)) (U := {x : E | x ≠ 0})
      isCompact_sphereOneControl hsubset
      (fun x hx =>
        ((contDiffAt_unitBallShellFormula (d := d) hψ hx).of_le (by norm_num)).sub
          ((hψ.contDiffAt).of_le (by norm_num))) with ⟨C, hC_nonneg, hC⟩
  exact ⟨C, hC_nonneg, hC⟩

omit [NeZero d] in
theorem exists_shellFormula_fderiv_bound
    {ψ : E → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ x ∈ sphereTwoControl (d := d),
        ‖fderiv ℝ (unitBallShellFormula (d := d) ψ) x‖ ≤ C := by
  have hsubset : sphereTwoControl (d := d) ⊆ {x : E | x ≠ 0} := by
    intro x hx
    have : 0 < ‖x‖ := by linarith [hx.1]
    intro hx0
    simpa [hx0] using this.ne'
  rcases exists_fderiv_bound_on_compact (d := d)
      (f := unitBallShellFormula (d := d) ψ) (K := sphereTwoControl (d := d))
      (U := {x : E | x ≠ 0}) isCompact_sphereTwoControl hsubset
      (fun x hx => (contDiffAt_unitBallShellFormula (d := d) hψ hx).of_le (by norm_num))
      with ⟨C, hC_nonneg, hC⟩
  exact ⟨C, hC_nonneg, hC⟩

def sphereOneRadial (x : E) : E :=
  (‖x‖)⁻¹ • x

def sphereTwoRadial (x : E) : E :=
  (2 / ‖x‖) • x

omit [NeZero d] in
lemma mem_sphereOneRadial_of_mem_badAnnulusOne {ε : ℝ} (hε : ε < 1) {x : E}
    (hx : x ∈ unitBallBadAnnulusOne (d := d) ε) :
    sphereOneRadial x ∈ Metric.sphere (0 : E) 1 := by
  have hxnorm : 0 < ‖x‖ := by linarith [hx.1, hε]
  have hx0 : ‖x‖ ≠ 0 := ne_of_gt hxnorm
  rw [Metric.mem_sphere, dist_zero_right, sphereOneRadial, norm_smul, Real.norm_of_nonneg (by positivity),
    inv_mul_cancel₀ hx0]

omit [NeZero d] in
lemma mem_sphereTwoRadial_of_mem_badAnnulusTwo {ε : ℝ} (hε : ε < 2) {x : E}
    (hx : x ∈ unitBallBadAnnulusTwo (d := d) ε) :
    sphereTwoRadial x ∈ Metric.sphere (0 : E) 2 := by
  have hxnorm : 0 < ‖x‖ := by linarith [hx.1, hε]
  have hx0 : ‖x‖ ≠ 0 := ne_of_gt hxnorm
  rw [Metric.mem_sphere, dist_zero_right, sphereTwoRadial, norm_smul, Real.norm_eq_abs]
  have hmul : |2 / ‖x‖| * ‖x‖ = 2 := by
    rw [abs_of_nonneg (by positivity)]
    field_simp [hx0]
  simpa using hmul

omit [NeZero d] in
lemma dist_sphereOneRadial_le_of_mem_badAnnulusOne {ε : ℝ} {x : E}
    (_hε : 0 ≤ ε) (hε' : ε < 1) (hx : x ∈ unitBallBadAnnulusOne (d := d) ε) :
    dist x (sphereOneRadial x) ≤ ε := by
  have hxnorm : 0 < ‖x‖ := by linarith [hx.1, hε']
  have hx0 : ‖x‖ ≠ 0 := ne_of_gt hxnorm
  have hsub : x - ‖x‖⁻¹ • x = (1 - ‖x‖⁻¹) • x := by
    simp [sub_eq_add_neg, add_smul, one_smul]
  calc
    dist x (sphereOneRadial x) = |‖x‖ - 1| := by
      rw [dist_eq_norm, sphereOneRadial, hsub, norm_smul, Real.norm_eq_abs]
      have hmul : (1 - ‖x‖⁻¹) * ‖x‖ = ‖x‖ - 1 := by
        field_simp [hx0]
      calc
        |1 - ‖x‖⁻¹| * ‖x‖ = |1 - ‖x‖⁻¹| * |‖x‖| := by
          rw [abs_of_nonneg (norm_nonneg _)]
        _ = |(1 - ‖x‖⁻¹) * ‖x‖| := by rw [← abs_mul]
        _ = |‖x‖ - 1| := by rw [hmul]
    _ ≤ ε := by
      rw [abs_sub_le_iff]
      constructor <;> linarith [hx.1, hx.2]

omit [NeZero d] in
lemma dist_sphereTwoRadial_le_of_mem_badAnnulusTwo {ε : ℝ} {x : E}
    (_hε : 0 ≤ ε) (hε' : ε < 2) (hx : x ∈ unitBallBadAnnulusTwo (d := d) ε) :
    dist x (sphereTwoRadial x) ≤ ε := by
  have hxnorm : 0 < ‖x‖ := by linarith [hx.1, hε']
  have hx0 : ‖x‖ ≠ 0 := ne_of_gt hxnorm
  have hsub : x - (2 / ‖x‖) • x = (1 - 2 / ‖x‖) • x := by
    simp [sub_eq_add_neg, add_smul, one_smul]
  calc
    dist x (sphereTwoRadial x) = |‖x‖ - 2| := by
      rw [dist_eq_norm, sphereTwoRadial, hsub, norm_smul, Real.norm_eq_abs]
      have hmul : (1 - 2 / ‖x‖) * ‖x‖ = ‖x‖ - 2 := by
        field_simp [hx0]
      calc
        |1 - 2 / ‖x‖| * ‖x‖ = |1 - 2 / ‖x‖| * |‖x‖| := by
          rw [abs_of_nonneg (norm_nonneg _)]
        _ = |(1 - 2 / ‖x‖) * ‖x‖| := by rw [← abs_mul]
        _ = |‖x‖ - 2| := by rw [hmul]
    _ ≤ ε := by
      rw [abs_sub_le_iff]
      constructor <;> linarith [hx.1, hx.2]

omit [NeZero d] in
lemma closedBall_sphereOneRadial_subset_control {ε : ℝ} {x : E}
    (hε : ε ≤ (1 / 5 : ℝ)) (hx : x ∈ unitBallBadAnnulusOne (d := d) ε) :
    Metric.closedBall (sphereOneRadial x) ε ⊆ sphereOneControl (d := d) := by
  intro z hz
  have hy : sphereOneRadial x ∈ Metric.sphere (0 : E) 1 :=
    mem_sphereOneRadial_of_mem_badAnnulusOne (d := d) (by linarith) hx
  rw [Metric.mem_sphere, dist_zero_right] at hy
  rw [Metric.mem_closedBall, dist_eq_norm] at hz
  constructor
  · have hlow : ‖z‖ ≥ 1 - ε := by
      have hdist : |‖z‖ - 1| ≤ ε := by
        simpa [hy] using le_trans (abs_norm_sub_norm_le z (sphereOneRadial x)) hz
      rw [abs_sub_le_iff] at hdist
      linarith [hdist.1]
    linarith
  · have hupp : ‖z‖ ≤ 1 + ε := by
      have hdist : |‖z‖ - 1| ≤ ε := by
        simpa [hy] using le_trans (abs_norm_sub_norm_le z (sphereOneRadial x)) hz
      rw [abs_sub_le_iff] at hdist
      linarith [hdist.2]
    linarith

omit [NeZero d] in
lemma closedBall_sphereTwoRadial_subset_control {ε : ℝ} {x : E}
    (hε : ε ≤ (1 / 5 : ℝ)) (hx : x ∈ unitBallBadAnnulusTwo (d := d) ε) :
    Metric.closedBall (sphereTwoRadial x) ε ⊆ sphereTwoControl (d := d) := by
  intro z hz
  have hy : sphereTwoRadial x ∈ Metric.sphere (0 : E) 2 :=
    mem_sphereTwoRadial_of_mem_badAnnulusTwo (d := d) (by linarith) hx
  rw [Metric.mem_sphere, dist_zero_right] at hy
  rw [Metric.mem_closedBall, dist_eq_norm] at hz
  constructor
  · have hlow : ‖z‖ ≥ 2 - ε := by
      have hdist : |‖z‖ - 2| ≤ ε := by
        simpa [hy] using le_trans (abs_norm_sub_norm_le z (sphereTwoRadial x)) hz
      rw [abs_sub_le_iff] at hdist
      linarith [hdist.1]
    linarith
  · have hupp : ‖z‖ ≤ 2 + ε := by
      have hdist : |‖z‖ - 2| ≤ ε := by
        simpa [hy] using le_trans (abs_norm_sub_norm_le z (sphereTwoRadial x)) hz
      rw [abs_sub_le_iff] at hdist
      linarith [hdist.2]
    linarith

-- Helper: cancels ε in the product bound (Cerr * ε) * (M / (2 * ε)) = Cerr * (M / 2)
lemma product_bound_cancel_eps {Cder Cerr ε M : ℝ} (hε : 0 < ε) :
    1 * Cder + (Cerr * ε) * (M / (2 * ε)) ≤ Cder + Cerr * (M / 2) := by
  have key : (Cerr * ε) * (M / (2 * ε)) = Cerr * (M / 2) := by
    field_simp [hε.ne']
  linarith [key]

-- Mean-value bound in a form convenient for the approximation estimates below.
omit [NeZero d] in
lemma norm_sub_le_of_fderiv_bound_closedBall
    {f : E → ℝ} {C : ℝ} {y : E} {ε : ℝ} {x : E}
    (hf : ∀ z ∈ Metric.closedBall y ε, DifferentiableAt ℝ f z)
    (hbound : ∀ z ∈ Metric.closedBall y ε, ‖fderiv ℝ f z‖ ≤ C)
    (hx : x ∈ Metric.closedBall y ε)
    (hε : 0 ≤ ε) :
    ‖f x - f y‖ ≤ C * ‖x - y‖ := by
  have hymem : y ∈ Metric.closedBall y ε := Metric.mem_closedBall_self hε
  have h := (convex_closedBall y ε).norm_image_sub_le_of_norm_fderiv_le hf hbound hymem hx
  simpa [norm_sub_rev] using h

-- Inner proof extracted to a standalone lemma to keep the proof context small.
omit [NeZero d] in
set_option maxHeartbeats 1600000 in
lemma shellSubPsi_error_bound_at
    {ψ : E → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    {C : ℝ} (hC_nonneg : 0 ≤ C) (hC : ∀ x ∈ sphereOneControl (d := d),
      ‖fderiv ℝ (fun y => unitBallShellFormula (d := d) ψ y - ψ y) x‖ ≤ C)
    {n : ℕ} {x : E} (hx : x ∈ unitBallBadAnnulusOne (d := d) (unitBallApproxEps n)) :
    ‖unitBallShellFormula (d := d) ψ x - ψ x‖ ≤ C * unitBallApproxEps n := by
  have hsubset := closedBall_sphereOneRadial_subset_control (d := d)
    (unitBallApproxEps_le_one_fifth n) hx
  have hDiffAt : ∀ z ∈ Metric.closedBall (sphereOneRadial x) (unitBallApproxEps n),
      DifferentiableAt ℝ (fun w => unitBallShellFormula (d := d) ψ w - ψ w) z :=
    fun z hz => by
      have hznz : z ≠ (0 : E) := by
        have : 0 < ‖z‖ := by linarith [(hsubset hz).1]
        intro hz0; simpa [hz0] using this.ne'
      exact DifferentiableAt.sub
        ((contDiffAt_unitBallShellFormula (d := d) hψ hznz).differentiableAt (by simp))
        (hψ.differentiable (by simp) |>.differentiableAt)
  have hdist : dist x (sphereOneRadial x) ≤ unitBallApproxEps n :=
    dist_sphereOneRadial_le_of_mem_badAnnulusOne (d := d)
      (le_of_lt (unitBallApproxEps_pos n)) (unitBallApproxEps_lt_one n) hx
  have hxmem : x ∈ Metric.closedBall (sphereOneRadial x) (unitBallApproxEps n) :=
    Metric.mem_closedBall.mpr hdist
  have hmvt := norm_sub_le_of_fderiv_bound_closedBall (d := d)
    hDiffAt (fun z hz => hC z (hsubset hz)) hxmem (le_of_lt (unitBallApproxEps_pos n))
  have hy0 : unitBallShellFormula (d := d) ψ (sphereOneRadial x) - ψ (sphereOneRadial x) = 0 :=
    by simp [unitBallShellFormula_eq_on_sphereOne (d := d)
      (mem_sphereOneRadial_of_mem_badAnnulusOne (d := d) (unitBallApproxEps_lt_one n) hx)]
  rw [hy0, sub_zero] at hmvt
  calc
    ‖unitBallShellFormula (d := d) ψ x - ψ x‖ ≤ C * ‖x - sphereOneRadial x‖ := hmvt
    _ = C * dist x (sphereOneRadial x) := by rw [dist_eq_norm]
    _ ≤ C * unitBallApproxEps n := by gcongr

omit [NeZero d] in
theorem exists_shellSubPsi_error_bound
    {ψ : E → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ n x, x ∈ unitBallBadAnnulusOne (d := d) (unitBallApproxEps n) →
        ‖unitBallShellFormula (d := d) ψ x - ψ x‖ ≤ C * unitBallApproxEps n := by
  rcases exists_shellSubPsi_fderiv_bound (d := d) hψ with ⟨C, hC_nonneg, hC⟩
  exact ⟨C, hC_nonneg, fun n x hx => shellSubPsi_error_bound_at (d := d) hψ hC_nonneg hC hx⟩

set_option maxHeartbeats 1600000 in
omit [NeZero d] in
lemma shellFormula_error_bound_at
    {ψ : E → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    {C : ℝ} (hC_nonneg : 0 ≤ C) (hC : ∀ x ∈ sphereTwoControl (d := d),
      ‖fderiv ℝ (unitBallShellFormula (d := d) ψ) x‖ ≤ C)
    {n : ℕ} {x : E} (hx : x ∈ unitBallBadAnnulusTwo (d := d) (unitBallApproxEps n)) :
    ‖unitBallShellFormula (d := d) ψ x‖ ≤ C * unitBallApproxEps n := by
  have hsubset := closedBall_sphereTwoRadial_subset_control (d := d)
    (unitBallApproxEps_le_one_fifth n) hx
  have hDiffAt : ∀ z ∈ Metric.closedBall (sphereTwoRadial x) (unitBallApproxEps n),
      DifferentiableAt ℝ (unitBallShellFormula (d := d) ψ) z :=
    fun z hz => by
      have hznz : z ≠ (0 : E) := by
        have : 0 < ‖z‖ := by linarith [(hsubset hz).1]
        intro hz0; simpa [hz0] using this.ne'
      exact (contDiffAt_unitBallShellFormula (d := d) hψ hznz).differentiableAt (by simp)
  have hdist : dist x (sphereTwoRadial x) ≤ unitBallApproxEps n :=
    dist_sphereTwoRadial_le_of_mem_badAnnulusTwo (d := d)
      (le_of_lt (unitBallApproxEps_pos n)) (by linarith [unitBallApproxEps_lt_one n]) hx
  have hxmem : x ∈ Metric.closedBall (sphereTwoRadial x) (unitBallApproxEps n) :=
    Metric.mem_closedBall.mpr hdist
  have hmvt := norm_sub_le_of_fderiv_bound_closedBall (d := d)
    hDiffAt (fun z hz => hC z (hsubset hz)) hxmem (le_of_lt (unitBallApproxEps_pos n))
  have hy0 : unitBallShellFormula (d := d) ψ (sphereTwoRadial x) = 0 :=
    unitBallShellFormula_eq_zero_on_sphereTwo (d := d)
      (mem_sphereTwoRadial_of_mem_badAnnulusTwo (d := d) (by linarith [unitBallApproxEps_lt_one n]) hx)
  rw [hy0, sub_zero] at hmvt
  calc
    ‖unitBallShellFormula (d := d) ψ x‖ ≤ C * ‖x - sphereTwoRadial x‖ := hmvt
    _ = C * dist x (sphereTwoRadial x) := by rw [dist_eq_norm]
    _ ≤ C * unitBallApproxEps n := by gcongr

omit [NeZero d] in
theorem exists_shellFormula_error_bound
    {ψ : E → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ n x, x ∈ unitBallBadAnnulusTwo (d := d) (unitBallApproxEps n) →
        ‖unitBallShellFormula (d := d) ψ x‖ ≤ C * unitBallApproxEps n := by
  rcases exists_shellFormula_fderiv_bound (d := d) hψ with ⟨C, hC_nonneg, hC⟩
  exact ⟨C, hC_nonneg, fun n x hx => shellFormula_error_bound_at (d := d) hψ hC_nonneg hC hx⟩

omit [NeZero d] in
set_option maxHeartbeats 800000 in
theorem exists_fun_error_bound_badSet
    {ψ : E → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ n x,
        ‖smoothUnitBallExtensionApprox (d := d) (unitBallApproxEps n) ψ x -
            exactUnitBallExtensionModel (d := d) ψ x‖
          ≤ (unitBallBadSet (d := d) (unitBallApproxEps n)).indicator (fun _ => C) x := by
  rcases exists_shellSubPsi_error_bound (d := d) hψ with ⟨C1, hC1_nonneg, hC1⟩
  rcases exists_shellFormula_error_bound (d := d) hψ with ⟨C2, hC2_nonneg, hC2⟩
  refine ⟨max (C1 / 5) (C2 / 5), by positivity, ?_⟩
  intro n x
  by_cases hbad : x ∈ unitBallBadSet (d := d) (unitBallApproxEps n)
  · rw [Set.indicator_of_mem hbad]
    rcases hbad with hx1 | hx2
    · have hεsmall : unitBallApproxEps n ≤ (1 / 5 : ℝ) := unitBallApproxEps_le_one_fifth n
      have hxball2 : x ∈ Metric.ball (0 : E) (2 - unitBallApproxEps n) := by
        rw [Metric.mem_ball, dist_zero_right]; linarith [hx1.2, hεsmall]
      have hβ2 : sphereTwoBlend (d := d) (unitBallApproxEps n) x = 1 :=
        sphereTwoBlend_eq_one_of_mem_ball (d := d) (unitBallApproxEps_pos n) hxball2
      by_cases hxle1 : ‖x‖ ≤ 1
      · have hxclosed : x ∈ Metric.closedBall (0 : E) 1 := by
          rw [Metric.mem_closedBall, dist_zero_right]; exact hxle1
        have hEq :
            smoothUnitBallExtensionApprox (d := d) (unitBallApproxEps n) ψ x -
              exactUnitBallExtensionModel (d := d) ψ x =
              sphereOneBlend (d := d) (unitBallApproxEps n) x *
                (unitBallShellFormula (d := d) ψ x - ψ x) := by
          unfold smoothUnitBallExtensionApprox exactUnitBallExtensionModel exactUnitBallShellOrZero
          simp [hβ2, hxclosed, sub_eq_add_neg]; ring
        calc ‖smoothUnitBallExtensionApprox (d := d) (unitBallApproxEps n) ψ x -
              exactUnitBallExtensionModel (d := d) ψ x‖
              = ‖sphereOneBlend (d := d) (unitBallApproxEps n) x *
                  (unitBallShellFormula (d := d) ψ x - ψ x)‖ := by rw [hEq]
          _ ≤ ‖unitBallShellFormula (d := d) ψ x - ψ x‖ := by
                rw [norm_mul, Real.norm_eq_abs]
                nlinarith [abs_of_nonneg (sphereOneBlend_nonneg (d := d) (ε := unitBallApproxEps n) (x := x)),
                  sphereOneBlend_le_one (d := d) (ε := unitBallApproxEps n) (x := x),
                  norm_nonneg (unitBallShellFormula (d := d) ψ x - ψ x)]
          _ ≤ C1 * unitBallApproxEps n := hC1 n x hx1
          _ ≤ max (C1 / 5) (C2 / 5) := by
                have := unitBallApproxEps_le_one_fifth n
                exact le_trans (by nlinarith [hC1_nonneg]) (le_max_left _ _)
      · have hxOuter : x ∈ unitBallOuterShell (d := d) := ⟨by linarith, by linarith [hx1.2, hεsmall]⟩
        have hEq :
            smoothUnitBallExtensionApprox (d := d) (unitBallApproxEps n) ψ x -
              exactUnitBallExtensionModel (d := d) ψ x =
              (1 - sphereOneBlend (d := d) (unitBallApproxEps n) x) *
                (ψ x - unitBallShellFormula (d := d) ψ x) := by
          unfold smoothUnitBallExtensionApprox exactUnitBallExtensionModel exactUnitBallShellOrZero
          simp [hβ2, hxOuter, hxle1, sub_eq_add_neg]; ring
        calc ‖smoothUnitBallExtensionApprox (d := d) (unitBallApproxEps n) ψ x -
              exactUnitBallExtensionModel (d := d) ψ x‖
              = ‖(1 - sphereOneBlend (d := d) (unitBallApproxEps n) x) *
                  (ψ x - unitBallShellFormula (d := d) ψ x)‖ := by rw [hEq]
          _ ≤ ‖ψ x - unitBallShellFormula (d := d) ψ x‖ := by
                rw [norm_mul, Real.norm_eq_abs]
                have h1 : |1 - sphereOneBlend (d := d) (unitBallApproxEps n) x| ≤ 1 := by
                  rw [abs_of_nonneg (by linarith [sphereOneBlend_le_one (d := d) (ε := unitBallApproxEps n) (x := x)])]
                  linarith [sphereOneBlend_nonneg (d := d) (ε := unitBallApproxEps n) (x := x)]
                nlinarith [norm_nonneg (ψ x - unitBallShellFormula (d := d) ψ x)]
          _ = ‖unitBallShellFormula (d := d) ψ x - ψ x‖ := norm_sub_rev _ _
          _ ≤ C1 * unitBallApproxEps n := hC1 n x hx1
          _ ≤ max (C1 / 5) (C2 / 5) := by
                have := unitBallApproxEps_le_one_fifth n
                exact le_trans (by nlinarith [hC1_nonneg]) (le_max_left _ _)
    · have hεsmall : unitBallApproxEps n ≤ (1 / 5 : ℝ) := unitBallApproxEps_le_one_fifth n
      have hβ1 : sphereOneBlend (d := d) (unitBallApproxEps n) x = 1 := by
        apply sphereOneBlend_eq_one_of_norm_ge (d := d) (unitBallApproxEps_pos n); linarith [hx2.1]
      have hnotclosed1 : x ∉ Metric.closedBall (0 : E) 1 := by
        rw [Metric.mem_closedBall, dist_zero_right]; linarith [hx2.1, hεsmall]
      by_cases hxlt2 : ‖x‖ < 2
      · have hxOuter : x ∈ unitBallOuterShell (d := d) := ⟨by linarith [hx2.1], hxlt2⟩
        have hExactModel :
            exactUnitBallExtensionModel (d := d) ψ x = unitBallShellFormula (d := d) ψ x := by
          unfold exactUnitBallExtensionModel exactUnitBallShellOrZero
          simp [hxOuter, hnotclosed1]
        have hEq :
            smoothUnitBallExtensionApprox (d := d) (unitBallApproxEps n) ψ x -
              exactUnitBallExtensionModel (d := d) ψ x =
              (sphereTwoBlend (d := d) (unitBallApproxEps n) x - 1) *
                unitBallShellFormula (d := d) ψ x := by
          rw [hExactModel]; unfold smoothUnitBallExtensionApprox; simp [hβ1, sub_eq_add_neg]; ring
        calc ‖smoothUnitBallExtensionApprox (d := d) (unitBallApproxEps n) ψ x -
              exactUnitBallExtensionModel (d := d) ψ x‖
              = ‖(sphereTwoBlend (d := d) (unitBallApproxEps n) x - 1) *
                  unitBallShellFormula (d := d) ψ x‖ := by rw [hEq]
          _ ≤ ‖unitBallShellFormula (d := d) ψ x‖ := by
                rw [norm_mul, Real.norm_eq_abs, abs_sub_comm]
                have h1 : |1 - sphereTwoBlend (d := d) (unitBallApproxEps n) x| ≤ 1 := by
                  rw [abs_of_nonneg (by linarith [sphereTwoBlend_le_one (d := d) (ε := unitBallApproxEps n) (x := x)])]
                  linarith [sphereTwoBlend_nonneg (d := d) (ε := unitBallApproxEps n) (x := x)]
                nlinarith [norm_nonneg (unitBallShellFormula (d := d) ψ x)]
          _ ≤ C2 * unitBallApproxEps n := hC2 n x hx2
          _ ≤ max (C1 / 5) (C2 / 5) := by
                have := unitBallApproxEps_le_one_fifth n
                exact le_trans (by nlinarith [hC2_nonneg]) (le_max_right _ _)
      · have hxge2 : 2 ≤ ‖x‖ := by linarith
        have hnotOuter : x ∉ unitBallOuterShell (d := d) := fun h => not_lt_of_ge hxge2 h.2
        have hExactModel :
            exactUnitBallExtensionModel (d := d) ψ x = 0 := by
          unfold exactUnitBallExtensionModel exactUnitBallShellOrZero
          simp [hnotclosed1, hnotOuter]
        have hEq :
            smoothUnitBallExtensionApprox (d := d) (unitBallApproxEps n) ψ x -
              exactUnitBallExtensionModel (d := d) ψ x =
              sphereTwoBlend (d := d) (unitBallApproxEps n) x *
                unitBallShellFormula (d := d) ψ x := by
          rw [hExactModel]; unfold smoothUnitBallExtensionApprox; simp [hβ1, sub_eq_add_neg]
        calc ‖smoothUnitBallExtensionApprox (d := d) (unitBallApproxEps n) ψ x -
              exactUnitBallExtensionModel (d := d) ψ x‖
              = ‖sphereTwoBlend (d := d) (unitBallApproxEps n) x *
                  unitBallShellFormula (d := d) ψ x‖ := by rw [hEq]
          _ ≤ ‖unitBallShellFormula (d := d) ψ x‖ := by
                rw [norm_mul, Real.norm_eq_abs]
                nlinarith [abs_of_nonneg (sphereTwoBlend_nonneg (d := d) (ε := unitBallApproxEps n) (x := x)),
                  sphereTwoBlend_le_one (d := d) (ε := unitBallApproxEps n) (x := x),
                  norm_nonneg (unitBallShellFormula (d := d) ψ x)]
          _ ≤ C2 * unitBallApproxEps n := hC2 n x hx2
          _ ≤ max (C1 / 5) (C2 / 5) := by
                have := unitBallApproxEps_le_one_fifth n
                exact le_trans (by nlinarith [hC2_nonneg]) (le_max_right _ _)
  · rw [Set.indicator_of_notMem hbad]
    rw [smoothUnitBallExtensionApprox_eq_unitBallExtension_of_not_mem_badSet (d := d) hbad,
      ← exactUnitBallExtensionModel_eq_unitBallExtension (d := d) (ψ := ψ)]
    simp

end SmoothApproximationInternal

end DeGiorgi
