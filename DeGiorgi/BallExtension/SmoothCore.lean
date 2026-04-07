import DeGiorgi.BallExtension.RoughInput

/-!
# Ball Extension Smooth Core

This file contains the basic smooth approximants for the explicit unit-ball
extension and their local geometric identities.
-/

noncomputable section

open MeasureTheory Metric Filter Topology Set Function Matrix
open scoped ENNReal NNReal RealInnerProductSpace

namespace DeGiorgi

variable {d : ℕ} [NeZero d]

local notation "E" => EuclideanSpace ℝ (Fin d)

namespace SmoothApproximationInternal

/-- Transition profile used to smooth the explicit unit-ball extension across
the sphere interfaces `‖x‖ = 1` and `‖x‖ = 2`. -/
def sphereOneBlend (ε : ℝ) : E → ℝ :=
  fun x => 1 - myCutoff (0 : E) (1 - ε) (1 + ε) x

def sphereTwoBlend (ε : ℝ) : E → ℝ :=
  fun x => myCutoff (0 : E) (2 - ε) (2 + ε) x

def smoothUnitBallExtensionApprox (ε : ℝ) (ψ : E → ℝ) : E → ℝ :=
  fun x =>
    (1 - sphereOneBlend (d := d) ε x) * ψ x +
      sphereOneBlend (d := d) ε x * sphereTwoBlend (d := d) ε x *
        unitBallShellFormula (d := d) ψ x

def unitBallBadAnnulusOne (ε : ℝ) : Set E :=
  {x : E | 1 - ε < ‖x‖ ∧ ‖x‖ < 1 + ε}

def unitBallBadAnnulusTwo (ε : ℝ) : Set E :=
  {x : E | 2 - ε < ‖x‖ ∧ ‖x‖ < 2 + ε}

omit [NeZero d] in
lemma sphereOneBlend_eq_zero_of_mem_ball {ε : ℝ} (hε : 0 < ε) {x : E}
    (hx : x ∈ Metric.ball (0 : E) (1 - ε)) :
    sphereOneBlend (d := d) ε x = 0 := by
  unfold sphereOneBlend
  rw [myCutoff_eq_one (x₀ := (0 : E)) (r := 1 - ε) (R := 1 + ε)]
  · ring
  · linarith
  · exact hx

omit [NeZero d] in
lemma sphereOneBlend_eq_one_of_norm_ge {ε : ℝ} (hε : 0 < ε) {x : E}
    (hx : 1 + ε ≤ ‖x‖) :
    sphereOneBlend (d := d) ε x = 1 := by
  unfold sphereOneBlend
  unfold myCutoff
  have hnonpos : ((1 + ε) - ‖x‖) / ((1 + ε) - (1 - ε)) ≤ 0 := by
    have hden : 0 < (1 + ε) - (1 - ε) := by linarith
    have hnum : (1 + ε) - ‖x‖ ≤ 0 := sub_nonpos.mpr hx
    exact div_nonpos_of_nonpos_of_nonneg hnum hden.le
  simpa using Real.smoothTransition.zero_of_nonpos hnonpos

omit [NeZero d] in
lemma sphereOneBlend_eq_zero_of_norm_le {ε : ℝ} (hε : 0 < ε) {x : E}
    (hx : ‖x‖ ≤ 1 - ε) :
    sphereOneBlend (d := d) ε x = 0 := by
  unfold sphereOneBlend myCutoff
  have hden : 0 < (1 + ε) - (1 - ε) := by linarith
  have hx' : ‖x - 0‖ ≤ 1 - ε := by simpa using hx
  have hone : 1 ≤ ((1 + ε) - ‖x - 0‖) / ((1 + ε) - (1 - ε)) := by
    rw [le_div_iff₀ hden, one_mul]
    linarith
  have hst : ((1 + ε - ‖x - 0‖) / ((1 + ε) - (1 - ε))).smoothTransition = 1 :=
    Real.smoothTransition.one_of_one_le hone
  have hst' : ((1 + ε - ‖x‖) / (ε + ε)).smoothTransition = 1 := by
    simpa using hst
  simp [hst']

omit [NeZero d] in
lemma sphereTwoBlend_eq_one_of_mem_ball {ε : ℝ} (hε : 0 < ε) {x : E}
    (hx : x ∈ Metric.ball (0 : E) (2 - ε)) :
    sphereTwoBlend (d := d) ε x = 1 := by
  unfold sphereTwoBlend
  rw [myCutoff_eq_one (x₀ := (0 : E)) (r := 2 - ε) (R := 2 + ε) (by linarith) hx]

omit [NeZero d] in
lemma sphereTwoBlend_eq_one_of_norm_le {ε : ℝ} (hε : 0 < ε) {x : E}
    (hx : ‖x‖ ≤ 2 - ε) :
    sphereTwoBlend (d := d) ε x = 1 := by
  unfold sphereTwoBlend myCutoff
  have hden : 0 < (2 + ε) - (2 - ε) := by linarith
  have hx' : ‖x - 0‖ ≤ 2 - ε := by simpa using hx
  have hone : 1 ≤ ((2 + ε) - ‖x - 0‖) / ((2 + ε) - (2 - ε)) := by
    rw [le_div_iff₀ hden, one_mul]
    linarith
  simpa using Real.smoothTransition.one_of_one_le hone

omit [NeZero d] in
lemma sphereTwoBlend_eq_zero_of_norm_ge {ε : ℝ} (hε : 0 < ε) {x : E}
    (hx : 2 + ε ≤ ‖x‖) :
    sphereTwoBlend (d := d) ε x = 0 := by
  unfold sphereTwoBlend
  unfold myCutoff
  have hnonpos : ((2 + ε) - ‖x‖) / ((2 + ε) - (2 - ε)) ≤ 0 := by
    have hden : 0 < (2 + ε) - (2 - ε) := by linarith
    have hnum : (2 + ε) - ‖x‖ ≤ 0 := sub_nonpos.mpr hx
    exact div_nonpos_of_nonpos_of_nonneg hnum hden.le
  simpa using Real.smoothTransition.zero_of_nonpos hnonpos

omit [NeZero d] in
lemma sphereOneBlend_nonneg {ε : ℝ} {x : E} :
    0 ≤ sphereOneBlend (d := d) ε x := by
  unfold sphereOneBlend
  linarith [myCutoff_nonneg (x₀ := (0 : E)) (r := 1 - ε) (R := 1 + ε) x,
    myCutoff_le_one (x₀ := (0 : E)) (r := 1 - ε) (R := 1 + ε) x]

omit [NeZero d] in
lemma sphereOneBlend_le_one {ε : ℝ} {x : E} :
    sphereOneBlend (d := d) ε x ≤ 1 := by
  unfold sphereOneBlend
  linarith [myCutoff_nonneg (x₀ := (0 : E)) (r := 1 - ε) (R := 1 + ε) x]

omit [NeZero d] in
lemma sphereTwoBlend_nonneg {ε : ℝ} {x : E} :
    0 ≤ sphereTwoBlend (d := d) ε x := by
  unfold sphereTwoBlend
  exact myCutoff_nonneg (x₀ := (0 : E)) (r := 2 - ε) (R := 2 + ε) x

omit [NeZero d] in
lemma sphereTwoBlend_le_one {ε : ℝ} {x : E} :
    sphereTwoBlend (d := d) ε x ≤ 1 := by
  unfold sphereTwoBlend
  exact myCutoff_le_one (x₀ := (0 : E)) (r := 2 - ε) (R := 2 + ε) x

omit [NeZero d] in
lemma sphereOneBlend_fderiv_bound {ε : ℝ} (hε : 0 < ε) (x : E) :
    ‖fderiv ℝ (sphereOneBlend (d := d) ε) x‖ ≤ ↑Mst * (ε + ε)⁻¹ := by
  have hcut :
      ‖fderiv ℝ (myCutoff (0 : E) (1 - ε) (1 + ε)) x‖ ≤ ↑Mst * ((1 + ε) - (1 - ε))⁻¹ :=
    myCutoff_fderiv_bound (d := d) (x₀ := (0 : E)) (r := 1 - ε) (R := 1 + ε) (by linarith) x
  have hEq :
      fderiv ℝ (sphereOneBlend (d := d) ε) x =
        -(fderiv ℝ (myCutoff (0 : E) (1 - ε) (1 + ε)) x) := by
    simpa [sphereOneBlend] using
      (fderiv_const_sub (𝕜 := ℝ) (f := myCutoff (0 : E) (1 - ε) (1 + ε)) (c := (1 : ℝ)) (x := x))
  calc
    ‖fderiv ℝ (sphereOneBlend (d := d) ε) x‖
        = ‖fderiv ℝ (myCutoff (0 : E) (1 - ε) (1 + ε)) x‖ := by
            rw [hEq, norm_neg]
  _ ≤ ↑Mst * ((1 + ε) - (1 - ε))⁻¹ := hcut
  _ = ↑Mst * (ε + ε)⁻¹ := by ring_nf

omit [NeZero d] in
lemma sphereTwoBlend_fderiv_bound {ε : ℝ} (hε : 0 < ε) (x : E) :
    ‖fderiv ℝ (sphereTwoBlend (d := d) ε) x‖ ≤ ↑Mst * (ε + ε)⁻¹ := by
  have hcut :
      ‖fderiv ℝ (myCutoff (0 : E) (2 - ε) (2 + ε)) x‖ ≤ ↑Mst * ((2 + ε) - (2 - ε))⁻¹ :=
    myCutoff_fderiv_bound (d := d) (x₀ := (0 : E)) (r := 2 - ε) (R := 2 + ε) (by linarith) x
  have hden : ((2 + ε) - (2 - ε))⁻¹ = (ε + ε)⁻¹ := by ring_nf
  simpa [sphereTwoBlend, hden] using hcut

omit [NeZero d] in
lemma norm_fderiv_mul_le
    {f g : E → ℝ} {x : E}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    ‖fderiv ℝ (fun y => f y * g y) x‖ ≤
      |f x| * ‖fderiv ℝ g x‖ + |g x| * ‖fderiv ℝ f x‖ := by
  have hfg :
      fderiv ℝ (fun y => f y * g y) x =
        f x • fderiv ℝ g x + g x • fderiv ℝ f x := by
    simpa using (hf.hasFDerivAt.mul hg.hasFDerivAt).fderiv
  calc
    ‖fderiv ℝ (fun y => f y * g y) x‖
        = ‖f x • fderiv ℝ g x + g x • fderiv ℝ f x‖ := by rw [hfg]
    _ ≤ ‖f x • fderiv ℝ g x‖ + ‖g x • fderiv ℝ f x‖ := norm_add_le _ _
    _ = |f x| * ‖fderiv ℝ g x‖ + |g x| * ‖fderiv ℝ f x‖ := by
          simp [norm_smul]

omit [NeZero d] in
lemma smoothUnitBallExtensionApprox_eq_of_mem_innerCore {ε : ℝ}
    (hε : 0 < ε) {ψ : E → ℝ} {x : E}
    (hx : x ∈ Metric.ball (0 : E) (1 - ε)) :
    smoothUnitBallExtensionApprox (d := d) ε ψ x = unitBallExtension (d := d) ψ x := by
  rw [unitBallExtension_eq_of_mem_ball (d := d)]
  · unfold smoothUnitBallExtensionApprox
    rw [sphereOneBlend_eq_zero_of_mem_ball (d := d) hε hx]
    ring
  ·
    rw [Metric.mem_ball, dist_zero_right] at hx ⊢
    linarith

omit [NeZero d] in
lemma smoothUnitBallExtensionApprox_eq_of_norm_le_innerCore {ε : ℝ}
    (hε : 0 < ε) {ψ : E → ℝ} {x : E}
    (hx : ‖x‖ ≤ 1 - ε) :
    smoothUnitBallExtensionApprox (d := d) ε ψ x = unitBallExtension (d := d) ψ x := by
  have hxball : x ∈ Metric.ball (0 : E) 1 := by
    rw [Metric.mem_ball, dist_zero_right]
    linarith
  unfold smoothUnitBallExtensionApprox
  rw [sphereOneBlend_eq_zero_of_norm_le (d := d) hε hx]
  rw [unitBallExtension_eq_of_mem_ball (d := d) hxball]
  ring

omit [NeZero d] in
lemma smoothUnitBallExtensionApprox_eq_of_mem_shellCore {ε : ℝ}
    (hε : 0 < ε) {ψ : E → ℝ} {x : E}
    (hxl : 1 + ε < ‖x‖) (hxr : ‖x‖ < 2 - ε) :
    smoothUnitBallExtensionApprox (d := d) ε ψ x = unitBallExtension (d := d) ψ x := by
  have hx_outer : x ∈ unitBallOuterShell (d := d) := by
    constructor <;> linarith
  unfold smoothUnitBallExtensionApprox
  rw [sphereOneBlend_eq_one_of_norm_ge (d := d) hε (le_of_lt hxl)]
  rw [sphereTwoBlend_eq_one_of_mem_ball (d := d) hε]
  · rw [unitBallExtension, unitBallCutoff_eq_two_sub_norm_of_mem_outerShell (d := d) hx_outer,
      unitBallRetraction_eq_inversion_of_mem_outerShell (d := d) hx_outer]
    simp [unitBallShellFormula]
  · rw [Metric.mem_ball, dist_zero_right]
    linarith

omit [NeZero d] in
lemma smoothUnitBallExtensionApprox_eq_of_shellCore_closed {ε : ℝ}
    (hε : 0 < ε) {ψ : E → ℝ} {x : E}
    (hxl : 1 + ε ≤ ‖x‖) (hxr : ‖x‖ ≤ 2 - ε) :
    smoothUnitBallExtensionApprox (d := d) ε ψ x = unitBallExtension (d := d) ψ x := by
  have hx_outer : x ∈ unitBallOuterShell (d := d) := by
    constructor <;> linarith
  unfold smoothUnitBallExtensionApprox
  rw [sphereOneBlend_eq_one_of_norm_ge (d := d) hε hxl]
  rw [sphereTwoBlend_eq_one_of_norm_le (d := d) hε hxr]
  rw [unitBallExtension, unitBallCutoff_eq_two_sub_norm_of_mem_outerShell (d := d) hx_outer,
    unitBallRetraction_eq_inversion_of_mem_outerShell (d := d) hx_outer]
  simp [unitBallShellFormula]

omit [NeZero d] in
lemma smoothUnitBallExtensionApprox_eq_of_norm_ge {ε : ℝ}
    (hε : 0 < ε) {ψ : E → ℝ} {x : E}
    (hx : 2 + ε ≤ ‖x‖) :
    smoothUnitBallExtensionApprox (d := d) ε ψ x = unitBallExtension (d := d) ψ x := by
  unfold smoothUnitBallExtensionApprox
  rw [sphereTwoBlend_eq_zero_of_norm_ge (d := d) hε hx]
  rw [sphereOneBlend_eq_one_of_norm_ge (d := d) hε (by linarith [hx])]
  have h2 : 2 ≤ ‖x‖ := by linarith
  unfold unitBallExtension unitBallCutoff
  rw [max_eq_right (by linarith), min_eq_right (by positivity)]
  simp

omit [NeZero d] in
lemma contDiff_sphereOneBlend {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    ContDiff ℝ (⊤ : ℕ∞) (sphereOneBlend (d := d) ε) := by
  unfold sphereOneBlend
  simpa using
    (contDiff_const.sub (myCutoff_contDiff (d := d) (x₀ := (0 : E))
      (r := 1 - ε) (R := 1 + ε) (by linarith) (by linarith)))

omit [NeZero d] in
lemma contDiff_sphereTwoBlend {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 2) :
    ContDiff ℝ (⊤ : ℕ∞) (sphereTwoBlend (d := d) ε) := by
  unfold sphereTwoBlend
  simpa using
    (myCutoff_contDiff (d := d) (x₀ := (0 : E))
      (r := 2 - ε) (R := 2 + ε) (by linarith) (by linarith))

omit [NeZero d] in
lemma contDiffAt_unitBallShellFormula
    {ψ : E → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) {x : E} (hx0 : x ≠ (0 : E)) :
    ContDiffAt ℝ (⊤ : ℕ∞) (unitBallShellFormula (d := d) ψ) x := by
  unfold unitBallShellFormula
  have hnorm : ContDiffAt ℝ (⊤ : ℕ∞) (fun y : E => ‖y‖) x :=
    contDiffAt_norm ℝ hx0
  have hinv : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun y : E => EuclideanGeometry.inversion (0 : E) 1 y) x := by
    simpa using
      (contDiffAt_const.inversion contDiffAt_const contDiffAt_id hx0)
  exact (contDiffAt_const.sub hnorm).mul (hψ.contDiffAt.comp x hinv)

omit [NeZero d] in
lemma smoothUnitBallExtensionApprox_contDiff
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    {ψ : E → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) :
    ContDiff ℝ (⊤ : ℕ∞) (smoothUnitBallExtensionApprox (d := d) ε ψ) := by
  let β1 := sphereOneBlend (d := d) ε
  let β2 := sphereTwoBlend (d := d) ε
  have hβ1 : ContDiff ℝ (⊤ : ℕ∞) β1 := contDiff_sphereOneBlend (d := d) hε hε1
  have hβ2 : ContDiff ℝ (⊤ : ℕ∞) β2 := contDiff_sphereTwoBlend (d := d) hε (by linarith)
  have hsmooth1 : ContDiff ℝ (⊤ : ℕ∞) (fun x => (1 - β1 x) * ψ x) :=
    (contDiff_const.sub hβ1).mul hψ
  have hsmooth2 : ContDiff ℝ (⊤ : ℕ∞)
      (fun x => β1 x * β2 x * unitBallShellFormula (d := d) ψ x) := by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ Metric.ball (0 : E) (1 - ε)
    · have hβ1_zero :
          β1 =ᶠ[𝓝 x] fun _ : E => (0 : ℝ) := by
        filter_upwards [Metric.isOpen_ball.mem_nhds hx] with y hy
        simp [β1, sphereOneBlend_eq_zero_of_mem_ball (d := d) hε hy]
      have hzero :
          (fun y => β1 y * β2 y * unitBallShellFormula (d := d) ψ y)
            =ᶠ[𝓝 x] fun _ : E => (0 : ℝ) := by
        filter_upwards [hβ1_zero] with y hy
        simp [hy]
      exact contDiffAt_const.congr_of_eventuallyEq hzero
    · have hxnorm : 1 - ε ≤ ‖x‖ := by
        rw [Metric.mem_ball, dist_zero_right] at hx
        exact le_of_not_gt hx
      have hx0 : x ≠ (0 : E) := by
        intro hx0
        simp [hx0] at hxnorm
        linarith [hε1]
      exact ((hβ1.mul hβ2).contDiffAt.mul
        (contDiffAt_unitBallShellFormula (d := d) hψ hx0))
  unfold smoothUnitBallExtensionApprox
  exact hsmooth1.add hsmooth2

omit [NeZero d] in
lemma smoothUnitBallExtensionApprox_eq_zero_of_norm_ge
    {ε : ℝ} (hε : 0 < ε) {ψ : E → ℝ} {x : E} (hx : 2 + ε ≤ ‖x‖) :
    smoothUnitBallExtensionApprox (d := d) ε ψ x = 0 := by
  unfold smoothUnitBallExtensionApprox
  have hβ1 : sphereOneBlend (d := d) ε x = 1 :=
    sphereOneBlend_eq_one_of_norm_ge (d := d) hε (by linarith)
  rw [sphereTwoBlend_eq_zero_of_norm_ge (d := d) hε hx]
  simp [hβ1]

omit [NeZero d] in
lemma smoothUnitBallExtensionApprox_hasCompactSupport
    {ε : ℝ} (hε : 0 < ε) {ψ : E → ℝ} :
    HasCompactSupport (smoothUnitBallExtensionApprox (d := d) ε ψ) := by
  apply HasCompactSupport.intro' (isCompact_closedBall (0 : E) (2 + ε))
    isClosed_closedBall
  intro x hx
  have hnorm : 2 + ε ≤ ‖x‖ := by
    rw [Metric.mem_closedBall, dist_zero_right] at hx
    linarith
  exact smoothUnitBallExtensionApprox_eq_zero_of_norm_ge (d := d) hε hnorm

omit [NeZero d] in
lemma fderiv_unitBallExtension_eq_shellFormula_of_mem_outerShell
    {ψ : E → ℝ} {x : E} (hx : x ∈ unitBallOuterShell (d := d)) :
    fderiv ℝ (unitBallExtension (d := d) ψ) x =
      fderiv ℝ (unitBallShellFormula (d := d) ψ) x := by
  apply Filter.EventuallyEq.fderiv_eq
  filter_upwards [isOpen_unitBallOuterShell (d := d) |>.mem_nhds hx] with y hy
  exact unitBallExtension_eq_shellFormula_of_mem_outerShell (d := d) hy

end SmoothApproximationInternal

end DeGiorgi
