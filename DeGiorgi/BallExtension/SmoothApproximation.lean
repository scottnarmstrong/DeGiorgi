import DeGiorgi.BallExtension.ApproximationControl

/-!
# Ball Extension Smooth Approximation

This file contains the convergence and public `W^{1,p}` packaging for the
smooth approximants of the explicit unit-ball extension.
-/

noncomputable section

open MeasureTheory Metric Filter Topology Set Function Matrix
open scoped ENNReal NNReal RealInnerProductSpace

namespace DeGiorgi

variable {d : ℕ} [NeZero d]

local notation "E" => EuclideanSpace ℝ (Fin d)

open SmoothApproximationInternal

abbrev exactUnitBallExtensionGrad (ψ : E → ℝ) : E → E :=
  SmoothApproximationInternal.exactUnitBallExtensionGrad (d := d) ψ

omit [NeZero d] in
private lemma tendsto_sub_unitBallExtension_pointwise
    {ψ : E → ℝ} {x : E}
    (hx1 : x ∉ Metric.sphere (0 : E) 1) (hx2 : x ∉ Metric.sphere (0 : E) 2) :
    Tendsto (fun n =>
      smoothUnitBallExtensionApprox (d := d) (unitBallApproxEps n) ψ x -
        unitBallExtension (d := d) ψ x) atTop (nhds 0) := by
  have hx1' : ‖x‖ ≠ 1 := by simpa [Metric.mem_sphere, dist_zero_right] using hx1
  have hx2' : ‖x‖ ≠ 2 := by simpa [Metric.mem_sphere, dist_zero_right] using hx2
  have hpt := tendsto_smoothUnitBallExtensionApprox_pointwise (d := d) (ψ := ψ) hx1' hx2'
  rwa [tendsto_sub_nhds_zero_iff]

-- AE version of above.
private lemma tendsto_sub_unitBallExtension_pointwise_ae
    {ψ : E → ℝ} (_hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) :
    ∀ᵐ x ∂(volume : Measure E), Tendsto (fun n =>
      smoothUnitBallExtensionApprox (d := d) (unitBallApproxEps n) ψ x -
        unitBallExtension (d := d) ψ x) atTop (nhds 0) := by
  have hae1 : ∀ᵐ x ∂(volume : Measure E), x ∉ Metric.sphere (0 : E) 1 := by
    rw [ae_iff]; simpa [Metric.sphere, dist_zero_right] using
      Measure.addHaar_sphere (μ := (volume : Measure E)) (x := (0 : E)) 1
  have hae2 : ∀ᵐ x ∂(volume : Measure E), x ∉ Metric.sphere (0 : E) 2 := by
    rw [ae_iff]; simpa [Metric.sphere, dist_zero_right] using
      Measure.addHaar_sphere (μ := (volume : Measure E)) (x := (0 : E)) 2
  filter_upwards [hae1, hae2] with x hx1 hx2
  exact tendsto_sub_unitBallExtension_pointwise (d := d) hx1 hx2

-- Standalone helper: indicator eLpNorm monotonicity for dominated families.
omit [NeZero d] in
private lemma eLpNorm_indicator_le_of_norm_le {F : E → ℝ} {H : E → ℝ}
    (hFH : ∀ x, ‖F x‖ ≤ ‖H x‖) (s : Set E) {p : ℝ≥0∞} :
    eLpNorm (s.indicator F) p (volume : Measure E) ≤
      eLpNorm (s.indicator H) p (volume : Measure E) :=
  eLpNorm_mono fun x => by
    unfold Set.indicator
    split
    · exact hFH x
    · simp

set_option maxHeartbeats 1600000 in
private theorem tendsto_eLpNorm_smoothUnitBallExtensionApprox_sub_unitBallExtension
    {p : ℝ} (hp : 1 < p) {ψ : E → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) :
    Tendsto
      (fun n =>
        eLpNorm
          (fun x =>
            smoothUnitBallExtensionApprox (d := d) (unitBallApproxEps n) ψ x -
              unitBallExtension (d := d) ψ x)
          (ENNReal.ofReal p) volume)
      atTop (nhds 0) := by
  rcases exists_fun_error_bound_badSet (d := d) hψ with ⟨C, hC_nonneg, hC⟩
  let K : Set E := Metric.closedBall (0 : E) (9 / 4 : ℝ)
  let F : ℕ → E → ℝ := fun n x =>
    smoothUnitBallExtensionApprox (d := d) (unitBallApproxEps n) ψ x -
      unitBallExtension (d := d) ψ x
  let H : E → ℝ := K.indicator fun _ => C
  have hHp : 1 ≤ ENNReal.ofReal p := by simpa using (ENNReal.ofReal_le_ofReal hp.le)
  have hHp' : ENNReal.ofReal p ≠ ∞ := by simp
  have hH_memLp : MemLp H (ENNReal.ofReal p) volume := by
    unfold H K
    rw [MeasureTheory.memLp_indicator_iff_restrict (μ := volume)
      (s := Metric.closedBall (0 : E) (9 / 4 : ℝ))
      (p := ENNReal.ofReal p) Metric.isClosed_closedBall.measurableSet]
    letI : IsFiniteMeasure (volume.restrict (Metric.closedBall (0 : E) (9 / 4 : ℝ))) := by
      refine ⟨by simpa using (measure_closedBall_lt_top (x := (0 : E)) (r := (9 / 4 : ℝ)))⟩
    simpa using (memLp_const C : MemLp (fun _ : E => C) (ENNReal.ofReal p)
      (volume.restrict (Metric.closedBall (0 : E) (9 / 4 : ℝ))))
  have hF_meas : ∀ n, AEStronglyMeasurable (F n) volume := by
    intro n; unfold F
    exact ((smoothUnitBallExtensionApprox_contDiff (d := d) (unitBallApproxEps_pos n)
      (unitBallApproxEps_lt_one n) hψ).continuous.aestronglyMeasurable.sub
        ((measurable_exactUnitBallExtensionModel (d := d) hψ).aestronglyMeasurable.congr
          (Filter.EventuallyEq.of_eq
            (exactUnitBallExtensionModel_eq_unitBallExtension (d := d) (ψ := ψ)))))
  have hF_dom : ∀ n x, ‖F n x‖ ≤ H x := by
    intro n x; unfold F H K
    by_cases hxK : x ∈ Metric.closedBall (0 : E) (9 / 4 : ℝ)
    · rw [Set.indicator_of_mem hxK]
      by_cases hbad : x ∈ unitBallBadSet (d := d) (unitBallApproxEps n)
      · have hbound := hC n x
        rw [Set.indicator_of_mem hbad] at hbound
        have hEqx : exactUnitBallExtensionModel (d := d) ψ x = unitBallExtension (d := d) ψ x :=
          congrFun (exactUnitBallExtensionModel_eq_unitBallExtension (d := d) (ψ := ψ)) x
        simpa [hEqx] using hbound
      · have hEq := smoothUnitBallExtensionApprox_eq_unitBallExtension_of_not_mem_badSet
          (d := d) (ψ := ψ) (n := n) hbad
        simp [hEq, hC_nonneg]
    · rw [Set.indicator_of_notMem hxK]
      have hxnot : x ∉ unitBallBadSet (d := d) (unitBallApproxEps n) := by
        intro hxbad
        rcases hxbad with hx1 | hx2
        · have hxK' := sphereOneControl_subset_closedBall (d := d)
            (badAnnulusOne_subset_sphereOneControl (d := d) n hx1)
          exact hxK (by rw [Metric.mem_closedBall, dist_zero_right] at hxK' ⊢; linarith)
        · exact hxK (sphereTwoControl_subset_closedBall (d := d)
            (badAnnulusTwo_subset_sphereTwoControl (d := d) n hx2))
      simp [smoothUnitBallExtensionApprox_eq_unitBallExtension_of_not_mem_badSet
        (d := d) (ψ := ψ) (n := n) hxnot]
  have hH_nonneg : ∀ x, 0 ≤ H x := by
    intro x; unfold H K
    by_cases hxK : x ∈ Metric.closedBall (0 : E) (9 / 4 : ℝ) <;> simp [Set.indicator, hxK, hC_nonneg]
  have hF_dom_norm : ∀ n x, ‖F n x‖ ≤ ‖H x‖ := fun n x => by
    have := hF_dom n x
    simp only [Real.norm_eq_abs] at this ⊢
    exact this.trans (le_abs_self _)
  have huiF : UnifIntegrable F (ENNReal.ofReal p) volume := by
    intro ε hε
    obtain ⟨δ, hδ, hδ'⟩ :=
      MeasureTheory.unifIntegrable_const (p := ENNReal.ofReal p) hHp hHp' hH_memLp hε
    exact ⟨δ, hδ, fun n s hs hμs =>
      le_trans (eLpNorm_indicator_le_of_norm_le (d := d) (fun x => hF_dom_norm n x) s)
        (hδ' 0 s hs hμs)⟩
  have hutF : UnifTight F (ENNReal.ofReal p) volume := by
    intro ε hε
    obtain ⟨s, hμs, hs'⟩ := MeasureTheory.unifTight_const
      (p := ENNReal.ofReal p) hHp' hH_memLp hε
    exact ⟨s, hμs, fun n =>
      le_trans (eLpNorm_indicator_le_of_norm_le (d := d) (fun x => hF_dom_norm n x) sᶜ) (hs' 0)⟩
  have hF_ae : ∀ᵐ x ∂volume, Tendsto (fun n => F n x) atTop (nhds 0) := by
    have hae1 : ∀ᵐ x ∂(volume : Measure E), x ∉ Metric.sphere (0 : E) 1 := by
      rw [ae_iff]; simpa [Metric.sphere, dist_zero_right] using
        Measure.addHaar_sphere (μ := (volume : Measure E)) (x := (0 : E)) 1
    have hae2 : ∀ᵐ x ∂(volume : Measure E), x ∉ Metric.sphere (0 : E) 2 := by
      rw [ae_iff]; simpa [Metric.sphere, dist_zero_right] using
        Measure.addHaar_sphere (μ := (volume : Measure E)) (x := (0 : E)) 2
    exact tendsto_sub_unitBallExtension_pointwise_ae (d := d) hψ
  have hLpF0 :=
    MeasureTheory.tendsto_Lp_of_tendsto_ae hHp hHp' hF_meas
      (MeasureTheory.MemLp.zero' (p := ENNReal.ofReal p) (μ := volume)) huiF hutF hF_ae
  have hEq0 : (fun n => eLpNorm (F n - fun _ => (0 : ℝ)) (ENNReal.ofReal p) volume) =
      (fun n => eLpNorm (F n) (ENNReal.ofReal p) volume) := by
    funext n; congr 1; ext x; simp
  rw [hEq0] at hLpF0
  simpa [F] using hLpF0

omit [NeZero d] in
set_option maxHeartbeats 1600000 in
private theorem exists_gradApply_error_bound_badAnnulusOne
    {ψ : E → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ n x i,
        x ∈ unitBallBadAnnulusOne (d := d) (unitBallApproxEps n) →
        x ∉ Metric.sphere (0 : E) 1 →
        ‖(fderiv ℝ (smoothUnitBallExtensionApprox (d := d) (unitBallApproxEps n) ψ) x)
            (EuclideanSpace.single i 1) -
          exactUnitBallExtensionGradApply (d := d) ψ i x‖ ≤ C := by
  rcases exists_shellSubPsi_fderiv_bound (d := d) hψ with ⟨Cder, hCder_nonneg, hCder⟩
  rcases exists_shellSubPsi_error_bound (d := d) hψ with ⟨Cerr, hCerr_nonneg, hCerr⟩
  refine ⟨Cder + Cerr * (↑Mst / 2), by positivity, ?_⟩
  intro n x i hx hxSphere
  let ε := unitBallApproxEps n
  have hε : 0 < ε := unitBallApproxEps_pos n
  have hεsmall : ε ≤ (1 / 5 : ℝ) := unitBallApproxEps_le_one_fifth n
  have hxball2 : x ∈ Metric.ball (0 : E) (2 - ε) := by
    rw [Metric.mem_ball, dist_zero_right]
    linarith [hx.2, hεsmall]
  have hβ2 : sphereTwoBlend (d := d) ε x = 1 :=
    sphereTwoBlend_eq_one_of_mem_ball (d := d) hε hxball2
  let Eerr : E → ℝ := fun y => unitBallShellFormula (d := d) ψ y - ψ y
  have hEerr_cd1 : ContDiffAt ℝ 1 Eerr x := by
    have hShell_cd1 :
        ContDiffAt ℝ 1 (unitBallShellFormula (d := d) ψ) x := by
      have hx0 : x ≠ (0 : E) := by
        have : 0 < ‖x‖ := by linarith [hx.1, hεsmall]
        intro hx0
        simpa [hx0] using this.ne'
      exact (contDiffAt_unitBallShellFormula (d := d) hψ hx0).of_le (by simp)
    exact hShell_cd1.sub ((hψ.contDiffAt).of_le (by simp))
  have hEerr_diff : DifferentiableAt ℝ Eerr x := by
    exact hEerr_cd1.differentiableAt (by simp)
  have hβ_contDiff1 : ContDiff ℝ 1 (sphereOneBlend (d := d) ε) :=
    (contDiff_sphereOneBlend (d := d) hε (by linarith [unitBallApproxEps_lt_one n])).of_le
      (by simp)
  have hβ_diff : DifferentiableAt ℝ (sphereOneBlend (d := d) ε) x :=
    (hβ_contDiff1.differentiable (by simp)).differentiableAt
  have hEerr_val : ‖Eerr x‖ ≤ Cerr * ε := hCerr n x hx
  have hEerr_fderiv : ‖fderiv ℝ Eerr x‖ ≤ Cder := by
    exact hCder x (badAnnulusOne_subset_sphereOneControl (d := d) n hx)
  have hβ_fderiv : ‖fderiv ℝ (sphereOneBlend (d := d) ε) x‖ ≤ ↑Mst / (2 * ε) := by
    simpa [div_eq_mul_inv, two_mul, mul_assoc, mul_left_comm, mul_comm] using
      sphereOneBlend_fderiv_bound (d := d) hε x
  by_cases hlt1 : ‖x‖ < 1
  · have hxball : x ∈ Metric.ball (0 : E) 1 := by simpa [Metric.mem_ball, dist_zero_right] using hlt1
    have hEq :
        smoothUnitBallExtensionApprox (d := d) ε ψ =ᶠ[𝓝 x]
          fun y => ψ y + sphereOneBlend (d := d) ε y * Eerr y := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hxball2] with y hy
      unfold smoothUnitBallExtensionApprox Eerr
      rw [sphereTwoBlend_eq_one_of_mem_ball (d := d) hε hy]
      ring
    have hEqDer :
        (fderiv ℝ (smoothUnitBallExtensionApprox (d := d) ε ψ) x)
            (EuclideanSpace.single i 1) -
          exactUnitBallExtensionGradApply (d := d) ψ i x =
        (fderiv ℝ (fun y => sphereOneBlend (d := d) ε y * Eerr y) x)
          (EuclideanSpace.single i 1) := by
      have hψ_diff : DifferentiableAt ℝ ψ x := (hψ.differentiable (by simp)).differentiableAt
      have hprod_diff : DifferentiableAt ℝ (fun y => sphereOneBlend (d := d) ε y * Eerr y) x :=
        hβ_diff.mul hEerr_diff
      have hDeriv : fderiv ℝ (smoothUnitBallExtensionApprox (d := d) ε ψ) x =
          fderiv ℝ (fun y => ψ y + sphereOneBlend (d := d) ε y * Eerr y) x :=
        Filter.EventuallyEq.fderiv_eq hEq
      have hExact : exactUnitBallExtensionGradApply (d := d) ψ i x =
          (fderiv ℝ ψ x) (EuclideanSpace.single i 1) := by
        simp [exactUnitBallExtensionGradApply, hxball]
      rw [hExact, show (fderiv ℝ (smoothUnitBallExtensionApprox (d := d) ε ψ) x) =
        fderiv ℝ ψ x + fderiv ℝ (fun y => sphereOneBlend (d := d) ε y * Eerr y) x from
        hDeriv.trans (fderiv_add hψ_diff hprod_diff), ContinuousLinearMap.add_apply,
        add_sub_cancel_left]
    have hprod :=
      norm_fderiv_mul_le (d := d) (f := sphereOneBlend (d := d) ε) (g := Eerr) hβ_diff hEerr_diff
    have hei : ‖EuclideanSpace.single i (1 : ℝ)‖ = 1 := by simp
    calc
      ‖(fderiv ℝ (smoothUnitBallExtensionApprox (d := d) ε ψ) x)
          (EuclideanSpace.single i 1) -
        exactUnitBallExtensionGradApply (d := d) ψ i x‖
          = ‖(fderiv ℝ (fun y => sphereOneBlend (d := d) ε y * Eerr y) x)
              (EuclideanSpace.single i 1)‖ := by rw [hEqDer]
      _ ≤ ‖fderiv ℝ (fun y => sphereOneBlend (d := d) ε y * Eerr y) x‖ := by
            simpa [hei] using
              ContinuousLinearMap.le_opNorm
                (fderiv ℝ (fun y => sphereOneBlend (d := d) ε y * Eerr y) x)
                (EuclideanSpace.single i (1 : ℝ))
      _ ≤ |sphereOneBlend (d := d) ε x| * ‖fderiv ℝ Eerr x‖ +
            |Eerr x| * ‖fderiv ℝ (sphereOneBlend (d := d) ε) x‖ := hprod
      _ ≤ 1 * Cder + (Cerr * ε) * (↑Mst / (2 * ε)) := by
            have hβabs : |sphereOneBlend (d := d) ε x| ≤ 1 := by
              rw [abs_of_nonneg (sphereOneBlend_nonneg (d := d) (ε := ε) (x := x))]
              exact sphereOneBlend_le_one (d := d) (ε := ε) (x := x)
            have hterm1 :
                |sphereOneBlend (d := d) ε x| * ‖fderiv ℝ Eerr x‖ ≤ 1 * Cder := by
              exact mul_le_mul hβabs hEerr_fderiv (norm_nonneg _) (by positivity)
            have hterm2 :
                |Eerr x| * ‖fderiv ℝ (sphereOneBlend (d := d) ε) x‖
                  ≤ (Cerr * ε) * (↑Mst / (2 * ε)) := by
              exact mul_le_mul hEerr_val hβ_fderiv (by positivity) (by positivity)
            linarith
      _ ≤ Cder + Cerr * (↑Mst / 2) := product_bound_cancel_eps hε
  · have hgt1 : 1 < ‖x‖ := by
      have hle1 : 1 ≤ ‖x‖ := by linarith
      have hx1' : (1 : ℝ) ≠ ‖x‖ := by
        rw [Metric.mem_sphere, dist_zero_right] at hxSphere
        exact ne_comm.mp hxSphere
      exact lt_of_le_of_ne hle1 hx1'
    have hxOuter : x ∈ unitBallOuterShell (d := d) := by
      constructor
      · exact hgt1
      · linarith [hx.2, hεsmall]
    let Gerr : E → ℝ := fun y => (1 - sphereOneBlend (d := d) ε y) * Eerr y
    have hγ_diff : DifferentiableAt ℝ (fun y => 1 - sphereOneBlend (d := d) ε y) x :=
      by simpa using ((hasFDerivAt_const (1 : ℝ) x).sub hβ_diff.hasFDerivAt).differentiableAt
    have hγ_fderiv : ‖fderiv ℝ (fun y => 1 - sphereOneBlend (d := d) ε y) x‖
        ≤ ↑Mst / (2 * ε) := by
      have hγ_eq :
          fderiv ℝ (fun y => 1 - sphereOneBlend (d := d) ε y) x =
            -fderiv ℝ (sphereOneBlend (d := d) ε) x := by
        simpa using ((hasFDerivAt_const (1 : ℝ) x).sub hβ_diff.hasFDerivAt).fderiv
      rw [hγ_eq, norm_neg]
      exact hβ_fderiv
    have hEq :
        smoothUnitBallExtensionApprox (d := d) ε ψ =ᶠ[𝓝 x]
          fun y => unitBallShellFormula (d := d) ψ y - Gerr y := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hxball2] with y hy
      unfold smoothUnitBallExtensionApprox Gerr
      rw [sphereTwoBlend_eq_one_of_mem_ball (d := d) hε hy]
      simp [Eerr]
      ring
    have hExact :
        exactUnitBallExtensionGradApply (d := d) ψ i x =
          (fderiv ℝ (unitBallShellFormula (d := d) ψ) x) (EuclideanSpace.single i 1) := by
      simp [exactUnitBallExtensionGradApply, exactUnitBallShellGradApply, hxOuter, hlt1]
    have hx0 : x ≠ (0 : E) := by
      have : 0 < ‖x‖ := by linarith
      intro hx0
      simpa [hx0] using this.ne'
    have hShell_hasFDerivAt :
        HasFDerivAt (unitBallShellFormula (d := d) ψ)
          (fderiv ℝ (unitBallShellFormula (d := d) ψ) x) x := by
      exact ((contDiffAt_unitBallShellFormula (d := d) hψ hx0).differentiableAt (by simp)).hasFDerivAt
    have hGerr_diff : DifferentiableAt ℝ Gerr x := hγ_diff.mul hEerr_diff
    have hEqDer :
        (fderiv ℝ (smoothUnitBallExtensionApprox (d := d) ε ψ) x)
            (EuclideanSpace.single i 1) -
          exactUnitBallExtensionGradApply (d := d) ψ i x =
        -((fderiv ℝ Gerr x) (EuclideanSpace.single i 1)) := by
      have hDeriv : fderiv ℝ (smoothUnitBallExtensionApprox (d := d) ε ψ) x =
          fderiv ℝ (fun y => unitBallShellFormula (d := d) ψ y - Gerr y) x :=
        Filter.EventuallyEq.fderiv_eq hEq
      rw [hExact, show (fderiv ℝ (smoothUnitBallExtensionApprox (d := d) ε ψ) x) =
        fderiv ℝ (unitBallShellFormula (d := d) ψ) x - fderiv ℝ Gerr x from
        hDeriv.trans (fderiv_sub hShell_hasFDerivAt.differentiableAt hGerr_diff),
        ContinuousLinearMap.sub_apply, sub_sub_cancel_left]
    have hprod :=
      norm_fderiv_mul_le (d := d) (f := fun y => 1 - sphereOneBlend (d := d) ε y)
        (g := Eerr) hγ_diff hEerr_diff
    have hei : ‖EuclideanSpace.single i (1 : ℝ)‖ = 1 := by simp
    calc
      ‖(fderiv ℝ (smoothUnitBallExtensionApprox (d := d) ε ψ) x)
          (EuclideanSpace.single i 1) -
        exactUnitBallExtensionGradApply (d := d) ψ i x‖
          = ‖(fderiv ℝ Gerr x) (EuclideanSpace.single i 1)‖ := by
              rw [hEqDer, norm_neg]
      _ ≤ ‖fderiv ℝ Gerr x‖ := by
            simpa [hei] using
              ContinuousLinearMap.le_opNorm
                (fderiv ℝ Gerr x) (EuclideanSpace.single i (1 : ℝ))
      _ ≤ |1 - sphereOneBlend (d := d) ε x| * ‖fderiv ℝ Eerr x‖ +
            |Eerr x| * ‖fderiv ℝ (fun y => 1 - sphereOneBlend (d := d) ε y) x‖ := hprod
      _ ≤ 1 * Cder + (Cerr * ε) * (↑Mst / (2 * ε)) := by
            have hγabs : |1 - sphereOneBlend (d := d) ε x| ≤ 1 := by
              have hγ_nonneg : 0 ≤ 1 - sphereOneBlend (d := d) ε x := by
                linarith [sphereOneBlend_le_one (d := d) (ε := ε) (x := x)]
              rw [abs_of_nonneg hγ_nonneg]
              linarith [sphereOneBlend_nonneg (d := d) (ε := ε) (x := x)]
            have hterm1 :
                |1 - sphereOneBlend (d := d) ε x| * ‖fderiv ℝ Eerr x‖ ≤ 1 * Cder := by
              exact mul_le_mul hγabs hEerr_fderiv (norm_nonneg _) (by positivity)
            have hterm2 :
                |Eerr x| * ‖fderiv ℝ (fun y => 1 - sphereOneBlend (d := d) ε y) x‖
                  ≤ (Cerr * ε) * (↑Mst / (2 * ε)) := by
              exact mul_le_mul hEerr_val hγ_fderiv (by positivity) (by positivity)
            linarith
      _ ≤ Cder + Cerr * (↑Mst / 2) := product_bound_cancel_eps hε

omit [NeZero d] in
set_option maxHeartbeats 1600000 in
private theorem exists_gradApply_error_bound_badAnnulusTwo
    {ψ : E → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ n x i,
        x ∈ unitBallBadAnnulusTwo (d := d) (unitBallApproxEps n) →
        x ∉ Metric.sphere (0 : E) 2 →
        ‖(fderiv ℝ (smoothUnitBallExtensionApprox (d := d) (unitBallApproxEps n) ψ) x)
            (EuclideanSpace.single i 1) -
          exactUnitBallExtensionGradApply (d := d) ψ i x‖ ≤ C := by
  rcases exists_shellFormula_fderiv_bound (d := d) hψ with ⟨Cder, hCder_nonneg, hCder⟩
  rcases exists_shellFormula_error_bound (d := d) hψ with ⟨Cerr, hCerr_nonneg, hCerr⟩
  refine ⟨Cder + Cerr * (↑Mst / 2), by positivity, ?_⟩
  intro n x i hx hxSphere
  let ε := unitBallApproxEps n
  have hε : 0 < ε := unitBallApproxEps_pos n
  have hεsmall : ε ≤ (1 / 5 : ℝ) := unitBallApproxEps_le_one_fifth n
  let Ferr : E → ℝ := unitBallShellFormula (d := d) ψ
  have hFerr_cd1 : ContDiffAt ℝ 1 Ferr x := by
    have hx0 : x ≠ (0 : E) := by
      have : 0 < ‖x‖ := by linarith [hx.1]
      intro hx0
      simpa [hx0] using this.ne'
    exact (contDiffAt_unitBallShellFormula (d := d) hψ hx0).of_le (by simp)
  have hFerr_diff : DifferentiableAt ℝ Ferr x := by
    exact hFerr_cd1.differentiableAt (by simp)
  have hβ_contDiff1 : ContDiff ℝ 1 (sphereTwoBlend (d := d) ε) :=
    (contDiff_sphereTwoBlend (d := d) hε (by linarith [unitBallApproxEps_lt_one n])).of_le
      (by simp)
  have hβ_diff : DifferentiableAt ℝ (sphereTwoBlend (d := d) ε) x :=
    (hβ_contDiff1.differentiable (by simp)).differentiableAt
  have hFerr_val : ‖Ferr x‖ ≤ Cerr * ε := hCerr n x hx
  have hFerr_fderiv : ‖fderiv ℝ Ferr x‖ ≤ Cder := by
    exact hCder x (badAnnulusTwo_subset_sphereTwoControl (d := d) n hx)
  have hβ_fderiv : ‖fderiv ℝ (sphereTwoBlend (d := d) ε) x‖ ≤ ↑Mst / (2 * ε) := by
    simpa [div_eq_mul_inv, two_mul, mul_assoc, mul_left_comm, mul_comm] using
      sphereTwoBlend_fderiv_bound (d := d) hε x
  by_cases hxlt2 : ‖x‖ < 2
  · have hxOuter : x ∈ unitBallOuterShell (d := d) := by
      constructor <;> linarith [hx.1]
    have hgt1 : 1 + ε < ‖x‖ := by
      linarith [hx.1, hεsmall]
    have hEq :
        smoothUnitBallExtensionApprox (d := d) ε ψ =ᶠ[𝓝 x]
          fun y => unitBallShellFormula (d := d) ψ y +
            (sphereTwoBlend (d := d) ε y - 1) * Ferr y := by
      have hNhds : {y : E | 1 + ε < ‖y‖} ∈ 𝓝 x :=
        (isOpen_lt continuous_const continuous_norm).mem_nhds hgt1
      filter_upwards [hNhds] with y hy
      unfold smoothUnitBallExtensionApprox Ferr
      rw [sphereOneBlend_eq_one_of_norm_ge (d := d) hε (le_of_lt hy)]
      ring
    have hExact :
        exactUnitBallExtensionGradApply (d := d) ψ i x =
          (fderiv ℝ (unitBallShellFormula (d := d) ψ) x) (EuclideanSpace.single i 1) := by
      have hxnotBall1 : x ∉ Metric.ball (0 : E) 1 := by
        rw [Metric.mem_ball, dist_zero_right]
        exact not_lt_of_ge (le_of_lt hxOuter.1)
      simp [exactUnitBallExtensionGradApply, exactUnitBallShellGradApply, hxnotBall1, hxOuter]
    have hβm1_diff : DifferentiableAt ℝ (fun y => sphereTwoBlend (d := d) ε y - 1) x := by
      simpa using (hβ_diff.hasFDerivAt.sub (hasFDerivAt_const (1 : ℝ) x)).differentiableAt
    have hEqDer :
        (fderiv ℝ (smoothUnitBallExtensionApprox (d := d) ε ψ) x)
            (EuclideanSpace.single i 1) -
          exactUnitBallExtensionGradApply (d := d) ψ i x =
        (fderiv ℝ (fun y => (sphereTwoBlend (d := d) ε y - 1) * Ferr y) x)
          (EuclideanSpace.single i 1) := by
      have hShell_diff : DifferentiableAt ℝ (unitBallShellFormula (d := d) ψ) x := hFerr_diff
      have hDeriv : fderiv ℝ (smoothUnitBallExtensionApprox (d := d) ε ψ) x =
          fderiv ℝ (fun y => unitBallShellFormula (d := d) ψ y +
            (sphereTwoBlend (d := d) ε y - 1) * Ferr y) x :=
        Filter.EventuallyEq.fderiv_eq hEq
      rw [hExact, show (fderiv ℝ (smoothUnitBallExtensionApprox (d := d) ε ψ) x) =
        fderiv ℝ (unitBallShellFormula (d := d) ψ) x +
          fderiv ℝ (fun y => (sphereTwoBlend (d := d) ε y - 1) * Ferr y) x from
        hDeriv.trans (fderiv_add hShell_diff (hβm1_diff.mul hFerr_diff)),
        ContinuousLinearMap.add_apply, add_sub_cancel_left]
    have hβm1_fderiv :
        ‖fderiv ℝ (fun y => sphereTwoBlend (d := d) ε y - 1) x‖ ≤ ↑Mst / (2 * ε) := by
      have hβm1_eq :
          fderiv ℝ (fun y => sphereTwoBlend (d := d) ε y - 1) x =
            fderiv ℝ (sphereTwoBlend (d := d) ε) x := by
        simpa using (hβ_diff.hasFDerivAt.sub (hasFDerivAt_const (1 : ℝ) x)).fderiv
      rw [hβm1_eq]
      exact hβ_fderiv
    have hβm1_diff : DifferentiableAt ℝ (fun y => sphereTwoBlend (d := d) ε y - 1) x := by
      simpa using (hβ_diff.hasFDerivAt.sub (hasFDerivAt_const (1 : ℝ) x)).differentiableAt
    have hprod :=
      norm_fderiv_mul_le (d := d) (f := fun y => sphereTwoBlend (d := d) ε y - 1)
        (g := Ferr)
        hβm1_diff hFerr_diff
    have hei : ‖EuclideanSpace.single i (1 : ℝ)‖ = 1 := by simp
    calc
      ‖(fderiv ℝ (smoothUnitBallExtensionApprox (d := d) ε ψ) x)
          (EuclideanSpace.single i 1) -
        exactUnitBallExtensionGradApply (d := d) ψ i x‖
          = ‖(fderiv ℝ (fun y => (sphereTwoBlend (d := d) ε y - 1) * Ferr y) x)
              (EuclideanSpace.single i 1)‖ := by rw [hEqDer]
      _ ≤ ‖fderiv ℝ (fun y => (sphereTwoBlend (d := d) ε y - 1) * Ferr y) x‖ := by
            simpa [hei] using
              ContinuousLinearMap.le_opNorm
                (fderiv ℝ (fun y => (sphereTwoBlend (d := d) ε y - 1) * Ferr y) x)
                (EuclideanSpace.single i (1 : ℝ))
      _ ≤ |sphereTwoBlend (d := d) ε x - 1| * ‖fderiv ℝ Ferr x‖ +
            |Ferr x| * ‖fderiv ℝ (fun y => sphereTwoBlend (d := d) ε y - 1) x‖ := hprod
      _ ≤ 1 * Cder + (Cerr * ε) * (↑Mst / (2 * ε)) := by
            have hβabs : |sphereTwoBlend (d := d) ε x - 1| ≤ 1 := by
              rw [abs_sub_comm]
              have : 0 ≤ 1 - sphereTwoBlend (d := d) ε x := by
                linarith [sphereTwoBlend_le_one (d := d) (ε := ε) (x := x)]
              rw [abs_of_nonneg this]
              linarith [sphereTwoBlend_nonneg (d := d) (ε := ε) (x := x)]
            have hterm1 :
                |sphereTwoBlend (d := d) ε x - 1| * ‖fderiv ℝ Ferr x‖ ≤ 1 * Cder := by
              exact mul_le_mul hβabs hFerr_fderiv (norm_nonneg _) (by positivity)
            have hterm2 :
                |Ferr x| * ‖fderiv ℝ (fun y => sphereTwoBlend (d := d) ε y - 1) x‖
                  ≤ (Cerr * ε) * (↑Mst / (2 * ε)) := by
              exact mul_le_mul hFerr_val hβm1_fderiv (by positivity) (by positivity)
            linarith
      _ ≤ Cder + Cerr * (↑Mst / 2) := product_bound_cancel_eps hε
  · have hgt2 : 2 < ‖x‖ := by
        have hle2 : 2 ≤ ‖x‖ := by linarith
        have hx2' : (2 : ℝ) ≠ ‖x‖ := by
          simpa [Metric.mem_sphere, dist_zero_right, eq_comm] using hxSphere
        exact lt_of_le_of_ne hle2 hx2'
    have hgt1 : 1 + ε < ‖x‖ := by
      linarith [hgt2, unitBallApproxEps_lt_one n]
    have hEq :
        smoothUnitBallExtensionApprox (d := d) ε ψ =ᶠ[𝓝 x]
          fun y => sphereTwoBlend (d := d) ε y * Ferr y := by
      have hNhds : {y : E | 1 + ε < ‖y‖} ∈ 𝓝 x :=
        (isOpen_lt continuous_const continuous_norm).mem_nhds hgt1
      filter_upwards [hNhds] with y hy
      unfold smoothUnitBallExtensionApprox Ferr
      rw [sphereOneBlend_eq_one_of_norm_ge (d := d) hε (le_of_lt hy)]
      ring
    have hExact :
        exactUnitBallExtensionGradApply (d := d) ψ i x = 0 := by
      have hxnotBall1 : x ∉ Metric.ball (0 : E) 1 := by
        rw [Metric.mem_ball, dist_zero_right]
        exact not_lt_of_ge (le_trans (by norm_num) (le_of_lt hgt2))
      have hnotOuter : x ∉ unitBallOuterShell (d := d) := by
        intro hxOuter
        exact not_lt_of_ge (le_of_lt hgt2) hxOuter.2
      simp [exactUnitBallExtensionGradApply, exactUnitBallShellGradApply, hxnotBall1, hnotOuter]
    have hEqDer :
        (fderiv ℝ (smoothUnitBallExtensionApprox (d := d) ε ψ) x)
            (EuclideanSpace.single i 1) -
          exactUnitBallExtensionGradApply (d := d) ψ i x =
        (fderiv ℝ (fun y => sphereTwoBlend (d := d) ε y * Ferr y) x)
          (EuclideanSpace.single i 1) := by
      have hDeriv : fderiv ℝ (smoothUnitBallExtensionApprox (d := d) ε ψ) x =
          fderiv ℝ (fun y => sphereTwoBlend (d := d) ε y * Ferr y) x :=
        Filter.EventuallyEq.fderiv_eq hEq
      rw [hExact, sub_zero, hDeriv]
    have hprod :=
      norm_fderiv_mul_le (d := d) (f := sphereTwoBlend (d := d) ε) (g := Ferr) hβ_diff hFerr_diff
    have hei : ‖EuclideanSpace.single i (1 : ℝ)‖ = 1 := by simp
    calc
      ‖(fderiv ℝ (smoothUnitBallExtensionApprox (d := d) ε ψ) x)
          (EuclideanSpace.single i 1) -
        exactUnitBallExtensionGradApply (d := d) ψ i x‖
          = ‖(fderiv ℝ (fun y => sphereTwoBlend (d := d) ε y * Ferr y) x)
              (EuclideanSpace.single i 1)‖ := by rw [hEqDer]
      _ ≤ ‖fderiv ℝ (fun y => sphereTwoBlend (d := d) ε y * Ferr y) x‖ := by
            simpa [hei] using
              ContinuousLinearMap.le_opNorm
                (fderiv ℝ (fun y => sphereTwoBlend (d := d) ε y * Ferr y) x)
                (EuclideanSpace.single i (1 : ℝ))
      _ ≤ |sphereTwoBlend (d := d) ε x| * ‖fderiv ℝ Ferr x‖ +
            |Ferr x| * ‖fderiv ℝ (sphereTwoBlend (d := d) ε) x‖ := hprod
      _ ≤ 1 * Cder + (Cerr * ε) * (↑Mst / (2 * ε)) := by
            have hβabs : |sphereTwoBlend (d := d) ε x| ≤ 1 := by
              rw [abs_of_nonneg (sphereTwoBlend_nonneg (d := d) (ε := ε) (x := x))]
              exact sphereTwoBlend_le_one (d := d) (ε := ε) (x := x)
            have hterm1 :
                |sphereTwoBlend (d := d) ε x| * ‖fderiv ℝ Ferr x‖ ≤ 1 * Cder := by
              exact mul_le_mul hβabs hFerr_fderiv (norm_nonneg _) (by positivity)
            have hterm2 :
                |Ferr x| * ‖fderiv ℝ (sphereTwoBlend (d := d) ε) x‖
                  ≤ (Cerr * ε) * (↑Mst / (2 * ε)) := by
              exact mul_le_mul hFerr_val hβ_fderiv (by positivity) (by positivity)
            linarith
      _ ≤ Cder + Cerr * (↑Mst / 2) := product_bound_cancel_eps hε

omit [NeZero d] in
set_option maxHeartbeats 1600000 in
private lemma fderiv_smoothUnitBallExtensionApprox_eq_exactUnitBallExtensionGradApply_of_not_mem_badSet
    {ψ : E → ℝ} {n : ℕ} {x : E} {i : Fin d}
    (hx1 : x ∉ Metric.sphere (0 : E) 1)
    (hx2 : x ∉ Metric.sphere (0 : E) 2)
    (hx1L : x ∉ Metric.sphere (0 : E) (1 - unitBallApproxEps n))
    (hx1R : x ∉ Metric.sphere (0 : E) (1 + unitBallApproxEps n))
    (hx2L : x ∉ Metric.sphere (0 : E) (2 - unitBallApproxEps n))
    (hx2R : x ∉ Metric.sphere (0 : E) (2 + unitBallApproxEps n))
    (hbad : x ∉ unitBallBadSet (d := d) (unitBallApproxEps n)) :
    (fderiv ℝ (smoothUnitBallExtensionApprox (d := d) (unitBallApproxEps n) ψ) x)
        (EuclideanSpace.single i 1) =
      exactUnitBallExtensionGradApply (d := d) ψ i x := by
  let ε := unitBallApproxEps n
  by_cases hlt1 : ‖x‖ < 1
  · have hcore : ‖x‖ < 1 - ε := by
      by_contra hnot
      have hge : 1 - ε ≤ ‖x‖ := by
        exact not_lt.mp hnot
      have hne : (1 - ε : ℝ) ≠ ‖x‖ := by
        intro hEq
        exact hx1L (by simpa [Metric.mem_sphere, dist_zero_right, eq_comm] using hEq)
      have hgt : 1 - ε < ‖x‖ := lt_of_le_of_ne hge hne
      have hlt : ‖x‖ < 1 + ε := by
        linarith [hlt1, unitBallApproxEps_pos n]
      exact hbad (Or.inl ⟨hgt, hlt⟩)
    have hxcore : x ∈ Metric.ball (0 : E) (1 - ε) := by
      simpa [Metric.mem_ball, dist_zero_right] using hcore
    have hEq :
        smoothUnitBallExtensionApprox (d := d) ε ψ =ᶠ[𝓝 x]
          unitBallExtension (d := d) ψ := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hxcore] with y hy
      simpa using smoothUnitBallExtensionApprox_eq_of_mem_innerCore (d := d)
        (unitBallApproxEps_pos n) (ψ := ψ) hy
    have hDer :
        fderiv ℝ (smoothUnitBallExtensionApprox (d := d) ε ψ) x =
          fderiv ℝ (unitBallExtension (d := d) ψ) x :=
      Filter.EventuallyEq.fderiv_eq hEq
    have hxball : x ∈ Metric.ball (0 : E) 1 := by
      simpa [Metric.mem_ball, dist_zero_right] using hlt1
    calc
      (fderiv ℝ (smoothUnitBallExtensionApprox (d := d) ε ψ) x)
          (EuclideanSpace.single i 1)
          = (fderiv ℝ (unitBallExtension (d := d) ψ) x) (EuclideanSpace.single i 1) := by
              simpa using congrArg (fun A => A (EuclideanSpace.single i 1)) hDer
      _ = exactUnitBallExtensionGradApply (d := d) ψ i x := by
            simpa [exactUnitBallExtensionGradApply, hxball] using
              congrArg (fun T : E →L[ℝ] ℝ => T (EuclideanSpace.single i 1))
                (fderiv_unitBallExtension_eq_of_mem_ball (d := d) (u := ψ) hxball)
  · by_cases hlt2 : ‖x‖ < 2
    · have hgt1 : 1 < ‖x‖ := by
        have hle1 : 1 ≤ ‖x‖ := by linarith
        have hx1' : (1 : ℝ) ≠ ‖x‖ := by
          simpa [Metric.mem_sphere, dist_zero_right, eq_comm] using hx1
        exact lt_of_le_of_ne hle1 hx1'
      have hcoreL : 1 + ε < ‖x‖ := by
        by_contra hnot
        have hle : ‖x‖ ≤ 1 + ε := by linarith
        have hne : ‖x‖ ≠ 1 + ε := by
          intro hEq
          exact hx1R (by simpa [Metric.mem_sphere, dist_zero_right] using hEq)
        have hlt : ‖x‖ < 1 + ε := lt_of_le_of_ne hle hne
        exact hbad (Or.inl ⟨by linarith, hlt⟩)
      have hcoreR : ‖x‖ < 2 - ε := by
        by_contra hnot
        have hge : 2 - ε ≤ ‖x‖ := by
          exact not_lt.mp hnot
        have hne : (2 - ε : ℝ) ≠ ‖x‖ := by
          intro hEq
          exact hx2L (by simpa [Metric.mem_sphere, dist_zero_right, eq_comm] using hEq)
        have hgt : 2 - ε < ‖x‖ := lt_of_le_of_ne hge hne
        exact hbad (Or.inr ⟨hgt, by linarith⟩)
      have hEq :
          smoothUnitBallExtensionApprox (d := d) ε ψ =ᶠ[𝓝 x]
            unitBallExtension (d := d) ψ := by
        have hLeft :
            {y : E | 1 + ε < ‖y‖} ∈ 𝓝 x :=
          (isOpen_lt continuous_const continuous_norm).mem_nhds hcoreL
        have hRight :
            {y : E | ‖y‖ < 2 - ε} ∈ 𝓝 x :=
          (isOpen_lt continuous_norm continuous_const).mem_nhds hcoreR
        filter_upwards [hLeft, hRight] with y hyL hyR
        simpa using smoothUnitBallExtensionApprox_eq_of_mem_shellCore (d := d)
          (unitBallApproxEps_pos n) (ψ := ψ) hyL hyR
      have hDer :
          fderiv ℝ (smoothUnitBallExtensionApprox (d := d) ε ψ) x =
            fderiv ℝ (unitBallExtension (d := d) ψ) x :=
        Filter.EventuallyEq.fderiv_eq hEq
      have hxOuter : x ∈ unitBallOuterShell (d := d) := by
        constructor <;> linarith
      calc
        (fderiv ℝ (smoothUnitBallExtensionApprox (d := d) ε ψ) x)
            (EuclideanSpace.single i 1)
            = (fderiv ℝ (unitBallExtension (d := d) ψ) x) (EuclideanSpace.single i 1) := by
                simpa using congrArg (fun A => A (EuclideanSpace.single i 1)) hDer
        _ = exactUnitBallExtensionGradApply (d := d) ψ i x := by
              simpa [exactUnitBallExtensionGradApply, exactUnitBallShellGradApply, hxOuter, hlt1] using
                congrArg (fun T : E →L[ℝ] ℝ => T (EuclideanSpace.single i 1))
                  (fderiv_unitBallExtension_eq_shellFormula_of_mem_outerShell (d := d) hxOuter)
    · have hgt2 : 2 < ‖x‖ := by
        have hle2 : 2 ≤ ‖x‖ := by linarith
        have hx2' : (2 : ℝ) ≠ ‖x‖ := by
          simpa [Metric.mem_sphere, dist_zero_right, eq_comm] using hx2
        exact lt_of_le_of_ne hle2 hx2'
      have hfar : 2 + ε < ‖x‖ := by
        by_contra hnot
        have hle : ‖x‖ ≤ 2 + ε := by linarith
        have hne : ‖x‖ ≠ 2 + ε := by
          intro hEq
          exact hx2R (by simpa [Metric.mem_sphere, dist_zero_right] using hEq)
        have hlt : ‖x‖ < 2 + ε := lt_of_le_of_ne hle hne
        exact hbad (Or.inr ⟨by linarith, hlt⟩)
      have hEq :
          smoothUnitBallExtensionApprox (d := d) ε ψ =ᶠ[𝓝 x] fun _ : E => (0 : ℝ) := by
        have hNhds :
            {y : E | 2 + ε < ‖y‖} ∈ 𝓝 x :=
          (isOpen_lt continuous_const continuous_norm).mem_nhds hfar
        filter_upwards [hNhds] with y hy
        simpa using smoothUnitBallExtensionApprox_eq_zero_of_norm_ge (d := d)
          (unitBallApproxEps_pos n) (ψ := ψ) (le_of_lt hy)
      have hDer :
          fderiv ℝ (smoothUnitBallExtensionApprox (d := d) ε ψ) x = 0 :=
        by simpa using (Filter.EventuallyEq.fderiv_eq hEq)
      have hnotOuter : x ∉ unitBallOuterShell (d := d) := by
        intro hxOuter
        linarith [hxOuter.2, hgt2]
      simpa [exactUnitBallExtensionGradApply, exactUnitBallShellGradApply, hlt1, hlt2,
        hnotOuter]
        using congrArg (fun A => A (EuclideanSpace.single i 1)) hDer

-- Standalone: pointwise gradient convergence at a point away from spheres.
omit [NeZero d] in
set_option maxHeartbeats 1600000 in
private lemma tendsto_fderiv_sub_exactGrad_pointwise
    {ψ : E → ℝ} {x : E} {i : Fin d}
    (hx1 : x ∉ Metric.sphere (0 : E) 1) (hx2 : x ∉ Metric.sphere (0 : E) 2)
    (hgrad : exactUnitBallExtensionGradApply (d := d) ψ i x =
      (fderiv ℝ (unitBallExtension (d := d) ψ) x) (EuclideanSpace.single i 1)) :
    Tendsto (fun n =>
      (fderiv ℝ (smoothUnitBallExtensionApprox (d := d) (unitBallApproxEps n) ψ) x)
          (EuclideanSpace.single i 1) -
        exactUnitBallExtensionGradApply (d := d) ψ i x) atTop (nhds 0) := by
  have hx1' : ‖x‖ ≠ 1 := by simpa [Metric.mem_sphere, dist_zero_right] using hx1
  have hx2' : ‖x‖ ≠ 2 := by simpa [Metric.mem_sphere, dist_zero_right] using hx2
  have hpt := tendsto_fderiv_smoothUnitBallExtensionApprox_pointwise (d := d) (ψ := ψ) hx1' hx2'
  -- hpt : Tendsto (fun n => fderiv(smoothApprox n) x) atTop (nhds (fderiv(E) x))
  -- We need: fderiv(smoothApprox n)(ei) - exactGrad i x → 0
  -- Since exactGrad i x = fderiv(E)(ei) (by hgrad), this is:
  --   fderiv(smoothApprox n)(ei) - fderiv(E)(ei) → 0
  rw [hgrad]
  have happly : Tendsto (fun n =>
      (fderiv ℝ (smoothUnitBallExtensionApprox (d := d) (unitBallApproxEps n) ψ) x)
        (EuclideanSpace.single i 1)) atTop
      (nhds ((fderiv ℝ (unitBallExtension (d := d) ψ) x) (EuclideanSpace.single i 1))) :=
    (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single i 1)).continuous.continuousAt.tendsto.comp hpt
  rwa [tendsto_sub_nhds_zero_iff]

set_option maxHeartbeats 3200000 in
private theorem tendsto_eLpNorm_fderiv_smoothUnitBallExtensionApprox_sub_exactGradApply
    {p : ℝ} (hp : 1 < p) {ψ : E → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) :
    ∀ i : Fin d,
      Tendsto
        (fun n =>
          eLpNorm
            (fun x =>
              (fderiv ℝ (smoothUnitBallExtensionApprox (d := d) (unitBallApproxEps n) ψ) x)
                  (EuclideanSpace.single i 1) -
                exactUnitBallExtensionGradApply (d := d) ψ i x)
            (ENNReal.ofReal p) volume)
        atTop (nhds 0) := by
  rcases exists_gradApply_error_bound_badAnnulusOne (d := d) hψ with ⟨C1, hC1_nonneg, hC1⟩
  rcases exists_gradApply_error_bound_badAnnulusTwo (d := d) hψ with ⟨C2, hC2_nonneg, hC2⟩
  intro i
  let C : ℝ := max C1 C2
  let K : Set E := Metric.closedBall (0 : E) (9 / 4 : ℝ)
  let F : ℕ → E → ℝ := fun n x =>
    (fderiv ℝ (smoothUnitBallExtensionApprox (d := d) (unitBallApproxEps n) ψ) x)
        (EuclideanSpace.single i 1) -
      exactUnitBallExtensionGradApply (d := d) ψ i x
  let H : E → ℝ := K.indicator fun _ => C
  have hHp : 1 ≤ ENNReal.ofReal p := by simpa using ENNReal.ofReal_le_ofReal hp.le
  have hHp' : ENNReal.ofReal p ≠ ∞ := by simp
  have hH_memLp : MemLp H (ENNReal.ofReal p) volume := by
    unfold H K
    rw [MeasureTheory.memLp_indicator_iff_restrict (μ := volume)
      (s := Metric.closedBall (0 : E) (9 / 4 : ℝ))
      (p := ENNReal.ofReal p) Metric.isClosed_closedBall.measurableSet]
    letI : IsFiniteMeasure (volume.restrict (Metric.closedBall (0 : E) (9 / 4 : ℝ))) := by
      refine ⟨by simpa using measure_closedBall_lt_top (x := (0 : E)) (r := (9 / 4 : ℝ))⟩
    simpa using (memLp_const C : MemLp (fun _ : E => C) (ENNReal.ofReal p)
      (volume.restrict (Metric.closedBall (0 : E) (9 / 4 : ℝ))))
  have hF_meas : ∀ n, AEStronglyMeasurable (F n) volume := by
    intro n; unfold F
    have hderiv_cont :
        Continuous (fun x =>
          (fderiv ℝ (smoothUnitBallExtensionApprox (d := d) (unitBallApproxEps n) ψ) x)
            (EuclideanSpace.single i 1)) :=
      ((smoothUnitBallExtensionApprox_contDiff (d := d) (unitBallApproxEps_pos n)
        (unitBallApproxEps_lt_one n) hψ).continuous_fderiv (by simp)).clm_apply continuous_const
    exact hderiv_cont.aestronglyMeasurable.sub
      (measurable_exactUnitBallExtensionGradApply (d := d) hψ i).aestronglyMeasurable
  -- AE domination by H
  have hF_dom : ∀ n, ∀ᵐ x ∂volume, ‖F n x‖ ≤ H x := by
    intro n
    have hae1 : ∀ᵐ x ∂(volume : Measure E), x ∉ Metric.sphere (0 : E) 1 := by
      rw [ae_iff]; simpa [Metric.sphere, dist_zero_right] using
        Measure.addHaar_sphere (μ := (volume : Measure E)) (x := (0 : E)) 1
    have hae2 : ∀ᵐ x ∂(volume : Measure E), x ∉ Metric.sphere (0 : E) 2 := by
      rw [ae_iff]; simpa [Metric.sphere, dist_zero_right] using
        Measure.addHaar_sphere (μ := (volume : Measure E)) (x := (0 : E)) 2
    have hae1L : ∀ᵐ x ∂(volume : Measure E),
        x ∉ Metric.sphere (0 : E) (1 - unitBallApproxEps n) := by
      rw [ae_iff]; simpa [Metric.sphere, dist_zero_right] using
        Measure.addHaar_sphere (μ := (volume : Measure E)) (x := (0 : E)) _
    have hae1R : ∀ᵐ x ∂(volume : Measure E),
        x ∉ Metric.sphere (0 : E) (1 + unitBallApproxEps n) := by
      rw [ae_iff]; simpa [Metric.sphere, dist_zero_right] using
        Measure.addHaar_sphere (μ := (volume : Measure E)) (x := (0 : E)) _
    have hae2L : ∀ᵐ x ∂(volume : Measure E),
        x ∉ Metric.sphere (0 : E) (2 - unitBallApproxEps n) := by
      rw [ae_iff]; simpa [Metric.sphere, dist_zero_right] using
        Measure.addHaar_sphere (μ := (volume : Measure E)) (x := (0 : E)) _
    have hae2R : ∀ᵐ x ∂(volume : Measure E),
        x ∉ Metric.sphere (0 : E) (2 + unitBallApproxEps n) := by
      rw [ae_iff]; simpa [Metric.sphere, dist_zero_right] using
        Measure.addHaar_sphere (μ := (volume : Measure E)) (x := (0 : E)) _
    filter_upwards [hae1, hae2, hae1L, hae1R, hae2L, hae2R] with x hx1 hx2 hx1L hx1R hx2L hx2R
    unfold F H K C
    by_cases hxK : x ∈ Metric.closedBall (0 : E) (9 / 4 : ℝ)
    · rw [Set.indicator_of_mem hxK]
      by_cases hbad : x ∈ unitBallBadSet (d := d) (unitBallApproxEps n)
      · rcases hbad with hxA1 | hxA2
        · exact le_trans (hC1 n x i hxA1 hx1) (le_max_left _ _)
        · exact le_trans (hC2 n x i hxA2 hx2) (le_max_right _ _)
      · have hEq :=
          fderiv_smoothUnitBallExtensionApprox_eq_exactUnitBallExtensionGradApply_of_not_mem_badSet
            (d := d) (ψ := ψ) (n := n) (i := i) hx1 hx2 hx1L hx1R hx2L hx2R hbad
        have hC_nonneg : 0 ≤ C := le_trans hC1_nonneg (le_max_left _ _)
        simp only [hEq, sub_self, norm_zero]; exact hC_nonneg
    · rw [Set.indicator_of_notMem hxK]
      have hbad : x ∉ unitBallBadSet (d := d) (unitBallApproxEps n) := by
        intro hxBad
        rcases hxBad with hx1' | hx2'
        · have hxK' := sphereOneControl_subset_closedBall (d := d)
            (badAnnulusOne_subset_sphereOneControl (d := d) n hx1')
          exact hxK (by rw [Metric.mem_closedBall, dist_zero_right] at hxK' ⊢; linarith)
        · exact hxK (sphereTwoControl_subset_closedBall (d := d)
            (badAnnulusTwo_subset_sphereTwoControl (d := d) n hx2'))
      have hEq :=
        fderiv_smoothUnitBallExtensionApprox_eq_exactUnitBallExtensionGradApply_of_not_mem_badSet
          (d := d) (ψ := ψ) (n := n) (i := i) hx1 hx2 hx1L hx1R hx2L hx2R hbad
      simp [hEq]
  -- Indicator domination for norms
  have hF_dom_norm : ∀ n, ∀ᵐ x ∂volume, ‖F n x‖ ≤ ‖H x‖ := by
    intro n
    filter_upwards [hF_dom n] with x hx
    exact hx.trans (le_abs_self _)
  -- UnifIntegrable and UnifTight
  have huiF : UnifIntegrable F (ENNReal.ofReal p) volume := by
    intro ε hε
    obtain ⟨δ, hδ, hδ'⟩ :=
      MeasureTheory.unifIntegrable_const (p := ENNReal.ofReal p) hHp hHp' hH_memLp hε
    exact ⟨δ, hδ, fun n s hs hμs =>
      le_trans (eLpNorm_mono_ae ((hF_dom_norm n).mono fun x hx => by
        simp only [Set.indicator]; split <;> [exact hx; exact le_refl _]))
        (hδ' 0 s hs hμs)⟩
  have hutF : UnifTight F (ENNReal.ofReal p) volume := by
    intro ε hε
    obtain ⟨s, hμs, hs'⟩ := MeasureTheory.unifTight_const
      (p := ENNReal.ofReal p) hHp' hH_memLp hε
    exact ⟨s, hμs, fun n =>
      le_trans (eLpNorm_mono_ae ((hF_dom_norm n).mono fun x hx => by
        simp only [Set.indicator]; split <;> [exact hx; exact le_refl _]))
        (hs' 0)⟩
  -- Pointwise AE convergence
  have hF_ae : ∀ᵐ x ∂volume, Tendsto (fun n => F n x) atTop (nhds 0) := by
    have hae1 : ∀ᵐ x ∂(volume : Measure E), x ∉ Metric.sphere (0 : E) 1 := by
      rw [ae_iff]; simpa [Metric.sphere, dist_zero_right] using
        Measure.addHaar_sphere (μ := (volume : Measure E)) (x := (0 : E)) 1
    have hae2 : ∀ᵐ x ∂(volume : Measure E), x ∉ Metric.sphere (0 : E) 2 := by
      rw [ae_iff]; simpa [Metric.sphere, dist_zero_right] using
        Measure.addHaar_sphere (μ := (volume : Measure E)) (x := (0 : E)) 2
    have hgrad_ae : ∀ᵐ x ∂volume,
        exactUnitBallExtensionGradApply (d := d) ψ i x =
          (fderiv ℝ (unitBallExtension (d := d) ψ) x) (EuclideanSpace.single i 1) := by
      filter_upwards [ae_eq_exactUnitBallExtensionGrad (d := d) (ψ := ψ)] with x hx
      simp only [exactUnitBallExtensionGradApply,
        smoothUnitBallExtensionGrad] at hx ⊢
      exact congrArg (· i) hx
    filter_upwards [hae1, hae2, hgrad_ae] with x hx1 hx2 hgrad
    exact tendsto_fderiv_sub_exactGrad_pointwise (d := d) hx1 hx2 hgrad
  -- Conclude via Vitali convergence
  have hLpF0 :=
    MeasureTheory.tendsto_Lp_of_tendsto_ae hHp hHp' hF_meas
      (MeasureTheory.MemLp.zero' (p := ENNReal.ofReal p) (μ := volume)) huiF hutF hF_ae
  have hEq0 : (fun n => eLpNorm (F n - fun _ => (0 : ℝ)) (ENNReal.ofReal p) volume) =
      (fun n => eLpNorm (F n) (ENNReal.ofReal p) volume) := by
    funext n; congr 1; ext x; simp
  rw [hEq0] at hLpF0
  simpa [F] using hLpF0

omit [NeZero d] in
set_option maxHeartbeats 800000 in
private theorem memLp_smoothUnitBallExtensionApprox_sub_unitBallExtension
    {p : ℝ} (_hp : 1 < p) {ψ : E → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (n : ℕ) :
    MemLp
      (fun x =>
        smoothUnitBallExtensionApprox (d := d) (unitBallApproxEps n) ψ x -
          unitBallExtension (d := d) ψ x)
      (ENNReal.ofReal p) volume := by
  rcases exists_fun_error_bound_badSet (d := d) hψ with ⟨C, hC_nonneg, hC⟩
  let K : Set E := Metric.closedBall (0 : E) (9 / 4 : ℝ)
  let F : E → ℝ := fun x =>
    smoothUnitBallExtensionApprox (d := d) (unitBallApproxEps n) ψ x -
      unitBallExtension (d := d) ψ x
  let H : E → ℝ := K.indicator fun _ => C
  have hF_meas : AEStronglyMeasurable F volume := by
    unfold F
    exact ((smoothUnitBallExtensionApprox_contDiff (d := d) (unitBallApproxEps_pos n)
      (unitBallApproxEps_lt_one n) hψ).continuous.aestronglyMeasurable.sub
        ((measurable_exactUnitBallExtensionModel (d := d) hψ).aestronglyMeasurable.congr
          (Filter.EventuallyEq.of_eq
            (exactUnitBallExtensionModel_eq_unitBallExtension (d := d) (ψ := ψ)))))
  have hHp' : ENNReal.ofReal p ≠ ∞ := by simp
  have hH_memLp : MemLp H (ENNReal.ofReal p) volume := by
    unfold H K
    rw [MeasureTheory.memLp_indicator_iff_restrict (μ := volume)
      (s := Metric.closedBall (0 : E) (9 / 4 : ℝ))
      (p := ENNReal.ofReal p) Metric.isClosed_closedBall.measurableSet]
    letI : IsFiniteMeasure (volume.restrict (Metric.closedBall (0 : E) (9 / 4 : ℝ))) := by
      refine ⟨by
        simpa using (measure_closedBall_lt_top (x := (0 : E)) (r := (9 / 4 : ℝ)))⟩
    simpa using (memLp_const C : MemLp (fun _ : E => C) (ENNReal.ofReal p)
      (volume.restrict (Metric.closedBall (0 : E) (9 / 4 : ℝ))))
  have hF_dom : ∀ x, ‖F x‖ ≤ H x := by
    intro x
    unfold F H K
    by_cases hxK : x ∈ Metric.closedBall (0 : E) (9 / 4 : ℝ)
    · by_cases hbad : x ∈ unitBallBadSet (d := d) (unitBallApproxEps n)
      · rw [Set.indicator_of_mem hxK]
        have hbound := hC n x
        rw [Set.indicator_of_mem hbad] at hbound
        have hEqx :
            exactUnitBallExtensionModel (d := d) ψ x = unitBallExtension (d := d) ψ x :=
          congrFun (exactUnitBallExtensionModel_eq_unitBallExtension (d := d) (ψ := ψ)) x
        simpa [hEqx] using hbound
      · rw [Set.indicator_of_mem hxK]
        have hEq := smoothUnitBallExtensionApprox_eq_unitBallExtension_of_not_mem_badSet
          (d := d) (ψ := ψ) (n := n) hbad
        have hC_nonneg' : 0 ≤ C := hC_nonneg
        simpa [hEq] using hC_nonneg'
    · rw [Set.indicator_of_notMem hxK]
      have hbad : x ∉ unitBallBadSet (d := d) (unitBallApproxEps n) := by
        intro hxBad
        rcases hxBad with hx1 | hx2
        · have hxK' : x ∈ Metric.closedBall (0 : E) (5 / 4 : ℝ) :=
            sphereOneControl_subset_closedBall (d := d)
              (badAnnulusOne_subset_sphereOneControl (d := d) n hx1)
          have : x ∈ Metric.closedBall (0 : E) (9 / 4 : ℝ) := by
            rw [Metric.mem_closedBall, dist_zero_right] at hxK' ⊢
            linarith
          exact hxK this
        · exact hxK (sphereTwoControl_subset_closedBall (d := d)
            (badAnnulusTwo_subset_sphereTwoControl (d := d) n hx2))
      have hEq := smoothUnitBallExtensionApprox_eq_unitBallExtension_of_not_mem_badSet
        (d := d) (ψ := ψ) (n := n) hbad
      simp [hEq]
  have hH_nonneg : ∀ x, 0 ≤ H x := by
    intro x
    unfold H K
    by_cases hxK : x ∈ Metric.closedBall (0 : E) (9 / 4 : ℝ) <;> simp [Set.indicator, hxK, hC_nonneg]
  exact MemLp.of_le hH_memLp hF_meas <|
    (Eventually.of_forall hF_dom).mono fun x hx => by
      simpa [abs_of_nonneg (hH_nonneg x)] using hx

set_option maxHeartbeats 800000 in
private theorem memLp_fderiv_smoothUnitBallExtensionApprox_sub_exactGradApply
    {p : ℝ} (_hp : 1 < p) {ψ : E → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (n : ℕ) (i : Fin d) :
    MemLp
      (fun x =>
        (fderiv ℝ (smoothUnitBallExtensionApprox (d := d) (unitBallApproxEps n) ψ) x)
            (EuclideanSpace.single i 1) -
          exactUnitBallExtensionGradApply (d := d) ψ i x)
      (ENNReal.ofReal p) volume := by
  rcases exists_gradApply_error_bound_badAnnulusOne (d := d) hψ with ⟨C1, hC1_nonneg, hC1⟩
  rcases exists_gradApply_error_bound_badAnnulusTwo (d := d) hψ with ⟨C2, hC2_nonneg, hC2⟩
  let C : ℝ := max C1 C2
  let K : Set E := Metric.closedBall (0 : E) (9 / 4 : ℝ)
  let F : E → ℝ := fun x =>
    (fderiv ℝ (smoothUnitBallExtensionApprox (d := d) (unitBallApproxEps n) ψ) x)
        (EuclideanSpace.single i 1) -
      exactUnitBallExtensionGradApply (d := d) ψ i x
  let H : E → ℝ := K.indicator fun _ => C
  have hF_meas : AEStronglyMeasurable F volume := by
    unfold F
    have hderiv_cont :
        Continuous (fun x =>
          (fderiv ℝ (smoothUnitBallExtensionApprox (d := d) (unitBallApproxEps n) ψ) x)
            (EuclideanSpace.single i 1)) :=
      ((smoothUnitBallExtensionApprox_contDiff (d := d) (unitBallApproxEps_pos n)
        (unitBallApproxEps_lt_one n) hψ).continuous_fderiv
          (by simp : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0)).clm_apply continuous_const
    exact hderiv_cont.aestronglyMeasurable.sub
      (measurable_exactUnitBallExtensionGradApply (d := d) hψ i).aestronglyMeasurable
  have hH_memLp : MemLp H (ENNReal.ofReal p) volume := by
    unfold H K
    rw [MeasureTheory.memLp_indicator_iff_restrict (μ := volume)
      (s := Metric.closedBall (0 : E) (9 / 4 : ℝ))
      (p := ENNReal.ofReal p) Metric.isClosed_closedBall.measurableSet]
    letI : IsFiniteMeasure (volume.restrict (Metric.closedBall (0 : E) (9 / 4 : ℝ))) := by
      refine ⟨by
        simpa using (measure_closedBall_lt_top (x := (0 : E)) (r := (9 / 4 : ℝ)))⟩
    simpa using (memLp_const C : MemLp (fun _ : E => C) (ENNReal.ofReal p)
      (volume.restrict (Metric.closedBall (0 : E) (9 / 4 : ℝ))))
  have hs1 : volume (Metric.sphere (0 : E) 1) = 0 := by
    simpa using (Measure.addHaar_sphere (μ := (volume : Measure E)) (x := (0 : E)) 1)
  have hs2 : volume (Metric.sphere (0 : E) 2) = 0 := by
    simpa using (Measure.addHaar_sphere (μ := (volume : Measure E)) (x := (0 : E)) 2)
  have hs1L : volume (Metric.sphere (0 : E) (1 - unitBallApproxEps n)) = 0 := by
    simpa using
      (Measure.addHaar_sphere (μ := (volume : Measure E)) (x := (0 : E))
        (1 - unitBallApproxEps n))
  have hs1R : volume (Metric.sphere (0 : E) (1 + unitBallApproxEps n)) = 0 := by
    simpa using
      (Measure.addHaar_sphere (μ := (volume : Measure E)) (x := (0 : E))
        (1 + unitBallApproxEps n))
  have hs2L : volume (Metric.sphere (0 : E) (2 - unitBallApproxEps n)) = 0 := by
    simpa using
      (Measure.addHaar_sphere (μ := (volume : Measure E)) (x := (0 : E))
        (2 - unitBallApproxEps n))
  have hs2R : volume (Metric.sphere (0 : E) (2 + unitBallApproxEps n)) = 0 := by
    simpa using
      (Measure.addHaar_sphere (μ := (volume : Measure E)) (x := (0 : E))
        (2 + unitBallApproxEps n))
  have hF_dom :
      ∀ᵐ x ∂volume, ‖F x‖ ≤ H x := by
    have hae1 : ∀ᵐ x ∂volume, x ∉ Metric.sphere (0 : E) 1 := by
      rw [ae_iff]
      simpa [Metric.sphere, dist_zero_right] using hs1
    have hae2 : ∀ᵐ x ∂volume, x ∉ Metric.sphere (0 : E) 2 := by
      rw [ae_iff]
      simpa [Metric.sphere, dist_zero_right] using hs2
    have hae1L : ∀ᵐ x ∂volume, x ∉ Metric.sphere (0 : E) (1 - unitBallApproxEps n) := by
      rw [ae_iff]
      simpa [Metric.sphere, dist_zero_right] using hs1L
    have hae1R : ∀ᵐ x ∂volume, x ∉ Metric.sphere (0 : E) (1 + unitBallApproxEps n) := by
      rw [ae_iff]
      simpa [Metric.sphere, dist_zero_right] using hs1R
    have hae2L : ∀ᵐ x ∂volume, x ∉ Metric.sphere (0 : E) (2 - unitBallApproxEps n) := by
      rw [ae_iff]
      simpa [Metric.sphere, dist_zero_right] using hs2L
    have hae2R : ∀ᵐ x ∂volume, x ∉ Metric.sphere (0 : E) (2 + unitBallApproxEps n) := by
      rw [ae_iff]
      simpa [Metric.sphere, dist_zero_right] using hs2R
    filter_upwards [hae1, hae2, hae1L, hae1R, hae2L, hae2R] with x hx1 hx2 hx1L hx1R hx2L hx2R
    unfold F H K C
    by_cases hxK : x ∈ Metric.closedBall (0 : E) (9 / 4 : ℝ)
    · by_cases hbad : x ∈ unitBallBadSet (d := d) (unitBallApproxEps n)
      · rw [Set.indicator_of_mem hxK]
        rcases hbad with hxA1 | hxA2
        · exact le_trans (hC1 n x i hxA1 hx1) (le_max_left _ _)
        · exact le_trans (hC2 n x i hxA2 hx2) (le_max_right _ _)
      · rw [Set.indicator_of_mem hxK]
        have hEq :=
          fderiv_smoothUnitBallExtensionApprox_eq_exactUnitBallExtensionGradApply_of_not_mem_badSet
            (d := d) (ψ := ψ) (n := n) (i := i) hx1 hx2 hx1L hx1R hx2L hx2R hbad
        have hC_nonneg : 0 ≤ C := by
          exact le_trans hC1_nonneg (le_max_left _ _)
        simp only [hEq, sub_self, norm_zero]; exact hC_nonneg
    · rw [Set.indicator_of_notMem hxK]
      have hbad : x ∉ unitBallBadSet (d := d) (unitBallApproxEps n) := by
        intro hxBad
        rcases hxBad with hx1 | hx2
        · have hxK' : x ∈ Metric.closedBall (0 : E) (5 / 4 : ℝ) :=
            sphereOneControl_subset_closedBall (d := d)
              (badAnnulusOne_subset_sphereOneControl (d := d) n hx1)
          have : x ∈ Metric.closedBall (0 : E) (9 / 4 : ℝ) := by
            rw [Metric.mem_closedBall, dist_zero_right] at hxK' ⊢
            linarith
          exact hxK this
        · exact hxK (sphereTwoControl_subset_closedBall (d := d)
            (badAnnulusTwo_subset_sphereTwoControl (d := d) n hx2))
      have hEq :=
        fderiv_smoothUnitBallExtensionApprox_eq_exactUnitBallExtensionGradApply_of_not_mem_badSet
          (d := d) (ψ := ψ) (n := n) (i := i) hx1 hx2 hx1L hx1R hx2L hx2R hbad
      simp [hEq]
  have hH_nonneg : ∀ x, 0 ≤ H x := by
    intro x
    unfold H K
    by_cases hxK : x ∈ Metric.closedBall (0 : E) (9 / 4 : ℝ)
    · simp [Set.indicator, hxK]; exact le_trans hC1_nonneg (le_max_left _ _)
    · simp [Set.indicator, hxK]
  exact MemLp.of_le hH_memLp hF_meas <|
    hF_dom.mono fun x hx => by
      simpa [abs_of_nonneg (hH_nonneg x)] using hx

/-!
This block smooths the explicit unit-ball extension on smooth compactly
supported inputs by blending across shrinking annuli around `‖x‖ = 1` and
`‖x‖ = 2`. It provides the final analytic bridge needed to upgrade the explicit
extension operator to a full `W^{1,p}` witness on rough data.
-/

theorem hasWeakPartials_of_global_smoothApprox
    {p : ℝ} (hp : 1 < p)
    {v : E → ℝ} {G : E → E} {Φ : ℕ → E → ℝ}
    (hv_memLp : MemLp v (ENNReal.ofReal p) volume)
    (hG_memLp : ∀ i : Fin d, MemLp (fun x => G x i) (ENNReal.ofReal p) volume)
    (hΦ_smooth : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (Φ n))
    (hΦ_cpt : ∀ n, HasCompactSupport (Φ n))
    (hΦ_fun :
      Tendsto
        (fun n => eLpNorm (fun x => Φ n x - v x) (ENNReal.ofReal p) volume)
        atTop (nhds 0))
    (hΦ_grad :
      ∀ i : Fin d,
        Tendsto
          (fun n =>
            eLpNorm
              (fun x => (fderiv ℝ (Φ n) x) (EuclideanSpace.single i 1) - G x i)
              (ENNReal.ofReal p) volume)
          atTop (nhds 0)) :
    ∀ i : Fin d, HasWeakPartialDeriv i (fun x => G x i) v Set.univ := by
  let _ := (inferInstance : NeZero d)
  intro i
  have hΦ_wd : ∀ n, HasWeakPartialDeriv i
      (fun x => (fderiv ℝ (Φ n) x) (EuclideanSpace.single i 1)) (Φ n) Set.univ := by
    intro n
    simpa using (HasWeakPartialDeriv.of_contDiff (Ω := Set.univ) (i := i) (f := Φ n)
      isOpen_univ ((hΦ_smooth n).of_le (by simp)))
  have hΦ_fun_memLp : ∀ n, MemLp (fun x => Φ n x - v x) (ENNReal.ofReal p) volume := by
    intro n
    exact ((hΦ_smooth n).continuous.memLp_of_hasCompactSupport (hΦ_cpt n)).sub hv_memLp
  have hΦ_grad_memLp : ∀ n,
      MemLp (fun x => (fderiv ℝ (Φ n) x) (EuclideanSpace.single i 1) - G x i)
        (ENNReal.ofReal p) volume := by
    intro n
    have hderiv_smooth : ContDiff ℝ (⊤ : ℕ∞)
        (fun x => (fderiv ℝ (Φ n) x) (EuclideanSpace.single i 1)) :=
      (hΦ_smooth n).fderiv_right (m := (⊤ : ℕ∞)) (by simp) |>.clm_apply contDiff_const
    exact (hderiv_smooth.continuous.memLp_of_hasCompactSupport
      ((hΦ_cpt n).fderiv_apply (𝕜 := ℝ) _)).sub (hG_memLp i)
  exact HasWeakPartialDeriv.of_eLpNormApprox_p (d := d) (Ω := Set.univ) isOpen_univ hp
    (by simpa using hv_memLp) (by simpa using hG_memLp i)
    hΦ_wd (fun n => by simpa using hΦ_fun_memLp n) (by simpa using hΦ_fun)
    (fun n => by simpa using hΦ_grad_memLp n) (by simpa using hΦ_grad i)

omit [NeZero d] in
private lemma differentiableAt_unitBallExtension_of_smooth
    {ψ : E → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) {x : E}
    (hx1 : x ∉ Metric.sphere (0 : E) 1) (hx2 : x ∉ Metric.sphere (0 : E) 2) :
    DifferentiableAt ℝ (unitBallExtension (d := d) ψ) x := by
  by_cases hlt1 : ‖x‖ < 1
  · -- Inside ball: unitBallExtension ψ =ᶠ ψ
    have hEq : unitBallExtension (d := d) ψ =ᶠ[𝓝 x] ψ :=
      Filter.eventuallyEq_iff_exists_mem.mpr ⟨Metric.ball (0 : E) 1,
        Metric.isOpen_ball.mem_nhds (by simpa [Metric.mem_ball, dist_zero_right]),
        fun y hy => unitBallExtension_eq_of_mem_ball (d := d) hy⟩
    exact (Filter.EventuallyEq.differentiableAt_iff hEq).mpr
      ((hψ.differentiable (by simp)).differentiableAt)
  · by_cases hlt2 : ‖x‖ < 2
    · -- Annulus: unitBallExtension ψ =ᶠ shellFormula
      have hgt1 : 1 < ‖x‖ := lt_of_le_of_ne (not_lt.mp hlt1)
        (by simpa [Metric.mem_sphere, dist_zero_right, eq_comm] using hx1)
      have hxOuter : x ∈ unitBallOuterShell (d := d) := ⟨hgt1, hlt2⟩
      have hEq : unitBallExtension (d := d) ψ =ᶠ[𝓝 x] unitBallShellFormula (d := d) ψ :=
        Filter.eventuallyEq_iff_exists_mem.mpr ⟨unitBallOuterShell (d := d),
          (isOpen_unitBallOuterShell (d := d)).mem_nhds hxOuter,
          fun y hy => unitBallExtension_eq_shellFormula_of_mem_outerShell (d := d) hy⟩
      exact (Filter.EventuallyEq.differentiableAt_iff hEq).mpr
        (((contDiffOn_unitBallShellFormula (d := d) (hψ.of_le (by simp))).differentiableOn
          (by simp)).differentiableAt
            ((isOpen_unitBallOuterShell (d := d)).mem_nhds hxOuter))
    · -- Outside: unitBallExtension ψ =ᶠ 0
      have hgt2 : 2 < ‖x‖ := lt_of_le_of_ne (not_lt.mp hlt2)
        (by simpa [Metric.mem_sphere, dist_zero_right, eq_comm] using hx2)
      have hEq : unitBallExtension (d := d) ψ =ᶠ[𝓝 x] fun _ => (0 : ℝ) :=
        Filter.eventuallyEq_iff_exists_mem.mpr ⟨{y | 2 < ‖y‖},
          (isOpen_lt continuous_const continuous_norm).mem_nhds hgt2,
          fun y hy => unitBallExtension_eq_zero_of_two_le_norm (d := d) (le_of_lt hy)⟩
      exact (Filter.EventuallyEq.differentiableAt_iff hEq).mpr (differentiableAt_const 0)

private lemma ae_eq_exactUnitBallExtensionGrad_sub
    {u v : E → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u) (hv : ContDiff ℝ (⊤ : ℕ∞) v) :
    exactUnitBallExtensionGrad (d := d) (fun x => u x - v x) =ᵐ[volume]
      (fun x => exactUnitBallExtensionGrad (d := d) u x - exactUnitBallExtensionGrad (d := d) v x) := by
  have hae1 : ∀ᵐ x ∂(volume : Measure E), x ∉ Metric.sphere (0 : E) 1 := by
    rw [ae_iff]
    simpa [Metric.sphere, dist_zero_right] using
      Measure.addHaar_sphere (μ := (volume : Measure E)) (x := (0 : E)) 1
  have hae2 : ∀ᵐ x ∂(volume : Measure E), x ∉ Metric.sphere (0 : E) 2 := by
    rw [ae_iff]
    simpa [Metric.sphere, dist_zero_right] using
      Measure.addHaar_sphere (μ := (volume : Measure E)) (x := (0 : E)) 2
  have hae_sub :
      exactUnitBallExtensionGrad (d := d) (fun x => u x - v x) =ᵐ[volume]
        smoothUnitBallExtensionGrad (d := d) (fun x => u x - v x) := by
    simpa [exactUnitBallExtensionGrad] using
      (ae_eq_exactUnitBallExtensionGrad (d := d) (ψ := fun x => u x - v x))
  have hae_u :
      exactUnitBallExtensionGrad (d := d) u =ᵐ[volume]
        smoothUnitBallExtensionGrad (d := d) u := by
    simpa [exactUnitBallExtensionGrad] using
      (ae_eq_exactUnitBallExtensionGrad (d := d) (ψ := u))
  have hae_v :
      exactUnitBallExtensionGrad (d := d) v =ᵐ[volume]
        smoothUnitBallExtensionGrad (d := d) v := by
    simpa [exactUnitBallExtensionGrad] using
      (ae_eq_exactUnitBallExtensionGrad (d := d) (ψ := v))
  filter_upwards
      [hae_sub, hae_u, hae_v, hae1, hae2] with x huv hux hvx hx1 hx2
  rw [huv, hux, hvx]
  -- Goal: smoothGrad(u-v) x = smoothGrad(u) x - smoothGrad(v) x
  have hdu := differentiableAt_unitBallExtension_of_smooth (d := d) hu hx1 hx2
  have hdv := differentiableAt_unitBallExtension_of_smooth (d := d) hv hx1 hx2
  ext i
  simp only [smoothUnitBallExtensionGrad, PiLp.toLp_apply, unitBallExtension_sub]
  exact congrArg (· (EuclideanSpace.single i 1)) (fderiv_sub hdu hdv)

set_option maxHeartbeats 1600000 in
theorem exactUnitBallExtensionGrad_bound
    {p : ℝ} (hp : 1 < p) {ψ : E → ℝ}
    (hψ_smooth : ContDiff ℝ (⊤ : ℕ∞) ψ) :
    (∫⁻ x, (ENNReal.ofReal ‖exactUnitBallExtensionGrad (d := d) ψ x‖) ^ p ∂volume)
      ≤ (∫⁻ x in Metric.ball (0 : E) 1, (ENNReal.ofReal ‖fderiv ℝ ψ x‖) ^ p ∂volume) +
          C_unitBallExtensionGrad d p *
            (∫⁻ x in Metric.ball (0 : E) 1, (ENNReal.ofReal |ψ x|) ^ p ∂volume +
             ∫⁻ x in Metric.ball (0 : E) 1, (ENNReal.ofReal ‖fderiv ℝ ψ x‖) ^ p ∂volume) := by
  have hψ_smooth1 : ContDiff ℝ 1 ψ := hψ_smooth.of_le (by simp)
  have hest := smooth_unitBallExtension_W1p_estimate (d := d) (p := p) hp.le hψ_smooth1
  have hgrad_ae :
      exactUnitBallExtensionGrad (d := d) ψ =ᵐ[volume]
        smoothUnitBallExtensionGrad (d := d) ψ := by
    simpa [exactUnitBallExtensionGrad] using
      (ae_eq_exactUnitBallExtensionGrad (d := d) (ψ := ψ))
  have hgrad_norm_ae :
      (fun x => (ENNReal.ofReal ‖exactUnitBallExtensionGrad (d := d) ψ x‖) ^ p) =ᵐ[volume]
        (fun x =>
          (ENNReal.ofReal ‖fderiv ℝ (unitBallExtension (d := d) ψ) x‖) ^ p) := by
    filter_upwards [hgrad_ae] with x hx
    -- hx : exactUnitBallExtensionGrad ψ x = smoothUnitBallExtensionGrad ψ x
    -- Goal: ‖exactGrad ψ x‖ = ‖fderiv (unitBallExtension ψ) x‖
    -- smoothGrad uses fderiv, and norm_fderiv_eq_norm_partials_local converts
    congr 1
    rw [hx, smoothUnitBallExtensionGrad, norm_fderiv_eq_norm_partials_local (d := d)]
  have hs2 : volume (Metric.sphere (0 : E) 2) = 0 := by
    simpa using (Measure.addHaar_sphere (μ := (volume : Measure E)) (x := (0 : E)) 2)
  have hderiv_support_ae :
      (fun x => (ENNReal.ofReal ‖fderiv ℝ (unitBallExtension (d := d) ψ) x‖) ^ p) =ᵐ[volume]
        (Metric.ball (0 : E) 2).indicator
          (fun x => (ENNReal.ofReal ‖fderiv ℝ (unitBallExtension (d := d) ψ) x‖) ^ p) := by
    have hae2 : ∀ᵐ x ∂(volume : Measure E), x ∉ Metric.sphere (0 : E) 2 := by
      rw [ae_iff]; simpa [Metric.sphere, dist_zero_right] using hs2
    filter_upwards [hae2] with x hx
    by_cases hball : x ∈ Metric.ball (0 : E) 2
    · simp [hball]
    · have hnorm : 2 ≤ ‖x‖ := by
        rw [Metric.mem_ball, dist_zero_right] at hball
        linarith
      have hgt2 : 2 < ‖x‖ := by
        exact lt_of_le_of_ne hnorm (fun hEq =>
          hx (by rw [Metric.mem_sphere, dist_zero_right]; exact hEq.symm))
      have hzero :
          fderiv ℝ (unitBallExtension (d := d) ψ) x = 0 := by
        simpa using fderiv_unitBallExtension_eq_zero_of_norm_gt_two (d := d) (ψ := ψ) hgt2
      simp [Set.indicator, hball, hzero, ENNReal.zero_rpow_of_pos (by positivity : (0 : ℝ) < p)]
  calc
    ∫⁻ x, (ENNReal.ofReal ‖exactUnitBallExtensionGrad (d := d) ψ x‖) ^ p ∂volume
        = ∫⁻ x, (ENNReal.ofReal ‖fderiv ℝ (unitBallExtension (d := d) ψ) x‖) ^ p ∂volume := by
            exact lintegral_congr_ae hgrad_norm_ae
    _ = ∫⁻ x, (Metric.ball (0 : E) 2).indicator
          (fun x => (ENNReal.ofReal ‖fderiv ℝ (unitBallExtension (d := d) ψ) x‖) ^ p) x
          ∂volume := by
          exact lintegral_congr_ae hderiv_support_ae
    _ = ∫⁻ x in Metric.ball (0 : E) 2,
          (ENNReal.ofReal ‖fderiv ℝ (unitBallExtension (d := d) ψ) x‖) ^ p ∂volume := by
          rw [lintegral_indicator Metric.isOpen_ball.measurableSet]
    _ ≤ (∫⁻ x in Metric.ball (0 : E) 1, (ENNReal.ofReal ‖fderiv ℝ ψ x‖) ^ p ∂volume) +
          C_unitBallExtensionGrad d p *
            (∫⁻ x in Metric.ball (0 : E) 1, (ENNReal.ofReal |ψ x|) ^ p ∂volume +
             ∫⁻ x in Metric.ball (0 : E) 1, (ENNReal.ofReal ‖fderiv ℝ ψ x‖) ^ p ∂volume) := by
          simpa [C_unitBallExtensionGrad] using hest.2


/-- Smooth-input interface smoothing for the explicit extension operator.

For smooth compactly supported input `ψ`, the piecewise extension
`unitBallExtension ψ` can itself be approximated globally in full `W^{1,p}` by
smooth compactly supported functions. The gradient side is expressed against
some global field `Gψ` attached to the exact extension.

The surrounding rough-data extension theorem follows from this together with the
already available unit-ball approximation theorem.
-/
theorem smooth_input_unitBallExtension_smoothing
    {p : ℝ} (hp : 1 < p) {ψ : E → ℝ}
    (hψ_smooth : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (_hψ_cpt : HasCompactSupport ψ) :
    ∃ Gψ : E → E,
      MemLp (unitBallExtension (d := d) ψ) (ENNReal.ofReal p) volume ∧
      (∀ i : Fin d, MemLp (fun x => Gψ x i) (ENNReal.ofReal p) volume) ∧
      (∫⁻ x, (ENNReal.ofReal |unitBallExtension (d := d) ψ x|) ^ p ∂volume)
        ≤ C_unitBallExtensionFun d *
          ∫⁻ x in Metric.ball (0 : E) 1, (ENNReal.ofReal |ψ x|) ^ p ∂volume ∧
      (∫⁻ x, (ENNReal.ofReal ‖Gψ x‖) ^ p ∂volume)
        ≤ (∫⁻ x in Metric.ball (0 : E) 1, (ENNReal.ofReal ‖fderiv ℝ ψ x‖) ^ p ∂volume) +
          C_unitBallExtensionGrad d p *
            (∫⁻ x in Metric.ball (0 : E) 1, (ENNReal.ofReal |ψ x|) ^ p ∂volume +
             ∫⁻ x in Metric.ball (0 : E) 1, (ENNReal.ofReal ‖fderiv ℝ ψ x‖) ^ p ∂volume) ∧
      ∃ Φ : ℕ → E → ℝ,
        (∀ n, ContDiff ℝ (⊤ : ℕ∞) (Φ n)) ∧
        (∀ n, HasCompactSupport (Φ n)) ∧
        Tendsto
          (fun n =>
            eLpNorm (fun x => Φ n x - unitBallExtension (d := d) ψ x)
              (ENNReal.ofReal p) volume)
          atTop (nhds 0) ∧
        ∀ i : Fin d,
          Tendsto
            (fun n =>
              eLpNorm
                (fun x => (fderiv ℝ (Φ n) x) (EuclideanSpace.single i 1) - Gψ x i)
                (ENNReal.ofReal p) volume)
            atTop (nhds 0) := by
  have hΦ_smooth : ∀ n, ContDiff ℝ (⊤ : ℕ∞)
      (smoothUnitBallExtensionApprox (d := d) (unitBallApproxEps n) ψ) :=
    fun n => smoothUnitBallExtensionApprox_contDiff (d := d) (unitBallApproxEps_pos n)
      (unitBallApproxEps_lt_one n) hψ_smooth
  have hΦ_cpt : ∀ n, HasCompactSupport
      (smoothUnitBallExtensionApprox (d := d) (unitBallApproxEps n) ψ) :=
    fun n => smoothUnitBallExtensionApprox_hasCompactSupport (d := d) (ψ := ψ)
      (unitBallApproxEps_pos n)
  have huExt_memLp : MemLp (unitBallExtension (d := d) ψ) (ENNReal.ofReal p) volume := by
    have hΦ0_memLp : MemLp (smoothUnitBallExtensionApprox (d := d) (unitBallApproxEps 0) ψ)
        (ENNReal.ofReal p) (volume : Measure E) :=
      (hΦ_smooth 0).continuous.memLp_of_hasCompactSupport (hΦ_cpt 0)
    have hDiff_memLp :=
      memLp_smoothUnitBallExtensionApprox_sub_unitBallExtension (d := d) hp hψ_smooth 0
    have hTmp := hΦ0_memLp.sub hDiff_memLp
    exact memLp_congr_ae (Filter.Eventually.of_forall fun x => by simp [sub_sub_cancel]) |>.mp hTmp
  have hGψ_memLp : ∀ i : Fin d,
      MemLp (fun x => (exactUnitBallExtensionGrad (d := d) ψ x) i)
        (ENNReal.ofReal p) volume := by
    intro i
    have hderiv_memLp :
        MemLp
          (fun x => (fderiv ℝ (smoothUnitBallExtensionApprox (d := d) (unitBallApproxEps 0) ψ) x)
            (EuclideanSpace.single i 1))
          (ENNReal.ofReal p) volume := by
      have hderiv_smooth :
          ContDiff ℝ (⊤ : ℕ∞)
            (fun x => (fderiv ℝ (smoothUnitBallExtensionApprox (d := d) (unitBallApproxEps 0) ψ) x)
              (EuclideanSpace.single i 1)) :=
        (hΦ_smooth 0).fderiv_right (m := (⊤ : ℕ∞)) (by simp)
          |>.clm_apply contDiff_const
      exact hderiv_smooth.continuous.memLp_of_hasCompactSupport
        ((hΦ_cpt 0).fderiv_apply (𝕜 := ℝ) _)
    have hDiff_memLp :=
      memLp_fderiv_smoothUnitBallExtensionApprox_sub_exactGradApply (d := d) hp hψ_smooth 0 i
    have hTmp := hderiv_memLp.sub hDiff_memLp
    exact memLp_congr_ae (Filter.Eventually.of_forall fun x => by
      simp [sub_sub_cancel, exactUnitBallExtensionGrad,
        SmoothApproximationInternal.exactUnitBallExtensionGrad, exactUnitBallExtensionGradApply])
      |>.mp hTmp
  have hweak :
      ∀ i : Fin d, HasWeakPartialDeriv i
        (fun x => (exactUnitBallExtensionGrad (d := d) ψ x) i)
        (unitBallExtension (d := d) ψ) Set.univ := by
    have hΦ_tendsto_fun :=
      tendsto_eLpNorm_smoothUnitBallExtensionApprox_sub_unitBallExtension (d := d) hp hψ_smooth
    have hΦ_tendsto_grad :=
      tendsto_eLpNorm_fderiv_smoothUnitBallExtensionApprox_sub_exactGradApply (d := d) hp hψ_smooth
    exact hasWeakPartials_of_global_smoothApprox (d := d) hp huExt_memLp hGψ_memLp
      hΦ_smooth hΦ_cpt hΦ_tendsto_fun (fun i => by
        convert hΦ_tendsto_grad i using 2)
  let hwExt : MemW1pWitness (ENNReal.ofReal p)
      (unitBallExtension (d := d) ψ) Set.univ :=
    { memLp := by rw [Measure.restrict_univ]; exact huExt_memLp
      weakGrad := exactUnitBallExtensionGrad (d := d) ψ
      weakGrad_component_memLp := by
        intro i; rw [Measure.restrict_univ]; exact hGψ_memLp i
      isWeakGrad := hweak }
  rcases exists_global_smooth_W1p_approx_of_localizedWitness
      (d := d) (Ω := Set.univ) isOpen_univ hp hwExt
      (unitBallExtension_hasCompactSupport (d := d) ψ) (Set.subset_univ _) with
    ⟨Ψ, hΨ_smooth, hΨ_cpt, hΨ_fun, hΨ_grad⟩
  have hψ_smooth1 : ContDiff ℝ 1 ψ := hψ_smooth.of_le (by simp)
  have hest := smooth_unitBallExtension_W1p_estimate (d := d) (p := p) hp.le hψ_smooth1
  have hfun_bound :
      (∫⁻ x, (ENNReal.ofReal |unitBallExtension (d := d) ψ x|) ^ p ∂volume)
        ≤ C_unitBallExtensionFun d *
          ∫⁻ x in Metric.ball (0 : E) 1, (ENNReal.ofReal |ψ x|) ^ p ∂volume := by
    have hfun_support :
        (fun x => (ENNReal.ofReal |unitBallExtension (d := d) ψ x|) ^ p) =
          (Metric.ball (0 : E) 2).indicator
            (fun x => (ENNReal.ofReal |unitBallExtension (d := d) ψ x|) ^ p) := by
      funext x
      by_cases hx : x ∈ Metric.ball (0 : E) 2
      · simp [hx]
      · have hnorm : 2 ≤ ‖x‖ := by
          simp only [Metric.mem_ball, dist_zero_right, not_lt] at hx; exact hx
        have hzero := unitBallExtension_eq_zero_of_two_le_norm (d := d) (u := ψ) hnorm
        simp only [hzero, abs_zero, ENNReal.ofReal_zero, Set.indicator_of_notMem hx,
          ENNReal.zero_rpow_of_pos (show (0 : ℝ) < p by linarith)]
    rw [hfun_support, lintegral_indicator Metric.isOpen_ball.measurableSet]
    exact hest.1
  have hgrad_bound := exactUnitBallExtensionGrad_bound (d := d) hp hψ_smooth
  refine ⟨exactUnitBallExtensionGrad (d := d) ψ,
    huExt_memLp, hGψ_memLp, hfun_bound, hgrad_bound,
    Ψ, hΨ_smooth, hΨ_cpt, hΨ_fun, ?_⟩
  intro i
  have h := hΨ_grad i
  refine (Filter.tendsto_congr fun n => eLpNorm_congr_ae ?_).mpr h
  filter_upwards with x; simp [hwExt]


omit [NeZero d] in
set_option maxHeartbeats 800000 in
/-- Lintegral component bound: ∫ |F · i|^p ≤ ∫ ‖F‖^p. Uses lintegral_mono. -/
theorem lintegral_rpow_abs_component_le_lintegral_rpow_norm
    {p : ℝ} (hp : 0 < p) {F : E → E} (i : Fin d) {μ : Measure E} :
    ∫⁻ x, (ENNReal.ofReal |F x i|) ^ p ∂μ ≤
      ∫⁻ x, (ENNReal.ofReal ‖F x‖) ^ p ∂μ := by
  apply lintegral_mono
  intro x
  apply ENNReal.rpow_le_rpow _ hp.le
  exact ENNReal.ofReal_le_ofReal (by
    simpa using PiLp.norm_apply_le (p := (2 : ℝ≥0∞)) (x := F x) (i := i))

/-- Component Cauchy bound for weak gradients of smooth extensions.
Uses HasWeakPartialDeriv.ae_eq + lintegral_rpow_abs_component_le. -/
theorem weakGrad_component_cauchy_bound
    {p : ℝ} (hp : 1 < p)
    {ψ₁ ψ₂ : E → ℝ}
    (_hψ₁_smooth : ContDiff ℝ (⊤ : ℕ∞) ψ₁) (_hψ₂_smooth : ContDiff ℝ (⊤ : ℕ∞) ψ₂)
    (_hψ₁_cpt : HasCompactSupport ψ₁) (_hψ₂_cpt : HasCompactSupport ψ₂)
    {G₁ G₂ : E → E} {i : Fin d}
    (_hG₁_wd : HasWeakPartialDeriv i (fun x => G₁ x i)
        (unitBallExtension (d := d) ψ₁) Set.univ)
    (_hG₂_wd : HasWeakPartialDeriv i (fun x => G₂ x i)
        (unitBallExtension (d := d) ψ₂) Set.univ)
    (_hG₁_memLp : MemLp (fun x => G₁ x i) (ENNReal.ofReal p) volume)
    (_hG₂_memLp : MemLp (fun x => G₂ x i) (ENNReal.ofReal p) volume) :
    ∫⁻ x, (ENNReal.ofReal |G₁ x i - G₂ x i|) ^ p ∂volume ≤
      ∫⁻ x, (ENNReal.ofReal ‖exactUnitBallExtensionGrad (d := d) (fun x => ψ₁ x - ψ₂ x) x‖) ^ p
        ∂volume := by
  set ψ : E → ℝ := fun x => ψ₁ x - ψ₂ x with hψ_def
  have hψ_smooth : ContDiff ℝ (⊤ : ℕ∞) ψ := _hψ₁_smooth.sub _hψ₂_smooth
  have hp_enn : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    simpa using ENNReal.ofReal_le_ofReal hp.le
  have hGdiff_wd : HasWeakPartialDeriv i (fun x => G₁ x i - G₂ x i)
      (unitBallExtension (d := d) ψ) Set.univ := by
    intro φ hφ hφ_supp hφ_tsupport
    have h1 := _hG₁_wd φ hφ hφ_supp hφ_tsupport
    have h2 := _hG₂_wd φ hφ hφ_supp hφ_tsupport
    let ei : E := EuclideanSpace.single i (1 : ℝ)
    have hderiv_cont : Continuous (fun x => (fderiv ℝ φ x) ei) :=
      (hφ.continuous_fderiv (by simp : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0)).clm_apply
        continuous_const
    have hderiv_supp : HasCompactSupport (fun x => (fderiv ℝ φ x) ei) :=
      hφ_supp.fderiv_apply (𝕜 := ℝ) ei
    have hG₁_loc : LocallyIntegrable (fun x => G₁ x i) (volume.restrict Set.univ) := by
      rw [Measure.restrict_univ]; exact _hG₁_memLp.locallyIntegrable hp_enn
    have hG₂_loc : LocallyIntegrable (fun x => G₂ x i) (volume.restrict Set.univ) := by
      rw [Measure.restrict_univ]; exact _hG₂_memLp.locallyIntegrable hp_enn
    have hG₁_int : Integrable (fun x => G₁ x i * φ x) (volume.restrict Set.univ) := by
      simpa [smul_eq_mul] using
        hG₁_loc.integrable_smul_right_of_hasCompactSupport hφ.continuous hφ_supp
    have hG₂_int : Integrable (fun x => G₂ x i * φ x) (volume.restrict Set.univ) := by
      simpa [smul_eq_mul] using
        hG₂_loc.integrable_smul_right_of_hasCompactSupport hφ.continuous hφ_supp
    have hLHS : ∀ x, unitBallExtension (d := d) ψ x * (fderiv ℝ φ x) ei =
        unitBallExtension (d := d) ψ₁ x * (fderiv ℝ φ x) ei -
        unitBallExtension (d := d) ψ₂ x * (fderiv ℝ φ x) ei := by
      intro x; simp only [hψ_def, unitBallExtension_sub (d := d) ψ₁ ψ₂]; ring
    have hψ₁_memLp : MemLp (unitBallExtension (d := d) ψ₁) (ENNReal.ofReal p) volume := by
      rcases smooth_input_unitBallExtension_smoothing (d := d) hp _hψ₁_smooth _hψ₁_cpt with
        ⟨_, hml, _⟩; exact hml
    have hψ₂_memLp : MemLp (unitBallExtension (d := d) ψ₂) (ENNReal.ofReal p) volume := by
      rcases smooth_input_unitBallExtension_smoothing (d := d) hp _hψ₂_smooth _hψ₂_cpt with
        ⟨_, hml, _⟩; exact hml
    have hψ₁_loc : LocallyIntegrable (unitBallExtension (d := d) ψ₁)
        (volume.restrict Set.univ) := by
      rw [Measure.restrict_univ]; exact hψ₁_memLp.locallyIntegrable hp_enn
    have hψ₂_loc : LocallyIntegrable (unitBallExtension (d := d) ψ₂)
        (volume.restrict Set.univ) := by
      rw [Measure.restrict_univ]; exact hψ₂_memLp.locallyIntegrable hp_enn
    have hψ₁_int : Integrable (fun x => unitBallExtension (d := d) ψ₁ x * (fderiv ℝ φ x) ei)
        (volume.restrict Set.univ) := by
      simpa [smul_eq_mul, mul_comm] using
        hψ₁_loc.integrable_smul_right_of_hasCompactSupport hderiv_cont hderiv_supp
    have hψ₂_int : Integrable (fun x => unitBallExtension (d := d) ψ₂ x * (fderiv ℝ φ x) ei)
        (volume.restrict Set.univ) := by
      simpa [smul_eq_mul, mul_comm] using
        hψ₂_loc.integrable_smul_right_of_hasCompactSupport hderiv_cont hderiv_supp
    calc ∫ x in Set.univ,
          unitBallExtension (d := d) ψ x * (fderiv ℝ φ x) ei
        = ∫ x in Set.univ, (unitBallExtension (d := d) ψ₁ x * (fderiv ℝ φ x) ei -
            unitBallExtension (d := d) ψ₂ x * (fderiv ℝ φ x) ei) := by
          congr 1; ext x; exact hLHS x
      _ = (∫ x in Set.univ, unitBallExtension (d := d) ψ₁ x * (fderiv ℝ φ x) ei) -
          (∫ x in Set.univ, unitBallExtension (d := d) ψ₂ x * (fderiv ℝ φ x) ei) :=
          integral_sub hψ₁_int hψ₂_int
      _ = (-∫ x in Set.univ, G₁ x i * φ x) - (-∫ x in Set.univ, G₂ x i * φ x) := by
          rw [h1, h2]
      _ = -∫ x in Set.univ, (G₁ x i - G₂ x i) * φ x := by
          have hsub := (integral_sub hG₁_int hG₂_int).symm
          have hfun : (fun x => G₁ x i * φ x - G₂ x i * φ x) =
              (fun x => (G₁ x i - G₂ x i) * φ x) := by funext x; ring
          linarith [hsub, hfun ▸ hsub]
  have hΦ_smooth_ψ : ∀ n, ContDiff ℝ (⊤ : ℕ∞)
      (smoothUnitBallExtensionApprox (d := d) (unitBallApproxEps n) ψ) :=
    fun n => smoothUnitBallExtensionApprox_contDiff (d := d) (unitBallApproxEps_pos n)
      (unitBallApproxEps_lt_one n) hψ_smooth
  have hΦ_cpt_ψ : ∀ n, HasCompactSupport
      (smoothUnitBallExtensionApprox (d := d) (unitBallApproxEps n) ψ) :=
    fun n => smoothUnitBallExtensionApprox_hasCompactSupport (d := d) (ψ := ψ)
      (unitBallApproxEps_pos n)
  have hExt_memLp : MemLp (unitBallExtension (d := d) ψ) (ENNReal.ofReal p) volume := by
    have hΦ0_memLp : MemLp (smoothUnitBallExtensionApprox (d := d) (unitBallApproxEps 0) ψ)
        (ENNReal.ofReal p) (volume : Measure E) :=
      (hΦ_smooth_ψ 0).continuous.memLp_of_hasCompactSupport (hΦ_cpt_ψ 0)
    have hDiff_memLp :=
      memLp_smoothUnitBallExtensionApprox_sub_unitBallExtension (d := d) hp hψ_smooth 0
    exact memLp_congr_ae (Filter.Eventually.of_forall fun x => by
      simp [sub_sub_cancel]) |>.mp (hΦ0_memLp.sub hDiff_memLp)
  have hGψ_memLp : ∀ j : Fin d,
      MemLp (fun x => (exactUnitBallExtensionGrad (d := d) ψ x) j)
        (ENNReal.ofReal p) volume := by
    intro j
    have hderiv_memLp :
        MemLp (fun x => (fderiv ℝ (smoothUnitBallExtensionApprox (d := d)
            (unitBallApproxEps 0) ψ) x) (EuclideanSpace.single j 1))
          (ENNReal.ofReal p) volume := by
      exact ((hΦ_smooth_ψ 0).fderiv_right (m := (⊤ : ℕ∞)) (by simp)
        |>.clm_apply contDiff_const).continuous.memLp_of_hasCompactSupport
          ((hΦ_cpt_ψ 0).fderiv_apply (𝕜 := ℝ) _)
    have hDiff_memLp :=
      memLp_fderiv_smoothUnitBallExtensionApprox_sub_exactGradApply
        (d := d) hp hψ_smooth 0 j
    exact memLp_congr_ae (Filter.Eventually.of_forall fun x => by
      simp [sub_sub_cancel, exactUnitBallExtensionGrad,
        SmoothApproximationInternal.exactUnitBallExtensionGrad, exactUnitBallExtensionGradApply])
        |>.mp (hderiv_memLp.sub hDiff_memLp)
  have hExact_wd : HasWeakPartialDeriv i
      (fun x => (exactUnitBallExtensionGrad (d := d) ψ x) i)
      (unitBallExtension (d := d) ψ) Set.univ :=
    hasWeakPartials_of_global_smoothApprox (d := d) hp hExt_memLp hGψ_memLp
      hΦ_smooth_ψ hΦ_cpt_ψ
      (tendsto_eLpNorm_smoothUnitBallExtensionApprox_sub_unitBallExtension
        (d := d) hp hψ_smooth)
      (fun j => by
        convert tendsto_eLpNorm_fderiv_smoothUnitBallExtensionApprox_sub_exactGradApply
          (d := d) hp hψ_smooth j using 2) i
  have hGdiff_loc : LocallyIntegrable (fun x => G₁ x i - G₂ x i)
      (volume.restrict Set.univ) := by
    rw [Measure.restrict_univ]
    exact (_hG₁_memLp.sub _hG₂_memLp).locallyIntegrable hp_enn
  have hExact_loc : LocallyIntegrable
      (fun x => (exactUnitBallExtensionGrad (d := d) ψ x) i)
      (volume.restrict Set.univ) := by
    rw [Measure.restrict_univ]; exact (hGψ_memLp i).locallyIntegrable hp_enn
  have hae : (fun x => G₁ x i - G₂ x i) =ᵐ[volume.restrict Set.univ]
      (fun x => (exactUnitBallExtensionGrad (d := d) ψ x) i) :=
    HasWeakPartialDeriv.ae_eq isOpen_univ hGdiff_wd hExact_wd hGdiff_loc hExact_loc
  rw [Measure.restrict_univ] at hae
  calc ∫⁻ x, (ENNReal.ofReal |G₁ x i - G₂ x i|) ^ p ∂volume
      = ∫⁻ x, (ENNReal.ofReal |(exactUnitBallExtensionGrad (d := d) ψ x) i|) ^ p
          ∂volume := by
        apply lintegral_congr_ae
        filter_upwards [hae] with x hx; rw [hx]
    _ ≤ ∫⁻ x, (ENNReal.ofReal ‖exactUnitBallExtensionGrad (d := d) ψ x‖) ^ p
          ∂volume :=
        lintegral_rpow_abs_component_le_lintegral_rpow_norm (d := d) (by linarith) i



end DeGiorgi
