import DeGiorgi.PositivePart
import DeGiorgi.BallExtension
import DeGiorgi.WeakFormulation

/-!
# De Giorgi Iteration: Cutoff Admissibility

This module packages the truncation and cutoff-admissibility layer used at the
start of the De Giorgi iteration.
-/

noncomputable section

open MeasureTheory Metric Filter Topology Set Function Matrix
open scoped ENNReal NNReal

namespace DeGiorgi

/-- Positive-part truncation `(u-k)₊`. -/
def positivePartSub {α : Type*} (u : α → ℝ) (k : ℝ) : α → ℝ :=
  fun x => max (u x - k) 0

lemma positivePartSub_nonneg {α : Type*} {u : α → ℝ} {k : ℝ} {x : α} :
    0 ≤ positivePartSub u k x := by
  simp [positivePartSub]

lemma positivePartSub_sq_ge_gap_sq_of_lt
    {α : Type*} {u : α → ℝ} {θ lam : ℝ} {x : α}
    (hθl : θ < lam) (hxl : lam < u x) :
    (lam - θ) ^ 2 ≤ |positivePartSub u θ x| ^ 2 := by
  have hgap_pos : 0 < lam - θ := sub_pos.mpr hθl
  have hpos : 0 < u x - θ := by linarith
  have hle : lam - θ ≤ u x - θ := by linarith
  have hpp : positivePartSub u θ x = u x - θ := by
    simp [positivePartSub, max_eq_left (le_of_lt hpos)]
  rw [hpp, abs_of_nonneg (le_of_lt hpos)]
  nlinarith

section CutoffAdmissibility

variable {d : ℕ} [NeZero d]

local notation "E" => AmbientSpace d

/-- Generalized De Giorgi cutoff test `η² (u-k)₊` for an arbitrary scalar
cutoff `η`. -/
def deGiorgiCutoffTestGeneral
    (η u : E → ℝ) (k : ℝ) : E → ℝ :=
  fun x => η x * (η x * positivePartSub u k x)

omit [NeZero d] in
lemma eq_zero_of_not_mem_tsupport
    {f : E → ℝ} {x : E} (hx : x ∉ tsupport f) : f x = 0 := by
  by_contra hfx
  exact hx (subset_tsupport f (Function.mem_support.mpr hfx))

omit [NeZero d] in
lemma hasCompactSupport_of_tsupport_subset_ball
    {f : E → ℝ} {x₀ : E} {s : ℝ}
    (hsub : tsupport f ⊆ Metric.ball x₀ s) :
    HasCompactSupport f := by
  apply HasCompactSupport.intro' (isCompact_closedBall x₀ s) isClosed_closedBall
  intro x hx
  apply eq_zero_of_not_mem_tsupport
  intro hxt
  exact hx <| Metric.ball_subset_closedBall (hsub hxt)

omit [NeZero d] in
lemma deGiorgiCutoffTestGeneral_hasCompactSupport
    {η u : E → ℝ} {k : ℝ}
    (hη_comp : HasCompactSupport η) :
    HasCompactSupport (deGiorgiCutoffTestGeneral η u k) := by
  simpa [deGiorgiCutoffTestGeneral, smul_eq_mul] using
    hη_comp.smul_right (f' := fun x => η x * positivePartSub u k x)

omit [NeZero d] in
lemma deGiorgiCutoffTestGeneral_tsupport_subset
    {Ω : Set E} {η u : E → ℝ} {k : ℝ}
    (hη_sub : tsupport η ⊆ Ω) :
    tsupport (deGiorgiCutoffTestGeneral η u k) ⊆ Ω := by
  simpa [deGiorgiCutoffTestGeneral, smul_eq_mul] using
    (tsupport_smul_subset_left η (fun x => η x * positivePartSub u k x)).trans hη_sub

private noncomputable def positivePartSub_memW1pWitness
    {Ω : Set E} [IsFiniteMeasure (volume.restrict Ω)]
    (hΩ : IsOpen Ω) {u : E → ℝ}
    (hw : MemW1pWitness 2 u Ω) (k : ℝ)
    (happroxShift :
      ∃ ψ : ℕ → E → ℝ,
        (∀ n, ContDiff ℝ 1 (ψ n)) ∧
        (∀ n, HasCompactSupport (ψ n)) ∧
        Tendsto (fun n => eLpNorm (fun x => ψ n x - (u x - k)) 2 (volume.restrict Ω))
          atTop (nhds 0) ∧
        (∀ i : Fin d,
          Tendsto (fun n => eLpNorm (fun x =>
            (fderiv ℝ (ψ n) x) (EuclideanSpace.single i 1) - hw.weakGrad x i)
            2 (volume.restrict Ω))
          atTop (nhds 0))) :
    MemW1pWitness 2 (positivePartSub u k) Ω := by
  let hwShift : MemW1pWitness 2 (fun x => u x - k) Ω := hw.sub_const hΩ k
  simpa [positivePartSub] using (hwShift.posPart hΩ happroxShift)

theorem deGiorgiCutoffTest_memW01p_of_truncWitness
    {Ω : Set E} [IsFiniteMeasure (volume.restrict Ω)]
    (hΩ : IsOpen Ω)
    {u η : E → ℝ} {k : ℝ}
    (hw_trunc : MemW1pWitness 2 (positivePartSub u k) Ω)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    {C₀ C₁ : ℝ}
    (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁)
    (hη_bound : ∀ x, |η x| ≤ C₀)
    (hη_grad_bound : ∀ x, ‖fderiv ℝ η x‖ ≤ C₁)
    (hη_comp : HasCompactSupport η)
    (hη_sub : tsupport η ⊆ Ω) :
    MemW01p 2 (deGiorgiCutoffTestGeneral η u k) Ω := by
  let hwη :=
    hw_trunc.mul_smooth_bounded hΩ hη
      (C₀ := C₀) (C₁ := C₁) hC₀ hC₁ hη_bound hη_grad_bound
  let hwηθ : MemW1pWitness 2 (deGiorgiCutoffTestGeneral η u k) Ω :=
    hwη.mul_smooth_bounded hΩ hη
      (C₀ := C₀) (C₁ := C₁) hC₀ hC₁ hη_bound hη_grad_bound
  have hv_comp : HasCompactSupport (deGiorgiCutoffTestGeneral η u k) :=
    deGiorgiCutoffTestGeneral_hasCompactSupport hη_comp
  have hv_sub : tsupport (deGiorgiCutoffTestGeneral η u k) ⊆ Ω :=
    deGiorgiCutoffTestGeneral_tsupport_subset hη_sub
  have hwηθ_memW1p_real :
      MemW1p (ENNReal.ofReal 2) (deGiorgiCutoffTestGeneral η u k) Ω := by
    simpa using hwηθ.memW1p
  simpa using
    (memW01p_of_memW1p_of_tsupport_subset
      hΩ (by norm_num : (1 : ℝ) < 2) hwηθ_memW1p_real hv_comp hv_sub)

/-- General cutoff admissibility theorem, parameterized by a positive-part
witness theorem. This packages the reusable cutoff argument while keeping the
localization argument in
`memW01p_of_memW1p_of_tsupport_subset`. -/
theorem deGiorgiCutoffTest_memW01p_of_posPart
    {Ω : Set E} [IsFiniteMeasure (volume.restrict Ω)]
    (hΩ : IsOpen Ω)
    {u η : E → ℝ}
    (hw : MemW1pWitness 2 u Ω)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    {C₀ C₁ : ℝ}
    (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁)
    (hη_bound : ∀ x, |η x| ≤ C₀)
    (hη_grad_bound : ∀ x, ‖fderiv ℝ η x‖ ≤ C₁)
    (hη_comp : HasCompactSupport η)
    (hη_sub : tsupport η ⊆ Ω)
    (k : ℝ)
    (hpos :
      ∀ {v : E → ℝ},
        MemW1pWitness 2 v Ω →
          MemW1pWitness 2 (fun x => max (v x) 0) Ω) :
    MemW01p 2 (deGiorgiCutoffTestGeneral η u k) Ω := by
  let hwShift : MemW1pWitness 2 (fun x => u x - k) Ω := hw.sub_const hΩ k
  have hw_trunc : MemW1pWitness 2 (positivePartSub u k) Ω := by
    simpa [positivePartSub] using (hpos hwShift)
  exact
    deGiorgiCutoffTest_memW01p_of_truncWitness
      hΩ hw_trunc hη hC₀ hC₁ hη_bound hη_grad_bound hη_comp hη_sub

/-- Concrete cutoff admissibility theorem using the Chapter 02 positive-part
witness constructor and an explicit smooth-approximation package for `u - k`. -/
theorem deGiorgiCutoffTest_memW01p_of_posPartApprox
    {Ω : Set E} [IsFiniteMeasure (volume.restrict Ω)]
    (hΩ : IsOpen Ω)
    {u η : E → ℝ}
    (hw : MemW1pWitness 2 u Ω)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    {C₀ C₁ : ℝ}
    (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁)
    (hη_bound : ∀ x, |η x| ≤ C₀)
    (hη_grad_bound : ∀ x, ‖fderiv ℝ η x‖ ≤ C₁)
    (hη_comp : HasCompactSupport η)
    (hη_sub : tsupport η ⊆ Ω)
    (k : ℝ)
    (happroxShift :
      ∃ ψ : ℕ → E → ℝ,
        (∀ n, ContDiff ℝ 1 (ψ n)) ∧
        (∀ n, HasCompactSupport (ψ n)) ∧
        Tendsto (fun n => eLpNorm (fun x => ψ n x - (u x - k)) 2 (volume.restrict Ω))
          atTop (nhds 0) ∧
        (∀ i : Fin d,
          Tendsto (fun n => eLpNorm (fun x =>
            (fderiv ℝ (ψ n) x) (EuclideanSpace.single i 1) - hw.weakGrad x i)
            2 (volume.restrict Ω))
          atTop (nhds 0))) :
    MemW01p 2 (deGiorgiCutoffTestGeneral η u k) Ω := by
  let hw_trunc : MemW1pWitness 2 (positivePartSub u k) Ω :=
    positivePartSub_memW1pWitness hΩ hw k happroxShift
  exact
    deGiorgiCutoffTest_memW01p_of_truncWitness
      hΩ hw_trunc hη hC₀ hC₁ hη_bound hη_grad_bound hη_comp hη_sub

/-- Ball version of generalized cutoff admissibility. This avoids any
dependence on the legacy `Cutoff` structure. -/
theorem deGiorgiCutoffTest_memW01p_on_ball_of_ballPosPart
    {u η : E → ℝ} {x₀ : E} {s Cη : ℝ}
    (_hs : 0 < s)
    (hw : MemW1pWitness 2 u (Metric.ball x₀ s))
    (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hη_bound : ∀ x, |η x| ≤ 1)
    (hCη : 0 ≤ Cη)
    (hη_grad_bound : ∀ x, ‖fderiv ℝ η x‖ ≤ Cη)
    (hη_sub_ball : tsupport η ⊆ Metric.ball x₀ s)
    (k : ℝ)
    (hposBall :
      ∀ {v : E → ℝ},
        MemW1pWitness 2 v (Metric.ball x₀ s) →
          MemW1pWitness 2 (fun x => max (v x) 0) (Metric.ball x₀ s)) :
    MemW01p 2 (deGiorgiCutoffTestGeneral η u k) (Metric.ball x₀ s) := by
  haveI : IsFiniteMeasure (volume.restrict (Metric.ball x₀ s)) := by
    rw [isFiniteMeasure_restrict]
    exact measure_ball_lt_top.ne
  have hη_comp : HasCompactSupport η :=
    hasCompactSupport_of_tsupport_subset_ball hη_sub_ball
  exact
    deGiorgiCutoffTest_memW01p_of_posPart
      isOpen_ball hw hη (by norm_num) hCη hη_bound hη_grad_bound hη_comp
      hη_sub_ball k hposBall

/-- Ball version of cutoff admissibility driven by the concrete Chapter 02
positive-part witness constructor. -/
theorem deGiorgiCutoffTest_memW01p_on_ball_of_ballPosPartApprox
    {u η : E → ℝ} {x₀ : E} {s Cη : ℝ}
    (_hs : 0 < s)
    (hw : MemW1pWitness 2 u (Metric.ball x₀ s))
    (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hη_bound : ∀ x, |η x| ≤ 1)
    (hCη : 0 ≤ Cη)
    (hη_grad_bound : ∀ x, ‖fderiv ℝ η x‖ ≤ Cη)
    (hη_sub_ball : tsupport η ⊆ Metric.ball x₀ s)
    (k : ℝ)
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
                  (fderiv ℝ (ψ n) x) (EuclideanSpace.single i 1) - hw.weakGrad x i)
                2 (volume.restrict (Metric.ball x₀ s)))
            atTop (nhds 0))) :
    MemW01p 2 (deGiorgiCutoffTestGeneral η u k) (Metric.ball x₀ s) := by
  haveI : IsFiniteMeasure (volume.restrict (Metric.ball x₀ s)) := by
    rw [isFiniteMeasure_restrict]
    exact measure_ball_lt_top.ne
  have hη_comp : HasCompactSupport η :=
    hasCompactSupport_of_tsupport_subset_ball hη_sub_ball
  exact
    deGiorgiCutoffTest_memW01p_of_posPartApprox
      isOpen_ball hw hη (by norm_num) hCη hη_bound hη_grad_bound hη_comp
      hη_sub_ball k happroxBallShift

/-- Concrete truncation witness on a ball, obtained from the Chapter 02
positive-part constructor applied to `u - k`. -/
noncomputable def positivePartSub_memW1pWitness_on_ball
    {u : E → ℝ} {x₀ : E} {s : ℝ}
    (_hs : 0 < s)
    (hw : MemW1pWitness 2 u (Metric.ball x₀ s))
    (k : ℝ)
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
                  (fderiv ℝ (ψ n) x) (EuclideanSpace.single i 1) - hw.weakGrad x i)
                2 (volume.restrict (Metric.ball x₀ s)))
            atTop (nhds 0))) :
    MemW1pWitness 2 (positivePartSub u k) (Metric.ball x₀ s) := by
  have hΩ : IsOpen (Metric.ball x₀ s) := isOpen_ball
  haveI : IsFiniteMeasure (volume.restrict (Metric.ball x₀ s)) := by
    rw [isFiniteMeasure_restrict]
    exact measure_ball_lt_top.ne
  exact positivePartSub_memW1pWitness hΩ hw k happroxBallShift

end CutoffAdmissibility

end DeGiorgi
