import DeGiorgi.MoserIteration.CutoffPrep.ExactRegularization

/-!
# Moser Regularized Witnesses

This module packages the regularized clipped positive-part, power-cutoff, and test-cutoff witnesses used in the Chapter 06 energy argument.
-/

noncomputable section

open MeasureTheory Filter

namespace DeGiorgi

variable {d : ℕ} [NeZero d]

local notation "E" => AmbientSpace d

/-- Regularized clipped positive-part witness. This isolates the witness
construction side of the Moser power-test argument from the remaining energy
estimate and limit passage. -/
noncomputable def moserRegClippedPosPartWitness
    {u : E → ℝ} {s ε N p : ℝ}
    (hs : 0 < s) (hs1 : s ≤ 1) (hε : 0 < ε) (hN : 0 ≤ N)
    (hu1 : MemW1pWitness 2 u (Metric.ball (0 : E) 1)) :
    MemW1pWitness 2
      (fun x => moserRegPow ε N p (min (max (u x) 0) N))
      (Metric.ball (0 : E) s) := by
  let hwClip :=
    moserClippedPosPartWitness (d := d) (u := u) (s := s) (N := N) hs hs1 hN hu1
  exact (MemW1pWitness.comp_smooth_bounded
    (d := d) Metric.isOpen_ball hwClip (moserRegPow ε N p)
    (moserRegPow_contDiff (ε := ε) (N := N) (p := p) hε hN)
    (moserRegPow_eq_zero_of_nonpos (ε := ε) (N := N) (p := p) hε hN (le_rfl : (0 : ℝ) ≤ 0))
    (moserRegPow_deriv_bounded (ε := ε) (N := N) (p := p) hε hN))

/-- Regularized powered cutoff witness. This packages the Chapter 06
regularization layer into the exact witness shape used by the pre-Moser
argument. The remaining gap is the quantitative energy estimate. -/
noncomputable def moserRegPowerCutoffWitness
    {u η : E → ℝ} {s ε N p Cη : ℝ}
    (hs : 0 < s) (hs1 : s ≤ 1) (hε : 0 < ε) (hN : 0 ≤ N)
    (hu1 : MemW1pWitness 2 u (Metric.ball (0 : E) 1))
    (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hη_bound : ∀ x, |η x| ≤ 1)
    (hη_grad_bound : ∀ x, ‖fderiv ℝ η x‖ ≤ Cη) :
    MemW1pWitness 2
      (fun x => η x * moserRegPow ε N p (min (max (u x) 0) N))
      (Metric.ball (0 : E) s) := by
  let hwReg :=
    moserRegClippedPosPartWitness (d := d) (u := u) (s := s) (ε := ε) (N := N) (p := p)
      hs hs1 hε hN hu1
  have hCη_nonneg : 0 ≤ Cη := by
    have := hη_grad_bound (0 : E)
    exact le_trans (norm_nonneg _) this
  exact hwReg.mul_smooth_bounded Metric.isOpen_ball hη
    (C₀ := 1) (C₁ := Cη) (by norm_num) hCη_nonneg hη_bound hη_grad_bound

noncomputable def moserRegTestCutoff
    (η u : E → ℝ) (ε N p : ℝ) : E → ℝ :=
  fun x => η x * (η x * moserRegTestPow ε N p (min (max (u x) 0) N))

noncomputable def moserRegTestCutoffWitness
    {u η : E → ℝ} {s ε N p Cη : ℝ}
    (hs : 0 < s) (hs1 : s ≤ 1) (hε : 0 < ε) (hN : 0 ≤ N)
    (hu1 : MemW1pWitness 2 u (Metric.ball (0 : E) 1))
    (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hη_bound : ∀ x, |η x| ≤ 1)
    (hη_grad_bound : ∀ x, ‖fderiv ℝ η x‖ ≤ Cη) :
    MemW1pWitness 2
      (moserRegTestCutoff η u ε N p)
      (Metric.ball (0 : E) s) := by
  let hwTest :
      MemW1pWitness 2
        (fun x => moserRegTestPow ε N p (min (max (u x) 0) N))
        (Metric.ball (0 : E) s) :=
    (MemW1pWitness.comp_smooth_bounded
      (d := d) Metric.isOpen_ball
      (moserClippedPosPartWitness (d := d) (u := u) (s := s) (N := N) hs hs1 hN hu1)
      (moserRegTestPow ε N p)
      (moserRegTestPow_contDiff (ε := ε) (N := N) (p := p) hε hN)
      (moserRegTestPow_eq_zero_of_nonpos (ε := ε) (N := N) (p := p) hε hN (le_rfl : (0 : ℝ) ≤ 0))
      (moserRegTestPow_deriv_bounded (ε := ε) (N := N) (p := p) hε hN))
  have hCη_nonneg : 0 ≤ Cη := by
    have := hη_grad_bound (0 : E)
    exact le_trans (norm_nonneg _) this
  let hwη :=
    hwTest.mul_smooth_bounded Metric.isOpen_ball hη
      (C₀ := 1) (C₁ := Cη) (by norm_num) hCη_nonneg hη_bound hη_grad_bound
  exact
    hwη.mul_smooth_bounded Metric.isOpen_ball hη
      (C₀ := 1) (C₁ := Cη) (by norm_num) hCη_nonneg hη_bound hη_grad_bound

/-- The `moserRegTestPow` is nonneg on nonneg inputs: since `smoothClip(t) ≥ 0` for `t ≥ 0`,
we have `(ε + smoothClip(t))^{p-1} ≥ ε^{p-1}`. -/
theorem moserRegTestPow_nonneg_of_nonneg
    {ε N p t : ℝ} (hε : 0 < ε) (hN : 0 ≤ N) (ht : 0 ≤ t) (hp : 1 < p) :
    0 ≤ moserRegTestPow ε N p t := by
  dsimp [moserRegTestPow]
  refine sub_nonneg.mpr ?_
  refine Real.rpow_le_rpow (by linarith) ?_ (by linarith)
  have hclip_nonneg : 0 ≤ moserSmoothClip ε N t := by
    -- moserSmoothClip ε N t = t · σ₀(t/ε) · σ₁(N+1-t) + N · (1 - σ₁(N+1-t))
    -- where σ₀, σ₁ ∈ [0,1]. For t ≥ 0: both terms are nonneg.
    dsimp [moserSmoothClip]
    have hσ₀ : 0 ≤ Real.smoothTransition (t / ε) := Real.smoothTransition.nonneg _
    have hσ₁ : 0 ≤ Real.smoothTransition (N + 1 - t) := Real.smoothTransition.nonneg _
    have hσ₁_le : Real.smoothTransition (N + 1 - t) ≤ 1 := Real.smoothTransition.le_one _
    have hterm1 : 0 ≤ t * Real.smoothTransition (t / ε) * Real.smoothTransition (N + 1 - t) := by
      positivity
    have hterm2 : 0 ≤ N * (1 - Real.smoothTransition (N + 1 - t)) := by
      exact mul_nonneg hN (by linarith)
    linarith
  linarith

omit [NeZero d] in
theorem moserRegTestCutoff_nonneg
    {u η : E → ℝ} {ε N p : ℝ}
    (hε : 0 < ε) (hN : 0 ≤ N) (hp : 1 < p) :
    ∀ x, 0 ≤ moserRegTestCutoff η u ε N p x := by
  intro x
  dsimp [moserRegTestCutoff]
  -- η x * (η x * f x) = η x ^ 2 * f x where f = moserRegTestPow ... ≥ 0
  have hf_nonneg : 0 ≤ moserRegTestPow ε N p (min (max (u x) 0) N) := by
    exact moserRegTestPow_nonneg_of_nonneg hε hN (le_min (le_max_right _ _) hN) hp
  have : η x * (η x * moserRegTestPow ε N p (min (max (u x) 0) N)) =
      η x ^ 2 * moserRegTestPow ε N p (min (max (u x) 0) N) := by ring
  rw [this]
  exact mul_nonneg (sq_nonneg _) hf_nonneg

omit [NeZero d] in
/-- The regularized Moser test function has tsupport ⊆ tsupport η ⊆ ball. -/
theorem moserRegTestCutoff_tsupport_subset
    {u η : E → ℝ} {ε N p s : ℝ}
    (hη_sub_ball : tsupport η ⊆ Metric.ball (0 : E) s) :
    tsupport (moserRegTestCutoff η u ε N p) ⊆ Metric.ball (0 : E) s := by
  exact (tsupport_mul_subset_left
    (f := η) (g := fun x => η x * moserRegTestPow ε N p (min (max (u x) 0) N))).trans
    hη_sub_ball

/-- The regularized Moser test function belongs to `H₀¹(B_s)`. -/
theorem moserRegTestCutoff_memH01
    {u η : E → ℝ} {s ε N p Cη : ℝ}
    (hs : 0 < s) (hs1 : s ≤ 1) (hε : 0 < ε) (hN : 0 ≤ N) (_hp : 1 < p)
    (hu1 : MemW1pWitness 2 u (Metric.ball (0 : E) 1))
    (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hη_bound : ∀ x, |η x| ≤ 1)
    (hη_grad_bound : ∀ x, ‖fderiv ℝ η x‖ ≤ Cη)
    (hη_sub_ball : tsupport η ⊆ Metric.ball (0 : E) s) :
    MemH01 (moserRegTestCutoff η u ε N p) (Metric.ball (0 : E) s) := by
  let hwTest := moserRegTestCutoffWitness (d := d) (p := p) hs hs1 hε hN hu1 hη hη_bound hη_grad_bound
  have hv_support : tsupport (moserRegTestCutoff η u ε N p) ⊆ Metric.ball (0 : E) s :=
    moserRegTestCutoff_tsupport_subset (d := d) hη_sub_ball
  have hv_compact : HasCompactSupport (moserRegTestCutoff η u ε N p) :=
    hasCompactSupport_of_tsupport_subset_ball hv_support
  have hv_memW01p : MemW01p (ENNReal.ofReal (2 : ℝ)) (moserRegTestCutoff η u ε N p)
      (Metric.ball (0 : E) s) :=
    memW01p_of_memW1p_of_tsupport_subset Metric.isOpen_ball (by norm_num : (1 : ℝ) < 2)
      (by simpa using hwTest.memW1p) hv_compact hv_support
  simpa using hv_memW01p

set_option maxHeartbeats 400000 in
/-- The gradient of `moserRegPowerCutoffWitness` decomposes as η · (chain rule) + (product rule).
This is the analogue of `deGiorgiCutoffTestWitnessWeighted_grad` from Chapter 05. -/
lemma moserRegPowerCutoffWitness_grad
    {u η : E → ℝ} {s ε N p Cη : ℝ}
    (hs : 0 < s) (hs1 : s ≤ 1) (hε : 0 < ε) (hN : 0 ≤ N)
    (hu1 : MemW1pWitness 2 u (Metric.ball (0 : E) 1))
    (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hη_bound : ∀ x, |η x| ≤ 1)
    (hη_grad_bound : ∀ x, ‖fderiv ℝ η x‖ ≤ Cη)
    (x : E) (i : Fin d) :
    (moserRegPowerCutoffWitness (d := d) (p := p)
      hs hs1 hε hN hu1 hη hη_bound hη_grad_bound).weakGrad x i =
      η x * (moserRegClippedPosPartWitness (d := d) (u := u) (p := p)
        hs hs1 hε hN hu1).weakGrad x i +
      (fderiv ℝ η x) (EuclideanSpace.single i 1) *
        moserRegPow ε N p (min (max (u x) 0) N) := by
  -- moserRegPowerCutoffWitness = hwComp.mul_smooth_bounded η
  -- mul_smooth_bounded.weakGrad x i = η x * hw.weakGrad x i + ∂ᵢη(x) * u(x)
  -- This is definitionally true by the construction.
  set_option maxHeartbeats 400000 in
  simp only [moserRegPowerCutoffWitness, MemW1pWitness.mul_smooth_bounded,
    moserRegClippedPosPartWitness, WithLp.ofLp_add, WithLp.ofLp_smul,
    smul_eq_mul, Pi.add_apply, Pi.smul_apply]


end DeGiorgi
