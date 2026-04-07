import DeGiorgi.MoserIteration.CutoffPrep.Profiles

/-!
# Moser Exact Regularization

This module contains the exact-on-support witnesses, derivative identities, and epsilon-limit lemmas for the Chapter 06 regularization scheme.
-/

noncomputable section

open MeasureTheory Filter

namespace DeGiorgi

variable {d : ℕ} [NeZero d]

local notation "E" => AmbientSpace d

noncomputable def moserPosPartWitnessUnitBall
    {u : E → ℝ}
    (hu1 : MemW1pWitness 2 u (Metric.ball (0 : E) 1)) :
    MemW1pWitness 2 (fun x => max (u x) 0) (Metric.ball (0 : E) 1) := by
  let happrox0 :=
    moser_shiftApprox_on_ball_of_unitBall (d := d) (u := u) (s := (1 : ℝ)) (θ := 0)
      (by norm_num) (by norm_num) hu1
  let hw0 : MemW1pWitness 2 (positivePartSub u 0) (Metric.ball (0 : E) 1) :=
    positivePartSub_memW1pWitness_on_ball (d := d) (x₀ := (0 : E)) (s := (1 : ℝ))
      (by norm_num) hu1 0 happrox0
  have hEq : positivePartSub u 0 = fun x => max (u x) 0 := by
    funext x
    simp [positivePartSub]
  refine
    { memLp := by
        simpa [hEq] using hw0.memLp
      weakGrad := hw0.weakGrad
      weakGrad_component_memLp := hw0.weakGrad_component_memLp
      isWeakGrad := by
        simpa [hEq] using hw0.isWeakGrad }

lemma moserPosPartWitnessUnitBall_grad_eq_on_pos
    {u : E → ℝ}
    (hu1 : MemW1pWitness 2 u (Metric.ball (0 : E) 1)) :
    ∀ᵐ x ∂(volume.restrict (Metric.ball (0 : E) 1)),
      0 < u x →
        (moserPosPartWitnessUnitBall (d := d) (u := u) hu1).weakGrad x = hu1.weakGrad x := by
  haveI : IsFiniteMeasure (volume.restrict (Metric.ball (0 : E) 1)) := by
    rw [isFiniteMeasure_restrict]
    exact measure_ball_lt_top.ne
  let happrox0 :=
    moser_shiftApprox_on_ball_of_unitBall (d := d) (u := u) (s := (1 : ℝ)) (θ := 0)
      (by norm_num) (by norm_num) hu1
  let hw0 : MemW1pWitness 2 (positivePartSub u 0) (Metric.ball (0 : E) 1) :=
    positivePartSub_memW1pWitness_on_ball (d := d) (x₀ := (0 : E)) (s := (1 : ℝ))
      (by norm_num) hu1 0 happrox0
  have hEq : positivePartSub u 0 = fun x => max (u x) 0 := by
    funext x
    simp [positivePartSub]
  have hgrad_eq :=
    positivePartSub_grad_eq_on_superlevel (d := d) Metric.isOpen_ball hu1 hw0
  filter_upwards [hgrad_eq] with x hx hxpos
  simpa [moserPosPartWitnessUnitBall, happrox0, hw0, hEq] using (hx hxpos).symm

lemma moserPosPartWitnessUnitBall_grad_zero_on_nonpos
    {u : E → ℝ}
    (hu1 : MemW1pWitness 2 u (Metric.ball (0 : E) 1)) :
    ∀ᵐ x ∂(volume.restrict (Metric.ball (0 : E) 1)),
      u x ≤ 0 →
        (moserPosPartWitnessUnitBall (d := d) (u := u) hu1).weakGrad x = 0 := by
  let happrox0 :=
    moser_shiftApprox_on_ball_of_unitBall (d := d) (u := u) (s := (1 : ℝ)) (θ := 0)
      (by norm_num) (by norm_num) hu1
  let hw0 : MemW1pWitness 2 (positivePartSub u 0) (Metric.ball (0 : E) 1) :=
    positivePartSub_memW1pWitness_on_ball (d := d) (x₀ := (0 : E)) (s := (1 : ℝ))
      (by norm_num) hu1 0 happrox0
  have hEq : positivePartSub u 0 = fun x => max (u x) 0 := by
    funext x
    simp [positivePartSub]
  have hgrad_zero :=
    positivePartSub_grad_zero_on_sublevel (d := d) Metric.isOpen_ball hw0
  filter_upwards [hgrad_zero] with x hx hxnonpos
  simpa [moserPosPartWitnessUnitBall, happrox0, hw0, hEq] using hx hxnonpos

lemma moserPosPartWitness_restrict_grad_eq_on_pos
    {Ω : Set E} {u : E → ℝ}
    (hΩ : IsOpen Ω)
    (hsub : Ω ⊆ Metric.ball (0 : E) 1)
    (hu1 : MemW1pWitness 2 u (Metric.ball (0 : E) 1)) :
    ∀ᵐ x ∂(volume.restrict Ω),
      0 < u x →
        ((moserPosPartWitnessUnitBall (d := d) (u := u) hu1).restrict hΩ hsub).weakGrad x =
          (hu1.restrict hΩ hsub).weakGrad x := by
  have hbig :
      ∀ᵐ x ∂(volume.restrict Ω),
        0 < u x →
          (moserPosPartWitnessUnitBall (d := d) (u := u) hu1).weakGrad x = hu1.weakGrad x := by
    exact ae_restrict_of_ae_restrict_of_subset hsub <|
      moserPosPartWitnessUnitBall_grad_eq_on_pos (d := d) (u := u) hu1
  filter_upwards [hbig] with x hx hxpos
  exact hx hxpos

lemma moserPosPartWitness_restrict_grad_zero_on_nonpos
    {Ω : Set E} {u : E → ℝ}
    (hΩ : IsOpen Ω)
    (hsub : Ω ⊆ Metric.ball (0 : E) 1)
    (hu1 : MemW1pWitness 2 u (Metric.ball (0 : E) 1)) :
    ∀ᵐ x ∂(volume.restrict Ω),
      u x ≤ 0 →
        ((moserPosPartWitnessUnitBall (d := d) (u := u) hu1).restrict hΩ hsub).weakGrad x = 0 := by
  have hbig :
      ∀ᵐ x ∂(volume.restrict Ω),
        u x ≤ 0 →
          (moserPosPartWitnessUnitBall (d := d) (u := u) hu1).weakGrad x = 0 := by
    exact ae_restrict_of_ae_restrict_of_subset hsub <|
      moserPosPartWitnessUnitBall_grad_zero_on_nonpos (d := d) (u := u) hu1
  filter_upwards [hbig] with x hx hxnonpos
  exact hx hxnonpos

noncomputable def moserExactRegPosPartWitness
    {u : E → ℝ} {ε N p : ℝ}
    (hε : 0 < ε) (hN : 0 ≤ N)
    (hu1 : MemW1pWitness 2 u (Metric.ball (0 : E) 1)) :
    MemW1pWitness 2
      (fun x => moserExactRegPow ε N p (max (u x) 0))
      (Metric.ball (0 : E) 1) := by
  let hwPos := moserPosPartWitnessUnitBall (d := d) (u := u) hu1
  have hzero :
      moserExactRegPow ε N p 0 = 0 := by
    rw [moserExactRegPow_eq_shifted_of_nonneg_le_N (ε := ε) (N := N) (p := p) hε le_rfl hN]
    ring_nf
  exact
    (MemW1pWitness.comp_smooth_bounded
      (d := d) Metric.isOpen_ball hwPos
      (moserExactRegPow ε N p)
      (moserExactRegPow_contDiff (ε := ε) (N := N) (p := p) hε hN)
      hzero
      (moserExactRegPow_deriv_bounded (ε := ε) (N := N) (p := p) hε hN))

noncomputable def moserExactRegPowerCutoff
    (η u : E → ℝ) (ε N p : ℝ) : E → ℝ :=
  fun x => η x * moserExactRegPow ε N p (max (u x) 0)

noncomputable def moserExactRegPowerCutoffWitness
    {u η : E → ℝ} {ε N p Cη : ℝ}
    (hε : 0 < ε) (hN : 0 ≤ N)
    (hu1 : MemW1pWitness 2 u (Metric.ball (0 : E) 1))
    (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hη_bound : ∀ x, |η x| ≤ 1)
    (hη_grad_bound : ∀ x, ‖fderiv ℝ η x‖ ≤ Cη) :
    MemW1pWitness 2
      (moserExactRegPowerCutoff η u ε N p)
      (Metric.ball (0 : E) 1) := by
  let hwReg :=
    moserExactRegPosPartWitness (d := d) (u := u) (ε := ε) (N := N) (p := p) hε hN hu1
  have hCη_nonneg : 0 ≤ Cη := by
    exact le_trans (norm_nonneg _) (hη_grad_bound (0 : E))
  exact hwReg.mul_smooth_bounded Metric.isOpen_ball hη
    (C₀ := 1) (C₁ := Cη) (by norm_num) hCη_nonneg hη_bound hη_grad_bound

noncomputable def moserExactRegTestCutoff
    (η u : E → ℝ) (ε N p : ℝ) : E → ℝ :=
  fun x => η x * (η x * moserExactRegTestPow ε N p (max (u x) 0))

noncomputable def moserExactRegTestCutoffWitness
    {u η : E → ℝ} {ε N p Cη : ℝ}
    (hε : 0 < ε) (hN : 0 ≤ N)
    (hu1 : MemW1pWitness 2 u (Metric.ball (0 : E) 1))
    (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hη_bound : ∀ x, |η x| ≤ 1)
    (hη_grad_bound : ∀ x, ‖fderiv ℝ η x‖ ≤ Cη) :
    MemW1pWitness 2
      (moserExactRegTestCutoff η u ε N p)
      (Metric.ball (0 : E) 1) := by
  let hwTest :
      MemW1pWitness 2
        (fun x => moserExactRegTestPow ε N p (max (u x) 0))
        (Metric.ball (0 : E) 1) := by
      let hwPos := moserPosPartWitnessUnitBall (d := d) (u := u) hu1
      have hzero :
          moserExactRegTestPow ε N p 0 = 0 := by
        rw [moserExactRegTestPow_eq_shifted_of_nonneg_le_N (ε := ε) (N := N) (p := p) hε le_rfl hN]
        ring_nf
      exact
        (MemW1pWitness.comp_smooth_bounded
          (d := d) Metric.isOpen_ball hwPos
          (moserExactRegTestPow ε N p)
          (moserExactRegTestPow_contDiff (ε := ε) (N := N) (p := p) hε hN)
          hzero
          (moserExactRegTestPow_deriv_bounded (ε := ε) (N := N) (p := p) hε hN))
  have hCη_nonneg : 0 ≤ Cη := by
    exact le_trans (norm_nonneg _) (hη_grad_bound (0 : E))
  let hwη :=
    hwTest.mul_smooth_bounded Metric.isOpen_ball hη
      (C₀ := 1) (C₁ := Cη) (by norm_num) hCη_nonneg hη_bound hη_grad_bound
  exact
    hwη.mul_smooth_bounded Metric.isOpen_ball hη
      (C₀ := 1) (C₁ := Cη) (by norm_num) hCη_nonneg hη_bound hη_grad_bound

theorem moserExactRegTestPow_nonneg_of_nonneg_le_N
    {ε N p t : ℝ} (hε : 0 < ε) (_hN : 0 ≤ N) (ht0 : 0 ≤ t) (htN : t ≤ N) (hp : 1 < p) :
    0 ≤ moserExactRegTestPow ε N p t := by
  rw [moserExactRegTestPow_eq_shifted_of_nonneg_le_N (ε := ε) (N := N) (p := p) hε ht0 htN]
  refine sub_nonneg.mpr ?_
  exact Real.rpow_le_rpow (by linarith) (by linarith) (by linarith)

theorem moserExactRegTestPow_nonneg_of_nonneg
    {ε N p t : ℝ} (hε : 0 < ε) (hN : 0 ≤ N) (ht0 : 0 ≤ t) (hp : 1 < p) :
    0 ≤ moserExactRegTestPow ε N p t := by
  dsimp [moserExactRegTestPow]
  refine sub_nonneg.mpr ?_
  refine Real.rpow_le_rpow (by linarith) ?_ (by linarith)
  have hinput_nonneg :
      0 ≤ moserExactInput ε N t :=
    moserExactInput_nonneg_of_nonneg (ε := ε) (N := N) hε hN ht0
  linarith

omit [NeZero d] in
theorem moserExactRegTestCutoff_nonneg
    {u η : E → ℝ} {ε N p : ℝ}
    (hε : 0 < ε) (hN : 0 ≤ N) (hp : 1 < p)
    (hbound : ∀ x, x ∈ tsupport η → max (u x) 0 ≤ N) :
    ∀ x, 0 ≤ moserExactRegTestCutoff η u ε N p x := by
  intro x
  dsimp [moserExactRegTestCutoff]
  by_cases hx : x ∈ tsupport η
  · have huN : max (u x) 0 ≤ N := hbound x hx
    have hψ_nonneg :
        0 ≤ moserExactRegTestPow ε N p (max (u x) 0) := by
      exact moserExactRegTestPow_nonneg_of_nonneg_le_N (ε := ε) (N := N) (p := p)
        hε hN (le_max_right _ _) huN hp
    ring_nf
    exact mul_nonneg (sq_nonneg (η x)) hψ_nonneg
  · have hηx : η x = 0 := image_eq_zero_of_notMem_tsupport hx
    simp [hηx]

omit [NeZero d] in
theorem moserExactRegTestCutoff_nonneg_global
    {u η : E → ℝ} {ε N p : ℝ}
    (hε : 0 < ε) (hN : 0 ≤ N) (hp : 1 < p)
    (_hη_nonneg : ∀ x, 0 ≤ η x) :
    ∀ x, 0 ≤ moserExactRegTestCutoff η u ε N p x := by
  intro x
  dsimp [moserExactRegTestCutoff]
  have hψ_nonneg :
      0 ≤ moserExactRegTestPow ε N p (max (u x) 0) := by
    exact moserExactRegTestPow_nonneg_of_nonneg (ε := ε) (N := N) (p := p)
      hε hN (le_max_right _ _) hp
  have hEq :
      η x * (η x * moserExactRegTestPow ε N p (max (u x) 0)) =
        η x ^ 2 * moserExactRegTestPow ε N p (max (u x) 0) := by
    ring
  rw [hEq]
  exact mul_nonneg (sq_nonneg (η x)) hψ_nonneg

theorem moserExactRegPow_zero
    {ε N p : ℝ} (hε : 0 < ε) (hN : 0 ≤ N) :
    moserExactRegPow ε N p 0 = 0 := by
  rw [moserExactRegPow_eq_shifted_of_nonneg_le_N (ε := ε) (N := N) (p := p) hε le_rfl hN]
  ring_nf

theorem moserExactRegTestPow_zero
    {ε N p : ℝ} (hε : 0 < ε) (hN : 0 ≤ N) :
    moserExactRegTestPow ε N p 0 = 0 := by
  rw [moserExactRegTestPow_eq_shifted_of_nonneg_le_N (ε := ε) (N := N) (p := p) hε le_rfl hN]
  ring_nf

omit [NeZero d] in
theorem moserExactRegPowerCutoff_tsupport_subset
    {u η : E → ℝ} {ε N p : ℝ}
    (hη_sub : tsupport η ⊆ Metric.ball (0 : E) 1) :
    tsupport (moserExactRegPowerCutoff η u ε N p) ⊆ Metric.ball (0 : E) 1 := by
  exact (tsupport_mul_subset_left
    (f := η) (g := fun x => moserExactRegPow ε N p (max (u x) 0))).trans hη_sub

theorem moserExactRegPowerCutoff_memW01p_on_ball
    {u η : E → ℝ} {ρ ε N p Cη : ℝ}
    (hρ1 : ρ < 1)
    (hε : 0 < ε) (hN : 0 ≤ N)
    (hu1 : MemW1pWitness 2 u (Metric.ball (0 : E) 1))
    (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hη_bound : ∀ x, |η x| ≤ 1)
    (hη_grad_bound : ∀ x, ‖fderiv ℝ η x‖ ≤ Cη)
    (hη_sub_ball : tsupport η ⊆ Metric.ball (0 : E) ρ) :
    MemW01p 2 (moserExactRegPowerCutoff η u ε N p) (Metric.ball (0 : E) ρ) := by
  let Ω : Set E := Metric.ball (0 : E) ρ
  let hwPowerBig :
      MemW1pWitness 2 (moserExactRegPowerCutoff η u ε N p) (Metric.ball (0 : E) 1) :=
    moserExactRegPowerCutoffWitness (d := d) (u := u) (η := η) (ε := ε) (N := N) (p := p)
      (Cη := Cη) hε hN hu1 hη hη_bound hη_grad_bound
  let hwPower : MemW1pWitness 2 (moserExactRegPowerCutoff η u ε N p) Ω :=
    hwPowerBig.restrict Metric.isOpen_ball (Metric.ball_subset_ball (le_of_lt hρ1))
  have hv_support : tsupport (moserExactRegPowerCutoff η u ε N p) ⊆ Ω := by
    exact (tsupport_mul_subset_left
      (f := η) (g := fun x => moserExactRegPow ε N p (max (u x) 0))).trans hη_sub_ball
  have hv_compact : HasCompactSupport (moserExactRegPowerCutoff η u ε N p) :=
    hasCompactSupport_of_tsupport_subset_ball hv_support
  have hv_memW01p : MemW01p (ENNReal.ofReal (2 : ℝ))
      (moserExactRegPowerCutoff η u ε N p) Ω :=
    memW01p_of_memW1p_of_tsupport_subset Metric.isOpen_ball (by norm_num : (1 : ℝ) < 2)
      (by simpa [Ω] using hwPower.memW1p) hv_compact hv_support
  simpa [Ω] using hv_memW01p

omit [NeZero d] in
theorem moserExactRegTestCutoff_tsupport_subset
    {u η : E → ℝ} {ε N p : ℝ}
    (hη_sub : tsupport η ⊆ Metric.ball (0 : E) 1) :
    tsupport (moserExactRegTestCutoff η u ε N p) ⊆ Metric.ball (0 : E) 1 := by
  exact (tsupport_mul_subset_left
    (f := η) (g := fun x => η x * moserExactRegTestPow ε N p (max (u x) 0))).trans hη_sub

theorem moserExactRegTestCutoff_memH01_on_ball
    {u η : E → ℝ} {ρ ε N p Cη : ℝ}
    (_hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hε : 0 < ε) (hN : 0 ≤ N)
    (hu1 : MemW1pWitness 2 u (Metric.ball (0 : E) 1))
    (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hη_bound : ∀ x, |η x| ≤ 1)
    (hη_grad_bound : ∀ x, ‖fderiv ℝ η x‖ ≤ Cη)
    (hη_sub_ball : tsupport η ⊆ Metric.ball (0 : E) ρ) :
    MemH01 (moserExactRegTestCutoff η u ε N p) (Metric.ball (0 : E) ρ) := by
  let Ω : Set E := Metric.ball (0 : E) ρ
  let hwTestBig :
      MemW1pWitness 2 (moserExactRegTestCutoff η u ε N p) (Metric.ball (0 : E) 1) :=
    moserExactRegTestCutoffWitness (d := d) (u := u) (η := η) (ε := ε) (N := N) (p := p)
      (Cη := Cη) hε hN hu1 hη hη_bound hη_grad_bound
  let hwTest : MemW1pWitness 2 (moserExactRegTestCutoff η u ε N p) Ω :=
    hwTestBig.restrict Metric.isOpen_ball (Metric.ball_subset_ball (le_of_lt hρ1))
  have hv_support : tsupport (moserExactRegTestCutoff η u ε N p) ⊆ Ω := by
    exact (tsupport_mul_subset_left
      (f := η) (g := fun x => η x * moserExactRegTestPow ε N p (max (u x) 0))).trans hη_sub_ball
  have hv_compact : HasCompactSupport (moserExactRegTestCutoff η u ε N p) :=
    hasCompactSupport_of_tsupport_subset_ball hv_support
  have hv_memW01p : MemW01p (ENNReal.ofReal (2 : ℝ))
      (moserExactRegTestCutoff η u ε N p) Ω :=
    memW01p_of_memW1p_of_tsupport_subset Metric.isOpen_ball (by norm_num : (1 : ℝ) < 2)
      (by simpa [Ω] using hwTest.memW1p) hv_compact hv_support
  simpa [Ω] using hv_memW01p

lemma moserExactRegPowerCutoffWitness_grad
    {u η : E → ℝ} {ε N p Cη : ℝ}
    (hε : 0 < ε) (hN : 0 ≤ N)
    (hu1 : MemW1pWitness 2 u (Metric.ball (0 : E) 1))
    (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hη_bound : ∀ x, |η x| ≤ 1)
    (hη_grad_bound : ∀ x, ‖fderiv ℝ η x‖ ≤ Cη)
    (x : E) (i : Fin d) :
    (moserExactRegPowerCutoffWitness (d := d) (u := u) (η := η) (ε := ε) (N := N) (p := p)
      (Cη := Cη) hε hN hu1 hη hη_bound hη_grad_bound).weakGrad x i =
      η x * deriv (moserExactRegPow ε N p) (max (u x) 0) *
        (moserPosPartWitnessUnitBall (d := d) (u := u) hu1).weakGrad x i +
      (fderiv ℝ η x) (EuclideanSpace.single i 1) *
        moserExactRegPow ε N p (max (u x) 0) := by
  simp only [moserExactRegPowerCutoffWitness, moserExactRegPosPartWitness, moserPosPartWitnessUnitBall,
    MemW1pWitness.mul_smooth_bounded, MemW1pWitness.comp_smooth_bounded,
    WithLp.ofLp_add, WithLp.ofLp_smul, smul_eq_mul, Pi.add_apply, Pi.smul_apply]
  ring

lemma moserExactRegTestCutoffWitness_grad
    {u η : E → ℝ} {ε N p Cη : ℝ}
    (hε : 0 < ε) (hN : 0 ≤ N)
    (hu1 : MemW1pWitness 2 u (Metric.ball (0 : E) 1))
    (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hη_bound : ∀ x, |η x| ≤ 1)
    (hη_grad_bound : ∀ x, ‖fderiv ℝ η x‖ ≤ Cη)
    (x : E) (i : Fin d) :
    (moserExactRegTestCutoffWitness (d := d) (u := u) (η := η) (ε := ε) (N := N) (p := p)
      (Cη := Cη) hε hN hu1 hη hη_bound hη_grad_bound).weakGrad x i =
      2 * η x * (fderiv ℝ η x) (EuclideanSpace.single i 1) *
        moserExactRegTestPow ε N p (max (u x) 0) +
      η x ^ 2 * deriv (moserExactRegTestPow ε N p) (max (u x) 0) *
        (moserPosPartWitnessUnitBall (d := d) (u := u) hu1).weakGrad x i := by
  simp only [moserExactRegTestCutoffWitness, moserPosPartWitnessUnitBall, MemW1pWitness.mul_smooth_bounded,
    MemW1pWitness.comp_smooth_bounded, WithLp.ofLp_add, WithLp.ofLp_smul,
    smul_eq_mul, Pi.add_apply, Pi.smul_apply]
  ring

lemma moserExactRegPowerCutoffWitness_norm_sq_le
    {u η : E → ℝ} {ε N p Cη : ℝ}
    (hε : 0 < ε) (hN : 0 ≤ N)
    (hu1 : MemW1pWitness 2 u (Metric.ball (0 : E) 1))
    (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hη_bound : ∀ x, |η x| ≤ 1)
    (hη_grad_bound : ∀ x, ‖fderiv ℝ η x‖ ≤ Cη)
    (x : E) :
    ‖(moserExactRegPowerCutoffWitness (d := d) (u := u) (η := η) (ε := ε) (N := N) (p := p)
      (Cη := Cη) hε hN hu1 hη hη_bound hη_grad_bound).weakGrad x‖ ^ 2 ≤
      2 * (η x ^ 2 * (deriv (moserExactRegPow ε N p) (max (u x) 0)) ^ 2 *
        ‖(moserPosPartWitnessUnitBall (d := d) (u := u) hu1).weakGrad x‖ ^ 2) +
      2 * (‖fderiv ℝ η x‖ ^ 2 *
        (moserExactRegPow ε N p (max (u x) 0)) ^ 2) := by
  have hterm : ∀ i : Fin d,
      (moserExactRegPowerCutoffWitness (d := d) (u := u) (η := η) (ε := ε) (N := N) (p := p)
        (Cη := Cη) hε hN hu1 hη hη_bound hη_grad_bound).weakGrad x i ^ 2 ≤
      2 * (η x * deriv (moserExactRegPow ε N p) (max (u x) 0) *
        (moserPosPartWitnessUnitBall (d := d) (u := u) hu1).weakGrad x i) ^ 2 +
      2 * ((fderiv ℝ η x) (EuclideanSpace.single i 1) *
        moserExactRegPow ε N p (max (u x) 0)) ^ 2 := by
    intro i
    rw [moserExactRegPowerCutoffWitness_grad (d := d) (u := u) (η := η) (ε := ε) (N := N)
      (p := p) (Cη := Cη) hε hN hu1 hη hη_bound hη_grad_bound x i]
    nlinarith [sq_nonneg
      (η x * deriv (moserExactRegPow ε N p) (max (u x) 0) *
        (moserPosPartWitnessUnitBall (d := d) (u := u) hu1).weakGrad x i -
        (fderiv ℝ η x) (EuclideanSpace.single i 1) *
          moserExactRegPow ε N p (max (u x) 0))]
  rw [EuclideanSpace.norm_eq (𝕜 := ℝ),
    Real.sq_sqrt (Finset.sum_nonneg fun i _ => by positivity)]
  simp_rw [Real.norm_eq_abs, sq_abs]
  rw [EuclideanSpace.norm_eq (𝕜 := ℝ)
      ((moserPosPartWitnessUnitBall (d := d) (u := u) hu1).weakGrad x),
    Real.sq_sqrt (Finset.sum_nonneg fun i _ => by positivity)]
  simp_rw [Real.norm_eq_abs, sq_abs]
  rw [show ‖fderiv ℝ η x‖ ^ 2 = ∑ i : Fin d,
      ((fderiv ℝ η x) (EuclideanSpace.single i 1)) ^ 2 by
    rw [← moser_norm_fderivVec_eq_norm_fderiv (d := d) (η := η) (x := x),
      EuclideanSpace.norm_eq (𝕜 := ℝ),
      Real.sq_sqrt (Finset.sum_nonneg fun i _ => by positivity)]
    simp_rw [Real.norm_eq_abs, sq_abs, moserFderivVec_apply]]
  calc
    ∑ i, (moserExactRegPowerCutoffWitness (d := d) (u := u) (η := η) (ε := ε) (N := N)
          (p := p) (Cη := Cη) hε hN hu1 hη hη_bound hη_grad_bound).weakGrad x i ^ 2
        ≤ ∑ i,
            (2 * (η x * deriv (moserExactRegPow ε N p) (max (u x) 0) *
              (moserPosPartWitnessUnitBall (d := d) (u := u) hu1).weakGrad x i) ^ 2 +
            2 * ((fderiv ℝ η x) (EuclideanSpace.single i 1) *
              moserExactRegPow ε N p (max (u x) 0)) ^ 2) := by
            exact Finset.sum_le_sum fun i _ => hterm i
    _ = 2 * (η x ^ 2 * deriv (moserExactRegPow ε N p) (max (u x) 0) ^ 2 *
          ∑ i, (moserPosPartWitnessUnitBall (d := d) (u := u) hu1).weakGrad x i ^ 2) +
        2 * ((∑ i, ((fderiv ℝ η x) (EuclideanSpace.single i 1)) ^ 2) *
          moserExactRegPow ε N p (max (u x) 0) ^ 2) := by
          have : ∀ i : Fin d,
              2 * (η x * deriv (moserExactRegPow ε N p) (max (u x) 0) *
                (moserPosPartWitnessUnitBall (d := d) (u := u) hu1).weakGrad x i) ^ 2 +
              2 * ((fderiv ℝ η x) (EuclideanSpace.single i 1) *
                moserExactRegPow ε N p (max (u x) 0)) ^ 2 =
              2 * (η x ^ 2 * deriv (moserExactRegPow ε N p) (max (u x) 0) ^ 2 *
                ((moserPosPartWitnessUnitBall (d := d) (u := u) hu1).weakGrad x i ^ 2)) +
              2 * (((fderiv ℝ η x) (EuclideanSpace.single i 1)) ^ 2 *
                moserExactRegPow ε N p (max (u x) 0) ^ 2) := by
            intro i
            ring
          simp_rw [this, Finset.sum_add_distrib, ← Finset.mul_sum]
          simp [mul_comm, mul_left_comm, mul_assoc, ← Finset.mul_sum]

theorem moserExactRegPow_hasDerivAt_shifted
    {ε N p t : ℝ} (hε : 0 < ε) (ht0 : 0 < t) (htN : t < N) :
    HasDerivAt (moserExactRegPow ε N p)
      ((p / 2) * (ε + t) ^ (p / 2 - 1)) t := by
  have hloc :
      moserExactRegPow ε N p =ᶠ[nhds t]
        fun y : ℝ => (ε + y) ^ (p / 2) - ε ^ (p / 2) := by
    filter_upwards [Ioo_mem_nhds ht0 htN] with y hy
    rw [moserExactRegPow_eq_shifted_of_nonneg_le_N (ε := ε) (N := N) (p := p) hε hy.1.le hy.2.le]
  have hbase :
      HasDerivAt (fun y : ℝ => (ε + y) ^ (p / 2) - ε ^ (p / 2))
        ((p / 2) * (ε + t) ^ (p / 2 - 1)) t := by
    have hbase0 :
        HasDerivAt (fun y : ℝ => (ε + y) ^ (p / 2))
          (((p / 2) * (ε + t) ^ (p / 2 - 1)) * 1) t := by
      simpa using
        (((hasDerivAt_id t).const_add ε).rpow_const
          (p := p / 2) (Or.inl (by linarith : ε + t ≠ 0)))
    simpa [one_mul] using hbase0.sub_const (ε ^ (p / 2))
  exact hbase.congr_of_eventuallyEq hloc

theorem moserExactRegTestPow_hasDerivAt_shifted
    {ε N p t : ℝ} (hε : 0 < ε) (ht0 : 0 < t) (htN : t < N) :
    HasDerivAt (moserExactRegTestPow ε N p)
      ((p - 1) * (ε + t) ^ (p - 2)) t := by
  have hloc :
      moserExactRegTestPow ε N p =ᶠ[nhds t]
        fun y : ℝ => (ε + y) ^ (p - 1) - ε ^ (p - 1) := by
    filter_upwards [Ioo_mem_nhds ht0 htN] with y hy
    rw [moserExactRegTestPow_eq_shifted_of_nonneg_le_N (ε := ε) (N := N) (p := p) hε hy.1.le hy.2.le]
  have hbase :
      HasDerivAt (fun y : ℝ => (ε + y) ^ (p - 1) - ε ^ (p - 1))
        ((p - 1) * (ε + t) ^ (p - 2)) t := by
    have hraw :
        HasDerivAt (fun y : ℝ => (ε + y) ^ (p - 1))
          (1 * ((p - 1) * (ε + t) ^ ((p - 1) - 1))) t := by
      simpa [one_mul] using
        (((hasDerivAt_id t).const_add ε).rpow_const
          (p := p - 1) (Or.inl (by linarith : ε + t ≠ 0)))
    have hbase0 :
        HasDerivAt (fun y : ℝ => (ε + y) ^ (p - 1))
          (((p - 1) * (ε + t) ^ (p - 2)) * 1) t := by
      convert hraw using 1
      ring_nf
    simpa [one_mul] using hbase0.sub_const (ε ^ (p - 1))
  exact hbase.congr_of_eventuallyEq hloc

theorem moserExactInput_hasDerivAt_zero
    {ε N : ℝ} (hε : 0 < ε) (hN : 0 < N) :
    HasDerivAt (moserExactInput ε N) 1 0 := by
  have hloc :
      moserExactInput ε N =ᶠ[nhds 0]
        fun t : ℝ => t * moserExactLeftTransition ε t := by
    filter_upwards [Iio_mem_nhds hN] with t ht
    have hσR : Real.smoothTransition (N + 1 - t) = 1 := by
      apply Real.smoothTransition.one_of_one_le
      have htN : t < N := ht
      linarith
    simp [moserExactInput, hσR]
  have hσL_diff : DifferentiableAt ℝ (moserExactLeftTransition ε) 0 := by
    exact ((moserExactLeftTransition_contDiff (ε := ε) hε).differentiable (by simp)).differentiableAt
  have hprod :
      HasDerivAt (fun t : ℝ => t * moserExactLeftTransition ε t)
        (1 * moserExactLeftTransition ε 0 + 0 * deriv (moserExactLeftTransition ε) 0) 0 := by
    exact (hasDerivAt_id 0).mul hσL_diff.hasDerivAt
  have hσL0 : moserExactLeftTransition ε 0 = 1 := by
    exact moserExactLeftTransition_eq_one_of_nonneg (ε := ε) hε le_rfl
  have hprod' : HasDerivAt (fun t : ℝ => t * moserExactLeftTransition ε t) 1 0 := by
    simpa [hσL0] using hprod
  exact hprod'.congr_of_eventuallyEq hloc

theorem moserExactRegTestPow_hasDerivAt_zero
    {ε N p : ℝ} (hε : 0 < ε) (hN : 0 < N) :
    HasDerivAt (moserExactRegTestPow ε N p)
      ((p - 1) * ε ^ (p - 2)) 0 := by
  have hinput :
      HasDerivAt (moserExactInput ε N) 1 0 :=
    moserExactInput_hasDerivAt_zero (ε := ε) (N := N) hε hN
  have hbase :
      HasDerivAt (fun t : ℝ => (ε + moserExactInput ε N t) ^ (p - 1))
        (((p - 1) * (ε + moserExactInput ε N 0) ^ ((p - 1) - 1)) * 1) 0 := by
    simpa using
      ((hinput.const_add ε).rpow_const
        (p := p - 1) (Or.inl (by
          have hε0 : 0 < ε + moserExactInput ε N 0 := by
            rw [moserExactInput_eq_self_of_nonneg_le_N (ε := ε) hε le_rfl hN.le]
            linarith
          linarith)))
  have hinput0 : moserExactInput ε N 0 = 0 := by
    rw [moserExactInput_eq_self_of_nonneg_le_N (ε := ε) hε le_rfl hN.le]
  have hbase' :
      HasDerivAt (fun t : ℝ => (ε + moserExactInput ε N t) ^ (p - 1))
        ((p - 1) * ε ^ (p - 2)) 0 := by
    have hpow : (p - 1) - 1 = p - 2 := by ring
    simpa [hinput0, hpow] using hbase
  change HasDerivAt
    (fun t : ℝ => (ε + moserExactInput ε N t) ^ (p - 1) - ε ^ (p - 1))
    ((p - 1) * ε ^ (p - 2)) 0
  exact hbase'.sub_const (ε ^ (p - 1))

theorem moserExactRegPow_deriv_eq_shifted
    {ε N p t : ℝ} (hε : 0 < ε) (ht0 : 0 < t) (htN : t < N) :
    deriv (moserExactRegPow ε N p) t = (p / 2) * (ε + t) ^ (p / 2 - 1) :=
  (moserExactRegPow_hasDerivAt_shifted (ε := ε) (N := N) (p := p) hε ht0 htN).deriv

theorem moserExactRegTestPow_deriv_eq_shifted
    {ε N p t : ℝ} (hε : 0 < ε) (ht0 : 0 < t) (htN : t < N) :
    deriv (moserExactRegTestPow ε N p) t = (p - 1) * (ε + t) ^ (p - 2) :=
  (moserExactRegTestPow_hasDerivAt_shifted (ε := ε) (N := N) (p := p) hε ht0 htN).deriv

theorem moserExactRegTestPow_deriv_eq_zero
    {ε N p : ℝ} (hε : 0 < ε) (hN : 0 < N) :
    deriv (moserExactRegTestPow ε N p) 0 = (p - 1) * ε ^ (p - 2) :=
  (moserExactRegTestPow_hasDerivAt_zero (ε := ε) (N := N) (p := p) hε hN).deriv

theorem moserExactRegTestPow_deriv_pos_of_pos_lt_N
    {ε N p t : ℝ} (hε : 0 < ε) (hp : 1 < p)
    (ht0 : 0 < t) (htN : t < N) :
    0 < deriv (moserExactRegTestPow ε N p) t := by
  rw [moserExactRegTestPow_deriv_eq_shifted (ε := ε) (N := N) (p := p) hε ht0 htN]
  have hp1 : 0 < p - 1 := by linarith
  exact mul_pos hp1 (Real.rpow_pos_of_pos (by linarith) _)

theorem moserExactRegTestPow_deriv_pos_of_nonneg_lt_N
    {ε N p t : ℝ} (hε : 0 < ε) (hp : 1 < p)
    (ht0 : 0 ≤ t) (htN : t < N) :
    0 < deriv (moserExactRegTestPow ε N p) t := by
  by_cases hzero : t = 0
  · subst hzero
    have hNpos : 0 < N := by linarith
    rw [moserExactRegTestPow_deriv_eq_zero (ε := ε) (N := N) (p := p) hε hNpos]
    have hp1 : 0 < p - 1 := by linarith
    exact mul_pos hp1 (Real.rpow_pos_of_pos hε _)
  · exact moserExactRegTestPow_deriv_pos_of_pos_lt_N (ε := ε) (N := N) (p := p)
      hε hp (lt_of_le_of_ne ht0 (Ne.symm hzero)) htN

theorem moserExactRegPow_deriv_sq_le_const_mul_testDeriv
    {ε N p t : ℝ} (hε : 0 < ε) (hp : 1 < p)
    (ht0 : 0 < t) (htN : t < N) :
    (deriv (moserExactRegPow ε N p) t) ^ 2 ≤
      (p ^ 2 / (4 * (p - 1))) * deriv (moserExactRegTestPow ε N p) t := by
  rw [moserExactRegPow_deriv_eq_shifted (ε := ε) (N := N) (p := p) hε ht0 htN,
    moserExactRegTestPow_deriv_eq_shifted (ε := ε) (N := N) (p := p) hε ht0 htN]
  have hbase_pos : 0 < ε + t := by linarith
  have hpow :
      ((ε + t) ^ (p / 2 - 1)) ^ 2 = (ε + t) ^ (p - 2) := by
    rw [← Real.rpow_natCast ((ε + t) ^ (p / 2 - 1)) 2, ← Real.rpow_mul hbase_pos.le]
    congr 1
    ring
  calc
    ((p / 2) * (ε + t) ^ (p / 2 - 1)) ^ 2
        = (p / 2) ^ 2 * (ε + t) ^ (p - 2) := by
            rw [mul_pow, hpow]
    _ = (p ^ 2 / 4) * (ε + t) ^ (p - 2) := by
          ring
    _ = (p ^ 2 / (4 * (p - 1))) * ((p - 1) * (ε + t) ^ (p - 2)) := by
          field_simp [show p - 1 ≠ 0 by linarith]
    _ ≤ (p ^ 2 / (4 * (p - 1))) * ((p - 1) * (ε + t) ^ (p - 2)) := by
          exact le_rfl

theorem moserExactRegPow_nonneg_of_nonneg_le_N
    {ε N p t : ℝ} (hε : 0 < ε) (ht0 : 0 ≤ t) (htN : t ≤ N) (hp : 0 ≤ p) :
    0 ≤ moserExactRegPow ε N p t := by
  rw [moserExactRegPow_eq_shifted_of_nonneg_le_N (ε := ε) (N := N) (p := p) hε ht0 htN]
  simpa using Real.rpow_le_rpow (by linarith) (by linarith) (by positivity)

theorem moserExactRegPow_le_rpow_of_nonneg_le_N
    {ε N p t : ℝ} (hε : 0 < ε) (ht0 : 0 ≤ t) (htN : t ≤ N) (_hp : 0 < p) :
    moserExactRegPow ε N p t ≤ (ε + t) ^ (p / 2) := by
  rw [moserExactRegPow_eq_shifted_of_nonneg_le_N (ε := ε) (N := N) (p := p) hε ht0 htN]
  have : 0 ≤ ε ^ (p / 2) := Real.rpow_nonneg hε.le (p / 2)
  linarith

theorem moserExactRegPow_sq_le_rpow_of_nonneg_le_N
    {ε N p t : ℝ} (hε : 0 < ε) (ht0 : 0 ≤ t) (htN : t ≤ N) (hp : 1 < p) :
    moserExactRegPow ε N p t ^ 2 ≤ (ε + t) ^ p := by
  have hp0 : 0 < p := by linarith
  have hle := moserExactRegPow_le_rpow_of_nonneg_le_N (ε := ε) (N := N) (p := p) hε ht0 htN hp0
  have hnn := moserExactRegPow_nonneg_of_nonneg_le_N (ε := ε) (N := N) (p := p) hε ht0 htN (by linarith)
  have hbase : 0 ≤ ε + t := by linarith
  calc
    moserExactRegPow ε N p t ^ 2 ≤ ((ε + t) ^ (p / 2)) ^ 2 := sq_le_sq' (by linarith) hle
    _ = (ε + t) ^ p := by
      rw [← Real.rpow_natCast ((ε + t) ^ (p / 2)) 2, ← Real.rpow_mul hbase]
      congr 1
      ring

theorem moserExactRegTestPow_sq_div_deriv_le_rpow
    {ε N p t : ℝ} (hε : 0 < ε) (hp : 1 < p)
    (ht0 : 0 < t) (htN : t < N) :
    (moserExactRegTestPow ε N p t) ^ 2 / deriv (moserExactRegTestPow ε N p) t ≤
      (ε + t) ^ p / (p - 1) := by
  rw [moserExactRegTestPow_eq_shifted_of_nonneg_le_N (ε := ε) (N := N) (p := p) hε ht0.le htN.le,
    moserExactRegTestPow_deriv_eq_shifted (ε := ε) (N := N) (p := p) hε ht0 htN]
  have hden_pos : 0 < (p - 1) * (ε + t) ^ (p - 2) := by
    have hp1 : 0 < p - 1 := by linarith
    exact mul_pos hp1 (Real.rpow_pos_of_pos (by linarith) _)
  have hnum_le : ((ε + t) ^ (p - 1) - ε ^ (p - 1)) ^ 2 ≤ ((ε + t) ^ (p - 1)) ^ 2 := by
    have hA_nonneg : 0 ≤ (ε + t) ^ (p - 1) := Real.rpow_nonneg (by linarith) _
    have hB_nonneg : 0 ≤ ε ^ (p - 1) := Real.rpow_nonneg hε.le _
    have hnn : 0 ≤ (ε + t) ^ (p - 1) - ε ^ (p - 1) := by
      refine sub_nonneg.mpr ?_
      exact Real.rpow_le_rpow (by linarith) (by linarith) (by linarith)
    have hsub_le : (ε + t) ^ (p - 1) - ε ^ (p - 1) ≤ (ε + t) ^ (p - 1) := by
      linarith
    nlinarith [hnn, hsub_le]
  have hbase_pos : 0 < ε + t := by linarith
  have hpow :
      ((ε + t) ^ (p - 1)) ^ 2 / ((p - 1) * (ε + t) ^ (p - 2)) = (ε + t) ^ p / (p - 1) := by
    have hpow_num :
        ((ε + t) ^ (p - 1)) ^ 2 = (ε + t) ^ p * (ε + t) ^ (p - 2) := by
      rw [← Real.rpow_natCast ((ε + t) ^ (p - 1)) 2, ← Real.rpow_mul hbase_pos.le,
        ← Real.rpow_add hbase_pos]
      congr 1
      ring
    have hp1_ne : p - 1 ≠ 0 := by linarith
    have hbasepow_ne : (ε + t) ^ (p - 2) ≠ 0 := by
      exact (Real.rpow_pos_of_pos hbase_pos _).ne'
    rw [hpow_num]
    field_simp [hden_pos.ne', hp1_ne, hbasepow_ne]
  have hdiv := div_le_div_of_nonneg_right hnum_le hden_pos.le
  simpa [hpow] using hdiv

theorem moserExactRegTestPow_sq_div_deriv_le_rpow_of_nonneg_lt_N
    {ε N p t : ℝ} (hε : 0 < ε) (hp : 1 < p)
    (ht0 : 0 ≤ t) (htN : t < N) :
    (moserExactRegTestPow ε N p t) ^ 2 / deriv (moserExactRegTestPow ε N p) t ≤
      (ε + t) ^ p / (p - 1) := by
  by_cases hzero : t = 0
  · subst hzero
    have hNpos : 0 < N := by linarith
    rw [moserExactRegTestPow_zero (ε := ε) (N := N) (p := p) hε hNpos.le,
      moserExactRegTestPow_deriv_eq_zero (ε := ε) (N := N) (p := p) hε hNpos]
    have hp1 : 0 < p - 1 := by linarith
    have hrhs_nonneg : 0 ≤ ε ^ p / (p - 1) := by
      exact div_nonneg (Real.rpow_nonneg hε.le _) hp1.le
    simpa using hrhs_nonneg
  · exact moserExactRegTestPow_sq_div_deriv_le_rpow (ε := ε) (N := N) (p := p)
      hε hp (lt_of_le_of_ne ht0 (Ne.symm hzero)) htN

omit [NeZero d] in
theorem moserExactRegTestPow_deriv_pos_of_support_bound
    {ε N p : ℝ} {u : E → ℝ} {x : E}
    (hε : 0 < ε) (hp : 1 < p)
    (hbound : max (u x) 0 < N) :
    0 < deriv (moserExactRegTestPow ε N p) (max (u x) 0) := by
  exact moserExactRegTestPow_deriv_pos_of_nonneg_lt_N
    (ε := ε) (N := N) (p := p) hε hp (le_max_right _ _) hbound

omit [NeZero d] in
theorem moserExactRegPow_sq_le_rpow_of_support_bound
    {ε N p : ℝ} {u : E → ℝ} {x : E}
    (hε : 0 < ε) (hp : 1 < p)
    (hbound : max (u x) 0 < N) :
    moserExactRegPow ε N p (max (u x) 0) ^ 2 ≤
      (ε + |max (u x) 0|) ^ p := by
  have hbase :=
    moserExactRegPow_sq_le_rpow_of_nonneg_le_N
      (ε := ε) (N := N) (p := p) (t := max (u x) 0)
      hε (le_max_right _ _) hbound.le hp
  simpa [abs_of_nonneg (show (0 : ℝ) ≤ max (u x) 0 by exact le_max_right _ _)] using hbase

omit [NeZero d] in
theorem moserExactRegTestPow_sq_div_deriv_le_rpow_of_support_bound
    {ε N p : ℝ} {u : E → ℝ} {x : E}
    (hε : 0 < ε) (hp : 1 < p)
    (hbound : max (u x) 0 < N) :
    (moserExactRegTestPow ε N p (max (u x) 0)) ^ 2 /
        deriv (moserExactRegTestPow ε N p) (max (u x) 0) ≤
      (ε + |max (u x) 0|) ^ p / (p - 1) := by
  have hbase :=
    moserExactRegTestPow_sq_div_deriv_le_rpow_of_nonneg_lt_N
      (ε := ε) (N := N) (p := p) (t := max (u x) 0)
      hε hp (le_max_right _ _) hbound
  simpa [abs_of_nonneg (show (0 : ℝ) ≤ max (u x) 0 by exact le_max_right _ _)] using hbase

def moserEpsSeq (n : ℕ) : ℝ := (((n : ℝ) + 1) : ℝ)⁻¹

theorem moserEpsSeq_pos (n : ℕ) : 0 < moserEpsSeq n := by
  dsimp [moserEpsSeq]
  positivity

theorem tendsto_moserEpsSeq :
    Tendsto moserEpsSeq atTop (nhds 0) := by
  unfold moserEpsSeq
  have hbase : Tendsto (fun n : ℕ => n + 1) atTop atTop := tendsto_add_atTop_nat 1
  have h :=
    ((tendsto_inv_atTop_nhds_zero_nat : Tendsto (fun n : ℕ => ((n : ℝ))⁻¹) atTop (nhds 0)).comp
      hbase)
  refine h.congr' ?_
  exact Filter.Eventually.of_forall fun n => by
    change ((((n + 1 : ℕ) : ℝ))⁻¹) = (((n : ℝ) + 1)⁻¹)
    norm_num [Nat.cast_add]

theorem moserEpsSeq_le_one (n : ℕ) : moserEpsSeq n ≤ 1 := by
  dsimp [moserEpsSeq]
  have hn_nonneg : (0 : ℝ) ≤ n := by exact_mod_cast Nat.zero_le n
  have hden_ge : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith
  exact inv_le_one_of_one_le₀ hden_ge

theorem moserExactRegPow_tendsto_rpow_of_nonneg_lt_N
    {N p t : ℝ}
    (ht0 : 0 ≤ t) (htN : t < N) (hp : 1 < p) :
    Tendsto (fun n : ℕ => moserExactRegPow (moserEpsSeq n) N p t)
      atTop (nhds (t ^ (p / 2))) := by
  have hp_half_nonneg : 0 ≤ p / 2 := by linarith
  have hp_half_pos : 0 < p / 2 := by linarith
  have hsum :
      Tendsto (fun n : ℕ => moserEpsSeq n + t) atTop (nhds (0 + t)) :=
    tendsto_moserEpsSeq.add tendsto_const_nhds
  have hpow :
      Tendsto (fun n : ℕ => (moserEpsSeq n + t) ^ (p / 2)) atTop (nhds ((0 + t) ^ (p / 2))) :=
    hsum.rpow_const (Or.inr hp_half_nonneg)
  have hpow0 :
      Tendsto (fun n : ℕ => moserEpsSeq n ^ (p / 2)) atTop (nhds (0 ^ (p / 2))) :=
    tendsto_moserEpsSeq.rpow_const (Or.inr hp_half_nonneg)
  have hsub :
      Tendsto (fun n : ℕ => (moserEpsSeq n + t) ^ (p / 2) - moserEpsSeq n ^ (p / 2))
        atTop (nhds ((0 + t) ^ (p / 2) - 0 ^ (p / 2))) := by
    exact hpow.sub hpow0
  have heq :
      (fun n : ℕ => moserExactRegPow (moserEpsSeq n) N p t) =ᶠ[atTop]
        (fun n : ℕ => (moserEpsSeq n + t) ^ (p / 2) - moserEpsSeq n ^ (p / 2)) := by
    exact Filter.Eventually.of_forall fun n => by
      simpa using
        (moserExactRegPow_eq_shifted_of_nonneg_le_N
          (ε := moserEpsSeq n) (N := N) (p := p) (hε := moserEpsSeq_pos n) ht0 htN.le)
  simpa [zero_add, Real.zero_rpow hp_half_pos.ne'] using Tendsto.congr' heq.symm hsub

theorem moserExactRegPow_deriv_tendsto_of_pos_lt_N
    {N p t : ℝ}
    (ht0 : 0 < t) (htN : t < N) :
    Tendsto (fun n : ℕ => deriv (moserExactRegPow (moserEpsSeq n) N p) t)
      atTop (nhds ((p / 2) * t ^ (p / 2 - 1))) := by
  have hsum :
      Tendsto (fun n : ℕ => moserEpsSeq n + t) atTop (nhds (0 + t)) :=
    tendsto_moserEpsSeq.add tendsto_const_nhds
  have hpow :
      Tendsto (fun n : ℕ => (moserEpsSeq n + t) ^ (p / 2 - 1))
        atTop (nhds ((0 + t) ^ (p / 2 - 1))) := by
    have ht_ne : (0 : ℝ) + t ≠ 0 := by linarith
    simpa [zero_add] using hsum.rpow_const (Or.inl ht_ne)
  have hmul :
      Tendsto (fun n : ℕ => (p / 2) * (moserEpsSeq n + t) ^ (p / 2 - 1))
        atTop (nhds ((p / 2) * t ^ (p / 2 - 1))) := by
    simpa [zero_add] using Tendsto.const_mul (p / 2) hpow
  have heq :
      (fun n : ℕ => deriv (moserExactRegPow (moserEpsSeq n) N p) t) =ᶠ[atTop]
        (fun n : ℕ => (p / 2) * (moserEpsSeq n + t) ^ (p / 2 - 1)) := by
    exact Filter.Eventually.of_forall fun n => by
      simpa using
        (moserExactRegPow_deriv_eq_shifted (ε := moserEpsSeq n) (N := N) (p := p)
          (hε := moserEpsSeq_pos n) ht0 htN)
  exact Tendsto.congr' heq.symm hmul

omit [NeZero d] in
theorem moserExactRegPowerCutoff_tendsto_powerCutoff_of_support_bound
    {u η : E → ℝ} {N p : ℝ} {x : E}
    (hp : 1 < p)
    (hbound : x ∈ tsupport η → max (u x) 0 < N) :
    Tendsto (fun n : ℕ => moserExactRegPowerCutoff η u (moserEpsSeq n) N p x)
      atTop (nhds (moserPowerCutoff (d := d) η u p x)) := by
  by_cases hx : x ∈ tsupport η
  · have ht0 : 0 ≤ max (u x) 0 := le_max_right _ _
    have htN : max (u x) 0 < N := hbound hx
    have hpow :=
      moserExactRegPow_tendsto_rpow_of_nonneg_lt_N
        (N := N) (p := p) (t := max (u x) 0) ht0 htN hp
    have hmul : Tendsto
        (fun n : ℕ => η x * moserExactRegPow (moserEpsSeq n) N p (max (u x) 0))
        atTop
        (nhds (η x * (max (u x) 0) ^ (p / 2))) := by
      exact Tendsto.const_mul (η x) hpow
    simpa [moserExactRegPowerCutoff, moserPowerCutoff,
      abs_of_nonneg (show (0 : ℝ) ≤ max (u x) 0 by exact le_max_right _ _)] using hmul
  · have hηx : η x = 0 := image_eq_zero_of_notMem_tsupport hx
    simp [moserExactRegPowerCutoff, moserPowerCutoff, hηx]

omit [NeZero d] in
theorem moserExactRegRhs_tendsto
    {u : E → ℝ} {p : ℝ} {x : E}
    (hp : 1 < p) :
    Tendsto (fun n : ℕ => (moserEpsSeq n + |max (u x) 0|) ^ p)
      atTop (nhds (|max (u x) 0| ^ p)) := by
  have hp_nonneg : 0 ≤ p := by linarith
  have hsum :
      Tendsto (fun n : ℕ => moserEpsSeq n + |max (u x) 0|) atTop
        (nhds (0 + |max (u x) 0|)) :=
    tendsto_moserEpsSeq.add tendsto_const_nhds
  simpa [zero_add] using hsum.rpow_const (Or.inr hp_nonneg)

theorem moser_weighted_pointwise_core
    {Λ η ζ ψ ψd Q M : ℝ}
    (hΛ : 0 < Λ) (hψd : 0 < ψd)
    (hcoeff : |M| ^ 2 ≤ Λ * Q) :
    2 * η * |ψ| * ζ * |M| ≤
      (1 / 2 : ℝ) * η ^ 2 * ψd * Q + 2 * Λ * ζ ^ 2 * (|ψ| ^ 2 / ψd) := by
  let a : ℝ := η * |M| * Real.sqrt ψd / Real.sqrt (2 * Λ)
  let b : ℝ := Real.sqrt (2 * Λ) * ζ * |ψ| / Real.sqrt ψd
  have hyoung : 2 * a * b ≤ a ^ 2 + b ^ 2 := by
    nlinarith [sq_nonneg (a - b)]
  have hsqrtΛ_pos : 0 < Real.sqrt (2 * Λ) := by
    apply Real.sqrt_pos.2
    positivity
  have hsqrtΛ_ne : Real.sqrt (2 * Λ) ≠ 0 := hsqrtΛ_pos.ne'
  have hsqrtψd_pos : 0 < Real.sqrt ψd := Real.sqrt_pos.2 hψd
  have hsqrtψd_ne : Real.sqrt ψd ≠ 0 := hsqrtψd_pos.ne'
  have hsqrtΛ_sq : (Real.sqrt (2 * Λ)) ^ 2 = 2 * Λ := by
    rw [Real.sq_sqrt]
    positivity
  have hsqrtψd_sq : (Real.sqrt ψd) ^ 2 = ψd := by
    rw [Real.sq_sqrt hψd.le]
  have ha_sq :
      a ^ 2 = η ^ 2 * |M| ^ 2 * ψd / (2 * Λ) := by
    dsimp [a]
    rw [div_pow, mul_pow, mul_pow, hsqrtψd_sq, hsqrtΛ_sq]
  have hb_sq :
      b ^ 2 = 2 * Λ * ζ ^ 2 * (|ψ| ^ 2 / ψd) := by
    dsimp [b]
    rw [div_pow, mul_pow, mul_pow, hsqrtΛ_sq, hsqrtψd_sq]
    ring
  have hcoeff' :
      η ^ 2 * |M| ^ 2 * ψd / (2 * Λ) ≤ (1 / 2 : ℝ) * η ^ 2 * ψd * Q := by
    have hmul :
        (η ^ 2 * ψd / (2 * Λ)) * (|M| ^ 2) ≤
          (η ^ 2 * ψd / (2 * Λ)) * (Λ * Q) := by
      refine mul_le_mul_of_nonneg_left hcoeff ?_
      positivity
    have hfac :
        (η ^ 2 * ψd / (2 * Λ)) * (Λ * Q) =
          (1 / 2 : ℝ) * η ^ 2 * ψd * Q := by
      field_simp [hΛ.ne']
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hmul.trans_eq hfac
  have hmain :
      2 * η * |ψ| * ζ * |M| ≤
        η ^ 2 * |M| ^ 2 * ψd / (2 * Λ) + 2 * Λ * ζ ^ 2 * (|ψ| ^ 2 / ψd) := by
    have hconv : 2 * a * b = 2 * η * |ψ| * ζ * |M| := by
      dsimp [a, b]
      field_simp [hsqrtΛ_ne, hsqrtψd_ne]
    rwa [hconv, ha_sq, hb_sq] at hyoung
  have hsum :
      η ^ 2 * |M| ^ 2 * ψd / (2 * Λ) + 2 * Λ * ζ ^ 2 * (|ψ| ^ 2 / ψd) ≤
        (1 / 2 : ℝ) * η ^ 2 * ψd * Q + 2 * Λ * ζ ^ 2 * (|ψ| ^ 2 / ψd) := by
    nlinarith [hcoeff']
  exact hmain.trans hsum

theorem moser_weighted_absorb
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {Quad M η ζ ψ ψd : α → ℝ} {Λ : ℝ}
    (hΛ : 0 < Λ)
    (hcore :
      ∫ x, η x ^ 2 * ψd x * Quad x ∂μ ≤
        ∫ x, 2 * η x * |ψ x| * ζ x * |M x| ∂μ)
    (hcoeff : ∀ᵐ x ∂μ, |M x| ^ 2 ≤ Λ * Quad x)
    (hψd_pos : ∀ᵐ x ∂μ, 0 < ψd x)
    (hleft_int : Integrable (fun x => η x ^ 2 * ψd x * Quad x) μ)
    (hcross_int : Integrable (fun x => 2 * η x * |ψ x| * ζ x * |M x|) μ)
    (hbound_int : Integrable (fun x => ζ x ^ 2 * (|ψ x| ^ 2 / ψd x)) μ) :
    ∫ x, η x ^ 2 * ψd x * Quad x ∂μ ≤
      4 * Λ * ∫ x, ζ x ^ 2 * (|ψ x| ^ 2 / ψd x) ∂μ := by
  have hupper_pt :
      ∀ᵐ x ∂μ,
        2 * η x * |ψ x| * ζ x * |M x| ≤
          (1 / 2 : ℝ) * η x ^ 2 * ψd x * Quad x +
            2 * Λ * ζ x ^ 2 * (|ψ x| ^ 2 / ψd x) := by
    filter_upwards [hcoeff, hψd_pos] with x hx hψx
    exact moser_weighted_pointwise_core hΛ hψx hx
  have hupper_int :
      Integrable
        (fun x =>
          (1 / 2 : ℝ) * η x ^ 2 * ψd x * Quad x +
            2 * Λ * ζ x ^ 2 * (|ψ x| ^ 2 / ψd x)) μ := by
    simpa [mul_assoc, add_comm, add_left_comm, add_assoc] using
      (hleft_int.const_mul (1 / 2 : ℝ)).add (hbound_int.const_mul (2 * Λ))
  have hcross_bound :
      ∫ x, 2 * η x * |ψ x| * ζ x * |M x| ∂μ ≤
        ∫ x, (1 / 2 : ℝ) * η x ^ 2 * ψd x * Quad x +
          2 * Λ * ζ x ^ 2 * (|ψ x| ^ 2 / ψd x) ∂μ := by
    exact integral_mono_ae hcross_int hupper_int hupper_pt
  have hsplit :
      ∫ x, (1 / 2 : ℝ) * η x ^ 2 * ψd x * Quad x +
          2 * Λ * ζ x ^ 2 * (|ψ x| ^ 2 / ψd x) ∂μ =
        (1 / 2 : ℝ) * ∫ x, η x ^ 2 * ψd x * Quad x ∂μ +
          2 * Λ * ∫ x, ζ x ^ 2 * (|ψ x| ^ 2 / ψd x) ∂μ := by
    have hrewrite :
        (fun x =>
          (1 / 2 : ℝ) * η x ^ 2 * ψd x * Quad x +
            2 * Λ * ζ x ^ 2 * (|ψ x| ^ 2 / ψd x)) =
          (fun x =>
            ((1 / 2 : ℝ) * (η x ^ 2 * ψd x * Quad x)) +
              ((2 * Λ) * (ζ x ^ 2 * (|ψ x| ^ 2 / ψd x)))) := by
      funext x
      ring
    rw [hrewrite,
      integral_add (hleft_int.const_mul (1 / 2 : ℝ)) (hbound_int.const_mul (2 * Λ))]
    rw [integral_const_mul, integral_const_mul]
  have hmain :
      ∫ x, η x ^ 2 * ψd x * Quad x ∂μ ≤
        (1 / 2 : ℝ) * ∫ x, η x ^ 2 * ψd x * Quad x ∂μ +
          2 * Λ * ∫ x, ζ x ^ 2 * (|ψ x| ^ 2 / ψd x) ∂μ := by
    calc
      ∫ x, η x ^ 2 * ψd x * Quad x ∂μ
          ≤ ∫ x, 2 * η x * |ψ x| * ζ x * |M x| ∂μ := hcore
      _ ≤ ∫ x, (1 / 2 : ℝ) * η x ^ 2 * ψd x * Quad x +
            2 * Λ * ζ x ^ 2 * (|ψ x| ^ 2 / ψd x) ∂μ := hcross_bound
      _ = (1 / 2 : ℝ) * ∫ x, η x ^ 2 * ψd x * Quad x ∂μ +
            2 * Λ * ∫ x, ζ x ^ 2 * (|ψ x| ^ 2 / ψd x) ∂μ := hsplit
  linarith


end DeGiorgi
