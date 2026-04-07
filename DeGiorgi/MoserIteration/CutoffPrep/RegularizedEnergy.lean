import DeGiorgi.MoserIteration.CutoffPrep.RegularizedWitnesses

/-!
# Moser Regularized Energy

This module contains the regularized energy estimates for the Chapter 06 Moser iteration, including the exact-regularized main-ball bounds.
-/

noncomputable section

open MeasureTheory Filter

namespace DeGiorgi

variable {d : ℕ} [NeZero d]

local notation "E" => AmbientSpace d

/-! #### Sub-theorem B: Regularized energy bound

For fixed ε > 0, N > 0, the regularized powered cutoff satisfies the energy bound.
This follows the Chapter 05 De Giorgi expand-bound-absorb pattern:
1. Test the subsolution with `η² · moserRegTestPow ε N p (clip(u₊,N))`
2. Expand the bilinear form using the product/chain rule gradient structure
3. Use coercivity + Cauchy-Schwarz + Young to absorb cross terms -/

set_option maxHeartbeats 800000 in
/-- Pointwise gradient norm bound for the regularized powered cutoff.
Extracted as a standalone lemma to keep the surrounding proof context small. -/
lemma moserRegPowerCutoffWitness_norm_sq_le
    {u η : E → ℝ} {s ε N p Cη : ℝ}
    (hs : 0 < s) (hs1 : s ≤ 1) (hε : 0 < ε) (hN : 0 ≤ N)
    (hu1 : MemW1pWitness 2 u (Metric.ball (0 : E) 1))
    (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hη_bound : ∀ x, |η x| ≤ 1)
    (hη_grad_bound : ∀ x, ‖fderiv ℝ η x‖ ≤ Cη)
    (x : E) :
    ‖(moserRegPowerCutoffWitness (d := d) (p := p)
      hs hs1 hε hN hu1 hη hη_bound hη_grad_bound).weakGrad x‖ ^ 2 ≤
      2 * (η x ^ 2 * (deriv (moserRegPow ε N p) (min (max (u x) 0) N)) ^ 2 *
        ‖(moserClippedPosPartWitness (d := d) (u := u) hs hs1 hN hu1).weakGrad x‖ ^ 2) +
      2 * (‖fderiv ℝ η x‖ ^ 2 *
        (moserRegPow ε N p (min (max (u x) 0) N)) ^ 2) := by
  -- The gradient identity is callable now that the /-! comment is fixed.
  -- Componentwise: hwReg_i = η·α·clip_i + ∂ᵢη·β
  -- where α = deriv(moserRegPow)(clip), β = moserRegPow(clip).
  -- Also: hwComp_i = α · clip_i (from comp_smooth_bounded).
  -- So (hwReg_i)² = (η·α·clip_i + ∂ᵢη·β)² ≤ 2(η·α·clip_i)² + 2(∂ᵢη·β)²
  -- Summing: ‖hwReg‖² ≤ 2η²α²‖clip_grad‖² + 2β²‖∇η‖²
  let hwClip := moserClippedPosPartWitness (d := d) (u := u) hs hs1 hN hu1
  -- Componentwise bound
  have hterm : ∀ i : Fin d,
      (moserRegPowerCutoffWitness (d := d) (p := p)
        hs hs1 hε hN hu1 hη hη_bound hη_grad_bound).weakGrad x i ^ 2 ≤
      2 * (η x * deriv (moserRegPow ε N p) (min (max (u x) 0) N) *
        hwClip.weakGrad x i) ^ 2 +
      2 * ((fderiv ℝ η x) (EuclideanSpace.single i 1) *
        moserRegPow ε N p (min (max (u x) 0) N)) ^ 2 := by
    intro i
    -- Use gradient identity + comp_smooth_bounded unfolding
    have hgi := moserRegPowerCutoffWitness_grad (d := d) (p := p) hs hs1 hε hN hu1
      hη hη_bound hη_grad_bound x i
    have hcomp : (moserRegClippedPosPartWitness (d := d) (u := u) (p := p)
        hs hs1 hε hN hu1).weakGrad x i =
      deriv (moserRegPow ε N p) (min (max (u x) 0) N) * hwClip.weakGrad x i := by
      set_option maxHeartbeats 400000 in
      simp only [moserRegClippedPosPartWitness, MemW1pWitness.comp_smooth_bounded]
      ring
    rw [hgi, hcomp]
    nlinarith [sq_nonneg (η x * (deriv (moserRegPow ε N p) (min (max (u x) 0) N) *
      hwClip.weakGrad x i) -
      (fderiv ℝ η x) (EuclideanSpace.single i 1) *
      moserRegPow ε N p (min (max (u x) 0) N))]
  -- Convert ‖·‖² to Σᵢ and back using EuclideanSpace.norm_eq
  rw [EuclideanSpace.norm_eq (𝕜 := ℝ),
    Real.sq_sqrt (Finset.sum_nonneg fun i _ => by positivity)]
  simp_rw [Real.norm_eq_abs, sq_abs]
  rw [EuclideanSpace.norm_eq (𝕜 := ℝ) (hwClip.weakGrad x),
    Real.sq_sqrt (Finset.sum_nonneg fun i _ => by positivity)]
  simp_rw [Real.norm_eq_abs, sq_abs]
  -- Expand ‖fderiv ℝ η x‖² as sum
  rw [show ‖fderiv ℝ η x‖ ^ 2 = ∑ i : Fin d,
      ((fderiv ℝ η x) (EuclideanSpace.single i 1)) ^ 2 by
    rw [← moser_norm_fderivVec_eq_norm_fderiv (d := d) (η := η) (x := x),
      EuclideanSpace.norm_eq (𝕜 := ℝ),
      Real.sq_sqrt (Finset.sum_nonneg fun i _ => by positivity)]
    simp_rw [Real.norm_eq_abs, sq_abs, moserFderivVec_apply]]
  -- Sum the componentwise bounds and factor
  calc ∑ i, (moserRegPowerCutoffWitness (d := d) (p := p)
          hs hs1 hε hN hu1 hη hη_bound hη_grad_bound).weakGrad x i ^ 2
      ≤ ∑ i, (2 * (η x * deriv (moserRegPow ε N p) (min (max (u x) 0) N) *
            hwClip.weakGrad x i) ^ 2 +
          2 * ((fderiv ℝ η x) (EuclideanSpace.single i 1) *
            moserRegPow ε N p (min (max (u x) 0) N)) ^ 2) :=
        Finset.sum_le_sum fun i _ => hterm i
    _ = 2 * (η x ^ 2 * deriv (moserRegPow ε N p) (min (max (u x) 0) N) ^ 2 *
          ∑ i, hwClip.weakGrad x i ^ 2) +
        2 * ((∑ i, ((fderiv ℝ η x) (EuclideanSpace.single i 1)) ^ 2) *
          moserRegPow ε N p (min (max (u x) 0) N) ^ 2) := by
        have : ∀ i : Fin d,
            2 * (η x * deriv (moserRegPow ε N p) (min (max (u x) 0) N) *
              hwClip.weakGrad x i) ^ 2 +
            2 * ((fderiv ℝ η x) (EuclideanSpace.single i 1) *
              moserRegPow ε N p (min (max (u x) 0) N)) ^ 2 =
            2 * (η x ^ 2 * deriv (moserRegPow ε N p) (min (max (u x) 0) N) ^ 2 *
              (hwClip.weakGrad x i ^ 2)) +
            2 * (((fderiv ℝ η x) (EuclideanSpace.single i 1)) ^ 2 *
              moserRegPow ε N p (min (max (u x) 0) N) ^ 2) := by
          intro i; ring
        simp_rw [this, Finset.sum_add_distrib, ← Finset.mul_sum]
        simp [mul_comm, mul_left_comm, mul_assoc, ← Finset.mul_sum]

/-- For `0 ≤ t ≤ N`, the smooth clip satisfies `moserSmoothClip ε N t ≤ t`.
This uses the fact that `σ₁(N+1-t) = 1` when `t ≤ N` (since `N+1-t ≥ 1`),
so the formula reduces to `t · σ₀(t/ε)` which is `≤ t`. -/
theorem moserSmoothClip_le_of_nonneg_le_N
    {ε N t : ℝ} (_hε : 0 < ε) (_hN : 0 ≤ N) (ht0 : 0 ≤ t) (htN : t ≤ N) :
    moserSmoothClip ε N t ≤ t := by
  have hσ₁ : Real.smoothTransition (N + 1 - t) = 1 := by
    apply Real.smoothTransition.one_of_one_le
    linarith
  simp [moserSmoothClip, hσ₁]
  exact mul_le_of_le_one_right ht0 (Real.smoothTransition.le_one _)

/-- For `0 ≤ t ≤ N`, the smooth clip is nonneg. -/
theorem moserSmoothClip_nonneg_of_nonneg_le_N
    {ε N t : ℝ} (_hε : 0 < ε) (_hN : 0 ≤ N) (ht0 : 0 ≤ t) (htN : t ≤ N) :
    0 ≤ moserSmoothClip ε N t := by
  have hσ₁ : Real.smoothTransition (N + 1 - t) = 1 := by
    apply Real.smoothTransition.one_of_one_le; linarith
  simp [moserSmoothClip, hσ₁]
  exact mul_nonneg ht0 (Real.smoothTransition.nonneg _)

/-- `moserRegPow ε N p t` is nonneg for `0 ≤ t ≤ N` and `0 ≤ p`. -/
theorem moserRegPow_nonneg_of_nonneg_le_N
    {ε N p t : ℝ} (hε : 0 < ε) (hN : 0 ≤ N) (ht0 : 0 ≤ t) (htN : t ≤ N)
    (hp : 0 ≤ p) :
    0 ≤ moserRegPow ε N p t := by
  dsimp [moserRegPow]
  apply sub_nonneg.mpr
  have hclip_nn : 0 ≤ moserSmoothClip ε N t :=
    moserSmoothClip_nonneg_of_nonneg_le_N (ε := ε) (N := N) hε hN ht0 htN
  exact Real.rpow_le_rpow (by linarith) (by linarith) (by positivity)

/-- `moserRegPow ε N p t ≤ (ε + t) ^ (p / 2)` for `0 ≤ t ≤ N`, since
`moserRegPow t = (ε + clip(t))^{p/2} - ε^{p/2}` and `ε^{p/2} ≥ 0`. -/
theorem moserRegPow_le_rpow_of_nonneg_le_N
    {ε N p t : ℝ} (hε : 0 < ε) (hN : 0 ≤ N) (ht0 : 0 ≤ t) (htN : t ≤ N)
    (hp : 0 < p) :
    moserRegPow ε N p t ≤ (ε + t) ^ (p / 2) := by
  dsimp [moserRegPow]
  have hclip_le : moserSmoothClip ε N t ≤ t :=
    moserSmoothClip_le_of_nonneg_le_N (ε := ε) (N := N) hε hN ht0 htN
  have hclip_nn : 0 ≤ moserSmoothClip ε N t :=
    moserSmoothClip_nonneg_of_nonneg_le_N (ε := ε) (N := N) hε hN ht0 htN
  have h1 : (ε + moserSmoothClip ε N t) ^ (p / 2) ≤ (ε + t) ^ (p / 2) :=
    Real.rpow_le_rpow (by linarith) (by linarith) (by positivity)
  linarith [Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ ε) (p / 2)]

/-- `moserRegPow ε N p t ^ 2 ≤ (ε + t) ^ p` for `0 ≤ t ≤ N` and `1 < p`.
Since `0 ≤ moserRegPow ≤ (ε + t)^{p/2}`, squaring gives `≤ ((ε + t)^{p/2})^2 = (ε + t)^p`. -/
theorem moserRegPow_sq_le_rpow_of_nonneg_le_N
    {ε N p t : ℝ} (hε : 0 < ε) (hN : 0 ≤ N) (ht0 : 0 ≤ t) (htN : t ≤ N)
    (hp : 1 < p) :
    moserRegPow ε N p t ^ 2 ≤ (ε + t) ^ p := by
  have hp0 : 0 < p := by linarith
  have hle : moserRegPow ε N p t ≤ (ε + t) ^ (p / 2) :=
    moserRegPow_le_rpow_of_nonneg_le_N hε hN ht0 htN hp0
  have hnn : 0 ≤ moserRegPow ε N p t :=
    moserRegPow_nonneg_of_nonneg_le_N hε hN ht0 htN (by linarith)
  have hbase : 0 ≤ ε + t := by linarith
  calc moserRegPow ε N p t ^ 2
      ≤ ((ε + t) ^ (p / 2)) ^ 2 := sq_le_sq' (by linarith) hle
    _ = (ε + t) ^ p := by
        rw [← Real.rpow_natCast ((ε + t) ^ (p / 2)) 2, ← Real.rpow_mul hbase]
        congr 1; ring

theorem moserExactReg_core_eq_ae
    {Ω : Set E}
    (Aρ : NormalizedEllipticCoeff d Ω)
    {u η : E → ℝ} {p Cη ε N : ℝ}
    [DecidablePred fun x => x ∈ tsupport η]
    (hΩ : IsOpen Ω)
    (hsub : Ω ⊆ Metric.ball (0 : E) 1)
    (hu1 : MemW1pWitness 2 u (Metric.ball (0 : E) 1))
    (hε : 0 < ε) (hN : 0 ≤ N)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hη_bound : ∀ x, |η x| ≤ 1)
    (hη_grad_bound : ∀ x, ‖fderiv ℝ η x‖ ≤ Cη) :
    let huρ : MemW1pWitness 2 u Ω := hu1.restrict hΩ hsub
    let hwPosBig : MemW1pWitness 2 (fun x => max (u x) 0) (Metric.ball (0 : E) 1) :=
      moserPosPartWitnessUnitBall (d := d) (u := u) hu1
    let hwPos : MemW1pWitness 2 (fun x => max (u x) 0) Ω :=
      hwPosBig.restrict hΩ hsub
    let hwφBig : MemW1pWitness 2 (moserExactRegTestCutoff η u ε N p) (Metric.ball (0 : E) 1) :=
      moserExactRegTestCutoffWitness (d := d) (u := u) (η := η) (ε := ε) (N := N) (p := p)
        (Cη := Cη) hε hN hu1 hη hη_bound hη_grad_bound
    let hwφ : MemW1pWitness 2 (moserExactRegTestCutoff η u ε N p) Ω :=
      hwφBig.restrict hΩ hsub
    let ψ : E → ℝ := fun x => moserExactRegTestPow ε N p (max (u x) 0)
    let ψd : E → ℝ := fun x =>
      if x ∈ tsupport η then
        deriv (moserExactRegTestPow ε N p) (max (u x) 0)
      else 1
    let Equad : E → ℝ := bilinFormIntegrandOfCoeff Aρ.1 hwPos hwPos
    let leftTerm : E → ℝ := fun x => η x ^ 2 * ψd x * Equad x
    let crossInner : E → ℝ := fun x =>
      (2 * η x * ψ x) *
        inner ℝ (matMulE (Aρ.1.a x) (hwPos.weakGrad x)) (moserFderivVec η x)
    let coreIntegrand : E → ℝ := fun x => leftTerm x + crossInner x
    coreIntegrand =ᵐ[volume.restrict Ω] bilinFormIntegrandOfCoeff Aρ.1 huρ hwφ := by
  classical
  let huρ : MemW1pWitness 2 u Ω := hu1.restrict hΩ hsub
  let hwPosBig : MemW1pWitness 2 (fun x => max (u x) 0) (Metric.ball (0 : E) 1) :=
    moserPosPartWitnessUnitBall (d := d) (u := u) hu1
  let hwPos : MemW1pWitness 2 (fun x => max (u x) 0) Ω :=
    hwPosBig.restrict hΩ hsub
  let hwφBig : MemW1pWitness 2 (moserExactRegTestCutoff η u ε N p) (Metric.ball (0 : E) 1) :=
    moserExactRegTestCutoffWitness (d := d) (u := u) (η := η) (ε := ε) (N := N) (p := p)
      (Cη := Cη) hε hN hu1 hη hη_bound hη_grad_bound
  let hwφ : MemW1pWitness 2 (moserExactRegTestCutoff η u ε N p) Ω :=
    hwφBig.restrict hΩ hsub
  let ψ : E → ℝ := fun x => moserExactRegTestPow ε N p (max (u x) 0)
  let ψd : E → ℝ := fun x =>
    if x ∈ tsupport η then
      deriv (moserExactRegTestPow ε N p) (max (u x) 0)
    else 1
  let Equad : E → ℝ := bilinFormIntegrandOfCoeff Aρ.1 hwPos hwPos
  let leftTerm : E → ℝ := fun x => η x ^ 2 * ψd x * Equad x
  let crossInner : E → ℝ := fun x =>
    (2 * η x * ψ x) *
      inner ℝ (matMulE (Aρ.1.a x) (hwPos.weakGrad x)) (moserFderivVec η x)
  let coreIntegrand : E → ℝ := fun x => leftTerm x + crossInner x
  change coreIntegrand =ᵐ[volume.restrict Ω] bilinFormIntegrandOfCoeff Aρ.1 huρ hwφ
  have hsuper_ρ_raw :=
    moserPosPartWitness_restrict_grad_eq_on_pos
      (d := d) (Ω := Ω) (u := u) hΩ hsub hu1
  have hsublevel_ρ_raw :=
    moserPosPartWitness_restrict_grad_zero_on_nonpos
      (d := d) (Ω := Ω) (u := u) hΩ hsub hu1
  have hpos_cases_ρ := hsuper_ρ_raw.and hsublevel_ρ_raw
  refine hpos_cases_ρ.mono ?_
  intro x hx
  rcases hx with ⟨hsuperx, hsublevelx⟩
  by_cases hx : x ∈ tsupport η
  · by_cases hux : 0 < u x
    · have hgrad_eq : huρ.weakGrad x = hwPos.weakGrad x := by
        change
          (hu1.restrict hΩ hsub).weakGrad x =
            ((moserPosPartWitnessUnitBall (d := d) (u := u) hu1).restrict hΩ hsub).weakGrad x
        exact (hsuperx hux).symm
      have hψd_eq : ψd x = deriv (moserExactRegTestPow ε N p) (max (u x) 0) := by
        simp [ψd, hx]
      have hφformula :
          hwφ.weakGrad x =
            (2 * η x * ψ x) • moserFderivVec η x +
              (η x ^ 2 * deriv (moserExactRegTestPow ε N p) (max (u x) 0)) • hwPos.weakGrad x := by
        apply PiLp.ext
        intro i
        change hwφBig.weakGrad x i =
          (2 * η x * ψ x) * moserFderivVec η x i +
            (η x ^ 2 * deriv (moserExactRegTestPow ε N p) (max (u x) 0)) *
              hwPosBig.weakGrad x i
        simpa [ψ, moserFderivVec_apply, hwφBig, hwPosBig, mul_assoc, mul_left_comm, mul_comm] using
          (moserExactRegTestCutoffWitness_grad (d := d) (u := u) (η := η) (ε := ε) (N := N)
            (p := p) (Cη := Cη) hε hN hu1 hη hη_bound hη_grad_bound x i)
      symm
      calc
        bilinFormIntegrandOfCoeff Aρ.1 huρ hwφ x
            = inner ℝ (matMulE (Aρ.1.a x) (hwPos.weakGrad x))
                ((2 * η x * ψ x) • moserFderivVec η x +
                  (η x ^ 2 * deriv (moserExactRegTestPow ε N p) (max (u x) 0)) •
                    hwPos.weakGrad x) := by
                rw [bilinFormIntegrandOfCoeff, hgrad_eq, hφformula]
        _ = (2 * η x * ψ x) *
              inner ℝ (matMulE (Aρ.1.a x) (hwPos.weakGrad x)) (moserFderivVec η x) +
            (η x ^ 2 * deriv (moserExactRegTestPow ε N p) (max (u x) 0)) *
              inner ℝ (matMulE (Aρ.1.a x) (hwPos.weakGrad x)) (hwPos.weakGrad x) := by
                rw [inner_add_right, inner_smul_right, inner_smul_right]
        _ = crossInner x + leftTerm x := by
              dsimp [crossInner, leftTerm, Equad, bilinFormIntegrandOfCoeff]
              rw [hψd_eq]
        _ = coreIntegrand x := by
              dsimp [coreIntegrand]
              ring
    · have hunonpos : u x ≤ 0 := not_lt.mp hux
      have hgrad_zero : hwPos.weakGrad x = 0 := by
        change
          ((moserPosPartWitnessUnitBall (d := d) (u := u) hu1).restrict hΩ hsub).weakGrad x = 0
        exact hsublevelx hunonpos
      have hψ_zero : ψ x = 0 := by
        simp [ψ, max_eq_right hunonpos, moserExactRegTestPow_zero (ε := ε) (N := N) (p := p) hε hN]
      have hEquad_zero : Equad x = 0 := by
        simp [Equad, bilinFormIntegrandOfCoeff, hgrad_zero]
      have hφgrad_zero : hwφ.weakGrad x = 0 := by
        have hφformula :
            hwφ.weakGrad x =
              (2 * η x * ψ x) • moserFderivVec η x +
                (η x ^ 2 * deriv (moserExactRegTestPow ε N p) (max (u x) 0)) • hwPos.weakGrad x := by
          apply PiLp.ext
          intro i
          change hwφBig.weakGrad x i =
            (2 * η x * ψ x) * moserFderivVec η x i +
              (η x ^ 2 * deriv (moserExactRegTestPow ε N p) (max (u x) 0)) *
                hwPosBig.weakGrad x i
          simpa [ψ, moserFderivVec_apply, hwφBig, hwPosBig, mul_assoc, mul_left_comm, mul_comm] using
            (moserExactRegTestCutoffWitness_grad (d := d) (u := u) (η := η) (ε := ε) (N := N)
              (p := p) (Cη := Cη) hε hN hu1 hη hη_bound hη_grad_bound x i)
        rw [hφformula, hgrad_zero, hψ_zero]
        simp
      symm
      calc
        bilinFormIntegrandOfCoeff Aρ.1 huρ hwφ x = 0 := by
          rw [bilinFormIntegrandOfCoeff, hφgrad_zero]
          simp
        _ = coreIntegrand x := by
          dsimp [coreIntegrand, leftTerm, crossInner]
          rw [hEquad_zero, hψ_zero]
          simp
  · have hηx : η x = 0 := image_eq_zero_of_notMem_tsupport hx
    have hφgrad_zero : hwφ.weakGrad x = 0 := by
      apply PiLp.ext
      intro i
      have hformula :
          hwφ.weakGrad x i =
            2 * η x * (fderiv ℝ η x) (EuclideanSpace.single i 1) *
              moserExactRegTestPow ε N p (max (u x) 0) +
            η x ^ 2 * deriv (moserExactRegTestPow ε N p) (max (u x) 0) *
              hwPosBig.weakGrad x i := by
        simpa [hwφ, hwφBig, hwPosBig] using
          (moserExactRegTestCutoffWitness_grad (d := d) (u := u) (η := η) (ε := ε) (N := N)
            (p := p) (Cη := Cη) hε hN hu1 hη hη_bound hη_grad_bound x i)
      rw [hformula]
      have hfdi_zero :
          (fderiv ℝ η x) (EuclideanSpace.single i 1) = 0 := by
        exact fderiv_apply_zero_outside_of_tsupport_subset
          (Ω := tsupport η) (hf := hη) (hsub := subset_rfl) hx i
      simp [hηx, hfdi_zero]
    symm
    calc
      bilinFormIntegrandOfCoeff Aρ.1 huρ hwφ x = 0 := by
        rw [bilinFormIntegrandOfCoeff, hφgrad_zero]
        simp
      _ = coreIntegrand x := by
        dsimp [coreIntegrand, leftTerm, crossInner]
        rw [hηx]
        ring

set_option maxHeartbeats 1000000 in
theorem moser_exact_regularized_energy_bound
    (A : NormalizedEllipticCoeff d (Metric.ball (0 : E) 1))
    {u η : E → ℝ} {p ρ Cη ε N : ℝ}
    (hp : 1 < p)
    (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hε : 0 < ε) (hN : 0 ≤ N)
    (hsub : IsSubsolution A.1 u)
    (hu1 : MemW1pWitness 2 u (Metric.ball (0 : E) 1))
    (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hη_nonneg : ∀ x, 0 ≤ η x)
    (hη_bound : ∀ x, |η x| ≤ 1)
    (hη_grad_bound : ∀ x, ‖fderiv ℝ η x‖ ≤ Cη)
    (hη_sub_ball : tsupport η ⊆ Metric.ball (0 : E) ρ)
    (hqual :
      ∀ᵐ x ∂(volume.restrict (Metric.ball (0 : E) ρ)),
        x ∈ tsupport η → max (u x) 0 < N)
    (hpInt : IntegrableOn (fun x => (ε + |max (u x) 0|) ^ p)
        (Metric.ball (0 : E) ρ) volume) :
    let hwReg := moserExactRegPowerCutoffWitness (d := d) (u := u) (η := η)
      (ε := ε) (N := N) (p := p) (Cη := Cη)
      hε hN hu1 hη hη_bound hη_grad_bound
    ∫ x in Metric.ball (0 : E) ρ, ‖hwReg.weakGrad x‖ ^ 2 ∂volume ≤
      2 * Cη ^ 2 * (A.1.Λ * (p / (p - 1)) ^ 2 + 1) *
        ∫ x in Metric.ball (0 : E) ρ, (ε + |max (u x) 0|) ^ p ∂volume := by
  classical
  intro hwReg
  let Ω : Set E := Metric.ball (0 : E) ρ
  let μ : Measure E := volume.restrict Ω
  have hball_sub : Ω ⊆ Metric.ball (0 : E) 1 :=
    Metric.ball_subset_ball (le_of_lt hρ1)
  let Aρ : NormalizedEllipticCoeff d Ω :=
    NormalizedEllipticCoeff.restrict A (Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_ball hρ1))
  let huρ : MemW1pWitness 2 u Ω :=
    hu1.restrict Metric.isOpen_ball hball_sub
  let hwPosBig : MemW1pWitness 2 (fun x => max (u x) 0) (Metric.ball (0 : E) 1) :=
    moserPosPartWitnessUnitBall (d := d) (u := u) hu1
  let hwPos : MemW1pWitness 2 (fun x => max (u x) 0) Ω :=
    hwPosBig.restrict Metric.isOpen_ball hball_sub
  let hwφBig : MemW1pWitness 2 (moserExactRegTestCutoff η u ε N p) (Metric.ball (0 : E) 1) :=
    moserExactRegTestCutoffWitness (d := d) (u := u) (η := η) (ε := ε) (N := N) (p := p)
      (Cη := Cη) hε hN hu1 hη hη_bound hη_grad_bound
  let hwφ : MemW1pWitness 2 (moserExactRegTestCutoff η u ε N p) Ω :=
    hwφBig.restrict Metric.isOpen_ball hball_sub
  let hwRegρ : MemW1pWitness 2 (moserExactRegPowerCutoff η u ε N p) Ω :=
    hwReg.restrict Metric.isOpen_ball hball_sub
  have hsubρ : IsSubsolution Aρ.1 u := by
    simpa [Aρ] using
      isSubsolution_restrict_ball (d := d) (Ω := Metric.ball (0 : E) 1)
        Metric.isOpen_ball (c := (0 : E)) (r := ρ) hρ (Metric.closedBall_subset_ball hρ1) hsub
  have hφ0 : MemH01 (moserExactRegTestCutoff η u ε N p) Ω := by
    simpa [Ω] using
      moserExactRegTestCutoff_memH01_on_ball (d := d) (u := u) (η := η)
        (ρ := ρ) (ε := ε) (N := N) (p := p) (Cη := Cη)
        hρ hρ1 hε hN hu1 hη hη_bound hη_grad_bound hη_sub_ball
  have hsub_test :
      bilinFormOfCoeff Aρ.1 huρ hwφ ≤ 0 := by
    exact hsubρ.2 huρ _ hφ0 hwφ
      (moserExactRegTestCutoff_nonneg_global (u := u) (η := η) (ε := ε) (N := N) (p := p)
        hε hN hp hη_nonneg)
  let ψ : E → ℝ := fun x => moserExactRegTestPow ε N p (max (u x) 0)
  let ψd : E → ℝ := fun x =>
    if x ∈ tsupport η then
      deriv (moserExactRegTestPow ε N p) (max (u x) 0)
    else 1
  let Equad : E → ℝ := bilinFormIntegrandOfCoeff Aρ.1 hwPos hwPos
  let leftTerm : E → ℝ := fun x => η x ^ 2 * ψd x * Equad x
  let gradEtaNorm : E → ℝ := fun x => ‖fderiv ℝ η x‖
  let fluxNorm : E → ℝ := fun x => ‖matMulE (Aρ.1.a x) (hwPos.weakGrad x)‖
  let boundTerm : E → ℝ := fun x => gradEtaNorm x ^ 2 * (|ψ x| ^ 2 / ψd x)
  let crossAbs : E → ℝ := fun x => 2 * η x * |ψ x| * gradEtaNorm x * |fluxNorm x|
  let crossInner : E → ℝ := fun x =>
    (2 * η x * ψ x) *
      inner ℝ (matMulE (Aρ.1.a x) (hwPos.weakGrad x)) (moserFderivVec η x)
  let coreIntegrand : E → ℝ := fun x => leftTerm x + crossInner x
  have hCη_nonneg : 0 ≤ Cη := by
    exact le_trans (norm_nonneg _) (hη_grad_bound (0 : E))
  have hmaxu_aemeas : AEMeasurable (fun x => max (u x) 0) μ := by
    exact huρ.memLp.aestronglyMeasurable.aemeasurable.max measurable_const.aemeasurable
  have hψ_meas : Measurable (moserExactRegTestPow ε N p) := by
    exact (moserExactRegTestPow_contDiff (ε := ε) (N := N) (p := p) hε hN).continuous.measurable
  have hψ_aemeas : AEMeasurable ψ μ := by
    exact hψ_meas.comp_aemeasurable hmaxu_aemeas
  have hψd_raw_aemeas :
      AEMeasurable (fun x => deriv (moserExactRegTestPow ε N p) (max (u x) 0)) μ := by
    have hcont :
        Continuous (deriv (moserExactRegTestPow ε N p)) := by
      have h1 : ContDiff ℝ 1 (moserExactRegTestPow ε N p) :=
        (moserExactRegTestPow_contDiff (ε := ε) (N := N) (p := p) hε hN).of_le (by simp)
      exact h1.continuous_deriv_one
    exact hcont.measurable.comp_aemeasurable hmaxu_aemeas
  have hα_raw_aemeas :
      AEMeasurable (fun x => deriv (moserExactRegPow ε N p) (max (u x) 0)) μ := by
    have hcont :
        Continuous (deriv (moserExactRegPow ε N p)) := by
      have h1 : ContDiff ℝ 1 (moserExactRegPow ε N p) :=
        (moserExactRegPow_contDiff (ε := ε) (N := N) (p := p) hε hN).of_le (by simp)
      exact h1.continuous_deriv_one
    exact hcont.measurable.comp_aemeasurable hmaxu_aemeas
  have hβ_meas : Measurable (moserExactRegPow ε N p) := by
    exact (moserExactRegPow_contDiff (ε := ε) (N := N) (p := p) hε hN).continuous.measurable
  have hβ_aemeas :
      AEMeasurable (fun x => moserExactRegPow ε N p (max (u x) 0)) μ := by
    exact hβ_meas.comp_aemeasurable hmaxu_aemeas
  have hψd_aemeas : AEMeasurable ψd μ := by
    rcases hψd_raw_aemeas with ⟨g, hg_meas, hg_ae⟩
    refine ⟨Set.piecewise (tsupport η) g (fun _ => (1 : ℝ)),
      hg_meas.piecewise (isClosed_tsupport η).measurableSet measurable_const, ?_⟩
    filter_upwards [hg_ae] with x hxg
    by_cases hx : x ∈ tsupport η
    · simp [ψd, hx, hxg]
    · simp [ψd, hx]
  have hψd_aestr : AEStronglyMeasurable ψd μ := by
    exact hψd_aemeas.aestronglyMeasurable
  have hgradEtaNorm_aemeas : AEMeasurable gradEtaNorm μ := by
    exact (hη.continuous_fderiv (by simp : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0)).norm.aemeasurable
  have hfluxNorm_aemeas : AEMeasurable fluxNorm μ := by
    exact
      (moser_aestronglyMeasurable_matMulE Aρ.1 hwPos.weakGrad_memLp.aestronglyMeasurable).norm.aemeasurable
  have hψ_nonneg : ∀ x, 0 ≤ ψ x := by
    intro x
    exact moserExactRegTestPow_nonneg_of_nonneg (ε := ε) (N := N) (p := p)
      hε hN (le_max_right _ _) hp
  have hweighted_grad_sq_int :
      Integrable (fun x => η x ^ 2 * ‖hwPos.weakGrad x‖ ^ 2) μ := by
    have hbase : Integrable (fun x => ‖hwPos.weakGrad x‖ ^ 2) μ := by
      simpa [pow_two, μ] using hwPos.weakGrad_norm_memLp.integrable_sq
    refine Integrable.mono' hbase ?_ ?_
    · exact
        (((hη.continuous.pow 2).aemeasurable).mul
          hbase.aestronglyMeasurable.aemeasurable).aestronglyMeasurable
    · filter_upwards with x
      have hη_sq_le : η x ^ 2 ≤ 1 := by
        have hη_sq_le' : η x ^ 2 ≤ (1 : ℝ) ^ 2 := by
          exact sq_le_sq.mpr (by simpa using hη_bound x)
        simpa using hη_sq_le'
      have hgrad_nonneg : 0 ≤ ‖hwPos.weakGrad x‖ ^ 2 := by positivity
      have hterm_nonneg : 0 ≤ η x ^ 2 * ‖hwPos.weakGrad x‖ ^ 2 := by positivity
      have hle :
          η x ^ 2 * ‖hwPos.weakGrad x‖ ^ 2 ≤ ‖hwPos.weakGrad x‖ ^ 2 := by
        simpa [one_mul] using mul_le_mul_of_nonneg_right hη_sq_le hgrad_nonneg
      simpa [Real.norm_eq_abs, abs_of_nonneg hterm_nonneg] using hle
  obtain ⟨Mψd, hMψd⟩ :=
    moserExactRegTestPow_deriv_bounded (ε := ε) (N := N) (p := p) hε hN
  let Kψd : ℝ := max 1 (|Mψd|)
  have hleft_int :
      Integrable leftTerm μ := by
    refine Integrable.mono' ((hweighted_grad_sq_int.const_mul (Aρ.1.Λ * Kψd))) ?_ ?_
    · exact
        ((((hη.continuous.pow 2).aemeasurable).mul hψd_aemeas).mul
          (aestronglyMeasurable_bilinFormIntegrandOfCoeff Aρ.1 hwPos hwPos).aemeasurable).aestronglyMeasurable
    · filter_upwards [Aρ.1.quadratic_upper, Aρ.1.ae_coercive_nonneg] with x hx_quad hx_nonneg
      by_cases hx : x ∈ tsupport η
      · have hψd_eq : ψd x = deriv (moserExactRegTestPow ε N p) (max (u x) 0) := by
          simp [ψd, hx]
        have hψd_abs_le : |ψd x| ≤ Kψd := by
          rw [hψd_eq]
          calc
            |deriv (moserExactRegTestPow ε N p) (max (u x) 0)| ≤ Mψd := hMψd _
            _ ≤ |Mψd| := le_abs_self _
            _ ≤ Kψd := le_max_right _ _
        have hquad :
            Equad x ≤ Aρ.1.Λ * ‖hwPos.weakGrad x‖ ^ 2 := by
          simpa [Equad, bilinFormIntegrandOfCoeff, real_inner_comm] using
            hx_quad (hwPos.weakGrad x)
        have hEquad_nonneg : 0 ≤ Equad x := by
          simpa [Equad, bilinFormIntegrandOfCoeff, real_inner_comm] using
            hx_nonneg (hwPos.weakGrad x)
        have hKψd_nonneg : 0 ≤ Kψd := by
          exact le_trans zero_le_one (le_max_left _ _)
        have hrhs_nonneg :
            0 ≤ (Aρ.1.Λ * Kψd) * (η x ^ 2 * ‖hwPos.weakGrad x‖ ^ 2) := by
          exact mul_nonneg (mul_nonneg Aρ.1.Λ_pos.le hKψd_nonneg) (by positivity)
        have hη_sq_nonneg : 0 ≤ η x ^ 2 := by positivity
        have hpoint :
            ‖leftTerm x‖ ≤ (Aρ.1.Λ * Kψd) * (η x ^ 2 * ‖hwPos.weakGrad x‖ ^ 2) := by
          calc
            ‖leftTerm x‖ = |η x ^ 2 * ψd x * Equad x| := by
              simp [leftTerm]
            _ = η x ^ 2 * |ψd x| * Equad x := by
              rw [abs_mul, abs_mul, abs_of_nonneg hη_sq_nonneg, abs_of_nonneg hEquad_nonneg]
            _ ≤ η x ^ 2 * Kψd * (Aρ.1.Λ * ‖hwPos.weakGrad x‖ ^ 2) := by
              gcongr
            _ = (Aρ.1.Λ * Kψd) * (η x ^ 2 * ‖hwPos.weakGrad x‖ ^ 2) := by ring
        have hrhs_eq :
            (Aρ.1.Λ * Kψd) * (η x ^ 2 * ‖hwPos.weakGrad x‖ ^ 2) =
              ‖(Aρ.1.Λ * Kψd) * (η x ^ 2 * ‖hwPos.weakGrad x‖ ^ 2)‖ := by
          symm
          rw [Real.norm_eq_abs, abs_of_nonneg hrhs_nonneg]
        exact hpoint
      · have hηx : η x = 0 := image_eq_zero_of_notMem_tsupport hx
        simp [leftTerm, ψd, hx, hηx]
  have hψd_pos :
      ∀ᵐ x ∂μ, 0 < ψd x := by
    filter_upwards [hqual] with x hxqual
    by_cases hx : x ∈ tsupport η
    · have hboundx : max (u x) 0 < N := hxqual hx
      have hpos :=
        moserExactRegTestPow_deriv_pos_of_support_bound (u := u) (x := x)
          (ε := ε) (N := N) (p := p) hε hp hboundx
      simpa [ψd, hx] using hpos
    · simp [ψd, hx]
  have hbound_int :
      Integrable boundTerm μ := by
    refine Integrable.mono' (hpInt.const_mul (Cη ^ 2 / (p - 1))) ?_ ?_
    · exact
        ((((hgradEtaNorm_aemeas.pow aemeasurable_const).mul
          (((hψ_aemeas.norm).pow aemeasurable_const).div hψd_aemeas))).aestronglyMeasurable)
    · filter_upwards [hqual] with x hxqual
      by_cases hx : x ∈ tsupport η
      · have hboundx : max (u x) 0 < N := hxqual hx
        have hp1 : 0 < p - 1 := by linarith
        have hgrad_sq_le : gradEtaNorm x ^ 2 ≤ Cη ^ 2 := by
          have := hη_grad_bound x
          exact sq_le_sq.mpr (by
            simp [gradEtaNorm, abs_of_nonneg (norm_nonneg _), abs_of_nonneg hCη_nonneg, this])
        have hψdpos : 0 < ψd x := by
          have hbase :=
            moserExactRegTestPow_deriv_pos_of_support_bound (u := u) (x := x)
              (ε := ε) (N := N) (p := p) hε hp hboundx
          simpa [ψd, hx] using hbase
        have hquot_le :
            |ψ x| ^ 2 / ψd x ≤ (ε + |max (u x) 0|) ^ p / (p - 1) := by
          have hbase :=
            moserExactRegTestPow_sq_div_deriv_le_rpow_of_support_bound (u := u) (x := x)
              (ε := ε) (N := N) (p := p) hε hp hboundx
          have hψd_eq : ψd x = deriv (moserExactRegTestPow ε N p) (max (u x) 0) := by
            simp [ψd, hx]
          have hψ_eq : |ψ x| = ψ x := by
            rw [abs_of_nonneg (hψ_nonneg x)]
          simpa [ψ, hψd_eq, hψ_eq] using hbase
        have hquot_nonneg : 0 ≤ |ψ x| ^ 2 / ψd x := by
          exact div_nonneg (by positivity) hψdpos.le
        have hterm_nonneg : 0 ≤ boundTerm x := by
          exact mul_nonneg (sq_nonneg _) hquot_nonneg
        have hdom_nonneg :
            0 ≤ (Cη ^ 2 / (p - 1)) * (ε + |max (u x) 0|) ^ p := by
          exact mul_nonneg (div_nonneg (sq_nonneg _) hp1.le) (Real.rpow_nonneg (by positivity) _)
        have hmul_le :
            boundTerm x ≤ Cη ^ 2 * ((ε + |max (u x) 0|) ^ p / (p - 1)) := by
          exact mul_le_mul hgrad_sq_le hquot_le hquot_nonneg (sq_nonneg _)
        have hpoint :
            ‖boundTerm x‖ ≤ (Cη ^ 2 / (p - 1)) * (ε + |max (u x) 0|) ^ p := by
          calc
            ‖boundTerm x‖ = boundTerm x := by
              rw [Real.norm_eq_abs, abs_of_nonneg hterm_nonneg]
            _ ≤ Cη ^ 2 * ((ε + |max (u x) 0|) ^ p / (p - 1)) := hmul_le
            _ = (Cη ^ 2 / (p - 1)) * (ε + |max (u x) 0|) ^ p := by
              field_simp [show p - 1 ≠ 0 by linarith]
        have hrhs_eq :
            (Cη ^ 2 / (p - 1)) * (ε + |max (u x) 0|) ^ p =
              ‖(Cη ^ 2 / (p - 1)) * (ε + |max (u x) 0|) ^ p‖ := by
          symm
          rw [Real.norm_eq_abs, abs_of_nonneg hdom_nonneg]
        exact hpoint
      · have hgrad_zero : gradEtaNorm x = 0 := by
          simpa [gradEtaNorm] using moser_fderiv_norm_zero_outside_tsupport (d := d) (f := η) hη hx
        have hp1 : 0 < p - 1 := by linarith
        have hdom_nonneg :
            0 ≤ (Cη ^ 2 / (p - 1)) * (ε + |max (u x) 0|) ^ p := by
          exact mul_nonneg (div_nonneg (sq_nonneg _) hp1.le) (Real.rpow_nonneg (by positivity) _)
        simpa [boundTerm, hgrad_zero, Real.norm_eq_abs, abs_of_nonneg hdom_nonneg]
  have hcoeff :
      ∀ᵐ x ∂μ, |fluxNorm x| ^ 2 ≤ Aρ.1.Λ * Equad x := by
    filter_upwards [Aρ.1.mulVec_sq_le] with x hx
    simpa [fluxNorm, Equad, bilinFormIntegrandOfCoeff, real_inner_comm] using
      hx (hwPos.weakGrad x)
  have hcross_upper_pt :
      ∀ᵐ x ∂μ,
        crossAbs x ≤
          (1 / 2 : ℝ) * leftTerm x + 2 * Aρ.1.Λ * boundTerm x := by
    filter_upwards [hcoeff, hψd_pos] with x hx hψx
    have hx' :=
      moser_weighted_pointwise_core
        (Λ := Aρ.1.Λ) (η := η x) (ζ := gradEtaNorm x) (ψ := ψ x)
        (ψd := ψd x) (Q := Equad x) (M := fluxNorm x) Aρ.1.Λ_pos hψx hx
    dsimp [crossAbs, leftTerm, boundTerm, gradEtaNorm, fluxNorm] at hx' ⊢
    ring_nf at hx' ⊢
    exact hx'
  have hcross_upper_int :
      Integrable
        (fun x =>
          (1 / 2 : ℝ) * leftTerm x + 2 * Aρ.1.Λ * boundTerm x) μ := by
    have htmp :
        Integrable (fun x => 2 * ((Aρ.1.Λ * boundTerm x)) + (1 / 2 : ℝ) * leftTerm x) μ := by
      simpa [mul_assoc] using
        (hbound_int.const_mul (2 * Aρ.1.Λ)).add (hleft_int.const_mul (1 / 2 : ℝ))
    simpa [mul_assoc, add_comm, add_left_comm, add_assoc] using htmp
  have hcrossAbs_int :
      Integrable crossAbs μ := by
    refine Integrable.mono' hcross_upper_int ?_ ?_
    · exact
        (by
          simpa [crossAbs, mul_assoc, mul_left_comm, mul_comm] using
            (((((hη.continuous.aemeasurable).mul hψ_aemeas.norm).mul hgradEtaNorm_aemeas).mul
              hfluxNorm_aemeas.norm).const_mul (2 : ℝ)).aestronglyMeasurable)
    · filter_upwards [hcross_upper_pt] with x hx
      have hcross_nonneg : 0 ≤ crossAbs x := by
        have hηx : 0 ≤ η x := hη_nonneg x
        have hψx : 0 ≤ |ψ x| := abs_nonneg _
        have hgradx : 0 ≤ gradEtaNorm x := norm_nonneg _
        have hfluxx : 0 ≤ |fluxNorm x| := abs_nonneg _
        dsimp [crossAbs]
        exact mul_nonneg
          (mul_nonneg (mul_nonneg (mul_nonneg (by positivity) hηx) hψx) hgradx)
          hfluxx
      have hrhs_nonneg :
          0 ≤ (1 / 2 : ℝ) * leftTerm x + 2 * Aρ.1.Λ * boundTerm x := by
        exact le_trans hcross_nonneg hx
      have hnorm_cross : ‖crossAbs x‖ = crossAbs x := by
        rw [Real.norm_of_nonneg hcross_nonneg]
      rw [hnorm_cross]
      exact hx
  have hcore_eq_ae :
      coreIntegrand =ᵐ[μ] bilinFormIntegrandOfCoeff Aρ.1 huρ hwφ := by
    have hcore_eq_ae' :
        coreIntegrand =ᵐ[volume.restrict Ω] bilinFormIntegrandOfCoeff Aρ.1 huρ hwφ := by
      exact
        (moserExactReg_core_eq_ae
          (d := d) (Ω := Ω) (Aρ := Aρ) (u := u) (η := η)
          (p := p) (Cη := Cη) (ε := ε) (N := N)
          (hΩ := Metric.isOpen_ball) (hsub := hball_sub) (hu1 := hu1)
          (hε := hε) (hN := hN) (hη := hη) (hη_bound := hη_bound)
          (hη_grad_bound := hη_grad_bound))
    exact hcore_eq_ae'
  have hcore_int :
      Integrable coreIntegrand μ := by
    exact (integrable_bilinFormIntegrandOfCoeff Aρ.1 huρ hwφ).congr hcore_eq_ae.symm
  have hcrossInner_int :
      Integrable crossInner μ := by
    convert hcore_int.sub hleft_int using 1
    ext x
    simp [coreIntegrand]
  have hcrossInner_abs_le :
      ∀ᵐ x ∂μ, |crossInner x| ≤ crossAbs x := by
    filter_upwards with x
    have hηx_nonneg : 0 ≤ η x := hη_nonneg x
    have hψx_nonneg : 0 ≤ ψ x := hψ_nonneg x
    have hinner :
        |inner ℝ (matMulE (Aρ.1.a x) (hwPos.weakGrad x)) (moserFderivVec η x)| ≤
          fluxNorm x * gradEtaNorm x := by
      have := abs_real_inner_le_norm (matMulE (Aρ.1.a x) (hwPos.weakGrad x)) (moserFderivVec η x)
      have hfdv := moser_norm_fderivVec_eq_norm_fderiv (η := η) (x := x)
      change
        |inner ℝ (matMulE (Aρ.1.a x) (hwPos.weakGrad x)) (moserFderivVec η x)| ≤
          ‖matMulE (Aρ.1.a x) (hwPos.weakGrad x)‖ * ‖fderiv ℝ η x‖
      simpa [fluxNorm, gradEtaNorm, hfdv, mul_comm] using this
    have hcoeff_nonneg : 0 ≤ 2 * η x * ψ x := by
      nlinarith
    have hflux_nonneg : 0 ≤ fluxNorm x := by
      simp [fluxNorm]
    change
      |2 * η x * ψ x *
          inner ℝ (matMulE (Aρ.1.a x) (hwPos.weakGrad x)) (moserFderivVec η x)| ≤
        2 * η x * |ψ x| * gradEtaNorm x * |fluxNorm x|
    calc
      |2 * η x * ψ x *
          inner ℝ (matMulE (Aρ.1.a x) (hwPos.weakGrad x)) (moserFderivVec η x)|
          = (2 * η x * ψ x) *
          |inner ℝ (matMulE (Aρ.1.a x) (hwPos.weakGrad x)) (moserFderivVec η x)|
            := by rw [abs_mul, abs_of_nonneg hcoeff_nonneg]
      _ ≤ (2 * η x * ψ x) * (fluxNorm x * gradEtaNorm x) := by
            exact mul_le_mul_of_nonneg_left hinner hcoeff_nonneg
      _ = 2 * η x * |ψ x| * gradEtaNorm x * |fluxNorm x| := by
            rw [abs_of_nonneg hψx_nonneg, abs_of_nonneg hflux_nonneg]
            ring
  have hcross_lower :
      -∫ x, crossAbs x ∂μ ≤ ∫ x, crossInner x ∂μ := by
    have hneg :
        ∫ x, (-1 : ℝ) * crossAbs x ∂μ ≤ ∫ x, crossInner x ∂μ := by
      refine integral_mono_ae (hcrossAbs_int.const_mul (-1)) hcrossInner_int ?_
      filter_upwards [hcrossInner_abs_le] with x hx
      simpa using (abs_le.mp hx).1
    simpa [integral_neg] using hneg
  have hcore_integral :
      ∫ x, leftTerm x ∂μ ≤ ∫ x, crossAbs x ∂μ := by
    have hsub_test' :
        ∫ x, coreIntegrand x ∂μ ≤ 0 := by
      calc
        ∫ x, coreIntegrand x ∂μ = bilinFormOfCoeff Aρ.1 huρ hwφ := by
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
      ∫ x, leftTerm x ∂μ ≤ 4 * Aρ.1.Λ * ∫ x, boundTerm x ∂μ := by
    exact moser_weighted_absorb (μ := μ) (Quad := Equad) (M := fluxNorm) (η := η)
      (ζ := gradEtaNorm) (ψ := ψ) (ψd := ψd) (Λ := Aρ.1.Λ) Aρ.1.Λ_pos
      hcore_integral hcoeff hψd_pos hleft_int hcrossAbs_int hbound_int
  have hsublevel_ρ :
      ∀ᵐ x ∂μ, u x ≤ 0 → hwPos.weakGrad x = 0 := by
    simpa [μ, hwPos] using
      moserPosPartWitness_restrict_grad_zero_on_nonpos
        (d := d) (Ω := Ω) Metric.isOpen_ball hball_sub hu1
  have hTermA_pt :
      ∀ᵐ x ∂μ,
        η x ^ 2 *
          (deriv (moserExactRegPow ε N p) (max (u x) 0)) ^ 2 *
          ‖hwPos.weakGrad x‖ ^ 2 ≤
        (p ^ 2 / (4 * (p - 1))) * leftTerm x := by
    filter_upwards [Aρ.1.coercive, hqual, hsublevel_ρ] with x hxcoer hxqual hsublevelx
    by_cases hx : x ∈ tsupport η
    · by_cases hux : 0 < u x
      · have hboundx : max (u x) 0 < N := hxqual hx
        have hα :
            (deriv (moserExactRegPow ε N p) (max (u x) 0)) ^ 2 ≤
              (p ^ 2 / (4 * (p - 1))) *
                deriv (moserExactRegTestPow ε N p) (max (u x) 0) := by
          simpa [max_eq_left hux.le] using
            moserExactRegPow_deriv_sq_le_const_mul_testDeriv (ε := ε) (N := N) (p := p)
              hε hp hux (by simpa [max_eq_left hux.le] using hboundx)
        have hgrad :
            ‖hwPos.weakGrad x‖ ^ 2 ≤ Equad x := by
          simpa [Equad, bilinFormIntegrandOfCoeff, real_inner_comm] using
            hxcoer (hwPos.weakGrad x)
        have hη_sq_nonneg : 0 ≤ η x ^ 2 := by positivity
        have hψd_eq : ψd x = deriv (moserExactRegTestPow ε N p) (max (u x) 0) := by
          simp [ψd, hx]
        have hψd_pos :
            0 < deriv (moserExactRegTestPow ε N p) (max (u x) 0) := by
          simpa [max_eq_left hux.le] using
            moserExactRegTestPow_deriv_pos_of_support_bound
              (u := u) (x := x) (ε := ε) (N := N) (p := p) hε hp hboundx
        have hα_nonneg :
            0 ≤ (deriv (moserExactRegPow ε N p) (max (u x) 0)) ^ 2 := by
          positivity
        have hconst_nonneg :
            0 ≤
              (p ^ 2 / (4 * (p - 1))) *
                deriv (moserExactRegTestPow ε N p) (max (u x) 0) := by
          have hp1 : 0 < p - 1 := by linarith
          positivity
        have hαη :
            η x ^ 2 *
                (deriv (moserExactRegPow ε N p) (max (u x) 0)) ^ 2 ≤
              η x ^ 2 *
                ((p ^ 2 / (4 * (p - 1))) *
                  deriv (moserExactRegTestPow ε N p) (max (u x) 0)) := by
          exact mul_le_mul_of_nonneg_left hα hη_sq_nonneg
        have hrhs_nonneg :
            0 ≤
              η x ^ 2 *
                ((p ^ 2 / (4 * (p - 1))) *
                  deriv (moserExactRegTestPow ε N p) (max (u x) 0)) := by
          exact mul_nonneg hη_sq_nonneg hconst_nonneg
        calc
          η x ^ 2 *
              (deriv (moserExactRegPow ε N p) (max (u x) 0)) ^ 2 *
              ‖hwPos.weakGrad x‖ ^ 2
              ≤ η x ^ 2 *
                  ((p ^ 2 / (4 * (p - 1))) *
                    deriv (moserExactRegTestPow ε N p) (max (u x) 0)) *
                  Equad x := by
                    exact mul_le_mul hαη hgrad (by positivity) hrhs_nonneg
          _ = (p ^ 2 / (4 * (p - 1))) * leftTerm x := by
              simp [leftTerm, ψd, hx, mul_assoc, mul_left_comm, mul_comm]
      · have hunonpos : u x ≤ 0 := not_lt.mp hux
        have hgrad_zero : hwPos.weakGrad x = 0 := hsublevelx hunonpos
        simp [leftTerm, Equad, bilinFormIntegrandOfCoeff, hgrad_zero]
    · have hηx : η x = 0 := image_eq_zero_of_notMem_tsupport hx
      simp [leftTerm, ψd, hx, hηx]
  have hTermA_int :
      Integrable
        (fun x =>
          η x ^ 2 *
            (deriv (moserExactRegPow ε N p) (max (u x) 0)) ^ 2 *
            ‖hwPos.weakGrad x‖ ^ 2) μ := by
    refine Integrable.mono' (hleft_int.const_mul (p ^ 2 / (4 * (p - 1)))) ?_ ?_
    · exact
        ((((hη.continuous.pow 2).aemeasurable).mul
          ((hα_raw_aemeas.pow aemeasurable_const))).mul
          hwPos.weakGrad_norm_memLp.integrable_sq.aestronglyMeasurable.aemeasurable).aestronglyMeasurable
    · filter_upwards [hTermA_pt] with x hx
      have hlhs_nonneg :
          0 ≤ η x ^ 2 *
            (deriv (moserExactRegPow ε N p) (max (u x) 0)) ^ 2 *
            ‖hwPos.weakGrad x‖ ^ 2 := by
        positivity
      have hrhs_nonneg : 0 ≤ (p ^ 2 / (4 * (p - 1))) * leftTerm x := by
        exact le_trans hlhs_nonneg hx
      simpa [Real.norm_eq_abs, abs_of_nonneg hlhs_nonneg, abs_of_nonneg hrhs_nonneg] using hx
  have hTermA :
      ∫ x in Ω,
        η x ^ 2 *
          (deriv (moserExactRegPow ε N p) (max (u x) 0)) ^ 2 *
          ‖hwPos.weakGrad x‖ ^ 2 ∂volume ≤
        A.1.Λ * (p / (p - 1)) ^ 2 * Cη ^ 2 *
          ∫ x in Ω, (ε + |max (u x) 0|) ^ p ∂volume := by
    have hbound_integral_le :
        ∫ x, boundTerm x ∂μ ≤
          (Cη ^ 2 / (p - 1)) * ∫ x in Ω, (ε + |max (u x) 0|) ^ p ∂volume := by
      have hbound_pt :
          ∀ᵐ x ∂μ,
            boundTerm x ≤ (Cη ^ 2 / (p - 1)) * (ε + |max (u x) 0|) ^ p := by
        filter_upwards [hqual] with x hxqual
        by_cases hx : x ∈ tsupport η
        · have hboundx : max (u x) 0 < N := hxqual hx
          have hp1 : 0 < p - 1 := by linarith
          have hgrad_sq_le : gradEtaNorm x ^ 2 ≤ Cη ^ 2 := by
            exact sq_le_sq.mpr (by
              simp [gradEtaNorm, abs_of_nonneg (norm_nonneg _), abs_of_nonneg hCη_nonneg,
                hη_grad_bound x])
          have hquot_le :
              |ψ x| ^ 2 / ψd x ≤ (ε + |max (u x) 0|) ^ p / (p - 1) := by
            have hbase :=
              moserExactRegTestPow_sq_div_deriv_le_rpow_of_support_bound (u := u) (x := x)
                (ε := ε) (N := N) (p := p) hε hp hboundx
            have hψd_eq : ψd x = deriv (moserExactRegTestPow ε N p) (max (u x) 0) := by
              simp [ψd, hx]
            have hψ_eq : |ψ x| = ψ x := by
              rw [abs_of_nonneg (hψ_nonneg x)]
            simpa [ψ, hψd_eq, hψ_eq] using hbase
          have hquot_nonneg : 0 ≤ |ψ x| ^ 2 / ψd x := by
            have hψd_pos :
                0 < ψd x := by
              simpa [ψd, hx] using
                moserExactRegTestPow_deriv_pos_of_support_bound
                  (u := u) (x := x) (ε := ε) (N := N) (p := p) hε hp hboundx
            exact div_nonneg (by positivity) hψd_pos.le
          have hterm_nonneg : 0 ≤ boundTerm x := by
            exact mul_nonneg (sq_nonneg _) hquot_nonneg
          have hmul_le :
              boundTerm x ≤ Cη ^ 2 * ((ε + |max (u x) 0|) ^ p / (p - 1)) := by
            exact mul_le_mul hgrad_sq_le hquot_le hquot_nonneg (sq_nonneg _)
          calc
            boundTerm x ≤ Cη ^ 2 * ((ε + |max (u x) 0|) ^ p / (p - 1)) := hmul_le
            _ = (Cη ^ 2 / (p - 1)) * (ε + |max (u x) 0|) ^ p := by
                field_simp [show p - 1 ≠ 0 by linarith]
        · have hgrad_zero : gradEtaNorm x = 0 := by
            simpa [gradEtaNorm] using moser_fderiv_norm_zero_outside_tsupport (d := d) (f := η) hη hx
          have hrhs_nonneg :
              0 ≤ (Cη ^ 2 / (p - 1)) * (ε + |max (u x) 0|) ^ p := by
            have hp1 : 0 < p - 1 := by linarith
            exact mul_nonneg (div_nonneg (sq_nonneg _) hp1.le) (Real.rpow_nonneg (by positivity) _)
          simp [boundTerm, hgrad_zero, hrhs_nonneg]
      calc
        ∫ x, boundTerm x ∂μ
            ≤ ∫ x, (Cη ^ 2 / (p - 1)) * (ε + |max (u x) 0|) ^ p ∂μ := by
                refine integral_mono_ae hbound_int ?_ hbound_pt
                simpa [μ] using hpInt.const_mul (Cη ^ 2 / (p - 1))
        _ = (Cη ^ 2 / (p - 1)) * ∫ x in Ω, (ε + |max (u x) 0|) ^ p ∂volume := by
              simp [μ, integral_const_mul]
    have hcoreA :
        ∫ x in Ω,
          η x ^ 2 *
            (deriv (moserExactRegPow ε N p) (max (u x) 0)) ^ 2 *
            ‖hwPos.weakGrad x‖ ^ 2 ∂volume ≤
          (p ^ 2 / (4 * (p - 1))) * ∫ x, leftTerm x ∂μ := by
      have hmono :
          ∫ x,
            η x ^ 2 *
              (deriv (moserExactRegPow ε N p) (max (u x) 0)) ^ 2 *
              ‖hwPos.weakGrad x‖ ^ 2 ∂μ ≤
            ∫ x, (p ^ 2 / (4 * (p - 1))) * leftTerm x ∂μ := by
        exact integral_mono_ae hTermA_int (hleft_int.const_mul (p ^ 2 / (4 * (p - 1)))) hTermA_pt
      simpa [μ, integral_const_mul] using hmono
    calc
      ∫ x in Ω,
          η x ^ 2 *
            (deriv (moserExactRegPow ε N p) (max (u x) 0)) ^ 2 *
            ‖hwPos.weakGrad x‖ ^ 2 ∂volume
          ≤ (p ^ 2 / (4 * (p - 1))) * ∫ x, leftTerm x ∂μ := hcoreA
      _ ≤ (p ^ 2 / (4 * (p - 1))) * (4 * Aρ.1.Λ * ∫ x, boundTerm x ∂μ) := by
            have hconst_nonneg : 0 ≤ p ^ 2 / (4 * (p - 1)) := by
              have hp1 : 0 < p - 1 := by linarith
              positivity
            exact mul_le_mul_of_nonneg_left hleft_bound hconst_nonneg
      _ ≤ (p ^ 2 / (4 * (p - 1))) *
            (4 * Aρ.1.Λ *
              ((Cη ^ 2 / (p - 1)) * ∫ x in Ω, (ε + |max (u x) 0|) ^ p ∂volume)) := by
            have hconst_nonneg : 0 ≤ p ^ 2 / (4 * (p - 1)) := by
              have hp1 : 0 < p - 1 := by linarith
              positivity
            have hΛ_nonneg : 0 ≤ 4 * Aρ.1.Λ := by
              nlinarith [Aρ.1.Λ_pos]
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hbound_integral_le hΛ_nonneg) hconst_nonneg
      _ = A.1.Λ * (p / (p - 1)) ^ 2 * Cη ^ 2 *
            ∫ x in Ω, (ε + |max (u x) 0|) ^ p ∂volume := by
            have hΛeq : Aρ.1.Λ = A.1.Λ := by
              simp [Aρ, NormalizedEllipticCoeff.restrict, EllipticCoeff.restrict_Λ]
            rw [hΛeq]
            have hp1 : p - 1 ≠ 0 := by linarith
            field_simp [hp1]
  have hTermB_int :
      Integrable
        (fun x =>
          ‖fderiv ℝ η x‖ ^ 2 *
            (moserExactRegPow ε N p (max (u x) 0)) ^ 2) μ := by
    refine Integrable.mono' (hpInt.const_mul (Cη ^ 2)) ?_ ?_
    · exact
        ((((hgradEtaNorm_aemeas.pow aemeasurable_const).mul
          (hβ_aemeas.pow aemeasurable_const))).aestronglyMeasurable)
    · filter_upwards [hqual] with x hxqual
      by_cases hx : x ∈ tsupport η
      · have hboundx : max (u x) 0 < N := hxqual hx
        have hgrad_sq_le : ‖fderiv ℝ η x‖ ^ 2 ≤ Cη ^ 2 := by
          exact sq_le_sq.mpr (by
            simp [abs_of_nonneg (norm_nonneg _), abs_of_nonneg hCη_nonneg, hη_grad_bound x])
        have hpow_le :=
          moserExactRegPow_sq_le_rpow_of_support_bound (u := u) (x := x)
            (ε := ε) (N := N) (p := p) hε hp hboundx
        have hpow_nonneg :
            0 ≤ (moserExactRegPow ε N p (max (u x) 0)) ^ 2 := by
          positivity
        have hrhs_nonneg : 0 ≤ Cη ^ 2 * (ε + |max (u x) 0|) ^ p := by
          exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (by positivity) _)
        have hle :
            ‖fderiv ℝ η x‖ ^ 2 * (moserExactRegPow ε N p (max (u x) 0)) ^ 2 ≤
              Cη ^ 2 * (ε + |max (u x) 0|) ^ p := by
          exact mul_le_mul hgrad_sq_le hpow_le hpow_nonneg (sq_nonneg _)
        simpa [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) hpow_nonneg),
          abs_of_nonneg hrhs_nonneg] using hle
      · have hgrad_zero : ‖fderiv ℝ η x‖ = 0 := by
          exact moser_fderiv_norm_zero_outside_tsupport (d := d) (f := η) hη hx
        have hrhs_nonneg : 0 ≤ Cη ^ 2 * (ε + |max (u x) 0|) ^ p := by
          exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (by positivity) _)
        simp [hgrad_zero, hrhs_nonneg]
  have hTermB :
      ∫ x in Ω,
        ‖fderiv ℝ η x‖ ^ 2 *
          (moserExactRegPow ε N p (max (u x) 0)) ^ 2 ∂volume ≤
        Cη ^ 2 * ∫ x in Ω, (ε + |max (u x) 0|) ^ p ∂volume := by
    have hTermB_pt :
        ∀ᵐ x ∂μ,
          ‖fderiv ℝ η x‖ ^ 2 *
            (moserExactRegPow ε N p (max (u x) 0)) ^ 2 ≤
          Cη ^ 2 * (ε + |max (u x) 0|) ^ p := by
      filter_upwards [hqual] with x hxqual
      by_cases hx : x ∈ tsupport η
      · have hboundx : max (u x) 0 < N := hxqual hx
        have hgrad_sq_le : ‖fderiv ℝ η x‖ ^ 2 ≤ Cη ^ 2 := by
          exact sq_le_sq.mpr (by
            simp [abs_of_nonneg (norm_nonneg _), abs_of_nonneg hCη_nonneg, hη_grad_bound x])
        have hpow_le :=
          moserExactRegPow_sq_le_rpow_of_support_bound (u := u) (x := x)
            (ε := ε) (N := N) (p := p) hε hp hboundx
        have hpow_nonneg :
            0 ≤ (moserExactRegPow ε N p (max (u x) 0)) ^ 2 := by
          positivity
        exact mul_le_mul hgrad_sq_le hpow_le hpow_nonneg (sq_nonneg _)
      · have hgrad_zero : ‖fderiv ℝ η x‖ = 0 := by
          exact moser_fderiv_norm_zero_outside_tsupport (d := d) (f := η) hη hx
        have hrhs_nonneg : 0 ≤ Cη ^ 2 * (ε + |max (u x) 0|) ^ p := by
          exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (by positivity) _)
        simp [hgrad_zero, hrhs_nonneg]
    calc
      ∫ x in Ω,
          ‖fderiv ℝ η x‖ ^ 2 *
            (moserExactRegPow ε N p (max (u x) 0)) ^ 2 ∂volume
          = ∫ x,
              ‖fderiv ℝ η x‖ ^ 2 *
                (moserExactRegPow ε N p (max (u x) 0)) ^ 2 ∂μ := by
                simp [μ]
      _ ≤ ∫ x, Cη ^ 2 * (ε + |max (u x) 0|) ^ p ∂μ := by
            exact integral_mono_ae hTermB_int (hpInt.const_mul (Cη ^ 2)) hTermB_pt
      _ = Cη ^ 2 * ∫ x in Ω, (ε + |max (u x) 0|) ^ p ∂volume := by
            simp [μ, integral_const_mul]
  have hgrad_split :
      ∫ x in Ω, ‖hwReg.weakGrad x‖ ^ 2 ∂volume ≤
        2 * ∫ x in Ω,
          η x ^ 2 *
            (deriv (moserExactRegPow ε N p) (max (u x) 0)) ^ 2 *
            ‖hwPos.weakGrad x‖ ^ 2 ∂volume +
        2 * ∫ x in Ω,
          ‖fderiv ℝ η x‖ ^ 2 *
            (moserExactRegPow ε N p (max (u x) 0)) ^ 2 ∂volume := by
    let termAfun : E → ℝ := fun x =>
      η x ^ 2 *
        (deriv (moserExactRegPow ε N p) (max (u x) 0)) ^ 2 *
        ‖hwPos.weakGrad x‖ ^ 2
    let termBfun : E → ℝ := fun x =>
      ‖fderiv ℝ η x‖ ^ 2 *
        (moserExactRegPow ε N p (max (u x) 0)) ^ 2
    have hupper_int :
        Integrable
          (fun x => 2 * termAfun x + 2 * termBfun x) μ := by
      convert (hTermA_int.const_mul (2 : ℝ)).add (hTermB_int.const_mul (2 : ℝ)) using 1
    have hmono :
        ∫ x, ‖hwRegρ.weakGrad x‖ ^ 2 ∂μ ≤
          ∫ x, 2 * termAfun x + 2 * termBfun x ∂μ := by
      refine integral_mono_ae ?_ hupper_int ?_
      · simpa [pow_two, μ, hwRegρ] using hwRegρ.weakGrad_norm_memLp.integrable_sq
      · filter_upwards with x
        simpa [hwRegρ, termAfun, termBfun, mul_assoc, add_comm, add_left_comm, add_assoc] using
          (moserExactRegPowerCutoffWitness_norm_sq_le (d := d) (u := u) (η := η)
            (ε := ε) (N := N) (p := p) (Cη := Cη)
            hε hN hu1 hη hη_bound hη_grad_bound x)
    calc
      ∫ x in Ω, ‖hwReg.weakGrad x‖ ^ 2 ∂volume
          = ∫ x, ‖hwRegρ.weakGrad x‖ ^ 2 ∂μ := by
              change ∫ x, ‖hwReg.weakGrad x‖ ^ 2 ∂μ = ∫ x, ‖hwReg.weakGrad x‖ ^ 2 ∂μ
              simp [μ]
      _ ≤ ∫ x, 2 * termAfun x + 2 * termBfun x ∂μ := hmono
      _ = 2 * ∫ x in Ω, termAfun x ∂volume + 2 * ∫ x in Ω, termBfun x ∂volume := by
            rw [integral_add (hTermA_int.const_mul (2 : ℝ)) (hTermB_int.const_mul (2 : ℝ)),
              integral_const_mul, integral_const_mul]
  calc
    ∫ x in Ω, ‖hwReg.weakGrad x‖ ^ 2 ∂volume
        = ∫ x in Ω, ‖hwRegρ.weakGrad x‖ ^ 2 ∂volume := by rfl
    _ ≤ 2 * ∫ x in Ω,
          η x ^ 2 *
            (deriv (moserExactRegPow ε N p) (max (u x) 0)) ^ 2 *
            ‖hwPos.weakGrad x‖ ^ 2 ∂volume +
        2 * ∫ x in Ω,
          ‖fderiv ℝ η x‖ ^ 2 *
            (moserExactRegPow ε N p (max (u x) 0)) ^ 2 ∂volume := hgrad_split
    _ ≤ 2 * (A.1.Λ * (p / (p - 1)) ^ 2 * Cη ^ 2 *
          ∫ x in Ω, (ε + |max (u x) 0|) ^ p ∂volume) +
        2 * (Cη ^ 2 * ∫ x in Ω, (ε + |max (u x) 0|) ^ p ∂volume) := by
          exact add_le_add
            (mul_le_mul_of_nonneg_left hTermA (by positivity))
            (mul_le_mul_of_nonneg_left hTermB (by positivity))
    _ = 2 * Cη ^ 2 * (A.1.Λ * (p / (p - 1)) ^ 2 + 1) *
          ∫ x in Ω, (ε + |max (u x) 0|) ^ p ∂volume := by
          ring

theorem moser_regularized_energy_bound
    (A : NormalizedEllipticCoeff d (Metric.ball (0 : E) 1))
    {u η : E → ℝ} {p ρ Cη ε N : ℝ}
    (hp : 1 < p)
    (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hε : 0 < ε) (hN : 0 ≤ N)
    (hsub : IsSubsolution A.1 u)
    (hu1 : MemW1pWitness 2 u (Metric.ball (0 : E) 1))
    (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hη_nonneg : ∀ x, 0 ≤ η x)
    (hη_bound : ∀ x, |η x| ≤ 1)
    (hη_grad_bound : ∀ x, ‖fderiv ℝ η x‖ ≤ Cη)
    (hη_sub_ball : tsupport η ⊆ Metric.ball (0 : E) ρ)
    (hqual :
      ∀ᵐ x ∂(volume.restrict (Metric.ball (0 : E) ρ)),
        x ∈ tsupport η → max (u x) 0 < N)
    (hpInt : IntegrableOn (fun x => (ε + |max (u x) 0|) ^ p)
        (Metric.ball (0 : E) ρ) volume) :
    let hwReg := moserExactRegPowerCutoffWitness (d := d) (u := u) (η := η)
      (ε := ε) (N := N) (p := p) (Cη := Cη)
      hε hN hu1 hη hη_bound hη_grad_bound
    ∫ x in Metric.ball (0 : E) ρ, ‖hwReg.weakGrad x‖ ^ 2 ∂volume ≤
      2 * Cη ^ 2 * (A.1.Λ * (p / (p - 1)) ^ 2 + 1) *
        ∫ x in Metric.ball (0 : E) ρ, (ε + |max (u x) 0|) ^ p ∂volume := by
  simpa using
    moser_exact_regularized_energy_bound
      (d := d) A (u := u) (η := η) (p := p) (ρ := ρ) (Cη := Cη) (ε := ε) (N := N)
      hp hρ hρ1 hε hN hsub hu1 hη hη_nonneg hη_bound hη_grad_bound hη_sub_ball hqual hpInt

theorem moserExactReg_energy_mainBall
    (A : NormalizedEllipticCoeff d (Metric.ball (0 : E) 1))
    {u η : E → ℝ} {p ρ Cη N : ℝ}
    (hp : 1 < p)
    (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hN : 0 ≤ N)
    (hsub : IsSubsolution A.1 u)
    (hu1 : MemW1pWitness 2 u (Metric.ball (0 : E) 1))
    (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hη_nonneg : ∀ x, 0 ≤ η x)
    (hη_bound : ∀ x, |η x| ≤ 1)
    (hη_grad_bound : ∀ x, ‖fderiv ℝ η x‖ ≤ Cη)
    (hη_sub_ball : tsupport η ⊆ Metric.ball (0 : E) ρ)
    (hqual :
      ∀ᵐ x ∂(volume.restrict (Metric.ball (0 : E) ρ)),
        x ∈ tsupport η → max (u x) 0 < N)
    (hpInt : ∀ n,
      IntegrableOn (fun x => (moserEpsSeq n + |max (u x) 0|) ^ p)
        (Metric.ball (0 : E) ρ) volume) :
    ∀ n,
      let hwReg :=
        moserExactRegPowerCutoffWitness (d := d) (u := u) (η := η)
          (ε := moserEpsSeq n) (N := N) (p := p) (Cη := Cη)
          (moserEpsSeq_pos n) hN hu1 hη hη_bound hη_grad_bound
      ∫ x in Metric.ball (0 : E) ρ, ‖hwReg.weakGrad x‖ ^ 2 ∂volume ≤
        2 * Cη ^ 2 * (A.1.Λ * (p / (p - 1)) ^ 2 + 1) *
          ∫ x in Metric.ball (0 : E) ρ, (moserEpsSeq n + |max (u x) 0|) ^ p ∂volume := by
  intro n
  exact
    moser_regularized_energy_bound
      (d := d) (A := A) (u := u) (η := η) (p := p) (ρ := ρ)
      (Cη := Cη) (ε := moserEpsSeq n) (N := N)
      (hp := hp) (hρ := hρ) (hρ1 := hρ1) (hε := moserEpsSeq_pos n) (hN := hN)
      (hsub := hsub) (hu1 := hu1) (hη := hη) (hη_nonneg := hη_nonneg)
      (hη_bound := hη_bound) (hη_grad_bound := hη_grad_bound)
      (hη_sub_ball := hη_sub_ball) (hqual := hqual) (hpInt := hpInt n)
  /-
  intro hwReg
  let Ω : Set E := Metric.ball (0 : E) s
  let μ : Measure E := volume.restrict Ω
  -- ‖a + b‖² ≤ 2‖a‖² + 2‖b‖² for vectors a, b
  -- Applied to the gradient decomposition:
  --   hwReg.weakGrad x = η(x)·α(x)·∇clip(x) + moserFderivVec(η)(x)·β(x)
  -- where α = deriv(moserRegPow ε N p) ∘ clip, β = moserRegPow ε N p ∘ clip.
  --
  -- Term A = ∫ η²·α²·‖∇clip‖² — bounded via subsolution testing
  -- Term B = ∫ ‖∇η‖²·β² — bounded directly
  -- Total: ∫ ‖hwReg.weakGrad‖² ≤ 2(Term A + Term B)
  --
  -- (requires extending test function to ball 0 1, expanding bilinear form a.e.)
  let Λ_coeff : ℝ := A.1.Λ * (p / (p - 1)) ^ 2
  have hTermA :
      ∫ x in Ω, η x ^ 2 *
        (deriv (moserRegPow ε N p) (min (max (u x) 0) N)) ^ 2 *
        ‖(moserClippedPosPartWitness (d := d) hs hs1 hN hu1).weakGrad x‖ ^ 2 ∂volume ≤
      Λ_coeff * Cη ^ 2 * ∫ x in Ω, (ε + |max (u x) 0|) ^ p ∂volume := by
    -- Earlier expanded derivation of the same estimate.
    --
    -- This follows the same expand-bound-absorb pattern as the De Giorgi
    -- energy estimate, with the regularized Moser profiles supplying the
    -- derivative-ratio bound that controls the principal term by the cutoff
    -- error term.
  have hTermB :
      ∫ x in Ω, ‖fderiv ℝ η x‖ ^ 2 *
        (moserRegPow ε N p (min (max (u x) 0) N)) ^ 2 ∂volume ≤
      Cη ^ 2 * ∫ x in Ω, (ε + |max (u x) 0|) ^ p ∂volume := by
    -- Pointwise: ‖∇η‖² * β² ≤ Cη² * (ε + u₊)^p, then integrate.
    have hpw : ∀ x,
        ‖fderiv ℝ η x‖ ^ 2 * (moserRegPow ε N p (min (max (u x) 0) N)) ^ 2 ≤
          Cη ^ 2 * (ε + |max (u x) 0|) ^ p := by
      intro x
      have h_grad : ‖fderiv ℝ η x‖ ^ 2 ≤ Cη ^ 2 :=
        sq_le_sq' (by linarith [hη_grad_bound x, norm_nonneg (fderiv ℝ η x)])
          (hη_grad_bound x)
      have ht0 : 0 ≤ min (max (u x) 0) N := le_min (le_max_right _ _) hN
      have htN : min (max (u x) 0) N ≤ N := min_le_right _ _
      have h_sq : (moserRegPow ε N p (min (max (u x) 0) N)) ^ 2 ≤
          (ε + min (max (u x) 0) N) ^ p :=
        moserRegPow_sq_le_rpow_of_nonneg_le_N hε hN ht0 htN hp
      have h_base_le : ε + min (max (u x) 0) N ≤ ε + |max (u x) 0| := by
        gcongr; exact (min_le_left _ _).trans (le_abs_self _)
      have h_rpow : (ε + min (max (u x) 0) N) ^ p ≤ (ε + |max (u x) 0|) ^ p :=
        Real.rpow_le_rpow (by linarith) h_base_le (by linarith)
      nlinarith [sq_nonneg (moserRegPow ε N p (min (max (u x) 0) N)),
        Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ ε + |max (u x) 0|) p]
    calc ∫ x in Ω, ‖fderiv ℝ η x‖ ^ 2 *
            (moserRegPow ε N p (min (max (u x) 0) N)) ^ 2 ∂volume
        ≤ ∫ x in Ω, Cη ^ 2 * (ε + |max (u x) 0|) ^ p ∂volume := by
          apply integral_mono_of_nonneg (ae_of_all _ fun x => by positivity)
            (hpInt.const_mul _)
            (ae_of_all _ fun x => hpw x)
      _ = Cη ^ 2 * ∫ x in Ω, (ε + |max (u x) 0|) ^ p ∂volume :=
          integral_const_mul _ _
  -- The weak gradient of hwReg = η · (comp_smooth_bounded grad) + fderiv η · (comp value)
  -- by mul_smooth_bounded.
  have hgrad_split :
      ∫ x in Ω, ‖hwReg.weakGrad x‖ ^ 2 ∂volume ≤
        2 * ∫ x in Ω, η x ^ 2 *
          (deriv (moserRegPow ε N p) (min (max (u x) 0) N)) ^ 2 *
          ‖(moserClippedPosPartWitness (d := d) hs hs1 hN hu1).weakGrad x‖ ^ 2 ∂volume +
        2 * ∫ x in Ω, ‖fderiv ℝ η x‖ ^ 2 *
          (moserRegPow ε N p (min (max (u x) 0) N)) ^ 2 ∂volume := by
    -- Pointwise: from moserRegPowerCutoffWitness_grad, ∇(hwReg)_i = a_i + b_i
    -- where a_i = η·α·∇clip_i and b_i = ∂ᵢη·β.
    -- Then (a_i + b_i)² ≤ 2a_i² + 2b_i² and sum over i.
    let hwClip := moserClippedPosPartWitness (d := d) (u := u) hs hs1 hN hu1
    let hwComp := moserRegClippedPosPartWitness (d := d) (u := u) (p := p) hs hs1 hε hN hu1
    -- Pointwise bound
    have hpw : ∀ x,
        ‖hwReg.weakGrad x‖ ^ 2 ≤
          2 * (η x ^ 2 * (deriv (moserRegPow ε N p) (min (max (u x) 0) N)) ^ 2 *
            ‖hwClip.weakGrad x‖ ^ 2) +
          2 * (‖fderiv ℝ η x‖ ^ 2 *
            (moserRegPow ε N p (min (max (u x) 0) N)) ^ 2) := by
      intro x
      exact moserRegPowerCutoffWitness_norm_sq_le (d := d) hs hs1 hε hN hu1
        hη hη_bound hη_grad_bound x
    -- Integrability of the two terms (follows from hwReg ∈ W^{1,2} + pointwise bound)
    have hA_int : Integrable (fun x => η x ^ 2 *
        (deriv (moserRegPow ε N p) (min (max (u x) 0) N)) ^ 2 *
        ‖hwClip.weakGrad x‖ ^ 2) (volume.restrict Ω) := by
      -- η² ≤ 1 (bounded), α² ≤ M² (deriv bounded by moserRegPow_deriv_bounded),
      -- ‖∇clip‖² integrable (hwClip ∈ W^{1,2}).
      -- Product of bounded × integrable → integrable.
      obtain ⟨M, hM⟩ := moserRegPow_deriv_bounded (ε := ε) (N := N) (p := p) hε hN
      refine Integrable.mono' (hwClip.weakGrad_norm_memLp.integrable_sq.const_mul (M ^ 2)) ?_ ?_
      · exact ((hη.continuous.pow 2).aemeasurable.mul
            (((moserRegPow_contDiff hε hN).continuous_deriv (by simp)).measurable.comp_aemeasurable
              hwClip.memLp.aestronglyMeasurable.aemeasurable |>.pow
              aemeasurable_const)).mul
            (hwClip.weakGrad_norm_memLp.aestronglyMeasurable.aemeasurable.pow aemeasurable_const)
          |>.aestronglyMeasurable
      · exact ae_of_all _ fun x => by
          have h1 : η x ^ 2 ≤ 1 := by
            have habsη := abs_le.mp (hη_bound x); nlinarith [habsη.1, habsη.2]
          have habsM := abs_le.mp (hM (min (max (u x) 0) N))
          have h2 : (deriv (moserRegPow ε N p) (min (max (u x) 0) N)) ^ 2 ≤ M ^ 2 :=
            sq_le_sq' habsM.1 habsM.2
          calc |η x ^ 2 * (deriv (moserRegPow ε N p) (min (max (u x) 0) N)) ^ 2 *
                  ‖hwClip.weakGrad x‖ ^ 2|
              = η x ^ 2 * (deriv (moserRegPow ε N p) (min (max (u x) 0) N)) ^ 2 *
                  ‖hwClip.weakGrad x‖ ^ 2 := by
                rw [abs_of_nonneg (by positivity)]
            _ ≤ 1 * M ^ 2 * ‖hwClip.weakGrad x‖ ^ 2 := by
                nlinarith [mul_le_mul h1 h2 (sq_nonneg _) zero_le_one,
                  sq_nonneg ‖hwClip.weakGrad x‖]
            _ = M ^ 2 * ‖hwClip.weakGrad x‖ ^ 2 := by ring
    have hB_int : Integrable (fun x => ‖fderiv ℝ η x‖ ^ 2 *
        (moserRegPow ε N p (min (max (u x) 0) N)) ^ 2) (volume.restrict Ω) := by
      -- ‖∇η‖² ≤ Cη² (bounded), β² integrable (hwComp ∈ L²).
      -- Product of bounded × integrable → integrable.
      refine Integrable.mono' (hwComp.memLp.integrable_sq.const_mul (Cη ^ 2)) ?_ ?_
      · exact (((hη.continuous_fderiv (by simp)).norm.pow 2).aemeasurable.mul
            (hwComp.memLp.aestronglyMeasurable.aemeasurable.pow aemeasurable_const))
          |>.aestronglyMeasurable
      · exact ae_of_all _ fun x => by
          have h1 : ‖fderiv ℝ η x‖ ^ 2 ≤ Cη ^ 2 :=
            sq_le_sq' (by linarith [hη_grad_bound x, norm_nonneg (fderiv ℝ η x)])
              (hη_grad_bound x)
          rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
          nlinarith [sq_nonneg (moserRegPow ε N p (min (max (u x) 0) N))]
    have hRHS_int := (hA_int.const_mul 2).add (hB_int.const_mul 2)
    calc ∫ x in Ω, ‖hwReg.weakGrad x‖ ^ 2 ∂volume
        ≤ ∫ x in Ω,
            (2 * (η x ^ 2 * (deriv (moserRegPow ε N p) (min (max (u x) 0) N)) ^ 2 *
              ‖hwClip.weakGrad x‖ ^ 2) +
            2 * (‖fderiv ℝ η x‖ ^ 2 *
              (moserRegPow ε N p (min (max (u x) 0) N)) ^ 2)) ∂volume :=
          integral_mono_of_nonneg
            (ae_of_all _ fun x => by positivity)
            hRHS_int
            (ae_of_all _ fun x => hpw x)
      _ = 2 * ∫ x in Ω, η x ^ 2 *
              (deriv (moserRegPow ε N p) (min (max (u x) 0) N)) ^ 2 *
              ‖hwClip.weakGrad x‖ ^ 2 ∂volume +
          2 * ∫ x in Ω, ‖fderiv ℝ η x‖ ^ 2 *
              (moserRegPow ε N p (min (max (u x) 0) N)) ^ 2 ∂volume := by
          rw [integral_add (hA_int.const_mul 2) (hB_int.const_mul 2),
            integral_const_mul, integral_const_mul]
  calc ∫ x in Ω, ‖hwReg.weakGrad x‖ ^ 2 ∂volume
      ≤ 2 * ∫ x in Ω, η x ^ 2 *
          (deriv (moserRegPow ε N p) (min (max (u x) 0) N)) ^ 2 *
          ‖(moserClippedPosPartWitness (d := d) hs hs1 hN hu1).weakGrad x‖ ^ 2 ∂volume +
        2 * ∫ x in Ω, ‖fderiv ℝ η x‖ ^ 2 *
          (moserRegPow ε N p (min (max (u x) 0) N)) ^ 2 ∂volume := hgrad_split
    _ ≤ 2 * (Λ_coeff * Cη ^ 2 * ∫ x in Ω, (ε + |max (u x) 0|) ^ p ∂volume) +
        2 * (Cη ^ 2 * ∫ x in Ω, (ε + |max (u x) 0|) ^ p ∂volume) := by
        gcongr
    _ = 2 * Cη ^ 2 * (A.1.Λ * (p / (p - 1)) ^ 2 + 1) *
        ∫ x in Ω, (ε + |max (u x) 0|) ^ p ∂volume := by
        dsimp [Λ_coeff]
        ring
-/


end DeGiorgi
