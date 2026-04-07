import DeGiorgi.Crossover.LogGradient

/-!
# Crossover Exponential Integrability

John--Nirenberg and exponential-integrability machinery for the crossover product bound.
-/

noncomputable section

open MeasureTheory Metric Filter Set
open scoped ENNReal NNReal Topology RealInnerProductSpace

namespace DeGiorgi

variable {d : ℕ} [NeZero d]

local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "Cmo" =>
  ((volume.real (Metric.ball (0 : E) 1)) ^ (-(1 / 2 : ℝ)) * C_poinc_val d)


/-! ### Crossover Exponential Integrability

Helper lemmas for the John-Nirenberg-based crossover argument. -/

set_option maxHeartbeats 800000 in
omit [NeZero d] in
/-- Smooth cutoff: φ = 1 on closedBall 0 1, tsupport ⊆ ball 0 (7/6), range ⊆ [0,1].
    Used for the log gradient bound on rescaled cover balls. -/
lemma exists_unitBall_cutoff :
    ∃ (φ : E → ℝ),
      ContDiff ℝ (⊤ : ℕ∞) φ ∧
      HasCompactSupport φ ∧
      tsupport φ ⊆ Metric.ball (0 : E) (7 / 6 : ℝ) ∧
      (∀ x ∈ Metric.closedBall (0 : E) 1, φ x = 1) ∧
      Set.range φ ⊆ Set.Icc (0 : ℝ) 1 := by
  have hK : IsCompact (Metric.closedBall (0 : E) 1) := isCompact_closedBall 0 1
  have hΩ : IsOpen (Metric.ball (0 : E) (7 / 6 : ℝ)) := isOpen_ball
  have hKΩ : Metric.closedBall (0 : E) 1 ⊆ Metric.ball (0 : E) (7 / 6 : ℝ) :=
    Metric.closedBall_subset_ball (by norm_num : (1 : ℝ) < 7 / 6)
  obtain ⟨δ, hδ_pos, hδΩ⟩ := hK.exists_cthickening_subset_open hΩ hKΩ
  rcases exists_contMDiff_support_eq_eq_one_iff
      (I := modelWithCornersSelf ℝ E) (s := Metric.thickening δ (Metric.closedBall (0 : E) 1))
      (t := Metric.closedBall (0 : E) 1)
      isOpen_thickening isClosed_closedBall
      (self_subset_thickening hδ_pos (Metric.closedBall (0 : E) 1)) with
    ⟨η, hη_smooth, hη_range, hη_support, hη_one_iff⟩
  refine ⟨η, contMDiff_iff_contDiff.mp hη_smooth, ?_, ?_, ?_, hη_range⟩
  · apply HasCompactSupport.intro' (K := Metric.cthickening δ (Metric.closedBall (0 : E) 1))
    · exact (isCompact_closedBall 0 1).cthickening (r := δ)
    · exact isClosed_cthickening
    · intro x hx
      have hxt : x ∉ tsupport η := by
        intro hxt
        have hx_closure : x ∈ closure (Metric.thickening δ (Metric.closedBall (0 : E) 1)) := by
          rw [tsupport, hη_support] at hxt; exact hxt
        exact hx (Metric.closure_thickening_subset_cthickening δ _ hx_closure)
      exact image_eq_zero_of_notMem_tsupport hxt
  · rw [tsupport, hη_support]
    exact (Metric.closure_thickening_subset_cthickening δ _).trans hδΩ
  · intro x hx; exact (hη_one_iff x).1 hx

noncomputable def crossoverUnitBallCutoff : E → ℝ :=
  Classical.choose (exists_unitBall_cutoff (d := d))

omit [NeZero d] in
theorem crossoverUnitBallCutoff_spec :
    ContDiff ℝ (⊤ : ℕ∞) (crossoverUnitBallCutoff (d := d)) ∧
    HasCompactSupport (crossoverUnitBallCutoff (d := d)) ∧
    tsupport (crossoverUnitBallCutoff (d := d)) ⊆ Metric.ball (0 : E) (7 / 6 : ℝ) ∧
    (∀ x ∈ Metric.closedBall (0 : E) 1, crossoverUnitBallCutoff (d := d) x = 1) ∧
    Set.range (crossoverUnitBallCutoff (d := d)) ⊆ Set.Icc (0 : ℝ) 1 := by
  simpa [crossoverUnitBallCutoff] using
    (Classical.choose_spec (exists_unitBall_cutoff (d := d)))

omit [NeZero d] in
theorem exists_crossoverUnitBallCutoff_fderiv_bound :
    ∃ G : ℝ, 0 ≤ G ∧
      ∀ x, ‖fderiv ℝ (crossoverUnitBallCutoff (d := d)) x‖ ≤ G := by
  obtain ⟨hφ, hφ_cs, _, _, _⟩ := crossoverUnitBallCutoff_spec (d := d)
  obtain ⟨G, hG⟩ := (hφ_cs.fderiv (𝕜 := ℝ)).exists_bound_of_continuous
    (hφ.continuous_fderiv (by simp))
  refine ⟨G, le_trans (norm_nonneg _) (hG 0), hG⟩

noncomputable def crossoverUnitBallCutoffFDerivBound : ℝ :=
  Classical.choose (exists_crossoverUnitBallCutoff_fderiv_bound (d := d))

omit [NeZero d] in
theorem crossoverUnitBallCutoffFDerivBound_spec :
    0 ≤ crossoverUnitBallCutoffFDerivBound (d := d) ∧
      ∀ x,
        ‖fderiv ℝ (crossoverUnitBallCutoff (d := d)) x‖ ≤
          crossoverUnitBallCutoffFDerivBound (d := d) := by
  simpa [crossoverUnitBallCutoffFDerivBound] using
    (Classical.choose_spec (exists_crossoverUnitBallCutoff_fderiv_bound (d := d)))

theorem crossover_volumeReal_ball_eq
    (x : E) {r : ℝ} (hr : 0 < r) :
    volume.real (Metric.ball x r) =
      r ^ d * volume.real (Metric.ball (0 : E) 1) := by
  have hd : d ≠ 0 := NeZero.ne d
  have hdpos : 0 < d := Nat.pos_of_ne_zero hd
  haveI : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) (M := E) <| by
    simpa [finrank_euclideanSpace] using hdpos
  rw [← Measure.addHaar_real_closedBall_eq_addHaar_real_ball (μ := volume) x r,
    Measure.addHaar_real_closedBall (μ := volume) x hr.le]
  simp [finrank_euclideanSpace]

theorem crossover_volumeReal_closedBall_eq
    (x : E) {r : ℝ} (hr : 0 < r) :
    volume.real (Metric.closedBall x r) =
      r ^ d * volume.real (Metric.ball (0 : E) 1) := by
  have hd : d ≠ 0 := NeZero.ne d
  have hdpos : 0 < d := Nat.pos_of_ne_zero hd
  haveI : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) (M := E) <| by
    simpa [finrank_euclideanSpace] using hdpos
  rw [Measure.addHaar_real_closedBall (μ := volume) x hr.le]
  simp [finrank_euclideanSpace]

theorem dist_add_lt_of_closedBall_subset_ball
    {x z : E} {R s : ℝ}
    (hs : 0 < s)
    (hsub : Metric.closedBall z s ⊆ Metric.ball x R) :
    dist z x + s < R := by
  have hdpos : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  let i0 : Fin d := ⟨0, hdpos⟩
  let e0 : E := EuclideanSpace.single i0 1
  have he0_norm : ‖e0‖ = 1 := by
    simp [e0]
  by_cases hzx : z = x
  · let y : E := z + s • e0
    have hy_mem : y ∈ Metric.closedBall z s := by
      rw [Metric.mem_closedBall, dist_eq_norm]
      rw [show y - z = s • e0 by simp [y]]
      simp [norm_smul, he0_norm, Real.norm_of_nonneg hs.le]
    have hy_ball : y ∈ Metric.ball x R := hsub hy_mem
    subst hzx
    have hy_dist : dist y z = s := by
      rw [dist_eq_norm]
      rw [show y - z = s • e0 by simp [y], norm_smul, he0_norm,
        Real.norm_of_nonneg hs.le]
      ring
    have hy_ball' : dist y z < R := Metric.mem_ball.1 hy_ball
    simpa [hy_dist] using hy_ball'
  · let y : E := z + (s / ‖z - x‖) • (z - x)
    have hzx_norm : ‖z - x‖ ≠ 0 := by
      exact norm_ne_zero_iff.mpr (sub_ne_zero.mpr hzx)
    have hzx_pos : 0 < ‖z - x‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hzx)
    have hy_mem : y ∈ Metric.closedBall z s := by
      rw [Metric.mem_closedBall, dist_eq_norm]
      rw [show y - z = (s / ‖z - x‖) • (z - x) by simp [y]]
      rw [norm_smul, Real.norm_of_nonneg (div_nonneg hs.le hzx_pos.le)]
      have hmul : (s / ‖z - x‖) * ‖z - x‖ = s := by
        field_simp [hzx_norm]
      calc
        (s / ‖z - x‖) * ‖z - x‖ = s := hmul
        _ ≤ s := le_rfl
    have hy_ball : y ∈ Metric.ball x R := hsub hy_mem
    have hy_sub :
        y - x = (1 + s / ‖z - x‖) • (z - x) := by
      calc
        y - x = (z - x) + (s / ‖z - x‖) • (z - x) := by
          simp [y, sub_eq_add_neg]
          abel
        _ = (1 : ℝ) • (z - x) + (s / ‖z - x‖) • (z - x) := by simp
        _ = (1 + s / ‖z - x‖) • (z - x) := by rw [← add_smul]
    have hy_dist : dist y x = dist z x + s := by
      rw [dist_eq_norm]
      rw [hy_sub]
      rw [norm_smul]
      have hcoef_nonneg : 0 ≤ 1 + s / ‖z - x‖ := by
        positivity
      rw [Real.norm_of_nonneg hcoef_nonneg, dist_eq_norm]
      field_simp [hzx_norm]
    linarith [Metric.mem_ball.1 hy_ball, hy_dist]

theorem closedBall_twoMul_subset_unitBall_of_mem_halfBall
    {x₀ z : E} {s : ℝ}
    (hx₀ : x₀ ∈ Metric.closedBall (0 : E) (1 / 2 : ℝ))
    (hs : 0 < s)
    (hsub : Metric.closedBall z s ⊆ Metric.ball x₀ (1 / 5 : ℝ)) :
    Metric.closedBall z (2 * s) ⊆ Metric.ball (0 : E) 1 := by
  have hdist : dist z x₀ + s < 1 / 5 := dist_add_lt_of_closedBall_subset_ball hs hsub
  have hs_small : s < 1 / 5 := by
    have hdist_nonneg : 0 ≤ dist z x₀ := dist_nonneg
    linarith
  intro y hy
  have hyz : dist y z ≤ 2 * s := by simpa using hy
  have hx₀_half : dist x₀ (0 : E) ≤ 1 / 2 := by
    simpa [dist_comm] using hx₀
  have hyx₀ : dist y x₀ < 2 / 5 := by
    calc
      dist y x₀ ≤ dist y z + dist z x₀ := dist_triangle _ _ _
      _ ≤ 2 * s + dist z x₀ := by linarith
      _ < 2 / 5 := by linarith
  rw [Metric.mem_ball]
  calc
    dist y (0 : E) ≤ dist y x₀ + dist x₀ (0 : E) := dist_triangle _ _ _
    _ < 2 / 5 + 1 / 2 := by linarith
    _ < 1 := by norm_num

theorem add_const_isSupersolution_unitBall
    (A : NormalizedEllipticCoeff d (Metric.ball (0 : E) 1))
    {u : E → ℝ}
    (hsuper : IsSupersolution A.1 u)
    (ε : ℝ) :
    IsSupersolution A.1 (fun x => u x + ε) := by
  simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
    (IsSupersolution.sub_const_ball (d := d) (c := (0 : E)) (r := (1 : ℝ))
      (by norm_num) (A := A.1) (u := u) hsuper (-ε))

theorem weak_harnack_stage_one_forward_ball
    (hd : 2 < (d : ℝ))
    (A : NormalizedEllipticCoeff d (Metric.ball (0 : E) 1))
    {x₀ : E} {R : ℝ} (hR : 0 < R)
    (hsub : Metric.closedBall x₀ R ⊆ Metric.ball (0 : E) 1)
    {u : E → ℝ} {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hpq : p < q) (hq1 : q < 1)
    (hu_pos : ∀ x ∈ Metric.ball (0 : E) 1, 0 < u x)
    (hsuper : IsSupersolution A.1 u) :
    (((R ^ Module.finrank ℝ E)⁻¹ *
        ∫ x in Metric.ball x₀ (R / 2 : ℝ),
          |u x| ^ (q * (d : ℝ) / ((d : ℝ) - 2)) ∂volume)) ^
          (p * (((d : ℝ) - 2) / (q * (d : ℝ)))) ≤
      C_weakHarnack0Forward (d := d) hd *
        (A.1.Λ * p ^ 2 / (1 - q) ^ 2 + 1) ^ (((d : ℝ) * moserChi d) / 2) *
        ((R ^ Module.finrank ℝ E)⁻¹ *
          ∫ x in Metric.ball x₀ R, |u x| ^ p ∂volume) := by
  let ALoc : NormalizedEllipticCoeff d (Metric.ball x₀ R) :=
    NormalizedEllipticCoeff.restrict A (Metric.ball_subset_closedBall.trans hsub)
  let uR : E → ℝ := rescaleToUnitBall (d := d) (x₀ := x₀) (R := R) u
  let AR : NormalizedEllipticCoeff d (Metric.ball (0 : E) 1) :=
    rescaleNormalizedCoeffToUnitBall (d := d) (x₀ := x₀) (R := R) hR ALoc
  have hsuperLoc : IsSupersolution ALoc.1 u := by
    simpa [ALoc] using hsuper.restrict_ball (d := d) Metric.isOpen_ball hR hsub
  have hposR : ∀ z ∈ Metric.ball (0 : E) 1, 0 < uR z := by
    intro z hz
    have hz_ball : x₀ + R • z ∈ Metric.ball x₀ R := by
      have hz_norm : ‖z‖ < 1 := by
        simpa [Metric.mem_ball, dist_eq_norm, sub_zero] using hz
      rw [Metric.mem_ball, dist_eq_norm]
      have hnorm : ‖x₀ + R • z - x₀‖ = R * ‖z‖ := by
        rw [show x₀ + R • z - x₀ = R • z by abel, norm_smul, Real.norm_of_nonneg hR.le]
      rw [hnorm]
      nlinarith
    exact hu_pos _ (hsub <| Metric.mem_closedBall.2 (le_of_lt hz_ball))
  have hsuperR : IsSupersolution AR.1 uR := by
    change IsSupersolution
      (rescaleCoeffToUnitBall (d := d) (x₀ := x₀) (R := R) hR ALoc.1)
      (rescaleToUnitBall (d := d) (x₀ := x₀) (R := R) u)
    exact rescaleToUnitBall_isSupersolution (d := d) (x₀ := x₀) (R := R) hR ALoc.1 hsuperLoc
  have hbase := weak_harnack_stage_one_forward (d := d) hd AR hp hp1 hpq hq1 hposR hsuperR
  have hhalf_eq :
      ∫ z in Metric.ball (0 : E) (1 / 2 : ℝ),
          |uR z| ^ (q * (d : ℝ) / ((d : ℝ) - 2)) ∂volume =
        (R ^ Module.finrank ℝ E)⁻¹ *
          ∫ x in Metric.ball x₀ (R / 2 : ℝ),
            |u x| ^ (q * (d : ℝ) / ((d : ℝ) - 2)) ∂volume := by
    dsimp [uR]
    simpa [show R * (1 / 2 : ℝ) = R / 2 by ring] using
      crossover_integral_comp_affine_ball (x₀ := x₀) (R := R) (ρ := (1 / 2 : ℝ)) hR
        (fun x => |u x| ^ (q * (d : ℝ) / ((d : ℝ) - 2)))
  have hunit_eq :
      ∫ z in Metric.ball (0 : E) 1, |uR z| ^ p ∂volume =
        (R ^ Module.finrank ℝ E)⁻¹ *
          ∫ x in Metric.ball x₀ R, |u x| ^ p ∂volume := by
    dsimp [uR]
    simpa using
      crossover_integral_comp_affine_ball (x₀ := x₀) (R := R) (ρ := (1 : ℝ)) hR
        (fun x => |u x| ^ p)
  rw [hhalf_eq, hunit_eq] at hbase
  simpa [AR, ALoc, rescaleNormalizedCoeffToUnitBall, rescaleCoeffToUnitBall,
    NormalizedEllipticCoeff.restrict, EllipticCoeff.restrict] using hbase

theorem weak_harnack_stage_one_inverse_ball
    (hd : 2 < (d : ℝ))
    (A : NormalizedEllipticCoeff d (Metric.ball (0 : E) 1))
    {x₀ : E} {R : ℝ} (hR : 0 < R)
    (hsub : Metric.closedBall x₀ R ⊆ Metric.ball (0 : E) 1)
    {u : E → ℝ} {p : ℝ}
    (hp : 0 < p)
    (hu_pos : ∀ x ∈ Metric.ball (0 : E) 1, 0 < u x)
    (hsuper : IsSupersolution A.1 u) :
    (A.1.Λ * p ^ 2 + 1) ^ (-(d : ℝ) / 2) *
        ((R ^ Module.finrank ℝ E)⁻¹ *
          ∫ x in Metric.ball x₀ R, |(u x)⁻¹| ^ p ∂volume)⁻¹ ≤
      C_weakHarnack0 d *
        (essInf u (volume.restrict (Metric.ball x₀ (R / 2 : ℝ)))) ^ p := by
  let ALoc : NormalizedEllipticCoeff d (Metric.ball x₀ R) :=
    NormalizedEllipticCoeff.restrict A (Metric.ball_subset_closedBall.trans hsub)
  let uR : E → ℝ := rescaleToUnitBall (d := d) (x₀ := x₀) (R := R) u
  let AR : NormalizedEllipticCoeff d (Metric.ball (0 : E) 1) :=
    rescaleNormalizedCoeffToUnitBall (d := d) (x₀ := x₀) (R := R) hR ALoc
  have hsuperLoc : IsSupersolution ALoc.1 u := by
    simpa [ALoc] using hsuper.restrict_ball (d := d) Metric.isOpen_ball hR hsub
  have hposR : ∀ z ∈ Metric.ball (0 : E) 1, 0 < uR z := by
    intro z hz
    have hz_ball : x₀ + R • z ∈ Metric.ball x₀ R := by
      have hz_norm : ‖z‖ < 1 := by
        simpa [Metric.mem_ball, dist_eq_norm, sub_zero] using hz
      rw [Metric.mem_ball, dist_eq_norm]
      have hnorm : ‖x₀ + R • z - x₀‖ = R * ‖z‖ := by
        rw [show x₀ + R • z - x₀ = R • z by abel, norm_smul, Real.norm_of_nonneg hR.le]
      rw [hnorm]
      nlinarith
    exact hu_pos _ (hsub <| Metric.mem_closedBall.2 (le_of_lt hz_ball))
  have hsuperR : IsSupersolution AR.1 uR := by
    change IsSupersolution
      (rescaleCoeffToUnitBall (d := d) (x₀ := x₀) (R := R) hR ALoc.1)
      (rescaleToUnitBall (d := d) (x₀ := x₀) (R := R) u)
    exact rescaleToUnitBall_isSupersolution (d := d) (x₀ := x₀) (R := R) hR ALoc.1 hsuperLoc
  have hbase := weak_harnack_stage_one_inverse (d := d) hd AR hp hposR hsuperR
  have hess :
      essInf uR (volume.restrict (Metric.ball (0 : E) (1 / 2 : ℝ))) =
        essInf u (volume.restrict (Metric.ball x₀ (R / 2 : ℝ))) := by
    simpa [uR] using essInf_rescale_halfBall (d := d) (x₀ := x₀) (R := R) hR
  have hunit_eq :
      ∫ z in Metric.ball (0 : E) 1, |(uR z)⁻¹| ^ p ∂volume =
        (R ^ Module.finrank ℝ E)⁻¹ *
          ∫ x in Metric.ball x₀ R, |(u x)⁻¹| ^ p ∂volume := by
    dsimp [uR]
    simpa using
      crossover_integral_comp_affine_ball (x₀ := x₀) (R := R) (ρ := (1 : ℝ)) hR
        (fun x => |(u x)⁻¹| ^ p)
  rw [hess] at hbase
  rw [hunit_eq] at hbase
  simpa [AR, ALoc, rescaleNormalizedCoeffToUnitBall, rescaleCoeffToUnitBall,
    NormalizedEllipticCoeff.restrict, EllipticCoeff.restrict] using hbase

theorem regularizedLog_unit_halfBall_meanOscillation
    (A : NormalizedEllipticCoeff d (Metric.ball (0 : E) 1))
    {u : E → ℝ}
    (hu_pos : ∀ x ∈ Metric.ball (0 : E) 1, 0 < u x)
    (hsuper : IsSupersolution A.1 u)
    {ε : ℝ} (hε : 0 < ε) :
    let v := regularizedLogFun (u := u) hε
    (⨍ x in Metric.ball (0 : E) (1 / 2 : ℝ),
        |v x - ⨍ y in Metric.ball (0 : E) (1 / 2 : ℝ), v y ∂volume| ∂volume) ≤
      c_crossover_bmo_scale d * A.1.Λ ^ ((1 : ℝ) / 2) := by
  intro v
  let Ω : Set E := Metric.ball (0 : E) 1
  let Bhalf : Set E := Metric.ball (0 : E) (1 / 2 : ℝ)
  let hw_u : MemW1pWitness 2 u Ω :=
    (isSupersolution_memW1p hsuper).someWitness
  let hw_v : MemW1pWitness 2 v Ω := by
    simpa [v, Ω] using regularizedLogWitness (Ω := Ω) Metric.isOpen_ball hu_pos hw_u hε
  let hw_v_half : MemW1pWitness 2 v Bhalf :=
    hw_v.restrict Metric.isOpen_ball (Metric.ball_subset_ball (by norm_num))
  obtain ⟨η, _⟩ := Cutoff.exists (d := d) (0 : E)
    (r := (1 / 2 : ℝ)) (R := (3 / 4 : ℝ)) (by norm_num) (by norm_num)
  have hη_cs : HasCompactSupport η.toFun := by
    apply HasCompactSupport.intro' (K := Metric.closedBall (0 : E) (3 / 4 : ℝ))
    · exact isCompact_closedBall (0 : E) (3 / 4 : ℝ)
    · exact isClosed_closedBall
    · intro x hx
      exact zero_outside_of_tsupport_subset (Ω := Metric.closedBall (0 : E) (3 / 4 : ℝ))
        η.support_subset hx
  have hη_sub : tsupport η.toFun ⊆ Ω := by
    exact η.support_subset.trans (Metric.closedBall_subset_ball (by norm_num : (3 / 4 : ℝ) < 1))
  have hlog :=
    log_gradient_bound_eps (Ω := Ω) Metric.isOpen_ball A.1 hu_pos hsuper
      η.smooth hη_cs hη_sub hw_u hε
  have hfactor_meas :
      AEStronglyMeasurable
        (fun x => η.toFun x ^ 2 / (u x + ε) ^ 2)
        (volume.restrict Ω) := by
    have hη_meas : Measurable η.toFun := η.smooth.continuous.measurable
    have hnum_ae :
        AEStronglyMeasurable (fun x => η.toFun x ^ 2) (volume.restrict Ω) :=
      (hη_meas.pow_const 2).aestronglyMeasurable
    have hden_ae :
        AEStronglyMeasurable (fun x => ((u x + ε) ^ 2)⁻¹) (volume.restrict Ω) := by
      have hden_ae' :
          AEMeasurable (fun x => ((u x + ε) ^ 2)⁻¹) (volume.restrict Ω) := by
        exact AEMeasurable.inv (((hw_u.memLp.aestronglyMeasurable.add_const ε).pow 2).aemeasurable)
      exact hden_ae'.aestronglyMeasurable
    simpa [div_eq_mul_inv] using hnum_ae.mul hden_ae
  have hfactor_bound :
      ∀ᵐ x ∂(volume.restrict Ω), |η.toFun x ^ 2 / (u x + ε) ^ 2| ≤ 1 / ε ^ 2 := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    have hηsq_le : η.toFun x ^ 2 ≤ 1 := by
      have hη_nonneg : 0 ≤ η.toFun x := η.nonneg x
      have hη_le : η.toFun x ≤ 1 := η.le_one x
      nlinarith
    have hux : 0 < u x := hu_pos x hx
    have hfrac :
        η.toFun x ^ 2 / (u x + ε) ^ 2 ≤ 1 / ε ^ 2 := by
      have hden : ε ^ 2 ≤ (u x + ε) ^ 2 := by
        nlinarith [hux, hε]
      have hinv :
          1 / (u x + ε) ^ 2 ≤ 1 / ε ^ 2 := by
        exact one_div_le_one_div_of_le (by positivity) hden
      have hmono :
          η.toFun x ^ 2 / (u x + ε) ^ 2 ≤ 1 / (u x + ε) ^ 2 := by
        exact div_le_div_of_nonneg_right hηsq_le (sq_nonneg (u x + ε))
      exact hmono.trans hinv
    have hnonneg : 0 ≤ η.toFun x ^ 2 / (u x + ε) ^ 2 := by positivity
    rw [abs_of_nonneg hnonneg]
    exact hfrac
  have hweight_int :
      IntegrableOn
        (fun x => η.toFun x ^ 2 / (u x + ε) ^ 2 * ‖hw_u.weakGrad x‖ ^ 2)
        Ω volume := by
    simpa [Ω, mul_assoc, mul_left_comm, mul_comm] using
      (hw_u.weakGrad_norm_memLp.integrable_sq).bdd_mul
        (c := 1 / ε ^ 2) hfactor_meas hfactor_bound
  have hhalf_eq :
      ∫ x in Bhalf, ‖hw_v_half.weakGrad x‖ ^ 2 ∂volume =
        ∫ x in Bhalf, η.toFun x ^ 2 / (u x + ε) ^ 2 * ‖hw_u.weakGrad x‖ ^ 2 ∂volume := by
    apply MeasureTheory.setIntegral_congr_fun measurableSet_ball
    intro x hx
    have hxΩ : x ∈ Ω := Metric.ball_subset_ball (by norm_num : (1 / 2 : ℝ) ≤ 1) hx
    have hux : 0 < u x := hu_pos x hxΩ
    have hvec :
        hw_v_half.weakGrad x = (-(1 / (u x + ε))) • hw_u.weakGrad x := by
      have hgrad := regularizedLogWitness_grad (Ω := Ω) Metric.isOpen_ball hu_pos hw_u hε
      ext i
      simpa [hw_v_half, Pi.smul_apply, smul_eq_mul] using
        hgrad x hxΩ i
    have hηx : η.toFun x = 1 := η.eq_one x hx
    calc
      ‖hw_v_half.weakGrad x‖ ^ 2
          = (1 / (u x + ε)) ^ 2 * ‖hw_u.weakGrad x‖ ^ 2 := by
              rw [hvec, norm_smul, Real.norm_eq_abs, abs_neg,
                abs_of_pos (one_div_pos.mpr (by linarith : 0 < u x + ε))]
              ring
      _ = η.toFun x ^ 2 / (u x + ε) ^ 2 * ‖hw_u.weakGrad x‖ ^ 2 := by
            rw [hηx]
            field_simp [show u x + ε ≠ 0 by linarith]
  have hhalf_le :
      ∫ x in Bhalf, η.toFun x ^ 2 / (u x + ε) ^ 2 * ‖hw_u.weakGrad x‖ ^ 2 ∂volume ≤
        ∫ x in Ω, η.toFun x ^ 2 / (u x + ε) ^ 2 * ‖hw_u.weakGrad x‖ ^ 2 ∂volume := by
    exact MeasureTheory.setIntegral_mono_set hweight_int
      (ae_of_all _ (by intro x; positivity))
      (ae_of_all _ (Metric.ball_subset_ball (by norm_num : (1 / 2 : ℝ) ≤ 1))
        )
  have hgrad_sq_bound :
      ∫ x in Bhalf, ‖hw_v_half.weakGrad x‖ ^ 2 ∂volume ≤
        4 * A.1.Λ * ∫ x in Ω, ‖fderiv ℝ η.toFun x‖ ^ 2 ∂volume := by
    have hlog' :
        ∫ x in Ω, η.toFun x ^ 2 * ‖hw_u.weakGrad x‖ ^ 2 / (u x + ε) ^ 2 ∂volume ≤
          4 * A.1.Λ * ∫ x in Ω, ‖fderiv ℝ η.toFun x‖ ^ 2 ∂volume := by
      simpa [A.lam_eq_one] using hlog
    have hlog'' :
        ∫ x in Ω, η.toFun x ^ 2 / (u x + ε) ^ 2 * ‖hw_u.weakGrad x‖ ^ 2 ∂volume ≤
          4 * A.1.Λ * ∫ x in Ω, ‖fderiv ℝ η.toFun x‖ ^ 2 ∂volume := by
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hlog'
    rw [hhalf_eq]
    exact le_trans hhalf_le hlog''
  have hderiv_sq_int :
      IntegrableOn (fun x => ‖fderiv ℝ η.toFun x‖ ^ 2) Ω volume := by
    have hmeas : AEStronglyMeasurable (fun x => ‖fderiv ℝ η.toFun x‖ ^ 2) volume := by
      have hmeas' : Measurable (fun x => ‖fderiv ℝ η.toFun x‖ ^ 2) := by
        fun_prop
      exact hmeas'.aestronglyMeasurable
    have hbd :
        ∀ᵐ x ∂(volume.restrict Ω), ‖‖fderiv ℝ η.toFun x‖ ^ 2‖ ≤ (4 * (Mst : ℝ)) ^ 2 := by
      filter_upwards with x
      have hgrad_bd :
          ‖fderiv ℝ η.toFun x‖ ≤ (Mst : ℝ) * (((3 / 4 : ℝ) - 1 / 2)⁻¹) := by
        simpa using η.grad_bound x
      have hgrad_bd' : ‖fderiv ℝ η.toFun x‖ ≤ 4 * (Mst : ℝ) := by
        have hgrad_bd'' : ‖fderiv ℝ η.toFun x‖ ≤ (Mst : ℝ) * 4 := by
          calc
            ‖fderiv ℝ η.toFun x‖ ≤ (Mst : ℝ) * (((3 / 4 : ℝ) - 1 / 2)⁻¹) := hgrad_bd
            _ = (Mst : ℝ) * 4 := by norm_num
        simpa [mul_comm] using hgrad_bd''
      have hsq_nonneg : 0 ≤ ‖fderiv ℝ η.toFun x‖ ^ 2 := by positivity
      have hsq : ‖fderiv ℝ η.toFun x‖ ^ 2 ≤ (4 * (Mst : ℝ)) ^ 2 := by
        nlinarith [hgrad_bd', norm_nonneg (fderiv ℝ η.toFun x)]
      rw [Real.norm_of_nonneg hsq_nonneg]
      exact hsq
    exact Measure.integrableOn_of_bounded
      (s_finite := by simpa [Ω] using measure_ball_lt_top.ne)
      hmeas hbd
  have hderiv_sq_bound :
      ∫ x in Ω, ‖fderiv ℝ η.toFun x‖ ^ 2 ∂volume ≤
        (4 * (Mst : ℝ)) ^ 2 * volume.real Ω := by
    have hmono := MeasureTheory.setIntegral_mono (μ := volume) (s := Ω)
      (f := fun x => ‖fderiv ℝ η.toFun x‖ ^ 2)
      (g := fun _ : E => (4 * (Mst : ℝ)) ^ 2)
      hderiv_sq_int (integrableOn_const (μ := volume) (show volume Ω ≠ ∞ by simpa [Ω] using measure_ball_lt_top.ne))
      (by
        intro x
        have hgrad_bd :
            ‖fderiv ℝ η.toFun x‖ ≤ (Mst : ℝ) * (((3 / 4 : ℝ) - 1 / 2)⁻¹) := by
          simpa using η.grad_bound x
        have hbd' : ‖fderiv ℝ η.toFun x‖ ≤ 4 * (Mst : ℝ) := by
          have hbd'' : ‖fderiv ℝ η.toFun x‖ ≤ (Mst : ℝ) * 4 := by
            calc
              ‖fderiv ℝ η.toFun x‖ ≤ (Mst : ℝ) * (((3 / 4 : ℝ) - 1 / 2)⁻¹) := hgrad_bd
              _ = (Mst : ℝ) * 4 := by norm_num
          simpa [mul_comm] using hbd''
        have hsq : ‖fderiv ℝ η.toFun x‖ ^ 2 ≤ (4 * (Mst : ℝ)) ^ 2 := by
          nlinarith [hbd', norm_nonneg (fderiv ℝ η.toFun x)]
        exact hsq)
    simpa [Ω, MeasureTheory.setIntegral_const, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc]
      using hmono
  have hgrad_lp_eq :
      MeasureTheory.lpNorm (fun x => ‖hw_v_half.weakGrad x‖) 2 (volume.restrict Bhalf) =
        (∫ x in Bhalf, ‖hw_v_half.weakGrad x‖ ^ 2 ∂volume) ^ ((1 : ℝ) / 2) := by
    simpa using
      (MeasureTheory.lpNorm_eq_integral_norm_rpow_toReal
        (μ := volume.restrict Bhalf) (p := (2 : ℝ≥0∞))
        (f := fun x => ‖hw_v_half.weakGrad x‖) (by norm_num) (by norm_num)
        hw_v_half.weakGrad_norm_memLp.aestronglyMeasurable)
  have hgrad_lp_bound :
      MeasureTheory.lpNorm (fun x => ‖hw_v_half.weakGrad x‖) 2 (volume.restrict Bhalf) ≤
        8 * (Mst : ℝ) * A.1.Λ ^ ((1 : ℝ) / 2) * (volume.real Ω) ^ ((1 : ℝ) / 2) := by
    rw [hgrad_lp_eq]
    have hgrad_sq_bound' :
        ∫ x in Bhalf, ‖hw_v_half.weakGrad x‖ ^ 2 ∂volume ≤
          4 * A.1.Λ * ((4 * (Mst : ℝ)) ^ 2 * volume.real Ω) := by
      calc
        ∫ x in Bhalf, ‖hw_v_half.weakGrad x‖ ^ 2 ∂volume
            ≤ 4 * A.1.Λ * ∫ x in Ω, ‖fderiv ℝ η.toFun x‖ ^ 2 ∂volume := hgrad_sq_bound
        _ ≤ 4 * A.1.Λ * ((4 * (Mst : ℝ)) ^ 2 * volume.real Ω) := by
              exact mul_le_mul_of_nonneg_left hderiv_sq_bound (by nlinarith [A.1.Λ_nonneg])
    have hmain :
        (∫ x in Bhalf, ‖hw_v_half.weakGrad x‖ ^ 2 ∂volume) ^
            ((1 : ℝ) / 2) ≤
          (4 * A.1.Λ * ((4 * (Mst : ℝ)) ^ 2 * volume.real Ω)) ^ ((1 : ℝ) / 2) := by
      exact Real.rpow_le_rpow (by positivity) hgrad_sq_bound' (by norm_num)
    refine le_trans hmain ?_
    have hcalc :
        (4 * A.1.Λ * ((4 * (Mst : ℝ)) ^ 2 * volume.real Ω)) ^ ((1 : ℝ) / 2) =
          8 * (Mst : ℝ) * A.1.Λ ^ ((1 : ℝ) / 2) * (volume.real Ω) ^ ((1 : ℝ) / 2) := by
      have hsqrt4 :
          (4 * A.1.Λ) ^ ((1 : ℝ) / 2) = 2 * A.1.Λ ^ ((1 : ℝ) / 2) := by
        rw [Real.mul_rpow (by positivity : 0 ≤ (4 : ℝ)) A.1.Λ_nonneg]
        norm_num [Real.sqrt_eq_rpow]
      rw [show 4 * A.1.Λ * ((4 * (Mst : ℝ)) ^ 2 * volume.real Ω) =
            (4 * A.1.Λ) * ((4 * (Mst : ℝ)) ^ 2 * volume.real Ω) by ring,
        Real.mul_rpow (by nlinarith [A.1.Λ_nonneg] : 0 ≤ 4 * A.1.Λ)
          (by positivity : 0 ≤ (4 * (Mst : ℝ)) ^ 2 * volume.real Ω),
        Real.mul_rpow (by positivity : 0 ≤ (4 * (Mst : ℝ)) ^ 2)
          (by positivity : 0 ≤ volume.real Ω),
        show ((4 * (Mst : ℝ)) ^ 2) ^ ((1 : ℝ) / 2) = 4 * (Mst : ℝ) by
          rw [← Real.sqrt_eq_rpow, Real.sqrt_sq]
          positivity,
        hsqrt4]
      ring
    rw [hcalc]
  calc
    (⨍ x in Bhalf, |v x - ⨍ y in Bhalf, v y ∂volume| ∂volume)
        ≤ Cmo * (1 / 2 : ℝ) ^ (1 - (d : ℝ) / 2) *
            MeasureTheory.lpNorm (fun x => ‖hw_v_half.weakGrad x‖) 2
              (volume.restrict Bhalf) := by
            simpa [Bhalf, hw_v_half] using
              (crossover_average_abs_sub_average_ball_le_grad_lpNorm_two
                (u := v) (x₀ := (0 : E)) (R := (1 / 2 : ℝ))
                (by norm_num) hw_v_half)
    _ ≤ Cmo * (1 / 2 : ℝ) ^ (1 - (d : ℝ) / 2) *
          (8 * (Mst : ℝ) * A.1.Λ ^ ((1 : ℝ) / 2) * (volume.real Ω) ^ ((1 : ℝ) / 2)) := by
            have hfac_nonneg : 0 ≤ Cmo * (1 / 2 : ℝ) ^ (1 - (d : ℝ) / 2) := by
              have hd_pos : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
              rw [show Cmo =
                (volume.real (Metric.ball (0 : E) 1)) ^ (-(1 / 2 : ℝ)) * C_poinc_val d by rfl]
              exact mul_nonneg
                (mul_nonneg
                  (Real.rpow_nonneg MeasureTheory.measureReal_nonneg _)
                  (C_poinc_val_pos hd_pos).le)
                (Real.rpow_nonneg (by positivity : 0 ≤ (1 / 2 : ℝ)) _)
            exact mul_le_mul_of_nonneg_left hgrad_lp_bound hfac_nonneg
    _ = c_crossover_bmo_scale d * A.1.Λ ^ ((1 : ℝ) / 2) := by
          change
            (((volume.real (Metric.ball (0 : E) 1)) ^ (-(1 / 2 : ℝ)) * C_poinc_val d) *
              (1 / 2 : ℝ) ^ (1 - (d : ℝ) / 2) *
              (8 * (Mst : ℝ) * A.1.Λ ^ ((1 : ℝ) / 2) *
                (volume.real (Metric.ball (0 : E) 1)) ^ ((1 : ℝ) / 2))) =
              c_crossover_bmo_scale d * A.1.Λ ^ ((1 : ℝ) / 2)
          simp [c_crossover_bmo_scale, mul_assoc, mul_left_comm, mul_comm]

theorem regularizedLog_ball_meanOscillation
    (A : NormalizedEllipticCoeff d (Metric.ball (0 : E) 1))
    {x₀ : E} {R : ℝ} (hR : 0 < R)
    (hsub : Metric.closedBall x₀ R ⊆ Metric.ball (0 : E) 1)
    {u : E → ℝ}
    (hu_pos : ∀ x ∈ Metric.ball (0 : E) 1, 0 < u x)
    (hsuper : IsSupersolution A.1 u)
    {ε : ℝ} (hε : 0 < ε) :
    let v := regularizedLogFun (u := u) hε
    (⨍ x in Metric.ball x₀ (R / 2 : ℝ),
        |v x - ⨍ y in Metric.ball x₀ (R / 2 : ℝ), v y ∂volume| ∂volume) ≤
      c_crossover_bmo_scale d * A.1.Λ ^ ((1 : ℝ) / 2) := by
  intro v
  let ALoc : NormalizedEllipticCoeff d (Metric.ball x₀ R) :=
    NormalizedEllipticCoeff.restrict A (Metric.ball_subset_closedBall.trans hsub)
  let uR : E → ℝ := rescaleToUnitBall (d := d) (x₀ := x₀) (R := R) u
  let AR : NormalizedEllipticCoeff d (Metric.ball (0 : E) 1) :=
    rescaleNormalizedCoeffToUnitBall (d := d) (x₀ := x₀) (R := R) hR ALoc
  have hsuperLoc : IsSupersolution ALoc.1 u := by
    simpa [ALoc] using hsuper.restrict_ball (d := d) Metric.isOpen_ball hR hsub
  have hposR : ∀ z ∈ Metric.ball (0 : E) 1, 0 < uR z := by
    intro z hz
    have hz_ball : x₀ + R • z ∈ Metric.ball x₀ R := by
      have hz_norm : ‖z‖ < 1 := by
        simpa [Metric.mem_ball, dist_eq_norm, sub_zero] using hz
      rw [Metric.mem_ball, dist_eq_norm]
      have hnorm : ‖x₀ + R • z - x₀‖ = R * ‖z‖ := by
        rw [show x₀ + R • z - x₀ = R • z by abel, norm_smul, Real.norm_of_nonneg hR.le]
      rw [hnorm]
      nlinarith
    exact hu_pos _ (hsub <| Metric.mem_closedBall.2 (le_of_lt hz_ball))
  have hsuperR : IsSupersolution AR.1 uR := by
    change IsSupersolution
      (rescaleCoeffToUnitBall (d := d) (x₀ := x₀) (R := R) hR ALoc.1)
      (rescaleToUnitBall (d := d) (x₀ := x₀) (R := R) u)
    exact rescaleToUnitBall_isSupersolution (d := d) (x₀ := x₀) (R := R) hR ALoc.1 hsuperLoc
  have hunit :=
    regularizedLog_unit_halfBall_meanOscillation (d := d) (A := AR) hposR hsuperR hε
  have havg :
      ⨍ y in Metric.ball (0 : E) (1 / 2 : ℝ), regularizedLogFun (u := uR) hε y ∂volume =
        ⨍ y in Metric.ball x₀ (R / 2 : ℝ), v y ∂volume := by
    simpa [uR, v, show R * (1 / 2 : ℝ) = R / 2 by ring] using
      crossover_average_rescale_ball_radius (x₀ := x₀) (R := R) (ρ := (1 / 2 : ℝ)) hR (by norm_num) v
  have hrescale :
      (⨍ x in Metric.ball x₀ (R / 2 : ℝ),
        |v x - ⨍ y in Metric.ball x₀ (R / 2 : ℝ), v y ∂volume| ∂volume) =
      (⨍ z in Metric.ball (0 : E) (1 / 2 : ℝ),
        |v (x₀ + R • z) - ⨍ y in Metric.ball x₀ (R / 2 : ℝ), v y ∂volume| ∂volume) := by
    symm
    simpa [show R * (1 / 2 : ℝ) = R / 2 by ring] using
      crossover_average_abs_sub_average_rescale_ball_radius
        (u := v) (x₀ := x₀) (R := R) (ρ := (1 / 2 : ℝ)) hR (by norm_num)
  have hunit' :
      (⨍ z in Metric.ball (0 : E) (1 / 2 : ℝ),
        |v (x₀ + R • z) - ⨍ y in Metric.ball x₀ (R / 2 : ℝ), v y ∂volume| ∂volume) ≤
      c_crossover_bmo_scale d * A.1.Λ ^ ((1 : ℝ) / 2) := by
    have hcomp :
        (fun z => regularizedLogFun (u := uR) hε z) =
          fun z => v (x₀ + R • z) := by
      funext z
      rfl
    have havg' :
        ⨍ y in Metric.ball (0 : E) (1 / 2 : ℝ), v (x₀ + R • y) ∂volume =
          ⨍ y in Metric.ball x₀ (R / 2 : ℝ), v y ∂volume := by
      simpa [show R * (1 / 2 : ℝ) = R / 2 by ring] using
        crossover_average_rescale_ball_radius (x₀ := x₀) (R := R) (ρ := (1 / 2 : ℝ)) hR (by norm_num) v
    have hunit'' :
        (⨍ z in Metric.ball (0 : E) (1 / 2 : ℝ),
          |regularizedLogFun (u := uR) hε z -
              ⨍ y in Metric.ball (0 : E) (1 / 2 : ℝ),
                regularizedLogFun (u := uR) hε y ∂volume| ∂volume) ≤
        c_crossover_bmo_scale d * A.1.Λ ^ ((1 : ℝ) / 2) := by
      simpa [AR, ALoc, rescaleNormalizedCoeffToUnitBall, rescaleCoeffToUnitBall,
        NormalizedEllipticCoeff.restrict, EllipticCoeff.restrict] using hunit
    have hunit''' :
        (⨍ z in Metric.ball (0 : E) (1 / 2 : ℝ),
          |v (x₀ + R • z) -
              ⨍ y in Metric.ball (0 : E) (1 / 2 : ℝ), v (x₀ + R • y) ∂volume| ∂volume) ≤
        c_crossover_bmo_scale d * A.1.Λ ^ ((1 : ℝ) / 2) := by
      simpa [hcomp] using hunit''
    have hunit'''' := hunit'''
    rw [havg'] at hunit''''
    exact hunit''''
  rw [hrescale]
  exact hunit'

lemma crossover_bmo_scale_nonneg : 0 ≤ c_crossover_bmo_scale d := by
  let B1 : Set E := Metric.ball (0 : E) 1
  have hvol_pos : 0 < volume.real B1 := by
    exact ENNReal.toReal_pos
      (measure_ball_pos (μ := volume) (0 : E) (by norm_num : (0 : ℝ) < 1)).ne'
      (measure_ball_lt_top (μ := volume) (x := (0 : E)) (r := (1 : ℝ))).ne
  have hd_pos : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  have hCp_nonneg : 0 ≤ C_poinc_val d := le_of_lt (C_poinc_val_pos (d := d) hd_pos)
  unfold c_crossover_bmo_scale
  have h1 : 0 ≤ (volume.real B1) ^ (-(1 / 2 : ℝ)) := by
    exact Real.rpow_nonneg hvol_pos.le _
  have h2 : 0 ≤ (1 / 2 : ℝ) ^ (1 - (d : ℝ) / 2) := by
    exact Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) _
  have h3 : 0 ≤ 8 * (Mst : ℝ) * (volume.real B1) ^ ((1 : ℝ) / 2) := by
    refine mul_nonneg ?_ ?_
    · positivity
    · exact Real.rpow_nonneg hvol_pos.le _
  have hleft_nonneg :
      0 ≤
        ((volume.real B1) ^ (-(1 / 2 : ℝ)) * C_poinc_val d) := by
    exact mul_nonneg h1 hCp_nonneg
  have hright_nonneg :
      0 ≤
        (1 / 2 : ℝ) ^ (1 - (d : ℝ) / 2) *
          (8 * (Mst : ℝ) * (volume.real B1) ^ ((1 : ℝ) / 2)) := by
    exact mul_nonneg h2 h3
  have hfirst_nonneg :
      0 ≤
        ((volume.real B1) ^ (-(1 / 2 : ℝ)) * C_poinc_val d) *
          (1 / 2 : ℝ) ^ (1 - (d : ℝ) / 2) := by
    exact mul_nonneg hleft_nonneg h2
  have htotal_nonneg :
      0 ≤
        (((volume.real B1) ^ (-(1 / 2 : ℝ)) * C_poinc_val d) *
          (1 / 2 : ℝ) ^ (1 - (d : ℝ) / 2)) *
          (8 * (Mst : ℝ) * (volume.real B1) ^ ((1 : ℝ) / 2)) := by
    exact mul_nonneg hfirst_nonneg h3
  simpa [c_crossover_bmo_scale, B1, mul_assoc] using htotal_nonneg

lemma crossoverC'_pos : 0 < c_crossover' d := by
  unfold c_crossover'
  have hbmo_nonneg : 0 ≤ c_crossover_bmo_scale d := crossover_bmo_scale_nonneg (d := d)
  have hCJN_nonneg : 0 ≤ C_JN d := (C_JN_pos d).le
  have hX_nonneg : 0 ≤ C_JN d * c_crossover_bmo_scale d := by
    exact mul_nonneg hCJN_nonneg hbmo_nonneg
  have hden_pos : 0 < 2 * C_JN d * c_crossover_bmo_scale d + 1 := by
    nlinarith
  simpa [one_div] using (inv_pos.mpr hden_pos)

lemma c_crossover'_le_one : c_crossover' d ≤ 1 := by
  unfold c_crossover'
  have hbmo_nonneg : 0 ≤ c_crossover_bmo_scale d := crossover_bmo_scale_nonneg (d := d)
  have hCJN_nonneg : 0 ≤ C_JN d := (C_JN_pos d).le
  have hden_ge_one : 1 ≤ 2 * C_JN d * c_crossover_bmo_scale d + 1 := by
    nlinarith
  simpa [one_div] using (inv_le_one_of_one_le₀ hden_ge_one)

theorem crossover_abs_rpow_neg_eq_abs_inv_rpow
    {a p : ℝ} (ha : 0 < a) :
    |a| ^ (-p) = |a⁻¹| ^ p := by
  rw [abs_of_pos ha, abs_of_pos (inv_pos.mpr ha)]
  calc
    a ^ (-p) = (a ^ p)⁻¹ := by
      rw [Real.rpow_neg ha.le]
    _ = (a⁻¹) ^ p := by
      rw [← Real.inv_rpow ha.le]

lemma c_crossover_mul_bmo_le_half
    (A : NormalizedEllipticCoeff d (Metric.ball (0 : E) 1)) :
    (c_crossover' d / A.1.Λ ^ ((1 : ℝ) / 2)) * C_JN d *
        (c_crossover_bmo_scale d * A.1.Λ ^ ((1 : ℝ) / 2)) ≤
      1 / 2 := by
  have hΛpos : 0 < A.1.Λ ^ ((1 : ℝ) / 2) := by
    have hΛge : 1 ≤ A.1.Λ := by
      have := A.1.hΛ
      rw [A.2] at this
      simpa using this
    exact Real.rpow_pos_of_pos (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hΛge) _
  have hcancel :
      (c_crossover' d / A.1.Λ ^ ((1 : ℝ) / 2)) *
          (c_crossover_bmo_scale d * A.1.Λ ^ ((1 : ℝ) / 2)) =
        c_crossover' d * c_crossover_bmo_scale d := by
    field_simp [hΛpos.ne']
  have hscale_nonneg : 0 ≤ c_crossover_bmo_scale d := crossover_bmo_scale_nonneg (d := d)
  have hCJN_nonneg : 0 ≤ C_JN d := (C_JN_pos d).le
  calc
    (c_crossover' d / A.1.Λ ^ ((1 : ℝ) / 2)) * C_JN d *
        (c_crossover_bmo_scale d * A.1.Λ ^ ((1 : ℝ) / 2))
        = c_crossover' d * C_JN d * c_crossover_bmo_scale d := by
            calc
              (c_crossover' d / A.1.Λ ^ ((1 : ℝ) / 2)) * C_JN d *
                  (c_crossover_bmo_scale d * A.1.Λ ^ ((1 : ℝ) / 2))
                  = C_JN d *
                      ((c_crossover' d / A.1.Λ ^ ((1 : ℝ) / 2)) *
                        (c_crossover_bmo_scale d * A.1.Λ ^ ((1 : ℝ) / 2))) := by
                          ring
              _ = C_JN d * (c_crossover' d * c_crossover_bmo_scale d) := by rw [hcancel]
              _ = c_crossover' d * C_JN d * c_crossover_bmo_scale d := by ring
    _ = (C_JN d * c_crossover_bmo_scale d) /
          (2 * C_JN d * c_crossover_bmo_scale d + 1) := by
            unfold c_crossover'
            field_simp
    _ ≤ 1 / 2 := by
          let X : ℝ := C_JN d * c_crossover_bmo_scale d
          have hX_nonneg : 0 ≤ X := by
            dsimp [X]
            exact mul_nonneg hCJN_nonneg hscale_nonneg
          have hden_pos : 0 < 2 * X + 1 := by
            nlinarith
          have haux : X / (2 * X + 1) ≤ 1 / 2 := by
            rw [div_le_iff₀ hden_pos]
            nlinarith
          simpa [X, mul_assoc, mul_left_comm, mul_comm] using haux

lemma regularizedLog_integrableOn_ball
    (A : NormalizedEllipticCoeff d (Metric.ball (0 : E) 1))
    {u : E → ℝ}
    (hu_pos : ∀ x ∈ Metric.ball (0 : E) 1, 0 < u x)
    (hsuper : IsSupersolution A.1 u)
    {x₀ : E} {R : ℝ}
    (hsub : Metric.ball x₀ R ⊆ Metric.ball (0 : E) 1)
    {ε : ℝ} (hε : 0 < ε) :
    IntegrableOn (regularizedLogFun (u := u) hε) (Metric.ball x₀ R) volume := by
  let Ω : Set E := Metric.ball (0 : E) 1
  let hw_u : MemW1pWitness 2 u Ω :=
    (isSupersolution_memW1p hsuper).someWitness
  let hw_v : MemW1pWitness 2 (regularizedLogFun (u := u) hε) Ω := by
    simpa [Ω] using regularizedLogWitness (Ω := Ω) Metric.isOpen_ball hu_pos hw_u hε
  letI : IsFiniteMeasure (volume.restrict (Metric.ball x₀ R)) := by
    refine ⟨?_⟩
    simpa using
      (measure_ball_lt_top (μ := volume) (x := x₀) (r := R))
  have hv_memLp_ball :
      MemLp (regularizedLogFun (u := u) hε) 2 (volume.restrict (Metric.ball x₀ R)) :=
    hw_v.memLp.mono_measure (Measure.restrict_mono hsub le_rfl)
  have hp : (1 : ENNReal) ≤ 2 := by norm_num
  simpa [IntegrableOn] using hv_memLp_ball.integrable hp

omit [NeZero d] in
lemma closedBall_subset_unitBall_of_mem_halfBall_of_le_eighth
    {x₀ : E} {R : ℝ}
    (hx₀ : x₀ ∈ Metric.closedBall (0 : E) (1 / 2 : ℝ))
    (hR : R ≤ (1 / 8 : ℝ)) :
    Metric.closedBall x₀ R ⊆ Metric.ball (0 : E) 1 := by
  intro x hx
  have hx₀' : dist x₀ (0 : E) ≤ 1 / 2 := by simpa using hx₀
  have hx' : dist x x₀ ≤ R := by simpa using hx
  rw [Metric.mem_ball]
  calc
    dist x (0 : E) ≤ dist x x₀ + dist x₀ (0 : E) := dist_triangle _ _ _
    _ ≤ R + 1 / 2 := by linarith
    _ ≤ 1 / 8 + 1 / 2 := by gcongr
    _ < 1 := by norm_num

omit [NeZero d] in
lemma ball_subset_unitBall_of_mem_halfBall_of_le_eighth
    {x₀ : E} {R : ℝ}
    (hx₀ : x₀ ∈ Metric.closedBall (0 : E) (1 / 2 : ℝ))
    (hR : R ≤ (1 / 8 : ℝ)) :
    Metric.ball x₀ R ⊆ Metric.ball (0 : E) 1 :=
  (Metric.ball_subset_closedBall.trans
    (closedBall_subset_unitBall_of_mem_halfBall_of_le_eighth hx₀ hR))

lemma doubled_subball_subset_unitBall_of_closedBall_subset_eighth
    {x₀ z : E} {s : ℝ}
    (hx₀ : x₀ ∈ Metric.closedBall (0 : E) (1 / 2 : ℝ))
    (hs : 0 < s)
    (hsub : Metric.closedBall z s ⊆ Metric.ball x₀ (1 / 8 : ℝ)) :
    Metric.closedBall z (2 * s) ⊆ Metric.ball (0 : E) 1 := by
  intro y hy
  have hdist : dist z x₀ + s < 1 / 8 := dist_add_lt_of_closedBall_subset_ball hs hsub
  have hs_lt : s < 1 / 8 := by
    have hdist_nonneg : 0 ≤ dist z x₀ := by positivity
    have : s ≤ dist z x₀ + s := by nlinarith
    exact lt_of_le_of_lt this hdist
  have hx₀' : dist x₀ (0 : E) ≤ 1 / 2 := by simpa using hx₀
  have hyz : dist y z ≤ 2 * s := by simpa using hy
  rw [Metric.mem_ball]
  calc
    dist y (0 : E) ≤ dist y z + dist z x₀ + dist x₀ (0 : E) := dist_triangle4 _ _ _ _
    _ ≤ 2 * s + dist z x₀ + 1 / 2 := by linarith
    _ = s + (dist z x₀ + s) + 1 / 2 := by ring
    _ < s + 1 / 8 + 1 / 2 := by gcongr
    _ < 1 := by linarith

theorem regularizedLog_smallBallAverage_step_le
    (A : NormalizedEllipticCoeff d (Metric.ball (0 : E) 1))
    {u : E → ℝ}
    (hu_pos : ∀ x ∈ Metric.ball (0 : E) 1, 0 < u x)
    (hsuper : IsSupersolution A.1 u)
    {ε : ℝ} (hε : 0 < ε)
    {x y : E}
    (hx : x ∈ Metric.closedBall (0 : E) (1 / 2 : ℝ))
    (hy : y ∈ Metric.closedBall (0 : E) (1 / 2 : ℝ))
    (hxy : dist x y ≤ (1 / 48 : ℝ)) :
    let v := regularizedLogFun (u := u) hε
    |⨍ z in Metric.ball x (1 / 48 : ℝ), v z ∂volume -
        ⨍ z in Metric.ball y (1 / 48 : ℝ), v z ∂volume|
      ≤ (2 : ℝ) ^ (d + 1) *
          (c_crossover_bmo_scale d * A.1.Λ ^ ((1 : ℝ) / 2)) := by
  intro v
  let c : E := midpoint ℝ x y
  have hr : 0 < (1 / 48 : ℝ) := by norm_num
  have hsubx : Metric.ball c ((1 / 48 : ℝ) / 2) ⊆ Metric.ball x (1 / 48 : ℝ) := by
    intro z hz
    have hcz : dist z c < (1 / 48 : ℝ) / 2 := by simpa [Metric.mem_ball] using hz
    have hcx : dist c x ≤ (1 / 48 : ℝ) / 2 := by
      calc
        dist c x = (1 / 2 : ℝ) * dist x y := by
          simp [c, dist_midpoint_left (𝕜 := ℝ)]
        _ ≤ (1 / 2 : ℝ) * (1 / 48 : ℝ) := by gcongr
        _ = (1 / 48 : ℝ) / 2 := by ring
    rw [Metric.mem_ball]
    exact lt_of_le_of_lt (dist_triangle z c x) (by linarith)
  have hsuby : Metric.ball c ((1 / 48 : ℝ) / 2) ⊆ Metric.ball y (1 / 48 : ℝ) := by
    intro z hz
    have hcz : dist z c < (1 / 48 : ℝ) / 2 := by simpa [Metric.mem_ball] using hz
    have hcy : dist c y ≤ (1 / 48 : ℝ) / 2 := by
      calc
        dist c y = (1 / 2 : ℝ) * dist x y := by
          simp [c, dist_midpoint_right (𝕜 := ℝ)]
        _ ≤ (1 / 2 : ℝ) * (1 / 48 : ℝ) := by gcongr
        _ = (1 / 48 : ℝ) / 2 := by ring
    rw [Metric.mem_ball]
    exact lt_of_le_of_lt (dist_triangle z c y) (by linarith)
  have hintx :
      IntegrableOn v (Metric.ball x (1 / 48 : ℝ)) volume :=
    regularizedLog_integrableOn_ball (d := d) (A := A) hu_pos hsuper
      (ball_subset_unitBall_of_mem_halfBall_of_le_eighth hx (by norm_num)) hε
  have hinty :
      IntegrableOn v (Metric.ball y (1 / 48 : ℝ)) volume :=
    regularizedLog_integrableOn_ball (d := d) (A := A) hu_pos hsuper
      (ball_subset_unitBall_of_mem_halfBall_of_le_eighth hy (by norm_num)) hε
  have hoscx :
      (⨍ z in Metric.ball x (1 / 48 : ℝ),
        |v z - ⨍ w in Metric.ball x (1 / 48 : ℝ), v w ∂volume| ∂volume) ≤
      c_crossover_bmo_scale d * A.1.Λ ^ ((1 : ℝ) / 2) := by
    have hRhalf : ((1 / 24 : ℝ) / 2) = (1 / 48 : ℝ) := by ring
    have hoscx' :=
      regularizedLog_ball_meanOscillation (d := d) (A := A)
        (x₀ := x) (R := (1 / 24 : ℝ)) (by norm_num)
        (closedBall_subset_unitBall_of_mem_halfBall_of_le_eighth hx (by norm_num))
        (u := u) hu_pos hsuper hε
    simpa [v, ← hRhalf] using hoscx'
  have hoscy :
      (⨍ z in Metric.ball y (1 / 48 : ℝ),
        |v z - ⨍ w in Metric.ball y (1 / 48 : ℝ), v w ∂volume| ∂volume) ≤
      c_crossover_bmo_scale d * A.1.Λ ^ ((1 : ℝ) / 2) := by
    have hRhalf : ((1 / 24 : ℝ) / 2) = (1 / 48 : ℝ) := by ring
    have hoscy' :=
      regularizedLog_ball_meanOscillation (d := d) (A := A)
        (x₀ := y) (R := (1 / 24 : ℝ)) (by norm_num)
        (closedBall_subset_unitBall_of_mem_halfBall_of_le_eighth hy (by norm_num))
        (u := u) hu_pos hsuper hε
    simpa [v, ← hRhalf] using hoscy'
  calc
    |⨍ z in Metric.ball x (1 / 48 : ℝ), v z ∂volume -
        ⨍ z in Metric.ball y (1 / 48 : ℝ), v z ∂volume|
        ≤
        |⨍ z in Metric.ball x (1 / 48 : ℝ), v z ∂volume -
            ⨍ z in Metric.ball c ((1 / 48 : ℝ) / 2), v z ∂volume| +
          |⨍ z in Metric.ball c ((1 / 48 : ℝ) / 2), v z ∂volume -
            ⨍ z in Metric.ball y (1 / 48 : ℝ), v z ∂volume| := by
            have habs :=
              abs_add_le
                (⨍ z in Metric.ball x (1 / 48 : ℝ), v z ∂volume -
                  ⨍ z in Metric.ball c ((1 / 48 : ℝ) / 2), v z ∂volume)
                (⨍ z in Metric.ball c ((1 / 48 : ℝ) / 2), v z ∂volume -
                  ⨍ z in Metric.ball y (1 / 48 : ℝ), v z ∂volume)
            simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using habs
    _ ≤ (2 : ℝ) ^ d *
          (⨍ z in Metric.ball x (1 / 48 : ℝ),
            |v z - ⨍ w in Metric.ball x (1 / 48 : ℝ), v w ∂volume| ∂volume) +
        (2 : ℝ) ^ d *
          (⨍ z in Metric.ball y (1 / 48 : ℝ),
            |v z - ⨍ w in Metric.ball y (1 / 48 : ℝ), v w ∂volume| ∂volume) := by
          gcongr
          · simpa [abs_sub_comm] using
              abs_halfSubballAverage_sub_ballAverage_le (u := v) hr hsubx hintx
          · simpa using
              abs_halfSubballAverage_sub_ballAverage_le (u := v) hr hsuby hinty
    _ ≤ (2 : ℝ) ^ (d + 1) *
          (c_crossover_bmo_scale d * A.1.Λ ^ ((1 : ℝ) / 2)) := by
          have hxterm :
              (2 : ℝ) ^ d *
                  (⨍ z in Metric.ball x (1 / 48 : ℝ),
                    |v z - ⨍ w in Metric.ball x (1 / 48 : ℝ), v w ∂volume| ∂volume) ≤
                (2 : ℝ) ^ d * (c_crossover_bmo_scale d * A.1.Λ ^ ((1 : ℝ) / 2)) := by
            exact mul_le_mul_of_nonneg_left hoscx (by positivity)
          have hyterm :
              (2 : ℝ) ^ d *
                  (⨍ z in Metric.ball y (1 / 48 : ℝ),
                    |v z - ⨍ w in Metric.ball y (1 / 48 : ℝ), v w ∂volume| ∂volume) ≤
                (2 : ℝ) ^ d * (c_crossover_bmo_scale d * A.1.Λ ^ ((1 : ℝ) / 2)) := by
            exact mul_le_mul_of_nonneg_left hoscy (by positivity)
          have hsum_le := add_le_add hxterm hyterm
          have hpow :
              (2 : ℝ) ^ (d + 1) * (c_crossover_bmo_scale d * A.1.Λ ^ ((1 : ℝ) / 2)) =
                (2 : ℝ) ^ d * (c_crossover_bmo_scale d * A.1.Λ ^ ((1 : ℝ) / 2)) +
                  (2 : ℝ) ^ d * (c_crossover_bmo_scale d * A.1.Λ ^ ((1 : ℝ) / 2)) := by
            rw [pow_succ']
            ring
          rw [hpow]
          exact hsum_le

noncomputable def regularizedLogAEMeasurable
    (A : NormalizedEllipticCoeff d (Metric.ball (0 : E) 1))
    {u : E → ℝ}
    (hu_pos : ∀ x ∈ Metric.ball (0 : E) 1, 0 < u x)
    (hsuper : IsSupersolution A.1 u)
    {ε : ℝ} (hε : 0 < ε) :
    AEMeasurable (regularizedLogFun (u := u) hε)
      (volume.restrict (Metric.ball (0 : E) 1)) := by
  let Ω : Set E := Metric.ball (0 : E) 1
  let hw_u : MemW1pWitness 2 u Ω :=
    (isSupersolution_memW1p hsuper).someWitness
  let hw_v : MemW1pWitness 2 (regularizedLogFun (u := u) hε) Ω := by
    simpa [Ω] using regularizedLogWitness (Ω := Ω) Metric.isOpen_ball hu_pos hw_u hε
  simpa [Ω] using hw_v.memLp.aestronglyMeasurable.aemeasurable

noncomputable def regularizedLogMeasurable
    (A : NormalizedEllipticCoeff d (Metric.ball (0 : E) 1))
    {u : E → ℝ}
    (hu_pos : ∀ x ∈ Metric.ball (0 : E) 1, 0 < u x)
    (hsuper : IsSupersolution A.1 u)
    {ε : ℝ} (hε : 0 < ε) : E → ℝ :=
  (regularizedLogAEMeasurable (d := d) (A := A) hu_pos hsuper hε).mk
    (regularizedLogFun (u := u) hε)

lemma regularizedLogMeasurable_measurable
    (A : NormalizedEllipticCoeff d (Metric.ball (0 : E) 1))
    {u : E → ℝ}
    (hu_pos : ∀ x ∈ Metric.ball (0 : E) 1, 0 < u x)
    (hsuper : IsSupersolution A.1 u)
    {ε : ℝ} (hε : 0 < ε) :
    Measurable (regularizedLogMeasurable (A := A) hu_pos hsuper hε) := by
  classical
  simpa [regularizedLogMeasurable] using
    (regularizedLogAEMeasurable (d := d) (A := A) hu_pos hsuper hε).measurable_mk

lemma regularizedLogMeasurable_ae_eq
    (A : NormalizedEllipticCoeff d (Metric.ball (0 : E) 1))
    {u : E → ℝ}
    (hu_pos : ∀ x ∈ Metric.ball (0 : E) 1, 0 < u x)
    (hsuper : IsSupersolution A.1 u)
    {ε : ℝ} (hε : 0 < ε) :
    regularizedLogFun (u := u) hε =ᵐ[volume.restrict (Metric.ball (0 : E) 1)]
      regularizedLogMeasurable (A := A) hu_pos hsuper hε := by
  classical
  simpa [regularizedLogMeasurable] using
    (regularizedLogAEMeasurable (d := d) (A := A) hu_pos hsuper hε).ae_eq_mk

lemma regularizedLogMeasurable_integrableOn_ball
    (A : NormalizedEllipticCoeff d (Metric.ball (0 : E) 1))
    {u : E → ℝ}
    (hu_pos : ∀ x ∈ Metric.ball (0 : E) 1, 0 < u x)
    (hsuper : IsSupersolution A.1 u)
    {x₀ : E} {R : ℝ}
    (hsub : Metric.ball x₀ R ⊆ Metric.ball (0 : E) 1)
    {ε : ℝ} (hε : 0 < ε) :
    IntegrableOn
      (regularizedLogMeasurable (A := A) hu_pos hsuper hε)
      (Metric.ball x₀ R) volume := by
  have hint :
      IntegrableOn (regularizedLogFun (u := u) hε) (Metric.ball x₀ R) volume :=
    regularizedLog_integrableOn_ball (d := d) (A := A) hu_pos hsuper hsub hε
  have hEq :
      regularizedLogFun (u := u) hε =ᵐ[volume.restrict (Metric.ball x₀ R)]
        regularizedLogMeasurable (A := A) hu_pos hsuper hε := by
    exact ae_mono (Measure.restrict_mono hsub le_rfl)
      (regularizedLogMeasurable_ae_eq (d := d) (A := A) hu_pos hsuper hε)
  exact hint.congr_fun_ae hEq

lemma regularizedLogMeasurable_ball_meanOscillation
    (A : NormalizedEllipticCoeff d (Metric.ball (0 : E) 1))
    {u : E → ℝ}
    (hu_pos : ∀ x ∈ Metric.ball (0 : E) 1, 0 < u x)
    (hsuper : IsSupersolution A.1 u)
    {x₀ : E} {R : ℝ} (hR : 0 < R)
    (hsub : Metric.closedBall x₀ R ⊆ Metric.ball (0 : E) 1)
    {ε : ℝ} (hε : 0 < ε) :
    let v := regularizedLogMeasurable (A := A) hu_pos hsuper hε
    (⨍ x in Metric.ball x₀ (R / 2 : ℝ),
        |v x - ⨍ y in Metric.ball x₀ (R / 2 : ℝ), v y ∂volume| ∂volume) ≤
      c_crossover_bmo_scale d * A.1.Λ ^ ((1 : ℝ) / 2) := by
  intro v
  let v0 : E → ℝ := regularizedLogFun (u := u) hε
  have hbase :
      (⨍ x in Metric.ball x₀ (R / 2 : ℝ),
        |v0 x - ⨍ y in Metric.ball x₀ (R / 2 : ℝ), v0 y ∂volume| ∂volume) ≤
      c_crossover_bmo_scale d * A.1.Λ ^ ((1 : ℝ) / 2) :=
    regularizedLog_ball_meanOscillation (d := d) (A := A)
      (x₀ := x₀) (R := R) hR hsub hu_pos hsuper hε
  have hballsub : Metric.ball x₀ (R / 2 : ℝ) ⊆ Metric.ball (0 : E) 1 := by
    intro x hx
    apply hsub
    refine Metric.mem_closedBall.2 ?_
    have hx' : dist x x₀ < R / 2 := by simpa using hx
    have hhalf_le : R / 2 ≤ R := by linarith [hR]
    exact le_trans (le_of_lt hx') hhalf_le
  have hEq_restrict :
      v0 =ᵐ[volume.restrict (Metric.ball x₀ (R / 2 : ℝ))] v := by
    exact ae_mono (Measure.restrict_mono hballsub le_rfl)
      (regularizedLogMeasurable_ae_eq (d := d) (A := A) hu_pos hsuper hε)
  have hEq_ball :
      ∀ᵐ x ∂volume,
        x ∈ Metric.ball x₀ (R / 2 : ℝ) → v0 x = v x := by
    rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_ball] at hEq_restrict
    exact hEq_restrict
  have havg_eq :
      (⨍ y in Metric.ball x₀ (R / 2 : ℝ), v0 y ∂volume) =
        ⨍ y in Metric.ball x₀ (R / 2 : ℝ), v y ∂volume := by
    exact MeasureTheory.setAverage_congr_fun measurableSet_ball hEq_ball
  let avg0 : ℝ := ⨍ y in Metric.ball x₀ (R / 2 : ℝ), v0 y ∂volume
  let avg : ℝ := ⨍ y in Metric.ball x₀ (R / 2 : ℝ), v y ∂volume
  have hosc_eq :
      ∀ᵐ x ∂volume,
        x ∈ Metric.ball x₀ (R / 2 : ℝ) → |v0 x - avg0| = |v x - avg| := by
    filter_upwards [hEq_ball] with x hx hxmem
    have hEqx : v0 x = v x := hx hxmem
    simp only [avg0, avg]
    rw [hEqx, havg_eq]
  have hosc_avg_eq :
      (⨍ x in Metric.ball x₀ (R / 2 : ℝ), |v0 x - avg0| ∂volume) =
        ⨍ x in Metric.ball x₀ (R / 2 : ℝ), |v x - avg| ∂volume := by
    exact MeasureTheory.setAverage_congr_fun measurableSet_ball hosc_eq
  calc
    (⨍ x in Metric.ball x₀ (R / 2 : ℝ),
      |v x - ⨍ y in Metric.ball x₀ (R / 2 : ℝ), v y ∂volume| ∂volume)
        =
      (⨍ x in Metric.ball x₀ (R / 2 : ℝ),
        |v0 x - ⨍ y in Metric.ball x₀ (R / 2 : ℝ), v0 y ∂volume| ∂volume) := by
          simpa [avg0, avg] using hosc_avg_eq.symm
    _ ≤ c_crossover_bmo_scale d * A.1.Λ ^ ((1 : ℝ) / 2) := hbase

theorem regularizedLog_smallBallAverage_step_le_measurable
    (A : NormalizedEllipticCoeff d (Metric.ball (0 : E) 1))
    {u : E → ℝ}
    (hu_pos : ∀ x ∈ Metric.ball (0 : E) 1, 0 < u x)
    (hsuper : IsSupersolution A.1 u)
    {ε : ℝ} (hε : 0 < ε)
    {x y : E}
    (hx : x ∈ Metric.closedBall (0 : E) (1 / 2 : ℝ))
    (hy : y ∈ Metric.closedBall (0 : E) (1 / 2 : ℝ))
    (hxy : dist x y ≤ (1 / 48 : ℝ)) :
    let v := regularizedLogMeasurable (A := A) hu_pos hsuper hε
    |⨍ z in Metric.ball x (1 / 48 : ℝ), v z ∂volume -
        ⨍ z in Metric.ball y (1 / 48 : ℝ), v z ∂volume|
      ≤ (2 : ℝ) ^ (d + 1) *
          (c_crossover_bmo_scale d * A.1.Λ ^ ((1 : ℝ) / 2)) := by
  intro v
  let v0 : E → ℝ := regularizedLogFun (u := u) hε
  have hbase :
      |⨍ z in Metric.ball x (1 / 48 : ℝ), v0 z ∂volume -
          ⨍ z in Metric.ball y (1 / 48 : ℝ), v0 z ∂volume|
        ≤ (2 : ℝ) ^ (d + 1) *
            (c_crossover_bmo_scale d * A.1.Λ ^ ((1 : ℝ) / 2)) :=
    regularizedLog_smallBallAverage_step_le (d := d) (A := A)
      hu_pos hsuper hε hx hy hxy
  have hsubx : Metric.ball x (1 / 48 : ℝ) ⊆ Metric.ball (0 : E) 1 :=
    ball_subset_unitBall_of_mem_halfBall_of_le_eighth hx (by norm_num)
  have hsuby : Metric.ball y (1 / 48 : ℝ) ⊆ Metric.ball (0 : E) 1 :=
    ball_subset_unitBall_of_mem_halfBall_of_le_eighth hy (by norm_num)
  have hEqx_restrict :
      v0 =ᵐ[volume.restrict (Metric.ball x (1 / 48 : ℝ))] v := by
    exact ae_mono (Measure.restrict_mono hsubx le_rfl)
      (regularizedLogMeasurable_ae_eq (d := d) (A := A) hu_pos hsuper hε)
  have hEqy_restrict :
      v0 =ᵐ[volume.restrict (Metric.ball y (1 / 48 : ℝ))] v := by
    exact ae_mono (Measure.restrict_mono hsuby le_rfl)
      (regularizedLogMeasurable_ae_eq (d := d) (A := A) hu_pos hsuper hε)
  have hEqx_ball :
      ∀ᵐ z ∂volume, z ∈ Metric.ball x (1 / 48 : ℝ) → v0 z = v z := by
    rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_ball] at hEqx_restrict
    exact hEqx_restrict
  have hEqy_ball :
      ∀ᵐ z ∂volume, z ∈ Metric.ball y (1 / 48 : ℝ) → v0 z = v z := by
    rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_ball] at hEqy_restrict
    exact hEqy_restrict
  have havgx :
      (⨍ z in Metric.ball x (1 / 48 : ℝ), v0 z ∂volume) =
        ⨍ z in Metric.ball x (1 / 48 : ℝ), v z ∂volume := by
    exact MeasureTheory.setAverage_congr_fun measurableSet_ball hEqx_ball
  have havgy :
      (⨍ z in Metric.ball y (1 / 48 : ℝ), v0 z ∂volume) =
        ⨍ z in Metric.ball y (1 / 48 : ℝ), v z ∂volume := by
    exact MeasureTheory.setAverage_congr_fun measurableSet_ball hEqy_ball
  rw [havgx, havgy] at hbase
  simpa using hbase

theorem regularizedLog_smallBallAverage_to_origin_le
    (A : NormalizedEllipticCoeff d (Metric.ball (0 : E) 1))
    {u : E → ℝ}
    (hu_pos : ∀ x ∈ Metric.ball (0 : E) 1, 0 < u x)
    (hsuper : IsSupersolution A.1 u)
    {ε : ℝ} (hε : 0 < ε)
    {x : E}
    (hx : x ∈ Metric.closedBall (0 : E) (1 / 2 : ℝ)) :
    let v := regularizedLogMeasurable (A := A) hu_pos hsuper hε
    |⨍ z in Metric.ball x (1 / 48 : ℝ), v z ∂volume -
        ⨍ z in Metric.ball (0 : E) (1 / 48 : ℝ), v z ∂volume|
      ≤ 24 * (2 : ℝ) ^ (d + 1) *
          (c_crossover_bmo_scale d * A.1.Λ ^ ((1 : ℝ) / 2)) := by
  intro v
  let L : ℝ := (2 : ℝ) ^ (d + 1) * (c_crossover_bmo_scale d * A.1.Λ ^ ((1 : ℝ) / 2))
  let xk : ℕ → E := fun k => (((k : ℝ) / 24 : ℝ)) • x
  let avgAt : E → ℝ := fun c => ⨍ z in Metric.ball c (1 / 48 : ℝ), v z ∂volume
  have hΛ_nonneg : 0 ≤ A.1.Λ := by
    have hΛge : 1 ≤ A.1.Λ := by
      have hΛ := A.1.hΛ
      rw [A.2] at hΛ
      simpa using hΛ
    linarith
  have hL_nonneg : 0 ≤ L := by
    dsimp [L]
    refine mul_nonneg ?_ ?_
    · positivity
    · refine mul_nonneg crossover_bmo_scale_nonneg ?_
      exact Real.rpow_nonneg hΛ_nonneg _
  have hx_norm : ‖x‖ ≤ 1 / 2 := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hx
  have hxk_mem : ∀ k, k ≤ 24 → xk k ∈ Metric.closedBall (0 : E) (1 / 2 : ℝ) := by
    intro k hk
    rw [Metric.mem_closedBall, dist_eq_norm]
    calc
      ‖xk k - 0‖ = ‖xk k‖ := by simp
      _ = ‖((k : ℝ) / 24 : ℝ)‖ * ‖x‖ := by
        simp [xk, norm_smul]
      _ = ((k : ℝ) / 24) * ‖x‖ := by
        have hk_nonneg : 0 ≤ (k : ℝ) / 24 := by positivity
        rw [Real.norm_of_nonneg hk_nonneg]
      _ ≤ ((k : ℝ) / 24) * (1 / 2 : ℝ) := by
        gcongr
      _ ≤ 1 / 2 := by
        have hk' : (k : ℝ) ≤ 24 := by exact_mod_cast hk
        nlinarith
  have hstep : ∀ k, k < 24 → |avgAt (xk (k + 1)) - avgAt (xk k)| ≤ L := by
    intro k hk
    have hk_mem : xk k ∈ Metric.closedBall (0 : E) (1 / 2 : ℝ) :=
      hxk_mem k (Nat.le_of_lt hk)
    have hk1_mem : xk (k + 1) ∈ Metric.closedBall (0 : E) (1 / 2 : ℝ) :=
      hxk_mem (k + 1) (Nat.succ_le_of_lt hk)
    have hdist : dist (xk k) (xk (k + 1)) ≤ (1 / 48 : ℝ) := by
      have hdiff :
          xk (k + 1) - xk k =
            ((((k + 1 : ℕ) : ℝ) / 24 - (k : ℝ) / 24 : ℝ) • x) := by
        simpa [xk] using
          (sub_smul ((((k + 1 : ℕ) : ℝ) / 24 : ℝ)) (((k : ℝ) / 24 : ℝ)) x).symm
      have hk_cast : (((k + 1 : ℕ) : ℝ)) = (k : ℝ) + 1 := by
        norm_num
      have hscalar :
          (((k + 1 : ℕ) : ℝ) / 24 - (k : ℝ) / 24 : ℝ) = (1 / 24 : ℝ) := by
        rw [hk_cast]
        ring
      calc
        dist (xk k) (xk (k + 1)) = ‖xk (k + 1) - xk k‖ := by
          rw [dist_eq_norm, norm_sub_rev]
        _ = ‖((((k + 1 : ℕ) : ℝ) / 24 - (k : ℝ) / 24 : ℝ) • x)‖ := by
            rw [hdiff]
        _ = ‖(1 / 24 : ℝ) • x‖ := by
            rw [hscalar]
        _ = (1 / 24 : ℝ) * ‖x‖ := by
            rw [norm_smul, Real.norm_of_nonneg (by positivity)]
        _ ≤ (1 / 24 : ℝ) * (1 / 2 : ℝ) := by
            gcongr
        _ = (1 / 48 : ℝ) := by
            ring
    have hstep0 :=
      regularizedLog_smallBallAverage_step_le_measurable (d := d) (A := A)
        hu_pos hsuper hε hk_mem hk1_mem hdist
    simpa [abs_sub_comm, avgAt, L] using hstep0
  have hind : ∀ k, k ≤ 24 → |avgAt (xk k) - avgAt (xk 0)| ≤ (k : ℝ) * L := by
    intro k hk
    induction k with
    | zero =>
        simp [avgAt, xk, L]
    | succ k ih =>
        have hklt : k < 24 := Nat.lt_of_succ_le hk
        have hk_le : k ≤ 24 := Nat.le_of_lt hklt
        have htri :
            |avgAt (xk (k + 1)) - avgAt (xk 0)| ≤
              |avgAt (xk (k + 1)) - avgAt (xk k)| + |avgAt (xk k) - avgAt (xk 0)| := by
          have hsplit :
              avgAt (xk (k + 1)) - avgAt (xk 0) =
                (avgAt (xk (k + 1)) - avgAt (xk k)) +
                  (avgAt (xk k) - avgAt (xk 0)) := by
            ring
          rw [hsplit]
          exact abs_add_le _ _
        calc
          |avgAt (xk (k + 1)) - avgAt (xk 0)|
              ≤ |avgAt (xk (k + 1)) - avgAt (xk k)| +
                  |avgAt (xk k) - avgAt (xk 0)| := htri
          _ ≤ L + (k : ℝ) * L := by
                gcongr
                · exact hstep k hklt
                · exact ih hk_le
          _ = ((k + 1 : ℕ) : ℝ) * L := by
                have hk_cast : (((k + 1 : ℕ) : ℝ)) = (k : ℝ) + 1 := by
                  norm_num
                rw [hk_cast]
                ring
  have h24 := hind 24 le_rfl
  have hx24 : xk 24 = x := by
    simp [xk]
  have hx0 : xk 0 = (0 : E) := by
    simp [xk]
  rw [hx24, hx0] at h24
  convert h24 using 1
  ring

set_option maxHeartbeats 800000 in
theorem regularizedLog_smallBall_exp_average_le
    (A : NormalizedEllipticCoeff d (Metric.ball (0 : E) 1))
    {u : E → ℝ}
    (hu_pos : ∀ x ∈ Metric.ball (0 : E) 1, 0 < u x)
    (hsuper : IsSupersolution A.1 u)
    {ε : ℝ} (hε : 0 < ε)
    {x₀ : E}
    (hx₀ : x₀ ∈ Metric.closedBall (0 : E) (1 / 2 : ℝ)) :
    let v := regularizedLogMeasurable (A := A) hu_pos hsuper hε
    let p := c_crossover' d / A.1.Λ ^ ((1 : ℝ) / 2)
    IntegrableOn
      (fun z => Real.exp (p * |v z - ⨍ y in Metric.ball x₀ (1 / 48 : ℝ), v y ∂volume|))
      (Metric.ball x₀ (1 / 48 : ℝ)) volume ∧
    (⨍ z in Metric.ball x₀ (1 / 48 : ℝ),
      Real.exp (p * |v z - ⨍ y in Metric.ball x₀ (1 / 48 : ℝ), v y ∂volume|) ∂volume)
      ≤ 1 + C_JN d := by
  intro v p
  let B : Set E := Metric.ball x₀ (1 / 48 : ℝ)
  let μ : Measure E := volume.restrict B
  let avg : ℝ := ⨍ y in B, v y ∂volume
  let f : E → ℝ := fun z => ‖v z - avg‖
  let M : ℝ := c_crossover_bmo_scale d * A.1.Λ ^ ((1 : ℝ) / 2)
  let β : ℝ := 1 / (C_JN d * M)
  letI : IsFiniteMeasure μ := by
    refine ⟨?_⟩
    simpa [μ, B] using
      (measure_ball_lt_top (μ := volume) (x := x₀) (r := (1 / 48 : ℝ)))
  have hΛsqrt_pos : 0 < A.1.Λ ^ ((1 : ℝ) / 2) := by
    have hΛge : 1 ≤ A.1.Λ := by
      have := A.1.hΛ
      rw [A.2] at this
      simpa using this
    exact Real.rpow_pos_of_pos (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hΛge) _
  have hbmo_scale_pos : 0 < c_crossover_bmo_scale d := by
    let B1 : Set E := Metric.ball (0 : E) 1
    have hvol_pos : 0 < volume.real B1 := by
      exact ENNReal.toReal_pos
        (measure_ball_pos (μ := volume) (0 : E) (by norm_num : (0 : ℝ) < 1)).ne'
        (measure_ball_lt_top (μ := volume) (x := (0 : E)) (r := (1 : ℝ))).ne
    have hd_pos : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
    have hCp_pos : 0 < C_poinc_val d := C_poinc_val_pos (d := d) hd_pos
    have hMst_ge_one : (1 : ℝ) ≤ (Mst : ℝ) := by
      have hLip := smoothTransition_lipschitz
      simpa using hLip.dist_le_mul 1 0
    have hMst_pos : 0 < (Mst : ℝ) := by
      linarith
    unfold c_crossover_bmo_scale
    have h1 : 0 < (volume.real B1) ^ (-(1 / 2 : ℝ)) := by
      exact Real.rpow_pos_of_pos hvol_pos _
    have h2 : 0 < (1 / 2 : ℝ) ^ (1 - (d : ℝ) / 2) := by
      exact Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 1 / 2) _
    have h3 : 0 < 8 * (Mst : ℝ) * (volume.real B1) ^ ((1 : ℝ) / 2) := by
      refine mul_pos ?_ ?_
      · exact mul_pos (by positivity) hMst_pos
      · exact Real.rpow_pos_of_pos hvol_pos _
    have hleft_pos :
        0 < ((volume.real B1) ^ (-(1 / 2 : ℝ)) * C_poinc_val d) := by
      exact mul_pos h1 hCp_pos
    have hfirst_pos :
        0 <
          ((volume.real B1) ^ (-(1 / 2 : ℝ)) * C_poinc_val d) *
            (1 / 2 : ℝ) ^ (1 - (d : ℝ) / 2) := by
      exact mul_pos hleft_pos h2
    have htotal_pos :
        0 <
          (((volume.real B1) ^ (-(1 / 2 : ℝ)) * C_poinc_val d) *
            (1 / 2 : ℝ) ^ (1 - (d : ℝ) / 2)) *
            (8 * (Mst : ℝ) * (volume.real B1) ^ ((1 : ℝ) / 2)) := by
      exact mul_pos hfirst_pos h3
    simpa [c_crossover_bmo_scale, B1, mul_assoc] using htotal_pos
  have hM_pos : 0 < M := by
    dsimp [M]
    exact mul_pos hbmo_scale_pos hΛsqrt_pos
  have hp_pos : 0 < p := by
    dsimp [p]
    exact div_pos (crossoverC'_pos (d := d)) hΛsqrt_pos
  have hCM_pos : 0 < C_JN d * M := by
    exact mul_pos (C_JN_pos d) hM_pos
  have hβ_pos : 0 < β := by
    dsimp [β]
    positivity
  have hp_le_halfbeta : p ≤ β / 2 := by
    have hmain :
        p * (C_JN d * M) ≤ 1 / 2 := by
      dsimp [p, M]
      simpa [mul_assoc, mul_left_comm, mul_comm] using
        c_crossover_mul_bmo_le_half (d := d) (A := A)
    have htwo : p * (2 * (C_JN d * M)) ≤ 1 := by
      nlinarith
    have hden_pos : 0 < 2 * (C_JN d * M) := by positivity
    have hdiv : p ≤ 1 / (2 * (C_JN d * M)) := by
      exact (le_div_iff₀ hden_pos).2 htwo
    simpa [β, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hdiv
  have hBsub : Metric.ball x₀ (1 / 8 : ℝ) ⊆ Metric.ball (0 : E) 1 :=
    ball_subset_unitBall_of_mem_halfBall_of_le_eighth hx₀ le_rfl
  have hv_int :
      IntegrableOn v (Metric.ball x₀ (1 / 8 : ℝ)) volume :=
    regularizedLogMeasurable_integrableOn_ball (d := d) (A := A) hu_pos hsuper hBsub hε
  have hv_bmo :
      ∀ (z : E) (s : ℝ), 0 < s →
        Metric.closedBall z s ⊆ Metric.ball x₀ (1 / 8 : ℝ) →
        (⨍ x in Metric.ball z s,
          ‖v x - ⨍ y in Metric.ball z s, v y ∂volume‖ ∂volume) ≤ M := by
    intro z s hs hsub
    have h2sub :
        Metric.closedBall z (2 * s) ⊆ Metric.ball (0 : E) 1 :=
      doubled_subball_subset_unitBall_of_closedBall_subset_eighth hx₀ hs hsub
    simpa [M, show (2 * s) / 2 = s by ring] using
      regularizedLogMeasurable_ball_meanOscillation (d := d) (A := A)
        hu_pos hsuper (x₀ := z) (R := 2 * s) (by positivity) h2sub hε
  have hsixR : 6 * (1 / 48 : ℝ) = 1 / 8 := by ring
  have hv_int_small :
      IntegrableOn v (Metric.ball x₀ (6 * (1 / 48 : ℝ))) volume := by
    rw [hsixR]
    exact hv_int
  have hv_bmo_small :
      ∀ (z : E) (s : ℝ), 0 < s →
        Metric.closedBall z s ⊆ Metric.ball x₀ (6 * (1 / 48 : ℝ)) →
        (⨍ x in Metric.ball z s,
          ‖v x - ⨍ y in Metric.ball z s, v y ∂volume‖ ∂volume) ≤ M := by
    intro z s hs hsub
    have hsub' : Metric.closedBall z s ⊆ Metric.ball x₀ (1 / 8 : ℝ) := by
      rw [hsixR] at hsub
      exact hsub
    exact hv_bmo z s hs hsub'
  have hJN :
      ∀ {t : ℝ}, 0 < t →
        μ {a : E | t < f a} ≤
          ENNReal.ofReal (C_JN d) * μ Set.univ *
            ENNReal.ofReal (Real.exp (-t / (C_JN d * M))) := by
    intro t ht
    have hbase :=
      john_nirenberg_local (d := d) (u := v) (x₀ := x₀) (R := (1 / 48 : ℝ))
        (M := M) (by norm_num) hM_pos
        (regularizedLogMeasurable_measurable (d := d) (A := A) hu_pos hsuper hε)
        hv_int_small hv_bmo_small ht
    simpa [μ, B, f, avg, M, Measure.restrict_apply, measurableSet_ball,
      Set.inter_comm, Set.inter_left_comm, Set.inter_assoc] using hbase
  have hf_nonneg : 0 ≤ᵐ[μ] f := Eventually.of_forall fun _ => norm_nonneg _
  have hf_meas : AEMeasurable f μ := by
    have hv_meas : Measurable v :=
      regularizedLogMeasurable_measurable (d := d) (A := A) hu_pos hsuper hε
    exact ((hv_meas.sub measurable_const).norm).aemeasurable
  have hg_int :
      ∀ t > 0, IntervalIntegrable (fun s : ℝ => p * Real.exp (p * s)) volume 0 t := by
    intro t ht
    exact (continuous_const.mul
      (Real.continuous_exp.comp (continuous_const.mul continuous_id))).intervalIntegrable _ _
  have hg_nonneg :
      ∀ᵐ t ∂volume.restrict (Set.Ioi 0), 0 ≤ p * Real.exp (p * t) := by
    filter_upwards with t
    positivity
  have hLayer :=
    MeasureTheory.lintegral_comp_eq_lintegral_meas_lt_mul μ hf_nonneg hf_meas hg_int hg_nonneg
  have hderiv :
      deriv (fun s : ℝ => Real.exp (p * s)) = fun s => p * Real.exp (p * s) := by
    funext s
    calc
      deriv (fun s : ℝ => Real.exp (p * s)) s = Real.exp (p * s) * (p * 1) := by
        exact (((Real.hasDerivAt_exp (p * s)).comp s ((hasDerivAt_id s).const_mul p)).deriv)
      _ = Real.exp (p * s) * p := by ring
      _ = p * Real.exp (p * s) := by ring
  have hprimitive :
      ∀ a : ℝ, ∫ s in 0..a, p * Real.exp (p * s) = Real.exp (p * a) - 1 := by
    intro a
    rw [intervalIntegral.integral_deriv_eq_sub' (f := fun s : ℝ => Real.exp (p * s)) hderiv
        (fun s _ =>
          ((Real.hasDerivAt_exp (p * s)).comp s ((hasDerivAt_id s).const_mul p)).differentiableAt)
        ((continuous_const.mul
          (Real.continuous_exp.comp (continuous_const.mul continuous_id))).continuousOn)
        ]
    simp
  have hLayer' :
      ∫⁻ z, ENNReal.ofReal (Real.exp (p * f z) - 1) ∂μ =
        ∫⁻ t in Set.Ioi 0, μ {a : E | t < f a} * ENNReal.ofReal (p * Real.exp (p * t)) := by
    calc
      ∫⁻ z, ENNReal.ofReal (Real.exp (p * f z) - 1) ∂μ
          = ∫⁻ z, ENNReal.ofReal (∫ t in 0..f z, p * Real.exp (p * t)) ∂μ := by
              apply lintegral_congr_ae
              exact Eventually.of_forall fun z => by simp [hprimitive (f z)]
      _ =
          ∫⁻ t in Set.Ioi 0, μ {a : E | t < f a} * ENNReal.ofReal (p * Real.exp (p * t)) :=
            hLayer
  have hcoeff :
      p - β ≤ -(β / 2) := by
    linarith
  have hmajor :
      ∫⁻ t in Set.Ioi 0, μ {a : E | t < f a} * ENNReal.ofReal (p * Real.exp (p * t))
        ≤ ENNReal.ofReal (C_JN d) * μ Set.univ *
            ∫⁻ t in Set.Ioi 0, ENNReal.ofReal (p * Real.exp (-(β / 2) * t)) := by
    calc
      ∫⁻ t in Set.Ioi 0, μ {a : E | t < f a} * ENNReal.ofReal (p * Real.exp (p * t))
          ≤
            ∫⁻ t in Set.Ioi 0,
              ENNReal.ofReal (C_JN d) * μ Set.univ *
                ENNReal.ofReal (p * Real.exp (-(β / 2) * t)) := by
                  refine lintegral_mono_ae ?_
                  rw [ae_restrict_iff' measurableSet_Ioi]
                  filter_upwards with t ht
                  have htail := hJN ht
                  have hexp_le :
                      Real.exp (-t / (C_JN d * M)) * Real.exp (p * t) ≤
                        Real.exp (-(β / 2) * t) := by
                    have hexp_eq :
                        Real.exp (-t / (C_JN d * M)) * Real.exp (p * t) =
                          Real.exp ((p - β) * t) := by
                      rw [← Real.exp_add]
                      congr 1
                      dsimp [β]
                      field_simp [hCM_pos.ne']
                      ring
                    rw [hexp_eq]
                    apply Real.exp_le_exp.mpr
                    have ht_nonneg : 0 ≤ t := le_of_lt ht
                    gcongr
                  calc
                    μ {a : E | t < f a} * ENNReal.ofReal (p * Real.exp (p * t))
                        ≤ (ENNReal.ofReal (C_JN d) * μ Set.univ *
                            ENNReal.ofReal (Real.exp (-t / (C_JN d * M)))) *
                          ENNReal.ofReal (p * Real.exp (p * t)) := by
                            exact mul_le_mul_of_nonneg_right htail (by positivity)
                    _ = ENNReal.ofReal (C_JN d) * μ Set.univ *
                          ENNReal.ofReal
                            (Real.exp (-t / (C_JN d * M)) * (p * Real.exp (p * t))) := by
                          rw [ENNReal.ofReal_mul (Real.exp_nonneg _), mul_assoc, mul_assoc]
                    _ ≤ ENNReal.ofReal (C_JN d) * μ Set.univ *
                          ENNReal.ofReal (p * Real.exp (-(β / 2) * t)) := by
                          have hinner_le :
                              Real.exp (-t / (C_JN d * M)) * (p * Real.exp (p * t)) ≤
                                p * Real.exp (-(β / 2) * t) := by
                            calc
                              Real.exp (-t / (C_JN d * M)) * (p * Real.exp (p * t))
                                  = p *
                                      (Real.exp (-t / (C_JN d * M)) *
                                        Real.exp (p * t)) := by ring
                              _ ≤ p * Real.exp (-(β / 2) * t) := by
                                    gcongr
                          exact mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal hinner_le)
                            (by positivity : 0 ≤ ENNReal.ofReal (C_JN d) * μ Set.univ)
      _ = ENNReal.ofReal (C_JN d) * μ Set.univ *
            ∫⁻ t in Set.Ioi 0, ENNReal.ofReal (p * Real.exp (-(β / 2) * t)) := by
              rw [show
                    (fun t : ℝ =>
                      ENNReal.ofReal (C_JN d) * μ Set.univ *
                        ENNReal.ofReal (p * Real.exp (-(β / 2) * t))) =
                      fun t : ℝ =>
                        (ENNReal.ofReal (C_JN d) * μ Set.univ) *
                          ENNReal.ofReal (p * Real.exp (-(β / 2) * t)) by
                    funext t
                    ring]
              rw [lintegral_const_mul'' _ (by measurability)]
  have hmajor_int :
      IntegrableOn (fun t : ℝ => p * Real.exp (-(β / 2) * t)) (Set.Ioi 0) volume := by
    have hneg : -(β / 2) < 0 := by linarith
    exact (integrableOn_exp_mul_Ioi (a := -(β / 2)) hneg 0).const_mul p
  have hmajor_lintegral :
      ∫⁻ t in Set.Ioi 0, ENNReal.ofReal (p * Real.exp (-(β / 2) * t)) =
        ENNReal.ofReal (∫ t in Set.Ioi 0, p * Real.exp (-(β / 2) * t)) := by
    symm
    exact MeasureTheory.ofReal_integral_eq_lintegral_ofReal hmajor_int
      (by
        filter_upwards with t
        positivity)
  have hmajor_val :
      ∫ t in Set.Ioi 0, p * Real.exp (-(β / 2) * t) ≤ 1 := by
    have hneg : -(β / 2) < 0 := by linarith
    have hexp_eq :
        ∫ t in Set.Ioi 0, Real.exp (-(β / 2) * t) = 2 / β := by
      simpa using (integral_exp_mul_Ioi (a := -(β / 2)) hneg 0)
    rw [integral_const_mul, hexp_eq]
    have hβ_ne : β ≠ 0 := hβ_pos.ne'
    rw [show p * (2 / β) = (2 * p) / β by
      field_simp [hβ_ne]]
    have htwo : 2 * p ≤ β := by linarith
    exact (div_le_iff₀ hβ_pos).2 (by simpa using htwo)
  have hlin_bound :
      ∫⁻ z, ENNReal.ofReal (Real.exp (p * f z) - 1) ∂μ ≤
        ENNReal.ofReal (C_JN d * μ.real Set.univ) := by
    have hμ_univ_ne_top : μ Set.univ ≠ ∞ := by
      simpa [μ, B] using
        (measure_ball_lt_top (μ := volume) (x := x₀) (r := (1 / 48 : ℝ))).ne
    calc
      ∫⁻ z, ENNReal.ofReal (Real.exp (p * f z) - 1) ∂μ
          = ∫⁻ t in Set.Ioi 0, μ {a : E | t < f a} * ENNReal.ofReal (p * Real.exp (p * t)) := hLayer'
      _ ≤ ENNReal.ofReal (C_JN d) * μ Set.univ *
          ∫⁻ t in Set.Ioi 0, ENNReal.ofReal (p * Real.exp (-(β / 2) * t)) := hmajor
      _ = ENNReal.ofReal (C_JN d) * μ Set.univ *
          ENNReal.ofReal (∫ t in Set.Ioi 0, p * Real.exp (-(β / 2) * t)) := by
            rw [hmajor_lintegral]
      _ ≤ ENNReal.ofReal (C_JN d) * μ Set.univ * ENNReal.ofReal 1 := by
            gcongr
      _ = ENNReal.ofReal (C_JN d) * μ Set.univ := by simp
      _ = ENNReal.ofReal (C_JN d) * ENNReal.ofReal (μ.real Set.univ) := by
            congr 1
            rw [measureReal_def, ENNReal.ofReal_toReal hμ_univ_ne_top]
      _ = ENNReal.ofReal (C_JN d * μ.real Set.univ) := by
            rw [ENNReal.ofReal_mul (C_JN_pos d).le]
  have hlin_finite :
      ∫⁻ z, ENNReal.ofReal (Real.exp (p * f z) - 1) ∂μ ≠ ∞ := by
    exact ne_of_lt (lt_of_le_of_lt hlin_bound (by simp : ENNReal.ofReal (C_JN d * μ.real Set.univ) < ∞))
  have hF_meas :
      AEMeasurable (fun z => ENNReal.ofReal (Real.exp (p * f z) - 1)) μ := by
    exact (hf_meas.const_mul p).exp.sub_const 1 |>.ennreal_ofReal
  have hF_int :
      Integrable (fun z => Real.exp (p * f z) - 1) μ := by
    refine (integrable_toReal_of_lintegral_ne_top hF_meas hlin_finite).congr ?_
    filter_upwards with z
    have hnonneg : 0 ≤ Real.exp (p * f z) - 1 := by
      have hpf_nonneg : 0 ≤ p * f z := by
        exact mul_nonneg hp_pos.le (by simp [f])
      have hexp_ge : 1 ≤ Real.exp (p * f z) := by
        simpa using (Real.one_le_exp_iff.mpr hpf_nonneg)
      exact sub_nonneg.mpr hexp_ge
    simp [hnonneg]
  have hF_nonneg :
      0 ≤ᵐ[μ] fun z => Real.exp (p * f z) - 1 := by
    filter_upwards with z
    have hpf_nonneg : 0 ≤ p * f z := by
      exact mul_nonneg hp_pos.le (by simp [f])
    have hexp_ge : 1 ≤ Real.exp (p * f z) := by
      simpa using (Real.one_le_exp_iff.mpr hpf_nonneg)
    exact sub_nonneg.mpr hexp_ge
  have hF_le :
      ∫ z, (Real.exp (p * f z) - 1) ∂μ ≤ C_JN d * μ.real Set.univ := by
    have hof :
        ENNReal.ofReal (∫ z, (Real.exp (p * f z) - 1) ∂μ) ≤
          ENNReal.ofReal (C_JN d * μ.real Set.univ) := by
      rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal hF_int hF_nonneg]
      exact hlin_bound
    have hμ_nonneg : 0 ≤ μ.real Set.univ := by
      rw [measureReal_def]
      exact ENNReal.toReal_nonneg
    have hrhs_nonneg : 0 ≤ C_JN d * μ.real Set.univ := by
      exact mul_nonneg (C_JN_pos d).le hμ_nonneg
    exact (ENNReal.ofReal_le_ofReal_iff hrhs_nonneg).mp hof
  have hμ_pos : 0 < μ.real Set.univ := by
    have hμ_univ :
        μ Set.univ = volume (Metric.ball x₀ (1 / 48 : ℝ)) := by
      simp [μ, B]
    rw [measureReal_def, hμ_univ]
    exact ENNReal.toReal_pos
      (measure_ball_pos (μ := volume) x₀ (by norm_num : (0 : ℝ) < 1 / 48)).ne'
      (measure_ball_lt_top (μ := volume) (x := x₀) (r := (1 / 48 : ℝ))).ne
  have havg_eq :
      (⨍ z, Real.exp (p * f z) ∂μ) =
        1 + (μ.real Set.univ)⁻¹ * ∫ z, (Real.exp (p * f z) - 1) ∂μ := by
    have hconst_int : Integrable (fun _ : E => (1 : ℝ)) μ := integrable_const 1
    rw [MeasureTheory.average_eq]
    rw [show (∫ z, Real.exp (p * f z) ∂μ) =
        ∫ z, ((Real.exp (p * f z) - 1) + 1) ∂μ by
          apply integral_congr_ae
          exact Eventually.of_forall fun z => by ring]
    rw [integral_add hF_int hconst_int, integral_const]
    rw [smul_eq_mul, smul_eq_mul, mul_one]
    field_simp [hμ_pos.ne']
    ring
  have havg_le :
      (⨍ z, Real.exp (p * f z) ∂μ) ≤ 1 + C_JN d := by
    rw [havg_eq]
    have hterm :
        (μ.real Set.univ)⁻¹ * ∫ z, (Real.exp (p * f z) - 1) ∂μ ≤ C_JN d := by
      rw [show (μ.real Set.univ)⁻¹ * ∫ z, (Real.exp (p * f z) - 1) ∂μ =
          (∫ z, (Real.exp (p * f z) - 1) ∂μ) / μ.real Set.univ by
            field_simp [hμ_pos.ne']]
      exact (div_le_iff₀ hμ_pos).2 (by simpa [mul_comm, mul_left_comm, mul_assoc] using hF_le)
    simpa [add_comm, add_left_comm, add_assoc] using add_le_add_left hterm 1
  have hExp_int : Integrable (fun z => Real.exp (p * f z)) μ := by
    have hconst_int : Integrable (fun _ : E => (1 : ℝ)) μ := integrable_const 1
    refine (hF_int.add hconst_int).congr ?_
    filter_upwards with z
    have hpoint : (Real.exp (p * f z) - 1) + 1 = Real.exp (p * f z) := by ring
    simp [hpoint]
  have hExp_int_ball :
      IntegrableOn
        (fun z => Real.exp (p * |v z - ⨍ y in Metric.ball x₀ (1 / 48 : ℝ), v y ∂volume|))
        (Metric.ball x₀ (1 / 48 : ℝ)) volume := by
    simpa [IntegrableOn, μ, B, f, avg, Real.norm_eq_abs] using hExp_int
  have havg_ball :
      (⨍ z in Metric.ball x₀ (1 / 48 : ℝ),
        Real.exp (p * |v z - ⨍ y in Metric.ball x₀ (1 / 48 : ℝ), v y ∂volume|) ∂volume)
        ≤ 1 + C_JN d := by
    simpa [μ, B, f, avg, Real.norm_eq_abs] using havg_le
  exact ⟨hExp_int_ball, havg_ball⟩

set_option maxHeartbeats 800000 in
theorem regularizedLog_halfBall_exp_average_to_origin_le
    (A : NormalizedEllipticCoeff d (Metric.ball (0 : E) 1))
    {u : E → ℝ}
    (hu_pos : ∀ x ∈ Metric.ball (0 : E) 1, 0 < u x)
    (hsuper : IsSupersolution A.1 u)
    {ε : ℝ} (hε : 0 < ε) :
    let v := regularizedLogMeasurable (A := A) hu_pos hsuper hε
    let p := c_crossover' d / A.1.Λ ^ ((1 : ℝ) / 2)
    let a := ⨍ z in Metric.ball (0 : E) (1 / 48 : ℝ), v z ∂volume
    let δ := 24 * (2 : ℝ) ^ (d + 1) *
      (c_crossover_bmo_scale d * A.1.Λ ^ ((1 : ℝ) / 2))
    let Kloc := Real.exp (p * δ) * (1 + C_JN d)
    let Khalf := (Nat.ceil ((97 : ℝ) ^ d) : ℝ) * Kloc
    IntegrableOn (fun z => Real.exp (p * |v z - a|))
      (Metric.ball (0 : E) (1 / 2 : ℝ)) volume ∧
    (⨍ z in Metric.ball (0 : E) (1 / 2 : ℝ),
      Real.exp (p * |v z - a|) ∂volume) ≤ Khalf := by
  intro v p a δ Kloc Khalf
  let Bhalf : Set E := Metric.ball (0 : E) (1 / 2 : ℝ)
  let F : E → ℝ := fun z => Real.exp (p * |v z - a|)
  let μ : Measure E := volume.restrict Bhalf
  have hρ_pos : 0 < (1 / 48 : ℝ) := by norm_num
  have hhalf_pos : 0 < (1 / 2 : ℝ) := by norm_num
  obtain ⟨t, htcard, htmem, hcover, _⟩ :=
    exists_finite_inner_ball_cover_with_card
      (d := d) (x₀ := (0 : E))
      (r := (1 / 2 : ℝ)) (ρ := (1 / 48 : ℝ)) (R := 1)
      hhalf_pos hρ_pos (by norm_num)
  let G : E → ℝ := fun x => Finset.sum t (fun c => Set.indicator (Metric.ball c (1 / 48 : ℝ)) F x)
  have hΛsqrt_pos : 0 < A.1.Λ ^ ((1 : ℝ) / 2) := by
    have hΛge : 1 ≤ A.1.Λ := by
      have hΛ := A.1.hΛ
      rw [A.2] at hΛ
      simpa using hΛ
    exact Real.rpow_pos_of_pos (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hΛge) _
  have hp_pos : 0 < p := by
    exact div_pos (crossoverC'_pos (d := d)) hΛsqrt_pos
  have hp_nonneg : 0 ≤ p := hp_pos.le
  have hKloc_nonneg : 0 ≤ Kloc := by
    dsimp [Kloc]
    refine mul_nonneg (le_of_lt (Real.exp_pos _)) ?_
    linarith [show 0 < C_JN d from C_JN_pos d]
  have hv_meas : Measurable v :=
    regularizedLogMeasurable_measurable (d := d) (A := A) hu_pos hsuper hε
  have hF_meas : Measurable F := by
    refine Real.measurable_exp.comp ?_
    exact measurable_const.mul ((hv_meas.sub measurable_const).abs)
  have hF_nonneg : ∀ z, 0 ≤ F z := by
    intro z
    exact le_of_lt (Real.exp_pos _)
  have hlocal_integrable :
      ∀ c ∈ t, IntegrableOn F (Metric.ball c (1 / 48 : ℝ)) volume := by
    intro c hc
    let ac : ℝ := ⨍ z in Metric.ball c (1 / 48 : ℝ), v z ∂volume
    let Fc : E → ℝ := fun z => Real.exp (p * |v z - ac|)
    have hcenter : c ∈ Metric.closedBall (0 : E) (1 / 2 : ℝ) := htmem c hc
    have hbase :=
      regularizedLog_smallBall_exp_average_le (d := d) (A := A)
        hu_pos hsuper hε hcenter
    have hFc_int : IntegrableOn Fc (Metric.ball c (1 / 48 : ℝ)) volume := by
      simpa [v, p, Fc, ac] using hbase.1
    refine Integrable.mono' (hFc_int.const_mul (Real.exp (p * δ))) ?_ ?_
    · exact hF_meas.aestronglyMeasurable
    · filter_upwards with z
      have htri : |v z - a| ≤ |v z - ac| + |ac - a| := by
        simpa [ac, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
          (abs_sub_le (v z) ac a)
      have hchain :
          |ac - a| ≤ δ := by
        simpa [ac, a, δ] using
          (regularizedLog_smallBallAverage_to_origin_le (d := d) (A := A)
            hu_pos hsuper hε hcenter)
      have hbound : |v z - a| ≤ |v z - ac| + δ := by
        nlinarith [htri, hchain]
      have hmul : p * |v z - a| ≤ p * |v z - ac| + p * δ := by
        nlinarith
      have hmajor :
          F z ≤ Real.exp (p * δ) * Fc z := by
        calc
          F z = Real.exp (p * |v z - a|) := by rfl
          _ ≤ Real.exp (p * |v z - ac| + p * δ) := by
                exact Real.exp_le_exp.mpr hmul
          _ = Real.exp (p * δ) * Fc z := by
                rw [show p * |v z - ac| + p * δ = p * δ + p * |v z - ac| by ring,
                  Real.exp_add]
      rw [Real.norm_eq_abs, abs_of_nonneg (hF_nonneg z)]
      exact hmajor
  have hlocal_integral_bound :
      ∀ c ∈ t,
        ∫ z in Metric.ball c (1 / 48 : ℝ), F z ∂volume ≤
          volume.real (Metric.ball c (1 / 48 : ℝ)) * Kloc := by
    intro c hc
    let ac : ℝ := ⨍ z in Metric.ball c (1 / 48 : ℝ), v z ∂volume
    let Fc : E → ℝ := fun z => Real.exp (p * |v z - ac|)
    have hcenter : c ∈ Metric.closedBall (0 : E) (1 / 2 : ℝ) := htmem c hc
    have hbase :=
      regularizedLog_smallBall_exp_average_le (d := d) (A := A)
        hu_pos hsuper hε hcenter
    have hFc_int : IntegrableOn Fc (Metric.ball c (1 / 48 : ℝ)) volume := by
      simpa [v, p, Fc, ac] using hbase.1
    have hF_int : IntegrableOn F (Metric.ball c (1 / 48 : ℝ)) volume :=
      hlocal_integrable c hc
    have hpointwise :
        ∀ z ∈ Metric.ball c (1 / 48 : ℝ), F z ≤ Real.exp (p * δ) * Fc z := by
      intro z hz
      have htri : |v z - a| ≤ |v z - ac| + |ac - a| := by
        simpa [ac, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
          (abs_sub_le (v z) ac a)
      have hchain :
          |ac - a| ≤ δ := by
        simpa [ac, a, δ] using
          (regularizedLog_smallBallAverage_to_origin_le (d := d) (A := A)
            hu_pos hsuper hε hcenter)
      have hbound : |v z - a| ≤ |v z - ac| + δ := by
        nlinarith [htri, hchain]
      have hmul : p * |v z - a| ≤ p * |v z - ac| + p * δ := by
        nlinarith
      calc
        F z = Real.exp (p * |v z - a|) := by rfl
        _ ≤ Real.exp (p * |v z - ac| + p * δ) := by
              exact Real.exp_le_exp.mpr hmul
        _ = Real.exp (p * δ) * Fc z := by
              rw [show p * |v z - ac| + p * δ = p * δ + p * |v z - ac| by ring,
                Real.exp_add]
    have hmajor_int :
        ∫ z in Metric.ball c (1 / 48 : ℝ), F z ∂volume ≤
          ∫ z in Metric.ball c (1 / 48 : ℝ), Real.exp (p * δ) * Fc z ∂volume := by
      have hmajor_ae :
          ∀ᵐ z ∂(volume.restrict (Metric.ball c (1 / 48 : ℝ))),
            F z ≤ Real.exp (p * δ) * Fc z := by
        filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
        exact hpointwise z hz
      have hmajor_int' :
          ∫ z, F z ∂(volume.restrict (Metric.ball c (1 / 48 : ℝ))) ≤
            ∫ z, Real.exp (p * δ) * Fc z ∂(volume.restrict (Metric.ball c (1 / 48 : ℝ))) := by
        exact integral_mono_ae hF_int (hFc_int.const_mul _) hmajor_ae
      simpa using hmajor_int'
    have hball_pos : 0 < volume.real (Metric.ball c (1 / 48 : ℝ)) := by
      exact ENNReal.toReal_pos
        (measure_ball_pos (μ := volume) c hρ_pos).ne'
        (measure_ball_lt_top (μ := volume) (x := c) (r := (1 / 48 : ℝ))).ne
    have hFc_avg :
        (⨍ z in Metric.ball c (1 / 48 : ℝ), Fc z ∂volume) ≤ 1 + C_JN d := by
      simpa [v, p, Fc, ac] using hbase.2
    have hFc_int_bound :
        ∫ z in Metric.ball c (1 / 48 : ℝ), Fc z ∂volume ≤
          volume.real (Metric.ball c (1 / 48 : ℝ)) * (1 + C_JN d) := by
      rw [MeasureTheory.setAverage_eq, smul_eq_mul] at hFc_avg
      rw [show (volume.real (Metric.ball c (1 / 48 : ℝ)))⁻¹ *
          ∫ z in Metric.ball c (1 / 48 : ℝ), Fc z ∂volume =
            (∫ z in Metric.ball c (1 / 48 : ℝ), Fc z ∂volume) /
              volume.real (Metric.ball c (1 / 48 : ℝ)) by
            field_simp [hball_pos.ne']] at hFc_avg
      simpa [mul_comm, mul_left_comm, mul_assoc] using (div_le_iff₀ hball_pos).mp hFc_avg
    calc
      ∫ z in Metric.ball c (1 / 48 : ℝ), F z ∂volume
          ≤ ∫ z in Metric.ball c (1 / 48 : ℝ), Real.exp (p * δ) * Fc z ∂volume := hmajor_int
      _ = Real.exp (p * δ) * ∫ z in Metric.ball c (1 / 48 : ℝ), Fc z ∂volume := by
            rw [integral_const_mul]
      _ ≤ Real.exp (p * δ) *
            (volume.real (Metric.ball c (1 / 48 : ℝ)) * (1 + C_JN d)) := by
              gcongr
      _ = volume.real (Metric.ball c (1 / 48 : ℝ)) * Kloc := by
            dsimp [Kloc]
            ring
  have hBcover :
      Bhalf ⊆ ⋃ c ∈ t, Metric.ball c (1 / 48 : ℝ) := by
    intro x hx
    exact hcover (Metric.mem_closedBall.2 (le_of_lt (Metric.mem_ball.1 hx)))
  have hterm_int :
      ∀ c ∈ t, Integrable (Set.indicator (Metric.ball c (1 / 48 : ℝ)) F) μ := by
    intro c hc
    exact ((hlocal_integrable c hc).integrable_indicator measurableSet_ball).mono_measure
      Measure.restrict_le_self
  have hsum_int :
      Integrable G μ := by
    dsimp [G]
    refine integrable_finset_sum _ ?_
    intro c hc
    exact hterm_int c hc
  have hdom_plain :
      ∀ᵐ x ∂μ, F x ≤ G x := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    have hxcover := hBcover hx
    rw [Set.mem_iUnion] at hxcover
    obtain ⟨c, hxcover⟩ := hxcover
    rw [Set.mem_iUnion] at hxcover
    obtain ⟨hc, hxc⟩ := hxcover
    have hsum_nonneg :
        ∀ c' ∈ t, 0 ≤ Set.indicator (Metric.ball c' (1 / 48 : ℝ)) F x := by
      intro c' hc'
      by_cases hx' : x ∈ Metric.ball c' (1 / 48 : ℝ)
      · rw [Set.indicator_of_mem hx']
        exact hF_nonneg x
      · rw [Set.indicator_of_notMem hx']
    have hle :
        F x ≤ G x := by
      calc
        F x = Set.indicator (Metric.ball c (1 / 48 : ℝ)) F x := by
          symm
          exact (show Set.indicator (Metric.ball c (1 / 48 : ℝ)) F x = F x from
            Set.indicator_of_mem (f := F) hxc)
        _ ≤ G x := by
              exact Finset.single_le_sum hsum_nonneg (by simpa using hc)
    exact hle
  have hdom_ae :
      ∀ᵐ x ∂μ, ‖F x‖ ≤ G x := by
    filter_upwards [hdom_plain] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (hF_nonneg x)]
    exact hx
  have hF_int_mu : Integrable F μ := by
    exact Integrable.mono' hsum_int hF_meas.aestronglyMeasurable hdom_ae
  have hint_le_sum :
      ∫ x, F x ∂μ ≤ ∫ x, G x ∂μ := by
    exact integral_mono_ae hF_int_mu hsum_int hdom_plain
  have hterm_le :
      ∀ c ∈ t,
        ∫ x, Set.indicator (Metric.ball c (1 / 48 : ℝ)) F x ∂μ ≤
          ∫ x in Metric.ball c (1 / 48 : ℝ), F x ∂volume := by
    intro c hc
    have hterm_nonneg :
        0 ≤ᵐ[volume] Set.indicator (Metric.ball c (1 / 48 : ℝ)) F := by
      exact Filter.Eventually.of_forall fun x => by
        by_cases hx : x ∈ Metric.ball c (1 / 48 : ℝ)
        · rw [Set.indicator_of_mem hx]
          exact hF_nonneg x
        · rw [Set.indicator_of_notMem hx]
          positivity
    have hterm_int_vol :
        Integrable (Set.indicator (Metric.ball c (1 / 48 : ℝ)) F) volume :=
      (hlocal_integrable c hc).integrable_indicator measurableSet_ball
    calc
      ∫ x, Set.indicator (Metric.ball c (1 / 48 : ℝ)) F x ∂μ
          ≤ ∫ x, Set.indicator (Metric.ball c (1 / 48 : ℝ)) F x ∂volume := by
                exact integral_mono_measure Measure.restrict_le_self hterm_nonneg hterm_int_vol
      _ = ∫ x in Metric.ball c (1 / 48 : ℝ), F x ∂volume := by
            rw [integral_indicator measurableSet_ball]
  have hsmall_meas_le :
      ∀ c : E, volume.real (Metric.ball c (1 / 48 : ℝ)) ≤ volume.real Bhalf := by
    intro c
    rw [crossover_volumeReal_ball_eq (d := d) c hρ_pos]
    rw [crossover_volumeReal_ball_eq (d := d) (0 : E) hhalf_pos]
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 1 / 48)
        (by norm_num : (1 / 48 : ℝ) ≤ 1 / 2) d)
      (by positivity)
  have hμ_eq : μ.real Set.univ = volume.real Bhalf := by
    simp [μ, Bhalf]
  have hμ_pos : 0 < μ.real Set.univ := by
    rw [hμ_eq]
    exact ENNReal.toReal_pos
      (measure_ball_pos (μ := volume) (0 : E) hhalf_pos).ne'
      (measure_ball_lt_top (μ := volume) (x := (0 : E)) (r := (1 / 2 : ℝ))).ne
  have hint_bound :
      ∫ x, F x ∂μ ≤ μ.real Set.univ * Khalf := by
    calc
      ∫ x, F x ∂μ
          ≤ ∫ x, G x ∂μ := hint_le_sum
      _ = Finset.sum t (fun c => ∫ x, Set.indicator (Metric.ball c (1 / 48 : ℝ)) F x ∂μ) := by
            dsimp [G]
            rw [integral_finset_sum]
            intro c hc
            exact hterm_int c hc
      _ ≤ Finset.sum t (fun c => ∫ x in Metric.ball c (1 / 48 : ℝ), F x ∂volume) := by
            refine Finset.sum_le_sum ?_
            intro c hc
            exact hterm_le c hc
      _ ≤ Finset.sum t (fun _ => volume.real Bhalf * Kloc) := by
            refine Finset.sum_le_sum ?_
            intro c hc
            exact le_trans (hlocal_integral_bound c hc) (by
              exact mul_le_mul_of_nonneg_right (hsmall_meas_le c) hKloc_nonneg)
      _ = (t.card : ℝ) * (volume.real Bhalf * Kloc) := by simp
      _ ≤ (Nat.ceil ((97 : ℝ) ^ d) : ℝ) * (volume.real Bhalf * Kloc) := by
            gcongr
            have h97 :
                (4 * (2 : ℝ)⁻¹ * 48 + 1 : ℝ) = 97 := by
              norm_num
            simpa [div_eq_mul_inv, h97] using htcard
      _ = μ.real Set.univ * Khalf := by
            rw [hμ_eq]
            dsimp [Khalf]
            ring
  have hAvg :
      (⨍ z in Bhalf, F z ∂volume) ≤ Khalf := by
    rw [MeasureTheory.setAverage_eq, smul_eq_mul]
    rw [show (volume.real Bhalf)⁻¹ * ∫ z in Bhalf, F z ∂volume =
        (μ.real Set.univ)⁻¹ * ∫ z, F z ∂μ by
          simp [μ, Bhalf]]
    rw [show (μ.real Set.univ)⁻¹ * ∫ z, F z ∂μ =
        (∫ z, F z ∂μ) / μ.real Set.univ by
          field_simp [hμ_pos.ne']]
    exact (div_le_iff₀ hμ_pos).2 (by simpa [mul_comm, mul_left_comm, mul_assoc] using hint_bound)
  exact ⟨by simpa [IntegrableOn, μ, Bhalf] using hF_int_mu, by simpa [Bhalf, F] using hAvg⟩

omit [NeZero d] in
lemma setAverage_mono_of_nonneg_local
    {f g : E → ℝ} {s : Set E}
    (hf_nonneg : ∀ x, 0 ≤ f x)
    (hg_int : IntegrableOn g s volume)
    (hfg : ∀ᵐ x ∂(volume.restrict s), f x ≤ g x) :
    (⨍ x in s, f x ∂volume) ≤ ⨍ x in s, g x ∂volume := by
  rw [MeasureTheory.setAverage_eq, MeasureTheory.setAverage_eq, smul_eq_mul, smul_eq_mul]
  refine mul_le_mul_of_nonneg_left ?_ ?_
  · exact integral_mono_of_nonneg (Filter.Eventually.of_forall hf_nonneg) hg_int hfg
  · positivity

noncomputable def crossoverJNTheta (d : ℕ) [NeZero d] : ℝ :=
  24 * (2 : ℝ) ^ (d + 1) * (c_crossover' d * c_crossover_bmo_scale d)

noncomputable def crossoverJNKloc (d : ℕ) [NeZero d] : ℝ :=
  Real.exp (crossoverJNTheta d) * (1 + C_JN d)

noncomputable def crossoverJNKhalf (d : ℕ) [NeZero d] : ℝ :=
  (Nat.ceil ((97 : ℝ) ^ d) : ℝ) * crossoverJNKloc d


end DeGiorgi
