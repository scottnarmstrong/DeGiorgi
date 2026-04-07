import DeGiorgi.MoserIteration.CutoffPrep.RegularizedEnergy

/-!
# Moser Witness Construction

This module constructs the limiting power-cutoff witness from the exact-on-support regularized witnesses.
-/

noncomputable section

open MeasureTheory Filter

namespace DeGiorgi

variable {d : ℕ} [NeZero d]

local notation "E" => AmbientSpace d

/-! #### Sub-theorem A: Witness construction for `η · u₊^{p/2}`

Build `MemW1pWitness 2 (moserPowerCutoff η u p)` by taking L² limits of the
exact-on-support regularized witnesses `moserExactRegPowerCutoffWitness`
with fixed qualitative cutoff level `N` and ε → 0.
Uses `HasWeakPartialDeriv.of_eLpNormApprox_p` and dominated convergence,
simplified by the Chapter 05 a.e. boundedness of `u₊`. -/
set_option maxHeartbeats 1000000 in
theorem moserPowerCutoff_memW1pWitness
    (hd : 2 < (d : ℝ))
    (A : NormalizedEllipticCoeff d (Metric.ball (0 : E) 1))
    {u η : E → ℝ} {p s Cη : ℝ}
    (hp : 1 < p)
    (hs : 0 < s) (hs1 : s ≤ 1)
    (hsub : IsSubsolution A.1 u)
    (hpInt :
      IntegrableOn (fun x => |max (u x) 0| ^ p)
        (Metric.ball (0 : E) s) volume)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hη_nonneg : ∀ x, 0 ≤ η x)
    (hη_bound : ∀ x, |η x| ≤ 1)
    (hη_grad_bound : ∀ x, ‖fderiv ℝ η x‖ ≤ Cη)
    (hη_sub_ball : tsupport η ⊆ Metric.ball (0 : E) s) :
    ∃ hwv : MemW1pWitness 2 (moserPowerCutoff (d := d) η u p) (Metric.ball (0 : E) s),
      ∫ x in Metric.ball (0 : E) s, ‖hwv.weakGrad x‖ ^ 2 ∂volume ≤
        2 * Cη ^ 2 * (A.1.Λ * (p / (p - 1)) ^ 2 + 1) *
          ∫ x in Metric.ball (0 : E) s, |max (u x) 0| ^ p ∂volume := by
  classical
  let Ω : Set E := Metric.ball (0 : E) s
  let hu1 : MemW1pWitness 2 u (Metric.ball (0 : E) 1) := MemW1p.someWitness hsub.1
  obtain ⟨N0, hN0_pos, hqual0⟩ :=
    qualitative_bound_on_tsupport_of_subsolution
      (d := d) hd A (u := u) (η := η) (s := s) hs hs1 hsub hu1 hη_sub_ball
  let N : ℝ := N0 + 1
  have hN_pos : 0 < N := by
    dsimp [N]
    linarith
  have hN : 0 ≤ N := hN_pos.le
  have hqual :
      ∀ᵐ x ∂(volume.restrict Ω),
        x ∈ tsupport η → max (u x) 0 < N := by
    filter_upwards [hqual0] with x hx hxη
    dsimp [N]
    linarith [hx hxη]
  obtain ⟨ρ, hρ, hρs, hη_sub_ρ⟩ :=
    exists_lt_one_ball_of_tsupport_subset_ball (η := η) (s := s) hs hs1 hη_sub_ball
  have hρ1 : ρ < 1 := lt_of_lt_of_le hρs hs1
  let f : E → ℝ := moserPowerCutoff (d := d) η u p
  let fn : ℕ → E → ℝ := fun n => moserExactRegPowerCutoff η u (moserEpsSeq n) N p
  let wfnBig : ∀ n : ℕ, MemW1pWitness 2 (fun x => fn n x) (Metric.ball (0 : E) 1) := fun n =>
    by
      dsimp [fn]
      exact
        moserExactRegPowerCutoffWitness
          (d := d) (u := u) (η := η) (ε := moserEpsSeq n) (N := N) (p := p) (Cη := Cη)
          (moserEpsSeq_pos n) hN hu1 hη hη_bound hη_grad_bound
  let wfn : ∀ n : ℕ, MemW1pWitness 2 (fun x => fn n x) Ω := fun n =>
    (wfnBig n).restrict Metric.isOpen_ball (Metric.ball_subset_ball hs1)
  have hfn_tendsto_ae :
      ∀ᵐ x ∂(volume.restrict Ω), Tendsto (fun n => fn n x) atTop (nhds (f x)) := by
    filter_upwards [hqual] with x hx
    exact
      moserExactRegPowerCutoff_tendsto_powerCutoff_of_support_bound
        (d := d) (u := u) (η := η) (N := N) (p := p) (x := x) hp
        (fun hxη => hx hxη)
  let μ : Measure E := volume.restrict Ω
  let Ωρ : Set E := Metric.ball (0 : E) ρ
  let μρ : Measure E := volume.restrict Ωρ
  let huΩ : MemW1pWitness 2 u Ω :=
    hu1.restrict Metric.isOpen_ball (Metric.ball_subset_ball hs1)
  let hwPos : MemW1pWitness 2 (fun x => max (u x) 0) Ω :=
    (moserPosPartWitnessUnitBall (d := d) (u := u) hu1).restrict
      Metric.isOpen_ball (Metric.ball_subset_ball hs1)
  have hΩρ_sub_Ω : Ωρ ⊆ Ω := Metric.ball_subset_ball (le_of_lt hρs)
  have hqualρ :
      ∀ᵐ x ∂μρ, x ∈ tsupport η → max (u x) 0 < N := by
    exact ae_restrict_of_ae_restrict_of_subset hΩρ_sub_Ω hqual
  have hsublevelΩ :
      ∀ᵐ x ∂μ, u x ≤ 0 → hwPos.weakGrad x = 0 := by
    simpa [μ, hwPos] using
      moserPosPartWitness_restrict_grad_zero_on_nonpos
        (d := d) (Ω := Ω) Metric.isOpen_ball (Metric.ball_subset_ball hs1) hu1
  letI : IsFiniteMeasure μ := by
    refine ⟨?_⟩
    simpa [μ, Ω] using
      (measure_ball_lt_top (μ := volume) (x := (0 : E)) (r := s))
  letI : IsFiniteMeasure μρ := by
    refine ⟨?_⟩
    simpa [μρ, Ωρ] using
      (measure_ball_lt_top (μ := volume) (x := (0 : E)) (r := ρ))
  let Cfun : ℝ := 2 * (1 + N) ^ (p / 2)
  have hCfun_nonneg : 0 ≤ Cfun := by
    dsimp [Cfun]
    positivity
  have hCfun_norm : ‖Cfun‖ = Cfun := by
    rw [Real.norm_eq_abs, abs_of_nonneg hCfun_nonneg]
  have hCfun_memLp : MemLp (fun _ : E => Cfun) 2 μ := by
    simpa [Cfun] using (memLp_const Cfun : MemLp (fun _ : E => Cfun) 2 μ)
  have hf_memLp : MemLp f 2 μ := by
    refine hCfun_memLp.of_le ?_ ?_
    · have hpow_cont : Continuous fun t : ℝ => t ^ (p / 2) := by
        exact Real.continuous_rpow_const (by linarith)
      have hpow_meas :
          AEStronglyMeasurable (fun x => |max (u x) 0| ^ (p / 2)) μ := by
        exact
          ((hpow_cont.measurable.comp_aemeasurable
            ((measurable_abs.comp_aemeasurable
              (huΩ.memLp.aestronglyMeasurable.aemeasurable.max
                measurable_const.aemeasurable)))).aestronglyMeasurable)
      simpa [f, moserPowerCutoff] using
        hη.continuous.aestronglyMeasurable.mul hpow_meas
    · filter_upwards [hqual] with x hx
      by_cases hxη : x ∈ tsupport η
      · have hboundx : max (u x) 0 < N := hx hxη
        have hmax_abs : |max (u x) 0| = max (u x) 0 := by
          exact abs_of_nonneg (le_max_right _ _)
        have hpow_le :
            |max (u x) 0| ^ (p / 2) ≤ (1 + N) ^ (p / 2) := by
          simpa [hmax_abs] using
            (Real.rpow_le_rpow (show 0 ≤ max (u x) 0 by exact le_max_right _ _)
              (by linarith) (by linarith))
        have hpow_norm_le :
            ‖|max (u x) 0| ^ (p / 2)‖ ≤ (1 + N) ^ (p / 2) := by
          rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
          exact hpow_le
        have hpow_nonneg : 0 ≤ (1 + N) ^ (p / 2) := by
          exact Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ 1 + N) (p / 2)
        calc
          ‖f x‖ = ‖η x * (|max (u x) 0| ^ (p / 2))‖ := by
            simp [f, moserPowerCutoff]
          _ = ‖η x‖ * ‖|max (u x) 0| ^ (p / 2)‖ := by rw [norm_mul]
          _ = |η x| * ‖|max (u x) 0| ^ (p / 2)‖ := by
            rw [Real.norm_eq_abs]
          _ ≤ |η x| * (1 + N) ^ (p / 2) := by
            exact mul_le_mul_of_nonneg_left hpow_norm_le (abs_nonneg _)
          _ ≤ 1 * (1 + N) ^ (p / 2) := by
            exact mul_le_mul_of_nonneg_right (hη_bound x) hpow_nonneg
          _ ≤ ‖Cfun‖ := by
            dsimp [Cfun]
            have hCfun'_nonneg : 0 ≤ 2 * (1 + N) ^ (p / 2) := by positivity
            have habs : |2 * (1 + N) ^ (p / 2)| = 2 * (1 + N) ^ (p / 2) := by
              exact abs_of_nonneg hCfun'_nonneg
            nlinarith [hpow_nonneg, habs]
      · have hηx : η x = 0 := image_eq_zero_of_notMem_tsupport hxη
        calc
          ‖f x‖ = 0 := by simp [f, moserPowerCutoff, hηx]
          _ ≤ ‖Cfun‖ := by
            simpa [hCfun_norm] using hCfun_nonneg
  have hfn_fun_memLp :
      ∀ n, MemLp (fun x => fn n x - f x) 2 μ := by
    intro n
    exact (wfn n).memLp.sub hf_memLp
  have hfn_meas : ∀ n, AEStronglyMeasurable (fun x => fn n x - f x) μ := by
    intro n
    exact (hfn_fun_memLp n).aestronglyMeasurable
  have hfn_dom :
      ∀ n, ∀ᵐ x ∂μ, |fn n x - f x| ≤ Cfun := by
    intro n
    filter_upwards [hqual] with x hx
    by_cases hxη : x ∈ tsupport η
    · have hboundx : max (u x) 0 < N := hx hxη
      have hp_nonneg : 0 ≤ p := by linarith
      have hmax_abs : |max (u x) 0| = max (u x) 0 := by
        exact abs_of_nonneg (le_max_right _ _)
      have hreg_le :
          moserExactRegPow (moserEpsSeq n) N p (max (u x) 0) ≤ (1 + N) ^ (p / 2) := by
        have hbase :=
          moserExactRegPow_le_rpow_of_nonneg_le_N
            (ε := moserEpsSeq n) (N := N) (p := p) (t := max (u x) 0)
            (moserEpsSeq_pos n) (le_max_right _ _) hboundx.le (by linarith)
        have hsum_le : moserEpsSeq n + max (u x) 0 ≤ 1 + N := by
          have := moserEpsSeq_le_one n
          linarith
        have hsum_nonneg : 0 ≤ moserEpsSeq n + max (u x) 0 := by
          exact add_nonneg (moserEpsSeq_pos n).le (le_max_right _ _)
        calc
          moserExactRegPow (moserEpsSeq n) N p (max (u x) 0)
              ≤ (moserEpsSeq n + max (u x) 0) ^ (p / 2) := hbase
          _ ≤ (1 + N) ^ (p / 2) := by
              exact Real.rpow_le_rpow hsum_nonneg hsum_le (by linarith)
      have hreg_nonneg :
          0 ≤ moserExactRegPow (moserEpsSeq n) N p (max (u x) 0) := by
        exact moserExactRegPow_nonneg_of_nonneg_le_N
          (ε := moserEpsSeq n) (N := N) (p := p) (t := max (u x) 0)
          (moserEpsSeq_pos n) (le_max_right _ _) hboundx.le hp_nonneg
      have hreg_norm_le :
          ‖moserExactRegPow (moserEpsSeq n) N p (max (u x) 0)‖ ≤ (1 + N) ^ (p / 2) := by
        rw [Real.norm_eq_abs, abs_of_nonneg hreg_nonneg]
        exact hreg_le
      have hpow_le :
          |max (u x) 0| ^ (p / 2) ≤ (1 + N) ^ (p / 2) := by
        simpa [hmax_abs] using
          (Real.rpow_le_rpow (show 0 ≤ max (u x) 0 by exact le_max_right _ _)
            (by linarith) (by linarith))
      have hpow_norm_le :
          ‖|max (u x) 0| ^ (p / 2)‖ ≤ (1 + N) ^ (p / 2) := by
        rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
        exact hpow_le
      have hpow_nonneg : 0 ≤ (1 + N) ^ (p / 2) := by
        exact Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ 1 + N) (p / 2)
      have hfn_bound : ‖fn n x‖ ≤ (1 + N) ^ (p / 2) := by
        calc
          ‖fn n x‖ = |η x| * ‖moserExactRegPow (moserEpsSeq n) N p (max (u x) 0)‖ := by
            simp [fn, moserExactRegPowerCutoff, norm_mul]
          _ ≤ |η x| * (1 + N) ^ (p / 2) := by
            exact mul_le_mul_of_nonneg_left hreg_norm_le (abs_nonneg _)
          _ ≤ 1 * (1 + N) ^ (p / 2) := by
            exact mul_le_mul_of_nonneg_right (hη_bound x) hpow_nonneg
          _ = (1 + N) ^ (p / 2) := by ring
      have hfn_abs_bound : |fn n x| ≤ (1 + N) ^ (p / 2) := by
        simpa [Real.norm_eq_abs] using hfn_bound
      have hf_bound : ‖f x‖ ≤ (1 + N) ^ (p / 2) := by
        calc
          ‖f x‖ = |η x| * ‖|max (u x) 0| ^ (p / 2)‖ := by
            simp [f, moserPowerCutoff, norm_mul]
          _ ≤ |η x| * (1 + N) ^ (p / 2) := by
            exact mul_le_mul_of_nonneg_left hpow_norm_le (abs_nonneg _)
          _ ≤ 1 * (1 + N) ^ (p / 2) := by
            exact mul_le_mul_of_nonneg_right (hη_bound x) hpow_nonneg
          _ = (1 + N) ^ (p / 2) := by ring
      have hf_abs_bound : |f x| ≤ (1 + N) ^ (p / 2) := by
        simpa [Real.norm_eq_abs] using hf_bound
      calc
        |fn n x - f x| ≤ ‖fn n x‖ + ‖f x‖ := by simpa [Real.norm_eq_abs] using norm_sub_le (fn n x) (f x)
        _ ≤ Cfun := by
            dsimp [Cfun]
            nlinarith [hfn_abs_bound, hf_abs_bound, hpow_nonneg]
    · have hηx : η x = 0 := image_eq_zero_of_notMem_tsupport hxη
      calc
        |fn n x - f x| = 0 := by simp [fn, f, moserExactRegPowerCutoff, moserPowerCutoff, hηx]
        _ ≤ Cfun := hCfun_nonneg
  have hfn_tendsto :
      Tendsto (fun n => eLpNorm (fun x => fn n x - f x) 2 μ) atTop (nhds 0) := by
    exact moser_tendsto_eLpNorm_zero_of_dominated hCfun_memLp hfn_meas hfn_dom <| by
      filter_upwards [hfn_tendsto_ae] with x hx
      have hconst : Tendsto (fun _ : ℕ => f x) atTop (nhds (f x)) := tendsto_const_nhds
      simpa using hx.sub hconst
  have hCη_nonneg : 0 ≤ Cη := by
    have hgrad0 : ‖fderiv ℝ η (0 : E)‖ ≤ Cη := hη_grad_bound (0 : E)
    nlinarith [norm_nonneg (fderiv ℝ η (0 : E))]
  let Bn : ℕ → Fin d → E → ℝ := fun n i x =>
    (fderiv ℝ η x) (EuclideanSpace.single i 1) *
      moserExactRegPow (moserEpsSeq n) N p (max (u x) 0)
  let B : Fin d → E → ℝ := fun i x =>
    (fderiv ℝ η x) (EuclideanSpace.single i 1) * (max (u x) 0) ^ (p / 2)
  let CB : ℝ := 2 * Cη * (1 + N) ^ (p / 2)
  have hCB_nonneg : 0 ≤ CB := by
    dsimp [CB]
    have h1N_nonneg : 0 ≤ 1 + N := by linarith
    positivity
  have hCB_memLp : MemLp (fun _ : E => CB) 2 μ := by
    simpa [CB] using (memLp_const CB : MemLp (fun _ : E => CB) 2 μ)
  have hB_tendsto_ae :
      ∀ i : Fin d, ∀ᵐ x ∂μ, Tendsto (fun n => Bn n i x) atTop (nhds (B i x)) := by
    intro i
    filter_upwards [hqual] with x hx
    by_cases hxη : x ∈ tsupport η
    · have hboundx : max (u x) 0 < N := hx hxη
      have hpow :=
        moserExactRegPow_tendsto_rpow_of_nonneg_lt_N
          (N := N) (p := p) (t := max (u x) 0)
          (le_max_right _ _) hboundx hp
      simpa [Bn, B, mul_assoc, mul_left_comm, mul_comm] using
        Tendsto.const_mul ((fderiv ℝ η x) (EuclideanSpace.single i 1)) hpow
    · have hfderiv_zero :
          (fderiv ℝ η x) (EuclideanSpace.single i 1) = 0 := by
        exact fderiv_apply_zero_outside_of_tsupport_subset
          (Ω := tsupport η) (hf := hη) (hsub := subset_rfl) hxη i
      simp [Bn, B, hfderiv_zero]
  have hB_memLp :
      ∀ i : Fin d, MemLp (B i) 2 μ := by
    intro i
    refine hCB_memLp.of_le ?_ ?_
    · exact aestronglyMeasurable_of_tendsto_ae atTop
        (fun n => by
          have hpow_meas :
              AEMeasurable (fun x => moserExactRegPow (moserEpsSeq n) N p (max (u x) 0)) μ := by
            exact
              (moserExactRegPow_contDiff (ε := moserEpsSeq n) (N := N) (p := p)
                (moserEpsSeq_pos n) hN).continuous.measurable.comp_aemeasurable
                  (huΩ.memLp.aestronglyMeasurable.aemeasurable.max measurable_const.aemeasurable)
          exact
            (((hη.continuous_fderiv (by simp)).clm_apply continuous_const).aestronglyMeasurable.mul
              hpow_meas.aestronglyMeasurable)
        ) (hB_tendsto_ae i)
    · filter_upwards [hqual] with x hx
      by_cases hxη : x ∈ tsupport η
      · have hboundx : max (u x) 0 < N := hx hxη
        have hpow_le :
            (max (u x) 0) ^ (p / 2) ≤ (1 + N) ^ (p / 2) := by
          exact Real.rpow_le_rpow (show 0 ≤ max (u x) 0 by exact le_max_right _ _)
            (by linarith) (by linarith)
        have hpow_norm_le :
            ‖(max (u x) 0) ^ (p / 2)‖ ≤ (1 + N) ^ (p / 2) := by
          rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (show 0 ≤ max (u x) 0 by
            exact le_max_right _ _) _)]
          exact hpow_le
        have hfd_le :
            ‖(fderiv ℝ η x) (EuclideanSpace.single i 1)‖ ≤ Cη := by
          calc
            ‖(fderiv ℝ η x) (EuclideanSpace.single i 1)‖ ≤ ‖fderiv ℝ η x‖ := by
              simpa using (ContinuousLinearMap.le_opNorm (fderiv ℝ η x)
                (EuclideanSpace.single i (1 : ℝ)))
            _ ≤ Cη := hη_grad_bound x
        have hpow_nonneg : 0 ≤ (1 + N) ^ (p / 2) := by
          exact Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ 1 + N) (p / 2)
        calc
          ‖B i x‖ = ‖(fderiv ℝ η x) (EuclideanSpace.single i 1)‖ * ‖(max (u x) 0) ^ (p / 2)‖ := by
            simp [B, norm_mul]
          _ ≤ Cη * (1 + N) ^ (p / 2) := by
            exact mul_le_mul hfd_le hpow_norm_le (norm_nonneg _) hCη_nonneg
          _ ≤ CB := by
            calc
              Cη * (1 + N) ^ (p / 2) ≤ 2 * (Cη * (1 + N) ^ (p / 2)) := by
                nlinarith [hCη_nonneg, hpow_nonneg]
              _ = CB := by ring
          _ = ‖CB‖ := by
            rw [Real.norm_eq_abs, abs_of_nonneg hCB_nonneg]
      · have hfderiv_zero :
          (fderiv ℝ η x) (EuclideanSpace.single i 1) = 0 := by
          exact fderiv_apply_zero_outside_of_tsupport_subset
            (Ω := tsupport η) (hf := hη) (hsub := subset_rfl) hxη i
        calc
          ‖B i x‖ = 0 := by simp [B, hfderiv_zero]
          _ ≤ ‖CB‖ := by
            simpa [Real.norm_eq_abs, abs_of_nonneg hCB_nonneg] using hCB_nonneg
  have hBn_fun_memLp :
      ∀ n i, MemLp (fun x => Bn n i x - B i x) 2 μ := by
    intro n i
    have hpow_meas :
        AEMeasurable (fun x => moserExactRegPow (moserEpsSeq n) N p (max (u x) 0)) μ := by
      exact
        (moserExactRegPow_contDiff (ε := moserEpsSeq n) (N := N) (p := p)
          (moserEpsSeq_pos n) hN).continuous.measurable.comp_aemeasurable
            (huΩ.memLp.aestronglyMeasurable.aemeasurable.max measurable_const.aemeasurable)
    have hBn_memLp : MemLp (Bn n i) 2 μ := by
      refine hCB_memLp.of_le ?_ ?_
      · exact
          (((hη.continuous_fderiv (by simp)).clm_apply continuous_const).aestronglyMeasurable.mul
            hpow_meas.aestronglyMeasurable)
      · filter_upwards [hqual] with x hx
        by_cases hxη : x ∈ tsupport η
        · have hboundx : max (u x) 0 < N := hx hxη
          have hp_nonneg : 0 ≤ p := by linarith
          have hreg_le :
              moserExactRegPow (moserEpsSeq n) N p (max (u x) 0) ≤ (1 + N) ^ (p / 2) := by
            have hbase :=
              moserExactRegPow_le_rpow_of_nonneg_le_N
                (ε := moserEpsSeq n) (N := N) (p := p) (t := max (u x) 0)
                (moserEpsSeq_pos n) (le_max_right _ _) hboundx.le (by linarith)
            have hsum_le : moserEpsSeq n + max (u x) 0 ≤ 1 + N := by
              have := moserEpsSeq_le_one n
              linarith
            have hsum_nonneg : 0 ≤ moserEpsSeq n + max (u x) 0 := by
              exact add_nonneg (moserEpsSeq_pos n).le (le_max_right _ _)
            calc
              moserExactRegPow (moserEpsSeq n) N p (max (u x) 0)
                  ≤ (moserEpsSeq n + max (u x) 0) ^ (p / 2) := hbase
              _ ≤ (1 + N) ^ (p / 2) := by
                  exact Real.rpow_le_rpow hsum_nonneg hsum_le (by linarith)
          have hreg_nonneg :
              0 ≤ moserExactRegPow (moserEpsSeq n) N p (max (u x) 0) := by
            exact moserExactRegPow_nonneg_of_nonneg_le_N
              (ε := moserEpsSeq n) (N := N) (p := p) (t := max (u x) 0)
              (moserEpsSeq_pos n) (le_max_right _ _) hboundx.le hp_nonneg
          have hreg_norm_le :
              ‖moserExactRegPow (moserEpsSeq n) N p (max (u x) 0)‖ ≤ (1 + N) ^ (p / 2) := by
            rw [Real.norm_eq_abs, abs_of_nonneg hreg_nonneg]
            exact hreg_le
          have hfd_le :
              ‖(fderiv ℝ η x) (EuclideanSpace.single i 1)‖ ≤ Cη := by
            calc
              ‖(fderiv ℝ η x) (EuclideanSpace.single i 1)‖ ≤ ‖fderiv ℝ η x‖ := by
                simpa using (ContinuousLinearMap.le_opNorm (fderiv ℝ η x)
                  (EuclideanSpace.single i (1 : ℝ)))
              _ ≤ Cη := hη_grad_bound x
          have hpow_nonneg : 0 ≤ (1 + N) ^ (p / 2) := by
            exact Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ 1 + N) (p / 2)
          calc
            ‖Bn n i x‖
                = ‖(fderiv ℝ η x) (EuclideanSpace.single i 1)‖ *
                    ‖moserExactRegPow (moserEpsSeq n) N p (max (u x) 0)‖ := by
                      simp [Bn, norm_mul]
            _ ≤ Cη * (1 + N) ^ (p / 2) := by
                exact mul_le_mul hfd_le hreg_norm_le (norm_nonneg _) hCη_nonneg
            _ ≤ CB := by
                calc
                  Cη * (1 + N) ^ (p / 2) ≤ 2 * (Cη * (1 + N) ^ (p / 2)) := by
                    nlinarith [hCη_nonneg, hpow_nonneg]
                  _ = CB := by ring
            _ = ‖CB‖ := by
                rw [Real.norm_eq_abs, abs_of_nonneg hCB_nonneg]
        · have hfderiv_zero :
            (fderiv ℝ η x) (EuclideanSpace.single i 1) = 0 := by
            exact fderiv_apply_zero_outside_of_tsupport_subset
              (Ω := tsupport η) (hf := hη) (hsub := subset_rfl) hxη i
          calc
            ‖Bn n i x‖ = 0 := by simp [Bn, hfderiv_zero]
            _ ≤ ‖CB‖ := by
              simpa [Real.norm_eq_abs, abs_of_nonneg hCB_nonneg] using hCB_nonneg
    exact hBn_memLp.sub (hB_memLp i)
  have hBn_meas : ∀ n i, AEStronglyMeasurable (fun x => Bn n i x - B i x) μ := by
    intro n i
    exact (hBn_fun_memLp n i).aestronglyMeasurable
  have hBn_dom :
      ∀ n i, ∀ᵐ x ∂μ, |Bn n i x - B i x| ≤ CB := by
    intro n i
    filter_upwards [hqual] with x hx
    by_cases hxη : x ∈ tsupport η
    · have hboundx : max (u x) 0 < N := hx hxη
      have hp_nonneg : 0 ≤ p := by linarith
      have hBn_bound :
          ‖Bn n i x‖ ≤ Cη * (1 + N) ^ (p / 2) := by
        have hreg_le :
            moserExactRegPow (moserEpsSeq n) N p (max (u x) 0) ≤ (1 + N) ^ (p / 2) := by
          have hbase :=
            moserExactRegPow_le_rpow_of_nonneg_le_N
              (ε := moserEpsSeq n) (N := N) (p := p) (t := max (u x) 0)
              (moserEpsSeq_pos n) (le_max_right _ _) hboundx.le (by linarith)
          have hsum_le : moserEpsSeq n + max (u x) 0 ≤ 1 + N := by
            have := moserEpsSeq_le_one n
            linarith
          have hsum_nonneg : 0 ≤ moserEpsSeq n + max (u x) 0 := by
            exact add_nonneg (moserEpsSeq_pos n).le (le_max_right _ _)
          calc
            moserExactRegPow (moserEpsSeq n) N p (max (u x) 0)
                ≤ (moserEpsSeq n + max (u x) 0) ^ (p / 2) := hbase
            _ ≤ (1 + N) ^ (p / 2) := by
                exact Real.rpow_le_rpow hsum_nonneg hsum_le (by linarith)
        have hreg_nonneg :
            0 ≤ moserExactRegPow (moserEpsSeq n) N p (max (u x) 0) := by
          exact moserExactRegPow_nonneg_of_nonneg_le_N
            (ε := moserEpsSeq n) (N := N) (p := p) (t := max (u x) 0)
            (moserEpsSeq_pos n) (le_max_right _ _) hboundx.le hp_nonneg
        have hreg_norm_le :
            ‖moserExactRegPow (moserEpsSeq n) N p (max (u x) 0)‖ ≤ (1 + N) ^ (p / 2) := by
          rw [Real.norm_eq_abs, abs_of_nonneg hreg_nonneg]
          exact hreg_le
        have hfd_le :
            ‖(fderiv ℝ η x) (EuclideanSpace.single i 1)‖ ≤ Cη := by
          calc
            ‖(fderiv ℝ η x) (EuclideanSpace.single i 1)‖ ≤ ‖fderiv ℝ η x‖ := by
              simpa using (ContinuousLinearMap.le_opNorm (fderiv ℝ η x)
                (EuclideanSpace.single i (1 : ℝ)))
            _ ≤ Cη := hη_grad_bound x
        have hpow_nonneg : 0 ≤ (1 + N) ^ (p / 2) := by
          exact Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ 1 + N) (p / 2)
        calc
          ‖Bn n i x‖
              = ‖(fderiv ℝ η x) (EuclideanSpace.single i 1)‖ *
                  ‖moserExactRegPow (moserEpsSeq n) N p (max (u x) 0)‖ := by
                    simp [Bn, norm_mul]
          _ ≤ Cη * (1 + N) ^ (p / 2) := by
              exact mul_le_mul hfd_le hreg_norm_le (norm_nonneg _) hCη_nonneg
      have hB_bound :
          ‖B i x‖ ≤ Cη * (1 + N) ^ (p / 2) := by
        have hpow_le :
            (max (u x) 0) ^ (p / 2) ≤ (1 + N) ^ (p / 2) := by
          exact Real.rpow_le_rpow (show 0 ≤ max (u x) 0 by exact le_max_right _ _)
            (by linarith) (by linarith)
        have hpow_norm_le :
            ‖(max (u x) 0) ^ (p / 2)‖ ≤ (1 + N) ^ (p / 2) := by
          rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (show 0 ≤ max (u x) 0 by
            exact le_max_right _ _) _)]
          exact hpow_le
        have hfd_le :
            ‖(fderiv ℝ η x) (EuclideanSpace.single i 1)‖ ≤ Cη := by
          calc
            ‖(fderiv ℝ η x) (EuclideanSpace.single i 1)‖ ≤ ‖fderiv ℝ η x‖ := by
              simpa using (ContinuousLinearMap.le_opNorm (fderiv ℝ η x)
                (EuclideanSpace.single i (1 : ℝ)))
            _ ≤ Cη := hη_grad_bound x
        have hpow_nonneg : 0 ≤ (1 + N) ^ (p / 2) := by
          exact Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ 1 + N) (p / 2)
        calc
          ‖B i x‖ = ‖(fderiv ℝ η x) (EuclideanSpace.single i 1)‖ * ‖(max (u x) 0) ^ (p / 2)‖ := by
            simp [B, norm_mul]
          _ ≤ Cη * (1 + N) ^ (p / 2) := by
              exact mul_le_mul hfd_le hpow_norm_le (norm_nonneg _) hCη_nonneg
      calc
        |Bn n i x - B i x| ≤ ‖Bn n i x‖ + ‖B i x‖ := by
          simpa [Real.norm_eq_abs] using norm_sub_le (Bn n i x) (B i x)
        _ ≤ CB := by
            have hsum_bound :
                ‖Bn n i x‖ + ‖B i x‖ ≤ 2 * (Cη * (1 + N) ^ (p / 2)) := by
              linarith [hBn_bound, hB_bound]
            calc
              ‖Bn n i x‖ + ‖B i x‖ ≤ 2 * (Cη * (1 + N) ^ (p / 2)) := hsum_bound
              _ = CB := by ring
    · have hfderiv_zero :
          (fderiv ℝ η x) (EuclideanSpace.single i 1) = 0 := by
        exact fderiv_apply_zero_outside_of_tsupport_subset
          (Ω := tsupport η) (hf := hη) (hsub := subset_rfl) hxη i
      have hBn_zero : Bn n i x = 0 := by simp [Bn, hfderiv_zero]
      have hB_zero : B i x = 0 := by simp [B, hfderiv_zero]
      rw [hBn_zero, hB_zero, sub_self, abs_zero]
      exact hCB_nonneg
  have hB_tendsto :
      ∀ i : Fin d,
        Tendsto (fun n => eLpNorm (fun x => Bn n i x - B i x) 2 μ) atTop (nhds 0) := by
    intro i
    exact moser_tendsto_eLpNorm_zero_of_dominated (hCB_memLp) (fun n => hBn_meas n i)
      (fun n => hBn_dom n i) <| by
        filter_upwards [hB_tendsto_ae i] with x hx
        have hconst : Tendsto (fun _ : ℕ => B i x) atTop (nhds (B i x)) := tendsto_const_nhds
        simpa using hx.sub hconst
  let Gn : ℕ → Fin d → E → ℝ := fun n i x => (wfn n).weakGrad x i
  let AsingSeq : ℕ → Fin d → E → ℝ := fun n i x => Gn n i x - Bn n i x
  let Asing : Fin d → E → ℝ := fun i x =>
    if 0 < u x then
      η x * ((p / 2) * (max (u x) 0) ^ (p / 2 - 1)) * hwPos.weakGrad x i
    else 0
  have hBn_memLp :
      ∀ n i, MemLp (Bn n i) 2 μ := by
    intro n i
    convert (hBn_fun_memLp n i).add (hB_memLp i) using 1
    ext x
    simp [sub_eq_add_neg]
  have hAsingSeq_memLp :
      ∀ n i, MemLp (AsingSeq n i) 2 μ := by
    intro n i
    simpa [AsingSeq, Gn] using ((wfn n).weakGrad_component_memLp i).sub (hBn_memLp n i)
  have hAsingSeq_formula :
      ∀ n i x,
        AsingSeq n i x =
          η x * deriv (moserExactRegPow (moserEpsSeq n) N p) (max (u x) 0) *
            hwPos.weakGrad x i := by
    intro n i x
    dsimp [AsingSeq, Gn, Bn, wfn, wfnBig, hwPos]
    simp [MemW1pWitness.restrict]
    rw [moserExactRegPowerCutoffWitness_grad (d := d) (u := u) (η := η) (ε := moserEpsSeq n)
      (N := N) (p := p) (Cη := Cη) (moserEpsSeq_pos n) hN hu1 hη hη_bound
      hη_grad_bound x i]
    ring
  have hAsing_tendsto_ae :
      ∀ i : Fin d, ∀ᵐ x ∂μ, Tendsto (fun n => AsingSeq n i x) atTop (nhds (Asing i x)) := by
    intro i
    filter_upwards [hqual, hsublevelΩ] with x hxqual hsublevelx
    by_cases hxη : x ∈ tsupport η
    · by_cases hux : 0 < u x
      · have hboundx : max (u x) 0 < N := hxqual hxη
        have hderiv :=
          moserExactRegPow_deriv_tendsto_of_pos_lt_N
            (N := N) (p := p) (t := max (u x) 0)
            (by simpa [max_eq_left hux.le] using hux) hboundx
        have hmul :
            Tendsto
              (fun n =>
                (η x * hwPos.weakGrad x i) *
                  deriv (moserExactRegPow (moserEpsSeq n) N p) (max (u x) 0))
              atTop
              (nhds
                ((η x * hwPos.weakGrad x i) *
                  ((p / 2) * (max (u x) 0) ^ (p / 2 - 1)))) := by
          exact Tendsto.const_mul (η x * hwPos.weakGrad x i) hderiv
        have hEq :
            (fun n => AsingSeq n i x) =
              (fun n =>
                (η x * hwPos.weakGrad x i) *
                  deriv (moserExactRegPow (moserEpsSeq n) N p) (max (u x) 0)) := by
          funext n
          rw [hAsingSeq_formula n i x]
          ring
        rw [hEq]
        simpa [Asing, hux, mul_assoc, mul_left_comm, mul_comm] using hmul
      · have hunonpos : u x ≤ 0 := le_of_not_gt hux
        have hgrad_zero : hwPos.weakGrad x = 0 := hsublevelx hunonpos
        have hEq :
            ∀ n, AsingSeq n i x = 0 := by
          intro n
          rw [hAsingSeq_formula n i x, hgrad_zero]
          simp
        refine tendsto_const_nhds.congr' ?_
        exact Filter.Eventually.of_forall fun n => by simp [hEq n, Asing, hux]
    · have hηx : η x = 0 := image_eq_zero_of_notMem_tsupport hxη
      have hEq :
          ∀ n, AsingSeq n i x = 0 := by
        intro n
        rw [hAsingSeq_formula n i x, hηx]
        ring
      refine tendsto_const_nhds.congr' ?_
      exact Filter.Eventually.of_forall fun n => by simp [hEq n, Asing, hηx]
  have hAsing_aestrong :
      ∀ i : Fin d, AEStronglyMeasurable (Asing i) μ := by
    intro i
    exact aestronglyMeasurable_of_tendsto_ae atTop
      (fun n => (hAsingSeq_memLp n i).aestronglyMeasurable) (hAsing_tendsto_ae i)
  have hpIntρ_base :
      Integrable (fun x => |max (u x) 0| ^ p) μρ := by
    have hpIntΩ : Integrable (fun x => |max (u x) 0| ^ p) μ := by
      simpa [μ, Ω] using hpInt
    exact hpIntΩ.mono_measure (Measure.restrict_mono_set volume hΩρ_sub_Ω)
  have hRhsDom_int :
      Integrable (fun x => (2 : ℝ) ^ p * (1 + |max (u x) 0| ^ p)) μρ := by
    have hone : Integrable (fun _ : E => (1 : ℝ)) μρ := by
      change IntegrableOn (fun _ : E => (1 : ℝ)) Ωρ volume
      exact
        integrableOn_const (s := Ωρ)
          ((measure_ball_lt_top (μ := volume) (x := (0 : E)) (r := ρ)).ne)
    exact (hone.add hpIntρ_base).const_mul ((2 : ℝ) ^ p)
  have hpIntρ_eps :
      ∀ n, IntegrableOn (fun x => (moserEpsSeq n + |max (u x) 0|) ^ p) Ωρ volume := by
    intro n
    let huρw : MemW1pWitness 2 u Ωρ :=
      hu1.restrict Metric.isOpen_ball (Metric.ball_subset_ball (le_of_lt hρ1))
    have hmeas :
        AEStronglyMeasurable (fun x => (moserEpsSeq n + |max (u x) 0|) ^ p) μρ := by
      have hmax_meas : AEMeasurable (fun x => max (u x) 0) μρ :=
        huρw.memLp.aestronglyMeasurable.aemeasurable.max measurable_const.aemeasurable
      have habs_meas : AEMeasurable (fun x => |max (u x) 0|) μρ := hmax_meas.norm
      have hsum_meas : AEMeasurable (fun x => moserEpsSeq n + |max (u x) 0|) μρ :=
        habs_meas.const_add (moserEpsSeq n)
      exact (hsum_meas.pow_const p).aestronglyMeasurable
    have hbound :
        ∀ᵐ x ∂μρ, ‖(moserEpsSeq n + |max (u x) 0|) ^ p‖ ≤
          (2 : ℝ) ^ p * (1 + |max (u x) 0| ^ p) := by
      exact Filter.Eventually.of_forall (fun x => by
        have hbase_nonneg : 0 ≤ |max (u x) 0| := abs_nonneg _
        have hsum_nonneg : 0 ≤ moserEpsSeq n + |max (u x) 0| := by
          exact add_nonneg (moserEpsSeq_pos n).le hbase_nonneg
        have hpt :
            |(moserEpsSeq n + |max (u x) 0|) ^ p| ≤
              (2 : ℝ) ^ p * (1 + |max (u x) 0| ^ p) := by
          calc
            |(moserEpsSeq n + |max (u x) 0|) ^ p|
                = (moserEpsSeq n + |max (u x) 0|) ^ p := by
                    rw [abs_of_nonneg (Real.rpow_nonneg hsum_nonneg _)]
            _ ≤ (1 + |max (u x) 0|) ^ p := by
                exact Real.rpow_le_rpow hsum_nonneg (by linarith [moserEpsSeq_le_one n]) (by linarith)
            _ ≤ (2 : ℝ) ^ p * (1 + |max (u x) 0| ^ p) := by
                exact one_add_rpow_le_two_rpow_mul_one_add_rpow hbase_nonneg (by linarith)
        simpa [Real.norm_eq_abs] using hpt)
    exact Integrable.mono' hRhsDom_int hmeas hbound
  have hGn_zero_outside_ρ :
      ∀ n, ∀ᵐ x ∂μ, x ∉ Ωρ → (wfn n).weakGrad x = 0 := by
    intro n
    filter_upwards with x hxρ
    have hxη : x ∉ tsupport η := fun hxt => hxρ (hη_sub_ρ hxt)
    have hηx : η x = 0 := image_eq_zero_of_notMem_tsupport hxη
    apply PiLp.ext
    intro i
    have hfderiv_zero :
        (fderiv ℝ η x) (EuclideanSpace.single i 1) = 0 := by
      exact fderiv_apply_zero_outside_of_tsupport_subset
        (Ω := tsupport η) (hf := hη) (hsub := subset_rfl) hxη i
    simpa [wfn, wfnBig, fn, hηx, hfderiv_zero] using
      (moserExactRegPowerCutoffWitness_grad (d := d) (u := u) (η := η) (ε := moserEpsSeq n)
        (N := N) (p := p) (Cη := Cη) (moserEpsSeq_pos n) hN hu1 hη hη_bound
        hη_grad_bound x i)
  have hGn_int_eq_ρ :
      ∀ n,
        ∫ x in Ω, ‖(wfn n).weakGrad x‖ ^ 2 ∂volume =
          ∫ x in Ωρ, ‖(wfn n).weakGrad x‖ ^ 2 ∂volume := by
    intro n
    have hEq_ind :
        (fun x => ‖(wfn n).weakGrad x‖ ^ 2) =ᵐ[μ]
          Set.indicator Ωρ (fun x => ‖(wfn n).weakGrad x‖ ^ 2) := by
      filter_upwards [hGn_zero_outside_ρ n] with x hx
      by_cases hxρ : x ∈ Ωρ
      · simp [Set.indicator_of_mem, hxρ]
      · simp [Set.indicator_of_notMem, hxρ, hx hxρ]
    calc
      ∫ x in Ω, ‖(wfn n).weakGrad x‖ ^ 2 ∂volume
          = ∫ x, ‖(wfn n).weakGrad x‖ ^ 2 ∂μ := by
              simp [μ]
      _ = ∫ x, Set.indicator Ωρ (fun x => ‖(wfn n).weakGrad x‖ ^ 2) x ∂μ := by
            exact integral_congr_ae hEq_ind
      _ = ∫ x in Ωρ, ‖(wfn n).weakGrad x‖ ^ 2 ∂μ := by
            exact integral_indicator Metric.isOpen_ball.measurableSet
      _ = ∫ x in Ωρ, ‖(wfn n).weakGrad x‖ ^ 2 ∂volume := by
            simp [μ, Measure.restrict_restrict_of_subset hΩρ_sub_Ω]
  let CE : ℝ := 2 * Cη ^ 2 * (A.1.Λ * (p / (p - 1)) ^ 2 + 1)
  have hCE_nonneg : 0 ≤ CE := by
    dsimp [CE]
    have hterm_nonneg : 0 ≤ A.1.Λ * (p / (p - 1)) ^ 2 + 1 := by
      have hratio_sq_nonneg : 0 ≤ (p / (p - 1)) ^ 2 := sq_nonneg _
      exact add_nonneg (mul_nonneg A.1.Λ_pos.le hratio_sq_nonneg) zero_le_one
    exact mul_nonneg (mul_nonneg (by positivity) (sq_nonneg Cη)) hterm_nonneg
  have hGn_energy :
      ∀ n,
        ∫ x in Ω, ‖(wfn n).weakGrad x‖ ^ 2 ∂volume ≤
          CE * ∫ x in Ωρ, (2 : ℝ) ^ p * (1 + |max (u x) 0| ^ p) ∂volume := by
    intro n
    have hbound_pt :
        ∀ᵐ x ∂μρ,
          (moserEpsSeq n + |max (u x) 0|) ^ p ≤
            (2 : ℝ) ^ p * (1 + |max (u x) 0| ^ p) := by
      filter_upwards with x
      have hbase_nonneg : 0 ≤ |max (u x) 0| := abs_nonneg _
      have hsum_nonneg : 0 ≤ moserEpsSeq n + |max (u x) 0| := by
        exact add_nonneg (moserEpsSeq_pos n).le hbase_nonneg
      calc
        (moserEpsSeq n + |max (u x) 0|) ^ p
            ≤ (1 + |max (u x) 0|) ^ p := by
                exact Real.rpow_le_rpow hsum_nonneg (by linarith [moserEpsSeq_le_one n]) (by linarith)
        _ ≤ (2 : ℝ) ^ p * (1 + |max (u x) 0| ^ p) := by
            exact one_add_rpow_le_two_rpow_mul_one_add_rpow hbase_nonneg (by linarith)
    have hmainρ :
        ∫ x in Ωρ, ‖(wfn n).weakGrad x‖ ^ 2 ∂volume ≤
          CE * ∫ x in Ωρ, (moserEpsSeq n + |max (u x) 0|) ^ p ∂volume := by
      have hmainρ_big :
          ∫ x in Ωρ, ‖(wfnBig n).weakGrad x‖ ^ 2 ∂volume ≤
            CE * ∫ x in Ωρ, (moserEpsSeq n + |max (u x) 0|) ^ p ∂volume := by
        simpa [CE, Ωρ, wfnBig, fn] using
          (moserExactReg_energy_mainBall
            (d := d) (A := A) (u := u) (η := η) (p := p) (ρ := ρ)
            (Cη := Cη) (N := N) (hp := hp) (hρ := hρ) (hρ1 := hρ1) (hN := hN)
            (hsub := hsub) (hu1 := hu1) (hη := hη) (hη_nonneg := hη_nonneg)
            (hη_bound := hη_bound) (hη_grad_bound := hη_grad_bound)
            (hη_sub_ball := hη_sub_ρ) (hqual := hqualρ) (hpInt := hpIntρ_eps) n)
      change ∫ x in Ωρ, ‖(wfnBig n).weakGrad x‖ ^ 2 ∂volume ≤
        CE * ∫ x in Ωρ, (moserEpsSeq n + |max (u x) 0|) ^ p ∂volume
      exact hmainρ_big
    have hdom_int :
        Integrable (fun x => (2 : ℝ) ^ p * (1 + |max (u x) 0| ^ p)) μρ := hRhsDom_int
    calc
      ∫ x in Ω, ‖(wfn n).weakGrad x‖ ^ 2 ∂volume
          = ∫ x in Ωρ, ‖(wfn n).weakGrad x‖ ^ 2 ∂volume := hGn_int_eq_ρ n
      _ ≤ CE * ∫ x in Ωρ, (moserEpsSeq n + |max (u x) 0|) ^ p ∂volume := hmainρ
      _ ≤ CE * ∫ x in Ωρ, (2 : ℝ) ^ p * (1 + |max (u x) 0| ^ p) ∂volume := by
            refine mul_le_mul_of_nonneg_left ?_ hCE_nonneg
            exact integral_mono_ae (hpIntρ_eps n) hdom_int hbound_pt
  let CB0 : ℝ := Cη * (1 + N) ^ (p / 2)
  have hBn_sq_bound :
      ∀ n i,
        ∫ x in Ω, (Bn n i x) ^ 2 ∂volume ≤
          CB0 ^ 2 * (volume Ω).toReal := by
    intro n i
    have hBn_pt :
        ∀ᵐ x ∂μ, (Bn n i x) ^ 2 ≤ CB0 ^ 2 := by
      filter_upwards [hqual] with x hx
      by_cases hxη : x ∈ tsupport η
      · have hboundx : max (u x) 0 < N := hx hxη
        have hp_nonneg : 0 ≤ p := by linarith
        have hreg_le :
            moserExactRegPow (moserEpsSeq n) N p (max (u x) 0) ≤ (1 + N) ^ (p / 2) := by
          have hbase :=
            moserExactRegPow_le_rpow_of_nonneg_le_N
              (ε := moserEpsSeq n) (N := N) (p := p) (t := max (u x) 0)
              (moserEpsSeq_pos n) (le_max_right _ _) hboundx.le (by linarith)
          have hsum_le : moserEpsSeq n + max (u x) 0 ≤ 1 + N := by
            have := moserEpsSeq_le_one n
            linarith
          have hsum_nonneg : 0 ≤ moserEpsSeq n + max (u x) 0 := by
            exact add_nonneg (moserEpsSeq_pos n).le (le_max_right _ _)
          calc
            moserExactRegPow (moserEpsSeq n) N p (max (u x) 0)
                ≤ (moserEpsSeq n + max (u x) 0) ^ (p / 2) := hbase
            _ ≤ (1 + N) ^ (p / 2) := by
                exact Real.rpow_le_rpow hsum_nonneg hsum_le (by linarith)
        have hreg_nonneg :
            0 ≤ moserExactRegPow (moserEpsSeq n) N p (max (u x) 0) := by
          exact moserExactRegPow_nonneg_of_nonneg_le_N
            (ε := moserEpsSeq n) (N := N) (p := p) (t := max (u x) 0)
            (moserEpsSeq_pos n) (le_max_right _ _) hboundx.le hp_nonneg
        have hreg_norm_le :
            ‖moserExactRegPow (moserEpsSeq n) N p (max (u x) 0)‖ ≤ (1 + N) ^ (p / 2) := by
          rw [Real.norm_eq_abs, abs_of_nonneg hreg_nonneg]
          exact hreg_le
        have hfd_le :
            ‖(fderiv ℝ η x) (EuclideanSpace.single i 1)‖ ≤ Cη := by
          calc
            ‖(fderiv ℝ η x) (EuclideanSpace.single i 1)‖ ≤ ‖fderiv ℝ η x‖ := by
              simpa using (ContinuousLinearMap.le_opNorm (fderiv ℝ η x)
                (EuclideanSpace.single i (1 : ℝ)))
            _ ≤ Cη := hη_grad_bound x
        have hpow_nonneg : 0 ≤ (1 + N) ^ (p / 2) := by
          exact Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ 1 + N) (p / 2)
        have hBn_bound :
            ‖Bn n i x‖ ≤ CB0 := by
          calc
            ‖Bn n i x‖
                = ‖(fderiv ℝ η x) (EuclideanSpace.single i 1)‖ *
                    ‖moserExactRegPow (moserEpsSeq n) N p (max (u x) 0)‖ := by
                      simp [Bn, norm_mul]
            _ ≤ Cη * (1 + N) ^ (p / 2) := by
                exact mul_le_mul hfd_le hreg_norm_le (norm_nonneg _) hCη_nonneg
            _ = CB0 := by rfl
        have habs_bound : |Bn n i x| ≤ CB0 := by
          simpa [Real.norm_eq_abs] using hBn_bound
        have hCB0_nonneg : 0 ≤ CB0 := by
          dsimp [CB0]
          exact mul_nonneg hCη_nonneg hpow_nonneg
        exact sq_le_sq.mpr (by simpa [abs_of_nonneg hCB0_nonneg] using habs_bound)
      · have hfderiv_zero :
          (fderiv ℝ η x) (EuclideanSpace.single i 1) = 0 := by
          exact fderiv_apply_zero_outside_of_tsupport_subset
            (Ω := tsupport η) (hf := hη) (hsub := subset_rfl) hxη i
        simp [Bn, hfderiv_zero]
        nlinarith [sq_nonneg (CB0 : ℝ)]
    have hBn_int : Integrable (fun x => (Bn n i x) ^ 2) μ := by
      simpa [pow_two] using (hBn_memLp n i).integrable_sq
    calc
      ∫ x in Ω, (Bn n i x) ^ 2 ∂volume
          ≤ ∫ x in Ω, CB0 ^ 2 ∂volume := by
              exact integral_mono_ae hBn_int (by
                change IntegrableOn (fun _ : E => CB0 ^ 2) Ω volume
                exact
                  integrableOn_const (s := Ω)
                    ((measure_ball_lt_top (μ := volume) (x := (0 : E)) (r := s)).ne)) hBn_pt
      _ = ∫ x, (CB0 ^ 2 : ℝ) ∂μ := by
            simp [μ]
      _ = μ.real Set.univ * (CB0 ^ 2) := by
            rw [integral_const]
            simp [smul_eq_mul]
      _ = volume.real Ω * (CB0 ^ 2) := by
            rw [show μ = volume.restrict Ω by rfl]
            rw [MeasureTheory.measureReal_restrict_apply_univ]
      _ = (volume Ω).toReal * (CB0 ^ 2) := by
            rfl
      _ = CB0 ^ 2 * (volume Ω).toReal := by
            ring
  have hAsingSeq_sq_bound :
      ∀ n i,
        ∫ x in Ω, (AsingSeq n i x) ^ 2 ∂volume ≤
          2 * (CE * ∫ x in Ωρ, (2 : ℝ) ^ p * (1 + |max (u x) 0| ^ p) ∂volume) +
            2 * (CB0 ^ 2 * (volume Ω).toReal) := by
    intro n i
    have hpt :
        ∀ᵐ x ∂μ, (AsingSeq n i x) ^ 2 ≤
          2 * ‖(wfn n).weakGrad x‖ ^ 2 + 2 * (Bn n i x) ^ 2 := by
      filter_upwards with x
      have haux :
          (AsingSeq n i x) ^ 2 ≤
            2 * ((wfn n).weakGrad x i) ^ 2 + 2 * (Bn n i x) ^ 2 := by
        dsimp [AsingSeq, Gn]
        nlinarith [sq_nonneg ((wfn n).weakGrad x i + Bn n i x)]
      have hcoord_le :
          |(wfn n).weakGrad x i| ≤ ‖(wfn n).weakGrad x‖ := by
        have hcoord_le_raw :=
          PiLp.norm_apply_le ((wfn n).weakGrad x) i
        simpa [Real.norm_eq_abs] using hcoord_le_raw
      have hcoord_sq_le :
          ((wfn n).weakGrad x i) ^ 2 ≤ ‖(wfn n).weakGrad x‖ ^ 2 := by
        exact sq_le_sq.mpr (by
          have hnorm_nonneg : 0 ≤ ‖(wfn n).weakGrad x‖ := norm_nonneg _
          simpa [Real.norm_eq_abs, abs_of_nonneg hnorm_nonneg] using hcoord_le)
      calc
        (AsingSeq n i x) ^ 2 ≤ 2 * ((wfn n).weakGrad x i) ^ 2 + 2 * (Bn n i x) ^ 2 := haux
        _ ≤ 2 * ‖(wfn n).weakGrad x‖ ^ 2 + 2 * (Bn n i x) ^ 2 := by
            have htwice :
                2 * ((wfn n).weakGrad x i) ^ 2 ≤ 2 * ‖(wfn n).weakGrad x‖ ^ 2 := by
              exact mul_le_mul_of_nonneg_left hcoord_sq_le (by positivity)
            linarith
    have hintR :
        Integrable (fun x => 2 * ‖(wfn n).weakGrad x‖ ^ 2 + 2 * (Bn n i x) ^ 2) μ := by
      simpa [pow_two, μ] using
        ((wfn n).weakGrad_norm_memLp.integrable_sq.const_mul (2 : ℝ)).add
          ((hBn_memLp n i).integrable_sq.const_mul (2 : ℝ))
    have hintL : Integrable (fun x => (AsingSeq n i x) ^ 2) μ := by
      simpa [pow_two] using (hAsingSeq_memLp n i).integrable_sq
    calc
      ∫ x in Ω, (AsingSeq n i x) ^ 2 ∂volume
          = ∫ x, (AsingSeq n i x) ^ 2 ∂μ := by simp [μ]
      _ ≤ ∫ x, (2 * ‖(wfn n).weakGrad x‖ ^ 2 + 2 * (Bn n i x) ^ 2) ∂μ := by
            exact integral_mono_ae hintL hintR hpt
      _ = 2 * ∫ x in Ω, ‖(wfn n).weakGrad x‖ ^ 2 ∂volume +
            2 * ∫ x in Ω, (Bn n i x) ^ 2 ∂volume := by
            simp [μ, integral_add,
              ((wfn n).weakGrad_norm_memLp.integrable_sq.const_mul (2 : ℝ)),
              ((hBn_memLp n i).integrable_sq.const_mul (2 : ℝ)), integral_const_mul]
      _ ≤ 2 * (CE * ∫ x in Ωρ, (2 : ℝ) ^ p * (1 + |max (u x) 0| ^ p) ∂volume) +
            2 * (CB0 ^ 2 * (volume Ω).toReal) := by
            gcongr
            · exact hGn_energy n
            · exact hBn_sq_bound n i
  have hAsing_memLp :
      ∀ i : Fin d, MemLp (Asing i) 2 μ := by
    intro i
    by_cases hp_ge2 : 2 ≤ p
    · let KA : ℝ := 2 * ((p / 2) * (1 + N) ^ (p / 2 - 1))
      have hKA_memLp : MemLp (fun x => KA * |hwPos.weakGrad x i|) 2 μ := by
        simpa [KA, mul_assoc] using ((hwPos.weakGrad_component_memLp i).norm.const_mul KA)
      refine hKA_memLp.of_le (hAsing_aestrong i) ?_
      filter_upwards [hqual, hsublevelΩ] with x hxqual hsublevelx
      by_cases hxη : x ∈ tsupport η
      · by_cases hux : 0 < u x
        · have hboundx : max (u x) 0 < N := hxqual hxη
          have hpow_le :
              (max (u x) 0) ^ (p / 2 - 1) ≤ (1 + N) ^ (p / 2 - 1) := by
            exact Real.rpow_le_rpow (show 0 ≤ max (u x) 0 by exact le_max_right _ _)
              (by linarith) (by linarith)
          have hcoeff_nonneg :
              0 ≤ (p / 2) * (max (u x) 0) ^ (p / 2 - 1) := by
            exact mul_nonneg (by linarith) (Real.rpow_nonneg (le_max_right _ _) _)
          have hcoeff_le :
              ‖(p / 2) * (max (u x) 0) ^ (p / 2 - 1)‖ ≤
                (p / 2) * (1 + N) ^ (p / 2 - 1) := by
            rw [Real.norm_eq_abs, abs_of_nonneg hcoeff_nonneg]
            exact mul_le_mul_of_nonneg_left hpow_le (by linarith)
          have hη_abs_le : |η x| ≤ 1 := by
            simpa [abs_of_nonneg (hη_nonneg x)] using hη_bound x
          calc
            ‖Asing i x‖
                = |η x| * ‖(p / 2) * (max (u x) 0) ^ (p / 2 - 1)‖ * |hwPos.weakGrad x i| := by
                    simp [Asing, hux, norm_mul, Real.norm_eq_abs, mul_assoc]
            _ ≤ 1 * ((p / 2) * (1 + N) ^ (p / 2 - 1)) * |hwPos.weakGrad x i| := by
                have hmul :
                    |η x| * ‖(p / 2) * (max (u x) 0) ^ (p / 2 - 1)‖ ≤
                      1 * ((p / 2) * (1 + N) ^ (p / 2 - 1)) := by
                  exact mul_le_mul hη_abs_le hcoeff_le (by positivity) (by positivity : (0 : ℝ) ≤ 1)
                exact mul_le_mul_of_nonneg_right hmul (abs_nonneg _)
            _ ≤ KA * |hwPos.weakGrad x i| := by
                have hc_nonneg : 0 ≤ (p / 2) * (1 + N) ^ (p / 2 - 1) := by
                  exact mul_nonneg (by linarith)
                    (Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ 1 + N) _)
                have hgrad_nonneg : 0 ≤ |hwPos.weakGrad x i| := abs_nonneg _
                calc
                  1 * ((p / 2) * (1 + N) ^ (p / 2 - 1)) * |hwPos.weakGrad x i|
                      ≤ 2 * ((p / 2) * (1 + N) ^ (p / 2 - 1)) * |hwPos.weakGrad x i| := by
                        nlinarith
                  _ = KA * |hwPos.weakGrad x i| := by
                      dsimp [KA]
            _ = ‖KA * |hwPos.weakGrad x i|‖ := by
                have hKA_nonneg : 0 ≤ KA := by
                  dsimp [KA]
                  positivity
                rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hKA_nonneg (abs_nonneg _))]
        · have hunonpos : u x ≤ 0 := le_of_not_gt hux
          have hgrad_zero : hwPos.weakGrad x = 0 := hsublevelx hunonpos
          simp [Asing, hux, hgrad_zero, KA]
      · have hηx : η x = 0 := image_eq_zero_of_notMem_tsupport hxη
        have hKA_nonneg : 0 ≤ KA := by
          dsimp [KA]
          positivity
        have hgrad_nonneg : 0 ≤ |hwPos.weakGrad x i| := abs_nonneg _
        calc
          ‖Asing i x‖ = 0 := by simp [Asing, hηx]
          _ ≤ KA * |hwPos.weakGrad x i| := by
              exact mul_nonneg hKA_nonneg hgrad_nonneg
          _ = ‖KA * |hwPos.weakGrad x i|‖ := by
              rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hKA_nonneg hgrad_nonneg)]
    · have hp_lt2 : p < 2 := lt_of_not_ge hp_ge2
      have hFatou :
          ∫⁻ x, ENNReal.ofReal ((Asing i x) ^ 2) ∂μ ≤
            atTop.liminf (fun n => ∫⁻ x, ENNReal.ofReal ((AsingSeq n i x) ^ 2) ∂μ) := by
        have hmeas :
            ∀ n, AEMeasurable (fun x => ENNReal.ofReal ((AsingSeq n i x) ^ 2)) μ := by
          intro n
          exact (((hAsingSeq_memLp n i).aestronglyMeasurable.aemeasurable.pow_const 2).ennreal_ofReal)
        have hleft :=
          MeasureTheory.lintegral_liminf_le' (μ := μ) hmeas
        have hlim :
            (fun x =>
              Filter.liminf (fun n => ENNReal.ofReal ((AsingSeq n i x) ^ 2)) atTop) =ᵐ[μ]
              (fun x => ENNReal.ofReal ((Asing i x) ^ 2)) := by
          filter_upwards [hAsing_tendsto_ae i] with x hx
          have hsq :
              Tendsto (fun n => ENNReal.ofReal ((AsingSeq n i x) ^ 2)) atTop
                (nhds (ENNReal.ofReal ((Asing i x) ^ 2))) := by
            exact (ENNReal.continuous_ofReal.tendsto _
              |>.comp (((continuous_pow 2).tendsto (Asing i x)).comp hx))
          simp [hsq.liminf_eq]
        calc
          ∫⁻ x, ENNReal.ofReal ((Asing i x) ^ 2) ∂μ
              = ∫⁻ x, Filter.liminf (fun n => ENNReal.ofReal ((AsingSeq n i x) ^ 2)) atTop ∂μ := by
                  exact lintegral_congr_ae hlim.symm
          _ ≤ atTop.liminf (fun n => ∫⁻ x, ENNReal.ofReal ((AsingSeq n i x) ^ 2) ∂μ) := hleft
      have hBound_ne_top :
          atTop.liminf (fun n => ∫⁻ x, ENNReal.ofReal ((AsingSeq n i x) ^ 2) ∂μ) ≠ ⊤ := by
        apply ne_of_lt
        have htop :
            ENNReal.ofReal
              (2 * (CE * ∫ x in Ωρ, (2 : ℝ) ^ p * (1 + |max (u x) 0| ^ p) ∂volume) +
                2 * (CB0 ^ 2 * (volume Ω).toReal)) < ⊤ := by
          simp
        have hle :
            atTop.liminf (fun n => ∫⁻ x, ENNReal.ofReal ((AsingSeq n i x) ^ 2) ∂μ) ≤
              ENNReal.ofReal
                (2 * (CE * ∫ x in Ωρ, (2 : ℝ) ^ p * (1 + |max (u x) 0| ^ p) ∂volume) +
                  2 * (CB0 ^ 2 * (volume Ω).toReal)) := by
          refine Filter.liminf_le_of_frequently_le' (Frequently.of_forall fun n => ?_)
          have hEq :
              ∫⁻ x, ENNReal.ofReal ((AsingSeq n i x) ^ 2) ∂μ =
                ENNReal.ofReal (∫ x in Ω, (AsingSeq n i x) ^ 2 ∂volume) := by
            change
              ∫⁻ x, ENNReal.ofReal ((AsingSeq n i x) ^ 2) ∂μ =
                ENNReal.ofReal (∫ x, (AsingSeq n i x) ^ 2 ∂μ)
            exact
              (MeasureTheory.ofReal_integral_eq_lintegral_ofReal
                (μ := μ) (f := fun x => (AsingSeq n i x) ^ 2)
                ((hAsingSeq_memLp n i).integrable_sq)
                (ae_of_all _ fun _ => sq_nonneg _)).symm
          rw [hEq]
          exact ENNReal.ofReal_le_ofReal (hAsingSeq_sq_bound n i)
        exact lt_of_le_of_lt hle htop
      have hAsing_sq_int :
          Integrable (fun x => (Asing i x) ^ 2) μ := by
        have hlin_top :
            ∫⁻ x, ENNReal.ofReal ((Asing i x) ^ 2) ∂μ ≠ ⊤ := by
          exact ne_of_lt (lt_of_le_of_lt hFatou (lt_top_iff_ne_top.mpr hBound_ne_top))
        have hInt :=
          integrable_toReal_of_lintegral_ne_top
            (((hAsing_aestrong i).aemeasurable.pow_const 2).ennreal_ofReal) hlin_top
        simpa [ENNReal.toReal_ofReal, sq_nonneg] using hInt
      exact (memLp_two_iff_integrable_sq (hAsing_aestrong i)).2 hAsing_sq_int
  have hAsing_fun_memLp :
      ∀ n i, MemLp (fun x => AsingSeq n i x - Asing i x) 2 μ := by
    intro n i
    exact (hAsingSeq_memLp n i).sub (hAsing_memLp i)
  have hAsing_tendsto :
      ∀ i : Fin d,
        Tendsto (fun n => eLpNorm (fun x => AsingSeq n i x - Asing i x) 2 μ) atTop (nhds 0) := by
    intro i
    by_cases hp_ge2 : 2 ≤ p
    · let KA : ℝ := 2 * ((p / 2) * (1 + N) ^ (p / 2 - 1))
      have hKA_memLp : MemLp (fun x => KA * |hwPos.weakGrad x i|) 2 μ := by
        simpa [KA, mul_assoc] using ((hwPos.weakGrad_component_memLp i).norm.const_mul KA)
      have hdom :
          ∀ n, ∀ᵐ x ∂μ, |AsingSeq n i x - Asing i x| ≤ KA * |hwPos.weakGrad x i| := by
        intro n
        filter_upwards [hqual, hsublevelΩ] with x hxqual hsublevelx
        by_cases hxη : x ∈ tsupport η
        · by_cases hux : 0 < u x
          · have hboundx : max (u x) 0 < N := hxqual hxη
            have hsum_nonneg : 0 ≤ moserEpsSeq n + max (u x) 0 := by
              exact add_nonneg (moserEpsSeq_pos n).le (le_max_right _ _)
            have hsum_le : moserEpsSeq n + max (u x) 0 ≤ 1 + N := by
              have := moserEpsSeq_le_one n
              linarith
            have hderiv_nonneg :
                0 ≤ deriv (moserExactRegPow (moserEpsSeq n) N p) (max (u x) 0) := by
              rw [moserExactRegPow_deriv_eq_shifted (ε := moserEpsSeq n) (N := N) (p := p)
                (moserEpsSeq_pos n) (by simpa [max_eq_left hux.le] using hux) hboundx]
              exact mul_nonneg (by linarith) (Real.rpow_nonneg hsum_nonneg _)
            have hderiv_le :
                ‖deriv (moserExactRegPow (moserEpsSeq n) N p) (max (u x) 0)‖ ≤
                  (p / 2) * (1 + N) ^ (p / 2 - 1) := by
              rw [Real.norm_eq_abs, abs_of_nonneg hderiv_nonneg,
                moserExactRegPow_deriv_eq_shifted (ε := moserEpsSeq n) (N := N) (p := p)
                  (moserEpsSeq_pos n) (by simpa [max_eq_left hux.le] using hux) hboundx]
              exact mul_le_mul_of_nonneg_left
                (Real.rpow_le_rpow hsum_nonneg hsum_le (by linarith)) (by linarith)
            have hlimit_nonneg :
                0 ≤ (p / 2) * (max (u x) 0) ^ (p / 2 - 1) := by
              exact mul_nonneg (by linarith) (Real.rpow_nonneg (le_max_right _ _) _)
            have hlimit_le :
                ‖(p / 2) * (max (u x) 0) ^ (p / 2 - 1)‖ ≤
                  (p / 2) * (1 + N) ^ (p / 2 - 1) := by
              rw [Real.norm_eq_abs, abs_of_nonneg hlimit_nonneg]
              exact mul_le_mul_of_nonneg_left
                (Real.rpow_le_rpow (le_max_right _ _) (by linarith) (by linarith)) (by linarith)
            have hη_abs_le : |η x| ≤ 1 := by
              simpa [abs_of_nonneg (hη_nonneg x)] using hη_bound x
            have hseq_bound :
                ‖AsingSeq n i x‖ ≤ ((p / 2) * (1 + N) ^ (p / 2 - 1)) * |hwPos.weakGrad x i| := by
              rw [hAsingSeq_formula n i x]
              calc
                ‖η x * deriv (moserExactRegPow (moserEpsSeq n) N p) (max (u x) 0) *
                    hwPos.weakGrad x i‖
                    = |η x| *
                        ‖deriv (moserExactRegPow (moserEpsSeq n) N p) (max (u x) 0)‖ *
                        |hwPos.weakGrad x i| := by
                          simp [norm_mul, mul_assoc]
                _ ≤ 1 * ((p / 2) * (1 + N) ^ (p / 2 - 1)) * |hwPos.weakGrad x i| := by
                      have hmul :
                          |η x| *
                              ‖deriv (moserExactRegPow (moserEpsSeq n) N p) (max (u x) 0)‖ ≤
                            1 * ((p / 2) * (1 + N) ^ (p / 2 - 1)) := by
                        exact mul_le_mul hη_abs_le hderiv_le (by positivity)
                          (by positivity : (0 : ℝ) ≤ 1)
                      exact mul_le_mul_of_nonneg_right hmul (abs_nonneg _)
                _ = ((p / 2) * (1 + N) ^ (p / 2 - 1)) * |hwPos.weakGrad x i| := by ring
            have hsing_bound :
                ‖Asing i x‖ ≤ ((p / 2) * (1 + N) ^ (p / 2 - 1)) * |hwPos.weakGrad x i| := by
              calc
                ‖Asing i x‖
                    = |η x| * ‖(p / 2) * (max (u x) 0) ^ (p / 2 - 1)‖ *
                        |hwPos.weakGrad x i| := by
                          simp [Asing, hux, norm_mul, Real.norm_eq_abs, mul_assoc]
                _ ≤ 1 * ((p / 2) * (1 + N) ^ (p / 2 - 1)) * |hwPos.weakGrad x i| := by
                      have hmul :
                          |η x| * ‖(p / 2) * (max (u x) 0) ^ (p / 2 - 1)‖ ≤
                            1 * ((p / 2) * (1 + N) ^ (p / 2 - 1)) := by
                        exact mul_le_mul hη_abs_le hlimit_le (by positivity)
                          (by positivity : (0 : ℝ) ≤ 1)
                      exact mul_le_mul_of_nonneg_right hmul (abs_nonneg _)
                _ = ((p / 2) * (1 + N) ^ (p / 2 - 1)) * |hwPos.weakGrad x i| := by ring
            have hKA_nonneg : 0 ≤ KA := by
              dsimp [KA]
              positivity
            calc
              |AsingSeq n i x - Asing i x| ≤ ‖AsingSeq n i x‖ + ‖Asing i x‖ := by
                simpa [Real.norm_eq_abs] using norm_sub_le (AsingSeq n i x) (Asing i x)
              _ ≤ KA * |hwPos.weakGrad x i| := by
                  calc
                    ‖AsingSeq n i x‖ + ‖Asing i x‖
                        ≤ ((p / 2) * (1 + N) ^ (p / 2 - 1)) * |hwPos.weakGrad x i| +
                            ((p / 2) * (1 + N) ^ (p / 2 - 1)) * |hwPos.weakGrad x i| := by
                              exact add_le_add hseq_bound hsing_bound
                    _ = KA * |hwPos.weakGrad x i| := by
                        dsimp [KA]
                        ring
          · have hunonpos : u x ≤ 0 := le_of_not_gt hux
            have hgrad_zero : hwPos.weakGrad x = 0 := hsublevelx hunonpos
            have hEq : AsingSeq n i x = 0 := by
              rw [hAsingSeq_formula n i x, hgrad_zero]
              simp
            simp [hEq, Asing, hux, hgrad_zero, KA]
        · have hηx : η x = 0 := image_eq_zero_of_notMem_tsupport hxη
          have hEq : AsingSeq n i x = 0 := by
            rw [hAsingSeq_formula n i x, hηx]
            ring
          have hKA_nonneg : 0 ≤ KA := by
            dsimp [KA]
            positivity
          have hgrad_nonneg : 0 ≤ |hwPos.weakGrad x i| := abs_nonneg _
          simpa [hEq, Asing, hηx] using mul_nonneg hKA_nonneg hgrad_nonneg
      exact moser_tendsto_eLpNorm_zero_of_dominated hKA_memLp
        (fun n => (hAsing_fun_memLp n i).aestronglyMeasurable)
        hdom <| by
          filter_upwards [hAsing_tendsto_ae i] with x hx
          have hconst : Tendsto (fun _ : ℕ => Asing i x) atTop (nhds (Asing i x)) :=
            tendsto_const_nhds
          have hsub :
              Tendsto (fun n => AsingSeq n i x - Asing i x) atTop
                (nhds (Asing i x - Asing i x)) := hx.sub hconst
          simpa using hsub
    · have hp_lt2 : p < 2 := lt_of_not_ge hp_ge2
      have hAsing_norm_memLp : MemLp (fun x => ‖Asing i x‖) 2 μ := (hAsing_memLp i).norm
      have hdom :
          ∀ n, ∀ᵐ x ∂μ, |AsingSeq n i x - Asing i x| ≤ ‖Asing i x‖ := by
        intro n
        filter_upwards [hqual, hsublevelΩ] with x hxqual hsublevelx
        by_cases hxη : x ∈ tsupport η
        · by_cases hux : 0 < u x
          · have hboundx : max (u x) 0 < N := hxqual hxη
            have hcoeff_nonneg :
                0 ≤ (p / 2) * (max (u x) 0) ^ (p / 2 - 1) := by
              exact mul_nonneg (by linarith) (Real.rpow_nonneg (le_max_right _ _) _)
            have hderiv_nonneg :
                0 ≤ deriv (moserExactRegPow (moserEpsSeq n) N p) (max (u x) 0) := by
              have hsum_nonneg : 0 ≤ moserEpsSeq n + max (u x) 0 := by
                exact add_nonneg (moserEpsSeq_pos n).le (le_max_right _ _)
              rw [moserExactRegPow_deriv_eq_shifted (ε := moserEpsSeq n) (N := N) (p := p)
                (moserEpsSeq_pos n) (by simpa [max_eq_left hux.le] using hux) hboundx]
              exact mul_nonneg (by linarith) (Real.rpow_nonneg hsum_nonneg _)
            have hcoeff_le :
                deriv (moserExactRegPow (moserEpsSeq n) N p) (max (u x) 0) ≤
                  (p / 2) * (max (u x) 0) ^ (p / 2 - 1) := by
              rw [moserExactRegPow_deriv_eq_shifted (ε := moserEpsSeq n) (N := N) (p := p)
                (moserEpsSeq_pos n) (by simpa [max_eq_left hux.le] using hux) hboundx]
              exact mul_le_mul_of_nonneg_left
                (Real.rpow_le_rpow_of_nonpos
                  (by simpa [max_eq_left hux.le] using hux)
                  (by linarith [moserEpsSeq_pos n])
                  (by linarith [hp_lt2]))
                (by linarith)
            calc
              |AsingSeq n i x - Asing i x|
                  = |η x| *
                      |deriv (moserExactRegPow (moserEpsSeq n) N p) (max (u x) 0) -
                        ((p / 2) * (max (u x) 0) ^ (p / 2 - 1))| *
                      |hwPos.weakGrad x i| := by
                        have hAsing_eq :
                            Asing i x =
                              η x * ((p / 2) * (max (u x) 0) ^ (p / 2 - 1)) *
                                hwPos.weakGrad x i := by
                          simp [Asing, hux, mul_assoc]
                        rw [hAsingSeq_formula n i x, hAsing_eq]
                        have hfactor :
                            η x * deriv (moserExactRegPow (moserEpsSeq n) N p) (max (u x) 0) *
                                hwPos.weakGrad x i -
                              η x * ((p / 2) * (max (u x) 0) ^ (p / 2 - 1)) * hwPos.weakGrad x i =
                                η x *
                                  (deriv (moserExactRegPow (moserEpsSeq n) N p) (max (u x) 0) -
                                    ((p / 2) * (max (u x) 0) ^ (p / 2 - 1))) *
                                  hwPos.weakGrad x i := by
                          ring
                        rw [hfactor]
                        rw [abs_mul, abs_mul]
              _ = η x *
                    (((p / 2) * (max (u x) 0) ^ (p / 2 - 1)) -
                      deriv (moserExactRegPow (moserEpsSeq n) N p) (max (u x) 0)) *
                    |hwPos.weakGrad x i| := by
                      rw [abs_of_nonneg (hη_nonneg x), abs_of_nonpos (sub_nonpos.mpr hcoeff_le)]
                      ring
              _ ≤ η x * ((p / 2) * (max (u x) 0) ^ (p / 2 - 1)) * |hwPos.weakGrad x i| := by
                    have hηx_nonneg : 0 ≤ η x := hη_nonneg x
                    have hgrad_nonneg : 0 ≤ |hwPos.weakGrad x i| := abs_nonneg _
                    have hdiff_nonneg :
                        0 ≤
                          ((p / 2) * (max (u x) 0) ^ (p / 2 - 1)) -
                            deriv (moserExactRegPow (moserEpsSeq n) N p) (max (u x) 0) := by
                      linarith
                    have hdiff_le :
                        ((p / 2) * (max (u x) 0) ^ (p / 2 - 1)) -
                            deriv (moserExactRegPow (moserEpsSeq n) N p) (max (u x) 0) ≤
                          (p / 2) * (max (u x) 0) ^ (p / 2 - 1) := by
                      linarith
                    have hmul_le :
                        η x *
                            (((p / 2) * (max (u x) 0) ^ (p / 2 - 1)) -
                              deriv (moserExactRegPow (moserEpsSeq n) N p) (max (u x) 0)) ≤
                          η x * ((p / 2) * (max (u x) 0) ^ (p / 2 - 1)) := by
                      exact mul_le_mul_of_nonneg_left hdiff_le hηx_nonneg
                    exact mul_le_mul_of_nonneg_right hmul_le hgrad_nonneg
              _ = ‖Asing i x‖ := by
                    have hAsing_norm :
                        ‖Asing i x‖ =
                          η x * ((p / 2) * (max (u x) 0) ^ (p / 2 - 1)) *
                            |hwPos.weakGrad x i| := by
                      calc
                        ‖Asing i x‖ = |Asing i x| := by rw [Real.norm_eq_abs]
                        _ = |η x * ((p / 2) * (max (u x) 0) ^ (p / 2 - 1)) * hwPos.weakGrad x i| := by
                              simp [Asing, hux, mul_assoc]
                        _ = η x * ((p / 2) * (max (u x) 0) ^ (p / 2 - 1)) *
                              |hwPos.weakGrad x i| := by
                              rw [abs_mul, abs_mul, abs_of_nonneg (hη_nonneg x),
                                abs_of_nonneg hcoeff_nonneg]
                    rw [hAsing_norm]
          · have hunonpos : u x ≤ 0 := le_of_not_gt hux
            have hgrad_zero : hwPos.weakGrad x = 0 := hsublevelx hunonpos
            have hEq : AsingSeq n i x = 0 := by
              rw [hAsingSeq_formula n i x, hgrad_zero]
              simp
            simp [hEq, Asing, hux]
        · have hηx : η x = 0 := image_eq_zero_of_notMem_tsupport hxη
          have hEq : AsingSeq n i x = 0 := by
            rw [hAsingSeq_formula n i x, hηx]
            ring
          simp [hEq, Asing, hηx]
      exact moser_tendsto_eLpNorm_zero_of_dominated hAsing_norm_memLp
        (fun n => (hAsing_fun_memLp n i).aestronglyMeasurable)
        hdom <| by
          filter_upwards [hAsing_tendsto_ae i] with x hx
          have hconst : Tendsto (fun _ : ℕ => Asing i x) atTop (nhds (Asing i x)) :=
            tendsto_const_nhds
          simpa using hx.sub hconst
  let gComp : Fin d → E → ℝ := fun i x => Asing i x + B i x
  have hgComp_memLp :
      ∀ i : Fin d, MemLp (gComp i) 2 μ := by
    intro i
    simpa [gComp] using (hAsing_memLp i).add (hB_memLp i)
  have hGn_fun_memLp :
      ∀ n i, MemLp (fun x => Gn n i x - gComp i x) 2 μ := by
    intro n i
    simpa [Gn, gComp] using ((wfn n).weakGrad_component_memLp i).sub (hgComp_memLp i)
  have hGn_tendsto :
      ∀ i : Fin d,
        Tendsto (fun n => eLpNorm (fun x => Gn n i x - gComp i x) 2 μ) atTop (nhds 0) := by
    intro i
    let rhs : ℕ → ENNReal := fun n =>
      eLpNorm (fun x => AsingSeq n i x - Asing i x) 2 μ +
        eLpNorm (fun x => Bn n i x - B i x) 2 μ
    have hbound :
        ∀ n,
          eLpNorm (fun x => Gn n i x - gComp i x) 2 μ ≤ rhs n := by
      intro n
      have hEq :
          (fun x => Gn n i x - gComp i x) =
            (fun x => (AsingSeq n i x - Asing i x) + (Bn n i x - B i x)) := by
        ext x
        dsimp [Gn, AsingSeq, gComp]
        ring
      rw [hEq]
      simpa [rhs] using eLpNorm_add_le
        (hAsing_fun_memLp n i).aestronglyMeasurable
        (hBn_fun_memLp n i).aestronglyMeasurable (by norm_num)
    have hsum_tendsto :
        Tendsto rhs atTop (nhds 0) := by
      simpa [rhs] using (hAsing_tendsto i).add (hB_tendsto i)
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum_tendsto
      (fun _ => zero_le _) hbound
  have hWeakComp :
      ∀ i : Fin d, HasWeakPartialDeriv i (gComp i) f Ω := by
    intro i
    have hf_memLp' : MemLp f (ENNReal.ofReal (2 : ℝ)) (volume.restrict Ω) := by
      simpa [μ] using hf_memLp
    have hgComp_memLp' : MemLp (gComp i) (ENNReal.ofReal (2 : ℝ)) (volume.restrict Ω) := by
      simpa [μ] using hgComp_memLp i
    have hGn_isWeak : ∀ n, HasWeakPartialDeriv i (Gn n i) (fn n) Ω := by
      intro n
      simpa [Gn] using (wfn n).isWeakGrad i
    have hfn_fun_memLp' :
        ∀ n, MemLp (fun x => fn n x - f x) (ENNReal.ofReal (2 : ℝ)) (volume.restrict Ω) := by
      intro n
      simpa [μ] using hfn_fun_memLp n
    have hfn_tendsto' :
        Tendsto
          (fun n => eLpNorm (fun x => fn n x - f x) (ENNReal.ofReal (2 : ℝ)) (volume.restrict Ω))
          atTop (nhds 0) := by
      simpa [μ] using hfn_tendsto
    have hGn_fun_memLp' :
        ∀ n, MemLp (fun x => Gn n i x - gComp i x) (ENNReal.ofReal (2 : ℝ)) (volume.restrict Ω) := by
      intro n
      simpa [μ] using hGn_fun_memLp n i
    have hGn_tendsto' :
        Tendsto
          (fun n => eLpNorm (fun x => Gn n i x - gComp i x) (ENNReal.ofReal (2 : ℝ))
            (volume.restrict Ω))
          atTop (nhds 0) := by
      simpa [μ] using hGn_tendsto i
    refine HasWeakPartialDeriv.of_eLpNormApprox_p
      (d := d) (Ω := Ω) (p := 2) (hΩ := Metric.isOpen_ball) (hp := by norm_num)
      (i := i) (f := f) (g := gComp i) (ψ := fn) (gψ := fun n => Gn n i)
      hf_memLp' hgComp_memLp'
      hGn_isWeak
      hfn_fun_memLp' hfn_tendsto'
      hGn_fun_memLp' hGn_tendsto'
  let G : E → E := fun x => WithLp.toLp 2 fun i => gComp i x
  let hwv : MemW1pWitness 2 f Ω := {
    memLp := hf_memLp
    weakGrad := G
    weakGrad_component_memLp := by
      intro i
      simpa [G, gComp, PiLp.toLp_apply] using hgComp_memLp i
    isWeakGrad := by
      intro i
      simpa [G, gComp, PiLp.toLp_apply] using hWeakComp i }
  have hGn_comp_tendsto_ae :
      ∀ i : Fin d, ∀ᵐ x ∂μ, Tendsto (fun n => Gn n i x) atTop (nhds (gComp i x)) := by
    intro i
    filter_upwards [hAsing_tendsto_ae i, hB_tendsto_ae i] with x hA hB
    have hEq :
        (fun n => Gn n i x) = (fun n => AsingSeq n i x + Bn n i x) := by
      funext n
      dsimp [AsingSeq, Gn]
      ring
    rw [hEq]
    have hsum :
        Tendsto (fun n => AsingSeq n i x + Bn n i x) atTop
          (nhds (Asing i x + B i x)) := hA.add hB
    simpa [gComp] using hsum
  have hGn_vec_tendsto_ae :
      ∀ᵐ x ∂μ, Tendsto (fun n => (wfn n).weakGrad x) atTop (nhds (hwv.weakGrad x)) := by
    have hcoords :
        ∀ᵐ x ∂μ, ∀ i : Fin d, Tendsto (fun n => Gn n i x) atTop (nhds (gComp i x)) := by
      rw [ae_all_iff]
      intro i
      exact hGn_comp_tendsto_ae i
    filter_upwards [hcoords] with x hx
    have hpi :
        Tendsto (fun n : ℕ => fun i : Fin d => Gn n i x) atTop (nhds fun i : Fin d => gComp i x) := by
      rw [tendsto_pi_nhds]
      intro i
      exact hx i
    have htoLp :
        Tendsto (fun y : Fin d → ℝ => WithLp.toLp 2 y) (nhds fun i : Fin d => gComp i x)
          (nhds (WithLp.toLp 2 fun i : Fin d => gComp i x)) :=
      (PiLp.continuous_toLp 2 (fun _ : Fin d => ℝ)).tendsto (fun i : Fin d => gComp i x)
    simpa [G, hwv, Gn] using htoLp.comp hpi
  have hFatou :
      ∫⁻ x, ENNReal.ofReal (‖hwv.weakGrad x‖ ^ 2) ∂μ ≤
        atTop.liminf (fun n => ∫⁻ x, ENNReal.ofReal (‖(wfn n).weakGrad x‖ ^ 2) ∂μ) := by
    have hmeas :
        ∀ n, AEMeasurable (fun x => ENNReal.ofReal (‖(wfn n).weakGrad x‖ ^ 2)) μ := by
      intro n
      have hsq_meas :
          AEMeasurable (fun x => ‖(wfn n).weakGrad x‖ ^ 2) μ := by
        exact (wfn n).weakGrad_norm_memLp.aestronglyMeasurable.aemeasurable.pow_const 2
      exact hsq_meas.ennreal_ofReal
    have hleft := MeasureTheory.lintegral_liminf_le' (μ := μ) hmeas
    have hlim :
        (fun x =>
          Filter.liminf (fun n => ENNReal.ofReal (‖(wfn n).weakGrad x‖ ^ 2)) atTop) =ᵐ[μ]
            (fun x => ENNReal.ofReal (‖hwv.weakGrad x‖ ^ 2)) := by
      filter_upwards [hGn_vec_tendsto_ae] with x hx
      have hsq :
          Tendsto (fun n => ENNReal.ofReal (‖(wfn n).weakGrad x‖ ^ 2)) atTop
            (nhds (ENNReal.ofReal (‖hwv.weakGrad x‖ ^ 2))) := by
        exact ((ENNReal.continuous_ofReal.comp (continuous_norm.pow 2)).tendsto _).comp hx
      exact hsq.liminf_eq
    calc
      ∫⁻ x, ENNReal.ofReal (‖hwv.weakGrad x‖ ^ 2) ∂μ
          = ∫⁻ x, Filter.liminf (fun n => ENNReal.ofReal (‖(wfn n).weakGrad x‖ ^ 2)) atTop ∂μ := by
              exact lintegral_congr_ae hlim.symm
      _ ≤ atTop.liminf (fun n => ∫⁻ x, ENNReal.ofReal (‖(wfn n).weakGrad x‖ ^ 2) ∂μ) := hleft
  have hGn_energy_exact :
      ∀ n,
        ∫ x in Ω, ‖(wfn n).weakGrad x‖ ^ 2 ∂volume ≤
          CE * ∫ x in Ωρ, (moserEpsSeq n + |max (u x) 0|) ^ p ∂volume := by
    intro n
    have hmainρ :
        ∫ x in Ωρ, ‖(wfn n).weakGrad x‖ ^ 2 ∂volume ≤
          CE * ∫ x in Ωρ, (moserEpsSeq n + |max (u x) 0|) ^ p ∂volume := by
      simpa [CE, Ωρ, wfn, wfnBig, fn] using
        (moser_regularized_energy_bound (d := d) A (u := u) (η := η) (p := p) (ρ := ρ)
          (Cη := Cη) (ε := moserEpsSeq n) (N := N) hp hρ hρ1 (moserEpsSeq_pos n) hN
          hsub hu1 hη hη_nonneg hη_bound hη_grad_bound hη_sub_ρ hqualρ
          (hpIntρ_eps n))
    calc
      ∫ x in Ω, ‖(wfn n).weakGrad x‖ ^ 2 ∂volume
          = ∫ x in Ωρ, ‖(wfn n).weakGrad x‖ ^ 2 ∂volume := hGn_int_eq_ρ n
      _ ≤ CE * ∫ x in Ωρ, (moserEpsSeq n + |max (u x) 0|) ^ p ∂volume := hmainρ
  have hRhs_meas :
      ∀ n, AEStronglyMeasurable (fun x => (moserEpsSeq n + |max (u x) 0|) ^ p) μρ := by
    intro n
    exact (hpIntρ_eps n).aestronglyMeasurable
  have hRhs_dom :
      ∀ n, ∀ᵐ x ∂μρ,
        |(moserEpsSeq n + |max (u x) 0|) ^ p| ≤
          (2 : ℝ) ^ p * (1 + |max (u x) 0| ^ p) := by
    intro n
    filter_upwards with x
    have hbase_nonneg : 0 ≤ |max (u x) 0| := abs_nonneg _
    have hsum_nonneg : 0 ≤ moserEpsSeq n + |max (u x) 0| := by
      exact add_nonneg (moserEpsSeq_pos n).le hbase_nonneg
    calc
      |(moserEpsSeq n + |max (u x) 0|) ^ p|
          = (moserEpsSeq n + |max (u x) 0|) ^ p := by
              rw [abs_of_nonneg (Real.rpow_nonneg hsum_nonneg _)]
      _ ≤ (1 + |max (u x) 0|) ^ p := by
          exact Real.rpow_le_rpow hsum_nonneg (by linarith [moserEpsSeq_le_one n]) (by linarith)
      _ ≤ (2 : ℝ) ^ p * (1 + |max (u x) 0| ^ p) := by
          exact one_add_rpow_le_two_rpow_mul_one_add_rpow hbase_nonneg (by linarith)
  have hRhs_tendsto :
      Tendsto
        (fun n => ∫ x in Ωρ, (moserEpsSeq n + |max (u x) 0|) ^ p ∂volume)
        atTop
        (nhds (∫ x in Ωρ, |max (u x) 0| ^ p ∂volume)) := by
    have hpt :
        ∀ᵐ x ∂μρ,
          Tendsto (fun n => (moserEpsSeq n + |max (u x) 0|) ^ p) atTop
            (nhds (|max (u x) 0| ^ p)) := by
      filter_upwards with x
      have hp_nonneg : 0 ≤ p := by linarith
      simpa using
        (tendsto_moserEpsSeq.add tendsto_const_nhds).rpow_const (Or.inr hp_nonneg)
    exact MeasureTheory.tendsto_integral_of_dominated_convergence
      (fun x => (2 : ℝ) ^ p * (1 + |max (u x) 0| ^ p))
      hRhs_meas hRhsDom_int hRhs_dom hpt
  have hleft_eq :
      ∫⁻ x, ENNReal.ofReal (‖hwv.weakGrad x‖ ^ 2) ∂μ =
        ENNReal.ofReal (∫ x in Ω, ‖hwv.weakGrad x‖ ^ 2 ∂volume) := by
    change
      ∫⁻ x, ENNReal.ofReal (‖hwv.weakGrad x‖ ^ 2) ∂μ =
        ENNReal.ofReal (∫ x, ‖hwv.weakGrad x‖ ^ 2 ∂μ)
    exact
      (MeasureTheory.ofReal_integral_eq_lintegral_ofReal
        (μ := μ) (f := fun x => ‖hwv.weakGrad x‖ ^ 2)
        hwv.weakGrad_norm_memLp.integrable_sq
        (ae_of_all _ fun _ => sq_nonneg _)).symm
  have hright_eq :
      ∀ n,
        ∫⁻ x, ENNReal.ofReal (‖(wfn n).weakGrad x‖ ^ 2) ∂μ =
          ENNReal.ofReal (∫ x in Ω, ‖(wfn n).weakGrad x‖ ^ 2 ∂volume) := by
    intro n
    change
      ∫⁻ x, ENNReal.ofReal (‖(wfn n).weakGrad x‖ ^ 2) ∂μ =
        ENNReal.ofReal (∫ x, ‖(wfn n).weakGrad x‖ ^ 2 ∂μ)
    exact
      (MeasureTheory.ofReal_integral_eq_lintegral_ofReal
        (μ := μ) (f := fun x => ‖(wfn n).weakGrad x‖ ^ 2)
        (wfn n).weakGrad_norm_memLp.integrable_sq
        (ae_of_all _ fun _ => sq_nonneg _)).symm
  have hmain_enn :
      ENNReal.ofReal (∫ x in Ω, ‖hwv.weakGrad x‖ ^ 2 ∂volume) ≤
        ENNReal.ofReal (CE * ∫ x in Ωρ, |max (u x) 0| ^ p ∂volume) := by
    rw [← hleft_eq]
    refine le_trans hFatou ?_
    rw [Filter.liminf_congr (Eventually.of_forall hright_eq)]
    have hliminf_le :
        atTop.liminf (fun n => ENNReal.ofReal (∫ x in Ω, ‖(wfn n).weakGrad x‖ ^ 2 ∂volume)) ≤
          atTop.liminf
            (fun n =>
              ENNReal.ofReal
                (CE * ∫ x in Ωρ, (moserEpsSeq n + |max (u x) 0|) ^ p ∂volume)) := by
      refine Filter.liminf_le_liminf (Eventually.of_forall fun n => ?_) ?_ ?_
      · exact ENNReal.ofReal_le_ofReal (hGn_energy_exact n)
      · exact isBounded_ge_of_bot
      · exact isCobounded_ge_of_top
    exact hliminf_le.trans_eq
      (((ENNReal.continuous_ofReal.tendsto _).comp (Tendsto.const_mul CE hRhs_tendsto)).liminf_eq)
  have hpIntΩ : Integrable (fun x => |max (u x) 0| ^ p) μ := by
    simpa [μ, Ω] using hpInt
  have hρ_integral_le :
      ∫ x in Ωρ, |max (u x) 0| ^ p ∂volume ≤
        ∫ x in Ω, |max (u x) 0| ^ p ∂volume := by
    have hnonneg :
        0 ≤ᵐ[μ] fun x => |max (u x) 0| ^ p := by
      exact ae_of_all _ fun _ => Real.rpow_nonneg (abs_nonneg _) _
    simpa [μ, μρ, Ω, Ωρ] using
      (integral_mono_measure
        (μ := volume.restrict Ωρ) (ν := volume.restrict Ω)
        (f := fun x => |max (u x) 0| ^ p)
        (Measure.restrict_mono_set volume hΩρ_sub_Ω) hnonneg hpIntΩ)
  have hmain_real :
      ∫ x in Ω, ‖hwv.weakGrad x‖ ^ 2 ∂volume ≤
        CE * ∫ x in Ωρ, |max (u x) 0| ^ p ∂volume := by
    exact (ENNReal.ofReal_le_ofReal_iff (by
      have hnonneg :
          0 ≤ ∫ x in Ωρ, |max (u x) 0| ^ p ∂volume := by
        exact integral_nonneg fun _ => Real.rpow_nonneg (abs_nonneg _) _
      exact mul_nonneg hCE_nonneg hnonneg)).mp hmain_enn
  refine ⟨hwv, ?_⟩
  change
    ∫ x in Ω, ‖hwv.weakGrad x‖ ^ 2 ∂volume ≤
      2 * Cη ^ 2 * (A.1.Λ * (p / (p - 1)) ^ 2 + 1) *
        ∫ x in Ω, |max (u x) 0| ^ p ∂volume
  simpa [CE] using
    calc
      ∫ x in Ω, ‖hwv.weakGrad x‖ ^ 2 ∂volume
          ≤ CE * ∫ x in Ωρ, |max (u x) 0| ^ p ∂volume := hmain_real
      _ ≤ CE * ∫ x in Ω, |max (u x) 0| ^ p ∂volume := by
          exact mul_le_mul_of_nonneg_left hρ_integral_le hCE_nonneg
      _ = 2 * Cη ^ 2 * (A.1.Λ * (p / (p - 1)) ^ 2 + 1) *
            ∫ x in Ω, |max (u x) 0| ^ p ∂volume := by
              rfl


end DeGiorgi
