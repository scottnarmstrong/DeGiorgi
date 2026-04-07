import DeGiorgi.MoserIteration.Iteration

/-!
# Moser Linfty Closeout

This module contains the closeout from the iterated `L^{p_n}` bounds to the
final Chapter 06 `L^p -> L^\infty` theorem.
-/

noncomputable section

open MeasureTheory Filter

namespace DeGiorgi

variable {d : ℕ} [NeZero d]

local notation "E" => AmbientSpace d

/-- Auxiliary closeout: a uniform bound on the iterated `L^{p_n}` quantities gives
the a.e. half-ball `L∞` estimate. -/
theorem moserRadius_gt_half (n : ℕ) :
    (1 / 2 : ℝ) < moserRadius n := by
  rw [moserRadius]
  have hpow_pos : 0 < (1 / 2 : ℝ) ^ n := by positivity
  nlinarith

private theorem moserCloseoutExponent_tendsto_atTop
    (hd : 2 < (d : ℝ)) :
    Filter.Tendsto (fun n : ℕ => 2 * moserChi d ^ n) Filter.atTop Filter.atTop := by
  exact Filter.Tendsto.const_mul_atTop (by norm_num : 0 < (2 : ℝ))
    (tendsto_pow_atTop_atTop_of_one_lt (one_lt_moserChi (d := d) hd))

private theorem moserLinftyBoundPow_nonneg
    (A : NormalizedEllipticCoeff d (Metric.ball (0 : E) 1))
    {u : E → ℝ} {p₀ : ℝ} (hp₀ : 1 < p₀) :
    0 ≤ moserLinftyBoundPow (d := d) A (u := u) p₀ := by
  have hratio_nonneg : 0 ≤ p₀ / (p₀ - 1) := by
    have hp₀_pos : 0 < p₀ := by linarith
    have hp₀m1_pos : 0 < p₀ - 1 := by linarith
    exact div_nonneg hp₀_pos.le hp₀m1_pos.le
  have hint_nonneg :
      0 ≤ ∫ x in Metric.ball (0 : E) 1, |max (u x) 0| ^ p₀ ∂volume := by
    refine integral_nonneg ?_
    intro x
    positivity
  dsimp [moserLinftyBoundPow]
  refine mul_nonneg ?_ hint_nonneg
  refine mul_nonneg ?_ ?_
  · exact mul_nonneg
      (le_trans (by norm_num : (0 : ℝ) ≤ 1) (one_le_C_Moser (d := d)))
      (Real.rpow_nonneg A.1.Λ_nonneg _)
  · exact Real.rpow_nonneg hratio_nonneg _

private theorem moserLinftyMajorant_rpow_half
    (A : NormalizedEllipticCoeff d (Metric.ball (0 : E) 1))
    {u : E → ℝ} {p₀ : ℝ} (hp₀ : 1 < p₀) :
    moserLinftyMajorant (d := d) A (u := u) p₀ ^ (p₀ / 2) =
      moserLinftyBoundPow (d := d) A (u := u) p₀ ^ (1 / 2 : ℝ) := by
  have hp₀_ne : p₀ ≠ 0 := by linarith
  have hbound_nonneg :
      0 ≤ moserLinftyBoundPow (d := d) A (u := u) p₀ :=
    moserLinftyBoundPow_nonneg (d := d) A hp₀
  have hmul : (1 / p₀) * (p₀ / 2) = (1 / 2 : ℝ) := by
    field_simp [hp₀_ne]
  calc
    moserLinftyMajorant (d := d) A (u := u) p₀ ^ (p₀ / 2)
        = moserLinftyBoundPow (d := d) A (u := u) p₀ ^ ((1 / p₀) * (p₀ / 2)) := by
            rw [moserLinftyMajorant, Real.rpow_mul hbound_nonneg]
    _ = moserLinftyBoundPow (d := d) A (u := u) p₀ ^ (1 / 2 : ℝ) := by rw [hmul]

private theorem moser_closeout_superlevel_null
    (hd : 2 < (d : ℝ))
    (A : NormalizedEllipticCoeff d (Metric.ball (0 : E) 1))
    {u : E → ℝ} {p₀ : ℝ} (hp₀ : 1 < p₀)
    (hiter :
      ∀ n,
        IntegrableOn (fun x => |max (u x) 0| ^ moserExponentSeq d p₀ n)
          (Metric.ball (0 : E) (moserRadius n)) volume ∧
        moserIterNorm (d := d) (u := u) p₀ n ≤
          moserLinftyMajorant (d := d) A (u := u) p₀)
    {c : ℝ}
    (hc :
      moserLinftyBoundPow (d := d) A (u := u) p₀ ^ (1 / 2 : ℝ) < c) :
    (volume.restrict (Metric.ball (0 : E) (1 / 2 : ℝ))).real
      {x | c ≤ |max (u x) 0| ^ (p₀ / 2 : ℝ)} = 0 := by
  let Bhalf : Set E := Metric.ball (0 : E) (1 / 2 : ℝ)
  let μ : Measure E := volume.restrict Bhalf
  let f : E → ℝ := fun x => |max (u x) 0|
  let g : E → ℝ := fun x => f x ^ (p₀ / 2)
  let K : ℝ := moserLinftyBoundPow (d := d) A (u := u) p₀ ^ (1 / 2 : ℝ)
  let S : Set E := {x | c ≤ g x}
  haveI : IsFiniteMeasure μ := by
    dsimp [μ, Bhalf]
    rw [isFiniteMeasure_restrict]
    exact measure_ne_top_of_subset Metric.ball_subset_closedBall
      (isCompact_closedBall (0 : E) (1 / 2 : ℝ)).measure_lt_top.ne
  have hp₀_pos : 0 < p₀ := by linarith
  have hchi_pos : 0 < moserChi d := moserChi_pos (d := d) hd
  have hK_nonneg : 0 ≤ K := by
    dsimp [K]
    exact Real.rpow_nonneg (moserLinftyBoundPow_nonneg (d := d) A hp₀) _
  have hc_pos : 0 < c := by linarith
  have hratio_nonneg : 0 ≤ K / c := by positivity
  have hratio_lt_one : K / c < 1 := by
    exact (div_lt_one hc_pos).2 hc
  have hq_tendsto :
      Filter.Tendsto (fun n : ℕ => 2 * moserChi d ^ n) Filter.atTop Filter.atTop :=
    moserCloseoutExponent_tendsto_atTop (d := d) hd
  have hratio_tendsto :
      Filter.Tendsto (fun n : ℕ => (K / c) ^ (2 * moserChi d ^ n)) Filter.atTop (nhds 0) := by
    have hratio_gt_neg_one : -1 < K / c := by
      linarith
    exact (tendsto_rpow_atTop_of_base_lt_one (K / c) hratio_gt_neg_one hratio_lt_one).comp
      hq_tendsto
  have hmeasure_le :
      ∀ n : ℕ,
        μ.real S ≤ (K / c) ^ (2 * moserChi d ^ n) := by
    intro n
    let p_n : ℝ := moserExponentSeq d p₀ n
    let q_n : ℝ := 2 * moserChi d ^ n
    have hp_n_pos : 0 < p_n := by
      simpa [p_n] using moserExponentSeq_pos (d := d) hd hp₀_pos n
    have hq_n_nonneg : 0 ≤ q_n := by
      dsimp [q_n]
      positivity
    have hq_n_pos : 0 < q_n := by
      dsimp [q_n]
      positivity
    have hq_n_ge_two : 2 ≤ q_n := by
      dsimp [q_n]
      have hpow_ge : 1 ≤ moserChi d ^ n := by
        exact one_le_pow₀ (one_le_moserChi (d := d) hd)
      nlinarith
    have hBsub : Bhalf ⊆ Metric.ball (0 : E) (moserRadius n) := by
      exact Metric.ball_subset_ball (le_of_lt (moserRadius_gt_half n))
    have hf_nonneg : ∀ x, 0 ≤ f x := by
      intro x
      exact abs_nonneg (max (u x) 0)
    have hg_nonneg : ∀ x, 0 ≤ g x := by
      intro x
      dsimp [g]
      exact Real.rpow_nonneg (hf_nonneg x) _
    have hgq_eq :
        ∀ x, g x ^ q_n = f x ^ p_n := by
      intro x
      have hexp : (p₀ / 2) * q_n = p_n := by
        dsimp [q_n, p_n, moserExponentSeq]
        ring
      calc
        g x ^ q_n = f x ^ ((p₀ / 2) * q_n) := by
          dsimp [g]
          rw [← Real.rpow_mul (hf_nonneg x)]
        _ = f x ^ p_n := by rw [hexp]
    have hInt_half :
        IntegrableOn (fun x => g x ^ q_n) Bhalf volume := by
      have hInt_big :
          IntegrableOn (fun x => f x ^ p_n) Bhalf volume :=
        (hiter n).1.mono_set hBsub
      convert hInt_big using 1
      ext x
      exact hgq_eq x
    have hInt_mu : Integrable (fun x => g x ^ q_n) μ := by
      simpa [μ, Bhalf] using hInt_half
    have hnonneg_ae : 0 ≤ᵐ[μ] fun x => g x ^ q_n := by
      exact Filter.Eventually.of_forall fun x => Real.rpow_nonneg (hg_nonneg x) _
    have hmarkov :
        c ^ q_n * μ.real {x | c ^ q_n ≤ g x ^ q_n} ≤
          ∫ x, g x ^ q_n ∂μ := by
      simpa using
        (MeasureTheory.mul_meas_ge_le_integral_of_nonneg
          (μ := μ) hnonneg_ae hInt_mu (c ^ q_n))
    have hsubset :
        S ⊆ {x | c ^ q_n ≤ g x ^ q_n} := by
      intro x hx
      dsimp [S] at hx ⊢
      exact Real.rpow_le_rpow hc_pos.le hx hq_n_nonneg
    have hmain :
        c ^ q_n * μ.real S ≤ K ^ q_n := by
      have hmono :
          μ.real S ≤ μ.real {x | c ^ q_n ≤ g x ^ q_n} := by
        exact measureReal_mono hsubset (measure_ne_top μ _)
      calc
        c ^ q_n * μ.real S ≤ c ^ q_n * μ.real {x | c ^ q_n ≤ g x ^ q_n} := by
          exact mul_le_mul_of_nonneg_left hmono (by positivity)
        _ ≤ ∫ x, g x ^ q_n ∂μ := hmarkov
        _ ≤ K ^ q_n := by
          let Ihalf : ℝ := ∫ x, g x ^ q_n ∂μ
          let Ibig : ℝ := moserIterIntegral (d := d) (u := u) p₀ n
          have hIhalf_nonneg : 0 ≤ Ihalf := by
            dsimp [Ihalf]
            refine integral_nonneg ?_
            intro x
            exact Real.rpow_nonneg (hg_nonneg x) _
          have hIbig_nonneg : 0 ≤ Ibig := by
            dsimp [Ibig, moserIterIntegral]
            refine integral_nonneg ?_
            intro x
            positivity
          have hIhalf_eq :
              Ihalf = ∫ x in Bhalf, f x ^ p_n ∂volume := by
            dsimp [Ihalf, μ, Bhalf]
            congr with x
            exact hgq_eq x
          have hIhalf_le_big : Ihalf ≤ Ibig := by
            calc
              Ihalf = ∫ x in Bhalf, f x ^ p_n ∂volume := hIhalf_eq
              _ ≤ ∫ x in Metric.ball (0 : E) (moserRadius n), f x ^ p_n ∂volume := by
                  exact setIntegral_mono_set ((hiter n).1) (ae_of_all _ (by intro x; positivity))
                    (ae_of_all _ hBsub)
              _ = Ibig := by rfl
          have hroot_half_le :
              Ihalf ^ (1 / q_n) ≤ K := by
            have hroot_big_le :
                Ibig ^ (1 / q_n) ≤ K := by
              have hq_inv :
                  1 / q_n = (1 / p_n) * (p₀ / 2) := by
                dsimp [q_n, p_n, moserExponentSeq]
                field_simp [hp₀_pos.ne', pow_ne_zero n hchi_pos.ne']
              have hpow_le :
                  moserIterNorm (d := d) (u := u) p₀ n ^ (p₀ / 2) ≤
                    moserLinftyMajorant (d := d) A (u := u) p₀ ^ (p₀ / 2) := by
                exact Real.rpow_le_rpow
                  (by
                    dsimp [moserIterNorm]
                    exact Real.rpow_nonneg hIbig_nonneg _)
                  ((hiter n).2)
                  (by positivity)
              calc
                Ibig ^ (1 / q_n)
                    = moserIterNorm (d := d) (u := u) p₀ n ^ (p₀ / 2) := by
                        dsimp [Ibig, moserIterNorm]
                        rw [hq_inv, ← Real.rpow_mul hIbig_nonneg]
                _ ≤ moserLinftyMajorant (d := d) A (u := u) p₀ ^ (p₀ / 2) := hpow_le
                _ = K := by
                      dsimp [K]
                      exact moserLinftyMajorant_rpow_half (d := d) A hp₀
            calc
              Ihalf ^ (1 / q_n) ≤ Ibig ^ (1 / q_n) := by
                exact Real.rpow_le_rpow hIhalf_nonneg hIhalf_le_big (by positivity)
              _ ≤ K := hroot_big_le
          have hIhalf_le_K : Ihalf ≤ K ^ q_n := by
            have hIhalf_pow :
                (Ihalf ^ (1 / q_n)) ^ q_n = Ihalf := by
              calc
                (Ihalf ^ (1 / q_n)) ^ q_n = Ihalf ^ ((1 / q_n) * q_n) := by
                  rw [← Real.rpow_mul hIhalf_nonneg]
                _ = Ihalf ^ (1 : ℝ) := by
                  congr 2
                  field_simp [hq_n_pos.ne']
                _ = Ihalf := by rw [Real.rpow_one]
            calc
              Ihalf = (Ihalf ^ (1 / q_n)) ^ q_n := hIhalf_pow.symm
              _ ≤ K ^ q_n := by
                exact Real.rpow_le_rpow
                  (Real.rpow_nonneg hIhalf_nonneg _)
                  hroot_half_le hq_n_nonneg
          exact hIhalf_le_K
    have hcq_pos : 0 < c ^ q_n := by
      exact Real.rpow_pos_of_pos hc_pos q_n
    have hdiv :
        μ.real S ≤ K ^ q_n / c ^ q_n := by
      rw [le_div_iff₀ hcq_pos]
      simpa [mul_comm] using hmain
    simpa [q_n, p_n] using (show μ.real S ≤ (K / c) ^ q_n by
      rwa [← Real.div_rpow hK_nonneg hc_pos.le q_n] at hdiv)
  have hS_nonneg : 0 ≤ μ.real S := measureReal_nonneg
  by_contra hS_ne
  have hS_pos : 0 < μ.real S := lt_of_le_of_ne hS_nonneg (Ne.symm hS_ne)
  rw [Metric.tendsto_atTop] at hratio_tendsto
  obtain ⟨N, hN⟩ := hratio_tendsto (μ.real S / 2) (by linarith)
  have hYN_nonneg : 0 ≤ (K / c) ^ (2 * moserChi d ^ N) := by
    exact hS_nonneg.trans (hmeasure_le N)
  have hYN_lt : (K / c) ^ (2 * moserChi d ^ N) < μ.real S / 2 := by
    have hdist := hN N le_rfl
    rwa [Real.dist_eq, sub_zero, abs_of_nonneg hYN_nonneg] at hdist
  linarith [hmeasure_le N]

private theorem moser_ae_closeout
    (hd : 2 < (d : ℝ))
    (A : NormalizedEllipticCoeff d (Metric.ball (0 : E) 1))
    {u : E → ℝ} {p₀ : ℝ} (hp₀ : 1 < p₀)
    (hiter :
      ∀ n,
        IntegrableOn (fun x => |max (u x) 0| ^ moserExponentSeq d p₀ n)
          (Metric.ball (0 : E) (moserRadius n)) volume ∧
        moserIterNorm (d := d) (u := u) p₀ n ≤
          moserLinftyMajorant (d := d) A (u := u) p₀) :
    ∀ᵐ x ∂(volume.restrict (Metric.ball (0 : E) (1 / 2 : ℝ))),
      |max (u x) 0| ^ p₀ ≤ moserLinftyBoundPow (d := d) A (u := u) p₀ := by
  let Bhalf : Set E := Metric.ball (0 : E) (1 / 2 : ℝ)
  let μ : Measure E := volume.restrict Bhalf
  let f : E → ℝ := fun x => |max (u x) 0|
  let g : E → ℝ := fun x => f x ^ (p₀ / 2)
  let K : ℝ := moserLinftyBoundPow (d := d) A (u := u) p₀ ^ (1 / 2 : ℝ)
  haveI : IsFiniteMeasure μ := by
    dsimp [μ, Bhalf]
    rw [isFiniteMeasure_restrict]
    exact measure_ne_top_of_subset Metric.ball_subset_closedBall
      (isCompact_closedBall (0 : E) (1 / 2 : ℝ)).measure_lt_top.ne
  have hK_nonneg : 0 ≤ K := by
    dsimp [K]
    exact Real.rpow_nonneg (moserLinftyBoundPow_nonneg (d := d) A hp₀) _
  have hbound_all :
      ∀ m : ℕ, ∀ᵐ x ∂μ, g x < K + 1 / (m + 1 : ℝ) := by
    intro m
    have hzero :
        μ.real {x | K + 1 / (m + 1 : ℝ) ≤ g x} = 0 := by
      refine moser_closeout_superlevel_null (d := d) hd A (u := u) hp₀ hiter ?_
      dsimp [K]
      have hfrac_pos : 0 < 1 / (m + 1 : ℝ) := by positivity
      linarith
    rw [ae_iff]
    simpa [μ, Bhalf, g, K, not_lt] using
      (measureReal_eq_zero_iff
        (μ := μ) (s := {x | K + 1 / (m + 1 : ℝ) ≤ g x})
        (measure_ne_top μ {x | K + 1 / (m + 1 : ℝ) ≤ g x})).1 hzero
  have hbound_ae :
      ∀ᵐ x ∂μ, ∀ m : ℕ, g x < K + 1 / (m + 1 : ℝ) := by
    exact ae_all_iff.2 hbound_all
  filter_upwards [hbound_ae] with x hx
  have hfx_nonneg : 0 ≤ f x := by
    dsimp [f]
    exact abs_nonneg (max (u x) 0)
  have hgx_nonneg : 0 ≤ g x := by
    dsimp [g]
    exact Real.rpow_nonneg hfx_nonneg _
  have hgx_le : g x ≤ K := by
    by_contra hgx_gt
    have hgap_pos : 0 < g x - K := by linarith
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt hgap_pos
    have hlt : K + 1 / (m + 1 : ℝ) < g x := by linarith
    linarith [hx m]
  have hgpow :
      g x ^ (2 : ℝ) ≤ K ^ (2 : ℝ) := by
    exact Real.rpow_le_rpow hgx_nonneg hgx_le (by norm_num)
  have hg_sq_eq : g x ^ (2 : ℝ) = f x ^ p₀ := by
    calc
      g x ^ (2 : ℝ) = (f x ^ (p₀ / 2)) ^ (2 : ℝ) := by rfl
      _ = f x ^ ((p₀ / 2) * 2) := by rw [← Real.rpow_mul hfx_nonneg]
      _ = f x ^ p₀ := by
            congr 2
            ring
  have hK_sq_eq :
      K ^ (2 : ℝ) = moserLinftyBoundPow (d := d) A (u := u) p₀ := by
    calc
      K ^ (2 : ℝ)
          = moserLinftyBoundPow (d := d) A (u := u) p₀ ^ ((1 / 2 : ℝ) * 2) := by
              dsimp [K]
              rw [← Real.rpow_mul (moserLinftyBoundPow_nonneg (d := d) A hp₀)]
      _ = moserLinftyBoundPow (d := d) A (u := u) p₀ := by
            rw [show ((1 / 2 : ℝ) * 2) = (1 : ℝ) by ring, Real.rpow_one]
  calc
    |max (u x) 0| ^ p₀ = f x ^ p₀ := by rfl
    _ = g x ^ (2 : ℝ) := hg_sq_eq.symm
    _ ≤ K ^ (2 : ℝ) := hgpow
    _ = moserLinftyBoundPow (d := d) A (u := u) p₀ := hK_sq_eq

/-- Moser `L^p → L∞` estimate for subsolutions on the unit ball, in the honest
essential/a.e. form available before the continuity upgrade.

This is the normalized-coefficient unit-ball form of the Moser local maximum
estimate. -/
theorem linfty_subsolution_Moser
    (hd : 2 < (d : ℝ))
    (A : NormalizedEllipticCoeff d (Metric.ball (0 : E) 1))
    {u : E → ℝ} {p₀ : ℝ} (hp₀ : 1 < p₀)
    (hsub : IsSubsolution A.1 u)
    (hposInt :
      IntegrableOn (fun x => |max (u x) 0| ^ p₀)
        (Metric.ball (0 : E) 1) volume) :
    ∀ᵐ x ∂(volume.restrict (Metric.ball (0 : E) (1 / 2 : ℝ))),
      |max (u x) 0| ^ p₀ ≤
      C_Moser d * A.1.Λ ^ ((d : ℝ) / 2) *
        (p₀ / (p₀ - 1)) ^ (d : ℝ) *
        ∫ x in Metric.ball (0 : E) 1, |max (u x) 0| ^ p₀ ∂volume := by
  have hiter_raw :=
    moser_iteration_bound (d := d) hd A (u := u) hp₀ hsub hposInt
  have hiter :
      ∀ n,
        IntegrableOn (fun x => |max (u x) 0| ^ moserExponentSeq d p₀ n)
          (Metric.ball (0 : E) (moserRadius n)) volume ∧
        moserIterNorm (d := d) (u := u) p₀ n ≤
          moserLinftyMajorant (d := d) A (u := u) p₀ := by
    intro n
    rcases hiter_raw n with ⟨hInt_n, hbound_n⟩
    exact ⟨hInt_n, hbound_n.trans (moser_geometric_majorant (d := d) hd A hp₀ n)⟩
  simpa [moserLinftyBoundPow] using
    moser_ae_closeout (d := d) hd A (u := u) hp₀ hiter

/-- The `p = 2` anchor for Chapter 06 is already available from Chapter 05.

This is the exact normalized De Giorgi unit-ball estimate rewritten in the
Chapter 06 a.e. power-bound format. It is the base case that the later Moser
iteration should strictly improve from `p = 2` to arbitrary `p > 1`. -/
theorem linfty_subsolution_Moser_two
    (hd : 2 < (d : ℝ))
    (A : NormalizedEllipticCoeff d (Metric.ball (0 : E) 1))
    {u : E → ℝ}
    (hsub : IsSubsolution A.1 u)
    (hposInt :
      IntegrableOn (fun x => |max (u x) 0| ^ 2)
        (Metric.ball (0 : E) 1) volume) :
    ∀ᵐ x ∂(volume.restrict (Metric.ball (0 : E) (1 / 2 : ℝ))),
      |max (u x) 0| ^ 2 ≤
        C_Moser d * A.1.Λ ^ ((d : ℝ) / 2) *
          (2 / (2 - 1 : ℝ)) ^ (d : ℝ) *
          ∫ x in Metric.ball (0 : E) 1, |max (u x) 0| ^ 2 ∂volume := by
  let I₂ : ℝ := ∫ x in Metric.ball (0 : E) 1, |max (u x) 0| ^ 2 ∂volume
  let c : ℝ := C_DeGiorgi_subsolution_normalized d * A.1.Λ ^ ((d : ℝ) / 4)
  have hI₂_nonneg : 0 ≤ I₂ := by
    dsimp [I₂]
    refine integral_nonneg ?_
    intro x
    positivity
  have hc_nonneg : 0 ≤ c := by
    have hCDG_nonneg : 0 ≤ C_DeGiorgi_subsolution_normalized d := by
      dsimp [C_DeGiorgi_subsolution_normalized]
      exact
        (C_DeGiorgiSmallness_pos (d := d)
          (K_DeGiorgi_subsolution_normalized_pos (d := d))).le
    dsimp [c]
    exact mul_nonneg
      hCDG_nonneg
      (Real.rpow_nonneg A.1.Λ_nonneg _)
  filter_upwards
    [linfty_subsolution_DeGiorgi_normalized (d := d) hd A hsub hposInt]
    with x hx
  have hx_nonneg : 0 ≤ max (u x) 0 := by
    positivity
  have hsq :
      |max (u x) 0| ^ 2 ≤ c ^ 2 * I₂ := by
    have hx' : max (u x) 0 ≤ c * Real.sqrt I₂ := hx
    have hrhs_nonneg : 0 ≤ c * Real.sqrt I₂ := by
      exact mul_nonneg hc_nonneg (Real.sqrt_nonneg I₂)
    have hsq' : (max (u x) 0) ^ 2 ≤ (c * Real.sqrt I₂) ^ 2 := by
      nlinarith
    calc
      |max (u x) 0| ^ 2 = (max (u x) 0) ^ 2 := by
        rw [abs_of_nonneg hx_nonneg]
      _ ≤ (c * Real.sqrt I₂) ^ 2 := hsq'
      _ = c ^ 2 * I₂ := by
        rw [mul_pow, Real.sq_sqrt hI₂_nonneg]
  have hconst :
      c ^ 2 * I₂ ≤
        C_Moser d * A.1.Λ ^ ((d : ℝ) / 2) *
          (2 / (2 - 1 : ℝ)) ^ (d : ℝ) * I₂ := by
    have hbase :
        c ^ 2 ≤
          C_Moser d * A.1.Λ ^ ((d : ℝ) / 2) *
            (2 / (2 - 1 : ℝ)) ^ (d : ℝ) := by
      have hpow :
          (A.1.Λ ^ ((d : ℝ) / 4)) ^ 2 = A.1.Λ ^ ((d : ℝ) / 2) := by
        rw [pow_two, ← Real.rpow_add A.1.Λ_pos]
        ring_nf
      calc
        c ^ 2
            = (C_DeGiorgi_subsolution_normalized d) ^ 2 *
                A.1.Λ ^ ((d : ℝ) / 2) := by
                  dsimp [c]
                  rw [mul_pow, hpow]
        _ ≤ C_Moser d * A.1.Λ ^ ((d : ℝ) / 2) := by
            exact mul_le_mul_of_nonneg_right
              (C_DeGiorgi_subsolution_normalized_sq_le_C_Moser (d := d))
              (Real.rpow_nonneg A.1.Λ_nonneg _)
        _ ≤ C_Moser d * A.1.Λ ^ ((d : ℝ) / 2) *
              (2 / (2 - 1 : ℝ)) ^ (d : ℝ) := by
            have hleft_nonneg : 0 ≤ C_Moser d * A.1.Λ ^ ((d : ℝ) / 2) := by
              exact mul_nonneg
                (le_trans (by norm_num : (0 : ℝ) ≤ 1) (one_le_C_Moser (d := d)))
                (Real.rpow_nonneg A.1.Λ_nonneg _)
            have hone : (1 : ℝ) ≤ (2 / (2 - 1 : ℝ)) ^ (d : ℝ) := by
              have hbase : (1 : ℝ) ≤ 2 / (2 - 1 : ℝ) := by norm_num
              have hd_nonneg : 0 ≤ (d : ℝ) := by exact_mod_cast Nat.zero_le d
              exact Real.one_le_rpow hbase hd_nonneg
            simpa [mul_assoc] using
              (mul_le_mul_of_nonneg_left hone hleft_nonneg)
    exact mul_le_mul_of_nonneg_right hbase hI₂_nonneg
  exact le_trans hsq (by
    simpa [I₂] using hconst)

-- The supersolution iteration stages (weak_harnack_stage_one_inverse,
-- weak_harnack_stage_one_forward) have been split out to
-- Supersolutions.lean for independent development.
--
-- The weak Harnack inequality (weak_harnack) and the sharp Moser estimate
-- (linfty_subsolution_Moser_sharp) have been split out to

end DeGiorgi
