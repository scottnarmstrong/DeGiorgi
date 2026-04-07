import DeGiorgi.DeGiorgiIteration.Recurrence

/-!
# De Giorgi Iteration: Linfty Assembly

This module contains the final De Giorgi iteration assembly, from the
canonical energy sequence to the Linfty endpoint theorems.
-/

noncomputable section

open MeasureTheory Metric Filter Topology Set Function Matrix
open scoped ENNReal NNReal

namespace DeGiorgi

section LinftyAssembly

variable {d : ℕ} [NeZero d]

local notation "E" => AmbientSpace d

/-- Canonical De Giorgi energy sequence on nested balls and levels. -/
noncomputable def deGiorgiEnergySeq
    (u : E → ℝ) (x₀ : E) (lamStar : ℝ) (n : ℕ) : ℝ :=
  ∫ x in Metric.ball x₀ (deGiorgiRadius n), |positivePartSub u (deGiorgiLevel lamStar n) x| ^ 2 ∂volume

lemma deGiorgiTail_lt_one (n : ℕ) : deGiorgiTail n < 1 := by
  dsimp [deGiorgiTail]
  exact pow_lt_one₀ (by norm_num : 0 ≤ (1 / 2 : ℝ))
    (by norm_num : (1 / 2 : ℝ) < 1) (Nat.succ_ne_zero n)

lemma deGiorgiRadius_gt_half (n : ℕ) : (1 / 2 : ℝ) < deGiorgiRadius n := by
  have htail_pos : 0 < deGiorgiTail n := deGiorgiTail_pos n
  dsimp [deGiorgiRadius]
  linarith

lemma deGiorgiRadius_lt_one (n : ℕ) : deGiorgiRadius n < 1 := by
  have htail_lt : deGiorgiTail n < 1 := deGiorgiTail_lt_one n
  dsimp [deGiorgiRadius]
  linarith

lemma deGiorgiLevel_lt {lamStar : ℝ} (hLamStar : 0 < lamStar) (n : ℕ) :
    deGiorgiLevel lamStar n < lamStar := by
  have htail_pos : 0 < deGiorgiTail n := deGiorgiTail_pos n
  have hone_sub_lt : 1 - deGiorgiTail n < 1 := sub_lt_self _ htail_pos
  have hmul_lt : lamStar * (1 - deGiorgiTail n) < lamStar * 1 := by
    exact mul_lt_mul_of_pos_left hone_sub_lt hLamStar
  simpa [deGiorgiLevel] using hmul_lt

omit [NeZero d] in
lemma positivePartSub_antitone
    {u : E → ℝ} {k₁ k₂ : ℝ} (hk : k₁ ≤ k₂) (x : E) :
    positivePartSub u k₂ x ≤ positivePartSub u k₁ x := by
  dsimp [positivePartSub]
  exact max_le_max (by linarith) le_rfl

omit [NeZero d] in
lemma positivePartSub_le_posPartZero
    {u : E → ℝ} {k : ℝ} (hk : 0 ≤ k) (x : E) :
    positivePartSub u k x ≤ max (u x) 0 := by
  simpa [positivePartSub] using positivePartSub_antitone (u := u) hk x

omit [NeZero d] in
lemma le_of_positivePartSub_eq_zero
    {u : E → ℝ} {k : ℝ} {x : E}
    (hzero : positivePartSub u k x = 0) :
    u x ≤ k := by
  by_cases hux : 0 ≤ u x - k
  · have hsub : u x - k = 0 := by
      simpa [positivePartSub, max_eq_left hux] using hzero
    linarith
  · linarith

omit [NeZero d] in
theorem ae_eq_zero_of_forall_setIntegral_sq_le_of_tendsto_zero
    {f : E → ℝ} {s : Set E} {Y : ℕ → ℝ}
    (hfi : IntegrableOn (fun x => |f x| ^ 2) s volume)
    (hbound : ∀ n, ∫ x in s, |f x| ^ 2 ∂volume ≤ Y n)
    (hY_tendsto : Tendsto Y atTop (nhds 0)) :
    ∀ᵐ x ∂(volume.restrict s), f x = 0 := by
  let I : ℝ := ∫ x in s, |f x| ^ 2 ∂volume
  have hI_nonneg : 0 ≤ I := by
    dsimp [I]
    refine integral_nonneg ?_
    intro x
    positivity
  have hI_zero : I = 0 := by
    by_contra hI_ne
    have hI_pos : 0 < I := lt_of_le_of_ne hI_nonneg (Ne.symm hI_ne)
    rw [Metric.tendsto_atTop] at hY_tendsto
    obtain ⟨N, hN⟩ := hY_tendsto (I / 2) (by linarith)
    have hYN_nonneg : 0 ≤ Y N := hI_nonneg.trans (hbound N)
    have hYN_lt : Y N < I / 2 := by
      have hdist := hN N le_rfl
      rwa [Real.dist_eq, sub_zero, abs_of_nonneg hYN_nonneg] at hdist
    linarith [hbound N]
  have hsq_zero :
      (fun x => |f x| ^ 2) =ᵐ[volume.restrict s] 0 := by
    refine (integral_eq_zero_iff_of_nonneg_ae
      (Filter.Eventually.of_forall (fun x => by positivity)) hfi).1 ?_
    simpa [I] using hI_zero
  filter_upwards [hsq_zero] with x hx
  have habs_zero : |f x| = 0 := by
    exact sq_eq_zero_iff.mp hx
  exact abs_eq_zero.mp habs_zero

omit [NeZero d] in
theorem integral_sq_halfBall_le_deGiorgiEnergySeq
    {u : E → ℝ} {x₀ : E} {lamStar : ℝ}
    (hLamStar : 0 < lamStar)
    (hStarInt :
      IntegrableOn (fun x => |positivePartSub u lamStar x| ^ 2)
        (Metric.ball x₀ (1 / 2 : ℝ)) volume)
    (hAint :
      ∀ n,
        IntegrableOn (fun x => |positivePartSub u (deGiorgiLevel lamStar n) x| ^ 2)
          (Metric.ball x₀ (deGiorgiRadius n)) volume) :
    ∀ n,
      ∫ x in Metric.ball x₀ (1 / 2 : ℝ), |positivePartSub u lamStar x| ^ 2 ∂volume ≤
        deGiorgiEnergySeq u x₀ lamStar n := by
  intro n
  have hs : Metric.ball x₀ (1 / 2 : ℝ) ⊆ Metric.ball x₀ (deGiorgiRadius n) := by
    exact Metric.ball_subset_ball (le_of_lt (deGiorgiRadius_gt_half n))
  have hbig_int_half :
      IntegrableOn (fun x => |positivePartSub u (deGiorgiLevel lamStar n) x| ^ 2)
        (Metric.ball x₀ (1 / 2 : ℝ)) volume :=
    (hAint n).mono_set hs
  have hpointwise :
      ∀ x ∈ Metric.ball x₀ (1 / 2 : ℝ),
        |positivePartSub u lamStar x| ^ 2 ≤
          |positivePartSub u (deGiorgiLevel lamStar n) x| ^ 2 := by
    intro x hx
    have hmono :
        positivePartSub u lamStar x ≤ positivePartSub u (deGiorgiLevel lamStar n) x := by
      exact positivePartSub_antitone (show deGiorgiLevel lamStar n ≤ lamStar by
        linarith [deGiorgiLevel_lt hLamStar n]) x
    have hsmall_nonneg : 0 ≤ positivePartSub u lamStar x := positivePartSub_nonneg
    have hbig_nonneg : 0 ≤ positivePartSub u (deGiorgiLevel lamStar n) x :=
      positivePartSub_nonneg
    have hsq :
        (positivePartSub u lamStar x) ^ 2 ≤
          (positivePartSub u (deGiorgiLevel lamStar n) x) ^ 2 := by
      nlinarith
    simpa [abs_of_nonneg hsmall_nonneg, abs_of_nonneg hbig_nonneg] using hsq
  have hmono_same_set :
      ∫ x in Metric.ball x₀ (1 / 2 : ℝ), |positivePartSub u lamStar x| ^ 2 ∂volume ≤
        ∫ x in Metric.ball x₀ (1 / 2 : ℝ),
          |positivePartSub u (deGiorgiLevel lamStar n) x| ^ 2 ∂volume := by
    refine integral_mono_ae hStarInt hbig_int_half ?_
    refine (ae_restrict_iff' (μ := volume) isOpen_ball.measurableSet).2 ?_
    filter_upwards with x hx
    exact hpointwise x hx
  have hnonneg :
      ∀ x, 0 ≤ |positivePartSub u (deGiorgiLevel lamStar n) x| ^ 2 := by
    intro x
    positivity
  have hmono_set :
      ∫ x in Metric.ball x₀ (1 / 2 : ℝ),
          |positivePartSub u (deGiorgiLevel lamStar n) x| ^ 2 ∂volume ≤
        ∫ x in Metric.ball x₀ (deGiorgiRadius n),
          |positivePartSub u (deGiorgiLevel lamStar n) x| ^ 2 ∂volume := by
    exact setIntegral_mono_set (hAint n) (ae_of_all _ hnonneg) (ae_of_all _ hs)
  calc
    ∫ x in Metric.ball x₀ (1 / 2 : ℝ), |positivePartSub u lamStar x| ^ 2 ∂volume
        ≤ ∫ x in Metric.ball x₀ (1 / 2 : ℝ),
            |positivePartSub u (deGiorgiLevel lamStar n) x| ^ 2 ∂volume := hmono_same_set
    _ ≤ ∫ x in Metric.ball x₀ (deGiorgiRadius n),
          |positivePartSub u (deGiorgiLevel lamStar n) x| ^ 2 ∂volume := hmono_set
    _ = deGiorgiEnergySeq u x₀ lamStar n := by
          simp [deGiorgiEnergySeq]

omit [NeZero d] in
theorem deGiorgiEnergySeq_zero_le_integral_sq_posPartZero_on_unitBall
    {u : E → ℝ} {x₀ : E} {lamStar : ℝ}
    (hLamStar : 0 < lamStar)
    (hA0Int :
      IntegrableOn (fun x => |positivePartSub u (deGiorgiLevel lamStar 0) x| ^ 2)
        (Metric.ball x₀ (deGiorgiRadius 0)) volume)
    (hposInt :
      IntegrableOn (fun x => |max (u x) 0| ^ 2)
        (Metric.ball x₀ 1) volume) :
    deGiorgiEnergySeq u x₀ lamStar 0 ≤
      ∫ x in Metric.ball x₀ 1, |max (u x) 0| ^ 2 ∂volume := by
  have hs : Metric.ball x₀ (deGiorgiRadius 0) ⊆ Metric.ball x₀ 1 := by
    exact Metric.ball_subset_ball (le_of_lt (deGiorgiRadius_lt_one 0))
  have hlev_nonneg : 0 ≤ deGiorgiLevel lamStar 0 := by
    dsimp [deGiorgiLevel, deGiorgiTail]
    nlinarith
  have hpointwise :
      ∀ x ∈ Metric.ball x₀ (deGiorgiRadius 0),
        |positivePartSub u (deGiorgiLevel lamStar 0) x| ^ 2 ≤ |max (u x) 0| ^ 2 := by
    intro x hx
    have hmono : positivePartSub u (deGiorgiLevel lamStar 0) x ≤ max (u x) 0 := by
      exact positivePartSub_le_posPartZero hlev_nonneg x
    have hsmall_nonneg : 0 ≤ positivePartSub u (deGiorgiLevel lamStar 0) x :=
      positivePartSub_nonneg
    have hbig_nonneg : 0 ≤ max (u x) 0 := le_max_right _ _
    have hsq :
        (positivePartSub u (deGiorgiLevel lamStar 0) x) ^ 2 ≤
          (max (u x) 0) ^ 2 := by
      nlinarith
    simpa [abs_of_nonneg hsmall_nonneg, abs_of_nonneg hbig_nonneg] using hsq
  have hbig_int_small :
      IntegrableOn (fun x => |max (u x) 0| ^ 2)
        (Metric.ball x₀ (deGiorgiRadius 0)) volume :=
    hposInt.mono_set hs
  have hmono_same_set :
      ∫ x in Metric.ball x₀ (deGiorgiRadius 0),
          |positivePartSub u (deGiorgiLevel lamStar 0) x| ^ 2 ∂volume ≤
        ∫ x in Metric.ball x₀ (deGiorgiRadius 0), |max (u x) 0| ^ 2 ∂volume := by
    refine integral_mono_ae hA0Int hbig_int_small ?_
    · refine (ae_restrict_iff' (μ := volume) isOpen_ball.measurableSet).2 ?_
      filter_upwards with x hx
      exact hpointwise x hx
  have hnonneg :
      ∀ x, 0 ≤ |max (u x) 0| ^ 2 := by
    intro x
    positivity
  have hmono_set :
      ∫ x in Metric.ball x₀ (deGiorgiRadius 0), |max (u x) 0| ^ 2 ∂volume ≤
        ∫ x in Metric.ball x₀ 1, |max (u x) 0| ^ 2 ∂volume := by
    exact setIntegral_mono_set hposInt (ae_of_all _ hnonneg) (ae_of_all _ hs)
  calc
    deGiorgiEnergySeq u x₀ lamStar 0
        = ∫ x in Metric.ball x₀ (deGiorgiRadius 0),
            |positivePartSub u (deGiorgiLevel lamStar 0) x| ^ 2 ∂volume := by
              simp [deGiorgiEnergySeq]
    _ ≤ ∫ x in Metric.ball x₀ (deGiorgiRadius 0), |max (u x) 0| ^ 2 ∂volume := hmono_same_set
    _ ≤ ∫ x in Metric.ball x₀ 1, |max (u x) 0| ^ 2 ∂volume := hmono_set

/-- Height constant for converting a unit-ball `L²` smallness condition into
the abstract initial De Giorgi recurrence threshold. This still depends on the
one-step coefficient `K`; later PDE-facing theorems will substitute the
specific `K` coming from pre-iteration. -/
noncomputable def C_DeGiorgiSmallness (d : ℕ) (K : ℝ) : ℝ :=
  (K * (2 : ℝ) ^ (6 + 8 / (d : ℝ))) ^ ((d : ℝ) / 4) *
    (deGiorgiRecurrenceBase d) ^ (((d : ℝ) ^ 2) / 8)

omit [NeZero d] in
theorem C_DeGiorgiSmallness_pos
    {K : ℝ} (hK : 0 < K) :
    0 < C_DeGiorgiSmallness d K := by
  rw [C_DeGiorgiSmallness]
  have hA_pos : 0 < K * (2 : ℝ) ^ (6 + 8 / (d : ℝ)) := by
    positivity
  have hB_pos : 0 < deGiorgiRecurrenceBase d := by
    rw [deGiorgiRecurrenceBase]
    positivity
  exact mul_pos (Real.rpow_pos_of_pos hA_pos _) (Real.rpow_pos_of_pos hB_pos _)

omit [NeZero d] in
theorem C_DeGiorgiSmallness_mono
    {K₁ K₂ : ℝ} (hK₁_nonneg : 0 ≤ K₁) (hK : K₁ ≤ K₂) :
    C_DeGiorgiSmallness d K₁ ≤ C_DeGiorgiSmallness d K₂ := by
  rw [C_DeGiorgiSmallness, C_DeGiorgiSmallness]
  have hpow_nonneg : 0 ≤ (2 : ℝ) ^ (6 + 8 / (d : ℝ)) := by
    positivity
  have harg_le :
      K₁ * (2 : ℝ) ^ (6 + 8 / (d : ℝ)) ≤
        K₂ * (2 : ℝ) ^ (6 + 8 / (d : ℝ)) :=
    mul_le_mul_of_nonneg_right hK hpow_nonneg
  have hexp_nonneg : 0 ≤ (d : ℝ) / 4 := by
    positivity
  have hrpow :
      (K₁ * (2 : ℝ) ^ (6 + 8 / (d : ℝ))) ^ ((d : ℝ) / 4) ≤
        (K₂ * (2 : ℝ) ^ (6 + 8 / (d : ℝ))) ^ ((d : ℝ) / 4) := by
    exact Real.rpow_le_rpow (mul_nonneg hK₁_nonneg hpow_nonneg) harg_le hexp_nonneg
  have hbase_nonneg :
      0 ≤ (deGiorgiRecurrenceBase d) ^ (((d : ℝ) ^ 2) / 8) := by
    have hbase_pos : 0 < deGiorgiRecurrenceBase d := by
      rw [deGiorgiRecurrenceBase]
      positivity
    exact (Real.rpow_pos_of_pos hbase_pos _).le
  exact mul_le_mul_of_nonneg_right hrpow hbase_nonneg

omit [NeZero d] in
theorem C_DeGiorgiSmallness_mul_right
    {K t : ℝ} (hK : 0 ≤ K) (ht : 0 ≤ t) :
    C_DeGiorgiSmallness d (K * t) =
      C_DeGiorgiSmallness d K * t ^ ((d : ℝ) / 4) := by
  rw [C_DeGiorgiSmallness, C_DeGiorgiSmallness]
  have hpow_nonneg : 0 ≤ (2 : ℝ) ^ (6 + 8 / (d : ℝ)) := by
    positivity
  have hKt_nonneg : 0 ≤ K * (2 : ℝ) ^ (6 + 8 / (d : ℝ)) := by
    exact mul_nonneg hK hpow_nonneg
  calc
    (((K * t) * (2 : ℝ) ^ (6 + 8 / (d : ℝ))) ^ ((d : ℝ) / 4)) *
            (deGiorgiRecurrenceBase d) ^ (((d : ℝ) ^ 2) / 8)
            = (((K * (2 : ℝ) ^ (6 + 8 / (d : ℝ))) * t) ^ ((d : ℝ) / 4)) *
                (deGiorgiRecurrenceBase d) ^ (((d : ℝ) ^ 2) / 8) := by
            congr 1
            ring_nf
    _ = ((K * (2 : ℝ) ^ (6 + 8 / (d : ℝ))) ^ ((d : ℝ) / 4) *
            t ^ ((d : ℝ) / 4)) *
            (deGiorgiRecurrenceBase d) ^ (((d : ℝ) ^ 2) / 8) := by
            rw [Real.mul_rpow hKt_nonneg ht]
    _ = (((K * (2 : ℝ) ^ (6 + 8 / (d : ℝ))) ^ ((d : ℝ) / 4)) *
          (deGiorgiRecurrenceBase d) ^ (((d : ℝ) ^ 2) / 8)) *
          t ^ ((d : ℝ) / 4) := by
            ring

omit [NeZero d] in
/-- Positive-energy height threshold on the unit ball with the exact
De Giorgi smallness constant. -/
theorem deGiorgi_exact_height_threshold_on_unitBall
    {u : E → ℝ} {K : ℝ}
    (hK : 0 < K)
    (hI₀_pos :
      0 < ∫ x in Metric.ball (0 : E) 1, |max (u x) 0| ^ 2 ∂volume) :
    0 < C_DeGiorgiSmallness d K *
      Real.sqrt (∫ x in Metric.ball (0 : E) 1, |max (u x) 0| ^ 2 ∂volume) := by
  exact mul_pos
    (C_DeGiorgiSmallness_pos (d := d) hK)
    (Real.sqrt_pos.2 hI₀_pos)

omit [NeZero d] in
private lemma setIntegral_ball_eq_of_zero_off_innerBall
    {f : E → ℝ} {x₀ : E} {r s : ℝ}
    (hrs : r < s)
    (_hf_int : IntegrableOn f (Metric.ball x₀ s) volume)
    (hzero :
      ∀ x ∈ Metric.ball x₀ s, x ∉ Metric.ball x₀ r → f x = 0) :
    ∫ x in Metric.ball x₀ s, f x ∂volume =
      ∫ x in Metric.ball x₀ r, f x ∂volume := by
  let Ω : Set E := Metric.ball x₀ s
  let B : Set E := Metric.ball x₀ r
  have hsub : B ⊆ Ω := Metric.ball_subset_ball (le_of_lt hrs)
  have hB_meas : MeasurableSet B := by
    simpa [B] using measurableSet_ball
  have h_eq :
      (fun x => f x) =ᵐ[volume.restrict Ω] B.indicator f := by
    refine (ae_restrict_iff' (μ := volume) isOpen_ball.measurableSet).2 ?_
    filter_upwards with x hxΩ
    by_cases hxB : x ∈ B
    · simp [B, hxB]
    · simp [B, hxB, hzero x hxΩ hxB]
  calc
    ∫ x in Ω, f x ∂volume = ∫ x, B.indicator f x ∂(volume.restrict Ω) := by
      exact integral_congr_ae h_eq
    _ = ∫ x in B, f x ∂(volume.restrict Ω) := by
      simpa using
        (integral_indicator (μ := volume.restrict Ω) (s := B) (f := f) hB_meas)
    _ = ∫ x in B, f x ∂volume := by
      rw [Measure.restrict_restrict_of_subset hsub]

/-- Dimension-only coefficient in the unit-ball De Giorgi iteration package.

It packages the assembly step from `IsSubsolution` to the concrete
De Giorgi recurrence data used by the closeout layer: a positive one-step
coefficient `K`, integrability of the truncated energies on the canonical balls,
and the nonlinear recurrence itself. -/
noncomputable def K_DeGiorgi_subsolution
    (d : ℕ) [NeZero d]
    (A : EllipticCoeff d (Metric.ball (0 : AmbientSpace d) 1)) : ℝ :=
  (C_gns d 2) ^ 2 * (8 * (ellipticityRatio A + 1) * (2 * (Mst : ℝ)) ^ 2) + 1

theorem K_DeGiorgi_subsolution_pos
    (A : EllipticCoeff d (Metric.ball (0 : E) 1)) :
    0 < K_DeGiorgi_subsolution d A := by
  rw [K_DeGiorgi_subsolution]
  have hnonneg :
      0 ≤ (C_gns d 2) ^ 2 * (8 * (ellipticityRatio A + 1) * (2 * (Mst : ℝ)) ^ 2) := by
    have hratio_nonneg : 0 ≤ ellipticityRatio A + 1 := by
      linarith [A.ellipticityRatio_nonneg]
    have htmp_nonneg : 0 ≤ (ellipticityRatio A + 1) * (2 * (Mst : ℝ)) ^ 2 := by
      exact mul_nonneg hratio_nonneg (sq_nonneg _)
    have hfactor_nonneg : 0 ≤ 8 * (ellipticityRatio A + 1) * (2 * (Mst : ℝ)) ^ 2 := by
      have h8_nonneg : (0 : ℝ) ≤ 8 := by norm_num
      simpa [mul_assoc] using mul_nonneg h8_nonneg htmp_nonneg
    exact mul_nonneg (sq_nonneg _) hfactor_nonneg
  linarith

noncomputable def C_DeGiorgi_subsolution
    (d : ℕ) [NeZero d]
    (A : EllipticCoeff d (Metric.ball (0 : AmbientSpace d) 1)) : ℝ :=
  C_DeGiorgiSmallness d (K_DeGiorgi_subsolution d A)

theorem C_DeGiorgi_subsolution_pos
    (A : EllipticCoeff d (Metric.ball (0 : E) 1)) :
    0 < C_DeGiorgi_subsolution d A := by
  rw [C_DeGiorgi_subsolution]
  exact C_DeGiorgiSmallness_pos (d := d) (K_DeGiorgi_subsolution_pos (d := d) A)

theorem deGiorgi_iteration_package_on_unitBall_of_subsolution
    (hd : 2 < (d : ℝ))
    (A : EllipticCoeff d (Metric.ball (0 : E) 1))
    {u : E → ℝ}
    (hsub : IsSubsolution A u) :
    0 < K_DeGiorgi_subsolution d A ∧
      ∀ {lamStar : ℝ}, 0 < lamStar →
        IntegrableOn (fun x => |positivePartSub u lamStar x| ^ 2)
          (Metric.ball (0 : E) (1 / 2 : ℝ)) volume ∧
        (∀ n,
          IntegrableOn (fun x => |positivePartSub u (deGiorgiLevel lamStar n) x| ^ 2)
            (Metric.ball (0 : E) (deGiorgiRadius n)) volume) ∧
        (∀ n,
          deGiorgiEnergySeq u (0 : E) lamStar (n + 1) ≤
            K_DeGiorgi_subsolution d A /
              ((deGiorgiRadius n - deGiorgiRadius (n + 1)) ^ 2 *
                (deGiorgiLevel lamStar (n + 1) - deGiorgiLevel lamStar n) ^ (4 / (d : ℝ))) *
              deGiorgiEnergySeq u (0 : E) lamStar n ^ (1 + 2 / (d : ℝ))) := by
  let hu1 : MemW1pWitness 2 u (Metric.ball (0 : E) 1) :=
    DeGiorgi.MemW1p.someWitness (isSubsolution_memW1p hsub)
  haveI : IsFiniteMeasure (volume.restrict (Metric.ball (0 : E) 1)) := by
    rw [isFiniteMeasure_restrict]
    exact measure_ball_lt_top.ne
  have happroxUnit :
      ∀ θ : ℝ,
        ∃ ψ : ℕ → E → ℝ,
          (∀ n, ContDiff ℝ 1 (ψ n)) ∧
          (∀ n, HasCompactSupport (ψ n)) ∧
          Tendsto
            (fun n =>
              eLpNorm (fun x => ψ n x - (u x - θ)) 2
                (volume.restrict (Metric.ball (0 : E) 1)))
            atTop (nhds 0) ∧
          (∀ i : Fin d,
            Tendsto
              (fun n =>
                eLpNorm
                  (fun x =>
                    (fderiv ℝ (ψ n) x) (EuclideanSpace.single i 1) - hu1.weakGrad x i)
                  2 (volume.restrict (Metric.ball (0 : E) 1)))
              atTop (nhds 0)) := by
    intro θ
    let huShift : MemW1pWitness 2 (fun x => u x - θ) (Metric.ball (0 : E) 1) :=
      hu1.sub_const isOpen_ball θ
    rcases exists_smooth_W12_approx_on_unitBall (d := d) huShift with
      ⟨ψ, hψ_smooth, hψ_compact, hψ_fun, hψ_grad⟩
    refine ⟨ψ, ?_, hψ_compact, hψ_fun, ?_⟩
    · intro n
      exact (hψ_smooth n).of_le (by norm_num)
    · intro i
      simpa [huShift] using hψ_grad i
  let Kraw : ℝ :=
    (C_gns d 2) ^ 2 * (8 * (ellipticityRatio A + 1) * (2 * (Mst : ℝ)) ^ 2)
  let K : ℝ := K_DeGiorgi_subsolution d A
  have hK_eq : K = Kraw + 1 := by
    dsimp [K, Kraw, K_DeGiorgi_subsolution]
  have hKraw_nonneg : 0 ≤ Kraw := by
    dsimp [Kraw]
    have hratio_nonneg : 0 ≤ ellipticityRatio A + 1 := by
      linarith [A.ellipticityRatio_nonneg]
    have htmp_nonneg : 0 ≤ (ellipticityRatio A + 1) * (2 * (Mst : ℝ)) ^ 2 := by
      exact mul_nonneg hratio_nonneg (sq_nonneg _)
    have hfactor_nonneg : 0 ≤ 8 * (ellipticityRatio A + 1) * (2 * (Mst : ℝ)) ^ 2 := by
      have h8_nonneg : (0 : ℝ) ≤ 8 := by norm_num
      simpa [mul_assoc] using mul_nonneg h8_nonneg htmp_nonneg
    exact mul_nonneg (sq_nonneg _) hfactor_nonneg
  have hKraw_le_K : Kraw ≤ K := by
    rw [hK_eq]
    linarith
  have hK : 0 < K := by
    rw [hK_eq]
    linarith
  refine ⟨by simpa [K] using hK, ?_⟩
  intro lamStar hLamStar
  have hStarInt :
      IntegrableOn (fun x => |positivePartSub u lamStar x| ^ 2)
        (Metric.ball (0 : E) (1 / 2 : ℝ)) volume := by
    let hwStar1 : MemW1pWitness 2 (positivePartSub u lamStar) (Metric.ball (0 : E) 1) :=
      positivePartSub_memW1pWitness_on_ball (d := d) (x₀ := (0 : E)) (s := 1)
        zero_lt_one hu1 lamStar (happroxUnit lamStar)
    have hStarInt1 :
        IntegrableOn (fun x => |positivePartSub u lamStar x| ^ 2)
          (Metric.ball (0 : E) 1) volume := by
      simpa [pow_two] using hwStar1.memLp.integrable_sq
    exact hStarInt1.mono_set (Metric.ball_subset_ball (by norm_num : (1 / 2 : ℝ) ≤ 1))
  have hAint :
      ∀ n,
        IntegrableOn (fun x => |positivePartSub u (deGiorgiLevel lamStar n) x| ^ 2)
          (Metric.ball (0 : E) (deGiorgiRadius n)) volume := by
    intro n
    let θ : ℝ := deGiorgiLevel lamStar n
    let hwθ1 : MemW1pWitness 2 (positivePartSub u θ) (Metric.ball (0 : E) 1) :=
      positivePartSub_memW1pWitness_on_ball (d := d) (x₀ := (0 : E)) (s := 1)
        zero_lt_one hu1 θ (happroxUnit θ)
    have hθInt1 :
        IntegrableOn (fun x => |positivePartSub u θ x| ^ 2)
          (Metric.ball (0 : E) 1) volume := by
      simpa [θ, pow_two] using hwθ1.memLp.integrable_sq
    exact hθInt1.mono_set (Metric.ball_subset_ball (le_of_lt (deGiorgiRadius_lt_one n)))
  have hpre :
      ∀ n,
        deGiorgiEnergySeq u (0 : E) lamStar (n + 1) ≤
          K / ((deGiorgiRadius n - deGiorgiRadius (n + 1)) ^ 2 *
            (deGiorgiLevel lamStar (n + 1) - deGiorgiLevel lamStar n) ^ (4 / (d : ℝ))) *
          deGiorgiEnergySeq u (0 : E) lamStar n ^ (1 + 2 / (d : ℝ)) := by
    intro n
    let r : ℝ := deGiorgiRadius (n + 1)
    let s : ℝ := deGiorgiRadius n
    let θ : ℝ := deGiorgiLevel lamStar n
    let lam : ℝ := deGiorgiLevel lamStar (n + 1)
    have hr : 0 < r := by
      dsimp [r]
      linarith [deGiorgiRadius_gt_half (n + 1)]
    have hs : 0 < s := by
      dsimp [s]
      linarith [deGiorgiRadius_gt_half n]
    have hrs : r < s := by
      have hgap : 0 < s - r := by
        dsimp [s, r]
        rw [deGiorgiRadius_gap]
        positivity
      linarith
    have hs_lt_one : s < 1 := by
      dsimp [s]
      exact deGiorgiRadius_lt_one n
    have hθl : θ < lam := by
      have hgap : 0 < lam - θ := by
        dsimp [lam, θ]
        rw [deGiorgiLevel_gap]
        positivity
      linarith
    have hsr_pos : 0 < s - r := sub_pos.mpr hrs
    let huS : MemW1pWitness 2 u (Metric.ball (0 : E) s) :=
      hu1.restrict isOpen_ball (Metric.ball_subset_ball (le_of_lt hs_lt_one))
    have happroxBallTheta :
        ∃ ψ : ℕ → E → ℝ,
          (∀ n, ContDiff ℝ 1 (ψ n)) ∧
          (∀ n, HasCompactSupport (ψ n)) ∧
          Tendsto
            (fun n =>
              eLpNorm (fun x => ψ n x - (u x - θ)) 2
                (volume.restrict (Metric.ball (0 : E) s)))
            atTop (nhds 0) ∧
          (∀ i : Fin d,
            Tendsto
              (fun n =>
                eLpNorm
                  (fun x =>
                    (fderiv ℝ (ψ n) x) (EuclideanSpace.single i 1) - huS.weakGrad x i)
                  2 (volume.restrict (Metric.ball (0 : E) s)))
              atTop (nhds 0)) := by
      rcases happroxUnit θ with ⟨ψ, hψ_smooth, hψ_compact, hψ_fun, hψ_grad⟩
      refine ⟨ψ, hψ_smooth, hψ_compact, ?_, ?_⟩
      · refine ENNReal.tendsto_nhds_zero.2 ?_
        intro ε hε
        filter_upwards [ENNReal.tendsto_nhds_zero.1 hψ_fun ε hε] with m hm
        exact le_trans
          (eLpNorm_mono_measure (fun x => ψ m x - (u x - θ))
            (Measure.restrict_mono_set volume
              (Metric.ball_subset_ball (le_of_lt hs_lt_one))))
          hm
      · intro i
        refine ENNReal.tendsto_nhds_zero.2 ?_
        intro ε hε
        filter_upwards [ENNReal.tendsto_nhds_zero.1 (hψ_grad i) ε hε] with m hm
        have hmono :
            eLpNorm
              (fun x =>
                (fderiv ℝ (ψ m) x) (EuclideanSpace.single i 1) - huS.weakGrad x i)
              2 (volume.restrict (Metric.ball (0 : E) s)) ≤
              eLpNorm
                (fun x =>
                  (fderiv ℝ (ψ m) x) (EuclideanSpace.single i 1) - hu1.weakGrad x i)
                2 (volume.restrict (Metric.ball (0 : E) 1)) := by
          simpa [huS] using
            (eLpNorm_mono_measure
              (fun x =>
                (fderiv ℝ (ψ m) x) (EuclideanSpace.single i 1) - hu1.weakGrad x i)
              (Measure.restrict_mono_set volume
                (Metric.ball_subset_ball (le_of_lt hs_lt_one))))
        exact le_trans hmono hm
    let R : ℝ := (r + s) / 2
    have hR : r < R := by
      dsimp [R]
      linarith
    have hR_lt_s : R < s := by
      dsimp [R]
      linarith
    obtain ⟨ηCut, _⟩ := Cutoff.exists (d := d) (0 : E) (r := r) (R := R) hr hR
    let η : E → ℝ := ηCut.toFun
    let Cη : ℝ := 2 * (Mst : ℝ) * (s - r)⁻¹
    have hη : ContDiff ℝ (⊤ : ℕ∞) η := ηCut.smooth
    have hη_nonneg : ∀ x, 0 ≤ η x := ηCut.nonneg
    have hη_eq_one : ∀ x ∈ Metric.ball (0 : E) r, η x = 1 := ηCut.eq_one
    have hη_bound : ∀ x, |η x| ≤ 1 := by
      intro x
      rw [abs_of_nonneg (ηCut.nonneg x)]
      exact ηCut.le_one x
    have hη_sub_ball_s : tsupport η ⊆ Metric.ball (0 : E) s := by
      exact ηCut.support_subset.trans (Metric.closedBall_subset_ball hR_lt_s)
    have hη_sub_ball1 : tsupport η ⊆ Metric.ball (0 : E) 1 := by
      exact hη_sub_ball_s.trans (Metric.ball_subset_ball (le_of_lt hs_lt_one))
    have hCη : 0 ≤ Cη := by
      dsimp [Cη]
      positivity
    have hη_grad_bound : ∀ x, ‖fderiv ℝ η x‖ ≤ Cη := by
      intro x
      have hmid :
          (((r + s) / 2 : ℝ) - r) = (s - r) / 2 := by
        ring
      have h_inv : ((((r + s) / 2 : ℝ) - r)⁻¹) = 2 * (s - r)⁻¹ := by
        rw [hmid]
        field_simp [hsr_pos.ne']
      calc
        ‖fderiv ℝ η x‖ ≤ ↑Mst * ((((r + s) / 2 : ℝ) - r)⁻¹) := by
          simpa [η, R] using ηCut.grad_bound x
        _ = 2 * (Mst : ℝ) * (s - r)⁻¹ := by
          rw [h_inv]
          ring
        _ = Cη := by
          rfl
    obtain ⟨hwηθ, hsob⟩ :=
      deGiorgi_cutoffSobolev_on_concentricBalls_of_posPartApprox
        (d := d) hd hs hr hrs huS happroxBallTheta hθl hη hη_nonneg
        hη_eq_one hη_bound hη_sub_ball_s
    let hwθ1 : MemW1pWitness 2 (positivePartSub u θ) (Metric.ball (0 : E) 1) :=
      positivePartSub_memW1pWitness_on_ball (d := d) (x₀ := (0 : E)) (s := 1)
        zero_lt_one hu1 θ (happroxUnit θ)
    let hwθs : MemW1pWitness 2 (positivePartSub u θ) (Metric.ball (0 : E) s) :=
      hwθ1.restrict isOpen_ball (Metric.ball_subset_ball (le_of_lt hs_lt_one))
    have hweighted_unit :
        ∫ x in Metric.ball (0 : E) 1, η x ^ 2 * ‖hwθ1.weakGrad x‖ ^ 2 ∂volume ≤
          4 * ellipticityRatio A *
            ∫ x in Metric.ball (0 : E) 1,
              ‖fderiv ℝ η x‖ ^ 2 * |positivePartSub u θ x| ^ 2 ∂volume := by
      simpa [hwθ1] using
        caccioppoli_weighted_on_ball_of_posPartApprox
          (d := d) (x₀ := (0 : E)) (s := 1) (u := u) (η := η) (Cη := Cη) (k := θ)
          A zero_lt_one hsub hu1 (happroxUnit θ) hη hη_nonneg hη_bound
          hCη hη_grad_bound hη_sub_ball1
    have hleft_int_unit :
        IntegrableOn (fun x => η x ^ 2 * ‖hwθ1.weakGrad x‖ ^ 2)
          (Metric.ball (0 : E) 1) volume := by
      have hgradSqInt :
          Integrable (fun x => ‖hwθ1.weakGrad x‖ ^ 2)
            (volume.restrict (Metric.ball (0 : E) 1)) := by
        simpa [pow_two] using hwθ1.weakGrad_norm_memLp.integrable_sq
      refine Integrable.mono' hgradSqInt ?_ ?_
      · exact
          (((hη.continuous.pow 2).aemeasurable).mul
            hgradSqInt.aestronglyMeasurable.aemeasurable).aestronglyMeasurable
      · filter_upwards with x
        have hηx_nonneg : 0 ≤ η x := hη_nonneg x
        have hηx_le_one : η x ≤ 1 := by
          simpa [abs_of_nonneg hηx_nonneg] using hη_bound x
        have hηx_sq_le_one : η x ^ 2 ≤ 1 := by
          nlinarith
        have hgw_nonneg : 0 ≤ ‖hwθ1.weakGrad x‖ ^ 2 := by positivity
        have hprod_nonneg : 0 ≤ η x ^ 2 * ‖hwθ1.weakGrad x‖ ^ 2 := by positivity
        have hle :
            η x ^ 2 * ‖hwθ1.weakGrad x‖ ^ 2 ≤ ‖hwθ1.weakGrad x‖ ^ 2 := by
          nlinarith
        simpa [Real.norm_eq_abs, abs_of_nonneg hprod_nonneg, abs_of_nonneg hgw_nonneg] using hle
    have hright_int_unit :
        IntegrableOn (fun x => ‖fderiv ℝ η x‖ ^ 2 * |positivePartSub u θ x| ^ 2)
          (Metric.ball (0 : E) 1) volume := by
      have hposSqInt :
          Integrable (fun x => |positivePartSub u θ x| ^ 2)
            (volume.restrict (Metric.ball (0 : E) 1)) := by
        simpa [pow_two] using hwθ1.memLp.integrable_sq
      refine Integrable.mono' (hposSqInt.const_mul (Cη ^ 2)) ?_ ?_
      · exact
          ((((hη.continuous_fderiv (by simp : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0)).norm.pow 2).aemeasurable).mul
            hposSqInt.aestronglyMeasurable.aemeasurable).aestronglyMeasurable
      · filter_upwards with x
        have hfd_sq_le : ‖fderiv ℝ η x‖ ^ 2 ≤ Cη ^ 2 := by
          exact sq_le_sq.mpr (by
            simpa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg hCη] using hη_grad_bound x)
        have hpos_nonneg : 0 ≤ |positivePartSub u θ x| ^ 2 := by positivity
        have hterm_nonneg :
            0 ≤ ‖fderiv ℝ η x‖ ^ 2 * |positivePartSub u θ x| ^ 2 := by positivity
        have hle :
            ‖fderiv ℝ η x‖ ^ 2 * |positivePartSub u θ x| ^ 2 ≤
              Cη ^ 2 * |positivePartSub u θ x| ^ 2 :=
          mul_le_mul_of_nonneg_right hfd_sq_le hpos_nonneg
        simpa [Real.norm_eq_abs, abs_of_nonneg hterm_nonneg] using hle
    have hleft_eq :
        ∫ x in Metric.ball (0 : E) 1, η x ^ 2 * ‖hwθ1.weakGrad x‖ ^ 2 ∂volume =
          ∫ x in Metric.ball (0 : E) s, η x ^ 2 * ‖hwθs.weakGrad x‖ ^ 2 ∂volume := by
      calc
        ∫ x in Metric.ball (0 : E) 1, η x ^ 2 * ‖hwθ1.weakGrad x‖ ^ 2 ∂volume
            = ∫ x in Metric.ball (0 : E) s, η x ^ 2 * ‖hwθ1.weakGrad x‖ ^ 2 ∂volume := by
                refine setIntegral_ball_eq_of_zero_off_innerBall (x₀ := (0 : E)) hs_lt_one
                  hleft_int_unit ?_
                intro x hx1 hxs
                have hηx : η x = 0 := by
                  exact zero_outside_of_tsupport_subset
                    (Ω := Metric.ball (0 : E) s) hη_sub_ball_s hxs
                simp [hηx]
        _ = ∫ x in Metric.ball (0 : E) s, η x ^ 2 * ‖hwθs.weakGrad x‖ ^ 2 ∂volume := by
              rfl
    have hright_eq :
        ∫ x in Metric.ball (0 : E) 1, ‖fderiv ℝ η x‖ ^ 2 * |positivePartSub u θ x| ^ 2 ∂volume =
          ∫ x in Metric.ball (0 : E) s, ‖fderiv ℝ η x‖ ^ 2 * |positivePartSub u θ x| ^ 2
            ∂volume := by
      refine setIntegral_ball_eq_of_zero_off_innerBall (x₀ := (0 : E)) hs_lt_one
        hright_int_unit ?_
      intro x hx1 hxs
      have hfdv_zero : deGiorgiFderivVec η x = 0 := by
        ext i
        rw [deGiorgiFderivVec_apply]
        exact fderiv_apply_zero_outside_of_tsupport_subset
          (Ω := Metric.ball (0 : E) s) (hf := hη) hη_sub_ball_s hxs i
      have hfd_zero : ‖fderiv ℝ η x‖ = 0 := by
        rw [← deGiorgi_norm_fderivVec_eq_norm_fderiv (η := η) (x := x), hfdv_zero, norm_zero]
      simp [hfd_zero]
    have hweighted_small :
        ∫ x in Metric.ball (0 : E) s, η x ^ 2 * ‖hwθs.weakGrad x‖ ^ 2 ∂volume ≤
          4 * ellipticityRatio A *
            ∫ x in Metric.ball (0 : E) s,
              ‖fderiv ℝ η x‖ ^ 2 * |positivePartSub u θ x| ^ 2 ∂volume := by
      rw [← hleft_eq, ← hright_eq]
      exact hweighted_unit
    let Iθ : ℝ := deGiorgiEnergySeq u (0 : E) lamStar n
    let Ilam : ℝ := deGiorgiEnergySeq u (0 : E) lamStar (n + 1)
    let hwφ : MemW1pWitness 2 (deGiorgiCutoffTestGeneral η u θ) (Metric.ball (0 : E) s) :=
      deGiorgiCutoffTestWitnessWeighted
        isOpen_ball hwθs hη (by norm_num) hCη hη_bound hη_grad_bound
    have hgrad_bound_phi :
        ∫ x in Metric.ball (0 : E) s, ‖hwφ.weakGrad x‖ ^ 2 ∂volume ≤
          (8 * (ellipticityRatio A + 1) * Cη ^ 2) * Iθ := by
      simpa [Iθ, deGiorgiEnergySeq, hwφ, s, θ] using
        deGiorgi_cutoff_gradient_bound_of_weighted
          (x₀ := (0 : E)) (s := s) (u := u) (η := η) (k := θ)
          (Cη := Cη) (Cw := ellipticityRatio A)
          A.ellipticityRatio_nonneg hwθs hη hη_nonneg hη_bound hCη hη_grad_bound
          hweighted_small
    have hgrad_ae :
        hwηθ.weakGrad =ᵐ[volume.restrict (Metric.ball (0 : E) s)] hwφ.weakGrad :=
      MemW1pWitness.ae_eq isOpen_ball hwηθ hwφ
    have henergy :
        ∫ x in Metric.ball (0 : E) s, ‖hwηθ.weakGrad x‖ ^ 2 ∂volume ≤
          (8 * (ellipticityRatio A + 1) * Cη ^ 2) * Iθ := by
      have hgrad_eq :
          ∫ x in Metric.ball (0 : E) s, ‖hwηθ.weakGrad x‖ ^ 2 ∂volume =
            ∫ x in Metric.ball (0 : E) s, ‖hwφ.weakGrad x‖ ^ 2 ∂volume := by
        refine integral_congr_ae ?_
        filter_upwards [hgrad_ae] with x hx
        simp [hx]
      rw [hgrad_eq]
      exact hgrad_bound_phi
    have hθ_int :
        Integrable (fun x => |positivePartSub u θ x| ^ 2)
          (volume.restrict (Metric.ball (0 : E) s)) := by
      simpa [pow_two] using hwθs.memLp.integrable_sq
    have hIθ_nonneg : 0 ≤ Iθ := by
      dsimp [Iθ, deGiorgiEnergySeq]
      refine integral_nonneg ?_
      intro x
      positivity
    have hd_pos : 0 < (d : ℝ) := by
      linarith
    have hCenergy_nonneg : 0 ≤ 8 * (ellipticityRatio A + 1) * Cη ^ 2 := by
      nlinarith [A.ellipticityRatio_nonneg, sq_nonneg Cη]
    haveI : IsFiniteMeasure (volume.restrict (Metric.ball (0 : E) s)) := by
      rw [isFiniteMeasure_restrict]
      exact measure_ball_lt_top.ne
    have hpre_raw :
        Ilam ≤
          (C_gns d 2) ^ 2 * (8 * (ellipticityRatio A + 1) * Cη ^ 2) *
            ((((lam - θ) ^ 2)⁻¹ * Iθ) ^ (2 / (d : ℝ))) * Iθ := by
      have hsob' :
          Ilam ≤
            (C_gns d 2) ^ 2 *
              (∫ x in Metric.ball (0 : E) s, ‖hwηθ.weakGrad x‖ ^ 2 ∂volume) *
              ((volume.restrict (Metric.ball (0 : E) s)).real {x | lam < u x}) ^ (2 / (d : ℝ)) := by
        simpa [Ilam, deGiorgiEnergySeq, r, lam] using hsob
      exact
        deGiorgi_preiter_of_energy
          (μ := volume.restrict (Metric.ball (0 : E) s))
          (d := d) hd_pos (u := u) (θ := θ) (lam := lam)
          (Ilam := Ilam)
          (Iθ := Iθ)
          (G := ∫ x in Metric.ball (0 : E) s, ‖hwηθ.weakGrad x‖ ^ 2 ∂volume)
          (Csob := (C_gns d 2) ^ 2)
          (Cenergy := 8 * (ellipticityRatio A + 1) * Cη ^ 2)
          hθl (sq_nonneg _) hCenergy_nonneg hIθ_nonneg hθ_int hsob'
          henergy (by simp [Iθ, deGiorgiEnergySeq, s, θ])
    have hgap_pos : 0 < lam - θ := sub_pos.mpr hθl
    have hCη_sq :
        Cη ^ 2 = (2 * (Mst : ℝ)) ^ 2 * (((s - r) ^ 2)⁻¹) := by
      dsimp [Cη]
      rw [mul_pow, inv_pow]
    have hpow_gap :
        ((((lam - θ) ^ 2)⁻¹) ^ (2 / (d : ℝ))) = (lam - θ) ^ (-(4 / (d : ℝ))) := by
      calc
        ((((lam - θ) ^ 2)⁻¹) ^ (2 / (d : ℝ)))
            = ((((lam - θ) ^ 2) ^ (-(1 : ℝ))) ^ (2 / (d : ℝ))) := by
                rw [Real.rpow_neg (by positivity), Real.rpow_one]
        _ = ((lam - θ) ^ 2) ^ ((-(1 : ℝ)) * (2 / (d : ℝ))) := by
              rw [← Real.rpow_mul (by positivity : 0 ≤ (lam - θ) ^ 2)]
        _ = ((lam - θ) ^ 2) ^ (-(2 / (d : ℝ))) := by
              congr 1
              ring
        _ = ((lam - θ) ^ (2 : ℝ)) ^ (-(2 / (d : ℝ))) := by
              congr 1
              exact (Real.rpow_natCast (lam - θ) 2).symm
        _ = (lam - θ) ^ (-(4 / (d : ℝ))) := by
              rw [← Real.rpow_mul hgap_pos.le]
              congr 1
              ring
    have hIθ_pow :
        Iθ ^ (2 / (d : ℝ)) * Iθ = Iθ ^ (1 + 2 / (d : ℝ)) := by
      by_cases hIθ_zero : Iθ = 0
      · have hexp1_pos : 0 < 2 / (d : ℝ) := by positivity
        have hexp2_pos : 0 < 1 + 2 / (d : ℝ) := by linarith
        simp [hIθ_zero, Real.zero_rpow hexp1_pos.ne', Real.zero_rpow hexp2_pos.ne']
      · have hIθ_pos : 0 < Iθ := lt_of_le_of_ne hIθ_nonneg (by simpa [eq_comm] using hIθ_zero)
        have hmul_one :
            Iθ ^ (2 / (d : ℝ)) * Iθ = Iθ ^ (2 / (d : ℝ)) * Iθ ^ (1 : ℝ) := by
          rw [Real.rpow_one]
        calc
          Iθ ^ (2 / (d : ℝ)) * Iθ = Iθ ^ (2 / (d : ℝ)) * Iθ ^ (1 : ℝ) := hmul_one
          _ = Iθ ^ ((2 / (d : ℝ)) + 1) := by
            rw [← Real.rpow_add hIθ_pos]
          _ = Iθ ^ (1 + 2 / (d : ℝ)) := by
            congr 1
            ring
    have hcoeff_eq :
        (C_gns d 2) ^ 2 * (8 * (ellipticityRatio A + 1) *
            ((2 * (Mst : ℝ)) ^ 2 * ((s - r) ^ 2)⁻¹)) *
            ((lam - θ) ^ (4 / (d : ℝ)))⁻¹ =
          Kraw * ((s - r) ^ 2 * (lam - θ) ^ (4 / (d : ℝ)))⁻¹ := by
      dsimp [Kraw]
      conv_rhs =>
        rw [_root_.mul_inv_rev]
        rw [mul_comm]
      ring
    have hrewrite :
        (C_gns d 2) ^ 2 * (8 * (ellipticityRatio A + 1) * Cη ^ 2) *
            ((((lam - θ) ^ 2)⁻¹ * Iθ) ^ (2 / (d : ℝ))) * Iθ =
          Kraw / ((s - r) ^ 2 * (lam - θ) ^ (4 / (d : ℝ))) * Iθ ^ (1 + 2 / (d : ℝ)) := by
      rw [hCη_sq]
      rw [Real.mul_rpow (by positivity) hIθ_nonneg]
      rw [hpow_gap]
      have hstep :
          (C_gns d 2) ^ 2 * (8 * (ellipticityRatio A + 1) * ((2 * (Mst : ℝ)) ^ 2 * (((s - r) ^ 2)⁻¹))) *
              ((lam - θ) ^ (-(4 / (d : ℝ))) * Iθ ^ (2 / (d : ℝ))) * Iθ =
            (C_gns d 2) ^ 2 * (8 * (ellipticityRatio A + 1) * ((2 * (Mst : ℝ)) ^ 2 * (((s - r) ^ 2)⁻¹))) *
              (lam - θ) ^ (-(4 / (d : ℝ))) * (Iθ ^ (2 / (d : ℝ)) * Iθ) := by
        ring
      rw [hstep, hIθ_pow]
      rw [Real.rpow_neg hgap_pos.le, div_eq_mul_inv]
      have hcoeff_mul :
          ((C_gns d 2) ^ 2 * (8 * (ellipticityRatio A + 1) *
              ((2 * (Mst : ℝ)) ^ 2 * ((s - r) ^ 2)⁻¹)) *
              ((lam - θ) ^ (4 / (d : ℝ)))⁻¹) *
              Iθ ^ (1 + 2 / (d : ℝ)) =
            (Kraw * ((s - r) ^ 2 * (lam - θ) ^ (4 / (d : ℝ)))⁻¹) *
              Iθ ^ (1 + 2 / (d : ℝ)) := by
        exact congrArg (fun t : ℝ => t * Iθ ^ (1 + 2 / (d : ℝ))) hcoeff_eq
      simpa [div_eq_mul_inv, mul_assoc] using hcoeff_mul
    have hIθ_pow_nonneg : 0 ≤ Iθ ^ (1 + 2 / (d : ℝ)) := by
      exact Real.rpow_nonneg hIθ_nonneg _
    have hden_pos : 0 < (s - r) ^ 2 * (lam - θ) ^ (4 / (d : ℝ)) := by
      have hpow_pos : 0 < (lam - θ) ^ (4 / (d : ℝ)) := by
        exact Real.rpow_pos_of_pos hgap_pos _
      positivity
    have hden_inv_nonneg : 0 ≤ ((s - r) ^ 2 * (lam - θ) ^ (4 / (d : ℝ)))⁻¹ := by
      exact inv_nonneg.mpr (le_of_lt hden_pos)
    calc
      deGiorgiEnergySeq u (0 : E) lamStar (n + 1) = Ilam := by
          rfl
      _ ≤ (C_gns d 2) ^ 2 * (8 * (ellipticityRatio A + 1) * Cη ^ 2) *
            ((((lam - θ) ^ 2)⁻¹ * Iθ) ^ (2 / (d : ℝ))) * Iθ := hpre_raw
      _ = Kraw / ((s - r) ^ 2 * (lam - θ) ^ (4 / (d : ℝ))) * Iθ ^ (1 + 2 / (d : ℝ)) := hrewrite
      _ ≤ K / ((s - r) ^ 2 * (lam - θ) ^ (4 / (d : ℝ))) * Iθ ^ (1 + 2 / (d : ℝ)) := by
            let D : ℝ := ((s - r) ^ 2 * (lam - θ) ^ (4 / (d : ℝ)))⁻¹
            let P : ℝ := Iθ ^ (1 + 2 / (d : ℝ))
            have hD_nonneg : 0 ≤ D := by
              dsimp [D]
              exact hden_inv_nonneg
            have hP_nonneg : 0 ≤ P := by
              dsimp [P]
              exact hIθ_pow_nonneg
            have hKD : Kraw * D ≤ K * D :=
              mul_le_mul_of_nonneg_right hKraw_le_K hD_nonneg
            have hKDP : Kraw * D * P ≤ K * D * P :=
              mul_le_mul_of_nonneg_right hKD hP_nonneg
            simpa [D, P, div_eq_mul_inv, mul_assoc]
              using hKDP
      _ = K / ((deGiorgiRadius n - deGiorgiRadius (n + 1)) ^ 2 *
            (deGiorgiLevel lamStar (n + 1) - deGiorgiLevel lamStar n) ^ (4 / (d : ℝ))) *
            deGiorgiEnergySeq u (0 : E) lamStar n ^ (1 + 2 / (d : ℝ)) := by
            simp [Iθ, deGiorgiEnergySeq, r, s, θ, lam]
  exact ⟨hStarInt, hAint, hpre⟩

theorem deGiorgi_initial_energy_small_of_height_bound
    {K lamStar I₀ : ℝ}
    (hK : 0 < K) (hLamStar : 0 < lamStar)
    (hI₀_nonneg : 0 ≤ I₀)
    (hheight :
      C_DeGiorgiSmallness d K * Real.sqrt I₀ ≤ lamStar) :
    I₀ ≤
      (deGiorgiRecurrenceCoeff d K lamStar) ^ (-(1 : ℝ) / (2 / (d : ℝ))) *
        (deGiorgiRecurrenceBase d) ^ (-(1 : ℝ) / (2 / (d : ℝ)) ^ 2) := by
  have hd_pos : 0 < (d : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
  have hd_ne : (d : ℝ) ≠ 0 := by linarith
  let A : ℝ := K * (2 : ℝ) ^ (6 + 8 / (d : ℝ))
  let B : ℝ := deGiorgiRecurrenceBase d
  have hA_pos : 0 < A := by
    dsimp [A]
    positivity
  have hB_pos : 0 < B := by
    dsimp [B, deGiorgiRecurrenceBase]
    positivity
  have hSmall_pos : 0 < C_DeGiorgiSmallness d K := by
    rw [C_DeGiorgiSmallness]
    exact mul_pos (Real.rpow_pos_of_pos hA_pos _) (Real.rpow_pos_of_pos hB_pos _)
  have hSmall_nonneg : 0 ≤ C_DeGiorgiSmallness d K := by
    exact hSmall_pos.le
  have hheight_sq :
      (C_DeGiorgiSmallness d K * Real.sqrt I₀) ^ 2 ≤ lamStar ^ 2 := by
    exact sq_le_sq' (by nlinarith [hLamStar.le, hSmall_nonneg, Real.sqrt_nonneg I₀]) hheight
  have hsq :
      (C_DeGiorgiSmallness d K) ^ 2 * I₀ ≤ lamStar ^ 2 := by
    nlinarith [hheight_sq, Real.sq_sqrt hI₀_nonneg]
  have hE1 : (-(1 : ℝ) / (2 / (d : ℝ))) = -((d : ℝ) / 2) := by
    field_simp [hd_ne]
  have hE2 : (-(1 : ℝ) / (2 / (d : ℝ)) ^ 2) = -(((d : ℝ) ^ 2) / 4) := by
    field_simp [hd_ne]
    ring_nf
  have hAsq :
      A ^ ((d : ℝ) / 4) * A ^ ((d : ℝ) / 4) = A ^ ((d : ℝ) / 2) := by
    rw [← Real.rpow_add hA_pos]
    congr 1
    ring
  have hBsq :
      B ^ (((d : ℝ) ^ 2) / 8) * B ^ (((d : ℝ) ^ 2) / 8) = B ^ (((d : ℝ) ^ 2) / 4) := by
    rw [← Real.rpow_add hB_pos]
    congr 1
    ring
  have hcoeff :
      (A * lamStar ^ (-(4 / (d : ℝ)))) ^ (-((d : ℝ) / 2)) =
        A ^ (-((d : ℝ) / 2)) * (lamStar ^ (-(4 / (d : ℝ)))) ^ (-((d : ℝ) / 2)) := by
    rw [Real.mul_rpow hA_pos.le (by positivity)]
  have hlam :
      (lamStar ^ (-(4 / (d : ℝ)))) ^ (-((d : ℝ) / 2)) = lamStar ^ (2 : ℝ) := by
    rw [← Real.rpow_mul hLamStar.le]
    congr 1
    field_simp [hd_ne]
    ring_nf
  have hA_cancel :
      A ^ ((d : ℝ) / 2) * A ^ (-((d : ℝ) / 2)) = 1 := by
    rw [← Real.rpow_add hA_pos]
    rw [show (d : ℝ) / 2 + -((d : ℝ) / 2) = 0 by ring, Real.rpow_zero]
  have hB_cancel :
      B ^ (((d : ℝ) ^ 2) / 4) * B ^ (-(((d : ℝ) ^ 2) / 4)) = 1 := by
    rw [← Real.rpow_add hB_pos]
    rw [show ((d : ℝ) ^ 2) / 4 + -(((d : ℝ) ^ 2) / 4) = 0 by ring, Real.rpow_zero]
  have hthreshold :
      (C_DeGiorgiSmallness d K) ^ 2 *
          ((deGiorgiRecurrenceCoeff d K lamStar) ^ (-(1 : ℝ) / (2 / (d : ℝ))) *
            (deGiorgiRecurrenceBase d) ^ (-(1 : ℝ) / (2 / (d : ℝ)) ^ 2)) =
        lamStar ^ 2 := by
    rw [C_DeGiorgiSmallness, deGiorgiRecurrenceCoeff, hE1, hE2]
    change (A ^ ((d : ℝ) / 4) * B ^ (((d : ℝ) ^ 2) / 8)) ^ 2 *
          ((A * lamStar ^ (-(4 / (d : ℝ)))) ^ (-((d : ℝ) / 2)) *
            B ^ (-(((d : ℝ) ^ 2) / 4))) =
        lamStar ^ 2
    rw [pow_two, hcoeff, hlam]
    calc
      (A ^ ((d : ℝ) / 4) * B ^ (((d : ℝ) ^ 2) / 8)) *
            (A ^ ((d : ℝ) / 4) * B ^ (((d : ℝ) ^ 2) / 8)) *
          (A ^ (-((d : ℝ) / 2)) * lamStar ^ (2 : ℝ) * B ^ (-(((d : ℝ) ^ 2) / 4)))
          =
            (A ^ ((d : ℝ) / 4) * A ^ ((d : ℝ) / 4)) *
              (B ^ (((d : ℝ) ^ 2) / 8) * B ^ (((d : ℝ) ^ 2) / 8)) *
              (A ^ (-((d : ℝ) / 2)) * lamStar ^ (2 : ℝ) * B ^ (-(((d : ℝ) ^ 2) / 4))) := by
            ring
      _ =
            A ^ ((d : ℝ) / 2) * B ^ (((d : ℝ) ^ 2) / 4) *
              (A ^ (-((d : ℝ) / 2)) * lamStar ^ (2 : ℝ) * B ^ (-(((d : ℝ) ^ 2) / 4))) := by
            rw [hAsq, hBsq]
      _ =
            (A ^ ((d : ℝ) / 2) * A ^ (-((d : ℝ) / 2))) *
              (B ^ (((d : ℝ) ^ 2) / 4) * B ^ (-(((d : ℝ) ^ 2) / 4))) *
              lamStar ^ (2 : ℝ) := by
            ring
      _ = lamStar ^ 2 := by
            rw [hA_cancel, hB_cancel]
            simp
  have hgoal_mul :
      (C_DeGiorgiSmallness d K) ^ 2 * I₀ ≤
        (C_DeGiorgiSmallness d K) ^ 2 *
          ((deGiorgiRecurrenceCoeff d K lamStar) ^ (-(1 : ℝ) / (2 / (d : ℝ))) *
            (deGiorgiRecurrenceBase d) ^ (-(1 : ℝ) / (2 / (d : ℝ)) ^ 2)) := by
    calc
      (C_DeGiorgiSmallness d K) ^ 2 * I₀ ≤ lamStar ^ 2 := hsq
      _ = (C_DeGiorgiSmallness d K) ^ 2 *
            ((deGiorgiRecurrenceCoeff d K lamStar) ^ (-(1 : ℝ) / (2 / (d : ℝ))) *
              (deGiorgiRecurrenceBase d) ^ (-(1 : ℝ) / (2 / (d : ℝ)) ^ 2)) := by
            symm
            exact hthreshold
  have hSmall_sq_pos : 0 < (C_DeGiorgiSmallness d K) ^ 2 := by
    positivity
  exact le_of_mul_le_mul_left hgoal_mul hSmall_sq_pos

/-- Quantitative constant for the final De Giorgi `L² → L∞` theorem.

The current choice is a simple global normalization compatible with the
preceding pre-iteration bounds and height-threshold lemma. -/
noncomputable def C_DeGiorgi (d : ℕ) [NeZero d] : ℝ :=
  (C_gns d 2) ^ 2

omit [NeZero d] in
/-- Small-data De Giorgi endpoint: if the canonical De Giorgi energy sequence
tends to zero, then the final truncation vanishes almost everywhere on the
half-ball. This is the formally correct endpoint available from the current
Chapter 05 infrastructure before any representative/continuity upgrade. -/
theorem linfty_subsolution_DeGiorgi_ae_zero_of_smallness
    {u : E → ℝ} {x₀ : E} {K lamStar : ℝ}
    (hd : 2 < (d : ℝ))
    (hK : 0 < K) (hLamStar : 0 < lamStar)
    (hStarInt :
      IntegrableOn (fun x => |positivePartSub u lamStar x| ^ 2)
        (Metric.ball x₀ (1 / 2 : ℝ)) volume)
    (hAint :
      ∀ n,
        IntegrableOn (fun x => |positivePartSub u (deGiorgiLevel lamStar n) x| ^ 2)
          (Metric.ball x₀ (deGiorgiRadius n)) volume)
    (hpre :
      ∀ n,
        deGiorgiEnergySeq u x₀ lamStar (n + 1) ≤
          K / ((deGiorgiRadius n - deGiorgiRadius (n + 1)) ^ 2 *
            (deGiorgiLevel lamStar (n + 1) - deGiorgiLevel lamStar n) ^ (4 / (d : ℝ))) *
          deGiorgiEnergySeq u x₀ lamStar n ^ (1 + 2 / (d : ℝ)))
    (hsmall :
      deGiorgiEnergySeq u x₀ lamStar 0 ≤
        (deGiorgiRecurrenceCoeff d K lamStar) ^ (-(1 : ℝ) / (2 / (d : ℝ))) *
          (deGiorgiRecurrenceBase d) ^ (-(1 : ℝ) / (2 / (d : ℝ)) ^ 2)) :
    ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ (1 / 2 : ℝ))),
      positivePartSub u lamStar x = 0 := by
  have hA_nonneg : ∀ n, 0 ≤ deGiorgiEnergySeq u x₀ lamStar n := by
    intro n
    simp [deGiorgiEnergySeq]
    refine integral_nonneg ?_
    intro x
    positivity
  have hvanish :
      Tendsto (deGiorgiEnergySeq u x₀ lamStar) atTop (nhds 0) :=
    deGiorgi_preiter_vanishing hd hK hLamStar hA_nonneg hpre hsmall
  exact ae_eq_zero_of_forall_setIntegral_sq_le_of_tendsto_zero hStarInt
    (integral_sq_halfBall_le_deGiorgiEnergySeq hLamStar hStarInt hAint) hvanish

omit [NeZero d] in
/-- A.e. `L∞` bound on the half-ball in the small-data De Giorgi regime. -/
theorem linfty_subsolution_DeGiorgi_ae_of_smallness
    {u : E → ℝ} {x₀ : E} {K lamStar : ℝ}
    (hd : 2 < (d : ℝ))
    (hK : 0 < K) (hLamStar : 0 < lamStar)
    (hStarInt :
      IntegrableOn (fun x => |positivePartSub u lamStar x| ^ 2)
        (Metric.ball x₀ (1 / 2 : ℝ)) volume)
    (hAint :
      ∀ n,
        IntegrableOn (fun x => |positivePartSub u (deGiorgiLevel lamStar n) x| ^ 2)
          (Metric.ball x₀ (deGiorgiRadius n)) volume)
    (hpre :
      ∀ n,
        deGiorgiEnergySeq u x₀ lamStar (n + 1) ≤
          K / ((deGiorgiRadius n - deGiorgiRadius (n + 1)) ^ 2 *
            (deGiorgiLevel lamStar (n + 1) - deGiorgiLevel lamStar n) ^ (4 / (d : ℝ))) *
          deGiorgiEnergySeq u x₀ lamStar n ^ (1 + 2 / (d : ℝ)))
    (hsmall :
      deGiorgiEnergySeq u x₀ lamStar 0 ≤
        (deGiorgiRecurrenceCoeff d K lamStar) ^ (-(1 : ℝ) / (2 / (d : ℝ))) *
          (deGiorgiRecurrenceBase d) ^ (-(1 : ℝ) / (2 / (d : ℝ)) ^ 2)) :
    ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ (1 / 2 : ℝ))),
      max (u x) 0 ≤ lamStar := by
  filter_upwards
    [linfty_subsolution_DeGiorgi_ae_zero_of_smallness
      hd hK hLamStar hStarInt hAint hpre hsmall] with x hx
  have hux : u x ≤ lamStar := le_of_positivePartSub_eq_zero hx
  exact max_le_iff.mpr ⟨hux, hLamStar.le⟩

omit [NeZero d] in
/-- Unit-ball smallness packaging for the De Giorgi endpoint.

This is the direct successor to the raw `hsmall`-based theorem: instead of
assuming a bound on the abstract initial De Giorgi energy `A₀`, it is enough to
assume the same recurrence threshold for the concrete unit-ball quantity
`∫_{B₁} (u₊)^2`. The radius/level bookkeeping then supplies the `A₀` bound
automatically. -/
theorem linfty_subsolution_DeGiorgi_ae_of_unitBall_initial_energy_smallness
    {u : E → ℝ} {x₀ : E} {K lamStar : ℝ}
    (hd : 2 < (d : ℝ))
    (hK : 0 < K) (hLamStar : 0 < lamStar)
    (hposInt :
      IntegrableOn (fun x => |max (u x) 0| ^ 2)
        (Metric.ball x₀ 1) volume)
    (hStarInt :
      IntegrableOn (fun x => |positivePartSub u lamStar x| ^ 2)
        (Metric.ball x₀ (1 / 2 : ℝ)) volume)
    (hAint :
      ∀ n,
        IntegrableOn (fun x => |positivePartSub u (deGiorgiLevel lamStar n) x| ^ 2)
          (Metric.ball x₀ (deGiorgiRadius n)) volume)
    (hpre :
      ∀ n,
        deGiorgiEnergySeq u x₀ lamStar (n + 1) ≤
          K / ((deGiorgiRadius n - deGiorgiRadius (n + 1)) ^ 2 *
            (deGiorgiLevel lamStar (n + 1) - deGiorgiLevel lamStar n) ^ (4 / (d : ℝ))) *
          deGiorgiEnergySeq u x₀ lamStar n ^ (1 + 2 / (d : ℝ)))
    (hsmall0 :
      ∫ x in Metric.ball x₀ 1, |max (u x) 0| ^ 2 ∂volume ≤
        (deGiorgiRecurrenceCoeff d K lamStar) ^ (-(1 : ℝ) / (2 / (d : ℝ))) *
          (deGiorgiRecurrenceBase d) ^ (-(1 : ℝ) / (2 / (d : ℝ)) ^ 2)) :
    ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ (1 / 2 : ℝ))),
      max (u x) 0 ≤ lamStar := by
  have hsmall :
      deGiorgiEnergySeq u x₀ lamStar 0 ≤
        (deGiorgiRecurrenceCoeff d K lamStar) ^ (-(1 : ℝ) / (2 / (d : ℝ))) *
          (deGiorgiRecurrenceBase d) ^ (-(1 : ℝ) / (2 / (d : ℝ)) ^ 2) := by
    exact
      (deGiorgiEnergySeq_zero_le_integral_sq_posPartZero_on_unitBall hLamStar (hAint 0) hposInt).trans
        hsmall0
  exact linfty_subsolution_DeGiorgi_ae_of_smallness
    hd hK hLamStar hStarInt hAint hpre hsmall

/-- Height-threshold version of the De Giorgi endpoint.

Once the PDE-facing one-step estimate is supplied, a lower bound for `lamStar`
of the form `C(d,K) * sqrt(∫_{B₁} (u₊)^2)` yields the a.e. half-ball `L∞`
bound. -/
theorem linfty_subsolution_DeGiorgi_ae_of_unitBall_height_bound
    {u : E → ℝ} {x₀ : E} {K lamStar : ℝ}
    (hd : 2 < (d : ℝ))
    (hK : 0 < K) (hLamStar : 0 < lamStar)
    (hposInt :
      IntegrableOn (fun x => |max (u x) 0| ^ 2)
        (Metric.ball x₀ 1) volume)
    (hStarInt :
      IntegrableOn (fun x => |positivePartSub u lamStar x| ^ 2)
        (Metric.ball x₀ (1 / 2 : ℝ)) volume)
    (hAint :
      ∀ n,
        IntegrableOn (fun x => |positivePartSub u (deGiorgiLevel lamStar n) x| ^ 2)
          (Metric.ball x₀ (deGiorgiRadius n)) volume)
    (hpre :
      ∀ n,
        deGiorgiEnergySeq u x₀ lamStar (n + 1) ≤
          K / ((deGiorgiRadius n - deGiorgiRadius (n + 1)) ^ 2 *
            (deGiorgiLevel lamStar (n + 1) - deGiorgiLevel lamStar n) ^ (4 / (d : ℝ))) *
          deGiorgiEnergySeq u x₀ lamStar n ^ (1 + 2 / (d : ℝ)))
    (hheight :
      C_DeGiorgiSmallness d K *
        Real.sqrt (∫ x in Metric.ball x₀ 1, |max (u x) 0| ^ 2 ∂volume) ≤
          lamStar) :
    ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ (1 / 2 : ℝ))),
      max (u x) 0 ≤ lamStar := by
  have hI₀_nonneg :
      0 ≤ ∫ x in Metric.ball x₀ 1, |max (u x) 0| ^ 2 ∂volume := by
    refine integral_nonneg ?_
    intro x
    positivity
  have hsmall0 :
      ∫ x in Metric.ball x₀ 1, |max (u x) 0| ^ 2 ∂volume ≤
        (deGiorgiRecurrenceCoeff d K lamStar) ^ (-(1 : ℝ) / (2 / (d : ℝ))) *
          (deGiorgiRecurrenceBase d) ^ (-(1 : ℝ) / (2 / (d : ℝ)) ^ 2) :=
    deGiorgi_initial_energy_small_of_height_bound hK hLamStar hI₀_nonneg hheight
  exact linfty_subsolution_DeGiorgi_ae_of_unitBall_initial_energy_smallness
    hd hK hLamStar hposInt hStarInt hAint hpre hsmall0

/-- De Giorgi `L∞` bound for subsolutions on the unit ball.

The positive part is bounded almost everywhere on the half-ball by an explicit
coefficient-dependent constant times the `L²` size of `u₊` on `B₁`. The result
is stated as an a.e. bound rather than a pointwise supremum bound, since the
representative/continuity upgrade comes later in the theory. -/
theorem linfty_subsolution_DeGiorgi
    (hd : 2 < (d : ℝ))
    (A : EllipticCoeff d (Metric.ball (0 : E) 1))
    {u : E → ℝ}
    (hsub : IsSubsolution A u)
    (hposInt :
      IntegrableOn (fun x => |max (u x) 0| ^ 2)
        (Metric.ball (0 : E) 1) volume) :
    ∀ᵐ x ∂(volume.restrict (Metric.ball (0 : E) (1 / 2 : ℝ))),
      max (u x) 0 ≤
        C_DeGiorgi_subsolution d A *
          Real.sqrt (∫ x in Metric.ball (0 : E) 1, |max (u x) 0| ^ 2 ∂volume) := by
  let I₀ : ℝ := ∫ x in Metric.ball (0 : E) 1, |max (u x) 0| ^ 2 ∂volume
  have hI₀_nonneg : 0 ≤ I₀ := by
    dsimp [I₀]
    refine integral_nonneg ?_
    intro x
    positivity
  obtain ⟨hK, hiter⟩ :=
    deGiorgi_iteration_package_on_unitBall_of_subsolution (d := d) hd A hsub
  by_cases hI₀_zero : I₀ = 0
  · have hposInt_half :
        IntegrableOn (fun x => |max (u x) 0| ^ 2)
          (Metric.ball (0 : E) (1 / 2 : ℝ)) volume :=
      hposInt.mono_set (Metric.ball_subset_ball (by norm_num : (1 / 2 : ℝ) ≤ 1))
    have hnonneg : ∀ x, 0 ≤ |max (u x) 0| ^ 2 := by
      intro x
      positivity
    have hbound_half :
        ∀ n : ℕ,
          ∫ x in Metric.ball (0 : E) (1 / 2 : ℝ), |max (u x) 0| ^ 2 ∂volume ≤ (0 : ℝ) := by
      intro n
      calc
        ∫ x in Metric.ball (0 : E) (1 / 2 : ℝ), |max (u x) 0| ^ 2 ∂volume
            ≤ ∫ x in Metric.ball (0 : E) 1, |max (u x) 0| ^ 2 ∂volume := by
                exact setIntegral_mono_set hposInt (ae_of_all _ hnonneg)
                  (ae_of_all _ (Metric.ball_subset_ball (by norm_num : (1 / 2 : ℝ) ≤ 1)))
        _ = 0 := by
              simpa [I₀] using hI₀_zero
    have hzero_ae :
        ∀ᵐ x ∂(volume.restrict (Metric.ball (0 : E) (1 / 2 : ℝ))), max (u x) 0 = 0 := by
      refine ae_eq_zero_of_forall_setIntegral_sq_le_of_tendsto_zero hposInt_half hbound_half ?_
      exact (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0))
    filter_upwards [hzero_ae] with x hx
    have hrhs_zero :
        C_DeGiorgi_subsolution d A * Real.sqrt I₀ = 0 := by
      simp [I₀, hI₀_zero]
    rw [hrhs_zero]
    simp [hx]
  · have hI₀_pos : 0 < I₀ := lt_of_le_of_ne hI₀_nonneg (by simpa [eq_comm] using hI₀_zero)
    let lamStar : ℝ := C_DeGiorgi_subsolution d A * Real.sqrt I₀
    have hLamStar : 0 < lamStar := by
      dsimp [lamStar, I₀]
      exact deGiorgi_exact_height_threshold_on_unitBall
        (d := d) (K := K_DeGiorgi_subsolution d A) hK hI₀_pos
    obtain ⟨hStarInt, htail⟩ := hiter hLamStar
    obtain ⟨hAint, hpre⟩ := htail
    simpa [lamStar, I₀] using
      (linfty_subsolution_DeGiorgi_ae_of_unitBall_height_bound
        (d := d) (u := u) (x₀ := (0 : E)) (K := K_DeGiorgi_subsolution d A)
        (lamStar := lamStar) hd hK hLamStar hposInt hStarInt hAint hpre
        (by simp [lamStar, I₀, C_DeGiorgi_subsolution]))

/-- Existence of a threshold realizing the De Giorgi `L∞` estimate. -/
theorem linfty_subsolution_DeGiorgi_exists_threshold
    (hd : 2 < (d : ℝ))
    (A : EllipticCoeff d (Metric.ball (0 : E) 1))
    {u : E → ℝ}
    (hsub : IsSubsolution A u)
    (hposInt :
      IntegrableOn (fun x => |max (u x) 0| ^ 2)
        (Metric.ball (0 : E) 1) volume) :
    ∃ lamStar : ℝ,
      0 < lamStar ∧
      C_DeGiorgi_subsolution d A *
        Real.sqrt (∫ x in Metric.ball (0 : E) 1, |max (u x) 0| ^ 2 ∂volume) ≤
          lamStar ∧
      ∀ᵐ x ∂(volume.restrict (Metric.ball (0 : E) (1 / 2 : ℝ))),
        max (u x) 0 ≤ lamStar := by
  let I₀ : ℝ := ∫ x in Metric.ball (0 : E) 1, |max (u x) 0| ^ 2 ∂volume
  have hI₀_nonneg : 0 ≤ I₀ := by
    dsimp [I₀]
    refine integral_nonneg ?_
    intro x
    positivity
  have hbound := linfty_subsolution_DeGiorgi (d := d) hd A hsub hposInt
  by_cases hI₀_zero : I₀ = 0
  · refine ⟨1, by norm_num, ?_, ?_⟩
    · have hsmall_zero :
          C_DeGiorgi_subsolution d A * Real.sqrt I₀ = 0 := by
        simp [I₀, hI₀_zero]
      rw [hsmall_zero]
      norm_num
    · filter_upwards [hbound] with x hx
      have hsqrt_zero :
          Real.sqrt (∫ x in Metric.ball (0 : E) 1, |max (u x) 0| ^ 2 ∂volume) = 0 := by
        rw [show (∫ x in Metric.ball (0 : E) 1, |max (u x) 0| ^ 2 ∂volume) = I₀ by rfl, hI₀_zero]
        simp
      have hsmall_zero' :
          C_DeGiorgi_subsolution d A *
              Real.sqrt (∫ x in Metric.ball (0 : E) 1, |max (u x) 0| ^ 2 ∂volume) = 0 := by
        rw [hsqrt_zero]
        ring
      have hx_pair :
          u x ≤
              C_DeGiorgi_subsolution d A *
                Real.sqrt (∫ x in Metric.ball (0 : E) 1, |max (u x) 0| ^ 2 ∂volume) ∧
            0 ≤
              C_DeGiorgi_subsolution d A *
                Real.sqrt (∫ x in Metric.ball (0 : E) 1, |max (u x) 0| ^ 2 ∂volume) := by
        simpa using hx
      rw [hsmall_zero'] at hx_pair
      have hx_zero : max (u x) 0 ≤ 0 := by
        exact max_le_iff.mpr ⟨hx_pair.1, le_rfl⟩
      linarith
  · let lamStar : ℝ := C_DeGiorgi_subsolution d A * Real.sqrt I₀
    have hLamStar : 0 < lamStar := by
      have hI₀_pos : 0 < I₀ := lt_of_le_of_ne hI₀_nonneg (by simpa [eq_comm] using hI₀_zero)
      dsimp [lamStar, I₀]
      exact deGiorgi_exact_height_threshold_on_unitBall
        (d := d) (K := K_DeGiorgi_subsolution d A)
        (K_DeGiorgi_subsolution_pos (d := d) A) hI₀_pos
    refine ⟨lamStar, hLamStar, le_rfl, ?_⟩
    simpa [lamStar, I₀] using hbound

noncomputable def K_DeGiorgi_subsolution_normalized
    (d : ℕ) [NeZero d] : ℝ :=
  2 * (C_gns d 2) ^ 2 * (8 * (2 * (Mst : ℝ)) ^ 2) + 1

theorem K_DeGiorgi_subsolution_normalized_pos :
    0 < K_DeGiorgi_subsolution_normalized d := by
  rw [K_DeGiorgi_subsolution_normalized]
  positivity

noncomputable def C_DeGiorgi_subsolution_normalized
    (d : ℕ) [NeZero d] : ℝ :=
  C_DeGiorgiSmallness d (K_DeGiorgi_subsolution_normalized d)

theorem C_DeGiorgi_subsolution_le_normalized
    (A : NormalizedEllipticCoeff d (Metric.ball (0 : E) 1)) :
    C_DeGiorgi_subsolution d A.1 ≤
      C_DeGiorgi_subsolution_normalized d * A.1.Λ ^ ((d : ℝ) / 4) := by
  let c : ℝ := (C_gns d 2) ^ 2 * (8 * (2 * (Mst : ℝ)) ^ 2)
  have hc_nonneg : 0 ≤ c := by
    dsimp [c]
    positivity
  have hΛ_ge_one : 1 ≤ A.1.Λ := by
    simpa [A.2] using A.1.hΛ
  have hratio_eq : ellipticityRatio A.1 = A.1.Λ := by
    exact NormalizedEllipticCoeff.ellipticityRatio_eq_Λ (A := A)
  have hK_formula :
      K_DeGiorgi_subsolution d A.1 = c * (A.1.Λ + 1) + 1 := by
    rw [K_DeGiorgi_subsolution, hratio_eq]
    dsimp [c]
    ring
  have hK0_formula :
      K_DeGiorgi_subsolution_normalized d = 2 * c + 1 := by
    rw [K_DeGiorgi_subsolution_normalized]
    dsimp [c]
    ring
  have hK_le :
      K_DeGiorgi_subsolution d A.1 ≤
        K_DeGiorgi_subsolution_normalized d * A.1.Λ := by
    rw [hK_formula, hK0_formula]
    nlinarith
  have hmono :
      C_DeGiorgi_subsolution d A.1 ≤
        C_DeGiorgiSmallness d (K_DeGiorgi_subsolution_normalized d * A.1.Λ) := by
    rw [C_DeGiorgi_subsolution]
    exact C_DeGiorgiSmallness_mono (d := d)
      (K_DeGiorgi_subsolution_pos (d := d) A.1).le hK_le
  calc
    C_DeGiorgi_subsolution d A.1 ≤
        C_DeGiorgiSmallness d (K_DeGiorgi_subsolution_normalized d * A.1.Λ) := hmono
    _ = C_DeGiorgi_subsolution_normalized d * A.1.Λ ^ ((d : ℝ) / 4) := by
        rw [C_DeGiorgi_subsolution_normalized]
        exact C_DeGiorgiSmallness_mul_right (d := d)
          (K_DeGiorgi_subsolution_normalized_pos (d := d)).le A.1.Λ_nonneg

/-- Normalized-coefficient De Giorgi `L∞` bound with the explicit scaling
`C(d) * Λ^(d/4)` on the unit ball. -/
theorem linfty_subsolution_DeGiorgi_normalized
    (hd : 2 < (d : ℝ))
    (A : NormalizedEllipticCoeff d (Metric.ball (0 : E) 1))
    {u : E → ℝ}
    (hsub : IsSubsolution A.1 u)
    (hposInt :
      IntegrableOn (fun x => |max (u x) 0| ^ 2)
        (Metric.ball (0 : E) 1) volume) :
    ∀ᵐ x ∂(volume.restrict (Metric.ball (0 : E) (1 / 2 : ℝ))),
      max (u x) 0 ≤
        C_DeGiorgi_subsolution_normalized d *
          A.1.Λ ^ ((d : ℝ) / 4) *
          Real.sqrt (∫ x in Metric.ball (0 : E) 1, |max (u x) 0| ^ 2 ∂volume) := by
  let I₀ : ℝ := ∫ x in Metric.ball (0 : E) 1, |max (u x) 0| ^ 2 ∂volume
  have hsqrt_nonneg : 0 ≤ Real.sqrt I₀ := Real.sqrt_nonneg I₀
  have hconst :
      C_DeGiorgi_subsolution d A.1 * Real.sqrt I₀ ≤
        C_DeGiorgi_subsolution_normalized d *
          A.1.Λ ^ ((d : ℝ) / 4) * Real.sqrt I₀ :=
    mul_le_mul_of_nonneg_right
      (C_DeGiorgi_subsolution_le_normalized (d := d) A) hsqrt_nonneg
  filter_upwards [linfty_subsolution_DeGiorgi (d := d) hd A.1 hsub hposInt] with x hx
  exact le_trans hx hconst

end LinftyAssembly

end DeGiorgi
