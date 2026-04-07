import DeGiorgi.Holder.OscillationDecay

/-!
# Holder Representative

Construction of the Holder representative and the large/small distance bounds.
-/

noncomputable section

open MeasureTheory Filter

namespace DeGiorgi

variable {d : ℕ} [NeZero d]

local notation "E" => AmbientSpace d
local notation "μ1" => volume.restrict (Metric.ball (0 : E) 1)
local notation "μhalf" => volume.restrict (Metric.ball (0 : E) (1 / 2 : ℝ))

theorem solution_integrableOn_unitBall
    (A : NormalizedEllipticCoeff d (Metric.ball (0 : E) 1))
    {u : E → ℝ} (hsol : IsSolution A.1 u) :
    IntegrableOn u (Metric.ball (0 : E) 1) volume := by
  letI : IsFiniteMeasure (volume.restrict (Metric.ball (0 : E) 1)) := by
    refine ⟨?_⟩
    simpa [Measure.restrict_apply, measurableSet_ball] using
      (measure_ball_lt_top (μ := volume) (x := (0 : E)) (r := (1 : ℝ)))
  let hu : MemW1pWitness 2 u (Metric.ball (0 : E) 1) := MemW1p.someWitness hsol.1.1
  have hp : (1 : ENNReal) ≤ 2 := by norm_num
  simpa [IntegrableOn] using hu.memLp.integrable hp

omit [NeZero d] in
theorem ballAverage_mem_Icc_of_ae_bounds
    {u : E → ℝ} {c : E} {r m M : ℝ}
    (hr : 0 < r)
    (hu_int : IntegrableOn u (Metric.ball c r) volume)
    (hm : ∀ᵐ z ∂ ballMeasure c r, m ≤ u z)
    (hM : ∀ᵐ z ∂ ballMeasure c r, u z ≤ M) :
    m ≤ ⨍ z in Metric.ball c r, u z ∂volume ∧
      ⨍ z in Metric.ball c r, u z ∂volume ≤ M := by
  have hmem : ∀ᵐ z ∂ ballMeasure c r, u z ∈ Set.Icc m M := by
    filter_upwards [hm, hM] with z hmz hMz
    exact ⟨hmz, hMz⟩
  have havg :
      (⨍ z in Metric.ball c r, u z ∂volume) ∈ Set.Icc m M := by
    refine Convex.set_average_mem (hs := convex_Icc m M) isClosed_Icc ?_ ?_ hmem hu_int
    · simpa [ballMeasure] using restrict_ball_ne_zero (c := c) (r := r) hr
    · simpa using (measure_ball_lt_top (μ := volume) (x := c) (r := r)).ne
  exact havg

omit [NeZero d] in
theorem moserDyadicAverage_eq
    (u : E → ℝ) (x : E) (n : ℕ) :
    dyadicBallAverage u x (1 / 4 : ℝ) n =
      ⨍ z in Metric.ball x (moserDyadicRadius n), u z ∂volume := by
  simp [dyadicBallAverage, moserDyadicRadius, div_eq_mul_inv]

theorem moserDyadicRadius_antitone
    {m n : ℕ} (hmn : m ≤ n) :
    moserDyadicRadius n ≤ moserDyadicRadius m := by
  rw [moserDyadicRadius_eq_half_pow, moserDyadicRadius_eq_half_pow]
  have hpow : (2 : ℝ) ^ m ≤ (2 : ℝ) ^ n := by
    exact pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hmn
  have hm_pos : 0 < (2 : ℝ) ^ m := by positivity
  have hn_pos : 0 < (2 : ℝ) ^ n := by positivity
  have hinv : ((2 : ℝ) ^ n)⁻¹ ≤ ((2 : ℝ) ^ m)⁻¹ := by
    exact (inv_le_inv₀ hn_pos hm_pos).2 hpow
  have hquarter_nonneg : 0 ≤ (1 / 4 : ℝ) := by norm_num
  exact mul_le_mul_of_nonneg_left (by simpa [one_div, inv_pow] using hinv) hquarter_nonneg

theorem dyadicBallAverage_mem_moserEssInterval_of_le
    (hd : 2 < (d : ℝ))
    (A : NormalizedEllipticCoeff d (Metric.ball (0 : E) 1))
    {u : E → ℝ} {p₀ : ℝ} (hp₀ : 1 < p₀)
    (hsol : IsSolution A.1 u)
    (hInt : IntegrableOn (fun z => |u z| ^ p₀) (Metric.ball (0 : E) 1) volume)
    {x : E} (hx : x ∈ Metric.ball (0 : E) (1 / 2 : ℝ))
    {n k : ℕ} (hnk : n ≤ k) :
    moserDyadicEssInf u x n ≤ dyadicBallAverage u x (1 / 4 : ℝ) k ∧
      dyadicBallAverage u x (1 / 4 : ℝ) k ≤ moserDyadicEssSup u x n := by
  have hsub :
      Metric.ball x (moserDyadicRadius k) ⊆ Metric.ball x (moserDyadicRadius n) := by
    exact Metric.ball_subset_ball (moserDyadicRadius_antitone hnk)
  have hu_bound :
      ∀ᵐ z ∂ ballMeasure x (moserDyadicRadius n),
        |u z| ≤ (C_holder_Moser d / 64) * moserHolderNorm A u p₀ := by
    exact
      ae_abs_le_moserHolderNorm_on_smallBall
        (d := d) hd A hp₀ hsol hInt hx
        (r := moserDyadicRadius n)
        (moserDyadicRadius_pos (n := n))
        (moserDyadicRadius_le_quarter (n := n))
  have hu_upper :
      ∀ᵐ z ∂ ballMeasure x (moserDyadicRadius n),
        u z ≤ (C_holder_Moser d / 64) * moserHolderNorm A u p₀ :=
    ae_upper_of_ae_abs_le hu_bound
  have hu_lower :
      ∀ᵐ z ∂ ballMeasure x (moserDyadicRadius n),
        -((C_holder_Moser d / 64) * moserHolderNorm A u p₀) ≤ u z :=
    ae_lower_of_ae_abs_le hu_bound
  have hu_bdd_below :
      Filter.IsBoundedUnder (· ≥ ·) (ae (ballMeasure x (moserDyadicRadius n))) u :=
    ⟨-((C_holder_Moser d / 64) * moserHolderNorm A u p₀), hu_lower⟩
  have hu_bdd_above :
      Filter.IsBoundedUnder (· ≤ ·) (ae (ballMeasure x (moserDyadicRadius n))) u :=
    ⟨(C_holder_Moser d / 64) * moserHolderNorm A u p₀, hu_upper⟩
  have hm_outer :
      ∀ᵐ z ∂ ballMeasure x (moserDyadicRadius n), moserDyadicEssInf u x n ≤ u z := by
    simpa [moserDyadicEssInf] using
      (ae_essInf_le (μ := ballMeasure x (moserDyadicRadius n)) (f := u) (hf := hu_bdd_below))
  have hM_outer :
      ∀ᵐ z ∂ ballMeasure x (moserDyadicRadius n), u z ≤ moserDyadicEssSup u x n := by
    simpa [moserDyadicEssSup] using
      (ae_le_essSup (μ := ballMeasure x (moserDyadicRadius n)) (f := u) (hf := hu_bdd_above))
  have hm_inner :
      ∀ᵐ z ∂ ballMeasure x (moserDyadicRadius k), moserDyadicEssInf u x n ≤ u z :=
    ae_restrict_of_ae_restrict_of_subset hsub hm_outer
  have hM_inner :
      ∀ᵐ z ∂ ballMeasure x (moserDyadicRadius k), u z ≤ moserDyadicEssSup u x n :=
    ae_restrict_of_ae_restrict_of_subset hsub hM_outer
  have hu_int_unit : IntegrableOn u (Metric.ball (0 : E) 1) volume :=
    solution_integrableOn_unitBall (d := d) A hsol
  have hu_int_k : IntegrableOn u (Metric.ball x (moserDyadicRadius k)) volume := by
    refine hu_int_unit.mono_set ?_
    exact smallBall_subset_unitBall hx (moserDyadicRadius_le_quarter (n := k))
  rw [moserDyadicAverage_eq]
  exact
    (ballAverage_mem_Icc_of_ae_bounds
      (d := d) (u := u) (c := x) (r := moserDyadicRadius k)
      (m := moserDyadicEssInf u x n) (M := moserDyadicEssSup u x n)
      (moserDyadicRadius_pos (n := k)) hu_int_k hm_inner hM_inner)

theorem moserDyadicAverage_step_le_geometric
    (hd : 2 < (d : ℝ))
    (A : NormalizedEllipticCoeff d (Metric.ball (0 : E) 1))
    {u : E → ℝ} {p₀ : ℝ} (hp₀ : 1 < p₀)
    (hsol : IsSolution A.1 u)
    (hInt : IntegrableOn (fun z => |u z| ^ p₀) (Metric.ball (0 : E) 1) volume)
    {x : E} (hx : x ∈ Metric.ball (0 : E) (1 / 2 : ℝ))
    (n : ℕ) :
    dist (dyadicBallAverage u x (1 / 4 : ℝ) n)
        (dyadicBallAverage u x (1 / 4 : ℝ) (n + 1))
      ≤ (1 - moserDecayAlpha A) ^ n *
          ((C_holder_Moser d / 32) * moserHolderNorm A u p₀) := by
  rcases
      dyadicBallAverage_mem_moserEssInterval_of_le
        (d := d) hd A hp₀ hsol hInt hx (n := n) (k := n) le_rfl with
    ⟨hn_lo, hn_hi⟩
  rcases
      dyadicBallAverage_mem_moserEssInterval_of_le
        (d := d) hd A hp₀ hsol hInt hx (n := n) (k := n + 1) (Nat.le_succ n) with
    ⟨hs_lo, hs_hi⟩
  have hinterval :
      |dyadicBallAverage u x (1 / 4 : ℝ) n -
          dyadicBallAverage u x (1 / 4 : ℝ) (n + 1)| ≤
        moserDyadicEssSup u x n - moserDyadicEssInf u x n := by
    have hup :
        dyadicBallAverage u x (1 / 4 : ℝ) n -
            dyadicBallAverage u x (1 / 4 : ℝ) (n + 1) ≤
          moserDyadicEssSup u x n - moserDyadicEssInf u x n := by
      linarith
    have hlo :
        -(moserDyadicEssSup u x n - moserDyadicEssInf u x n) ≤
          dyadicBallAverage u x (1 / 4 : ℝ) n -
            dyadicBallAverage u x (1 / 4 : ℝ) (n + 1) := by
      linarith
    exact abs_le.mpr ⟨hlo, hup⟩
  have hosc :
      moserDyadicEssSup u x n - moserDyadicEssInf u x n ≤
        (1 - moserDecayAlpha A) ^ n *
          ((C_holder_Moser d / 32) * moserHolderNorm A u p₀) := by
    exact moserDyadic_oscillation_bound (d := d) hd A hp₀ hsol hInt hx n
  simpa [Real.dist_eq] using le_trans hinterval hosc

theorem moserDyadicAverage_cauchy
    (hd : 2 < (d : ℝ))
    (A : NormalizedEllipticCoeff d (Metric.ball (0 : E) 1))
    {u : E → ℝ} {p₀ : ℝ} (hp₀ : 1 < p₀)
    (hsol : IsSolution A.1 u)
    (hInt : IntegrableOn (fun z => |u z| ^ p₀) (Metric.ball (0 : E) 1) volume)
    {x : E} (hx : x ∈ Metric.ball (0 : E) (1 / 2 : ℝ)) :
    CauchySeq (dyadicBallAverage u x (1 / 4 : ℝ)) := by
  have hratio_lt : 1 - moserDecayAlpha A < 1 := by
    linarith [moserDecayAlpha_pos (d := d) A]
  exact
    cauchySeq_of_le_geometric
      (r := 1 - moserDecayAlpha A)
      (C := (C_holder_Moser d / 32) * moserHolderNorm A u p₀)
      hratio_lt
      (by
        intro n
        simpa [mul_assoc, mul_left_comm, mul_comm] using
          (moserDyadicAverage_step_le_geometric
            (d := d) hd A hp₀ hsol hInt hx n))

theorem tendsto_moserDyadicAverageLimit
    (hd : 2 < (d : ℝ))
    (A : NormalizedEllipticCoeff d (Metric.ball (0 : E) 1))
    {u : E → ℝ} {p₀ : ℝ} (hp₀ : 1 < p₀)
    (hsol : IsSolution A.1 u)
    (hInt : IntegrableOn (fun z => |u z| ^ p₀) (Metric.ball (0 : E) 1) volume)
    {x : E} (hx : x ∈ Metric.ball (0 : E) (1 / 2 : ℝ)) :
    Tendsto (dyadicBallAverage u x (1 / 4 : ℝ)) atTop
      (nhds (dyadicBallAverageLimit u x (1 / 4 : ℝ))) := by
  simpa [dyadicBallAverageLimit] using
    (moserDyadicAverage_cauchy (d := d) hd A hp₀ hsol hInt hx).tendsto_limUnder

omit [NeZero d] in
theorem ball_subset_ball_of_dist_add_lt
    {c y : E} {r ρ : ℝ}
    (h : dist y c + ρ < r) :
    Metric.ball y ρ ⊆ Metric.ball c r := by
  intro z hz
  refine Metric.mem_ball.2 ?_
  have hz' : dist z y < ρ := by simpa using hz
  calc
    dist z c ≤ dist z y + dist y c := dist_triangle _ _ _
    _ < ρ + dist y c := by linarith
    _ = dist y c + ρ := by ring
    _ < r := h

noncomputable def moserRepresentative
    (u : E → ℝ) : E → ℝ := by
  classical
  exact fun x =>
    if x ∈ Metric.ball (0 : E) (1 / 2 : ℝ) then
      dyadicBallAverageLimit u x (1 / 4 : ℝ)
    else
      u x

theorem moserRepresentative_mem_essInterval_on_smallBall
    (hd : 2 < (d : ℝ))
    (A : NormalizedEllipticCoeff d (Metric.ball (0 : E) 1))
    {u : E → ℝ} {p₀ : ℝ} (hp₀ : 1 < p₀)
    (hsol : IsSolution A.1 u)
    (hInt : IntegrableOn (fun z => |u z| ^ p₀) (Metric.ball (0 : E) 1) volume)
    {c y : E} (hc : c ∈ Metric.ball (0 : E) (1 / 2 : ℝ))
    {r : ℝ} (hr : 0 < r) (hrq : r ≤ (1 / 4 : ℝ))
    (hy_half : y ∈ Metric.ball (0 : E) (1 / 2 : ℝ))
    (hy_ball : y ∈ Metric.ball c r) :
    essInf u (ballMeasure c r) ≤ dyadicBallAverageLimit u y (1 / 4 : ℝ) ∧
      dyadicBallAverageLimit u y (1 / 4 : ℝ) ≤ essSup u (ballMeasure c r) := by
  have hydist : dist y c < r := by
    simpa [dist_eq_norm, norm_sub_rev] using hy_ball
  let δ : ℝ := r - dist y c
  have hδ_pos : 0 < δ := by
    dsimp [δ]
    linarith
  have hδ_le : δ ≤ (1 / 4 : ℝ) := by
    dsimp [δ]
    have hdist_nonneg : 0 ≤ dist y c := dist_nonneg
    linarith
  rcases exists_moserDyadicRadius_near hδ_pos hδ_le with ⟨n, hn_lt, hn_le⟩
  let N : ℕ := n + 1
  let I : Set ℝ := Set.Icc (essInf u (ballMeasure c r)) (essSup u (ballMeasure c r))
  have hclosed : IsClosed I := isClosed_Icc
  have hu_bound :
      ∀ᵐ z ∂ ballMeasure c r, |u z| ≤ (C_holder_Moser d / 64) * moserHolderNorm A u p₀ := by
    exact
      ae_abs_le_moserHolderNorm_on_smallBall
        (d := d) hd A hp₀ hsol hInt hc (r := r) hr hrq
  have hu_upper :
      ∀ᵐ z ∂ ballMeasure c r, u z ≤ (C_holder_Moser d / 64) * moserHolderNorm A u p₀ :=
    ae_upper_of_ae_abs_le hu_bound
  have hu_lower :
      ∀ᵐ z ∂ ballMeasure c r, -((C_holder_Moser d / 64) * moserHolderNorm A u p₀) ≤ u z :=
    ae_lower_of_ae_abs_le hu_bound
  have hu_bdd_below : Filter.IsBoundedUnder (· ≥ ·) (ae (ballMeasure c r)) u :=
    ⟨-((C_holder_Moser d / 64) * moserHolderNorm A u p₀), hu_lower⟩
  have hu_bdd_above : Filter.IsBoundedUnder (· ≤ ·) (ae (ballMeasure c r)) u :=
    ⟨(C_holder_Moser d / 64) * moserHolderNorm A u p₀, hu_upper⟩
  have hm_outer :
      ∀ᵐ z ∂ ballMeasure c r, essInf u (ballMeasure c r) ≤ u z := by
    exact ae_essInf_le (μ := ballMeasure c r) (f := u) (hf := hu_bdd_below)
  have hM_outer :
      ∀ᵐ z ∂ ballMeasure c r, u z ≤ essSup u (ballMeasure c r) := by
    exact ae_le_essSup (μ := ballMeasure c r) (f := u) (hf := hu_bdd_above)
  have htail :
      ∀ᶠ k in atTop, dyadicBallAverage u y (1 / 4 : ℝ) k ∈ I := by
    refine (Filter.eventually_ge_atTop N).mono ?_
    intro k hk
    have hrk_le : moserDyadicRadius k ≤ moserDyadicRadius N :=
      moserDyadicRadius_antitone hk
    have hrk_lt : moserDyadicRadius k < δ := by
      exact lt_of_le_of_lt hrk_le hn_lt
    have hsub : Metric.ball y (moserDyadicRadius k) ⊆ Metric.ball c r := by
      have hsum : dist y c + moserDyadicRadius k < r := by
        dsimp [δ] at hrk_lt
        linarith
      exact ball_subset_ball_of_dist_add_lt hsum
    have hu_int_unit : IntegrableOn u (Metric.ball (0 : E) 1) volume :=
      solution_integrableOn_unitBall (d := d) A hsol
    have hu_int_k : IntegrableOn u (Metric.ball y (moserDyadicRadius k)) volume := by
      refine hu_int_unit.mono_set ?_
      exact smallBall_subset_unitBall hy_half (moserDyadicRadius_le_quarter (n := k))
    have hm_inner :
        ∀ᵐ z ∂ ballMeasure y (moserDyadicRadius k), essInf u (ballMeasure c r) ≤ u z :=
      ae_restrict_of_ae_restrict_of_subset hsub hm_outer
    have hM_inner :
        ∀ᵐ z ∂ ballMeasure y (moserDyadicRadius k), u z ≤ essSup u (ballMeasure c r) :=
      ae_restrict_of_ae_restrict_of_subset hsub hM_outer
    have hmem :
        dyadicBallAverage u y (1 / 4 : ℝ) k ∈ I := by
      rw [moserDyadicAverage_eq]
      exact
        (ballAverage_mem_Icc_of_ae_bounds
          (d := d) (u := u) (c := y) (r := moserDyadicRadius k)
          (m := essInf u (ballMeasure c r)) (M := essSup u (ballMeasure c r))
          (moserDyadicRadius_pos (n := k)) hu_int_k hm_inner hM_inner)
    exact hmem
  have hlim :
      dyadicBallAverageLimit u y (1 / 4 : ℝ) ∈ I := by
    exact hclosed.mem_of_tendsto
      (tendsto_moserDyadicAverageLimit (d := d) hd A hp₀ hsol hInt hy_half) htail
  exact hlim

theorem moserRepresentative_ae_eq
    (hd : 2 < (d : ℝ))
    (A : NormalizedEllipticCoeff d (Metric.ball (0 : E) 1))
    {u : E → ℝ} {p₀ : ℝ} (hp₀ : 1 < p₀)
    (hsol : IsSolution A.1 u)
    (hInt : IntegrableOn (fun z => |u z| ^ p₀) (Metric.ball (0 : E) 1) volume) :
    moserRepresentative u =ᵐ[μ1] u := by
  classical
  let outer : Set E := Metric.ball (0 : E) 1
  let inner : Set E := Metric.ball (0 : E) (1 / 2 : ℝ)
  let ρ : ℝ := (1 / 4 : ℝ)
  let f : E → ℝ := outer.indicator u
  have hρ : 0 < ρ := by norm_num [ρ]
  have houter_int : IntegrableOn u outer volume :=
    solution_integrableOn_unitBall (d := d) A hsol
  have hf_int : Integrable f volume := houter_int.integrable_indicator measurableSet_ball
  have hdiff_ae :
      ∀ᵐ x ∂volume,
        Tendsto (fun n : ℕ => ⨍ y in Metric.closedBall x (ρ / (2 : ℝ) ^ n), f y ∂volume)
          atTop (nhds (f x)) := by
    filter_upwards
        [((IsUnifLocDoublingMeasure.vitaliFamily (μ := volume) (K := 0)).ae_tendsto_average
          hf_int.locallyIntegrable)] with x hdx
    exact Tendsto.comp hdx <|
      IsUnifLocDoublingMeasure.tendsto_closedBall_filterAt (μ := volume) (K := 0)
        (fun _ : ℕ => x) (fun n : ℕ => ρ / (2 : ℝ) ^ n)
        (tendsto_dyadic_radius_nhdsWithin_zero hρ)
        (Eventually.of_forall fun n => by
          exact Metric.mem_closedBall_self (x := x) (by positivity))
  have hinner_eq_ae :
      ∀ᵐ x ∂volume.restrict inner, dyadicBallAverageLimit u x ρ = u x := by
    rw [ae_restrict_iff' measurableSet_ball]
    filter_upwards [hdiff_ae] with x hdx hx_inner
    have hx_outer : x ∈ outer := by
      exact Metric.ball_subset_ball (by norm_num : (1 / 2 : ℝ) ≤ 1) hx_inner
    have hx_closed : x ∈ Metric.closedBall (0 : E) (1 / 2 : ℝ) := by
      exact Metric.mem_closedBall.2 (le_of_lt (by simpa using hx_inner))
    have hlimit_u :
        Tendsto (dyadicBallAverage u x ρ) atTop (nhds (dyadicBallAverageLimit u x ρ)) :=
      tendsto_moserDyadicAverageLimit (d := d) hd A hp₀ hsol hInt hx_inner
    have hclosed_to_u :
        Tendsto (fun n : ℕ => ⨍ y in Metric.closedBall x (ρ / (2 : ℝ) ^ n), f y ∂volume)
          atTop (nhds (u x)) := by
      simpa [f, outer, hx_outer] using hdx
    have hclosed_eq :
        (fun n : ℕ => ⨍ y in Metric.closedBall x (ρ / (2 : ℝ) ^ n), f y ∂volume)
          =ᶠ[atTop] dyadicBallAverage u x ρ := by
      refine Eventually.of_forall fun n => ?_
      have hrn_nonneg : 0 ≤ ρ / (2 : ℝ) ^ n := by positivity
      have hrn_quarter : ρ / (2 : ℝ) ^ n ≤ (1 / 4 : ℝ) := by
        calc
          ρ / (2 : ℝ) ^ n ≤ ρ := by
            exact div_le_self hρ.le (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))
          _ = (1 / 4 : ℝ) := by rfl
      have hclosedsub :
          Metric.closedBall x (ρ / (2 : ℝ) ^ n) ⊆ outer :=
        closedBall_subset_unitBall_of_mem_closedBall_half hx_closed hrn_nonneg hrn_quarter
      calc
        ⨍ y in Metric.closedBall x (ρ / (2 : ℝ) ^ n), f y ∂volume
            = ⨍ y in Metric.closedBall x (ρ / (2 : ℝ) ^ n), u y ∂volume := by
                apply MeasureTheory.setAverage_congr_fun Metric.isClosed_closedBall.measurableSet
                exact Eventually.of_forall fun z hz => by
                  simp [f, outer, hclosedsub hz]
        _ = ⨍ y in Metric.ball x (ρ / (2 : ℝ) ^ n), u y ∂volume := by
              exact setAverage_closedBall_eq_ball_of_pos x (by positivity)
        _ = dyadicBallAverage u x ρ n := by
              simp [dyadicBallAverage]
    have hdyad_to_u :
        Tendsto (dyadicBallAverage u x ρ) atTop (nhds (u x)) :=
      Tendsto.congr' hclosed_eq hclosed_to_u
    exact tendsto_nhds_unique hlimit_u hdyad_to_u
  show ∀ᵐ x ∂ volume.restrict outer, moserRepresentative u x = u x
  rw [ae_restrict_iff' measurableSet_ball] at hinner_eq_ae
  rw [ae_restrict_iff' measurableSet_ball]
  filter_upwards [hinner_eq_ae] with x hx hx_outer
  by_cases hx_half : x ∈ inner
  · unfold moserRepresentative
    rw [if_pos hx_half]
    exact hx hx_half
  · unfold moserRepresentative
    rw [if_neg hx_half]

theorem pointwise_abs_le_moserRepresentative_on_halfBall
    (hd : 2 < (d : ℝ))
    (A : NormalizedEllipticCoeff d (Metric.ball (0 : E) 1))
    {u : E → ℝ} {p₀ : ℝ} (hp₀ : 1 < p₀)
    (hsol : IsSolution A.1 u)
    (hInt : IntegrableOn (fun z => |u z| ^ p₀) (Metric.ball (0 : E) 1) volume)
    {x : E} (hx : x ∈ Metric.ball (0 : E) (1 / 2 : ℝ)) :
    |moserRepresentative u x| ≤ (C_holder_Moser d / 64) * moserHolderNorm A u p₀ := by
  have hx_int :
      moserDyadicEssInf u x 0 ≤ dyadicBallAverageLimit u x (1 / 4 : ℝ) ∧
        dyadicBallAverageLimit u x (1 / 4 : ℝ) ≤ moserDyadicEssSup u x 0 := by
    simpa [moserDyadicEssInf, moserDyadicEssSup, ballMeasure, moserDyadicRadius] using
      (moserRepresentative_mem_essInterval_on_smallBall
        (d := d) hd A hp₀ hsol hInt hx
        (r := (1 / 4 : ℝ)) (by norm_num) (by norm_num) hx
        (Metric.mem_ball_self (by norm_num : 0 < (1 / 4 : ℝ))))
  have hae :
      ∀ᵐ z ∂ ballMeasure x (1 / 4 : ℝ),
        |u z| ≤ (C_holder_Moser d / 64) * moserHolderNorm A u p₀ :=
    ae_abs_le_moserHolderNorm_on_quarterBall
      (d := d) hd A hp₀ hsol hInt hx
  have hupper :
      ∀ᵐ z ∂ ballMeasure x (1 / 4 : ℝ),
        u z ≤ (C_holder_Moser d / 64) * moserHolderNorm A u p₀ :=
    ae_upper_of_ae_abs_le hae
  have hlower :
      ∀ᵐ z ∂ ballMeasure x (1 / 4 : ℝ),
        -((C_holder_Moser d / 64) * moserHolderNorm A u p₀) ≤ u z :=
    ae_lower_of_ae_abs_le hae
  have hsup :
      moserDyadicEssSup u x 0 ≤
        (C_holder_Moser d / 64) * moserHolderNorm A u p₀ := by
    simpa [moserDyadicEssSup, ballMeasure, moserDyadicRadius] using
      (essSup_le_of_ae_bdd
        (μ := ballMeasure x (1 / 4 : ℝ))
        (restrict_ball_ne_zero (c := x) (r := (1 / 4 : ℝ)) (by norm_num))
        hlower hupper)
  have hinf :
      -((C_holder_Moser d / 64) * moserHolderNorm A u p₀) ≤ moserDyadicEssInf u x 0 := by
    simpa [moserDyadicEssInf, ballMeasure, moserDyadicRadius] using
      (le_essInf_of_ae_bdd
        (μ := ballMeasure x (1 / 4 : ℝ))
        (restrict_ball_ne_zero (c := x) (r := (1 / 4 : ℝ)) (by norm_num))
        hlower hupper)
  rcases hx_int with ⟨hx_lo, hx_hi⟩
  have hle :
      moserRepresentative u x ≤ (C_holder_Moser d / 64) * moserHolderNorm A u p₀ := by
    have hvx : moserRepresentative u x = dyadicBallAverageLimit u x (1 / 4 : ℝ) := by
      unfold moserRepresentative
      rw [if_pos hx]
    rw [hvx]
    exact le_trans hx_hi hsup
  have hge :
      -((C_holder_Moser d / 64) * moserHolderNorm A u p₀) ≤ moserRepresentative u x := by
    have hvx : moserRepresentative u x = dyadicBallAverageLimit u x (1 / 4 : ℝ) := by
      unfold moserRepresentative
      rw [if_pos hx]
    rw [hvx]
    exact le_trans hinf hx_lo
  exact abs_le.mpr ⟨hge, hle⟩

theorem moserRepresentative_large_distance_bound
    (hd : 2 < (d : ℝ))
    (A : NormalizedEllipticCoeff d (Metric.ball (0 : E) 1))
    {u : E → ℝ} {p₀ : ℝ} (hp₀ : 1 < p₀)
    (hsol : IsSolution A.1 u)
    (hInt : IntegrableOn (fun z => |u z| ^ p₀) (Metric.ball (0 : E) 1) volume)
    {x y : E}
    (hx : x ∈ Metric.ball (0 : E) (1 / 2 : ℝ))
    (hy : y ∈ Metric.ball (0 : E) (1 / 2 : ℝ))
    (_hxy_ne : x ≠ y)
    (hlarge : (1 / 8 : ℝ) ≤ ‖x - y‖) :
    |moserRepresentative u x - moserRepresentative u y| ≤
      C_holder_Moser d * moserHolderNorm A u p₀ * ‖x - y‖ ^ moserDecayAlpha A := by
  let α : ℝ := moserDecayAlpha A
  let N : ℝ := moserHolderNorm A u p₀
  have hα_le : α ≤ 1 := by
    simpa [α] using moserDecayAlpha_le_one (d := d) hd A
  have hN_nonneg : 0 ≤ N := by
    simpa [N] using moserHolderNorm_nonneg (d := d) A hp₀
  have hC_nonneg : 0 ≤ C_holder_Moser d := by
    exact le_trans (C_harnack_nonneg (d := d) hd) (C_harnack_le_C_holder_Moser (d := d))
  have hx_abs :
      |moserRepresentative u x| ≤ (C_holder_Moser d / 64) * N := by
    simpa [N] using
      (pointwise_abs_le_moserRepresentative_on_halfBall
        (d := d) hd A hp₀ hsol hInt hx)
  have hy_abs :
      |moserRepresentative u y| ≤ (C_holder_Moser d / 64) * N := by
    simpa [N] using
      (pointwise_abs_le_moserRepresentative_on_halfBall
        (d := d) hd A hp₀ hsol hInt hy)
  have htri : |moserRepresentative u x - moserRepresentative u y|
      ≤ |moserRepresentative u x| + |moserRepresentative u y| := by
    simpa [sub_eq_add_neg, abs_neg] using
      abs_add_le (moserRepresentative u x) (-moserRepresentative u y)
  have hdist_nonneg : 0 ≤ ‖x - y‖ := norm_nonneg _
  have hdist_le_one : ‖x - y‖ ≤ 1 := by
    have hx0 : dist x (0 : E) < 1 / 2 := by simpa using hx
    have hy0 : dist y (0 : E) < 1 / 2 := by simpa using hy
    have hdist_lt : dist x y < 1 := by
      calc
        dist x y ≤ dist x (0 : E) + dist y (0 : E) := by
          simpa [dist_comm] using (dist_triangle x (0 : E) y)
        _ < 1 / 2 + 1 / 2 := by linarith
        _ = 1 := by norm_num
    simpa [dist_eq_norm] using le_of_lt hdist_lt
  have hpow_lower : (1 / 8 : ℝ) ≤ ‖x - y‖ ^ α := by
    have hself :
        ‖x - y‖ ≤ ‖x - y‖ ^ α :=
      Real.self_le_rpow_of_le_one hdist_nonneg hdist_le_one hα_le
    linarith
  have hsum :
      |moserRepresentative u x| + |moserRepresentative u y| ≤
        (C_holder_Moser d / 32) * N := by
    nlinarith
  have hbig :
      (C_holder_Moser d / 32) * N ≤
        C_holder_Moser d * N * ‖x - y‖ ^ α := by
    have hone32 : (1 / 32 : ℝ) ≤ ‖x - y‖ ^ α := by
      linarith [hpow_lower]
    have hCN_nonneg : 0 ≤ C_holder_Moser d * N := mul_nonneg hC_nonneg hN_nonneg
    have hscaled := mul_le_mul_of_nonneg_left hone32 hCN_nonneg
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hscaled
  have hfinal :
      |moserRepresentative u x - moserRepresentative u y|
        ≤ C_holder_Moser d * N * ‖x - y‖ ^ α := by
    exact le_trans htri (le_trans hsum hbig)
  simpa [N, α] using hfinal

theorem moserRepresentative_small_distance_bound
    (hd : 2 < (d : ℝ))
    (A : NormalizedEllipticCoeff d (Metric.ball (0 : E) 1))
    {u : E → ℝ} {p₀ : ℝ} (hp₀ : 1 < p₀)
    (hsol : IsSolution A.1 u)
    (hInt : IntegrableOn (fun z => |u z| ^ p₀) (Metric.ball (0 : E) 1) volume)
    {x y : E}
    (hx : x ∈ Metric.ball (0 : E) (1 / 2 : ℝ))
    (hy : y ∈ Metric.ball (0 : E) (1 / 2 : ℝ))
    (hxy_ne : x ≠ y)
    (hsmall : ‖x - y‖ < (1 / 8 : ℝ)) :
    |moserRepresentative u x - moserRepresentative u y| ≤
      C_holder_Moser d * moserHolderNorm A u p₀ * ‖x - y‖ ^ moserDecayAlpha A := by
  let α : ℝ := moserDecayAlpha A
  let N : ℝ := moserHolderNorm A u p₀
  have hα_pos : 0 < α := by
    simpa [α] using moserDecayAlpha_pos (d := d) A
  have hα_nonneg : 0 ≤ α := hα_pos.le
  have hα_le : α ≤ 1 := by
    simpa [α] using moserDecayAlpha_le_one (d := d) hd A
  have hN_nonneg : 0 ≤ N := by
    simpa [N] using moserHolderNorm_nonneg (d := d) A hp₀
  have hC_nonneg : 0 ≤ C_holder_Moser d := by
    exact le_trans (C_harnack_nonneg (d := d) hd) (C_harnack_le_C_holder_Moser (d := d))
  have hdist_pos : 0 < ‖x - y‖ := by
    exact norm_pos_iff.mpr (sub_ne_zero.mpr hxy_ne)
  rcases exists_moserDyadicRadius_near
      hdist_pos (by linarith : ‖x - y‖ ≤ (1 / 4 : ℝ)) with
    ⟨n, hn_lower, hn_upper⟩
  have hdist_lt_r1 : ‖x - y‖ < moserDyadicRadius 1 := by
    change ‖x - y‖ < (1 / 4 : ℝ) / (2 : ℝ) ^ (1 : ℕ)
    norm_num [moserDyadicRadius] at hsmall ⊢
    exact hsmall
  cases n with
  | zero =>
      exfalso
      exact (not_lt_of_ge (le_of_lt hdist_lt_r1)) hn_lower
  | succ m =>
      have hy_ball : y ∈ Metric.ball x (moserDyadicRadius m) := by
        refine Metric.mem_ball.2 ?_
        have hrad_lt : moserDyadicRadius (m + 1) < moserDyadicRadius m := by
          rw [moserDyadicRadius_succ]
          nlinarith [moserDyadicRadius_pos (n := m)]
        have hxy_lt : ‖x - y‖ < moserDyadicRadius m :=
          lt_of_le_of_lt hn_upper hrad_lt
        simpa [dist_eq_norm, norm_sub_rev] using hxy_lt
      have hx_int :
          moserDyadicEssInf u x m ≤ dyadicBallAverageLimit u x (1 / 4 : ℝ) ∧
            dyadicBallAverageLimit u x (1 / 4 : ℝ) ≤ moserDyadicEssSup u x m := by
        simpa [moserDyadicEssInf, moserDyadicEssSup, ballMeasure] using
          (moserRepresentative_mem_essInterval_on_smallBall
            (d := d) hd A hp₀ hsol hInt hx
            (r := moserDyadicRadius m)
            (moserDyadicRadius_pos (n := m))
            (moserDyadicRadius_le_quarter (n := m))
            hx (Metric.mem_ball_self (moserDyadicRadius_pos (n := m))))
      have hy_int :
          moserDyadicEssInf u x m ≤ dyadicBallAverageLimit u y (1 / 4 : ℝ) ∧
            dyadicBallAverageLimit u y (1 / 4 : ℝ) ≤ moserDyadicEssSup u x m := by
        simpa [moserDyadicEssInf, moserDyadicEssSup, ballMeasure] using
          (moserRepresentative_mem_essInterval_on_smallBall
            (d := d) hd A hp₀ hsol hInt hx
            (r := moserDyadicRadius m)
            (moserDyadicRadius_pos (n := m))
            (moserDyadicRadius_le_quarter (n := m))
            hy hy_ball)
      have hinterval :
          |moserRepresentative u x - moserRepresentative u y|
            ≤ moserDyadicEssSup u x m - moserDyadicEssInf u x m := by
        rcases hx_int with ⟨hx_lo, hx_hi⟩
        rcases hy_int with ⟨hy_lo, hy_hi⟩
        have hup :
            dyadicBallAverageLimit u x (1 / 4 : ℝ) -
                dyadicBallAverageLimit u y (1 / 4 : ℝ) ≤
              moserDyadicEssSup u x m - moserDyadicEssInf u x m := by
          linarith
        have hlo :
            -(moserDyadicEssSup u x m - moserDyadicEssInf u x m) ≤
              dyadicBallAverageLimit u x (1 / 4 : ℝ) -
                dyadicBallAverageLimit u y (1 / 4 : ℝ) := by
          linarith
        have habs :
            |dyadicBallAverageLimit u x (1 / 4 : ℝ) -
                dyadicBallAverageLimit u y (1 / 4 : ℝ)|
              ≤ moserDyadicEssSup u x m - moserDyadicEssInf u x m :=
          abs_le.mpr ⟨hlo, hup⟩
        have hvx : moserRepresentative u x = dyadicBallAverageLimit u x (1 / 4 : ℝ) := by
          unfold moserRepresentative
          rw [if_pos hx]
        have hvy : moserRepresentative u y = dyadicBallAverageLimit u y (1 / 4 : ℝ) := by
          unfold moserRepresentative
          rw [if_pos hy]
        rw [hvx, hvy]
        exact habs
      have hosc :
          moserDyadicEssSup u x m - moserDyadicEssInf u x m ≤
            (1 - α) ^ m * ((C_holder_Moser d / 32) * N) := by
        simpa [α, N] using
          (moserDyadic_oscillation_bound
            (d := d) hd A hp₀ hsol hInt hx m)
      have hfac_nonneg : 0 ≤ 1 - α := by
        linarith
      have hfac_le :
          (1 - α) ^ m ≤ ((1 / 2 : ℝ) ^ ((m : ℝ) * α)) := by
        calc
          (1 - α) ^ m ≤ (((1 / 2 : ℝ) ^ α) ^ m) := by
            exact pow_le_pow_left₀ hfac_nonneg
              (one_sub_moserDecayAlpha_le_two_rpow_neg (d := d) hd A) m
          _ = (1 / 2 : ℝ) ^ ((m : ℝ) * α) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : 0 ≤ (1 / 2 : ℝ))]
            ring_nf
      have hhalfpow_le : (1 / 2 : ℝ) ^ (m : ℝ) ≤ 16 * ‖x - y‖ := by
        have hrad : ((1 / 2 : ℝ) ^ m) / 16 < ‖x - y‖ := by
          have htmp := hn_lower
          rw [moserDyadicRadius_eq_half_pow] at htmp
          have hrewrite :
              (1 / 4 : ℝ) * (1 / 2 : ℝ) ^ (m + 1 + 1) = ((1 / 2 : ℝ) ^ m) / 16 := by
            rw [pow_add, pow_add]
            norm_num
            ring
          rw [hrewrite] at htmp
          exact htmp
        rw [Real.rpow_natCast]
        nlinarith
      have hrpow_le :
          (1 / 2 : ℝ) ^ ((m : ℝ) * α) ≤ (16 * ‖x - y‖) ^ α := by
        have htmp :
            ((1 / 2 : ℝ) ^ (m : ℝ)) ^ α ≤ (16 * ‖x - y‖) ^ α := by
          exact Real.rpow_le_rpow (by positivity) hhalfpow_le hα_nonneg
        have hpow_eq : ((1 / 2 : ℝ) ^ (m : ℝ)) ^ α = (1 / 2 : ℝ) ^ ((m : ℝ) * α) := by
          symm
          rw [← Real.rpow_mul (by norm_num : 0 ≤ (1 / 2 : ℝ))]
        rw [← hpow_eq]
        exact htmp
      have h16pow_le : (16 * ‖x - y‖) ^ α ≤ 16 * ‖x - y‖ ^ α := by
        have hpow16 : (16 : ℝ) ^ α ≤ 16 := by
          calc
            (16 : ℝ) ^ α ≤ (16 : ℝ) ^ (1 : ℝ) := by
              exact Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 16) hα_le
            _ = 16 := by rw [Real.rpow_one]
        have hpow_nonneg : 0 ≤ ‖x - y‖ ^ α := by
          exact Real.rpow_nonneg (norm_nonneg _) _
        calc
          (16 * ‖x - y‖) ^ α = (16 : ℝ) ^ α * ‖x - y‖ ^ α := by
            rw [Real.mul_rpow (by positivity) (norm_nonneg _)]
          _ ≤ 16 * ‖x - y‖ ^ α := by
            exact mul_le_mul_of_nonneg_right hpow16 hpow_nonneg
      have hfactor :
          (1 - α) ^ m ≤ 16 * ‖x - y‖ ^ α := by
        exact le_trans hfac_le (le_trans hrpow_le h16pow_le)
      have hosc_final :
          moserDyadicEssSup u x m - moserDyadicEssInf u x m ≤
            C_holder_Moser d * N * ‖x - y‖ ^ α := by
        have hmul :
            (1 - α) ^ m * ((C_holder_Moser d / 32) * N) ≤
              (16 * ‖x - y‖ ^ α) * ((C_holder_Moser d / 32) * N) := by
          exact mul_le_mul_of_nonneg_right hfactor (by nlinarith [hC_nonneg, hN_nonneg])
        calc
          moserDyadicEssSup u x m - moserDyadicEssInf u x m
              ≤ (1 - α) ^ m * ((C_holder_Moser d / 32) * N) := hosc
          _ ≤ (16 * ‖x - y‖ ^ α) * ((C_holder_Moser d / 32) * N) := hmul
          _ ≤ C_holder_Moser d * N * ‖x - y‖ ^ α := by
                nlinarith [hC_nonneg, hN_nonneg, Real.rpow_nonneg (norm_nonneg (x - y)) α]
      have hfinal :
          |moserRepresentative u x - moserRepresentative u y|
            ≤ C_holder_Moser d * N * ‖x - y‖ ^ α := by
        exact le_trans hinterval hosc_final
      simpa [N, α] using hfinal


end DeGiorgi
