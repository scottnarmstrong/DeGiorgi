import DeGiorgi.Holder.LocalBounds

/-!
# Holder Oscillation Decay

Oscillation-decay machinery along dyadic balls for the Holder endpoint.
-/

noncomputable section

open MeasureTheory Filter

namespace DeGiorgi

variable {d : ℕ} [NeZero d]

local notation "E" => AmbientSpace d
local notation "μ1" => volume.restrict (Metric.ball (0 : E) 1)
local notation "μhalf" => volume.restrict (Metric.ball (0 : E) (1 / 2 : ℝ))

noncomputable def moserDecayAlpha
    (A : NormalizedEllipticCoeff d (Metric.ball (0 : E) 1)) : ℝ :=
  Real.exp (-(C_harnack d * A.1.Λ ^ ((1 : ℝ) / 2)))

theorem C_harnack_nonneg
    (hd : 2 < (d : ℝ)) :
    0 ≤ C_harnack d := by
  unfold C_harnack
  have hcoeff_nonneg : 0 ≤ ((d : ℝ) - 2) / ((d : ℝ) - 1) := by
    have hnum_nonneg : 0 ≤ (d : ℝ) - 2 := by
      linarith
    have hden_nonneg : 0 ≤ (d : ℝ) - 1 := by
      linarith
    exact div_nonneg hnum_nonneg hden_nonneg
  have hlogM_nonneg :
      0 ≤ Real.log (C_Moser d * (((d : ℝ) - 1) ^ (d : ℝ)) * ((4 : ℝ) ^ (d : ℝ))) := by
    simpa [localMoserBase] using Real.log_nonneg (one_le_localMoserBase (d := d) hd)
  have hlogW_nonneg :
      0 ≤ Real.log (C_weakHarnack_of d * ((d : ℝ) ^ (weak_harnack_decay_exp d))) := by
    simpa [localWeakHarnackBase] using Real.log_nonneg (one_le_localWeakHarnackBase (d := d) hd)
  have hd_nonneg : 0 ≤ (d : ℝ) := by positivity
  refine mul_nonneg (by norm_num) ?_
  exact add_nonneg (add_nonneg (mul_nonneg hcoeff_nonneg hlogM_nonneg) hd_nonneg) hlogW_nonneg

theorem C_harnack_le_C_holder_Moser :
    C_harnack d ≤ C_holder_Moser d := by
  unfold C_holder_Moser
  have hlocal_nonneg : 0 ≤ localMoserBase d := localMoserBase_nonneg (d := d)
  have htwo_nonneg : 0 ≤ C_Moser d * (2 : ℝ) ^ (d : ℝ) := by
    refine mul_nonneg ?_ ?_
    · exact le_trans (by norm_num : (0 : ℝ) ≤ 1) (one_le_C_Moser (d := d))
    · exact Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _
  have hweak_nonneg : 0 ≤ C_weakHarnack_of d * (d : ℝ) ^ (d : ℝ) := by
    refine mul_nonneg ?_ ?_
    · exact le_trans (by norm_num : (0 : ℝ) ≤ 1) (one_le_C_weakHarnack_of (d := d))
    · exact Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ d) _
  have hsum_nonneg :
      0 ≤
        |C_harnack d| + localMoserBase d + C_Moser d * (2 : ℝ) ^ (d : ℝ) +
          C_weakHarnack_of d * (d : ℝ) ^ (d : ℝ) + 8 := by
    nlinarith [abs_nonneg (C_harnack d), hlocal_nonneg, htwo_nonneg, hweak_nonneg]
  have hsum_ge_abs :
      |C_harnack d| ≤
        |C_harnack d| + localMoserBase d + C_Moser d * (2 : ℝ) ^ (d : ℝ) +
          C_weakHarnack_of d * (d : ℝ) ^ (d : ℝ) + 8 := by
    nlinarith [hlocal_nonneg, htwo_nonneg, hweak_nonneg]
  have hmul_ge :
      |C_harnack d| + localMoserBase d + C_Moser d * (2 : ℝ) ^ (d : ℝ) +
          C_weakHarnack_of d * (d : ℝ) ^ (d : ℝ) + 8 ≤
        256 *
          (|C_harnack d| + localMoserBase d + C_Moser d * (2 : ℝ) ^ (d : ℝ) +
            C_weakHarnack_of d * (d : ℝ) ^ (d : ℝ) + 8) := by
    nlinarith
  exact le_trans (le_abs_self _) (le_trans hsum_ge_abs hmul_ge)

theorem moserDecayAlpha_pos
    (A : NormalizedEllipticCoeff d (Metric.ball (0 : E) 1)) :
    0 < moserDecayAlpha A := by
  unfold moserDecayAlpha
  positivity

theorem moserDecayAlpha_le_one
    (hd : 2 < (d : ℝ))
    (A : NormalizedEllipticCoeff d (Metric.ball (0 : E) 1)) :
    moserDecayAlpha A ≤ 1 := by
  unfold moserDecayAlpha
  refine Real.exp_le_one_iff.mpr ?_
  have hnonneg :
      0 ≤ C_harnack d * A.1.Λ ^ ((1 : ℝ) / 2) := by
    exact mul_nonneg (C_harnack_nonneg (d := d) hd) (Real.rpow_nonneg A.1.Λ_nonneg _)
  linarith

theorem moserLowerBound_le_decayAlpha
    (_hd : 2 < (d : ℝ))
    (A : NormalizedEllipticCoeff d (Metric.ball (0 : E) 1)) :
    Real.exp (-(C_holder_Moser d * A.1.Λ ^ ((1 : ℝ) / 2))) ≤ moserDecayAlpha A := by
  unfold moserDecayAlpha
  refine Real.exp_le_exp.mpr ?_
  have hs_nonneg : 0 ≤ A.1.Λ ^ ((1 : ℝ) / 2) := by
    exact Real.rpow_nonneg A.1.Λ_nonneg _
  have hmul :
      C_harnack d * A.1.Λ ^ ((1 : ℝ) / 2) ≤
        C_holder_Moser d * A.1.Λ ^ ((1 : ℝ) / 2) := by
    exact mul_le_mul_of_nonneg_right (C_harnack_le_C_holder_Moser (d := d)) hs_nonneg
  linarith

theorem one_sub_moserDecayAlpha_le_two_rpow_neg
    (hd : 2 < (d : ℝ))
    (A : NormalizedEllipticCoeff d (Metric.ball (0 : E) 1)) :
    1 - moserDecayAlpha A ≤ (1 / 2 : ℝ) ^ moserDecayAlpha A := by
  let α : ℝ := moserDecayAlpha A
  have hα_pos : 0 < α := by
    simpa [α] using moserDecayAlpha_pos (d := d) A
  have hα_le : α ≤ 1 := by
    simpa [α] using moserDecayAlpha_le_one (d := d) hd A
  have hlog_two_le_one : Real.log (2 : ℝ) ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : 0 < (2 : ℝ))
    norm_num at this ⊢
    linarith
  have hneg_le : -α ≤ -α * Real.log 2 := by
    nlinarith
  have hlin : 1 - α ≤ Real.exp (-α) := by
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
      (Real.add_one_le_exp (-α))
  have hexp_mono : Real.exp (-α) ≤ Real.exp (-α * Real.log 2) := by
    exact Real.exp_le_exp.mpr hneg_le
  calc
    1 - moserDecayAlpha A = 1 - α := by rfl
    _ ≤ Real.exp (-α) := hlin
    _ ≤ Real.exp (-α * Real.log 2) := hexp_mono
    _ = (1 / 2 : ℝ) ^ α := by
          rw [Real.rpow_def_of_pos (by norm_num : 0 < (1 / 2 : ℝ))]
          congr 1
          have hlog_half : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
            rw [show (1 / 2 : ℝ) = ((2 : ℝ)⁻¹) by norm_num, Real.log_inv]
          rw [hlog_half]
          ring
    _ = (1 / 2 : ℝ) ^ moserDecayAlpha A := by rfl

omit [NeZero d] in
theorem smallBall_subset_unitBall
    {c : E} (hc : c ∈ Metric.ball (0 : E) (1 / 2 : ℝ))
    {r : ℝ} (hr : r ≤ (1 / 4 : ℝ)) :
    Metric.ball c r ⊆ Metric.ball (0 : E) 1 := by
  refine Set.Subset.trans ?_ (ball_half_subset_unitBall hc)
  exact Metric.ball_subset_ball (by linarith)

omit [NeZero d] in
theorem closedBall_subset_unitBall_of_mem_closedBall_half
    {c : E} (hc : c ∈ Metric.closedBall (0 : E) (1 / 2 : ℝ))
    {r : ℝ} (_hr_nonneg : 0 ≤ r) (hr_quarter : r ≤ (1 / 4 : ℝ)) :
    Metric.closedBall c r ⊆ Metric.ball (0 : E) 1 := by
  intro x hx
  have hc' : dist c (0 : E) ≤ 1 / 2 := by
    simpa using hc
  have hx' : dist x c ≤ r := by
    simpa using hx
  refine Metric.mem_ball.2 ?_
  calc
    dist x (0 : E) ≤ dist x c + dist c (0 : E) := dist_triangle _ _ _
    _ ≤ r + 1 / 2 := by linarith
    _ ≤ 3 / 4 := by linarith
    _ < 1 := by norm_num

theorem ae_abs_le_moserHolderNorm_on_smallBall
    (hd : 2 < (d : ℝ))
    (A : NormalizedEllipticCoeff d (Metric.ball (0 : E) 1))
    {u : E → ℝ} {p₀ : ℝ} (hp₀ : 1 < p₀)
    (hsol : IsSolution A.1 u)
    (hInt : IntegrableOn (fun z => |u z| ^ p₀) (Metric.ball (0 : E) 1) volume)
    {c : E} (hc : c ∈ Metric.ball (0 : E) (1 / 2 : ℝ))
    {r : ℝ} (_hr : 0 < r) (hrq : r ≤ (1 / 4 : ℝ)) :
    ∀ᵐ z ∂ ballMeasure c r,
      |u z| ≤ (C_holder_Moser d / 64) * moserHolderNorm A u p₀ := by
  have hquarter :
      ∀ᵐ z ∂ ballMeasure c (1 / 4 : ℝ),
        |u z| ≤ (C_holder_Moser d / 64) * moserHolderNorm A u p₀ :=
    ae_abs_le_moserHolderNorm_on_quarterBall
      (d := d) hd A hp₀ hsol hInt hc
  have hsub : Metric.ball c r ⊆ Metric.ball c (1 / 4 : ℝ) := by
    exact Metric.ball_subset_ball hrq
  exact ae_restrict_of_ae_restrict_of_subset hsub hquarter

omit [NeZero d] in
theorem holderOnWith_of_realBound
    {v : E → ℝ} {s : Set E} {K α : ℝ}
    (hK : 0 ≤ K) (hα : 0 ≤ α)
    (hbound : ∀ x ∈ s, ∀ y ∈ s, |v x - v y| ≤ K * ‖x - y‖ ^ α) :
    HolderOnWith ⟨K, hK⟩ ⟨α, hα⟩ v s := by
  intro x hx y hy
  have hxy := hbound x hx y hy
  have hmain : edist (v x) (v y) ≤ ENNReal.ofReal K * edist x y ^ α := by
    have hxy' : ENNReal.ofReal |v x - v y| ≤ ENNReal.ofReal (K * ‖x - y‖ ^ α) :=
      ENNReal.ofReal_le_ofReal hxy
    calc
      edist (v x) (v y) = ENNReal.ofReal |v x - v y| := by
        rw [edist_dist, Real.dist_eq]
      _ ≤ ENNReal.ofReal (K * ‖x - y‖ ^ α) := hxy'
      _ = ENNReal.ofReal K * ENNReal.ofReal (‖x - y‖ ^ α) := by
            rw [ENNReal.ofReal_mul hK]
      _ = ENNReal.ofReal K * edist x y ^ α := by
            rw [edist_dist, dist_eq_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hα]
  convert hmain using 1
  rw [(ENNReal.ofReal_eq_coe_nnreal (x := K) hK).symm, NNReal.coe_mk]

omit [NeZero d] in
theorem pointwise_le_of_ae_le_on_ball_inter_half
    {u v : E → ℝ} {c x : E} {r M : ℝ}
    (hx_half : x ∈ Metric.ball (0 : E) (1 / 2 : ℝ))
    (hx_ball : x ∈ Metric.ball c r)
    (hv_cont : ContinuousOn v (Metric.ball (0 : E) (1 / 2 : ℝ)))
    (hvu : v =ᵐ[μ1] u)
    (hu_le : ∀ᵐ z ∂ ballMeasure c r, u z ≤ M) :
    v x ≤ M := by
  let s : Set E := Metric.ball c r ∩ Metric.ball (0 : E) (1 / 2 : ℝ)
  have hs_open : IsOpen s := Metric.isOpen_ball.inter Metric.isOpen_ball
  have hs_subset_half : s ⊆ Metric.ball (0 : E) (1 / 2 : ℝ) := by
    intro z hz
    exact hz.2
  have hs_subset_ball : s ⊆ Metric.ball c r := by
    intro z hz
    exact hz.1
  have hs_subset_unit : s ⊆ Metric.ball (0 : E) 1 := by
    intro z hz
    exact Metric.ball_subset_ball (by norm_num : (1 / 2 : ℝ) ≤ 1) hz.2
  have hx : x ∈ s := ⟨hx_ball, hx_half⟩
  let w : E → ℝ := fun z => max (v z - M) 0
  have hw_cont : ContinuousOn w s := by
    simpa [w] using
      (((hv_cont.mono hs_subset_half).sub continuousOn_const).sup continuousOn_const)
  have hvu_s : v =ᵐ[volume.restrict s] u :=
    ae_restrict_of_ae_restrict_of_subset hs_subset_unit hvu
  have hu_le_s : ∀ᵐ z ∂ volume.restrict s, u z ≤ M :=
    ae_restrict_of_ae_restrict_of_subset hs_subset_ball hu_le
  have hw_ae : w =ᵐ[volume.restrict s] fun _ => (0 : ℝ) := by
    filter_upwards [hvu_s, hu_le_s] with z hz_eq hz_le
    simp [w, hz_eq, hz_le]
  have hs_reg : s ⊆ closure (interior s) := by
    simpa [hs_open.interior_eq] using (subset_closure : s ⊆ closure s)
  have hw_eq : Set.EqOn w (fun _ => (0 : ℝ)) s :=
    MeasureTheory.Measure.eqOn_of_ae_eq (μ := volume) hw_ae hw_cont continuousOn_const hs_reg
  have hmax0 : max (v x - M) 0 = 0 := by
    simpa [w] using hw_eq hx
  have hle0 : v x - M ≤ 0 := by
    simpa [hmax0] using (le_max_left (v x - M) (0 : ℝ))
  linarith

omit [NeZero d] in
theorem pointwise_ge_of_ae_ge_on_ball_inter_half
    {u v : E → ℝ} {c x : E} {r m : ℝ}
    (hx_half : x ∈ Metric.ball (0 : E) (1 / 2 : ℝ))
    (hx_ball : x ∈ Metric.ball c r)
    (hv_cont : ContinuousOn v (Metric.ball (0 : E) (1 / 2 : ℝ)))
    (hvu : v =ᵐ[μ1] u)
    (hm_le : ∀ᵐ z ∂ ballMeasure c r, m ≤ u z) :
    m ≤ v x := by
  let s : Set E := Metric.ball c r ∩ Metric.ball (0 : E) (1 / 2 : ℝ)
  have hs_open : IsOpen s := Metric.isOpen_ball.inter Metric.isOpen_ball
  have hs_subset_half : s ⊆ Metric.ball (0 : E) (1 / 2 : ℝ) := by
    intro z hz
    exact hz.2
  have hs_subset_ball : s ⊆ Metric.ball c r := by
    intro z hz
    exact hz.1
  have hs_subset_unit : s ⊆ Metric.ball (0 : E) 1 := by
    intro z hz
    exact Metric.ball_subset_ball (by norm_num : (1 / 2 : ℝ) ≤ 1) hz.2
  have hx : x ∈ s := ⟨hx_ball, hx_half⟩
  let w : E → ℝ := fun z => max (m - v z) 0
  have hw_cont : ContinuousOn w s := by
    simpa [w] using
      ((continuousOn_const.sub (hv_cont.mono hs_subset_half)).sup continuousOn_const)
  have hvu_s : v =ᵐ[volume.restrict s] u :=
    ae_restrict_of_ae_restrict_of_subset hs_subset_unit hvu
  have hm_le_s : ∀ᵐ z ∂ volume.restrict s, m ≤ u z :=
    ae_restrict_of_ae_restrict_of_subset hs_subset_ball hm_le
  have hw_ae : w =ᵐ[volume.restrict s] fun _ => (0 : ℝ) := by
    filter_upwards [hvu_s, hm_le_s] with z hz_eq hz_ge
    simp [w, hz_eq, hz_ge]
  have hs_reg : s ⊆ closure (interior s) := by
    simpa [hs_open.interior_eq] using (subset_closure : s ⊆ closure s)
  have hw_eq : Set.EqOn w (fun _ => (0 : ℝ)) s :=
    MeasureTheory.Measure.eqOn_of_ae_eq (μ := volume) hw_ae hw_cont continuousOn_const hs_reg
  have hmax0 : max (m - v x) 0 = 0 := by
    simpa [w] using hw_eq hx
  have hle0 : m - v x ≤ 0 := by
    simpa [hmax0] using (le_max_left (m - v x) (0 : ℝ))
  linarith

omit [NeZero d] in
theorem pointwise_mem_essInterval_on_ball_inter_half
    {u v : E → ℝ} {c x : E} {r : ℝ}
    (hx_half : x ∈ Metric.ball (0 : E) (1 / 2 : ℝ))
    (hx_ball : x ∈ Metric.ball c r)
    (hv_cont : ContinuousOn v (Metric.ball (0 : E) (1 / 2 : ℝ)))
    (hvu : v =ᵐ[μ1] u)
    (hu_bdd_below : Filter.IsBoundedUnder (· ≥ ·) (ae (ballMeasure c r)) u)
    (hu_bdd_above : Filter.IsBoundedUnder (· ≤ ·) (ae (ballMeasure c r)) u) :
    essInf u (ballMeasure c r) ≤ v x ∧ v x ≤ essSup u (ballMeasure c r) := by
  constructor
  · exact pointwise_ge_of_ae_ge_on_ball_inter_half
      (x := x) (c := c) (r := r) (m := essInf u (ballMeasure c r))
      hx_half hx_ball hv_cont hvu
      (ae_essInf_le (μ := ballMeasure c r) (f := u) (hf := hu_bdd_below))
  · exact pointwise_le_of_ae_le_on_ball_inter_half
      (x := x) (c := c) (r := r) (M := essSup u (ballMeasure c r))
      hx_half hx_ball hv_cont hvu
      (ae_le_essSup (μ := ballMeasure c r) (f := u) (hf := hu_bdd_above))

theorem pointwise_abs_le_moserHolderNorm_on_halfBall
    (hd : 2 < (d : ℝ))
    (A : NormalizedEllipticCoeff d (Metric.ball (0 : E) 1))
    {u v : E → ℝ} {p₀ : ℝ} (hp₀ : 1 < p₀)
    (hsol : IsSolution A.1 u)
    (hInt : IntegrableOn (fun z => |u z| ^ p₀) (Metric.ball (0 : E) 1) volume)
    (hvu : v =ᵐ[μ1] u)
    (hv_cont : ContinuousOn v (Metric.ball (0 : E) (1 / 2 : ℝ)))
    {x : E} (hx : x ∈ Metric.ball (0 : E) (1 / 2 : ℝ)) :
    |v x| ≤ (C_holder_Moser d / 64) * moserHolderNorm A u p₀ := by
  have hae :
      ∀ᵐ z ∂ ballMeasure x (1 / 4 : ℝ),
        |u z| ≤ (C_holder_Moser d / 64) * moserHolderNorm A u p₀ :=
    ae_abs_le_moserHolderNorm_on_quarterBall
      (d := d) hd A hp₀ hsol hInt hx
  have hupper :
      ∀ᵐ z ∂ ballMeasure x (1 / 4 : ℝ),
        u z ≤ (C_holder_Moser d / 64) * moserHolderNorm A u p₀ := by
    filter_upwards [hae] with z hz
    exact (abs_le.mp hz).2
  have hlower :
      ∀ᵐ z ∂ ballMeasure x (1 / 4 : ℝ),
        -((C_holder_Moser d / 64) * moserHolderNorm A u p₀) ≤ u z := by
    filter_upwards [hae] with z hz
    exact (abs_le.mp hz).1
  have hx_ball : x ∈ Metric.ball x (1 / 4 : ℝ) := Metric.mem_ball_self (by norm_num)
  have hle :
      v x ≤ (C_holder_Moser d / 64) * moserHolderNorm A u p₀ :=
    pointwise_le_of_ae_le_on_ball_inter_half
      (x := x) (c := x) (r := (1 / 4 : ℝ))
      (M := (C_holder_Moser d / 64) * moserHolderNorm A u p₀)
      hx hx_ball hv_cont hvu hupper
  have hge :
      -((C_holder_Moser d / 64) * moserHolderNorm A u p₀) ≤ v x :=
    pointwise_ge_of_ae_ge_on_ball_inter_half
      (x := x) (c := x) (r := (1 / 4 : ℝ))
      (m := -((C_holder_Moser d / 64) * moserHolderNorm A u p₀))
      hx hx_ball hv_cont hvu hlower
  exact abs_le.mpr ⟨hge, hle⟩

theorem exists_moserDyadicRadius_near
    {δ : ℝ} (hδ_pos : 0 < δ) (hδ_le : δ ≤ (1 / 4 : ℝ)) :
    ∃ n : ℕ, moserDyadicRadius (n + 1) < δ ∧ δ ≤ moserDyadicRadius n := by
  have h4δ_pos : 0 < (4 : ℝ) * δ := by positivity
  have h4δ_le : (4 : ℝ) * δ ≤ 1 := by nlinarith
  rcases exists_nat_pow_near_of_lt_one h4δ_pos h4δ_le
      (by norm_num : 0 < (1 / 2 : ℝ))
      (by norm_num : (1 / 2 : ℝ) < 1) with ⟨n, hn_lt, hn_le⟩
  refine ⟨n, ?_, ?_⟩
  · rw [moserDyadicRadius_eq_half_pow]
    nlinarith
  · rw [moserDyadicRadius_eq_half_pow]
    nlinarith

omit [NeZero d] in
theorem ae_upper_of_ae_abs_le {μ : Measure E} {u : E → ℝ} {K : ℝ}
    (hu_bound : ∀ᵐ z ∂ μ, |u z| ≤ K) :
    ∀ᵐ z ∂ μ, u z ≤ K := by
  filter_upwards [hu_bound] with z hz
  exact (abs_le.mp hz).2

omit [NeZero d] in
theorem ae_lower_of_ae_abs_le {μ : Measure E} {u : E → ℝ} {K : ℝ}
    (hu_bound : ∀ᵐ z ∂ μ, |u z| ≤ K) :
    ∀ᵐ z ∂ μ, -K ≤ u z := by
  filter_upwards [hu_bound] with z hz
  exact (abs_le.mp hz).1

omit [NeZero d] in
theorem ae_neg_upper_of_ae_lower {μ : Measure E} {u : E → ℝ} {K : ℝ}
    (hu_lower : ∀ᵐ z ∂ μ, -K ≤ u z) :
    ∀ᵐ z ∂ μ, -u z ≤ K := by
  filter_upwards [hu_lower] with z hz
  linarith

omit [NeZero d] in
theorem ae_neg_lower_of_ae_upper {μ : Measure E} {u : E → ℝ} {K : ℝ}
    (hu_upper : ∀ᵐ z ∂ μ, u z ≤ K) :
    ∀ᵐ z ∂ μ, -K ≤ -u z := by
  filter_upwards [hu_upper] with z hz
  linarith

omit [NeZero d] in
theorem essSup_sub_const_add_ballMeasure
    {u : E → ℝ} {c : E} {r m δ : ℝ}
    (hμ : ballMeasure c r ≠ 0)
    (hu_bdd_below : Filter.IsBoundedUnder (· ≥ ·) (ae (ballMeasure c r)) u)
    (hu_bdd_above : Filter.IsBoundedUnder (· ≤ ·) (ae (ballMeasure c r)) u) :
    essSup (fun z => u z - m + δ) (ballMeasure c r) =
      essSup u (ballMeasure c r) - m + δ := by
  have hshift :=
    essSup_add_const_of_bdd
      (μ := ballMeasure c r) hμ (-m + δ) hu_bdd_below hu_bdd_above
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hshift

omit [NeZero d] in
theorem essInf_sub_const_add_ballMeasure
    {u : E → ℝ} {c : E} {r m δ : ℝ}
    (hμ : ballMeasure c r ≠ 0)
    (hu_bdd_below : Filter.IsBoundedUnder (· ≥ ·) (ae (ballMeasure c r)) u)
    (hu_bdd_above : Filter.IsBoundedUnder (· ≤ ·) (ae (ballMeasure c r)) u) :
    essInf (fun z => u z - m + δ) (ballMeasure c r) =
      essInf u (ballMeasure c r) - m + δ := by
  have hshift :=
    essInf_add_const_of_bdd
      (μ := ballMeasure c r) hμ (-m + δ) hu_bdd_below hu_bdd_above
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hshift

omit [NeZero d] in
theorem essSup_const_sub_add_ballMeasure
    {u : E → ℝ} {c : E} {r M δ : ℝ}
    (hμ : ballMeasure c r ≠ 0)
    (hu_bdd_below : Filter.IsBoundedUnder (· ≥ ·) (ae (ballMeasure c r)) u)
    (hu_bdd_above : Filter.IsBoundedUnder (· ≤ ·) (ae (ballMeasure c r)) u)
    (hneg_bdd_below :
      Filter.IsBoundedUnder (· ≥ ·) (ae (ballMeasure c r)) (fun z => -u z))
    (hneg_bdd_above :
      Filter.IsBoundedUnder (· ≤ ·) (ae (ballMeasure c r)) (fun z => -u z)) :
    essSup (fun z => M - u z + δ) (ballMeasure c r) =
      M - essInf u (ballMeasure c r) + δ := by
  have hneg :
      essSup (fun z => -u z) (ballMeasure c r) = -essInf u (ballMeasure c r) := by
    simpa using
      (essSup_neg_of_bdd
        (μ := ballMeasure c r) hμ
        hu_bdd_below hu_bdd_above hneg_bdd_below hneg_bdd_above)
  have hshift :=
    essSup_add_const_of_bdd
      (μ := ballMeasure c r) hμ (M + δ) hneg_bdd_below hneg_bdd_above
  calc
    essSup (fun z => M - u z + δ) (ballMeasure c r)
        = essSup (fun z => -u z + (M + δ)) (ballMeasure c r) := by
            congr 1
            ext z
            ring
    _ = essSup (fun z => -u z) (ballMeasure c r) + (M + δ) := hshift
    _ = -essInf u (ballMeasure c r) + (M + δ) := by rw [hneg]
    _ = M - essInf u (ballMeasure c r) + δ := by ring

omit [NeZero d] in
theorem essInf_const_sub_add_ballMeasure
    {u : E → ℝ} {c : E} {r M δ : ℝ}
    (hμ : ballMeasure c r ≠ 0)
    (hu_bdd_below : Filter.IsBoundedUnder (· ≥ ·) (ae (ballMeasure c r)) u)
    (hu_bdd_above : Filter.IsBoundedUnder (· ≤ ·) (ae (ballMeasure c r)) u)
    (hneg_bdd_below :
      Filter.IsBoundedUnder (· ≥ ·) (ae (ballMeasure c r)) (fun z => -u z))
    (hneg_bdd_above :
      Filter.IsBoundedUnder (· ≤ ·) (ae (ballMeasure c r)) (fun z => -u z)) :
    essInf (fun z => M - u z + δ) (ballMeasure c r) =
      M - essSup u (ballMeasure c r) + δ := by
  have hneg :
      essInf (fun z => -u z) (ballMeasure c r) = -essSup u (ballMeasure c r) := by
    simpa using
      (essInf_neg_of_bdd
        (μ := ballMeasure c r) hμ
        hu_bdd_below hu_bdd_above hneg_bdd_below hneg_bdd_above)
  have hshift :=
    essInf_add_const_of_bdd
      (μ := ballMeasure c r) hμ (M + δ) hneg_bdd_below hneg_bdd_above
  calc
    essInf (fun z => M - u z + δ) (ballMeasure c r)
        = essInf (fun z => -u z + (M + δ)) (ballMeasure c r) := by
            congr 1
            ext z
            ring
    _ = essInf (fun z => -u z) (ballMeasure c r) + (M + δ) := hshift
    _ = -essSup u (ballMeasure c r) + (M + δ) := by rw [hneg]
    _ = M - essSup u (ballMeasure c r) + δ := by ring

theorem oscillation_decay_from_shifted_harnack
    {α M m S i δ : ℝ}
    (hα_nonneg : 0 ≤ α)
    (_hα_le_one : α ≤ 1)
    (hδ_nonneg : 0 ≤ δ)
    (hSi_nonneg : 0 ≤ S - i)
    (hlo : α * (S - m + δ) ≤ i - m + δ)
    (hhi : α * (M - i + δ) ≤ M - S + δ) :
    S - i ≤ (1 - α) * (M - m) + 2 * δ := by
  have hmain : (1 + α) * (S - i) ≤ (1 - α) * (M - m + 2 * δ) := by
    nlinarith
  have hmul : S - i ≤ (1 + α) * (S - i) := by
    nlinarith
  have hright :
      (1 - α) * (M - m + 2 * δ) ≤ (1 - α) * (M - m) + 2 * δ := by
    nlinarith
  exact le_trans hmul (le_trans hmain hright)

theorem moser_oscillation_decay_on_ball
    (hd : 2 < (d : ℝ))
    (A : NormalizedEllipticCoeff d (Metric.ball (0 : E) 1))
    {u : E → ℝ}
    (hsol : IsSolution A.1 u)
    {c : E} (hc : c ∈ Metric.ball (0 : E) (1 / 2 : ℝ))
    {r : ℝ} (hr : 0 < r) (hrq : r ≤ (1 / 4 : ℝ))
    (K : ℝ)
    (hu_bound : ∀ᵐ z ∂ ballMeasure c r, |u z| ≤ K) :
    essSup u (ballMeasure c (r / 2 : ℝ)) - essInf u (ballMeasure c (r / 2 : ℝ)) ≤
      (1 - moserDecayAlpha A) *
        (essSup u (ballMeasure c r) - essInf u (ballMeasure c r)) := by
  have hc_closed : c ∈ Metric.closedBall (0 : E) (1 / 2 : ℝ) := by
    exact Metric.mem_closedBall.2 (le_of_lt (by simpa using hc))
  have hsub_closed : Metric.closedBall c r ⊆ Metric.ball (0 : E) 1 :=
    closedBall_subset_unitBall_of_mem_closedBall_half (d := d) hc_closed hr.le hrq
  have hsub_ball : Metric.ball c r ⊆ Metric.ball (0 : E) 1 :=
    Metric.ball_subset_closedBall.trans hsub_closed
  let Ar : NormalizedEllipticCoeff d (Metric.ball c r) :=
    NormalizedEllipticCoeff.restrict A hsub_ball
  have hsol_r : IsSolution Ar.1 u := by
    change IsSolution ((A.1).restrict hsub_ball) u
    exact hsol.restrict_ball (d := d) Metric.isOpen_ball hr hsub_closed
  set α : ℝ := moserDecayAlpha A
  set M : ℝ := essSup u (ballMeasure c r)
  set m : ℝ := essInf u (ballMeasure c r)
  set S : ℝ := essSup u (ballMeasure c (r / 2 : ℝ))
  set i : ℝ := essInf u (ballMeasure c (r / 2 : ℝ))
  have hα_pos : 0 < α := by
    simpa [α] using moserDecayAlpha_pos (d := d) A
  have hα_nonneg : 0 ≤ α := hα_pos.le
  have hα_le : α ≤ 1 := by
    simpa [α] using moserDecayAlpha_le_one (d := d) hd A
  have hαH :
      α * Real.exp (C_harnack d * A.1.Λ ^ ((1 : ℝ) / 2)) = 1 := by
    dsimp [α, moserDecayAlpha]
    rw [← Real.exp_add]
    have hsum :
        -(C_harnack d * A.1.Λ ^ ((1 : ℝ) / 2)) +
            (C_harnack d * A.1.Λ ^ ((1 : ℝ) / 2)) = 0 := by
      ring
    rw [hsum, Real.exp_zero]
  refine le_of_forall_pos_add_bound ?_
  intro ε hε
  let δ : ℝ := ε / 2
  have hδ_pos : 0 < δ := by
    dsimp [δ]
    positivity
  have hhalf_subset : Metric.ball c (r / 2 : ℝ) ⊆ Metric.ball c r := by
    exact Metric.ball_subset_ball (by nlinarith [hr])
  have hu_upper : ∀ᵐ z ∂ ballMeasure c r, u z ≤ K :=
    ae_upper_of_ae_abs_le hu_bound
  have hu_lower : ∀ᵐ z ∂ ballMeasure c r, -K ≤ u z :=
    ae_lower_of_ae_abs_le hu_bound
  have hu_upper_half : ∀ᵐ z ∂ ballMeasure c (r / 2 : ℝ), u z ≤ K :=
    ae_restrict_of_ae_restrict_of_subset hhalf_subset hu_upper
  have hu_lower_half : ∀ᵐ z ∂ ballMeasure c (r / 2 : ℝ), -K ≤ u z :=
    ae_restrict_of_ae_restrict_of_subset hhalf_subset hu_lower
  have hu_bdd_below : Filter.IsBoundedUnder (· ≥ ·) (ae (ballMeasure c r)) u := ⟨-K, hu_lower⟩
  have hu_bdd_above : Filter.IsBoundedUnder (· ≤ ·) (ae (ballMeasure c r)) u := ⟨K, hu_upper⟩
  have hu_bdd_below_half : Filter.IsBoundedUnder (· ≥ ·) (ae (ballMeasure c (r / 2 : ℝ))) u :=
    ⟨-K, hu_lower_half⟩
  have hu_bdd_above_half : Filter.IsBoundedUnder (· ≤ ·) (ae (ballMeasure c (r / 2 : ℝ))) u :=
    ⟨K, hu_upper_half⟩
  have hμ_half_ne : ballMeasure c (r / 2 : ℝ) ≠ 0 := by
    exact restrict_ball_ne_zero (c := c) (r := (r / 2 : ℝ)) (by nlinarith [hr])
  have hneg_upper_half : ∀ᵐ z ∂ ballMeasure c (r / 2 : ℝ), -u z ≤ K :=
    ae_neg_upper_of_ae_lower hu_lower_half
  have hneg_lower_half : ∀ᵐ z ∂ ballMeasure c (r / 2 : ℝ), -K ≤ -u z :=
    ae_neg_lower_of_ae_upper hu_upper_half
  have hneg_bdd_above_half :
      Filter.IsBoundedUnder (· ≤ ·) (ae (ballMeasure c (r / 2 : ℝ))) (fun z => -u z) :=
    ⟨K, hneg_upper_half⟩
  have hneg_bdd_below_half :
      Filter.IsBoundedUnder (· ≥ ·) (ae (ballMeasure c (r / 2 : ℝ))) (fun z => -u z) :=
    ⟨-K, hneg_lower_half⟩
  have hm_ae : ∀ᵐ z ∂ ballMeasure c r, m ≤ u z := by
    simpa [m] using (ae_essInf_le (μ := ballMeasure c r) (f := u) (hf := hu_bdd_below))
  have hM_ae : ∀ᵐ z ∂ ballMeasure c r, u z ≤ M := by
    simpa [M] using (ae_le_essSup (μ := ballMeasure c r) (f := u) (hf := hu_bdd_above))
  have hsol_lo : IsSolution Ar.1 (fun z => u z - m + δ) := by
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm, δ] using
      (hsol_r.sub_const_ball (d := d) hr (m - δ))
  have hsol_hi : IsSolution Ar.1 (fun z => M - u z + δ) := by
    have hneg : IsSolution Ar.1 (fun z => -u z) := hsol_r.neg_ball (d := d) hr
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm, δ] using
      (hneg.sub_const_ball (d := d) hr (-M - δ))
  have hpos_lo : ∀ᵐ z ∂ ballMeasure c r, 0 < u z - m + δ := by
    filter_upwards [hm_ae] with z hz
    linarith
  have hpos_hi : ∀ᵐ z ∂ ballMeasure c r, 0 < M - u z + δ := by
    filter_upwards [hM_ae] with z hz
    linarith
  have hlo_raw :=
    harnack_on_ball_ae_pos (d := d) hd (x₀ := c) (R := r) hr Ar
      (u := fun z => u z - m + δ) hpos_lo hsol_lo
  have hhi_raw :=
    harnack_on_ball_ae_pos (d := d) hd (x₀ := c) (R := r) hr Ar
      (u := fun z => M - u z + δ) hpos_hi hsol_hi
  have hsup_lo :
      essSup (fun z => u z - m + δ) (ballMeasure c (r / 2 : ℝ)) = S - m + δ := by
    simpa [S] using
      (essSup_sub_const_add_ballMeasure
        (u := u) (c := c) (r := (r / 2 : ℝ)) (m := m) (δ := δ)
        hμ_half_ne hu_bdd_below_half hu_bdd_above_half)
  have hinf_lo :
      essInf (fun z => u z - m + δ) (ballMeasure c (r / 2 : ℝ)) = i - m + δ := by
    simpa [i] using
      (essInf_sub_const_add_ballMeasure
        (u := u) (c := c) (r := (r / 2 : ℝ)) (m := m) (δ := δ)
        hμ_half_ne hu_bdd_below_half hu_bdd_above_half)
  have hsup_hi :
      essSup (fun z => M - u z + δ) (ballMeasure c (r / 2 : ℝ)) = M - i + δ := by
    simpa [i] using
      (essSup_const_sub_add_ballMeasure
        (u := u) (c := c) (r := (r / 2 : ℝ)) (M := M) (δ := δ)
        hμ_half_ne hu_bdd_below_half hu_bdd_above_half
        hneg_bdd_below_half hneg_bdd_above_half)
  have hinf_hi :
      essInf (fun z => M - u z + δ) (ballMeasure c (r / 2 : ℝ)) = M - S + δ := by
    simpa [S] using
      (essInf_const_sub_add_ballMeasure
        (u := u) (c := c) (r := (r / 2 : ℝ)) (M := M) (δ := δ)
        hμ_half_ne hu_bdd_below_half hu_bdd_above_half
        hneg_bdd_below_half hneg_bdd_above_half)
  have hlo :
      S - m + δ ≤
        Real.exp (C_harnack d * A.1.Λ ^ ((1 : ℝ) / 2)) * (i - m + δ) := by
    rw [hsup_lo, hinf_lo] at hlo_raw
    exact hlo_raw
  have hhi :
      M - i + δ ≤
        Real.exp (C_harnack d * A.1.Λ ^ ((1 : ℝ) / 2)) * (M - S + δ) := by
    rw [hsup_hi, hinf_hi] at hhi_raw
    exact hhi_raw
  have hlo' : α * (S - m + δ) ≤ i - m + δ := by
    have hmul := mul_le_mul_of_nonneg_left hlo hα_nonneg
    rw [← mul_assoc, hαH, one_mul] at hmul
    exact hmul
  have hhi' : α * (M - i + δ) ≤ M - S + δ := by
    have hmul := mul_le_mul_of_nonneg_left hhi hα_nonneg
    rw [← mul_assoc, hαH, one_mul] at hmul
    exact hmul
  have hSi_nonneg : 0 ≤ S - i := by
    by_contra hneg
    have hlt : S < i := by
      linarith
    let a : ℝ := (S + i) / 2
    have hS_lt_a : S < a := by
      dsimp [a]
      linarith
    have ha_lt_i : a < i := by
      dsimp [a]
      linarith
    have hu_lt_a : ∀ᵐ z ∂ ballMeasure c (r / 2 : ℝ), u z < a := by
      filter_upwards [ae_le_essSup (μ := ballMeasure c (r / 2 : ℝ)) (f := u)
          (hf := hu_bdd_above_half)] with z hz
      linarith
    have ha_lt_u : ∀ᵐ z ∂ ballMeasure c (r / 2 : ℝ), a < u z := by
      filter_upwards [ae_essInf_le (μ := ballMeasure c (r / 2 : ℝ)) (f := u)
          (hf := hu_bdd_below_half)] with z hz
      linarith
    have hfalse : ∀ᵐ z ∂ ballMeasure c (r / 2 : ℝ), False := by
      filter_upwards [hu_lt_a, ha_lt_u] with z hz1 hz2
      linarith
    rw [ae_iff] at hfalse
    have hzero : (ballMeasure c (r / 2 : ℝ)) Set.univ = 0 := by
      simpa using hfalse
    exact hμ_half_ne (Measure.measure_univ_eq_zero.mp hzero)
  have hosc :
      S - i ≤ (1 - α) * (M - m) + ε := by
    have hδ_eq : 2 * δ = ε := by
      dsimp [δ]
      ring
    have hoscδ :
        S - i ≤ (1 - α) * (M - m) + 2 * δ :=
      oscillation_decay_from_shifted_harnack hα_nonneg hα_le hδ_pos.le hSi_nonneg hlo' hhi'
    simpa [hδ_eq] using hoscδ
  simpa [S, i, M, m, α] using hosc

theorem moserDyadic_oscillation_bound
    (hd : 2 < (d : ℝ))
    (A : NormalizedEllipticCoeff d (Metric.ball (0 : E) 1))
    {u : E → ℝ} {p₀ : ℝ} (hp₀ : 1 < p₀)
    (hsol : IsSolution A.1 u)
    (hInt : IntegrableOn (fun z => |u z| ^ p₀) (Metric.ball (0 : E) 1) volume)
    {x : E} (hx : x ∈ Metric.ball (0 : E) (1 / 2 : ℝ)) :
    ∀ n : ℕ,
      moserDyadicEssSup u x n - moserDyadicEssInf u x n ≤
        (1 - moserDecayAlpha A) ^ n *
          ((C_holder_Moser d / 32) * moserHolderNorm A u p₀) := by
  intro n
  induction n with
  | zero =>
      have hae :
          ∀ᵐ z ∂ ballMeasure x (1 / 4 : ℝ),
            |u z| ≤ (C_holder_Moser d / 64) * moserHolderNorm A u p₀ :=
        ae_abs_le_moserHolderNorm_on_quarterBall
          (d := d) hd A hp₀ hsol hInt hx
      have hupper :
          ∀ᵐ z ∂ ballMeasure x (1 / 4 : ℝ),
            u z ≤ (C_holder_Moser d / 64) * moserHolderNorm A u p₀ := by
        filter_upwards [hae] with z hz
        exact (abs_le.mp hz).2
      have hlower :
          ∀ᵐ z ∂ ballMeasure x (1 / 4 : ℝ),
            -((C_holder_Moser d / 64) * moserHolderNorm A u p₀) ≤ u z := by
        filter_upwards [hae] with z hz
        exact (abs_le.mp hz).1
      have hsup :
          moserDyadicEssSup u x 0 ≤
            (C_holder_Moser d / 64) * moserHolderNorm A u p₀ := by
        have hμ_ne : ballMeasure x (1 / 4 : ℝ) ≠ 0 := by
          exact restrict_ball_ne_zero (c := x) (r := (1 / 4 : ℝ)) (by norm_num)
        simpa [moserDyadicEssSup, ballMeasure, moserDyadicRadius] using
          (essSup_le_of_ae_bdd
            (μ := ballMeasure x (1 / 4 : ℝ)) hμ_ne hlower hupper)
      have hinf :
          -((C_holder_Moser d / 64) * moserHolderNorm A u p₀) ≤
            moserDyadicEssInf u x 0 := by
        have hμ_ne : ballMeasure x (1 / 4 : ℝ) ≠ 0 := by
          exact restrict_ball_ne_zero (c := x) (r := (1 / 4 : ℝ)) (by norm_num)
        simpa [moserDyadicEssInf, ballMeasure, moserDyadicRadius] using
          (le_essInf_of_ae_bdd
            (μ := ballMeasure x (1 / 4 : ℝ)) hμ_ne hlower hupper)
      have hbase :
          moserDyadicEssSup u x 0 - moserDyadicEssInf u x 0 ≤
            (C_holder_Moser d / 32) * moserHolderNorm A u p₀ := by
        nlinarith
      simpa using hbase
  | succ n ihn =>
      have hstep :
          moserDyadicEssSup u x (n + 1) - moserDyadicEssInf u x (n + 1) ≤
            (1 - moserDecayAlpha A) *
              (moserDyadicEssSup u x n - moserDyadicEssInf u x n) := by
        have hu_bound :
            ∀ᵐ z ∂ ballMeasure x (moserDyadicRadius n),
              |u z| ≤ (C_holder_Moser d / 64) * moserHolderNorm A u p₀ :=
          ae_abs_le_moserHolderNorm_on_smallBall
            (d := d) hd A hp₀ hsol hInt hx
            (r := moserDyadicRadius n)
            (moserDyadicRadius_pos (n := n))
            (moserDyadicRadius_le_quarter (n := n))
        have hdecay :=
          moser_oscillation_decay_on_ball
            (d := d) hd A hsol hx
            (r := moserDyadicRadius n)
            (moserDyadicRadius_pos (n := n))
            (moserDyadicRadius_le_quarter (n := n))
            ((C_holder_Moser d / 64) * moserHolderNorm A u p₀) hu_bound
        simpa [moserDyadicEssSup, moserDyadicEssInf, moserDyadicRadius_succ] using hdecay
      have hfac_nonneg : 0 ≤ 1 - moserDecayAlpha A := by
        have hα_le := moserDecayAlpha_le_one (d := d) hd A
        linarith [moserDecayAlpha_pos (d := d) A]
      have hmul :
          (1 - moserDecayAlpha A) *
              (moserDyadicEssSup u x n - moserDyadicEssInf u x n) ≤
            (1 - moserDecayAlpha A) *
              ((1 - moserDecayAlpha A) ^ n *
                ((C_holder_Moser d / 32) * moserHolderNorm A u p₀)) :=
        mul_le_mul_of_nonneg_left ihn hfac_nonneg
      calc
        moserDyadicEssSup u x (n + 1) - moserDyadicEssInf u x (n + 1)
            ≤ (1 - moserDecayAlpha A) *
                (moserDyadicEssSup u x n - moserDyadicEssInf u x n) := hstep
        _ ≤ (1 - moserDecayAlpha A) *
              ((1 - moserDecayAlpha A) ^ n *
                ((C_holder_Moser d / 32) * moserHolderNorm A u p₀)) := hmul
        _ = (1 - moserDecayAlpha A) ^ (n + 1) *
              ((C_holder_Moser d / 32) * moserHolderNorm A u p₀) := by
              rw [pow_succ]
              ring


end DeGiorgi
