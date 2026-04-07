import DeGiorgi.Supersolutions
import DeGiorgi.Crossover
import DeGiorgi.Support.MeasureBounds

/-!
# Chapter 06: Weak Harnack Inequality

This file proves the weak Harnack inequality for positive supersolutions,
combining the forward and inverse Moser estimates with the crossover bound.

## Proof strategy

Set `p₀ = c_crossover'(d) / Λ^{1/2}`. The proof chains three ingredients
at half scale (rescaling `v(z) = u(z/2)` from `B_{1/2}` to `B_1`):

1. **Forward Moser** on `v`: LHS on `B_{1/4}`, RHS = `C · ∫_{B_{1/2}} |u|^{p₀}`
2. **Crossover** on `u`: `∫_{B_{1/2}} |u|^{p₀} · ∫_{B_{1/2}} |u|^{-p₀} ≤ C · vol²`
3. **Inverse Moser** on `v`: `(∫_{B_{1/2}} |u⁻¹|^{p₀})⁻¹ ≤ C · (essInf_{B_{1/4}} u)^{p₀}`

All intermediate integrals match on `B_{1/2}`. Output on `B_{1/4}`.

## Dependencies

- `Supersolutions` for the two stage theorems
- `Crossover` for `crossover_estimate_unaveraged`
- `BallScaling` (transitively) for rescaling infrastructure
-/

noncomputable section

open MeasureTheory Metric

namespace DeGiorgi

variable {d : ℕ} [NeZero d]

local notation "E" => AmbientSpace d

/-! ### Constants -/

/-- The exponent `dχ / c_crossover'(d)` on `(1-q)`. -/
noncomputable def weak_harnack_decay_exp (d : ℕ) [NeZero d] : ℝ :=
  ((d : ℝ) * moserChi d) / c_crossover' d

/-! ### Arithmetic helpers -/

private theorem c_crossover_bmo_scale_nonneg : 0 ≤ c_crossover_bmo_scale d := by
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
      0 ≤ ((volume.real B1) ^ (-(1 / 2 : ℝ)) * C_poinc_val d) := by
    exact mul_nonneg h1 hCp_nonneg
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

private theorem c_crossover_bmo_scale_pos : 0 < c_crossover_bmo_scale d := by
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
  have htotal_pos :
      0 <
        (((volume.real B1) ^ (-(1 / 2 : ℝ)) * C_poinc_val d) *
          (1 / 2 : ℝ) ^ (1 - (d : ℝ) / 2)) *
          (8 * (Mst : ℝ) * (volume.real B1) ^ ((1 : ℝ) / 2)) := by
    exact mul_pos (mul_pos (mul_pos h1 hCp_pos) h2) h3
  simpa [c_crossover_bmo_scale, B1, mul_assoc] using htotal_pos

theorem c_crossover'_pos : 0 < c_crossover' (d := d) := by
  unfold c_crossover'
  have hbmo_nonneg : 0 ≤ c_crossover_bmo_scale d := c_crossover_bmo_scale_nonneg (d := d)
  have hCJN_nonneg : 0 ≤ C_JN d := (C_JN_pos d).le
  have hden_pos : 0 < 2 * C_JN d * c_crossover_bmo_scale d + 1 := by
    nlinarith
  simpa [one_div] using (inv_pos.mpr hden_pos)

theorem c_crossover'_lt_one : c_crossover' (d := d) < 1 := by
  unfold c_crossover'
  have hbmo_pos : 0 < c_crossover_bmo_scale d := c_crossover_bmo_scale_pos (d := d)
  have hden_gt_one : (1 : ℝ) < 2 * C_JN d * c_crossover_bmo_scale d + 1 := by
    have hCJN_pos : 0 < C_JN d := C_JN_pos d
    nlinarith
  have hlt :
      1 / (2 * C_JN d * c_crossover_bmo_scale d + 1) < 1 / 1 := by
    exact one_div_lt_one_div_of_lt (by positivity : (0 : ℝ) < 1) hden_gt_one
  simpa using hlt

theorem weak_harnack_decay_exp_nonneg (hd : 2 < (d : ℝ)) :
    0 ≤ weak_harnack_decay_exp d := by
  unfold weak_harnack_decay_exp
  have hchi_pos : 0 < moserChi d := moserChi_pos (d := d) hd
  have hnum_nonneg : 0 ≤ (d : ℝ) * moserChi d := by
    positivity
  exact div_nonneg hnum_nonneg (c_crossover'_pos (d := d)).le

private theorem isSupersolution_add_const_unitBall
    (A : NormalizedEllipticCoeff d (ball (0 : E) 1))
    {u : E → ℝ} (hsuper : IsSupersolution A.1 u)
    (c : ℝ) :
    IsSupersolution A.1 (fun x => u x + c) := by
  simpa [sub_eq_add_neg] using
    (hsuper.sub_const_ball (d := d) (by norm_num : (0 : ℝ) < 1) (-c))

omit [NeZero d] in
private theorem essInf_add_const
    {μ : Measure E} (hμ : μ ≠ 0) {u : E → ℝ} (c : ℝ)
    (hu_bdd_below : Filter.IsBoundedUnder (· ≥ ·) (ae μ) u)
    (hu_shift_bdd_below : Filter.IsBoundedUnder (· ≥ ·) (ae μ) (fun x => u x + c)) :
    essInf (fun x => u x + c) μ = essInf u μ + c := by
  apply le_antisymm
  ·
    have hlow : ∀ᵐ x ∂μ, essInf (fun x => u x + c) μ - c ≤ u x := by
      have htmp := ae_essInf_le (μ := μ) (f := fun x => u x + c) (hf := hu_shift_bdd_below)
      filter_upwards [htmp] with x hx
      linarith
    have hle : essInf (fun x => u x + c) μ - c ≤ essInf u μ :=
      le_essInf_real_of_ae_le (d := d) hμ hlow
    linarith
  ·
    have hlow : ∀ᵐ x ∂μ, essInf u μ + c ≤ u x + c := by
      have htmp := ae_essInf_le (μ := μ) (f := u) (hf := hu_bdd_below)
      filter_upwards [htmp] with x hx
      linarith
    exact le_essInf_real_of_ae_le (d := d) hμ hlow

theorem one_le_Λ_of_normalized
    (A : NormalizedEllipticCoeff d (ball (0 : E) 1)) :
    1 ≤ A.1.Λ := by
  have := A.1.hΛ; rw [A.2] at this; exact this

/-- The crossover exponent `p₀ = c_crossover'(d) / Λ^{1/2}`. -/
noncomputable def weakHarnackP0
    (A : NormalizedEllipticCoeff d (ball (0 : E) 1)) : ℝ :=
  c_crossover' d / A.1.Λ ^ ((1 : ℝ) / 2)

theorem p₀_pos
    (A : NormalizedEllipticCoeff d (ball (0 : E) 1)) :
    0 < weakHarnackP0 A := by
  unfold weakHarnackP0
  exact div_pos c_crossover'_pos (Real.rpow_pos_of_pos A.1.Λ_pos _)

theorem p₀_lt_one
    (A : NormalizedEllipticCoeff d (ball (0 : E) 1)) :
    weakHarnackP0 A < 1 := by
  unfold weakHarnackP0
  have hΛsqrt_ge : 1 ≤ A.1.Λ ^ ((1 : ℝ) / 2) :=
    Real.one_le_rpow (one_le_Λ_of_normalized A) (by positivity)
  calc c_crossover' d / A.1.Λ ^ ((1 : ℝ) / 2)
      ≤ c_crossover' d / 1 :=
        div_le_div_of_nonneg_left c_crossover'_pos.le (by norm_num) hΛsqrt_ge
    _ = c_crossover' d := div_one _
    _ < 1 := c_crossover'_lt_one

theorem p₀_le_crossover'
    (A : NormalizedEllipticCoeff d (ball (0 : E) 1)) :
    weakHarnackP0 A ≤ c_crossover' d := by
  unfold weakHarnackP0
  have hΛsqrt_ge : 1 ≤ A.1.Λ ^ ((1 : ℝ) / 2) :=
    Real.one_le_rpow (one_le_Λ_of_normalized A) (by positivity)
  calc
    c_crossover' d / A.1.Λ ^ ((1 : ℝ) / 2)
        ≤ c_crossover' d / 1 :=
          div_le_div_of_nonneg_left c_crossover'_pos.le (by norm_num) hΛsqrt_ge
    _ = c_crossover' d := div_one _

theorem Λ_mul_p₀_sq
    (A : NormalizedEllipticCoeff d (ball (0 : E) 1)) :
    A.1.Λ * weakHarnackP0 A ^ 2 = c_crossover' d ^ 2 := by
  unfold weakHarnackP0
  have hΛ_pos := A.1.Λ_pos
  have hΛsqrt_pos : 0 < A.1.Λ ^ ((1 : ℝ) / 2) := Real.rpow_pos_of_pos hΛ_pos _
  have hΛsqrt_sq : A.1.Λ ^ ((1 : ℝ) / 2) * A.1.Λ ^ ((1 : ℝ) / 2) = A.1.Λ := by
    rw [← Real.rpow_add hΛ_pos]; norm_num
  field_simp [ne_of_gt hΛsqrt_pos]
  nlinarith [hΛsqrt_sq]

/-! ### Half-scale rescaling infrastructure -/

/-- Rescaled coefficients from `B_{1/2}` to `B_1`, preserving `Λ`. -/
private noncomputable def rescaledCoeff
    (A : NormalizedEllipticCoeff d (ball (0 : E) 1)) :
    NormalizedEllipticCoeff d (ball (0 : E) 1) :=
  rescaleNormalizedCoeffToUnitBall (d := d) (x₀ := (0 : E)) (R := 1 / 2)
    (by norm_num : (0 : ℝ) < 1 / 2)
    (A.restrict (ball_subset_ball (by norm_num : (1 / 2 : ℝ) ≤ 1)))

private theorem rescaledCoeff_Λ_eq
    (A : NormalizedEllipticCoeff d (ball (0 : E) 1)) :
    (rescaledCoeff A).1.Λ = A.1.Λ := by
  simp [rescaledCoeff, rescaleNormalizedCoeffToUnitBall, rescaleCoeffToUnitBall,
        NormalizedEllipticCoeff.restrict, EllipticCoeff.restrict]

omit [NeZero d] in
/-- Change of variables: `∫_{B_1} f(x₀ + R·z) dz = R^{-d} · ∫_{B_R(x₀)} f(x) dx`.
Local version of BallScaling.affine_cov_helper (which is private). -/
private theorem integral_rescale_ball
    {R : ℝ} (hR : 0 < R) (f : E → ℝ) :
    ∫ z in ball (0 : E) 1, f ((R : ℝ) • z) ∂volume =
      (R ^ Module.finrank ℝ E)⁻¹ * ∫ x in ball (0 : E) R, f x ∂volume := by
  -- Specialization of affine_cov_helper with x₀ = 0.
  -- ∫_{B_1} f(R·z) dz = ∫_{B_1} f(0 + R·z) dz = R^{-d} ∫_{B_R} f(x) dx
  have := Measure.setIntegral_comp_smul_of_pos volume (fun x => f x)
    (ball (0 : E) 1) hR
  open scoped Pointwise in
  rw [show R • ball (0 : E) 1 = ball (0 : E) R from by
    rw [smul_unitBall hR.ne']; simp [Real.norm_of_nonneg hR.le]] at this
  simpa [zero_add] using this

omit [NeZero d] in
/-- General change of variables: `∫_{B_ρ} f(R·z) dz = R^{-d} · ∫_{B_{R·ρ}} f(x) dx`. -/
private theorem integral_rescale_ball_general
    {R ρ : ℝ} (hR : 0 < R) (_hρ : 0 < ρ) (f : E → ℝ) :
    ∫ z in ball (0 : E) ρ, f ((R : ℝ) • z) ∂volume =
      (R ^ Module.finrank ℝ E)⁻¹ * ∫ x in ball (0 : E) (R * ρ), f x ∂volume := by
  have := Measure.setIntegral_comp_smul_of_pos volume (fun x => f x)
    (ball (0 : E) ρ) hR
  open scoped Pointwise in
  have hball : R • ball (0 : E) ρ = ball (0 : E) (R * ρ) := by
    ext x
    simp only [Set.mem_smul_set, Metric.mem_ball, dist_zero_right]
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [norm_smul, Real.norm_of_nonneg hR.le]
      exact mul_lt_mul_of_pos_left hy hR
    · intro hx
      exact ⟨R⁻¹ • x, by
        rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hR.le), inv_mul_lt_iff₀ hR]
        exact hx, by rw [smul_smul, mul_inv_cancel₀ hR.ne', one_smul]⟩
  rw [hball] at this
  simpa [zero_add] using this

omit [NeZero d] in
private theorem quarterBall_volume_real_le_one :
    volume.real (ball (0 : E) (1 / 4 : ℝ)) ≤ 1 := by
  let T :
      E → (Fin d → ℝ) :=
    ((MeasurableEquiv.toLp 2 (Fin d → ℝ)).symm :
      EuclideanSpace ℝ (Fin d) → (Fin d → ℝ))
  let Q : Set (Fin d → ℝ) :=
    Set.pi Set.univ (fun _ => Set.Ioo (-(1 / 4 : ℝ)) (1 / 4 : ℝ))
  have hsubset : ball (0 : E) (1 / 4 : ℝ) ⊆ T ⁻¹' Q := by
    intro x hx
    change T x ∈ Q
    simp only [Q, Set.mem_pi, Set.mem_univ, true_implies]
    intro i
    have hxnorm : ‖x‖ < (1 / 4 : ℝ) := by
      simpa [Metric.mem_ball, dist_zero_right] using hx
    have hcoord_sq : ‖x.ofLp i‖ ^ 2 ≤ ‖x‖ ^ 2 := by
      have hsingle :
          x.ofLp i ^ 2 ≤ ∑ j : Fin d, x.ofLp j ^ 2 := by
        simpa using
          (Finset.single_le_sum
            (f := fun j : Fin d => x.ofLp j ^ 2)
            (fun j _ => by positivity)
            (Finset.mem_univ i))
      simpa [Real.norm_eq_abs, sq_abs, PiLp.norm_sq_eq_of_L2] using hsingle
    have hcoord : ‖x.ofLp i‖ ≤ ‖x‖ := by
      exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 hcoord_sq
    have habs : |T x i| < (1 / 4 : ℝ) := by
      exact lt_of_le_of_lt (by simpa [T, Real.norm_eq_abs] using hcoord) hxnorm
    rcases abs_lt.mp habs with ⟨hleft, hright⟩
    simpa [Set.mem_Ioo] using And.intro hleft hright
  have hpres : MeasurePreserving T volume volume := by
    simpa [T] using (PiLp.volume_preserving_ofLp (ι := Fin d))
  have hQ_meas : MeasurableSet Q := by
    simpa [Q] using MeasurableSet.univ_pi (fun _ => isOpen_Ioo.measurableSet)
  have hQ_null : NullMeasurableSet Q volume := hQ_meas.nullMeasurableSet
  have hpre_enn : volume (T ⁻¹' Q) = volume Q := by
    exact MeasureTheory.MeasurePreserving.measure_preimage hpres hQ_null
  have hpre_fin : volume (T ⁻¹' Q) < ⊤ := by
    rw [hpre_enn]
    dsimp [Q]
    rw [Real.volume_pi_Ioo]
    simp
  have hmono :
      volume.real (ball (0 : E) (1 / 4 : ℝ)) ≤ volume.real (T ⁻¹' Q) := by
    exact measureReal_mono hsubset hpre_fin.ne
  have hpre : volume.real (T ⁻¹' Q) = volume.real Q := by
    change (volume (T ⁻¹' Q)).toReal = (volume Q).toReal
    rw [hpre_enn]
  have hQ :
      volume.real Q = (1 / 2 : ℝ) ^ d := by
    change (volume Q).toReal = (1 / 2 : ℝ) ^ d
    have hQ' :
        (volume Q).toReal = ((4⁻¹ : ℝ) + 4⁻¹) ^ d := by
      dsimp [Q]
      simpa [Fintype.card_fin] using
        (Real.volume_pi_Ioo_toReal
          (ι := Fin d)
          (a := fun _ => (-(1 / 4 : ℝ)))
          (b := fun _ => (1 / 4 : ℝ))
          (by intro i; norm_num))
    calc
      (volume Q).toReal = ((4⁻¹ : ℝ) + 4⁻¹) ^ d := hQ'
      _ = (1 / 2 : ℝ) ^ d := by
            congr 1
            norm_num
  calc
    volume.real (ball (0 : E) (1 / 4 : ℝ))
        ≤ volume.real (T ⁻¹' Q) := hmono
    _ = volume.real Q := hpre
    _ = (1 / 2 : ℝ) ^ d := hQ
    _ ≤ 1 := by
          exact pow_le_one₀ (by norm_num : (0 : ℝ) ≤ 1 / 2)
            (by norm_num : (1 / 2 : ℝ) ≤ 1)

omit [NeZero d] in
private theorem quarterBall_lpNorm_mono
    {u : E → ℝ} {r s : ℝ}
    (hr : 0 < r) (hrs : r ≤ s)
    (hu_aesm : AEStronglyMeasurable u (volume.restrict (ball (0 : E) (1 / 4 : ℝ))))
    (hs_int : IntegrableOn (fun x => |u x| ^ s) (ball (0 : E) (1 / 4 : ℝ)) volume) :
    (∫ x in ball (0 : E) (1 / 4 : ℝ), |u x| ^ r ∂volume) ^ (1 / r) ≤
      (∫ x in ball (0 : E) (1 / 4 : ℝ), |u x| ^ s ∂volume) ^ (1 / s) := by
  let μq : Measure E := volume.restrict (ball (0 : E) (1 / 4 : ℝ))
  have hμq_le_one : μq Set.univ ≤ (1 : ENNReal) := by
    dsimp [μq]
    rw [Measure.restrict_apply_univ]
    rw [← ENNReal.toReal_le_toReal measure_ball_lt_top.ne ENNReal.one_ne_top]
    simpa [measureReal_def] using quarterBall_volume_real_le_one
  have hs_pos : 0 < s := lt_of_lt_of_le hr hrs
  have hs_ne_zero : ENNReal.ofReal s ≠ 0 := by
    simpa [ENNReal.ofReal_eq_zero, not_le] using hs_pos
  have hs_mem : MemLp u (ENNReal.ofReal s) μq := by
    rw [IntegrableOn] at hs_int
    exact (MeasureTheory.integrable_norm_rpow_iff
      (μ := μq) (f := u) hu_aesm hs_ne_zero ENNReal.ofReal_ne_top).1 <|
      by simpa [μq, Real.norm_eq_abs, ENNReal.toReal_ofReal hs_pos.le] using hs_int
  have hexp_nonneg : 0 ≤ 1 / r - 1 / s := by
    have hdiv : 1 / s ≤ 1 / r := by
      exact one_div_le_one_div_of_le hr hrs
    linarith
  have hfactor_le_one :
      μq Set.univ ^ (1 / r - 1 / s) ≤ 1 := by
    exact ENNReal.rpow_le_one hμq_le_one hexp_nonneg
  have hcompare_enn :
      eLpNorm u (ENNReal.ofReal r) μq ≤ eLpNorm u (ENNReal.ofReal s) μq := by
    have hcompare_enn0 :=
      MeasureTheory.eLpNorm_le_eLpNorm_mul_rpow_measure_univ
        (μ := μq) (f := u)
        (p := ENNReal.ofReal r) (q := ENNReal.ofReal s)
        (ENNReal.ofReal_le_ofReal hrs) hu_aesm
    calc
      eLpNorm u (ENNReal.ofReal r) μq
          ≤ eLpNorm u (ENNReal.ofReal s) μq *
              μq Set.univ ^ (1 / r - 1 / s) := by
                simpa [ENNReal.toReal_ofReal hr.le,
                  ENNReal.toReal_ofReal hs_pos.le] using hcompare_enn0
      _ ≤ eLpNorm u (ENNReal.ofReal s) μq * 1 := by
            exact mul_le_mul_of_nonneg_left hfactor_le_one bot_le
      _ = eLpNorm u (ENNReal.ofReal s) μq := by simp
  have hcompare_real :
      lpNorm u (ENNReal.ofReal r) μq ≤ lpNorm u (ENNReal.ofReal s) μq := by
    have hr_ne_top : eLpNorm u (ENNReal.ofReal r) μq ≠ ⊤ := by
      exact ne_of_lt <|
        lt_of_le_of_lt hcompare_enn (lt_top_iff_ne_top.2 hs_mem.eLpNorm_ne_top)
    have htoReal :=
      (ENNReal.toReal_le_toReal hr_ne_top hs_mem.eLpNorm_ne_top).2 hcompare_enn
    simpa [MeasureTheory.toReal_eLpNorm hu_aesm,
      MeasureTheory.toReal_eLpNorm hs_mem.aestronglyMeasurable] using htoReal
  rw [lpNorm_eq_integral_norm_rpow_toReal (p := ENNReal.ofReal r)
      (by simpa [ENNReal.ofReal_eq_zero, not_le] using hr) ENNReal.ofReal_ne_top hu_aesm,
    lpNorm_eq_integral_norm_rpow_toReal (p := ENNReal.ofReal s)
      (by simpa [ENNReal.ofReal_eq_zero, not_le] using hs_pos) ENNReal.ofReal_ne_top hu_aesm] at hcompare_real
  simpa [μq, Real.norm_eq_abs, ENNReal.toReal_ofReal hr.le,
    ENNReal.toReal_ofReal hs_pos.le] using hcompare_real

/-- The un-powered chain constant. The chain produces this times `(1-q)^{-dχ}`.
Raising to `1/c'` gives `C_weakHarnack`. -/
private noncomputable def C_chainGeom (_hd : 2 < (d : ℝ)) : ℝ :=
  ((((1 / 2 : ℝ) ^ (-(d : ℝ))) + 1) ^ 2) *
    ((volume.real (ball (0 : E) (1 / 2 : ℝ)) + 1) ^ 2) *
    ((c_crossover' d ^ 2 + 1) ^
      ((((d : ℝ) * moserChi d) / 2) + ((d : ℝ) / 2)))

private noncomputable def C_chainMain (hd : 2 < (d : ℝ)) : ℝ :=
  C_weakHarnack0Forward (d := d) hd * C_weakHarnack0 d ^ 3 *
    C_crossover' d * C_chainGeom (d := d) hd

private theorem one_le_C_chainMain (hd : 2 < (d : ℝ)) : 1 ≤ C_chainMain (d := d) hd := by
  unfold C_chainMain
  have h0 : 1 ≤ C_weakHarnack0Forward (d := d) hd :=
    one_le_C_weakHarnack0Forward (d := d) hd
  have h1 : 1 ≤ C_weakHarnack0 (d := d) ^ 3 := by
    have := one_le_C_weakHarnack0 (d := d)
    nlinarith [this, sq_nonneg (C_weakHarnack0 (d := d))]
  have h01 : 1 ≤ C_weakHarnack0Forward (d := d) hd * C_weakHarnack0 d ^ 3 := by
    nlinarith [h0, h1]
  have h01_nonneg : 0 ≤ C_weakHarnack0Forward (d := d) hd * C_weakHarnack0 d ^ 3 := by
    exact le_trans (by norm_num : (0 : ℝ) ≤ 1) h01
  have hgeom : 1 ≤ C_chainGeom (d := d) hd := by
    unfold C_chainGeom
    have h1 :
        1 ≤ (((1 / 2 : ℝ) ^ (-(d : ℝ))) + 1) ^ 2 := by
      have hbase : 1 ≤ ((1 / 2 : ℝ) ^ (-(d : ℝ))) + 1 := by
        have hnonneg : 0 ≤ ((1 / 2 : ℝ) ^ (-(d : ℝ))) := by
          positivity
        linarith
      nlinarith [hbase]
    have h2 :
        1 ≤ (volume.real (ball (0 : E) (1 / 2 : ℝ)) + 1) ^ 2 := by
      have hbase : 1 ≤ volume.real (ball (0 : E) (1 / 2 : ℝ)) + 1 := by
        have hnonneg : 0 ≤ volume.real (ball (0 : E) (1 / 2 : ℝ)) := by
          exact measureReal_nonneg
        linarith
      nlinarith [hbase]
    have h3 :
        1 ≤
          (c_crossover' d ^ 2 + 1) ^
            ((((d : ℝ) * moserChi d) / 2) + ((d : ℝ) / 2)) := by
      have hbase : 1 ≤ c_crossover' d ^ 2 + 1 := by
        have hnonneg : 0 ≤ c_crossover' d ^ 2 := sq_nonneg _
        linarith
      have hexp_nonneg :
          0 ≤ (((d : ℝ) * moserChi d) / 2) + ((d : ℝ) / 2) := by
        have hchi_pos : 0 < moserChi d := moserChi_pos (d := d) hd
        positivity
      exact Real.one_le_rpow hbase hexp_nonneg
    have h4 : 1 ≤ (2 : ℝ) ^ ((d : ℝ) * moserChi d) := by
      have hexp_nonneg : 0 ≤ (d : ℝ) * moserChi d := by
        have hchi_pos : 0 < moserChi d := moserChi_pos (d := d) hd
        positivity
      exact Real.one_le_rpow (by norm_num : (1 : ℝ) ≤ 2) hexp_nonneg
    have h12 :
        1 ≤
          (((1 / 2 : ℝ) ^ (-(d : ℝ))) + 1) ^ 2 *
            (volume.real (ball (0 : E) (1 / 2 : ℝ)) + 1) ^ 2 := by
      nlinarith [h1, h2]
    have h12_nonneg :
        0 ≤
          (((1 / 2 : ℝ) ^ (-(d : ℝ))) + 1) ^ 2 *
            (volume.real (ball (0 : E) (1 / 2 : ℝ)) + 1) ^ 2 := by
      positivity
    calc
      (1 : ℝ)
          ≤ (((1 / 2 : ℝ) ^ (-(d : ℝ))) + 1) ^ 2 *
              (volume.real (ball (0 : E) (1 / 2 : ℝ)) + 1) ^ 2 := h12
      _ = ((((1 / 2 : ℝ) ^ (-(d : ℝ))) + 1) ^ 2 *
              (volume.real (ball (0 : E) (1 / 2 : ℝ)) + 1) ^ 2) * 1 := by ring
      _ ≤ ((((1 / 2 : ℝ) ^ (-(d : ℝ))) + 1) ^ 2 *
              (volume.real (ball (0 : E) (1 / 2 : ℝ)) + 1) ^ 2) *
            (c_crossover' d ^ 2 + 1) ^
              ((((d : ℝ) * moserChi d) / 2) + ((d : ℝ) / 2)) := by
            exact mul_le_mul_of_nonneg_left h3 h12_nonneg
      _ = ((((1 / 2 : ℝ) ^ (-(d : ℝ))) + 1) ^ 2 *
              (volume.real (ball (0 : E) (1 / 2 : ℝ)) + 1) ^ 2 *
              (c_crossover' d ^ 2 + 1) ^
                ((((d : ℝ) * moserChi d) / 2) + ((d : ℝ) / 2))) := by
            ring
  have hmid_nonneg : 0 ≤
      C_weakHarnack0Forward (d := d) hd * C_weakHarnack0 d ^ 3 * C_crossover' d := by
    have hcross_nonneg : 0 ≤ C_crossover' d := le_trans (by norm_num) one_le_C_crossover'
    exact mul_nonneg h01_nonneg hcross_nonneg
  calc
    (1 : ℝ) ≤ C_weakHarnack0Forward (d := d) hd * C_weakHarnack0 d ^ 3 := h01
    _ = (C_weakHarnack0Forward (d := d) hd * C_weakHarnack0 d ^ 3) * 1 := by ring
    _ ≤ (C_weakHarnack0Forward (d := d) hd * C_weakHarnack0 d ^ 3) * C_crossover' d := by
        exact mul_le_mul_of_nonneg_left one_le_C_crossover' h01_nonneg
    _ = (C_weakHarnack0Forward (d := d) hd * C_weakHarnack0 d ^ 3 * C_crossover' d) * 1 := by ring
    _ ≤ (C_weakHarnack0Forward (d := d) hd * C_weakHarnack0 d ^ 3 * C_crossover' d) *
          C_chainGeom (d := d) hd := by
        exact mul_le_mul_of_nonneg_left hgeom hmid_nonneg

private noncomputable def C_chain (hd : 2 < (d : ℝ)) : ℝ :=
  C_chainMain (d := d) hd *
    (((1 - c_crossover' d) / 2) ^ ((d : ℝ) * moserChi d))⁻¹

private theorem C_chainMain_le_C_chain (hd : 2 < (d : ℝ)) :
    C_chainMain (d := d) hd ≤ C_chain (d := d) hd := by
  let β : ℝ := (d : ℝ) * moserChi d
  have hβ_nonneg : 0 ≤ β := by
    dsimp [β]
    have hchi_pos : 0 < moserChi d := moserChi_pos (d := d) hd
    positivity
  have hmain_nonneg : 0 ≤ C_chainMain (d := d) hd := by
    exact le_trans (by norm_num : (0 : ℝ) ≤ 1) (one_le_C_chainMain (d := d) hd)
  have hbase_pos : 0 < (1 - c_crossover' d) / 2 := by
    have hc_lt_one : c_crossover' d < 1 := c_crossover'_lt_one (d := d)
    linarith
  have hpow_pos : 0 < ((1 - c_crossover' d) / 2) ^ β := by
    exact Real.rpow_pos_of_pos hbase_pos _
  have hbase_le_one : (1 - c_crossover' d) / 2 ≤ 1 := by
    have hc_pos : 0 < c_crossover' d := c_crossover'_pos (d := d)
    linarith
  have hpow_le_one : ((1 - c_crossover' d) / 2) ^ β ≤ 1 := by
    exact Real.rpow_le_one hbase_pos.le hbase_le_one hβ_nonneg
  have hinv_ge_one : 1 ≤ (((1 - c_crossover' d) / 2) ^ β)⁻¹ := by
    exact (one_le_inv₀ hpow_pos).2 hpow_le_one
  calc
    C_chainMain (d := d) hd
        = C_chainMain (d := d) hd * 1 := by ring
    _ ≤ C_chainMain (d := d) hd * (((1 - c_crossover' d) / 2) ^ β)⁻¹ := by
          exact mul_le_mul_of_nonneg_left hinv_ge_one hmain_nonneg
    _ = C_chain (d := d) hd := by
          unfold C_chain
          simp [β]

private theorem one_le_C_chain (hd : 2 < (d : ℝ)) : 1 ≤ C_chain (d := d) hd := by
  exact le_trans (one_le_C_chainMain (d := d) hd) (C_chainMain_le_C_chain (d := d) hd)

/-- The constant `C(d)` for the weak Harnack inequality.
The chain produces `(C_chain)^{1/p₀}` where the forward stage uses the honest
finite-measure-upgrade constant `C_weakHarnack0Forward`. Since
`1/p₀ = Λ^{1/2}/c'`, the stated bound has `(C_wH/(1-q)^{dχ/c'})^{Λ^{1/2}}`,
so `C_wH` must absorb `C_chain^{1/c'}`. -/
noncomputable def C_weakHarnack (d : ℕ) [NeZero d] (hd : 2 < (d : ℝ)) : ℝ :=
  (C_chain (d := d) hd) ^ (1 / c_crossover' d)

theorem one_le_C_weakHarnack (hd : 2 < (d : ℝ)) : 1 ≤ C_weakHarnack (d := d) hd := by
  unfold C_weakHarnack
  have hexp_nonneg : 0 ≤ 1 / c_crossover' d := by
    exact div_nonneg (by norm_num : (0 : ℝ) ≤ 1) (c_crossover'_pos (d := d)).le
  exact Real.one_le_rpow (one_le_C_chain (d := d) hd) hexp_nonneg

private theorem C_weakHarnack_eq_C_chain_rpow (hd : 2 < (d : ℝ)) :
    C_weakHarnack (d := d) hd = C_chain (d := d) hd ^ (1 / c_crossover' d) := by
  rfl

private theorem abs_rpow_neg_eq_abs_inv_rpow
    {a p : ℝ} (ha : 0 < a) :
    |a| ^ (-p) = |a⁻¹| ^ p := by
  rw [abs_of_pos ha, abs_of_pos (inv_pos.mpr ha)]
  calc
    a ^ (-p) = (a ^ p)⁻¹ := by
      rw [Real.rpow_neg ha.le]
    _ = (a⁻¹) ^ p := by
      rw [← Real.inv_rpow ha.le]

private theorem integral_abs_neg_eq_integral_abs_inv
    (A : NormalizedEllipticCoeff d (ball (0 : E) 1))
    {u : E → ℝ}
    (hu_pos : ∀ x ∈ ball (0 : E) 1, 0 < u x) :
    let p₀ := weakHarnackP0 A
    ∫ x in ball (0 : E) (1 / 2 : ℝ), |u x| ^ (-p₀) ∂volume =
      ∫ x in ball (0 : E) (1 / 2 : ℝ), |(u x)⁻¹| ^ p₀ ∂volume := by
  intro p₀
  refine integral_congr_ae ?_
  filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
  exact abs_rpow_neg_eq_abs_inv_rpow
    (hu_pos x ((Metric.ball_subset_ball (by norm_num : (1 / 2 : ℝ) ≤ 1)) hx))

omit [NeZero d] in
private theorem integral_half_power_mono_add_const
    {u : E → ℝ} {p : ℝ} (hp : 0 < p)
    (hu_pos : ∀ x ∈ ball (0 : E) 1, 0 < u x)
    {δ : ℝ} (hδ : 0 < δ)
    (hint :
      IntegrableOn (fun x => |u x| ^ p) (ball (0 : E) (1 / 2 : ℝ)) volume)
    (hintδ :
      IntegrableOn (fun x => |u x + δ| ^ p) (ball (0 : E) (1 / 2 : ℝ)) volume) :
    ∫ x in ball (0 : E) (1 / 2 : ℝ), |u x| ^ p ∂volume ≤
      ∫ x in ball (0 : E) (1 / 2 : ℝ), |u x + δ| ^ p ∂volume := by
  simpa [IntegrableOn] using
    integral_mono_ae hint hintδ <| by
      filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
      have hux_pos : 0 < u x :=
        hu_pos x ((Metric.ball_subset_ball (by norm_num : (1 / 2 : ℝ) ≤ 1)) hx)
      have huxδ_pos : 0 < u x + δ := by linarith [hux_pos, hδ]
      rw [abs_of_pos hux_pos, abs_of_pos huxδ_pos]
      exact Real.rpow_le_rpow (le_of_lt hux_pos) (by linarith) hp.le

omit [NeZero d] in
private theorem shifted_half_power_integrable
    {u : E → ℝ} {p δ : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hu_aesm :
      AEStronglyMeasurable u (volume.restrict (ball (0 : E) (1 / 2 : ℝ))))
    (hu_pos : ∀ x ∈ ball (0 : E) 1, 0 < u x)
    (hδ : 0 < δ)
    (hint :
      IntegrableOn (fun x => |u x| ^ p) (ball (0 : E) (1 / 2 : ℝ)) volume) :
    IntegrableOn (fun x => |u x + δ| ^ p) (ball (0 : E) (1 / 2 : ℝ)) volume := by
  rw [IntegrableOn] at hint ⊢
  have haesm :
      AEStronglyMeasurable (fun x => |u x + δ| ^ p)
        (volume.restrict (ball (0 : E) (1 / 2 : ℝ))) := by
    exact
      ((Real.continuous_rpow_const hp.le).measurable.comp_aemeasurable
        ((continuous_abs.measurable).comp_aemeasurable
          (hu_aesm.aemeasurable.add measurable_const.aemeasurable))).aestronglyMeasurable
  have hdom :
      Integrable (fun x => δ ^ p + |u x| ^ p)
        (volume.restrict (ball (0 : E) (1 / 2 : ℝ))) := by
    exact (integrableOn_const measure_ball_lt_top.ne).add hint
  refine Integrable.mono' hdom haesm ?_
  filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
  have hux_nonneg : 0 ≤ u x :=
    (hu_pos x ((Metric.ball_subset_ball (by norm_num : (1 / 2 : ℝ) ≤ 1)) hx)).le
  have hsubadd :
      (δ + u x) ^ p ≤ δ ^ p + u x ^ p :=
    Real.rpow_add_le_add_rpow hδ.le hux_nonneg hp.le hp1.le
  have hpow_nonneg : 0 ≤ |δ + u x| ^ p := by
    positivity
  have hδux_nonneg : 0 ≤ δ + u x := by linarith
  have hpow_nonneg' : 0 ≤ |u x + δ| ^ p := by
    simpa [add_comm] using hpow_nonneg
  have hsubadd' : (u x + δ) ^ p ≤ δ ^ p + u x ^ p := by
    simpa [add_comm] using hsubadd
  have huxδ_nonneg : 0 ≤ u x + δ := by
    linarith
  calc
    ‖|u x + δ| ^ p‖ = (u x + δ) ^ p := by
      rw [Real.norm_eq_abs, abs_of_nonneg hpow_nonneg', abs_of_nonneg huxδ_nonneg]
    _ ≤ δ ^ p + u x ^ p := hsubadd'
    _ = δ ^ p + |u x| ^ p := by
      rw [abs_of_nonneg hux_nonneg]

omit [NeZero d] in
private theorem shifted_half_inv_integrable
    {u : E → ℝ} {p δ : ℝ} (hp : 0 < p)
    (hu_aesm :
      AEStronglyMeasurable u (volume.restrict (ball (0 : E) (1 / 2 : ℝ))))
    (hu_pos : ∀ x ∈ ball (0 : E) 1, 0 < u x)
    (hδ : 0 < δ) :
    IntegrableOn (fun x => |(u x + δ)⁻¹| ^ p)
      (ball (0 : E) (1 / 2 : ℝ)) volume := by
  rw [IntegrableOn]
  have haesm :
      AEStronglyMeasurable (fun x => |(u x + δ)⁻¹| ^ p)
        (volume.restrict (ball (0 : E) (1 / 2 : ℝ))) := by
    exact
      ((Real.continuous_rpow_const hp.le).measurable.comp_aemeasurable
        ((continuous_abs.measurable).comp_aemeasurable
          ((hu_aesm.aemeasurable.add measurable_const.aemeasurable).inv))).aestronglyMeasurable
  have hdom :
      Integrable (fun _ : E => (δ⁻¹) ^ p)
        (volume.restrict (ball (0 : E) (1 / 2 : ℝ))) := by
    exact integrableOn_const measure_ball_lt_top.ne
  refine Integrable.mono' hdom haesm ?_
  filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
  have huxδ_pos : 0 < u x + δ := by
    have hux_pos :=
      hu_pos x ((Metric.ball_subset_ball (by norm_num : (1 / 2 : ℝ) ≤ 1)) hx)
    linarith
  have hux_pos :=
    hu_pos x ((Metric.ball_subset_ball (by norm_num : (1 / 2 : ℝ) ≤ 1)) hx)
  have hδ_le : δ ≤ u x + δ := by
    linarith
  have hle_inv : (u x + δ)⁻¹ ≤ δ⁻¹ := by
    rw [inv_le_inv₀ huxδ_pos hδ]
    exact hδ_le
  have hpow_nonneg : 0 ≤ |(u x + δ)⁻¹| ^ p := by
    positivity
  calc
    ‖|(u x + δ)⁻¹| ^ p‖ = ((u x + δ)⁻¹) ^ p := by
      rw [Real.norm_eq_abs, abs_of_nonneg hpow_nonneg, abs_of_pos (inv_pos.mpr huxδ_pos)]
    _ ≤ δ⁻¹ ^ p := by
      exact Real.rpow_le_rpow (inv_nonneg.mpr huxδ_pos.le) hle_inv hp.le

omit [NeZero d] in
private theorem shifted_half_inv_integral_pos
    {u : E → ℝ} {p δ : ℝ} (_hp : 0 < p)
    (hu_pos : ∀ x ∈ ball (0 : E) 1, 0 < u x)
    (hδ : 0 < δ)
    (hint :
      IntegrableOn (fun x => |(u x + δ)⁻¹| ^ p)
        (ball (0 : E) (1 / 2 : ℝ)) volume) :
    0 <
      ∫ x in ball (0 : E) (1 / 2 : ℝ), |(u x + δ)⁻¹| ^ p ∂volume := by
  have hnonneg :
      0 ≤ᵐ[volume.restrict (ball (0 : E) (1 / 2 : ℝ))] fun x => |(u x + δ)⁻¹| ^ p := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    positivity
  have hI_nonneg :
      0 ≤ ∫ x in ball (0 : E) (1 / 2 : ℝ), |(u x + δ)⁻¹| ^ p ∂volume := by
    exact integral_nonneg fun x => by positivity
  have hI_ne_zero :
      ∫ x in ball (0 : E) (1 / 2 : ℝ), |(u x + δ)⁻¹| ^ p ∂volume ≠ 0 := by
    intro hI_zero
    have hzero_ae :
        (fun x => |(u x + δ)⁻¹| ^ p) =ᵐ[volume.restrict (ball (0 : E) (1 / 2 : ℝ))] 0 := by
      rw [← sub_eq_zero] at hI_zero
      rwa [sub_zero, setIntegral_eq_zero_iff_of_nonneg_ae hnonneg hint] at hI_zero
    have hpos_ae :
        ∀ᵐ x ∂(volume.restrict (ball (0 : E) (1 / 2 : ℝ))), |(u x + δ)⁻¹| ^ p ≠ 0 := by
      filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
      have huxδ_pos : 0 < u x + δ := by
        have hux_pos :=
          hu_pos x ((Metric.ball_subset_ball (by norm_num : (1 / 2 : ℝ) ≤ 1)) hx)
        linarith
      have hpow_pos : 0 < |(u x + δ)⁻¹| ^ p := by
        rw [abs_of_pos (inv_pos.mpr huxδ_pos)]
        exact Real.rpow_pos_of_pos (inv_pos.mpr huxδ_pos) p
      exact hpow_pos.ne'
    have hfalse : ∀ᵐ x ∂(volume.restrict (ball (0 : E) (1 / 2 : ℝ))), False := by
      filter_upwards [hzero_ae, hpos_ae] with x hx0 hxpos
      exact hxpos hx0
    rw [ae_iff] at hfalse
    have hball_zero : volume (ball (0 : E) (1 / 2 : ℝ)) = 0 := by
      simpa [Measure.restrict_apply_univ] using hfalse
    exact (Metric.measure_ball_pos volume (0 : E) (by norm_num : (0 : ℝ) < 1 / 2)).ne'
      hball_zero
  exact lt_of_le_of_ne hI_nonneg (Ne.symm hI_ne_zero)

private theorem weak_harnack_inverse_factor_eq
    (A : NormalizedEllipticCoeff d (ball (0 : E) 1)) :
    A.1.Λ * weakHarnackP0 A ^ 2 + 1 = c_crossover' d ^ 2 + 1 := by
  rw [Λ_mul_p₀_sq]

private theorem weak_harnack_forward_factor_bound
    (hd : 2 < (d : ℝ))
    (A : NormalizedEllipticCoeff d (ball (0 : E) 1))
    {q : ℝ} (hq : 0 < q) (hq1 : q < 1) :
    (A.1.Λ * weakHarnackP0 A ^ 2 / (1 - q) ^ 2 + 1) ^ (((d : ℝ) * moserChi d) / 2) ≤
      (c_crossover' d ^ 2 + 1) ^ (((d : ℝ) * moserChi d) / 2) *
        (1 - q) ^ (-((d : ℝ) * moserChi d)) := by
  have h1q_pos : 0 < 1 - q := by linarith
  have h1q_sq_pos : 0 < (1 - q) ^ 2 := sq_pos_of_pos h1q_pos
  have h1q_sq_le_one : (1 - q) ^ 2 ≤ 1 := by
    nlinarith [hq.le]
  have hsq_inv_ge_one : 1 ≤ ((1 - q) ^ 2)⁻¹ := by
    exact (one_le_inv₀ h1q_sq_pos).2 h1q_sq_le_one
  set β : ℝ := (((d : ℝ) * moserChi d) / 2)
  have hbase_le :
      c_crossover' d ^ 2 / (1 - q) ^ 2 + 1 ≤
        (c_crossover' d ^ 2 + 1) / (1 - q) ^ 2 := by
    have haux : (1 : ℝ) ≤ 1 / (1 - q) ^ 2 := by
      simpa [one_div] using hsq_inv_ge_one
    calc
      c_crossover' d ^ 2 / (1 - q) ^ 2 + 1
          ≤ c_crossover' d ^ 2 / (1 - q) ^ 2 + 1 / (1 - q) ^ 2 := by
              gcongr
      _ = (c_crossover' d ^ 2 + 1) / (1 - q) ^ 2 := by
            field_simp [pow_ne_zero 2 (sub_ne_zero.mpr (ne_of_lt hq1))]
  have hβ_nonneg : 0 ≤ β := by
    dsimp [β]
    nlinarith [moserChi_pos (d := d) hd]
  have hpow_le :
      (c_crossover' d ^ 2 / (1 - q) ^ 2 + 1) ^ β ≤
        (((c_crossover' d ^ 2 + 1) / (1 - q) ^ 2) : ℝ) ^ β := by
    exact Real.rpow_le_rpow (by positivity) hbase_le hβ_nonneg
  have hsplit :
      (((c_crossover' d ^ 2 + 1) / (1 - q) ^ 2) : ℝ) ^ β =
        (c_crossover' d ^ 2 + 1) ^ β * ((1 - q) ^ 2) ^ (-β) := by
    calc
      (((c_crossover' d ^ 2 + 1) / (1 - q) ^ 2) : ℝ) ^ β
          = (c_crossover' d ^ 2 + 1) ^ β / ((1 - q) ^ 2) ^ β := by
              rw [Real.div_rpow (by positivity) (by positivity)]
      _ = (c_crossover' d ^ 2 + 1) ^ β * (((1 - q) ^ 2) ^ β)⁻¹ := by
            rw [div_eq_mul_inv]
      _ = (c_crossover' d ^ 2 + 1) ^ β * ((1 - q) ^ 2) ^ (-β) := by
            rw [← Real.rpow_neg h1q_sq_pos.le]
  have hden_rw : ((1 - q) ^ 2) ^ (-β) = (1 - q) ^ (-((d : ℝ) * moserChi d)) := by
    have hsq_as_rpow : ((1 - q) ^ 2 : ℝ) = (1 - q) ^ (2 : ℝ) := by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rw [hsq_as_rpow, ← Real.rpow_mul h1q_pos.le]
    congr 1
    dsimp [β]
    ring
  calc
    (A.1.Λ * weakHarnackP0 A ^ 2 / (1 - q) ^ 2 + 1) ^ (((d : ℝ) * moserChi d) / 2)
        = (c_crossover' d ^ 2 / (1 - q) ^ 2 + 1) ^ β := by
            dsimp [β]
            congr 2
            rw [Λ_mul_p₀_sq]
    _ ≤ (((c_crossover' d ^ 2 + 1) / (1 - q) ^ 2) : ℝ) ^ β := hpow_le
    _ = (c_crossover' d ^ 2 + 1) ^ β * ((1 - q) ^ 2) ^ (-β) := hsplit
    _ = (c_crossover' d ^ 2 + 1) ^ β * (1 - q) ^ (-((d : ℝ) * moserChi d)) := by
          rw [hden_rw]

set_option maxHeartbeats 755000

/-! ### Three-stage chain -/

/-- Shifted `p₀ < q` branch of the three-stage weak-Harnack chain. -/
private theorem weak_harnack_chain_shifted
    (hd : 2 < (d : ℝ))
    (A : NormalizedEllipticCoeff d (ball (0 : E) 1))
    {u : E → ℝ} {q : ℝ}
    (hq : 0 < q) (hq1 : q < 1)
    (hu_pos : ∀ x ∈ ball (0 : E) 1, 0 < u x)
    (hsuper : IsSupersolution A.1 u)
    (hpq : weakHarnackP0 A < q)
    {δ : ℝ} (hδ : 0 < δ) :
    let p₀ := weakHarnackP0 A
    (∫ x in ball (0 : E) (1 / 4 : ℝ),
        |u x| ^ (q * (d : ℝ) / ((d : ℝ) - 2)) ∂volume) ^
          (p₀ * (((d : ℝ) - 2) / (q * (d : ℝ)))) ≤
      C_chainMain (d := d) hd / (1 - q) ^ ((d : ℝ) * moserChi d) *
        (essInf u (volume.restrict (ball (0 : E) (1 / 4 : ℝ))) + δ) ^ p₀ := by
  intro p₀
  have hp₀ := p₀_pos A
  have hp₀_lt := p₀_lt_one A
  -- Define the rescaled problem: v(z) = u(z/2), A' = rescaled coefficients.
  let A' := rescaledCoeff A
  let v : E → ℝ := fun z => u ((1 / 2 : ℝ) • z)
  -- v is a positive supersolution on B_1 (via rescaleToUnitBall_isSupersolution).
  -- A'.Λ = A.Λ (via rescaledCoeff_Λ_eq), so weakHarnackP0 A' = p₀.

  -- === Prerequisites: v is a positive supersolution on B_1 for A' ===
  have hv_pos : ∀ x ∈ ball (0 : E) 1, 0 < v x := by
    intro z hz
    show 0 < u ((1 / 2 : ℝ) • z)
    apply hu_pos
    rw [Metric.mem_ball, dist_zero_right] at hz ⊢
    rw [norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    linarith
  -- v is a supersolution for A'.1. This follows from rescaleToUnitBall_isSupersolution
  -- after restricting u's supersolution to B_{1/2}.
  have hv_super : IsSupersolution A'.1 v := by
    have hR : (0 : ℝ) < 1 / 2 := by norm_num
    have hsub : Metric.closedBall (0 : E) (1 / 2 : ℝ) ⊆ ball (0 : E) 1 :=
      Metric.closedBall_subset_ball (by norm_num)
    have hsuper_half :=
      hsuper.restrict_ball (d := d) Metric.isOpen_ball hR hsub
    have hrescale :=
      rescaleToUnitBall_isSupersolution (d := d) (x₀ := (0 : E)) hR _ hsuper_half
    convert hrescale using 2
    ext z; show v z = u (0 + (1 / 2) • z); simp [v, zero_add]
  -- A' has the same Λ as A, so the same p₀.
  have hΛ_eq : A'.1.Λ = A.1.Λ := rescaledCoeff_Λ_eq A
  have hp₀_eq : weakHarnackP0 A' = p₀ := by
    show weakHarnackP0 A' = weakHarnackP0 A
    unfold weakHarnackP0; rw [hΛ_eq]
  have hp₀_def : p₀ = weakHarnackP0 A := by rfl
  -- Key arithmetic: Λ·p₀² = c'² (dimension-only constant).
  have hΛp₀sq := Λ_mul_p₀_sq A

  -- Forward Moser estimate on the rescaled supersolution `v`.
  have hpq' : p₀ < q := by
    simpa [hp₀_def] using hpq
  have hfwd :=
    weak_harnack_stage_one_forward hd A' hp₀ hp₀_lt hpq' hq1 hv_pos hv_super
  -- hfwd : (∫ z ∈ B_{1/2}, |v z|^{q*})^{p₀·(d-2)/(qd)} ≤
  --          C₀ · (A'.Λ·p₀²/(1-q)²+1)^{d/2} · ∫ z ∈ B_1, |v z|^{p₀}

  -- Change of variables for the v-integrals using integral_rescale_ball.
  -- ∫_{B_1} |v z|^{p₀} dz = ∫_{B_1} |u((1/2)z)|^{p₀} dz
  --                        = (1/2)^{-d} · ∫_{B_{1/2}} |u x|^{p₀} dx
  have hcov_rhs :
      ∫ z in ball (0 : E) 1, |v z| ^ p₀ ∂volume =
        ((1 / 2 : ℝ) ^ Module.finrank ℝ E)⁻¹ *
          ∫ x in ball (0 : E) (1 / 2 : ℝ), |u x| ^ p₀ ∂volume := by
    show ∫ z in ball (0 : E) 1, |u ((1 / 2 : ℝ) • z)| ^ p₀ ∂volume = _
    exact integral_rescale_ball (by norm_num : (0 : ℝ) < 1 / 2)
      (fun x => |u x| ^ p₀)
  -- ∫_{B_{1/2}} |v z|^{q*} dz = (1/2)^{-d} · ∫_{B_{1/4}} |u x|^{q*} dx
  -- (since (1/2)·B_{1/2} = B_{1/4})
  set q_star := q * (d : ℝ) / ((d : ℝ) - 2) with hq_star_def
  have hcov_lhs :
      ∫ z in ball (0 : E) (1 / 2 : ℝ), |v z| ^ q_star ∂volume =
        ((1 / 2 : ℝ) ^ Module.finrank ℝ E)⁻¹ *
          ∫ x in ball (0 : E) (1 / 4 : ℝ), |u x| ^ q_star ∂volume := by
    show ∫ z in ball (0 : E) (1 / 2 : ℝ), |u ((1 / 2 : ℝ) • z)| ^ q_star ∂volume = _
    have h14 : (1 / 2 : ℝ) * (1 / 2 : ℝ) = 1 / 4 := by norm_num
    rw [← h14]
    exact integral_rescale_ball_general (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (0 : ℝ) < 1 / 2) (fun x => |u x| ^ q_star)
  -- Substitute COV into hfwd and replace A'.1.Λ with A.1.Λ:
  rw [hcov_lhs, hcov_rhs] at hfwd
  rw [hΛ_eq] at hfwd

  -- Crossover estimate on the half-ball.
  have hcross := crossover_estimate_unaveraged hd A hu_pos hsuper
  -- hcross: (∫_{B_{1/2}} |u|^{p₀}) · (∫_{B_{1/2}} |u|^{-p₀}) ≤ C_cross'·vol²

  -- Inverse Moser estimate on the rescaled supersolution `v`.
  have hinv := weak_harnack_stage_one_inverse hd A' hp₀ hv_pos hv_super
  -- hinv: (Λ·p₀²+1)^{-d/2} · (∫_{B_1} |v⁻¹|^{p₀})⁻¹ ≤ C₀ · (essInf v μhalf)^{p₀}

  -- COV for the inverse integral:
  -- ∫_{B_1} |(v z)⁻¹|^{p₀} dz = 2^d · ∫_{B_{1/2}} |(u x)⁻¹|^{p₀} dx
  have hcov_inv :
      ∫ z in ball (0 : E) 1, |(v z)⁻¹| ^ p₀ ∂volume =
        ((1 / 2 : ℝ) ^ Module.finrank ℝ E)⁻¹ *
          ∫ x in ball (0 : E) (1 / 2 : ℝ), |(u x)⁻¹| ^ p₀ ∂volume := by
    show ∫ z in ball (0 : E) 1, |(u ((1 / 2 : ℝ) • z))⁻¹| ^ p₀ ∂volume = _
    exact integral_rescale_ball (by norm_num : (0 : ℝ) < 1 / 2)
      (fun x => |(u x)⁻¹| ^ p₀)
  -- Substitute COV into hinv so its integral term matches I_neg:
  rw [hcov_inv] at hinv

  -- COV for essInf:
  -- essInf v (volume.restrict (ball 0 (1/2))) = essInf u (volume.restrict (ball 0 (1/4)))
  have hcov_essInf :
      essInf v (volume.restrict (ball (0 : E) (1 / 2 : ℝ))) =
        essInf u (volume.restrict (ball (0 : E) (1 / 4 : ℝ))) := by
    have h := essInf_rescale_halfBall (d := d) (x₀ := (0 : E)) (R := 1 / 2)
      (by norm_num : (0 : ℝ) < 1 / 2) (u := u)
    simp only [zero_add, show (1 / 2 : ℝ) / 2 = 1 / 4 from by norm_num] at h
    exact h
  -- Substitute essInf COV and Λ equality into hinv:
  rw [hcov_essInf] at hinv
  rw [hΛ_eq] at hinv
  -- Now hinv reads (after all substitutions):
  --   (A.1.Λ·p₀²+1)^{-d/2} · (C_vol * I_neg)⁻¹ ≤ C₀ · inf_u^{p₀}
  -- where C_vol = ((1/2)^d)⁻¹, I_neg = ∫_{B_{1/2}} |(u x)⁻¹|^{p₀}, inf_u = essInf_{B_{1/4}} u.

  -- Combine the forward, crossover, and inverse estimates.
  -- After substituting COV into hfwd, hcross, hinv, the integrals on B_{1/2} match.
  -- We use Λ·p₀² = c'² (hΛp₀sq) so (c'²/(1-q)²+1)^{d/2} ≤ (1/(1-q)²+1)^{d/2}
  -- ≤ C·(1-q)^{-d}, and the three C₀ factors combine into C₀³·C_cross' = C_chain.
  --
  -- Abbreviations for the key integrals (after COV substitution):
  set C_vol := ((1 / 2 : ℝ) ^ Module.finrank ℝ E)⁻¹ with hC_vol_def
  set I_fwd := ∫ x in ball (0 : E) (1 / 4 : ℝ), |u x| ^ q_star ∂volume
  set I_pos := ∫ x in ball (0 : E) (1 / 2 : ℝ), |u x| ^ p₀ ∂volume
  set I_neg := ∫ x in ball (0 : E) (1 / 2 : ℝ), |(u x)⁻¹| ^ p₀ ∂volume
  set inf_u := essInf u (volume.restrict (ball (0 : E) (1 / 4 : ℝ)))
  -- After COV + rw, hfwd reads:
  --   (C_vol * I_fwd)^{p₀·(d-2)/(q·d)} ≤ C₀·(A.1.Λ·p₀²/(1-q)²+1)^{d/2}·(C_vol * I_pos)
  -- After COV + rw, hinv reads:
  --   (A.1.Λ·p₀²+1)^{-d/2} · (C_vol * I_neg)⁻¹ ≤ C₀ · inf_u^{p₀}
  -- hcross reads:
  --   I_pos * (∫_{B_{1/2}} |u|^{-p₀}) ≤ C_cross' · vol(B_{1/2})²
  -- Note: |u x|^{-p₀} = |(u x)⁻¹|^{p₀} for u x > 0, so ∫|u|^{-p₀} = I_neg.

  -- The chain in calc form:
  show I_fwd ^ (p₀ * (((d : ℝ) - 2) / (q * (d : ℝ)))) ≤
    C_chainMain (d := d) hd / (1 - q) ^ ((d : ℝ) * moserChi d) *
      (inf_u + δ) ^ p₀
  have hμhalf_le :
      volume.restrict (ball (0 : E) (1 / 2 : ℝ)) ≤
        volume.restrict (ball (0 : E) 1) := by
    have hsubset :
        ball (0 : E) (1 / 2 : ℝ) ⊆ ball (0 : E) 1 :=
      Metric.ball_subset_ball (by norm_num : (1 / 2 : ℝ) ≤ 1)
    exact Measure.restrict_mono_set volume hsubset
  haveI : IsFiniteMeasure (volume.restrict (ball (0 : E) 1)) := by
    rw [isFiniteMeasure_restrict]
    exact measure_ball_lt_top.ne
  let huW : MemW1pWitness 2 u (ball (0 : E) 1) := hsuper.1.someWitness
  have hu_aesm_half :
      AEStronglyMeasurable u (volume.restrict (ball (0 : E) (1 / 2 : ℝ))) := by
    exact huW.memLp.aestronglyMeasurable.mono_measure hμhalf_le
  have hp₀_le_two : p₀ ≤ 2 := by
    linarith
  have hu_memLp_p₀_ball1 :
      MemLp u (ENNReal.ofReal p₀) (volume.restrict (ball (0 : E) 1)) := by
    exact huW.memLp.mono_exponent <| by
      simpa using (ENNReal.ofReal_le_ofReal hp₀_le_two)
  have hint_ball1 :
      IntegrableOn (fun x => |u x| ^ p₀) (ball (0 : E) 1) volume := by
    rw [IntegrableOn, ← memLp_one_iff_integrable]
    have hp₀_enn_ne_zero : ENNReal.ofReal p₀ ≠ 0 := by
      positivity
    have hnorm_rpow :
        MemLp (fun x => ‖u x‖ ^ (ENNReal.ofReal p₀).toReal) 1
          (volume.restrict (ball (0 : E) 1)) :=
      hu_memLp_p₀_ball1.norm_rpow hp₀_enn_ne_zero ENNReal.ofReal_ne_top
    rw [ENNReal.toReal_ofReal hp₀.le] at hnorm_rpow
    simpa [Real.norm_eq_abs] using hnorm_rpow
  have hint_half :
      IntegrableOn (fun x => |u x| ^ p₀) (ball (0 : E) (1 / 2 : ℝ)) volume := by
    rw [IntegrableOn] at hint_ball1 ⊢
    exact hint_ball1.mono_measure hμhalf_le
  have hμquarter_ne_zero :
      volume.restrict (ball (0 : E) (1 / 4 : ℝ)) ≠ 0 := by
    intro hzero
    have hball_zero : volume (ball (0 : E) (1 / 4 : ℝ)) = 0 := by
      simpa [Measure.restrict_apply_univ] using
        congrArg (fun μ : Measure E => μ Set.univ) hzero
    exact (Metric.measure_ball_pos volume (0 : E) (by norm_num : (0 : ℝ) < 1 / 4)).ne'
      hball_zero
  have hquarter_nonneg :
      ∀ᵐ x ∂(volume.restrict (ball (0 : E) (1 / 4 : ℝ))), 0 ≤ u x := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    exact (hu_pos x ((Metric.ball_subset_ball (by norm_num : (1 / 4 : ℝ) ≤ 1)) hx)).le
  have hinf_nonneg : 0 ≤ inf_u := by
    dsimp [inf_u]
    exact le_essInf_real_of_ae_le (d := d) hμquarter_ne_zero hquarter_nonneg
  have hq_star_pos : 0 < q_star := by
    dsimp [q_star]
    have hdm2 : 0 < (d : ℝ) - 2 := by linarith
    exact div_pos (mul_pos hq (by positivity)) hdm2
  have hα_nonneg : 0 ≤ p₀ * (((d : ℝ) - 2) / (q * (d : ℝ))) := by
    have hdm2 : 0 < (d : ℝ) - 2 := by linarith
    positivity
  have hI_fwd_nonneg : 0 ≤ I_fwd := by
    dsimp [I_fwd]
    exact integral_nonneg fun x => by positivity
  have hC_vol_pos : 0 < C_vol := by
    dsimp [C_vol]
    positivity
  have hC_vol_nonneg : 0 ≤ C_vol := hC_vol_pos.le
  have hC_vol_ge_one : 1 ≤ C_vol := by
    dsimp [C_vol]
    have hpow_pos : 0 < (1 / 2 : ℝ) ^ Module.finrank ℝ E := by positivity
    have hpow_le_one : (1 / 2 : ℝ) ^ Module.finrank ℝ E ≤ 1 := by
      have hfin : Module.finrank ℝ E = d := by simp [AmbientSpace]
      rw [hfin]
      exact pow_le_one₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) ≤ 1)
    exact (one_le_inv₀ hpow_pos).2 hpow_le_one
  have hforward_bound :
      I_fwd ^ (p₀ * (((d : ℝ) - 2) / (q * (d : ℝ)))) ≤
        C_weakHarnack0Forward (d := d) hd *
          (A.1.Λ * p₀ ^ 2 / (1 - q) ^ 2 + 1) ^ (((d : ℝ) * moserChi d) / 2) *
          C_vol * I_pos := by
    have hI_le : I_fwd ≤ C_vol * I_fwd := by
      nlinarith [hI_fwd_nonneg, hC_vol_ge_one]
    have hpow_le :=
      Real.rpow_le_rpow hI_fwd_nonneg hI_le hα_nonneg
    calc
      I_fwd ^ (p₀ * (((d : ℝ) - 2) / (q * (d : ℝ))))
          ≤ (C_vol * I_fwd) ^ (p₀ * (((d : ℝ) - 2) / (q * (d : ℝ)))) := hpow_le
      _ ≤ C_weakHarnack0Forward (d := d) hd *
            (A.1.Λ * p₀ ^ 2 / (1 - q) ^ 2 + 1) ^ (((d : ℝ) * moserChi d) / 2) *
            (C_vol * I_pos) := by
              simpa [I_fwd, I_pos, C_vol, q_star] using hfwd
      _ = C_weakHarnack0Forward (d := d) hd *
            (A.1.Λ * p₀ ^ 2 / (1 - q) ^ 2 + 1) ^ (((d : ℝ) * moserChi d) / 2) *
            C_vol * I_pos := by ring
  have hbound_shift :
        I_fwd ^ (p₀ * (((d : ℝ) - 2) / (q * (d : ℝ)))) ≤
          C_chainMain (d := d) hd / (1 - q) ^ ((d : ℝ) * moserChi d) *
            (inf_u + δ) ^ p₀ := by
      let uδ : E → ℝ := fun x => u x + δ
      let vδ : E → ℝ := fun z => v z + δ
      let I_pos_shift : ℝ := ∫ x in ball (0 : E) (1 / 2 : ℝ), |u x + δ| ^ p₀ ∂volume
      let J_shift : ℝ := ∫ x in ball (0 : E) (1 / 2 : ℝ), |(u x + δ)⁻¹| ^ p₀ ∂volume
      have huδ_pos : ∀ x ∈ ball (0 : E) 1, 0 < uδ x := by
        intro x hx
        dsimp [uδ]
        linarith [hu_pos x hx]
      have hvδ_pos : ∀ z ∈ ball (0 : E) 1, 0 < vδ z := by
        intro z hz
        dsimp [vδ, v]
        linarith [hv_pos z hz]
      have hsuperδ : IsSupersolution A.1 uδ := by
        dsimp [uδ]
        exact isSupersolution_add_const_unitBall A hsuper δ
      have hvδ_super : IsSupersolution A'.1 vδ := by
        dsimp [vδ]
        exact isSupersolution_add_const_unitBall A' hv_super δ
      have hint_shift_half :
          IntegrableOn (fun x => |u x + δ| ^ p₀) (ball (0 : E) (1 / 2 : ℝ)) volume := by
        exact shifted_half_power_integrable hp₀ hp₀_lt hu_aesm_half hu_pos hδ hint_half
      have hI_pos_mono : I_pos ≤ I_pos_shift := by
        simpa [I_pos, I_pos_shift] using
          integral_half_power_mono_add_const hp₀ hu_pos hδ hint_half hint_shift_half
      have hJ_shift_int :
          IntegrableOn (fun x => |(u x + δ)⁻¹| ^ p₀)
            (ball (0 : E) (1 / 2 : ℝ)) volume := by
        exact shifted_half_inv_integrable hp₀ hu_aesm_half hu_pos hδ
      have hJ_shift_pos : 0 < J_shift := by
        simpa [J_shift] using
          shifted_half_inv_integral_pos hp₀ hu_pos hδ hJ_shift_int
      have hcross_shift_raw := crossover_estimate_unaveraged hd A huδ_pos hsuperδ
      have hneg_eq :
          ∫ x in ball (0 : E) (1 / 2 : ℝ), |u x + δ| ^ (-p₀) ∂volume = J_shift := by
        simpa [J_shift] using
          (integral_abs_neg_eq_integral_abs_inv
            (A := A) (u := fun x => u x + δ) huδ_pos)
      have hcross_shift :
          I_pos_shift * J_shift ≤
            C_crossover' d * (volume.real (ball (0 : E) (1 / 2 : ℝ))) ^ 2 := by
        rw [← hneg_eq]
        simpa [I_pos_shift, p₀, weakHarnackP0] using hcross_shift_raw
      have hcov_inv_shift :
          ∫ z in ball (0 : E) 1, |(vδ z)⁻¹| ^ p₀ ∂volume = C_vol * J_shift := by
        dsimp [vδ, v, C_vol, J_shift]
        exact integral_rescale_ball (by norm_num : (0 : ℝ) < 1 / 2)
          (fun x => |(u x + δ)⁻¹| ^ p₀)
      have hcov_essInf_shift :
          essInf vδ (volume.restrict (ball (0 : E) (1 / 2 : ℝ))) =
            essInf (fun x => u x + δ) (volume.restrict (ball (0 : E) (1 / 4 : ℝ))) := by
        have h := essInf_rescale_halfBall (d := d) (x₀ := (0 : E)) (R := 1 / 2)
          (by norm_num : (0 : ℝ) < 1 / 2) (u := fun x => u x + δ)
        simp only [zero_add, show (1 / 2 : ℝ) / 2 = 1 / 4 from by norm_num] at h
        exact h
      have hu_bdd_below :
          Filter.IsBoundedUnder (· ≥ ·)
            (ae (volume.restrict (ball (0 : E) (1 / 4 : ℝ)))) u := ⟨0, hquarter_nonneg⟩
      have hquarter_shift_nonneg :
          ∀ᵐ x ∂(volume.restrict (ball (0 : E) (1 / 4 : ℝ))), δ ≤ u x + δ := by
        filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
        linarith [hu_pos x ((Metric.ball_subset_ball (by norm_num : (1 / 4 : ℝ) ≤ 1)) hx)]
      have hu_shift_bdd_below :
          Filter.IsBoundedUnder (· ≥ ·)
            (ae (volume.restrict (ball (0 : E) (1 / 4 : ℝ)))) (fun x => u x + δ) :=
        ⟨δ, hquarter_shift_nonneg⟩
      have hessInf_shift :
          essInf (fun x => u x + δ) (volume.restrict (ball (0 : E) (1 / 4 : ℝ))) =
            inf_u + δ := by
        dsimp [inf_u]
        exact essInf_add_const hμquarter_ne_zero δ hu_bdd_below hu_shift_bdd_below
      have hinv_shift := weak_harnack_stage_one_inverse hd A' hp₀ hvδ_pos hvδ_super
      rw [hcov_inv_shift, hcov_essInf_shift, hessInf_shift, hΛ_eq] at hinv_shift
      set L : ℝ := A.1.Λ * p₀ ^ 2 + 1
      have hL_pos : 0 < L := by
        dsimp [L]
        nlinarith [A.1.Λ_nonneg, sq_nonneg p₀]
      have hLneg :
          L ^ (-(d : ℝ) / 2) = (L ^ ((d : ℝ) / 2))⁻¹ := by
        rw [show (-(d : ℝ) / 2) = -((d : ℝ) / 2) by ring, Real.rpow_neg hL_pos.le]
      have hCvolJ_inv :
          (C_vol * J_shift)⁻¹ ≤
            C_weakHarnack0 d * (inf_u + δ) ^ p₀ * L ^ ((d : ℝ) / 2) := by
        have hineq :
            (C_vol * J_shift)⁻¹ * L ^ (-(d : ℝ) / 2) ≤
              C_weakHarnack0 d * (inf_u + δ) ^ p₀ := by
          simpa [L, mul_comm, mul_left_comm, mul_assoc] using hinv_shift
        have hstep :
            (C_vol * J_shift)⁻¹ ≤
              (C_weakHarnack0 d * (inf_u + δ) ^ p₀) /
                (L ^ (-(d : ℝ) / 2)) := by
          exact (le_div_iff₀ (Real.rpow_pos_of_pos hL_pos _)).2 hineq
        calc
          (C_vol * J_shift)⁻¹
              ≤ (C_weakHarnack0 d * (inf_u + δ) ^ p₀) /
                  (L ^ (-(d : ℝ) / 2)) := hstep
          _ = C_weakHarnack0 d * (inf_u + δ) ^ p₀ * L ^ ((d : ℝ) / 2) := by
                rw [hLneg, div_eq_mul_inv, inv_inv, mul_assoc]
      have hJinv :
          J_shift⁻¹ ≤
            C_vol * C_weakHarnack0 d *
              (c_crossover' d ^ 2 + 1) ^ ((d : ℝ) / 2) *
              (inf_u + δ) ^ p₀ := by
        calc
          J_shift⁻¹ = C_vol * (C_vol * J_shift)⁻¹ := by
            field_simp [hC_vol_pos.ne', hJ_shift_pos.ne']
          _ ≤ C_vol * (C_weakHarnack0 d * (inf_u + δ) ^ p₀ * L ^ ((d : ℝ) / 2)) := by
                exact mul_le_mul_of_nonneg_left hCvolJ_inv hC_vol_nonneg
          _ = C_vol * C_weakHarnack0 d * L ^ ((d : ℝ) / 2) * (inf_u + δ) ^ p₀ := by
                ring
          _ = C_vol * C_weakHarnack0 d *
                (c_crossover' d ^ 2 + 1) ^ ((d : ℝ) / 2) *
                (inf_u + δ) ^ p₀ := by
                have hL_eq : L = c_crossover' d ^ 2 + 1 := by
                  dsimp [L, p₀]
                  rw [weak_harnack_inverse_factor_eq (A := A)]
                rw [hL_eq]
      have hI_pos_shift :
          I_pos_shift ≤
            C_crossover' d * (volume.real (ball (0 : E) (1 / 2 : ℝ))) ^ 2 * J_shift⁻¹ := by
        calc
          I_pos_shift = I_pos_shift * J_shift * J_shift⁻¹ := by
            field_simp [hJ_shift_pos.ne']
          _ ≤
              (C_crossover' d * (volume.real (ball (0 : E) (1 / 2 : ℝ))) ^ 2) *
                J_shift⁻¹ := by
                  gcongr
          _ = C_crossover' d * (volume.real (ball (0 : E) (1 / 2 : ℝ))) ^ 2 * J_shift⁻¹ := by
                ring
      have hC_vol_eq : C_vol = (1 / 2 : ℝ) ^ (-(d : ℝ)) := by
        dsimp [C_vol]
        have hfin : Module.finrank ℝ E = d := by simp [AmbientSpace]
        rw [hfin]
        rw [show (((1 / 2 : ℝ) ^ d)⁻¹) = (((1 / 2 : ℝ) ^ (d : ℝ))⁻¹) by
          rw [Real.rpow_natCast]]
        rw [show (((1 / 2 : ℝ) ^ (d : ℝ))⁻¹) = (1 / 2 : ℝ) ^ (-(d : ℝ)) by
          symm
          exact Real.rpow_neg (x := (1 / 2 : ℝ)) (y := (d : ℝ))
            (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      have hC_vol_sq_bound :
          C_vol ^ 2 ≤ (((1 / 2 : ℝ) ^ (-(d : ℝ))) + 1) ^ 2 := by
        have hbase_le : C_vol ≤ ((1 / 2 : ℝ) ^ (-(d : ℝ))) + 1 := by
          rw [hC_vol_eq]
          have hnonneg : 0 ≤ (1 / 2 : ℝ) ^ (-(d : ℝ)) := by positivity
          linarith
        have hbase_nonneg : 0 ≤ ((1 / 2 : ℝ) ^ (-(d : ℝ))) + 1 := by positivity
        have hbase_abs :
            |C_vol| ≤ |((1 / 2 : ℝ) ^ (-(d : ℝ))) + 1| := by
          rw [abs_of_nonneg hC_vol_nonneg, abs_of_nonneg hbase_nonneg]
          exact hbase_le
        exact (sq_le_sq).2 hbase_abs
      have hvol_sq_bound :
          (volume.real (ball (0 : E) (1 / 2 : ℝ))) ^ 2 ≤
            (volume.real (ball (0 : E) (1 / 2 : ℝ)) + 1) ^ 2 := by
        have hnonneg : 0 ≤ volume.real (ball (0 : E) (1 / 2 : ℝ)) := measureReal_nonneg
        have hbase_le :
            volume.real (ball (0 : E) (1 / 2 : ℝ)) ≤
              volume.real (ball (0 : E) (1 / 2 : ℝ)) + 1 := by
          linarith
        have hbig_nonneg : 0 ≤ volume.real (ball (0 : E) (1 / 2 : ℝ)) + 1 := by positivity
        have habs :
            |volume.real (ball (0 : E) (1 / 2 : ℝ))| ≤
              |volume.real (ball (0 : E) (1 / 2 : ℝ)) + 1| := by
          rw [abs_of_nonneg hnonneg, abs_of_nonneg hbig_nonneg]
          exact hbase_le
        exact (sq_le_sq).2 habs
      have hgeom_bound :
          C_vol ^ 2 * (volume.real (ball (0 : E) (1 / 2 : ℝ))) ^ 2 *
            (c_crossover' d ^ 2 + 1) ^
              ((((d : ℝ) * moserChi d) / 2) + ((d : ℝ) / 2)) ≤
            C_chainGeom (d := d) hd := by
        let G : ℝ :=
          (c_crossover' d ^ 2 + 1) ^
            ((((d : ℝ) * moserChi d) / 2) + ((d : ℝ) / 2))
        have hG_nonneg : 0 ≤ G := by
          dsimp [G]
          positivity
        have hmul12 :
            C_vol ^ 2 * (volume.real (ball (0 : E) (1 / 2 : ℝ))) ^ 2 ≤
              (((1 / 2 : ℝ) ^ (-(d : ℝ))) + 1) ^ 2 *
                (volume.real (ball (0 : E) (1 / 2 : ℝ)) + 1) ^ 2 := by
          exact mul_le_mul hC_vol_sq_bound hvol_sq_bound
            (by positivity) (by positivity)
        have hmul12G :
            (C_vol ^ 2 * (volume.real (ball (0 : E) (1 / 2 : ℝ))) ^ 2) * G ≤
              ((((1 / 2 : ℝ) ^ (-(d : ℝ))) + 1) ^ 2 *
                  (volume.real (ball (0 : E) (1 / 2 : ℝ)) + 1) ^ 2) * G := by
          exact mul_le_mul_of_nonneg_right hmul12 hG_nonneg
        simpa [G, C_chainGeom, mul_assoc, mul_left_comm, mul_comm] using hmul12G
      have hC0_pow :
          C_weakHarnack0 d ≤ C_weakHarnack0 d ^ 3 := by
        have hC0_ge_one := one_le_C_weakHarnack0 (d := d)
        have hC0_nonneg : 0 ≤ C_weakHarnack0 d := by
          exact le_trans (by norm_num : (0 : ℝ) ≤ 1) hC0_ge_one
        have hC0_sq_ge_one : 1 ≤ C_weakHarnack0 d ^ 2 := by
          have hmul :
              (1 : ℝ) * 1 ≤ C_weakHarnack0 d * C_weakHarnack0 d := by
            exact mul_le_mul hC0_ge_one hC0_ge_one (by positivity) (by positivity)
          simpa [pow_two] using hmul
        have hmul :
            C_weakHarnack0 d * 1 ≤ C_weakHarnack0 d * (C_weakHarnack0 d ^ 2) := by
          exact mul_le_mul_of_nonneg_left hC0_sq_ge_one hC0_nonneg
        simpa [pow_two, pow_three, mul_assoc] using hmul
      have hsmall_to_chain :
          (C_weakHarnack0Forward (d := d) hd * C_weakHarnack0 d * C_crossover' d) *
            C_chainGeom (d := d) hd ≤
            C_chainMain (d := d) hd := by
        have hfwd_nonneg : 0 ≤ C_weakHarnack0Forward (d := d) hd := by
          exact le_trans (by norm_num : (0 : ℝ) ≤ 1) (one_le_C_weakHarnack0Forward (d := d) hd)
        have hcross_nonneg : 0 ≤ C_crossover' d := by
          exact le_trans (by norm_num : (0 : ℝ) ≤ 1) one_le_C_crossover'
        have hgeom_nonneg : 0 ≤ C_chainGeom (d := d) hd := by
          unfold C_chainGeom
          positivity
        have hcoeff_inner :
            C_weakHarnack0 d * C_crossover' d ≤ C_weakHarnack0 d ^ 3 * C_crossover' d := by
          exact mul_le_mul_of_nonneg_right hC0_pow hcross_nonneg
        have hcoeff :
            C_weakHarnack0Forward (d := d) hd * C_weakHarnack0 d * C_crossover' d ≤
              C_weakHarnack0Forward (d := d) hd * C_weakHarnack0 d ^ 3 * C_crossover' d := by
          simpa [mul_assoc] using mul_le_mul_of_nonneg_left hcoeff_inner hfwd_nonneg
        calc
          (C_weakHarnack0Forward (d := d) hd * C_weakHarnack0 d * C_crossover' d) *
              C_chainGeom (d := d) hd
              ≤ (C_weakHarnack0Forward (d := d) hd * C_weakHarnack0 d ^ 3 * C_crossover' d) *
                  C_chainGeom (d := d) hd := by
                    exact mul_le_mul_of_nonneg_right hcoeff hgeom_nonneg
          _ = C_chainMain (d := d) hd := by
                rw [C_chainMain]
      have h1q_pos : 0 < 1 - q := by linarith
      have hfwd_const_nonneg : 0 ≤ C_weakHarnack0Forward (d := d) hd := by
        exact le_trans (by norm_num : (0 : ℝ) ≤ 1)
          (one_le_C_weakHarnack0Forward (d := d) hd)
      have hfactor_nonneg :
          0 ≤ (A.1.Λ * p₀ ^ 2 / (1 - q) ^ 2 + 1) ^ (((d : ℝ) * moserChi d) / 2) := by
        have hbase_nonneg :
            0 ≤ A.1.Λ * p₀ ^ 2 / (1 - q) ^ 2 + 1 := by
          have hterm_nonneg :
              0 ≤ A.1.Λ * p₀ ^ 2 / (1 - q) ^ 2 := by
            exact div_nonneg (mul_nonneg A.1.Λ_nonneg (sq_nonneg _)) (sq_nonneg _)
          linarith
        exact Real.rpow_nonneg hbase_nonneg _
      have hcross_nonneg : 0 ≤ C_crossover' d := by
        exact le_trans (by norm_num : (0 : ℝ) ≤ 1) one_le_C_crossover'
      have hcrossvol_nonneg :
          0 ≤ C_crossover' d * (volume.real (ball (0 : E) (1 / 2 : ℝ))) ^ 2 := by
        exact mul_nonneg hcross_nonneg (sq_nonneg _)
      have hmid_nonneg :
          0 ≤ C_weakHarnack0Forward (d := d) hd * C_weakHarnack0 d * C_crossover' d := by
        have hC0_nonneg : 0 ≤ C_weakHarnack0 d := by
          exact le_trans (by norm_num : (0 : ℝ) ≤ 1) (one_le_C_weakHarnack0 (d := d))
        exact mul_nonneg (mul_nonneg hfwd_const_nonneg hC0_nonneg) hcross_nonneg
      have hdecay_nonneg : 0 ≤ (1 - q) ^ (-((d : ℝ) * moserChi d)) := by
        positivity
      have hconst_bound :
          C_weakHarnack0Forward (d := d) hd *
              (A.1.Λ * p₀ ^ 2 / (1 - q) ^ 2 + 1) ^ (((d : ℝ) * moserChi d) / 2) *
              C_vol *
              (C_crossover' d * (volume.real (ball (0 : E) (1 / 2 : ℝ))) ^ 2 *
                (C_vol * C_weakHarnack0 d *
                  (c_crossover' d ^ 2 + 1) ^ ((d : ℝ) / 2))) ≤
            C_chainMain (d := d) hd / (1 - q) ^ ((d : ℝ) * moserChi d) := by
        calc
          C_weakHarnack0Forward (d := d) hd *
              (A.1.Λ * p₀ ^ 2 / (1 - q) ^ 2 + 1) ^ (((d : ℝ) * moserChi d) / 2) *
              C_vol *
              (C_crossover' d * (volume.real (ball (0 : E) (1 / 2 : ℝ))) ^ 2 *
                (C_vol * C_weakHarnack0 d *
                  (c_crossover' d ^ 2 + 1) ^ ((d : ℝ) / 2)))
              ≤ C_weakHarnack0Forward (d := d) hd *
                  ((c_crossover' d ^ 2 + 1) ^ (((d : ℝ) * moserChi d) / 2) *
                    (1 - q) ^ (-((d : ℝ) * moserChi d))) *
                  C_vol *
                  (C_crossover' d * (volume.real (ball (0 : E) (1 / 2 : ℝ))) ^ 2 *
                    (C_vol * C_weakHarnack0 d *
                      (c_crossover' d ^ 2 + 1) ^ ((d : ℝ) / 2))) := by
                    have hright_nonneg :
                        0 ≤ C_weakHarnack0Forward (d := d) hd *
                          C_vol *
                          (C_crossover' d * (volume.real (ball (0 : E) (1 / 2 : ℝ))) ^ 2 *
                            (C_vol * C_weakHarnack0 d *
                              (c_crossover' d ^ 2 + 1) ^ ((d : ℝ) / 2))) := by
                      have hC0_nonneg : 0 ≤ C_weakHarnack0 d := by
                        exact le_trans (by norm_num : (0 : ℝ) ≤ 1) (one_le_C_weakHarnack0 (d := d))
                      have hpow_half_nonneg :
                          0 ≤ (c_crossover' d ^ 2 + 1) ^ ((d : ℝ) / 2) := by
                        positivity
                      exact mul_nonneg
                        (mul_nonneg hfwd_const_nonneg hC_vol_nonneg)
                        (mul_nonneg hcrossvol_nonneg
                          (mul_nonneg (mul_nonneg hC_vol_nonneg hC0_nonneg) hpow_half_nonneg))
                    simpa [mul_assoc, mul_left_comm, mul_comm] using
                      (mul_le_mul_of_nonneg_left
                        (weak_harnack_forward_factor_bound hd A hq hq1) hright_nonneg)
          _ = (C_weakHarnack0Forward (d := d) hd * C_weakHarnack0 d * C_crossover' d) *
                (C_vol ^ 2 * (volume.real (ball (0 : E) (1 / 2 : ℝ))) ^ 2 *
                  (c_crossover' d ^ 2 + 1) ^
                    ((((d : ℝ) * moserChi d) / 2) + ((d : ℝ) / 2))) *
                (1 - q) ^ (-((d : ℝ) * moserChi d)) := by
                  calc
                    C_weakHarnack0Forward (d := d) hd *
                        ((c_crossover' d ^ 2 + 1) ^ (((d : ℝ) * moserChi d) / 2) *
                          (1 - q) ^ (-((d : ℝ) * moserChi d))) *
                        C_vol *
                        (C_crossover' d * (volume.real (ball (0 : E) (1 / 2 : ℝ))) ^ 2 *
                          (C_vol * C_weakHarnack0 d * (c_crossover' d ^ 2 + 1) ^ ((d : ℝ) / 2)))
                        =
                      C_weakHarnack0Forward (d := d) hd * C_weakHarnack0 d * C_crossover' d *
                        (C_vol ^ 2 * (volume.real (ball (0 : E) (1 / 2 : ℝ))) ^ 2 *
                          ((c_crossover' d ^ 2 + 1) ^ (((d : ℝ) * moserChi d) / 2) *
                            (c_crossover' d ^ 2 + 1) ^ ((d : ℝ) / 2))) *
                        (1 - q) ^ (-((d : ℝ) * moserChi d)) := by
                          ring
                    _ = (C_weakHarnack0Forward (d := d) hd * C_weakHarnack0 d * C_crossover' d) *
                          (C_vol ^ 2 * (volume.real (ball (0 : E) (1 / 2 : ℝ))) ^ 2 *
                            (c_crossover' d ^ 2 + 1) ^
                              ((((d : ℝ) * moserChi d) / 2) + ((d : ℝ) / 2))) *
                          (1 - q) ^ (-((d : ℝ) * moserChi d)) := by
                            rw [← Real.rpow_add (by positivity)]
          _ ≤ ((C_weakHarnack0Forward (d := d) hd * C_weakHarnack0 d * C_crossover' d) *
                C_chainGeom (d := d) hd) *
                (1 - q) ^ (-((d : ℝ) * moserChi d)) := by
                  have hmid_geom :
                      (C_weakHarnack0Forward (d := d) hd * C_weakHarnack0 d * C_crossover' d) *
                          (C_vol ^ 2 * (volume.real (ball (0 : E) (1 / 2 : ℝ))) ^ 2 *
                            (c_crossover' d ^ 2 + 1) ^
                              ((((d : ℝ) * moserChi d) / 2) + ((d : ℝ) / 2))) ≤
                        (C_weakHarnack0Forward (d := d) hd * C_weakHarnack0 d * C_crossover' d) *
                          C_chainGeom (d := d) hd := by
                    exact mul_le_mul_of_nonneg_left hgeom_bound hmid_nonneg
                  exact mul_le_mul_of_nonneg_right hmid_geom hdecay_nonneg
          _ ≤ C_chainMain (d := d) hd * (1 - q) ^ (-((d : ℝ) * moserChi d)) := by
                exact mul_le_mul_of_nonneg_right hsmall_to_chain hdecay_nonneg
          _ = C_chainMain (d := d) hd / (1 - q) ^ ((d : ℝ) * moserChi d) := by
                rw [div_eq_mul_inv, ← Real.rpow_neg h1q_pos.le]
      calc
        I_fwd ^ (p₀ * (((d : ℝ) - 2) / (q * (d : ℝ))))
            ≤ C_weakHarnack0Forward (d := d) hd *
                (A.1.Λ * p₀ ^ 2 / (1 - q) ^ 2 + 1) ^ (((d : ℝ) * moserChi d) / 2) *
                C_vol * I_pos := hforward_bound
        _ ≤ C_weakHarnack0Forward (d := d) hd *
              (A.1.Λ * p₀ ^ 2 / (1 - q) ^ 2 + 1) ^ (((d : ℝ) * moserChi d) / 2) *
              C_vol * I_pos_shift := by
                have hfront_nonneg :
                    0 ≤ C_weakHarnack0Forward (d := d) hd *
                      (A.1.Λ * p₀ ^ 2 / (1 - q) ^ 2 + 1) ^ (((d : ℝ) * moserChi d) / 2) *
                      C_vol := by
                  exact mul_nonneg (mul_nonneg hfwd_const_nonneg hfactor_nonneg) hC_vol_nonneg
                exact mul_le_mul_of_nonneg_left hI_pos_mono hfront_nonneg
        _ ≤ C_weakHarnack0Forward (d := d) hd *
              (A.1.Λ * p₀ ^ 2 / (1 - q) ^ 2 + 1) ^ (((d : ℝ) * moserChi d) / 2) *
              C_vol *
              (C_crossover' d * (volume.real (ball (0 : E) (1 / 2 : ℝ))) ^ 2 * J_shift⁻¹) := by
                have hfront_nonneg :
                    0 ≤ C_weakHarnack0Forward (d := d) hd *
                      (A.1.Λ * p₀ ^ 2 / (1 - q) ^ 2 + 1) ^ (((d : ℝ) * moserChi d) / 2) *
                      C_vol := by
                  exact mul_nonneg (mul_nonneg hfwd_const_nonneg hfactor_nonneg) hC_vol_nonneg
                exact mul_le_mul_of_nonneg_left hI_pos_shift hfront_nonneg
        _ ≤ C_weakHarnack0Forward (d := d) hd *
              (A.1.Λ * p₀ ^ 2 / (1 - q) ^ 2 + 1) ^ (((d : ℝ) * moserChi d) / 2) *
              C_vol *
              (C_crossover' d * (volume.real (ball (0 : E) (1 / 2 : ℝ))) ^ 2 *
                (C_vol * C_weakHarnack0 d *
                  (c_crossover' d ^ 2 + 1) ^ ((d : ℝ) / 2) *
                  (inf_u + δ) ^ p₀)) := by
                have hfront_nonneg :
                    0 ≤ C_weakHarnack0Forward (d := d) hd *
                      (A.1.Λ * p₀ ^ 2 / (1 - q) ^ 2 + 1) ^ (((d : ℝ) * moserChi d) / 2) *
                      C_vol := by
                  exact mul_nonneg (mul_nonneg hfwd_const_nonneg hfactor_nonneg) hC_vol_nonneg
                have hinner :
                    C_crossover' d * (volume.real (ball (0 : E) (1 / 2 : ℝ))) ^ 2 * J_shift⁻¹ ≤
                      C_crossover' d * (volume.real (ball (0 : E) (1 / 2 : ℝ))) ^ 2 *
                        (C_vol * C_weakHarnack0 d *
                          (c_crossover' d ^ 2 + 1) ^ ((d : ℝ) / 2) *
                          (inf_u + δ) ^ p₀) := by
                  exact mul_le_mul_of_nonneg_left hJinv hcrossvol_nonneg
                exact mul_le_mul_of_nonneg_left hinner hfront_nonneg
        _ = (C_weakHarnack0Forward (d := d) hd *
              (A.1.Λ * p₀ ^ 2 / (1 - q) ^ 2 + 1) ^ (((d : ℝ) * moserChi d) / 2) *
              C_vol *
              (C_crossover' d * (volume.real (ball (0 : E) (1 / 2 : ℝ))) ^ 2 *
                (C_vol * C_weakHarnack0 d *
                  (c_crossover' d ^ 2 + 1) ^ ((d : ℝ) / 2)))) *
                (inf_u + δ) ^ p₀ := by
                  ring
        _ ≤ (C_chainMain (d := d) hd / (1 - q) ^ ((d : ℝ) * moserChi d)) *
              (inf_u + δ) ^ p₀ := by
                have hshift_nonneg : 0 ≤ (inf_u + δ) ^ p₀ := by
                  have hinf_shift_nonneg : 0 ≤ inf_u + δ := by
                    linarith [hinf_nonneg, hδ]
                  exact Real.rpow_nonneg hinf_shift_nonneg p₀
                exact mul_le_mul_of_nonneg_right hconst_bound hshift_nonneg
  simpa [I_fwd, inf_u, q_star] using hbound_shift

/-- Main `p₀ < q` branch of the three-stage weak-Harnack chain. -/
private theorem weak_harnack_chain_main
    (hd : 2 < (d : ℝ))
    (A : NormalizedEllipticCoeff d (ball (0 : E) 1))
    {u : E → ℝ} {q : ℝ}
    (hq : 0 < q) (hq1 : q < 1)
    (hu_pos : ∀ x ∈ ball (0 : E) 1, 0 < u x)
    (hsuper : IsSupersolution A.1 u)
    (hpq : weakHarnackP0 A < q) :
    let p₀ := weakHarnackP0 A
    (∫ x in ball (0 : E) (1 / 4 : ℝ),
        |u x| ^ (q * (d : ℝ) / ((d : ℝ) - 2)) ∂volume) ^
          (p₀ * (((d : ℝ) - 2) / (q * (d : ℝ)))) ≤
      C_chainMain (d := d) hd / (1 - q) ^ ((d : ℝ) * moserChi d) *
        (essInf u (volume.restrict (ball (0 : E) (1 / 4 : ℝ)))) ^ p₀ := by
  intro p₀
  have hp₀ := p₀_pos A
  set I_fwd := ∫ x in ball (0 : E) (1 / 4 : ℝ), |u x| ^ (q * (d : ℝ) / ((d : ℝ) - 2)) ∂volume
  set inf_u := essInf u (volume.restrict (ball (0 : E) (1 / 4 : ℝ)))
  have hδ_tendsto :
      Filter.Tendsto (fun n : ℕ => (1 : ℝ) / (n + 1)) Filter.atTop (nhds 0) := by
    simpa using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  have hrhs_tendsto :
      Filter.Tendsto
        (fun n : ℕ =>
          (C_chainMain (d := d) hd / (1 - q) ^ ((d : ℝ) * moserChi d)) *
            (inf_u + (1 : ℝ) / (n + 1)) ^ p₀)
        Filter.atTop
        (nhds
          ((C_chainMain (d := d) hd / (1 - q) ^ ((d : ℝ) * moserChi d)) *
            inf_u ^ p₀)) := by
    have hshift_tendsto :
        Filter.Tendsto (fun n : ℕ => inf_u + (1 : ℝ) / (n + 1)) Filter.atTop (nhds inf_u) := by
      simpa [add_comm] using hδ_tendsto.const_add inf_u
    have hpow_tendsto :
        Filter.Tendsto (fun n : ℕ => (inf_u + (1 : ℝ) / (n + 1)) ^ p₀)
          Filter.atTop (nhds (inf_u ^ p₀)) := by
      exact (Real.continuous_rpow_const hp₀.le).continuousAt.tendsto.comp hshift_tendsto
    exact tendsto_const_nhds.mul hpow_tendsto
  have hbound_n :
      ∀ n : ℕ,
        I_fwd ^ (p₀ * (((d : ℝ) - 2) / (q * (d : ℝ)))) ≤
          (C_chainMain (d := d) hd / (1 - q) ^ ((d : ℝ) * moserChi d)) *
            (inf_u + (1 : ℝ) / (n + 1)) ^ p₀ := by
    intro n
    simpa [I_fwd, inf_u, p₀] using
      (weak_harnack_chain_shifted
        (d := d) hd A (u := u) (q := q) hq hq1 hu_pos hsuper hpq
        (δ := (1 : ℝ) / (n + 1)) (by positivity : 0 < (1 : ℝ) / (n + 1)))
  have hlimit :
      I_fwd ^ (p₀ * (((d : ℝ) - 2) / (q * (d : ℝ)))) ≤
        (C_chainMain (d := d) hd / (1 - q) ^ ((d : ℝ) * moserChi d)) *
          inf_u ^ p₀ := by
    exact le_of_tendsto_of_tendsto' tendsto_const_nhds hrhs_tendsto hbound_n
  simpa [I_fwd, inf_u] using hlimit

/-- **Three-stage chain** at the `p₀`-power level, on `B_{1/4}`.

Uses the un-powered constant `C_chain` (not `C_weakHarnack`). The `1/c'`
power is introduced when raising to `1/p₀` in `weak_harnack`. -/
theorem weak_harnack_chain
    (hd : 2 < (d : ℝ))
    (A : NormalizedEllipticCoeff d (ball (0 : E) 1))
    {u : E → ℝ} {q : ℝ}
    (hq : 0 < q) (hq1 : q < 1)
    (hu_pos : ∀ x ∈ ball (0 : E) 1, 0 < u x)
    (hsuper : IsSupersolution A.1 u) :
    let p₀ := weakHarnackP0 A
    (∫ x in ball (0 : E) (1 / 4 : ℝ),
        |u x| ^ (q * (d : ℝ) / ((d : ℝ) - 2)) ∂volume) ^
          (p₀ * (((d : ℝ) - 2) / (q * (d : ℝ)))) ≤
      C_chain (d := d) hd / (1 - q) ^ ((d : ℝ) * moserChi d) *
        (essInf u (volume.restrict (ball (0 : E) (1 / 4 : ℝ)))) ^ p₀ := by
  intro p₀
  have hp₀_def : p₀ = weakHarnackP0 A := by rfl
  have hμquarter_ne_zero :
      volume.restrict (ball (0 : E) (1 / 4 : ℝ)) ≠ 0 := by
    intro hzero
    have hball_zero : volume (ball (0 : E) (1 / 4 : ℝ)) = 0 := by
      simpa [Measure.restrict_apply_univ] using
        congrArg (fun μ : Measure E => μ Set.univ) hzero
    exact (Metric.measure_ball_pos volume (0 : E) (by norm_num : (0 : ℝ) < 1 / 4)).ne'
      hball_zero
  have hquarter_nonneg :
      ∀ᵐ x ∂(volume.restrict (ball (0 : E) (1 / 4 : ℝ))), 0 ≤ u x := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    exact (hu_pos x ((Metric.ball_subset_ball (by norm_num : (1 / 4 : ℝ) ≤ 1)) hx)).le
  have hinf_nonneg :
      0 ≤ essInf u (volume.restrict (ball (0 : E) (1 / 4 : ℝ))) := by
    exact le_essInf_real_of_ae_le (d := d) hμquarter_ne_zero hquarter_nonneg
  by_cases hpq : p₀ < q
  · have hmain := weak_harnack_chain_main
        (d := d) hd A (u := u) (q := q) hq hq1 hu_pos hsuper hpq
    have hC_le :
        C_chainMain (d := d) hd / (1 - q) ^ ((d : ℝ) * moserChi d) ≤
          C_chain (d := d) hd / (1 - q) ^ ((d : ℝ) * moserChi d) := by
      let β : ℝ := (d : ℝ) * moserChi d
      have hden_pos : 0 < (1 - q) ^ β := by
        have h1q_pos : 0 < 1 - q := by linarith [hq1]
        exact Real.rpow_pos_of_pos h1q_pos β
      exact (div_le_div_iff_of_pos_right hden_pos).2 <| by
        simpa [β] using (C_chainMain_le_C_chain (d := d) hd)
    have hpow_nonneg :
        0 ≤ essInf u (volume.restrict (ball (0 : E) (1 / 4 : ℝ))) ^ p₀ := by
      exact Real.rpow_nonneg hinf_nonneg p₀
    have hfinal :
        C_chainMain (d := d) hd / (1 - q) ^ ((d : ℝ) * moserChi d) *
          (essInf u (volume.restrict (ball (0 : E) (1 / 4 : ℝ)))) ^ p₀ ≤
        C_chain (d := d) hd / (1 - q) ^ ((d : ℝ) * moserChi d) *
          (essInf u (volume.restrict (ball (0 : E) (1 / 4 : ℝ)))) ^ p₀ := by
      exact mul_le_mul_of_nonneg_right hC_le hpow_nonneg
    exact le_trans hmain hfinal
  · push_neg at hpq
    let q' : ℝ := (p₀ + 1) / 2
    let q_star : ℝ := q * (d : ℝ) / ((d : ℝ) - 2)
    let q'_star : ℝ := q' * (d : ℝ) / ((d : ℝ) - 2)
    have hp₀_pos : 0 < p₀ := by
      simpa using p₀_pos A
    have hp₀_lt : p₀ < 1 := by
      simpa using p₀_lt_one A
    have hq'_pos : 0 < q' := by
      dsimp [q']
      linarith
    have hq'_lt_one : q' < 1 := by
      dsimp [q']
      linarith
    have hp₀_lt_q' : p₀ < q' := by
      dsimp [q']
      linarith
    have hq_le_q' : q ≤ q' := by
      exact le_trans hpq (le_of_lt hp₀_lt_q')
    have hq_star_pos : 0 < q_star := by
      dsimp [q_star]
      have hdm2 : 0 < (d : ℝ) - 2 := by linarith
      exact div_pos (mul_pos hq (by positivity)) hdm2
    have hq'_star_pos : 0 < q'_star := by
      dsimp [q'_star]
      have hdm2 : 0 < (d : ℝ) - 2 := by linarith
      exact div_pos (mul_pos hq'_pos (by positivity)) hdm2
    have hqstar_le : q_star ≤ q'_star := by
      have hdm2_pos : 0 < (d : ℝ) - 2 := by linarith
      have hnum : q * (d : ℝ) ≤ q' * (d : ℝ) := by
        nlinarith [hq_le_q']
      simpa [q_star, q'_star] using
        (div_le_div_iff_of_pos_right hdm2_pos).2 hnum
    have hmain_q' := weak_harnack_chain_main
      (d := d) hd A (u := u) (q := q') hq'_pos hq'_lt_one hu_pos hsuper hp₀_lt_q'
    have hq'_le_two : q' ≤ 2 := by
      dsimp [q']
      linarith
    let huW : MemW1pWitness 2 u (ball (0 : E) 1) := hsuper.1.someWitness
    have hq'_int_ball1 :
        IntegrableOn (fun x => |u x| ^ q') (ball (0 : E) 1) volume := by
      haveI : IsFiniteMeasure (volume.restrict (ball (0 : E) 1)) := by
        rw [isFiniteMeasure_restrict]
        exact measure_ball_lt_top.ne
      have hmem_q' : MemLp u (ENNReal.ofReal q') (volume.restrict (ball (0 : E) 1)) := by
        exact huW.memLp.mono_exponent <| by
          simpa using (ENNReal.ofReal_le_ofReal hq'_le_two)
      have hint_q' :
          Integrable (fun x => ‖u x‖ ^ q') (volume.restrict (ball (0 : E) 1)) := by
        have hint' :=
          hmem_q'.integrable_norm_rpow (ENNReal.ofReal_pos.mpr hq'_pos).ne' ENNReal.ofReal_ne_top
        simpa [ENNReal.toReal_ofReal hq'_pos.le] using hint'
      simpa [IntegrableOn, Real.norm_eq_abs] using hint_q'
    have hq'_int_half :
        IntegrableOn (fun x => |u x| ^ q') (ball (0 : E) (1 / 2 : ℝ)) volume := by
      exact hq'_int_ball1.mono_set (Metric.ball_subset_ball (by norm_num : (1 / 2 : ℝ) ≤ 1))
    have hstep2 := supersolution_reverseHolder_forward
      (d := d) hd A (u := u) (p := q') (r := (1 / 4 : ℝ)) (s := (1 / 2 : ℝ))
      hq'_pos hq'_lt_one (by norm_num) (by norm_num) (by norm_num)
      hu_pos hsuper hq'_int_half
    have hq'_star_int :
        IntegrableOn (fun x => |u x| ^ q'_star) (ball (0 : E) (1 / 4 : ℝ)) volume := by
      have hq'_star_eq : moserChi d * q' = q'_star := by
        dsimp [q'_star, moserChi]
        rw [div_eq_mul_inv, div_eq_mul_inv]
        ring
      simpa [hq'_star_eq] using hstep2.1
    have hμquarter_le :
        volume.restrict (ball (0 : E) (1 / 4 : ℝ)) ≤
          volume.restrict (ball (0 : E) 1) := by
      have hsubset : ball (0 : E) (1 / 4 : ℝ) ⊆ ball (0 : E) 1 :=
        Metric.ball_subset_ball (by norm_num : (1 / 4 : ℝ) ≤ 1)
      exact Measure.restrict_mono_set volume hsubset
    have hu_aesm_quarter :
        AEStronglyMeasurable u (volume.restrict (ball (0 : E) (1 / 4 : ℝ))) := by
      let huW : MemW1pWitness 2 u (ball (0 : E) 1) := hsuper.1.someWitness
      exact huW.memLp.aestronglyMeasurable.mono_measure hμquarter_le
    have hnorm_mono :
        (∫ x in ball (0 : E) (1 / 4 : ℝ), |u x| ^ q_star ∂volume) ^ (1 / q_star) ≤
          (∫ x in ball (0 : E) (1 / 4 : ℝ), |u x| ^ q'_star ∂volume) ^ (1 / q'_star) := by
      exact quarterBall_lpNorm_mono
        (u := u) (r := q_star) (s := q'_star) hq_star_pos hqstar_le
        hu_aesm_quarter hq'_star_int
    have hIq_nonneg :
        0 ≤ ∫ x in ball (0 : E) (1 / 4 : ℝ), |u x| ^ q_star ∂volume := by
      exact integral_nonneg fun x => by positivity
    have hIq'_nonneg :
        0 ≤ ∫ x in ball (0 : E) (1 / 4 : ℝ), |u x| ^ q'_star ∂volume := by
      exact integral_nonneg fun x => by positivity
    have hpow_mono :
        (∫ x in ball (0 : E) (1 / 4 : ℝ), |u x| ^ q_star ∂volume) ^ (p₀ / q_star) ≤
          (∫ x in ball (0 : E) (1 / 4 : ℝ), |u x| ^ q'_star ∂volume) ^ (p₀ / q'_star) := by
      have hraw :
          ((∫ x in ball (0 : E) (1 / 4 : ℝ), |u x| ^ q_star ∂volume) ^ (1 / q_star)) ^ p₀ ≤
            ((∫ x in ball (0 : E) (1 / 4 : ℝ), |u x| ^ q'_star ∂volume) ^ (1 / q'_star)) ^ p₀ := by
        exact Real.rpow_le_rpow (by positivity) hnorm_mono hp₀_pos.le
      have hleft :
          ((∫ x in ball (0 : E) (1 / 4 : ℝ), |u x| ^ q_star ∂volume) ^ (1 / q_star)) ^ p₀ =
            (∫ x in ball (0 : E) (1 / 4 : ℝ), |u x| ^ q_star ∂volume) ^ (p₀ / q_star) := by
        rw [← Real.rpow_mul hIq_nonneg]
        rw [show (1 / q_star) * p₀ = p₀ / q_star by field_simp [hq_star_pos.ne']]
      have hright :
          ((∫ x in ball (0 : E) (1 / 4 : ℝ), |u x| ^ q'_star ∂volume) ^ (1 / q'_star)) ^ p₀ =
            (∫ x in ball (0 : E) (1 / 4 : ℝ), |u x| ^ q'_star ∂volume) ^ (p₀ / q'_star) := by
        rw [← Real.rpow_mul hIq'_nonneg]
        rw [show (1 / q'_star) * p₀ = p₀ / q'_star by field_simp [hq'_star_pos.ne']]
      rwa [hleft, hright] at hraw
    have hq_pow :
        p₀ / q_star = p₀ * (((d : ℝ) - 2) / (q * (d : ℝ))) := by
      dsimp [q_star]
      field_simp [hq.ne', show (d : ℝ) - 2 ≠ 0 by linarith]
    have hq'_pow :
        p₀ / q'_star = p₀ * (((d : ℝ) - 2) / (q' * (d : ℝ))) := by
      dsimp [q'_star]
      field_simp [hq'_pos.ne', show (d : ℝ) - 2 ≠ 0 by linarith]
    have hmain_to_public :
        C_chainMain (d := d) hd / (1 - q') ^ ((d : ℝ) * moserChi d) ≤
          C_chain (d := d) hd / (1 - q) ^ ((d : ℝ) * moserChi d) := by
      let β : ℝ := (d : ℝ) * moserChi d
      have h1q_pos : 0 < 1 - q := by linarith [hq1]
      have h1q_nonneg : 0 ≤ 1 - q := h1q_pos.le
      have hp₀_le_c : p₀ ≤ c_crossover' d := by
        simpa [hp₀_def] using (p₀_le_crossover' (d := d) A)
      have h1q'_eq : 1 - q' = (1 - p₀) / 2 := by
        dsimp [q']
        ring
      have hβ_pos : 0 < β := by
        dsimp [β]
        have hchi_pos : 0 < moserChi d := moserChi_pos (d := d) hd
        positivity
      have h1q'_pos : 0 < 1 - q' := by
        linarith [hq'_lt_one]
      have hsmall_pos : 0 < (1 - c_crossover' d) / 2 := by
        have hc_lt_one : c_crossover' d < 1 := c_crossover'_lt_one (d := d)
        linarith
      have hsmall_le : (1 - c_crossover' d) / 2 ≤ 1 - q' := by
        rw [h1q'_eq]
        linarith
      have hpow_small_le :
          ((1 - c_crossover' d) / 2) ^ β ≤ (1 - q') ^ β := by
        exact Real.rpow_le_rpow hsmall_pos.le hsmall_le hβ_pos.le
      have hpow_small_pos : 0 < ((1 - c_crossover' d) / 2) ^ β := by
        exact Real.rpow_pos_of_pos hsmall_pos _
      have hto_chain :
          C_chainMain (d := d) hd / (1 - q') ^ β ≤ C_chain (d := d) hd := by
        calc
          C_chainMain (d := d) hd / (1 - q') ^ β
              ≤ C_chainMain (d := d) hd / (((1 - c_crossover' d) / 2) ^ β) := by
                  have hmain_nonneg : 0 ≤ C_chainMain (d := d) hd := by
                    exact le_trans (by norm_num : (0 : ℝ) ≤ 1) (one_le_C_chainMain (d := d) hd)
                  exact div_le_div_of_nonneg_left hmain_nonneg hpow_small_pos hpow_small_le
          _ = C_chain (d := d) hd := by
                rw [C_chain, div_eq_mul_inv]
      have hpow_q_le_one : (1 - q) ^ β ≤ 1 := by
        have h1q_le_one : 1 - q ≤ 1 := by linarith [hq]
        exact Real.rpow_le_one h1q_nonneg h1q_le_one hβ_pos.le
      have hpow_q_pos : 0 < (1 - q) ^ β := by
        exact Real.rpow_pos_of_pos h1q_pos β
      have hC_nonneg : 0 ≤ C_chain (d := d) hd := by
        exact le_trans (by norm_num : (0 : ℝ) ≤ 1) (one_le_C_chain (d := d) hd)
      have hfrom_chain :
          C_chain (d := d) hd ≤ C_chain (d := d) hd / (1 - q) ^ β := by
        have hinv_ge_one : 1 ≤ ((1 - q) ^ β)⁻¹ := by
          exact (one_le_inv₀ hpow_q_pos).2 hpow_q_le_one
        calc
          C_chain (d := d) hd = C_chain (d := d) hd * 1 := by ring
          _ ≤ C_chain (d := d) hd * ((1 - q) ^ β)⁻¹ := by
                exact mul_le_mul_of_nonneg_left hinv_ge_one hC_nonneg
          _ = C_chain (d := d) hd / (1 - q) ^ β := by
                rw [div_eq_mul_inv]
      exact le_trans hto_chain hfrom_chain
    have hpow_nonneg :
        0 ≤ essInf u (volume.restrict (ball (0 : E) (1 / 4 : ℝ))) ^ p₀ := by
      exact Real.rpow_nonneg hinf_nonneg p₀
    calc
      (∫ x in ball (0 : E) (1 / 4 : ℝ),
        |u x| ^ q_star ∂volume) ^ (p₀ * (((d : ℝ) - 2) / (q * (d : ℝ))))
        = (∫ x in ball (0 : E) (1 / 4 : ℝ),
            |u x| ^ q_star ∂volume) ^ (p₀ / q_star) := by rw [hq_pow]
      _
        ≤ (∫ x in ball (0 : E) (1 / 4 : ℝ),
            |u x| ^ q'_star ∂volume) ^ (p₀ / q'_star) := hpow_mono
      _ ≤ C_chainMain (d := d) hd / (1 - q') ^ ((d : ℝ) * moserChi d) *
            (essInf u (volume.restrict (ball (0 : E) (1 / 4 : ℝ)))) ^ p₀ := by
              have hmain_q'' :
                  (∫ x in ball (0 : E) (1 / 4 : ℝ), |u x| ^ q'_star ∂volume) ^ (p₀ / q'_star) ≤
                    C_chainMain (d := d) hd / (1 - q') ^ ((d : ℝ) * moserChi d) *
                      (essInf u (volume.restrict (ball (0 : E) (1 / 4 : ℝ)))) ^ p₀ := by
                rw [hq'_pow]
                simpa [hp₀_def, q'_star] using hmain_q'
              exact hmain_q''
      _ ≤ C_chain (d := d) hd / (1 - q) ^ ((d : ℝ) * moserChi d) *
            (essInf u (volume.restrict (ball (0 : E) (1 / 4 : ℝ)))) ^ p₀ := by
              exact mul_le_mul_of_nonneg_right hmain_to_public hpow_nonneg

/-! ### Rpow exponent helper -/

/-- If `x ^ a ≤ C * y ^ p` with `x, C, y ≥ 0` and `p > 0`, then
`x ^ (a / p) ≤ C ^ (1 / p) * y`. -/
private theorem rpow_le_rpow_of_exponent
    {x C y a p : ℝ} (hx : 0 ≤ x) (hC : 0 ≤ C) (hy : 0 ≤ y)
    (hp : 0 < p) (_ha : 0 ≤ a)
    (h : x ^ a ≤ C * y ^ p) :
    x ^ (a / p) ≤ C ^ (1 / p) * y := by
  have hp_ne : p ≠ 0 := ne_of_gt hp
  have hinvp : 0 < 1 / p := div_pos one_pos hp
  have h_raised : (x ^ a) ^ (1 / p) ≤ (C * y ^ p) ^ (1 / p) :=
    Real.rpow_le_rpow (Real.rpow_nonneg hx a) h hinvp.le
  have lhs_eq : (x ^ a) ^ (1 / p) = x ^ (a / p) := by
    rw [← Real.rpow_mul hx]; ring_nf
  have rhs_eq : (C * y ^ p) ^ (1 / p) = C ^ (1 / p) * y := by
    rw [Real.mul_rpow hC (Real.rpow_nonneg hy p), ← Real.rpow_mul hy]
    congr 1; field_simp [hp_ne]; rw [Real.rpow_one]
  linarith

/-! ### Main theorem -/

/-- **Weak Harnack inequality** for positive supersolutions on `B₁`.

For `u > 0` with `-∇·(A∇u) ≥ 0` on `B₁`, and `0 < q < 1`:
```
‖u‖_{L^{q*}(B_{1/4})} ≤ (C(d)/(1-q)^{d/c'})^{Λ^{1/2}} · essInf_{B_{1/4}} u
```

The estimate is stated on `B_{1/4}`, the ball naturally produced by the
forward and inverse Moser steps together with the crossover estimate. -/
theorem weak_harnack
    (hd : 2 < (d : ℝ))
    (A : NormalizedEllipticCoeff d (ball (0 : E) 1))
    {u : E → ℝ} {q : ℝ} (hq : 0 < q) (hq1 : q < 1)
    (hu_pos : ∀ x ∈ ball (0 : E) 1, 0 < u x)
    (hsuper : IsSupersolution A.1 u) :
    (∫ x in ball (0 : E) (1 / 4 : ℝ),
        |u x| ^ (q * (d : ℝ) / ((d : ℝ) - 2)) ∂volume) ^
          (((d : ℝ) - 2) / (q * (d : ℝ))) ≤
      (C_weakHarnack d hd / (1 - q) ^ (weak_harnack_decay_exp d)) ^
        (A.1.Λ ^ ((1 : ℝ) / 2)) *
        essInf u (volume.restrict (ball (0 : E) (1 / 4 : ℝ))) := by
  set p₀ := weakHarnackP0 A with hp₀_def
  have hp₀_pos : 0 < p₀ := p₀_pos A
  have hinv_p₀ : 1 / p₀ = A.1.Λ ^ ((1 : ℝ) / 2) / c_crossover' d := by
    rw [hp₀_def, weakHarnackP0]; field_simp
  -- The chain at the p₀ level, using C_chain (un-powered constant).
  have hchain := weak_harnack_chain hd A hq hq1 hu_pos hsuper
  -- Abbreviations.
  set I := ∫ x in ball (0 : E) (1 / 4 : ℝ),
      |u x| ^ (q * (d : ℝ) / ((d : ℝ) - 2)) ∂volume
  set α := p₀ * (((d : ℝ) - 2) / (q * (d : ℝ)))
  set inf_u := essInf u (volume.restrict (ball (0 : E) (1 / 4 : ℝ)))
  -- hchain: I^α ≤ (C_chain/(1-q)^d) · inf_u^{p₀}
  -- Raise to 1/p₀: I^{α/p₀} ≤ (C_chain/(1-q)^d)^{1/p₀} · inf_u
  have hI_nonneg : 0 ≤ I := integral_nonneg fun x => by positivity
  have hC_nonneg : 0 ≤ C_chain (d := d) hd / (1 - q) ^ ((d : ℝ) * moserChi d) := by
    exact div_nonneg (le_trans (by norm_num) (one_le_C_chain (d := d) hd))
      (Real.rpow_nonneg (by linarith) _)
  have hinf_nonneg : 0 ≤ inf_u := by
    have hμ_ne_zero :
        volume.restrict (ball (0 : E) (1 / 4 : ℝ)) ≠ 0 := by
      intro hzero
      have hball_zero : volume (ball (0 : E) (1 / 4 : ℝ)) = 0 := by
        simpa [Measure.restrict_apply_univ] using
          congrArg (fun μ : Measure E => μ Set.univ) hzero
      exact (Metric.measure_ball_pos volume (0 : E) (by norm_num : 0 < (1 / 4 : ℝ))).ne'
        hball_zero
    have hquarter_nonneg :
        ∀ᵐ x ∂(volume.restrict (ball (0 : E) (1 / 4 : ℝ))), (0 : ℝ) ≤ u x := by
      filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
      exact (hu_pos x ((Metric.ball_subset_ball (by norm_num : (1 / 4 : ℝ) ≤ 1)) hx)).le
    exact le_essInf_real_of_ae_le (d := d) hμ_ne_zero hquarter_nonneg
  have hα_nonneg : 0 ≤ α := mul_nonneg hp₀_pos.le (div_nonneg (by linarith) (by positivity))
  have hstep := rpow_le_rpow_of_exponent hI_nonneg hC_nonneg hinf_nonneg hp₀_pos hα_nonneg hchain
  -- hstep: I^{α/p₀} ≤ (C_chain/(1-q)^d)^{1/p₀} · inf_u
  -- α/p₀ = (d-2)/(qd).
  have hα_div : α / p₀ = ((d : ℝ) - 2) / (q * (d : ℝ)) := by
    simp only [α]; field_simp
  rw [hα_div] at hstep
  -- Key identity: (C_chain/(1-q)^d)^{1/p₀} = (C_chain^{1/c'}/(1-q)^{d/c'})^{Λ^{1/2}}
  -- Since C_weakHarnack = C_chain^{1/c'}, this is (C_wH/(1-q)^{d/c'})^{Λ^{1/2}}.
  -- So hstep gives exactly the stated bound.
  have hconst_eq :
      (C_chain (d := d) hd / (1 - q) ^ ((d : ℝ) * moserChi d)) ^ (1 / p₀) =
        (C_weakHarnack d hd / (1 - q) ^ (weak_harnack_decay_exp d)) ^
          (A.1.Λ ^ ((1 : ℝ) / 2)) := by
    -- 1/p₀ = Λ^{1/2}/c'. So LHS = (C_chain/(1-q)^d)^{Λ^{1/2}/c'}.
    -- Distribute: = C_chain^{Λ^{1/2}/c'} · (1-q)^{-d·Λ^{1/2}/c'}.
    -- C_chain^{Λ^{1/2}/c'} = (C_chain^{1/c'})^{Λ^{1/2}} = C_wH^{Λ^{1/2}}.
    -- (1-q)^{-d·Λ^{1/2}/c'} = ((1-q)^{d/c'})^{-Λ^{1/2}}.
    -- Combined: (C_wH · (1-q)^{-d/c'})^{Λ^{1/2}} = (C_wH/(1-q)^{d/c'})^{Λ^{1/2}}.
    rw [hinv_p₀]
    -- Goal: (C_chain d / (1 - q) ^ (d : ℝ)) ^ (A.1.Λ ^ ((1:ℝ)/2) / c_crossover' d) =
    --       (C_weakHarnack d / (1 - q) ^ weak_harnack_decay_exp d) ^ (A.1.Λ ^ ((1:ℝ)/2))
    have hc'_pos := c_crossover'_pos (d := d)
    have hc'_ne : c_crossover' (d := d) ≠ 0 := ne_of_gt hc'_pos
    have h1q_pos : 0 < 1 - q := by linarith
    have h1q_nonneg : 0 ≤ 1 - q := h1q_pos.le
    have hbase_nonneg : 0 ≤ C_chain (d := d) hd / (1 - q) ^ ((d : ℝ) * moserChi d) :=
      div_nonneg (le_trans (by norm_num) (one_le_C_chain (d := d) hd)) (by positivity)
    have hexp_rw : A.1.Λ ^ ((1:ℝ)/2) / c_crossover' d =
        (1 / c_crossover' d) * A.1.Λ ^ ((1:ℝ)/2) := by
      rw [div_eq_inv_mul]; congr 1; exact (one_div _).symm
    rw [hexp_rw]
    rw [Real.rpow_mul hbase_nonneg]
    -- Goal: ((C_chain d / (1 - q) ^ (d : ℝ)) ^ (1 / c_crossover' d)) ^ (Λ^{1/2}) =
    --       (C_weakHarnack d / (1 - q) ^ weak_harnack_decay_exp d) ^ (Λ^{1/2})
    congr 1
    -- Goal: (C_chain d / (1 - q) ^ (d : ℝ)) ^ (1 / c_crossover' d) =
    --       C_weakHarnack d / (1 - q) ^ weak_harnack_decay_exp d
    rw [Real.div_rpow (le_trans (by norm_num) (one_le_C_chain (d := d) hd))
        (Real.rpow_nonneg h1q_nonneg _)]
    -- Goal: C_chain d ^ (1/c') / ((1-q)^d)^{1/c'} = C_wH / (1-q)^{d/c'}
    rw [← C_weakHarnack_eq_C_chain_rpow (d := d) hd]
    have : ((1 - q) ^ ((d : ℝ) * moserChi d)) ^ (1 / c_crossover' d) =
        (1 - q) ^ weak_harnack_decay_exp d := by
      rw [← Real.rpow_mul h1q_nonneg]
      unfold weak_harnack_decay_exp
      congr 1
      rw [mul_one_div]
    rw [this]
  rw [hconst_eq] at hstep
  exact hstep

end DeGiorgi
