import DeGiorgi.Supersolutions.RegularizationSupport

/-!
# Supersolutions Forward Iteration Basics

This module contains the forward cutoff definition and the basic setup lemmas
for the forward low-power supersolution iteration.
-/

noncomputable section

open MeasureTheory Metric

namespace DeGiorgi

variable {d : ℕ} [NeZero d]

local notation "E" => AmbientSpace d
local notation "μhalf" => (volume.restrict (Metric.ball (0 : E) (1 / 2 : ℝ)))

/-- Forward low-power energy bound for `η · u^{p/2}` where `p ∈ (0,1)`.

This is the analogue of `superPowerCutoff_energy_bound` for positive powers
of `u` (not `u⁻¹`). The Caccioppoli inequality gives `(1-p)` in the denominator
instead of `(1+p)`.

The proof is the same test-function computation as the inverse case but with
`p ↦ -p` substitution. When `p ∈ (-1,0)` in the general formula, we get
`u^{-(-p)/2} = u^{p/2}` and `1 + (-p) = 1 - p`. -/
noncomputable def superPowerCutoffFwd
    (η u : E → ℝ) (p : ℝ) : E → ℝ :=
  fun x => η x * |u x| ^ (p / 2)

omit [NeZero d] in
theorem superPowerCutoff_neg_eq_fwd
    {u η : E → ℝ} {p : ℝ}
    (hu_pos : ∀ x, 0 < u x) :
    superPowerCutoff (d := d) η u (-p) = superPowerCutoffFwd (d := d) η u p := by
  funext x
  have hux_pos : 0 < u x := hu_pos x
  have hux_inv_pos : 0 < (u x)⁻¹ := inv_pos.mpr hux_pos
  have hpow :
      |(u x)⁻¹| ^ (-p / 2 : ℝ) = |u x| ^ (p / 2) := by
    rw [abs_of_pos hux_inv_pos, abs_of_pos hux_pos]
    rw [show (-p / 2 : ℝ) = -(p / 2) by ring, Real.rpow_neg hux_inv_pos.le]
    rw [Real.inv_rpow hux_pos.le]
    simp
  calc
    superPowerCutoff (d := d) η u (-p) x
        = η x * |(u x)⁻¹| ^ (-p / 2 : ℝ) := by
            simp [superPowerCutoff]
    _ = η x * |u x| ^ (p / 2) := by rw [hpow]
    _ = superPowerCutoffFwd (d := d) η u p x := by
          simp [superPowerCutoffFwd]

theorem exists_forward_iteration_depth
    (hd : 2 < (d : ℝ))
    {p q : ℝ} (hp : 0 < p) (hpq : p < q) :
    ∃ m : ℕ,
      let p₀ := q * (moserChi d)⁻¹ ^ m
      p₀ < p ∧ p ≤ moserChi d * p₀ := by
  let ρ : ℝ := (moserChi d)⁻¹
  have hρ_pos : 0 < ρ := inv_pos.mpr (moserChi_pos (d := d) hd)
  have hρ_lt_one : ρ < 1 := by
    simpa [ρ] using
      (one_div_lt_one_div_of_lt (a := (1 : ℝ)) (b := moserChi d)
        zero_lt_one (one_lt_moserChi (d := d) hd))
  have hpq_ratio_pos : 0 < p / q := div_pos hp (lt_trans hp hpq)
  have hpq_ratio_le : p / q ≤ 1 := by
    have hq_pos : 0 < q := lt_trans hp hpq
    exact (div_le_one hq_pos).2 hpq.le
  rcases exists_nat_pow_near_of_lt_one hpq_ratio_pos hpq_ratio_le hρ_pos hρ_lt_one with
    ⟨n, hn_lt, hn_le⟩
  refine ⟨n + 1, ?_⟩
  dsimp
  constructor
  · have hq_pos : 0 < q := lt_trans hp hpq
    have hmul := mul_lt_mul_of_pos_left hn_lt hq_pos
    simpa [ρ, div_eq_mul_inv, hq_pos.ne', mul_assoc, mul_left_comm, mul_comm] using hmul
  · have hq_pos : 0 < q := lt_trans hp hpq
    have hmul := mul_le_mul_of_nonneg_left hn_le hq_pos.le
    have hp_le_base : p ≤ q * ρ ^ n := by
      simpa [ρ, div_eq_mul_inv, hq_pos.ne', mul_assoc, mul_left_comm, mul_comm] using hmul
    have hχ_ne : moserChi d ≠ 0 := (moserChi_pos (d := d) hd).ne'
    calc
      p ≤ q * ρ ^ n := hp_le_base
      _ = moserChi d * (q * ρ ^ (n + 1)) := by
            dsimp [ρ]
            rw [pow_succ]
            field_simp [hχ_ne]

theorem supersolution_integrableOn_ball_one_rpow
    (A : NormalizedEllipticCoeff d (Metric.ball (0 : E) 1))
    {u : E → ℝ} {p : ℝ}
    (hp : 0 < p) (hp2 : p ≤ 2)
    (hsuper : IsSupersolution A.1 u) :
    IntegrableOn (fun x => |u x| ^ p) (Metric.ball (0 : E) 1) volume := by
  let μ : Measure E := volume.restrict (Metric.ball (0 : E) 1)
  haveI : IsFiniteMeasure μ := by
    dsimp [μ]
    rw [isFiniteMeasure_restrict]
    exact measure_ne_top_of_subset Metric.ball_subset_closedBall
      (isCompact_closedBall (0 : E) (1 : ℝ)).measure_lt_top.ne
  let hu : MemW1pWitness 2 u (Metric.ball (0 : E) 1) := hsuper.1.someWitness
  have hu_memLp_p :
      MemLp u (ENNReal.ofReal p) μ := by
    exact hu.memLp.mono_exponent <| by
      simpa using (ENNReal.ofReal_le_ofReal hp2)
  have hint :
      Integrable (fun x => ‖u x‖ ^ p) μ := by
    have hint' :=
      hu_memLp_p.integrable_norm_rpow (ENNReal.ofReal_pos.mpr hp).ne' ENNReal.ofReal_ne_top
    simpa [ENNReal.toReal_ofReal hp.le] using hint'
  simpa [μ, IntegrableOn, Real.norm_eq_abs] using hint

omit [NeZero d] in
theorem superPowerCutoffFwd_tsupport_subset
    {u η : E → ℝ} {p s : ℝ}
    (hη_sub_ball : tsupport η ⊆ Metric.ball (0 : E) s) :
    tsupport (superPowerCutoffFwd (d := d) η u p) ⊆ Metric.ball (0 : E) s :=
  (tsupport_mul_subset_left
    (f := η) (g := fun x => |u x| ^ (p / 2))).trans hη_sub_ball

set_option maxHeartbeats 1000000


end DeGiorgi
