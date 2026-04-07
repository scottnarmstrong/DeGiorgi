import DeGiorgi.Common

/-!
# Chapter 02: Oscillation BMO Prelude

This module packages the BMO definitions, basic John-Nirenberg geometry, and
preliminary iteration and covering lemmas.
-/

noncomputable section

open MeasureTheory Metric Filter Set
open scoped ENNReal NNReal Topology

namespace DeGiorgi

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)

/-! ## Constants -/

/-- The John-Nirenberg constant. -/
noncomputable def C_JN (d : ℕ) : ℝ :=
  16 * 36 ^ d

theorem C_JN_pos (d : ℕ) : 0 < C_JN d := by
  unfold C_JN
  positivity

lemma five_pow_half_factor (d : ℕ) :
    (5 : ℝ) ^ d * (1 / (2 * 5 ^ d)) = (1 / 2 : ℝ) := by
  have h5d_ne : (5 : ℝ) ^ d ≠ 0 := by positivity
  field_simp [h5d_ne]

/-- The constant in the simple iteration lemma with exponent ξ = 2.
  Using δ = 1/4 gives C_iter = 4 · 144 = 576; we round up to 1024 for margin. -/
noncomputable def C_iter : ℝ := 1024

theorem C_iter_pos : 0 < C_iter := by
  unfold C_iter; positivity

/-! ## BMO -/

/-- The BMO seminorm on a set `U`. -/
noncomputable def bmoNorm (u : E → ℝ) (U : Set E) : ℝ :=
  sSup {t : ℝ | ∃ (x₀ : E) (r : ℝ), 0 < r ∧
    Metric.closedBall x₀ r ⊆ U ∧
    t = (⨍ x in Metric.ball x₀ r, ‖u x - ⨍ y in Metric.ball x₀ r, u y ∂volume‖ ∂volume)}

/-! ## John-Nirenberg Geometry -/

/-- Balls inside a fixed ambient ball, used in the Calderón-Zygmund selection behind the
John-Nirenberg argument. -/
structure JNBall (x₀ : E) (R : ℝ) where
  center : E
  radius : ℝ
  radius_pos : 0 < radius
  radius_le : radius ≤ R
  center_mem : center ∈ Metric.ball x₀ R

namespace JNBall

def carrier {x₀ : E} {R : ℝ} (b : JNBall x₀ R) : Set E :=
  Metric.ball b.center b.radius

def fivefold {x₀ : E} {R : ℝ} (b : JNBall x₀ R) : Set E :=
  Metric.ball b.center (5 * b.radius)

lemma measurableSet_carrier {x₀ : E} {R : ℝ} (b : JNBall x₀ R) :
    MeasurableSet b.carrier := measurableSet_ball

lemma measurableSet_fivefold {x₀ : E} {R : ℝ} (b : JNBall x₀ R) :
    MeasurableSet b.fivefold := measurableSet_ball

lemma carrier_nonempty {x₀ : E} {R : ℝ} (b : JNBall x₀ R) :
    b.carrier.Nonempty := nonempty_ball.2 b.radius_pos

end JNBall

lemma ball_subset_fivefold_of_inter_nonempty
    {a c d : E} {ρ r s : ℝ}
    (hsub : Metric.ball a ρ ⊆ Metric.ball c r)
    (hint : (Metric.ball c r ∩ Metric.ball d s).Nonempty)
    (hrad : r ≤ 2 * s) :
    Metric.ball a ρ ⊆ Metric.ball d (5 * s) := by
  intro y hy
  rcases hint with ⟨z, hzcr, hzds⟩
  have hycr : y ∈ Metric.ball c r := hsub hy
  have hzc : dist c z < r := by simpa [dist_comm] using hzcr
  have hyd : dist y d < 5 * s := by
    calc
      dist y d ≤ dist y c + dist c z + dist z d := by
        exact dist_triangle4 y c z d
      _ < r + r + s := by
        have hyc : dist y c < r := by simpa [Metric.mem_ball] using hycr
        have hzd : dist z d < s := by simpa [Metric.mem_ball] using hzds
        linarith
      _ ≤ 5 * s := by linarith
  exact hyd

/-- Iterating one-step level-set decay gives a geometric bound. -/
lemma john_nirenberg_iteration_decay_iterate
    {E_lam : ℝ → Set E} {A : ℝ} (hA : 0 < A) {θ : ℝ}
    (h_decay : ∀ lam : ℝ, 0 < lam → volume (E_lam (lam + A)) ≤ ENNReal.ofReal θ * volume (E_lam lam))
    (lam : ℝ) (hlam : 0 < lam) (n : ℕ) :
    volume (E_lam (lam + n * A)) ≤ ENNReal.ofReal θ ^ n * volume (E_lam lam) := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      have hlam_n_pos : 0 < lam + n * A := by positivity
      have h_step : volume (E_lam (lam + ↑(n + 1) * A)) ≤
          ENNReal.ofReal θ * volume (E_lam (lam + n * A)) := by
        have : lam + ↑(n + 1) * A = (lam + ↑n * A) + A := by
          push_cast
          ring
        rw [this]
        exact h_decay _ hlam_n_pos
      calc
        volume (E_lam (lam + ↑(n + 1) * A))
            ≤ ENNReal.ofReal θ * volume (E_lam (lam + ↑n * A)) := h_step
        _ ≤ ENNReal.ofReal θ * (ENNReal.ofReal θ ^ n * volume (E_lam lam)) := by
            gcongr
        _ = ENNReal.ofReal θ ^ (n + 1) * volume (E_lam lam) := by
            ring

/-- `ENNReal.ofReal θ ^ n = ENNReal.ofReal (θ ^ n)` for `θ ≥ 0`. -/
lemma john_nirenberg_iteration_ofReal_pow (θ : ℝ) (hθ : 0 ≤ θ) (n : ℕ) :
    ENNReal.ofReal θ ^ n = ENNReal.ofReal (θ ^ n) := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [pow_succ, ih, pow_succ, ← ENNReal.ofReal_mul (pow_nonneg hθ n)]

/-- Exponential domination for the discrete John-Nirenberg iteration. -/
lemma john_nirenberg_iteration_rpow_bound (θ lam A : ℝ) (hθ_pos : 0 < θ) (hθ_lt : θ < 1)
    (k : ℕ) (hk : (↑k : ℝ) ≥ lam / A - 1) :
    ENNReal.ofReal (θ ^ k) ≤
      ENNReal.ofReal (1 / θ) * ENNReal.ofReal (Real.exp (-lam * (-Real.log θ / A))) := by
  rw [← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  rw [show (θ ^ k : ℝ) = θ ^ (k : ℝ) from by rw [Real.rpow_natCast]]
  have h1 : θ ^ (k : ℝ) ≤ θ ^ (lam / A - 1) :=
    Real.rpow_le_rpow_of_exponent_ge hθ_pos (le_of_lt hθ_lt) hk
  have h2 : θ ^ (lam / A - 1) = 1 / θ * Real.exp (-lam * (-Real.log θ / A)) := by
    rw [Real.rpow_def_of_pos hθ_pos]
    have h_inv : (1 : ℝ) / θ = Real.exp (-Real.log θ) := by
      rw [Real.exp_neg, Real.exp_log hθ_pos, one_div]
    rw [h_inv, ← Real.exp_add]
    congr 1
    ring
  linarith

/-- Iteration of level-set decay to exponential decay. -/
theorem john_nirenberg_iteration
    {B : Set E} {E_lam : ℝ → Set E}
    (_hB : MeasurableSet B) (_hB_fin : volume B ≠ ⊤)
    (hE_sub : ∀ lam, E_lam lam ⊆ B)
    (_hE_meas : ∀ lam, MeasurableSet (E_lam lam))
    (_hE_anti : ∀ lam₁ lam₂, lam₁ ≤ lam₂ → E_lam lam₂ ⊆ E_lam lam₁)
    {A : ℝ} (hA : 0 < A)
    {θ : ℝ} (hθ_pos : 0 < θ) (hθ_lt : θ < 1)
    (h_decay : ∀ lam : ℝ, 0 < lam → volume (E_lam (lam + A)) ≤ ENNReal.ofReal θ * volume (E_lam lam)) :
    ∀ lam : ℝ, 0 < lam →
      volume (E_lam lam) ≤ ENNReal.ofReal (1 / θ) * volume B *
        ENNReal.ofReal (Real.exp (-lam * (-Real.log θ / A))) := by
  intro lam hlam
  have hlamA_pos : 0 < lam / A := div_pos hlam hA
  have hceil_ge1 : 1 ≤ ⌈lam / A⌉₊ := Nat.ceil_pos.mpr hlamA_pos
  set n := ⌈lam / A⌉₊ - 1 with hn_def
  set lam₀ := lam - ↑n * A with hlam0_def
  have hlam0_pos : 0 < lam₀ := by
    have hn_lt : (↑n : ℝ) < lam / A := by
      rw [hn_def, Nat.cast_sub hceil_ge1]
      push_cast
      linarith [Nat.ceil_lt_add_one (le_of_lt hlamA_pos)]
    have := mul_lt_mul_of_pos_right hn_lt hA
    rw [div_mul_cancel₀] at this
    · linarith
    · exact ne_of_gt hA
  have hlam_eq : lam₀ + ↑n * A = lam := by
    ring
  have h_iter := john_nirenberg_iteration_decay_iterate hA h_decay lam₀ hlam0_pos n
  rw [hlam_eq] at h_iter
  have h_sub : volume (E_lam lam₀) ≤ volume B := measure_mono (hE_sub lam₀)
  have hn_ge : (↑n : ℝ) ≥ lam / A - 1 := by
    rw [hn_def, Nat.cast_sub hceil_ge1]
    push_cast
    linarith [Nat.le_ceil (lam / A)]
  calc
    volume (E_lam lam)
        ≤ ENNReal.ofReal θ ^ n * volume (E_lam lam₀) := h_iter
    _ ≤ ENNReal.ofReal θ ^ n * volume B := by
        gcongr
    _ = ENNReal.ofReal (θ ^ n) * volume B := by
        rw [john_nirenberg_iteration_ofReal_pow θ (le_of_lt hθ_pos) n]
    _ ≤ (ENNReal.ofReal (1 / θ) * ENNReal.ofReal (Real.exp (-lam * (-Real.log θ / A)))) * volume B := by
        gcongr
        exact john_nirenberg_iteration_rpow_bound θ lam A hθ_pos hθ_lt n hn_ge
    _ = ENNReal.ofReal (1 / θ) * volume B * ENNReal.ofReal (Real.exp (-lam * (-Real.log θ / A))) := by
        ring

/-- John-Nirenberg exponential decay from a one-step decay hypothesis on pointwise level sets. -/
theorem john_nirenberg
    {u : E → ℝ} {x₀ : E} {r t A θ : ℝ}
    (_hr : 0 < r) (ht : 0 < t) (hu_meas : Measurable u)
    (hA : 0 < A) (hθ_pos : 0 < θ) (hθ_lt : θ < 1)
    (h_decay : ∀ lam : ℝ, 0 < lam →
      volume ({x ∈ Metric.ball x₀ r |
        ‖u x - ⨍ y in Metric.ball x₀ r, u y ∂volume‖ > lam + A}) ≤
        ENNReal.ofReal θ *
          volume ({x ∈ Metric.ball x₀ r |
            ‖u x - ⨍ y in Metric.ball x₀ r, u y ∂volume‖ > lam})) :
    volume ({x ∈ Metric.ball x₀ r |
      ‖u x - ⨍ y in Metric.ball x₀ r, u y ∂volume‖ > t}) ≤
    ENNReal.ofReal (1 / θ) * volume (Metric.ball x₀ r) *
      ENNReal.ofReal (Real.exp (-t * (-Real.log θ / A))) := by
  set avg := ⨍ y in Metric.ball x₀ r, u y ∂volume
  set E_lam : ℝ → Set E := fun lam => {x ∈ Metric.ball x₀ r | ‖u x - avg‖ > lam}
  have hball_meas : MeasurableSet (Metric.ball x₀ r) := measurableSet_ball
  have hE_sub : ∀ lam, E_lam lam ⊆ Metric.ball x₀ r := fun lam x hx => hx.1
  have hE_meas : ∀ lam, MeasurableSet (E_lam lam) := by
    intro lam
    exact hball_meas.inter (measurableSet_lt measurable_const ((hu_meas.sub_const avg).norm))
  have hE_anti : ∀ lam₁ lam₂, lam₁ ≤ lam₂ → E_lam lam₂ ⊆ E_lam lam₁ := by
    intro lam₁ lam₂ hle x hx
    exact ⟨hx.1, lt_of_le_of_lt hle hx.2⟩
  simpa [E_lam, avg] using
    john_nirenberg_iteration hball_meas (measure_ball_lt_top (μ := volume) (x := x₀) (r := r)).ne
      hE_sub hE_meas hE_anti hA hθ_pos hθ_lt h_decay t ht

/-- On balls staying inside `Metric.ball x₀ r`, the zero extension agrees with `u`. -/
theorem indicator_bmo_bound
    {u : E → ℝ} {x₀ : E} {r M : ℝ}
    (hu_bmo : ∀ (z : E) (s : ℝ), 0 < s → Metric.closedBall z s ⊆ Metric.ball x₀ r →
      (⨍ x in Metric.ball z s, ‖u x - ⨍ y in Metric.ball z s, u y ∂volume‖ ∂volume) ≤ M)
    (z : E) (s : ℝ) (hs : 0 < s) (hzs : Metric.closedBall z s ⊆ Metric.ball x₀ r) :
    (⨍ x in Metric.ball z s,
      ‖(Metric.ball x₀ r).indicator u x -
        ⨍ y in Metric.ball z s, (Metric.ball x₀ r).indicator u y ∂volume‖ ∂volume) ≤
      M := by
  have hball : Metric.ball z s ⊆ Metric.ball x₀ r := by
    exact Set.Subset.trans ball_subset_closedBall hzs
  have havg :
      (⨍ y in Metric.ball z s, (Metric.ball x₀ r).indicator u y ∂volume) =
        ⨍ y in Metric.ball z s, u y ∂volume := by
    apply MeasureTheory.setAverage_congr_fun isOpen_ball.measurableSet
    filter_upwards with y
    intro hy
    simp [hball hy]
  have hosc :
      (⨍ x in Metric.ball z s,
        ‖(Metric.ball x₀ r).indicator u x -
          ⨍ y in Metric.ball z s, (Metric.ball x₀ r).indicator u y ∂volume‖ ∂volume) =
        (⨍ x in Metric.ball z s, ‖u x - ⨍ y in Metric.ball z s, u y ∂volume‖ ∂volume) := by
    apply MeasureTheory.setAverage_congr_fun isOpen_ball.measurableSet
    filter_upwards with x
    intro hx
    simp [hball hx, havg]
  rw [hosc]
  exact hu_bmo z s hs hzs

/-! ## Simple Iteration Lemma (AKM, Lemma C.6) -/

/-- **Simple Iteration Lemma** (AKM, Appendix C, Lemma C.6, specialized to ξ = 2).

Suppose `ρ : ℝ → ℝ` satisfies:
1. `ρ ≥ 0` on `[1/2, 1)`,
2. `sup_{t ∈ [1/2,1)} (1-t)² ρ(t) < ∞` (finiteness of weighted supremum),
3. For all `1/2 ≤ s < t < 1`: `ρ(s) ≤ (1/2) ρ(t) + A_iter · (t - s)⁻²`

Then `ρ(1/2) ≤ C_iter · A_iter`.

**Proof sketch** (following AKM):
- Let `M = sup_{t ∈ [1/2,1)} (1-t)² ρ(t)`.
- Choose `δ = 1 - (2/3)^{1/2}` and set `t = 1 - (1-δ)(1-s)` in hypothesis (3).
- Multiply by `(1-s)²` to get: `(1-s)² ρ(s) ≤ (3/4) · (1-t)² ρ(t) + δ⁻² · A_iter`.
- Take supremum: `M ≤ (3/4) M + δ⁻² · A_iter`, hence `M ≤ 4 δ⁻² A_iter`.
- Evaluate at `s = 1/2`: `ρ(1/2) ≤ 2² · M ≤ 4 · 4 · δ⁻² · A_iter ≤ C_iter · A_iter`.
-/
theorem simple_iteration_lemma
    {ρ : ℝ → ℝ} {A_iter : ℝ}
    (hA_iter : 0 ≤ A_iter)
    (hρ_nonneg : ∀ t : ℝ, 1 / 2 ≤ t → t < 1 → 0 ≤ ρ t)
    (hρ_bdd : ∃ M : ℝ, ∀ t : ℝ, 1 / 2 ≤ t → t < 1 → (1 - t) ^ 2 * ρ t ≤ M)
    (hρ_contract : ∀ s t : ℝ, 1 / 2 ≤ s → s < t → t < 1 →
      ρ s ≤ 1 / 2 * ρ t + A_iter * (t - s) ⁻¹ ^ 2) :
    ρ (1 / 2) ≤ C_iter * A_iter := by
  /- Proof using δ = 1/4: for s ∈ [1/2,1), set t = s + (1-s)/4 = (3s+1)/4.
     Then t-s = (1-s)/4, 1-t = 3(1-s)/4, (1-s)/(1-t) = 4/3.
     Multiplying the contraction by (1-s)² gives
       (1-s)² ρ(s) ≤ (8/9)(1-t)² ρ(t) + 16 A_iter.
     Iterating: if M bounds (1-t)² ρ(t), then (8/9)M + 16 A_iter also does.
     After n iterations the bound is (8/9)^n M + 144(1-(8/9)^n) A_iter.
     As n → ∞ this tends to 144 A_iter. So (1/2)² ρ(1/2) ≤ 144 A_iter,
     hence ρ(1/2) ≤ 576 A_iter ≤ 1024 A_iter = C_iter A_iter. -/
  -- Extract M from hρ_bdd and make it nonneg
  obtain ⟨M₀, hM₀⟩ := hρ_bdd
  set M : ℝ := max M₀ 0 with hM_def
  have hM_nn : 0 ≤ M := le_max_right _ _
  have hM_bound : ∀ t : ℝ, 1 / 2 ≤ t → t < 1 → (1 - t) ^ 2 * ρ t ≤ M := by
    intro t ht1 ht2
    exact le_trans (hM₀ t ht1 ht2) (le_max_left _ _)
  -- Key one-step improvement: for any upper bound B ≥ 0 on (1-t)²ρ(t),
  -- (8/9)B + 16 A_iter is also an upper bound.
  have improvement : ∀ B : ℝ, 0 ≤ B →
      (∀ t : ℝ, 1 / 2 ≤ t → t < 1 → (1 - t) ^ 2 * ρ t ≤ B) →
      (∀ s : ℝ, 1 / 2 ≤ s → s < 1 → (1 - s) ^ 2 * ρ s ≤ 8 / 9 * B + 16 * A_iter) := by
    intro B hB_nn hB_bound s hs1 hs2
    -- Set t = (3s + 1) / 4
    set t := (3 * s + 1) / 4 with ht_def
    have ht_gt_s : s < t := by linarith
    have ht_lt_1 : t < 1 := by linarith
    have ht_ge : 1 / 2 ≤ t := by linarith
    have h1ms_pos : 0 < 1 - s := by linarith
    have h1mt_pos : 0 < 1 - t := by linarith
    have hts_pos : 0 < t - s := by linarith
    -- Compute key ratios
    have h1mt : 1 - t = 3 / 4 * (1 - s) := by rw [ht_def]; ring
    have hts : t - s = 1 / 4 * (1 - s) := by rw [ht_def]; ring
    -- Apply the contraction hypothesis
    have hcontr := hρ_contract s t hs1 ht_gt_s ht_lt_1
    -- Multiply both sides by (1-s)²
    have hρ_s_nn : 0 ≤ ρ s := hρ_nonneg s hs1 hs2
    have hρ_t_nn : 0 ≤ ρ t := hρ_nonneg t ht_ge ht_lt_1
    -- (1-s)² ρ(s) ≤ (1-s)² ((1/2) ρ(t) + A_iter (t-s)⁻²)
    have step1 : (1 - s) ^ 2 * ρ s ≤
        (1 - s) ^ 2 * (1 / 2 * ρ t + A_iter * (t - s)⁻¹ ^ 2) := by
      exact mul_le_mul_of_nonneg_left hcontr (sq_nonneg _)
    -- (1-s)² · (t-s)⁻¹² = 16
    have hprod1 : (1 - s) ^ 2 * ((t - s)⁻¹ ^ 2) = 16 := by
      rw [hts]
      have : 1 / 4 * (1 - s) ≠ 0 := by positivity
      field_simp
      ring
    -- Also (1-s)² · (1/2) ρ(t) = (1/2) ((1-s)/(1-t))² (1-t)² ρ(t)
    -- = (1/2)(4/3)²(1-t)² ρ(t) = (8/9)(1-t)² ρ(t)
    have hratio : (1 - s) ^ 2 * (1 / 2 * ρ t) = 8 / 9 * ((1 - t) ^ 2 * ρ t) := by
      rw [h1mt]; ring
    -- Combine
    calc (1 - s) ^ 2 * ρ s
        ≤ (1 - s) ^ 2 * (1 / 2 * ρ t + A_iter * (t - s)⁻¹ ^ 2) := step1
      _ = (1 - s) ^ 2 * (1 / 2 * ρ t) + A_iter * ((1 - s) ^ 2 * (t - s)⁻¹ ^ 2) := by ring
      _ = 8 / 9 * ((1 - t) ^ 2 * ρ t) + A_iter * 16 := by rw [hratio, hprod1]
      _ ≤ 8 / 9 * B + 16 * A_iter := by
          have := hB_bound t ht_ge ht_lt_1
          nlinarith
  -- Iterate the improvement n times: after n steps the bound is
  -- (8/9)^n M + 144(1 - (8/9)^n) A_iter
  -- Define the iterated bound
  let bound : ℕ → ℝ := fun n => (8 / 9) ^ n * M + (1 - (8 / 9) ^ n) * (144 * A_iter)
  have hbound_nn : ∀ n, 0 ≤ bound n := by
    intro n
    have h89 : (0 : ℝ) ≤ (8 / 9) ^ n := by positivity
    have h89_le1 : (8 / 9 : ℝ) ^ n ≤ 1 := pow_le_one₀ (by positivity) (by norm_num)
    nlinarith [mul_nonneg h89 hM_nn]
  -- Show that bound n is an upper bound for all n
  have hbound_is_bound : ∀ n, ∀ t : ℝ, 1 / 2 ≤ t → t < 1 →
      (1 - t) ^ 2 * ρ t ≤ bound n := by
    intro n
    induction n with
    | zero =>
      intro t ht1 ht2
      simp only [bound, pow_zero, one_mul, sub_self, zero_mul, add_zero]
      exact hM_bound t ht1 ht2
    | succ n ih =>
      intro s hs1 hs2
      have him := improvement (bound n) (hbound_nn n) ih s hs1 hs2
      -- Need: 8/9 * bound n + 16 * A_iter ≤ bound (n+1)
      -- bound (n+1) = (8/9)^(n+1) M + (1 - (8/9)^(n+1)) * 144 * A_iter
      -- 8/9 * bound n + 16 * A_iter
      --   = 8/9 * ((8/9)^n M + (1-(8/9)^n) * 144 A_iter) + 16 A_iter
      --   = (8/9)^(n+1) M + (8/9)(1-(8/9)^n) * 144 A_iter + 16 A_iter
      --   = (8/9)^(n+1) M + (8/9 - (8/9)^(n+1)) * 144 A_iter + 16 A_iter
      --   = (8/9)^(n+1) M + (8/9)*144 A_iter - (8/9)^(n+1)*144 A_iter + 16 A_iter
      --   = (8/9)^(n+1) M + 128 A_iter + 16 A_iter - (8/9)^(n+1) * 144 A_iter
      --   = (8/9)^(n+1) M + 144 A_iter - (8/9)^(n+1) * 144 A_iter
      --   = (8/9)^(n+1) M + (1 - (8/9)^(n+1)) * 144 A_iter = bound (n+1) ✓
      suffices 8 / 9 * bound n + 16 * A_iter = bound (n + 1) by linarith
      show 8 / 9 * ((8 / 9) ^ n * M + (1 - (8 / 9) ^ n) * (144 * A_iter)) + 16 * A_iter =
        (8 / 9) ^ (n + 1) * M + (1 - (8 / 9) ^ (n + 1)) * (144 * A_iter)
      rw [pow_succ]
      ring
  -- ρ(1/2) ≤ 4 * bound n for all n
  have hρ_le_4bound : ∀ n, ρ (1 / 2) ≤ 4 * bound n := by
    intro n
    have h12 : (1 : ℝ) / 2 ≤ 1 / 2 := le_refl _
    have h12_lt : (1 : ℝ) / 2 < 1 := by norm_num
    have := hbound_is_bound n (1 / 2) h12 h12_lt
    -- (1 - 1/2)² ρ(1/2) ≤ bound n, i.e., (1/4) ρ(1/2) ≤ bound n
    have h14 : (1 - 1 / 2 : ℝ) ^ 2 = 1 / 4 := by norm_num
    rw [h14] at this
    -- ρ(1/2) ≤ 4 * bound n
    have hρ12_nn : 0 ≤ ρ (1 / 2) := hρ_nonneg (1 / 2) h12 h12_lt
    linarith
  -- Now: bound n → 144 * A_iter as n → ∞ (since (8/9)^n → 0)
  -- We need: ρ(1/2) ≤ 576 * A_iter
  -- Use: for all ε > 0, exists n such that bound n ≤ 144 * A_iter + ε
  -- Then ρ(1/2) ≤ 4 * (144 * A_iter + ε) = 576 * A_iter + 4ε
  -- Since ε arbitrary, ρ(1/2) ≤ 576 * A_iter
  suffices h576 : ρ (1 / 2) ≤ 576 * A_iter by
    calc ρ (1 / 2) ≤ 576 * A_iter := h576
      _ ≤ C_iter * A_iter := by unfold C_iter; nlinarith [hA_iter]
  -- Prove via le_of_forall_pos_lt_add
  rw [show (576 : ℝ) * A_iter = 4 * (144 * A_iter) from by ring]
  apply le_of_forall_pos_lt_add
  intro ε hε
  -- Find n such that (8/9)^n * M < ε / 4
  have h89_lt : (8 : ℝ) / 9 < 1 := by norm_num
  have h89_nn : (0 : ℝ) ≤ 8 / 9 := by norm_num
  have hε4 : (0 : ℝ) < ε / 4 := by linarith
  have htend : Filter.Tendsto (fun n => (8 / 9 : ℝ) ^ n * M) Filter.atTop (nhds 0) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one h89_nn h89_lt).mul_const M
    rwa [zero_mul] at this
  rw [tendsto_atTop_nhds] at htend
  obtain ⟨N, hN⟩ := htend (Set.Iio (ε / 4)) (show (0 : ℝ) ∈ Set.Iio (ε / 4) from hε4)
    isOpen_Iio
  have hN' : (8 / 9) ^ N * M < ε / 4 := hN N (le_refl _)
  -- bound N ≤ (8/9)^N * M + 144 * A_iter
  have hboundN : bound N ≤ (8 / 9) ^ N * M + 144 * A_iter := by
    show (8 / 9) ^ N * M + (1 - (8 / 9) ^ N) * (144 * A_iter) ≤
      (8 / 9) ^ N * M + 144 * A_iter
    nlinarith [pow_nonneg h89_nn N, hA_iter]
  calc ρ (1 / 2)
      ≤ 4 * bound N := hρ_le_4bound N
    _ ≤ 4 * ((8 / 9) ^ N * M + 144 * A_iter) := by nlinarith
    _ < 4 * (ε / 4 + 144 * A_iter) := by nlinarith
    _ = 4 * (144 * A_iter) + ε := by ring

/-! ## Vitali Covering Lemma -/

/-- Vitali covering lemma (5r-covering): from any family of balls, one can extract a
disjoint subfamily such that the 5× enlargements cover the union, and every original
ball meets a selected ball of at least half its radius. -/
theorem vitali_covering_lemma
    {ι : Type*} {x : ι → E} {r : ι → ℝ}
    (hr_pos : ∀ i, 0 < r i)
    (hr_bdd : BddAbove (Set.range r))
    (hfin : (⋃ i, Metric.ball (x i) (r i)).Nonempty) :
    ∃ S : Set ι, S.Countable ∧
      (∀ i ∈ S, ∀ j ∈ S, i ≠ j →
        Disjoint (Metric.ball (x i) (r i)) (Metric.ball (x j) (r j))) ∧
      (∀ i, ∃ j ∈ S,
        (Metric.ball (x i) (r i) ∩ Metric.ball (x j) (r j)).Nonempty ∧ r i ≤ 2 * r j) ∧
      (⋃ i, Metric.ball (x i) (r i)) ⊆ ⋃ i ∈ S, Metric.ball (x i) (5 * r i) := by
  classical
  let _ := hfin
  let t : Set ι := Set.univ
  obtain ⟨R, hR⟩ := hr_bdd
  rcases
      Vitali.exists_disjoint_subfamily_covering_enlargement
        (fun i => Metric.ball (x i) (r i)) t r 2 (by norm_num)
        (fun i _ => (hr_pos i).le) R (by
          intro i hi
          exact hR (Set.mem_range_self i)) (fun i _ =>
            nonempty_ball.2 (hr_pos i))
    with ⟨S, _, hS_disj, hS_hit⟩
  have hS_ball_disj : S.PairwiseDisjoint (fun i => Metric.ball (x i) (r i)) := by
    exact hS_disj
  have hS_count : S.Countable := by
    exact hS_ball_disj.countable_of_isOpen
      (fun i _ => isOpen_ball)
      (fun i _ => nonempty_ball.2 (hr_pos i))
  refine ⟨S, hS_count, ?_, ?_, ?_⟩
  · intro i hi j hj hij
    exact hS_ball_disj hi hj hij
  · intro i
    rcases hS_hit i (by simp [t]) with ⟨j, hjS, hij, hrad⟩
    exact ⟨j, hjS, hij, hrad⟩
  · intro y hy
    rcases Set.mem_iUnion.1 hy with ⟨i, hyi⟩
    rcases hS_hit i (by simp [t]) with ⟨j, hjS, hij, hrad⟩
    refine Set.mem_iUnion.2 ⟨j, Set.mem_iUnion.2 ⟨hjS, ?_⟩⟩
    rcases hij with ⟨z, hzi, hzj⟩
    have hyj : dist y (x j) < 5 * r j := by
      calc
        dist y (x j) ≤ dist y (x i) + dist (x i) z + dist z (x j) :=
          dist_triangle4 y (x i) z (x j)
        _ < r i + r i + r j := by
          have h1 : dist y (x i) < r i := by simpa [Metric.mem_ball] using hyi
          have h2 : dist (x i) z < r i := by rw [dist_comm]; simpa [Metric.mem_ball] using hzi
          have h3 : dist z (x j) < r j := by simpa [Metric.mem_ball] using hzj
          linarith
        _ ≤ 5 * r j := by linarith
    exact hyj


lemma volumeReal_ball_eq (x : E) {r : ℝ} (hr : 0 < r) :
    volume.real (Metric.ball x r) = r ^ d * volume.real (Metric.ball (0 : E) 1) := by
  by_cases hd : d = 0
  · subst hd
    have hballx : Metric.ball x r = Set.univ := by
      ext y
      have hyx : y = x := Subsingleton.elim _ _
      simp [Metric.mem_ball, hyx, hr]
    have hball0 : Metric.ball (0 : EuclideanSpace ℝ (Fin 0)) 1 = Set.univ := by
      ext y
      have hy0 : y = (0 : EuclideanSpace ℝ (Fin 0)) := Subsingleton.elim _ _
      simp [Metric.mem_ball, hy0]
    rw [hballx, hball0]
    simp
  · have hdpos : 0 < d := Nat.pos_of_ne_zero hd
    haveI : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) (M := E) <| by
      simpa [finrank_euclideanSpace] using hdpos
    rw [← Measure.addHaar_real_closedBall_eq_addHaar_real_ball (μ := volume) x r,
      Measure.addHaar_real_closedBall (μ := volume) x hr.le]
    simp [finrank_euclideanSpace]

lemma volumeReal_ball_halves (x : E) {r : ℝ} (hr : 0 < r) :
    volume.real (Metric.ball x r) = (2 : ℝ) ^ d * volume.real (Metric.ball x (r / 2)) := by
  rw [volumeReal_ball_eq x hr, volumeReal_ball_eq x (by positivity)]
  have hr_eq : r ^ d = ((2 : ℝ) * (r / 2)) ^ d := by
    congr 1
    ring
  rw [hr_eq, mul_pow]
  ring

lemma JNBall.volumeReal_fivefold {x₀ : E} {R : ℝ} (b : JNBall x₀ R) :
    volume.real b.fivefold = (5 : ℝ) ^ d * volume.real b.carrier := by
  rw [JNBall.carrier, JNBall.fivefold,
    volumeReal_ball_eq b.center (mul_pos (by norm_num : (0:ℝ) < 5) b.radius_pos),
    volumeReal_ball_eq b.center b.radius_pos]
  rw [mul_pow]
  ring

lemma JNBall.volume_fivefold {x₀ : E} {R : ℝ} (b : JNBall x₀ R) :
    volume b.fivefold = ENNReal.ofReal ((5 : ℝ) ^ d) * volume b.carrier := by
  have hleft : volume b.fivefold ≠ ⊤ := measure_ball_lt_top.ne
  have hright : ENNReal.ofReal ((5 : ℝ) ^ d) * volume b.carrier ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top measure_ball_lt_top.ne
  rw [← ENNReal.toReal_eq_toReal_iff' hleft hright]
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity : (0:ℝ) ≤ (5:ℝ) ^ d)]
  exact b.volumeReal_fivefold

end DeGiorgi
