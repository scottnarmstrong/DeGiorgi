import DeGiorgi.Crossover.ProductBound

/-!
# Chapter 06: Public Crossover Estimates

This module assembles the public crossover estimates from the product-bound
infrastructure.
-/

noncomputable section

open MeasureTheory Metric Filter Set
open scoped ENNReal NNReal Topology RealInnerProductSpace

namespace DeGiorgi

variable {d : ℕ} [NeZero d]

local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "Cmo" =>
  ((volume.real (Metric.ball (0 : E) 1)) ^ (-(1 / 2 : ℝ)) * C_poinc_val d)

/-! ### Crossover Estimate

Bridging positive and negative powers of a positive supersolution via
John-Nirenberg exponential integrability. -/

/-- Crossover estimate bridging positive and negative powers of a positive
supersolution. -/
theorem crossover_estimate
    (hd : 2 < (d : ℝ))
    (A : NormalizedEllipticCoeff d (Metric.ball (0 : E) 1))
    {u : E → ℝ}
    (hu_pos : ∀ x ∈ Metric.ball (0 : E) 1, 0 < u x)
    (hsuper : IsSupersolution A.1 u) :
    (⨍ x in Metric.ball (0 : E) (1 / 2 : ℝ),
        |u x| ^ (c_crossover' d / A.1.Λ ^ ((1 : ℝ) / 2)) ∂volume) *
      (⨍ x in Metric.ball (0 : E) (1 / 2 : ℝ),
        |u x| ^ (-(c_crossover' d / A.1.Λ ^ ((1 : ℝ) / 2))) ∂volume) ≤
        C_crossover' d := by
  -- Proof via local exponential integrability for `v = -log u`.
  -- Set v = -log u, c = c_crossover' d / Λ^{1/2}.
  -- Define w(x) = exp(c · (v_avg - v(x))) where v_avg = ⨍ v on B_{1/2}.
  -- Then log w = c(v_avg - v), so (log w)_{B_{1/2}} = 0.
  -- Also: w > 0 everywhere (exponential), w⁻¹(x) = exp(c(v(x) - v_avg)).
  -- The LHS equals ⨍ w · ⨍ w⁻¹ (the exp(±c·v_avg) factors cancel in the product).
  --
  --   Choose cutoff φ with φ = 1 on B_{3/4}, supp φ ⊆ B₁, |∇φ| ≤ C.
  --   ∫_{B_{3/4}} |∇v|² ≤ ∫_B φ²|∇v|² ≤ 4Λ ∫_B |∇φ|² ≤ C·Λ.
  --
  --   With c = c_crossover/Λ^{1/2}, this is ≤ c_crossover² · C.
  --   Choose c_crossover small enough → ≤ 1.
  --
  --   ∫_{B_{1/2}} |log w| ≤ C_P · ‖∇ log w‖_{L²} ≤ C_P.
  --
  --   dimension-only bounds for ⨍ w and ⨍ w⁻¹.
  --
  -- LHS = ⨍ |u|^c · ⨍ |u|^{-c}
  --      = ⨍ exp(c·log|u|) · ⨍ exp(-c·log|u|)
  --      = ⨍ exp(-c·v) · ⨍ exp(c·v)            (v = -log u)
  --      = exp(-c·v_avg) · ⨍ exp(c(v_avg-v)) · exp(c·v_avg) · ⨍ exp(c(v-v_avg))
  --        ^^^ the exp(±c·v_avg) factors cancel in the product ^^^
  --      = ⨍ w · ⨍ w⁻¹
  -- === Proof assembly ===
  set c := c_crossover' d / A.1.Λ ^ ((1 : ℝ) / 2)
  set v : E → ℝ := fun x => -Real.log (u x)
  set v_avg := ⨍ x in Metric.ball (0 : E) (1 / 2 : ℝ), v x ∂volume
  set w : E → ℝ := fun x => Real.exp (c * (v_avg - v x))
  set w_inv : E → ℝ := fun x => Real.exp (c * (v x - v_avg))
  have hw_pos : ∀ x, 0 < w x := fun x => Real.exp_pos _
  have hw_inv_pos : ∀ x, 0 < w_inv x := fun x => Real.exp_pos _
  have hw_mul : ∀ x, w x * w_inv x = 1 := by
    intro x; simp only [w, w_inv]
    rw [← Real.exp_add, show c * (v_avg - v x) + c * (v x - v_avg) = 0 by ring]
    exact Real.exp_zero
  have h_product_identity :
      (⨍ x in Metric.ball (0 : E) (1 / 2 : ℝ), |u x| ^ c ∂volume) *
        (⨍ x in Metric.ball (0 : E) (1 / 2 : ℝ), |u x| ^ (-c) ∂volume) =
      (⨍ x in Metric.ball (0 : E) (1 / 2 : ℝ), w x ∂volume) *
        (⨍ x in Metric.ball (0 : E) (1 / 2 : ℝ), w_inv x ∂volume) := by
    let B : Set E := Metric.ball (0 : E) (1 / 2 : ℝ)
    have hu_pos_half : ∀ x ∈ B, 0 < u x := by
      intro x hx
      exact hu_pos x (Metric.ball_subset_ball (by norm_num : (1 : ℝ) / 2 ≤ 1) hx)
    have hpow_eq :
        ∀ x ∈ B, |u x| ^ c = Real.exp (-c * v_avg) * w x := by
      intro x hx
      have hux : 0 < u x := hu_pos_half x hx
      have habs : |u x| = u x := abs_of_pos hux
      rw [habs, Real.rpow_def_of_pos hux]
      simp only [w, v]
      rw [← Real.exp_add]
      congr 1
      ring
    have hpow_inv_eq :
        ∀ x ∈ B, |u x| ^ (-c) = Real.exp (c * v_avg) * w_inv x := by
      intro x hx
      have hux : 0 < u x := hu_pos_half x hx
      have habs : |u x| = u x := abs_of_pos hux
      rw [habs, Real.rpow_def_of_pos hux]
      simp only [w_inv, v]
      rw [← Real.exp_add]
      congr 1
      ring
    have havg_pow :
        (⨍ x in B, |u x| ^ c ∂volume) =
          Real.exp (-c * v_avg) * (⨍ x in B, w x ∂volume) := by
      calc
        (⨍ x in B, |u x| ^ c ∂volume)
            = (volume.real B)⁻¹ * ∫ x in B, |u x| ^ c ∂volume := by
                rw [MeasureTheory.setAverage_eq, smul_eq_mul]
        _ = (volume.real B)⁻¹ * (Real.exp (-c * v_avg) * ∫ x in B, w x ∂volume) := by
              congr 1
              calc
                ∫ x in B, |u x| ^ c ∂volume
                    = ∫ x in B, Real.exp (-c * v_avg) * w x ∂volume := by
                        apply MeasureTheory.setIntegral_congr_fun measurableSet_ball
                        intro x hx
                        exact hpow_eq x hx
                _ = Real.exp (-c * v_avg) * ∫ x in B, w x ∂volume := by
                      rw [integral_const_mul]
        _ = Real.exp (-c * v_avg) * (⨍ x in B, w x ∂volume) := by
              rw [MeasureTheory.setAverage_eq, smul_eq_mul]
              ring
    have havg_pow_inv :
        (⨍ x in B, |u x| ^ (-c) ∂volume) =
          Real.exp (c * v_avg) * (⨍ x in B, w_inv x ∂volume) := by
      calc
        (⨍ x in B, |u x| ^ (-c) ∂volume)
            = (volume.real B)⁻¹ * ∫ x in B, |u x| ^ (-c) ∂volume := by
                rw [MeasureTheory.setAverage_eq, smul_eq_mul]
        _ = (volume.real B)⁻¹ * (Real.exp (c * v_avg) * ∫ x in B, w_inv x ∂volume) := by
              congr 1
              calc
                ∫ x in B, |u x| ^ (-c) ∂volume
                    = ∫ x in B, Real.exp (c * v_avg) * w_inv x ∂volume := by
                        apply MeasureTheory.setIntegral_congr_fun measurableSet_ball
                        intro x hx
                        exact hpow_inv_eq x hx
                _ = Real.exp (c * v_avg) * ∫ x in B, w_inv x ∂volume := by
                      rw [integral_const_mul]
        _ = Real.exp (c * v_avg) * (⨍ x in B, w_inv x ∂volume) := by
              rw [MeasureTheory.setAverage_eq, smul_eq_mul]
              ring
    rw [havg_pow, havg_pow_inv]
    calc
      (Real.exp (-c * v_avg) * (⨍ x in B, w x ∂volume)) *
          (Real.exp (c * v_avg) * (⨍ x in B, w_inv x ∂volume))
          = (Real.exp (-c * v_avg) * Real.exp (c * v_avg)) *
              ((⨍ x in B, w x ∂volume) * (⨍ x in B, w_inv x ∂volume)) := by
                ring
      _ = (⨍ x in B, w x ∂volume) * (⨍ x in B, w_inv x ∂volume) := by
            rw [show Real.exp (-c * v_avg) * Real.exp (c * v_avg) = 1 by
              rw [← Real.exp_add]
              simp]
            simp
  exact C_crossover'_spec.2 hd A hu_pos hsuper

/-- Un-averaged half-ball version of `crossover_estimate`.

This is the form needed by downstream weak-Harnack bookkeeping: multiply the
average-product estimate by `|B_{1/2}|^2`. -/
theorem crossover_estimate_unaveraged
    (hd : 2 < (d : ℝ))
    (A : NormalizedEllipticCoeff d (Metric.ball (0 : E) 1))
    {u : E → ℝ}
    (hu_pos : ∀ x ∈ Metric.ball (0 : E) 1, 0 < u x)
    (hsuper : IsSupersolution A.1 u) :
    (∫ x in Metric.ball (0 : E) (1 / 2 : ℝ),
        |u x| ^ (c_crossover' d / A.1.Λ ^ ((1 : ℝ) / 2)) ∂volume) *
      (∫ x in Metric.ball (0 : E) (1 / 2 : ℝ),
        |u x| ^ (-(c_crossover' d / A.1.Λ ^ ((1 : ℝ) / 2))) ∂volume) ≤
        C_crossover' d *
          (volume.real (Metric.ball (0 : E) (1 / 2 : ℝ))) ^ 2 := by
  let B : Set E := Metric.ball (0 : E) (1 / 2 : ℝ)
  set p₀ : ℝ := c_crossover' d / A.1.Λ ^ ((1 : ℝ) / 2)
  set Ipos : ℝ := ∫ x in B, |u x| ^ p₀ ∂volume
  set Ineg : ℝ := ∫ x in B, |u x| ^ (-p₀) ∂volume
  have havg := crossover_estimate (d := d) hd A hu_pos hsuper
  have hvol_pos : 0 < volume.real B := by
    exact ENNReal.toReal_pos
      (measure_ball_pos volume (0 : E) (by norm_num : (0 : ℝ) < 1 / 2)).ne'
      measure_ball_lt_top.ne
  have hvol_ne : volume.real B ≠ 0 := ne_of_gt hvol_pos
  have hscale_nonneg : 0 ≤ (volume.real B) ^ 2 := by positivity
  rw [MeasureTheory.setAverage_eq, MeasureTheory.setAverage_eq, smul_eq_mul, smul_eq_mul] at havg
  have hscaled :=
    mul_le_mul_of_nonneg_left havg hscale_nonneg
  calc
    Ipos * Ineg
        = (volume.real B) ^ 2 * ((volume.real B)⁻¹ * Ipos * ((volume.real B)⁻¹ * Ineg)) := by
            field_simp [hvol_ne]
    _ ≤ (volume.real B) ^ 2 * C_crossover' d := hscaled
    _ = C_crossover' d * (volume.real B) ^ 2 := by ring


end DeGiorgi
