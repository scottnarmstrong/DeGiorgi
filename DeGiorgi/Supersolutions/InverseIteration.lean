import DeGiorgi.Supersolutions.InverseOneStep

/-!
# Supersolutions Inverse Iteration

This module contains the inverse-power Moser iteration and the final
stage-one closeout for positive supersolutions.
-/

noncomputable section

open MeasureTheory Metric

namespace DeGiorgi

variable {d : ℕ} [NeZero d]

local notation "E" => AmbientSpace d
local notation "μhalf" => (volume.restrict (Metric.ball (0 : E) (1 / 2 : ℝ)))

/-! ### Inverse-Power Iteration

Iterate `supersolution_preMoser_inverse` along the geometric sequences
`pₙ = p₀ χⁿ` and `rₙ = (1 + 2^{-n})/2`, then estimate the product and
pass to `L^∞`.
-/

/-- Auxiliary integrals for the inverse-power Moser iteration. -/
noncomputable def superIterIntegralInv
    {u : E → ℝ} (p₀ : ℝ) (n : ℕ) : ℝ :=
  ∫ x in Metric.ball (0 : E) (moserRadius n),
    |(u x)⁻¹| ^ moserExponentSeq d p₀ n ∂volume

/-- Auxiliary `L^{pₙ}` norm for the inverse-power Moser iteration. -/
noncomputable def superIterNormInv
    {u : E → ℝ} (p₀ : ℝ) (n : ℕ) : ℝ :=
  (superIterIntegralInv (d := d) (u := u) p₀ n) ^
    (1 / moserExponentSeq d p₀ n)

/-- The step constant in the supersolution inverse-power iteration at stage `n`.
This is `(C_MoserAnchor d / gap² · (Λ (pₙ/(1+pₙ))² + 1))^{1/pₙ}`. -/
noncomputable def superStepConstInv
    (A : NormalizedEllipticCoeff d (Metric.ball (0 : E) 1))
    (p₀ : ℝ) (n : ℕ) : ℝ :=
  ((C_MoserAnchor d / (moserRadius n - moserRadius (n + 1)) ^ 2) *
    (A.1.Λ * (moserExponentSeq d p₀ n /
      (1 + moserExponentSeq d p₀ n)) ^ 2 + 1)) ^
    (1 / moserExponentSeq d p₀ n)

/-- Iteration of the inverse-power one-step bound by induction.

At each step, `supersolution_preMoser_inverse` provides the `Lᵖⁿ → Lᵖⁿ⁺¹` gain,
and we accumulate the product of step constants. -/
theorem supersolution_iteration_inverse
    (hd : 2 < (d : ℝ))
    (A : NormalizedEllipticCoeff d (Metric.ball (0 : E) 1))
    {u : E → ℝ} {p₀ : ℝ} (hp₀ : 0 < p₀)
    (hu_pos : ∀ x ∈ Metric.ball (0 : E) 1, 0 < u x)
    (hsuper : IsSupersolution A.1 u)
    (hpInt :
      IntegrableOn (fun x => |(u x)⁻¹| ^ p₀)
        (Metric.ball (0 : E) 1) volume) :
    ∀ n : ℕ,
      IntegrableOn (fun x => |(u x)⁻¹| ^ moserExponentSeq d p₀ n)
          (Metric.ball (0 : E) (moserRadius n)) volume ∧
        superIterNormInv (d := d) (u := u) p₀ n ≤
          (∏ i ∈ Finset.range n, superStepConstInv (d := d) A p₀ i) *
            superIterNormInv (d := d) (u := u) p₀ 0 := by
  intro n
  induction n with
  | zero =>
    constructor
    · -- Base case: moserRadius 0 = 1 and moserExponentSeq _ _ 0 = p₀
      rwa [moserExponentSeq_zero, moserRadius_zero]
    · -- Product over empty range is 1
      simp
  | succ n ihn =>
    obtain ⟨hInt_n, hbound_n⟩ := ihn
    let p_n := moserExponentSeq d p₀ n
    have hp_n : 0 < p_n := moserExponentSeq_pos hd hp₀ n
    -- Apply the one-step inverse-power bound
    have hpre :=
      supersolution_preMoser_inverse hd A (p := p_n)
        (r := moserRadius (n + 1)) (s := moserRadius n)
        hp_n (moserRadius_pos (n + 1)) (moserRadius_succ_lt n)
        (moserRadius_le_one n) hu_pos hsuper
        (by simpa [p_n] using hInt_n)
    obtain ⟨hInt_succ, hNorm_succ⟩ := hpre
    refine ⟨?_, ?_⟩
    · -- Integrability: convert moserChi * p_n to p_{n+1}
      have heq : moserChi d * p_n = moserExponentSeq d p₀ (n + 1) := by
        rw [moserExponentSeq_succ]
      rwa [heq] at hInt_succ
    · -- Bound: multiply step bound with inductive hypothesis
      have heq_norm : superIterNormInv (d := d) (u := u) p₀ (n + 1) =
          (∫ x in Metric.ball (0 : E) (moserRadius (n + 1)),
            |(u x)⁻¹| ^ (moserChi d * p_n) ∂volume) ^
              (1 / (moserChi d * p_n)) := by
        simp [superIterNormInv, superIterIntegralInv, p_n, moserExponentSeq_succ]
      have heq_step : superStepConstInv (d := d) A p₀ n =
          ((C_MoserAnchor d / (moserRadius n - moserRadius (n + 1)) ^ 2) *
            (A.1.Λ * (p_n / (1 + p_n)) ^ 2 + 1)) ^ (1 / p_n) := by
        simp [superStepConstInv, p_n]
      have hstep_nonneg : 0 ≤ superStepConstInv (d := d) A p₀ n := by
        rw [heq_step]
        apply Real.rpow_nonneg
        apply mul_nonneg
        · exact div_nonneg
            (le_trans (by norm_num : (0 : ℝ) ≤ 1) (one_le_C_MoserAnchor (d := d)))
            (sq_nonneg _)
        · nlinarith [A.1.Λ_nonneg, sq_nonneg (p_n / (1 + p_n))]
      -- The one-step bound gives:
      --   ‖u⁻¹‖_{n+1} ≤ step_n * ‖u⁻¹‖_n
      have hstep_bound :
          superIterNormInv (d := d) (u := u) p₀ (n + 1) ≤
            superStepConstInv (d := d) A p₀ n *
              superIterNormInv (d := d) (u := u) p₀ n := by
        rw [heq_norm, heq_step]
        convert hNorm_succ using 2
      -- Combine with IH
      calc superIterNormInv (d := d) (u := u) p₀ (n + 1)
          ≤ superStepConstInv (d := d) A p₀ n *
              superIterNormInv (d := d) (u := u) p₀ n := hstep_bound
        _ ≤ superStepConstInv (d := d) A p₀ n *
              ((∏ i ∈ Finset.range n, superStepConstInv (d := d) A p₀ i) *
                superIterNormInv (d := d) (u := u) p₀ 0) := by
            exact mul_le_mul_of_nonneg_left hbound_n hstep_nonneg
        _ = (∏ i ∈ Finset.range (n + 1), superStepConstInv (d := d) A p₀ i) *
              superIterNormInv (d := d) (u := u) p₀ 0 := by
            rw [Finset.prod_range_succ]
            ring

/-- Each inverse-power step constant is bounded by a simpler expression.

The key simplification: `pₙ/(1+pₙ) ≤ pₙ` (since pₙ > 0), and
`gap_n = 2^{-(n+2)}`, so `1/gap_n² = 4^{n+2} = 16 · 4^n`. -/
theorem superStepConstInv_le
    (hd : 2 < (d : ℝ))
    (A : NormalizedEllipticCoeff d (Metric.ball (0 : E) 1))
    {p₀ : ℝ} (hp₀ : 0 < p₀) (i : ℕ) :
    superStepConstInv (d := d) A p₀ i ≤
      (16 * C_MoserAnchor d * (A.1.Λ * p₀ ^ 2 + 1) *
        (4 * moserChi d ^ 2) ^ i) ^
        (1 / moserExponentSeq d p₀ i) := by
  unfold superStepConstInv
  apply Real.rpow_le_rpow
  · -- Nonnegativity of the base
    apply mul_nonneg
    · exact div_nonneg (le_trans (by norm_num : (0 : ℝ) ≤ 1) (one_le_C_MoserAnchor (d := d)))
        (sq_nonneg _)
    · nlinarith [A.1.Λ_nonneg, sq_nonneg (moserExponentSeq d p₀ i / (1 + moserExponentSeq d p₀ i))]
  · -- Main bound
    have hp_i := moserExponentSeq_pos (d := d) hd hp₀ i
    have hgap_eq : C_MoserAnchor d / (moserRadius i - moserRadius (i + 1)) ^ 2 =
        C_MoserAnchor d * (4 : ℝ) ^ (i + 2) := by
      rw [moserRadius_gap]
      have hsq : (((1 / 2 : ℝ) ^ (i + 2)) ^ 2) = (1 / 4 : ℝ) ^ (i + 2) := by
        rw [← pow_mul, show (i + 2) * 2 = 2 * (i + 2) by ring, pow_mul]; norm_num
      rw [hsq, div_eq_mul_inv,
        show (((1 / 4 : ℝ) ^ (i + 2))⁻¹) = (4 : ℝ) ^ (i + 2) by
          rw [show (1 / 4 : ℝ) = (4 : ℝ)⁻¹ by norm_num, inv_pow]; norm_num]
    have hpow4 : (4 : ℝ) ^ (i + 2) = 16 * 4 ^ i := by rw [pow_add]; ring
    -- pₙ/(1+pₙ) ≤ pₙ, so Λ(pₙ/(1+pₙ))² ≤ Λpₙ²
    have hratio_le : (moserExponentSeq d p₀ i / (1 + moserExponentSeq d p₀ i)) ^ 2 ≤
        (moserExponentSeq d p₀ i) ^ 2 := by
      have hdiv_le : moserExponentSeq d p₀ i / (1 + moserExponentSeq d p₀ i) ≤
          moserExponentSeq d p₀ i :=
        div_le_self hp_i.le (by linarith)
      have hdiv_nonneg : 0 ≤ moserExponentSeq d p₀ i / (1 + moserExponentSeq d p₀ i) :=
        div_nonneg hp_i.le (by linarith)
      nlinarith [sq_nonneg (moserExponentSeq d p₀ i - moserExponentSeq d p₀ i / (1 + moserExponentSeq d p₀ i))]
    -- pₙ² = p₀² · χ^{2i}
    have hseq_sq : (moserExponentSeq d p₀ i) ^ 2 = p₀ ^ 2 * (moserChi d) ^ (2 * i) := by
      rw [moserExponentSeq]; ring
    -- Combine: Λ(pₙ/(1+pₙ))² + 1 ≤ (Λp₀² + 1) · χ^{2i}
    have hcoeff_le :
        A.1.Λ * (moserExponentSeq d p₀ i / (1 + moserExponentSeq d p₀ i)) ^ 2 + 1 ≤
          (A.1.Λ * p₀ ^ 2 + 1) * (moserChi d ^ 2) ^ i := by
      have hchi_sq_ge_one : 1 ≤ (moserChi d ^ 2) ^ i :=
        one_le_pow₀ (by nlinarith [one_lt_moserChi (d := d) hd])
      have hΛratio :
          A.1.Λ * (moserExponentSeq d p₀ i / (1 + moserExponentSeq d p₀ i)) ^ 2 ≤
            A.1.Λ * p₀ ^ 2 * (moserChi d ^ 2) ^ i := by
        calc A.1.Λ * (moserExponentSeq d p₀ i / (1 + moserExponentSeq d p₀ i)) ^ 2
            ≤ A.1.Λ * (moserExponentSeq d p₀ i) ^ 2 :=
              mul_le_mul_of_nonneg_left hratio_le A.1.Λ_nonneg
          _ = A.1.Λ * (p₀ ^ 2 * (moserChi d) ^ (2 * i)) := by rw [hseq_sq]
          _ = A.1.Λ * p₀ ^ 2 * (moserChi d ^ 2) ^ i := by rw [pow_mul]; ring
      nlinarith
    rw [hgap_eq, hpow4]
    calc C_MoserAnchor d * (16 * 4 ^ i) *
            (A.1.Λ * (moserExponentSeq d p₀ i / (1 + moserExponentSeq d p₀ i)) ^ 2 + 1)
        ≤ C_MoserAnchor d * (16 * 4 ^ i) *
            ((A.1.Λ * p₀ ^ 2 + 1) * (moserChi d ^ 2) ^ i) := by
          gcongr
          exact mul_nonneg (le_trans (by norm_num : (0 : ℝ) ≤ 1) (one_le_C_MoserAnchor (d := d)))
            (by positivity)
      _ = 16 * C_MoserAnchor d * (A.1.Λ * p₀ ^ 2 + 1) * (4 * moserChi d ^ 2) ^ i := by
          rw [show (4 * moserChi d ^ 2) ^ i = 4 ^ i * (moserChi d ^ 2) ^ i by rw [mul_pow]]
          ring
  · exact div_nonneg (by norm_num) (moserExponentSeq_pos (d := d) hd hp₀ i).le

theorem supersolution_geometric_majorant_inv
    (hd : 2 < (d : ℝ))
    (A : NormalizedEllipticCoeff d (Metric.ball (0 : E) 1))
    {p₀ : ℝ} (hp₀ : 0 < p₀) (n : ℕ) :
    ∏ i ∈ Finset.range n, superStepConstInv (d := d) A p₀ i ≤
      (C_weakHarnack0 d * (A.1.Λ * p₀ ^ 2 + 1) ^ ((d : ℝ) / 2)) ^
        (1 / p₀) := by
  let q := moserDecayRatio d
  let K₀ : ℝ := 16 * C_MoserAnchor d
  let L : ℝ := A.1.Λ * p₀ ^ 2 + 1
  let K : ℝ := K₀ * L
  let CC : ℝ := 4 * moserChi d ^ 2
  let S : ℝ := Finset.sum (Finset.range n) (fun i => q ^ i)
  let T : ℝ := Finset.sum (Finset.range n) (fun i => (i : ℝ) * q ^ i)
  have hq_nonneg : 0 ≤ q := by
    simpa [q] using moserDecayRatio_nonneg (d := d) hd
  have hq_lt_one : q < 1 := by
    simpa [q] using moserDecayRatio_lt_one (d := d) hd
  have hS_le : S ≤ (d : ℝ) / 2 := by
    simpa [q, S] using moserDecayRatio_sum_le_half_dim (d := d) hd n
  have hT_le : T ≤ ∑' i : ℕ, (i : ℝ) * q ^ i := by
    simpa [q, T] using moserDecayRatio_weighted_sum_le_tsum (d := d) hd n
  have hK₀_ge_one : 1 ≤ K₀ := by
    dsimp [K₀]
    nlinarith [one_le_C_MoserAnchor (d := d)]
  have hK₀_nonneg : 0 ≤ K₀ := by
    linarith
  have hL_ge_one : 1 ≤ L := by
    dsimp [L]
    nlinarith [A.1.Λ_nonneg, sq_nonneg p₀]
  have hL_nonneg : 0 ≤ L := by
    linarith
  have hK_pos : 0 < K := by
    dsimp [K]
    exact mul_pos (lt_of_lt_of_le zero_lt_one hK₀_ge_one) (by positivity)
  have hK_nonneg : 0 ≤ K := hK_pos.le
  have hCC_pos : 0 < CC := by
    dsimp [CC]
    exact mul_pos (by norm_num : (0 : ℝ) < 4) (sq_pos_of_pos (moserChi_pos (d := d) hd))
  have hCC_nonneg : 0 ≤ CC := hCC_pos.le
  have hstep_le : ∀ i, i ∈ Finset.range n →
      superStepConstInv (d := d) A p₀ i ≤ (K * CC ^ i) ^
        (1 / moserExponentSeq d p₀ i) := by
    intro i _
    simpa [K, K₀, L, CC] using superStepConstInv_le (d := d) hd A hp₀ i
  -- Each step is nonneg
  have hstep_nonneg : ∀ i, i ∈ Finset.range n →
      0 ≤ superStepConstInv (d := d) A p₀ i := by
    intro i _
    dsimp [superStepConstInv]
    apply Real.rpow_nonneg
    apply mul_nonneg
    · exact div_nonneg (le_trans (by norm_num : (0:ℝ) ≤ 1) (one_le_C_MoserAnchor (d := d))) (sq_nonneg _)
    · nlinarith [A.1.Λ_nonneg, sq_nonneg (moserExponentSeq d p₀ i / (1 + moserExponentSeq d p₀ i))]
  have hprod_le :
      ∏ i ∈ Finset.range n, superStepConstInv (d := d) A p₀ i ≤
        ∏ i ∈ Finset.range n, (K * CC ^ i) ^
          (1 / moserExponentSeq d p₀ i) :=
    Finset.prod_le_prod hstep_nonneg hstep_le
  have hprod_eval :
      ∀ m : ℕ,
        ∏ i ∈ Finset.range m, (K * CC ^ i) ^
            (1 / moserExponentSeq d p₀ i) =
          (K ^ (Finset.sum (Finset.range m) (fun i => q ^ i)) *
            CC ^ (Finset.sum (Finset.range m) (fun i => (i : ℝ) * q ^ i))) ^
            (1 / p₀) := by
    intro m
    induction m with
    | zero =>
        simp
    | succ m ihm =>
        let Sₘ : ℝ := Finset.sum (Finset.range m) (fun i => q ^ i)
        let Tₘ : ℝ := Finset.sum (Finset.range m) (fun i => (i : ℝ) * q ^ i)
        have hinv :
            1 / moserExponentSeq d p₀ m = q ^ m / p₀ := by
          simpa [q] using inv_moserExponentSeq (d := d) hd hp₀ m
        have hdiv_eq :
            1 / moserExponentSeq d p₀ m = q ^ m * (1 / p₀) := by
          rw [hinv]
          ring
        rw [Finset.prod_range_succ, ihm, hdiv_eq]
        have hKC_nonneg : 0 ≤ K * CC ^ m := by
          exact mul_nonneg hK_nonneg (pow_nonneg hCC_nonneg m)
        rw [Real.rpow_mul hKC_nonneg]
        rw [Real.mul_rpow hK_nonneg (pow_nonneg hCC_nonneg m)]
        have hCC_pow :
            ((CC ^ m : ℝ)) ^ (q ^ m) = CC ^ ((m : ℝ) * q ^ m) := by
          rw [show ((CC ^ m : ℝ)) = CC ^ (m : ℝ) by rw [Real.rpow_natCast]]
          rw [← Real.rpow_mul hCC_nonneg]
        rw [hCC_pow]
        have hfront_nonneg :
            0 ≤ K ^ (q ^ m) * CC ^ ((m : ℝ) * q ^ m) := by
          exact mul_nonneg (Real.rpow_nonneg hK_nonneg _) (Real.rpow_nonneg hCC_nonneg _)
        have hback_nonneg :
            0 ≤ K ^ Sₘ * CC ^ Tₘ := by
          exact mul_nonneg (Real.rpow_nonneg hK_nonneg _) (Real.rpow_nonneg hCC_nonneg _)
        rw [mul_comm, ← Real.mul_rpow hfront_nonneg hback_nonneg]
        congr 1
        calc
          (K ^ (q ^ m) * CC ^ ((m : ℝ) * q ^ m)) * (K ^ Sₘ * CC ^ Tₘ)
              = (K ^ (q ^ m) * K ^ Sₘ) * (CC ^ ((m : ℝ) * q ^ m) * CC ^ Tₘ) := by
                  ring
          _ = K ^ (q ^ m + Sₘ) * CC ^ (((m : ℝ) * q ^ m) + Tₘ) := by
                rw [← Real.rpow_add hK_pos, ← Real.rpow_add hCC_pos]
          _ =
              K ^ (Finset.sum (Finset.range (m + 1)) (fun i => q ^ i)) *
                CC ^ (Finset.sum (Finset.range (m + 1))
                  (fun i => (i : ℝ) * q ^ i)) := by
                simp [Sₘ, Tₘ, Finset.sum_range_succ, add_comm]
  have hK_pow_eq :
      K ^ S = K₀ ^ S * L ^ S := by
    rw [show K = K₀ * L by rfl, Real.mul_rpow hK₀_nonneg hL_nonneg]
  have hK₀_pow_le : K₀ ^ S ≤ K₀ ^ ((d : ℝ) / 2) := by
    exact Real.rpow_le_rpow_of_exponent_le hK₀_ge_one hS_le
  have hL_pow_le : L ^ S ≤ L ^ ((d : ℝ) / 2) := by
    exact Real.rpow_le_rpow_of_exponent_le hL_ge_one hS_le
  have hK_le :
      K ^ S ≤ K₀ ^ ((d : ℝ) / 2) * L ^ ((d : ℝ) / 2) := by
    rw [hK_pow_eq]
    exact mul_le_mul hK₀_pow_le hL_pow_le
      (Real.rpow_nonneg hL_nonneg _) (Real.rpow_nonneg hK₀_nonneg _)
  have h4_le :
      (4 : ℝ) ^ T ≤ 4 ^ (∑' i : ℕ, (i : ℝ) * q ^ i) := by
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 4) hT_le
  have hchi_sq_ge_one : 1 ≤ moserChi d ^ 2 := by
    exact one_le_pow₀ (one_le_moserChi (d := d) hd)
  have hchi_le :
      (moserChi d ^ 2) ^ T ≤ (moserChi d ^ 2) ^ (∑' i : ℕ, (i : ℝ) * q ^ i) := by
    exact Real.rpow_le_rpow_of_exponent_le hchi_sq_ge_one hT_le
  have hCC_le :
      CC ^ T ≤
        4 ^ (∑' i : ℕ, (i : ℝ) * q ^ i) *
          (moserChi d ^ 2) ^ (∑' i : ℕ, (i : ℝ) * q ^ i) := by
    calc
      CC ^ T = (4 : ℝ) ^ T * (moserChi d ^ 2) ^ T := by
        rw [show CC = 4 * (moserChi d ^ 2) by simp [CC]]
        rw [Real.mul_rpow (by positivity) (sq_nonneg _)]
      _ ≤ 4 ^ (∑' i : ℕ, (i : ℝ) * q ^ i) *
            (moserChi d ^ 2) ^ (∑' i : ℕ, (i : ℝ) * q ^ i) := by
          exact mul_le_mul h4_le hchi_le
            (Real.rpow_nonneg (sq_nonneg _) _)
            (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 4) _)
  have hK₀_pow_le_big :
      K₀ ^ ((d : ℝ) / 2) ≤ ((32 : ℝ) * C_MoserAnchor d) ^ ((d : ℝ) / 2) := by
    exact Real.rpow_le_rpow
      hK₀_nonneg
      (by
        dsimp [K₀]
        nlinarith [one_le_C_MoserAnchor (d := d)])
      (by positivity)
  have hCMoser_le :
      K₀ ^ ((d : ℝ) / 2) * 4 ^ (∑' i : ℕ, (i : ℝ) * q ^ i) ≤ C_Moser d := by
    have hbase :
        K₀ ^ ((d : ℝ) / 2) * 4 ^ (∑' i : ℕ, (i : ℝ) * q ^ i) ≤
          ((32 : ℝ) * C_MoserAnchor d) ^ ((d : ℝ) / 2) *
            4 ^ (∑' i : ℕ, (i : ℝ) * q ^ i) := by
      exact mul_le_mul_of_nonneg_right hK₀_pow_le_big
        (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 4) _)
    have hmax :
        ((32 : ℝ) * C_MoserAnchor d) ^ ((d : ℝ) / 2) *
            4 ^ (∑' i : ℕ, (i : ℝ) * q ^ i) ≤
          C_Moser d := by
      dsimp [C_Moser, q]
      split_ifs with hlt
      · exact
          le_max_right (C_MoserAnchor d)
            (((32 : ℝ) * C_MoserAnchor d) ^ ((d : ℝ) / 2) *
              4 ^ (∑' i : ℕ, (i : ℝ) * moserDecayRatio d ^ i))
      · exact False.elim (hlt hd)
    exact hbase.trans hmax
  have hCweak_eq :
      C_Moser d * (moserChi d ^ 2) ^ (∑' i : ℕ, (i : ℝ) * q ^ i) =
        C_weakHarnack0 d := by
    simp [C_weakHarnack0, hd, q]
  have hbody_le :
      K ^ S * CC ^ T ≤
        C_weakHarnack0 d * L ^ ((d : ℝ) / 2) := by
    have hCC_target_nonneg :
        0 ≤ 4 ^ (∑' i : ℕ, (i : ℝ) * q ^ i) *
            (moserChi d ^ 2) ^ (∑' i : ℕ, (i : ℝ) * q ^ i) := by
      exact mul_nonneg
        (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 4) _)
        (Real.rpow_nonneg (sq_nonneg _) _)
    have hK_target_nonneg :
        0 ≤ K₀ ^ ((d : ℝ) / 2) * L ^ ((d : ℝ) / 2) := by
      exact mul_nonneg (Real.rpow_nonneg hK₀_nonneg _) (Real.rpow_nonneg hL_nonneg _)
    calc
      K ^ S * CC ^ T
          ≤ (K₀ ^ ((d : ℝ) / 2) * L ^ ((d : ℝ) / 2)) *
              (4 ^ (∑' i : ℕ, (i : ℝ) * q ^ i) *
                (moserChi d ^ 2) ^ (∑' i : ℕ, (i : ℝ) * q ^ i)) := by
            exact mul_le_mul hK_le hCC_le
              (Real.rpow_nonneg hCC_nonneg _)
              hK_target_nonneg
      _ = (K₀ ^ ((d : ℝ) / 2) * 4 ^ (∑' i : ℕ, (i : ℝ) * q ^ i)) *
            ((moserChi d ^ 2) ^ (∑' i : ℕ, (i : ℝ) * q ^ i) * L ^ ((d : ℝ) / 2)) := by
              ring
      _ ≤ C_Moser d *
            ((moserChi d ^ 2) ^ (∑' i : ℕ, (i : ℝ) * q ^ i) * L ^ ((d : ℝ) / 2)) := by
              exact mul_le_mul_of_nonneg_right hCMoser_le
                (mul_nonneg (Real.rpow_nonneg (sq_nonneg _) _) (Real.rpow_nonneg hL_nonneg _))
      _ = C_weakHarnack0 d * L ^ ((d : ℝ) / 2) := by
            rw [← hCweak_eq]
            ring
  calc
    ∏ i ∈ Finset.range n, superStepConstInv (d := d) A p₀ i
        ≤ ∏ i ∈ Finset.range n, (K * CC ^ i) ^ (1 / moserExponentSeq d p₀ i) := hprod_le
    _ = (K ^ S * CC ^ T) ^ (1 / p₀) := by
          simpa [q, S, T] using hprod_eval n
    _ ≤ (C_weakHarnack0 d * L ^ ((d : ℝ) / 2)) ^ (1 / p₀) := by
          exact Real.rpow_le_rpow
            (mul_nonneg (Real.rpow_nonneg hK_nonneg _) (Real.rpow_nonneg hCC_nonneg _))
            hbody_le (by positivity)
    _ = (C_weakHarnack0 d * (A.1.Λ * p₀ ^ 2 + 1) ^ ((d : ℝ) / 2)) ^ (1 / p₀) := by
          simp [L]

theorem supersolutionCloseoutExponent_tendsto_atTop
    (hd : 2 < (d : ℝ)) :
    Filter.Tendsto (fun n : ℕ => 2 * moserChi d ^ n) Filter.atTop Filter.atTop := by
  exact Filter.Tendsto.const_mul_atTop (by norm_num : 0 < (2 : ℝ))
    (tendsto_pow_atTop_atTop_of_one_lt (one_lt_moserChi (d := d) hd))

theorem supersolutionInvBoundPow_nonneg
    (A : NormalizedEllipticCoeff d (Metric.ball (0 : E) 1))
    {u : E → ℝ} {p₀ : ℝ} :
    0 ≤
      C_weakHarnack0 d * (A.1.Λ * p₀ ^ 2 + 1) ^ ((d : ℝ) / 2) *
        ∫ x in Metric.ball (0 : E) 1, |(u x)⁻¹| ^ p₀ ∂volume := by
  refine mul_nonneg ?_ ?_
  · refine mul_nonneg ?_ ?_
    · exact le_trans (by norm_num : (0 : ℝ) ≤ 1) (one_le_C_weakHarnack0 (d := d))
    · exact Real.rpow_nonneg (by nlinarith [A.1.Λ_nonneg, sq_nonneg p₀]) _
  · exact integral_nonneg fun x => by positivity

theorem superIterNormInv_zero
    {u : E → ℝ} {p₀ : ℝ} :
    superIterNormInv (d := d) (u := u) p₀ 0 =
      (∫ x in Metric.ball (0 : E) 1, |(u x)⁻¹| ^ p₀ ∂volume) ^ (1 / p₀) := by
  simp [superIterNormInv, superIterIntegralInv, moserRadius_zero, moserExponentSeq_zero]

theorem supersolutionInvMajorant_rpow_half
    (A : NormalizedEllipticCoeff d (Metric.ball (0 : E) 1))
    {u : E → ℝ} {p₀ : ℝ} (hp₀ : 0 < p₀) :
    ((((C_weakHarnack0 d * (A.1.Λ * p₀ ^ 2 + 1) ^ ((d : ℝ) / 2)) ^
          (1 / p₀)) *
        superIterNormInv (d := d) (u := u) p₀ 0) ^ (p₀ / 2))
      =
      (C_weakHarnack0 d * (A.1.Λ * p₀ ^ 2 + 1) ^ ((d : ℝ) / 2) *
        ∫ x in Metric.ball (0 : E) 1, |(u x)⁻¹| ^ p₀ ∂volume) ^ (1 / 2 : ℝ) := by
  let C : ℝ := C_weakHarnack0 d * (A.1.Λ * p₀ ^ 2 + 1) ^ ((d : ℝ) / 2)
  let I : ℝ := ∫ x in Metric.ball (0 : E) 1, |(u x)⁻¹| ^ p₀ ∂volume
  have hp₀_ne : p₀ ≠ 0 := hp₀.ne'
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    refine mul_nonneg ?_ ?_
    · exact le_trans (by norm_num : (0 : ℝ) ≤ 1) (one_le_C_weakHarnack0 (d := d))
    · exact Real.rpow_nonneg (by nlinarith [A.1.Λ_nonneg, sq_nonneg p₀]) _
  have hI_nonneg : 0 ≤ I := by
    dsimp [I]
    exact integral_nonneg fun x => by positivity
  have hCroot_nonneg : 0 ≤ C ^ (1 / p₀) := Real.rpow_nonneg hC_nonneg _
  have hIroot_nonneg : 0 ≤ I ^ (1 / p₀) := Real.rpow_nonneg hI_nonneg _
  have hmul : (1 / p₀) * (p₀ / 2) = (1 / 2 : ℝ) := by
    field_simp [hp₀_ne]
  rw [superIterNormInv_zero]
  calc
    ((C ^ (1 / p₀)) * I ^ (1 / p₀)) ^ (p₀ / 2)
        = (C ^ (1 / p₀)) ^ (p₀ / 2) * (I ^ (1 / p₀)) ^ (p₀ / 2) := by
            rw [Real.mul_rpow hCroot_nonneg hIroot_nonneg]
    _ = C ^ ((1 / p₀) * (p₀ / 2)) * I ^ ((1 / p₀) * (p₀ / 2)) := by
          rw [← Real.rpow_mul hC_nonneg, ← Real.rpow_mul hI_nonneg]
    _ = C ^ (1 / 2 : ℝ) * I ^ (1 / 2 : ℝ) := by rw [hmul]
    _ = (C * I) ^ (1 / 2 : ℝ) := by
          symm
          rw [Real.mul_rpow hC_nonneg hI_nonneg]

theorem supersolution_closeout_superlevel_null
    (hd : 2 < (d : ℝ))
    (A : NormalizedEllipticCoeff d (Metric.ball (0 : E) 1))
    {u : E → ℝ} {p₀ : ℝ} (hp₀ : 0 < p₀)
    (hiter :
      ∀ n,
        IntegrableOn (fun x => |(u x)⁻¹| ^ moserExponentSeq d p₀ n)
          (Metric.ball (0 : E) (moserRadius n)) volume ∧
        superIterNormInv (d := d) (u := u) p₀ n ≤
          ((C_weakHarnack0 d * (A.1.Λ * p₀ ^ 2 + 1) ^ ((d : ℝ) / 2)) ^
            (1 / p₀)) *
            superIterNormInv (d := d) (u := u) p₀ 0)
    {c : ℝ}
    (hc :
      (C_weakHarnack0 d * (A.1.Λ * p₀ ^ 2 + 1) ^ ((d : ℝ) / 2) *
        ∫ x in Metric.ball (0 : E) 1, |(u x)⁻¹| ^ p₀ ∂volume) ^
          (1 / 2 : ℝ) < c) :
    (volume.restrict (Metric.ball (0 : E) (1 / 2 : ℝ))).real
      {x | c ≤ |(u x)⁻¹| ^ (p₀ / 2 : ℝ)} = 0 := by
  let Bhalf : Set E := Metric.ball (0 : E) (1 / 2 : ℝ)
  let μ : Measure E := volume.restrict Bhalf
  let f : E → ℝ := fun x => |(u x)⁻¹|
  let g : E → ℝ := fun x => f x ^ (p₀ / 2)
  let K : ℝ :=
    (C_weakHarnack0 d * (A.1.Λ * p₀ ^ 2 + 1) ^ ((d : ℝ) / 2) *
      ∫ x in Metric.ball (0 : E) 1, |(u x)⁻¹| ^ p₀ ∂volume) ^ (1 / 2 : ℝ)
  let S : Set E := {x | c ≤ g x}
  haveI : IsFiniteMeasure μ := by
    dsimp [μ, Bhalf]
    rw [isFiniteMeasure_restrict]
    exact measure_ne_top_of_subset Metric.ball_subset_closedBall
      (isCompact_closedBall (0 : E) (1 / 2 : ℝ)).measure_lt_top.ne
  have hK_nonneg : 0 ≤ K := by
    dsimp [K]
    exact Real.rpow_nonneg (supersolutionInvBoundPow_nonneg (d := d) A) _
  have hc_pos : 0 < c := by linarith
  have hratio_nonneg : 0 ≤ K / c := by positivity
  have hratio_lt_one : K / c < 1 := by
    exact (div_lt_one hc_pos).2 hc
  have hq_tendsto :
      Filter.Tendsto (fun n : ℕ => 2 * moserChi d ^ n) Filter.atTop Filter.atTop :=
    supersolutionCloseoutExponent_tendsto_atTop (d := d) hd
  have hratio_tendsto :
      Filter.Tendsto (fun n : ℕ => (K / c) ^ (2 * moserChi d ^ n)) Filter.atTop (nhds 0) := by
    have hratio_gt_neg_one : -1 < K / c := by
      linarith
    exact (tendsto_rpow_atTop_of_base_lt_one (K / c) hratio_gt_neg_one hratio_lt_one).comp
      hq_tendsto
  have hmeasure_le :
      ∀ n : ℕ, μ.real S ≤ (K / c) ^ (2 * moserChi d ^ n) := by
    intro n
    let p_n : ℝ := moserExponentSeq d p₀ n
    let q_n : ℝ := 2 * moserChi d ^ n
    have hp_n_pos : 0 < p_n := by
      simpa [p_n] using moserExponentSeq_pos (d := d) hd hp₀ n
    have hq_n_nonneg : 0 ≤ q_n := by
      dsimp [q_n]
      exact mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
        (pow_nonneg (le_of_lt (moserChi_pos (d := d) hd)) n)
    have hq_n_pos : 0 < q_n := by
      dsimp [q_n]
      exact mul_pos (by norm_num : (0 : ℝ) < 2)
        (pow_pos (moserChi_pos (d := d) hd) n)
    have hq_n_ge_two : 2 ≤ q_n := by
      dsimp [q_n]
      have hpow_ge : 1 ≤ moserChi d ^ n := by
        exact one_le_pow₀ (one_le_moserChi (d := d) hd)
      nlinarith
    have hBsub : Bhalf ⊆ Metric.ball (0 : E) (moserRadius n) := by
      exact Metric.ball_subset_ball (le_of_lt (moserRadius_gt_half n))
    have hf_nonneg : ∀ x, 0 ≤ f x := by
      intro x
      exact abs_nonneg ((u x)⁻¹)
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
          let Ibig : ℝ := superIterIntegralInv (d := d) (u := u) p₀ n
          have hIhalf_nonneg : 0 ≤ Ihalf := by
            dsimp [Ihalf]
            refine integral_nonneg ?_
            intro x
            exact Real.rpow_nonneg (hg_nonneg x) _
          have hIbig_nonneg : 0 ≤ Ibig := by
            dsimp [Ibig, superIterIntegralInv]
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
                field_simp [hp₀.ne', pow_ne_zero n (moserChi_pos (d := d) hd).ne']
              have hpow_le :
                  superIterNormInv (d := d) (u := u) p₀ n ^ (p₀ / 2) ≤
                    (((C_weakHarnack0 d * (A.1.Λ * p₀ ^ 2 + 1) ^ ((d : ℝ) / 2)) ^
                      (1 / p₀)) *
                      superIterNormInv (d := d) (u := u) p₀ 0) ^ (p₀ / 2) := by
                exact Real.rpow_le_rpow
                  (by
                    dsimp [superIterNormInv]
                    exact Real.rpow_nonneg hIbig_nonneg _)
                  ((hiter n).2)
                  (by positivity)
              calc
                Ibig ^ (1 / q_n)
                    = superIterNormInv (d := d) (u := u) p₀ n ^ (p₀ / 2) := by
                        dsimp [Ibig, superIterNormInv]
                        rw [hq_inv, ← Real.rpow_mul hIbig_nonneg]
                _ ≤ (((C_weakHarnack0 d * (A.1.Λ * p₀ ^ 2 + 1) ^ ((d : ℝ) / 2)) ^
                      (1 / p₀)) *
                      superIterNormInv (d := d) (u := u) p₀ 0) ^ (p₀ / 2) := hpow_le
                _ = K := by
                      dsimp [K]
                      simpa using supersolutionInvMajorant_rpow_half
                        (d := d) A (u := u) hp₀
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

/-- Closeout: pass from iterated `L^{pₙ}(B_{rₙ})` bounds to an a.e. `L^∞`
bound on `u⁻¹` over `B_{1/2}`.

Since `rₙ > 1/2` for all `n` and `pₙ → ∞`, the `L^{pₙ}` norms converge to
the `L^∞` norm. The uniform bound from the iteration + geometric majorant
gives the pointwise bound. -/
theorem supersolution_ae_closeout_inv
    (hd : 2 < (d : ℝ))
    (A : NormalizedEllipticCoeff d (Metric.ball (0 : E) 1))
    {u : E → ℝ} {p₀ : ℝ} (hp₀ : 0 < p₀)
    (hu_pos : ∀ x ∈ Metric.ball (0 : E) 1, 0 < u x)
    (hsuper : IsSupersolution A.1 u)
    (hpInt :
      IntegrableOn (fun x => |(u x)⁻¹| ^ p₀)
        (Metric.ball (0 : E) 1) volume) :
    ∀ᵐ x ∂(volume.restrict (Metric.ball (0 : E) (1 / 2 : ℝ))),
      |(u x)⁻¹| ^ p₀ ≤
        C_weakHarnack0 d * (A.1.Λ * p₀ ^ 2 + 1) ^ ((d : ℝ) / 2) *
          ∫ x in Metric.ball (0 : E) 1, |(u x)⁻¹| ^ p₀ ∂volume := by
  let Bhalf : Set E := Metric.ball (0 : E) (1 / 2 : ℝ)
  let μ : Measure E := volume.restrict Bhalf
  let f : E → ℝ := fun x => |(u x)⁻¹|
  let g : E → ℝ := fun x => f x ^ (p₀ / 2)
  let K : ℝ :=
    (C_weakHarnack0 d * (A.1.Λ * p₀ ^ 2 + 1) ^ ((d : ℝ) / 2) *
      ∫ x in Metric.ball (0 : E) 1, |(u x)⁻¹| ^ p₀ ∂volume) ^ (1 / 2 : ℝ)
  haveI : IsFiniteMeasure μ := by
    dsimp [μ, Bhalf]
    rw [isFiniteMeasure_restrict]
    exact measure_ne_top_of_subset Metric.ball_subset_closedBall
      (isCompact_closedBall (0 : E) (1 / 2 : ℝ)).measure_lt_top.ne
  have hK_nonneg : 0 ≤ K := by
    dsimp [K]
    exact Real.rpow_nonneg (supersolutionInvBoundPow_nonneg (d := d) A) _
  have hiter :
      ∀ n,
        IntegrableOn (fun x => |(u x)⁻¹| ^ moserExponentSeq d p₀ n)
          (Metric.ball (0 : E) (moserRadius n)) volume ∧
        superIterNormInv (d := d) (u := u) p₀ n ≤
          ((C_weakHarnack0 d * (A.1.Λ * p₀ ^ 2 + 1) ^ ((d : ℝ) / 2)) ^
            (1 / p₀)) *
            superIterNormInv (d := d) (u := u) p₀ 0 := by
    intro n
    have hraw := supersolution_iteration_inverse (d := d) hd A hp₀ hu_pos hsuper hpInt n
    have hgeom := supersolution_geometric_majorant_inv (d := d) hd A hp₀ n
    refine ⟨hraw.1, ?_⟩
    calc
      superIterNormInv (d := d) (u := u) p₀ n
          ≤ (∏ i ∈ Finset.range n, superStepConstInv (d := d) A p₀ i) *
              superIterNormInv (d := d) (u := u) p₀ 0 := hraw.2
      _ ≤ ((C_weakHarnack0 d * (A.1.Λ * p₀ ^ 2 + 1) ^ ((d : ℝ) / 2)) ^
            (1 / p₀)) *
            superIterNormInv (d := d) (u := u) p₀ 0 := by
            exact mul_le_mul_of_nonneg_right hgeom
              (by
                dsimp [superIterNormInv]
                exact Real.rpow_nonneg (integral_nonneg fun x => by positivity) _)
  have hbound_all :
      ∀ m : ℕ, ∀ᵐ x ∂μ, g x < K + 1 / (m + 1 : ℝ) := by
    intro m
    have hzero :
        μ.real {x | K + 1 / (m + 1 : ℝ) ≤ g x} = 0 := by
      refine supersolution_closeout_superlevel_null (d := d) hd A (u := u) hp₀ hiter ?_
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
    exact abs_nonneg ((u x)⁻¹)
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
      K ^ (2 : ℝ) =
        C_weakHarnack0 d * (A.1.Λ * p₀ ^ 2 + 1) ^ ((d : ℝ) / 2) *
          ∫ x in Metric.ball (0 : E) 1, |(u x)⁻¹| ^ p₀ ∂volume := by
    calc
      K ^ (2 : ℝ)
          =
            (C_weakHarnack0 d * (A.1.Λ * p₀ ^ 2 + 1) ^ ((d : ℝ) / 2) *
              ∫ x in Metric.ball (0 : E) 1, |(u x)⁻¹| ^ p₀ ∂volume) ^
              ((1 / 2 : ℝ) * 2) := by
                dsimp [K]
                rw [← Real.rpow_mul (supersolutionInvBoundPow_nonneg (d := d) A)]
      _ =
            C_weakHarnack0 d * (A.1.Λ * p₀ ^ 2 + 1) ^ ((d : ℝ) / 2) *
              ∫ x in Metric.ball (0 : E) 1, |(u x)⁻¹| ^ p₀ ∂volume := by
                rw [show ((1 / 2 : ℝ) * 2) = (1 : ℝ) by ring, Real.rpow_one]
  calc
    |(u x)⁻¹| ^ p₀ = f x ^ p₀ := by rfl
    _ = g x ^ (2 : ℝ) := hg_sq_eq.symm
    _ ≤ K ^ (2 : ℝ) := hgpow
    _ = C_weakHarnack0 d * (A.1.Λ * p₀ ^ 2 + 1) ^ ((d : ℝ) / 2) *
          ∫ x in Metric.ball (0 : E) 1, |(u x)⁻¹| ^ p₀ ∂volume := hK_sq_eq


end DeGiorgi
