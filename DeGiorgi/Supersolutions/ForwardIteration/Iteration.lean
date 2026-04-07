import DeGiorgi.Supersolutions.ForwardIteration.OneStep

/-!
# Supersolutions Forward Finite Iteration

This module contains the finite forward iteration and geometric majorant used
in the second stage of weak Harnack.
-/

noncomputable section

open MeasureTheory Metric

namespace DeGiorgi

variable {d : ℕ} [NeZero d]

local notation "E" => AmbientSpace d
local notation "μhalf" => (volume.restrict (Metric.ball (0 : E) (1 / 2 : ℝ)))

/-! ### Forward Low-Power Iteration

This is a *finite* iteration: given `q ∈ (0,1)` and depth `m`, define
`p₀ = q χ^{-m}` and iterate `supersolution_preMoser_forward` `m` times from
`p₀` to `pₘ = q`. The product is bounded similarly, then send `m → ∞`.
-/

/-- Auxiliary integrals for the forward low-power Moser iteration. -/
noncomputable def superIterIntegralFwd
    {u : E → ℝ} (p₀ : ℝ) (n : ℕ) : ℝ :=
  ∫ x in Metric.ball (0 : E) (moserRadius n),
    |u x| ^ moserExponentSeq d p₀ n ∂volume

/-- Auxiliary `L^{pₙ}` norm for the forward low-power Moser iteration. -/
noncomputable def superIterNormFwd
    {u : E → ℝ} (p₀ : ℝ) (n : ℕ) : ℝ :=
  (superIterIntegralFwd (d := d) (u := u) p₀ n) ^
    (1 / moserExponentSeq d p₀ n)

/-- The step constant in the forward low-power iteration at stage `n`.
This is `(C_MoserAnchor d / gap² · (Λ (pₙ/(1-pₙ))² + 1))^{1/pₙ}`. -/
noncomputable def superStepConstFwd
    (A : NormalizedEllipticCoeff d (Metric.ball (0 : E) 1))
    (p₀ : ℝ) (n : ℕ) : ℝ :=
  ((C_MoserAnchor d / (moserRadius n - moserRadius (n + 1)) ^ 2) *
    (A.1.Λ * (moserExponentSeq d p₀ n /
      (1 - moserExponentSeq d p₀ n)) ^ 2 + 1)) ^
    (1 / moserExponentSeq d p₀ n)

/-- Finite iteration of the forward low-power one-step bound.

Given target `q ∈ (0,1)` and base exponent `p₀ = q χ^{-m}`, iterate
`supersolution_preMoser_forward` `m+1` steps to go from
`L^{p₀}(B₁)` to `L^{qχ}(B_{r_{m+1}})`. The exponents `pₙ` stay below 1
since `pₘ = q < 1` and the sequence is increasing. -/
theorem supersolution_iteration_forward
    (hd : 2 < (d : ℝ))
    (A : NormalizedEllipticCoeff d (Metric.ball (0 : E) 1))
    {u : E → ℝ} {q : ℝ} {m : ℕ}
    (hq : 0 < q) (hq1 : q < 1)
    (hu_pos : ∀ x ∈ Metric.ball (0 : E) 1, 0 < u x)
    (hsuper : IsSupersolution A.1 u) :
    let p₀ := q * (moserChi d)⁻¹ ^ m
    ∀ (_hpInt :
        IntegrableOn (fun x => |u x| ^ p₀)
          (Metric.ball (0 : E) 1) volume),
    ∀ n : ℕ, n ≤ m + 1 →
      IntegrableOn (fun x => |u x| ^ moserExponentSeq d p₀ n)
          (Metric.ball (0 : E) (moserRadius n)) volume ∧
        superIterNormFwd (d := d) (u := u) p₀ n ≤
          (∏ i ∈ Finset.range n, superStepConstFwd (d := d) A p₀ i) *
            superIterNormFwd (d := d) (u := u) p₀ 0 := by
  intro p₀ hpInt n hn
  -- p₀ = q · χ⁻ᵐ > 0
  have hp₀ : 0 < p₀ := mul_pos hq (pow_pos (inv_pos.mpr (moserChi_pos hd)) m)
  -- Key: moserExponentSeq d p₀ n = q · χ^{n-m}, so for n ≤ m, p_n ≤ q < 1
  induction n with
  | zero =>
    constructor
    · rwa [moserExponentSeq_zero, moserRadius_zero]
    · simp
  | succ n ihn =>
    have hn' : n ≤ m + 1 := Nat.le_of_succ_le hn
    obtain ⟨hInt_n, hbound_n⟩ := ihn hn'
    let p_n := moserExponentSeq d p₀ n
    have hp_n : 0 < p_n := moserExponentSeq_pos hd hp₀ n
    -- Need p_n < 1 for supersolution_preMoser_forward
    -- p_n = p₀ · χⁿ = q · χ^{n-m}. For n ≤ m: p_n ≤ q < 1.
    have hp_n_lt_one : p_n < 1 := by
      -- p_n = q * χ⁻ᵐ * χⁿ = q * χ^{n-m} ≤ q * χ⁰ = q < 1 when n ≤ m
      dsimp [p_n, p₀]
      rw [moserExponentSeq, show q * (moserChi d)⁻¹ ^ m * moserChi d ^ n =
        q * ((moserChi d)⁻¹ ^ m * moserChi d ^ n) from by ring]
      have hchi_pos := moserChi_pos hd
      have : n ≤ m := Nat.lt_succ_iff.mp (Nat.lt_of_lt_of_le (Nat.lt_succ_of_le (Nat.le_of_succ_le_succ hn)) le_rfl)
      have hprod_le : (moserChi d)⁻¹ ^ m * moserChi d ^ n ≤ 1 := by
        rw [inv_pow]
        have hchi_ge_one := (one_lt_moserChi hd).le
        have hchi_pow_pos : (0 : ℝ) < moserChi d ^ m := pow_pos (moserChi_pos hd) m
        rw [show (moserChi d ^ m)⁻¹ * moserChi d ^ n =
          moserChi d ^ n / moserChi d ^ m from by rw [div_eq_mul_inv, mul_comm]]
        rw [div_le_one hchi_pow_pos]
        exact pow_le_pow_right₀ hchi_ge_one this
      calc q * ((moserChi d)⁻¹ ^ m * moserChi d ^ n) ≤ q * 1 :=
            mul_le_mul_of_nonneg_left hprod_le hq.le
        _ = q := mul_one q
        _ < 1 := hq1
    have hpre :=
      supersolution_preMoser_forward hd A (p := p_n)
        (r := moserRadius (n + 1)) (s := moserRadius n)
        hp_n hp_n_lt_one (moserRadius_pos (n + 1)) (moserRadius_succ_lt n)
        (moserRadius_le_one n) hu_pos hsuper
        (by simpa [p_n] using hInt_n)
    obtain ⟨hInt_succ, hNorm_succ⟩ := hpre
    refine ⟨?_, ?_⟩
    · have heq : moserChi d * p_n = moserExponentSeq d p₀ (n + 1) := by
        rw [moserExponentSeq_succ]
      rwa [heq] at hInt_succ
    · have heq_norm : superIterNormFwd (d := d) (u := u) p₀ (n + 1) =
          (∫ x in Metric.ball (0 : E) (moserRadius (n + 1)),
            |u x| ^ (moserChi d * p_n) ∂volume) ^
              (1 / (moserChi d * p_n)) := by
        simp [superIterNormFwd, superIterIntegralFwd, p_n, moserExponentSeq_succ]
      have heq_step : superStepConstFwd (d := d) A p₀ n =
          ((C_MoserAnchor d / (moserRadius n - moserRadius (n + 1)) ^ 2) *
            (A.1.Λ * (p_n / (1 - p_n)) ^ 2 + 1)) ^ (1 / p_n) := by
        simp [superStepConstFwd, p_n]
      have hstep_nonneg : 0 ≤ superStepConstFwd (d := d) A p₀ n := by
        rw [heq_step]
        apply Real.rpow_nonneg
        apply mul_nonneg
        · exact div_nonneg
            (le_trans (by norm_num : (0 : ℝ) ≤ 1) (one_le_C_MoserAnchor (d := d)))
            (sq_nonneg _)
        · nlinarith [A.1.Λ_nonneg, sq_nonneg (p_n / (1 - p_n))]
      have hstep_bound :
          superIterNormFwd (d := d) (u := u) p₀ (n + 1) ≤
            superStepConstFwd (d := d) A p₀ n *
              superIterNormFwd (d := d) (u := u) p₀ n := by
        rw [heq_norm, heq_step]
        convert hNorm_succ using 2
      calc superIterNormFwd (d := d) (u := u) p₀ (n + 1)
          ≤ superStepConstFwd (d := d) A p₀ n *
              superIterNormFwd (d := d) (u := u) p₀ n := hstep_bound
        _ ≤ superStepConstFwd (d := d) A p₀ n *
              ((∏ i ∈ Finset.range n, superStepConstFwd (d := d) A p₀ i) *
                superIterNormFwd (d := d) (u := u) p₀ 0) := by
            exact mul_le_mul_of_nonneg_left hbound_n hstep_nonneg
        _ = (∏ i ∈ Finset.range (n + 1), superStepConstFwd (d := d) A p₀ i) *
              superIterNormFwd (d := d) (u := u) p₀ 0 := by
            rw [Finset.prod_range_succ]
            ring

/-- Each forward low-power step constant is bounded by a simpler expression.

The denominator `1 - pₙ` is controlled from below by `1 - q`, because along the
finite forward iteration we only use stages `n ≤ m` and then `pₙ ≤ q < 1`. -/
theorem superStepConstFwd_le
    (hd : 2 < (d : ℝ))
    (A : NormalizedEllipticCoeff d (Metric.ball (0 : E) 1))
    {q : ℝ} {m i : ℕ}
    (hq : 0 < q) (hq1 : q < 1)
    (hi : i ∈ Finset.range (m + 1)) :
    let p₀ := q * (moserChi d)⁻¹ ^ m
    superStepConstFwd (d := d) A p₀ i ≤
      (16 * C_MoserAnchor d * (A.1.Λ * p₀ ^ 2 / (1 - q) ^ 2 + 1) *
        (4 * moserChi d ^ 2) ^ i) ^
        (1 / moserExponentSeq d p₀ i) := by
  intro p₀
  have hp₀ : 0 < p₀ := by
    dsimp [p₀]
    exact mul_pos hq (pow_pos (inv_pos.mpr (moserChi_pos (d := d) hd)) m)
  have hi_le : i ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  unfold superStepConstFwd
  apply Real.rpow_le_rpow
  · apply mul_nonneg
    · exact div_nonneg
        (le_trans (by norm_num : (0 : ℝ) ≤ 1) (one_le_C_MoserAnchor (d := d)))
        (sq_nonneg _)
    · nlinarith [A.1.Λ_nonneg, sq_nonneg (moserExponentSeq d p₀ i / (1 - moserExponentSeq d p₀ i))]
  · have hp_i : 0 < moserExponentSeq d p₀ i := moserExponentSeq_pos (d := d) hd hp₀ i
    have hp_i_le_q : moserExponentSeq d p₀ i ≤ q := by
      dsimp [p₀]
      rw [moserExponentSeq, show q * (moserChi d)⁻¹ ^ m * moserChi d ^ i =
        q * ((moserChi d)⁻¹ ^ m * moserChi d ^ i) from by ring]
      have hprod_le : (moserChi d)⁻¹ ^ m * moserChi d ^ i ≤ 1 := by
        rw [inv_pow]
        have hchi_ge_one := (one_lt_moserChi (d := d) hd).le
        have hchi_pow_pos : (0 : ℝ) < moserChi d ^ m := pow_pos (moserChi_pos (d := d) hd) m
        rw [show (moserChi d ^ m)⁻¹ * moserChi d ^ i =
          moserChi d ^ i / moserChi d ^ m from by rw [div_eq_mul_inv, mul_comm]]
        rw [div_le_one hchi_pow_pos]
        exact pow_le_pow_right₀ hchi_ge_one hi_le
      calc q * ((moserChi d)⁻¹ ^ m * moserChi d ^ i) ≤ q * 1 :=
            mul_le_mul_of_nonneg_left hprod_le hq.le
        _ = q := mul_one q
    have hp_i_lt_one : moserExponentSeq d p₀ i < 1 := lt_of_le_of_lt hp_i_le_q hq1
    have hgap_eq : C_MoserAnchor d / (moserRadius i - moserRadius (i + 1)) ^ 2 =
        C_MoserAnchor d * (4 : ℝ) ^ (i + 2) := by
      rw [moserRadius_gap]
      have hsq : (((1 / 2 : ℝ) ^ (i + 2)) ^ 2) = (1 / 4 : ℝ) ^ (i + 2) := by
        rw [← pow_mul, show (i + 2) * 2 = 2 * (i + 2) by ring, pow_mul]; norm_num
      rw [hsq, div_eq_mul_inv,
        show (((1 / 4 : ℝ) ^ (i + 2))⁻¹) = (4 : ℝ) ^ (i + 2) by
          rw [show (1 / 4 : ℝ) = (4 : ℝ)⁻¹ by norm_num, inv_pow]; norm_num]
    have hpow4 : (4 : ℝ) ^ (i + 2) = 16 * 4 ^ i := by
      rw [pow_add]
      ring
    have hratio_le :
        (moserExponentSeq d p₀ i / (1 - moserExponentSeq d p₀ i)) ^ 2 ≤
          (moserExponentSeq d p₀ i / (1 - q)) ^ 2 := by
      have hratio :
          moserExponentSeq d p₀ i / (1 - moserExponentSeq d p₀ i) ≤
            moserExponentSeq d p₀ i / (1 - q) := by
        have hden_pos : 0 < 1 - moserExponentSeq d p₀ i := by linarith
        have hqden_pos : 0 < 1 - q := by linarith
        field_simp [hden_pos.ne', hqden_pos.ne']
        nlinarith [hp_i_le_q]
      have hratio_nonneg : 0 ≤ moserExponentSeq d p₀ i / (1 - moserExponentSeq d p₀ i) :=
        div_nonneg hp_i.le (by linarith)
      have hratio_rhs_nonneg : 0 ≤ moserExponentSeq d p₀ i / (1 - q) :=
        div_nonneg hp_i.le (by linarith)
      nlinarith [sq_nonneg
        (moserExponentSeq d p₀ i / (1 - q) -
          moserExponentSeq d p₀ i / (1 - moserExponentSeq d p₀ i))]
    have hseq_sq : (moserExponentSeq d p₀ i) ^ 2 = p₀ ^ 2 * (moserChi d) ^ (2 * i) := by
      rw [moserExponentSeq]
      ring
    have hcoeff_le :
        A.1.Λ * (moserExponentSeq d p₀ i / (1 - moserExponentSeq d p₀ i)) ^ 2 + 1 ≤
          (A.1.Λ * p₀ ^ 2 / (1 - q) ^ 2 + 1) * (moserChi d ^ 2) ^ i := by
      have hchi_sq_ge_one : 1 ≤ (moserChi d ^ 2) ^ i :=
        one_le_pow₀ (by nlinarith [one_lt_moserChi (d := d) hd])
      have hΛratio :
          A.1.Λ * (moserExponentSeq d p₀ i / (1 - moserExponentSeq d p₀ i)) ^ 2 ≤
            A.1.Λ * (p₀ ^ 2 / (1 - q) ^ 2) * (moserChi d ^ 2) ^ i := by
        calc A.1.Λ * (moserExponentSeq d p₀ i / (1 - moserExponentSeq d p₀ i)) ^ 2
            ≤ A.1.Λ * (moserExponentSeq d p₀ i / (1 - q)) ^ 2 :=
              mul_le_mul_of_nonneg_left hratio_le A.1.Λ_nonneg
          _ = A.1.Λ * ((moserExponentSeq d p₀ i) ^ 2 / (1 - q) ^ 2) := by
                field_simp [show (1 - q : ℝ) ≠ 0 by linarith]
          _ = A.1.Λ * (p₀ ^ 2 * (moserChi d) ^ (2 * i) / (1 - q) ^ 2) := by rw [hseq_sq]
          _ = A.1.Λ * (p₀ ^ 2 / (1 - q) ^ 2) * (moserChi d ^ 2) ^ i := by
                rw [pow_mul]
                field_simp [show (1 - q : ℝ) ≠ 0 by linarith]
      calc
        A.1.Λ * (moserExponentSeq d p₀ i / (1 - moserExponentSeq d p₀ i)) ^ 2 + 1
            ≤ A.1.Λ * (p₀ ^ 2 / (1 - q) ^ 2) * (moserChi d ^ 2) ^ i +
                (moserChi d ^ 2) ^ i := by
                  nlinarith
        _ = (A.1.Λ * p₀ ^ 2 / (1 - q) ^ 2 + 1) * (moserChi d ^ 2) ^ i := by
              ring
    rw [hgap_eq, hpow4]
    calc C_MoserAnchor d * (16 * 4 ^ i) *
            (A.1.Λ * (moserExponentSeq d p₀ i / (1 - moserExponentSeq d p₀ i)) ^ 2 + 1)
        ≤ C_MoserAnchor d * (16 * 4 ^ i) *
            ((A.1.Λ * p₀ ^ 2 / (1 - q) ^ 2 + 1) * (moserChi d ^ 2) ^ i) := by
          gcongr
          exact mul_nonneg (le_trans (by norm_num : (0 : ℝ) ≤ 1) (one_le_C_MoserAnchor (d := d)))
            (by positivity)
      _ = 16 * C_MoserAnchor d * (A.1.Λ * p₀ ^ 2 / (1 - q) ^ 2 + 1) *
            (4 * moserChi d ^ 2) ^ i := by
          rw [show (4 * moserChi d ^ 2) ^ i = 4 ^ i * (moserChi d ^ 2) ^ i by rw [mul_pow]]
          ring
  · exact div_nonneg (by norm_num) (moserExponentSeq_pos (d := d) hd hp₀ i).le

/-- The finite product of step constants in the forward iteration is bounded.

The key bound is:
```
∏ᵢ₌₀ᵐ step_i ≤ (C_Moser d * (Λp₀²/(1-q)² + 1)^{d/2})^{1/p₀}
```
The crucial point: `1 - pₙ ≥ 1 - q > 0` for `n ≤ m` (since `pₘ = q`
is the largest exponent), so the `(1-p)` denominators stay bounded. -/
theorem supersolution_geometric_majorant_fwd
    (hd : 2 < (d : ℝ))
    (A : NormalizedEllipticCoeff d (Metric.ball (0 : E) 1))
    {q : ℝ} {m : ℕ}
    (hq : 0 < q) (hq1 : q < 1) :
    let p₀ := q * (moserChi d)⁻¹ ^ m
    ∏ i ∈ Finset.range (m + 1), superStepConstFwd (d := d) A p₀ i ≤
      (C_weakHarnack0 d * (A.1.Λ * p₀ ^ 2 / (1 - q) ^ 2 + 1) ^
        ((d : ℝ) / 2)) ^ (1 / p₀) := by
  intro p₀
  have hp₀ : 0 < p₀ := by
    dsimp [p₀]
    exact mul_pos hq (pow_pos (inv_pos.mpr (moserChi_pos (d := d) hd)) m)
  let ρ := moserDecayRatio d
  let K₀ : ℝ := 16 * C_MoserAnchor d
  let L : ℝ := A.1.Λ * p₀ ^ 2 / (1 - q) ^ 2 + 1
  let K : ℝ := K₀ * L
  let CC : ℝ := 4 * moserChi d ^ 2
  let S : ℝ := Finset.sum (Finset.range (m + 1)) (fun i => ρ ^ i)
  let T : ℝ := Finset.sum (Finset.range (m + 1)) (fun i => (i : ℝ) * ρ ^ i)
  have hρ_nonneg : 0 ≤ ρ := by
    simpa [ρ] using moserDecayRatio_nonneg (d := d) hd
  have hρ_lt_one : ρ < 1 := by
    simpa [ρ] using moserDecayRatio_lt_one (d := d) hd
  have hS_le : S ≤ (d : ℝ) / 2 := by
    simpa [ρ, S] using moserDecayRatio_sum_le_half_dim (d := d) hd (m + 1)
  have hT_le : T ≤ ∑' i : ℕ, (i : ℝ) * ρ ^ i := by
    simpa [ρ, T] using moserDecayRatio_weighted_sum_le_tsum (d := d) hd (m + 1)
  have hK₀_ge_one : 1 ≤ K₀ := by
    dsimp [K₀]
    nlinarith [one_le_C_MoserAnchor (d := d)]
  have hK₀_nonneg : 0 ≤ K₀ := by linarith
  have hL_ge_one : 1 ≤ L := by
    dsimp [L]
    have hterm_nonneg : 0 ≤ A.1.Λ * p₀ ^ 2 / (1 - q) ^ 2 := by
      exact div_nonneg (mul_nonneg A.1.Λ_nonneg (sq_nonneg p₀)) (sq_nonneg (1 - q))
    linarith
  have hL_nonneg : 0 ≤ L := by linarith
  have hK_pos : 0 < K := by
    dsimp [K]
    exact mul_pos (lt_of_lt_of_le zero_lt_one hK₀_ge_one) (by positivity)
  have hK_nonneg : 0 ≤ K := hK_pos.le
  have hCC_pos : 0 < CC := by
    dsimp [CC]
    exact mul_pos (by norm_num : (0 : ℝ) < 4) (sq_pos_of_pos (moserChi_pos (d := d) hd))
  have hCC_nonneg : 0 ≤ CC := hCC_pos.le
  have hstep_le : ∀ i, i ∈ Finset.range (m + 1) →
      superStepConstFwd (d := d) A p₀ i ≤ (K * CC ^ i) ^
        (1 / moserExponentSeq d p₀ i) := by
    intro i hi
    simpa [p₀, K, K₀, L, CC] using superStepConstFwd_le (d := d) hd A hq hq1 hi
  have hstep_nonneg : ∀ i, i ∈ Finset.range (m + 1) →
      0 ≤ superStepConstFwd (d := d) A p₀ i := by
    intro i _
    dsimp [superStepConstFwd]
    apply Real.rpow_nonneg
    apply mul_nonneg
    · exact div_nonneg (le_trans (by norm_num : (0 : ℝ) ≤ 1) (one_le_C_MoserAnchor (d := d)))
        (sq_nonneg _)
    · nlinarith [A.1.Λ_nonneg, sq_nonneg (moserExponentSeq d p₀ i / (1 - moserExponentSeq d p₀ i))]
  have hprod_le :
      ∏ i ∈ Finset.range (m + 1), superStepConstFwd (d := d) A p₀ i ≤
        ∏ i ∈ Finset.range (m + 1), (K * CC ^ i) ^
          (1 / moserExponentSeq d p₀ i) :=
    Finset.prod_le_prod hstep_nonneg hstep_le
  have hprod_eval :
      ∀ n : ℕ,
        ∏ i ∈ Finset.range n, (K * CC ^ i) ^
            (1 / moserExponentSeq d p₀ i) =
          (K ^ (Finset.sum (Finset.range n) (fun i => ρ ^ i)) *
            CC ^ (Finset.sum (Finset.range n) (fun i => (i : ℝ) * ρ ^ i))) ^
            (1 / p₀) := by
    intro n
    induction n with
    | zero =>
        simp
    | succ n ihn =>
        let Sₙ : ℝ := Finset.sum (Finset.range n) (fun i => ρ ^ i)
        let Tₙ : ℝ := Finset.sum (Finset.range n) (fun i => (i : ℝ) * ρ ^ i)
        have hinv :
            1 / moserExponentSeq d p₀ n = ρ ^ n / p₀ := by
          simpa [ρ] using inv_moserExponentSeq (d := d) hd hp₀ n
        have hdiv_eq :
            1 / moserExponentSeq d p₀ n = ρ ^ n * (1 / p₀) := by
          rw [hinv]
          ring
        rw [Finset.prod_range_succ, ihn, hdiv_eq]
        have hKC_nonneg : 0 ≤ K * CC ^ n := by
          exact mul_nonneg hK_nonneg (pow_nonneg hCC_nonneg n)
        rw [Real.rpow_mul hKC_nonneg]
        rw [Real.mul_rpow hK_nonneg (pow_nonneg hCC_nonneg n)]
        have hCC_pow :
            ((CC ^ n : ℝ)) ^ (ρ ^ n) = CC ^ ((n : ℝ) * ρ ^ n) := by
          rw [show ((CC ^ n : ℝ)) = CC ^ (n : ℝ) by rw [Real.rpow_natCast]]
          rw [← Real.rpow_mul hCC_nonneg]
        rw [hCC_pow]
        have hfront_nonneg :
            0 ≤ K ^ (ρ ^ n) * CC ^ ((n : ℝ) * ρ ^ n) := by
          exact mul_nonneg (Real.rpow_nonneg hK_nonneg _) (Real.rpow_nonneg hCC_nonneg _)
        have hback_nonneg :
            0 ≤ K ^ Sₙ * CC ^ Tₙ := by
          exact mul_nonneg (Real.rpow_nonneg hK_nonneg _) (Real.rpow_nonneg hCC_nonneg _)
        rw [mul_comm, ← Real.mul_rpow hfront_nonneg hback_nonneg]
        congr 1
        calc
          (K ^ (ρ ^ n) * CC ^ ((n : ℝ) * ρ ^ n)) * (K ^ Sₙ * CC ^ Tₙ)
              = (K ^ (ρ ^ n) * K ^ Sₙ) * (CC ^ ((n : ℝ) * ρ ^ n) * CC ^ Tₙ) := by
                  ring
          _ = K ^ (ρ ^ n + Sₙ) * CC ^ (((n : ℝ) * ρ ^ n) + Tₙ) := by
                rw [← Real.rpow_add hK_pos, ← Real.rpow_add hCC_pos]
          _ =
              K ^ (Finset.sum (Finset.range (n + 1)) (fun i => ρ ^ i)) *
                CC ^ (Finset.sum (Finset.range (n + 1))
                  (fun i => (i : ℝ) * ρ ^ i)) := by
                simp [Sₙ, Tₙ, Finset.sum_range_succ, add_comm]
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
      (4 : ℝ) ^ T ≤ 4 ^ (∑' i : ℕ, (i : ℝ) * ρ ^ i) := by
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 4) hT_le
  have hchi_sq_ge_one : 1 ≤ moserChi d ^ 2 := by
    exact one_le_pow₀ (one_le_moserChi (d := d) hd)
  have hchi_le :
      (moserChi d ^ 2) ^ T ≤ (moserChi d ^ 2) ^ (∑' i : ℕ, (i : ℝ) * ρ ^ i) := by
    exact Real.rpow_le_rpow_of_exponent_le hchi_sq_ge_one hT_le
  have hCC_le :
      CC ^ T ≤
        4 ^ (∑' i : ℕ, (i : ℝ) * ρ ^ i) *
          (moserChi d ^ 2) ^ (∑' i : ℕ, (i : ℝ) * ρ ^ i) := by
    calc
      CC ^ T = (4 : ℝ) ^ T * (moserChi d ^ 2) ^ T := by
        rw [show CC = 4 * (moserChi d ^ 2) by simp [CC]]
        rw [Real.mul_rpow (by positivity) (sq_nonneg _)]
      _ ≤ 4 ^ (∑' i : ℕ, (i : ℝ) * ρ ^ i) *
            (moserChi d ^ 2) ^ (∑' i : ℕ, (i : ℝ) * ρ ^ i) := by
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
      K₀ ^ ((d : ℝ) / 2) * 4 ^ (∑' i : ℕ, (i : ℝ) * ρ ^ i) ≤ C_Moser d := by
    have hbase :
        K₀ ^ ((d : ℝ) / 2) * 4 ^ (∑' i : ℕ, (i : ℝ) * ρ ^ i) ≤
          ((32 : ℝ) * C_MoserAnchor d) ^ ((d : ℝ) / 2) *
            4 ^ (∑' i : ℕ, (i : ℝ) * ρ ^ i) := by
      exact mul_le_mul_of_nonneg_right hK₀_pow_le_big
        (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 4) _)
    have hmax :
        ((32 : ℝ) * C_MoserAnchor d) ^ ((d : ℝ) / 2) *
            4 ^ (∑' i : ℕ, (i : ℝ) * ρ ^ i) ≤
          C_Moser d := by
      dsimp [C_Moser, ρ]
      split_ifs with hlt
      · exact
          le_max_right (C_MoserAnchor d)
            (((32 : ℝ) * C_MoserAnchor d) ^ ((d : ℝ) / 2) *
              4 ^ (∑' i : ℕ, (i : ℝ) * moserDecayRatio d ^ i))
      · exact False.elim (hlt hd)
    exact hbase.trans hmax
  have hCweak_eq :
      C_Moser d * (moserChi d ^ 2) ^ (∑' i : ℕ, (i : ℝ) * ρ ^ i) =
        C_weakHarnack0 d := by
    simp [C_weakHarnack0, hd, ρ]
  have hbody_le :
      K ^ S * CC ^ T ≤
        C_weakHarnack0 d * L ^ ((d : ℝ) / 2) := by
    have hK_target_nonneg :
        0 ≤ K₀ ^ ((d : ℝ) / 2) * L ^ ((d : ℝ) / 2) := by
      exact mul_nonneg (Real.rpow_nonneg hK₀_nonneg _) (Real.rpow_nonneg hL_nonneg _)
    calc
      K ^ S * CC ^ T
          ≤ (K₀ ^ ((d : ℝ) / 2) * L ^ ((d : ℝ) / 2)) *
              (4 ^ (∑' i : ℕ, (i : ℝ) * ρ ^ i) *
                (moserChi d ^ 2) ^ (∑' i : ℕ, (i : ℝ) * ρ ^ i)) := by
            exact mul_le_mul hK_le hCC_le
              (Real.rpow_nonneg hCC_nonneg _)
              hK_target_nonneg
      _ = (K₀ ^ ((d : ℝ) / 2) * 4 ^ (∑' i : ℕ, (i : ℝ) * ρ ^ i)) *
            ((moserChi d ^ 2) ^ (∑' i : ℕ, (i : ℝ) * ρ ^ i) * L ^ ((d : ℝ) / 2)) := by
              ring
      _ ≤ C_Moser d *
            ((moserChi d ^ 2) ^ (∑' i : ℕ, (i : ℝ) * ρ ^ i) * L ^ ((d : ℝ) / 2)) := by
              exact mul_le_mul_of_nonneg_right hCMoser_le
                (mul_nonneg (Real.rpow_nonneg (sq_nonneg _) _) (Real.rpow_nonneg hL_nonneg _))
      _ = C_weakHarnack0 d * L ^ ((d : ℝ) / 2) := by
            rw [← hCweak_eq]
            ring
  calc
    ∏ i ∈ Finset.range (m + 1), superStepConstFwd (d := d) A p₀ i
        ≤ ∏ i ∈ Finset.range (m + 1), (K * CC ^ i) ^ (1 / moserExponentSeq d p₀ i) := hprod_le
    _ = (K ^ S * CC ^ T) ^ (1 / p₀) := by
          simpa [ρ, S, T] using hprod_eval (m + 1)
    _ ≤ (C_weakHarnack0 d * L ^ ((d : ℝ) / 2)) ^ (1 / p₀) := by
          exact Real.rpow_le_rpow
            (mul_nonneg (Real.rpow_nonneg hK_nonneg _) (Real.rpow_nonneg hCC_nonneg _))
            hbody_le (by positivity)
    _ = (C_weakHarnack0 d * (A.1.Λ * p₀ ^ 2 / (1 - q) ^ 2 + 1) ^ ((d : ℝ) / 2)) ^ (1 / p₀) := by
          simp [L]



end DeGiorgi
