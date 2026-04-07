import DeGiorgi.MoserIteration.CutoffPrep.PreEstimate
import Mathlib.Topology.MetricSpace.Thickening

/-!
# Moser Iteration Layer

This module contains the explicit majorant iteration, geometric-product bounds,
and stage-one constants used in the Chapter 06 Moser argument.
-/

noncomputable section

open MeasureTheory Filter

namespace DeGiorgi

variable {d : ℕ} [NeZero d]

local notation "E" => AmbientSpace d

/-- Dimension-only constant for the stage-one weak Harnack estimates.

Compared to `C_Moser`, this absorbs the extra `χ^(2i)` growth that appears in
the supersolution geometric product. -/
noncomputable def C_weakHarnack0 (d : ℕ) [NeZero d] : ℝ :=
  if _hd : 2 < (d : ℝ) then
    C_Moser d * (moserChi d ^ 2) ^ (∑' n : ℕ, (n : ℝ) * moserDecayRatio d ^ n)
  else
    C_Moser d

theorem C_Moser_le_C_weakHarnack0 :
    C_Moser d ≤ C_weakHarnack0 d := by
  by_cases hd : 2 < (d : ℝ)
  · simp [C_weakHarnack0, hd]
    have hq_nonneg : 0 ≤ moserDecayRatio d :=
      moserDecayRatio_nonneg (d := d) hd
    have hq_lt_one : moserDecayRatio d < 1 :=
      moserDecayRatio_lt_one (d := d) hd
    have hq_norm_lt_one : ‖moserDecayRatio d‖ < 1 := by
      simpa [Real.norm_of_nonneg hq_nonneg] using hq_lt_one
    have hexp_nonneg :
        0 ≤ ∑' n : ℕ, (n : ℝ) * moserDecayRatio d ^ n := by
      exact tsum_nonneg fun n => mul_nonneg (by exact_mod_cast Nat.zero_le n) (pow_nonneg hq_nonneg n)
    have hbase_ge_one : 1 ≤ moserChi d ^ 2 := by
      exact one_le_pow₀ (one_le_moserChi (d := d) hd)
    have hfactor_ge_one :
        1 ≤ (moserChi d ^ 2) ^ (∑' n : ℕ, (n : ℝ) * moserDecayRatio d ^ n) := by
      exact Real.one_le_rpow hbase_ge_one hexp_nonneg
    have hCMoser_nonneg : 0 ≤ C_Moser d := by
      exact le_trans (by norm_num : (0 : ℝ) ≤ 1) (one_le_C_Moser (d := d))
    calc
      C_Moser d = C_Moser d * 1 := by ring
      _ ≤ C_Moser d * (moserChi d ^ 2) ^ (∑' n : ℕ, (n : ℝ) * moserDecayRatio d ^ n) := by
          exact mul_le_mul_of_nonneg_left hfactor_ge_one hCMoser_nonneg
  · simp [C_weakHarnack0, hd]

theorem one_le_C_weakHarnack0 :
    1 ≤ C_weakHarnack0 d := by
  exact (one_le_C_Moser (d := d)).trans (C_Moser_le_C_weakHarnack0 (d := d))

/-- Auxiliary exponent `c(d)` used in the crossover estimate. -/
noncomputable def c_crossover (d : ℕ) [NeZero d] : ℝ :=
  1 / (C_Moser d + 1)

/-- Auxiliary constant `C(d)` used in the crossover estimate. -/
noncomputable def C_crossover (d : ℕ) [NeZero d] : ℝ :=
  C_Moser d


/-- Auxiliary powered integral along the standard Moser radius/exponent sequence. -/
noncomputable def moserIterIntegral
    {u : E → ℝ} (p₀ : ℝ) (n : ℕ) : ℝ :=
  ∫ x in Metric.ball (0 : E) (moserRadius n), |max (u x) 0| ^ moserExponentSeq d p₀ n ∂volume

/-- Auxiliary `L^{p_n}` quantity in the Moser iteration. -/
noncomputable def moserIterNorm
    {u : E → ℝ} (p₀ : ℝ) (n : ℕ) : ℝ :=
  (moserIterIntegral (d := d) (u := u) p₀ n) ^ (1 / moserExponentSeq d p₀ n)

/-- Auxiliary base integral on the unit ball used in the explicit Moser majorants. -/
noncomputable def moserBaseIntegral
    {u : E → ℝ} (p₀ : ℝ) : ℝ :=
  ∫ x in Metric.ball (0 : E) 1, |max (u x) 0| ^ p₀ ∂volume

/-- Auxiliary step constant in the normalized-coefficient pre-Moser estimate. -/
noncomputable def moserStepConst
    (A : NormalizedEllipticCoeff d (Metric.ball (0 : E) 1)) (p₀ : ℝ) : ℝ :=
  (32 : ℝ) * C_MoserAnchor d * A.1.Λ * (p₀ / (p₀ - 1)) ^ 2

/-- Auxiliary product majorant produced by iterating the pre-Moser estimate. -/
noncomputable def moserIterMajorant
    (A : NormalizedEllipticCoeff d (Metric.ball (0 : E) 1))
    {u : E → ℝ} (p₀ : ℝ) (n : ℕ) : ℝ :=
  ((moserStepConst (d := d) A p₀) ^
        (Finset.sum (Finset.range n) (fun i => moserDecayRatio d ^ i)) *
      4 ^ (Finset.sum (Finset.range n) (fun i => (i : ℝ) * moserDecayRatio d ^ i)) *
      ∫ x in Metric.ball (0 : E) 1, |max (u x) 0| ^ p₀ ∂volume) ^
    (1 / p₀)

/-- Auxiliary target constant for the Moser local-max theorem. -/
noncomputable def moserLinftyBoundPow
    (A : NormalizedEllipticCoeff d (Metric.ball (0 : E) 1))
    {u : E → ℝ} (p₀ : ℝ) : ℝ :=
  C_Moser d * A.1.Λ ^ ((d : ℝ) / 2) *
    (p₀ / (p₀ - 1)) ^ (d : ℝ) *
    ∫ x in Metric.ball (0 : E) 1, |max (u x) 0| ^ p₀ ∂volume

/-- Auxiliary root majorant corresponding to `moserLinftyBoundPow`. -/
noncomputable def moserLinftyMajorant
    (A : NormalizedEllipticCoeff d (Metric.ball (0 : E) 1))
    {u : E → ℝ} (p₀ : ℝ) : ℝ :=
  (moserLinftyBoundPow (d := d) A (u := u) p₀) ^ (1 / p₀)

theorem moser_step_majorant_le
    (hd : 2 < (d : ℝ))
    (A : NormalizedEllipticCoeff d (Metric.ball (0 : E) 1))
    {u : E → ℝ} {p₀ : ℝ} (hp₀ : 1 < p₀) (n : ℕ) :
    (((C_MoserAnchor d / (moserRadius n - moserRadius (n + 1)) ^ 2) *
        (A.1.Λ *
            (moserExponentSeq d p₀ n / (moserExponentSeq d p₀ n - 1)) ^ 2 + 1)) ^
        (1 / moserExponentSeq d p₀ n)) *
      moserIterMajorant (d := d) A (u := u) p₀ n ≤
      moserIterMajorant (d := d) A (u := u) p₀ (n + 1) := by
  let p_n : ℝ := moserExponentSeq d p₀ n
  have hp₀_pos : 0 < p₀ := by linarith
  have hp_n_gt_one : 1 < p_n := by
    simpa [p_n] using one_lt_moserExponentSeq (d := d) hd hp₀ n
  have hp_n_pos : 0 < p_n := by linarith
  have hp₀_nonneg : 0 ≤ p₀ := by linarith
  have hp_n_ge : p₀ ≤ p_n := by
    simpa [p_n] using moserExponentSeq_ge_initial (d := d) hd hp₀_nonneg n
  have hp₀m1_pos : 0 < p₀ - 1 := by linarith
  have hp_nm1_pos : 0 < p_n - 1 := by linarith
  have hratio_le : p_n / (p_n - 1) ≤ p₀ / (p₀ - 1) := by
    field_simp [hp_nm1_pos.ne', hp₀m1_pos.ne']
    nlinarith
  have hratio_nonneg : 0 ≤ p_n / (p_n - 1) := by positivity
  have hratio₀_nonneg : 0 ≤ p₀ / (p₀ - 1) := by positivity
  have hratio_sq_le :
      (p_n / (p_n - 1)) ^ 2 ≤ (p₀ / (p₀ - 1)) ^ 2 := by
    nlinarith
  have hΛ_ge_one : 1 ≤ A.1.Λ := by
    simpa [A.2] using A.1.hΛ
  have hratio₀_gt_one : 1 < p₀ / (p₀ - 1) := by
    exact (one_lt_div hp₀m1_pos).2 (by nlinarith)
  have hratio₀_sq_ge_one : 1 ≤ (p₀ / (p₀ - 1)) ^ 2 := by
    nlinarith
  have hΛratio_ge_one : 1 ≤ A.1.Λ * (p₀ / (p₀ - 1)) ^ 2 := by
    nlinarith
  have hbracket_le :
      A.1.Λ * (p_n / (p_n - 1)) ^ 2 + 1 ≤
        2 * A.1.Λ * (p₀ / (p₀ - 1)) ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hratio_sq_le A.1.Λ_nonneg]
  have hgap_eq :
      C_MoserAnchor d / (moserRadius n - moserRadius (n + 1)) ^ 2 =
        C_MoserAnchor d * (4 : ℝ) ^ (n + 2) := by
    rw [moserRadius_gap]
    have hsq : (((1 / 2 : ℝ) ^ (n + 2)) ^ 2) = (1 / 4 : ℝ) ^ (n + 2) := by
      rw [← pow_mul]
      rw [show (n + 2) * 2 = 2 * (n + 2) by ring]
      rw [pow_mul]
      norm_num
    rw [hsq, div_eq_mul_inv]
    rw [show (((1 / 4 : ℝ) ^ (n + 2))⁻¹) = (4 : ℝ) ^ (n + 2) by
      rw [show (1 / 4 : ℝ) = (4 : ℝ)⁻¹ by norm_num, inv_pow]
      norm_num]
  have hpow4 : (4 : ℝ) ^ (n + 2) = (4 : ℝ) ^ n * 16 := by
    rw [pow_add]
    norm_num
  have harg_nonneg :
      0 ≤
        (C_MoserAnchor d / (moserRadius n - moserRadius (n + 1)) ^ 2) *
          (A.1.Λ * (p_n / (p_n - 1)) ^ 2 + 1) := by
    have hanchor_nonneg : 0 ≤ C_MoserAnchor d := by
      exact le_trans (by norm_num : (0 : ℝ) ≤ 1) (one_le_C_MoserAnchor (d := d))
    refine mul_nonneg ?_ ?_
    · exact div_nonneg hanchor_nonneg (sq_nonneg _)
    · nlinarith [A.1.Λ_nonneg, sq_nonneg (p_n / (p_n - 1))]
  have hgap_nonneg : 0 ≤ C_MoserAnchor d * (4 : ℝ) ^ (n + 2) := by
    have hanchor_nonneg : 0 ≤ C_MoserAnchor d := by
      exact le_trans (by norm_num : (0 : ℝ) ≤ 1) (one_le_C_MoserAnchor (d := d))
    exact mul_nonneg hanchor_nonneg (by positivity)
  have harg_le :
      (C_MoserAnchor d / (moserRadius n - moserRadius (n + 1)) ^ 2) *
          (A.1.Λ * (p_n / (p_n - 1)) ^ 2 + 1) ≤
        moserStepConst (d := d) A p₀ * (4 : ℝ) ^ n := by
    rw [hgap_eq]
    calc
      C_MoserAnchor d * (4 : ℝ) ^ (n + 2) *
          (A.1.Λ * (p_n / (p_n - 1)) ^ 2 + 1)
          ≤ C_MoserAnchor d * (4 : ℝ) ^ (n + 2) *
              (2 * A.1.Λ * (p₀ / (p₀ - 1)) ^ 2) := by
              gcongr
      _ = moserStepConst (d := d) A p₀ * (4 : ℝ) ^ n := by
            rw [hpow4]
            dsimp [moserStepConst]
            ring
  have hprefactor_le :
      ((C_MoserAnchor d / (moserRadius n - moserRadius (n + 1)) ^ 2) *
          (A.1.Λ * (p_n / (p_n - 1)) ^ 2 + 1)) ^ (1 / p_n) ≤
        (moserStepConst (d := d) A p₀ * (4 : ℝ) ^ n) ^ (1 / p_n) := by
    refine Real.rpow_le_rpow harg_nonneg harg_le ?_
    · positivity
  have hprefactor_nonneg :
      0 ≤
        ((C_MoserAnchor d / (moserRadius n - moserRadius (n + 1)) ^ 2) *
          (A.1.Λ * (p_n / (p_n - 1)) ^ 2 + 1)) ^ (1 / p_n) := by
    exact Real.rpow_nonneg harg_nonneg _
  have hstep_pos : 0 < moserStepConst (d := d) A p₀ := by
    have hanchor_pos : 0 < C_MoserAnchor d := by
      exact lt_of_lt_of_le zero_lt_one (one_le_C_MoserAnchor (d := d))
    have hratio₀_pos : 0 < p₀ / (p₀ - 1) := by positivity
    dsimp [moserStepConst]
    positivity
  have hstep_nonneg : 0 ≤ moserStepConst (d := d) A p₀ := hstep_pos.le
  have hq_nonneg : 0 ≤ moserDecayRatio d ^ n := by
    exact pow_nonneg (moserDecayRatio_nonneg (d := d) hd) n
  let S : ℝ := Finset.sum (Finset.range n) (fun i => moserDecayRatio d ^ i)
  let T : ℝ := Finset.sum (Finset.range n) (fun i => (i : ℝ) * moserDecayRatio d ^ i)
  let I : ℝ := (∫ x in Metric.ball (0 : E) 1, |max (u x) 0| ^ p₀ ∂volume)
  have hinner_nonneg :
      0 ≤
        moserStepConst (d := d) A p₀ ^ S * 4 ^ T * I := by
    refine mul_nonneg ?_ ?_
    · refine mul_nonneg ?_ ?_
      · exact Real.rpow_nonneg hstep_nonneg _
      · positivity
    · dsimp [I]
      refine integral_nonneg ?_
      intro x
      positivity
  have hstep_eq :
      ((moserStepConst (d := d) A p₀ * (4 : ℝ) ^ n) ^ (1 / p_n)) *
          moserIterMajorant (d := d) A (u := u) p₀ n =
        moserIterMajorant (d := d) A (u := u) p₀ (n + 1) := by
    rw [moserIterMajorant, moserIterMajorant, Finset.sum_range_succ, Finset.sum_range_succ]
    have hinv : 1 / p_n = moserDecayRatio d ^ n / p₀ := by
      simpa [p_n] using inv_moserExponentSeq (d := d) hd hp₀_pos n
    have hdiv_eq : 1 / p_n = moserDecayRatio d ^ n * (1 / p₀) := by
      rw [hinv]
      ring
    rw [hdiv_eq]
    have hstep4_nonneg : 0 ≤ moserStepConst (d := d) A p₀ * (4 : ℝ) ^ n := by
      exact mul_nonneg hstep_nonneg (by positivity)
    rw [Real.rpow_mul hstep4_nonneg]
    rw [Real.mul_rpow hstep_nonneg (by positivity : 0 ≤ (4 : ℝ) ^ n)]
    have hfour_pow :
        ((4 : ℝ) ^ n) ^ (moserDecayRatio d ^ n) =
          (4 : ℝ) ^ ((n : ℝ) * moserDecayRatio d ^ n) := by
      rw [show ((4 : ℝ) ^ n) = (4 : ℝ) ^ (n : ℝ) by rw [Real.rpow_natCast]]
      rw [← Real.rpow_mul (by positivity : (0 : ℝ) ≤ 4)]
    rw [hfour_pow]
    have hstepFactor_nonneg :
        0 ≤
          moserStepConst (d := d) A p₀ ^ (moserDecayRatio d ^ n) *
            4 ^ ((n : ℝ) * moserDecayRatio d ^ n) := by
      exact mul_nonneg (Real.rpow_nonneg hstep_nonneg _) (by positivity)
    rw [← Real.mul_rpow hstepFactor_nonneg hinner_nonneg]
    calc
      ((moserStepConst (d := d) A p₀ ^ (moserDecayRatio d ^ n) *
          4 ^ ((n : ℝ) * moserDecayRatio d ^ n)) *
        (moserStepConst (d := d) A p₀ ^ S * 4 ^ T * I)) ^ (1 / p₀)
          =
        (moserStepConst (d := d) A p₀ ^
            (moserDecayRatio d ^ n + S) *
          4 ^ (((n : ℝ) * moserDecayRatio d ^ n) + T) * I) ^ (1 / p₀) := by
            congr 1
            calc
              (moserStepConst (d := d) A p₀ ^ (moserDecayRatio d ^ n) *
                    4 ^ ((n : ℝ) * moserDecayRatio d ^ n)) *
                  (moserStepConst (d := d) A p₀ ^ S * 4 ^ T * I)
                  =
                (moserStepConst (d := d) A p₀ ^ (moserDecayRatio d ^ n) *
                    moserStepConst (d := d) A p₀ ^ S) *
                  ((4 ^ ((n : ℝ) * moserDecayRatio d ^ n) *
                      4 ^ T) * I) := by
                      ring
              _ =
                (moserStepConst (d := d) A p₀ ^ (moserDecayRatio d ^ n + S)) *
                  ((4 ^ (((n : ℝ) * moserDecayRatio d ^ n) + T)) * I) := by
                      rw [← Real.rpow_add hstep_pos, ← Real.rpow_add (by positivity : 0 < (4 : ℝ))]
              _ =
                moserStepConst (d := d) A p₀ ^ (moserDecayRatio d ^ n + S) *
                  4 ^ (((n : ℝ) * moserDecayRatio d ^ n) + T) * I := by
                    ring
      _ =
        ((moserStepConst (d := d) A p₀ ^
            (Finset.sum (Finset.range n) (fun i => moserDecayRatio d ^ i) +
              moserDecayRatio d ^ n) *
          4 ^ (Finset.sum (Finset.range n)
              (fun i => (i : ℝ) * moserDecayRatio d ^ i) +
                (n : ℝ) * moserDecayRatio d ^ n) * I) ^ (1 / p₀)) := by
            simp [S, T, add_comm]
  have hmajorant_nonneg :
      0 ≤ moserIterMajorant (d := d) A (u := u) p₀ n := by
    simpa [moserIterMajorant, S, T, I] using
      (Real.rpow_nonneg hinner_nonneg (1 / p₀))
  simpa [p_n] using
    (calc
    (((C_MoserAnchor d / (moserRadius n - moserRadius (n + 1)) ^ 2) *
        (A.1.Λ * (p_n / (p_n - 1)) ^ 2 + 1)) ^ (1 / p_n)) *
        moserIterMajorant (d := d) A (u := u) p₀ n
        ≤ ((moserStepConst (d := d) A p₀ * (4 : ℝ) ^ n) ^ (1 / p_n)) *
            moserIterMajorant (d := d) A (u := u) p₀ n := by
            exact mul_le_mul_of_nonneg_right hprefactor_le hmajorant_nonneg
    _ = moserIterMajorant (d := d) A (u := u) p₀ (n + 1) := hstep_eq
    )

theorem moser_iteration_bound
    (hd : 2 < (d : ℝ))
    (A : NormalizedEllipticCoeff d (Metric.ball (0 : E) 1))
    {u : E → ℝ} {p₀ : ℝ} (hp₀ : 1 < p₀)
    (hsub : IsSubsolution A.1 u)
    (hposInt :
      IntegrableOn (fun x => |max (u x) 0| ^ p₀)
        (Metric.ball (0 : E) 1) volume) :
    ∀ n,
      IntegrableOn (fun x => |max (u x) 0| ^ moserExponentSeq d p₀ n)
        (Metric.ball (0 : E) (moserRadius n)) volume ∧
      moserIterNorm (d := d) (u := u) p₀ n ≤
        moserIterMajorant (d := d) A (u := u) p₀ n := by
  intro n
  induction n with
  | zero =>
      constructor
      · simpa [moserExponentSeq_zero, moserRadius_zero] using hposInt
      · simp [moserIterNorm, moserIterIntegral, moserIterMajorant, moserExponentSeq_zero,
          moserRadius_zero]
  | succ n ihn =>
      rcases ihn with ⟨hInt_n, hbound_n⟩
      let p_n : ℝ := moserExponentSeq d p₀ n
      have hp_n : 1 < p_n := by
        simpa [p_n] using one_lt_moserExponentSeq (d := d) hd hp₀ n
      have hpre :=
        moser_preMoser (d := d) hd A (u := u) (p := p_n)
          (r := moserRadius (n + 1)) (s := moserRadius n)
          hp_n (moserRadius_pos (n + 1)) (moserRadius_succ_lt n)
          (moserRadius_le_one n) hsub (by simpa [p_n] using hInt_n)
      rcases hpre with ⟨hInt_succ, hbound_succ⟩
      refine ⟨?_, ?_⟩
      · simpa [p_n, moserExponentSeq_succ, moserIterIntegral, mul_comm, mul_left_comm,
          mul_assoc] using hInt_succ
      · have hfactor_nonneg :
            0 ≤
              ((C_MoserAnchor d / (moserRadius n - moserRadius (n + 1)) ^ 2) *
                  (A.1.Λ * (p_n / (p_n - 1)) ^ 2 + 1)) ^ (1 / p_n) := by
            have harg_nonneg :
                0 ≤
                  (C_MoserAnchor d / (moserRadius n - moserRadius (n + 1)) ^ 2) *
                    (A.1.Λ * (p_n / (p_n - 1)) ^ 2 + 1) := by
              have hanchor_nonneg : 0 ≤ C_MoserAnchor d := by
                exact le_trans (by norm_num : (0 : ℝ) ≤ 1) (one_le_C_MoserAnchor (d := d))
              refine mul_nonneg ?_ ?_
              · exact div_nonneg hanchor_nonneg (sq_nonneg _)
              · nlinarith [A.1.Λ_nonneg, sq_nonneg (p_n / (p_n - 1))]
            exact Real.rpow_nonneg harg_nonneg _
        calc
          moserIterNorm (d := d) (u := u) p₀ (n + 1)
              ≤ ((C_MoserAnchor d / (moserRadius n - moserRadius (n + 1)) ^ 2) *
                    (A.1.Λ * (p_n / (p_n - 1)) ^ 2 + 1)) ^ (1 / p_n) *
                  moserIterNorm (d := d) (u := u) p₀ n := by
                    simpa [moserIterNorm, moserIterIntegral, p_n, moserExponentSeq_succ,
                      mul_comm, mul_left_comm, mul_assoc] using hbound_succ
          _ ≤ ((C_MoserAnchor d / (moserRadius n - moserRadius (n + 1)) ^ 2) *
                    (A.1.Λ * (p_n / (p_n - 1)) ^ 2 + 1)) ^ (1 / p_n) *
                  moserIterMajorant (d := d) A (u := u) p₀ n := by
                    exact mul_le_mul_of_nonneg_left hbound_n hfactor_nonneg
          _ ≤ moserIterMajorant (d := d) A (u := u) p₀ (n + 1) := by
                    simpa [p_n] using
                      moser_step_majorant_le (d := d) hd A (u := u) hp₀ n

/-- Auxiliary geometric-product bound for the explicit Moser majorant. -/
theorem moserDecayRatio_sum_le_half_dim
    (hd : 2 < (d : ℝ)) (n : ℕ) :
    Finset.sum (Finset.range n) (fun i => moserDecayRatio d ^ i) ≤ (d : ℝ) / 2 := by
  have hq_nonneg : 0 ≤ moserDecayRatio d :=
    moserDecayRatio_nonneg (d := d) hd
  have hq_lt_one : moserDecayRatio d < 1 :=
    moserDecayRatio_lt_one (d := d) hd
  have hsumm : Summable (fun i : ℕ => moserDecayRatio d ^ i) :=
    summable_geometric_of_lt_one hq_nonneg hq_lt_one
  have hsum_le :
      Finset.sum (Finset.range n) (fun i => moserDecayRatio d ^ i) ≤
        ∑' i : ℕ, moserDecayRatio d ^ i := by
    exact hsumm.sum_le_tsum (s := Finset.range n) (by
      intro i hi
      exact pow_nonneg hq_nonneg i)
  refine hsum_le.trans_eq ?_
  rw [tsum_geometric_of_lt_one hq_nonneg hq_lt_one, moserDecayRatio]
  have hd_ne : (d : ℝ) ≠ 0 := by
    exact_mod_cast (NeZero.ne d)
  field_simp [hd_ne]
  ring

theorem moserDecayRatio_weighted_sum_le_tsum
    (hd : 2 < (d : ℝ)) (n : ℕ) :
    Finset.sum (Finset.range n) (fun i => (i : ℝ) * moserDecayRatio d ^ i) ≤
      ∑' i : ℕ, (i : ℝ) * moserDecayRatio d ^ i := by
  have hq_nonneg : 0 ≤ moserDecayRatio d :=
    moserDecayRatio_nonneg (d := d) hd
  have hq_lt_one : moserDecayRatio d < 1 :=
    moserDecayRatio_lt_one (d := d) hd
  have hq_norm_lt_one : ‖moserDecayRatio d‖ < 1 := by
    simpa [Real.norm_of_nonneg hq_nonneg] using hq_lt_one
  have hsumm :
      Summable (fun i : ℕ => (i : ℝ) * moserDecayRatio d ^ i) := by
    simpa [pow_one] using
      (summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 hq_norm_lt_one)
  exact hsumm.sum_le_tsum (s := Finset.range n) (by
    intro i hi
    positivity)

theorem moser_geometric_majorant
    (hd : 2 < (d : ℝ))
    (A : NormalizedEllipticCoeff d (Metric.ball (0 : E) 1))
    {u : E → ℝ} {p₀ : ℝ} (hp₀ : 1 < p₀) :
    ∀ n,
      moserIterMajorant (d := d) A (u := u) p₀ n ≤
        moserLinftyMajorant (d := d) A (u := u) p₀ := by
  intro n
  let q : ℝ := moserDecayRatio d
  let S : ℝ := Finset.sum (Finset.range n) (fun i => q ^ i)
  let T : ℝ := Finset.sum (Finset.range n) (fun i => (i : ℝ) * q ^ i)
  let I : ℝ := ∫ x in Metric.ball (0 : E) 1, |max (u x) 0| ^ p₀ ∂volume
  let B : ℝ := (32 : ℝ) * C_MoserAnchor d
  let r : ℝ := p₀ / (p₀ - 1)
  have hp₀_pos : 0 < p₀ := by
    linarith
  have hp₀m1_pos : 0 < p₀ - 1 := by
    linarith
  have hq_nonneg : 0 ≤ q := by
    simpa [q] using moserDecayRatio_nonneg (d := d) hd
  have hq_lt_one : q < 1 := by
    simpa [q] using moserDecayRatio_lt_one (d := d) hd
  have hS_le : S ≤ (d : ℝ) / 2 := by
    simpa [q, S] using moserDecayRatio_sum_le_half_dim (d := d) hd n
  have hT_le : T ≤ ∑' i : ℕ, (i : ℝ) * q ^ i := by
    simpa [q, T] using moserDecayRatio_weighted_sum_le_tsum (d := d) hd n
  have hS_nonneg : 0 ≤ S := by
    dsimp [S]
    refine Finset.sum_nonneg ?_
    intro i hi
    exact pow_nonneg hq_nonneg i
  have hT_nonneg : 0 ≤ T := by
    dsimp [T]
    refine Finset.sum_nonneg ?_
    intro i hi
    positivity
  have h2S_le : 2 * S ≤ (d : ℝ) := by
    linarith
  have hanchor_nonneg : 0 ≤ C_MoserAnchor d := by
    exact le_trans (by norm_num : (0 : ℝ) ≤ 1) (one_le_C_MoserAnchor (d := d))
  have hB_ge_one : 1 ≤ B := by
    dsimp [B]
    nlinarith [one_le_C_MoserAnchor (d := d)]
  have hB_nonneg : 0 ≤ B := by
    linarith
  have hΛ_ge_one : 1 ≤ A.1.Λ := by
    simpa [A.2] using A.1.hΛ
  have hr_gt_one : 1 < r := by
    dsimp [r]
    exact (one_lt_div hp₀m1_pos).2 (by linarith)
  have hr_ge_one : 1 ≤ r := hr_gt_one.le
  have hr_nonneg : 0 ≤ r := by
    linarith
  have hstep_nonneg : 0 ≤ moserStepConst (d := d) A p₀ := by
    dsimp [moserStepConst, r]
    refine mul_nonneg ?_ (by positivity)
    refine mul_nonneg ?_ A.1.Λ_nonneg
    exact mul_nonneg (by norm_num : (0 : ℝ) ≤ 32) hanchor_nonneg
  have hI_nonneg : 0 ≤ I := by
    dsimp [I]
    refine integral_nonneg ?_
    intro x
    positivity
  have hB_pow_le : B ^ S ≤ B ^ ((d : ℝ) / 2) := by
    exact Real.rpow_le_rpow_of_exponent_le hB_ge_one hS_le
  have hΛ_pow_le : A.1.Λ ^ S ≤ A.1.Λ ^ ((d : ℝ) / 2) := by
    exact Real.rpow_le_rpow_of_exponent_le hΛ_ge_one hS_le
  have hr_sq_pow_le : (r ^ (2 : ℝ)) ^ S ≤ r ^ (d : ℝ) := by
    have hpow_le : r ^ (2 * S) ≤ r ^ (d : ℝ) := by
      exact Real.rpow_le_rpow_of_exponent_le hr_ge_one h2S_le
    simpa [Real.rpow_mul hr_nonneg] using hpow_le
  have hstep_eq_base :
      moserStepConst (d := d) A p₀ = ((B * A.1.Λ) * r ^ (2 : ℝ)) := by
    calc
      moserStepConst (d := d) A p₀
          = (32 : ℝ) * C_MoserAnchor d * A.1.Λ * (p₀ / (p₀ - 1)) ^ 2 := by
              rfl
      _ = ((B * A.1.Λ) * r ^ (2 : ℕ)) := by
            dsimp [B, r]
      _ = ((B * A.1.Λ) * r ^ (2 : ℝ)) := by
            exact congrArg (fun t : ℝ => (B * A.1.Λ) * t) (Real.rpow_natCast r 2).symm
  have hstep_eq :
      moserStepConst (d := d) A p₀ ^ S =
        B ^ S * A.1.Λ ^ S * (r ^ (2 : ℝ)) ^ S := by
    have hBmul_nonneg : 0 ≤ B * A.1.Λ := by
      exact mul_nonneg hB_nonneg A.1.Λ_nonneg
    calc
      moserStepConst (d := d) A p₀ ^ S = ((B * A.1.Λ) * r ^ (2 : ℝ)) ^ S := by
        rw [hstep_eq_base]
      _ = (B * A.1.Λ) ^ S * (r ^ (2 : ℝ)) ^ S := by
        rw [Real.mul_rpow hBmul_nonneg (by positivity : 0 ≤ r ^ (2 : ℝ))]
      _ = B ^ S * A.1.Λ ^ S * (r ^ (2 : ℝ)) ^ S := by
        rw [Real.mul_rpow hB_nonneg A.1.Λ_nonneg]
  have hstep_le :
      moserStepConst (d := d) A p₀ ^ S ≤
        B ^ ((d : ℝ) / 2) * A.1.Λ ^ ((d : ℝ) / 2) * r ^ (d : ℝ) := by
    rw [hstep_eq]
    have hBA_le :
        B ^ S * A.1.Λ ^ S ≤ B ^ ((d : ℝ) / 2) * A.1.Λ ^ ((d : ℝ) / 2) := by
      exact mul_le_mul hB_pow_le hΛ_pow_le
        (Real.rpow_nonneg A.1.Λ_nonneg _)
        (Real.rpow_nonneg hB_nonneg _)
    have hstep_le' :
        (B ^ S * A.1.Λ ^ S) * (r ^ (2 : ℝ)) ^ S ≤
          (B ^ ((d : ℝ) / 2) * A.1.Λ ^ ((d : ℝ) / 2)) * r ^ (d : ℝ) := by
      exact mul_le_mul hBA_le hr_sq_pow_le
        (Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ r ^ (2 : ℝ)) _)
        (mul_nonneg (Real.rpow_nonneg hB_nonneg _) (Real.rpow_nonneg A.1.Λ_nonneg _))
    simpa [mul_assoc] using hstep_le'
  have h4_le :
      (4 : ℝ) ^ T ≤ 4 ^ (∑' i : ℕ, (i : ℝ) * q ^ i) := by
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 4) hT_le
  have hgeom_le :
      moserStepConst (d := d) A p₀ ^ S * 4 ^ T ≤
        (B ^ ((d : ℝ) / 2) * 4 ^ (∑' i : ℕ, (i : ℝ) * q ^ i)) *
          A.1.Λ ^ ((d : ℝ) / 2) * r ^ (d : ℝ) := by
    have hmul_le :
        (moserStepConst (d := d) A p₀ ^ S) * (4 : ℝ) ^ T ≤
          (B ^ ((d : ℝ) / 2) * A.1.Λ ^ ((d : ℝ) / 2) * r ^ (d : ℝ)) *
            4 ^ (∑' i : ℕ, (i : ℝ) * q ^ i) := by
      exact mul_le_mul hstep_le h4_le
        (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 4) _)
        (mul_nonneg
          (mul_nonneg (Real.rpow_nonneg hB_nonneg _) (Real.rpow_nonneg A.1.Λ_nonneg _))
          (Real.rpow_nonneg hr_nonneg _))
    simpa [mul_assoc, mul_left_comm, mul_comm] using hmul_le
  have hC_le :
      (B ^ ((d : ℝ) / 2) * 4 ^ (∑' i : ℕ, (i : ℝ) * q ^ i)) *
          A.1.Λ ^ ((d : ℝ) / 2) * r ^ (d : ℝ) ≤
        C_Moser d * A.1.Λ ^ ((d : ℝ) / 2) * r ^ (d : ℝ) := by
    have hC_base :
        B ^ ((d : ℝ) / 2) * 4 ^ (∑' i : ℕ, (i : ℝ) * q ^ i) ≤ C_Moser d := by
      dsimp [B, q]
      rw [C_Moser, dif_pos hd]
      exact
        le_max_right (C_MoserAnchor d)
          (((32 : ℝ) * C_MoserAnchor d) ^ ((d : ℝ) / 2) *
            4 ^ (∑' n : ℕ, (n : ℝ) * moserDecayRatio d ^ n))
    have hfactor_nonneg : 0 ≤ A.1.Λ ^ ((d : ℝ) / 2) * r ^ (d : ℝ) := by
      exact mul_nonneg (Real.rpow_nonneg A.1.Λ_nonneg _) (Real.rpow_nonneg hr_nonneg _)
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      (mul_le_mul_of_nonneg_right hC_base hfactor_nonneg)
  have hinside_le :
      moserStepConst (d := d) A p₀ ^ S * 4 ^ T * I ≤
        C_Moser d * A.1.Λ ^ ((d : ℝ) / 2) * r ^ (d : ℝ) * I := by
    exact mul_le_mul_of_nonneg_right (hgeom_le.trans hC_le) hI_nonneg
  have hinside_nonneg :
      0 ≤ moserStepConst (d := d) A p₀ ^ S * 4 ^ T * I := by
    exact mul_nonneg
      (mul_nonneg
        (Real.rpow_nonneg hstep_nonneg _)
        (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 4) _))
      hI_nonneg
  have hroot_le :
      (moserStepConst (d := d) A p₀ ^ S * 4 ^ T * I) ^ (1 / p₀) ≤
        (C_Moser d * A.1.Λ ^ ((d : ℝ) / 2) * r ^ (d : ℝ) * I) ^ (1 / p₀) := by
    refine Real.rpow_le_rpow hinside_nonneg hinside_le ?_
    positivity
  simpa [moserIterMajorant, moserLinftyMajorant, moserLinftyBoundPow, S, T, I, r] using hroot_le

end DeGiorgi
