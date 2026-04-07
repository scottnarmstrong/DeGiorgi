import DeGiorgi.MoserIteration.Constants

/-!
# Moser Iteration Sequences

This module contains the geometric radii, exponent sequences, and the
basic algebraic lemmas that drive the Chapter 06 Moser iteration.
-/

noncomputable section

open MeasureTheory Filter

namespace DeGiorgi

variable {d : ℕ} [NeZero d]

/-- The Sobolev gain factor `χ = d/(d-2)` in the elliptic Moser iteration. -/
noncomputable def moserChi (d : ℕ) [NeZero d] : ℝ :=
  (d : ℝ) / ((d : ℝ) - 2)

/-- The standard nested radii `r_n = (1 + 2^{-n})/2`. -/
noncomputable def moserRadius (n : ℕ) : ℝ :=
  (1 + (1 / 2 : ℝ) ^ n) / 2

/-- The exponent sequence `p_{n+1} = χ p_n`. -/
noncomputable def moserExponentSeq (d : ℕ) [NeZero d] (p₀ : ℝ) (n : ℕ) : ℝ :=
  p₀ * moserChi d ^ n

theorem moserDecayRatio_nonneg (hd : 2 < (d : ℝ)) :
    0 ≤ moserDecayRatio d := by
  have hd_nonneg : 0 ≤ ((d : ℝ) - 2) := by linarith
  have hd_pos : 0 < (d : ℝ) := by
    exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne d))
  exact div_nonneg hd_nonneg hd_pos.le

theorem moserDecayRatio_lt_one (_hd : 2 < (d : ℝ)) :
    moserDecayRatio d < 1 := by
  have hd_pos : 0 < (d : ℝ) := by
    exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne d))
  rw [moserDecayRatio]
  have : ((d : ℝ) - 2) < (d : ℝ) := by linarith
  exact (div_lt_one hd_pos).2 this

theorem moserChi_pos (hd : 2 < (d : ℝ)) :
    0 < moserChi d := by
  rw [moserChi]
  have hnum_pos : 0 < (d : ℝ) := by
    exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne d))
  have hden_pos : 0 < (d : ℝ) - 2 := by linarith
  exact div_pos hnum_pos hden_pos

theorem one_lt_moserChi (hd : 2 < (d : ℝ)) :
    1 < moserChi d := by
  rw [moserChi]
  have hden_pos : 0 < (d : ℝ) - 2 := by linarith
  have : (d : ℝ) - 2 < (d : ℝ) := by linarith
  exact (one_lt_div hden_pos).2 this

theorem one_le_moserChi (hd : 2 < (d : ℝ)) :
    1 ≤ moserChi d :=
  (one_lt_moserChi (d := d) hd).le

theorem moserRadius_zero :
    moserRadius 0 = 1 := by
  simp [moserRadius]

theorem moserRadius_le_one (n : ℕ) :
    moserRadius n ≤ 1 := by
  have hpow_le : (1 / 2 : ℝ) ^ n ≤ 1 := by
    exact pow_le_one₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) ≤ 1)
  have hpow_nonneg : 0 ≤ (1 / 2 : ℝ) ^ n := by positivity
  rw [moserRadius]
  nlinarith

theorem moserRadius_pos (n : ℕ) :
    0 < moserRadius n := by
  rw [moserRadius]
  positivity

theorem moserRadius_gap (n : ℕ) :
    moserRadius n - moserRadius (n + 1) = (1 / 2 : ℝ) ^ (n + 2) := by
  rw [moserRadius, moserRadius]
  rw [pow_succ]
  field_simp
  ring_nf

theorem moserRadius_succ_lt (n : ℕ) :
    moserRadius (n + 1) < moserRadius n := by
  have hgap : 0 < moserRadius n - moserRadius (n + 1) := by
    rw [moserRadius_gap]
    positivity
  linarith

theorem moserExponentSeq_zero (p₀ : ℝ) :
    moserExponentSeq d p₀ 0 = p₀ := by
  simp [moserExponentSeq, moserChi]

theorem moserExponentSeq_succ (p₀ : ℝ) (n : ℕ) :
    moserExponentSeq d p₀ (n + 1) = moserChi d * moserExponentSeq d p₀ n := by
  rw [moserExponentSeq, pow_succ, moserExponentSeq]
  ring

theorem moserDecayRatio_eq_inv_moserChi (hd : 2 < (d : ℝ)) :
    moserDecayRatio d = (moserChi d)⁻¹ := by
  rw [moserDecayRatio, moserChi]
  have hd_ne : (d : ℝ) ≠ 0 := by
    exact_mod_cast (NeZero.ne d)
  have hdm2_ne : (d : ℝ) - 2 ≠ 0 := by
    linarith
  field_simp [hd_ne, hdm2_ne]

theorem moserExponentSeq_pos (hd : 2 < (d : ℝ)) {p₀ : ℝ} (hp₀ : 0 < p₀) (n : ℕ) :
    0 < moserExponentSeq d p₀ n := by
  rw [moserExponentSeq]
  exact mul_pos hp₀ (pow_pos (moserChi_pos (d := d) hd) n)

theorem moserExponentSeq_ge_initial (hd : 2 < (d : ℝ)) {p₀ : ℝ} (hp₀ : 0 ≤ p₀)
    (n : ℕ) :
    p₀ ≤ moserExponentSeq d p₀ n := by
  rw [moserExponentSeq]
  have hpow_ge : 1 ≤ moserChi d ^ n := by
    exact one_le_pow₀ (one_le_moserChi (d := d) hd)
  nlinarith

theorem one_lt_moserExponentSeq (hd : 2 < (d : ℝ)) {p₀ : ℝ} (hp₀ : 1 < p₀) (n : ℕ) :
    1 < moserExponentSeq d p₀ n := by
  have hp₀_nonneg : 0 ≤ p₀ := by linarith
  have hp_ge :
      p₀ ≤ moserExponentSeq d p₀ n :=
    moserExponentSeq_ge_initial (d := d) hd hp₀_nonneg n
  linarith

theorem inv_moserExponentSeq (hd : 2 < (d : ℝ)) {p₀ : ℝ} (hp₀ : 0 < p₀) (n : ℕ) :
    1 / moserExponentSeq d p₀ n = moserDecayRatio d ^ n / p₀ := by
  rw [moserExponentSeq]
  have hp₀_ne : p₀ ≠ 0 := hp₀.ne'
  have hchi_pos : 0 < moserChi d := moserChi_pos (d := d) hd
  have hchi_ne : moserChi d ≠ 0 := hchi_pos.ne'
  have hq_eq : moserDecayRatio d ^ n = (moserChi d ^ n)⁻¹ := by
    rw [moserDecayRatio_eq_inv_moserChi (d := d) hd, inv_pow]
  rw [hq_eq]
  field_simp [hp₀_ne, pow_ne_zero n hchi_ne]

end DeGiorgi
