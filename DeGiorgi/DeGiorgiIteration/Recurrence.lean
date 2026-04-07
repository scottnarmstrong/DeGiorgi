import DeGiorgi.DeGiorgiIteration.PreIteration

/-!
# De Giorgi Iteration: Recurrence

This module contains the abstract recurrence machinery and the canonical
De Giorgi iteration scales used by the final Linfty assembly layer.
-/

noncomputable section

open MeasureTheory Metric Filter Topology Set Function Matrix
open scoped ENNReal NNReal

namespace DeGiorgi

theorem deGiorgi_recurrence_closeout
    {Y : ℕ → ℝ} {C_rec B α : ℝ}
    (hC : 0 < C_rec) (hB : 1 < B) (hα : 0 < α)
    (hY_nonneg : ∀ n, 0 ≤ Y n)
    (h_rec : ∀ n, Y (n + 1) ≤ C_rec * B ^ n * Y n ^ (1 + α))
    (h_small : Y 0 ≤ C_rec ^ (-(1 : ℝ) / α) * B ^ (-(1 : ℝ) / α ^ 2)) :
    ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, Y n < ε := by
  let X : ℝ := C_rec * B ^ ((1 : ℝ) / α)
  let D : ℝ := X ^ ((1 : ℝ) / α)
  let q : ℝ := B ^ (-(1 : ℝ) / α)
  let W : ℕ → ℝ := fun n => B ^ ((n : ℝ) / α) * Y n
  let Z : ℕ → ℝ := fun n => D * W n
  have hBpos : 0 < B := by linarith
  have hX_nonneg : 0 ≤ X := by
    dsimp [X]
    positivity
  have hD_pos : 0 < D := by
    dsimp [D]
    positivity
  have hD_nonneg : 0 ≤ D := hD_pos.le
  have hq_nonneg : 0 ≤ q := by
    dsimp [q]
    positivity
  have hq_lt_one : q < 1 := by
    dsimp [q]
    have hneg : -(1 : ℝ) / α < 0 := by
      have hαinv_pos : 0 < (1 : ℝ) / α := by positivity
      rw [show -(1 : ℝ) / α = -((1 : ℝ) / α) by ring]
      simpa using neg_neg_of_pos hαinv_pos
    exact Real.rpow_lt_one_of_one_lt_of_neg hB hneg
  have hW_nonneg : ∀ n, 0 ≤ W n := by
    intro n
    dsimp [W]
    exact mul_nonneg (Real.rpow_nonneg (le_of_lt hBpos) _) (hY_nonneg n)
  have hDα : D ^ α = X := by
    dsimp [D]
    simpa [one_div] using (Real.rpow_inv_rpow hX_nonneg hα.ne')
  have h_small' : Y 0 ≤ D⁻¹ := by
    have hBterm : (B ^ ((1 : ℝ) / α)) ^ (-(1 : ℝ) / α) = B ^ (-(1 : ℝ) / α ^ 2) := by
      rw [← Real.rpow_mul (le_of_lt hBpos)]
      congr 1
      ring
    have hrewrite : C_rec ^ (-(1 : ℝ) / α) * B ^ (-(1 : ℝ) / α ^ 2) = D⁻¹ := by
      dsimp [D, X]
      rw [← Real.rpow_neg hX_nonneg]
      rw [Real.mul_rpow hC.le (by positivity)]
      rw [← hBterm]
      rw [show (-1 : ℝ) / α = -(1 / α) by ring]
    simpa [hrewrite] using h_small
  have hW_rec : ∀ n, W (n + 1) ≤ X * W n ^ (1 + α) := by
    intro n
    have hBn : (B ^ n : ℝ) = B ^ (n : ℝ) := by
      exact (Real.rpow_natCast B n).symm
    calc
      W (n + 1) = B ^ (((n + 1 : ℕ) : ℝ) / α) * Y (n + 1) := by
        simp [W]
      _ ≤ B ^ (((n + 1 : ℕ) : ℝ) / α) * (C_rec * B ^ n * Y n ^ (1 + α)) := by
        gcongr
        exact h_rec n
      _ = X * W n ^ (1 + α) := by
        dsimp [X, W]
        rw [hBn]
        rw [Real.mul_rpow (by positivity) (hY_nonneg n)]
        have hBpow : (B ^ ((n : ℝ) / α)) ^ (1 + α) = B ^ (((n : ℝ) / α) * (1 + α)) := by
          rw [← Real.rpow_mul (le_of_lt hBpos)]
        rw [hBpow]
        have hBcombine :
            B ^ (((n + 1 : ℕ) : ℝ) / α) * B ^ (n : ℝ) =
              B ^ ((1 : ℝ) / α) * B ^ (((n : ℝ) / α) * (1 + α)) := by
          rw [← Real.rpow_add hBpos, ← Real.rpow_add hBpos]
          congr 1
          rw [show (((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1) by norm_num]
          field_simp [hα.ne']
          ring
        calc
          B ^ (((n + 1 : ℕ) : ℝ) / α) * (C_rec * B ^ (n : ℝ) * Y n ^ (1 + α))
              = C_rec * (B ^ (((n + 1 : ℕ) : ℝ) / α) * B ^ (n : ℝ)) * Y n ^ (1 + α) := by ring
          _ = C_rec * (B ^ ((1 : ℝ) / α) * B ^ (((n : ℝ) / α) * (1 + α))) * Y n ^ (1 + α) := by
            rw [hBcombine]
          _ = C_rec * B ^ ((1 : ℝ) / α) * (B ^ (((n : ℝ) / α) * (1 + α)) * Y n ^ (1 + α)) := by
            ring
  have hZ_rec : ∀ n, Z (n + 1) ≤ Z n ^ (1 + α) := by
    intro n
    calc
      Z (n + 1) = D * W (n + 1) := by
        simp [Z]
      _ ≤ D * (X * W n ^ (1 + α)) := by
        gcongr
        exact hW_rec n
      _ = D * X * W n ^ (1 + α) := by ring
      _ = D * D ^ α * W n ^ (1 + α) := by rw [hDα]
      _ = D ^ (1 + α) * W n ^ (1 + α) := by
        have hmul : D * D ^ α = D ^ (1 + α) := by
          calc
            D * D ^ α = D ^ (1 : ℝ) * D ^ α := by rw [Real.rpow_one]
            _ = D ^ (1 + α) := by rw [← Real.rpow_add hD_pos]
        rw [hmul]
      _ = (D * W n) ^ (1 + α) := by
        rw [← Real.mul_rpow hD_nonneg (hW_nonneg n)]
      _ = Z n ^ (1 + α) := by
        simp [Z]
  have hZ_nonneg : ∀ n, 0 ≤ Z n := by
    intro n
    dsimp [Z]
    exact mul_nonneg hD_nonneg (hW_nonneg n)
  have hZ_le_one : ∀ n, Z n ≤ 1 := by
    intro n
    induction n with
    | zero =>
        calc
          Z 0 = D * Y 0 := by
            simp [Z, W]
          _ ≤ D * D⁻¹ := by
            gcongr
          _ = 1 := by
            field_simp [hD_pos.ne']
    | succ n ihn =>
        have hpow : Z n ^ (1 + α) ≤ 1 := by
          exact Real.rpow_le_one (hZ_nonneg n) ihn (by positivity)
        exact (hZ_rec n).trans hpow
  have hY_bound : ∀ n, Y n ≤ D⁻¹ * q ^ n := by
    intro n
    have hW_bound : W n ≤ D⁻¹ := by
      rw [inv_eq_one_div]
      refine (le_div_iff₀ hD_pos).2 ?_
      simpa [Z, mul_assoc, mul_comm, mul_left_comm] using hZ_le_one n
    have hY_eq : Y n = B ^ (-(n : ℝ) / α) * W n := by
      dsimp [W]
      have hcancel : B ^ (-(n : ℝ) / α) * B ^ ((n : ℝ) / α) = 1 := by
        rw [← Real.rpow_add hBpos]
        rw [show -(n : ℝ) / α + (n : ℝ) / α = 0 by ring, Real.rpow_zero]
      calc
        Y n = 1 * Y n := by ring
        _ = (B ^ (-(n : ℝ) / α) * B ^ ((n : ℝ) / α)) * Y n := by rw [hcancel]
        _ = B ^ (-(n : ℝ) / α) * W n := by ring
    calc
      Y n = B ^ (-(n : ℝ) / α) * W n := hY_eq
      _ ≤ B ^ (-(n : ℝ) / α) * D⁻¹ := by
        gcongr
      _ = D⁻¹ * B ^ (-(n : ℝ) / α) := by ring
      _ = D⁻¹ * q ^ n := by
        congr 1
        dsimp [q]
        rw [show -(n : ℝ) / α = (-(1 : ℝ) / α) * n by ring]
        rw [Real.rpow_mul (le_of_lt hBpos), Real.rpow_natCast]
  have hgeom :
      Filter.Tendsto (fun n : ℕ => D⁻¹ * q ^ n) Filter.atTop (nhds 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hq_nonneg hq_lt_one).const_mul D⁻¹
  intro ε hε
  rw [Metric.tendsto_atTop] at hgeom
  obtain ⟨N, hN⟩ := hgeom ε hε
  refine ⟨N, ?_⟩
  intro n hn
  have hgeom_lt : D⁻¹ * q ^ n < ε := by
    have := hN n hn
    rwa [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at this
  exact lt_of_le_of_lt (hY_bound n) hgeom_lt

/-- Canonical tail scale used in the De Giorgi iteration. -/
def deGiorgiTail (n : ℕ) : ℝ :=
  (1 / 2 : ℝ) ^ (n + 1)

/-- Canonical shrinking radii used in the De Giorgi iteration. -/
def deGiorgiRadius (n : ℕ) : ℝ :=
  (1 + deGiorgiTail n) / 2

/-- Canonical increasing levels used in the De Giorgi iteration. -/
def deGiorgiLevel (lamStar : ℝ) (n : ℕ) : ℝ :=
  lamStar * (1 - deGiorgiTail n)

/-- Geometric base in the canonical De Giorgi recurrence. -/
def deGiorgiRecurrenceBase (d : ℕ) : ℝ :=
  (2 : ℝ) ^ (2 + 4 / (d : ℝ))

/-- Leading coefficient in the canonical De Giorgi recurrence. -/
def deGiorgiRecurrenceCoeff (d : ℕ) (K lamStar : ℝ) : ℝ :=
  K * (2 : ℝ) ^ (6 + 8 / (d : ℝ)) * lamStar ^ (-(4 / (d : ℝ)))

lemma deGiorgiTail_pos (n : ℕ) : 0 < deGiorgiTail n := by
  dsimp [deGiorgiTail]
  positivity

lemma deGiorgiTail_sub (n : ℕ) :
    deGiorgiTail n - deGiorgiTail (n + 1) = (1 / 2 : ℝ) ^ (n + 2) := by
  dsimp [deGiorgiTail]
  rw [pow_succ']
  ring

lemma deGiorgiRadius_gap (n : ℕ) :
    deGiorgiRadius n - deGiorgiRadius (n + 1) = (1 / 2 : ℝ) ^ (n + 3) := by
  calc
    deGiorgiRadius n - deGiorgiRadius (n + 1)
        = (deGiorgiTail n - deGiorgiTail (n + 1)) / 2 := by
            dsimp [deGiorgiRadius]
            ring
    _ = ((1 / 2 : ℝ) ^ (n + 2)) / 2 := by rw [deGiorgiTail_sub]
    _ = (1 / 2 : ℝ) ^ (n + 3) := by
          rw [pow_succ']
          ring

lemma deGiorgiLevel_gap {lamStar : ℝ} (n : ℕ) :
    deGiorgiLevel lamStar (n + 1) - deGiorgiLevel lamStar n =
      lamStar * (1 / 2 : ℝ) ^ (n + 2) := by
  calc
    deGiorgiLevel lamStar (n + 1) - deGiorgiLevel lamStar n
        = lamStar * (deGiorgiTail n - deGiorgiTail (n + 1)) := by
            dsimp [deGiorgiLevel]
            ring
    _ = lamStar * (1 / 2 : ℝ) ^ (n + 2) := by rw [deGiorgiTail_sub]

/-- Rewrite the one-step estimate on canonical radii and levels into the
standard nonlinear recurrence. -/
theorem deGiorgi_preiter_to_recurrence
    {Aseq : ℕ → ℝ} {d : ℕ}
    {K lamStar : ℝ} (hLamStar : 0 < lamStar)
    (hpre :
      ∀ n,
        Aseq (n + 1) ≤
          K / ((deGiorgiRadius n - deGiorgiRadius (n + 1)) ^ 2 *
            (deGiorgiLevel lamStar (n + 1) - deGiorgiLevel lamStar n) ^ (4 / (d : ℝ))) *
          Aseq n ^ (1 + 2 / (d : ℝ))) :
    ∀ n,
      Aseq (n + 1) ≤
        deGiorgiRecurrenceCoeff d K lamStar *
          deGiorgiRecurrenceBase d ^ n *
          Aseq n ^ (1 + 2 / (d : ℝ)) := by
  intro n
  have htwo_pos : 0 < (2 : ℝ) := by positivity
  have hhalf : (1 / 2 : ℝ) = (2 : ℝ) ^ (-(1 : ℝ)) := by
    rw [Real.rpow_neg (by positivity), Real.rpow_one]
    norm_num
  have hrad :
      (deGiorgiRadius n - deGiorgiRadius (n + 1)) ^ 2 =
        (2 : ℝ) ^ (-(2 * n + 6 : ℝ)) := by
    rw [deGiorgiRadius_gap, pow_two, ← pow_add]
    have hnat : n + 3 + (n + 3) = 2 * n + 6 := by omega
    rw [hnat, ← Real.rpow_natCast]
    rw [hhalf]
    rw [← Real.rpow_mul htwo_pos.le]
    rw [show (-(1 : ℝ)) * (((2 * n + 6 : ℕ) : ℝ)) = -(2 * (n : ℝ) + 6) by
      norm_num [Nat.cast_add, Nat.cast_mul]]
  have htail_rpow :
      ((1 / 2 : ℝ) ^ (n + 2)) ^ (4 / (d : ℝ)) =
        (2 : ℝ) ^ (-((n + 2 : ℝ) * (4 / (d : ℝ)))) := by
    rw [← Real.rpow_natCast]
    rw [hhalf]
    rw [show (((n + 2 : ℕ) : ℝ) = (n : ℝ) + 2) by norm_num]
    calc
      (((2 : ℝ) ^ (-(1 : ℝ))) ^ ((n : ℝ) + 2)) ^ (4 / (d : ℝ))
          = ((2 : ℝ) ^ ((-(1 : ℝ)) * ((n : ℝ) + 2))) ^ (4 / (d : ℝ)) := by
              rw [← Real.rpow_mul htwo_pos.le]
      _ = (2 : ℝ) ^ (((-(1 : ℝ)) * ((n + 2 : ℝ))) * (4 / (d : ℝ))) := by
            rw [← Real.rpow_mul htwo_pos.le]
      _ = (2 : ℝ) ^ (-((n + 2 : ℝ) * (4 / (d : ℝ)))) := by
            congr 1
            ring
  have hlev :
      (deGiorgiLevel lamStar (n + 1) - deGiorgiLevel lamStar n) ^ (4 / (d : ℝ)) =
        lamStar ^ (4 / (d : ℝ)) * (2 : ℝ) ^ (-((n + 2 : ℝ) * (4 / (d : ℝ)))) := by
    rw [deGiorgiLevel_gap]
    rw [Real.mul_rpow hLamStar.le (by positivity)]
    rw [htail_rpow]
  have hden :
      (deGiorgiRadius n - deGiorgiRadius (n + 1)) ^ 2 *
          (deGiorgiLevel lamStar (n + 1) - deGiorgiLevel lamStar n) ^ (4 / (d : ℝ)) =
        lamStar ^ (4 / (d : ℝ)) *
          (2 : ℝ) ^ (-(6 + 8 / (d : ℝ) + n * (2 + 4 / (d : ℝ)))) := by
    rw [hrad, hlev]
    calc
      (2 : ℝ) ^ (-(2 * n + 6 : ℝ)) * (lamStar ^ (4 / (d : ℝ)) *
          (2 : ℝ) ^ (-((n + 2 : ℝ) * (4 / (d : ℝ)))))
          = lamStar ^ (4 / (d : ℝ)) *
              ((2 : ℝ) ^ (-(2 * n + 6 : ℝ)) *
                (2 : ℝ) ^ (-((n + 2 : ℝ) * (4 / (d : ℝ))))) := by
                ring
      _ = lamStar ^ (4 / (d : ℝ)) *
            (2 : ℝ) ^ (-(2 * n + 6 : ℝ) + -((n + 2 : ℝ) * (4 / (d : ℝ)))) := by
              rw [← Real.rpow_add htwo_pos]
      _ = lamStar ^ (4 / (d : ℝ)) *
            (2 : ℝ) ^ (-(6 + 8 / (d : ℝ) + n * (2 + 4 / (d : ℝ)))) := by
              congr 1
              ring_nf
  have hrec := hpre n
  calc
    Aseq (n + 1) ≤
      K / ((deGiorgiRadius n - deGiorgiRadius (n + 1)) ^ 2 *
        (deGiorgiLevel lamStar (n + 1) - deGiorgiLevel lamStar n) ^ (4 / (d : ℝ))) *
        Aseq n ^ (1 + 2 / (d : ℝ)) := hrec
    _ =
      deGiorgiRecurrenceCoeff d K lamStar *
        deGiorgiRecurrenceBase d ^ n *
        Aseq n ^ (1 + 2 / (d : ℝ)) := by
      rw [hden]
      rw [deGiorgiRecurrenceCoeff, deGiorgiRecurrenceBase]
      rw [div_eq_mul_inv]
      rw [show (lamStar ^ (4 / (d : ℝ)) *
          (2 : ℝ) ^ (-(6 + 8 / (d : ℝ) + n * (2 + 4 / (d : ℝ)))))⁻¹ =
          ((2 : ℝ) ^ (-(6 + 8 / (d : ℝ) + n * (2 + 4 / (d : ℝ)))))⁻¹ *
            (lamStar ^ (4 / (d : ℝ)))⁻¹ by rw [_root_.mul_inv_rev]]
      rw [Real.rpow_neg htwo_pos.le, Real.rpow_neg hLamStar.le]
      simp only [inv_inv]
      have hsplitpow :
          (2 : ℝ) ^ (6 + 8 / (d : ℝ) + n * (2 + 4 / (d : ℝ))) =
            (2 : ℝ) ^ (6 + 8 / (d : ℝ)) * (2 : ℝ) ^ (n * (2 + 4 / (d : ℝ))) := by
        rw [← Real.rpow_add htwo_pos]
      rw [hsplitpow]
      rw [show n * (2 + 4 / (d : ℝ)) = (2 + 4 / (d : ℝ)) * n by ring]
      rw [Real.rpow_mul htwo_pos.le, Real.rpow_natCast]
      ac_rfl

/-- The canonical De Giorgi recurrence tends to zero under the standard
smallness threshold. This is the non-PDE closeout for the De Giorgi
iteration. -/
theorem deGiorgi_preiter_vanishing
    {Aseq : ℕ → ℝ} {d : ℕ}
    (hd : 2 < (d : ℝ))
    {K lamStar : ℝ} (hK : 0 < K) (hLamStar : 0 < lamStar)
    (hA_nonneg : ∀ n, 0 ≤ Aseq n)
    (hpre :
      ∀ n,
        Aseq (n + 1) ≤
          K / ((deGiorgiRadius n - deGiorgiRadius (n + 1)) ^ 2 *
            (deGiorgiLevel lamStar (n + 1) - deGiorgiLevel lamStar n) ^ (4 / (d : ℝ))) *
          Aseq n ^ (1 + 2 / (d : ℝ)))
    (hsmall :
      Aseq 0 ≤
        (deGiorgiRecurrenceCoeff d K lamStar) ^ (-(1 : ℝ) / (2 / (d : ℝ))) *
          (deGiorgiRecurrenceBase d) ^ (-(1 : ℝ) / (2 / (d : ℝ)) ^ 2)) :
    Tendsto Aseq atTop (nhds 0) := by
  have hα : 0 < 2 / (d : ℝ) := by positivity
  have hB : 1 < deGiorgiRecurrenceBase d := by
    dsimp [deGiorgiRecurrenceBase]
    exact (Real.one_lt_rpow_iff_of_pos (by positivity)).2 (Or.inl ⟨by norm_num, by positivity⟩)
  have hC : 0 < deGiorgiRecurrenceCoeff d K lamStar := by
    dsimp [deGiorgiRecurrenceCoeff]
    positivity
  have hrec :
      ∀ n,
        Aseq (n + 1) ≤
          deGiorgiRecurrenceCoeff d K lamStar *
            deGiorgiRecurrenceBase d ^ n *
            Aseq n ^ (1 + 2 / (d : ℝ)) :=
    deGiorgi_preiter_to_recurrence hLamStar hpre
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ :=
    deGiorgi_recurrence_closeout hC hB hα hA_nonneg hrec hsmall ε hε
  exact ⟨N, fun n hn => by
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (hA_nonneg n)]
    exact hN n hn⟩

end DeGiorgi
