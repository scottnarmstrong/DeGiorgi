import DeGiorgi.ScaledBallEstimates
import DeGiorgi.WeakHarnack

/-!
# Support: Iteration Constants

Shared numerical constants and elementary positivity lemmas for the Harnack and
Moser Holder endpoint files.
-/

noncomputable section

namespace DeGiorgi

/-- The local Moser base constant appearing in the Chapter 07 endpoint bounds. -/
noncomputable def localMoserBase (d : ℕ) [NeZero d] : ℝ :=
  C_Moser d * (((d : ℝ) - 1) ^ (d : ℝ)) * ((4 : ℝ) ^ (d : ℝ))

/-- The local weak Harnack base constant appearing in the Chapter 07 endpoint
bounds. -/
noncomputable def localWeakHarnackBase (d : ℕ) [NeZero d] : ℝ :=
  C_weakHarnack_of d * ((d : ℝ) ^ (weak_harnack_decay_exp d))

theorem localMoserBase_nonneg (d : ℕ) [NeZero d] : 0 ≤ localMoserBase d := by
  unfold localMoserBase
  refine mul_nonneg (mul_nonneg ?_ ?_) ?_
  · exact le_trans (by norm_num : (0 : ℝ) ≤ 1) (one_le_C_Moser (d := d))
  · have hbase : 0 ≤ (d : ℝ) - 1 := by
      have hd_one : (1 : ℝ) ≤ d := by
        exact_mod_cast Nat.succ_le_of_lt (Nat.pos_of_ne_zero (NeZero.ne d))
      nlinarith
    exact Real.rpow_nonneg hbase _
  · exact Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 4) _

theorem localMoserBase_pos (d : ℕ) [NeZero d] (hd : 2 < (d : ℝ)) :
    0 < localMoserBase d := by
  unfold localMoserBase
  refine mul_pos (mul_pos ?_ ?_) ?_
  · exact lt_of_lt_of_le zero_lt_one (one_le_C_Moser (d := d))
  · have hbase : 0 < (d : ℝ) - 1 := by
      nlinarith
    exact Real.rpow_pos_of_pos hbase _
  · exact Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 4) _

theorem localWeakHarnackBase_pos (d : ℕ) [NeZero d] :
    0 < localWeakHarnackBase d := by
  unfold localWeakHarnackBase
  refine mul_pos ?_ ?_
  · exact lt_of_lt_of_le zero_lt_one (one_le_C_weakHarnack_of (d := d))
  · have hd_pos : 0 < (d : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
    exact Real.rpow_pos_of_pos hd_pos _

theorem one_le_localMoserBase (d : ℕ) [NeZero d] (hd : 2 < (d : ℝ)) :
    1 ≤ localMoserBase d := by
  unfold localMoserBase
  have hcm : 1 ≤ C_Moser d := one_le_C_Moser (d := d)
  have hpow1 : 1 ≤ ((d : ℝ) - 1) ^ (d : ℝ) := by
    have hbase : 1 ≤ (d : ℝ) - 1 := by linarith
    exact Real.one_le_rpow hbase (by positivity)
  have hpow2 : 1 ≤ (4 : ℝ) ^ (d : ℝ) := by
    exact Real.one_le_rpow (by norm_num : (1 : ℝ) ≤ 4) (by positivity)
  exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hcm hpow1) hpow2

theorem one_le_localWeakHarnackBase (d : ℕ) [NeZero d] (hd : 2 < (d : ℝ)) :
    1 ≤ localWeakHarnackBase d := by
  unfold localWeakHarnackBase
  have hcm : 1 ≤ C_weakHarnack_of d := by
    exact one_le_C_weakHarnack_of (d := d)
  have hpow : 1 ≤ (d : ℝ) ^ (weak_harnack_decay_exp d) := by
    have hd_one : 1 ≤ (d : ℝ) := by
      exact_mod_cast Nat.succ_le_of_lt (Nat.pos_of_ne_zero (NeZero.ne d))
    have hdecay_nonneg : 0 ≤ weak_harnack_decay_exp d :=
      weak_harnack_decay_exp_nonneg (d := d) hd
    exact Real.one_le_rpow hd_one hdecay_nonneg
  exact one_le_mul_of_one_le_of_one_le hcm hpow

end DeGiorgi
