import DeGiorgi.UnitBallApproximationCore.Dilation

/-!
# Chapter 02: Unit-Ball Approximation Package

This module proves the quantitative approximation results on the unit ball.
-/

noncomputable section

open MeasureTheory Metric Filter Topology Set Function Matrix
open scoped ENNReal NNReal

namespace DeGiorgi

variable {d : ℕ} [NeZero d]

local notation "E" => EuclideanSpace ℝ (Fin d)

omit [NeZero d] in
private theorem eLpNorm_unitBallDilate_le_global
    {p : ℝ} (hp : 1 ≤ p) {f : E → ℝ} {lam : ℝ}
    (hlam : 1 < lam)
    (hf : MemLp f (ENNReal.ofReal p) volume) :
    eLpNorm (fun x => DeGiorgi.unitBallDilate (d := d) lam f x)
      (ENNReal.ofReal p) (volume.restrict (Metric.ball (0 : E) 1)) ≤
      ENNReal.ofReal (lam ^ ((d : ℝ) / p)) * eLpNorm f (ENNReal.ofReal p) volume := by
  let Bsmall : Set E := Metric.ball (0 : E) lam⁻¹
  have hlam_pos : 0 < lam := lt_trans zero_lt_one hlam
  have hp_pos : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hp_ne_zero : ENNReal.ofReal p ≠ 0 := by
    exact ne_of_gt (ENNReal.ofReal_pos.mpr hp_pos)
  have hp_ne_top : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
  have hsmall_sub : Bsmall ⊆ Metric.ball (0 : E) 1 := by
    intro x hx
    rw [Metric.mem_ball, dist_zero_right] at hx ⊢
    exact lt_trans hx (inv_lt_one_of_one_lt₀ hlam)
  have hf_small : MemLp f (ENNReal.ofReal p) (volume.restrict Bsmall) := by
    exact hf.restrict Bsmall
  have hrescale :=
    eLpNorm_rescale_to_unitBall
      (d := d) (p := ENNReal.ofReal p) (x₀ := (0 : E))
      (R := lam⁻¹) (f := f) (inv_pos.mpr hlam_pos) hp_ne_zero hp_ne_top
  have hmono :
      eLpNorm f (ENNReal.ofReal p) (volume.restrict Bsmall) ≤
        eLpNorm f (ENNReal.ofReal p) volume := by
    exact eLpNorm_mono_measure f Measure.restrict_le_self
  calc
    eLpNorm (fun x => DeGiorgi.unitBallDilate (d := d) lam f x)
      (ENNReal.ofReal p) (volume.restrict (Metric.ball (0 : E) 1))
        = ENNReal.ofReal ((lam⁻¹)⁻¹ ^ ((d : ℝ) / (ENNReal.ofReal p).toReal)) *
            eLpNorm f (ENNReal.ofReal p) (volume.restrict Bsmall) := by
              simpa [DeGiorgi.unitBallDilate, Bsmall] using hrescale
    _ = ENNReal.ofReal (lam ^ ((d : ℝ) / p)) *
          eLpNorm f (ENNReal.ofReal p) (volume.restrict Bsmall) := by
            congr 1
            rw [ENNReal.toReal_ofReal (le_of_lt hp_pos), inv_inv]
    _ ≤ ENNReal.ofReal (lam ^ ((d : ℝ) / p)) * eLpNorm f (ENNReal.ofReal p) volume := by
          gcongr

omit [NeZero d] in
private theorem exists_unitBallDilate_close_of_continuous
    {p : ℝ} (hp : 1 ≤ p) {g : E → ℝ} (hg_cont : Continuous g)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ lam : ℝ,
      1 < lam ∧ lam < 2 ∧
      eLpNorm (fun x => DeGiorgi.unitBallDilate (d := d) lam g x - g x)
        (ENNReal.ofReal p) (volume.restrict (Metric.ball (0 : E) 1)) < ENNReal.ofReal ε := by
  let B : Set E := Metric.ball (0 : E) 1
  let μB : Measure E := volume.restrict B
  have hp_pos : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hp_ne_zero : ENNReal.ofReal p ≠ 0 := by
    exact ne_of_gt (ENNReal.ofReal_pos.mpr hp_pos)
  have hp_ne_top : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
  let K : ℝ := (eLpNorm (fun _ : E => (1 : ℝ)) (ENNReal.ofReal p) μB).toReal
  let η : ℝ := ε / (2 * (K + 1))
  have hη_pos : 0 < η := by
    dsimp [η, K]
    positivity
  have hK_ne_top : eLpNorm (fun _ : E => (1 : ℝ)) (ENNReal.ofReal p) μB ≠ ⊤ := by
    have hμB_lt_top : μB Set.univ < ⊤ := by
      simpa [μB, B] using measure_ball_lt_top
    exact ((eLpNorm_const_lt_top_iff (μ := μB) (p := ENNReal.ofReal p) (c := (1 : ℝ))
      hp_ne_zero hp_ne_top).2 (Or.inr hμB_lt_top)).ne
  have hconst_eq :
      eLpNorm (fun _ : E => η) (ENNReal.ofReal p) μB =
        ENNReal.ofReal (η * K) := by
    rw [show (fun _ : E => η) = η • (fun _ : E => (1 : ℝ)) by
          ext x; simp, eLpNorm_const_smul]
    rw [show eLpNorm (fun _ : E => (1 : ℝ)) (ENNReal.ofReal p) μB = ENNReal.ofReal K by
          exact (ENNReal.ofReal_toReal hK_ne_top).symm]
    rw [ENNReal.ofReal_mul (le_of_lt hη_pos)]
    simp [Real.enorm_eq_ofReal, hη_pos.le]
  have hconst_lt :
      eLpNorm (fun _ : E => η) (ENNReal.ofReal p) μB < ENNReal.ofReal ε := by
    rw [hconst_eq]
    refine (ENNReal.ofReal_lt_ofReal_iff hε).2 ?_
    have hKnonneg : 0 ≤ K := by
      dsimp [K]
      positivity
    have hden_pos : 0 < 2 * (K + 1) := by positivity
    have hfrac : K / (2 * (K + 1)) < (1 : ℝ) := by
      have hden_ne : 2 * (K + 1) ≠ 0 := by linarith
      have hlt : K < 2 * (K + 1) := by nlinarith
      have : K / (2 * (K + 1)) - 1 < 0 := by
        field_simp [hden_ne]
        nlinarith
      linarith
    calc
      η * K = ε * (K / (2 * (K + 1))) := by
        dsimp [η]
        field_simp [hden_pos.ne']
      _ < ε * 1 := by
        gcongr
      _ = ε := by ring
  have huc :
      UniformContinuousOn g (Metric.closedBall (0 : E) 1) :=
    (isCompact_closedBall (0 : E) 1).uniformContinuousOn_of_continuous hg_cont.continuousOn
  rcases Metric.uniformContinuousOn_iff.mp huc η hη_pos with ⟨δ, hδ_pos, hδ⟩
  let lam : ℝ := 1 + min (δ / 2) (1 / 2 : ℝ)
  have hlam_gt_one : 1 < lam := by
    dsimp [lam]
    have hmin_pos : 0 < min (δ / 2) (1 / 2 : ℝ) := by
      positivity
    linarith
  have hlam_lt_two : lam < 2 := by
    dsimp [lam]
    have hmin_le : min (δ / 2) (1 / 2 : ℝ) ≤ (1 / 2 : ℝ) := min_le_right _ _
    linarith
  have hlam_sub_lt : lam - 1 < δ := by
    dsimp [lam]
    have hmin_le : min (δ / 2) (1 / 2 : ℝ) ≤ δ / 2 := min_le_left _ _
    have hhalf_lt : δ / 2 < δ := by linarith
    linarith
  have hlam_inv_sub_lt : |lam⁻¹ - 1| < δ := by
    have hlam_pos : 0 < lam := lt_trans zero_lt_one hlam_gt_one
    have habs :
        |lam⁻¹ - 1| = 1 - lam⁻¹ := by
      have hinv_lt : lam⁻¹ < 1 := inv_lt_one_of_one_lt₀ hlam_gt_one
      have hnonpos : lam⁻¹ - 1 ≤ 0 := by linarith
      rw [abs_of_nonpos hnonpos]
      ring
    rw [habs]
    calc
      1 - lam⁻¹ = (lam - 1) / lam := by
        field_simp [ne_of_gt hlam_pos]
      _ ≤ lam - 1 := by
        have hsub_nonneg : 0 ≤ lam - 1 := sub_nonneg.mpr hlam_gt_one.le
        exact div_le_self hsub_nonneg hlam_gt_one.le
      _ < δ := hlam_sub_lt
  have hpoint :
      ∀ x ∈ B,
        ‖DeGiorgi.unitBallDilate (d := d) lam g x - g x‖ ≤ η := by
    intro x hx
    have hx_norm : ‖x‖ < 1 := by
      simpa [B, Metric.mem_ball, dist_zero_right] using hx
    have hx_closed : x ∈ Metric.closedBall (0 : E) 1 := by
      simpa [Metric.mem_closedBall, dist_zero_right] using le_of_lt hx_norm
    have hx_dil : lam⁻¹ • x ∈ Metric.ball (0 : E) 1 :=
      smul_inv_mem_unitBall (d := d) hlam_gt_one hx
    have hx_dil_closed : lam⁻¹ • x ∈ Metric.closedBall (0 : E) 1 := by
      have hx_dil_norm : ‖lam⁻¹ • x‖ < 1 := by
        simpa [Metric.mem_ball, dist_zero_right] using hx_dil
      simpa [Metric.mem_closedBall, dist_zero_right] using le_of_lt hx_dil_norm
    have hdist : dist (lam⁻¹ • x) x < δ := by
      rw [dist_eq_norm]
      have hvec : lam⁻¹ • x - x = (lam⁻¹ - 1) • x := by
        simpa [one_smul] using (sub_smul (lam⁻¹) (1 : ℝ) x).symm
      rw [hvec, norm_smul]
      calc
        |lam⁻¹ - 1| * ‖x‖ < |lam⁻¹ - 1| * 1 := by
          have habs_pos : 0 < |lam⁻¹ - 1| := by
            refine abs_pos.mpr ?_
            exact sub_ne_zero.mpr (ne_of_lt (inv_lt_one_of_one_lt₀ hlam_gt_one))
          gcongr
        _ = |lam⁻¹ - 1| := by ring
        _ < δ := hlam_inv_sub_lt
    have hdist_g : dist (g (lam⁻¹ • x)) (g x) < η := hδ _ hx_dil_closed _ hx_closed hdist
    simpa [DeGiorgi.unitBallDilate, Real.dist_eq, Real.norm_eq_abs, abs_sub_comm] using hdist_g.le
  have hbound_ae :
      ∀ᵐ x ∂μB,
        ‖DeGiorgi.unitBallDilate (d := d) lam g x - g x‖ ≤ η := by
    refine ae_restrict_of_forall_mem measurableSet_ball ?_
    intro x hx
    simpa [B] using hpoint x hx
  have hnorm_le :
      eLpNorm (fun x => DeGiorgi.unitBallDilate (d := d) lam g x - g x)
        (ENNReal.ofReal p) μB ≤
        eLpNorm (fun _ : E => η) (ENNReal.ofReal p) μB := by
    exact eLpNorm_mono_ae_real hbound_ae
  refine ⟨lam, hlam_gt_one, hlam_lt_two, ?_⟩
  exact lt_of_le_of_lt hnorm_le hconst_lt

omit [NeZero d] in
private theorem exists_unitBallDilate_close_of_memLp
    {p : ℝ} (hp : 1 ≤ p) {f : E → ℝ}
    (hf : MemLp f (ENNReal.ofReal p) (volume.restrict (Metric.ball (0 : E) 1)))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ lam : ℝ,
      1 < lam ∧ lam < 2 ∧
      eLpNorm (fun x => DeGiorgi.unitBallDilate (d := d) lam f x - f x)
        (ENNReal.ofReal p) (volume.restrict (Metric.ball (0 : E) 1)) < ENNReal.ofReal ε := by
  let B : Set E := Metric.ball (0 : E) 1
  let μB : Measure E := volume.restrict B
  let q : ℝ≥0∞ := ENNReal.ofReal p
  have hp_pos : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hq_ge_one : 1 ≤ q := by
    simpa [q] using (ENNReal.ofReal_le_ofReal hp)
  have hq_ne_top : q ≠ ⊤ := by
    simp [q]
  let C : ℝ := 2 ^ ((d : ℝ) / p)
  let δr : ℝ := ε / (4 * (C + 1))
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    positivity
  have hδr_pos : 0 < δr := by
    dsimp [δr, C]
    positivity
  let f0 : E → ℝ := B.indicator f
  have hf0 : MemLp f0 q volume := by
    exact
      (MeasureTheory.memLp_indicator_iff_restrict
        (μ := volume) (s := B) (f := f) (p := q) measurableSet_ball).2 hf
  obtain ⟨g, hg_cont, hg_supp, hfg⟩ :=
    Lp_approx_by_continuous_compactly_supported
      (p := q) hq_ge_one hq_ne_top hf0 (δ := ENNReal.ofReal δr)
      (ENNReal.ofReal_pos.mpr hδr_pos)
  have hg_mem : MemLp g q volume := hg_cont.memLp_of_hasCompactSupport hg_supp
  have hfg_mem : MemLp (fun x => f0 x - g x) q volume := hf0.sub hg_mem
  have hε_half_pos : 0 < ε / 2 := by positivity
  rcases exists_unitBallDilate_close_of_continuous
      (d := d) (p := p) hp hg_cont (ε := ε / 2) hε_half_pos with
    ⟨lam, hlam_gt_one, hlam_lt_two, hmid⟩
  have hlam_pos : 0 < lam := lt_trans zero_lt_one hlam_gt_one
  have hpow_le : lam ^ ((d : ℝ) / p) ≤ C := by
    dsimp [C]
    exact Real.rpow_le_rpow (le_of_lt hlam_pos) (by linarith) (by positivity)
  have hfactor_le :
      ENNReal.ofReal (lam ^ ((d : ℝ) / p)) ≤ ENNReal.ofReal C := by
    exact ENNReal.ofReal_le_ofReal hpow_le
  let a0 : E → ℝ := fun x => DeGiorgi.unitBallDilate (d := d) lam (fun y => f0 y - g y) x
  let b : E → ℝ := fun x => DeGiorgi.unitBallDilate (d := d) lam g x - g x
  let c : E → ℝ := fun x => g x - f x
  have ha0_aesm : AEStronglyMeasurable a0 μB := by
    dsimp [a0, DeGiorgi.unitBallDilate]
    have hqmp :
        MeasureTheory.Measure.QuasiMeasurePreserving (fun x : E => lam⁻¹ • x) μB volume := by
      exact
        (MeasureTheory.Measure.quasiMeasurePreserving_smul (μ := volume) (r := lam⁻¹)
          (inv_ne_zero (ne_of_gt hlam_pos))).mono_left
          Measure.restrict_le_self.absolutelyContinuous
    simpa using hfg_mem.1.comp_quasiMeasurePreserving hqmp
  have hb_aesm : AEStronglyMeasurable b μB := by
    dsimp [b, DeGiorgi.unitBallDilate]
    have hdil_cont : Continuous (fun x : E => g (lam⁻¹ • x)) := by
      simpa using hg_cont.comp (by fun_prop)
    exact hdil_cont.aestronglyMeasurable.sub hg_cont.aestronglyMeasurable
  have hc_aesm : AEStronglyMeasurable c μB := by
    dsimp [c]
    exact hg_cont.aestronglyMeasurable.sub hf.1
  have hsum_ae :
      (fun x => DeGiorgi.unitBallDilate (d := d) lam f x - f x) =ᵐ[μB]
        (fun x => a0 x + (b x + c x)) := by
    refine ae_restrict_of_forall_mem measurableSet_ball ?_
    intro x hx
    have hx_dil : lam⁻¹ • x ∈ B := smul_inv_mem_unitBall (d := d) hlam_gt_one hx
    have hf0_dil : f0 (lam⁻¹ • x) = f (lam⁻¹ • x) := by
      simp [f0, B, hx_dil]
    change f (lam⁻¹ • x) - f x =
      (f0 (lam⁻¹ • x) - g (lam⁻¹ • x)) + (g (lam⁻¹ • x) - g x + (g x - f x))
    rw [hf0_dil]
    ring
  have htotal_le :
      eLpNorm (fun x => DeGiorgi.unitBallDilate (d := d) lam f x - f x) q μB ≤
        eLpNorm a0 q μB + (eLpNorm b q μB + eLpNorm c q μB) := by
    rw [eLpNorm_congr_ae hsum_ae]
    have hbc_aesm : AEStronglyMeasurable (fun x => b x + c x) μB := hb_aesm.add hc_aesm
    calc
      eLpNorm (fun x => a0 x + (b x + c x)) q μB ≤
          eLpNorm a0 q μB + eLpNorm (fun x => b x + c x) q μB := by
            exact eLpNorm_add_le ha0_aesm hbc_aesm hq_ge_one
      _ ≤ eLpNorm a0 q μB + (eLpNorm b q μB + eLpNorm c q μB) := by
            gcongr
            exact eLpNorm_add_le hb_aesm hc_aesm hq_ge_one
  have hfirst_le :
      eLpNorm a0 q μB ≤ ENNReal.ofReal (C * δr) := by
    calc
      eLpNorm a0 q μB
          ≤ ENNReal.ofReal (lam ^ ((d : ℝ) / p)) *
              eLpNorm (fun x => f0 x - g x) q volume := by
                simpa [a0, q] using
                  eLpNorm_unitBallDilate_le_global (d := d) (p := p) hp hlam_gt_one hfg_mem
      _ ≤ ENNReal.ofReal C * eLpNorm (fun x => f0 x - g x) q volume := by
            gcongr
      _ ≤ ENNReal.ofReal C * ENNReal.ofReal δr := by
            gcongr
            exact le_of_lt hfg
      _ = ENNReal.ofReal (C * δr) := by
            rw [ENNReal.ofReal_mul hC_nonneg]
  have hthird_le :
      eLpNorm c q μB ≤ ENNReal.ofReal δr := by
    have hEqAe :
        c =ᵐ[μB] (fun x => g x - f0 x) := by
      refine ae_restrict_of_forall_mem measurableSet_ball ?_
      intro x hx
      simp [c, f0, B, hx]
    calc
      eLpNorm c q μB = eLpNorm (fun x => g x - f0 x) q μB := eLpNorm_congr_ae hEqAe
      _ = eLpNorm (fun x => f0 x - g x) q μB := by
            refine eLpNorm_congr_norm_ae ?_
            exact Eventually.of_forall (by intro x; simp [norm_sub_rev])
      _ ≤ eLpNorm (fun x => f0 x - g x) q volume := by
            exact eLpNorm_mono_measure _ Measure.restrict_le_self
      _ ≤ ENNReal.ofReal δr := le_of_lt hfg
  refine ⟨lam, hlam_gt_one, hlam_lt_two, ?_⟩
  calc
    eLpNorm (fun x => DeGiorgi.unitBallDilate (d := d) lam f x - f x) q μB
        ≤ ENNReal.ofReal (C * δr) +
            (eLpNorm b q μB + ENNReal.ofReal δr) := by
              exact htotal_le.trans (by gcongr)
    _ < ENNReal.ofReal (C * δr) +
          (ENNReal.ofReal (ε / 2) + ENNReal.ofReal δr) := by
            have hinner :
                eLpNorm b q μB + ENNReal.ofReal δr <
                  ENNReal.ofReal (ε / 2) + ENNReal.ofReal δr := by
              exact ENNReal.add_lt_add_right ENNReal.ofReal_ne_top hmid
            exact ENNReal.add_lt_add_left ENNReal.ofReal_ne_top hinner
    _ = ENNReal.ofReal (C * δr + (ε / 2 + δr)) := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
          rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    _ < ENNReal.ofReal ε := by
          refine (ENNReal.ofReal_lt_ofReal_iff hε).2 ?_
          have hC1_pos : 0 < C + 1 := by positivity
          calc
            C * δr + (ε / 2 + δr) = (C + 1) * δr + ε / 2 := by ring
            _ = ε / 4 + ε / 2 := by
                  dsimp [δr]
                  field_simp [hC1_pos.ne']
            _ < ε := by nlinarith

omit [NeZero d] in
private theorem exists_delta_unitBallDilate_close_of_continuous
    {p : ℝ} (hp : 1 ≤ p) {g : E → ℝ} (hg_cont : Continuous g)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ ⦃lam : ℝ⦄, 1 < lam → lam < 1 + δ →
        eLpNorm (fun x => DeGiorgi.unitBallDilate (d := d) lam g x - g x)
          (ENNReal.ofReal p) (volume.restrict (Metric.ball (0 : E) 1)) < ENNReal.ofReal ε := by
  let B : Set E := Metric.ball (0 : E) 1
  let μB : Measure E := volume.restrict B
  have hp_pos : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hp_ne_zero : ENNReal.ofReal p ≠ 0 := by
    exact ne_of_gt (ENNReal.ofReal_pos.mpr hp_pos)
  have hp_ne_top : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
  let K : ℝ := (eLpNorm (fun _ : E => (1 : ℝ)) (ENNReal.ofReal p) μB).toReal
  let η : ℝ := ε / (2 * (K + 1))
  have hη_pos : 0 < η := by
    dsimp [η, K]
    positivity
  have hK_ne_top : eLpNorm (fun _ : E => (1 : ℝ)) (ENNReal.ofReal p) μB ≠ ⊤ := by
    have hμB_lt_top : μB Set.univ < ⊤ := by
      simpa [μB, B] using measure_ball_lt_top
    exact ((eLpNorm_const_lt_top_iff (μ := μB) (p := ENNReal.ofReal p) (c := (1 : ℝ))
      hp_ne_zero hp_ne_top).2 (Or.inr hμB_lt_top)).ne
  have hconst_eq :
      eLpNorm (fun _ : E => η) (ENNReal.ofReal p) μB =
        ENNReal.ofReal (η * K) := by
    rw [show (fun _ : E => η) = η • (fun _ : E => (1 : ℝ)) by
          ext x; simp, eLpNorm_const_smul]
    rw [show eLpNorm (fun _ : E => (1 : ℝ)) (ENNReal.ofReal p) μB = ENNReal.ofReal K by
          exact (ENNReal.ofReal_toReal hK_ne_top).symm]
    rw [ENNReal.ofReal_mul (le_of_lt hη_pos)]
    simp [Real.enorm_eq_ofReal, hη_pos.le]
  have hconst_lt :
      eLpNorm (fun _ : E => η) (ENNReal.ofReal p) μB < ENNReal.ofReal ε := by
    rw [hconst_eq]
    refine (ENNReal.ofReal_lt_ofReal_iff hε).2 ?_
    have hden_pos : 0 < 2 * (K + 1) := by
      dsimp [K]
      positivity
    have hC1_pos : 0 < K + 1 := by
      dsimp [K]
      positivity
    calc
      η * K = ε * (K / (2 * (K + 1))) := by
        dsimp [η]
        field_simp [hden_pos.ne']
      _ < ε * 1 := by
        gcongr
        have : K / (2 * (K + 1)) < (1 : ℝ) := by
          have hden_ne : 2 * (K + 1) ≠ 0 := by linarith
          have : K / (2 * (K + 1)) - 1 < 0 := by
            field_simp [hden_ne]
            nlinarith
          linarith
        exact this
      _ = ε := by ring
  have huc :
      UniformContinuousOn g (Metric.closedBall (0 : E) 1) :=
    (isCompact_closedBall (0 : E) 1).uniformContinuousOn_of_continuous hg_cont.continuousOn
  rcases Metric.uniformContinuousOn_iff.mp huc η hη_pos with ⟨ρ, hρ_pos, hρ⟩
  let δ : ℝ := min (ρ / 2) (1 / 2 : ℝ)
  have hδ_pos : 0 < δ := by
    dsimp [δ]
    positivity
  refine ⟨δ, hδ_pos, ?_⟩
  intro lam hlam_gt_one hlam_lt
  have hlam_pos : 0 < lam := lt_trans zero_lt_one hlam_gt_one
  have hlam_lt_two : lam < 2 := by
    have hδ_le_half : δ ≤ (1 / 2 : ℝ) := by
      dsimp [δ]
      exact min_le_right _ _
    linarith
  have hlam_sub_lt : lam - 1 < ρ := by
    have hlam_sub_lt_delta : lam - 1 < δ := by linarith
    have hδ_le : δ ≤ ρ / 2 := by
      dsimp [δ]
      exact min_le_left _ _
    have hhalf_lt : ρ / 2 < ρ := by linarith
    exact lt_trans (lt_of_lt_of_le hlam_sub_lt_delta hδ_le) hhalf_lt
  have hlam_inv_sub_lt : |lam⁻¹ - 1| < ρ := by
    have habs :
        |lam⁻¹ - 1| = 1 - lam⁻¹ := by
      have hnonpos : lam⁻¹ - 1 ≤ 0 := by
        have hinv_lt : lam⁻¹ < 1 := inv_lt_one_of_one_lt₀ hlam_gt_one
        linarith
      rw [abs_of_nonpos hnonpos]
      ring
    rw [habs]
    calc
      1 - lam⁻¹ = (lam - 1) / lam := by
        field_simp [ne_of_gt hlam_pos]
      _ ≤ lam - 1 := by
        have hsub_nonneg : 0 ≤ lam - 1 := sub_nonneg.mpr hlam_gt_one.le
        exact div_le_self hsub_nonneg hlam_gt_one.le
      _ < ρ := hlam_sub_lt
  have hpoint :
      ∀ x ∈ B,
        ‖DeGiorgi.unitBallDilate (d := d) lam g x - g x‖ ≤ η := by
    intro x hx
    have hx_norm : ‖x‖ < 1 := by
      simpa [B, Metric.mem_ball, dist_zero_right] using hx
    have hx_closed : x ∈ Metric.closedBall (0 : E) 1 := by
      simpa [Metric.mem_closedBall, dist_zero_right] using le_of_lt hx_norm
    have hx_dil : lam⁻¹ • x ∈ Metric.ball (0 : E) 1 :=
      smul_inv_mem_unitBall (d := d) hlam_gt_one hx
    have hx_dil_closed : lam⁻¹ • x ∈ Metric.closedBall (0 : E) 1 := by
      have hx_dil_norm : ‖lam⁻¹ • x‖ < 1 := by
        simpa [Metric.mem_ball, dist_zero_right] using hx_dil
      simpa [Metric.mem_closedBall, dist_zero_right] using le_of_lt hx_dil_norm
    have hdist : dist (lam⁻¹ • x) x < ρ := by
      rw [dist_eq_norm]
      have hvec : lam⁻¹ • x - x = (lam⁻¹ - 1) • x := by
        simpa [one_smul] using (sub_smul (lam⁻¹) (1 : ℝ) x).symm
      rw [hvec, norm_smul]
      calc
        |lam⁻¹ - 1| * ‖x‖ < |lam⁻¹ - 1| * 1 := by
          have habs_pos : 0 < |lam⁻¹ - 1| := by
            refine abs_pos.mpr ?_
            exact sub_ne_zero.mpr (ne_of_lt (inv_lt_one_of_one_lt₀ hlam_gt_one))
          gcongr
        _ = |lam⁻¹ - 1| := by ring
        _ < ρ := hlam_inv_sub_lt
    have hdist_g : dist (g (lam⁻¹ • x)) (g x) < η := hρ _ hx_dil_closed _ hx_closed hdist
    simpa [DeGiorgi.unitBallDilate, Real.dist_eq, Real.norm_eq_abs, abs_sub_comm] using hdist_g.le
  have hbound_ae :
      ∀ᵐ x ∂μB,
        ‖DeGiorgi.unitBallDilate (d := d) lam g x - g x‖ ≤ η := by
    refine ae_restrict_of_forall_mem measurableSet_ball ?_
    intro x hx
    simpa [B] using hpoint x hx
  have hnorm_le :
      eLpNorm (fun x => DeGiorgi.unitBallDilate (d := d) lam g x - g x)
        (ENNReal.ofReal p) μB ≤
        eLpNorm (fun _ : E => η) (ENNReal.ofReal p) μB := by
    exact eLpNorm_mono_ae_real hbound_ae
  exact lt_of_le_of_lt hnorm_le hconst_lt

omit [NeZero d] in
private theorem exists_delta_unitBallDilate_close_of_memLp
    {p : ℝ} (hp : 1 ≤ p) {f : E → ℝ}
    (hf : MemLp f (ENNReal.ofReal p) (volume.restrict (Metric.ball (0 : E) 1)))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ ⦃lam : ℝ⦄, 1 < lam → lam < 1 + δ →
        eLpNorm (fun x => DeGiorgi.unitBallDilate (d := d) lam f x - f x)
          (ENNReal.ofReal p) (volume.restrict (Metric.ball (0 : E) 1)) < ENNReal.ofReal ε := by
  let B : Set E := Metric.ball (0 : E) 1
  let μB : Measure E := volume.restrict B
  let q : ℝ≥0∞ := ENNReal.ofReal p
  have hp_pos : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hq_ge_one : 1 ≤ q := by
    simpa [q] using (ENNReal.ofReal_le_ofReal hp)
  have hq_ne_top : q ≠ ⊤ := by
    simp [q]
  let C : ℝ := 2 ^ ((d : ℝ) / p)
  let δr : ℝ := ε / (4 * (C + 1))
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    positivity
  have hδr_pos : 0 < δr := by
    dsimp [δr, C]
    positivity
  let f0 : E → ℝ := B.indicator f
  have hf0 : MemLp f0 q volume := by
    exact
      (MeasureTheory.memLp_indicator_iff_restrict
        (μ := volume) (s := B) (f := f) (p := q) measurableSet_ball).2 hf
  obtain ⟨g, hg_cont, hg_supp, hfg⟩ :=
    Lp_approx_by_continuous_compactly_supported
      (p := q) hq_ge_one hq_ne_top hf0 (δ := ENNReal.ofReal δr)
      (ENNReal.ofReal_pos.mpr hδr_pos)
  have hg_mem : MemLp g q volume := hg_cont.memLp_of_hasCompactSupport hg_supp
  have hfg_mem : MemLp (fun x => f0 x - g x) q volume := hf0.sub hg_mem
  have hε_half_pos : 0 < ε / 2 := by positivity
  obtain ⟨δ0, hδ0_pos, hcont0⟩ :=
    exists_delta_unitBallDilate_close_of_continuous
      (d := d) (p := p) hp hg_cont (ε := ε / 2) hε_half_pos
  let δ : ℝ := min δ0 (1 / 2 : ℝ)
  have hδ_pos : 0 < δ := by
    dsimp [δ]
    positivity
  refine ⟨δ, hδ_pos, ?_⟩
  intro lam hlam_gt_one hlam_lt
  have hlam_lt_δ0 : lam < 1 + δ0 := by
    have hδ_le : δ ≤ δ0 := by
      dsimp [δ]
      exact min_le_left _ _
    linarith
  have hmid :
      eLpNorm (fun x => DeGiorgi.unitBallDilate (d := d) lam g x - g x)
        (ENNReal.ofReal p) μB < ENNReal.ofReal (ε / 2) :=
    hcont0 hlam_gt_one hlam_lt_δ0
  have hlam_pos : 0 < lam := lt_trans zero_lt_one hlam_gt_one
  have hlam_lt_two : lam < 2 := by
    have hδ_le_half : δ ≤ (1 / 2 : ℝ) := by
      dsimp [δ]
      exact min_le_right _ _
    linarith
  have hpow_le : lam ^ ((d : ℝ) / p) ≤ C := by
    dsimp [C]
    exact Real.rpow_le_rpow (le_of_lt hlam_pos) (by linarith) (by positivity)
  have hfactor_le :
      ENNReal.ofReal (lam ^ ((d : ℝ) / p)) ≤ ENNReal.ofReal C := by
    exact ENNReal.ofReal_le_ofReal hpow_le
  let a0 : E → ℝ := fun x => DeGiorgi.unitBallDilate (d := d) lam (fun y => f0 y - g y) x
  let b : E → ℝ := fun x => DeGiorgi.unitBallDilate (d := d) lam g x - g x
  let c : E → ℝ := fun x => g x - f x
  have ha0_aesm : AEStronglyMeasurable a0 μB := by
    dsimp [a0, DeGiorgi.unitBallDilate]
    have hqmp :
        MeasureTheory.Measure.QuasiMeasurePreserving (fun x : E => lam⁻¹ • x) μB volume := by
      exact
        (MeasureTheory.Measure.quasiMeasurePreserving_smul (μ := volume) (r := lam⁻¹)
          (inv_ne_zero (ne_of_gt hlam_pos))).mono_left
          Measure.restrict_le_self.absolutelyContinuous
    simpa using hfg_mem.1.comp_quasiMeasurePreserving hqmp
  have hb_aesm : AEStronglyMeasurable b μB := by
    dsimp [b, DeGiorgi.unitBallDilate]
    have hdil_cont : Continuous (fun x : E => g (lam⁻¹ • x)) := by
      simpa using hg_cont.comp (by fun_prop)
    exact hdil_cont.aestronglyMeasurable.sub hg_cont.aestronglyMeasurable
  have hc_aesm : AEStronglyMeasurable c μB := by
    dsimp [c]
    exact hg_cont.aestronglyMeasurable.sub hf.1
  have hsum_ae :
      (fun x => DeGiorgi.unitBallDilate (d := d) lam f x - f x) =ᵐ[μB]
        (fun x => a0 x + (b x + c x)) := by
    refine ae_restrict_of_forall_mem measurableSet_ball ?_
    intro x hx
    have hx_dil : lam⁻¹ • x ∈ B := smul_inv_mem_unitBall (d := d) hlam_gt_one hx
    have hf0_dil : f0 (lam⁻¹ • x) = f (lam⁻¹ • x) := by
      simp [f0, B, hx_dil]
    change f (lam⁻¹ • x) - f x =
      (f0 (lam⁻¹ • x) - g (lam⁻¹ • x)) + (g (lam⁻¹ • x) - g x + (g x - f x))
    rw [hf0_dil]
    ring
  have htotal_le :
      eLpNorm (fun x => DeGiorgi.unitBallDilate (d := d) lam f x - f x) q μB ≤
        eLpNorm a0 q μB + (eLpNorm b q μB + eLpNorm c q μB) := by
    rw [eLpNorm_congr_ae hsum_ae]
    have hbc_aesm : AEStronglyMeasurable (fun x => b x + c x) μB := hb_aesm.add hc_aesm
    calc
      eLpNorm (fun x => a0 x + (b x + c x)) q μB ≤
          eLpNorm a0 q μB + eLpNorm (fun x => b x + c x) q μB := by
            exact eLpNorm_add_le ha0_aesm hbc_aesm hq_ge_one
      _ ≤ eLpNorm a0 q μB + (eLpNorm b q μB + eLpNorm c q μB) := by
            gcongr
            exact eLpNorm_add_le hb_aesm hc_aesm hq_ge_one
  have hfirst_le :
      eLpNorm a0 q μB ≤ ENNReal.ofReal (C * δr) := by
    calc
      eLpNorm a0 q μB
          ≤ ENNReal.ofReal (lam ^ ((d : ℝ) / p)) *
              eLpNorm (fun x => f0 x - g x) q volume := by
                simpa [a0, q] using
                  eLpNorm_unitBallDilate_le_global (d := d) (p := p) hp hlam_gt_one hfg_mem
      _ ≤ ENNReal.ofReal C * eLpNorm (fun x => f0 x - g x) q volume := by
            gcongr
      _ ≤ ENNReal.ofReal C * ENNReal.ofReal δr := by
            gcongr
            exact le_of_lt hfg
      _ = ENNReal.ofReal (C * δr) := by
            rw [ENNReal.ofReal_mul hC_nonneg]
  have hthird_le :
      eLpNorm c q μB ≤ ENNReal.ofReal δr := by
    have hEqAe :
        c =ᵐ[μB] (fun x => g x - f0 x) := by
      refine ae_restrict_of_forall_mem measurableSet_ball ?_
      intro x hx
      simp [c, f0, B, hx]
    calc
      eLpNorm c q μB = eLpNorm (fun x => g x - f0 x) q μB := eLpNorm_congr_ae hEqAe
      _ = eLpNorm (fun x => f0 x - g x) q μB := by
            refine eLpNorm_congr_norm_ae ?_
            exact Eventually.of_forall (by intro x; simp [norm_sub_rev])
      _ ≤ eLpNorm (fun x => f0 x - g x) q volume := by
            exact eLpNorm_mono_measure _ Measure.restrict_le_self
      _ ≤ ENNReal.ofReal δr := le_of_lt hfg
  calc
    eLpNorm (fun x => DeGiorgi.unitBallDilate (d := d) lam f x - f x) q μB
        ≤ ENNReal.ofReal (C * δr) +
            (eLpNorm b q μB + ENNReal.ofReal δr) := by
              exact htotal_le.trans (by gcongr)
    _ < ENNReal.ofReal (C * δr) +
          (ENNReal.ofReal (ε / 2) + ENNReal.ofReal δr) := by
            have hinner :
                eLpNorm b q μB + ENNReal.ofReal δr <
                  ENNReal.ofReal (ε / 2) + ENNReal.ofReal δr := by
              exact ENNReal.add_lt_add_right ENNReal.ofReal_ne_top hmid
            exact ENNReal.add_lt_add_left ENNReal.ofReal_ne_top hinner
    _ = ENNReal.ofReal (C * δr + (ε / 2 + δr)) := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
          rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    _ < ENNReal.ofReal ε := by
          refine (ENNReal.ofReal_lt_ofReal_iff hε).2 ?_
          have hC1_pos : 0 < C + 1 := by positivity
          calc
            C * δr + (ε / 2 + δr) = (C + 1) * δr + ε / 2 := by ring
            _ = ε / 4 + ε / 2 := by
                  dsimp [δr]
                  field_simp [hC1_pos.ne']
            _ < ε := by nlinarith

private theorem exists_unitBallDilate_close_of_memLp_family
    {p : ℝ} (hp : 1 ≤ p)
    {f : E → ℝ} {G : Fin d → E → ℝ}
    (hf : MemLp f (ENNReal.ofReal p) (volume.restrict (Metric.ball (0 : E) 1)))
    (hG : ∀ i : Fin d, MemLp (G i) (ENNReal.ofReal p) (volume.restrict (Metric.ball (0 : E) 1)))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ lam : ℝ,
      1 < lam ∧ lam < 2 ∧
      eLpNorm (fun x => DeGiorgi.unitBallDilate (d := d) lam f x - f x)
        (ENNReal.ofReal p) (volume.restrict (Metric.ball (0 : E) 1)) < ENNReal.ofReal ε ∧
      (∀ i : Fin d,
        eLpNorm (fun x => DeGiorgi.unitBallDilate (d := d) lam (G i) x - G i x)
          (ENNReal.ofReal p) (volume.restrict (Metric.ball (0 : E) 1)) < ENNReal.ofReal ε) := by
  obtain ⟨δf, hδf_pos, hδf⟩ :=
    exists_delta_unitBallDilate_close_of_memLp (d := d) (p := p) hp hf (ε := ε) hε
  choose δG hδG_pos hδG using
    fun i : Fin d =>
      exists_delta_unitBallDilate_close_of_memLp (d := d) (p := p) hp (hG i) (ε := ε) hε
  let δgrad : ℝ := Finset.univ.inf' Finset.univ_nonempty δG
  have hδgrad_pos : 0 < δgrad := by
    dsimp [δgrad]
    rw [Finset.lt_inf'_iff]
    intro i hi
    exact hδG_pos i
  let δ : ℝ := min 1 (min δf δgrad)
  have hδ_pos : 0 < δ := by
    dsimp [δ]
    positivity
  let lam : ℝ := 1 + δ / 2
  have hlam_gt_one : 1 < lam := by
    dsimp [lam]
    have : 0 < δ / 2 := by positivity
    linarith
  have hlam_lt_two : lam < 2 := by
    dsimp [lam, δ]
    have hδ_le_one : δ ≤ 1 := by
      dsimp [δ]
      exact min_le_left _ _
    linarith
  have hlam_lt_f : lam < 1 + δf := by
    have hδ_le : δ ≤ δf := by
      dsimp [δ]
      exact (min_le_right _ _).trans (min_le_left _ _)
    have hδ_half_lt : δ / 2 < δf := by
      have : δ / 2 < δ := by
        have hδp : 0 < δ := hδ_pos
        nlinarith
      exact lt_of_lt_of_le this hδ_le
    dsimp [lam]
    linarith
  have hlam_lt_G : ∀ i : Fin d, lam < 1 + δG i := by
    intro i
    have hδgrad_le : δgrad ≤ δG i := by
      dsimp [δgrad]
      exact Finset.inf'_le (s := Finset.univ) (f := δG) (by simp)
    have hδ_le : δ ≤ δG i := by
      dsimp [δ]
      exact (min_le_right _ _).trans ((min_le_right _ _).trans hδgrad_le)
    have hδ_half_lt : δ / 2 < δG i := by
      have : δ / 2 < δ := by
        have hδp : 0 < δ := hδ_pos
        nlinarith
      exact lt_of_lt_of_le this hδ_le
    dsimp [lam]
    linarith
  refine ⟨lam, hlam_gt_one, hlam_lt_two, hδf hlam_gt_one hlam_lt_f, ?_⟩
  intro i
  exact (hδG i) hlam_gt_one (hlam_lt_G i)

omit [NeZero d] in
private theorem exists_delta_unitBallDilate_scaled_close_of_memLp
    {p : ℝ} (hp : 1 ≤ p) {f : E → ℝ}
    (hf : MemLp f (ENNReal.ofReal p) (volume.restrict (Metric.ball (0 : E) 1)))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ ⦃lam : ℝ⦄, 1 < lam → lam < 1 + δ →
        eLpNorm (fun x => lam⁻¹ * DeGiorgi.unitBallDilate (d := d) lam f x - f x)
          (ENNReal.ofReal p) (volume.restrict (Metric.ball (0 : E) 1)) < ENNReal.ofReal ε := by
  let B : Set E := Metric.ball (0 : E) 1
  let μB : Measure E := volume.restrict B
  let q : ℝ≥0∞ := ENNReal.ofReal p
  have hp_pos : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hq_ge_one : 1 ≤ q := by
    simpa [q] using (ENNReal.ofReal_le_ofReal hp)
  have hε_half_pos : 0 < ε / 2 := by positivity
  obtain ⟨δ0, hδ0_pos, hdil0⟩ :=
    exists_delta_unitBallDilate_close_of_memLp (d := d) (p := p) hp hf (ε := ε / 2) hε_half_pos
  let M : ℝ := (eLpNorm f q μB).toReal + 1
  have hM_nonneg : 0 ≤ M := by
    dsimp [M]
    positivity
  obtain ⟨δ1, hδ1_pos, hδ1_mul⟩ := exists_pos_mul_lt hε_half_pos M
  let δ : ℝ := min δ0 (min δ1 (1 / 2 : ℝ))
  have hδ_pos : 0 < δ := by
    dsimp [δ]
    positivity
  refine ⟨δ, hδ_pos, ?_⟩
  intro lam hlam_gt_one hlam_lt
  have hlam_pos : 0 < lam := lt_trans zero_lt_one hlam_gt_one
  have hlam_lt_δ0 : lam < 1 + δ0 := by
    have hδ_le : δ ≤ δ0 := by
      dsimp [δ]
      exact min_le_left _ _
    linarith
  have hmid :
      eLpNorm (fun x => DeGiorgi.unitBallDilate (d := d) lam f x - f x) q μB <
        ENNReal.ofReal (ε / 2) :=
    hdil0 hlam_gt_one hlam_lt_δ0
  have hlam_lt_two : lam < 2 := by
    have hδ_le_half : δ ≤ (1 / 2 : ℝ) := by
      dsimp [δ]
      exact (min_le_right _ _).trans (min_le_right _ _)
    linarith
  have hδ_le_δ1 : δ ≤ δ1 := by
    dsimp [δ]
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hlam_inv_sub_lt : |lam⁻¹ - 1| < δ1 := by
    have habs :
        |lam⁻¹ - 1| = 1 - lam⁻¹ := by
      have hnonpos : lam⁻¹ - 1 ≤ 0 := by
        have hinv_lt : lam⁻¹ < 1 := inv_lt_one_of_one_lt₀ hlam_gt_one
        linarith
      rw [abs_of_nonpos hnonpos]
      ring
    rw [habs]
    have hsub_lt_delta : lam - 1 < δ := by linarith
    calc
      1 - lam⁻¹ = (lam - 1) / lam := by
        field_simp [ne_of_gt hlam_pos]
      _ ≤ lam - 1 := by
        have hsub_nonneg : 0 ≤ lam - 1 := sub_nonneg.mpr hlam_gt_one.le
        exact div_le_self hsub_nonneg hlam_gt_one.le
      _ < δ := hsub_lt_delta
      _ ≤ δ1 := hδ_le_δ1
  have hnorm_ne_top : eLpNorm f q μB ≠ ⊤ := hf.eLpNorm_ne_top
  have hnorm_le_M : eLpNorm f q μB ≤ ENNReal.ofReal M := by
    rw [← ENNReal.ofReal_toReal hnorm_ne_top]
    have htoReal_nonneg : 0 ≤ (eLpNorm f q μB).toReal := ENNReal.toReal_nonneg
    gcongr
    dsimp [M]
    linarith
  let f0 : E → ℝ := B.indicator f
  have hf0 : MemLp f0 q volume := by
    exact
      (MeasureTheory.memLp_indicator_iff_restrict
        (μ := volume) (s := B) (f := f) (p := q) measurableSet_ball).2 hf
  have hEqAe :
      (fun x => DeGiorgi.unitBallDilate (d := d) lam f x) =ᵐ[μB]
        (fun x => DeGiorgi.unitBallDilate (d := d) lam f0 x) := by
    refine ae_restrict_of_forall_mem measurableSet_ball ?_
    intro x hx
    have hx_dil : lam⁻¹ • x ∈ B := smul_inv_mem_unitBall (d := d) hlam_gt_one hx
    have hf0_dil : f0 (lam⁻¹ • x) = f (lam⁻¹ • x) := by
      simp [f0, B, hx_dil]
    change f (lam⁻¹ • x) = f0 (lam⁻¹ • x)
    exact hf0_dil.symm
  have hdil_aesm : AEStronglyMeasurable (fun x => DeGiorgi.unitBallDilate (d := d) lam f x) μB := by
    have hqmp :
        MeasureTheory.Measure.QuasiMeasurePreserving (fun x : E => lam⁻¹ • x) μB volume := by
      exact
        (MeasureTheory.Measure.quasiMeasurePreserving_smul (μ := volume) (r := lam⁻¹)
          (inv_ne_zero (ne_of_gt hlam_pos))).mono_left
          Measure.restrict_le_self.absolutelyContinuous
    have hdil0_aesm : AEStronglyMeasurable (fun x => DeGiorgi.unitBallDilate (d := d) lam f0 x) μB := by
      dsimp [DeGiorgi.unitBallDilate]
      simpa using hf0.aestronglyMeasurable.comp_quasiMeasurePreserving hqmp
    exact hdil0_aesm.congr hEqAe.symm
  have hcoeff_inv_le_one : ENNReal.ofReal lam⁻¹ ≤ 1 := by
    simpa using
      (ENNReal.ofReal_le_ofReal (show lam⁻¹ ≤ 1 by exact inv_le_one_of_one_le₀ hlam_gt_one.le))
  have hfirst_lt :
      eLpNorm (fun x => lam⁻¹ * (DeGiorgi.unitBallDilate (d := d) lam f x - f x)) q μB <
        ENNReal.ofReal (ε / 2) := by
    calc
      eLpNorm (fun x => lam⁻¹ * (DeGiorgi.unitBallDilate (d := d) lam f x - f x)) q μB
          = ENNReal.ofReal lam⁻¹ *
              eLpNorm (fun x => DeGiorgi.unitBallDilate (d := d) lam f x - f x) q μB := by
                rw [show (fun x => lam⁻¹ * (DeGiorgi.unitBallDilate (d := d) lam f x - f x)) =
                      lam⁻¹ • (fun x => DeGiorgi.unitBallDilate (d := d) lam f x - f x) by
                        ext x; simp, eLpNorm_const_smul]
                simp [Real.enorm_eq_ofReal (inv_nonneg.mpr hlam_pos.le)]
      _ ≤ eLpNorm (fun x => DeGiorgi.unitBallDilate (d := d) lam f x - f x) q μB := by
            calc
              ENNReal.ofReal lam⁻¹ *
                  eLpNorm (fun x => DeGiorgi.unitBallDilate (d := d) lam f x - f x) q μB
                  ≤ 1 * eLpNorm (fun x => DeGiorgi.unitBallDilate (d := d) lam f x - f x) q μB := by
                        gcongr
              _ = eLpNorm (fun x => DeGiorgi.unitBallDilate (d := d) lam f x - f x) q μB := by simp
      _ < ENNReal.ofReal (ε / 2) := hmid
  have hscale_err_lt :
      eLpNorm (fun x => (lam⁻¹ - 1) * f x) q μB < ENNReal.ofReal (ε / 2) := by
    calc
      eLpNorm (fun x => (lam⁻¹ - 1) * f x) q μB
          = ENNReal.ofReal |lam⁻¹ - 1| * eLpNorm f q μB := by
                rw [show (fun x => (lam⁻¹ - 1) * f x) = (lam⁻¹ - 1) • f by
                      ext x; simp, eLpNorm_const_smul]
                rw [Real.enorm_eq_ofReal_abs]
      _ ≤ ENNReal.ofReal |lam⁻¹ - 1| * ENNReal.ofReal M := by
            exact mul_le_mul' le_rfl hnorm_le_M
      _ = ENNReal.ofReal (|lam⁻¹ - 1| * M) := by
            rw [← ENNReal.ofReal_mul (abs_nonneg _)]
      _ ≤ ENNReal.ofReal (δ1 * M) := by
            exact ENNReal.ofReal_le_ofReal <|
              mul_le_mul_of_nonneg_right (le_of_lt hlam_inv_sub_lt) hM_nonneg
      _ < ENNReal.ofReal (ε / 2) := by
            refine (ENNReal.ofReal_lt_ofReal_iff hε_half_pos).2 ?_
            simpa [mul_comm] using hδ1_mul
  have hsum_ae :
      (fun x => lam⁻¹ * DeGiorgi.unitBallDilate (d := d) lam f x - f x) =ᵐ[μB]
        (fun x => lam⁻¹ * (DeGiorgi.unitBallDilate (d := d) lam f x - f x) +
          (lam⁻¹ - 1) * f x) := by
    exact Eventually.of_forall (by intro x; ring)
  have hdiff_aesm :
      AEStronglyMeasurable
        (fun x => DeGiorgi.unitBallDilate (d := d) lam f x - f x) μB := by
    exact hdil_aesm.sub hf.aestronglyMeasurable
  calc
    eLpNorm (fun x => lam⁻¹ * DeGiorgi.unitBallDilate (d := d) lam f x - f x) q μB
        = eLpNorm (fun x => lam⁻¹ * (DeGiorgi.unitBallDilate (d := d) lam f x - f x) +
            (lam⁻¹ - 1) * f x) q μB := by
              exact eLpNorm_congr_ae hsum_ae
    _ ≤ eLpNorm (fun x => lam⁻¹ * (DeGiorgi.unitBallDilate (d := d) lam f x - f x)) q μB +
          eLpNorm (fun x => (lam⁻¹ - 1) * f x) q μB := by
            exact eLpNorm_add_le (hdiff_aesm.const_mul lam⁻¹)
              (hf.aestronglyMeasurable.const_mul (lam⁻¹ - 1)) hq_ge_one
    _ < ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) := by
          exact ENNReal.add_lt_add hfirst_lt hscale_err_lt
    _ = ENNReal.ofReal ε := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
          ring_nf

private theorem exists_unitBallDilate_scaled_close_of_memLp_family
    {p : ℝ} (hp : 1 ≤ p)
    {G : Fin d → E → ℝ}
    (hG : ∀ i : Fin d, MemLp (G i) (ENNReal.ofReal p) (volume.restrict (Metric.ball (0 : E) 1)))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ lam : ℝ,
      1 < lam ∧ lam < 2 ∧
      (∀ i : Fin d,
        eLpNorm (fun x => lam⁻¹ * DeGiorgi.unitBallDilate (d := d) lam (G i) x - G i x)
          (ENNReal.ofReal p) (volume.restrict (Metric.ball (0 : E) 1)) < ENNReal.ofReal ε) := by
  choose δG hδG_pos hδG using
    fun i : Fin d =>
      exists_delta_unitBallDilate_scaled_close_of_memLp (d := d) (p := p) hp (hG i)
        (ε := ε) hε
  let δgrad : ℝ := Finset.univ.inf' Finset.univ_nonempty δG
  have hδgrad_pos : 0 < δgrad := by
    dsimp [δgrad]
    rw [Finset.lt_inf'_iff]
    intro i hi
    exact hδG_pos i
  let δ : ℝ := min 1 δgrad
  have hδ_pos : 0 < δ := by
    dsimp [δ]
    positivity
  let lam : ℝ := 1 + δ / 2
  have hlam_gt_one : 1 < lam := by
    dsimp [lam]
    have : 0 < δ / 2 := by positivity
    linarith
  have hlam_lt_two : lam < 2 := by
    dsimp [lam, δ]
    have hδ_le_one : δ ≤ 1 := by
      dsimp [δ]
      exact min_le_left _ _
    linarith
  have hlam_lt_G : ∀ i : Fin d, lam < 1 + δG i := by
    intro i
    have hδgrad_le : δgrad ≤ δG i := by
      dsimp [δgrad]
      exact Finset.inf'_le (s := Finset.univ) (f := δG) (by simp)
    have hδ_le : δ ≤ δG i := by
      dsimp [δ]
      exact (min_le_right _ _).trans hδgrad_le
    have hδ_half_lt : δ / 2 < δG i := by
      have : δ / 2 < δ := by
        have hδp : 0 < δ := hδ_pos
        nlinarith
      exact lt_of_lt_of_le this hδ_le
    dsimp [lam]
    linarith
  refine ⟨lam, hlam_gt_one, hlam_lt_two, ?_⟩
  intro i
  exact (hδG i) hlam_gt_one (hlam_lt_G i)

omit [NeZero d] in
private lemma unitBall_subset_ball_of_one_lt {lam : ℝ} (hlam : 1 < lam) :
    Metric.ball (0 : E) 1 ⊆ Metric.ball (0 : E) lam := by
  intro x hx
  rw [Metric.mem_ball, dist_zero_right] at hx ⊢
  exact lt_trans hx hlam

omit [NeZero d] in
private lemma cutoff_fderiv_eq_zero_on_unitBall
    {lam : ℝ} (_hlam : 1 < lam)
    {η : Cutoff (0 : E) 1 ((1 + lam) / 2)} {x : E}
    (hx : x ∈ Metric.ball (0 : E) 1) :
    fderiv ℝ η.toFun x = 0 := by
  have hηeq : η.toFun =ᶠ[𝓝 x] (fun _ : E => (1 : ℝ)) := by
    exact Filter.eventuallyEq_of_mem (Metric.isOpen_ball.mem_nhds hx) (by
      intro y hy
      exact η.eq_one y hy)
  exact (hasFDerivAt_const (1 : ℝ) x).congr_of_eventuallyEq hηeq |>.fderiv

omit [NeZero d] in
private lemma cutoff_fderiv_apply_eq_zero_on_unitBall
    {lam : ℝ} (hlam : 1 < lam)
    {η : Cutoff (0 : E) 1 ((1 + lam) / 2)} {x : E}
    (hx : x ∈ Metric.ball (0 : E) 1) (i : Fin d) :
    (fderiv ℝ η.toFun x) (EuclideanSpace.single i 1) = 0 := by
  simp [cutoff_fderiv_eq_zero_on_unitBall (d := d) hlam hx]

/-- One-shot `W^{1,p}` approximation on the unit ball.

This is the core density statement we want. For every `ε > 0`, there is a
globally smooth approximant whose function and weak-gradient errors are all
smaller than `ε` on `B(0,1)`. -/
theorem exists_smooth_W1p_oneShot_on_unitBall
    {p : ℝ} (hp : 1 < p) {u : E → ℝ}
    (hw : MemW1pWitness (ENNReal.ofReal p) u (Metric.ball (0 : E) 1))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ ψ : E → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) ψ ∧
      HasCompactSupport ψ ∧
      eLpNorm (fun x => ψ x - u x)
        (ENNReal.ofReal p) (volume.restrict (Metric.ball (0 : E) 1)) < ENNReal.ofReal ε ∧
      ∀ i : Fin d,
        eLpNorm
          (fun x => (fderiv ℝ ψ x) (EuclideanSpace.single i 1) - hw.weakGrad x i)
          (ENNReal.ofReal p) (volume.restrict (Metric.ball (0 : E) 1)) < ENNReal.ofReal ε := by
  let B : Set E := Metric.ball (0 : E) 1
  let q : ℝ≥0∞ := ENNReal.ofReal p
  have hp_le : 1 ≤ p := le_of_lt hp
  have hq_ge_one : 1 ≤ q := by
    simpa [q] using (ENNReal.ofReal_le_ofReal hp_le)
  have hε_half_pos : 0 < ε / 2 := by positivity
  have hε_quarter_pos : 0 < ε / 4 := by positivity
  have hquarter_lt_half : ENNReal.ofReal (ε / 4) < ENNReal.ofReal (ε / 2) := by
    refine (ENNReal.ofReal_lt_ofReal_iff hε_half_pos).2 ?_
    nlinarith
  obtain ⟨δu, hδu_pos, hδu⟩ :=
    exists_delta_unitBallDilate_close_of_memLp (d := d) (p := p) hp_le hw.memLp
      (ε := ε / 2) hε_half_pos
  choose δG hδG_pos hδG using
    fun i : Fin d =>
      exists_delta_unitBallDilate_scaled_close_of_memLp (d := d) (p := p) hp_le
        (hw.weakGrad_component_memLp i) (ε := ε / 2) hε_half_pos
  let δgrad : ℝ := Finset.univ.inf' Finset.univ_nonempty δG
  have hδgrad_pos : 0 < δgrad := by
    dsimp [δgrad]
    rw [Finset.lt_inf'_iff]
    intro i hi
    exact hδG_pos i
  let δ : ℝ := min 1 (min δu δgrad)
  have hδ_pos : 0 < δ := by
    dsimp [δ]
    positivity
  let lam : ℝ := 1 + δ / 2
  have hlam_gt_one : 1 < lam := by
    dsimp [lam]
    have : 0 < δ / 2 := by positivity
    linarith
  have hlam_lt_two : lam < 2 := by
    dsimp [lam, δ]
    have hδ_le_one : δ ≤ 1 := by
      dsimp [δ]
      exact min_le_left _ _
    linarith
  have hlam_lt_u : lam < 1 + δu := by
    have hδ_le : δ ≤ δu := by
      dsimp [δ]
      exact (min_le_right _ _).trans (min_le_left _ _)
    have hδ_half_lt : δ / 2 < δu := by
      have : δ / 2 < δ := by
        have hδp : 0 < δ := hδ_pos
        nlinarith
      exact lt_of_lt_of_le this hδ_le
    dsimp [lam]
    linarith
  have hlam_lt_G : ∀ i : Fin d, lam < 1 + δG i := by
    intro i
    have hδgrad_le : δgrad ≤ δG i := by
      dsimp [δgrad]
      exact Finset.inf'_le (s := Finset.univ) (f := δG) (by simp)
    have hδ_le : δ ≤ δG i := by
      dsimp [δ]
      exact (min_le_right _ _).trans ((min_le_right _ _).trans hδgrad_le)
    have hδ_half_lt : δ / 2 < δG i := by
      have : δ / 2 < δ := by
        have hδp : 0 < δ := hδ_pos
        nlinarith
      exact lt_of_lt_of_le this hδ_le
    dsimp [lam]
    linarith
  have hfun_dil :
      eLpNorm (fun x => DeGiorgi.unitBallDilate (d := d) lam u x - u x)
        (ENNReal.ofReal p) (volume.restrict (Metric.ball (0 : E) 1)) <
        ENNReal.ofReal (ε / 2) := hδu hlam_gt_one hlam_lt_u
  have hgrad_dil :
      ∀ i : Fin d,
        eLpNorm
          (fun x => lam⁻¹ * DeGiorgi.unitBallDilate (d := d) lam (fun y => hw.weakGrad y i) x -
            hw.weakGrad x i)
          (ENNReal.ofReal p) (volume.restrict (Metric.ball (0 : E) 1)) < ENNReal.ofReal (ε / 2) := by
    intro i
    exact hδG i hlam_gt_one (hlam_lt_G i)
  obtain ⟨η, hη_sub⟩ := exists_unitBallCutoff_inside (d := d) hlam_gt_one
  let Ω : Set E := Metric.ball (0 : E) lam
  let udil : E → ℝ := DeGiorgi.unitBallDilate (d := d) lam u
  let v : E → ℝ := fun x => η.toFun x * udil x
  let hwDil : MemW1pWitness (ENNReal.ofReal p) udil Ω :=
    MemW1pWitness.unitBallDilate_largeBall (d := d) (p := p) hp_le hlam_gt_one hw
  have hη_bound : ∀ x, |η.toFun x| ≤ 1 := by
    intro x
    rw [abs_of_nonneg (η.nonneg x)]
    exact η.le_one x
  let C1 : ℝ := ↑Mst * (((1 + lam) / 2) - 1)⁻¹
  have hC1_nonneg : 0 ≤ C1 := by
    have hmid_pos : 0 < ((1 + lam) / 2 : ℝ) - 1 := by
      nlinarith
    dsimp [C1]
    exact mul_nonneg (by positivity) (inv_nonneg.mpr hmid_pos.le)
  let hwLoc : MemW1pWitness (ENNReal.ofReal p) v Ω :=
    MemW1pWitness.mul_smooth_bounded_p (d := d) (p := ENNReal.ofReal p) hq_ge_one isOpen_ball hwDil
      η.smooth zero_le_one hC1_nonneg hη_bound (by
        intro x
        simpa [C1] using η.grad_bound x)
  have hv_sub : tsupport v ⊆ Ω := by
    dsimp [v, Ω, udil]
    exact (tsupport_smul_subset_left η.toFun (DeGiorgi.unitBallDilate (d := d) lam u)).trans hη_sub
  have hv_compact : HasCompactSupport v := by
    apply HasCompactSupport.intro' (isCompact_closedBall (0 : E) ((1 + lam) / 2)) isClosed_closedBall
    intro x hx
    exact zero_outside_of_tsupport_subset
      (Ω := Metric.closedBall (0 : E) ((1 + lam) / 2))
      ((tsupport_smul_subset_left η.toFun (DeGiorgi.unitBallDilate (d := d) lam u)).trans η.support_subset) hx
  have hKΩ : Metric.closedBall (0 : E) ((1 + lam) / 2) ⊆ Ω := by
    dsimp [Ω]
    exact Metric.closedBall_subset_ball (midpoint_lt_of_one_lt hlam_gt_one)
  have hgrad_sub :
      ∀ i : Fin d,
        tsupport (fun x => hwLoc.weakGrad x i) ⊆ Metric.closedBall (0 : E) ((1 + lam) / 2) := by
    intro i
    rw [← isClosed_closedBall.closure_eq]
    apply closure_mono
    refine Function.support_subset_iff'.2 ?_
    intro x hx
    have hηx : η.toFun x = 0 := zero_outside_of_tsupport_subset (Ω := Metric.closedBall (0 : E) ((1 + lam) / 2))
      η.support_subset hx
    have hηdx :
        (fderiv ℝ η.toFun x) (EuclideanSpace.single i 1) = 0 :=
      fderiv_apply_zero_outside_of_tsupport_subset
        (Ω := Metric.closedBall (0 : E) ((1 + lam) / 2))
        (hf := η.smooth) η.support_subset hx i
    simp [hwLoc, MemW1pWitness.mul_smooth_bounded_p, hwDil,
      MemW1pWitness.unitBallDilate_largeBall, udil, DeGiorgi.unitBallDilate,
      PiLp.toLp_apply, hηx, hηdx]
  rcases exists_smooth_W1p_approx_of_supportedWitness
      (d := d) (Ω := Ω) (K := Metric.closedBall (0 : E) ((1 + lam) / 2))
      isOpen_ball hp hwLoc (isCompact_closedBall (0 : E) ((1 + lam) / 2)) hKΩ
      ((tsupport_smul_subset_left η.toFun (DeGiorgi.unitBallDilate (d := d) lam u)).trans η.support_subset)
      hgrad_sub with
    ⟨φ, hφ_smooth, hφ_compact, hφ_sub, hφ_fun, hφ_grad⟩
  have hB_sub_Ω : B ⊆ Ω := unitBall_subset_ball_of_one_lt (d := d) hlam_gt_one
  have hφ_fun_ev :
      ∀ᶠ n in atTop,
        eLpNorm (fun x => φ n x - v x) q (volume.restrict B) < ENNReal.ofReal (ε / 2) := by
    filter_upwards [ENNReal.tendsto_nhds_zero.1 hφ_fun (ENNReal.ofReal (ε / 4))
      (ENNReal.ofReal_pos.mpr hε_quarter_pos)] with n hn
    have hmono :
        eLpNorm (fun x => φ n x - v x) q (volume.restrict B) ≤
          eLpNorm (fun x => φ n x - v x) q (volume.restrict Ω) :=
      eLpNorm_mono_measure _ (Measure.restrict_mono_set volume hB_sub_Ω)
    exact lt_of_le_of_lt hmono (lt_of_le_of_lt (by simpa [q] using hn) hquarter_lt_half)
  have hφ_grad_ev :
      ∀ i : Fin d, ∀ᶠ n in atTop,
        eLpNorm
          (fun x => (fderiv ℝ (φ n) x) (EuclideanSpace.single i 1) -
            Ω.indicator (fun y => hwLoc.weakGrad y i) x)
          q (volume.restrict B) < ENNReal.ofReal (ε / 2) := by
    intro i
    filter_upwards [ENNReal.tendsto_nhds_zero.1 (hφ_grad i) (ENNReal.ofReal (ε / 4))
      (ENNReal.ofReal_pos.mpr hε_quarter_pos)] with n hn
    have hEq :
        (fun x => (fderiv ℝ (φ n) x) (EuclideanSpace.single i 1) -
            Ω.indicator (fun y => hwLoc.weakGrad y i) x) =ᵐ[volume.restrict B]
          (fun x => (fderiv ℝ (φ n) x) (EuclideanSpace.single i 1) - hwLoc.weakGrad x i) := by
      refine ae_restrict_of_forall_mem measurableSet_ball ?_
      intro x hx
      have hxΩ : x ∈ Ω := hB_sub_Ω hx
      simp [Ω, hxΩ]
    rw [eLpNorm_congr_ae hEq]
    have hmono :
        eLpNorm
            (fun x => (fderiv ℝ (φ n) x) (EuclideanSpace.single i 1) - hwLoc.weakGrad x i)
            q (volume.restrict B) ≤
          eLpNorm
            (fun x => (fderiv ℝ (φ n) x) (EuclideanSpace.single i 1) - hwLoc.weakGrad x i)
            q (volume.restrict Ω) :=
      eLpNorm_mono_measure _ (Measure.restrict_mono_set volume hB_sub_Ω)
    exact lt_of_le_of_lt hmono (lt_of_le_of_lt (by simpa [q] using hn) hquarter_lt_half)
  have hφ_grad_all :
      ∀ᶠ n in atTop,
        ∀ i ∈ Finset.univ,
          eLpNorm
            (fun x => (fderiv ℝ (φ n) x) (EuclideanSpace.single i 1) -
              Ω.indicator (fun y => hwLoc.weakGrad y i) x)
            q (volume.restrict B) < ENNReal.ofReal (ε / 2) := by
    simpa using (Finset.eventually_all (I := Finset.univ)
      (l := atTop)
      (p := fun i n =>
        eLpNorm
          (fun x => (fderiv ℝ (φ n) x) (EuclideanSpace.single i 1) -
            Ω.indicator (fun y => hwLoc.weakGrad y i) x)
          q (volume.restrict B) < ENNReal.ofReal (ε / 2))).2
      (by intro i hi; exact hφ_grad_ev i)
  have hchoose :
      ∀ᶠ n in atTop,
        eLpNorm (fun x => φ n x - v x) q (volume.restrict B) < ENNReal.ofReal (ε / 2) ∧
        ∀ i ∈ Finset.univ,
          eLpNorm
            (fun x => (fderiv ℝ (φ n) x) (EuclideanSpace.single i 1) -
              Ω.indicator (fun y => hwLoc.weakGrad y i) x)
            q (volume.restrict B) < ENNReal.ofReal (ε / 2) := by
    exact hφ_fun_ev.and hφ_grad_all
  rcases Filter.eventually_atTop.1 hchoose with ⟨N, hN⟩
  let ψ : E → ℝ := φ N
  have hψ_smooth : ContDiff ℝ (⊤ : ℕ∞) ψ := hφ_smooth N
  have hψ_compact : HasCompactSupport ψ := hφ_compact N
  have hψ_fun_half :
      eLpNorm (fun x => ψ x - v x) q (volume.restrict B) < ENNReal.ofReal (ε / 2) := by
    simpa [ψ] using (hN N le_rfl).1
  have hψ_grad_half :
      ∀ i : Fin d,
        eLpNorm
          (fun x => (fderiv ℝ ψ x) (EuclideanSpace.single i 1) -
            Ω.indicator (fun y => hwLoc.weakGrad y i) x)
          q (volume.restrict B) < ENNReal.ofReal (ε / 2) := by
    intro i
    simpa [ψ] using (hN N le_rfl).2 i (by simp)
  have hv_memLp_B : MemLp v q (volume.restrict B) := by
    exact hwLoc.memLp.mono_measure (Measure.restrict_mono_set volume hB_sub_Ω)
  have hv_sub_eq_udil_sub :
      (fun x => v x - u x) =ᵐ[volume.restrict B] (fun x => udil x - u x) := by
    refine ae_restrict_of_forall_mem measurableSet_ball ?_
    intro x hx
    simp [v, η.eq_one x hx]
  have hψ_sub_sum_ae :
      (fun x => ψ x - u x) =ᵐ[volume.restrict B]
        (fun x => (ψ x - v x) + (v x - u x)) := by
    exact Eventually.of_forall (by intro x; ring)
  have hψ_minus_v_aesm :
      AEStronglyMeasurable (fun x => ψ x - v x) (volume.restrict B) := by
    exact
      ((hψ_smooth.continuous.aestronglyMeasurable.mono_ac
        Measure.restrict_le_self.absolutelyContinuous).sub hv_memLp_B.aestronglyMeasurable)
  have hv_minus_u_aesm :
      AEStronglyMeasurable (fun x => v x - u x) (volume.restrict B) := by
    exact hv_memLp_B.aestronglyMeasurable.sub hw.memLp.aestronglyMeasurable
  have hv_minus_u_lt :
      eLpNorm (fun x => v x - u x) q (volume.restrict B) < ENNReal.ofReal (ε / 2) := by
    rw [eLpNorm_congr_ae hv_sub_eq_udil_sub]
    simpa [B, udil] using hfun_dil
  have hhalf_add :
      ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) = ENNReal.ofReal ε := by
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    ring_nf
  have hfun_final :
      eLpNorm (fun x => ψ x - u x) q (volume.restrict B) < ENNReal.ofReal ε := by
    calc
      eLpNorm (fun x => ψ x - u x) q (volume.restrict B)
          = eLpNorm (fun x => (ψ x - v x) + (v x - u x)) q (volume.restrict B) := by
              exact eLpNorm_congr_ae hψ_sub_sum_ae
      _ ≤ eLpNorm (fun x => ψ x - v x) q (volume.restrict B) +
            eLpNorm (fun x => v x - u x) q (volume.restrict B) := by
              exact eLpNorm_add_le hψ_minus_v_aesm hv_minus_u_aesm hq_ge_one
      _ < ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) := by
            exact ENNReal.add_lt_add hψ_fun_half hv_minus_u_lt
      _ = ENNReal.ofReal ε := hhalf_add
  have hgrad_local_eq :
      ∀ i : Fin d,
        (fun x => Ω.indicator (fun y => hwLoc.weakGrad y i) x - hw.weakGrad x i)
          =ᵐ[volume.restrict B]
        (fun x => lam⁻¹ * DeGiorgi.unitBallDilate (d := d) lam (fun y => hw.weakGrad y i) x -
          hw.weakGrad x i) := by
    intro i
    refine ae_restrict_of_forall_mem measurableSet_ball ?_
    intro x hx
    have hxΩ : x ∈ Ω := hB_sub_Ω hx
    have hηx : η.toFun x = 1 := η.eq_one x hx
    have hηdx :
        (fderiv ℝ η.toFun x) (EuclideanSpace.single i 1) = 0 :=
      cutoff_fderiv_apply_eq_zero_on_unitBall (d := d) hlam_gt_one hx i
    change Ω.indicator (fun y => hwLoc.weakGrad y i) x - hw.weakGrad x i =
      lam⁻¹ * DeGiorgi.unitBallDilate (d := d) lam (fun y => hw.weakGrad y i) x - hw.weakGrad x i
    have hΩ_ind :
        Ω.indicator (fun y => hwLoc.weakGrad y i) x = hwLoc.weakGrad x i := by
      simp [Ω, hxΩ]
    rw [hΩ_ind]
    change hwLoc.weakGrad x i - hw.weakGrad x i =
      lam⁻¹ * DeGiorgi.unitBallDilate (d := d) lam (fun y => hw.weakGrad y i) x - hw.weakGrad x i
    simp [hwLoc, MemW1pWitness.mul_smooth_bounded_p, hwDil, MemW1pWitness.unitBallDilate_largeBall, v, udil, DeGiorgi.unitBallDilate, hηx, hηdx, smul_eq_mul]
  have hgrad_final :
      ∀ i : Fin d,
        eLpNorm
          (fun x => (fderiv ℝ ψ x) (EuclideanSpace.single i 1) - hw.weakGrad x i)
          q (volume.restrict B) < ENNReal.ofReal ε := by
    intro i
    let giLoc : E → ℝ := fun x => Ω.indicator (fun y => hwLoc.weakGrad y i) x
    have hgiLoc_eq :
        giLoc =ᵐ[volume.restrict B] (fun x => hwLoc.weakGrad x i) := by
      refine ae_restrict_of_forall_mem measurableSet_ball ?_
      intro x hx
      have hxΩ : x ∈ Ω := hB_sub_Ω hx
      simp [giLoc, hxΩ]
    have hgiLoc_memLp_B : MemLp giLoc q (volume.restrict B) := by
      have htmp :
          MemLp (fun x => hwLoc.weakGrad x i) q (volume.restrict B) := by
        exact (hwLoc.weakGrad_component_memLp i).mono_measure
          (Measure.restrict_mono_set volume hB_sub_Ω)
      refine ⟨?_, ?_⟩
      · exact htmp.1.congr hgiLoc_eq.symm
      · simpa [eLpNorm_congr_ae hgiLoc_eq.symm] using htmp.2
    let ei : E := EuclideanSpace.single i (1 : ℝ)
    have hderiv_cont : Continuous (fun x => (fderiv ℝ ψ x) ei) := by
      simpa [ei] using
        ((hψ_smooth.continuous_fderiv
          (by simp : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0)).clm_apply continuous_const)
    have hderiv_minus_loc_aesm :
        AEStronglyMeasurable
          (fun x => (fderiv ℝ ψ x) ei - giLoc x) (volume.restrict B) := by
      exact
        ((hderiv_cont.aestronglyMeasurable.mono_ac
          Measure.restrict_le_self.absolutelyContinuous).sub hgiLoc_memLp_B.aestronglyMeasurable)
    have hloc_minus_grad_aesm :
        AEStronglyMeasurable (fun x => giLoc x - hw.weakGrad x i) (volume.restrict B) := by
      exact hgiLoc_memLp_B.aestronglyMeasurable.sub (hw.weakGrad_component_memLp i).aestronglyMeasurable
    have hsum_ae :
        (fun x => (fderiv ℝ ψ x) ei - hw.weakGrad x i) =ᵐ[volume.restrict B]
          (fun x => ((fderiv ℝ ψ x) ei - giLoc x) + (giLoc x - hw.weakGrad x i)) := by
      exact Eventually.of_forall (by intro x; ring)
    have hloc_minus_grad_lt :
        eLpNorm (fun x => giLoc x - hw.weakGrad x i) q (volume.restrict B)
          < ENNReal.ofReal (ε / 2) := by
      have hEq :
          (fun x => giLoc x - hw.weakGrad x i) =ᵐ[volume.restrict B]
            (fun x => lam⁻¹ * DeGiorgi.unitBallDilate (d := d) lam (fun y => hw.weakGrad y i) x -
              hw.weakGrad x i) := by
        simpa [giLoc] using hgrad_local_eq i
      rw [eLpNorm_congr_ae hEq]
      simpa [B] using hgrad_dil i
    calc
      eLpNorm (fun x => (fderiv ℝ ψ x) (EuclideanSpace.single i 1) - hw.weakGrad x i)
          q (volume.restrict B)
          = eLpNorm (fun x => ((fderiv ℝ ψ x) ei - giLoc x) +
              (giLoc x - hw.weakGrad x i)) q (volume.restrict B) := by
                exact eLpNorm_congr_ae hsum_ae
      _ ≤ eLpNorm (fun x => (fderiv ℝ ψ x) ei - giLoc x) q (volume.restrict B) +
            eLpNorm (fun x => giLoc x - hw.weakGrad x i) q (volume.restrict B) := by
              exact eLpNorm_add_le hderiv_minus_loc_aesm hloc_minus_grad_aesm hq_ge_one
      _ < ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) := by
            exact ENNReal.add_lt_add (hψ_grad_half i) hloc_minus_grad_lt
      _ = ENNReal.ofReal ε := hhalf_add
  refine ⟨ψ, hψ_smooth, hψ_compact, ?_, ?_⟩
  · simpa [B, q] using hfun_final
  · intro i
    simpa [B, q] using hgrad_final i

/-- Sequence form of full `W^{1,p}` smooth approximation on the unit ball. -/
theorem exists_smooth_W1p_approx_on_unitBall
    {p : ℝ} (hp : 1 < p) {u : E → ℝ}
    (hw : MemW1pWitness (ENNReal.ofReal p) u (Metric.ball (0 : E) 1)) :
    ∃ ψ : ℕ → E → ℝ,
      (∀ n, ContDiff ℝ (⊤ : ℕ∞) (ψ n)) ∧
      (∀ n, HasCompactSupport (ψ n)) ∧
      Tendsto
        (fun n => eLpNorm (fun x => ψ n x - u x)
          (ENNReal.ofReal p) (volume.restrict (Metric.ball (0 : E) 1)))
        atTop (nhds 0) ∧
      (∀ i : Fin d,
        Tendsto
          (fun n => eLpNorm
            (fun x => (fderiv ℝ (ψ n) x) (EuclideanSpace.single i 1) - hw.weakGrad x i)
            (ENNReal.ofReal p) (volume.restrict (Metric.ball (0 : E) 1)))
          atTop (nhds 0)) := by
  let eps : ℕ → ℝ := fun n => ((n : ℝ) + 1)⁻¹
  have heps_pos : ∀ n, 0 < eps n := by
    intro n
    exact inv_pos.mpr (by positivity)
  choose ψ hψ using
    fun n => exists_smooth_W1p_oneShot_on_unitBall (d := d) (p := p) hp hw
      (ε := eps n) (heps_pos n)
  have hψ_smooth : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (ψ n) := fun n => (hψ n).1
  have hψ_compact : ∀ n, HasCompactSupport (ψ n) := fun n => (hψ n).2.1
  have hψ_fun :
      ∀ n,
        eLpNorm (fun x => ψ n x - u x)
          (ENNReal.ofReal p) (volume.restrict (Metric.ball (0 : E) 1)) <
          ENNReal.ofReal (eps n) := fun n => (hψ n).2.2.1
  have hψ_grad :
      ∀ n (i : Fin d),
        eLpNorm
          (fun x => (fderiv ℝ (ψ n) x) (EuclideanSpace.single i 1) - hw.weakGrad x i)
          (ENNReal.ofReal p) (volume.restrict (Metric.ball (0 : E) 1)) <
          ENNReal.ofReal (eps n) := fun n => (hψ n).2.2.2
  refine ⟨ψ, hψ_smooth, hψ_compact, ?_, ?_⟩
  · have h_eps_tendsto_real' :
        Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (nhds (0 : ℝ)) := by
      exact tendsto_one_div_add_atTop_nhds_zero_nat
    have h_eps_tendsto_real : Tendsto eps atTop (nhds (0 : ℝ)) := by
      simpa [eps] using h_eps_tendsto_real'
    have h_eps_tendsto : Tendsto (fun n => ENNReal.ofReal (eps n)) atTop (nhds 0) := by
      simpa using (ENNReal.continuous_ofReal.tendsto (0 : ℝ)).comp h_eps_tendsto_real
    refine ENNReal.tendsto_nhds_zero.2 ?_
    intro ε hε
    filter_upwards [ENNReal.tendsto_nhds_zero.1 h_eps_tendsto ε hε] with n hn
    exact le_trans (le_of_lt (hψ_fun n)) hn
  · intro i
    have h_eps_tendsto_real' :
        Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (nhds (0 : ℝ)) := by
      exact tendsto_one_div_add_atTop_nhds_zero_nat
    have h_eps_tendsto_real : Tendsto eps atTop (nhds (0 : ℝ)) := by
      simpa [eps] using h_eps_tendsto_real'
    have h_eps_tendsto : Tendsto (fun n => ENNReal.ofReal (eps n)) atTop (nhds 0) := by
      simpa using (ENNReal.continuous_ofReal.tendsto (0 : ℝ)).comp h_eps_tendsto_real
    refine ENNReal.tendsto_nhds_zero.2 ?_
    intro ε hε
    filter_upwards [ENNReal.tendsto_nhds_zero.1 h_eps_tendsto ε hε] with n hn
    exact le_trans (le_of_lt (hψ_grad n i)) hn

/-- `L²` specialization of the unit-ball smooth approximation theorem. -/
theorem exists_smooth_W12_approx_on_unitBall
    {u : E → ℝ}
    (hw : MemW1pWitness 2 u (Metric.ball (0 : E) 1)) :
    ∃ ψ : ℕ → E → ℝ,
      (∀ n, ContDiff ℝ (⊤ : ℕ∞) (ψ n)) ∧
      (∀ n, HasCompactSupport (ψ n)) ∧
      Tendsto
        (fun n => eLpNorm (fun x => ψ n x - u x)
          2 (volume.restrict (Metric.ball (0 : E) 1)))
        atTop (nhds 0) ∧
      (∀ i : Fin d,
        Tendsto
          (fun n => eLpNorm
            (fun x => (fderiv ℝ (ψ n) x) (EuclideanSpace.single i 1) - hw.weakGrad x i)
            2 (volume.restrict (Metric.ball (0 : E) 1)))
          atTop (nhds 0)) := by
  let hw' : MemW1pWitness (ENNReal.ofReal (2 : ℝ)) u (Metric.ball (0 : E) 1) :=
    { memLp := by
        simpa using hw.memLp
      weakGrad := hw.weakGrad
      weakGrad_component_memLp := by
        intro i
        simpa using hw.weakGrad_component_memLp i
      isWeakGrad := hw.isWeakGrad }
  rcases exists_smooth_W1p_approx_on_unitBall (d := d) (p := (2 : ℝ)) (by norm_num) hw' with
    ⟨ψ, hψ_smooth, hψ_compact, hψ_fun, hψ_grad⟩
  refine ⟨ψ, hψ_smooth, hψ_compact, ?_, ?_⟩
  · simpa [hw'] using hψ_fun
  · intro i
    simpa [hw'] using hψ_grad i

end DeGiorgi
