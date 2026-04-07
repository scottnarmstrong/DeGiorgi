import DeGiorgi.Supersolutions.InverseEnergy

/-!
# Supersolutions Inverse One-Step Estimates

This module contains the one-step inverse reverse-Holder estimate used in the
first stage of weak Harnack.
-/

noncomputable section

open MeasureTheory Metric

namespace DeGiorgi

variable {d : ℕ} [NeZero d]

local notation "E" => AmbientSpace d
local notation "μhalf" => (volume.restrict (Metric.ball (0 : E) (1 / 2 : ℝ)))

/-- One-step Sobolev gain for positive supersolutions, inverse-power case.

For `p > 0` and `0 < r < s ≤ 1`, if `u > 0` is a supersolution on `B₁`, then
```
‖u⁻¹‖_{L^{pχ}(Bᵣ)} ≤ C^{1/p} (Λp²/(1+p)² + 1)^{1/p} (s-r)^{-2/p} ‖u⁻¹‖_{Lᵖ(Bₛ)}
```
Proof: set up a cutoff `η` with `1_{Bᵣ} ≤ η ≤ 1_{Bₛ}` and `‖∇η‖ ≤ 2/(s-r)`,
apply `superPowerCutoff_energy_bound` to get the W^{1,2} energy bound, then
apply the Sobolev inequality to `v = η · u^{-p/2}` to obtain the Lᵖ → Lᵖˣ gain.
The final step is norm arithmetic converting from L²* to Lᵖˣ. -/
theorem supersolution_preMoser_inverse
    (hd : 2 < (d : ℝ))
    (A : NormalizedEllipticCoeff d (Metric.ball (0 : E) 1))
    {u : E → ℝ} {p r s : ℝ}
    (hp : 0 < p)
    (hr : 0 < r) (hrs : r < s) (hs1 : s ≤ 1)
    (hu_pos : ∀ x ∈ Metric.ball (0 : E) 1, 0 < u x)
    (hsuper : IsSupersolution A.1 u)
    (hpInt :
      IntegrableOn (fun x => |(u x)⁻¹| ^ p)
        (Metric.ball (0 : E) s) volume) :
    IntegrableOn (fun x => |(u x)⁻¹| ^ (moserChi d * p))
        (Metric.ball (0 : E) r) volume ∧
      (∫ x in Metric.ball (0 : E) r,
          |(u x)⁻¹| ^ (moserChi d * p) ∂volume) ^
          (1 / (moserChi d * p)) ≤
        ((C_MoserAnchor d / (s - r) ^ 2) *
            (A.1.Λ * (p / (1 + p)) ^ 2 + 1)) ^ (1 / p) *
          (∫ x in Metric.ball (0 : E) s, |(u x)⁻¹| ^ p ∂volume) ^ (1 / p) := by
  -- Set up the cutoff function
  let Ω : Set E := Metric.ball (0 : E) s
  let R : ℝ := (r + s) / 2
  have hs_pos : 0 < s := lt_trans hr hrs
  have hsr_pos : 0 < s - r := by linarith
  have hR : r < R := by dsimp [R]; linarith
  have hR_lt_s : R < s := by dsimp [R]; linarith
  let ηCut : Cutoff (x₀ := (0 : E)) r R := Classical.choose
    (Cutoff.exists (d := d) (0 : E) (r := r) (R := R) hr hR)
  let η : E → ℝ := ηCut.toFun
  let Cη : ℝ := 2 * (Mst : ℝ) * (s - r)⁻¹
  have hη : ContDiff ℝ (⊤ : ℕ∞) η := ηCut.smooth
  have hη_bound : ∀ x, |η x| ≤ 1 := by
    intro x
    rw [abs_of_nonneg (ηCut.nonneg x)]
    exact ηCut.le_one x
  have hη_eq_one : ∀ x ∈ Metric.ball (0 : E) r, η x = 1 := by
    intro x hx; exact ηCut.eq_one x hx
  have hη_grad_bound : ∀ x, ‖fderiv ℝ η x‖ ≤ Cη := by
    intro x
    have hmid : (((r + s) / 2 : ℝ) - r) = (s - r) / 2 := by ring
    have h_inv : ((((r + s) / 2 : ℝ) - r)⁻¹) = 2 * (s - r)⁻¹ := by
      rw [hmid]; field_simp [hsr_pos.ne']
    calc ‖fderiv ℝ η x‖ ≤ ↑Mst * (((r + s) / 2 : ℝ) - r)⁻¹ := ηCut.grad_bound x
      _ = Cη := by rw [h_inv]; ring
  have hη_sub_ball : tsupport η ⊆ Ω := by
    intro x hx
    exact (Metric.closedBall_subset_ball hR_lt_s) (ηCut.support_subset hx)
  -- Apply the energy bound
  obtain ⟨hwv, hvW01, henergy⟩ :=
    superPowerCutoff_energy_bound hd A hp hs_pos hs1 hu_pos hsuper hpInt
      hη hη_bound hη_grad_bound hη_sub_ball
  let v : E → ℝ := superPowerCutoff (d := d) η u p
  have hv_support : tsupport v ⊆ Ω :=
    superPowerCutoff_tsupport_subset (d := d) hη_sub_ball
  -- Apply the Sobolev inequality via `sobolev_prepare_on_ball`.
  obtain ⟨hwv_real, hSob⟩ :=
    sobolev_prepare_on_ball (d := d) (v := v) hd hs_pos hvW01 hv_support
  let μ : Measure E := volume.restrict Ω
  -- Convert Sobolev bound from eLpNorm to real lpNorm
  let qexp : ℝ := ((d : ℝ) * 2 / ((d : ℝ) - 2))
  let q := ENNReal.ofReal qexp
  have hq_pos : 0 < qexp := by
    dsimp [qexp]; exact div_pos (mul_pos (by linarith) (by norm_num)) (by linarith)
  let hwvReal : MemW1pWitness (ENNReal.ofReal (2 : ℝ)) v Ω :=
    { memLp := by simpa [Ω] using hwv.memLp
      weakGrad := hwv.weakGrad
      weakGrad_component_memLp := by simpa [Ω] using hwv.weakGrad_component_memLp
      isWeakGrad := by simpa [Ω] using hwv.isWeakGrad }
  have hae_grad :
      hwv_real.weakGrad =ᵐ[μ] hwvReal.weakGrad := by
    simpa [μ, Ω] using
      (MemW1pWitness.ae_eq_p (d := d) Metric.isOpen_ball
        (p := (2 : ℝ)) (by norm_num) hwv_real hwvReal)
  have hgrad_sq_eq :
      ∫ x in Ω, ‖hwv_real.weakGrad x‖ ^ 2 ∂volume =
        ∫ x in Ω, ‖hwvReal.weakGrad x‖ ^ 2 ∂volume := by
    exact integral_congr_ae (hae_grad.fun_comp (fun z => ‖z‖ ^ 2))
  have hv_memLp_q : MemLp v q μ := by
    refine ⟨hwv_real.memLp.aestronglyMeasurable, ?_⟩
    exact lt_of_le_of_lt hSob
      (ENNReal.mul_lt_top_iff.mpr (Or.inl ⟨by simp,
        lt_top_iff_ne_top.mpr (by simpa using hwv_real.weakGrad_norm_memLp.eLpNorm_ne_top)⟩))
  have hSob' : eLpNorm v q μ ≤
      ENNReal.ofReal (C_gns d 2) *
        eLpNorm (fun x => ‖hwv_real.weakGrad x‖) 2 μ := by
    simpa [q, μ, Ω] using hSob
  have hgrad_ne_top : eLpNorm (fun x => ‖hwv_real.weakGrad x‖) 2 μ ≠ ⊤ := by
    simpa using hwv_real.weakGrad_norm_memLp.eLpNorm_ne_top
  have hSob_real :
      MeasureTheory.lpNorm v q μ ≤
        (C_gns d 2) * MeasureTheory.lpNorm (fun x => ‖hwv_real.weakGrad x‖) 2 μ := by
    have hSob_toReal :=
      (ENNReal.toReal_le_toReal hv_memLp_q.eLpNorm_ne_top
        (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hgrad_ne_top)).2 hSob'
    rwa [MeasureTheory.toReal_eLpNorm hv_memLp_q.aestronglyMeasurable,
      ENNReal.toReal_mul, MeasureTheory.toReal_eLpNorm
        hwv_real.weakGrad_norm_memLp.aestronglyMeasurable,
      ENNReal.toReal_ofReal (C_gns_nonneg d 2)] at hSob_toReal
  have hgrad_lp :
      MeasureTheory.lpNorm (fun x => ‖hwv_real.weakGrad x‖) 2 μ =
        (∫ x in Ω, ‖hwv_real.weakGrad x‖ ^ 2 ∂volume) ^ (1 / (2 : ℝ)) := by
    simpa [μ, Ω] using
      (MeasureTheory.lpNorm_eq_integral_norm_rpow_toReal (μ := μ)
        (f := fun x => ‖hwv_real.weakGrad x‖)
        two_ne_zero ENNReal.ofNat_ne_top hwv_real.weakGrad_norm_memLp.aestronglyMeasurable)
  have hgrad_bound :
      MeasureTheory.lpNorm (fun x => ‖hwv_real.weakGrad x‖) 2 μ ≤
        (2 * Cη ^ 2 * (A.1.Λ * (p / (1 + p)) ^ 2 + 1) *
          ∫ x in Ω, |(u x)⁻¹| ^ p ∂volume) ^ (1 / (2 : ℝ)) := by
    rw [hgrad_lp, hgrad_sq_eq]
    exact Real.rpow_le_rpow (by exact integral_nonneg fun x => by positivity)
      (by simpa [hwvReal] using henergy) (by norm_num)
  -- Convert v on Bᵣ to |u⁻¹|^{p/2} using η = 1
  have hq_ne_zero : q ≠ 0 := by
    dsimp [q]; rw [ENNReal.ofReal_eq_zero]; linarith
  have hv_lp_eq :
      MeasureTheory.lpNorm v q μ =
        (∫ x in Ω, |v x| ^ qexp ∂volume) ^ (1 / qexp) := by
    rw [MeasureTheory.lpNorm_eq_integral_norm_rpow_toReal (μ := μ) (f := v)]
    · simp [μ, Ω, q, qexp, ENNReal.toReal_ofReal hq_pos.le, Real.norm_eq_abs]
    · exact hq_ne_zero
    · exact ENNReal.ofReal_ne_top
    · exact hv_memLp_q.aestronglyMeasurable
  have hv_int : IntegrableOn (fun x => |v x| ^ qexp) Ω volume := by
    simpa [μ, Ω, q, qexp, ENNReal.toReal_ofReal hq_pos.le, Real.norm_eq_abs] using
      hv_memLp_q.integrable_norm_rpow hq_ne_zero ENNReal.ofReal_ne_top
  have hpow_eq_on : ∀ x ∈ Metric.ball (0 : E) r,
      |v x| ^ qexp = |(u x)⁻¹| ^ (moserChi d * p) := by
    intro x hx
    have hηx : η x = 1 := hη_eq_one x hx
    have hqexp_eq : qexp = 2 * moserChi d := by
      dsimp [qexp, moserChi]; field_simp
    have hvx : v x = |(u x)⁻¹| ^ (p / 2) := by
      simp [v, superPowerCutoff, hηx]
    calc |v x| ^ qexp
        = (|(u x)⁻¹| ^ (p / 2)) ^ qexp := by
          rw [hvx, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
      _ = |(u x)⁻¹| ^ (moserChi d * p) := by
          rw [hqexp_eq, ← Real.rpow_mul (abs_nonneg _)]; ring_nf
  have hleft_int : IntegrableOn (fun x => |(u x)⁻¹| ^ (moserChi d * p))
      (Metric.ball (0 : E) r) volume := by
    exact (hv_int.mono_set (Metric.ball_subset_ball (le_of_lt hrs))).congr_fun
      (fun x hx => hpow_eq_on x hx) measurableSet_ball
  have hleft_integral_le :
      ∫ x in Metric.ball (0 : E) r, |(u x)⁻¹| ^ (moserChi d * p) ∂volume ≤
        ∫ x in Ω, |v x| ^ qexp ∂volume := by
    calc ∫ x in Metric.ball (0 : E) r, |(u x)⁻¹| ^ (moserChi d * p) ∂volume
        = ∫ x in Metric.ball (0 : E) r, |v x| ^ qexp ∂volume := by
          symm; exact setIntegral_congr_fun measurableSet_ball (fun x hx => hpow_eq_on x hx)
      _ ≤ ∫ x in Ω, |v x| ^ qexp ∂volume := by
          exact setIntegral_mono_set hv_int (ae_of_all _ (by intro x; positivity))
            (ae_of_all _ (Metric.ball_subset_ball (le_of_lt hrs)))
  -- Constant consolidation
  have hCη_sq : Cη ^ 2 = 4 * (Mst : ℝ) ^ 2 / (s - r) ^ 2 := by
    dsimp [Cη]; field_simp [hsr_pos.ne']; ring
  have hconst_bound :
      (C_gns d 2) ^ 2 * (2 * Cη ^ 2) ≤ C_MoserAnchor d / (s - r) ^ 2 := by
    rw [hCη_sq]
    have hrewrite :
        (C_gns d 2) ^ 2 * (2 * (4 * (Mst : ℝ) ^ 2 / (s - r) ^ 2)) =
          ((C_gns d 2) ^ 2 * (8 * (Mst : ℝ) ^ 2)) / (s - r) ^ 2 := by
      field_simp [hsr_pos.ne']; ring
    rw [hrewrite]
    exact div_le_div_of_nonneg_right
      (by simpa [mul_assoc, mul_left_comm, mul_comm] using
        cutoff_sobolev_anchor_le_C_MoserAnchor (d := d))
      (by positivity)
  have hcoeff_nonneg : 0 ≤ A.1.Λ * (p / (1 + p)) ^ 2 + 1 := by
    nlinarith [A.1.Λ_nonneg, sq_nonneg (p / (1 + p))]
  have hIp_nonneg : 0 ≤ ∫ x in Ω, |(u x)⁻¹| ^ p ∂volume := integral_nonneg fun x => by positivity
  -- Main chain: Lᵖˣ(Bᵣ) ≤ Sobolev(v) ≤ C_gns · gradient ≤ C_gns · energy^{1/2} ≤ constant · Lᵖ(Bₛ)
  have hqexp_mul : (1 / qexp : ℝ) * (2 / p) = 1 / (moserChi d * p) := by
    dsimp [qexp, moserChi]; field_simp
  have hhalf_mul : (1 / (2 : ℝ)) * (2 / p) = 1 / p := by field_simp [hp.ne']
  have hclose_exp_nonneg : 0 ≤ 1 / (moserChi d * p) := by
    exact one_div_nonneg.mpr (mul_pos (moserChi_pos (d := d) hd) hp).le
  have hright_nonneg : 0 ≤ ∫ x in Ω, |v x| ^ qexp ∂volume := integral_nonneg fun x => by positivity
  have hinner_nonneg : 0 ≤ 2 * Cη ^ 2 * (A.1.Λ * (p / (1 + p)) ^ 2 + 1) *
      ∫ x in Ω, |(u x)⁻¹| ^ p ∂volume := by positivity
  have hgrad_rhs_nonneg : 0 ≤ (2 * Cη ^ 2 * (A.1.Λ * (p / (1 + p)) ^ 2 + 1) *
      ∫ x in Ω, |(u x)⁻¹| ^ p ∂volume) ^ (1 / (2 : ℝ)) :=
    Real.rpow_nonneg hinner_nonneg _
  have hmain_lp :
      (∫ x in Metric.ball (0 : E) r,
          |(u x)⁻¹| ^ (moserChi d * p) ∂volume) ^ (1 / (moserChi d * p)) ≤
        ((C_MoserAnchor d / (s - r) ^ 2) *
            (A.1.Λ * (p / (1 + p)) ^ 2 + 1) *
            ∫ x in Ω, |(u x)⁻¹| ^ p ∂volume) ^ (1 / p) := by
    calc (∫ x in Metric.ball (0 : E) r,
            |(u x)⁻¹| ^ (moserChi d * p) ∂volume) ^ (1 / (moserChi d * p))
        ≤ (∫ x in Ω, |v x| ^ qexp ∂volume) ^ (1 / (moserChi d * p)) := by
            exact Real.rpow_le_rpow (by positivity) hleft_integral_le hclose_exp_nonneg
      _ = ((∫ x in Ω, |v x| ^ qexp ∂volume) ^ (1 / qexp)) ^ (2 / p) := by
            rw [← Real.rpow_mul hright_nonneg, hqexp_mul]
      _ = (MeasureTheory.lpNorm v q μ) ^ (2 / p) := by rw [hv_lp_eq]
      _ ≤ ((C_gns d 2) * MeasureTheory.lpNorm (fun x => ‖hwv_real.weakGrad x‖) 2 μ) ^ (2 / p) := by
            exact Real.rpow_le_rpow MeasureTheory.lpNorm_nonneg hSob_real (by positivity)
      _ ≤ ((C_gns d 2) * (2 * Cη ^ 2 * (A.1.Λ * (p / (1 + p)) ^ 2 + 1) *
              ∫ x in Ω, |(u x)⁻¹| ^ p ∂volume) ^ (1 / (2 : ℝ))) ^ (2 / p) := by
            exact Real.rpow_le_rpow
              (mul_nonneg (C_gns_nonneg d 2) MeasureTheory.lpNorm_nonneg)
              (mul_le_mul_of_nonneg_left hgrad_bound (C_gns_nonneg d 2))
              (by positivity)
      _ = ((C_gns d 2) ^ 2 * (2 * Cη ^ 2) *
              (A.1.Λ * (p / (1 + p)) ^ 2 + 1) *
              ∫ x in Ω, |(u x)⁻¹| ^ p ∂volume) ^ (1 / p) := by
            calc ((C_gns d 2) * (2 * Cη ^ 2 * (A.1.Λ * (p / (1 + p)) ^ 2 + 1) *
                    ∫ x in Ω, |(u x)⁻¹| ^ p ∂volume) ^ (1 / (2 : ℝ))) ^ (2 / p)
                = (C_gns d 2) ^ (2 / p) *
                    ((2 * Cη ^ 2 * (A.1.Λ * (p / (1 + p)) ^ 2 + 1) *
                      ∫ x in Ω, |(u x)⁻¹| ^ p ∂volume) ^ (1 / (2 : ℝ))) ^ (2 / p) := by
                  rw [Real.mul_rpow (C_gns_nonneg d 2) hgrad_rhs_nonneg]
              _ = ((C_gns d 2) ^ 2) ^ (1 / p) *
                    (2 * Cη ^ 2 * (A.1.Λ * (p / (1 + p)) ^ 2 + 1) *
                      ∫ x in Ω, |(u x)⁻¹| ^ p ∂volume) ^ (1 / p) := by
                  congr 1
                  · rw [show (2 / p : ℝ) = 2 * (1 / p) by field_simp [hp.ne']]
                    simpa using (Real.rpow_mul (C_gns_nonneg d 2) 2 (1 / p))
                  · rw [← Real.rpow_mul hinner_nonneg, hhalf_mul]
              _ = ((C_gns d 2) ^ 2 * (2 * Cη ^ 2) *
                    (A.1.Λ * (p / (1 + p)) ^ 2 + 1) *
                    ∫ x in Ω, |(u x)⁻¹| ^ p ∂volume) ^ (1 / p) := by
                  rw [← Real.mul_rpow (sq_nonneg (C_gns d 2)) hinner_nonneg]; congr 1; ring
      _ ≤ ((C_MoserAnchor d / (s - r) ^ 2) *
              (A.1.Λ * (p / (1 + p)) ^ 2 + 1) *
              ∫ x in Ω, |(u x)⁻¹| ^ p ∂volume) ^ (1 / p) := by
            apply Real.rpow_le_rpow (by positivity)
            · exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right hconst_bound
                  (by nlinarith [A.1.Λ_nonneg, sq_nonneg (p / (1 + p))]))
                hIp_nonneg
            · positivity
  -- Separate the outer coefficient before applying `Real.mul_rpow`.
  refine ⟨hleft_int, ?_⟩
  have hsplit_nonneg : 0 ≤ (C_MoserAnchor d / (s - r) ^ 2) *
      (A.1.Λ * (p / (1 + p)) ^ 2 + 1) := by
    exact mul_nonneg (div_nonneg (le_trans (by norm_num : (0 : ℝ) ≤ 1)
      (one_le_C_MoserAnchor (d := d))) (by positivity)) hcoeff_nonneg
  calc (∫ x in Metric.ball (0 : E) r,
          |(u x)⁻¹| ^ (moserChi d * p) ∂volume) ^ (1 / (moserChi d * p))
      ≤ ((C_MoserAnchor d / (s - r) ^ 2) *
          (A.1.Λ * (p / (1 + p)) ^ 2 + 1) *
          ∫ x in Ω, |(u x)⁻¹| ^ p ∂volume) ^ (1 / p) := hmain_lp
    _ = ((C_MoserAnchor d / (s - r) ^ 2) *
            (A.1.Λ * (p / (1 + p)) ^ 2 + 1)) ^ (1 / p) *
          (∫ x in Ω, |(u x)⁻¹| ^ p ∂volume) ^ (1 / p) := by
          rw [Real.mul_rpow hsplit_nonneg hIp_nonneg]

/-- One-step inverse-power reverse-Holder estimate for positive supersolutions. -/
theorem supersolution_reverseHolder_inverse
    (hd : 2 < (d : ℝ))
    (A : NormalizedEllipticCoeff d (Metric.ball (0 : E) 1))
    {u : E → ℝ} {p r s : ℝ}
    (hp : 0 < p)
    (hr : 0 < r) (hrs : r < s) (hs1 : s ≤ 1)
    (hu_pos : ∀ x ∈ Metric.ball (0 : E) 1, 0 < u x)
    (hsuper : IsSupersolution A.1 u)
    (hpInt :
      IntegrableOn (fun x => |(u x)⁻¹| ^ p)
        (Metric.ball (0 : E) s) volume) :
    IntegrableOn (fun x => |(u x)⁻¹| ^ (moserChi d * p))
        (Metric.ball (0 : E) r) volume ∧
      (∫ x in Metric.ball (0 : E) r,
          |(u x)⁻¹| ^ (moserChi d * p) ∂volume) ^
          (1 / (moserChi d * p)) ≤
        ((C_MoserAnchor d / (s - r) ^ 2) *
            (A.1.Λ * (p / (1 + p)) ^ 2 + 1)) ^ (1 / p) *
          (∫ x in Metric.ball (0 : E) s, |(u x)⁻¹| ^ p ∂volume) ^ (1 / p) := by
  exact supersolution_preMoser_inverse hd A hp hr hrs hs1 hu_pos hsuper hpInt



end DeGiorgi
