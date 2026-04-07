import DeGiorgi.MoserIteration.CutoffPrep.WitnessConstruction

/-!
# Moser Pre-Estimate

This module contains the cutoff-power energy closeout and the auxiliary
concentric-ball pre-estimate `moser_preMoser`.
-/

noncomputable section

open MeasureTheory Filter

namespace DeGiorgi

variable {d : ℕ} [NeZero d]

local notation "E" => AmbientSpace d

/-- Hard nonlinear core of the Moser pre-estimate: build a `W^{1,2}` witness for
the cutoff-power `η · (u_+)^(p/2)` and prove the exact energy bound. The
zero-trace conclusion is derived separately from compact support. -/
theorem moser_powerCutoff_memW1p_energy_of_subsolution_core
    (hd : 2 < (d : ℝ))
    (A : NormalizedEllipticCoeff d (Metric.ball (0 : E) 1))
    {u η : E → ℝ} {p s Cη : ℝ}
    (hp : 1 < p)
    (hs : 0 < s) (hs1 : s ≤ 1)
    (hsub : IsSubsolution A.1 u)
    (hpInt :
      IntegrableOn (fun x => |max (u x) 0| ^ p)
        (Metric.ball (0 : E) s) volume)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hη_nonneg : ∀ x, 0 ≤ η x)
    (hη_bound : ∀ x, |η x| ≤ 1)
    (hη_grad_bound : ∀ x, ‖fderiv ℝ η x‖ ≤ Cη)
    (hη_sub_ball : tsupport η ⊆ Metric.ball (0 : E) s) :
    ∃ hwv : MemW1pWitness 2 (moserPowerCutoff (d := d) η u p) (Metric.ball (0 : E) s),
      ∫ x in Metric.ball (0 : E) s, ‖hwv.weakGrad x‖ ^ 2 ∂volume ≤
        2 * Cη ^ 2 * (A.1.Λ * (p / (p - 1)) ^ 2 + 1) *
          ∫ x in Metric.ball (0 : E) s, |max (u x) 0| ^ p ∂volume := by
  exact moserPowerCutoff_memW1pWitness (d := d) hd A hp hs hs1 hsub hpInt hη hη_nonneg
    hη_bound hη_grad_bound hη_sub_ball

/-- Analytic core of the Moser pre-estimate: the cutoff-power
`η · (u_+)^(p/2)` belongs to `W₀^{1,2}` on the outer ball and satisfies the
exact energy bound needed for Sobolev. The only remaining nonlinear gap is the
construction of the underlying `W^{1,2}` witness and its energy bound. -/
theorem moser_powerCutoff_memW01p_energy_of_subsolution
    (hd : 2 < (d : ℝ))
    (A : NormalizedEllipticCoeff d (Metric.ball (0 : E) 1))
    {u η : E → ℝ} {p s Cη : ℝ}
    (hp : 1 < p)
    (hs : 0 < s) (hs1 : s ≤ 1)
    (hsub : IsSubsolution A.1 u)
    (hpInt :
      IntegrableOn (fun x => |max (u x) 0| ^ p)
        (Metric.ball (0 : E) s) volume)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hη_nonneg : ∀ x, 0 ≤ η x)
    (hη_bound : ∀ x, |η x| ≤ 1)
    (hη_grad_bound : ∀ x, ‖fderiv ℝ η x‖ ≤ Cη)
    (hη_sub_ball : tsupport η ⊆ Metric.ball (0 : E) s) :
    ∃ hwv : MemW1pWitness 2 (moserPowerCutoff (d := d) η u p) (Metric.ball (0 : E) s),
      MemW01p 2 (moserPowerCutoff (d := d) η u p) (Metric.ball (0 : E) s) ∧
      ∫ x in Metric.ball (0 : E) s, ‖hwv.weakGrad x‖ ^ 2 ∂volume ≤
        2 * Cη ^ 2 * (A.1.Λ * (p / (p - 1)) ^ 2 + 1) *
          ∫ x in Metric.ball (0 : E) s, |max (u x) 0| ^ p ∂volume := by
  let Ω : Set E := Metric.ball (0 : E) s
  let v : E → ℝ := moserPowerCutoff (d := d) η u p
  have hv_support : tsupport v ⊆ Ω :=
    moserPowerCutoff_tsupport_subset (d := d) (u := u) (η := η) (p := p) hη_sub_ball
  obtain ⟨hwv, henergy⟩ :=
    moser_powerCutoff_memW1p_energy_of_subsolution_core
      (d := d) hd A (u := u) (η := η) (p := p) (s := s) (Cη := Cη)
      hp hs hs1 hsub hpInt hη hη_nonneg hη_bound hη_grad_bound hη_sub_ball
  have hv_compact : HasCompactSupport v :=
    hasCompactSupport_of_tsupport_subset_ball hv_support
  have hv_memW1p_real : MemW1p (ENNReal.ofReal (2 : ℝ)) v Ω := by
    simpa [Ω] using hwv.memW1p
  have hvW01_real : MemW01p (ENNReal.ofReal (2 : ℝ)) v Ω := by
    exact memW01p_of_memW1p_of_tsupport_subset
      (d := d) Metric.isOpen_ball (p := (2 : ℝ)) (by norm_num) hv_memW1p_real hv_compact hv_support
  have hvW01 : MemW01p 2 v Ω := by
    simpa [Ω] using hvW01_real
  exact ⟨hwv, hvW01, henergy⟩

/-- Auxiliary concentric-ball estimate for the Moser iteration.

The representative upgrade to pointwise `sup` statements is deferred to
Chapter 07. -/
theorem moser_preMoser
    (hd : 2 < (d : ℝ))
    (A : NormalizedEllipticCoeff d (Metric.ball (0 : E) 1))
    {u : E → ℝ} {p r s : ℝ}
    (hp : 1 < p)
    (hr : 0 < r) (hrs : r < s) (hs1 : s ≤ 1)
    (hsub : IsSubsolution A.1 u)
    (hpInt :
      IntegrableOn (fun x => |max (u x) 0| ^ p)
        (Metric.ball (0 : E) s) volume) :
    IntegrableOn (fun x => |max (u x) 0| ^ (moserChi d * p))
        (Metric.ball (0 : E) r) volume ∧
      (∫ x in Metric.ball (0 : E) r,
          |max (u x) 0| ^ (moserChi d * p) ∂volume) ^
          (1 / (moserChi d * p)) ≤
        ((C_MoserAnchor d / (s - r) ^ 2) *
            (A.1.Λ * (p / (p - 1)) ^ 2 + 1)) ^ (1 / p) *
          (∫ x in Metric.ball (0 : E) s, |max (u x) 0| ^ p ∂volume) ^ (1 / p) := by
  let Ω : Set E := Metric.ball (0 : E) s
  let μ : Measure E := volume.restrict Ω
  let R : ℝ := (r + s) / 2
  let η : E → ℝ := (Classical.choose (Cutoff.exists (d := d) (0 : E) (r := r) (R := R) hr (by
    dsimp [R]
    linarith))).toFun
  let Cη : ℝ := 2 * (Mst : ℝ) * (s - r)⁻¹
  have hs : 0 < s := lt_trans hr hrs
  have hsr_pos : 0 < s - r := by linarith
  have hR : r < R := by
    dsimp [R]
    linarith
  have hR_lt_s : R < s := by
    dsimp [R]
    linarith
  let ηCut : Cutoff (x₀ := (0 : E)) r R := Classical.choose
    (Cutoff.exists (d := d) (0 : E) (r := r) (R := R) hr hR)
  have hη : ContDiff ℝ (⊤ : ℕ∞) η := by
    simpa [η, ηCut] using ηCut.smooth
  have hη_bound : ∀ x, |η x| ≤ 1 := by
    intro x
    rw [abs_of_nonneg (ηCut.nonneg x)]
    simpa [η, ηCut] using ηCut.le_one x
  have hη_eq_one : ∀ x ∈ Metric.ball (0 : E) r, η x = 1 := by
    intro x hx
    simpa [η, ηCut] using ηCut.eq_one x hx
  have hη_grad_bound : ∀ x, ‖fderiv ℝ η x‖ ≤ Cη := by
    intro x
    have hmid :
        ((((r + s) / 2 : ℝ) - r)) = (s - r) / 2 := by
      ring
    have h_inv : ((((r + s) / 2 : ℝ) - r)⁻¹) = 2 * (s - r)⁻¹ := by
      rw [hmid]
      field_simp [hsr_pos.ne']
    calc
      ‖fderiv ℝ η x‖ ≤ ↑Mst * ((((r + s) / 2 : ℝ) - r)⁻¹) := by
        simpa [η, ηCut, R] using ηCut.grad_bound x
      _ = 2 * (Mst : ℝ) * (s - r)⁻¹ := by
        rw [h_inv]
        ring
      _ = Cη := by
        rfl
  have hη_sub_ball : tsupport η ⊆ Ω := by
    intro x hx
    exact (Metric.closedBall_subset_ball hR_lt_s) (ηCut.support_subset hx)
  let v : E → ℝ := moserPowerCutoff (d := d) η u p
  have hv_support : tsupport v ⊆ Ω :=
    moserPowerCutoff_tsupport_subset (d := d) (u := u) (η := η) (p := p) hη_sub_ball
  obtain ⟨hwv, hvW01, henergy⟩ :=
    moser_powerCutoff_memW01p_energy_of_subsolution
      (d := d) hd A (u := u) (η := η) (p := p) (s := s) (Cη := Cη)
      hp hs hs1 hsub hpInt hη ηCut.nonneg hη_bound hη_grad_bound hη_sub_ball
  obtain ⟨hwv_raw, hSob_raw⟩ :=
    sobolev_prepare_on_ball (d := d) (v := v) hd hs hvW01 hv_support
  let hwvSob : MemW1pWitness (ENNReal.ofReal (2 : ℝ)) v Ω :=
    { memLp := by
        simpa [Ω] using hwv_raw.memLp
      weakGrad := hwv_raw.weakGrad
      weakGrad_component_memLp := by
        simpa [Ω] using hwv_raw.weakGrad_component_memLp
      isWeakGrad := by
        simpa [Ω] using hwv_raw.isWeakGrad }
  let hwvReal : MemW1pWitness (ENNReal.ofReal (2 : ℝ)) v Ω :=
    { memLp := by
        simpa [Ω] using hwv.memLp
      weakGrad := hwv.weakGrad
      weakGrad_component_memLp := by
        simpa [Ω] using hwv.weakGrad_component_memLp
      isWeakGrad := by
        simpa [Ω] using hwv.isWeakGrad }
  have hSob :
      eLpNorm v
          (ENNReal.ofReal ((d : ℝ) * 2 / ((d : ℝ) - 2))) μ ≤
        ENNReal.ofReal (C_gns d 2) *
          eLpNorm (fun x => ‖hwvSob.weakGrad x‖) 2 μ := by
    simpa [Ω, μ, hwvSob] using hSob_raw
  have hae_grad :
      hwvSob.weakGrad =ᵐ[μ] hwvReal.weakGrad := by
    simpa [μ, Ω] using
      (MemW1pWitness.ae_eq_p (d := d) Metric.isOpen_ball (p := (2 : ℝ)) (by norm_num) hwvSob hwvReal)
  have hgrad_sq_eq :
      ∫ x in Ω, ‖hwvSob.weakGrad x‖ ^ 2 ∂volume =
        ∫ x in Ω, ‖hwvReal.weakGrad x‖ ^ 2 ∂volume := by
    exact integral_congr_ae (hae_grad.fun_comp (fun z => ‖z‖ ^ 2))
  let qexp : ℝ := ((d : ℝ) * 2 / ((d : ℝ) - 2))
  let q := ENNReal.ofReal qexp
  have hq_pos : 0 < qexp := by
    have hd_pos : 0 < (d : ℝ) := by linarith
    have hd_sub_pos : 0 < (d : ℝ) - 2 := by linarith
    dsimp [qexp]
    exact div_pos (mul_pos hd_pos (by norm_num)) hd_sub_pos
  have hv_memLp_q : MemLp v q μ := by
    refine ⟨hwvSob.memLp.aestronglyMeasurable, ?_⟩
    have hgrad_lt_top :
        eLpNorm (fun x => ‖hwvSob.weakGrad x‖) 2 μ < ⊤ :=
      lt_top_iff_ne_top.mpr (by simpa using hwvSob.weakGrad_norm_memLp.eLpNorm_ne_top)
    have hrhs_lt_top :
        ENNReal.ofReal (C_gns d 2) *
          eLpNorm (fun x => ‖hwvSob.weakGrad x‖) 2 μ < ⊤ := by
      rw [ENNReal.mul_lt_top_iff]
      exact Or.inl ⟨by simp, hgrad_lt_top⟩
    exact lt_of_le_of_lt hSob hrhs_lt_top
  have hSob_real :
      MeasureTheory.lpNorm v q μ ≤
        (C_gns d 2) * MeasureTheory.lpNorm (fun x => ‖hwvSob.weakGrad x‖) 2 μ := by
    have hgrad_ne_top :
        eLpNorm (fun x => ‖hwvSob.weakGrad x‖) 2 μ ≠ ⊤ :=
      by simpa using hwvSob.weakGrad_norm_memLp.eLpNorm_ne_top
    have hrhs_ne_top :
        ENNReal.ofReal (C_gns d 2) *
            eLpNorm (fun x => ‖hwvSob.weakGrad x‖) 2 μ ≠ ⊤ :=
      ENNReal.mul_ne_top (by simp) hgrad_ne_top
    have hSob_toReal :
        (eLpNorm v q μ).toReal ≤
          (ENNReal.ofReal (C_gns d 2) *
            eLpNorm (fun x => ‖hwvSob.weakGrad x‖) 2 μ).toReal :=
      (ENNReal.toReal_le_toReal hv_memLp_q.eLpNorm_ne_top hrhs_ne_top).2 hSob
    have hC_toReal : (ENNReal.ofReal (C_gns d 2)).toReal = C_gns d 2 :=
      ENNReal.toReal_ofReal (C_gns_nonneg d 2)
    have hSob_toReal' := hSob_toReal
    rw [MeasureTheory.toReal_eLpNorm hv_memLp_q.aestronglyMeasurable,
      ENNReal.toReal_mul, MeasureTheory.toReal_eLpNorm
      hwvSob.weakGrad_norm_memLp.aestronglyMeasurable, hC_toReal] at hSob_toReal'
    exact hSob_toReal'
  have hgrad_lp :
      MeasureTheory.lpNorm (fun x => ‖hwvSob.weakGrad x‖) 2 μ =
        (∫ x in Ω, ‖hwvSob.weakGrad x‖ ^ 2 ∂volume) ^ (1 / (2 : ℝ)) := by
    simpa [μ, Ω] using
      (MeasureTheory.lpNorm_eq_integral_norm_rpow_toReal
        (μ := μ) (f := fun x => ‖hwvSob.weakGrad x‖)
        two_ne_zero ENNReal.ofNat_ne_top
        hwvSob.weakGrad_norm_memLp.aestronglyMeasurable)
  have hgrad_bound :
      MeasureTheory.lpNorm (fun x => ‖hwvSob.weakGrad x‖) 2 μ ≤
        (2 * Cη ^ 2 * (A.1.Λ * (p / (p - 1)) ^ 2 + 1) *
          ∫ x in Ω, |max (u x) 0| ^ p ∂volume) ^ (1 / (2 : ℝ)) := by
    rw [hgrad_lp, hgrad_sq_eq]
    have henergy_real :
        ∫ x in Ω, ‖hwvReal.weakGrad x‖ ^ 2 ∂volume ≤
          2 * Cη ^ 2 * (A.1.Λ * (p / (p - 1)) ^ 2 + 1) *
            ∫ x in Ω, |max (u x) 0| ^ p ∂volume := by
      simpa [Ω, hwvReal] using henergy
    have henergy_rhs_nonneg :
        0 ≤
          2 * Cη ^ 2 * (A.1.Λ * (p / (p - 1)) ^ 2 + 1) *
            ∫ x in Ω, |max (u x) 0| ^ p ∂volume := by
      have hInt_nonneg :
          0 ≤ ∫ x in Ω, |max (u x) 0| ^ p ∂volume := by
        refine integral_nonneg ?_
        intro x
        positivity
      have hcoeff_nonneg : 0 ≤ A.1.Λ * (p / (p - 1)) ^ 2 + 1 := by
        have hratio_sq_nonneg : 0 ≤ (p / (p - 1)) ^ 2 := by positivity
        have hmul_nonneg : 0 ≤ A.1.Λ * (p / (p - 1)) ^ 2 := by
          exact mul_nonneg A.1.Λ_nonneg hratio_sq_nonneg
        linarith
      positivity
    exact Real.rpow_le_rpow
      (by
        refine integral_nonneg ?_
        intro x
        positivity)
      henergy_real (by
        show 0 ≤ (1 / (2 : ℝ))
        norm_num)
  have hq_ne_zero : q ≠ 0 := by
    dsimp [q]
    rw [ENNReal.ofReal_eq_zero]
    linarith
  have hq_toReal : q.toReal = qexp := by
    simp [q, qexp, ENNReal.toReal_ofReal hq_pos.le]
  have hv_lp_eq :
      MeasureTheory.lpNorm v q μ =
        (∫ x in Ω, |v x| ^ qexp ∂volume) ^ (1 / qexp) := by
    rw [MeasureTheory.lpNorm_eq_integral_norm_rpow_toReal
      (μ := μ) (f := v)]
    · simp [μ, Ω, q, qexp, hq_toReal, Real.norm_eq_abs]
    · exact hq_ne_zero
    · exact ENNReal.ofReal_ne_top
    · exact hv_memLp_q.aestronglyMeasurable
  have hv_int :
      IntegrableOn (fun x => |v x| ^ qexp) Ω volume := by
    simpa [μ, Ω, q, qexp, hq_toReal, Real.norm_eq_abs] using
      hv_memLp_q.integrable_norm_rpow hq_ne_zero ENNReal.ofReal_ne_top
  have hpow_eq_on :
      ∀ x ∈ Metric.ball (0 : E) r,
        |v x| ^ qexp = |max (u x) 0| ^ (moserChi d * p) := by
    intro x hx
    have hηx : η x = 1 := hη_eq_one x hx
    have hqexp_eq : qexp = 2 * moserChi d := by
      dsimp [qexp, moserChi]
      field_simp
    have hvx : v x = |max (u x) 0| ^ (p / 2) := by
      simp [v, moserPowerCutoff, hηx]
    calc
      |v x| ^ qexp = |(|max (u x) 0| ^ (p / 2))| ^ qexp := by
        rw [hvx]
      _ = (|max (u x) 0| ^ (p / 2)) ^ qexp := by
        rw [abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
      _ = |max (u x) 0| ^ (moserChi d * p) := by
        rw [hqexp_eq, ← Real.rpow_mul]
        · ring_nf
        · positivity
  have hleft_int :
      IntegrableOn (fun x => |max (u x) 0| ^ (moserChi d * p))
        (Metric.ball (0 : E) r) volume := by
    refine (hv_int.mono_set (Metric.ball_subset_ball (le_of_lt hrs))).congr_fun ?_ measurableSet_ball
    intro x hx
    exact hpow_eq_on x hx
  have hleft_integral_le :
      ∫ x in Metric.ball (0 : E) r, |max (u x) 0| ^ (moserChi d * p) ∂volume ≤
        ∫ x in Ω, |v x| ^ qexp ∂volume := by
    have hmono :
        ∫ x in Metric.ball (0 : E) r, |v x| ^ qexp ∂volume ≤
          ∫ x in Ω, |v x| ^ qexp ∂volume := by
      exact setIntegral_mono_set hv_int
        (ae_of_all _ (by intro x; positivity))
        (ae_of_all _ (Metric.ball_subset_ball (le_of_lt hrs)))
    calc
      ∫ x in Metric.ball (0 : E) r, |max (u x) 0| ^ (moserChi d * p) ∂volume
          = ∫ x in Metric.ball (0 : E) r, |v x| ^ qexp ∂volume := by
              apply setIntegral_congr_fun measurableSet_ball
              intro x hx
              symm
              exact hpow_eq_on x hx
      _ ≤ ∫ x in Ω, |v x| ^ qexp ∂volume := hmono
  have hCη_sq :
      Cη ^ 2 = 4 * (Mst : ℝ) ^ 2 / (s - r) ^ 2 := by
    dsimp [Cη]
    field_simp [hsr_pos.ne']
    ring
  have hconst_bound :
      (C_gns d 2) ^ 2 * (2 * Cη ^ 2) ≤ C_MoserAnchor d / (s - r) ^ 2 := by
    rw [hCη_sq]
    have hanchor :=
      cutoff_sobolev_anchor_le_C_MoserAnchor (d := d)
    have hsr_sq_pos : 0 < (s - r) ^ 2 := by positivity
    have hrewrite :
        (C_gns d 2) ^ 2 * (2 * (4 * (Mst : ℝ) ^ 2 / (s - r) ^ 2)) =
          ((C_gns d 2) ^ 2 * (8 * (Mst : ℝ) ^ 2)) / (s - r) ^ 2 := by
      field_simp [hsr_pos.ne']
      ring
    rw [hrewrite]
    have hnum :
        (C_gns d 2) ^ 2 * (8 * (Mst : ℝ) ^ 2) ≤ C_MoserAnchor d := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using hanchor
    exact div_le_div_of_nonneg_right hnum (by positivity)
  have hcoeff_nonneg : 0 ≤ A.1.Λ * (p / (p - 1)) ^ 2 + 1 := by
    have hratio_sq_nonneg : 0 ≤ (p / (p - 1)) ^ 2 := by positivity
    have hmul_nonneg : 0 ≤ A.1.Λ * (p / (p - 1)) ^ 2 := by
      exact mul_nonneg A.1.Λ_nonneg hratio_sq_nonneg
    linarith
  have hIp_nonneg :
      0 ≤ ∫ x in Ω, |max (u x) 0| ^ p ∂volume := by
    refine integral_nonneg ?_
    intro x
    positivity
  have hcoeffInt_nonneg :
      0 ≤
        (A.1.Λ * (p / (p - 1)) ^ 2 + 1) *
          ∫ x in Ω, |max (u x) 0| ^ p ∂volume := by
    exact mul_nonneg hcoeff_nonneg hIp_nonneg
  have hbase_nonneg :
      0 ≤
        (C_gns d 2) ^ 2 * (2 * Cη ^ 2) *
          (A.1.Λ * (p / (p - 1)) ^ 2 + 1) *
            ∫ x in Ω, |max (u x) 0| ^ p ∂volume := by
    have hleft_nonneg : 0 ≤ (C_gns d 2) ^ 2 * (2 * Cη ^ 2) := by
      exact mul_nonneg (sq_nonneg (C_gns d 2)) (mul_nonneg (by norm_num) (sq_nonneg Cη))
    have hmid_nonneg :
        0 ≤ (C_gns d 2) ^ 2 * (2 * Cη ^ 2) * (A.1.Λ * (p / (p - 1)) ^ 2 + 1) := by
      exact mul_nonneg hleft_nonneg hcoeff_nonneg
    exact mul_nonneg hmid_nonneg hIp_nonneg
  have hbase_le :
      (C_gns d 2) ^ 2 * (2 * Cη ^ 2) *
          (A.1.Λ * (p / (p - 1)) ^ 2 + 1) *
            ∫ x in Ω, |max (u x) 0| ^ p ∂volume ≤
        (C_MoserAnchor d / (s - r) ^ 2) *
          (A.1.Λ * (p / (p - 1)) ^ 2 + 1) *
            ∫ x in Ω, |max (u x) 0| ^ p ∂volume := by
    have hmul :
        ((C_gns d 2) ^ 2 * (2 * Cη ^ 2)) *
            ((A.1.Λ * (p / (p - 1)) ^ 2 + 1) *
              ∫ x in Ω, |max (u x) 0| ^ p ∂volume) ≤
          (C_MoserAnchor d / (s - r) ^ 2) *
            ((A.1.Λ * (p / (p - 1)) ^ 2 + 1) *
              ∫ x in Ω, |max (u x) 0| ^ p ∂volume) := by
      exact mul_le_mul_of_nonneg_right hconst_bound hcoeffInt_nonneg
    simpa [mul_assoc] using hmul
  have hmain_lp :
      (∫ x in Metric.ball (0 : E) r,
          |max (u x) 0| ^ (moserChi d * p) ∂volume) ^
          (1 / (moserChi d * p)) ≤
        ((C_MoserAnchor d / (s - r) ^ 2) *
            (A.1.Λ * (p / (p - 1)) ^ 2 + 1) *
            ∫ x in Ω, |max (u x) 0| ^ p ∂volume) ^ (1 / p) := by
    have hleft_nonneg :
        0 ≤ ∫ x in Metric.ball (0 : E) r,
          |max (u x) 0| ^ (moserChi d * p) ∂volume := by
      refine integral_nonneg ?_
      intro x
      positivity
    have hright_nonneg :
        0 ≤ ∫ x in Ω, |v x| ^ qexp ∂volume := by
      refine integral_nonneg ?_
      intro x
      positivity
    have hgrad_rhs_nonneg :
        0 ≤
          (2 * Cη ^ 2 * (A.1.Λ * (p / (p - 1)) ^ 2 + 1) *
            ∫ x in Ω, |max (u x) 0| ^ p ∂volume) ^ (1 / (2 : ℝ)) := by
      exact Real.rpow_nonneg
        (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg Cη)) hcoeff_nonneg) hIp_nonneg) _
    have hqexp_mul :
        (1 / qexp : ℝ) * (2 / p) = 1 / (moserChi d * p) := by
      dsimp [qexp, moserChi]
      field_simp
    have hhalf_mul :
        (1 / (2 : ℝ)) * (2 / p) = 1 / p := by
      field_simp [hp.ne']
    have hclose_exp_nonneg : 0 ≤ 1 / (moserChi d * p) := by
      have hchi_p_pos : 0 < moserChi d * p := by
        exact mul_pos (moserChi_pos (d := d) hd) (lt_trans zero_lt_one hp)
      exact one_div_nonneg.mpr hchi_p_pos.le
    calc
      (∫ x in Metric.ball (0 : E) r,
          |max (u x) 0| ^ (moserChi d * p) ∂volume) ^
          (1 / (moserChi d * p))
          ≤ (∫ x in Ω, |v x| ^ qexp ∂volume) ^ (1 / (moserChi d * p)) := by
              exact Real.rpow_le_rpow hleft_nonneg hleft_integral_le hclose_exp_nonneg
      _ = ((∫ x in Ω, |v x| ^ qexp ∂volume) ^ (1 / qexp)) ^ (2 / p) := by
            rw [← Real.rpow_mul hright_nonneg, hqexp_mul]
      _ = (MeasureTheory.lpNorm v q μ) ^ (2 / p) := by
            rw [hv_lp_eq]
      _ ≤ ((C_gns d 2) * MeasureTheory.lpNorm (fun x => ‖hwvSob.weakGrad x‖) 2 μ) ^ (2 / p) := by
            exact Real.rpow_le_rpow MeasureTheory.lpNorm_nonneg hSob_real (by positivity)
      _ ≤ ((C_gns d 2) *
            (2 * Cη ^ 2 * (A.1.Λ * (p / (p - 1)) ^ 2 + 1) *
              ∫ x in Ω, |max (u x) 0| ^ p ∂volume) ^ (1 / (2 : ℝ))) ^ (2 / p) := by
            exact Real.rpow_le_rpow
              (mul_nonneg (C_gns_nonneg d 2) (MeasureTheory.lpNorm_nonneg))
              (mul_le_mul_of_nonneg_left hgrad_bound (C_gns_nonneg d 2))
              (by positivity)
      _ = ((C_gns d 2) ^ 2 * (2 * Cη ^ 2) *
            (A.1.Λ * (p / (p - 1)) ^ 2 + 1) *
            ∫ x in Ω, |max (u x) 0| ^ p ∂volume) ^ (1 / p) := by
            have hinner_nonneg :
                0 ≤
                  2 * Cη ^ 2 * (A.1.Λ * (p / (p - 1)) ^ 2 + 1) *
                    ∫ x in Ω, |max (u x) 0| ^ p ∂volume := by
              exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg Cη)) hcoeff_nonneg) hIp_nonneg
            calc
              ((C_gns d 2) *
                  (2 * Cη ^ 2 * (A.1.Λ * (p / (p - 1)) ^ 2 + 1) *
                    ∫ x in Ω, |max (u x) 0| ^ p ∂volume) ^ (1 / (2 : ℝ))) ^ (2 / p)
                  = (C_gns d 2) ^ (2 / p) *
                      ((2 * Cη ^ 2 * (A.1.Λ * (p / (p - 1)) ^ 2 + 1) *
                        ∫ x in Ω, |max (u x) 0| ^ p ∂volume) ^ (1 / (2 : ℝ))) ^ (2 / p) := by
                          rw [Real.mul_rpow (C_gns_nonneg d 2) hgrad_rhs_nonneg]
              _ = ((C_gns d 2) ^ 2) ^ (1 / p) *
                    (2 * Cη ^ 2 * (A.1.Λ * (p / (p - 1)) ^ 2 + 1) *
                      ∫ x in Ω, |max (u x) 0| ^ p ∂volume) ^ (1 / p) := by
                        congr 1
                        · have htwo_div :
                              (2 / p : ℝ) = 2 * (1 / p) := by
                            field_simp [hp.ne']
                          rw [htwo_div]
                          simpa using (Real.rpow_mul (C_gns_nonneg d 2) 2 (1 / p))
                        · rw [← Real.rpow_mul hinner_nonneg, hhalf_mul]
              _ = (((C_gns d 2) ^ 2) *
                    (2 * Cη ^ 2 * (A.1.Λ * (p / (p - 1)) ^ 2 + 1) *
                      ∫ x in Ω, |max (u x) 0| ^ p ∂volume)) ^ (1 / p) := by
                        symm
                        rw [Real.mul_rpow (sq_nonneg (C_gns d 2)) hinner_nonneg]
              _ = ((C_gns d 2) ^ 2 * (2 * Cη ^ 2) *
                    (A.1.Λ * (p / (p - 1)) ^ 2 + 1) *
                    ∫ x in Ω, |max (u x) 0| ^ p ∂volume) ^ (1 / p) := by
                        congr 1
                        ring
      _ ≤ ((C_MoserAnchor d / (s - r) ^ 2) *
            (A.1.Λ * (p / (p - 1)) ^ 2 + 1) *
            ∫ x in Ω, |max (u x) 0| ^ p ∂volume) ^ (1 / p) := by
            exact Real.rpow_le_rpow hbase_nonneg hbase_le (by positivity)
  refine ⟨hleft_int, ?_⟩
  have hsplit_nonneg :
      0 ≤
        ((C_MoserAnchor d / (s - r) ^ 2) *
            (A.1.Λ * (p / (p - 1)) ^ 2 + 1)) := by
    have hfactor_nonneg : 0 ≤ C_MoserAnchor d / (s - r) ^ 2 := by
      have hanchor_nonneg : 0 ≤ C_MoserAnchor d := by
        exact le_trans (by norm_num : (0 : ℝ) ≤ 1) (one_le_C_MoserAnchor (d := d))
      exact div_nonneg hanchor_nonneg (by positivity)
    exact mul_nonneg hfactor_nonneg hcoeff_nonneg
  calc
    (∫ x in Metric.ball (0 : E) r,
        |max (u x) 0| ^ (moserChi d * p) ∂volume) ^
        (1 / (moserChi d * p))
        ≤ ((C_MoserAnchor d / (s - r) ^ 2) *
            (A.1.Λ * (p / (p - 1)) ^ 2 + 1) *
            ∫ x in Ω, |max (u x) 0| ^ p ∂volume) ^ (1 / p) := hmain_lp
    _ = ((C_MoserAnchor d / (s - r) ^ 2) *
            (A.1.Λ * (p / (p - 1)) ^ 2 + 1)) ^ (1 / p) *
          (∫ x in Ω, |max (u x) 0| ^ p ∂volume) ^ (1 / p) := by
            rw [Real.mul_rpow hsplit_nonneg hIp_nonneg]
    _ = ((C_MoserAnchor d / (s - r) ^ 2) *
            (A.1.Λ * (p / (p - 1)) ^ 2 + 1)) ^ (1 / p) *
          (∫ x in Metric.ball (0 : E) s, |max (u x) 0| ^ p ∂volume) ^ (1 / p) := by
            rfl

end DeGiorgi
