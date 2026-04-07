import DeGiorgi.Common

/-!
# Chapter 02: Whole-Space Sobolev

This module develops the whole-space Sobolev inequality used later in the local
iteration arguments.

The main export is `DeGiorgi.sobolev_of_approx`.
-/

noncomputable section

open MeasureTheory Metric Filter Set Function
open scoped ENNReal NNReal Topology

namespace DeGiorgi

variable {d : ℕ} [NeZero d]

local notation "E" => EuclideanSpace ℝ (Fin d)

/-! ## Section 1: Sobolev Constant -/

/-- The Sobolev constant for the general `W^{1,p} -> L^{p*}` embedding,
extracted from Mathlib. -/
noncomputable def C_gns (d : ℕ) [NeZero d] (p : ℝ) : ℝ :=
  (MeasureTheory.SNormLESNormFDerivOfEqConst (F := ℝ)
    (μ := (volume : Measure (EuclideanSpace ℝ (Fin d)))) p : ℝ≥0)

theorem C_gns_nonneg (d : ℕ) [NeZero d] (p : ℝ) : 0 ≤ C_gns d p :=
  NNReal.coe_nonneg _

/-! ## Section 2: Exponent Arithmetic -/

private lemma sobolev_exp_pos {p : ℝ} (hp : 1 ≤ p) (hpd : p < (d : ℝ)) :
    0 < (d : ℝ) * p / ((d : ℝ) - p) := by
  apply div_pos
  · exact mul_pos (Nat.cast_pos.mpr (NeZero.pos d)) (by linarith)
  · linarith

/-- The key exponent relation: `(d*p/(d-p))⁻¹ = p⁻¹ - d⁻¹`. -/
private lemma sobolev_exponent_relation
    {p : ℝ} (hp : 0 < p) (hpd : p < (d : ℝ)) :
    ((d : ℝ) * p / ((d : ℝ) - p))⁻¹ = p⁻¹ - (d : ℝ)⁻¹ := by
  let _ := (inferInstance : NeZero d)
  have hd : (0 : ℝ) < d := lt_trans hp hpd
  rw [inv_div, inv_sub_inv (ne_of_gt hp) (ne_of_gt hd)]
  field_simp

/-- The Sobolev conjugate exponent as `NNReal`, with the relation Mathlib
needs. -/
private lemma sobolev_exponent_nnreal_relation
    {p : ℝ} (hp : 1 ≤ p) (hpd : p < (d : ℝ)) :
    let p_nn : ℝ≥0 := Real.toNNReal p
    let p'_nn : ℝ≥0 := Real.toNNReal ((d : ℝ) * p / ((d : ℝ) - p))
    (p'_nn : ℝ)⁻¹ = (p_nn : ℝ)⁻¹ - (Module.finrank ℝ E : ℝ)⁻¹ := by
  simp only [finrank_euclideanSpace_fin]
  rw [Real.coe_toNNReal _ (by linarith : 0 ≤ p),
    Real.coe_toNNReal _ (sobolev_exp_pos hp hpd).le]
  exact sobolev_exponent_relation (by linarith) hpd

/-! ## Section 3: GNS for Smooth Compactly Supported Functions -/

/-- Sobolev inequality for smooth compactly supported functions at general `p`.
Direct wrapper around Mathlib's `eLpNorm_le_eLpNorm_fderiv_of_eq`. -/
theorem sobolev_smooth {p : ℝ} (hp : 1 ≤ p) (hpd : p < (d : ℝ))
    {u : E → ℝ} (hu : ContDiff ℝ 1 u) (hu_cpt : HasCompactSupport u) :
    eLpNorm u (ENNReal.ofReal ((d : ℝ) * p / ((d : ℝ) - p))) volume ≤
    ENNReal.ofReal (C_gns d p) *
      eLpNorm (fderiv ℝ u) (ENNReal.ofReal p) volume := by
  set p_nn : ℝ≥0 := Real.toNNReal p with hp_nn_def
  set p'_nn : ℝ≥0 := Real.toNNReal ((d : ℝ) * p / ((d : ℝ) - p)) with hp'_nn_def
  have hp_nn_ge : (1 : ℝ≥0) ≤ p_nn := by
    rwa [← Real.toNNReal_one, Real.toNNReal_le_toNNReal_iff (by linarith)]
  have hd_pos : 0 < Module.finrank ℝ E := by
    rw [finrank_euclideanSpace_fin]
    exact NeZero.pos d
  have hrel : (p'_nn : ℝ)⁻¹ = (p_nn : ℝ)⁻¹ - (Module.finrank ℝ E : ℝ)⁻¹ :=
    sobolev_exponent_nnreal_relation hp hpd
  have hmain := MeasureTheory.eLpNorm_le_eLpNorm_fderiv_of_eq
    (F := ℝ) (μ := (volume : Measure E)) hu hu_cpt hp_nn_ge hd_pos hrel
  have hp_real : (p_nn : ℝ) = p := Real.coe_toNNReal p (by linarith)
  have hp_conv : (p_nn : ℝ≥0∞) = ENNReal.ofReal p := by
    simp [p_nn, ENNReal.ofReal, Real.toNNReal]
  have hp'_conv : (p'_nn : ℝ≥0∞) = ENNReal.ofReal ((d : ℝ) * p / ((d : ℝ) - p)) := by
    simp [p'_nn, ENNReal.ofReal, Real.toNNReal]
  rw [hp_conv, hp'_conv, hp_real] at hmain
  calc
    eLpNorm u (ENNReal.ofReal ((d : ℝ) * p / ((d : ℝ) - p))) volume
      ≤ ↑(MeasureTheory.SNormLESNormFDerivOfEqConst (F := ℝ) (μ := (volume : Measure E)) p) *
          eLpNorm (fderiv ℝ u) (ENNReal.ofReal p) volume := hmain
    _ = ENNReal.ofReal (C_gns d p) *
          eLpNorm (fderiv ℝ u) (ENNReal.ofReal p) volume := by
        congr 1
        simp only [C_gns]
        exact (ENNReal.ofReal_coe_nnreal).symm

/-! ## Section 4: Gradient norm comparison -/

omit [NeZero d] in
private theorem norm_fderiv_eq_norm_partials
    {f : E → ℝ} {x : E} :
    ‖fderiv ℝ f x‖ =
    ‖WithLp.toLp 2
      (fun i => (fderiv ℝ f x) (EuclideanSpace.single i 1))‖ := by
  let v : E := (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ f x)
  have hv :
      v = WithLp.toLp 2
        (fun i => (fderiv ℝ f x) (EuclideanSpace.single i 1)) := by
    have hv_map : (InnerProductSpace.toDual ℝ E) v = fderiv ℝ f x := by
      simp [v]
    ext i
    calc
      v i = inner ℝ v (EuclideanSpace.single i (1 : ℝ)) := by
        simpa using
          (EuclideanSpace.inner_single_right (i := i) (a := (1 : ℝ)) v).symm
      _ = ((InnerProductSpace.toDual ℝ E) v) (EuclideanSpace.single i (1 : ℝ)) := by
        rw [InnerProductSpace.toDual_apply_apply]
      _ = (fderiv ℝ f x) (EuclideanSpace.single i (1 : ℝ)) := by
        rw [hv_map]
      _ = (WithLp.toLp 2
            (fun j => (fderiv ℝ f x) (EuclideanSpace.single j 1))) i := by
        simp
  calc
    ‖fderiv ℝ f x‖ = ‖v‖ := by
      simp [v]
    _ = ‖WithLp.toLp 2
        (fun i => (fderiv ℝ f x) (EuclideanSpace.single i 1))‖ := by
          rw [hv]

/-! ## Section 5: Extension to `W₀^{1,p}` by Fatou -/

omit [NeZero d] in
private theorem aestronglyMeasurable_euclidean_of_components
    {G : E → E}
    (hG_comp : ∀ i : Fin d, AEStronglyMeasurable (fun x => G x i) volume) :
    AEStronglyMeasurable G volume := by
  have h_ofLp : AEMeasurable (fun x => (WithLp.ofLp (G x) : Fin d → ℝ)) volume := by
    rw [aemeasurable_pi_iff]
    intro i
    simpa using (hG_comp i).aemeasurable
  have h_ofLp_aesm :
      AEStronglyMeasurable (fun x => (WithLp.ofLp (G x) : Fin d → ℝ)) volume :=
    h_ofLp.aestronglyMeasurable
  have h_toLp_cont : Continuous (fun x : Fin d → ℝ => WithLp.toLp 2 x) := by
    simpa using (PiLp.continuous_toLp 2 (fun _ : Fin d => ℝ))
  exact h_toLp_cont.comp_aestronglyMeasurable h_ofLp_aesm

omit [NeZero d] in
private theorem tendstoInMeasure_of_eLpNorm_tendsto
    {q : ℝ≥0∞} (hq : q ≠ 0) {f : ℕ → E → ℝ} {g : E → ℝ}
    (hf : ∀ n, AEStronglyMeasurable (f n) volume)
    (hg : AEStronglyMeasurable g volume)
    (h : Tendsto (fun n => eLpNorm (fun x => f n x - g x) q volume) atTop (nhds 0)) :
    TendstoInMeasure volume f atTop g :=
  tendstoInMeasure_of_tendsto_eLpNorm hq hf hg h

omit [NeZero d] in
private theorem partialDiff_aestronglyMeasurable
    {φ : ℕ → E → ℝ} {G : E → E}
    (hφ_smooth : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (φ n))
    (hG_comp_aesm : ∀ i : Fin d, AEStronglyMeasurable (fun x => G x i) volume)
    (i : Fin d) (n : ℕ) :
    AEStronglyMeasurable
      (fun x => (fderiv ℝ (φ n) x) (EuclideanSpace.single i 1) - G x i) volume := by
  have hcomp_cont :
      Continuous (fun x => (fderiv ℝ (φ n) x) (EuclideanSpace.single i 1)) := by
    exact ((hφ_smooth n).continuous_fderiv (by simp)).clm_apply continuous_const
  exact hcomp_cont.aestronglyMeasurable.sub (hG_comp_aesm i)

omit [NeZero d] in
private theorem partialDiff_sum_tendsto_zero
    {p : ℝ} {φ : ℕ → E → ℝ} {G : E → E}
    (hφ_grad : ∀ i : Fin d, Tendsto
      (fun n => eLpNorm
        (fun x => (fderiv ℝ (φ n) x) (EuclideanSpace.single i 1) - G x i)
        (ENNReal.ofReal p) volume) atTop (nhds 0)) :
    Tendsto
      (fun n => ∑ i : Fin d,
        eLpNorm
          (fun x => (fderiv ℝ (φ n) x) (EuclideanSpace.single i 1) - G x i)
          (ENNReal.ofReal p) volume)
      atTop (nhds 0) := by
  have hpi :
      Tendsto
        (fun n : ℕ => fun i : Fin d =>
          eLpNorm
            (fun x => (fderiv ℝ (φ n) x) (EuclideanSpace.single i 1) - G x i)
            (ENNReal.ofReal p) volume)
        atTop (nhds (0 : Fin d → ℝ≥0∞)) := by
    rw [tendsto_pi_nhds]
    intro i
    simpa using hφ_grad i
  simpa using
    ((continuous_finset_sum Finset.univ fun i _ => continuous_apply i).tendsto
      (0 : Fin d → ℝ≥0∞)).comp hpi

omit [NeZero d] in
private theorem gradVec_eLpNorm_le_sum
    {p : ℝ} {φ : ℕ → E → ℝ} {G : E → E}
    (hp : 1 ≤ p)
    (hφ_smooth : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (φ n))
    (hG_comp_aesm : ∀ i : Fin d, AEStronglyMeasurable (fun x => G x i) volume)
    (n : ℕ) :
    eLpNorm
      (fun x =>
        WithLp.toLp 2 (fun i => (fderiv ℝ (φ n) x) (EuclideanSpace.single i 1)) - G x)
      (ENNReal.ofReal p) volume
      ≤
    ∑ i : Fin d,
      eLpNorm
        (fun x => (fderiv ℝ (φ n) x) (EuclideanSpace.single i 1) - G x i)
        (ENNReal.ofReal p) volume := by
  let δ : Fin d → E → ℝ :=
    fun i x => (fderiv ℝ (φ n) x) (EuclideanSpace.single i 1) - G x i
  have hδ_aesm : ∀ i : Fin d, AEStronglyMeasurable (δ i) volume := by
    intro i
    simpa [δ] using partialDiff_aestronglyMeasurable hφ_smooth hG_comp_aesm i n
  have hδnorm_eq :
      ∀ i : Fin d,
        eLpNorm (fun x => ‖δ i x‖) (ENNReal.ofReal p) volume =
          eLpNorm (δ i) (ENNReal.ofReal p) volume := by
    intro i
    simpa using (eLpNorm_norm (f := δ i) (p := ENNReal.ofReal p) (μ := volume))
  have hPointwise :
      ∀ᵐ x ∂volume,
        ‖WithLp.toLp 2 (fun i => (fderiv ℝ (φ n) x) (EuclideanSpace.single i 1)) - G x‖ ≤
          ∑ i : Fin d, ‖δ i x‖ := by
    filter_upwards with x
    have hsplit :
        WithLp.toLp 2 (fun i => (fderiv ℝ (φ n) x) (EuclideanSpace.single i 1)) - G x
          =
        ∑ i : Fin d,
          EuclideanSpace.single i (δ i x) := by
      ext i
      simp [δ, Finset.sum_apply]
    calc
      ‖WithLp.toLp 2 (fun i => (fderiv ℝ (φ n) x) (EuclideanSpace.single i 1)) - G x‖
          =
        ‖∑ i : Fin d, EuclideanSpace.single i (δ i x)‖ := by
          rw [hsplit]
      _ ≤ ∑ i : Fin d, ‖EuclideanSpace.single i (δ i x)‖ := by
          exact norm_sum_le _ _
      _ = ∑ i : Fin d, ‖δ i x‖ := by
          simp
  calc
    eLpNorm
        (fun x =>
          WithLp.toLp 2 (fun i => (fderiv ℝ (φ n) x) (EuclideanSpace.single i 1)) - G x)
        (ENNReal.ofReal p) volume
        ≤
      eLpNorm
        (fun x => ∑ i : Fin d, ‖δ i x‖)
        (ENNReal.ofReal p) volume := by
          exact eLpNorm_mono_ae_real hPointwise
    _ ≤ ∑ i : Fin d,
          eLpNorm (fun x => ‖δ i x‖) (ENNReal.ofReal p) volume := by
        have hp_enn : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
          rwa [← ENNReal.ofReal_one, ENNReal.ofReal_le_ofReal_iff (by linarith)]
        convert eLpNorm_sum_le (s := Finset.univ) (f := fun i => fun x => ‖δ i x‖)
          (fun i _ => (hδ_aesm i).norm) hp_enn using 1
        congr 1
        ext x
        simp [Finset.sum_apply]
    _ = ∑ i : Fin d,
          eLpNorm (δ i) (ENNReal.ofReal p) volume := by
        congr 1
        ext i
        exact hδnorm_eq i
    _ = _ := rfl

/-- The main whole-space Sobolev inequality for functions approximated by
smooth compactly supported functions. -/
theorem sobolev_of_approx {p : ℝ} (hp : 1 ≤ p) (hpd : p < (d : ℝ))
    {u : E → ℝ} {G : E → E}
    (hu_aesm : AEStronglyMeasurable u volume)
    (hG_comp_aesm : ∀ i : Fin d, AEStronglyMeasurable (fun x => G x i) volume)
    (φ : ℕ → E → ℝ)
    (hφ_smooth : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (φ n))
    (hφ_cpt : ∀ n, HasCompactSupport (φ n))
    (hφ_fun : Tendsto (fun n => eLpNorm (fun x => φ n x - u x) (ENNReal.ofReal p) volume)
      atTop (nhds 0))
    (hφ_grad : ∀ i : Fin d, Tendsto (fun n => eLpNorm
      (fun x => (fderiv ℝ (φ n) x) (EuclideanSpace.single i 1) - G x i)
      (ENNReal.ofReal p) volume) atTop (nhds 0)) :
    eLpNorm u (ENNReal.ofReal ((d : ℝ) * p / ((d : ℝ) - p))) volume ≤
    ENNReal.ofReal (C_gns d p) *
      eLpNorm (fun x => ‖G x‖) (ENNReal.ofReal p) volume := by
  set p_star := ENNReal.ofReal ((d : ℝ) * p / ((d : ℝ) - p)) with hp_star_def
  set p_enn := ENNReal.ofReal p with hp_enn_def
  set C := ENNReal.ofReal (C_gns d p) with hC_def
  have hGNS : ∀ n,
      eLpNorm (φ n) p_star volume ≤
      C * eLpNorm (fderiv ℝ (φ n)) p_enn volume :=
    fun n => sobolev_smooth hp hpd ((hφ_smooth n).of_le (by norm_cast)) (hφ_cpt n)
  have hφ_aesm : ∀ n, AEStronglyMeasurable (φ n) volume :=
    fun n => (hφ_smooth n).continuous.aestronglyMeasurable
  have hp_ne : p_enn ≠ 0 := by
    simp [p_enn]
    linarith
  have hp_one_enn : (1 : ℝ≥0∞) ≤ p_enn := by
    rw [hp_enn_def, ← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hp
  have hTIM : TendstoInMeasure volume φ atTop u :=
    tendstoInMeasure_of_eLpNorm_tendsto hp_ne hφ_aesm hu_aesm hφ_fun
  obtain ⟨σ, hσ_mono, hσ_ae⟩ := hTIM.exists_seq_tendsto_ae
  have hFatou : eLpNorm u p_star volume ≤
      atTop.liminf (fun n => eLpNorm (φ (σ n)) p_star volume) :=
    Lp.eLpNorm_lim_le_liminf_eLpNorm (fun n => hφ_aesm (σ n)) u hσ_ae
  let gradVec : ℕ → E → E := fun n x =>
    WithLp.toLp 2 (fun i => (fderiv ℝ (φ n) x) (EuclideanSpace.single i 1))
  have hBridge : ∀ n, (fun x => ‖fderiv ℝ (φ n) x‖) =ᵐ[volume]
      (fun x => ‖gradVec n x‖) := by
    intro n
    filter_upwards with x
    exact norm_fderiv_eq_norm_partials
  have hGNS' : ∀ n,
      eLpNorm (φ n) p_star volume ≤
      C * eLpNorm (fun x => ‖gradVec n x‖) p_enn volume := by
    intro n
    calc
      eLpNorm (φ n) p_star volume
        ≤ C * eLpNorm (fderiv ℝ (φ n)) p_enn volume := hGNS n
      _ = C * eLpNorm (fun x => ‖gradVec n x‖) p_enn volume := by
          congr 1
          rw [← eLpNorm_norm (fderiv ℝ (φ n))]
          exact eLpNorm_congr_ae (hBridge n)
  have hGradDiffTendstoZero : Tendsto
      (fun n => eLpNorm (fun x => gradVec n x - G x) p_enn volume) atTop (nhds 0) := by
    have hNormCompTendsto :=
      partialDiff_sum_tendsto_zero (p := p) (φ := φ) (G := G) hφ_grad
    have hBound :
        ∀ᶠ n in atTop,
          eLpNorm (fun x => gradVec n x - G x) p_enn volume ≤
            ∑ i : Fin d,
              eLpNorm
                (fun x => (fderiv ℝ (φ n) x) (EuclideanSpace.single i 1) - G x i)
                p_enn volume := by
      apply Eventually.of_forall
      intro n
      simpa [gradVec, hp_enn_def] using
        gradVec_eLpNorm_le_sum (p := p) (φ := φ) (G := G) hp hφ_smooth hG_comp_aesm n
    have hZeroLE :
        ∀ᶠ n in atTop, (0 : ℝ≥0∞) ≤ eLpNorm (fun x => gradVec n x - G x) p_enn volume :=
      Eventually.of_forall fun n => zero_le _
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
      (show Tendsto (fun _ : ℕ => (0 : ℝ≥0∞)) atTop (nhds 0) from tendsto_const_nhds)
      hNormCompTendsto
      hZeroLE
      hBound
  have hBound : atTop.liminf (fun n => eLpNorm (φ (σ n)) p_star volume) ≤
      C * eLpNorm (fun x => ‖G x‖) p_enn volume := by
    have hC_ne_top : C ≠ ⊤ := ENNReal.ofReal_ne_top
    have hGnorm_aesm : AEStronglyMeasurable (fun x => ‖G x‖) volume := by
      exact (aestronglyMeasurable_euclidean_of_components hG_comp_aesm).norm
    have hGradNormUpper :
        ∀ᶠ n in atTop,
          eLpNorm (fun x => ‖gradVec (σ n) x‖) p_enn volume ≤
            eLpNorm (fun x => ‖G x‖) p_enn volume +
              eLpNorm (fun x => gradVec (σ n) x - G x) p_enn volume := by
      apply Eventually.of_forall
      intro n
      have hGradNormAesm :
          AEStronglyMeasurable (fun x => ‖gradVec (σ n) x‖ - ‖G x‖) volume := by
        have hGradVecCont : Continuous (gradVec (σ n)) := by
          have h_toLp_cont : Continuous (fun x : Fin d → ℝ => WithLp.toLp 2 x) := by
            simpa using (PiLp.continuous_toLp 2 (fun _ : Fin d => ℝ))
          refine h_toLp_cont.comp ?_
          rw [continuous_pi_iff]
          intro i
          exact ((hφ_smooth (σ n)).continuous_fderiv (by simp)).clm_apply continuous_const
        have hGradVecAesm : AEStronglyMeasurable (gradVec (σ n)) volume :=
          hGradVecCont.aestronglyMeasurable
        exact hGradVecAesm.norm.sub hGnorm_aesm
      have hNormDiff :
          eLpNorm (fun x => ‖gradVec (σ n) x‖ - ‖G x‖) p_enn volume ≤
            eLpNorm (fun x => gradVec (σ n) x - G x) p_enn volume := by
        calc
          eLpNorm (fun x => ‖gradVec (σ n) x‖ - ‖G x‖) p_enn volume
              = eLpNorm (fun x => |‖gradVec (σ n) x‖ - ‖G x‖|) p_enn volume := by
                  simpa [Real.norm_eq_abs] using
                    (eLpNorm_norm
                      (f := fun x => ‖gradVec (σ n) x‖ - ‖G x‖)
                      (p := p_enn) (μ := volume)).symm
          _ ≤ eLpNorm (fun x => gradVec (σ n) x - G x) p_enn volume := by
                refine eLpNorm_mono_ae ?_
                filter_upwards with x
                simpa [Real.norm_eq_abs] using
                  (abs_norm_sub_norm_le (gradVec (σ n) x) (G x))
      calc
        eLpNorm (fun x => ‖gradVec (σ n) x‖) p_enn volume
            = eLpNorm (fun x => (‖gradVec (σ n) x‖ - ‖G x‖) + ‖G x‖) p_enn volume := by
                congr 1
                ext x
                ring
        _ ≤ eLpNorm (fun x => ‖gradVec (σ n) x‖ - ‖G x‖) p_enn volume +
              eLpNorm (fun x => ‖G x‖) p_enn volume := by
                exact eLpNorm_add_le hGradNormAesm hGnorm_aesm hp_one_enn
        _ ≤ eLpNorm (fun x => gradVec (σ n) x - G x) p_enn volume +
              eLpNorm (fun x => ‖G x‖) p_enn volume := by
                exact add_le_add hNormDiff le_rfl
        _ = eLpNorm (fun x => ‖G x‖) p_enn volume +
              eLpNorm (fun x => gradVec (σ n) x - G x) p_enn volume := by
                rw [add_comm]
    have hGradBound :
        atTop.liminf (fun n => C * eLpNorm (fun x => ‖gradVec (σ n) x‖) p_enn volume) ≤
          C * eLpNorm (fun x => ‖G x‖) p_enn volume := by
      have hDiffZeroSubseq :
          Tendsto
            (fun n => C * eLpNorm (fun x => gradVec (σ n) x - G x) p_enn volume)
            atTop (nhds 0) := by
          simpa using
            (ENNReal.Tendsto.const_mul
              (hGradDiffTendstoZero.comp hσ_mono.tendsto_atTop)
              (Or.inr hC_ne_top))
      have hu_grad :
          atTop.IsBoundedUnder (· ≥ ·)
            (fun n => C * eLpNorm (fun x => ‖gradVec (σ n) x‖) p_enn volume) :=
        isBoundedUnder_of_eventually_ge (a := 0) <| Eventually.of_forall fun _ => by simp
      have hv_rhs :
          atTop.IsCoboundedUnder (· ≥ ·)
            (fun n =>
              C * eLpNorm (fun x => ‖G x‖) p_enn volume +
                C * eLpNorm (fun x => gradVec (σ n) x - G x) p_enn volume) :=
        isCoboundedUnder_ge_of_eventually_le atTop <|
          Eventually.of_forall fun _ => le_top
      calc
        atTop.liminf (fun n => C * eLpNorm (fun x => ‖gradVec (σ n) x‖) p_enn volume)
            ≤ atTop.liminf
                (fun n =>
                  C * eLpNorm (fun x => ‖G x‖) p_enn volume +
                    C * eLpNorm (fun x => gradVec (σ n) x - G x) p_enn volume) := by
                  exact Filter.liminf_le_liminf
                    (hGradNormUpper.mono fun n hn => by
                      simpa [mul_add, add_comm, add_left_comm, add_assoc] using
                        mul_le_mul_right hn C)
                    hu_grad hv_rhs
        _ = atTop.liminf (fun _ : ℕ => C * eLpNorm (fun x => ‖G x‖) p_enn volume) := by
              simpa using
                ENNReal.liminf_add_of_right_tendsto_zero hDiffZeroSubseq
                  (fun _ : ℕ => C * eLpNorm (fun x => ‖G x‖) p_enn volume)
        _ = C * eLpNorm (fun x => ‖G x‖) p_enn volume := by
              simp
    have hu_phi :
        atTop.IsBoundedUnder (· ≥ ·) (fun n => eLpNorm (φ (σ n)) p_star volume) :=
      isBoundedUnder_of_eventually_ge (a := 0) <| Eventually.of_forall fun _ => by simp
    have hv_grad :
        atTop.IsCoboundedUnder (· ≥ ·)
          (fun n => C * eLpNorm (fun x => ‖gradVec (σ n) x‖) p_enn volume) :=
      isCoboundedUnder_ge_of_eventually_le atTop <|
        Eventually.of_forall fun _ => le_top
    calc
      atTop.liminf (fun n => eLpNorm (φ (σ n)) p_star volume)
          ≤ atTop.liminf (fun n => C * eLpNorm (fun x => ‖gradVec (σ n) x‖) p_enn volume) := by
            exact Filter.liminf_le_liminf
              (Eventually.of_forall fun n => hGNS' (σ n))
              hu_phi hv_grad
      _ ≤ C * eLpNorm (fun x => ‖G x‖) p_enn volume := hGradBound
  exact le_trans hFatou hBound

end DeGiorgi
