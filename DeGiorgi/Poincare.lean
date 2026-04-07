import DeGiorgi.Common
import DeGiorgi.WholeSpaceSobolev

noncomputable section

open MeasureTheory Metric Filter Set Function
open scoped ENNReal NNReal Topology

namespace DeGiorgi

variable {d : ℕ} [NeZero d]

local notation "E" => EuclideanSpace ℝ (Fin d)

noncomputable def C_poinc_val (d : ℕ) : ℝ :=
  2 ^ (d + 1) * d

omit [NeZero d] in
theorem C_poinc_val_pos (hd : 0 < d) : 0 < C_poinc_val d := by
  unfold C_poinc_val
  positivity

/-- Pointwise Euclidean norm of the classical gradient of a smooth scalar
function, written in coordinates. This matches the weak-gradient norm used in
the Sobolev witness layer for smooth functions. -/
noncomputable def smoothGradNorm (u : E → ℝ) : E → ℝ :=
  fun x => ‖WithLp.toLp 2 (fun i => (fderiv ℝ u x) (EuclideanSpace.single i 1))‖

omit [NeZero d] in
theorem norm_fderiv_eq_smoothGradNorm
    {u : E → ℝ} {x : E} :
    ‖fderiv ℝ u x‖ = smoothGradNorm u x := by
  let v : E := (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ u x)
  have hv :
      v = WithLp.toLp 2
        (fun i => (fderiv ℝ u x) (EuclideanSpace.single i 1)) := by
    have hv_map : (InnerProductSpace.toDual ℝ E) v = fderiv ℝ u x := by
      simp [v]
    ext i
    calc
      v i = inner ℝ v (EuclideanSpace.single i (1 : ℝ)) := by
        simpa using
          (EuclideanSpace.inner_single_right (i := i) (a := (1 : ℝ)) v).symm
      _ = ((InnerProductSpace.toDual ℝ E) v) (EuclideanSpace.single i (1 : ℝ)) := by
        rw [InnerProductSpace.toDual_apply_apply]
      _ = (fderiv ℝ u x) (EuclideanSpace.single i (1 : ℝ)) := by
        rw [hv_map]
      _ = (WithLp.toLp 2
            (fun j => (fderiv ℝ u x) (EuclideanSpace.single j 1))) i := by
        simp
  calc
    ‖fderiv ℝ u x‖ = ‖v‖ := by
      change ‖fderiv ℝ u x‖ = ‖(InnerProductSpace.toDual ℝ E).symm (fderiv ℝ u x)‖
      exact (((InnerProductSpace.toDual ℝ E).symm.norm_map
        (fderiv ℝ u x))).symm
    _ = smoothGradNorm u x := by
      simp [smoothGradNorm, hv]

omit [NeZero d] in
theorem smoothGradNorm_eq_zero_of_notMem_tsupport
    {u : E → ℝ} {x : E} (hx : x ∉ tsupport u) :
    smoothGradNorm u x = 0 := by
  rw [smoothGradNorm]
  have hfderiv_zero : fderiv ℝ u x = 0 :=
    fderiv_of_notMem_tsupport (𝕜 := ℝ) (f := u) hx
  have hzero : (fun i : Fin d => (0 : ℝ)) = 0 := by
    ext i
    simp
  simp [hfderiv_zero, hzero]

omit [NeZero d] in
theorem support_smoothGradNorm_subset_tsupport
    {u : E → ℝ} :
    Function.support (smoothGradNorm u) ⊆ tsupport u := by
  refine Function.support_subset_iff'.2 ?_
  intro x hx
  exact smoothGradNorm_eq_zero_of_notMem_tsupport hx

omit [NeZero d] in
theorem smoothCompactSupport_L2_bound_on_bounded_ge_two
    {Ω : Set E} (hd : 2 ≤ d) (hΩ_bdd : Bornology.IsBounded Ω) :
    ∃ C : ℝ≥0∞, C < ∞ ∧
      ∀ {u : E → ℝ}, ContDiff ℝ (⊤ : ℕ∞) u → HasCompactSupport u → tsupport u ⊆ Ω →
        eLpNorm u 2 (volume.restrict Ω) ≤
          C * eLpNorm (smoothGradNorm u) 2 (volume.restrict Ω) := by
  obtain ⟨R, hR_pos, hΩ_sub⟩ := hΩ_bdd.subset_closedBall_lt (0 : ℝ) (0 : E)
  let s : Set E := Metric.closedBall (0 : E) R
  have hs_bdd : Bornology.IsBounded s := Metric.isBounded_closedBall
  have hs_finite : volume s < ∞ := measure_closedBall_lt_top
  by_cases hd_eq_two : d = 2
  · let Csob : ℝ≥0 := MeasureTheory.eLpNormLESNormFDerivOfLeConst ℝ volume s 1 2
    let C : ℝ≥0∞ := (Csob : ℝ≥0∞) * (volume s) ^ (1 / (1 : ℝ) - 1 / (2 : ℝ))
    refine ⟨C, ?_, ?_⟩
    · dsimp [C]
      exact ENNReal.mul_lt_top ENNReal.coe_lt_top <|
        ENNReal.rpow_lt_top_of_nonneg (by positivity) hs_finite.ne
    · intro u hu hu_cpt hu_sub
      have hu1 : ContDiff ℝ 1 u := hu.of_le (by norm_cast)
      have hu_support_sub : Function.support u ⊆ Ω := subset_closure.trans hu_sub
      have hu_support_sub_s : Function.support u ⊆ s := hu_support_sub.trans hΩ_sub
      have hgrad_support_sub : Function.support (smoothGradNorm u) ⊆ Ω :=
        support_smoothGradNorm_subset_tsupport.trans hu_sub
      have hgrad_support_sub_s : Function.support (smoothGradNorm u) ⊆ s :=
        hgrad_support_sub.trans hΩ_sub
      have hgrad_cont : Continuous (smoothGradNorm u) := by
        have hcont_fderiv : Continuous (fderiv ℝ u) :=
          hu.continuous_fderiv (by simp)
        have hsmooth_eq : smoothGradNorm u = fun x => ‖fderiv ℝ u x‖ := by
          ext x
          exact (norm_fderiv_eq_smoothGradNorm (u := u) (x := x)).symm
        rw [hsmooth_eq]
        exact continuous_norm.comp hcont_fderiv
      have hu_eq_full :
          eLpNorm u 2 (volume.restrict Ω) = eLpNorm u 2 volume := by
        rw [eLpNorm_restrict_eq_of_support_subset hu_support_sub]
      have hgrad_eq_full :
          eLpNorm (smoothGradNorm u) 2 (volume.restrict Ω) =
            eLpNorm (smoothGradNorm u) 2 volume := by
        rw [eLpNorm_restrict_eq_of_support_subset hgrad_support_sub]
      have hgrad_eq_s_one :
          eLpNorm (smoothGradNorm u) (ENNReal.ofReal 1) (volume.restrict s) =
            eLpNorm (smoothGradNorm u) (ENNReal.ofReal 1) volume := by
        rw [eLpNorm_restrict_eq_of_support_subset hgrad_support_sub_s]
      have hgrad_eq_s_two :
          eLpNorm (smoothGradNorm u) 2 (volume.restrict s) =
            eLpNorm (smoothGradNorm u) 2 volume := by
        rw [eLpNorm_restrict_eq_of_support_subset hgrad_support_sub_s]
      have hgrad_aesm_s :
          AEStronglyMeasurable (smoothGradNorm u) (volume.restrict s) :=
        hgrad_cont.aestronglyMeasurable
      have hsobolev :
        eLpNorm u 2 volume ≤
          (Csob : ℝ≥0∞) * eLpNorm (fderiv ℝ u) 1 volume := by
        have h2p : (1 : ℝ≥0) < Module.finrank ℝ E := by
          rw [finrank_euclideanSpace_fin, hd_eq_two]
          norm_num
        have hpq :
            ((1 : ℝ≥0) : ℝ)⁻¹ - (Module.finrank ℝ E : ℝ)⁻¹ ≤
              ((2 : ℝ≥0) : ℝ)⁻¹ := by
          rw [finrank_euclideanSpace_fin, hd_eq_two]
          norm_num
        simpa [Csob] using
          (MeasureTheory.eLpNorm_le_eLpNorm_fderiv_of_le
            (μ := volume) (F := ℝ) (u := u) (s := s) hu1 hu_support_sub_s
            (p := (1 : ℝ≥0)) (q := (2 : ℝ≥0)) (by norm_num) h2p hpq hs_bdd)
      have hgrad_eq_one :
          eLpNorm (fderiv ℝ u) 1 volume =
            eLpNorm (smoothGradNorm u) 1 volume := by
        calc
          eLpNorm (fderiv ℝ u) 1 volume
              = eLpNorm (fun x => ‖fderiv ℝ u x‖) 1 volume := by
                  exact (eLpNorm_norm (f := fderiv ℝ u) (p := (1 : ℝ≥0∞)) (μ := volume)).symm
          _ = eLpNorm (smoothGradNorm u) 1 volume := by
                exact eLpNorm_congr_ae (Eventually.of_forall fun x =>
                  norm_fderiv_eq_smoothGradNorm (u := u) (x := x))
      have hsobolev' :
        eLpNorm u 2 volume ≤
          (Csob : ℝ≥0∞) * eLpNorm (smoothGradNorm u) 1 volume := by
        rwa [hgrad_eq_one] at hsobolev
      have hcompare :
        eLpNorm (smoothGradNorm u) 1 (volume.restrict s) ≤
          eLpNorm (smoothGradNorm u) 2 (volume.restrict s) *
            (volume s) ^ (1 / (1 : ℝ) - 1 / (2 : ℝ)) := by
        simpa [s, Measure.restrict_apply_univ] using
          (eLpNorm_le_eLpNorm_mul_rpow_measure_univ
            (μ := volume.restrict s) (f := smoothGradNorm u)
            (p := (1 : ℝ≥0∞)) (q := (2 : ℝ≥0∞)) (by norm_num) hgrad_aesm_s)
      rw [hu_eq_full, hgrad_eq_full]
      calc
        eLpNorm u 2 volume
            ≤ (Csob : ℝ≥0∞) * eLpNorm (smoothGradNorm u) 1 volume := hsobolev'
        _ = (Csob : ℝ≥0∞) * eLpNorm (smoothGradNorm u) 1 (volume.restrict s) := by
              congr 1
              simpa using hgrad_eq_s_one.symm
        _ ≤ (Csob : ℝ≥0∞) *
              (eLpNorm (smoothGradNorm u) 2 (volume.restrict s) *
                (volume s) ^ (1 / (1 : ℝ) - 1 / (2 : ℝ))) := by
              gcongr
        _ = C * eLpNorm (smoothGradNorm u) 2 volume := by
              rw [hgrad_eq_s_two]
              dsimp [C]
              rw [mul_assoc, mul_comm (eLpNorm (smoothGradNorm u) 2 volume) ((volume s) ^ _)]
  · have hne : 2 ≠ d := by
      intro h
      exact hd_eq_two h.symm
    have hd_gt_two : 2 < d := lt_of_le_of_ne hd hne
    let Csob : ℝ≥0 := MeasureTheory.eLpNormLESNormFDerivOfLeConst ℝ volume s 2 2
    let C : ℝ≥0∞ := Csob
    refine ⟨C, ?_, ?_⟩
    · dsimp [C]
      exact ENNReal.coe_lt_top
    · intro u hu hu_cpt hu_sub
      have hu1 : ContDiff ℝ 1 u := hu.of_le (by norm_cast)
      have hu_support_sub : Function.support u ⊆ Ω := subset_closure.trans hu_sub
      have hu_support_sub_s : Function.support u ⊆ s := hu_support_sub.trans hΩ_sub
      have hgrad_support_sub : Function.support (smoothGradNorm u) ⊆ Ω :=
        support_smoothGradNorm_subset_tsupport.trans hu_sub
      have hu_eq_full :
          eLpNorm u 2 (volume.restrict Ω) = eLpNorm u 2 volume := by
        rw [eLpNorm_restrict_eq_of_support_subset hu_support_sub]
      have hgrad_eq_full :
          eLpNorm (smoothGradNorm u) 2 (volume.restrict Ω) =
            eLpNorm (smoothGradNorm u) 2 volume := by
        rw [eLpNorm_restrict_eq_of_support_subset hgrad_support_sub]
      have hsobolev :
        eLpNorm u 2 volume ≤
          (Csob : ℝ≥0∞) * eLpNorm (fderiv ℝ u) 2 volume := by
        have h2p : (2 : ℝ≥0) < Module.finrank ℝ E := by
          rw [finrank_euclideanSpace_fin]
          exact_mod_cast hd_gt_two
        simpa [Csob] using
          (MeasureTheory.eLpNorm_le_eLpNorm_fderiv
            (μ := volume) (F := ℝ) (u := u) (s := s) hu1 hu_support_sub_s
            (p := (2 : ℝ≥0)) (by norm_num) h2p hs_bdd)
      have hgrad_eq_two :
          eLpNorm (fderiv ℝ u) 2 volume =
            eLpNorm (smoothGradNorm u) 2 volume := by
        calc
          eLpNorm (fderiv ℝ u) 2 volume
              = eLpNorm (fun x => ‖fderiv ℝ u x‖) 2 volume := by
                  exact (eLpNorm_norm (f := fderiv ℝ u) (p := (2 : ℝ≥0∞)) (μ := volume)).symm
          _ = eLpNorm (smoothGradNorm u) 2 volume := by
                exact eLpNorm_congr_ae (Eventually.of_forall fun x =>
                  norm_fderiv_eq_smoothGradNorm (u := u) (x := x))
      have hsobolev' :
        eLpNorm u 2 volume ≤
          (Csob : ℝ≥0∞) * eLpNorm (smoothGradNorm u) 2 volume := by
        rwa [hgrad_eq_two] at hsobolev
      rw [hu_eq_full, hgrad_eq_full]
      calc
        eLpNorm u 2 volume
            ≤ (Csob : ℝ≥0∞) * eLpNorm (smoothGradNorm u) 2 volume := hsobolev'
        _ = C * eLpNorm (smoothGradNorm u) 2 volume := by
              rfl

set_option maxHeartbeats 400000 in
omit [NeZero d] in
private lemma indicator_integrable_on_sphere_prod
    {R : ℝ} {F : E → ℝ} (hF : IntegrableOn F (Metric.ball (0 : E) R) volume) :
    Integrable
      (fun p : Metric.sphere (0 : E) 1 × Set.Ioi (0 : ℝ) =>
        (Metric.ball (0 : E) R).indicator F (p.2.1 • (p.1 : E)))
      ((volume : Measure E).toSphere.prod
        (Measure.volumeIoiPow (Module.finrank ℝ E - 1))) := by
  set σ := (volume : Measure E).toSphere
  set ρ := Measure.volumeIoiPow (Module.finrank ℝ E - 1)
  set G := (Metric.ball (0 : E) R).indicator F
  have hmp := (volume : Measure E).measurePreserving_homeomorphUnitSphereProd
  have hemb := (homeomorphUnitSphereProd E).measurableEmbedding
  rw [← hmp.integrable_comp_emb hemb]
  have hcomp : ((fun p : Metric.sphere (0 : E) 1 × Set.Ioi (0 : ℝ) =>
      G (p.2.1 • (p.1 : E))) ∘ homeomorphUnitSphereProd E) = G ∘ Subtype.val := by
    funext ⟨z, hz⟩
    simp only [Function.comp_apply, homeomorphUnitSphereProd_apply_snd_coe,
      homeomorphUnitSphereProd_apply_fst_coe]
    show G (‖z‖ • (‖z‖⁻¹ • z)) = G z
    rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr (Set.mem_compl_singleton_iff.mp hz)),
      one_smul]
  rw [hcomp, ← integrableOn_iff_comap_subtypeVal (measurableSet_singleton _).compl]
  have hG_int : Integrable G volume :=
    (integrable_indicator_iff measurableSet_ball).mpr hF
  exact hG_int.integrableOn

theorem sphere_radial_integral_ball
    {R : ℝ} (_hR : 0 < R) {F : E → ℝ}
    (hF : IntegrableOn F (Metric.ball (0 : E) R) volume) :
    ∫ z in Metric.ball (0 : E) R, F z ∂volume =
    ∫ ω in Set.univ,
      (∫ r in Set.Ioo (0 : ℝ) R, r ^ (d - 1 : ℕ) • F (r • (ω : E)))
      ∂(volume : Measure E).toSphere := by
  set G : E → ℝ := (Metric.ball (0 : E) R).indicator F
  have hstep1 : ∫ z in Metric.ball (0 : E) R, F z ∂volume = ∫ z, G z ∂volume := by
    simp [G, integral_indicator measurableSet_ball]
  have hstep1' : ∫ z, G z ∂volume =
      ∫ z : ({(0 : E)}ᶜ : Set E), G z ∂((volume : Measure E).comap (↑)) := by
    rw [integral_subtype_comap (measurableSet_singleton _).compl,
      restrict_compl_singleton]
  have hmp := (volume : Measure E).measurePreserving_homeomorphUnitSphereProd
  have hemb := (homeomorphUnitSphereProd E).measurableEmbedding
  have hstep2 :
      ∫ z : ({(0 : E)}ᶜ : Set E), G z ∂((volume : Measure E).comap (↑)) =
      ∫ p : Metric.sphere (0 : E) 1 × Set.Ioi (0 : ℝ),
        G (p.2.1 • (p.1 : E))
        ∂(volume : Measure E).toSphere.prod (Measure.volumeIoiPow (Module.finrank ℝ E - 1)) := by
    convert hmp.integral_comp hemb (fun p => G (p.2.1 • (p.1 : E))) using 1
    congr 1
    ext ⟨z, hz⟩
    simp [homeomorphUnitSphereProd, homeomorphSphereProd, Set.mem_compl_iff,
      Set.mem_singleton_iff] at hz ⊢
    congr 1
    have hne : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
    rw [smul_smul, mul_inv_cancel₀ hne, one_smul]
  have hG_simp : ∀ (ω : Metric.sphere (0 : E) 1) (r : Set.Ioi (0 : ℝ)),
      G (r.1 • (ω : E)) = if r.1 < R then F (r.1 • (ω : E)) else 0 := by
    intro ⟨ω, hω⟩ ⟨r, hr⟩
    simp only [G, Set.indicator, Metric.mem_ball, dist_zero_right]
    have hω_norm : ‖ω‖ = 1 := by simpa using hω
    rw [norm_smul, Real.norm_of_nonneg (le_of_lt hr), hω_norm, mul_one]
  rw [hstep1, hstep1', hstep2]
  set σ := (volume : Measure E).toSphere
  set n := Module.finrank ℝ E - 1
  set ρ := Measure.volumeIoiPow n
  have hInteg : Integrable (fun p : Metric.sphere (0 : E) 1 × Set.Ioi (0 : ℝ) =>
      G (p.2.1 • (p.1 : E))) (σ.prod ρ) :=
    indicator_integrable_on_sphere_prod hF
  have hFubini :
      ∫ p : Metric.sphere (0 : E) 1 × Set.Ioi (0 : ℝ),
        G (p.2.1 • (p.1 : E)) ∂σ.prod ρ =
      ∫ ω : Metric.sphere (0 : E) 1,
        (∫ r : Set.Ioi (0 : ℝ), G (r.1 • (ω : E)) ∂ρ) ∂σ :=
    integral_prod
      (f := fun (p : Metric.sphere (0 : E) 1 × Set.Ioi (0 : ℝ)) =>
        G (p.2.1 • (p.1 : E)))
      hInteg
  rw [hFubini]
  rw [setIntegral_univ]
  congr 1
  ext ω
  simp only [ρ, Measure.volumeIoiPow]
  rw [integral_withDensity_eq_integral_toReal_smul
    ((measurable_subtype_coe.pow_const _).ennreal_ofReal)
    (by filter_upwards with ⟨r, hr⟩; exact ENNReal.ofReal_lt_top)]
  have h5b : ∫ r : Set.Ioi (0 : ℝ),
      (ENNReal.ofReal (r.1 ^ n)).toReal • G (r.1 • (ω : E))
      ∂(Measure.comap Subtype.val volume) =
      ∫ r in Set.Ioi (0 : ℝ), r ^ n • G (r • (ω : E)) ∂volume := by
    have : (fun (r : Set.Ioi (0 : ℝ)) =>
        (ENNReal.ofReal (r.1 ^ n)).toReal • G (r.1 • (ω : E))) =
        (fun (r : Set.Ioi (0 : ℝ)) => r.1 ^ n • G (r.1 • (ω : E))) := by
      ext ⟨r, hr⟩
      rw [ENNReal.toReal_ofReal (pow_nonneg hr.le _)]
    rw [this]
    exact integral_subtype_comap (α := ℝ) measurableSet_Ioi
      (fun r => r ^ n • G (r • (ω : E)))
  rw [h5b]
  have hfin : n = d - 1 := by simp [n]
  rw [show (∫ r in Set.Ioo (0 : ℝ) R, r ^ (d - 1 : ℕ) • F (r • (ω : E))) =
    ∫ r in Set.Ioi (0 : ℝ),
      (Set.Ioo (0 : ℝ) R).indicator (fun r => r ^ (d - 1 : ℕ) • F (r • (ω : E))) r from by
    rw [setIntegral_indicator measurableSet_Ioo,
      show Set.Ioi (0 : ℝ) ∩ Set.Ioo 0 R = Set.Ioo 0 R from
        Set.inter_eq_right.mpr Set.Ioo_subset_Ioi_self]]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro r hr
  rw [hfin]
  have hr_pos : 0 < r := hr
  simp only [Set.indicator, Set.mem_Ioo, hr_pos, true_and, smul_eq_mul]
  rw [hG_simp ω ⟨r, hr⟩]
  by_cases hlt : r < R
  · simp [hlt]
  · simp [hlt, mul_zero]

theorem polar_identity_ball
    {R : ℝ} (hR : 0 < R) {f : E → ℝ}
    (hf : IntegrableOn (fun z => f z * ‖z‖ ^ (1 - (d : ℝ))) (Metric.ball (0 : E) R) volume) :
    ∫ ω in Set.univ,
      (∫ s in Set.Ioo (0 : ℝ) R, f (s • (ω : E)))
      ∂(volume : Measure E).toSphere =
    ∫ z in Metric.ball (0 : E) R, f z * ‖z‖ ^ (1 - (d : ℝ)) ∂volume := by
  set g : E → ℝ := fun z => f z * ‖z‖ ^ (1 - (d : ℝ))
  have hpolar := sphere_radial_integral_ball hR hf
  rw [hpolar]
  congr 1
  ext ω
  apply setIntegral_congr_fun measurableSet_Ioo
  intro r ⟨hr_pos, hr_lt⟩
  simp only [g, smul_eq_mul]
  have hω_norm : ‖(ω : E)‖ = 1 := by
    have hm := ω.2
    simp only [Metric.mem_sphere, dist_zero_right] at hm
    exact hm
  rw [norm_smul, Real.norm_of_nonneg hr_pos.le, hω_norm, mul_one]
  have hd_ge : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)
  have hrpow_nat : (r : ℝ) ^ (d - 1 : ℕ) * r ^ (1 - (d : ℝ)) = 1 := by
    rw [← Real.rpow_natCast r (d - 1), Nat.cast_sub hd_ge, ← Real.rpow_add hr_pos]
    norm_num
  have : r ^ (d - 1 : ℕ) * (f (r • (ω : E)) * r ^ (1 - (d : ℝ))) = f (r • (ω : E)) := by
    rw [mul_comm (f _) _, ← mul_assoc, hrpow_nat, one_mul]
  linarith

omit [NeZero d] in
theorem norm_sub_le_integral_fderiv_along_segment
    {u : E → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u) (x y : E) :
    ‖u x - u y‖ ≤ ∫ t in (0 : ℝ)..‖x - y‖,
      ‖fderiv ℝ u (x + t • (‖x - y‖⁻¹ • (y - x)))‖ := by
  by_cases hxy : x = y
  · simp [hxy]
  set ω : E := ‖x - y‖⁻¹ • (y - x)
  set γ : ℝ → E := fun t => x + t • ω
  have hγ : ∀ t, HasDerivAt γ ω t := by
    intro t
    have : HasDerivAt (fun t => t • ω) ω t := by
      simpa using (hasDerivAt_id t).smul_const ω
    exact this.const_add x
  have huγ : ∀ t, HasDerivAt (u ∘ γ) ((fderiv ℝ u (γ t)) ω) t := by
    intro t
    exact (hu.differentiable (by norm_cast)).differentiableAt.hasFDerivAt.comp_hasDerivAt t
      (hγ t)
  have hγ0 : γ 0 = x := by simp [γ]
  have hγ1 : γ ‖x - y‖ = y := by
    simp only [γ, ω, smul_smul]
    rw [mul_inv_cancel₀ (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hxy)), one_smul]
    abel
  have hfderiv_cont : Continuous (fderiv ℝ u) := by
    have h1 : ContDiff ℝ 1 u := hu.of_le (by norm_cast)
    exact h1.continuous_fderiv (by norm_num)
  have hγ_cont : Continuous γ := by fun_prop
  have hcont_comp : Continuous (fun t => (fderiv ℝ u (γ t)) ω) :=
    (hfderiv_cont.comp hγ_cont).clm_apply continuous_const
  have hint1 : IntervalIntegrable (fun t => (fderiv ℝ u (γ t)) ω) volume 0 ‖x - y‖ :=
    hcont_comp.intervalIntegrable _ _
  have hint2 : IntervalIntegrable (fun t => ‖fderiv ℝ u (γ t)‖) volume 0 ‖x - y‖ :=
    (continuous_norm.comp (hfderiv_cont.comp hγ_cont)).intervalIntegrable _ _
  have hftc : u y - u x = ∫ t in (0 : ℝ)..‖x - y‖, (fderiv ℝ u (γ t)) ω := by
    have := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => huγ t) hint1
    simp only [Function.comp_apply, hγ0, hγ1] at this
    linarith
  have hω_norm : ‖ω‖ = 1 := by
    show ‖‖x - y‖⁻¹ • (y - x)‖ = 1
    rw [norm_smul, norm_inv, norm_norm, norm_sub_rev y x,
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hxy))]
  rw [norm_sub_rev]
  calc ‖u y - u x‖ = ‖∫ t in (0 : ℝ)..‖x - y‖, (fderiv ℝ u (γ t)) ω‖ := by rw [hftc]
    _ ≤ ∫ t in (0 : ℝ)..‖x - y‖, ‖(fderiv ℝ u (γ t)) ω‖ :=
        intervalIntegral.norm_integral_le_integral_norm (norm_nonneg _)
    _ ≤ ∫ t in (0 : ℝ)..‖x - y‖, ‖fderiv ℝ u (γ t)‖ := by
        apply intervalIntegral.integral_mono_on (norm_nonneg _) hint1.norm hint2
        intro t ht
        calc ‖(fderiv ℝ u (γ t)) ω‖ ≤ ‖fderiv ℝ u (γ t)‖ * ‖ω‖ :=
              ContinuousLinearMap.le_opNorm _ _
          _ = ‖fderiv ℝ u (γ t)‖ := by rw [hω_norm, mul_one]

theorem star_shaped_polar_identity
    {R : ℝ} (hR : 0 < R) {x : E} (hx : x ∈ Metric.ball (0 : E) R)
    {f : E → ℝ} (hf : IntegrableOn (fun y => f y * ‖y - x‖ ^ (1 - (d : ℝ)))
      (Metric.ball (0 : E) R) volume) :
    ∫ ω in Set.univ,
      (∫ s in Set.Ioo (0 : ℝ) (2 * R),
        (Metric.ball (0 : E) R).indicator (fun y => f y) (x + s • (ω : E)))
      ∂(volume : Measure E).toSphere =
    ∫ y in Metric.ball (0 : E) R, f y * ‖y - x‖ ^ (1 - (d : ℝ)) ∂volume := by
  set B := Metric.ball (0 : E) R
  set g : E → ℝ := fun z => B.indicator (fun y => f y) (x + z)
  have hpolar := polar_identity_ball (show (0 : ℝ) < 2 * R by linarith)
    (f := g) (hf := by
      have heq : (fun z => g z * ‖z‖ ^ (1 - (d : ℝ))) =ᵐ[volume.restrict (Metric.ball 0 (2*R))]
          (fun z => B.indicator (fun y => f y * ‖y - x‖ ^ (1 - (d : ℝ))) (x + z)) := by
        filter_upwards with z
        simp only [g, Set.indicator]
        split_ifs with h
        · congr 1
          congr 1
          show ‖z‖ = ‖(x + z) - x‖
          abel_nf
        · simp
      rw [IntegrableOn, integrable_congr heq]
      apply Integrable.integrableOn
      set F := B.indicator (fun y => f y * ‖y - x‖ ^ (1 - (d : ℝ)))
      have hF_int : Integrable F volume := (integrable_indicator_iff measurableSet_ball).mpr hf
      rw [show (fun z => F (x + z)) = F ∘ (· + x) from by ext z; rw [add_comm]; rfl]
      exact (measurePreserving_add_right volume x).integrable_comp_of_integrable hF_int)
  have hRHS : ∫ z in Metric.ball (0 : E) (2 * R), g z * ‖z‖ ^ (1 - (d : ℝ)) ∂volume =
      ∫ y in B, f y * ‖y - x‖ ^ (1 - (d : ℝ)) ∂volume := by
    have hx_norm : ‖x‖ < R := by rwa [Metric.mem_ball, dist_zero_right] at hx
    have hfun_eq : ∀ z, g z * ‖z‖ ^ (1 - (d : ℝ)) =
        B.indicator (fun y => f y * ‖y - x‖ ^ (1 - (d : ℝ))) (x + z) := by
      intro z
      simp only [g, Set.indicator]
      split_ifs with h
      · congr 1
        show ‖z‖ ^ (1 - (d : ℝ)) = ‖x + z - x‖ ^ (1 - (d : ℝ))
        congr 1
        abel_nf
      · ring
    conv_lhs =>
      arg 2
      ext z
      rw [hfun_eq]
    set h : E → ℝ := B.indicator (fun y => f y * ‖y - x‖ ^ (1 - (d : ℝ)))
    calc ∫ z in Metric.ball (0 : E) (2 * R), h (x + z) ∂volume
        = ∫ z, h (x + z) ∂volume := by
          rw [← integral_indicator measurableSet_ball]
          apply integral_congr_ae
          filter_upwards with z
          simp only [Set.indicator]
          split_ifs with hz
          · rfl
          · simp only [h, Set.indicator]
            split_ifs with hb
            · exfalso
              apply hz
              simp only [B, Metric.mem_ball, dist_zero_right] at hb ⊢
              calc ‖z‖ ≤ ‖x + z‖ + ‖x‖ := by
                    calc ‖z‖ = ‖(x + z) + (-x)‖ := by abel_nf
                      _ ≤ ‖x + z‖ + ‖-x‖ := norm_add_le _ _
                      _ = ‖x + z‖ + ‖x‖ := by rw [norm_neg]
                _ < R + R := add_lt_add hb hx_norm
                _ = 2 * R := by ring
            · rfl
      _ = ∫ y, h y ∂volume := by
          rw [show (fun z => h (x + z)) = (fun z => h (z + x)) from by ext z; rw [add_comm]]
          exact integral_add_right_eq_self _ x
      _ = ∫ y in B, f y * ‖y - x‖ ^ (1 - (d : ℝ)) ∂volume := by
          exact integral_indicator measurableSet_ball
  calc ∫ ω in Set.univ,
        (∫ s in Set.Ioo (0 : ℝ) (2 * R), B.indicator (fun y => f y) (x + s • (ω : E)))
        ∂(volume : Measure E).toSphere
      = ∫ ω in Set.univ,
        (∫ s in Set.Ioo (0 : ℝ) (2 * R), g (s • (ω : E)))
        ∂(volume : Measure E).toSphere := by rfl
    _ = ∫ z in Metric.ball (0 : E) (2 * R), g z * ‖z‖ ^ (1 - (d : ℝ)) ∂volume :=
        hpolar
    _ = ∫ y in B, f y * ‖y - x‖ ^ (1 - (d : ℝ)) ∂volume := hRHS

omit [NeZero d] in
private lemma ray_mem_ball_of_mem_ball
    {R : ℝ} {x : E} {ω : Metric.sphere (0 : E) 1} {s t : ℝ}
    (hx : x ∈ Metric.ball (0 : E) R)
    (hs_ball : x + s • (ω : E) ∈ Metric.ball (0 : E) R)
    (hs : 0 < s) (ht : t ∈ Set.Icc (0 : ℝ) s) :
    x + t • (ω : E) ∈ Metric.ball (0 : E) R := by
  have hts : t / s ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · exact div_nonneg ht.1 hs.le
    · have hts' : t ≤ (1 : ℝ) * s := by simpa using ht.2
      exact (div_le_iff₀ hs).2 hts'
  have hconv := (convex_ball (0 : E) R).add_smul_sub_mem hx hs_ball hts
  have hrewrite : x + t • (ω : E) = x + (t / s) • ((x + s • (ω : E)) - x) := by
    calc
      x + t • (ω : E) = x + (((t / s) * s) • (ω : E)) := by
          congr 2
          rw [div_eq_mul_inv, mul_assoc, inv_mul_cancel₀ hs.ne', mul_one]
      _ = x + (t / s) • (s • (ω : E)) := by rw [smul_smul]
      _ = x + (t / s) • ((x + s • (ω : E)) - x) := by congr 2; abel_nf
  rw [hrewrite]
  exact hconv

omit [NeZero d] in
private lemma integrableOn_radial_indicator_fderiv
    {R : ℝ} (_hR : 0 < R) {u : E → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (x : E) (ω : Metric.sphere (0 : E) 1) :
    IntegrableOn
      (fun t : ℝ =>
        (Metric.ball (0 : E) R).indicator (fun y => ‖fderiv ℝ u y‖)
          (x + t • (ω : E)))
      (Set.Ioo (0 : ℝ) (2 * R)) volume := by
  set g : ℝ → ℝ := fun t => ‖fderiv ℝ u (x + t • (ω : E))‖
  set S : Set ℝ := {t : ℝ | ‖x + t • (ω : E)‖ < R}
  have hg_cont : Continuous g := by
    have hfderiv_cont : Continuous (fderiv ℝ u) := by
      have h1 : ContDiff ℝ 1 u := hu.of_le (by norm_cast)
      exact h1.continuous_fderiv (by norm_num)
    have hline_cont : Continuous (fun t : ℝ => x + t • (ω : E)) :=
      continuous_const.add (continuous_id.smul continuous_const)
    exact continuous_norm.comp (hfderiv_cont.comp hline_cont)
  have hg_int_Icc : IntegrableOn g (Set.Icc (0 : ℝ) (2 * R)) volume :=
    (hg_cont.continuousOn.integrableOn_compact (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) (2 * R))))
  have hS_meas : MeasurableSet S := by
    have hcont : Continuous fun t : ℝ => ‖x + t • (ω : E)‖ :=
      continuous_norm.comp (continuous_const.add (continuous_id.smul continuous_const))
    exact (measurableSet_Iio).preimage hcont.measurable
  have hind_int_Icc : IntegrableOn (S.indicator g) (Set.Icc (0 : ℝ) (2 * R)) volume :=
    hg_int_Icc.indicator hS_meas
  have hsubset : Set.Ioo (0 : ℝ) (2 * R) ⊆ Set.Icc (0 : ℝ) (2 * R) := by
    intro t ht
    exact ⟨le_of_lt ht.1, le_of_lt ht.2⟩
  refine (hind_int_Icc.mono_set hsubset).congr_fun ?_ measurableSet_Ioo
  intro t ht
  by_cases hmem : ‖x + t • (ω : E)‖ < R
  · simp [g, S, hmem, Metric.mem_ball, dist_zero_right]
  · simp [g, S, hmem, Metric.mem_ball, dist_zero_right]

omit [NeZero d] in
private theorem integrable_sphere_radial_integral_ball
    {R : ℝ} (_hR : 0 < R) {F : E → ℝ}
    (hF : IntegrableOn F (Metric.ball (0 : E) R) volume) :
    Integrable
      (fun ω : Metric.sphere (0 : E) 1 =>
        ∫ r in Set.Ioo (0 : ℝ) R, r ^ (d - 1 : ℕ) • F (r • (ω : E)) ∂volume)
      ((volume : Measure E).toSphere) := by
  set G : E → ℝ := (Metric.ball (0 : E) R).indicator F
  set σ := (volume : Measure E).toSphere
  set n := Module.finrank ℝ E - 1
  set ρ := Measure.volumeIoiPow n
  have hInteg : Integrable (fun p : Metric.sphere (0 : E) 1 × Set.Ioi (0 : ℝ) =>
      G (p.2.1 • (p.1 : E))) (σ.prod ρ) :=
    indicator_integrable_on_sphere_prod hF
  have hOuter : Integrable
      (fun ω : Metric.sphere (0 : E) 1 =>
        ∫ r : Set.Ioi (0 : ℝ), G (r.1 • (ω : E)) ∂ρ) σ := by
    simpa [σ, ρ] using hInteg.integral_prod_left
  refine hOuter.congr ?_
  filter_upwards with ω
  simp only [ρ, Measure.volumeIoiPow]
  rw [integral_withDensity_eq_integral_toReal_smul
    ((measurable_subtype_coe.pow_const _).ennreal_ofReal)
    (by filter_upwards with ⟨r, hr⟩; exact ENNReal.ofReal_lt_top)]
  have h5b : ∫ r : Set.Ioi (0 : ℝ),
      (ENNReal.ofReal (r.1 ^ n)).toReal • G (r.1 • (ω : E))
      ∂(Measure.comap Subtype.val volume) =
      ∫ r in Set.Ioi (0 : ℝ), r ^ n • G (r • (ω : E)) ∂volume := by
    have : (fun (r : Set.Ioi (0 : ℝ)) =>
        (ENNReal.ofReal (r.1 ^ n)).toReal • G (r.1 • (ω : E))) =
        (fun (r : Set.Ioi (0 : ℝ)) => r.1 ^ n • G (r.1 • (ω : E))) := by
      ext ⟨r, hr⟩
      rw [ENNReal.toReal_ofReal (pow_nonneg hr.le _)]
    rw [this]
    exact integral_subtype_comap (α := ℝ) measurableSet_Ioi
      (fun r => r ^ n • G (r • (ω : E)))
  rw [h5b]
  have hfin : n = d - 1 := by simp [n]
  rw [show (∫ r in Set.Ioo (0 : ℝ) R, r ^ (d - 1 : ℕ) • F (r • (ω : E))) =
    ∫ r in Set.Ioi (0 : ℝ),
      (Set.Ioo (0 : ℝ) R).indicator (fun r => r ^ (d - 1 : ℕ) • F (r • (ω : E))) r from by
    rw [setIntegral_indicator measurableSet_Ioo,
      show Set.Ioi (0 : ℝ) ∩ Set.Ioo 0 R = Set.Ioo 0 R from
        Set.inter_eq_right.mpr Set.Ioo_subset_Ioi_self]]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro r hr
  rw [hfin]
  have hr_pos : 0 < r := hr
  have hω_norm : ‖(ω : E)‖ = 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using ω.2
  simp only [G, Set.indicator, Metric.mem_ball, dist_zero_right, Set.mem_Ioo, hr_pos, true_and,
    smul_eq_mul]
  rw [norm_smul, Real.norm_of_nonneg hr_pos.le, hω_norm, mul_one]
  by_cases hlt : r < R
  · simp [hlt]
  · simp [hlt]

private theorem integrable_polar_radial
    {R : ℝ} (hR : 0 < R) {f : E → ℝ}
    (hf : IntegrableOn (fun z => f z * ‖z‖ ^ (1 - (d : ℝ))) (Metric.ball (0 : E) R) volume) :
    Integrable
      (fun ω : Metric.sphere (0 : E) 1 =>
        ∫ s in Set.Ioo (0 : ℝ) R, f (s • (ω : E)) ∂volume)
      ((volume : Measure E).toSphere) := by
  have hbase := integrable_sphere_radial_integral_ball
    (d := d) (R := R) hR
    (F := fun z => f z * ‖z‖ ^ (1 - (d : ℝ))) hf
  refine hbase.congr ?_
  filter_upwards with ω
  apply setIntegral_congr_fun measurableSet_Ioo
  intro r hr
  have hr_pos : 0 < r := hr.1
  have hω_norm : ‖(ω : E)‖ = 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using ω.2
  simp only [smul_eq_mul]
  rw [norm_smul, Real.norm_of_nonneg hr_pos.le, hω_norm, mul_one]
  have hd_ge : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)
  have hrpow_nat : (r : ℝ) ^ (d - 1 : ℕ) * r ^ (1 - (d : ℝ)) = 1 := by
    rw [← Real.rpow_natCast r (d - 1), Nat.cast_sub hd_ge, ← Real.rpow_add hr_pos]
    norm_num
  rw [mul_comm (f (r • (ω : E))) _, ← mul_assoc, hrpow_nat, one_mul]

private theorem integrable_star_shaped_radial
    {R : ℝ} (hR : 0 < R) {x : E} (_hx : x ∈ Metric.ball (0 : E) R)
    {f : E → ℝ} (hf : IntegrableOn (fun y => f y * ‖y - x‖ ^ (1 - (d : ℝ)))
      (Metric.ball (0 : E) R) volume) :
    Integrable
      (fun ω : Metric.sphere (0 : E) 1 =>
        ∫ s in Set.Ioo (0 : ℝ) (2 * R),
          (Metric.ball (0 : E) R).indicator (fun y => f y) (x + s • (ω : E)) ∂volume)
      ((volume : Measure E).toSphere) := by
  set B := Metric.ball (0 : E) R
  set g : E → ℝ := fun z => B.indicator (fun y => f y) (x + z)
  have hg_int :
      IntegrableOn (fun z => g z * ‖z‖ ^ (1 - (d : ℝ)))
        (Metric.ball (0 : E) (2 * R)) volume := by
    have heq : (fun z => g z * ‖z‖ ^ (1 - (d : ℝ))) =ᵐ[volume.restrict (Metric.ball 0 (2 * R))]
        (fun z => B.indicator (fun y => f y * ‖y - x‖ ^ (1 - (d : ℝ))) (x + z)) := by
      filter_upwards with z
      simp only [g, Set.indicator]
      split_ifs with h
      · congr 1
        congr 1
        show ‖z‖ = ‖(x + z) - x‖
        abel_nf
      · simp
    rw [IntegrableOn, integrable_congr heq]
    apply Integrable.integrableOn
    set F := B.indicator (fun y => f y * ‖y - x‖ ^ (1 - (d : ℝ)))
    have hF_int : Integrable F volume := (integrable_indicator_iff measurableSet_ball).mpr hf
    rw [show (fun z => F (x + z)) = F ∘ (· + x) from by ext z; rw [add_comm]; rfl]
    exact (measurePreserving_add_right volume x).integrable_comp_of_integrable hF_int
  simpa [g, B] using integrable_polar_radial
    (d := d) (R := 2 * R) (hR := by linarith) (f := g) hg_int

private theorem translated_ball_sphere_radial_identity
    {R : ℝ} (hR : 0 < R) {x : E} (hx : x ∈ Metric.ball (0 : E) R)
    {f : E → ℝ} (hf : IntegrableOn f (Metric.ball (0 : E) R) volume) :
    ∫ ω in Set.univ,
      (∫ s in Set.Ioo (0 : ℝ) (2 * R),
        s ^ (d - 1 : ℕ) •
          (Metric.ball (0 : E) R).indicator (fun y => f y) (x + s • (ω : E)) ∂volume)
      ∂(volume : Measure E).toSphere =
    ∫ y in Metric.ball (0 : E) R, f y ∂volume := by
  set B := Metric.ball (0 : E) R
  set g : E → ℝ := fun z => B.indicator (fun y => f y) (x + z)
  have hg_int : IntegrableOn g (Metric.ball (0 : E) (2 * R)) volume := by
    have hF_int : Integrable (B.indicator f) volume := (integrable_indicator_iff measurableSet_ball).mpr hf
    have hcomp : Integrable (fun z => B.indicator f (x + z)) volume := by
      rw [show (fun z => B.indicator f (x + z)) = (B.indicator f) ∘ (· + x) from by
        ext z
        rw [add_comm]
        rfl]
      exact (measurePreserving_add_right volume x).integrable_comp_of_integrable hF_int
    exact hcomp.integrableOn
  have hrad := sphere_radial_integral_ball (d := d) (R := 2 * R)
    (show (0 : ℝ) < 2 * R by linarith) (F := g) hg_int
  have hRHS : ∫ z in Metric.ball (0 : E) (2 * R), g z ∂volume =
      ∫ y in B, f y ∂volume := by
    have hx_norm : ‖x‖ < R := by rwa [Metric.mem_ball, dist_zero_right] at hx
    set h : E → ℝ := B.indicator f
    calc ∫ z in Metric.ball (0 : E) (2 * R), h (x + z) ∂volume
        = ∫ z, h (x + z) ∂volume := by
          rw [← integral_indicator measurableSet_ball]
          apply integral_congr_ae
          filter_upwards with z
          simp only [Set.indicator]
          split_ifs with hz
          · rfl
          · simp only [h, Set.indicator]
            split_ifs with hb
            · exfalso
              apply hz
              simp only [B, Metric.mem_ball, dist_zero_right] at hb ⊢
              calc ‖z‖ ≤ ‖x + z‖ + ‖x‖ := by
                    calc ‖z‖ = ‖(x + z) + (-x)‖ := by abel_nf
                      _ ≤ ‖x + z‖ + ‖-x‖ := norm_add_le _ _
                      _ = ‖x + z‖ + ‖x‖ := by rw [norm_neg]
                _ < R + R := add_lt_add hb hx_norm
                _ = 2 * R := by ring
            · rfl
      _ = ∫ y, h y ∂volume := by
          rw [show (fun z => h (x + z)) = (fun z => h (z + x)) from by ext z; rw [add_comm]]
          exact integral_add_right_eq_self _ x
      _ = ∫ y in B, f y ∂volume := by
          exact integral_indicator measurableSet_ball
  calc ∫ ω in Set.univ,
        (∫ s in Set.Ioo (0 : ℝ) (2 * R),
          s ^ (d - 1 : ℕ) • B.indicator (fun y => f y) (x + s • (ω : E)) ∂volume)
        ∂(volume : Measure E).toSphere
      = ∫ ω in Set.univ,
        (∫ s in Set.Ioo (0 : ℝ) (2 * R), s ^ (d - 1 : ℕ) • g (s • (ω : E)) ∂volume)
        ∂(volume : Measure E).toSphere := by rfl
    _ = ∫ z in Metric.ball (0 : E) (2 * R), g z ∂volume := hrad.symm
    _ = ∫ y in B, f y ∂volume := hRHS

theorem integral_norm_rpow_neg_ball {R : ℝ} (hR : 0 < R) :
    ∫ x in Metric.ball (0 : E) R, ‖x‖ ^ (1 - (d : ℝ)) ∂volume =
    ↑d * (volume (Metric.ball (0 : E) 1)).toReal * R := by
  let f : ℝ → ℝ := fun r => if 0 < r ∧ r < R then r ^ (1 - (d : ℝ)) else 0
  have hconv : ∫ x in Metric.ball (0 : E) R, ‖x‖ ^ (1 - (d : ℝ)) ∂volume =
      ∫ x : E, f (‖x‖) ∂volume := by
    rw [← integral_indicator measurableSet_ball]
    refine integral_congr_ae ?_
    have hmeas0 : (volume : Measure E) {(0 : E)} = 0 := measure_singleton _
    have hae : ∀ᵐ x ∂(volume : Measure E), x ≠ (0 : E) :=
      compl_mem_ae_iff.mpr hmeas0
    filter_upwards [hae] with x hx
    simp only [f, indicator, Metric.mem_ball, dist_zero_right]
    have hpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
    simp only [and_iff_right hpos]
  have hrad : ∫ x : E, f (‖x‖) ∂volume =
      ↑(Module.finrank ℝ E) • (volume : Measure E).real (Metric.ball 0 1) •
        ∫ y in Set.Ioi (0 : ℝ), y ^ (Module.finrank ℝ E - 1) • f y :=
    MeasureTheory.integral_fun_norm_addHaar (μ := (volume : Measure E)) f
  have hfin : Module.finrank ℝ E = d := finrank_euclideanSpace_fin
  have h1d : ∫ y in Set.Ioi (0 : ℝ), y ^ (Module.finrank ℝ E - 1) • f y = R := by
    rw [hfin]
    have hsupp : ∀ y ∈ Set.Ioi (0 : ℝ), y ^ (d - 1) • f y =
        Set.indicator (Set.Ioo 0 R) (fun _ => (1 : ℝ)) y := by
      intro y hy
      have hy_pos : 0 < y := hy
      by_cases hlt : y < R
      · simp only [f, smul_eq_mul, Set.indicator, Set.mem_Ioo, hy_pos, hlt, true_and,
          if_true]
        rw [← Real.rpow_natCast y (d - 1),
          Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)),
          ← Real.rpow_add hy_pos]
        norm_num
      · simp only [f, smul_eq_mul, Set.indicator, Set.mem_Ioo, hy_pos, hlt, true_and,
          if_false, mul_zero]
    rw [setIntegral_congr_fun measurableSet_Ioi hsupp]
    rw [setIntegral_indicator measurableSet_Ioo]
    rw [show Set.Ioi (0 : ℝ) ∩ Set.Ioo 0 R = Set.Ioo 0 R from
      Set.inter_eq_right.mpr Set.Ioo_subset_Ioi_self]
    simp only [setIntegral_const, smul_eq_mul, mul_one, Measure.real,
      Real.volume_Ioo, ENNReal.toReal_ofReal (by linarith : (0 : ℝ) ≤ R - 0)]
    ring
  rw [hconv, hrad, h1d, hfin]
  simp [nsmul_eq_mul, Measure.real]
  ring

theorem riesz_kernel_integrable
    {R : ℝ} (_hR : 0 < R) :
    IntegrableOn (fun x : E => ‖x‖ ^ (1 - (d : ℝ)))
      (Metric.ball (0 : E) R) volume := by
  let g : ℝ → ℝ := fun r => if r < R then r ^ (1 - (d : ℝ)) else 0
  have hag : (fun x : E => ‖x‖ ^ (1 - (d : ℝ))) =ᵐ[volume.restrict (Metric.ball (0 : E) R)]
      (g ∘ (‖·‖)) := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    simp only [Function.comp_apply, g, Metric.mem_ball, dist_zero_right] at hx ⊢
    rw [if_pos hx]
  rw [IntegrableOn, integrable_congr hag]
  suffices h : Integrable (fun x : E => g ‖x‖) volume from h.integrableOn
  have h1d : IntegrableOn (fun y : ℝ => y ^ (Module.finrank ℝ E - 1) • g y) (Set.Ioi 0) := by
    have hfin : Module.finrank ℝ E = d := finrank_euclideanSpace_fin
    set h_ind : ℝ → ℝ := (Set.Ioo (0 : ℝ) R).indicator (fun _ => (1 : ℝ))
    have heq : Set.EqOn (fun y : ℝ => y ^ (Module.finrank ℝ E - 1) • g y)
        h_ind (Set.Ioi 0) := by
      intro r hr
      simp only [Set.mem_Ioi] at hr
      simp only [g, smul_eq_mul, h_ind, Set.indicator, Set.mem_Ioo]
      split_ifs with h1 h2
      · rw [hfin, ← Real.rpow_natCast r (d - 1),
          Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)),
          ← Real.rpow_add hr]
        norm_num
      · next h2 => exact absurd ⟨hr, h1⟩ h2
      · next h1 h2 => exact absurd h2.2 h1
      · simp [mul_zero]
    have h_ind_int : IntegrableOn h_ind (Set.Ioi 0) := by
      apply Integrable.integrableOn
      exact integrable_indicator_iff measurableSet_Ioo |>.mpr (integrableOn_const (hs := measure_Ioo_lt_top.ne))
    exact h_ind_int.congr_fun heq.symm measurableSet_Ioi
  exact (MeasureTheory.integrable_fun_norm_addHaar (μ := volume) (f := g)).mpr h1d

theorem riesz_kernel_L1_bound
    {R : ℝ} (hR : 0 < R) (x : E) (hx : x ∈ Metric.ball (0 : E) R) :
    ∫ y in Metric.ball (0 : E) R,
      ‖x - y‖ ^ (1 - (d : ℝ)) ∂volume ≤
    ↑d * (volume (Metric.ball (0 : E) 1)).toReal * (2 * R) := by
  have hx_dist : dist x 0 < R := Metric.mem_ball.mp hx
  have hBsub : Metric.ball (0 : E) R ⊆ Metric.ball x (2 * R) := by
    intro y hy
    rw [Metric.mem_ball] at hy ⊢
    calc dist y x ≤ dist y 0 + dist 0 x := dist_triangle y 0 x
      _ < R + R := by rw [dist_comm] at hx_dist; linarith [Metric.mem_ball.mp hy]
      _ = 2 * R := by ring
  calc ∫ y in Metric.ball (0 : E) R, ‖x - y‖ ^ (1 - (d : ℝ)) ∂volume
      ≤ ∫ z in Metric.ball (0 : E) (2 * R), ‖z‖ ^ (1 - (d : ℝ)) ∂volume := by
        have hmp := measurePreserving_add_right (volume : Measure E) x
        have hemb := (MeasurableEquiv.addRight x : E ≃ᵐ E).measurableEmbedding
        have hpre : (· + x) ⁻¹' Metric.ball x (2 * R) = Metric.ball (0 : E) (2 * R) := by
          ext z; simp [Metric.mem_ball]
        have htrans : ∫ y in Metric.ball x (2 * R), ‖x - y‖ ^ (1 - (d : ℝ)) ∂volume =
            ∫ z in Metric.ball (0 : E) (2 * R), ‖z‖ ^ (1 - (d : ℝ)) ∂volume := by
          rw [← hmp.setIntegral_preimage_emb hemb, hpre]
          congr 1 with z
          show ‖x - (z + x)‖ ^ (1 - (d : ℝ)) = ‖z‖ ^ (1 - (d : ℝ))
          simp [norm_neg]
        have hinteg : IntegrableOn (fun y => ‖x - y‖ ^ (1 - (d : ℝ)))
            (Metric.ball x (2 * R)) volume := by
          have h2R : (0 : ℝ) < 2 * R := by linarith
          rw [← hmp.integrableOn_comp_preimage hemb, hpre]
          exact (riesz_kernel_integrable h2R).congr
            (ae_of_all _ (fun z => by
              show ‖z‖ ^ (1 - (d : ℝ)) = ‖x - (z + x)‖ ^ (1 - (d : ℝ))
              simp [norm_neg]))
        calc ∫ y in Metric.ball (0 : E) R, ‖x - y‖ ^ (1 - (d : ℝ)) ∂volume
            ≤ ∫ y in Metric.ball x (2 * R), ‖x - y‖ ^ (1 - (d : ℝ)) ∂volume := by
              apply setIntegral_mono_set hinteg
              · exact ae_of_all _ (fun y => Real.rpow_nonneg (norm_nonneg _) _)
              · exact hBsub.eventuallyLE
          _ = ∫ z in Metric.ball (0 : E) (2 * R), ‖z‖ ^ (1 - (d : ℝ)) ∂volume := htrans
    _ = ↑d * (volume (Metric.ball (0 : E) 1)).toReal * (2 * R) := by
        exact integral_norm_rpow_neg_ball (by linarith)

theorem representation_formula_smooth
    {R : ℝ} (hR : 0 < R)
    {u : E → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u) (x : E) (hx : x ∈ Metric.ball (0 : E) R) :
    ‖u x - ⨍ y in Metric.ball (0 : E) R, u y ∂volume‖ ≤
    (2 : ℝ) ^ d / ((d : ℝ) * (volume (Metric.ball (0 : E) 1)).toReal) *
      ∫ y in Metric.ball (0 : E) R,
        ‖fderiv ℝ u y‖ * ‖x - y‖ ^ (1 - (d : ℝ)) ∂volume := by
  set B := Metric.ball (0 : E) R
  set ubar := ⨍ y in B, u y ∂volume
  have h1 : ‖u x - ubar‖ ≤ ⨍ y in B, ‖u x - u y‖ ∂volume := by
    have hB_ne : volume B ≠ 0 := by
      simp [B]
      exact (measure_ball_pos volume 0 hR).ne'
    have hB_fin : volume B ≠ ⊤ := measure_ball_lt_top.ne
    have hu_int : IntegrableOn u B volume :=
      (hu.continuous.continuousOn.integrableOn_compact (isCompact_closedBall 0 R)).mono_set
        Metric.ball_subset_closedBall
    set μ := volume.restrict B
    haveI : IsFiniteMeasure μ := ⟨by rw [Measure.restrict_apply_univ]; exact hB_fin.lt_top⟩
    haveI : NeZero μ := ⟨by rwa [ne_eq, Measure.restrict_eq_zero]⟩
    have havg_eq : u x - ubar = ⨍ y, (u x - u y) ∂μ := by
      show u x - ⨍ y, u y ∂μ = ⨍ y, (u x - u y) ∂μ
      rw [average_eq, average_eq,
        integral_sub (integrable_const (u x)) hu_int.integrable,
        integral_const, smul_sub]
      have hne : (μ.real Set.univ) ≠ 0 := by
        rw [measureReal_def, Measure.restrict_apply_univ]
        exact ENNReal.toReal_ne_zero.mpr ⟨hB_ne, hB_fin⟩
      rw [inv_smul_smul₀ hne]
    rw [havg_eq]
    show ‖⨍ y, (u x - u y) ∂μ‖ ≤ ⨍ y, ‖u x - u y‖ ∂μ
    simp only [average_eq]
    calc ‖(μ.real Set.univ)⁻¹ • ∫ y, (u x - u y) ∂μ‖
        ≤ ‖(μ.real Set.univ)⁻¹‖ * ‖∫ y, (u x - u y) ∂μ‖ := norm_smul_le _ _
      _ ≤ ‖(μ.real Set.univ)⁻¹‖ * ∫ y, ‖u x - u y‖ ∂μ :=
          mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (norm_nonneg _)
      _ = (μ.real Set.univ)⁻¹ • ∫ y, ‖u x - u y‖ ∂μ := by
          rw [Real.norm_of_nonneg (inv_nonneg.mpr measureReal_nonneg), smul_eq_mul]
  set C_rep := (2 : ℝ) ^ d / ((d : ℝ) * (volume (Metric.ball (0 : E) 1)).toReal)
  suffices h2 : ⨍ y in B, ‖u x - u y‖ ∂volume ≤
      C_rep * ∫ y in B, ‖fderiv ℝ u y‖ * ‖x - y‖ ^ (1 - (d : ℝ)) ∂volume from
    le_trans h1 h2
  have hB_ne : volume B ≠ 0 := by
    simp [B]; exact (measure_ball_pos volume 0 hR).ne'
  have hB_fin : volume B ≠ ⊤ := measure_ball_lt_top.ne
  have hvol_pos : (0 : ℝ) < (volume B).toReal :=
    ENNReal.toReal_pos hB_ne hB_fin
  have hd_pos : (0 : ℝ) < d := Nat.cast_pos.mpr (NeZero.pos d)
  have hvol1_pos : (0 : ℝ) < (volume (Metric.ball (0 : E) 1)).toReal :=
    ENNReal.toReal_pos (measure_ball_pos volume 0 one_pos).ne' measure_ball_lt_top.ne
  set volB := (volume B).toReal
  have hH_int : IntegrableOn (fun y : E => ‖u x - u y‖) B volume := by
    have hcont : Continuous (fun y : E => ‖u x - u y‖) :=
      continuous_norm.comp (continuous_const.sub hu.continuous)
    exact (hcont.continuousOn.integrableOn_compact (isCompact_closedBall 0 R)).mono_set
      Metric.ball_subset_closedBall
  have hfderiv_cont : Continuous (fderiv ℝ u) := by
    have h1u : ContDiff ℝ 1 u := hu.of_le (by norm_cast)
    exact h1u.continuous_fderiv (by norm_num)
  have hgrad_cont : Continuous (fun y : E => ‖fderiv ℝ u y‖) :=
    continuous_norm.comp hfderiv_cont
  obtain ⟨C0, hC0⟩ :=
    IsCompact.exists_bound_of_continuousOn (isCompact_closedBall (0 : E) R) hgrad_cont.continuousOn
  set M : ℝ := max C0 0
  have hM_nonneg : 0 ≤ M := le_max_right _ _
  have hM_bound : ∀ y ∈ B, ‖fderiv ℝ u y‖ ≤ M := by
    intro y hy
    have hy' : y ∈ Metric.closedBall (0 : E) R := Metric.ball_subset_closedBall hy
    have hbound := hC0 y hy'
    rw [Real.norm_of_nonneg (norm_nonneg _)] at hbound
    exact hbound.trans (le_max_left _ _)
  have hBsub : B ⊆ Metric.ball x (2 * R) := by
    intro y hy
    rw [Metric.mem_ball] at hy ⊢
    have hx_dist : dist x 0 < R := Metric.mem_ball.mp hx
    calc dist y x ≤ dist y 0 + dist 0 x := dist_triangle y 0 x
      _ < R + R := by rw [dist_comm] at hx_dist; linarith [Metric.mem_ball.mp hy]
      _ = 2 * R := by ring
  have hk_big : IntegrableOn (fun y : E => ‖y - x‖ ^ (1 - (d : ℝ)))
      (Metric.ball x (2 * R)) volume := by
    have hmp := measurePreserving_add_right (volume : Measure E) x
    have hemb := (MeasurableEquiv.addRight x : E ≃ᵐ E).measurableEmbedding
    have hpre : (· + x) ⁻¹' Metric.ball x (2 * R) = Metric.ball (0 : E) (2 * R) := by
      ext z
      simp [Metric.mem_ball]
    rw [← hmp.integrableOn_comp_preimage hemb, hpre]
    have h2R : (0 : ℝ) < 2 * R := by linarith
    exact (riesz_kernel_integrable (d := d) h2R).congr
      (ae_of_all _ (fun z => by
        show ‖z‖ ^ (1 - (d : ℝ)) = ‖(z + x) - x‖ ^ (1 - (d : ℝ))
        abel_nf))
  have hk : IntegrableOn (fun y : E => ‖y - x‖ ^ (1 - (d : ℝ))) B volume :=
    hk_big.mono_set hBsub
  have hfG : IntegrableOn (fun y : E => ‖fderiv ℝ u y‖ * ‖y - x‖ ^ (1 - (d : ℝ))) B volume := by
    rw [IntegrableOn] at hk ⊢
    have hmajor : Integrable (fun y : E => M * ‖y - x‖ ^ (1 - (d : ℝ))) (volume.restrict B) :=
      hk.const_mul M
    apply Integrable.mono' hmajor
    · have hmeas :
          Measurable (fun y : E => ‖fderiv ℝ u y‖ * ‖y - x‖ ^ (1 - (d : ℝ))) := by
          measurability
      exact hmeas.aestronglyMeasurable.restrict
    · filter_upwards [ae_restrict_mem measurableSet_ball] with y hy
      have hk_nonneg : 0 ≤ ‖y - x‖ ^ (1 - (d : ℝ)) := Real.rpow_nonneg (norm_nonneg _) _
      have hleft_nonneg : 0 ≤ ‖fderiv ℝ u y‖ * ‖y - x‖ ^ (1 - (d : ℝ)) :=
        mul_nonneg (norm_nonneg _) hk_nonneg
      have hright_nonneg : 0 ≤ M * ‖y - x‖ ^ (1 - (d : ℝ)) :=
        mul_nonneg hM_nonneg hk_nonneg
      simpa [Real.norm_of_nonneg hleft_nonneg, Real.norm_of_nonneg hright_nonneg] using
        (mul_le_mul_of_nonneg_right (hM_bound y hy) hk_nonneg)
  have houterG_int := integrable_star_shaped_radial
    (d := d) (R := R) hR (x := x) hx (f := fun y => ‖fderiv ℝ u y‖) hfG
  have hkernel_symm :
      ∫ y in B, ‖fderiv ℝ u y‖ * ‖y - x‖ ^ (1 - (d : ℝ)) ∂volume =
      ∫ y in B, ‖fderiv ℝ u y‖ * ‖x - y‖ ^ (1 - (d : ℝ)) ∂volume := by
    apply setIntegral_congr_fun measurableSet_ball
    intro y hy
    simp [norm_sub_rev]
  have hrad_u :
      ∫ ω in Set.univ,
        (∫ s in Set.Ioo (0 : ℝ) (2 * R),
          s ^ (d - 1 : ℕ) • B.indicator (fun y => ‖u x - u y‖) (x + s • (ω : E)) ∂volume)
        ∂(volume : Measure E).toSphere
      = ∫ y in B, ‖u x - u y‖ ∂volume := by
    simpa [B] using translated_ball_sphere_radial_identity
      (d := d) (R := R) hR (x := x) hx (f := fun y => ‖u x - u y‖) hH_int
  have hpointwise :
      ∀ ω : Metric.sphere (0 : E) 1,
        ∫ s in Set.Ioo (0 : ℝ) (2 * R),
          s ^ (d - 1 : ℕ) • B.indicator (fun y => ‖u x - u y‖) (x + s • (ω : E)) ∂volume
        ≤ ((2 * R) ^ d / ↑d) *
          ∫ s in Set.Ioo (0 : ℝ) (2 * R),
            B.indicator (fun y => ‖fderiv ℝ u y‖) (x + s • (ω : E)) ∂volume := by
    intro ω
    set Cω := ∫ s in Set.Ioo (0 : ℝ) (2 * R),
      B.indicator (fun y => ‖fderiv ℝ u y‖) (x + s • (ω : E)) ∂volume
    have hCω_nonneg : 0 ≤ Cω := by
      apply integral_nonneg
      intro s
      by_cases hs_ball : x + s • (ω : E) ∈ B <;> simp [B, hs_ball]
    have hpow_int :
        IntegrableOn (fun s : ℝ => Cω * s ^ (d - 1 : ℕ))
          (Set.Ioo (0 : ℝ) (2 * R)) volume := by
      have hcont : Continuous (fun s : ℝ => Cω * s ^ (d - 1 : ℕ)) :=
        continuous_const.mul (continuous_id.pow _)
      have hsubset : Set.Ioo (0 : ℝ) (2 * R) ⊆ Set.Icc (0 : ℝ) (2 * R) := by
        intro s hs
        exact ⟨le_of_lt hs.1, le_of_lt hs.2⟩
      exact (hcont.continuousOn.integrableOn_compact
        (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) (2 * R)))).mono_set hsubset
    have hnonneg_lhs :
        0 ≤ᵐ[volume.restrict (Set.Ioo (0 : ℝ) (2 * R))]
          (fun s : ℝ => s ^ (d - 1 : ℕ) • B.indicator (fun y => ‖u x - u y‖) (x + s • (ω : E))) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
      by_cases hs_ball : x + s • (ω : E) ∈ B
      · simpa [B, hs_ball, smul_eq_mul] using
          mul_nonneg (pow_nonneg hs.1.le _) (norm_nonneg (u x - u (x + s • (ω : E))))
      · simp [B, hs_ball, smul_eq_mul]
    have hrad_le :
        ∫ s in Set.Ioo (0 : ℝ) (2 * R),
          s ^ (d - 1 : ℕ) • B.indicator (fun y => ‖u x - u y‖) (x + s • (ω : E)) ∂volume
        ≤ ∫ s in Set.Ioo (0 : ℝ) (2 * R), Cω * s ^ (d - 1 : ℕ) ∂volume := by
      apply integral_mono_of_nonneg hnonneg_lhs hpow_int.integrable
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
      have hs_pos : 0 < s := hs.1
      by_cases hs_ball : x + s • (ω : E) ∈ B
      · have hω_norm : ‖(ω : E)‖ = 1 := by
          simpa only [Metric.mem_sphere, dist_zero_right] using ω.2
        have hnorm : ‖x - (x + s • (ω : E))‖ = s := by
          calc
            ‖x - (x + s • (ω : E))‖ = ‖-(s • (ω : E))‖ := by congr 1; abel_nf
            _ = ‖s • (ω : E)‖ := norm_neg _
            _ = s := by rw [norm_smul, Real.norm_of_nonneg hs_pos.le, hω_norm, mul_one]
        have hdir : s⁻¹ • ((x + s • (ω : E)) - x) = (ω : E) := by
          calc
            s⁻¹ • ((x + s • (ω : E)) - x) = s⁻¹ • (s • (ω : E)) := by congr 2; abel_nf
            _ = (s⁻¹ * s) • (ω : E) := by rw [smul_smul]
            _ = (ω : E) := by rw [inv_mul_cancel₀ hs_pos.ne', one_smul]
        have hseg0 := norm_sub_le_integral_fderiv_along_segment
          (d := d) (u := u) hu x (x + s • (ω : E))
        have hseg :
            ‖u x - u (x + s • (ω : E))‖ ≤
            ∫ t in (0 : ℝ)..s, ‖fderiv ℝ u (x + t • (ω : E))‖ := by
          calc
            ‖u x - u (x + s • (ω : E))‖
                ≤ ∫ t in (0 : ℝ)..‖x - (x + s • (ω : E))‖,
                    ‖fderiv ℝ u (x + t • (‖x - (x + s • (ω : E))‖⁻¹ • ((x + s • (ω : E)) - x)))‖ := hseg0
            _ = ∫ t in (0 : ℝ)..s, ‖fderiv ℝ u (x + t • (ω : E))‖ := by
                  rw [hnorm]
                  congr with t
                  simp [smul_smul, hs_pos.ne']
        have hrad_eq :
            ∫ t in (0 : ℝ)..s, ‖fderiv ℝ u (x + t • (ω : E))‖ =
            ∫ t in (0 : ℝ)..s,
              B.indicator (fun y => ‖fderiv ℝ u y‖) (x + t • (ω : E)) ∂volume := by
          rw [intervalIntegral.integral_of_le hs_pos.le, intervalIntegral.integral_of_le hs_pos.le]
          apply setIntegral_congr_fun measurableSet_Ioc
          intro t ht
          have htIcc : t ∈ Set.Icc (0 : ℝ) s := ⟨le_of_lt ht.1, ht.2⟩
          have hmem := ray_mem_ball_of_mem_ball (d := d) hx hs_ball hs_pos htIcc
          simp [B, hmem]
        have hsubset_s : Set.Ioo (0 : ℝ) s ⊆ Set.Ioo (0 : ℝ) (2 * R) := by
          intro t ht
          exact ⟨ht.1, lt_of_lt_of_le ht.2 hs.2.le⟩
        have hmono :
            ∫ t in (0 : ℝ)..s,
              B.indicator (fun y => ‖fderiv ℝ u y‖) (x + t • (ω : E)) ∂volume
            ≤ Cω := by
          rw [intervalIntegral.integral_of_le hs_pos.le, integral_Ioc_eq_integral_Ioo]
          apply setIntegral_mono_set
            (integrableOn_radial_indicator_fderiv (d := d) hR hu x ω)
          · filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
            by_cases ht_ball : x + t • (ω : E) ∈ B <;> simp [B, ht_ball]
          · exact hsubset_s.eventuallyLE
        have hk_nonneg : 0 ≤ s ^ (d - 1 : ℕ) := pow_nonneg hs_pos.le _
        have hseg' : ‖u x - u (x + s • (ω : E))‖ ≤ Cω := by
          exact hseg.trans (by rw [hrad_eq]; exact hmono)
        have hmul : ‖u x - u (x + s • (ω : E))‖ * s ^ (d - 1 : ℕ) ≤ Cω * s ^ (d - 1 : ℕ) :=
          mul_le_mul_of_nonneg_right hseg' hk_nonneg
        simpa [B, hs_ball, smul_eq_mul, mul_comm] using hmul
      · have : 0 ≤ Cω * s ^ (d - 1 : ℕ) := mul_nonneg hCω_nonneg (pow_nonneg hs_pos.le _)
        simpa [B, hs_ball, smul_eq_mul] using this
    have hpow_eval :
        ∫ s in Set.Ioo (0 : ℝ) (2 * R), s ^ (d - 1 : ℕ) ∂volume =
          (2 * R) ^ d / ↑d := by
      have h2R : (0 : ℝ) < 2 * R := by linarith
      calc
        ∫ s in Set.Ioo (0 : ℝ) (2 * R), s ^ (d - 1 : ℕ) ∂volume
            = ∫ s in Set.Ioc (0 : ℝ) (2 * R), s ^ (d - 1 : ℕ) ∂volume := by
                rw [integral_Ioc_eq_integral_Ioo]
        _ = ∫ s in (0 : ℝ)..(2 * R), s ^ (d - 1 : ℕ) := by
              rw [← intervalIntegral.integral_of_le h2R.le]
        _ = ((2 * R) ^ d - 0 ^ d) / ↑d := by
              rw [integral_pow (a := (0 : ℝ)) (b := 2 * R) (n := d - 1)]
              simp [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)),
                Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr (NeZero.ne d))]
        _ = (2 * R) ^ d / ↑d := by
              simp [NeZero.ne d]
    calc
      ∫ s in Set.Ioo (0 : ℝ) (2 * R),
          s ^ (d - 1 : ℕ) • B.indicator (fun y => ‖u x - u y‖) (x + s • (ω : E)) ∂volume
          ≤ ∫ s in Set.Ioo (0 : ℝ) (2 * R), Cω * s ^ (d - 1 : ℕ) ∂volume := hrad_le
      _ = Cω * ((2 * R) ^ d / ↑d) := by
            rw [integral_const_mul, hpow_eval]
      _ = ((2 * R) ^ d / ↑d) * Cω := by ring
  have houter_nonneg :
      0 ≤ᵐ[(volume : Measure E).toSphere]
        (fun ω : Metric.sphere (0 : E) 1 =>
          ∫ s in Set.Ioo (0 : ℝ) (2 * R),
            s ^ (d - 1 : ℕ) • B.indicator (fun y => ‖u x - u y‖) (x + s • (ω : E)) ∂volume) := by
    filter_upwards with ω
    rw [← integral_indicator measurableSet_Ioo]
    apply integral_nonneg
    intro s
    by_cases hs : s ∈ Set.Ioo (0 : ℝ) (2 * R)
    · by_cases hs_ball : x + s • (ω : E) ∈ B
      · simpa [hs, B, hs_ball, smul_eq_mul] using
          mul_nonneg (pow_nonneg hs.1.le _) (norm_nonneg (u x - u (x + s • (ω : E))))
      · simp [hs, B, hs_ball, smul_eq_mul]
    · simp [hs]
  have houter_le :
      ∫ ω in Set.univ,
        (∫ s in Set.Ioo (0 : ℝ) (2 * R),
          s ^ (d - 1 : ℕ) • B.indicator (fun y => ‖u x - u y‖) (x + s • (ω : E)) ∂volume)
        ∂(volume : Measure E).toSphere
      ≤
      ∫ ω in Set.univ,
        (((2 * R) ^ d / ↑d) *
          ∫ s in Set.Ioo (0 : ℝ) (2 * R),
            B.indicator (fun y => ‖fderiv ℝ u y‖) (x + s • (ω : E)) ∂volume)
        ∂(volume : Measure E).toSphere := by
    simpa [setIntegral_univ] using integral_mono_of_nonneg houter_nonneg
      (houterG_int.const_mul ((2 * R) ^ d / ↑d))
      (ae_of_all _ hpointwise)
  have hrad_g :
      ∫ ω in Set.univ,
        (∫ s in Set.Ioo (0 : ℝ) (2 * R),
          B.indicator (fun y => ‖fderiv ℝ u y‖) (x + s • (ω : E)) ∂volume)
        ∂(volume : Measure E).toSphere
      = ∫ y in B, ‖fderiv ℝ u y‖ * ‖y - x‖ ^ (1 - (d : ℝ)) ∂volume := by
    simpa [B] using star_shaped_polar_identity
      (d := d) (R := R) hR (x := x) hx (f := fun y => ‖fderiv ℝ u y‖) hfG
  have hkey_integral : ∫ y in B, ‖u x - u y‖ ∂volume ≤
      ((2 * R) ^ d / ↑d) *
        ∫ y in B, ‖fderiv ℝ u y‖ * ‖x - y‖ ^ (1 - (d : ℝ)) ∂volume := by
    calc
      ∫ y in B, ‖u x - u y‖ ∂volume
          = ∫ ω in Set.univ,
              (∫ s in Set.Ioo (0 : ℝ) (2 * R),
                s ^ (d - 1 : ℕ) • B.indicator (fun y => ‖u x - u y‖) (x + s • (ω : E)) ∂volume)
              ∂(volume : Measure E).toSphere := by
                symm
                exact hrad_u
      _ ≤ ∫ ω in Set.univ,
            (((2 * R) ^ d / ↑d) *
              ∫ s in Set.Ioo (0 : ℝ) (2 * R),
                B.indicator (fun y => ‖fderiv ℝ u y‖) (x + s • (ω : E)) ∂volume)
            ∂(volume : Measure E).toSphere := houter_le
      _ = ((2 * R) ^ d / ↑d) *
            ∫ ω in Set.univ,
              (∫ s in Set.Ioo (0 : ℝ) (2 * R),
                B.indicator (fun y => ‖fderiv ℝ u y‖) (x + s • (ω : E)) ∂volume)
              ∂(volume : Measure E).toSphere := by
                rw [integral_const_mul]
      _ = ((2 * R) ^ d / ↑d) *
            ∫ y in B, ‖fderiv ℝ u y‖ * ‖y - x‖ ^ (1 - (d : ℝ)) ∂volume := by
                rw [hrad_g]
      _ = ((2 * R) ^ d / ↑d) *
            ∫ y in B, ‖fderiv ℝ u y‖ * ‖x - y‖ ^ (1 - (d : ℝ)) ∂volume := by
                rw [hkernel_symm]
  have hfin : Module.finrank ℝ E = d := finrank_euclideanSpace_fin
  have hvolB_eq : volB = (volume (Metric.ball (0 : E) 1)).toReal * R ^ d := by
    simp only [volB, B]
    rw [MeasureTheory.Measure.addHaar_ball_of_pos _ _ hR]
    rw [ENNReal.toReal_mul, hfin, ENNReal.toReal_ofReal (pow_nonneg hR.le d)]
    ring
  have havg_unfold : ⨍ y in B, ‖u x - u y‖ ∂volume =
      volB⁻¹ * ∫ y in B, ‖u x - u y‖ ∂volume := by
    show _ = (volume B).toReal⁻¹ * _
    rw [average_eq, smul_eq_mul, measureReal_restrict_apply_univ, measureReal_def]
  rw [havg_unfold]
  calc volB⁻¹ * ∫ y in B, ‖u x - u y‖ ∂volume
      ≤ volB⁻¹ * (((2 * R) ^ d / ↑d) *
          ∫ y in B, ‖fderiv ℝ u y‖ * ‖x - y‖ ^ (1 - (d : ℝ)) ∂volume) := by
        apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hvol_pos.le)
        exact hkey_integral
    _ = (volB⁻¹ * ((2 * R) ^ d / ↑d)) *
          ∫ y in B, ‖fderiv ℝ u y‖ * ‖x - y‖ ^ (1 - (d : ℝ)) ∂volume := by ring
    _ = C_rep * ∫ y in B, ‖fderiv ℝ u y‖ * ‖x - y‖ ^ (1 - (d : ℝ)) ∂volume := by
        congr 1
        simp only [C_rep, hvolB_eq, mul_pow]
        field_simp

-- Local copy of lintegral_rpow_norm_eq_eLpNorm_pow (defined in BallExtension, not imported here)
private theorem lintegral_rpow_norm_eq_eLpNorm_pow'
    {α F : Type*} [MeasurableSpace α] [NormedAddCommGroup F]
    [MeasurableSpace F] [BorelSpace F] {μ : Measure α}
    {p : ℝ} (hp : 0 < p) {f : α → F} :
    ∫⁻ x, (ENNReal.ofReal ‖f x‖) ^ p ∂μ = eLpNorm f (ENNReal.ofReal p) μ ^ p := by
  let pnn : ℝ≥0 := Real.toNNReal p
  have hpnn0 : pnn ≠ 0 := by
    intro hzero; have := Real.toNNReal_eq_zero.mp hzero; linarith
  have hpnn_real : (pnn : ℝ) = p := by simp [pnn, Real.toNNReal_of_nonneg (le_of_lt hp)]
  have hpnn_enn : (pnn : ℝ≥0∞) = ENNReal.ofReal p := rfl
  calc ∫⁻ x, (ENNReal.ofReal ‖f x‖) ^ p ∂μ
      = ∫⁻ x, (ENNReal.ofReal ‖f x‖) ^ (pnn : ℝ) ∂μ := by simp [hpnn_real]
    _ = eLpNorm f (pnn : ℝ≥0∞) μ ^ (pnn : ℝ) := by
        simpa using
          (MeasureTheory.eLpNorm_nnreal_pow_eq_lintegral (μ := μ) (f := f) (p := pnn) hpnn0).symm
    _ = eLpNorm f (ENNReal.ofReal p) μ ^ p := by simp [hpnn_real, hpnn_enn]

-- Weighted power-mean inequality: (∫ f·w dμ)^p ≤ (∫ w dμ)^{p-1} · ∫ f^p · w dμ
-- for nonneg f, w and p > 1. Proved via Hölder's inequality at the lintegral level.
theorem weighted_power_mean_setIntegral
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {s : Set α} (hs : MeasurableSet s)
    {p : ℝ} (hp : 1 < p)
    {f w : α → ℝ} (hf : ∀ x, 0 ≤ f x) (hw : ∀ x, 0 ≤ w x)
    (hf_meas : AEMeasurable f (μ.restrict s))
    (hwi : IntegrableOn w s μ)
    (hfpwi : IntegrableOn (fun x => (f x) ^ p * w x) s μ) :
    (∫ x in s, f x * w x ∂μ) ^ p ≤
      (∫ x in s, w x ∂μ) ^ (p - 1) * ∫ x in s, (f x) ^ p * w x ∂μ := by
  set μs : Measure α := μ.restrict s
  set ρ : α → ℝ≥0∞ := fun x => ENNReal.ofReal (w x)
  set ν : Measure α := μs.withDensity ρ
  let q : ℝ := p / (p - 1)
  have hp_pos : 0 < p := lt_trans zero_lt_one hp
  have hp_nonneg : 0 ≤ p := le_of_lt hp_pos
  have hpq : p.HolderConjugate q := by
    dsimp [q]
    exact Real.HolderConjugate.conjExponent hp
  have hq_pos : 0 < q := hpq.symm.pos
  have hρ_aemeas : AEMeasurable ρ μs := by
    simpa [ρ, μs] using hwi.aestronglyMeasurable.aemeasurable.ennreal_ofReal
  have hρ_lt_top : ∀ᵐ x ∂μs, ρ x < ∞ := by
    filter_upwards with x
    simp [ρ]
  have hρ_lint_ne_top : ∫⁻ x, ρ x ∂μs ≠ ∞ := by
    rw [← ofReal_integral_eq_lintegral_ofReal hwi (ae_of_all _ fun x => hw x)]
    simp
  haveI : IsFiniteMeasure ν := isFiniteMeasure_withDensity hρ_lint_ne_top
  have hf_meas_ν : AEMeasurable f ν := by
    exact hf_meas.mono_ac (withDensity_absolutelyContinuous _ _)
  have hpow_int_base : Integrable (fun x => (ρ x).toReal • (‖f x‖ ^ p)) μs := by
    refine hfpwi.congr ?_
    filter_upwards with x
    rw [smul_eq_mul, ENNReal.toReal_ofReal (hw x), Real.norm_of_nonneg (hf x)]
    ring
  have hpow_int : Integrable (fun x => ‖f x‖ ^ p) ν := by
    rw [show ν = μs.withDensity ρ by rfl]
    exact
      (MeasureTheory.integrable_withDensity_iff_integrable_smul₀'
        (μ := μs) hρ_aemeas hρ_lt_top).2 hpow_int_base
  have hf_mem : MemLp f (ENNReal.ofReal p) ν := by
    exact
      (MeasureTheory.integrable_norm_rpow_iff
        (μ := ν) hf_meas_ν.aestronglyMeasurable
        (by simp [hp_pos]) ENNReal.ofReal_ne_top).1 <| by
          simpa [ENNReal.toReal_ofReal hp_nonneg] using hpow_int
  have h_one_mem : MemLp (fun _ : α => (1 : ℝ)) (ENNReal.ofReal q) ν := by
    simpa [q] using (MeasureTheory.memLp_const (μ := ν) (p := ENNReal.ofReal q) (1 : ℝ))
  have hHolder :
      ∫ x, f x * (1 : ℝ) ∂ν ≤
        (∫ x, (f x) ^ p ∂ν) ^ (1 / p : ℝ) *
          (∫ x, (1 : ℝ) ^ q ∂ν) ^ (1 / q : ℝ) := by
    exact MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg
      (μ := ν) hpq
      (ae_of_all _ fun x => hf x)
      (ae_of_all _ fun _ => by positivity)
      hf_mem h_one_mem
  have hleft_eq : ∫ x, f x ∂ν = ∫ x in s, f x * w x ∂μ := by
    rw [show ν = μs.withDensity ρ by rfl]
    rw [integral_withDensity_eq_integral_toReal_smul₀ (μ := μs) hρ_aemeas hρ_lt_top]
    simp [μs, ρ, smul_eq_mul, ENNReal.toReal_ofReal, hw, mul_comm]
  have hpow_eq : ∫ x, (f x) ^ p ∂ν = ∫ x in s, (f x) ^ p * w x ∂μ := by
    rw [show ν = μs.withDensity ρ by rfl]
    rw [integral_withDensity_eq_integral_toReal_smul₀ (μ := μs) hρ_aemeas hρ_lt_top]
    simp [μs, ρ, smul_eq_mul, ENNReal.toReal_ofReal, hw, mul_comm]
  have hone_eq : ∫ x, (1 : ℝ) ^ q ∂ν = ∫ x in s, w x ∂μ := by
    rw [show ν = μs.withDensity ρ by rfl]
    rw [integral_withDensity_eq_integral_toReal_smul₀ (μ := μs) hρ_aemeas hρ_lt_top]
    simp [μs, ρ, q, smul_eq_mul, ENNReal.toReal_ofReal, hw]
  set A := ∫ x in s, f x * w x ∂μ
  set I := ∫ x in s, (f x) ^ p * w x ∂μ
  set W := ∫ x in s, w x ∂μ
  have hA_nonneg : 0 ≤ A := by
    exact setIntegral_nonneg hs (fun x _ => mul_nonneg (hf x) (hw x))
  have hI_nonneg : 0 ≤ I := by
    exact setIntegral_nonneg hs (fun x _ =>
      mul_nonneg (Real.rpow_nonneg (hf x) _) (hw x))
  have hW_nonneg : 0 ≤ W := by
    exact setIntegral_nonneg hs (fun x _ => hw x)
  -- If ∫ w = 0, both sides are 0
  by_cases hW_zero : ∫ x in s, w x ∂μ = 0
  · -- Here `w = 0` a.e., so the weighted integral also vanishes.
    have hfw_nonneg : 0 ≤ ∫ x in s, f x * w x ∂μ :=
      setIntegral_nonneg hs (fun x _ => mul_nonneg (hf x) (hw x))
    have hfw_zero : ∫ x in s, f x * w x ∂μ ≤ 0 := by
      by_cases hfwi : IntegrableOn (fun x => f x * w x) s μ
      · -- w ≥ 0 and ∫ w = 0 → w =ᵃᵉ 0 → f·w =ᵃᵉ 0 → ∫ f·w = 0
        have hwi := hwi
        have hw_ae : w =ᵐ[μ.restrict s] 0 := by
          rwa [setIntegral_eq_zero_iff_of_nonneg_ae
            (ae_restrict_of_ae (ae_of_all _ (fun x => hw x))) hwi] at hW_zero
        have : (fun x => f x * w x) =ᵐ[μ.restrict s] 0 :=
          hw_ae.mono (fun x hx => by simp [hx])
        rw [integral_congr_ae this]; simp
      · simp [integral_undef hfwi]
    have h0 := le_antisymm hfw_zero hfw_nonneg
    -- h0 : ∫ f·w = 0, hW_zero : ∫ w = 0. Goal: 0^p ≤ 0^{p-1} * ∫ f^p·w
    simpa [A, I, W, h0, hW_zero] using
      (show A ^ p ≤ W ^ (p - 1) * I by
        simp [A, I, W, h0, hW_zero,
          mul_nonneg (Real.rpow_nonneg (le_refl _) _)
            (setIntegral_nonneg hs (fun x _ => mul_nonneg (Real.rpow_nonneg (hf x) _) (hw x))),
          Real.zero_rpow (by linarith : p ≠ 0)])
  · -- ∫ w > 0
    have hW_pos : 0 < ∫ x in s, w x ∂μ :=
      lt_of_le_of_ne (setIntegral_nonneg hs (fun x _ => hw x)) (Ne.symm hW_zero)
    have hνreal_eq : ν.real Set.univ = W := by
      calc
        ν.real Set.univ = ∫ x, (1 : ℝ) ∂ν := by
          rw [integral_const]
          simp [Measure.real]
        _ = ∫ x, (1 : ℝ) ^ q ∂ν := by simp [q]
        _ = W := hone_eq
    have hHolder' : A ≤ W ^ (1 / q : ℝ) * I ^ (1 / p : ℝ) := by
      simpa [A, I, W, hleft_eq, hpow_eq, hνreal_eq, one_div, mul_comm, mul_left_comm, mul_assoc]
        using hHolder
    have hpow :=
      Real.rpow_le_rpow hA_nonneg hHolder' (le_of_lt hp_pos)
    have hWroot_nonneg : 0 ≤ W ^ (1 / q : ℝ) := Real.rpow_nonneg hW_nonneg _
    have hIroot_nonneg : 0 ≤ I ^ (1 / p : ℝ) := Real.rpow_nonneg hI_nonneg _
    have hq_ne_zero : q ≠ 0 := by linarith
    have hp_ne_zero : p ≠ 0 := by linarith
    have hrhs :
        (W ^ (1 / q : ℝ) * I ^ (1 / p : ℝ)) ^ p = W ^ (p - 1) * I := by
      rw [Real.mul_rpow hWroot_nonneg hIroot_nonneg]
      rw [← Real.rpow_mul hW_nonneg, ← Real.rpow_mul hI_nonneg]
      have hWq : (1 / q : ℝ) * p = p - 1 := by
        dsimp [q]
        field_simp [hp_ne_zero, show p - 1 ≠ 0 by linarith]
      have hIp : (1 / p : ℝ) * p = 1 := by
        field_simp [hp_ne_zero]
      rw [hWq, hIp, Real.rpow_one]
    simpa [A, I, W] using hpow.trans_eq hrhs

theorem poincare_smooth_unitBall
    {p : ℝ} (hp : 1 ≤ p)
    {u : E → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u) :
    eLpNorm (fun x => u x - ⨍ y in Metric.ball (0 : E) 1, u y ∂volume)
      (ENNReal.ofReal p) (volume.restrict (Metric.ball (0 : E) 1)) ≤
    ENNReal.ofReal (C_poinc_val d) *
      eLpNorm (fun x => ‖fderiv ℝ u x‖) (ENNReal.ofReal p)
        (volume.restrict (Metric.ball (0 : E) 1)) := by
  set B := Metric.ball (0 : E) 1
  set ubar := ⨍ y in B, u y ∂volume
  set f : E → ℝ := fun x => u x - ubar
  set g : E → ℝ := fun x => ‖fderiv ℝ u x‖
  have hpw : ∀ x ∈ B, ‖f x‖ ≤
      (2 : ℝ) ^ d / ((d : ℝ) * (volume (Metric.ball (0 : E) 1)).toReal) *
        ∫ y in B, g y * ‖x - y‖ ^ (1 - (d : ℝ)) ∂volume :=
    fun x hx => representation_formula_smooth one_pos hu x hx
  set μ := volume.restrict B
  set C_rep := (2 : ℝ) ^ d / ((d : ℝ) * (volume (Metric.ball (0 : E) 1)).toReal)
  set K : E → ℝ := fun z => ‖z‖ ^ (1 - (d : ℝ))
  set h : E → ℝ := fun x => ∫ y in B, g y * K (x - y) ∂volume
  have hpw_ae : ∀ᵐ x ∂μ, ‖f x‖ ≤ C_rep * h x := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx_mem
    exact hpw x hx_mem
  have h_step2 : eLpNorm f (ENNReal.ofReal p) μ ≤
      eLpNorm (fun x => C_rep * h x) (ENNReal.ofReal p) μ :=
    eLpNorm_mono_ae_real hpw_ae
  set M := (d : ℝ) * (volume (Metric.ball (0 : E) 1)).toReal * (2 * 1)
  -- Young-type bound: ‖h‖_p ≤ M · ‖g‖_p
  -- Proof outline:
  --   (a) pointwise Jensen: |h(x)|^p ≤ M^{p-1} · ∫_B |g(y)|^p K(x-y) dy
  --   (b) integrate in x, Fubini swap, kernel L¹ bound → ∫_B |h|^p ≤ M^p ∫_B |g|^p
  --   (c) take p-th root: ‖h‖_p ≤ M · ‖g‖_p
  have hYoung : eLpNorm h (ENNReal.ofReal p) μ ≤
      ENNReal.ofReal M * eLpNorm g (ENNReal.ofReal p) μ := by
    have hp_pos : 0 < p := lt_of_lt_of_le one_pos hp
    have hp_nonneg : 0 ≤ p := le_of_lt hp_pos
    have hd_pos : (0 : ℝ) < d := Nat.cast_pos.mpr (NeZero.pos d)
    have hvol_pos : (0 : ℝ) < (volume (Metric.ball (0 : E) 1)).toReal :=
      ENNReal.toReal_pos (measure_ball_pos volume 0 one_pos).ne' measure_ball_lt_top.ne
    have hM_pos : 0 < M := by positivity
    have hM_nonneg : 0 ≤ M := le_of_lt hM_pos
    have h1 : ContDiff ℝ 1 u := hu.of_le (by norm_num)
    have hcont_fderiv : Continuous (fderiv ℝ u) := h1.continuous_fderiv (by norm_num)
    have hg_cont : Continuous g := by
      simpa [g] using (continuous_norm.comp hcont_fderiv)
    obtain ⟨z₀, hz₀_mem, hz₀_max⟩ :=
      (isCompact_closedBall (0 : E) 1).exists_isMaxOn
        (Metric.nonempty_closedBall.mpr (le_of_lt one_pos)) hg_cont.continuousOn
    set Cg := g z₀
    have hg_le : ∀ y ∈ Metric.closedBall (0 : E) 1, g y ≤ Cg := by
      intro y hy
      exact hz₀_max hy
    -- K ≥ 0
    have hK_nonneg : ∀ z : E, 0 ≤ K z := fun z =>
      Real.rpow_nonneg (norm_nonneg z) _
    have hK_meas : Measurable K := by
      fun_prop
    -- Kernel L¹ bound: for x ∈ B, ∫_B K(x-y) dy ≤ M
    have hK_L1 : ∀ x ∈ B, ∫ y in B, K (x - y) ∂volume ≤ M := by
      intro x hx
      have := riesz_kernel_L1_bound one_pos x hx
      simp only [mul_one] at this
      convert this using 1
      simp [M]
    have hK_int : ∀ x ∈ B, IntegrableOn (fun y => K (x - y)) B volume := by
      intro x hx
      have hball_int : IntegrableOn (fun y => K (x - y)) (Metric.ball x (2 : ℝ)) volume := by
        have hmp := measurePreserving_add_right (volume : Measure E) x
        have hemb := (MeasurableEquiv.addRight x : E ≃ᵐ E).measurableEmbedding
        have hpre : (fun z : E => z + x) ⁻¹' Metric.ball x (2 : ℝ) = Metric.ball (0 : E) (2 : ℝ) := by
          ext z
          simp [Metric.mem_ball]
        rw [← hmp.integrableOn_comp_preimage hemb, hpre]
        exact (riesz_kernel_integrable (by norm_num : (0 : ℝ) < 2)).congr
          (ae_of_all _ fun z => by
            show ‖z‖ ^ (1 - (d : ℝ)) = K (x - (z + x))
            simp [K, norm_neg])
      refine hball_int.mono_set ?_
      intro y hy
      have hx_ball : ‖x‖ < 1 := by
        simpa [B, Metric.mem_ball, dist_zero_right] using hx
      have hy_ball : ‖y‖ < 1 := by
        simpa [B, Metric.mem_ball, dist_zero_right] using hy
      rw [Metric.mem_ball, dist_eq_norm]
      calc
        ‖y - x‖ ≤ ‖y‖ + ‖x‖ := norm_sub_le _ _
        _ < 1 + 1 := add_lt_add hy_ball hx_ball
        _ = (2 : ℝ) := by ring
    -- g is nonneg
    have hg_nonneg : ∀ y, 0 ≤ g y := fun y => norm_nonneg _
    -- h is nonneg (integral of nonneg * nonneg)
    have hh_nonneg : ∀ x, 0 ≤ h x := by
      intro x; apply setIntegral_nonneg measurableSet_ball
      intro y _; exact mul_nonneg (hg_nonneg y) (hK_nonneg (x - y))
    -- |g y| = g y since g ≥ 0
    have habs_g : ∀ y, |g y| = g y := fun y => abs_of_nonneg (hg_nonneg y)
    -- |h x| = h x since h ≥ 0
    have habs_h : ∀ x, |h x| = h x := fun x => abs_of_nonneg (hh_nonneg x)
    -- (a) Pointwise Jensen: |h(x)|^p ≤ M^{p-1} · ∫_B |g(y)|^p · K(x-y) dy
    -- This is the weighted power-mean inequality for integrals:
    --   (∫ f·w)^p ≤ (∫ w)^{p-1} · ∫ f^p·w
    -- Proof: normalize w to probability measure ν = w/(∫w), apply Jensen
    --   (∫ f dν)^p ≤ ∫ f^p dν  (convexity of t^p)
    --   then scale back by (∫ w)^p on left, (∫ w) on right.
    have hJensen : ∀ x ∈ B,
        |h x| ^ p ≤ M ^ (p - 1) * ∫ y in B, |g y| ^ p * K (x - y) ∂volume := by
      intro x hx
      rw [habs_h]
      -- Let W = ∫_B K(x-y) dy, the kernel integral
      set W := ∫ y in B, K (x - y) ∂volume with hW_def
      have hW_nonneg : 0 ≤ W :=
        setIntegral_nonneg measurableSet_ball (fun y _ => hK_nonneg (x - y))
      have hW_le_M : W ≤ M := hK_L1 x hx
      -- Rewrite |g y|^p = (g y)^p since g ≥ 0
      have : ∫ y in B, |g y| ^ p * K (x - y) ∂volume =
          ∫ y in B, (g y) ^ p * K (x - y) ∂volume := by
        congr 1; ext y; rw [habs_g]
      rw [this]
      -- Core weighted power-mean inequality:
      -- (∫ g·K)^p ≤ W^{p-1} · ∫ g^p·K, then use W ≤ M
      -- Weighted power-mean inequality for integrals:
      -- (∫ f·w)^p ≤ (∫ w)^{p-1} · ∫ f^p·w, for nonneg f, w, and p ≥ 1
      -- Proof sketch: normalize w to a probability measure, apply Jensen
      -- (convexOn_rpow hp) to get (∫ f dν)^p ≤ ∫ f^p dν, then rescale.
      -- We bound (∫ K)^{p-1} ≤ M^{p-1} since ∫ K ≤ M.
      --         by Hölder with measure K·vol, exponents p and q = p/(p-1).
      calc (h x) ^ p
          ≤ W ^ (p - 1) * ∫ y in B, (g y) ^ p * K (x - y) ∂volume := by
            -- Weighted power-mean: (∫ g·K)^p ≤ (∫ K)^{p-1} · ∫ g^p·K
            -- via Hölder with f₁ = g · K^{1/p}, f₂ = K^{1/q}, exponents p, q
            -- For p = 1: trivial (LHS = RHS with W^0 = 1)
            by_cases hp1 : p = 1
            · -- p = 1: (h x)^1 = h x = ∫ g·K ≤ 1 · ∫ g·K = W^0 · ∫ g·K
              simp [hp1, h]
            · -- p > 1: use Hölder's inequality on lintegrals
              -- Set up: q = p/(p-1) is the conjugate exponent
              have hp_gt1 : 1 < p := lt_of_le_of_ne hp (Ne.symm hp1)
              have hpq : p.HolderConjugate (p / (p - 1)) := Real.HolderConjugate.conjExponent hp_gt1
              -- Convert Bochner integrals to lintegrals (nonneg functions)
              -- h x = ∫_B g·K = toReal(∫⁻_B ofReal(g·K))
              set μB := volume.restrict B
              -- Hölder: ∫⁻ (f₁ * f₂) ≤ (∫⁻ f₁^p)^{1/p} · (∫⁻ f₂^q)^{1/q}
              -- with f₁ y = ofReal(g y · K(x-y)^{1/p}), f₂ y = ofReal(K(x-y)^{1/q})
              -- f₁ * f₂ = ofReal(g · K^{1/p} · K^{1/q}) = ofReal(g · K)
              -- f₁^p = ofReal(g^p · K), f₂^q = ofReal(K)
              exact weighted_power_mean_setIntegral measurableSet_ball hp_gt1
                hg_nonneg (fun y => hK_nonneg (x - y))
                (hg_cont.aemeasurable.mono_measure Measure.restrict_le_self)
                (hK_int x hx)
                (by
                  have hgpow_cont : Continuous fun y => (g y) ^ p :=
                    hg_cont.rpow_const (fun _ => Or.inr hp_pos.le)
                  simpa [mul_comm] using
                    (hK_int x hx).mul_continuousOn_of_subset hgpow_cont.continuousOn
                      measurableSet_ball (isCompact_closedBall (0 : E) 1)
                      Metric.ball_subset_closedBall)
        _ ≤ M ^ (p - 1) * ∫ y in B, (g y) ^ p * K (x - y) ∂volume := by
            apply mul_le_mul_of_nonneg_right _ (setIntegral_nonneg measurableSet_ball
              (fun y _ => mul_nonneg (Real.rpow_nonneg (hg_nonneg y) _) (hK_nonneg _)))
            exact Real.rpow_le_rpow hW_nonneg hW_le_M (by linarith)
    -- (b) Integrate Jensen bound over B, Fubini, kernel bound → ∫_B |h|^p ≤ M^p · ∫_B |g|^p
    -- Kernel L¹ bound in swapped variables: ∀ y ∈ B, ∫_B K(x-y) dx ≤ M
    have hK_L1_swap : ∀ y ∈ B, ∫ x in B, K (x - y) ∂volume ≤ M := by
      intro y hy
      have hsym : ∫ x in B, K (x - y) ∂volume = ∫ x in B, K (y - x) ∂volume := by
        congr 1; ext x; simp only [K]; congr 1; rw [norm_sub_rev]
      rw [hsym]; exact hK_L1 y hy
    have hgpow_cont : Continuous fun y => |g y| ^ p :=
      (hg_cont.abs.rpow_const (fun _ => Or.inr hp_pos.le))
    have hF_aesm :
        AEStronglyMeasurable
          (fun xy : E × E => |g xy.2| ^ p * K (xy.1 - xy.2))
          ((volume.restrict B).prod (volume.restrict B)) := by
      exact (((hgpow_cont.measurable.comp_aemeasurable measurable_snd.aemeasurable).mul
        (hK_meas.comp_aemeasurable
          (measurable_fst.sub measurable_snd).aemeasurable))).aestronglyMeasurable
    have hprod_int :
        Integrable
          (fun xy : E × E => |g xy.2| ^ p * K (xy.1 - xy.2))
          ((volume.restrict B).prod (volume.restrict B)) := by
      rw [integrable_prod_iff hF_aesm]
      constructor
      · filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
        simpa [mul_comm] using
          (hK_int x hx).mul_continuousOn_of_subset hgpow_cont.continuousOn
            measurableSet_ball (isCompact_closedBall (0 : E) 1)
            Metric.ball_subset_closedBall
      · have houter_bdd :
            ∀ᵐ x ∂(volume.restrict B).restrict Set.univ,
              ‖∫ y in B, ‖|g y| ^ p * K (x - y)‖ ∂volume‖ ≤ Cg ^ p * M := by
          filter_upwards [show ∀ᵐ x ∂(volume.restrict B).restrict Set.univ, x ∈ B by
            simpa [Measure.restrict_univ] using
              (ae_restrict_mem (μ := volume) measurableSet_ball)] with x hx
          have hslice_int : IntegrableOn (fun y => |g y| ^ p * K (x - y)) B volume := by
            simpa [mul_comm] using
              (hK_int x hx).mul_continuousOn_of_subset hgpow_cont.continuousOn
                measurableSet_ball (isCompact_closedBall (0 : E) 1)
                Metric.ball_subset_closedBall
          have hslice_const_int : IntegrableOn (fun y => Cg ^ p * K (x - y)) B volume := by
            exact (hK_int x hx).const_mul (Cg ^ p)
          rw [Real.norm_of_nonneg
            (setIntegral_nonneg measurableSet_ball (fun y _ => norm_nonneg _))]
          calc
            ∫ y in B, ‖|g y| ^ p * K (x - y)‖ ∂volume
                = ∫ y in B, |g y| ^ p * K (x - y) ∂volume := by
                    congr 1
                    ext y
                    rw [Real.norm_of_nonneg
                      (mul_nonneg (Real.rpow_nonneg (abs_nonneg _) _) (hK_nonneg _))]
            _ ≤ ∫ y in B, Cg ^ p * K (x - y) ∂volume := by
                exact setIntegral_mono_on hslice_int hslice_const_int measurableSet_ball
                  (fun y hy =>
                    mul_le_mul_of_nonneg_right
                      (Real.rpow_le_rpow (abs_nonneg _)
                        (by
                          rw [habs_g y]
                          simpa [Cg] using hg_le y (ball_subset_closedBall hy))
                        hp_nonneg)
                      (hK_nonneg _))
            _ = Cg ^ p * ∫ y in B, K (x - y) ∂volume := by
                rw [integral_const_mul]
            _ ≤ Cg ^ p * M := by
                apply mul_le_mul_of_nonneg_left (hK_L1 x hx)
                exact Real.rpow_nonneg (le_trans (hg_nonneg _) (hg_le z₀ hz₀_mem)) _
        simpa [Measure.restrict_univ] using
          (Measure.integrableOn_of_bounded
            (μ := volume.restrict B) (s := Set.univ)
            (by simpa [B] using measure_ball_lt_top.ne)
            (hF_aesm.norm.integral_prod_right') houter_bdd).integrable
    have hFh_aesm :
        AEStronglyMeasurable
          (fun xy : E × E => g xy.2 * K (xy.1 - xy.2))
          ((volume.restrict B).prod (volume.restrict B)) := by
      exact ((hg_cont.measurable.comp_aemeasurable measurable_snd.aemeasurable).mul
        (hK_meas.comp_aemeasurable
          (measurable_fst.sub measurable_snd).aemeasurable)).aestronglyMeasurable
    have hh_aesm : AEStronglyMeasurable h (volume.restrict B) := by
      change AEStronglyMeasurable (fun x => ∫ y, g y * K (x - y) ∂(volume.restrict B))
        (volume.restrict B)
      exact hFh_aesm.integral_prod_right'
    have hh_bound : ∀ x ∈ B, h x ≤ Cg * M := by
      intro x hx
      have hslice_int : IntegrableOn (fun y => g y * K (x - y)) B volume := by
        simpa [mul_comm] using
          (hK_int x hx).mul_continuousOn_of_subset hg_cont.continuousOn
            measurableSet_ball (isCompact_closedBall (0 : E) 1)
            Metric.ball_subset_closedBall
      have hslice_const_int : IntegrableOn (fun y => Cg * K (x - y)) B volume := by
        exact (hK_int x hx).const_mul Cg
      calc
        h x = ∫ y in B, g y * K (x - y) ∂volume := rfl
        _ ≤ ∫ y in B, Cg * K (x - y) ∂volume := by
            exact setIntegral_mono_on hslice_int hslice_const_int measurableSet_ball
              (fun y hy =>
                mul_le_mul_of_nonneg_right
                  (hg_le y (ball_subset_closedBall hy))
                  (hK_nonneg _))
        _ = Cg * ∫ y in B, K (x - y) ∂volume := by
            rw [integral_const_mul]
        _ ≤ Cg * M := by
            apply mul_le_mul_of_nonneg_left (hK_L1 x hx)
            exact le_trans (hg_nonneg _) (hg_le z₀ hz₀_mem)
    have hhpow_int : IntegrableOn (fun x => |h x| ^ p) B volume := by
      change Integrable (fun x => |h x| ^ p) (volume.restrict B)
      have hhpow_aesm : AEStronglyMeasurable (fun x => |h x| ^ p) (volume.restrict B) := by
        exact ((Real.continuous_rpow_const hp_pos.le).measurable.comp_aemeasurable
          hh_aesm.aemeasurable.abs).aestronglyMeasurable
      have hhpow_bdd :
          ∀ᵐ x ∂(volume.restrict B).restrict Set.univ, ‖|h x| ^ p‖ ≤ (Cg * M) ^ p := by
        filter_upwards [show ∀ᵐ x ∂(volume.restrict B).restrict Set.univ, x ∈ B by
          simpa [Measure.restrict_univ] using
            (ae_restrict_mem (μ := volume) measurableSet_ball)] with x hx
        rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _),
          abs_of_nonneg (hh_nonneg x)]
        exact Real.rpow_le_rpow (hh_nonneg x) (hh_bound x hx) hp_nonneg
      simpa [Measure.restrict_univ] using
        (Measure.integrableOn_of_bounded
          (μ := volume.restrict B) (s := Set.univ)
          (by simpa [B] using measure_ball_lt_top.ne)
          hhpow_aesm hhpow_bdd).integrable
    have hgpow_int : IntegrableOn (fun y => |g y| ^ p) B volume := by
      exact
        ((hgpow_cont.continuousOn.integrableOn_compact
          (isCompact_closedBall (0 : E) 1)).mono_set Metric.ball_subset_closedBall)
    have hIntBound : ∫ x in B, |h x| ^ p ∂volume ≤
        M ^ p * ∫ y in B, |g y| ^ p ∂volume := by
      have hstep1 : ∫ x in B, |h x| ^ p ∂volume ≤
          ∫ x in B, (M ^ (p - 1) * ∫ y in B, |g y| ^ p * K (x - y) ∂volume) ∂volume := by
        exact setIntegral_mono_on
          (hf := hhpow_int)
          (hg := by
            have houter_int :
                Integrable
                  (fun x => ∫ y, |g y| ^ p * K (x - y) ∂(volume.restrict B))
                  (volume.restrict B) := by
              refine hprod_int.integral_norm_prod_left.congr ?_
              filter_upwards with x
              congr 1
              ext y
              rw [Real.norm_of_nonneg
                (mul_nonneg (Real.rpow_nonneg (abs_nonneg _) _) (hK_nonneg _))]
            exact houter_int.const_mul (M ^ (p - 1))
          )
          measurableSet_ball hJensen
      have hFubini : ∫ x in B, (∫ y in B, |g y| ^ p * K (x - y) ∂volume) ∂volume =
          ∫ y in B, (∫ x in B, |g y| ^ p * K (x - y) ∂volume) ∂volume := by
        let μB := volume.restrict B
        change ∫ x, (∫ y, |g y| ^ p * K (x - y) ∂μB) ∂μB =
            ∫ y, (∫ x, |g y| ^ p * K (x - y) ∂μB) ∂μB
        exact integral_integral_swap hprod_int
      have hpull : ∀ y, ∫ x in B, |g y| ^ p * K (x - y) ∂volume =
          |g y| ^ p * ∫ x in B, K (x - y) ∂volume := by
        intro y; exact integral_const_mul _ _
      have hstep4 : ∫ y in B, |g y| ^ p * (∫ x in B, K (x - y) ∂volume) ∂volume ≤
          ∫ y in B, |g y| ^ p * M ∂volume := by
        apply setIntegral_mono_on
        · have hinner_int :
              Integrable
                (fun y => ∫ x, |g y| ^ p * K (x - y) ∂(volume.restrict B))
                (volume.restrict B) := by
            refine hprod_int.integral_norm_prod_right.congr ?_
            filter_upwards with y
            congr 1
            ext x
            rw [Real.norm_of_nonneg
              (mul_nonneg (Real.rpow_nonneg (abs_nonneg _) _) (hK_nonneg _))]
          refine hinner_int.congr ?_
          filter_upwards with y
          exact hpull y
        · simpa [mul_comm] using hgpow_int.mul_const M
        · exact measurableSet_ball
        · intro y hy
          apply mul_le_mul_of_nonneg_left (hK_L1_swap y hy)
          exact Real.rpow_nonneg (abs_nonneg _) _
      -- M^{p-1} * M = M^p
      have hMpow : M ^ (p - 1) * M = M ^ p := by
        rw [mul_comm]
        -- Goal: M * M ^ (p - 1) = M ^ p
        -- Convert the leading M to M ^ (1:ℝ) without touching M inside rpow
        change M * M ^ (p - 1) = M ^ p
        conv_lhs => lhs; rw [show (M : ℝ) = M ^ (1 : ℝ) from (Real.rpow_one M).symm]
        rw [← Real.rpow_add hM_pos]
        congr 1; ring
      calc ∫ x in B, |h x| ^ p ∂volume
          ≤ ∫ x in B, (M ^ (p - 1) * ∫ y in B, |g y| ^ p * K (x - y) ∂volume) ∂volume :=
            hstep1
        _ = M ^ (p - 1) * ∫ x in B, (∫ y in B, |g y| ^ p * K (x - y) ∂volume) ∂volume := by
            rw [integral_const_mul]
        _ = M ^ (p - 1) * ∫ y in B, (∫ x in B, |g y| ^ p * K (x - y) ∂volume) ∂volume := by
            rw [hFubini]
        _ = M ^ (p - 1) * ∫ y in B, |g y| ^ p * (∫ x in B, K (x - y) ∂volume) ∂volume := by
            congr 1; congr 1; ext y; exact hpull y
        _ ≤ M ^ (p - 1) * ∫ y in B, |g y| ^ p * M ∂volume := by
            apply mul_le_mul_of_nonneg_left hstep4
            exact Real.rpow_nonneg (le_of_lt hM_pos) _
        _ = M ^ (p - 1) * (M * ∫ y in B, |g y| ^ p ∂volume) := by
            congr 1; simp_rw [mul_comm _ M]; rw [integral_const_mul]
        _ = M ^ p * ∫ y in B, |g y| ^ p ∂volume := by
            rw [← mul_assoc, hMpow]
    -- (c) Convert the integral bound to an `L^p` bound.
    have hIntBoundμ : ∫ x, |h x| ^ p ∂μ ≤ M ^ p * ∫ y, |g y| ^ p ∂μ := by
      simpa [μ] using hIntBound
    have h_pow : eLpNorm h (ENNReal.ofReal p) μ ^ p ≤
        (ENNReal.ofReal M * eLpNorm g (ENNReal.ofReal p) μ) ^ p := by
      rw [← lintegral_rpow_norm_eq_eLpNorm_pow' hp_pos (f := h)]
      rw [ENNReal.mul_rpow_of_nonneg _ _ (le_of_lt hp_pos)]
      rw [← lintegral_rpow_norm_eq_eLpNorm_pow' hp_pos (f := g)]
      simp_rw [ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (le_of_lt hp_pos),
        Real.norm_eq_abs]
      rw [← ofReal_integral_eq_lintegral_ofReal hhpow_int.integrable
          (ae_of_all _ (fun x => Real.rpow_nonneg (abs_nonneg _) _)),
        ← ofReal_integral_eq_lintegral_ofReal hgpow_int.integrable
          (ae_of_all _ (fun x => Real.rpow_nonneg (abs_nonneg _) _))]
      rw [ENNReal.ofReal_rpow_of_nonneg (le_of_lt hM_pos) (le_of_lt hp_pos),
        ← ENNReal.ofReal_mul (Real.rpow_nonneg (le_of_lt hM_pos) _)]
      exact ENNReal.ofReal_le_ofReal hIntBoundμ
    have hp_inv : 0 < (1 / p : ℝ) := div_pos one_pos hp_pos
    have hroot := ENNReal.rpow_le_rpow h_pow hp_inv.le
    rwa [← ENNReal.rpow_mul, ← ENNReal.rpow_mul,
      show p * (1 / p) = 1 from by field_simp [hp_pos.ne'],
      ENNReal.rpow_one, ENNReal.rpow_one] at hroot
  calc eLpNorm f (ENNReal.ofReal p) μ
      ≤ eLpNorm (fun x => C_rep * h x) (ENNReal.ofReal p) μ := h_step2
    _ ≤ ENNReal.ofReal C_rep * eLpNorm h (ENNReal.ofReal p) μ := by
        have : (fun x => C_rep * h x) = C_rep • h := by ext x; simp [Pi.smul_apply, smul_eq_mul]
        rw [this]
        calc eLpNorm (C_rep • h) (ENNReal.ofReal p) μ
            ≤ ‖C_rep‖ₑ * eLpNorm h (ENNReal.ofReal p) μ := eLpNorm_const_smul_le
          _ = ENNReal.ofReal C_rep * eLpNorm h (ENNReal.ofReal p) μ := by
              congr 1
              rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (by positivity)]
    _ ≤ ENNReal.ofReal C_rep * (ENNReal.ofReal M * eLpNorm g (ENNReal.ofReal p) μ) := by
        gcongr
    _ = ENNReal.ofReal (C_rep * M) * eLpNorm g (ENNReal.ofReal p) μ := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
    _ ≤ ENNReal.ofReal (C_poinc_val d) * eLpNorm g (ENNReal.ofReal p) μ := by
        gcongr
        simp only [C_rep, M, C_poinc_val]
        have hd_pos : (0 : ℝ) < d := Nat.cast_pos.mpr (NeZero.pos d)
        have hvol_pos : (0 : ℝ) < (volume (Metric.ball (0 : E) 1)).toReal :=
          ENNReal.toReal_pos (measure_ball_pos volume 0 one_pos).ne' measure_ball_lt_top.ne
        have hdv_ne : (d : ℝ) * (volume (Metric.ball (0 : E) 1)).toReal ≠ 0 :=
          mul_ne_zero hd_pos.ne' hvol_pos.ne'
        rw [mul_one]
        rw [div_mul_comm, mul_comm ((d : ℝ) * _) 2, mul_div_cancel_of_imp (fun h => absurd h hdv_ne)]
        calc (2 : ℝ) ^ d * 2 * ↑d = 2 * 2 ^ d * ↑d := by ring
          _ ≥ 2 * 2 ^ d * 1 := by
              nlinarith [pow_pos (show (0 : ℝ) < 2 by norm_num) d,
                show (1 : ℝ) ≤ (d : ℝ) from by
                  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)]
          _ = 2 * 2 ^ d := by ring

end DeGiorgi
