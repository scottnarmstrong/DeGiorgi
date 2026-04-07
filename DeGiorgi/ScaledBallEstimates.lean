import DeGiorgi.BallScaling
import DeGiorgi.Localization
import DeGiorgi.WeakHarnack

/-!
# Chapter 07: Scaled Moser Corollaries

This file packages the unit-ball Moser estimates from Chapter 06 into
arbitrary-ball corollaries using the affine transport machinery from
`BallScaling`.

The resulting theorems provide the arbitrary-ball interface used downstream in
the Harnack and Holder arguments.
-/

noncomputable section

open MeasureTheory

namespace DeGiorgi

variable {d : ℕ} [NeZero d]

local notation "E" => AmbientSpace d

/-- `C_weakHarnack` with a built-in decidability check so that definitions
and constants that mention it need not carry an explicit `hd` proof. When
`2 < d` this equals `C_weakHarnack d hd`; otherwise it defaults to `1`. -/
noncomputable def C_weakHarnack_of (d : ℕ) [NeZero d] : ℝ :=
  if hd : 2 < (d : ℝ) then C_weakHarnack d hd else 1

theorem C_weakHarnack_of_eq (hd : 2 < (d : ℝ)) :
    C_weakHarnack_of d = C_weakHarnack d hd :=
  dif_pos hd

theorem one_le_C_weakHarnack_of : 1 ≤ C_weakHarnack_of d := by
  unfold C_weakHarnack_of
  split
  · next hd => exact one_le_C_weakHarnack hd
  · exact le_refl 1

omit [NeZero d] in
private lemma inverse_affine_preimage_ball_mul
    {x₀ : E} {R ρ : ℝ} (hR : 0 < R) :
    (fun x : E => R⁻¹ • (x - x₀)) ⁻¹' Metric.ball (0 : E) ρ = Metric.ball x₀ (R * ρ) := by
  ext x
  simp only [Set.mem_preimage, Metric.mem_ball, dist_eq_norm, sub_zero]
  constructor
  · intro hx
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hR.le)] at hx
    exact (inv_mul_lt_iff₀ hR).1 hx
  · intro hx
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hR.le)]
    exact (inv_mul_lt_iff₀ hR).2 hx

omit [NeZero d] in
private lemma affine_map_restrict_ball_mul
    {x₀ : E} {R ρ : ℝ} (hR : 0 < R) :
    Measure.map (fun z : E => x₀ + R • z) (volume.restrict (Metric.ball (0 : E) ρ)) =
      ENNReal.ofReal (|R ^ Module.finrank ℝ E|⁻¹) •
        (volume.restrict (Metric.ball x₀ (R * ρ))) := by
  have hmeas : Measurable (fun z : E => x₀ + R • z) :=
    (measurable_const_add x₀).comp (measurable_const_smul R)
  calc
    Measure.map (fun z : E => x₀ + R • z) (volume.restrict (Metric.ball (0 : E) ρ))
        = Measure.map (fun z : E => x₀ + R • z)
            (volume.restrict ((fun z : E => x₀ + R • z) ⁻¹' Metric.ball x₀ (R * ρ))) := by
              rw [affine_preimage_ball_mul (d := d) (x₀ := x₀) (R := R) (ρ := ρ) hR]
    _ = (Measure.map (fun z : E => x₀ + R • z) volume).restrict (Metric.ball x₀ (R * ρ)) := by
          rw [Measure.restrict_map hmeas measurableSet_ball]
    _ = (ENNReal.ofReal (|R ^ Module.finrank ℝ E|⁻¹) • (volume : Measure E)).restrict
          (Metric.ball x₀ (R * ρ)) := by
            rw [show (fun z : E => x₀ + R • z) = (fun z => x₀ + z) ∘ (fun z => R • z) from rfl]
            rw [← Measure.map_map (measurable_const_add x₀) (measurable_const_smul R)]
            rw [Measure.map_addHaar_smul volume hR.ne']
            rw [Measure.map_smul, (measurePreserving_add_left volume x₀).map_eq, abs_inv]
    _ = ENNReal.ofReal (|R ^ Module.finrank ℝ E|⁻¹) •
          (volume.restrict (Metric.ball x₀ (R * ρ))) := by
            rw [Measure.restrict_smul]

omit [NeZero d] in
private lemma inverse_affine_map_restrict_ball_mul
    {x₀ : E} {R ρ : ℝ} (hR : 0 < R) :
    Measure.map (fun x : E => R⁻¹ • (x - x₀))
        (volume.restrict (Metric.ball x₀ (R * ρ))) =
      ENNReal.ofReal (|R⁻¹ ^ Module.finrank ℝ E|⁻¹) •
        (volume.restrict (Metric.ball (0 : E) ρ)) := by
  let S : E → E := fun x => R⁻¹ • (x - x₀)
  have hmeas : Measurable S :=
    (measurable_const_smul R⁻¹).comp (measurable_id.sub measurable_const)
  have hrestrict :
      Measure.map S (volume.restrict (Metric.ball x₀ (R * ρ))) =
        (Measure.map S volume).restrict (Metric.ball (0 : E) ρ) := by
    simpa [S, inverse_affine_preimage_ball_mul (d := d) (x₀ := x₀) (R := R) (ρ := ρ) hR] using
      (Measure.restrict_map (μ := volume) (f := S) hmeas
        (s := Metric.ball (0 : E) ρ) measurableSet_ball).symm
  calc
    Measure.map S (volume.restrict (Metric.ball x₀ (R * ρ)))
        = (Measure.map S volume).restrict (Metric.ball (0 : E) ρ) := hrestrict
    _ = (ENNReal.ofReal (|R⁻¹ ^ Module.finrank ℝ E|⁻¹) • (volume : Measure E)).restrict
          (Metric.ball (0 : E) ρ) := by
            have hmap :
                Measure.map S (volume : Measure E) =
                  ENNReal.ofReal (|R⁻¹ ^ Module.finrank ℝ E|⁻¹) • (volume : Measure E) := by
              rw [show S = (fun z : E => R⁻¹ • z) ∘ (fun z : E => (-x₀) + z) from by
                  ext z
                  simp [S, sub_eq_add_neg, add_comm]]
              rw [← Measure.map_map (measurable_const_smul R⁻¹) (measurable_const_add (-x₀))]
              rw [(measurePreserving_add_left volume (-x₀)).map_eq]
              simpa [abs_inv] using
                (Measure.map_addHaar_smul (μ := (volume : Measure E))
                  (r := R⁻¹) (inv_ne_zero hR.ne'))
            rw [hmap]
    _ = ENNReal.ofReal (|R⁻¹ ^ Module.finrank ℝ E|⁻¹) •
          (volume.restrict (Metric.ball (0 : E) ρ)) := by
            rw [Measure.restrict_smul]

omit [NeZero d] in
private lemma inverse_affine_scale_measure_ne_zero
    {R : ℝ} (hR : 0 < R) :
    ENNReal.ofReal (|R⁻¹ ^ Module.finrank ℝ E|⁻¹) ≠ 0 := by
  rw [ENNReal.ofReal_ne_zero_iff]
  have hpow_ne : R⁻¹ ^ Module.finrank ℝ E ≠ 0 := by
    exact pow_ne_zero _ (inv_ne_zero hR.ne')
  have habs_pos : 0 < |R⁻¹ ^ Module.finrank ℝ E| := by
    exact abs_pos.mpr hpow_ne
  exact inv_pos.mpr habs_pos

omit [NeZero d] in
private lemma integrableOn_rescaleToUnitBall_iff
    {x₀ : E} {R ρ : ℝ} (hR : 0 < R) {f : E → ℝ} :
    IntegrableOn (fun z => f (x₀ + R • z)) (Metric.ball (0 : E) ρ) volume ↔
      IntegrableOn f (Metric.ball x₀ (R * ρ)) volume := by
  let T : E → E := fun z => x₀ + R • z
  have hT_emb : MeasurableEmbedding T :=
    ((MeasurableEquiv.addLeft x₀).measurableEmbedding).comp
      ((Homeomorph.smulOfNeZero R hR.ne').toMeasurableEquiv.measurableEmbedding)
  have hiff :
      IntegrableOn (fun z => f (x₀ + R • z)) (Metric.ball (0 : E) ρ) volume ↔
        IntegrableOn f (Metric.ball x₀ (R * ρ)) (Measure.map T volume) := by
    have hmap_iff :=
      hT_emb.integrableOn_map_iff (μ := volume) (s := Metric.ball x₀ (R * ρ)) (f := f)
    simpa [T, affine_preimage_ball_mul (d := d) (x₀ := x₀) (R := R) (ρ := ρ) hR] using
      hmap_iff.symm
  have hsmul :
      IntegrableOn f (Metric.ball x₀ (R * ρ)) (Measure.map T volume) ↔
        IntegrableOn f (Metric.ball x₀ (R * ρ)) volume := by
    rw [show Measure.map T volume =
        ENNReal.ofReal (|R ^ Module.finrank ℝ E|⁻¹) • (volume : Measure E) from by
          rw [show T = (fun z : E => x₀ + z) ∘ (fun z : E => R • z) from rfl]
          rw [← Measure.map_map (measurable_const_add x₀) (measurable_const_smul R)]
          rw [Measure.map_addHaar_smul volume hR.ne']
          rw [Measure.map_smul, (measurePreserving_add_left volume x₀).map_eq, abs_inv]]
    rw [IntegrableOn, Measure.restrict_smul]
    exact integrable_smul_measure (affine_scale_measure_ne_zero (d := d) hR) ENNReal.ofReal_ne_top
  exact hiff.trans hsmul

omit [NeZero d] in
private lemma integral_comp_affine_ball
    {x₀ : E} {R ρ : ℝ} (hR : 0 < R) (f : E → ℝ) :
    ∫ z in Metric.ball (0 : E) ρ, f (x₀ + R • z) =
      (R ^ Module.finrank ℝ E)⁻¹ * ∫ x in Metric.ball x₀ (R * ρ), f x := by
  open scoped Pointwise in
  have hscale := Measure.setIntegral_comp_smul_of_pos volume (fun x => f (x₀ + x))
    (Metric.ball (0 : E) ρ) hR
  rw [show R • Metric.ball (0 : E) ρ = Metric.ball (0 : E) (R * ρ) from by
      rw [_root_.smul_ball hR.ne' (0 : E) ρ]
      simp [Real.norm_of_nonneg hR.le]] at hscale
  rw [hscale]
  congr 1
  rw [show Metric.ball x₀ (R * ρ) = (x₀ + ·) '' Metric.ball (0 : E) (R * ρ) from by
      ext x
      constructor
      · intro hx
        refine ⟨x - x₀, ?_, ?_⟩
        · simpa [Metric.mem_ball, dist_eq_norm, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
            using hx
        · abel_nf
      · rintro ⟨y, hy, rfl⟩
        simpa [Metric.mem_ball, dist_eq_norm, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
          using hy]
  exact ((measurePreserving_add_left volume x₀).setIntegral_image_emb
            (MeasurableEquiv.addLeft x₀).measurableEmbedding f (Metric.ball (0 : E) (R * ρ))).symm

/-- Moser `L^p → L∞` estimate on an arbitrary ball, in the same a.e.-power
format as the unit-ball Chapter 06 theorem. -/
theorem linfty_subsolution_Moser_on_ball
    (hd : 2 < (d : ℝ))
    {x₀ : E} {R : ℝ} (hR : 0 < R)
    (A : NormalizedEllipticCoeff d (Metric.ball x₀ R))
    {u : E → ℝ} {p₀ : ℝ} (hp₀ : 1 < p₀)
    (hsub : IsSubsolution A.1 u)
    (hposInt :
      IntegrableOn (fun x => |max (u x) 0| ^ p₀) (Metric.ball x₀ R) volume) :
    ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ (R / 2 : ℝ))),
      |max (u x) 0| ^ p₀ ≤
        C_Moser d * A.1.Λ ^ ((d : ℝ) / 2) *
          (p₀ / (p₀ - 1)) ^ (d : ℝ) *
          ((R ^ Module.finrank ℝ E)⁻¹ *
            ∫ x in Metric.ball x₀ R, |max (u x) 0| ^ p₀ ∂volume) := by
  let uR : E → ℝ := rescaleToUnitBall (d := d) (x₀ := x₀) (R := R) u
  let AR : NormalizedEllipticCoeff d (Metric.ball (0 : E) 1) :=
    rescaleNormalizedCoeffToUnitBall (d := d) (x₀ := x₀) (R := R) hR A
  have hsubR : IsSubsolution AR.1 uR := by
    change IsSubsolution
      (rescaleCoeffToUnitBall (d := d) (x₀ := x₀) (R := R) hR A.1)
      (rescaleToUnitBall (d := d) (x₀ := x₀) (R := R) u)
    exact rescaleToUnitBall_isSubsolution (d := d) (x₀ := x₀) (R := R) hR A.1 hsub
  have hIntR :
      IntegrableOn (fun z => |max (uR z) 0| ^ p₀) (Metric.ball (0 : E) 1) volume := by
    dsimp [uR]
    have hposInt' :
        IntegrableOn (fun x => |max (u x) 0| ^ p₀) (Metric.ball x₀ (R * (1 : ℝ))) volume := by
      simpa using hposInt
    exact (integrableOn_rescaleToUnitBall_iff
      (d := d) (x₀ := x₀) (R := R) (ρ := (1 : ℝ)) hR
      (f := fun x => |max (u x) 0| ^ p₀)).2 hposInt'
  have hInt_eq :
      ∫ z in Metric.ball (0 : E) 1, |max (uR z) 0| ^ p₀ ∂volume =
        (R ^ Module.finrank ℝ E)⁻¹ *
          ∫ x in Metric.ball x₀ R, |max (u x) 0| ^ p₀ ∂volume := by
    simpa [uR] using integral_comp_affine_ball
      (d := d) (x₀ := x₀) (R := R) (ρ := (1 : ℝ)) hR
      (fun x => |max (u x) 0| ^ p₀)
  have hunit :
      ∀ᵐ z ∂(volume.restrict (Metric.ball (0 : E) (1 / 2 : ℝ))),
        |max (u (x₀ + R • z)) 0| ^ p₀ ≤
          C_Moser d * A.1.Λ ^ ((d : ℝ) / 2) *
            (p₀ / (p₀ - 1)) ^ (d : ℝ) *
            ((R ^ Module.finrank ℝ E)⁻¹ *
              ∫ x in Metric.ball x₀ R, |max (u x) 0| ^ p₀ ∂volume) := by
    have hbase := linfty_subsolution_Moser (d := d) hd AR hp₀ hsubR hIntR
    rw [hInt_eq] at hbase
    simpa [uR, AR] using hbase
  have hRhalf : R * (1 / 2 : ℝ) = R / 2 := by
    ring
  have hmap_half :
      Measure.map (fun x : E => R⁻¹ • (x - x₀))
        (volume.restrict (Metric.ball x₀ (R / 2 : ℝ))) =
      ENNReal.ofReal (|R⁻¹ ^ Module.finrank ℝ E|⁻¹) •
        (volume.restrict (Metric.ball (0 : E) (1 / 2 : ℝ))) := by
    simpa [hRhalf] using
      inverse_affine_map_restrict_ball_mul
        (d := d) (x₀ := x₀) (R := R) (ρ := (1 / 2 : ℝ)) hR
  have hscaled :
      ∀ᵐ z ∂ ENNReal.ofReal (|R⁻¹ ^ Module.finrank ℝ E|⁻¹) •
          (volume.restrict (Metric.ball (0 : E) (1 / 2 : ℝ))),
        |max (u (x₀ + R • z)) 0| ^ p₀ ≤
          C_Moser d * A.1.Λ ^ ((d : ℝ) / 2) *
            (p₀ / (p₀ - 1)) ^ (d : ℝ) *
            ((R ^ Module.finrank ℝ E)⁻¹ *
              ∫ x in Metric.ball x₀ R, |max (u x) 0| ^ p₀ ∂volume) := by
    rw [ae_iff]
    rw [Measure.smul_apply]
    rw [ae_iff] at hunit
    rw [hunit]
    simp
  have hmap_event :
      ∀ᵐ z ∂ Measure.map (fun x : E => R⁻¹ • (x - x₀))
          (volume.restrict (Metric.ball x₀ (R / 2 : ℝ))),
        |max (u (x₀ + R • z)) 0| ^ p₀ ≤
          C_Moser d * A.1.Λ ^ ((d : ℝ) / 2) *
            (p₀ / (p₀ - 1)) ^ (d : ℝ) *
            ((R ^ Module.finrank ℝ E)⁻¹ *
              ∫ x in Metric.ball x₀ R, |max (u x) 0| ^ p₀ ∂volume) := by
    rw [hmap_half]
    exact hscaled
  have htarget :
      ∀ᵐ x ∂(volume.restrict (Metric.ball x₀ (R / 2 : ℝ))),
        |max (u (x₀ + R • (R⁻¹ • (x - x₀)))) 0| ^ p₀ ≤
          C_Moser d * A.1.Λ ^ ((d : ℝ) / 2) *
            (p₀ / (p₀ - 1)) ^ (d : ℝ) *
            ((R ^ Module.finrank ℝ E)⁻¹ *
              ∫ x in Metric.ball x₀ R, |max (u x) 0| ^ p₀ ∂volume) := by
    exact ae_of_ae_map
      (((measurable_const_smul R⁻¹).comp (measurable_id.sub measurable_const)).aemeasurable)
      hmap_event
  filter_upwards [htarget] with x hx
  have hcancel : x₀ + R • (R⁻¹ • (x - x₀)) = x := by
    calc
      x₀ + R • (R⁻¹ • (x - x₀)) = x₀ + (R * R⁻¹) • (x - x₀) := by
        rw [smul_smul]
      _ = x₀ + (1 : ℝ) • (x - x₀) := by
        simp [hR.ne']
      _ = x := by
        simp
  simpa [hcancel] using hx

/-- Weak Harnack on an arbitrary ball, obtained by rescaling the unit-ball
Chapter 06 statement. -/
theorem weak_harnack_on_ball
    (hd : 2 < (d : ℝ))
    {x₀ : E} {R : ℝ} (hR : 0 < R)
    (A : NormalizedEllipticCoeff d (Metric.ball x₀ R))
    {u : E → ℝ} {q : ℝ} (hq : 0 < q) (hq1 : q < 1)
    (hu_pos : ∀ x ∈ Metric.ball x₀ R, 0 < u x)
    (hsuper : IsSupersolution A.1 u) :
    (((R ^ Module.finrank ℝ E)⁻¹ *
        ∫ x in Metric.ball x₀ (R / 4 : ℝ),
          |u x| ^ (q * (d : ℝ) / ((d : ℝ) - 2)) ∂volume)) ^
          (((d : ℝ) - 2) / (q * (d : ℝ))) ≤
      (C_weakHarnack d hd / (1 - q) ^ (weak_harnack_decay_exp d)) ^
        (A.1.Λ ^ ((1 : ℝ) / 2)) *
        essInf (fun z : E => u (x₀ + R • z))
          (volume.restrict (Metric.ball (0 : E) (1 / 4 : ℝ))) := by
  let uR : E → ℝ := rescaleToUnitBall (d := d) (x₀ := x₀) (R := R) u
  let AR : NormalizedEllipticCoeff d (Metric.ball (0 : E) 1) :=
    rescaleNormalizedCoeffToUnitBall (d := d) (x₀ := x₀) (R := R) hR A
  have hposR : ∀ z ∈ Metric.ball (0 : E) 1, 0 < uR z := by
    intro z hz
    have hz_ball : x₀ + R • z ∈ Metric.ball x₀ R := by
      have hz' : z ∈ (fun y : E => x₀ + R • y) ⁻¹' Metric.ball x₀ (R * (1 : ℝ)) := by
        rw [affine_preimage_ball_mul (d := d) (x₀ := x₀) (R := R) (ρ := (1 : ℝ)) hR]
        exact hz
      simpa using hz'
    exact hu_pos (x₀ + R • z) hz_ball
  have hsuperR : IsSupersolution AR.1 uR := by
    change IsSupersolution
      (rescaleCoeffToUnitBall (d := d) (x₀ := x₀) (R := R) hR A.1)
      (rescaleToUnitBall (d := d) (x₀ := x₀) (R := R) u)
    exact rescaleToUnitBall_isSupersolution (d := d) (x₀ := x₀) (R := R) hR A.1 hsuper
  have hInt_eq :
      ∫ z in Metric.ball (0 : E) (1 / 4 : ℝ),
          |uR z| ^ (q * (d : ℝ) / ((d : ℝ) - 2)) ∂volume =
        (R ^ Module.finrank ℝ E)⁻¹ *
          ∫ x in Metric.ball x₀ (R / 4 : ℝ),
            |u x| ^ (q * (d : ℝ) / ((d : ℝ) - 2)) ∂volume := by
    dsimp [uR]
    simpa [show R * (1 / 4 : ℝ) = R / 4 by ring] using
      integral_comp_affine_ball
        (d := d) (x₀ := x₀) (R := R) (ρ := (1 / 4 : ℝ)) hR
        (fun x => |u x| ^ (q * (d : ℝ) / ((d : ℝ) - 2)))
  have hbase := weak_harnack (d := d) hd AR hq hq1 hposR hsuperR
  rw [hInt_eq] at hbase
  simpa [AR, uR, rescaleNormalizedCoeffToUnitBall, rescaleCoeffToUnitBall,
    rescaleToUnitBall] using hbase

end DeGiorgi
