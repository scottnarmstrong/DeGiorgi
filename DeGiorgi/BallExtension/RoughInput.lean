import DeGiorgi.BallExtension.Geometry

/-!
# Ball Extension Rough Input

Analytic bounds, measurable-function interfaces, and rough-input witness
packaging for the explicit unit-ball extension operator.
-/

noncomputable section

open MeasureTheory Metric Filter Topology Set Function Matrix
open scoped ENNReal NNReal RealInnerProductSpace

namespace DeGiorgi

variable {d : ℕ} [NeZero d]

local notation "E" => EuclideanSpace ℝ (Fin d)

omit [NeZero d] in
private lemma lintegral_rpow_abs_unitBallExtension_outerShell_le
    {p : ℝ} (hp : 0 ≤ p) {u : E → ℝ} :
    ∫⁻ x in unitBallOuterShell (d := d),
        (ENNReal.ofReal |unitBallExtension (d := d) u x|) ^ p ∂volume
      ≤ ENNReal.ofReal ((2 : ℝ) ^ (2 * d)) *
        ∫⁻ x in Metric.ball (0 : E) 1, (ENNReal.ofReal |u x|) ^ p ∂volume := by
  let Φ : E → ℝ≥0∞ := fun x => (ENNReal.ofReal |u x|) ^ p
  let inv : E → E := EuclideanGeometry.inversion (0 : E) 1
  calc
    ∫⁻ x in unitBallOuterShell (d := d),
        (ENNReal.ofReal |unitBallExtension (d := d) u x|) ^ p ∂volume
      ≤ ∫⁻ x in unitBallOuterShell (d := d), Φ (inv x) ∂volume := by
          refine lintegral_mono_ae ?_
          rw [ae_restrict_iff' measurableSet_unitBallOuterShell]
          refine Filter.Eventually.of_forall ?_
          intro x hx
          have hcut_nonneg : 0 ≤ unitBallCutoff (d := d) x := by
            unfold unitBallCutoff
            exact le_min (by positivity) (le_max_right _ _)
          have hcut_le : unitBallCutoff (d := d) x ≤ 1 := by
            unfold unitBallCutoff
            exact min_le_left _ _
          have hcut_abs : |unitBallCutoff (d := d) x| ≤ 1 := by
            rw [abs_of_nonneg hcut_nonneg]
            exact hcut_le
          have hnorm :
              |unitBallExtension (d := d) u x| ≤ |u (inv x)| := by
            rw [unitBallExtension, unitBallRetraction_eq_inversion_of_mem_outerShell (d := d) hx]
            calc
              |unitBallCutoff (d := d) x * u (inv x)|
                  = |unitBallCutoff (d := d) x| * |u (inv x)| := by rw [abs_mul]
              _ ≤ 1 * |u (inv x)| := by
                    gcongr
              _ = |u (inv x)| := by ring
          exact ENNReal.rpow_le_rpow
            (ENNReal.ofReal_le_ofReal hnorm) hp
    _ ≤ ENNReal.ofReal ((2 : ℝ) ^ (2 * d)) *
          ∫⁻ x in unitBallInnerShell (d := d), Φ x ∂volume := by
            simpa [Φ, inv] using
              lintegral_outerShell_comp_inversion_le (d := d) (Φ := Φ)
    _ ≤ ENNReal.ofReal ((2 : ℝ) ^ (2 * d)) *
          ∫⁻ x in Metric.ball (0 : E) 1, Φ x ∂volume := by
            exact mul_le_mul_right (lintegral_mono_set
              (unitBallInnerShell_subset_ball_zero_one (d := d)))
              _

private lemma lintegral_rpow_abs_unitBallExtension_ball_two_le
    {p : ℝ} (hp : 0 ≤ p) {u : E → ℝ} :
    ∫⁻ x in Metric.ball (0 : E) 2,
        (ENNReal.ofReal |unitBallExtension (d := d) u x|) ^ p ∂volume
      ≤ (1 + ENNReal.ofReal ((2 : ℝ) ^ (2 * d))) *
        ∫⁻ x in Metric.ball (0 : E) 1, (ENNReal.ofReal |u x|) ^ p ∂volume := by
  let F : E → ℝ≥0∞ := fun x => (ENNReal.ofReal |unitBallExtension (d := d) u x|) ^ p
  let G : E → ℝ≥0∞ := fun x => (ENNReal.ofReal |u x|) ^ p
  have hsphere_zero : volume (Metric.sphere (0 : E) 1) = 0 := by
    simpa using (Measure.addHaar_sphere (μ := (volume : Measure E)) (x := (0 : E)) 1)
  have hball :
      ∫⁻ x in Metric.ball (0 : E) 1, F x ∂volume =
        ∫⁻ x in Metric.ball (0 : E) 1, G x ∂volume := by
    refine lintegral_congr_ae ?_
    exact (ae_restrict_iff' measurableSet_ball).2 <| Filter.Eventually.of_forall <| fun x hx => by
      simp [F, G, unitBallExtension_eq_of_mem_ball (d := d) hx]
  calc
    ∫⁻ x in Metric.ball (0 : E) 2, F x ∂volume
        = ∫⁻ x in (Metric.ball (0 : E) 1 ∪ unitBallOuterShell (d := d)) ∪ Metric.sphere (0 : E) 1,
            F x ∂volume := by
              rw [ball_zero_two_eq_ball_zero_one_union_outerShell_union_sphere (d := d)]
    _ = ∫⁻ x in Metric.ball (0 : E) 1 ∪ unitBallOuterShell (d := d), F x ∂volume +
          ∫⁻ x in Metric.sphere (0 : E) 1, F x ∂volume := by
            rw [lintegral_union Metric.isClosed_sphere.measurableSet
              (disjoint_ball_zero_one_outerShell_union_sphere (d := d))]
    _ = ∫⁻ x in Metric.ball (0 : E) 1 ∪ unitBallOuterShell (d := d), F x ∂volume := by
          rw [setLIntegral_measure_zero _ _ hsphere_zero, add_zero]
    _ = ∫⁻ x in Metric.ball (0 : E) 1, F x ∂volume +
          ∫⁻ x in unitBallOuterShell (d := d), F x ∂volume := by
            rw [lintegral_union measurableSet_unitBallOuterShell
              (disjoint_ball_zero_one_outerShell (d := d))]
    _ ≤ ∫⁻ x in Metric.ball (0 : E) 1, G x ∂volume +
          ENNReal.ofReal ((2 : ℝ) ^ (2 * d)) *
            ∫⁻ x in Metric.ball (0 : E) 1, G x ∂volume := by
              rw [hball]
              gcongr
              exact lintegral_rpow_abs_unitBallExtension_outerShell_le (d := d) hp
    _ = (1 + ENNReal.ofReal ((2 : ℝ) ^ (2 * d))) *
          ∫⁻ x in Metric.ball (0 : E) 1, G x ∂volume := by
            ring

private lemma lintegral_rpow_norm_fderiv_unitBallExtension_outerShell_le
    {p : ℝ} (hp : 1 ≤ p) {u : E → ℝ} (hu : ContDiff ℝ 1 u) :
    ∫⁻ x in unitBallOuterShell (d := d),
        (ENNReal.ofReal ‖fderiv ℝ (unitBallExtension (d := d) u) x‖) ^ p ∂volume
      ≤ ENNReal.ofReal ((2 : ℝ) ^ (2 * d)) * (2 : ℝ≥0∞) ^ (p - 1) *
        (∫⁻ x in Metric.ball (0 : E) 1, (ENNReal.ofReal |u x|) ^ p ∂volume +
         ∫⁻ x in Metric.ball (0 : E) 1, (ENNReal.ofReal ‖fderiv ℝ u x‖) ^ p ∂volume) := by
  let Φu : E → ℝ≥0∞ := fun x => (ENNReal.ofReal |u x|) ^ p
  let ΦDu : E → ℝ≥0∞ := fun x => (ENNReal.ofReal ‖fderiv ℝ u x‖) ^ p
  let Ψ : E → ℝ≥0∞ := fun x => (2 : ℝ≥0∞) ^ (p - 1) * (Φu x + ΦDu x)
  let inv : E → E := EuclideanGeometry.inversion (0 : E) 1
  have huDiff : Differentiable ℝ u := hu.differentiable_one
  have hPhiDu_m : Measurable ΦDu := by
    exact ENNReal.continuous_rpow_const.measurable.comp
      ((hu.continuous_fderiv one_ne_zero).measurable.norm.ennreal_ofReal)
  calc
    ∫⁻ x in unitBallOuterShell (d := d),
        (ENNReal.ofReal ‖fderiv ℝ (unitBallExtension (d := d) u) x‖) ^ p ∂volume
      ≤ ∫⁻ x in unitBallOuterShell (d := d), Ψ (inv x) ∂volume := by
            refine lintegral_mono_ae ?_
            rw [ae_restrict_iff' measurableSet_unitBallOuterShell]
            refine Filter.Eventually.of_forall ?_
            intro x hx
            have hpoint :
                ENNReal.ofReal ‖fderiv ℝ (unitBallExtension (d := d) u) x‖
                  ≤ ENNReal.ofReal |u (inv x)| +
                    ENNReal.ofReal ‖fderiv ℝ u (inv x)‖ := by
              have hle := norm_fderiv_unitBallExtension_le_of_mem_outerShell (d := d) huDiff hx
              exact by
                rw [← ENNReal.ofReal_add (abs_nonneg _) (norm_nonneg _)]
                exact ENNReal.ofReal_le_ofReal hle
            calc
              (ENNReal.ofReal ‖fderiv ℝ (unitBallExtension (d := d) u) x‖) ^ p
                  ≤ (ENNReal.ofReal |u (inv x)| + ENNReal.ofReal ‖fderiv ℝ u (inv x)‖) ^ p := by
                    exact ENNReal.rpow_le_rpow hpoint (by positivity)
              _ ≤ (2 : ℝ≥0∞) ^ (p - 1) *
                    ((ENNReal.ofReal |u (inv x)|) ^ p +
                      (ENNReal.ofReal ‖fderiv ℝ u (inv x)‖) ^ p) := by
                        exact ENNReal.rpow_add_le_mul_rpow_add_rpow _ _ hp
              _ = Ψ (inv x) := by
                    simp [Ψ, Φu, ΦDu]
    _ ≤ ENNReal.ofReal ((2 : ℝ) ^ (2 * d)) *
          ∫⁻ x in unitBallInnerShell (d := d), Ψ x ∂volume := by
            simpa [Ψ, inv] using lintegral_outerShell_comp_inversion_le (d := d) (Φ := Ψ)
    _ = ENNReal.ofReal ((2 : ℝ) ^ (2 * d)) * ((2 : ℝ≥0∞) ^ (p - 1) *
          ∫⁻ x in unitBallInnerShell (d := d), (Φu x + ΦDu x) ∂volume) := by
            rw [lintegral_const_mul']
            simp
    _ = ENNReal.ofReal ((2 : ℝ) ^ (2 * d)) * (2 : ℝ≥0∞) ^ (p - 1) *
          ∫⁻ x in unitBallInnerShell (d := d), (Φu x + ΦDu x) ∂volume := by
            ring
    _ = ENNReal.ofReal ((2 : ℝ) ^ (2 * d)) * (2 : ℝ≥0∞) ^ (p - 1) *
          (∫⁻ x in unitBallInnerShell (d := d), Φu x ∂volume +
           ∫⁻ x in unitBallInnerShell (d := d), ΦDu x ∂volume) := by
            congr 2
            rw [lintegral_add_right' _ hPhiDu_m.aemeasurable.restrict]
    _ ≤ ENNReal.ofReal ((2 : ℝ) ^ (2 * d)) * (2 : ℝ≥0∞) ^ (p - 1) *
          (∫⁻ x in Metric.ball (0 : E) 1, Φu x ∂volume +
           ∫⁻ x in Metric.ball (0 : E) 1, ΦDu x ∂volume) := by
            have hsum :
                ∫⁻ x in unitBallInnerShell (d := d), Φu x ∂volume +
                    ∫⁻ x in unitBallInnerShell (d := d), ΦDu x ∂volume
                  ≤ ∫⁻ x in Metric.ball (0 : E) 1, Φu x ∂volume +
                    ∫⁻ x in Metric.ball (0 : E) 1, ΦDu x ∂volume := by
              exact add_le_add
                (lintegral_mono_set (unitBallInnerShell_subset_ball_zero_one (d := d)))
                (lintegral_mono_set (unitBallInnerShell_subset_ball_zero_one (d := d)))
            gcongr

private lemma lintegral_rpow_norm_fderiv_unitBallExtension_ball_two_le
    {p : ℝ} (hp : 1 ≤ p) {u : E → ℝ} (hu : ContDiff ℝ 1 u) :
    ∫⁻ x in Metric.ball (0 : E) 2,
        (ENNReal.ofReal ‖fderiv ℝ (unitBallExtension (d := d) u) x‖) ^ p ∂volume
      ≤ (∫⁻ x in Metric.ball (0 : E) 1, (ENNReal.ofReal ‖fderiv ℝ u x‖) ^ p ∂volume) +
        ENNReal.ofReal ((2 : ℝ) ^ (2 * d)) * (2 : ℝ≥0∞) ^ (p - 1) *
          (∫⁻ x in Metric.ball (0 : E) 1, (ENNReal.ofReal |u x|) ^ p ∂volume +
           ∫⁻ x in Metric.ball (0 : E) 1, (ENNReal.ofReal ‖fderiv ℝ u x‖) ^ p ∂volume) := by
  let F : E → ℝ≥0∞ := fun x => (ENNReal.ofReal ‖fderiv ℝ (unitBallExtension (d := d) u) x‖) ^ p
  let G : E → ℝ≥0∞ := fun x => (ENNReal.ofReal ‖fderiv ℝ u x‖) ^ p
  have hsphere_zero : volume (Metric.sphere (0 : E) 1) = 0 := by
    simpa using (Measure.addHaar_sphere (μ := (volume : Measure E)) (x := (0 : E)) 1)
  have hball :
      ∫⁻ x in Metric.ball (0 : E) 1, F x ∂volume =
        ∫⁻ x in Metric.ball (0 : E) 1, G x ∂volume := by
    refine lintegral_congr_ae ?_
    exact (ae_restrict_iff' measurableSet_ball).2 <| Filter.Eventually.of_forall <| fun x hx => by
      simp [F, G, fderiv_unitBallExtension_eq_of_mem_ball (d := d) hx]
  calc
    ∫⁻ x in Metric.ball (0 : E) 2, F x ∂volume
        = ∫⁻ x in (Metric.ball (0 : E) 1 ∪ unitBallOuterShell (d := d)) ∪ Metric.sphere (0 : E) 1,
            F x ∂volume := by
              rw [ball_zero_two_eq_ball_zero_one_union_outerShell_union_sphere (d := d)]
    _ = ∫⁻ x in Metric.ball (0 : E) 1 ∪ unitBallOuterShell (d := d), F x ∂volume +
          ∫⁻ x in Metric.sphere (0 : E) 1, F x ∂volume := by
            rw [lintegral_union Metric.isClosed_sphere.measurableSet
              (disjoint_ball_zero_one_outerShell_union_sphere (d := d))]
    _ = ∫⁻ x in Metric.ball (0 : E) 1 ∪ unitBallOuterShell (d := d), F x ∂volume := by
          rw [setLIntegral_measure_zero _ _ hsphere_zero, add_zero]
    _ = ∫⁻ x in Metric.ball (0 : E) 1, F x ∂volume +
          ∫⁻ x in unitBallOuterShell (d := d), F x ∂volume := by
            rw [lintegral_union measurableSet_unitBallOuterShell
              (disjoint_ball_zero_one_outerShell (d := d))]
    _ ≤ (∫⁻ x in Metric.ball (0 : E) 1, G x ∂volume) +
          ENNReal.ofReal ((2 : ℝ) ^ (2 * d)) * (2 : ℝ≥0∞) ^ (p - 1) *
            (∫⁻ x in Metric.ball (0 : E) 1, (ENNReal.ofReal |u x|) ^ p ∂volume +
             ∫⁻ x in Metric.ball (0 : E) 1, (ENNReal.ofReal ‖fderiv ℝ u x‖) ^ p ∂volume) := by
              rw [hball]
              gcongr
              exact lintegral_rpow_norm_fderiv_unitBallExtension_outerShell_le (d := d) hp hu

theorem smooth_unitBallExtension_W1p_estimate
    {p : ℝ} (hp : 1 ≤ p) {u : E → ℝ} (hu : ContDiff ℝ 1 u) :
    (∫⁻ x in Metric.ball (0 : E) 2,
        (ENNReal.ofReal |unitBallExtension (d := d) u x|) ^ p ∂volume)
      ≤ (1 + ENNReal.ofReal ((2 : ℝ) ^ (2 * d))) *
        ∫⁻ x in Metric.ball (0 : E) 1, (ENNReal.ofReal |u x|) ^ p ∂volume
    ∧
    (∫⁻ x in Metric.ball (0 : E) 2,
        (ENNReal.ofReal ‖fderiv ℝ (unitBallExtension (d := d) u) x‖) ^ p ∂volume)
      ≤ (∫⁻ x in Metric.ball (0 : E) 1, (ENNReal.ofReal ‖fderiv ℝ u x‖) ^ p ∂volume) +
        ENNReal.ofReal ((2 : ℝ) ^ (2 * d)) * (2 : ℝ≥0∞) ^ (p - 1) *
          (∫⁻ x in Metric.ball (0 : E) 1, (ENNReal.ofReal |u x|) ^ p ∂volume +
           ∫⁻ x in Metric.ball (0 : E) 1, (ENNReal.ofReal ‖fderiv ℝ u x‖) ^ p ∂volume) := by
  exact ⟨lintegral_rpow_abs_unitBallExtension_ball_two_le (d := d) (by linarith : 0 ≤ p),
    lintegral_rpow_norm_fderiv_unitBallExtension_ball_two_le (d := d) hp hu⟩

private theorem smooth_unitBallExtension_fun_sub_estimate
    {p : ℝ} (hp : 1 ≤ p) {u v : E → ℝ}
    (hu : ContDiff ℝ 1 u) (hv : ContDiff ℝ 1 v) :
    (∫⁻ x in Metric.ball (0 : E) 2,
        (ENNReal.ofReal |unitBallExtension (d := d) u x - unitBallExtension (d := d) v x|) ^ p
          ∂volume)
      ≤ (1 + ENNReal.ofReal ((2 : ℝ) ^ (2 * d))) *
        ∫⁻ x in Metric.ball (0 : E) 1, (ENNReal.ofReal |u x - v x|) ^ p ∂volume := by
  simpa [unitBallExtension_sub (d := d) u v] using
    (smooth_unitBallExtension_W1p_estimate (d := d) (p := p) hp (u := fun x => u x - v x)
      (hu.sub hv)).1

private theorem smooth_unitBallExtension_grad_sub_estimate
    {p : ℝ} (hp : 1 ≤ p) {u v : E → ℝ}
    (hu : ContDiff ℝ 1 u) (hv : ContDiff ℝ 1 v) :
    (∫⁻ x in Metric.ball (0 : E) 2,
        (ENNReal.ofReal ‖fderiv ℝ (fun y => unitBallExtension (d := d) u y -
            unitBallExtension (d := d) v y) x‖) ^ p ∂volume)
      ≤ (∫⁻ x in Metric.ball (0 : E) 1, (ENNReal.ofReal ‖fderiv ℝ (fun y => u y - v y) x‖) ^ p
            ∂volume) +
        ENNReal.ofReal ((2 : ℝ) ^ (2 * d)) * (2 : ℝ≥0∞) ^ (p - 1) *
          (∫⁻ x in Metric.ball (0 : E) 1, (ENNReal.ofReal |u x - v x|) ^ p ∂volume +
           ∫⁻ x in Metric.ball (0 : E) 1,
             (ENNReal.ofReal ‖fderiv ℝ (fun y => u y - v y) x‖) ^ p ∂volume) := by
  simpa [unitBallExtension_sub (d := d) u v] using
    (smooth_unitBallExtension_W1p_estimate (d := d) (p := p) hp (u := fun x => u x - v x)
      (hu.sub hv)).2

def smoothUnitBallExtensionGrad (u : E → ℝ) : E → E :=
  fun x => WithLp.toLp 2 fun i =>
    (fderiv ℝ (unitBallExtension (d := d) u) x) (EuclideanSpace.single i 1)

def unitBallShellFormula (u : E → ℝ) : E → ℝ :=
  fun x => (2 - ‖x‖) * u (EuclideanGeometry.inversion (0 : E) 1 x)

omit [NeZero d] in
lemma unitBallExtension_eq_shellFormula_of_mem_outerShell
    {u : E → ℝ} {x : E} (hx : x ∈ unitBallOuterShell (d := d)) :
    unitBallExtension (d := d) u x = unitBallShellFormula (d := d) u x := by
  rw [unitBallExtension, unitBallCutoff_eq_two_sub_norm_of_mem_outerShell (d := d) hx,
    unitBallRetraction_eq_inversion_of_mem_outerShell (d := d) hx, unitBallShellFormula]

omit [NeZero d] in
lemma contDiffOn_unitBallShellFormula
    {u : E → ℝ} (hu : ContDiff ℝ 1 u) :
    ContDiffOn ℝ 1 (unitBallShellFormula (d := d) u) (unitBallOuterShell (d := d)) := by
  have hnorm :
      ContDiffOn ℝ 1 (fun x : E => ‖x‖) (unitBallOuterShell (d := d)) := by
    refine ContDiffOn.norm (𝕜 := ℝ) contDiffOn_id ?_
    intro x hx
    have hx0 : 0 < ‖x‖ := by linarith [hx.1]
    intro hxz
    simp [hxz] at hx0
  have hscalar :
      ContDiffOn ℝ 1 (fun x : E => 2 - ‖x‖) (unitBallOuterShell (d := d)) :=
    contDiffOn_const.sub hnorm
  have hinv :
      ContDiffOn ℝ 1 (fun x : E => EuclideanGeometry.inversion (0 : E) 1 x)
        (unitBallOuterShell (d := d)) := by
    simpa using
      (contDiffOn_const.inversion contDiffOn_const contDiffOn_id
        (fun x hx => by
          have hx0 : 0 < ‖x‖ := by linarith [hx.1]
          have hxne_norm : ‖x‖ ≠ 0 := ne_of_gt hx0
          intro hxz
          exact hxne_norm (by simpa [hxz])))
  exact hscalar.mul (hu.comp_contDiffOn hinv)

omit [NeZero d] in
private lemma tendsto_integral_mul_of_eLpNorm_tendsto_zero_p
    {μ : Measure E} {f : E → ℝ} {g : ℕ → E → ℝ} {p q : ℝ}
    (hpq : p⁻¹ + q⁻¹ = 1) (hp : 1 < p) (hq : 1 < q)
    (hf : MemLp f (ENNReal.ofReal q) μ)
    (hg : ∀ n, MemLp (g n) (ENNReal.ofReal p) μ)
    (hlim : Tendsto (fun n => eLpNorm (g n) (ENNReal.ofReal p) μ) atTop (nhds 0)) :
    Tendsto (fun n => ∫ x, f x * g n x ∂μ) atTop (nhds 0) := by
  have hpqR : p.HolderConjugate q := Real.holderConjugate_iff.mpr ⟨hp, hpq⟩
  let C : ℝ := MeasureTheory.lpNorm f (ENNReal.ofReal q) μ
  have hlim' : Tendsto (fun n => MeasureTheory.lpNorm (g n) (ENNReal.ofReal p) μ) atTop (nhds 0) := by
    have hlim_toReal :
        Tendsto (fun n => (eLpNorm (g n) (ENNReal.ofReal p) μ).toReal) atTop (nhds 0) :=
      (ENNReal.tendsto_toReal_zero_iff (fun n => (hg n).eLpNorm_ne_top)).2 hlim
    have hEq :
        (fun n => (eLpNorm (g n) (ENNReal.ofReal p) μ).toReal) =
          (fun n => MeasureTheory.lpNorm (g n) (ENNReal.ofReal p) μ) := by
      funext n
      simpa using
        (MeasureTheory.toReal_eLpNorm
          (μ := μ) (p := ENNReal.ofReal p) (f := g n) (hg n).aestronglyMeasurable)
    simpa [hEq] using hlim_toReal
  have hbound :
      ∀ n, |∫ x, f x * g n x ∂μ| ≤ C * MeasureTheory.lpNorm (g n) (ENNReal.ofReal p) μ := by
    intro n
    have h_int :
        |∫ x, f x * g n x ∂μ| ≤ ∫ x, ‖f x‖ * ‖g n x‖ ∂μ := by
      calc
        |∫ x, f x * g n x ∂μ| = ‖∫ x, f x * g n x ∂μ‖ := by rw [Real.norm_eq_abs]
        _ ≤ ∫ x, ‖f x * g n x‖ ∂μ := by
          simpa using norm_integral_le_integral_norm (μ := μ) (f := fun x => f x * g n x)
        _ = ∫ x, ‖f x‖ * ‖g n x‖ ∂μ := by simp_rw [norm_mul]
    have h_holder :=
      MeasureTheory.integral_mul_norm_le_Lp_mul_Lq
        (μ := μ) (f := f) (g := g n) (p := q) (q := p) hpqR.symm hf (hg n)
    have hp0 : ENNReal.ofReal p ≠ 0 := by
      intro hp0'
      have : p ≤ 0 := by simpa [ENNReal.ofReal_eq_zero] using hp0'
      linarith
    have hq0 : ENNReal.ofReal q ≠ 0 := by
      intro hq0'
      have : q ≤ 0 := by simpa [ENNReal.ofReal_eq_zero] using hq0'
      linarith
    have h_f_lp :
        MeasureTheory.lpNorm f (ENNReal.ofReal q) μ =
          (∫ x, ‖f x‖ ^ q ∂μ) ^ q⁻¹ := by
      simpa [ENNReal.toReal_ofReal (by linarith : 0 ≤ q)] using
        (MeasureTheory.lpNorm_eq_integral_norm_rpow_toReal
          (μ := μ) (p := ENNReal.ofReal q) (f := f) hq0 (by simp) hf.aestronglyMeasurable)
    have h_g_lp :
        MeasureTheory.lpNorm (g n) (ENNReal.ofReal p) μ =
          (∫ x, ‖g n x‖ ^ p ∂μ) ^ p⁻¹ := by
      simpa [ENNReal.toReal_ofReal (by linarith : 0 ≤ p)] using
        (MeasureTheory.lpNorm_eq_integral_norm_rpow_toReal
          (μ := μ) (p := ENNReal.ofReal p) (f := g n) hp0 (by simp) (hg n).aestronglyMeasurable)
    calc
      |∫ x, f x * g n x ∂μ| ≤ ∫ x, ‖f x‖ * ‖g n x‖ ∂μ := h_int
      _ ≤ C * MeasureTheory.lpNorm (g n) (ENNReal.ofReal p) μ := by
        simpa [C, h_f_lp, h_g_lp, mul_comm, mul_left_comm, mul_assoc] using h_holder
  have h_upper :
      Tendsto (fun n => C * MeasureTheory.lpNorm (g n) (ENNReal.ofReal p) μ) atTop (nhds 0) := by
    simpa using Tendsto.const_mul C hlim'
  have h_abs :
      Tendsto (fun n => |∫ x, f x * g n x ∂μ|) atTop (nhds 0) :=
    squeeze_zero (fun n => abs_nonneg _) hbound h_upper
  exact (tendsto_zero_iff_abs_tendsto_zero _).2 h_abs

/-- Zero-extension of a compactly supported local `W₀^{1,p}` witness to all of
`ℝ^d`. -/
theorem zeroExtend_memW01p_p
    {Ω : Set E} (hΩ : IsOpen Ω)
    {p : ℝ} (hp : 1 < p)
    {v : E → ℝ}
    (hv : MemW01p (ENNReal.ofReal p) v Ω) :
    MemW01p (ENNReal.ofReal p) (Ω.indicator v) Set.univ := by
  classical
  have hΩ_meas : MeasurableSet Ω := hΩ.measurableSet
  let hw : MemW1pWitness (ENNReal.ofReal p) v Ω := Classical.choose hv.2
  let hExφ := Classical.choose_spec hv.2
  let φ : ℕ → E → ℝ := Classical.choose hExφ
  have hφspec := Classical.choose_spec hExφ
  have hφ_smooth : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (φ n) := hφspec.1
  have hφ_compact : ∀ n, HasCompactSupport (φ n) := hφspec.2.1
  have hφ_sub : ∀ n, tsupport (φ n) ⊆ Ω := hφspec.2.2.1
  have hφ_fun :
      Tendsto
        (fun n => eLpNorm (fun x => φ n x - v x) (ENNReal.ofReal p) (volume.restrict Ω))
        atTop (nhds 0) := hφspec.2.2.2.1
  have hφ_grad :
      ∀ i : Fin d,
        Tendsto
          (fun n =>
            eLpNorm
              (fun x => (fderiv ℝ (φ n) x) (EuclideanSpace.single i 1) - hw.weakGrad x i)
              (ENNReal.ofReal p) (volume.restrict Ω))
          atTop (nhds 0) := hφspec.2.2.2.2
  let hwExt := zeroExtend_memW1pWitness_p (d := d) hΩ hp hv hw
  refine ⟨hwExt.memW1p, hwExt, φ, hφ_smooth, hφ_compact, ?_, ?_, ?_⟩
  · intro n
    simp
  · have hEq :
        (fun n => eLpNorm (fun x => φ n x - Ω.indicator v x) (ENNReal.ofReal p) volume) =
          fun n => eLpNorm (fun x => φ n x - v x) (ENNReal.ofReal p) (volume.restrict Ω) := by
      funext n
      have hFn :
          (fun x => φ n x - Ω.indicator v x) =
            Ω.indicator (fun x => φ n x - v x) := by
        ext x
        by_cases hx : x ∈ Ω
        · simp [hx]
        · have hφx : φ n x = 0 := zero_outside_of_tsupport_subset (Ω := Ω) (hφ_sub n) hx
          simp [hx, hφx]
      rw [hFn, MeasureTheory.eLpNorm_indicator_eq_eLpNorm_restrict
        (μ := volume) (s := Ω) (p := ENNReal.ofReal p) hΩ_meas]
    rw [Measure.restrict_univ, hEq]
    simpa using hφ_fun
  · intro i
    have hEq :
        (fun n =>
          eLpNorm
            (fun x => (fderiv ℝ (φ n) x) (EuclideanSpace.single i 1) - hwExt.weakGrad x i)
            (ENNReal.ofReal p) volume) =
          fun n =>
            eLpNorm
              (fun x => (fderiv ℝ (φ n) x) (EuclideanSpace.single i 1) - hw.weakGrad x i)
              (ENNReal.ofReal p) (volume.restrict Ω) := by
      funext n
      have hFn :
          (fun x => (fderiv ℝ (φ n) x) (EuclideanSpace.single i 1) - hwExt.weakGrad x i) =
            Ω.indicator
              (fun x => (fderiv ℝ (φ n) x) (EuclideanSpace.single i 1) - hw.weakGrad x i) := by
        ext x
        by_cases hx : x ∈ Ω
        · simp [hwExt, zeroExtend_memW1pWitness_p, hx]
        · have hdx :
              (fderiv ℝ (φ n) x) (EuclideanSpace.single i 1) = 0 := by
            exact fderiv_apply_zero_outside_of_tsupport_subset (Ω := Ω) (hf := hφ_smooth n)
              (hsub := hφ_sub n) hx i
          simp [hwExt, zeroExtend_memW1pWitness_p, hx, hdx]
      rw [hFn, MeasureTheory.eLpNorm_indicator_eq_eLpNorm_restrict
        (μ := volume) (s := Ω) (p := ENNReal.ofReal p) hΩ_meas]
    rw [Measure.restrict_univ, hEq]
    simpa using hφ_grad i

/-- Global smooth compactly supported approximation for a local witness whose
support is already compactly contained in the source open set. -/
theorem exists_global_smooth_W1p_approx_of_localizedWitness
    {Ω : Set E} (hΩ : IsOpen Ω)
    {p : ℝ} (hp : 1 < p)
    {u : E → ℝ}
    (hw : MemW1pWitness (ENNReal.ofReal p) u Ω)
    (hu_compact : HasCompactSupport u)
    (hu_sub : tsupport u ⊆ Ω) :
    ∃ ψ : ℕ → E → ℝ,
      (∀ n, ContDiff ℝ (⊤ : ℕ∞) (ψ n)) ∧
      (∀ n, HasCompactSupport (ψ n)) ∧
      Tendsto
        (fun n => eLpNorm (fun x => ψ n x - u x) (ENNReal.ofReal p) volume)
        atTop (nhds 0) ∧
      (∀ i : Fin d,
        Tendsto
          (fun n =>
            eLpNorm
              (fun x => (fderiv ℝ (ψ n) x) (EuclideanSpace.single i 1) -
                Ω.indicator (fun y => hw.weakGrad y i) x)
              (ENNReal.ofReal p) volume)
          atTop (nhds 0)) := by
  have hu0 : MemW01p (ENNReal.ofReal p) u Ω :=
    memW01p_of_memW1p_of_tsupport_subset hΩ hp hw.memW1p hu_compact hu_sub
  let hwExt := zeroExtend_memW1pWitness_p (d := d) hΩ hp hu0 hw
  have hu_eq_ind : Ω.indicator u = u := by
    ext x
    by_cases hx : x ∈ Ω
    · simp [hx]
    · simp [hx, zero_outside_of_tsupport_subset (Ω := Ω) hu_sub hx]
  have huExt0 : MemW01p (ENNReal.ofReal p) (Ω.indicator u) Set.univ :=
    zeroExtend_memW01p_p (d := d) hΩ hp hu0
  rcases huExt0.2 with ⟨hw0, φ, hφ_smooth, hφ_compact, hφ_sub, hφ_fun, hφ_grad⟩
  refine ⟨φ, hφ_smooth, hφ_compact, ?_, ?_⟩
  · simpa [hu_eq_ind] using hφ_fun
  · intro i
    have hp_le : 1 ≤ p := le_of_lt hp
    have hcomp :
        (fun x => hw0.weakGrad x i) =ᵐ[volume.restrict Set.univ]
          (fun x => (Ω.indicator (fun y => hw.weakGrad y i)) x) := by
      filter_upwards [MemW1pWitness.ae_eq_p (d := d) isOpen_univ hp_le hw0 hwExt] with x hx
      simpa [zeroExtend_memW1pWitness_p, hwExt] using congrArg (fun z : E => z i) hx
    have hEqSeq :
        (fun n =>
          eLpNorm
            (fun x => (fderiv ℝ (φ n) x) (EuclideanSpace.single i 1) -
              Ω.indicator (fun y => hw.weakGrad y i) x)
            (ENNReal.ofReal p) volume) =
          (fun n =>
            eLpNorm
              (fun x => (fderiv ℝ (φ n) x) (EuclideanSpace.single i 1) - hw0.weakGrad x i)
              (ENNReal.ofReal p) volume) := by
      funext n
      refine eLpNorm_congr_ae ?_
      have hcomp' :
          (fun x => hw0.weakGrad x i) =ᵐ[volume]
            (fun x => (Ω.indicator (fun y => hw.weakGrad y i)) x) := by
        simpa [Measure.restrict_univ] using hcomp
      filter_upwards [hcomp'] with x hx
      simp [hx]
    rw [hEqSeq]
    simpa [Measure.restrict_univ] using hφ_grad i

/-- Explicit `L^p` constant from the unit-ball extension estimate. -/
abbrev C_unitBallExtensionFun (d : ℕ) [NeZero d] : ℝ≥0∞ :=
  1 + ENNReal.ofReal ((2 : ℝ) ^ (2 * d))

/-- Explicit gradient-side constant from the smooth unit-ball extension estimate. -/
abbrev C_unitBallExtensionGrad (d : ℕ) [NeZero d] (p : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal ((2 : ℝ) ^ (2 * d)) * (2 : ℝ≥0∞) ^ (p - 1)

omit [NeZero d] in
lemma unitBallCutoff_eq_zero_of_two_le_norm {x : E} (hx : 2 ≤ ‖x‖) :
    unitBallCutoff (d := d) x = 0 := by
  unfold unitBallCutoff
  rw [max_eq_right (by linarith), min_eq_right (by positivity)]

omit [NeZero d] in
lemma unitBallExtension_eq_zero_of_two_le_norm {u : E → ℝ} {x : E}
    (hx : 2 ≤ ‖x‖) :
    unitBallExtension (d := d) u x = 0 := by
  rw [unitBallExtension, unitBallCutoff_eq_zero_of_two_le_norm (d := d) hx, zero_mul]

omit [NeZero d] in
private lemma unitBallExtension_eq_zero_of_not_mem_closedBall_two {u : E → ℝ} {x : E}
    (hx : x ∉ Metric.closedBall (0 : E) 2) :
    unitBallExtension (d := d) u x = 0 := by
  apply unitBallExtension_eq_zero_of_two_le_norm (d := d)
  rw [Metric.mem_closedBall, dist_zero_right] at hx
  linarith

omit [NeZero d] in
lemma unitBallExtension_hasCompactSupport (u : E → ℝ) :
    HasCompactSupport (unitBallExtension (d := d) u) := by
  apply HasCompactSupport.intro' (isCompact_closedBall (0 : E) 2) isClosed_closedBall
  intro x hx
  exact unitBallExtension_eq_zero_of_not_mem_closedBall_two (d := d) hx

omit [NeZero d] in
theorem norm_fderiv_eq_norm_partials_local
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
        rfl
  calc
    ‖fderiv ℝ f x‖ = ‖v‖ := by
      simp [v]
    _ = ‖WithLp.toLp 2
        (fun i => (fderiv ℝ f x) (EuclideanSpace.single i 1))‖ := by
      rw [hv]

omit [NeZero d] in
theorem aestronglyMeasurable_euclidean_of_components_local
    {G : E → E}
    (hG_comp : ∀ i : Fin d, AEStronglyMeasurable (fun x => G x i) volume) :
    AEStronglyMeasurable G volume := by
  have h_ofLp : AEMeasurable (fun x => (WithLp.ofLp (G x) : Fin d → ℝ)) volume := by
    rw [aemeasurable_pi_iff]
    intro i
    simpa using (hG_comp i).aemeasurable
  have h_toLp_cont : Continuous (fun x : Fin d → ℝ => WithLp.toLp 2 x) := by
    simpa using (PiLp.continuous_toLp 2 (fun _ : Fin d => ℝ))
  have h_toLp_meas : Measurable (fun x : Fin d → ℝ => WithLp.toLp 2 x) := h_toLp_cont.measurable
  have h_id : (fun x => WithLp.toLp 2 (WithLp.ofLp (G x))) = G := by
    funext x
    simp
  exact (h_toLp_meas.comp_aemeasurable h_ofLp).aestronglyMeasurable.congr <| EventuallyEq.of_eq h_id

private theorem eLpNorm_le_of_lintegral_rpow_ofReal_le_generic
    {α F : Type*} [MeasurableSpace α] [NormedAddCommGroup F]
    [MeasurableSpace F] [BorelSpace F] {μ : Measure α}
    {p : ℝ} (hp : 0 < p) {f : α → F} {A : ℝ≥0∞}
    (hA : ∫⁻ x, (ENNReal.ofReal ‖f x‖) ^ p ∂μ ≤ A) :
    eLpNorm f (ENNReal.ofReal p) μ ≤ A ^ (1 / p) := by
  have hp0 : (ENNReal.ofReal p) ≠ 0 := by
    exact ne_of_gt (ENNReal.ofReal_pos.mpr hp)
  have hptop : (ENNReal.ofReal p) ≠ ∞ := by
    simp
  rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hptop]
  have hp_nonneg : 0 ≤ 1 / p := by
    positivity
  simpa [ENNReal.toReal_ofReal (le_of_lt hp)] using ENNReal.rpow_le_rpow hA hp_nonneg

theorem lintegral_rpow_norm_eq_eLpNorm_pow
    {α F : Type*} [MeasurableSpace α] [NormedAddCommGroup F]
    [MeasurableSpace F] [BorelSpace F] {μ : Measure α}
    {p : ℝ} (hp : 0 < p) {f : α → F} :
    ∫⁻ x, (ENNReal.ofReal ‖f x‖) ^ p ∂μ = eLpNorm f (ENNReal.ofReal p) μ ^ p := by
  let pnn : ℝ≥0 := Real.toNNReal p
  have hpnn0 : pnn ≠ 0 := by
    intro hzero
    have hp_nonpos : p ≤ 0 := Real.toNNReal_eq_zero.mp hzero
    linarith
  have hpnn_real : (pnn : ℝ) = p := by
    simp [pnn, Real.toNNReal_of_nonneg (le_of_lt hp)]
  have hpnn_enn : (pnn : ℝ≥0∞) = ENNReal.ofReal p := by
    change (Real.toNNReal p : ℝ≥0∞) = ENNReal.ofReal p
    rfl
  calc
    ∫⁻ x, (ENNReal.ofReal ‖f x‖) ^ p ∂μ
      = ∫⁻ x, (ENNReal.ofReal ‖f x‖) ^ (pnn : ℝ) ∂μ := by simp [hpnn_real]
    _ = eLpNorm f (pnn : ℝ≥0∞) μ ^ (pnn : ℝ) := by
      simpa using
        (MeasureTheory.eLpNorm_nnreal_pow_eq_lintegral (μ := μ) (f := f) (p := pnn) hpnn0).symm
    _ = eLpNorm f (ENNReal.ofReal p) μ ^ p := by simp [hpnn_real, hpnn_enn]

private lemma lintegral_rpow_abs_unitBallExtension_ball_two_le_local
    {p : ℝ} (hp : 0 ≤ p) {u : E → ℝ} :
    ∫⁻ x in Metric.ball (0 : E) 2,
        (ENNReal.ofReal |unitBallExtension (d := d) u x|) ^ p ∂volume
      ≤ (1 + ENNReal.ofReal ((2 : ℝ) ^ (2 * d))) *
        ∫⁻ x in Metric.ball (0 : E) 1, (ENNReal.ofReal |u x|) ^ p ∂volume := by
  let F : E → ℝ≥0∞ := fun x => (ENNReal.ofReal |unitBallExtension (d := d) u x|) ^ p
  let G : E → ℝ≥0∞ := fun x => (ENNReal.ofReal |u x|) ^ p
  have hsphere_zero : volume (Metric.sphere (0 : E) 1) = 0 := by
    simpa using (Measure.addHaar_sphere (μ := (volume : Measure E)) (x := (0 : E)) 1)
  have hball :
      ∫⁻ x in Metric.ball (0 : E) 1, F x ∂volume =
        ∫⁻ x in Metric.ball (0 : E) 1, G x ∂volume := by
    refine lintegral_congr_ae ?_
    exact (ae_restrict_iff' measurableSet_ball).2 <| Filter.Eventually.of_forall <| fun x hx => by
      simp [F, G, unitBallExtension_eq_of_mem_ball (d := d) hx]
  calc
    ∫⁻ x in Metric.ball (0 : E) 2, F x ∂volume
        = ∫⁻ x in (Metric.ball (0 : E) 1 ∪ unitBallOuterShell (d := d)) ∪ Metric.sphere (0 : E) 1,
            F x ∂volume := by
              rw [ball_zero_two_eq_ball_zero_one_union_outerShell_union_sphere (d := d)]
    _ = ∫⁻ x in Metric.ball (0 : E) 1 ∪ unitBallOuterShell (d := d), F x ∂volume +
          ∫⁻ x in Metric.sphere (0 : E) 1, F x ∂volume := by
            rw [lintegral_union Metric.isClosed_sphere.measurableSet
              (disjoint_ball_zero_one_outerShell_union_sphere (d := d))]
    _ = ∫⁻ x in Metric.ball (0 : E) 1 ∪ unitBallOuterShell (d := d), F x ∂volume := by
          rw [setLIntegral_measure_zero _ _ hsphere_zero, add_zero]
    _ = ∫⁻ x in Metric.ball (0 : E) 1, F x ∂volume +
          ∫⁻ x in unitBallOuterShell (d := d), F x ∂volume := by
            rw [lintegral_union measurableSet_unitBallOuterShell
              (disjoint_ball_zero_one_outerShell (d := d))]
    _ ≤ ∫⁻ x in Metric.ball (0 : E) 1, G x ∂volume +
          ENNReal.ofReal ((2 : ℝ) ^ (2 * d)) *
            ∫⁻ x in Metric.ball (0 : E) 1, G x ∂volume := by
              rw [hball]
              gcongr
              exact lintegral_rpow_abs_unitBallExtension_outerShell_le (d := d) hp
    _ = (1 + ENNReal.ofReal ((2 : ℝ) ^ (2 * d))) *
          ∫⁻ x in Metric.ball (0 : E) 1, G x ∂volume := by
          ring

lemma lintegral_rpow_abs_unitBallExtension_sub_le_local
    {p : ℝ} (hp : 0 < p) {u v : E → ℝ} :
    ∫⁻ x, (ENNReal.ofReal |unitBallExtension (d := d) u x -
        unitBallExtension (d := d) v x|) ^ p ∂volume
      ≤ (1 + ENNReal.ofReal ((2 : ℝ) ^ (2 * d))) *
        ∫⁻ x in Metric.ball (0 : E) 1, (ENNReal.ofReal |u x - v x|) ^ p ∂volume := by
  have hsupport :
      (fun x => (ENNReal.ofReal |unitBallExtension (d := d) u x -
        unitBallExtension (d := d) v x|) ^ p) =
        (Metric.ball (0 : E) 2).indicator
          (fun x => (ENNReal.ofReal |unitBallExtension (d := d) u x -
            unitBallExtension (d := d) v x|) ^ p) := by
    funext x
    by_cases hx : x ∈ Metric.ball (0 : E) 2
    · simp [hx]
    · have hnorm : 2 ≤ ‖x‖ := by
        rw [Metric.mem_ball, dist_zero_right] at hx
        linarith
      have hu0 : unitBallExtension (d := d) u x = 0 :=
        unitBallExtension_eq_zero_of_two_le_norm (d := d) (u := u) hnorm
      have hv0 : unitBallExtension (d := d) v x = 0 :=
        unitBallExtension_eq_zero_of_two_le_norm (d := d) (u := v) hnorm
      simp [hx, hu0, hv0, hp]
  calc
    ∫⁻ x, (ENNReal.ofReal |unitBallExtension (d := d) u x -
        unitBallExtension (d := d) v x|) ^ p ∂volume
        = ∫⁻ x, (Metric.ball (0 : E) 2).indicator
            (fun x => (ENNReal.ofReal |unitBallExtension (d := d) u x -
              unitBallExtension (d := d) v x|) ^ p) x ∂volume := by
          simpa using congrArg (fun g : E → ℝ≥0∞ => ∫⁻ x, g x ∂volume) hsupport
    _ = ∫⁻ x in Metric.ball (0 : E) 2,
          (ENNReal.ofReal |unitBallExtension (d := d) u x -
            unitBallExtension (d := d) v x|) ^ p ∂volume := by
          exact MeasureTheory.lintegral_indicator Metric.isOpen_ball.measurableSet _
    _ ≤ (1 + ENNReal.ofReal ((2 : ℝ) ^ (2 * d))) *
          ∫⁻ x in Metric.ball (0 : E) 1,
            (ENNReal.ofReal |u x - v x|) ^ p ∂volume := by
          simpa [unitBallExtension_sub (d := d) u v] using
            lintegral_rpow_abs_unitBallExtension_ball_two_le_local (d := d) hp.le
              (u := fun x => u x - v x)

private theorem tendsto_pair_sum_atTop_zero
    {a : ℕ → ℝ≥0∞}
    (ha : Tendsto a atTop (nhds 0)) :
    Tendsto (fun nm : ℕ × ℕ => a nm.1 + a nm.2) atTop (nhds 0) := by
  rw [← Filter.prod_atTop_atTop_eq]
  simpa using (ha.comp Filter.tendsto_fst).add (ha.comp Filter.tendsto_snd)

theorem tendsto_zero_of_le_pair_sum
    {b : ℕ × ℕ → ℝ≥0∞} {a : ℕ → ℝ≥0∞}
    (hb : ∀ nm : ℕ × ℕ, b nm ≤ a nm.1 + a nm.2)
    (ha : Tendsto a atTop (nhds 0)) :
    Tendsto b atTop (nhds 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (tendsto_pair_sum_atTop_zero ha) (fun _ => bot_le) hb

theorem eLpNorm_unitBallExtension_sub_le_local
    {p : ℝ} (hp : 1 < p) {u v : E → ℝ} :
    eLpNorm (fun x => unitBallExtension (d := d) u x - unitBallExtension (d := d) v x)
      (ENNReal.ofReal p) volume
      ≤
    (1 + ENNReal.ofReal ((2 : ℝ) ^ (2 * d))) ^ (1 / p) *
      eLpNorm (fun x => u x - v x) (ENNReal.ofReal p)
        (volume.restrict (Metric.ball (0 : E) 1)) := by
  have hp0 : 0 < p := by linarith
  have hInt :=
    lintegral_rpow_abs_unitBallExtension_sub_le_local (d := d) (p := p) hp0 (u := u) (v := v)
  calc
    eLpNorm (fun x => unitBallExtension (d := d) u x - unitBallExtension (d := d) v x)
        (ENNReal.ofReal p) volume
      ≤ ((1 + ENNReal.ofReal ((2 : ℝ) ^ (2 * d))) *
          ∫⁻ x in Metric.ball (0 : E) 1, (ENNReal.ofReal |u x - v x|) ^ p ∂volume) ^ (1 / p) := by
            simpa [Real.norm_eq_abs] using
              (eLpNorm_le_of_lintegral_rpow_ofReal_le_generic (α := E) (F := ℝ)
                (f := fun x => unitBallExtension (d := d) u x - unitBallExtension (d := d) v x)
                hp0 hInt)
    _ = (1 + ENNReal.ofReal ((2 : ℝ) ^ (2 * d))) ^ (1 / p) *
          eLpNorm (fun x => u x - v x) (ENNReal.ofReal p)
            (volume.restrict (Metric.ball (0 : E) 1)) := by
          have hAbs :
              (fun x => (ENNReal.ofReal |u x - v x|) ^ p) =
                (fun x => (ENNReal.ofReal ‖u x - v x‖) ^ p) := by
            funext x
            simp [Real.norm_eq_abs]
          have hPow :=
            lintegral_rpow_norm_eq_eLpNorm_pow (μ := volume.restrict (Metric.ball (0 : E) 1))
              (p := p) hp0 (f := fun x => u x - v x)
          rw [hAbs, hPow]
          have hMul :
              ((1 + ENNReal.ofReal ((2 : ℝ) ^ (2 * d))) *
                  eLpNorm (fun x => u x - v x) (ENNReal.ofReal p)
                    (volume.restrict (Metric.ball (0 : E) 1)) ^ p) ^ (1 / p) =
                (1 + ENNReal.ofReal ((2 : ℝ) ^ (2 * d))) ^ (1 / p) *
                  (eLpNorm (fun x => u x - v x) (ENNReal.ofReal p)
                    (volume.restrict (Metric.ball (0 : E) 1)) ^ p) ^ (1 / p) := by
            exact ENNReal.mul_rpow_of_nonneg _ _ (by positivity)
          rw [hMul]
          have hPowCancel :
              (eLpNorm (fun x => u x - v x) (ENNReal.ofReal p)
                (volume.restrict (Metric.ball (0 : E) 1)) ^ p) ^ (1 / p) =
                eLpNorm (fun x => u x - v x) (ENNReal.ofReal p)
                  (volume.restrict (Metric.ball (0 : E) 1)) := by
            rw [← ENNReal.rpow_mul, mul_comm, one_div, inv_mul_cancel₀ hp0.ne',
              ENNReal.rpow_one]
          rw [hPowCancel]

omit [NeZero d] in
private theorem measurable_unitBallRetraction :
    Measurable (unitBallRetraction (d := d)) := by
  classical
  unfold unitBallRetraction
  refine Measurable.piecewise (measurableSet_le measurable_norm measurable_const) measurable_id ?_
  refine Measurable.piecewise (measurableSet_lt measurable_norm measurable_const) ?_ measurable_const
  exact ((measurable_norm.pow_const 2).inv).smul measurable_id

omit [NeZero d] in
private theorem measurable_unitBallCutoff :
    Measurable (unitBallCutoff (d := d)) := by
  simpa [unitBallCutoff] using
    (measurable_const.min ((measurable_const.sub measurable_norm).max measurable_const))

omit [NeZero d] in
theorem measurable_unitBallExtension
    {u : E → ℝ} (hu : Measurable u) :
    Measurable (unitBallExtension (d := d) u) := by
  unfold unitBallExtension
  exact (measurable_unitBallCutoff (d := d)).mul (hu.comp (measurable_unitBallRetraction (d := d)))

omit [NeZero d] in
theorem eLpNorm_component_le
    {p : ℝ} (_hp : 0 < p) {F : E → E} {i : Fin d} {μ : Measure E}
    (_hF_aesm : AEStronglyMeasurable F μ) :
    eLpNorm (fun x => F x i) (ENNReal.ofReal p) μ ≤ eLpNorm F (ENNReal.ofReal p) μ := by
  refine eLpNorm_mono ?_
  intro x
  simpa using (PiLp.norm_apply_le (p := (2 : ℝ≥0∞)) (x := F x) (i := i))

omit [NeZero d] in
private theorem gradVec_eLpNorm_le_sum_local
    {μ : Measure E} {p : ℝ} {φ : E → ℝ} {G : E → E}
    (hp : 1 ≤ p)
    (hφ_smooth : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hG_comp_aesm : ∀ i : Fin d, AEStronglyMeasurable (fun x => G x i) μ) :
    eLpNorm
      (fun x =>
        WithLp.toLp 2 (fun i => (fderiv ℝ φ x) (EuclideanSpace.single i 1)) - G x)
      (ENNReal.ofReal p) μ
      ≤
    ∑ i : Fin d,
      eLpNorm
        (fun x => (fderiv ℝ φ x) (EuclideanSpace.single i 1) - G x i)
        (ENNReal.ofReal p) μ := by
  let δ : Fin d → E → ℝ :=
    fun i x => (fderiv ℝ φ x) (EuclideanSpace.single i 1) - G x i
  have hδ_aesm : ∀ i : Fin d, AEStronglyMeasurable (δ i) μ := by
    intro i
    have hpartial_meas :
        Measurable (fun x => (fderiv ℝ φ x) (EuclideanSpace.single i 1)) := by
      exact ((hφ_smooth.continuous_fderiv (by simp : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0)).clm_apply
        continuous_const).measurable
    exact hpartial_meas.aestronglyMeasurable.sub (hG_comp_aesm i)
  have hδnorm_eq :
      ∀ i : Fin d,
        eLpNorm (fun x => ‖δ i x‖) (ENNReal.ofReal p) μ =
          eLpNorm (δ i) (ENNReal.ofReal p) μ := by
    intro i
    simpa using (eLpNorm_norm (f := δ i) (p := ENNReal.ofReal p) (μ := μ))
  have hPointwise :
      ∀ᵐ x ∂μ,
        ‖WithLp.toLp 2 (fun i => (fderiv ℝ φ x) (EuclideanSpace.single i 1)) - G x‖ ≤
          ∑ i : Fin d, ‖δ i x‖ := by
    filter_upwards with x
    have hsplit :
        WithLp.toLp 2 (fun i => (fderiv ℝ φ x) (EuclideanSpace.single i 1)) - G x
          =
        ∑ i : Fin d,
          EuclideanSpace.single i (δ i x) := by
      ext i
      simp [δ, Finset.sum_apply]
    calc
      ‖WithLp.toLp 2 (fun i => (fderiv ℝ φ x) (EuclideanSpace.single i 1)) - G x‖
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
          WithLp.toLp 2 (fun i => (fderiv ℝ φ x) (EuclideanSpace.single i 1)) - G x)
        (ENNReal.ofReal p) μ
        ≤
      eLpNorm
        (fun x => ∑ i : Fin d, ‖δ i x‖)
        (ENNReal.ofReal p) μ := by
          exact eLpNorm_mono_ae_real hPointwise
    _ ≤ ∑ i : Fin d,
          eLpNorm (fun x => ‖δ i x‖) (ENNReal.ofReal p) μ := by
        have hp_enn : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
          rwa [← ENNReal.ofReal_one, ENNReal.ofReal_le_ofReal_iff (by linarith)]
        convert eLpNorm_sum_le (s := Finset.univ) (f := fun i => fun x => ‖δ i x‖)
          (fun i _ => (hδ_aesm i).norm) hp_enn using 1
        congr 1
        ext x
        simp [Finset.sum_apply]
    _ = ∑ i : Fin d,
          eLpNorm (δ i) (ENNReal.ofReal p) μ := by
        congr 1
        ext i
        exact hδnorm_eq i
    _ = _ := by
        simp [δ]

end DeGiorgi
