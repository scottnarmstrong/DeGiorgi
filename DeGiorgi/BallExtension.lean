import DeGiorgi.BallExtension.SmoothApproximation

/-!
# Chapter 02: Ball Extension

This file collects the main extension estimates built from the core, geometry,
rough-input, and smooth-approximation layers.
-/

noncomputable section

open MeasureTheory Metric Filter Topology Set Function Matrix
open scoped ENNReal NNReal RealInnerProductSpace

namespace DeGiorgi

variable {d : ℕ} [NeZero d]

local notation "E" => EuclideanSpace ℝ (Fin d)

-- === Main extension estimates ===
-- Pre-compiled in the geometry file where PiLp instance synthesis is already resolved.

/-- AEStronglyMeasurable for unitBallExtension of rough u.
Uses measurable representative + ae_eq transfer. -/
theorem aestronglyMeasurable_unitBallExtension_of_memLp
    {p : ℝ≥0∞} {u : E → ℝ}
    (hu : MemLp u p (volume.restrict (Metric.ball (0 : E) 1))) :
    AEStronglyMeasurable (unitBallExtension (d := d) u) volume := by
  -- Get measurable representative
  let u' := hu.aestronglyMeasurable.mk u
  have hu'_meas : Measurable u' := hu.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have hu'_ae : u =ᵐ[volume.restrict (Metric.ball (0 : E) 1)] u' :=
    hu.aestronglyMeasurable.ae_eq_mk
  -- unitBallExtension u' is measurable
  have hext_meas : Measurable (unitBallExtension (d := d) u') :=
    measurable_unitBallExtension (d := d) hu'_meas
  -- unitBallExtension u =ᵐ unitBallExtension u'
  -- because the retraction maps into closedBall(0,1) and u =ᵐ u' on ball(0,1)
  have hae_ext : unitBallExtension (d := d) u =ᵐ[volume] unitBallExtension (d := d) u' := by
    -- On the annulus {1 < ‖x‖ < 2}, retraction is inversion x ↦ x/‖x‖² which is
    -- a smooth diffeomorphism onto {1/2 < ‖y‖ < 1}. Preimage of null set under
    -- smooth diffeomorphism is null. Combined with: ball case (retract = id),
    -- sphere case (measure 0), and {‖x‖ ≥ 2} case (cutoff = 0).
    have hN : ∀ᵐ x ∂(volume : Measure E), x ∈ Metric.ball (0 : E) 1 → u x = u' x := by
      rwa [Filter.EventuallyEq, ae_restrict_iff' measurableSet_ball] at hu'_ae
    have hSph : ∀ᵐ x ∂(volume : Measure E), x ∉ Metric.sphere (0 : E) 1 := by
      have h0 : (volume : Measure E) (Metric.sphere (0 : E) 1) = 0 :=
        MeasureTheory.Measure.addHaar_sphere _ _ _
      exact ae_iff.mpr (by convert h0 using 1; simp only [not_not, Set.setOf_mem_eq])
    -- This follows from inversion being a smooth diffeomorphism (Lipschitz on compact subsets).
    have hAnn : ∀ᵐ x ∂(volume : Measure E),
        1 < ‖x‖ → ‖x‖ < 2 →
          u (unitBallRetraction (d := d) x) = u' (unitBallRetraction (d := d) x) := by
      let badInner : Set E := {y | y ∈ unitBallInnerShell (d := d) ∧ u y ≠ u' y}
      have hbadInner_ae : ∀ᵐ y ∂(volume : Measure E), y ∉ badInner := by
        filter_upwards [hN] with y hy
        intro hy_bad
        exact hy_bad.2 (hy <| by
          rcases hy_bad.1 with ⟨_hy_half, hy_lt_one⟩
          exact Metric.mem_ball.mpr (by rwa [dist_zero_right]))
      have hbadInner_zero : (volume : Measure E) badInner = 0 := by
        simpa [badInner] using (ae_iff.mp hbadInner_ae)
      have hdiff_badInner :
          DifferentiableOn ℝ (EuclideanGeometry.inversion (0 : E) 1) badInner := by
        intro y hy
        have hy0 : y ≠ (0 : E) := by
          intro hy0
          rcases hy.1 with ⟨hy_half, _hy_lt_one⟩
          have : (0 : ℝ) < ‖y‖ := by linarith
          simp [hy0] at this
        have hInv :=
          EuclideanGeometry.hasFDerivAt_inversion (c := (0 : E)) (R := (1 : ℝ)) hy0
        exact hInv.differentiableAt.differentiableWithinAt
      have himage_badInner_zero :
          (volume : Measure E) (EuclideanGeometry.inversion (0 : E) 1 '' badInner) = 0 := by
        exact addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero
          (μ := (volume : Measure E)) hdiff_badInner hbadInner_zero
      let badOuter : Set E := {x |
        x ∈ unitBallOuterShell (d := d) ∧
        u (unitBallRetraction (d := d) x) ≠ u' (unitBallRetraction (d := d) x)}
      have hbadOuter_subset :
          badOuter ⊆ EuclideanGeometry.inversion (0 : E) 1 '' badInner := by
        intro x hx
        rcases hx with ⟨hx_shell, hx_bad⟩
        refine ⟨EuclideanGeometry.inversion (0 : E) 1 x, ?_, ?_⟩
        · refine ⟨inversion_mem_unitBallInnerShell_of_mem_outerShell (d := d) hx_shell, ?_⟩
          simpa [unitBallRetraction_eq_inversion_of_mem_outerShell (d := d) hx_shell] using hx_bad
        · exact EuclideanGeometry.inversion_inversion (c := (0 : E)) (R := (1 : ℝ)) one_ne_zero x
      have hbadOuter_zero : (volume : Measure E) badOuter = 0 := by
        exact measure_mono_null hbadOuter_subset himage_badInner_zero
      have hbadOuter_ae : ∀ᵐ x ∂(volume : Measure E), x ∉ badOuter := by
        exact ae_iff.mpr (by simpa [badOuter, Set.setOf_mem_eq] using hbadOuter_zero)
      filter_upwards [hbadOuter_ae] with x hxBad
      intro hx1 hx2
      by_contra hneq
      exact hxBad ⟨⟨hx1, hx2⟩, hneq⟩
    filter_upwards [hN, hSph, hAnn] with x hx_ball hx_sph hx_ann
    simp only [unitBallExtension]
    by_cases h2 : 2 ≤ ‖x‖
    · simp [unitBallCutoff_eq_zero_of_two_le_norm (d := d) h2]
    · push_neg at h2
      rw [Metric.mem_sphere, dist_zero_right] at hx_sph
      rcases lt_or_gt_of_ne hx_sph with h1 | h1
      · -- ‖x‖ < 1: retraction = identity, x ∈ ball(0,1)
        rw [unitBallRetraction_eq_self_of_norm_le_one (d := d) h1.le]
        congr 1; exact hx_ball (Metric.mem_ball.mpr (by rwa [dist_zero_right]))
      · -- 1 < ‖x‖ < 2: use the annulus lemma
        congr 1; exact hx_ann h1 h2
  exact hext_meas.aestronglyMeasurable.congr hae_ext.symm

end DeGiorgi
