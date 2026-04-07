import DeGiorgi.Holder.Representative

/-!
# Holder Endpoint

Public Holder estimates obtained from the representative construction.
-/

noncomputable section

open MeasureTheory Filter

namespace DeGiorgi

variable {d : ℕ} [NeZero d]

local notation "E" => AmbientSpace d
local notation "μ1" => volume.restrict (Metric.ball (0 : E) 1)
local notation "μhalf" => volume.restrict (Metric.ball (0 : E) (1 / 2 : ℝ))

theorem holder_Moser
    (hd : 2 < (d : ℝ))
    (A : NormalizedEllipticCoeff d (Metric.ball (0 : E) 1))
    {u : E → ℝ} {p₀ : ℝ} (hp₀ : 1 < p₀)
    (hsol : IsSolution A.1 u)
    (hInt : IntegrableOn (fun z => |u z| ^ p₀) (Metric.ball (0 : E) 1) volume) :
    ∃ v : E → ℝ,
      (∀ᵐ x ∂μ1, v x = u x) ∧
      ∃ α > 0,
        Real.exp (-(C_holder_Moser d * A.1.Λ ^ ((1 : ℝ) / 2))) ≤ α ∧
        ∀ x ∈ Metric.ball (0 : E) (1 / 2 : ℝ),
        ∀ y ∈ Metric.ball (0 : E) (1 / 2 : ℝ),
          |v x - v y| ≤
            C_holder_Moser d * A.1.Λ ^ ((d : ℝ) / (2 * p₀)) *
              (p₀ / (p₀ - 1)) ^ ((d : ℝ) / p₀) *
              (∫ z in Metric.ball (0 : E) 1, |u z| ^ p₀ ∂volume) ^ ((1 : ℝ) / p₀) *
              ‖x - y‖ ^ α := by
  let α : ℝ := moserDecayAlpha A
  have hα_pos : 0 < α := by
    simpa [α] using moserDecayAlpha_pos (d := d) A
  let v : E → ℝ := moserRepresentative u
  have hvu : v =ᵐ[μ1] u :=
    moserRepresentative_ae_eq (d := d) hd A hp₀ hsol hInt
  refine ⟨v, hvu, α, hα_pos, ?_, ?_⟩
  · simpa [α] using moserLowerBound_le_decayAlpha (d := d) hd A
  · intro x hx y hy
    by_cases hxy_eq : x = y
    · subst hxy_eq
      simp [hα_pos.ne', α]
    · by_cases hlarge : (1 / 8 : ℝ) ≤ ‖x - y‖
      · simpa [v, α, moserHolderNorm, mul_assoc, mul_left_comm, mul_comm] using
          (moserRepresentative_large_distance_bound
            (d := d) hd A hp₀ hsol hInt hx hy hxy_eq hlarge)
      · have hsmall : ‖x - y‖ < (1 / 8 : ℝ) := lt_of_not_ge hlarge
        simpa [v, α, moserHolderNorm, mul_assoc, mul_left_comm, mul_comm] using
          (moserRepresentative_small_distance_bound
            (d := d) hd A hp₀ hsol hInt hx hy hxy_eq hsmall)

/-- Moser interior Hölder regularity for homogeneous local weak solutions. -/
theorem holder_Moser_of_homogeneousWeakSolution
    (hd : 2 < (d : ℝ))
    (A : NormalizedEllipticCoeff d (Metric.ball (0 : E) 1))
    {u : E → ℝ} {p₀ : ℝ} (hp₀ : 1 < p₀)
    (hweak : IsHomogeneousWeakSolution A.1 u)
    (hInt : IntegrableOn (fun z => |u z| ^ p₀) (Metric.ball (0 : E) 1) volume) :
    ∃ v : E → ℝ,
      (∀ᵐ x ∂μ1, v x = u x) ∧
      ∃ α > 0,
        Real.exp (-(C_holder_Moser d * A.1.Λ ^ ((1 : ℝ) / 2))) ≤ α ∧
        ∀ x ∈ Metric.ball (0 : E) (1 / 2 : ℝ),
        ∀ y ∈ Metric.ball (0 : E) (1 / 2 : ℝ),
          |v x - v y| ≤
            C_holder_Moser d * A.1.Λ ^ ((d : ℝ) / (2 * p₀)) *
              (p₀ / (p₀ - 1)) ^ ((d : ℝ) / p₀) *
              (∫ z in Metric.ball (0 : E) 1, |u z| ^ p₀ ∂volume) ^ ((1 : ℝ) / p₀) *
              ‖x - y‖ ^ α := by
  exact holder_Moser hd A hp₀ (isHomogeneousWeakSolution_isSolution hweak) hInt

end DeGiorgi
