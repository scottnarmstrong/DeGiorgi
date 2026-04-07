import DeGiorgi.BallScaling
import DeGiorgi.DeGiorgiIteration
import DeGiorgi.Localization

/-!
# Moser Iteration Constants

This module contains the anchor constants for the Chapter 06 Moser iteration.
-/

noncomputable section

open MeasureTheory Filter

namespace DeGiorgi

variable {d : ℕ} [NeZero d]

/-- The anchor constant coming from the normalized De Giorgi `L² → L∞` bound. -/
noncomputable def C_MoserAnchor (d : ℕ) [NeZero d] : ℝ :=
  max 1
    (max ((C_DeGiorgi_subsolution_normalized d) ^ 2)
      (8 * (Mst : ℝ) ^ 2 * (C_gns d 2) ^ 2))

/-- The geometric decay ratio `q = (d-2)/d` used in the Moser iteration. -/
noncomputable def moserDecayRatio (d : ℕ) [NeZero d] : ℝ :=
  ((d : ℝ) - 2) / (d : ℝ)

/-- Dimension-only constant `C(d)` for the basic Moser `L^p → L∞` estimate.

It is chosen large enough to absorb both the existing `p = 2` De Giorgi anchor
and the purely geometric product appearing in the exact Moser iteration. -/
noncomputable def C_Moser (d : ℕ) [NeZero d] : ℝ :=
  let base := C_MoserAnchor d
  if _hd : 2 < (d : ℝ) then
    max base
      (((32 : ℝ) * base) ^ ((d : ℝ) / 2) *
        4 ^ (∑' n : ℕ, (n : ℝ) * moserDecayRatio d ^ n))
  else
    base

theorem one_le_C_MoserAnchor : 1 ≤ C_MoserAnchor d := by
  simp [C_MoserAnchor]

theorem C_DeGiorgi_subsolution_normalized_sq_le_C_MoserAnchor :
    (C_DeGiorgi_subsolution_normalized d) ^ 2 ≤ C_MoserAnchor d := by
  simp [C_MoserAnchor]

theorem cutoff_sobolev_anchor_le_C_MoserAnchor :
    8 * (Mst : ℝ) ^ 2 * (C_gns d 2) ^ 2 ≤ C_MoserAnchor d := by
  simp [C_MoserAnchor]

theorem C_MoserAnchor_le_C_Moser :
    C_MoserAnchor d ≤ C_Moser d := by
  by_cases hd : 2 < (d : ℝ)
  · simp [C_Moser, hd]
  · simp [C_Moser, hd]

theorem one_le_C_Moser : 1 ≤ C_Moser d := by
  exact (one_le_C_MoserAnchor (d := d)).trans (C_MoserAnchor_le_C_Moser (d := d))

theorem C_DeGiorgi_subsolution_normalized_sq_le_C_Moser :
    (C_DeGiorgi_subsolution_normalized d) ^ 2 ≤ C_Moser d := by
  exact
    (C_DeGiorgi_subsolution_normalized_sq_le_C_MoserAnchor (d := d)).trans
      (C_MoserAnchor_le_C_Moser (d := d))

end DeGiorgi
