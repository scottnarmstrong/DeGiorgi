import Mathlib

/-!
# Common Prelude

This module is the shared prelude for the De Giorgi development.

Policy:

- imports come directly from `Mathlib`;
- declarations in this directory live under `DeGiorgi`;
- shared opens and scoped notations live here so the theorem files stay small.
-/

noncomputable section

open MeasureTheory Metric Set Filter
open scoped ENNReal NNReal Topology InnerProductSpace

namespace DeGiorgi

end DeGiorgi
