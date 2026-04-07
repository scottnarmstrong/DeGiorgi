import DeGiorgi.WeakFormulation.BilinearForm

/-!
# Weak Formulation: Solution Interfaces

This module packages weak problems together with the weak-solution,
subsolution, and supersolution interfaces built from the bilinear form.
-/

noncomputable section

open MeasureTheory Filter
open scoped InnerProductSpace

namespace DeGiorgi

variable {d : ℕ} [NeZero d]

local notation "E" => AmbientSpace d

/-- A weak elliptic Dirichlet problem on an open bounded domain. -/
structure WeakProblem where
  Ω : Set E
  hΩ : IsOpen Ω
  hΩ_bdd : Bornology.IsBounded Ω
  coeff : EllipticCoeff d Ω
  rhs : (E → ℝ) → ℝ

/-- `u` is a weak solution of the variational problem `P` if it lies in
`H₀¹(P.Ω)` and satisfies the weak identity against every `H₀¹` test function. -/
def IsWeakSolution (P : WeakProblem (d := d)) (u : E → ℝ) : Prop :=
  MemH01 u P.Ω ∧
  ∀ (hwu : MemW1pWitness 2 u P.Ω) (v : E → ℝ), MemH01 v P.Ω →
    ∀ (hwv : MemW1pWitness 2 v P.Ω),
      bilinFormOfCoeff P.coeff hwu hwv = P.rhs v

/-- `u` is a weak subsolution of `-div(A∇u) ≤ 0` on `Ω`. -/
def IsSubsolution {Ω : Set E} (A : EllipticCoeff d Ω) (u : E → ℝ) : Prop :=
  MemW1p 2 u Ω ∧
  ∀ (hu : MemW1pWitness 2 u Ω)
    (φ : E → ℝ), MemH01 φ Ω →
    ∀ (hφ : MemW1pWitness 2 φ Ω),
      (∀ x, 0 ≤ φ x) → bilinFormOfCoeff A hu hφ ≤ 0

/-- `u` is a weak supersolution of `-div(A∇u) ≥ 0` on `Ω`. -/
def IsSupersolution {Ω : Set E} (A : EllipticCoeff d Ω) (u : E → ℝ) : Prop :=
  MemW1p 2 u Ω ∧
  ∀ (hu : MemW1pWitness 2 u Ω)
    (φ : E → ℝ), MemH01 φ Ω →
    ∀ (hφ : MemW1pWitness 2 φ Ω),
      (∀ x, 0 ≤ φ x) → 0 ≤ bilinFormOfCoeff A hu hφ

/-- `u` is a weak solution of the homogeneous equation iff it is both a weak
subsolution and a weak supersolution. -/
def IsSolution {Ω : Set E} (A : EllipticCoeff d Ω) (u : E → ℝ) : Prop :=
  IsSubsolution A u ∧ IsSupersolution A u

/-- `u` is a local weak solution of the homogeneous equation on `Ω` if it lies
in `W^{1,2}(Ω)` and the bilinear form vanishes against every `H₀¹(Ω)` test
function. This is the equality-form local weak-solution interface used by the
Harnack and Holder statements. -/
def IsHomogeneousWeakSolution {Ω : Set E}
    (A : EllipticCoeff d Ω) (u : E → ℝ) : Prop :=
  MemW1p 2 u Ω ∧
  ∀ (hu : MemW1pWitness 2 u Ω)
    (φ : E → ℝ), MemH01 φ Ω →
    ∀ (hφ : MemW1pWitness 2 φ Ω),
      bilinFormOfCoeff A hu hφ = 0

/-- Extract Sobolev membership from a subsolution. -/
theorem isSubsolution_memW1p {Ω : Set E} {A : EllipticCoeff d Ω} {u : E → ℝ}
    (h : IsSubsolution A u) : MemW1p 2 u Ω :=
  h.left

/-- Extract Sobolev membership from a supersolution. -/
theorem isSupersolution_memW1p {Ω : Set E} {A : EllipticCoeff d Ω} {u : E → ℝ}
    (h : IsSupersolution A u) : MemW1p 2 u Ω :=
  h.left

/-- A homogeneous weak solution is a subsolution. -/
theorem isHomogeneousWeakSolution_isSubsolution
    {Ω : Set E} {A : EllipticCoeff d Ω} {u : E → ℝ}
    (h : IsHomogeneousWeakSolution A u) :
    IsSubsolution A u := by
  refine ⟨h.1, ?_⟩
  intro hu φ hφ hφw hφ_nonneg
  have hEq : bilinFormOfCoeff A hu hφw = 0 := h.2 hu φ hφ hφw
  simp [hEq]

/-- A homogeneous weak solution is a supersolution. -/
theorem isHomogeneousWeakSolution_isSupersolution
    {Ω : Set E} {A : EllipticCoeff d Ω} {u : E → ℝ}
    (h : IsHomogeneousWeakSolution A u) :
    IsSupersolution A u := by
  refine ⟨h.1, ?_⟩
  intro hu φ hφ hφw hφ_nonneg
  have hEq : bilinFormOfCoeff A hu hφw = 0 := h.2 hu φ hφ hφw
  simp [hEq]

/-- A homogeneous weak solution is both a subsolution and a supersolution. -/
theorem isHomogeneousWeakSolution_isSolution
    {Ω : Set E} {A : EllipticCoeff d Ω} {u : E → ℝ}
    (h : IsHomogeneousWeakSolution A u) :
    IsSolution A u :=
  ⟨isHomogeneousWeakSolution_isSubsolution h,
    isHomogeneousWeakSolution_isSupersolution h⟩

end DeGiorgi
