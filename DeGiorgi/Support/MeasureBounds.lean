import DeGiorgi.EllipticCoefficients

/-!
# Support: Measure Bounds

Shared measure-theoretic lemmas for essential suprema, essential infima, and
restricted ball measures used throughout the weak Harnack, Harnack, and Moser
Holder layers.
-/

noncomputable section

open MeasureTheory Filter Metric

namespace DeGiorgi

variable {d : ℕ} [NeZero d]

local notation "E" => AmbientSpace d

omit [NeZero d] in
theorem le_essInf_real_of_ae_le
    {μ : Measure E} (hμ : μ ≠ 0) {u : E → ℝ} {c : ℝ}
    (hlow : ∀ᵐ x ∂μ, c ≤ u x) :
    c ≤ essInf u μ := by
  rw [essInf_eq_sSup]
  refine le_csSup ?_ ?_
  · obtain ⟨N, hN_nonzero⟩ : ∃ N : ℕ, μ {x | u x ≤ N} ≠ 0 := by
      by_contra hN
      have hnull : ∀ N : ℕ, μ {x | u x ≤ N} = 0 := by
        intro N
        exact Classical.byContradiction fun hNZ => hN ⟨N, hNZ⟩
      have huniv : (⋃ N : ℕ, {x | u x ≤ N}) = Set.univ := by
        ext x
        constructor
        · intro _
          simp
        · intro _
          obtain ⟨N, hNx⟩ := exists_nat_ge (u x)
          exact Set.mem_iUnion.2 ⟨N, hNx⟩
      have hzero : μ Set.univ = 0 := by
        calc
          μ Set.univ = μ (⋃ N : ℕ, {x | u x ≤ N}) := by rw [huniv]
          _ = 0 := measure_iUnion_null hnull
      exact hμ (Measure.measure_univ_eq_zero.mp hzero)
    refine ⟨(N : ℝ), ?_⟩
    intro a ha
    rw [Set.mem_setOf_eq] at ha
    by_contra hle
    push_neg at hle
    have hsubset : {x | u x ≤ (N : ℝ)} ⊆ {x | u x < a} := by
      intro x hx
      exact lt_of_le_of_lt hx hle
    exact hN_nonzero (measure_mono_null hsubset ha)
  · rw [Set.mem_setOf_eq]
    rw [ae_iff] at hlow
    simpa [not_le] using hlow

omit [NeZero d] in
theorem restrict_ball_ne_zero {c : E} {r : ℝ} (hr : 0 < r) :
    volume.restrict (Metric.ball c r) ≠ 0 := by
  intro hzero
  have hball_zero : volume (Metric.ball c r) = 0 := by
    simpa [Measure.restrict_apply_univ] using
      congrArg (fun μ : Measure E => μ Set.univ) hzero
  exact (Metric.measure_ball_pos volume c hr).ne' hball_zero

omit [NeZero d] in
theorem essSup_le_of_ae_bdd
    {μ : Measure E} (hμ : μ ≠ 0)
    {u : E → ℝ} {K C : ℝ}
    (hlow : ∀ᵐ x ∂ μ, K ≤ u x)
    (hupp : ∀ᵐ x ∂ μ, u x ≤ C) :
    essSup u μ ≤ C := by
  rw [essSup_eq_sInf]
  refine csInf_le ?_ ?_
  · refine ⟨K, ?_⟩
    intro b hb
    by_contra hKb
    have hb_lt : b < K := lt_of_not_ge hKb
    have hlt : ∀ᵐ x ∂ μ, b < u x := by
      filter_upwards [hlow] with x hx
      linarith
    have hb_ae : ∀ᵐ x ∂ μ, ¬ b < u x := by
      change μ {x | b < u x} = 0 at hb
      rw [ae_iff]
      simpa using hb
    have hfalse : ∀ᵐ x ∂ μ, False := by
      filter_upwards [hlt, hb_ae] with x hx hx'
      exact hx' hx
    rw [ae_iff] at hfalse
    have hzero : μ Set.univ = 0 := by
      simpa using hfalse
    exact hμ (Measure.measure_univ_eq_zero.mp hzero)
  · change μ {x | C < u x} = 0
    simpa [ae_iff, not_lt] using hupp

omit [NeZero d] in
theorem le_essInf_of_ae_bdd
    {μ : Measure E} (hμ : μ ≠ 0)
    {u : E → ℝ} {c C : ℝ}
    (hlow : ∀ᵐ x ∂ μ, c ≤ u x)
    (hupp : ∀ᵐ x ∂ μ, u x ≤ C) :
    c ≤ essInf u μ := by
  rw [essInf_eq_sSup]
  refine le_csSup ?_ ?_
  · refine ⟨C, ?_⟩
    intro a ha
    by_contra hCa
    have hC_lt : C < a := lt_of_not_ge hCa
    have hlt : ∀ᵐ x ∂ μ, u x < a := by
      filter_upwards [hupp] with x hx
      linarith
    have ha_ae : ∀ᵐ x ∂ μ, ¬ u x < a := by
      change μ {x | u x < a} = 0 at ha
      rw [ae_iff]
      simpa using ha
    have hfalse : ∀ᵐ x ∂ μ, False := by
      filter_upwards [hlt, ha_ae] with x hx hx'
      exact hx' hx
    rw [ae_iff] at hfalse
    have hzero : μ Set.univ = 0 := by
      simpa using hfalse
    exact hμ (Measure.measure_univ_eq_zero.mp hzero)
  · change μ {x | u x < c} = 0
    simpa [ae_iff, not_lt] using hlow

omit [NeZero d] in
theorem essSup_add_const_of_bdd
    {μ : Measure E} (hμ : μ ≠ 0) {u : E → ℝ} (c : ℝ)
    (hu_bdd_below : Filter.IsBoundedUnder (· ≥ ·) (ae μ) u)
    (hu_bdd_above : Filter.IsBoundedUnder (· ≤ ·) (ae μ) u) :
    essSup (fun x => u x + c) μ = essSup u μ + c := by
  haveI : NeZero μ := ⟨hμ⟩
  haveI : (ae μ).NeBot := Measure.ae.neBot
  dsimp [essSup]
  simpa using
    (limsup_add_const (ae μ) u c hu_bdd_above hu_bdd_below.isCoboundedUnder_le)

omit [NeZero d] in
theorem essInf_add_const_of_bdd
    {μ : Measure E} (hμ : μ ≠ 0) {u : E → ℝ} (c : ℝ)
    (hu_bdd_below : Filter.IsBoundedUnder (· ≥ ·) (ae μ) u)
    (hu_bdd_above : Filter.IsBoundedUnder (· ≤ ·) (ae μ) u) :
    essInf (fun x => u x + c) μ = essInf u μ + c := by
  haveI : NeZero μ := ⟨hμ⟩
  haveI : (ae μ).NeBot := Measure.ae.neBot
  dsimp [essInf]
  simpa using
    (liminf_add_const (ae μ) u c hu_bdd_above.isCoboundedUnder_ge hu_bdd_below)

omit [NeZero d] in
theorem essSup_neg_of_bdd
    {μ : Measure E} (hμ : μ ≠ 0) {u : E → ℝ}
    (hu_bdd_below : Filter.IsBoundedUnder (· ≥ ·) (ae μ) u)
    (hu_bdd_above : Filter.IsBoundedUnder (· ≤ ·) (ae μ) u)
    (hneg_bdd_below : Filter.IsBoundedUnder (· ≥ ·) (ae μ) (fun x => -u x))
    (hneg_bdd_above : Filter.IsBoundedUnder (· ≤ ·) (ae μ) (fun x => -u x)) :
    essSup (fun x => -u x) μ = - essInf u μ := by
  haveI : NeZero μ := ⟨hμ⟩
  haveI : (ae μ).NeBot := Measure.ae.neBot
  dsimp [essSup, essInf]
  simpa using
    (OrderIso.liminf_apply (β := ℝ) (γ := ℝᵒᵈ) (f := ae μ) (u := u) (g := OrderIso.neg ℝ)
      hu_bdd_below hu_bdd_above.isCoboundedUnder_ge
      hneg_bdd_above hneg_bdd_below.isCoboundedUnder_le).symm

omit [NeZero d] in
theorem essInf_neg_of_bdd
    {μ : Measure E} (hμ : μ ≠ 0) {u : E → ℝ}
    (hu_bdd_below : Filter.IsBoundedUnder (· ≥ ·) (ae μ) u)
    (hu_bdd_above : Filter.IsBoundedUnder (· ≤ ·) (ae μ) u)
    (hneg_bdd_below : Filter.IsBoundedUnder (· ≥ ·) (ae μ) (fun x => -u x))
    (hneg_bdd_above : Filter.IsBoundedUnder (· ≤ ·) (ae μ) (fun x => -u x)) :
    essInf (fun x => -u x) μ = - essSup u μ := by
  haveI : NeZero μ := ⟨hμ⟩
  haveI : (ae μ).NeBot := Measure.ae.neBot
  dsimp [essSup, essInf]
  simpa using
    (OrderIso.limsup_apply (β := ℝ) (γ := ℝᵒᵈ) (f := ae μ) (u := u) (g := OrderIso.neg ℝ)
      hu_bdd_above hu_bdd_below.isCoboundedUnder_le
      hneg_bdd_below hneg_bdd_above.isCoboundedUnder_ge).symm

omit [NeZero d] in
theorem essInf_measurable_ennreal_smul_measure
    {μ : Measure E} {c : ENNReal} (hc : c ≠ 0) {f : E → ℝ} (_hf : Measurable f) :
    essInf f (c • μ) = essInf f μ := by
  rw [essInf_eq_sSup, essInf_eq_sSup]
  congr 1
  ext a
  change ((c • μ) {x | f x < a} = 0) ↔ (μ {x | f x < a} = 0)
  simp [Measure.smul_apply, hc, mul_eq_zero]

omit [NeZero d] in
theorem essInf_comp_measurableEmbedding_eq
    {μ : Measure E} {f : E → E} (hf : MeasurableEmbedding f)
    {g : E → ℝ} (_hg : Measurable g) :
    essInf (g ∘ f) μ = essInf g (Measure.map f μ) := by
  rw [essInf_eq_sSup, essInf_eq_sSup]
  congr 1
  ext a
  change (μ {x | (g ∘ f) x < a} = 0) ↔ ((Measure.map f μ) {x | g x < a} = 0)
  rw [hf.map_apply μ {x | g x < a}]
  simp [Function.comp]

end DeGiorgi
