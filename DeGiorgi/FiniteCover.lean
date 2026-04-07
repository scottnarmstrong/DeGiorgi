import DeGiorgi.Common

/-!
# Chapter 02: Finite Cover And Local-To-Global Glue

This file packages the compact-ball finite-cover pattern that later PDE proofs
use to pass from local estimates on small balls to a statement on a larger
interior ball.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace DeGiorgi

set_option maxHeartbeats 800000 in
private theorem lintegral_biUnion_finset_le_sum
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {ι : Type*} (t : Finset ι) (U : ι → Set α) (f : α → ℝ≥0∞) :
    (∫⁻ x in (⋃ i ∈ t, U i), f x ∂ μ) ≤
      Finset.sum t (fun i => ∫⁻ x in U i, f x ∂ μ) := by
  classical
  induction t using Finset.induction_on with
  | empty =>
      simp
  | insert a t ha ih =>
      calc
        (∫⁻ x in (⋃ i ∈ insert a t, U i), f x ∂ μ)
            = ∫⁻ x in (U a ∪ ⋃ i ∈ t, U i), f x ∂ μ := by
                simp
        _ ≤ (∫⁻ x in U a, f x ∂ μ) + ∫⁻ x in (⋃ i ∈ t, U i), f x ∂ μ := by
              exact lintegral_union_le f (U a) (⋃ i ∈ t, U i)
        _ ≤ (∫⁻ x in U a, f x ∂ μ) + Finset.sum t (fun i => ∫⁻ x in U i, f x ∂ μ) := by
              simpa [add_comm, add_left_comm, add_assoc] using
                add_le_add_right ih (∫⁻ x in U a, f x ∂ μ)
        _ = Finset.sum (insert a t) (fun i => ∫⁻ x in U i, f x ∂ μ) := by
              simp [Finset.sum_insert, ha]

private theorem volumeReal_ball_eq
    {d : ℕ} [NeZero d]
    (x : EuclideanSpace ℝ (Fin d)) {r : ℝ} (hr : 0 < r) :
    volume.real (Metric.ball x r) =
      r ^ d * volume.real (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1) := by
  have hdpos : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  haveI : Nontrivial (EuclideanSpace ℝ (Fin d)) :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (M := EuclideanSpace ℝ (Fin d)) <| by
      simpa [finrank_euclideanSpace] using hdpos
  rw [← Measure.addHaar_real_closedBall_eq_addHaar_real_ball (μ := volume) x r,
    Measure.addHaar_real_closedBall (μ := volume) x hr.le]
  simp [finrank_euclideanSpace]

private theorem exists_maximal_separated_subfinset
    {α : Type*} [PseudoMetricSpace α]
    (s : Finset α) {δ : ℝ} (hδ : 0 < δ) :
    ∃ t : Finset α,
      t ⊆ s ∧
      (↑t : Set α).Pairwise (fun x y => δ ≤ dist x y) ∧
      ∀ a ∈ s, ∃ c ∈ t, dist a c < δ := by
  classical
  let candidates :=
    s.powerset.filter (fun u : Finset α => (↑u : Set α).Pairwise fun x y => δ ≤ dist x y)
  have hcandidates_nonempty : candidates.Nonempty := by
    refine ⟨∅, ?_⟩
    refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.empty_subset s), ?_⟩
    intro x hx
    simp at hx
  obtain ⟨t, ht_mem, ht_max⟩ :=
    candidates.exists_max_image Finset.card hcandidates_nonempty
  have ht_subset : t ⊆ s := Finset.mem_powerset.mp (Finset.mem_filter.mp ht_mem).1
  have ht_sep : (↑t : Set α).Pairwise (fun x y => δ ≤ dist x y) :=
    (Finset.mem_filter.mp ht_mem).2
  refine ⟨t, ht_subset, ht_sep, ?_⟩
  intro a ha
  by_cases hat : a ∈ t
  · exact ⟨a, hat, by simpa using hδ⟩
  · by_contra hnet
    have hfar : ∀ c ∈ t, δ ≤ dist a c := by
      intro c hc
      by_contra hdist
      exact hnet ⟨c, hc, lt_of_not_ge hdist⟩
    have hinsert_subset : insert a t ⊆ s := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hxt
      · exact ha
      · exact ht_subset hxt
    have hinsert_sep : (↑(insert a t) : Set α).Pairwise (fun x y => δ ≤ dist x y) := by
      intro x hx y hy hxy
      rcases Finset.mem_insert.mp hx with rfl | hxt
      · rcases Finset.mem_insert.mp hy with rfl | hyt
        · exact False.elim (hxy rfl)
        · exact hfar y hyt
      · rcases Finset.mem_insert.mp hy with rfl | hyt
        · simpa [dist_comm] using hfar x hxt
        · exact ht_sep hxt hyt hxy
    have hinsert_mem : insert a t ∈ candidates := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hinsert_subset, hinsert_sep⟩
    have hcard_le : (insert a t).card ≤ t.card := ht_max _ hinsert_mem
    simp [Finset.card_insert_of_notMem hat] at hcard_le

/-- A compact inner ball can be covered by finitely many smaller balls whose
dilated closed balls still lie inside the ambient ball. -/
theorem exists_finite_inner_ball_cover
    {d : ℕ} [NeZero d]
    {x₀ : EuclideanSpace ℝ (Fin d)}
    {r ρ R : ℝ}
    (_hr : 0 < r)
    (hρ : 0 < ρ)
    (hbuffer : r + 2 * ρ < R) :
    ∃ t : Finset (EuclideanSpace ℝ (Fin d)),
      (∀ c ∈ t, c ∈ Metric.closedBall x₀ r) ∧
      Metric.closedBall x₀ r ⊆ ⋃ c ∈ t, Metric.ball c ρ ∧
      (∀ c ∈ t, Metric.closedBall c (2 * ρ) ⊆ Metric.ball x₀ R) := by
  obtain ⟨t, ht_mem, hcover⟩ :=
    (isCompact_closedBall x₀ r).elim_nhds_subcover
      (fun x => Metric.ball x ρ)
      (fun x hx => Metric.ball_mem_nhds x hρ)
  have hbuffer' : 2 * ρ + r < R := by
    simpa [add_comm, add_left_comm, add_assoc] using hbuffer
  refine ⟨t, ht_mem, hcover, ?_⟩
  intro c hc x hx
  have hc' : dist c x₀ ≤ r := by
    simpa using ht_mem c hc
  have hx' : dist x c ≤ 2 * ρ := by
    simpa using hx
  refine Metric.mem_ball.2 ?_
  calc
    dist x x₀ ≤ dist x c + dist c x₀ := dist_triangle _ _ _
    _ ≤ 2 * ρ + r := by linarith
    _ < R := hbuffer'

/-- A quantitative version of `exists_finite_inner_ball_cover` with a coarse
explicit cardinality bound depending only on `r / ρ` and `d`. -/
theorem exists_finite_inner_ball_cover_with_card
    {d : ℕ} [NeZero d]
    {x₀ : EuclideanSpace ℝ (Fin d)}
    {r ρ R : ℝ}
    (_hr : 0 < r)
    (hρ : 0 < ρ)
    (hbuffer : r + 2 * ρ < R) :
    ∃ t : Finset (EuclideanSpace ℝ (Fin d)),
      t.card ≤ Nat.ceil ((4 * r / ρ + 1) ^ d) ∧
      (∀ c ∈ t, c ∈ Metric.closedBall x₀ r) ∧
      Metric.closedBall x₀ r ⊆ ⋃ c ∈ t, Metric.ball c ρ ∧
      (∀ c ∈ t, Metric.closedBall c (2 * ρ) ⊆ Metric.ball x₀ R) := by
  classical
  have hquarter : 0 < ρ / 4 := by positivity
  obtain ⟨s, hs_mem, hs_cover, _⟩ :=
    exists_finite_inner_ball_cover
      (d := d) (x₀ := x₀) (r := r) (ρ := ρ / 4) (R := R)
      (by positivity) hquarter (by linarith)
  obtain ⟨t, ht_subset, ht_sep, ht_net⟩ :=
    exists_maximal_separated_subfinset s (δ := ρ / 2) (by positivity)
  have ht_mem : ∀ c ∈ t, c ∈ Metric.closedBall x₀ r := by
    intro c hc
    exact hs_mem c (ht_subset hc)
  have hcover : Metric.closedBall x₀ r ⊆ ⋃ c ∈ t, Metric.ball c ρ := by
    intro x hx
    have hxcover : x ∈ ⋃ c ∈ s, Metric.ball c (ρ / 4) := hs_cover hx
    rw [Set.mem_iUnion] at hxcover
    obtain ⟨a, hxcover⟩ := hxcover
    rw [Set.mem_iUnion] at hxcover
    obtain ⟨ha, hxa⟩ := hxcover
    obtain ⟨c, hc, hac⟩ := ht_net a ha
    refine Set.mem_iUnion.2 ⟨c, Set.mem_iUnion.2 ⟨hc, ?_⟩⟩
    refine Metric.mem_ball.2 ?_
    have hxa' : dist x a < ρ / 4 := by
      simpa using hxa
    calc
      dist x c ≤ dist x a + dist a c := dist_triangle _ _ _
      _ < ρ / 4 + ρ / 2 := by linarith
      _ < ρ := by linarith
  have hbuffer' : ∀ c ∈ t, Metric.closedBall c (2 * ρ) ⊆ Metric.ball x₀ R := by
    intro c hc x hx
    have hc' : dist c x₀ ≤ r := by
      simpa using ht_mem c hc
    have hx' : dist x c ≤ 2 * ρ := by
      simpa using hx
    refine Metric.mem_ball.2 ?_
    calc
      dist x x₀ ≤ dist x c + dist c x₀ := dist_triangle _ _ _
      _ ≤ 2 * ρ + r := by linarith
      _ < R := by simpa [add_comm, add_left_comm, add_assoc] using hbuffer
  have hdisj :
      (↑t : Set (EuclideanSpace ℝ (Fin d))).PairwiseDisjoint (fun c => Metric.ball c (ρ / 4)) := by
    intro c hc c' hc' hne
    change Disjoint (Metric.ball c (ρ / 4)) (Metric.ball c' (ρ / 4))
    rw [Set.disjoint_left]
    intro x hxc hxc'
    have hsep : ρ / 2 ≤ dist c c' := ht_sep hc hc' hne
    have hxc1 : dist x c < ρ / 4 := by
      simpa using hxc
    have hxc2 : dist x c' < ρ / 4 := by
      simpa using hxc'
    have hdist : dist c c' < ρ / 2 := by
      calc
        dist c c' ≤ dist c x + dist x c' := dist_triangle _ _ _
        _ < ρ / 4 + ρ / 4 := by
              simpa [dist_comm] using add_lt_add_of_lt_of_lt hxc1 hxc2
        _ = ρ / 2 := by ring
    exact False.elim ((not_lt_of_ge hsep) hdist)
  have hsmall_subset :
      (⋃ c ∈ t, Metric.ball c (ρ / 4)) ⊆ Metric.ball x₀ (r + ρ / 4) := by
    intro x hx
    rw [Set.mem_iUnion] at hx
    obtain ⟨c, hx⟩ := hx
    rw [Set.mem_iUnion] at hx
    obtain ⟨hc, hxc⟩ := hx
    have hc' : dist c x₀ ≤ r := by
      simpa using ht_mem c hc
    have hxc' : dist x c < ρ / 4 := by
      simpa using hxc
    refine Metric.mem_ball.2 ?_
    calc
      dist x x₀ ≤ dist x c + dist c x₀ := dist_triangle _ _ _
      _ < ρ / 4 + r := by linarith
      _ = r + ρ / 4 := by ring
  have hsum_le :
      ∑ c ∈ t, volume.real (Metric.ball c (ρ / 4))
        ≤ volume.real (Metric.ball x₀ (r + ρ / 4)) := by
    rw [← measureReal_biUnion_finset (μ := volume) hdisj (fun c hc => measurableSet_ball)
      (fun c hc => (measure_ball_lt_top (μ := volume) (x := c) (r := ρ / 4)).ne)]
    exact measureReal_mono hsmall_subset
  have hsum_eq :
      ∑ c ∈ t, volume.real (Metric.ball c (ρ / 4)) =
        (t.card : ℝ) *
          ((ρ / 4) ^ d * volume.real (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)) := by
    calc
      ∑ c ∈ t, volume.real (Metric.ball c (ρ / 4))
          = ∑ c ∈ t, ((ρ / 4) ^ d * volume.real (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)) := by
              refine Finset.sum_congr rfl ?_
              intro c hc
              exact volumeReal_ball_eq c hquarter
      _ = (t.card : ℝ) *
            ((ρ / 4) ^ d * volume.real (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)) := by
            simp [mul_left_comm]
  have hfactor : (ρ / 4) * (4 * r / ρ + 1) = r + ρ / 4 := by
    calc
      (ρ / 4) * (4 * r / ρ + 1) = (ρ / 4) * (4 * r / ρ) + ρ / 4 := by ring
      _ = r + ρ / 4 := by field_simp [hρ.ne']
  have houter_pos : 0 < r + ρ / 4 := by positivity
  have houter_eq :
      volume.real (Metric.ball x₀ (r + ρ / 4)) =
        ((4 * r / ρ + 1) ^ d) *
          ((ρ / 4) ^ d * volume.real (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)) := by
    rw [volumeReal_ball_eq x₀ houter_pos, ← hfactor, mul_pow]
    ring
  have hunit_pos : 0 < volume.real (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1) := by
    exact ENNReal.toReal_pos
      (Metric.measure_ball_pos volume (0 : EuclideanSpace ℝ (Fin d)) zero_lt_one).ne'
      measure_ball_lt_top.ne
  have hconst_pos :
      0 < (ρ / 4) ^ d * volume.real (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1) := by
    exact mul_pos (by positivity) hunit_pos
  have hcard_real : (t.card : ℝ) ≤ (4 * r / ρ + 1) ^ d := by
    rw [hsum_eq, houter_eq] at hsum_le
    nlinarith [hconst_pos]
  have hcard : t.card ≤ Nat.ceil ((4 * r / ρ + 1) ^ d) := by
    exact_mod_cast hcard_real.trans (Nat.le_ceil ((4 * r / ρ + 1) ^ d))
  exact ⟨t, hcard, ht_mem, hcover, hbuffer'⟩

/-- A specialized quantitative cover tailored to the half-ball / eighth-ball
geometry used in the crossover argument. -/
theorem exists_halfBall_cover_by_eighth_balls
    {d : ℕ} [NeZero d] :
    ∃ t : Finset (EuclideanSpace ℝ (Fin d)),
      t.card ≤ 17 ^ d ∧
      Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) (1 / 2 : ℝ) ⊆
        ⋃ c ∈ t, Metric.ball c (1 / 8 : ℝ) ∧
      (∀ c ∈ t,
        Metric.closedBall c (1 / 4 : ℝ) ⊆
          Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1) := by
  obtain ⟨t, htcard, _, hcover, hbuffer⟩ :=
    exists_finite_inner_ball_cover_with_card
      (d := d) (x₀ := (0 : EuclideanSpace ℝ (Fin d)))
      (r := (1 / 2 : ℝ)) (ρ := (1 / 8 : ℝ)) (R := 1)
      (by norm_num) (by norm_num) (by norm_num)
  have hpow :
      ((4 * (1 / 2 : ℝ) / (1 / 8 : ℝ) + 1) ^ d) = ((17 ^ d : ℕ) : ℝ) := by
    norm_num [Nat.cast_pow]
  have hceil :
      Nat.ceil ((4 * (1 / 2 : ℝ) / (1 / 8 : ℝ) + 1) ^ d) ≤ 17 ^ d := by
    rw [hpow, Nat.ceil_natCast]
  refine ⟨t, htcard.trans hceil, hcover, ?_⟩
  intro c hc
  convert hbuffer c hc using 1
  norm_num

/-- An a.e. statement on each member of a finite cover yields an a.e. statement
on the covered set. -/
theorem ae_on_set_of_ae_on_finite_cover
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {ι : Type*} {t : Finset ι}
    {s : Set α} {U : ι → Set α} {P : α → Prop}
    (hcover : s ⊆ ⋃ i ∈ t, U i)
    (hlocal : ∀ i ∈ t, ∀ᵐ x ∂ μ.restrict (U i), P x) :
    ∀ᵐ x ∂ μ.restrict s, P x := by
  have hunion : ∀ᵐ x ∂ μ.restrict (⋃ i ∈ t, U i), P x := by
    rw [ae_restrict_biUnion_finset_iff]
    exact hlocal
  exact ae_restrict_of_ae_restrict_of_subset hcover hunion

/-- The `lintegral` on a set is bounded by the sum of the `lintegral`s over any
finite cover of that set. -/
theorem lintegralOn_le_sum_lintegralOn_of_finite_cover
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {ι : Type*} {t : Finset ι}
    {s : Set α} {U : ι → Set α} {f : α → ℝ≥0∞}
    (hcover : s ⊆ ⋃ i ∈ t, U i) :
    (∫⁻ x in s, f x ∂ μ) ≤
      Finset.sum t (fun i => ∫⁻ x in U i, f x ∂ μ) := by
  calc
    (∫⁻ x in s, f x ∂ μ) ≤ (∫⁻ x in (⋃ i ∈ t, U i), f x ∂ μ) := by
      exact lintegral_mono_set hcover
    _ ≤ Finset.sum t (fun i => ∫⁻ x in U i, f x ∂ μ) :=
      lintegral_biUnion_finset_le_sum t U f

end DeGiorgi
