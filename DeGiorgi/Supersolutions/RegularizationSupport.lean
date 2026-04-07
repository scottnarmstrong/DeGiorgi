import DeGiorgi.Supersolutions.TestFunctions

/-!
# Supersolutions Regularization Support

This module contains the shared epsilon-regularization and dominated
convergence lemmas used by both the forward and inverse supersolution arguments.
-/

noncomputable section

open MeasureTheory Metric

namespace DeGiorgi

variable {d : ℕ} [NeZero d]

local notation "E" => AmbientSpace d
local notation "μhalf" => (volume.restrict (Metric.ball (0 : E) (1 / 2 : ℝ)))

set_option maxHeartbeats 200000

def superEpsSeq (n : ℕ) : ℝ := (((n : ℝ) + 1) : ℝ)⁻¹

theorem superEpsSeq_pos (n : ℕ) : 0 < superEpsSeq n := by
  dsimp [superEpsSeq]
  positivity

theorem tendsto_superEpsSeq :
    Filter.Tendsto superEpsSeq Filter.atTop (nhds 0) := by
  unfold superEpsSeq
  have hbase : Filter.Tendsto (fun n : ℕ => n + 1) Filter.atTop Filter.atTop :=
    Filter.tendsto_add_atTop_nat 1
  have h :=
    ((tendsto_inv_atTop_nhds_zero_nat :
        Filter.Tendsto (fun n : ℕ => ((n : ℝ))⁻¹) Filter.atTop (nhds 0)).comp hbase)
  refine h.congr' ?_
  exact Filter.Eventually.of_forall fun n => by
    change ((((n + 1 : ℕ) : ℝ))⁻¹) = (((n : ℝ) + 1)⁻¹)
    norm_num [Nat.cast_add]

theorem superEpsSeq_le_one (n : ℕ) : superEpsSeq n ≤ 1 := by
  dsimp [superEpsSeq]
  have hden_ge : (1 : ℝ) ≤ (n : ℝ) + 1 := by
    have hn_nonneg : (0 : ℝ) ≤ n := by exact_mod_cast Nat.zero_le n
    linarith
  exact inv_le_one_of_one_le₀ hden_ge

theorem superExactShiftPow_tendsto_rpow_of_pos
    {a t : ℝ} (ht : 0 < t) :
    Filter.Tendsto (fun n : ℕ => superExactShiftPow (superEpsSeq n) a t)
      Filter.atTop (nhds (t ^ a)) := by
  have hsum :
      Filter.Tendsto (fun n : ℕ => superEpsSeq n + t) Filter.atTop (nhds (0 + t)) :=
    tendsto_superEpsSeq.add tendsto_const_nhds
  have hpow :
      Filter.Tendsto (fun n : ℕ => (superEpsSeq n + t) ^ a) Filter.atTop
        (nhds ((0 + t) ^ a)) := by
    have ht_ne : (0 : ℝ) + t ≠ 0 := by linarith
    simpa [zero_add] using hsum.rpow_const (Or.inl ht_ne)
  have heq :
      (fun n : ℕ => superExactShiftPow (superEpsSeq n) a t) =ᶠ[Filter.atTop]
        (fun n : ℕ => (superEpsSeq n + t) ^ a) := by
    exact Filter.Eventually.of_forall fun n => by
      simpa using
        (superExactShiftPow_eq_shifted_of_nonneg (ε := superEpsSeq n) (a := a)
          (superEpsSeq_pos n) ht.le)
  simpa [zero_add] using hpow.congr' heq.symm

theorem superExactShiftReg_deriv_tendsto_of_pos
    {a t : ℝ} (ht : 0 < t) :
    Filter.Tendsto (fun n : ℕ => deriv (superExactShiftReg (superEpsSeq n) a) t)
      Filter.atTop (nhds (a * t ^ (a - 1))) := by
  have hsum :
      Filter.Tendsto (fun n : ℕ => superEpsSeq n + t) Filter.atTop (nhds (0 + t)) :=
    tendsto_superEpsSeq.add tendsto_const_nhds
  have hpow :
      Filter.Tendsto (fun n : ℕ => (superEpsSeq n + t) ^ (a - 1))
        Filter.atTop (nhds ((0 + t) ^ (a - 1))) := by
    have ht_ne : (0 : ℝ) + t ≠ 0 := by linarith
    simpa [zero_add] using hsum.rpow_const (Or.inl ht_ne)
  have hmul :
      Filter.Tendsto (fun n : ℕ => a * (superEpsSeq n + t) ^ (a - 1))
        Filter.atTop (nhds (a * t ^ (a - 1))) := by
    simpa [zero_add] using Filter.Tendsto.const_mul a hpow
  have heq :
      (fun n : ℕ => deriv (superExactShiftReg (superEpsSeq n) a) t) =ᶠ[Filter.atTop]
        (fun n : ℕ => a * (superEpsSeq n + t) ^ (a - 1)) := by
    exact Filter.Eventually.of_forall fun n => by
      simpa using
        (superExactShiftReg_deriv_eq_shifted (ε := superEpsSeq n) (a := a)
          (superEpsSeq_pos n) ht)
  exact hmul.congr' heq.symm

omit [NeZero d] in
theorem superExactPowerCutoff_tendsto_powerCutoff_of_pos
    {u η : E → ℝ} {p : ℝ} {x : E}
    (hux : 0 < u x) :
    Filter.Tendsto (fun n : ℕ => superExactPowerCutoff η u (superEpsSeq n) (-(p / 2)) x)
      Filter.atTop (nhds (superPowerCutoff (d := d) η u p x)) := by
  have hpow :=
    superExactShiftPow_tendsto_rpow_of_pos (a := -(p / 2)) (t := u x) hux
  have hmul :
      Filter.Tendsto (fun n : ℕ => η x * superExactShiftPow (superEpsSeq n) (-(p / 2)) (u x))
        Filter.atTop (nhds (η x * (u x) ^ (-(p / 2)))) := by
    exact Filter.Tendsto.const_mul (η x) hpow
  have hpow_eq :
      (u x) ^ (-(p / 2)) = |(u x)⁻¹| ^ (p / 2) := by
    rw [abs_of_pos (inv_pos.mpr hux)]
    rw [show (-(p / 2) : ℝ) = -(p / 2) by ring, Real.rpow_neg hux.le]
    rw [Real.inv_rpow hux.le]
  simpa [superExactPowerCutoff_eq_mul_shiftPow, superPowerCutoff, hpow_eq] using hmul

omit [NeZero d] in
theorem superExactInv_rhs_tendsto
    {u : E → ℝ} {p : ℝ} {x : E}
    (hux : 0 < u x) :
    Filter.Tendsto (fun n : ℕ => superExactShiftPow (superEpsSeq n) (-p) (u x))
      Filter.atTop (nhds (|(u x)⁻¹| ^ p)) := by
  have hpow :=
    superExactShiftPow_tendsto_rpow_of_pos (a := -p) (t := u x) hux
  have hpow_eq : (u x) ^ (-p) = |(u x)⁻¹| ^ p := by
    rw [abs_of_pos (inv_pos.mpr hux)]
    rw [show (-p : ℝ) = -p by ring, Real.rpow_neg hux.le]
    rw [Real.inv_rpow hux.le]
  simpa [hpow_eq] using hpow

theorem superExactShiftPow_le_inv_rpow_of_pos
    {ε q t : ℝ} (hε : 0 < ε) (hq : 0 ≤ q) (ht : 0 < t) :
    superExactShiftPow ε (-q) t ≤ |t⁻¹| ^ q := by
  rw [superExactShiftPow_eq_shifted_of_nonneg (ε := ε) (a := -q) hε ht.le]
  have hle : (ε + t) ^ (-q) ≤ t ^ (-q) := by
    exact Real.rpow_le_rpow_of_nonpos ht (by linarith) (by linarith)
  have heq : t ^ (-q) = |t⁻¹| ^ q := by
    rw [abs_of_pos (inv_pos.mpr ht)]
    rw [show (-q : ℝ) = -q by ring, Real.rpow_neg ht.le]
    rw [Real.inv_rpow ht.le]
  exact hle.trans_eq heq

theorem superExactShiftPow_le_one_add_rpow_of_pos
    {ε a t : ℝ} (hε : 0 < ε) (hε_le : ε ≤ 1) (ha : 0 ≤ a) (ha1 : a ≤ 1) (ht : 0 < t) :
    superExactShiftPow ε a t ≤ 1 + |t| ^ a := by
  rw [superExactShiftPow_eq_shifted_of_nonneg (ε := ε) (a := a) hε ht.le]
  have hsubadd := Real.rpow_add_le_add_rpow hε.le ht.le ha ha1
  have hεa_le : ε ^ a ≤ 1 := by
    simpa using (Real.rpow_le_rpow hε.le hε_le ha)
  have hta_nonneg : 0 ≤ t ^ a := Real.rpow_nonneg ht.le _
  calc
    (ε + t) ^ a ≤ ε ^ a + t ^ a := hsubadd
    _ ≤ 1 + t ^ a := by linarith
    _ = 1 + |t| ^ a := by rw [abs_of_pos ht]

theorem superExactShiftReg_deriv_abs_le_inv_rpow_of_pos
    {ε q t : ℝ} (hε : 0 < ε) (hq : 0 ≤ q) (ht : 0 < t) :
    |deriv (superExactShiftReg ε (-q)) t| ≤ q * |t⁻¹| ^ (q + 1) := by
  have hderiv :
      deriv (superExactShiftReg ε (-q)) t =
        (-q) * (ε + t) ^ (-q - 1) := by
    rw [superExactShiftReg_deriv_eq_shifted (ε := ε) (a := -q) hε ht]
  have hpow_nonneg : 0 ≤ (ε + t) ^ (-q - 1) := by
    exact Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ ε + t) _
  have hpow_le : (ε + t) ^ (-q - 1) ≤ |t⁻¹| ^ (q + 1) := by
    have hle : (ε + t) ^ (-q - 1) ≤ t ^ (-q - 1) := by
      exact Real.rpow_le_rpow_of_nonpos ht (by linarith) (by linarith)
    have heq : t ^ (-q - 1) = |t⁻¹| ^ (q + 1) := by
      rw [abs_of_pos (inv_pos.mpr ht)]
      rw [show (-q - 1 : ℝ) = -(q + 1) by ring, Real.rpow_neg ht.le]
      rw [Real.inv_rpow ht.le]
    exact hle.trans_eq heq
  calc
    |deriv (superExactShiftReg ε (-q)) t|
        = q * (ε + t) ^ (-q - 1) := by
            rw [hderiv, abs_mul, abs_of_nonpos (by linarith), abs_of_nonneg hpow_nonneg]
            ring
    _ ≤ q * |t⁻¹| ^ (q + 1) := by
          exact mul_le_mul_of_nonneg_left hpow_le hq

theorem superExactShiftReg_deriv_le_rpow_of_pos
    {ε a t : ℝ} (hε : 0 < ε) (ha : 0 ≤ a) (ha1 : a ≤ 1) (ht : 0 < t) :
    deriv (superExactShiftReg ε a) t ≤ a * |t| ^ (a - 1) := by
  have hderiv :
      deriv (superExactShiftReg ε a) t =
        a * (ε + t) ^ (a - 1) := by
    rw [superExactShiftReg_deriv_eq_shifted (ε := ε) (a := a) hε ht]
  have hpow_le : (ε + t) ^ (a - 1) ≤ t ^ (a - 1) := by
    exact Real.rpow_le_rpow_of_nonpos ht (by linarith) (by linarith)
  calc
    deriv (superExactShiftReg ε a) t = a * (ε + t) ^ (a - 1) := hderiv
    _ ≤ a * t ^ (a - 1) := by
          exact mul_le_mul_of_nonneg_left hpow_le ha
    _ = a * |t| ^ (a - 1) := by rw [abs_of_pos ht]

omit [NeZero d] in
theorem abs_fderiv_apply_le_norm_fderiv
    {f : E → ℝ} {x : E} (i : Fin d) :
    |(fderiv ℝ f x) (EuclideanSpace.single i 1)| ≤ ‖fderiv ℝ f x‖ := by
  calc
    |(fderiv ℝ f x) (EuclideanSpace.single i 1)|
        = |(WithLp.toLp 2
            (fun j => (fderiv ℝ f x) (EuclideanSpace.single j 1))) i| := by
              simp
    _ ≤ ‖WithLp.toLp 2
          (fun j => (fderiv ℝ f x) (EuclideanSpace.single j 1))‖ := by
            simpa [Real.norm_eq_abs] using
              (PiLp.norm_apply_le
                (WithLp.toLp 2
                  (fun j => (fderiv ℝ f x) (EuclideanSpace.single j 1))) i)
    _ = ‖fderiv ℝ f x‖ := by
          rw [← super_norm_fderiv_eq_norm_partials (d := d) (f := f) (x := x)]

omit [NeZero d] in
theorem superExactInv_deriv_tendsto
    {u : E → ℝ} {p : ℝ} {x : E}
    (hux : 0 < u x) :
    Filter.Tendsto
      (fun n : ℕ => deriv (superExactShiftReg (superEpsSeq n) (-(p / 2))) (u x))
      Filter.atTop
      (nhds ((-(p / 2)) * |(u x)⁻¹| ^ (p / 2 + 1))) := by
  have hderiv :=
    superExactShiftReg_deriv_tendsto_of_pos (a := -(p / 2)) (t := u x) hux
  have hpow_eq :
      (-(p / 2)) * (u x) ^ (-(p / 2) - 1) =
        (-(p / 2)) * |(u x)⁻¹| ^ (p / 2 + 1) := by
    congr 1
    rw [abs_of_pos (inv_pos.mpr hux)]
    rw [show (-(p / 2) - 1 : ℝ) = -((p / 2) + 1) by ring, Real.rpow_neg hux.le]
    rw [Real.inv_rpow hux.le]
  simpa [hpow_eq] using hderiv

omit [NeZero d] in
theorem superExactPowerCutoff_tendsto_powerCutoffFwd_of_pos
    {u η : E → ℝ} {p : ℝ} {x : E}
    (hux : 0 < u x) :
    Filter.Tendsto (fun n : ℕ => superExactPowerCutoff η u (superEpsSeq n) (p / 2) x)
      Filter.atTop (nhds (η x * |u x| ^ (p / 2))) := by
  have hpow :=
    superExactShiftPow_tendsto_rpow_of_pos (a := p / 2) (t := u x) hux
  have hmul :
      Filter.Tendsto (fun n : ℕ => η x * superExactShiftPow (superEpsSeq n) (p / 2) (u x))
        Filter.atTop (nhds (η x * (u x) ^ (p / 2))) := by
    exact Filter.Tendsto.const_mul (η x) hpow
  have hpow_eq : (u x) ^ (p / 2) = |u x| ^ (p / 2) := by
    rw [abs_of_pos hux]
  simpa [superExactPowerCutoff_eq_mul_shiftPow, hpow_eq] using hmul

omit [NeZero d] in
theorem superExactFwd_rhs_tendsto
    {u : E → ℝ} {p : ℝ} {x : E}
    (hux : 0 < u x) :
    Filter.Tendsto (fun n : ℕ => superExactShiftPow (superEpsSeq n) p (u x))
      Filter.atTop (nhds (|u x| ^ p)) := by
  have hpow :=
    superExactShiftPow_tendsto_rpow_of_pos (a := p) (t := u x) hux
  have hpow_eq : (u x) ^ p = |u x| ^ p := by
    rw [abs_of_pos hux]
  simpa [hpow_eq] using hpow

omit [NeZero d] in
theorem superExactFwd_deriv_tendsto
    {u : E → ℝ} {p : ℝ} {x : E}
    (hux : 0 < u x) :
    Filter.Tendsto
      (fun n : ℕ => deriv (superExactShiftReg (superEpsSeq n) (p / 2)) (u x))
      Filter.atTop
      (nhds ((p / 2) * |u x| ^ (p / 2 - 1))) := by
  have hderiv :=
    superExactShiftReg_deriv_tendsto_of_pos (a := p / 2) (t := u x) hux
  have hpow_eq :
      (p / 2) * (u x) ^ (p / 2 - 1) =
        (p / 2) * |u x| ^ (p / 2 - 1) := by
    congr 1
    rw [abs_of_pos hux]
  simpa [hpow_eq] using hderiv

omit [NeZero d] in
theorem invPower_half_memLp_of_integrableOn
    {Ω : Set E} {u : E → ℝ} {p : ℝ}
    (hp : 0 ≤ p)
    (hu : MemW1pWitness 2 u Ω)
    (hpInt : IntegrableOn (fun x => |(u x)⁻¹| ^ p) Ω volume) :
    MemLp (fun x => |(u x)⁻¹| ^ (p / 2)) 2 (volume.restrict Ω) := by
  have hpow_cont : Continuous fun t : ℝ => t ^ (p / 2) := by
    exact Real.continuous_rpow_const (by linarith)
  have hmeas :
      AEStronglyMeasurable (fun x => |(u x)⁻¹| ^ (p / 2)) (volume.restrict Ω) := by
    exact
      (hpow_cont.measurable.comp_aemeasurable
        ((measurable_abs.comp_aemeasurable
          hu.memLp.aestronglyMeasurable.aemeasurable.inv))).aestronglyMeasurable
  refine (MeasureTheory.memLp_two_iff_integrable_sq hmeas).2 ?_
  have hpInt' : Integrable (fun x => |(u x)⁻¹| ^ p) (volume.restrict Ω) := by
    simpa [IntegrableOn] using hpInt
  refine hpInt'.congr ?_
  filter_upwards with x
  symm
  rw [← Real.rpow_natCast (|(u x)⁻¹| ^ (p / 2)) 2]
  rw [← Real.rpow_mul]
  · congr 1
    ring
  · positivity

omit [NeZero d] in
theorem power_half_memLp_of_integrableOn
    {Ω : Set E} {u : E → ℝ} {p : ℝ}
    (hp : 0 ≤ p)
    (hu : MemW1pWitness 2 u Ω)
    (hpInt : IntegrableOn (fun x => |u x| ^ p) Ω volume) :
    MemLp (fun x => |u x| ^ (p / 2)) 2 (volume.restrict Ω) := by
  have hpow_cont : Continuous fun t : ℝ => t ^ (p / 2) := by
    exact Real.continuous_rpow_const (by linarith)
  have hmeas :
      AEStronglyMeasurable (fun x => |u x| ^ (p / 2)) (volume.restrict Ω) := by
    exact
      (hpow_cont.measurable.comp_aemeasurable
        (measurable_abs.comp_aemeasurable hu.memLp.aestronglyMeasurable.aemeasurable)).aestronglyMeasurable
  refine (MeasureTheory.memLp_two_iff_integrable_sq hmeas).2 ?_
  simpa [IntegrableOn] using hpInt.congr (by
    filter_upwards with x
    calc
      |u x| ^ p = (|u x| ^ (p / 2)) ^ 2 := by
        rw [← Real.rpow_natCast (|u x| ^ (p / 2)) 2]
        rw [← Real.rpow_mul]
        · congr 1
          ring
        · positivity
      _ = (|u x| ^ (p / 2)) ^ 2 := by rfl
    )

omit [NeZero d] in
theorem one_add_power_half_memLp_on_ball
    {u : E → ℝ} {p s : ℝ}
    (hp : 0 ≤ p) (_hs : 0 < s)
    (hu : MemW1pWitness 2 u (Metric.ball (0 : E) s))
    (hpInt : IntegrableOn (fun x => |u x| ^ p) (Metric.ball (0 : E) s) volume) :
    MemLp (fun x => 1 + |u x| ^ (p / 2)) 2 (volume.restrict (Metric.ball (0 : E) s)) := by
  let μ : Measure E := volume.restrict (Metric.ball (0 : E) s)
  haveI : IsFiniteMeasure μ := by
    dsimp [μ]
    rw [isFiniteMeasure_restrict]
    exact (measure_ball_lt_top (μ := volume) (x := (0 : E)) (r := s)).ne
  have hone : MemLp (fun _ : E => (1 : ℝ)) 2 μ := by
    simpa [μ] using (memLp_const (1 : ℝ) : MemLp (fun _ : E => (1 : ℝ)) 2 μ)
  have hhalf :
      MemLp (fun x => |u x| ^ (p / 2)) 2 μ := by
    simpa [μ] using power_half_memLp_of_integrableOn (Ω := Metric.ball (0 : E) s)
      (u := u) (p := p) hp hu hpInt
  simpa [μ] using hone.add hhalf

omit [NeZero d] in
theorem one_add_rpow_integrableOn_ball
    {u : E → ℝ} {p s : ℝ}
    (_hs : 0 < s)
    (hpInt : IntegrableOn (fun x => |u x| ^ p) (Metric.ball (0 : E) s) volume) :
    IntegrableOn (fun x => 1 + |u x| ^ p) (Metric.ball (0 : E) s) volume := by
  have hone :
      IntegrableOn (fun _ : E => (1 : ℝ)) (Metric.ball (0 : E) s) volume := by
    exact integrableOn_const (C := (1 : ℝ))
      (hC := by simp) (s := Metric.ball (0 : E) s)
      (hs := (measure_ball_lt_top (μ := volume) (x := (0 : E)) (r := s)).ne)
  exact hone.add hpInt

omit [NeZero d] in
theorem superExactFwd_rhs_dom_on_ball
    {u : E → ℝ} {p s : ℝ}
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (_hs : 0 < s)
    (hu_pos : ∀ x ∈ Metric.ball (0 : E) s, 0 < u x) :
    ∀ n, ∀ᵐ x ∂(volume.restrict (Metric.ball (0 : E) s)),
      |superExactShiftPow (superEpsSeq n) p (u x)| ≤ 1 + |u x| ^ p := by
  intro n
  filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx
  have hux : 0 < u x := hu_pos x hx
  have hpow_nonneg :
      0 ≤ superExactShiftPow (superEpsSeq n) p (u x) :=
    superExactShiftPow_nonneg (ε := superEpsSeq n) (a := p) (superEpsSeq_pos n)
  rw [abs_of_nonneg hpow_nonneg]
  exact superExactShiftPow_le_one_add_rpow_of_pos
    (ε := superEpsSeq n) (a := p) (t := u x)
    (superEpsSeq_pos n) (superEpsSeq_le_one n) hp hp1 hux


end DeGiorgi
