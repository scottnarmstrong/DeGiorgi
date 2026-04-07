import DeGiorgi.WeakFormulation.CoefficientOperator
import Mathlib.Analysis.InnerProductSpace.LaxMilgram
import Mathlib.Analysis.Normed.Operator.Extend

/-!
# Weak Formulation: Existence Theory

This module develops the Lax-Milgram existence argument, stability and
uniqueness, and the Dirichlet and `A`-harmonic replacement consequences built
from the coefficient-operator layer.
-/

noncomputable section

open MeasureTheory Filter
open scoped InnerProductSpace

namespace DeGiorgi

variable {d : ℕ} [NeZero d]

local notation "E" => AmbientSpace d

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000

/-! ## Weak Problem Existence (Lax-Milgram) -/

/-- Existence of weak solutions via Lax-Milgram.
The bilinear form `bilinFormOfCoeff` is bounded and coercive on `H₀¹(Ω)`
(proved above), and the RHS is a bounded linear functional, so Lax-Milgram
gives existence and uniqueness. -/
theorem weakProblem_exists
    {Ω : Set E}
    (hd : 2 ≤ d)
    (hΩ : IsOpen Ω) (hΩ_bdd : Bornology.IsBounded Ω)
    (A : EllipticCoeff d Ω)
    (rhs : (E → ℝ) → ℝ)
    (hF_add : ∀ u v : E → ℝ, MemH01 u Ω → MemH01 v Ω →
      rhs (fun x => u x + v x) = rhs u + rhs v)
    (hF_smul : ∀ c : ℝ, ∀ u : E → ℝ, MemH01 u Ω →
      rhs (fun x => c * u x) = c * rhs u)
    (hF_bounded : ∃ C, 0 ≤ C ∧ ∀ v : E → ℝ, MemH01 v Ω →
      ∀ hwv : MemW1pWitness 2 v Ω,
      |rhs v| ≤ C *
        (∫ x, ‖hwv.weakGrad x‖ ^ (2 : ℝ) ∂(volume.restrict Ω)) ^ (1 / (2 : ℝ))) :
    ∃ u : E → ℝ, IsWeakSolution (d := d) ⟨Ω, hΩ, hΩ_bdd, A, rhs⟩ u := by
  classical
  let μ : Measure E := volume.restrict Ω
  let S : Submodule ℝ (MeasureTheory.Lp E 2 μ) := smoothGradSubmodule hΩ
  let H : Submodule ℝ (MeasureTheory.Lp E 2 μ) := S.topologicalClosure
  let e : S →ₗ[ℝ] H := Submodule.inclusion S.le_topologicalClosure
  obtain ⟨Cp, hCp_top, hPoinc⟩ := smoothCompactSupport_L2_bound_on_bounded_ge_two hd hΩ_bdd
  obtain ⟨C_rhs, hC_rhs_nonneg, hF_bound⟩ := hF_bounded
  let repFun : S → E → ℝ := fun g => Classical.choose g.2
  let repSmooth : ∀ g : S, IsSmoothTestOn Ω (repFun g) := by
    intro g
    exact Classical.choose (Classical.choose_spec g.2)
  have repEq : ∀ g : S, smoothGradToLp hΩ (repSmooth g) = (g : MeasureTheory.Lp E 2 μ) := by
    intro g
    exact Classical.choose_spec (Classical.choose_spec g.2)
  have smoothFunToLp_bound :
      ∀ {u : E → ℝ} (hu : IsSmoothTestOn Ω u),
        ‖smoothFunToLp hΩ hu‖ ≤ Cp.toReal * ‖smoothGradToLp hΩ hu‖ := by
    intro u hu
    have hgradNorm_memLp : MemLp (smoothGradNorm u) 2 μ := by
      simpa [μ, norm_smoothGradField_eq_smoothGradNorm] using
        (smoothTestWitness hΩ hu).weakGrad_memLp.norm
    have hP :
        eLpNorm u 2 μ ≤ Cp * eLpNorm (smoothGradNorm u) 2 μ := by
      simpa [μ] using hPoinc hu.1 hu.2.1 hu.2.2
    have hleft_top : eLpNorm u 2 μ ≠ ⊤ :=
      (smoothTestWitness hΩ hu).memLp.eLpNorm_lt_top.ne
    have hright_top : Cp * eLpNorm (smoothGradNorm u) 2 μ ≠ ⊤ := by
      exact (ENNReal.mul_lt_top hCp_top hgradNorm_memLp.eLpNorm_lt_top).ne
    have hToReal :
        (eLpNorm u 2 μ).toReal ≤ (Cp * eLpNorm (smoothGradNorm u) 2 μ).toReal :=
      (ENNReal.toReal_le_toReal hleft_top hright_top).2 hP
    have hfunEq : ‖smoothFunToLp hΩ hu‖ = (eLpNorm u 2 μ).toReal := by
      rw [smoothFunToLp, Lp.norm_toLp]
    have hgradEq : ‖smoothGradToLp hΩ hu‖ = (eLpNorm (smoothGradNorm u) 2 μ).toReal := by
      have hgrad_memLp : MemLp (smoothGradField u) 2 μ :=
        (smoothTestWitness hΩ hu).weakGrad_memLp
      calc
        ‖smoothGradToLp hΩ hu‖ =
            (∫ x, ‖smoothGradField u x‖ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) := by
              simpa [μ] using (norm_smoothGradToLp_eq hΩ hu)
        _ = (eLpNorm (smoothGradField u) 2 μ).toReal := by
              symm
              rw [MeasureTheory.toReal_eLpNorm hgrad_memLp.aestronglyMeasurable]
              simpa using
                (MeasureTheory.lpNorm_eq_integral_norm_rpow_toReal
                  (μ := μ) (f := smoothGradField u) (p := (2 : ENNReal))
                  (by norm_num) (by simp) hgrad_memLp.aestronglyMeasurable)
        _ = (eLpNorm (smoothGradNorm u) 2 μ).toReal := by
          congr 1
          calc
            eLpNorm (smoothGradField u) 2 μ = eLpNorm (fun x => ‖smoothGradField u x‖) 2 μ := by
              symm
              exact eLpNorm_norm (μ := μ) (p := (2 : ENNReal)) (smoothGradField u)
            _ = eLpNorm (smoothGradNorm u) 2 μ := by
                  simp [norm_smoothGradField_eq_smoothGradNorm]
    rw [hfunEq, hgradEq]
    convert hToReal using 1
    rw [ENNReal.toReal_mul]
  have smoothFunToLp_eq_of_sameGrad :
      ∀ {u v : E → ℝ} (hu : IsSmoothTestOn Ω u) (hv : IsSmoothTestOn Ω v),
        smoothGradToLp hΩ hu = smoothGradToLp hΩ hv →
          smoothFunToLp hΩ hu = smoothFunToLp hΩ hv := by
    intro u v hu hv hgradEq
    have huv : IsSmoothTestOn Ω (fun x => u x - v x) := hu.sub hv
    have hgradZero : smoothGradToLp hΩ huv = 0 := by
      calc
        smoothGradToLp hΩ huv = smoothGradToLp hΩ hu - smoothGradToLp hΩ hv := by
          simpa using smoothGradToLp_sub hΩ hu hv
        _ = 0 := by rw [hgradEq, sub_self]
    have hfunZeroNorm : ‖smoothFunToLp hΩ huv‖ = 0 := by
      have hbound := smoothFunToLp_bound huv
      have hupper : ‖smoothFunToLp hΩ huv‖ ≤ 0 := by
        simpa [hgradZero] using hbound
      exact le_antisymm hupper (norm_nonneg _)
    have hfunZero : smoothFunToLp hΩ huv = 0 := norm_eq_zero.mp hfunZeroNorm
    have hsub :
        smoothFunToLp hΩ huv = smoothFunToLp hΩ hu - smoothFunToLp hΩ hv := by
      simpa using smoothFunToLp_sub hΩ hu hv
    rw [hsub] at hfunZero
    exact sub_eq_zero.mp hfunZero
  have rhs_eq_of_sameGrad :
      ∀ {u v : E → ℝ} (hu : IsSmoothTestOn Ω u) (hv : IsSmoothTestOn Ω v),
        smoothGradToLp hΩ hu = smoothGradToLp hΩ hv →
          rhs u = rhs v := by
    intro u v hu hv hgradEq
    have hu0 : MemH01 u Ω := smoothTest_memH01 hΩ hu
    have hv0 : MemH01 v Ω := smoothTest_memH01 hΩ hv
    have huv : IsSmoothTestOn Ω (fun x => u x - v x) := hu.sub hv
    have huv0 : MemH01 (fun x => u x - v x) Ω := smoothTest_memH01 hΩ huv
    let hwuv : MemW1pWitness 2 (fun x => u x - v x) Ω := smoothTestWitness hΩ huv
    have hgradZero : smoothGradToLp hΩ huv = 0 := by
      calc
        smoothGradToLp hΩ huv = smoothGradToLp hΩ hu - smoothGradToLp hΩ hv := by
          simpa using smoothGradToLp_sub hΩ hu hv
        _ = 0 := by rw [hgradEq, sub_self]
    have hseminormZero :
        (∫ x, ‖hwuv.weakGrad x‖ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) = 0 := by
      have hgradZero' : gradLpOfWitness hwuv = 0 := by
        simpa [hwuv, smoothGradToLp] using hgradZero
      have hnormZero : ‖gradLpOfWitness hwuv‖ = 0 := by
        rw [hgradZero']
        simp
      have hseminormEq := norm_gradLpOfWitness_eq hwuv
      rw [hnormZero] at hseminormEq
      simpa [μ] using hseminormEq.symm
    have hbound := hF_bound (fun x => u x - v x) huv0 hwuv
    have hrhsZero : rhs (fun x => u x - v x) = 0 := by
      have habsZero : |rhs (fun x => u x - v x)| = 0 := by
        have hupper : |rhs (fun x => u x - v x)| ≤ 0 := by
          calc
            |rhs (fun x => u x - v x)| ≤
                C_rhs * (∫ x, ‖hwuv.weakGrad x‖ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) := hbound
            _ = 0 := by rw [hseminormZero]; ring
        exact le_antisymm hupper (abs_nonneg _)
      exact abs_eq_zero.mp habsZero
    have hvNeg0 : MemH01 (fun x => (-1) * v x) Ω := by
      simpa [Pi.smul_apply, smul_eq_mul] using (MemW01p.smul (-1) hv0)
    have hsubEq : rhs (fun x => u x - v x) = rhs u - rhs v := by
      calc
        rhs (fun x => u x - v x) = rhs (fun x => u x + (-1) * v x) := by
          congr
          ext x
          ring
        _ = rhs u + rhs (fun x => (-1) * v x) := hF_add u (fun x => (-1) * v x) hu0 hvNeg0
        _ = rhs u + (-1) * rhs v := by rw [hF_smul (-1) v hv0]
        _ = rhs u - rhs v := by ring
    rw [hsubEq] at hrhsZero
    linarith
  let L0 : S →ₗ[ℝ] ℝ := {
    toFun := fun g => rhs (repFun g)
    map_add' := by
      intro g h
      have hEq :
          rhs (repFun (g + h)) = rhs (fun x => repFun g x + repFun h x) := by
        apply rhs_eq_of_sameGrad (repSmooth (g + h)) ((repSmooth g).add (repSmooth h))
        calc
          smoothGradToLp hΩ (repSmooth (g + h)) = (g + h : S) := repEq (g + h)
          _ = (g : MeasureTheory.Lp E 2 μ) + (h : MeasureTheory.Lp E 2 μ) := by rfl
          _ = smoothGradToLp hΩ (repSmooth g) + smoothGradToLp hΩ (repSmooth h) := by
                rw [repEq g, repEq h]
          _ = smoothGradToLp hΩ ((repSmooth g).add (repSmooth h)) := by
                symm
                exact smoothGradToLp_add hΩ (repSmooth g) (repSmooth h)
      rw [hEq, hF_add (repFun g) (repFun h)
        (smoothTest_memH01 hΩ (repSmooth g))
        (smoothTest_memH01 hΩ (repSmooth h))]
    map_smul' := by
      intro c g
      have hEq :
          rhs (repFun (c • g)) = rhs (fun x => c * repFun g x) := by
        apply rhs_eq_of_sameGrad (repSmooth (c • g)) ((repSmooth g).smul c)
        calc
          smoothGradToLp hΩ (repSmooth (c • g)) = (c • g : S) := repEq (c • g)
          _ = c • (g : MeasureTheory.Lp E 2 μ) := by rfl
          _ = c • smoothGradToLp hΩ (repSmooth g) := by rw [repEq g]
          _ = smoothGradToLp hΩ ((repSmooth g).smul c) := by
                symm
                exact smoothGradToLp_smul hΩ c (repSmooth g)
      calc
        rhs (repFun (c • g)) = rhs (fun x => c * repFun g x) := hEq
        _ = c * rhs (repFun g) := hF_smul c (repFun g) (smoothTest_memH01 hΩ (repSmooth g))
        _ = (RingHom.id ℝ) c • rhs (repFun g) := by simp [smul_eq_mul] }
  have hL0_bound : ∃ C, ∀ g : S, ‖L0 g‖ ≤ C * ‖e g‖ := by
    refine ⟨C_rhs, ?_⟩
    intro g
    let hwg : MemW1pWitness 2 (repFun g) Ω := smoothTestWitness hΩ (repSmooth g)
    calc
      ‖L0 g‖ = |rhs (repFun g)| := by rfl
      _ ≤ C_rhs * (∫ x, ‖hwg.weakGrad x‖ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) := by
            exact hF_bound (repFun g) (smoothTest_memH01 hΩ (repSmooth g)) hwg
      _ = C_rhs * ‖gradLpOfWitness hwg‖ := by rw [norm_gradLpOfWitness_eq hwg]
      _ = C_rhs * ‖smoothGradToLp hΩ (repSmooth g)‖ := by rfl
      _ = C_rhs * ‖(g : MeasureTheory.Lp E 2 μ)‖ := by rw [repEq g]
      _ = C_rhs * ‖g‖ := by rfl
      _ = C_rhs * ‖e g‖ := by simp [e]
  have hDense : DenseRange e := by
    have hDenseInclusion :
        DenseRange
          (Set.inclusion
            (Submodule.le_topologicalClosure S :
              (S : Set (MeasureTheory.Lp E 2 μ)) ⊆ (H : Set (MeasureTheory.Lp E 2 μ)))) := by
      rw [denseRange_inclusion_iff]
      change (H : Set (MeasureTheory.Lp E 2 μ)) ⊆ closure (S : Set (MeasureTheory.Lp E 2 μ))
      intro x hx
      simpa [H, Submodule.topologicalClosure_coe] using hx
    simpa [e] using hDenseInclusion
  let U0 : S →ₗ[ℝ] MeasureTheory.Lp ℝ 2 μ := {
    toFun := fun g => smoothFunToLp hΩ (repSmooth g)
    map_add' := by
      intro g h
      have hEq :
          smoothFunToLp hΩ (repSmooth (g + h)) =
            smoothFunToLp hΩ ((repSmooth g).add (repSmooth h)) := by
        apply smoothFunToLp_eq_of_sameGrad (repSmooth (g + h)) ((repSmooth g).add (repSmooth h))
        calc
          smoothGradToLp hΩ (repSmooth (g + h)) = (g + h : S) := repEq (g + h)
          _ = (g : MeasureTheory.Lp E 2 μ) + (h : MeasureTheory.Lp E 2 μ) := by rfl
          _ = smoothGradToLp hΩ (repSmooth g) + smoothGradToLp hΩ (repSmooth h) := by
                rw [repEq g, repEq h]
          _ = smoothGradToLp hΩ ((repSmooth g).add (repSmooth h)) := by
                symm
                exact smoothGradToLp_add hΩ (repSmooth g) (repSmooth h)
      rw [hEq, smoothFunToLp_add hΩ (repSmooth g) (repSmooth h)]
    map_smul' := by
      intro c g
      have hEq :
          smoothFunToLp hΩ (repSmooth (c • g)) =
            smoothFunToLp hΩ ((repSmooth g).smul c) := by
        apply smoothFunToLp_eq_of_sameGrad (repSmooth (c • g)) ((repSmooth g).smul c)
        calc
          smoothGradToLp hΩ (repSmooth (c • g)) = (c • g : S) := repEq (c • g)
          _ = c • (g : MeasureTheory.Lp E 2 μ) := by rfl
          _ = c • smoothGradToLp hΩ (repSmooth g) := by rw [repEq g]
          _ = smoothGradToLp hΩ ((repSmooth g).smul c) := by
                symm
                exact smoothGradToLp_smul hΩ c (repSmooth g)
      calc
        smoothFunToLp hΩ (repSmooth (c • g)) =
            smoothFunToLp hΩ ((repSmooth g).smul c) := hEq
        _ = c • smoothFunToLp hΩ (repSmooth g) := smoothFunToLp_smul hΩ c (repSmooth g)
        _ = (RingHom.id ℝ) c • smoothFunToLp hΩ (repSmooth g) := by simp }
  have hU0_bound : ∃ C, ∀ g : S, ‖U0 g‖ ≤ C * ‖e g‖ := by
    refine ⟨Cp.toReal, ?_⟩
    intro g
    calc
      ‖U0 g‖ = ‖smoothFunToLp hΩ (repSmooth g)‖ := by rfl
      _ ≤ Cp.toReal * ‖smoothGradToLp hΩ (repSmooth g)‖ := by
            exact smoothFunToLp_bound (repSmooth g)
      _ = Cp.toReal * ‖(g : MeasureTheory.Lp E 2 μ)‖ := by rw [repEq g]
      _ = Cp.toReal * ‖g‖ := by rfl
      _ = Cp.toReal * ‖e g‖ := by simp [e]
  let L : H →L[ℝ] ℝ := L0.extendOfNorm e
  let U : H →L[ℝ] MeasureTheory.Lp ℝ 2 μ := U0.extendOfNorm e
  have hL_eq : ∀ g : S, L (e g) = L0 g := by
    intro g
    exact LinearMap.extendOfNorm_eq hDense hL0_bound g
  have hU_eq : ∀ g : S, U (e g) = U0 g := by
    intro g
    exact LinearMap.extendOfNorm_eq hDense hU0_bound g
  have hcoercive : IsCoercive (coeffBilinSubmodule A H) := coeffBilinSubmodule_coercive A H
  have hComplete : CompleteSpace H := by
    simpa [H] using (Submodule.topologicalClosure.completeSpace (U := S))
  let fvec : H := by
    exact (@InnerProductSpace.toDual ℝ H _ _ _ hComplete).symm L
  let gsol : H := by
    exact (@IsCoercive.continuousLinearEquivOfBilin H _ _ hComplete _ hcoercive).symm fvec
  let Gsol : MeasureTheory.Lp E 2 μ := gsol
  have hLM :
      ∀ w : H, coeffBilinSubmodule A H gsol w = L w := by
    intro w
    calc
      coeffBilinSubmodule A H gsol w =
          ⟪(@IsCoercive.continuousLinearEquivOfBilin H _ _ hComplete _ hcoercive) gsol, w⟫_ℝ := by
            symm
            exact @IsCoercive.continuousLinearEquivOfBilin_apply H _ _ hComplete
              _ hcoercive gsol w
      _ = ⟪fvec, w⟫_ℝ := by simp [gsol]
      _ = L w := by
            change ⟪(@InnerProductSpace.toDual ℝ H _ _ _ hComplete).symm L, w⟫_ℝ = L w
            exact @InnerProductSpace.toDual_symm_apply ℝ H _ _ _ hComplete (x := w) (y := L)
  have hgsol_mem :
      (gsol : MeasureTheory.Lp E 2 μ) ∈ closure (S : Set (MeasureTheory.Lp E 2 μ)) := by
    change (gsol : MeasureTheory.Lp E 2 μ) ∈ (H : Set (MeasureTheory.Lp E 2 μ))
    exact gsol.2
  rw [mem_closure_iff_seq_limit] at hgsol_mem
  rcases hgsol_mem with ⟨Gseq, hGseq_mem, hGseq_tendsto⟩
  let ψ : ℕ → E → ℝ := fun n => repFun ⟨Gseq n, hGseq_mem n⟩
  let hψ : ∀ n : ℕ, IsSmoothTestOn Ω (ψ n) := fun n => repSmooth ⟨Gseq n, hGseq_mem n⟩
  have hψ_eq : ∀ n : ℕ, smoothGradToLp hΩ (hψ n) = Gseq n := by
    intro n
    exact repEq ⟨Gseq n, hGseq_mem n⟩
  let Gbar : ℕ → H := fun n => e ⟨Gseq n, hGseq_mem n⟩
  have hGbar_tendsto : Tendsto Gbar atTop (nhds gsol) := by
    rw [tendsto_subtype_rng]
    simpa [Gbar, e] using hGseq_tendsto
  let uLp : MeasureTheory.Lp ℝ 2 μ := U gsol
  let u : E → ℝ := uLp
  have hu_memLp : MemLp u 2 μ := Lp.memLp uLp
  have hu_toLp : hu_memLp.toLp u = uLp := by
    change hu_memLp.toLp (uLp : E → ℝ) = uLp
    exact Lp.toLp_coeFn uLp hu_memLp
  have hU_tendsto : Tendsto (fun n => U (Gbar n)) atTop (nhds uLp) := by
    simpa [uLp] using ((U.continuous.continuousAt).tendsto.comp hGbar_tendsto)
  have hψLp_tendsto : Tendsto (fun n => smoothFunToLp hΩ (hψ n)) atTop (nhds uLp) := by
    refine Tendsto.congr' (Filter.Eventually.of_forall ?_) hU_tendsto
    intro n
    exact hU_eq ⟨Gseq n, hGseq_mem n⟩
  letI : Fact (1 ≤ (2 : ENNReal)) := ⟨by norm_num⟩
  have hψ_fun_tendsto :
      Tendsto (fun n => eLpNorm (fun x => ψ n x - u x) 2 μ) atTop (nhds 0) := by
    have hψLp_tendsto' :
        Tendsto
          (fun n => ((smoothTestWitness hΩ (hψ n)).memLp).toLp (ψ n))
          atTop (nhds (hu_memLp.toLp u)) := by
      simpa [smoothFunToLp, hu_toLp] using hψLp_tendsto
    exact
      (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' (f := ψ)
        (f_ℒp := fun n => (smoothTestWitness hΩ (hψ n)).memLp)
        (f_lim := u) (f_lim_ℒp := hu_memLp)).1 hψLp_tendsto'
  have hgradLp_tendsto :
      Tendsto (fun n => smoothGradToLp hΩ (hψ n))
        atTop (nhds Gsol) := by
    refine Tendsto.congr' (Filter.Eventually.of_forall fun n => (hψ_eq n).symm) ?_
    simpa [Gsol] using hGseq_tendsto
  have hgrad_vec_tendsto :
      Tendsto
        (fun n => eLpNorm (fun x => (smoothTestWitness hΩ (hψ n)).weakGrad x - Gsol x) 2 μ)
        atTop (nhds 0) := by
    have hgradLp_tendsto' :
        Tendsto
          (fun n => ((smoothTestWitness hΩ (hψ n)).weakGrad_memLp).toLp
            ((smoothTestWitness hΩ (hψ n)).weakGrad))
          atTop (nhds ((Lp.memLp Gsol).toLp Gsol)) := by
      simpa [smoothGradToLp, gradLpOfWitness] using hgradLp_tendsto
    exact
      (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' (f := fun n => (smoothTestWitness hΩ (hψ n)).weakGrad)
        (f_ℒp := fun n => (smoothTestWitness hΩ (hψ n)).weakGrad_memLp)
        (f_lim := Gsol) (f_lim_ℒp := Lp.memLp Gsol)).1
        hgradLp_tendsto'
  have hgsol_comp_memLp : ∀ i : Fin d, MemLp (fun x => Gsol x i) 2 μ := by
    intro i
    exact (Lp.memLp Gsol).eval_piLp i
  have hψ_grad_comp_memLp :
      ∀ n : ℕ, ∀ i : Fin d,
        MemLp
          (fun x => ((smoothTestWitness hΩ (hψ n)).weakGrad x).ofLp i - Gsol x i)
          2 μ := by
    intro n i
    simpa [PiLp.toLp_apply] using
      ((smoothTestWitness hΩ (hψ n)).weakGrad_component_memLp i).sub (hgsol_comp_memLp i)
  have hgrad_comp_tendsto :
      ∀ i : Fin d,
        Tendsto
          (fun n =>
            eLpNorm
              (fun x => ((smoothTestWitness hΩ (hψ n)).weakGrad x).ofLp i - Gsol x i)
              2 μ)
          atTop (nhds 0) := by
    intro i
    have hupper :
        ∀ n,
          eLpNorm
              (fun x => ((smoothTestWitness hΩ (hψ n)).weakGrad x).ofLp i - Gsol x i)
              2 μ ≤
            eLpNorm (fun x => (smoothTestWitness hΩ (hψ n)).weakGrad x - Gsol x) 2 μ := by
      intro n
      exact eLpNorm_mono_ae <|
        Filter.Eventually.of_forall fun x => by
          simpa [PiLp.toLp_apply] using
            (PiLp.norm_apply_le ((smoothTestWitness hΩ (hψ n)).weakGrad x - Gsol x) i)
    exact
      tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hgrad_vec_tendsto
        (fun n => zero_le _) hupper
  have hu_memLp' : MemLp u (ENNReal.ofReal 2) (volume.restrict Ω) := by
    simpa using hu_memLp
  have hgsol_comp_memLp' :
      ∀ i : Fin d, MemLp (fun x => Gsol x i) (ENNReal.ofReal 2) (volume.restrict Ω) := by
    intro i
    simpa using hgsol_comp_memLp i
  have hψ_fun_memLp' :
      ∀ n, MemLp (fun x => ψ n x - u x) (ENNReal.ofReal 2) (volume.restrict Ω) := by
    intro n
    simpa using ((smoothTestWitness hΩ (hψ n)).memLp).sub hu_memLp
  have hψ_fun_tendsto' :
      Tendsto (fun n => eLpNorm (fun x => ψ n x - u x) (ENNReal.ofReal 2) (volume.restrict Ω))
        atTop (nhds 0) := by
    simpa using hψ_fun_tendsto
  have hψ_grad_comp_memLp' :
      ∀ n : ℕ, ∀ i : Fin d,
        MemLp
          (fun x => ((smoothTestWitness hΩ (hψ n)).weakGrad x).ofLp i - Gsol x i)
          (ENNReal.ofReal 2) (volume.restrict Ω) := by
    intro n i
    simpa using hψ_grad_comp_memLp n i
  have hgrad_comp_tendsto' :
      ∀ i : Fin d,
        Tendsto
          (fun n =>
            eLpNorm
              (fun x => ((smoothTestWitness hΩ (hψ n)).weakGrad x).ofLp i - Gsol x i)
              (ENNReal.ofReal 2) (volume.restrict Ω))
          atTop (nhds 0) := by
    intro i
    simpa using hgrad_comp_tendsto i
  have hu_isWeakGrad : ∀ i : Fin d, HasWeakPartialDeriv i (fun x => Gsol x i) u Ω := by
    intro i
    exact HasWeakPartialDeriv.of_eLpNormApprox_p hΩ (p := 2) (by norm_num)
      hu_memLp' (hgsol_comp_memLp' i)
      (fun n => (smoothTestWitness hΩ (hψ n)).isWeakGrad i)
      hψ_fun_memLp'
      hψ_fun_tendsto'
      (fun n => hψ_grad_comp_memLp' n i)
      (hgrad_comp_tendsto' i)
  let hwu : MemW1pWitness 2 u Ω := {
    memLp := hu_memLp
    weakGrad := fun x => WithLp.toLp 2 fun i => Gsol x i
    weakGrad_component_memLp := hgsol_comp_memLp
    isWeakGrad := hu_isWeakGrad }
  have hwu_gradEq : gradLpOfWitness hwu = Gsol := by
    have hgrad_ae :
        hwu.weakGrad =ᵐ[μ] fun x => Gsol x := by
      filter_upwards with x
      change WithLp.toLp 2 (WithLp.ofLp (Gsol x)) = Gsol x
      exact WithLp.toLp_ofLp (p := 2) (x := Gsol x)
    calc
      gradLpOfWitness hwu =
          (Lp.memLp Gsol).toLp (fun x => Gsol x) := by
            simpa [gradLpOfWitness] using
              (MemLp.toLp_congr hwu.weakGrad_memLp (Lp.memLp Gsol)
                hgrad_ae)
      _ = Gsol := by
            exact Lp.toLp_coeFn _ _
  have hu0 : MemH01 u Ω := by
    refine ⟨hwu.memW1p, ⟨hwu, ψ, ?_, ?_, ?_, ?_, ?_⟩⟩
    · intro n
      exact (hψ n).1
    · intro n
      exact (hψ n).2.1
    · intro n
      exact (hψ n).2.2
    · simpa [μ] using hψ_fun_tendsto
    · intro i
      simpa [μ] using hgrad_comp_tendsto i
  have hsmooth_eq :
      ∀ {φ : E → ℝ} (hφ : IsSmoothTestOn Ω φ),
        bilinFormOfCoeff A hwu (smoothTestWitness hΩ hφ) = rhs φ := by
    intro φ hφ
    let gφS : S := ⟨smoothGradToLp hΩ hφ, ⟨φ, hφ, rfl⟩⟩
    let gφH : H := e gφS
    have hφ_gradEq :
        H.subtypeL gφH = gradLpOfWitness (smoothTestWitness hΩ hφ) := by
      simp [gφH, gφS, e, smoothGradToLp]
    calc
      bilinFormOfCoeff A hwu (smoothTestWitness hΩ hφ)
          = coeffBilinSubmodule A H gsol gφH := by
              calc
                bilinFormOfCoeff A hwu (smoothTestWitness hΩ hφ) =
                    ⟪coeffMulLpL A (gradLpOfWitness hwu),
                      gradLpOfWitness (smoothTestWitness hΩ hφ)⟫_ℝ := by
                        symm
                        exact coeffMulLpL_inner_gradLpOfWitness_eq_bilinFormOfCoeff A hwu
                          (smoothTestWitness hΩ hφ)
                _ = ⟪coeffMulLpL A Gsol, H.subtypeL gφH⟫_ℝ := by
                      rw [hwu_gradEq, hφ_gradEq]
                _ = ⟪coeffMulLpL A (H.subtypeL gsol), H.subtypeL gφH⟫_ℝ := by
                      rfl
                _ = coeffBilinSubmodule A H gsol gφH := by rfl
      _ = L gφH := hLM gφH
      _ = L0 gφS := by simpa [gφH] using hL_eq gφS
      _ = rhs φ := by
            apply rhs_eq_of_sameGrad (repSmooth gφS) hφ
            calc
              smoothGradToLp hΩ (repSmooth gφS) = (gφS : MeasureTheory.Lp E 2 μ) := repEq gφS
              _ = smoothGradToLp hΩ hφ := by rfl
  refine ⟨u, hu0, ?_⟩
  intro hwu' v hv0 hv
  have hv0_all := hv0
  rcases hv0 with ⟨_hv_mem, hvw, φ, hφ_smooth, hφ_cpt, hφ_sub, hφ_fun, hφ_grad⟩
  let hφtest : ∀ n : ℕ, IsSmoothTestOn Ω (φ n) := fun n =>
    ⟨hφ_smooth n, hφ_cpt n, hφ_sub n⟩
  let hφw : ∀ n : ℕ, MemW1pWitness 2 (φ n) Ω := fun n => smoothTestWitness hΩ (hφtest n)
  let haddiff : ∀ n : ℕ, MemW1pWitness 2 (fun x => φ n x + (-1) * v x) Ω := fun n =>
    (hφw n).add (hvw.smul (-1))
  let hdiff : ∀ n : ℕ, MemW1pWitness 2 (fun x => φ n x - v x) Ω := fun n => {
    memLp := by
      simpa [sub_eq_add_neg, Pi.smul_apply] using (haddiff n).memLp
    weakGrad := (haddiff n).weakGrad
    weakGrad_component_memLp := by
      intro i
      simpa [sub_eq_add_neg, Pi.smul_apply] using (haddiff n).weakGrad_component_memLp i
    isWeakGrad := by
      intro i
      simpa [sub_eq_add_neg, Pi.smul_apply] using (haddiff n).isWeakGrad i }
  have hgradDiffVec_tendsto :
      Tendsto (fun n => eLpNorm (fun x => smoothGradField (φ n) x - hvw.weakGrad x) 2 μ)
        atTop (nhds 0) := by
    exact tendsto_eLpNorm_vector_of_componentwise
      (fun n i => by
        simpa [smoothTestWitness, smoothGradField, PiLp.toLp_apply] using
          ((hφw n).weakGrad_component_memLp i).sub (hvw.weakGrad_component_memLp i))
      (fun i => by
        simpa [μ] using hφ_grad i)
  have hdiff_grad_tendsto :
      Tendsto (fun n => gradLpOfWitness (hdiff n)) atTop (nhds 0) := by
    let h0_mem : MemLp (fun _ : E => (0 : E)) 2 μ := MeasureTheory.MemLp.zero'
    have hgradDiffVec_tendsto_add :
        Tendsto (fun n => eLpNorm (fun x => (haddiff n).weakGrad x) 2 μ)
          atTop (nhds 0) := by
      refine Tendsto.congr' (Filter.Eventually.of_forall ?_) hgradDiffVec_tendsto
      intro n
      have hweak_eq :
          (fun x => (haddiff n).weakGrad x) =
            fun x => smoothGradField (φ n) x - hvw.weakGrad x := by
        funext x
        simp [haddiff, hφw, smoothTestWitness, smoothGradField, MemW1pWitness.add,
          MemW1pWitness.smul, sub_eq_add_neg]
      simp [hweak_eq]
    have hgradDiffVec_tendsto_add' :
        Tendsto (fun n => eLpNorm (fun x => (haddiff n).weakGrad x - (0 : E)) 2 μ)
          atTop (nhds 0) := by
      simpa [sub_eq_add_neg] using hgradDiffVec_tendsto_add
    have hLp_tendsto_add :
        Tendsto
          (fun n => ((haddiff n).weakGrad_memLp).toLp ((haddiff n).weakGrad))
          atTop (nhds (h0_mem.toLp (fun _ : E => (0 : E)))) := by
      exact
        (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' (f := fun n => (haddiff n).weakGrad)
          (f_ℒp := fun n => (haddiff n).weakGrad_memLp)
          (f_lim := fun _ : E => (0 : E)) (f_lim_ℒp := h0_mem)).2 <| by
            exact hgradDiffVec_tendsto_add'
    simpa [hdiff, gradLpOfWitness] using hLp_tendsto_add
  have hdiff_seminorm_tendsto :
      Tendsto
        (fun n => (∫ x, ‖(hdiff n).weakGrad x‖ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)))
        atTop (nhds 0) := by
    have hnorm_tendsto :
        Tendsto (fun n => ‖gradLpOfWitness (hdiff n)‖) atTop (nhds 0) := by
      simpa using ((continuous_norm.tendsto (0 : MeasureTheory.Lp E 2 μ)).comp hdiff_grad_tendsto)
    refine Tendsto.congr' (Filter.Eventually.of_forall ?_) hnorm_tendsto
    intro n
    exact norm_gradLpOfWitness_eq (hdiff n)
  let seminormDiff : ℕ → ℝ := fun n =>
    (∫ x, ‖(hdiff n).weakGrad x‖ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ))
  have hseminormDiff_nonneg : ∀ n, 0 ≤ seminormDiff n := by
    intro n
    positivity
  have hrhsDiff_tendsto :
      Tendsto (fun n => rhs (φ n) - rhs v) atTop (nhds 0) := by
    have hbound_n :
        ∀ n, |rhs (φ n) - rhs v| ≤ C_rhs * seminormDiff n := by
      intro n
      have hφ0n : MemH01 (φ n) Ω := smoothTest_memH01 hΩ (hφtest n)
      have hvNeg0 : MemH01 (fun x => (-1) * v x) Ω := by
        simpa [Pi.smul_apply, smul_eq_mul] using (MemW01p.smul (-1) hv0_all)
      have hsub0n : MemH01 (fun x => φ n x - v x) Ω := MemW01p.sub hφ0n hv0_all
      have hsubEq : rhs (fun x => φ n x - v x) = rhs (φ n) - rhs v := by
        calc
          rhs (fun x => φ n x - v x) = rhs (fun x => φ n x + (-1) * v x) := by
            congr
            ext x
            ring
          _ = rhs (φ n) + rhs (fun x => (-1) * v x) := hF_add (φ n) (fun x => (-1) * v x) hφ0n hvNeg0
          _ = rhs (φ n) + (-1) * rhs v := by rw [hF_smul (-1) v hv0_all]
          _ = rhs (φ n) - rhs v := by ring
      have hbound := hF_bound (fun x => φ n x - v x) hsub0n (hdiff n)
      rw [hsubEq] at hbound
      simpa [seminormDiff, μ] using hbound
    have hupper :
        Tendsto (fun n => C_rhs * seminormDiff n) atTop (nhds 0) := by
      simpa [seminormDiff] using Tendsto.const_mul C_rhs hdiff_seminorm_tendsto
    have habs :
        Tendsto (fun n => |rhs (φ n) - rhs v|) atTop (nhds 0) :=
      squeeze_zero (fun n => abs_nonneg _) hbound_n hupper
    exact (tendsto_zero_iff_abs_tendsto_zero _).2 habs
  let seminormU : ℝ :=
    (∫ x, ‖hwu.weakGrad x‖ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ))
  have hbilinDiff_tendsto :
      Tendsto
        (fun n => bilinFormOfCoeff A hwu (hφw n) - bilinFormOfCoeff A hwu hvw)
        atTop (nhds 0) := by
    have hbound_n :
        ∀ n,
          |bilinFormOfCoeff A hwu (hφw n) - bilinFormOfCoeff A hwu hvw|
            ≤ A.Λ * seminormU * seminormDiff n := by
      intro n
      have hsplit :
          bilinFormOfCoeff A hwu (hdiff n) =
            bilinFormOfCoeff A hwu (hφw n) - bilinFormOfCoeff A hwu hvw := by
        calc
          bilinFormOfCoeff A hwu (hdiff n)
              = bilinFormOfCoeff A hwu (haddiff n) := by
                  unfold bilinFormOfCoeff
                  apply integral_congr_ae
                  filter_upwards with x
                  simp [bilinFormIntegrandOfCoeff, hdiff, haddiff]
          _ = bilinFormOfCoeff A hwu (hφw n) + bilinFormOfCoeff A hwu (hvw.smul (-1)) := by
                  rw [show haddiff n = (hφw n).add (hvw.smul (-1)) by simp [haddiff]]
                  rw [bilinFormOfCoeff_add_right A hwu (hφw n) (hvw.smul (-1))]
          _ = bilinFormOfCoeff A hwu (hφw n) + (-1) * bilinFormOfCoeff A hwu hvw := by
                rw [bilinFormOfCoeff_smul_right (-1) A hwu hvw]
          _ = bilinFormOfCoeff A hwu (hφw n) - bilinFormOfCoeff A hwu hvw := by
                ring
      have hbound := bilinForm_bound A hwu (hdiff n)
      rw [hsplit] at hbound
      simpa [seminormU, seminormDiff, μ, mul_assoc] using hbound
    have hupper :
        Tendsto (fun n => A.Λ * seminormU * seminormDiff n) atTop (nhds 0) := by
      simpa [seminormU, seminormDiff, mul_assoc] using
        Tendsto.const_mul (A.Λ * seminormU) hdiff_seminorm_tendsto
    have habs :
        Tendsto
          (fun n => |bilinFormOfCoeff A hwu (hφw n) - bilinFormOfCoeff A hwu hvw|)
          atTop (nhds 0) :=
      squeeze_zero (fun n => abs_nonneg _) hbound_n hupper
    exact (tendsto_zero_iff_abs_tendsto_zero _).2 habs
  have hLhs_tendsto :
      Tendsto (fun n => bilinFormOfCoeff A hwu (hφw n))
        atTop (nhds (bilinFormOfCoeff A hwu hvw)) := by
    convert hbilinDiff_tendsto.add tendsto_const_nhds using 1
    · ext n
      ring_nf
    · ring_nf
  have hRhs_tendsto :
      Tendsto (fun n => rhs (φ n)) atTop (nhds (rhs v)) := by
    convert hrhsDiff_tendsto.add tendsto_const_nhds using 1
    · ext n
      ring_nf
    · ring_nf
  have hEq_tendsto :
      Tendsto (fun n => bilinFormOfCoeff A hwu (hφw n)) atTop (nhds (rhs v)) := by
    refine Tendsto.congr' (Filter.Eventually.of_forall ?_) hRhs_tendsto
    intro n
    exact (hsmooth_eq (hφtest n)).symm
  have hChosen : bilinFormOfCoeff A hwu hvw = rhs v :=
    tendsto_nhds_unique hLhs_tendsto hEq_tendsto
  calc
    bilinFormOfCoeff A hwu' hv = bilinFormOfCoeff A hwu hv := by
      exact bilinFormOfCoeff_eq_left hΩ A hwu' hwu hv
    _ = bilinFormOfCoeff A hwu hvw := by
      exact bilinFormOfCoeff_eq_right hΩ A hwu hv hvw
    _ = rhs v := hChosen

/-- Existence of zero-Dirichlet weak solutions for divergence-form right-hand
side data `div F`. -/
theorem weakProblem_exists_of_divergenceData
    {Ω : Set E}
    (hd : 2 ≤ d)
    (hΩ : IsOpen Ω) (hΩ_bdd : Bornology.IsBounded Ω)
    (A : EllipticCoeff d Ω)
    {F : E → E} (hF : MemLp F 2 (volume.restrict Ω)) :
    ∃ u : E → ℝ,
      IsWeakSolution (d := d)
        ⟨Ω, hΩ, hΩ_bdd, A, weakProblemRHSOfField (Ω := Ω) F⟩ u := by
  refine weakProblem_exists hd hΩ hΩ_bdd A (weakProblemRHSOfField (Ω := Ω) F) ?_ ?_ ?_
  · intro u v hu0 hv0
    let hu : MemW1pWitness 2 u Ω :=
      DeGiorgi.MemW1p.someWitness (MemW01p.memW1p hu0)
    let hv : MemW1pWitness 2 v Ω :=
      DeGiorgi.MemW1p.someWitness (MemW01p.memW1p hv0)
    have huv0 : MemH01 (fun x => u x + v x) Ω := MemW01p.add hu0 hv0
    let huv : MemW1pWitness 2 (fun x => u x + v x) Ω := hu.add hv
    calc
      weakProblemRHSOfField (Ω := Ω) F (fun x => u x + v x)
          = divergenceRHSOfField F huv := by
              exact weakProblemRHSOfField_eq_of_memH01 hΩ huv0 huv
      _ = divergenceRHSOfField F hu + divergenceRHSOfField F hv := by
            exact divergenceRHSOfField_add hF hu hv
      _ = weakProblemRHSOfField (Ω := Ω) F u + weakProblemRHSOfField (Ω := Ω) F v := by
            rw [weakProblemRHSOfField_eq_of_memH01 hΩ hu0 hu,
              weakProblemRHSOfField_eq_of_memH01 hΩ hv0 hv]
  · intro c u hu0
    let hu : MemW1pWitness 2 u Ω :=
      DeGiorgi.MemW1p.someWitness (MemW01p.memW1p hu0)
    have hcu0 : MemH01 (fun x => c * u x) Ω := by
      simpa [Pi.smul_apply, smul_eq_mul] using (MemW01p.smul c hu0)
    let hcu : MemW1pWitness 2 (fun x => c * u x) Ω := hu.smul c
    calc
      weakProblemRHSOfField (Ω := Ω) F (fun x => c * u x)
          = divergenceRHSOfField F hcu := by
              exact weakProblemRHSOfField_eq_of_memH01 hΩ hcu0 hcu
      _ = c * divergenceRHSOfField F hu := by
            exact divergenceRHSOfField_smul c hu
      _ = c * weakProblemRHSOfField (Ω := Ω) F u := by
            rw [weakProblemRHSOfField_eq_of_memH01 hΩ hu0 hu]
  · refine ⟨(∫ x, ‖F x‖ ^ (2 : ℝ) ∂(volume.restrict Ω)) ^ (1 / (2 : ℝ)), by positivity, ?_⟩
    intro v hv0 hv
    exact weakProblemRHSOfField_bound hΩ hF v hv0 hv

/-- Existence of weak solutions to the inhomogeneous Dirichlet problem with
boundary datum `u₀` and divergence-form right-hand side `div F`. -/
theorem dirichletProblem_exists_of_divergenceData
    {Ω : Set E}
    (hd : 2 ≤ d)
    (hΩ : IsOpen Ω) (hΩ_bdd : Bornology.IsBounded Ω)
    (A : EllipticCoeff d Ω)
    {u₀ : E → ℝ} (hu₀ : MemW1p 2 u₀ Ω)
    {F : E → E} (hF : MemLp F 2 (volume.restrict Ω)) :
    ∃ u : E → ℝ,
      MemW1p 2 u Ω ∧
      MemW01p 2 (fun x => u x - u₀ x) Ω ∧
      ∀ (hu : MemW1pWitness 2 u Ω) (v : E → ℝ), MemH01 v Ω →
        ∀ (hv : MemW1pWitness 2 v Ω),
          bilinFormOfCoeff A hu hv = divergenceRHSOfField F hv := by
  let hu₀w : MemW1pWitness 2 u₀ Ω := DeGiorgi.MemW1p.someWitness hu₀
  let rhs := weakProblemRHSOfFieldAndDatum (A := A) (Ω := Ω) F hu₀w
  obtain ⟨w, hwsol⟩ :=
    weakProblem_exists hd hΩ hΩ_bdd A rhs
      (by
        intro u v hu0 hv0
        let hu : MemW1pWitness 2 u Ω :=
          DeGiorgi.MemW1p.someWitness (MemW01p.memW1p hu0)
        let hv : MemW1pWitness 2 v Ω :=
          DeGiorgi.MemW1p.someWitness (MemW01p.memW1p hv0)
        have huv0 : MemH01 (fun x => u x + v x) Ω := MemW01p.add hu0 hv0
        let huv : MemW1pWitness 2 (fun x => u x + v x) Ω := hu.add hv
        calc
          rhs (fun x => u x + v x)
              = divergenceRHSOfField F huv - bilinFormOfCoeff A hu₀w huv := by
                  exact weakProblemRHSOfFieldAndDatum_eq_of_memH01 hΩ A hu₀w huv0 huv
          _ = (divergenceRHSOfField F hu + divergenceRHSOfField F hv) -
                (bilinFormOfCoeff A hu₀w hu + bilinFormOfCoeff A hu₀w hv) := by
                  rw [divergenceRHSOfField_add hF hu hv, bilinFormOfCoeff_add_right A hu₀w hu hv]
          _ = weakProblemRHSOfFieldAndDatum (A := A) (Ω := Ω) F hu₀w u +
                weakProblemRHSOfFieldAndDatum (A := A) (Ω := Ω) F hu₀w v := by
                  rw [weakProblemRHSOfFieldAndDatum_eq_of_memH01 hΩ A hu₀w hu0 hu,
                    weakProblemRHSOfFieldAndDatum_eq_of_memH01 hΩ A hu₀w hv0 hv]
                  ring
          _ = rhs u + rhs v := by rfl)
      (by
        intro c u hu0
        let hu : MemW1pWitness 2 u Ω :=
          DeGiorgi.MemW1p.someWitness (MemW01p.memW1p hu0)
        have hcu0 : MemH01 (fun x => c * u x) Ω := by
          simpa [Pi.smul_apply, smul_eq_mul] using (MemW01p.smul c hu0)
        let hcu : MemW1pWitness 2 (fun x => c * u x) Ω := hu.smul c
        calc
          rhs (fun x => c * u x)
              = divergenceRHSOfField F hcu - bilinFormOfCoeff A hu₀w hcu := by
                  exact weakProblemRHSOfFieldAndDatum_eq_of_memH01 hΩ A hu₀w hcu0 hcu
          _ = c * divergenceRHSOfField F hu - c * bilinFormOfCoeff A hu₀w hu := by
                rw [divergenceRHSOfField_smul c hu, bilinFormOfCoeff_smul_right c A hu₀w hu]
          _ = c * weakProblemRHSOfFieldAndDatum (A := A) (Ω := Ω) F hu₀w u := by
                rw [weakProblemRHSOfFieldAndDatum_eq_of_memH01 hΩ A hu₀w hu0 hu]
                ring
          _ = c * rhs u := by rfl)
      <| by
        have hCF_nonneg :
            0 ≤ (∫ x, ‖F x‖ ^ (2 : ℝ) ∂(volume.restrict Ω)) ^ (1 / (2 : ℝ)) := by
          positivity
        have hCU_nonneg :
            0 ≤ A.Λ * (∫ x, ‖hu₀w.weakGrad x‖ ^ (2 : ℝ) ∂(volume.restrict Ω)) ^
              (1 / (2 : ℝ)) := by
          refine mul_nonneg A.Λ_nonneg ?_
          positivity
        refine ⟨((∫ x, ‖F x‖ ^ (2 : ℝ) ∂(volume.restrict Ω)) ^ (1 / (2 : ℝ)) +
            A.Λ * (∫ x, ‖hu₀w.weakGrad x‖ ^ (2 : ℝ) ∂(volume.restrict Ω)) ^
              (1 / (2 : ℝ))), add_nonneg hCF_nonneg hCU_nonneg, ?_⟩
        intro v hv0 hv
        simpa [rhs] using weakProblemRHSOfFieldAndDatum_bound hΩ A hF hu₀w v hv0 hv
  have hw0 : MemH01 w Ω := hwsol.left
  let hw : MemW1pWitness 2 w Ω :=
    DeGiorgi.MemW1p.someWitness (MemW01p.memW1p hw0)
  let u : E → ℝ := fun x => w x + u₀ x
  let hu : MemW1pWitness 2 u Ω := hw.add hu₀w
  refine ⟨u, hu.memW1p, ?_, ?_⟩
  · simpa [u] using hw0
  · intro hu' v hv0 hv
    calc
      bilinFormOfCoeff A hu' hv = bilinFormOfCoeff A hu hv := by
        exact bilinFormOfCoeff_eq_left hΩ A hu' hu hv
      _ = bilinFormOfCoeff A hw hv + bilinFormOfCoeff A hu₀w hv := by
        simpa [hu] using bilinFormOfCoeff_add_left A hw hu₀w hv
      _ = rhs v + bilinFormOfCoeff A hu₀w hv := by
        rw [hwsol.right hw v hv0 hv]
      _ = weakProblemRHSOfFieldAndDatum (A := A) (Ω := Ω) F hu₀w v +
            bilinFormOfCoeff A hu₀w hv := by
        rfl
      _ = divergenceRHSOfField F hv := by
        rw [weakProblemRHSOfFieldAndDatum_eq_of_memH01 hΩ A hu₀w hv0 hv]
        ring

/-- Stability estimate for weak solutions. -/
theorem weakSolution_stability
    {Ω : Set E}
    (A : EllipticCoeff d Ω)
    {u : E → ℝ}
    (hu0 : MemH01 u Ω)
    (hwu : MemW1pWitness 2 u Ω)
    {rhs : (E → ℝ) → ℝ}
    {C_F : ℝ} (hCF : 0 ≤ C_F)
    (hF : ∀ v : E → ℝ, MemH01 v Ω →
      ∀ hwv : MemW1pWitness 2 v Ω,
      |rhs v| ≤ C_F *
        (∫ x, ‖hwv.weakGrad x‖ ^ (2 : ℝ) ∂(volume.restrict Ω)) ^ (1 / (2 : ℝ)))
    (h_ws : bilinFormOfCoeff A hwu hwu = rhs u) :
    (∫ x, ‖hwu.weakGrad x‖ ^ (2 : ℝ) ∂(volume.restrict Ω)) ^ (1 / (2 : ℝ)) ≤
    A.lam⁻¹ * C_F := by
  let μ : Measure E := volume.restrict Ω
  let J : ℝ := ∫ x, ‖hwu.weakGrad x‖ ^ (2 : ℕ) ∂μ
  have hJ_nonneg : 0 ≤ J := by
    dsimp [J]
    refine integral_nonneg ?_
    intro x
    positivity
  have hnorm_eq :
      ‖gradLpOfWitness hwu‖ = Real.sqrt J := by
    calc
      ‖gradLpOfWitness hwu‖
          = (∫ x, ‖hwu.weakGrad x‖ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) := by
              simpa [μ] using norm_gradLpOfWitness_eq hwu
      _ = J ^ (1 / (2 : ℝ)) := by
            congr 1
            dsimp [J]
            apply integral_congr_ae
            filter_upwards with x
            exact Real.rpow_natCast ‖hwu.weakGrad x‖ 2
      _ = Real.sqrt J := by
            rw [Real.sqrt_eq_rpow]
  have hnorm_sq :
      ‖gradLpOfWitness hwu‖ ^ (2 : ℕ) = J := by
    calc
      ‖gradLpOfWitness hwu‖ ^ (2 : ℕ) = (Real.sqrt J) ^ (2 : ℕ) := by rw [hnorm_eq]
      _ = J := by simpa [pow_two] using Real.sq_sqrt hJ_nonneg
  have hcoercive :
      A.lam * ‖gradLpOfWitness hwu‖ ^ (2 : ℕ) ≤ bilinFormOfCoeff A hwu hwu := by
    calc
      A.lam * ‖gradLpOfWitness hwu‖ ^ (2 : ℕ) = A.lam * J := by rw [hnorm_sq]
      _ = A.lam * ∫ x, ‖hwu.weakGrad x‖ ^ (2 : ℕ) ∂μ := by rfl
      _ ≤ bilinFormOfCoeff A hwu hwu := by
            simpa [μ] using bilinForm_coercive A hwu
  have h_rhs_bound : |rhs u| ≤ C_F * ‖gradLpOfWitness hwu‖ := by
    calc
      |rhs u| ≤ C_F * (∫ x, ‖hwu.weakGrad x‖ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) := hF u hu0 hwu
      _ = C_F * ‖gradLpOfWitness hwu‖ := by rw [norm_gradLpOfWitness_eq hwu]
  have hbilin_nonneg : 0 ≤ bilinFormOfCoeff A hwu hwu := by
    exact le_trans (mul_nonneg A.lam_nonneg (sq_nonneg ‖gradLpOfWitness hwu‖)) hcoercive
  have hrhs_nonneg : 0 ≤ rhs u := by
    simpa [h_ws] using hbilin_nonneg
  have hmain :
      A.lam * ‖gradLpOfWitness hwu‖ ^ (2 : ℕ) ≤ C_F * ‖gradLpOfWitness hwu‖ := by
    calc
      A.lam * ‖gradLpOfWitness hwu‖ ^ (2 : ℕ) ≤ bilinFormOfCoeff A hwu hwu := hcoercive
      _ = rhs u := h_ws
      _ = |rhs u| := by symm; exact abs_of_nonneg hrhs_nonneg
      _ ≤ C_F * ‖gradLpOfWitness hwu‖ := h_rhs_bound
  have hlin :
      A.lam * ‖gradLpOfWitness hwu‖ ≤ C_F := by
    have hmain' :
        A.lam * ‖gradLpOfWitness hwu‖ ^ 2 ≤ C_F * ‖gradLpOfWitness hwu‖ := by
      simpa [pow_two] using hmain
    nlinarith [hmain', A.hlam, norm_nonneg (gradLpOfWitness hwu)]
  have hdiv :
      ‖gradLpOfWitness hwu‖ ≤ C_F / A.lam := by
    have hlin' : ‖gradLpOfWitness hwu‖ * A.lam ≤ C_F := by
      simpa [mul_comm] using hlin
    exact (le_div_iff₀ A.hlam).2 hlin'
  simpa [norm_gradLpOfWitness_eq hwu, div_eq_mul_inv, mul_comm] using hdiv

/-- A zero-trace Sobolev function with vanishing `L²` gradient class vanishes
almost everywhere. -/
theorem ae_eq_zero_of_memH01_of_gradLpOfWitness_eq_zero
    {Ω : Set E} (hd : 2 ≤ d) (hΩ : IsOpen Ω)
    (hΩ_bdd : Bornology.IsBounded Ω)
    {u : E → ℝ}
    (hu0 : MemH01 u Ω)
    (hwu : MemW1pWitness 2 u Ω)
    (hgrad_zero : gradLpOfWitness hwu = 0) :
    u =ᵐ[volume.restrict Ω] 0 := by
  let μ : Measure E := volume.restrict Ω
  obtain ⟨hu_mem, hw0, φ, hφ_smooth, hφ_cpt, hφ_sub, hφ_fun, hφ_grad⟩ := hu0
  have hgrad_ae :
      hw0.weakGrad =ᵐ[μ] hwu.weakGrad := by
    simpa [μ] using MemW1pWitness.ae_eq hΩ hw0 hwu
  have hgradLp_eq : gradLpOfWitness hw0 = gradLpOfWitness hwu := by
    simpa [gradLpOfWitness] using
      (MemLp.toLp_congr hw0.weakGrad_memLp hwu.weakGrad_memLp hgrad_ae)
  have hgrad_zero0 : gradLpOfWitness hw0 = 0 := by
    rw [hgradLp_eq]
    exact hgrad_zero
  let hφtest : ∀ n : ℕ, IsSmoothTestOn Ω (φ n) := fun n =>
    ⟨hφ_smooth n, hφ_cpt n, hφ_sub n⟩
  let hφw : ∀ n : ℕ, MemW1pWitness 2 (φ n) Ω := fun n =>
    smoothTestWitness hΩ (hφtest n)
  have hφ_fun_tendsto :
      Tendsto (fun n => smoothFunToLp hΩ (hφtest n))
        atTop (nhds (hu_mem.1.toLp u)) := by
    exact
      (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' (f := φ)
        (f_ℒp := fun n => (hφw n).memLp)
        (f_lim := u) (f_lim_ℒp := hu_mem.1)).2 <| by
          simpa [μ] using hφ_fun
  have hgrad_vec_tendsto :
      Tendsto
        (fun n => eLpNorm (fun x => (hφw n).weakGrad x - hw0.weakGrad x) 2 μ)
        atTop (nhds 0) := by
    exact tendsto_eLpNorm_vector_of_componentwise
      (fun n i => by
        simpa [hφw] using ((hφw n).weakGrad_component_memLp i).sub (hw0.weakGrad_component_memLp i))
      (fun i => by simpa [μ] using hφ_grad i)
  have hgradLp_tendsto :
      Tendsto (fun n => gradLpOfWitness (hφw n))
        atTop (nhds (gradLpOfWitness hw0)) := by
    exact
      (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' (f := fun n => (hφw n).weakGrad)
        (f_ℒp := fun n => (hφw n).weakGrad_memLp)
        (f_lim := hw0.weakGrad) (f_lim_ℒp := hw0.weakGrad_memLp)).2
        hgrad_vec_tendsto
  have hgradLp_zero_tendsto :
      Tendsto (fun n => gradLpOfWitness (hφw n)) atTop (nhds 0) := by
    simpa [hgrad_zero0] using hgradLp_tendsto
  obtain ⟨Cp, hCp_top, hPoinc⟩ := smoothCompactSupport_L2_bound_on_bounded_ge_two hd hΩ_bdd
  have hfun_bound :
      ∀ n, ‖smoothFunToLp hΩ (hφtest n)‖ ≤ Cp.toReal * ‖smoothGradToLp hΩ (hφtest n)‖ := by
    intro n
    have hgradNorm_memLp : MemLp (smoothGradNorm (φ n)) 2 μ := by
      simpa [μ, norm_smoothGradField_eq_smoothGradNorm] using (hφw n).weakGrad_memLp.norm
    have hP :
        eLpNorm (φ n) 2 μ ≤ Cp * eLpNorm (smoothGradNorm (φ n)) 2 μ := by
      simpa [μ] using hPoinc (hφ_smooth n) (hφ_cpt n) (hφ_sub n)
    have hleft_top : eLpNorm (φ n) 2 μ ≠ ⊤ := (hφw n).memLp.eLpNorm_lt_top.ne
    have hright_top : Cp * eLpNorm (smoothGradNorm (φ n)) 2 μ ≠ ⊤ := by
      exact (ENNReal.mul_lt_top hCp_top hgradNorm_memLp.eLpNorm_lt_top).ne
    have hToReal :
        (eLpNorm (φ n) 2 μ).toReal ≤ (Cp * eLpNorm (smoothGradNorm (φ n)) 2 μ).toReal :=
      (ENNReal.toReal_le_toReal hleft_top hright_top).2 hP
    have hfunEq : ‖smoothFunToLp hΩ (hφtest n)‖ = (eLpNorm (φ n) 2 μ).toReal := by
      rw [smoothFunToLp, Lp.norm_toLp]
    have hgradEq : ‖smoothGradToLp hΩ (hφtest n)‖ = (eLpNorm (smoothGradNorm (φ n)) 2 μ).toReal := by
      have hgrad_memLp : MemLp (smoothGradField (φ n)) 2 μ := (hφw n).weakGrad_memLp
      calc
        ‖smoothGradToLp hΩ (hφtest n)‖
            = (∫ x, ‖smoothGradField (φ n) x‖ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) := by
                simpa [μ] using norm_smoothGradToLp_eq hΩ (hφtest n)
        _ = (eLpNorm (smoothGradField (φ n)) 2 μ).toReal := by
              symm
              rw [MeasureTheory.toReal_eLpNorm hgrad_memLp.aestronglyMeasurable]
              simpa using
                (MeasureTheory.lpNorm_eq_integral_norm_rpow_toReal
                  (μ := μ) (f := smoothGradField (φ n)) (p := (2 : ENNReal))
                  (by norm_num) (by simp) hgrad_memLp.aestronglyMeasurable)
        _ = (eLpNorm (smoothGradNorm (φ n)) 2 μ).toReal := by
              congr 1
              calc
                eLpNorm (smoothGradField (φ n)) 2 μ =
                    eLpNorm (fun x => ‖smoothGradField (φ n) x‖) 2 μ := by
                      symm
                      exact eLpNorm_norm (μ := μ) (p := (2 : ENNReal)) (smoothGradField (φ n))
                _ = eLpNorm (smoothGradNorm (φ n)) 2 μ := by
                      simp [norm_smoothGradField_eq_smoothGradNorm]
    rw [hfunEq, hgradEq]
    convert hToReal using 1
    rw [ENNReal.toReal_mul]
  have hgrad_norm_tendsto :
      Tendsto (fun n => ‖smoothGradToLp hΩ (hφtest n)‖) atTop (nhds 0) := by
    have hnorm_tendsto :
        Tendsto (fun n => ‖gradLpOfWitness (hφw n)‖) atTop (nhds 0) := by
      simpa using ((continuous_norm.tendsto (0 : MeasureTheory.Lp E 2 μ)).comp hgradLp_zero_tendsto)
    simpa [smoothGradToLp, hφw] using hnorm_tendsto
  have hfun_norm_tendsto :
      Tendsto (fun n => ‖smoothFunToLp hΩ (hφtest n)‖) atTop (nhds 0) := by
    have hupper :
        Tendsto (fun n => Cp.toReal * ‖smoothGradToLp hΩ (hφtest n)‖) atTop (nhds 0) := by
      simpa using Tendsto.const_mul Cp.toReal hgrad_norm_tendsto
    exact squeeze_zero (fun n => norm_nonneg _) hfun_bound hupper
  have hfun_zero_tendsto :
      Tendsto (fun n => smoothFunToLp hΩ (hφtest n)) atTop (nhds 0) := by
    exact tendsto_zero_iff_norm_tendsto_zero.2 hfun_norm_tendsto
  have hu_toLp_zero : hu_mem.1.toLp u = 0 := by
    exact tendsto_nhds_unique hφ_fun_tendsto hfun_zero_tendsto
  have htoLp_zero_ae : (hu_mem.1.toLp u : E → ℝ) =ᵐ[μ] (0 : E → ℝ) := by
    let h0_mem : MemLp (0 : E → ℝ) 2 μ := MeasureTheory.MemLp.zero'
    have h0_ae : (h0_mem.toLp (0 : E → ℝ) : E → ℝ) =ᵐ[μ] (0 : E → ℝ) := by
      exact MemLp.coeFn_toLp h0_mem
    rw [hu_toLp_zero]
    simpa [h0_mem.toLp_zero] using h0_ae
  calc
    u =ᵐ[μ] hu_mem.1.toLp u := (MemLp.coeFn_toLp hu_mem.1).symm
    _ =ᵐ[μ] (0 : E → ℝ) := htoLp_zero_ae

/-- Zero-boundary weak solutions are unique up to a.e. equality. -/
theorem weakProblem_unique
    (hd : 2 ≤ d)
    {P : WeakProblem (d := d)}
    {u v : E → ℝ}
    (hu : IsWeakSolution P u)
    (hv : IsWeakSolution P v) :
    u =ᵐ[volume.restrict P.Ω] v := by
  have hu0 : MemH01 u P.Ω := hu.left
  have hv0 : MemH01 v P.Ω := hv.left
  have hdiff0 : MemH01 (fun x => u x - v x) P.Ω := MemW01p.sub hu0 hv0
  let hwu : MemW1pWitness 2 u P.Ω :=
    DeGiorgi.MemW1p.someWitness (MemW01p.memW1p hu0)
  let hwv : MemW1pWitness 2 v P.Ω :=
    DeGiorgi.MemW1p.someWitness (MemW01p.memW1p hv0)
  let hdiff_add : MemW1pWitness 2 (fun x => u x + (-1) * v x) P.Ω :=
    hwu.add (hwv.smul (-1))
  let hdiff : MemW1pWitness 2 (fun x => u x - v x) P.Ω := {
    memLp := by
      simpa [sub_eq_add_neg, Pi.smul_apply] using hdiff_add.memLp
    weakGrad := hdiff_add.weakGrad
    weakGrad_component_memLp := by
      intro i
      simpa [sub_eq_add_neg, Pi.smul_apply] using hdiff_add.weakGrad_component_memLp i
    isWeakGrad := by
      intro i
      simpa [sub_eq_add_neg, Pi.smul_apply] using hdiff_add.isWeakGrad i }
  have hzero_test :
      ∀ (φ : E → ℝ), MemH01 φ P.Ω →
        ∀ (hφ : MemW1pWitness 2 φ P.Ω),
          bilinFormOfCoeff P.coeff hdiff hφ = 0 := by
    intro φ hφ0 hφ
    calc
      bilinFormOfCoeff P.coeff hdiff hφ
          = bilinFormOfCoeff P.coeff hdiff_add hφ := by
              rfl
      _ = bilinFormOfCoeff P.coeff hwu hφ +
            bilinFormOfCoeff P.coeff (hwv.smul (-1)) hφ := by
              simpa [hdiff_add] using bilinFormOfCoeff_add_left P.coeff hwu (hwv.smul (-1)) hφ
      _ = bilinFormOfCoeff P.coeff hwu hφ + (-1) * bilinFormOfCoeff P.coeff hwv hφ := by
            rw [bilinFormOfCoeff_smul_left (-1) P.coeff hwv hφ]
      _ = P.rhs φ + (-1) * P.rhs φ := by rw [hu.right hwu φ hφ0 hφ, hv.right hwv φ hφ0 hφ]
      _ = 0 := by ring
  have h_ws : bilinFormOfCoeff P.coeff hdiff hdiff = (0 : ℝ) := hzero_test _ hdiff0 hdiff
  have hstab :
      (∫ x, ‖hdiff.weakGrad x‖ ^ (2 : ℝ) ∂(volume.restrict P.Ω)) ^ (1 / (2 : ℝ)) ≤
        P.coeff.lam⁻¹ * (0 : ℝ) := by
    simpa using weakSolution_stability P.coeff hdiff0 hdiff
      (rhs := fun _ : E → ℝ => (0 : ℝ)) (C_F := 0) (by norm_num)
      (by intro φ hφ0 hφ; simp) h_ws
  have hseminorm_zero :
      (∫ x, ‖hdiff.weakGrad x‖ ^ (2 : ℝ) ∂(volume.restrict P.Ω)) ^ (1 / (2 : ℝ)) = 0 := by
    refine le_antisymm ?_ ?_
    · simpa using hstab
    · positivity
  have hgrad_zero : gradLpOfWitness hdiff = 0 := by
    apply norm_eq_zero.mp
    simpa [norm_gradLpOfWitness_eq hdiff] using hseminorm_zero
  have hdiff_ae_zero :
      (fun x => u x - v x) =ᵐ[volume.restrict P.Ω] 0 := by
    exact ae_eq_zero_of_memH01_of_gradLpOfWitness_eq_zero hd P.hΩ P.hΩ_bdd hdiff0 hdiff hgrad_zero
  filter_upwards [hdiff_ae_zero] with x hx
  simpa [sub_eq_zero] using hx

/-- Weak solution of the inhomogeneous Dirichlet problem with boundary datum
`u₀` and divergence-form right-hand side `div F`. -/
def IsDirichletWeakSolutionOfDivergenceData
    {Ω : Set E}
    (A : EllipticCoeff d Ω)
    (u₀ : E → ℝ)
    (F : E → E)
    (u : E → ℝ) : Prop :=
  MemW1p 2 u Ω ∧
  MemW01p 2 (fun x => u x - u₀ x) Ω ∧
  ∀ (hu : MemW1pWitness 2 u Ω) (v : E → ℝ), MemH01 v Ω →
    ∀ (hv : MemW1pWitness 2 v Ω),
      bilinFormOfCoeff A hu hv = divergenceRHSOfField F hv

/-- Dirichlet existence theorem stated using the weak-solution predicate. -/
theorem dirichletProblem_exists_of_divergenceData'
    {Ω : Set E}
    (hd : 2 ≤ d)
    (hΩ : IsOpen Ω) (hΩ_bdd : Bornology.IsBounded Ω)
    (A : EllipticCoeff d Ω)
    {u₀ : E → ℝ} (hu₀ : MemW1p 2 u₀ Ω)
    {F : E → E} (hF : MemLp F 2 (volume.restrict Ω)) :
    ∃ u : E → ℝ, IsDirichletWeakSolutionOfDivergenceData A u₀ F u := by
  obtain ⟨u, hu_mem, hdiff, hweak⟩ :=
    dirichletProblem_exists_of_divergenceData hd hΩ hΩ_bdd A hu₀ hF
  exact ⟨u, hu_mem, hdiff, hweak⟩

/-- A Dirichlet solution lifts to a zero-boundary weak solution for the shifted
unknown `u - u₀`. -/
theorem isWeakSolution_subDatum_of_dirichletProblem
    {Ω : Set E}
    (hΩ : IsOpen Ω) (hΩ_bdd : Bornology.IsBounded Ω)
    (A : EllipticCoeff d Ω)
    {u₀ : E → ℝ} (hu₀ : MemW1p 2 u₀ Ω)
    {F : E → E} {u : E → ℝ}
    (hu : IsDirichletWeakSolutionOfDivergenceData A u₀ F u) :
    IsWeakSolution (d := d)
      ⟨Ω, hΩ, hΩ_bdd, A,
        weakProblemRHSOfFieldAndDatum (A := A) (Ω := Ω) F
          (DeGiorgi.MemW1p.someWitness hu₀)⟩
      (fun x => u x - u₀ x) := by
  let hu₀w : MemW1pWitness 2 u₀ Ω := DeGiorgi.MemW1p.someWitness hu₀
  let huu : MemW1pWitness 2 u Ω := DeGiorgi.MemW1p.someWitness hu.left
  let hsub_add : MemW1pWitness 2 (fun x => u x + (-1) * u₀ x) Ω :=
    huu.add (hu₀w.smul (-1))
  let hsub : MemW1pWitness 2 (fun x => u x - u₀ x) Ω := {
    memLp := by
      simpa [sub_eq_add_neg, Pi.smul_apply] using hsub_add.memLp
    weakGrad := hsub_add.weakGrad
    weakGrad_component_memLp := by
      intro i
      simpa [sub_eq_add_neg, Pi.smul_apply] using hsub_add.weakGrad_component_memLp i
    isWeakGrad := by
      intro i
      simpa [sub_eq_add_neg, Pi.smul_apply] using hsub_add.isWeakGrad i }
  refine ⟨hu.2.1, ?_⟩
  intro hw' v hv0 hv
  calc
    bilinFormOfCoeff A hw' hv = bilinFormOfCoeff A hsub hv := by
      exact bilinFormOfCoeff_eq_left hΩ A hw' hsub hv
    _ = bilinFormOfCoeff A hsub_add hv := by
          rfl
    _ = bilinFormOfCoeff A huu hv + bilinFormOfCoeff A (hu₀w.smul (-1)) hv := by
          simpa [hsub_add] using bilinFormOfCoeff_add_left A huu (hu₀w.smul (-1)) hv
    _ = bilinFormOfCoeff A huu hv + (-1) * bilinFormOfCoeff A hu₀w hv := by
          rw [bilinFormOfCoeff_smul_left (-1) A hu₀w hv]
    _ = divergenceRHSOfField F hv + (-1) * bilinFormOfCoeff A hu₀w hv := by
          rw [hu.2.2 huu v hv0 hv]
    _ = divergenceRHSOfField F hv - bilinFormOfCoeff A hu₀w hv := by
          ring
    _ = weakProblemRHSOfFieldAndDatum (A := A) (Ω := Ω) F hu₀w v := by
          symm
          exact weakProblemRHSOfFieldAndDatum_eq_of_memH01 hΩ A hu₀w hv0 hv

/-- Energy estimate for the shifted Dirichlet solution `u - u₀`. -/
theorem dirichletProblem_stability_of_divergenceData
    {Ω : Set E}
    (hΩ : IsOpen Ω) (hΩ_bdd : Bornology.IsBounded Ω)
    (A : EllipticCoeff d Ω)
    {u₀ : E → ℝ} (hu₀ : MemW1p 2 u₀ Ω)
    {F : E → E} (hF : MemLp F 2 (volume.restrict Ω))
    {u : E → ℝ}
    (hu : IsDirichletWeakSolutionOfDivergenceData A u₀ F u)
    (hw : MemW1pWitness 2 (fun x => u x - u₀ x) Ω) :
    (∫ x, ‖hw.weakGrad x‖ ^ (2 : ℝ) ∂(volume.restrict Ω)) ^ (1 / (2 : ℝ)) ≤
      A.lam⁻¹ *
        ((∫ x, ‖F x‖ ^ (2 : ℝ) ∂(volume.restrict Ω)) ^ (1 / (2 : ℝ)) +
          A.Λ * (∫ x, ‖(DeGiorgi.MemW1p.someWitness hu₀).weakGrad x‖ ^ (2 : ℝ)
            ∂(volume.restrict Ω)) ^ (1 / (2 : ℝ))) := by
  let hu₀w : MemW1pWitness 2 u₀ Ω := DeGiorgi.MemW1p.someWitness hu₀
  have hwsol :
      IsWeakSolution (d := d)
        ⟨Ω, hΩ, hΩ_bdd, A, weakProblemRHSOfFieldAndDatum (A := A) (Ω := Ω) F hu₀w⟩
        (fun x => u x - u₀ x) := by
    exact isWeakSolution_subDatum_of_dirichletProblem (Ω := Ω) hΩ hΩ_bdd A hu₀ hu
  have hbound :
      ∀ v : E → ℝ, MemH01 v Ω →
        ∀ hv : MemW1pWitness 2 v Ω,
          |weakProblemRHSOfFieldAndDatum (A := A) (Ω := Ω) F hu₀w v| ≤
            ((∫ x, ‖F x‖ ^ (2 : ℝ) ∂(volume.restrict Ω)) ^ (1 / (2 : ℝ)) +
              A.Λ * (∫ x, ‖hu₀w.weakGrad x‖ ^ (2 : ℝ) ∂(volume.restrict Ω)) ^
                (1 / (2 : ℝ))) *
            (∫ x, ‖hv.weakGrad x‖ ^ (2 : ℝ) ∂(volume.restrict Ω)) ^ (1 / (2 : ℝ)) := by
    intro v hv0 hv
    simpa [hu₀w] using weakProblemRHSOfFieldAndDatum_bound hΩ A hF hu₀w v hv0 hv
  exact weakSolution_stability A hu.2.1 hw (C_F :=
    (∫ x, ‖F x‖ ^ (2 : ℝ) ∂(volume.restrict Ω)) ^ (1 / (2 : ℝ)) +
      A.Λ * (∫ x, ‖hu₀w.weakGrad x‖ ^ (2 : ℝ) ∂(volume.restrict Ω)) ^ (1 / (2 : ℝ)))
    (by
      have hCF_nonneg :
          0 ≤ (∫ x, ‖F x‖ ^ (2 : ℝ) ∂(volume.restrict Ω)) ^ (1 / (2 : ℝ)) := by
        positivity
      have hCU_nonneg :
          0 ≤ A.Λ * (∫ x, ‖hu₀w.weakGrad x‖ ^ (2 : ℝ) ∂(volume.restrict Ω)) ^ (1 / (2 : ℝ)) := by
        exact mul_nonneg A.Λ_nonneg (by positivity)
      exact add_nonneg hCF_nonneg hCU_nonneg)
    hbound
    (hwsol.right hw (fun x => u x - u₀ x) hu.2.1 hw)

/-- Inhomogeneous Dirichlet solutions are unique up to a.e. equality. -/
theorem dirichletProblem_unique_of_divergenceData
    {Ω : Set E}
    (hd : 2 ≤ d)
    (hΩ : IsOpen Ω) (hΩ_bdd : Bornology.IsBounded Ω)
    (A : EllipticCoeff d Ω)
    {u₀ : E → ℝ} (hu₀ : MemW1p 2 u₀ Ω)
    {F : E → E} (_hF : MemLp F 2 (volume.restrict Ω))
    {u v : E → ℝ}
    (hu : IsDirichletWeakSolutionOfDivergenceData A u₀ F u)
    (hv : IsDirichletWeakSolutionOfDivergenceData A u₀ F v) :
    u =ᵐ[volume.restrict Ω] v := by
  let P : WeakProblem (d := d) :=
    ⟨Ω, hΩ, hΩ_bdd, A,
      weakProblemRHSOfFieldAndDatum (A := A) (Ω := Ω) F
        (DeGiorgi.MemW1p.someWitness hu₀)⟩
  have hu_shift :
      IsWeakSolution P (fun x => u x - u₀ x) := by
    exact isWeakSolution_subDatum_of_dirichletProblem (Ω := Ω) hΩ hΩ_bdd A hu₀ hu
  have hv_shift :
      IsWeakSolution P (fun x => v x - u₀ x) := by
    exact isWeakSolution_subDatum_of_dirichletProblem (Ω := Ω) hΩ hΩ_bdd A hu₀ hv
  have hshift_eq :
      (fun x => u x - u₀ x) =ᵐ[volume.restrict Ω] (fun x => v x - u₀ x) := by
    simpa [P] using weakProblem_unique hd hu_shift hv_shift
  filter_upwards [hshift_eq] with x hx
  linarith

/-- Packaged existence and uniqueness for the inhomogeneous Dirichlet problem. -/
theorem dirichletProblem_wellPosed_of_divergenceData
    {Ω : Set E}
    (hd : 2 ≤ d)
    (hΩ : IsOpen Ω) (hΩ_bdd : Bornology.IsBounded Ω)
    (A : EllipticCoeff d Ω)
    {u₀ : E → ℝ} (hu₀ : MemW1p 2 u₀ Ω)
    {F : E → E} (hF : MemLp F 2 (volume.restrict Ω)) :
    ∃ u : E → ℝ,
      IsDirichletWeakSolutionOfDivergenceData A u₀ F u ∧
      ∀ v : E → ℝ, IsDirichletWeakSolutionOfDivergenceData A u₀ F v →
        u =ᵐ[volume.restrict Ω] v := by
  obtain ⟨u, hu⟩ := dirichletProblem_exists_of_divergenceData' hd hΩ hΩ_bdd A hu₀ hF
  refine ⟨u, hu, ?_⟩
  intro v hv
  exact dirichletProblem_unique_of_divergenceData hd hΩ hΩ_bdd A hu₀ hF hu hv

/-- `A`-harmonic replacements are unique up to a.e. equality. -/
theorem aHarmonic_replacement_unique
    {Ω : Set E} (hd : 2 ≤ d)
    (hΩ : IsOpen Ω) (hΩ_bdd : Bornology.IsBounded Ω)
    {u h₁ h₂ : E → ℝ}
    (A : EllipticCoeff d Ω)
    (hu : MemW1p 2 u Ω)
    (hh₁ : IsHomogeneousWeakSolution A h₁)
    (hdiff₁ : MemW01p 2 (fun x => h₁ x - u x) Ω)
    (hh₂ : IsHomogeneousWeakSolution A h₂)
    (hdiff₂ : MemW01p 2 (fun x => h₂ x - u x) Ω) :
    h₁ =ᵐ[volume.restrict Ω] h₂ := by
  have hF0 : MemLp (fun _ : E => (0 : E)) 2 (volume.restrict Ω) := by
    exact MeasureTheory.MemLp.zero' (p := (2 : ENNReal)) (μ := volume.restrict Ω)
  have hs₁ : IsDirichletWeakSolutionOfDivergenceData A u (fun _ : E => (0 : E)) h₁ := by
    refine ⟨hh₁.left, hdiff₁, ?_⟩
    intro hh φ hφ hφw
    simpa [divergenceRHSOfField, divergenceRHSIntegrandOfField] using hh₁.right hh φ hφ hφw
  have hs₂ : IsDirichletWeakSolutionOfDivergenceData A u (fun _ : E => (0 : E)) h₂ := by
    refine ⟨hh₂.left, hdiff₂, ?_⟩
    intro hh φ hφ hφw
    simpa [divergenceRHSOfField, divergenceRHSIntegrandOfField] using hh₂.right hh φ hφ hφw
  exact dirichletProblem_unique_of_divergenceData hd hΩ hΩ_bdd A hu hF0 hs₁ hs₂

/-- A-harmonic replacement: given `u ∈ W^{1,2}(B_R)`, there exists
`h` that is A-harmonic with `h - u ∈ W₀^{1,2}(B_R)`. -/
theorem aHarmonic_replacement_exists
    {Ω : Set E} (hd : 2 ≤ d)
    (hΩ : IsOpen Ω) (hΩ_bdd : Bornology.IsBounded Ω)
    {u : E → ℝ}
    (A : EllipticCoeff d Ω)
    (hu : MemW1p 2 u Ω) :
    ∃ h : E → ℝ,
      IsHomogeneousWeakSolution A h ∧
      MemW01p 2 (fun x => h x - u x) Ω := by
  have hF0 : MemLp (fun _ : E => (0 : E)) 2 (volume.restrict Ω) := by
    exact MeasureTheory.MemLp.zero' (p := (2 : ENNReal)) (μ := volume.restrict Ω)
  obtain ⟨h, hh_mem, hdiff, hweak⟩ :=
    dirichletProblem_exists_of_divergenceData hd hΩ hΩ_bdd A hu hF0
  refine ⟨h, ?_, hdiff⟩
  refine ⟨hh_mem, ?_⟩
  intro hh φ hφ hφw
  have hEq := hweak hh φ hφ hφw
  simpa [divergenceRHSOfField, divergenceRHSIntegrandOfField] using hEq


end DeGiorgi
