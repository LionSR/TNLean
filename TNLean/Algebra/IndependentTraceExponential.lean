/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.TraceExpIntegralBounds
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.Probability.Independence.Basic

/-!
# Trace-exponential bounds for independent bounded random matrices

On an actual finite product probability space, iterated integral Jensen bounds the
expected trace exponential by the trace exponential of the sum of logarithmic
moment generating functions. The marginal distributions may differ. Finite-product
integrability is derived from boundedness and continuity.

The second form starts with independent random matrices on an arbitrary probability
space. Mathlib's joint-product-law theorem identifies their joint distribution;
the integral change-of-variables formula then gives the same bound. No common
marginal distribution or supplied joint expectation identity is assumed. Matrices
carry the Borel sigma algebra of their finite-dimensional norm topology.

**Scope restriction (bounded matrices):** This is the bounded form of Tropp,
*User-friendly tail bounds for sums of random matrices*, Lemma 3.4, needed in the
Bernstein argument. The unrestricted integrable moment-generating formulation is
outside this development; see `docs/paper-gaps/finite_uniform_matrix_bernstein.tex`.
The source is:
https://tropp.caltech.edu/papers/Tro11-User-Friendly-preprint.pdf.
-/

open scoped BigOperators Matrix Matrix.Norms.L2Operator ComplexOrder MatrixOrder
open MeasureTheory

namespace Matrix

noncomputable local instance {n : Type*} [Fintype n] [DecidableEq n] :
    MeasurableSpace (Matrix n n ℂ) := borel (Matrix n n ℂ)

local instance {n : Type*} [Fintype n] [DecidableEq n] :
    BorelSpace (Matrix n n ℂ) := ⟨rfl⟩

noncomputable local instance {n : Type*} [Fintype n] [DecidableEq n] :
    NormedAlgebra ℚ (Matrix n n ℂ) := NormedAlgebra.restrictScalars ℚ ℂ _

/-- A common almost-everywhere norm bound gives the cardinality bound for the
norm of the finite sum. No independence is required. -/
theorem ae_norm_sum_le_of_forall
    {Ω n : Type*} [MeasurableSpace Ω] [Fintype n] [DecidableEq n]
    {P : Measure Ω} {m : ℕ} (X : Fin m → Ω → Matrix n n ℂ) {R : ℝ}
    (hbound : ∀ i, ∀ᵐ ω ∂P, ‖X i ω‖ ≤ R) :
    ∀ᵐ ω ∂P, ‖∑ j, X j ω‖ ≤ (m : ℝ) * R := by
  filter_upwards [ae_all_iff.mpr hbound] with ω hω
  calc
    ‖∑ j, X j ω‖ ≤ ∑ j, ‖X j ω‖ := norm_sum_le _ _
    _ ≤ ∑ _j : Fin m, R := Finset.sum_le_sum fun j _ ↦ hω j
    _ = _ := by simp [nsmul_eq_mul]

/-- The trace exponential of a finite sum of measurable bounded matrix families
is integrable on a finite measure space. No independence or Hermiticity is required. -/
theorem integrable_trace_exp_sum_of_ae_norm_le
    {Ω n : Type*} [MeasurableSpace Ω] [Fintype n] [DecidableEq n]
    {P : Measure Ω} [IsFiniteMeasure P] {m : ℕ}
    (X : Fin m → Ω → Matrix n n ℂ) (hXm : ∀ j, AEMeasurable (X j) P)
    {R : ℝ} (hbound : ∀ j, ∀ᵐ ω ∂P, ‖X j ω‖ ≤ R) (H : Matrix n n ℂ) :
    Integrable (fun ω ↦ (NormedSpace.exp (H + ∑ j, X j ω)).trace.re) P := by
  have hsummeas : AEStronglyMeasurable (fun ω ↦ ∑ j, X j ω) P :=
    by simpa only [← Finset.sum_apply] using
      Finset.aestronglyMeasurable_sum Finset.univ (fun j _ ↦ (hXm j).aestronglyMeasurable)
  have hg : Continuous (fun A : Matrix n n ℂ ↦ (NormedSpace.exp (H + A)).trace.re) :=
    Complex.continuous_re.comp (NormedSpace.exp_continuous.comp
      (continuous_const.add continuous_id)).matrix_trace
  exact integrable_continuous_comp_of_ae_norm_le hsummeas
    (ae_norm_sum_le_of_forall X hbound) hg

private theorem ae_norm_sum_pi_le
    {n : Type*} [Fintype n] [DecidableEq n] {m : ℕ}
    (μ : Fin m → Measure (Matrix n n ℂ)) [∀ i, IsProbabilityMeasure (μ i)] {R : ℝ}
    (hbound : ∀ i, ∀ᵐ X ∂μ i, ‖X‖ ≤ R) :
    ∀ᵐ σ ∂Measure.pi μ, ‖∑ j, σ j‖ ≤ (m : ℝ) * R := by
  have hcoord (i : Fin m) : ∀ᵐ σ ∂Measure.pi μ, ‖σ i‖ ≤ R :=
    Measure.tendsto_eval_ae_ae (μ := μ) (i := i) (hbound i)
  exact ae_norm_sum_le_of_forall
    (fun (j : Fin m) (σ : Fin m → Matrix n n ℂ) ↦ σ j) hcoord

private theorem ae_isHermitian_sum_pi
    {n : Type*} [Fintype n] [DecidableEq n] {m : ℕ}
    (μ : Fin m → Measure (Matrix n n ℂ)) [∀ i, IsProbabilityMeasure (μ i)]
    (hHerm : ∀ i, ∀ᵐ X ∂μ i, X.IsHermitian) :
    ∀ᵐ σ ∂Measure.pi μ, (∑ j, σ j).IsHermitian := by
  have hcoord (i : Fin m) : ∀ᵐ σ ∂Measure.pi μ, (σ i).IsHermitian :=
    Measure.tendsto_eval_ae_ae (μ := μ) (i := i) (hHerm i)
  filter_upwards [ae_all_iff.mpr hcoord] with σ hσ
  exact (isSelfAdjoint_sum Finset.univ fun j _ ↦ (hσ j).isSelfAdjoint).isHermitian

private theorem integrable_trace_exp_sum_pi
    {n : Type*} [Fintype n] [DecidableEq n] {m : ℕ}
    (μ : Fin m → Measure (Matrix n n ℂ)) [∀ i, IsProbabilityMeasure (μ i)]
    {R : ℝ} (hbound : ∀ i, ∀ᵐ X ∂μ i, ‖X‖ ≤ R) (H : Matrix n n ℂ) :
    Integrable (fun σ ↦ (NormedSpace.exp (H + ∑ j, σ j)).trace.re) (Measure.pi μ) := by
  have hcont : Continuous (fun σ : Fin m → Matrix n n ℂ ↦ ∑ j, σ j) := by fun_prop
  have hmeas : AEStronglyMeasurable (fun σ : Fin m → Matrix n n ℂ ↦ ∑ j, σ j)
      (Measure.pi μ) := hcont.aestronglyMeasurable
  have hg : Continuous (fun A : Matrix n n ℂ ↦ (NormedSpace.exp (H + A)).trace.re) :=
    Complex.continuous_re.comp (NormedSpace.exp_continuous.comp
      (continuous_const.add continuous_id)).matrix_trace
  exact integrable_continuous_comp_of_ae_norm_le hmeas (ae_norm_sum_pi_le μ hbound) hg

/-- Iterated trace-exponential Jensen on an actual product of bounded Hermitian
matrix distributions. This is the bounded product-space form of Tropp, Lemma 3.4. -/
theorem integral_trace_exp_sum_pi_le
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (m : ℕ) (μ : Fin m → Measure (Matrix n n ℂ)) [∀ i, IsProbabilityMeasure (μ i)]
    (hHerm : ∀ i, ∀ᵐ X ∂μ i, X.IsHermitian) {R : ℝ}
    (hbound : ∀ i, ∀ᵐ X ∂μ i, ‖X‖ ≤ R) {H : Matrix n n ℂ} (hH : H.IsHermitian) :
    (∫ σ, (NormedSpace.exp (H + ∑ j, σ j)).trace.re ∂Measure.pi μ) ≤
      (NormedSpace.exp (H + ∑ j, CFC.log (∫ X, NormedSpace.exp X ∂μ j))).trace.re := by
  induction m generalizing H with
  | zero => simp
  | succ m ih =>
    let ν : Fin m → Measure (Matrix n n ℂ) := fun j ↦ μ j.succ
    let M : Matrix n n ℂ := ∫ X, NormedSpace.exp X ∂μ 0
    let f : Matrix n n ℂ × (Fin m → Matrix n n ℂ) → ℝ :=
      fun p ↦ (NormedSpace.exp ((H + ∑ j, p.2 j) + p.1)).trace.re
    have hmp := (measurePreserving_piFinSuccAbove μ 0).symm
    have hf : Integrable f ((μ 0).prod (Measure.pi ν)) := by
      have hi := integrable_trace_exp_sum_pi μ hbound H
      have hh := (hmp.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)).mpr hi
      convert hh using 1
      · funext p
        dsimp [f]
        simp only [MeasurableEquiv.piFinSuccAbove_symm_apply,
          Fin.insertNthEquiv, Fin.sum_univ_succ, Fin.insertNth_zero, Equiv.coe_fn_mk,
          Fin.cons_succ, Fin.zero_succAbove, cast_eq, Fin.cons_zero]
        congr 2
        abel
      · simp only [ν, Fin.zero_succAbove]
    have hsplit : (∫ σ, (NormedSpace.exp (H + ∑ j, σ j)).trace.re ∂Measure.pi μ) =
        ∫ τ, ∫ X, (NormedSpace.exp ((H + ∑ j, τ j) + X)).trace.re ∂μ 0 ∂Measure.pi ν := by
      rw [← hmp.integral_comp']
      convert integral_prod_symm f hf using 1
      congr 1
      funext p
      dsimp [f]
      simp only [MeasurableEquiv.piFinSuccAbove_symm_apply,
        Fin.insertNthEquiv, Fin.sum_univ_succ, Fin.insertNth_zero, Equiv.coe_fn_mk,
        Fin.cons_succ, Fin.zero_succAbove, cast_eq, Fin.cons_zero]
      congr 2
      abel
    have hright : Integrable
        (fun τ ↦ (NormedSpace.exp ((H + CFC.log M) + ∑ j, τ j)).trace.re)
        (Measure.pi ν) := integrable_trace_exp_sum_pi ν (fun j ↦ hbound j.succ) _
    have hJ : ∀ᵐ τ ∂Measure.pi ν,
        (∫ X, (NormedSpace.exp ((H + ∑ j, τ j) + X)).trace.re ∂μ 0) ≤
        (NormedSpace.exp ((H + CFC.log M) + ∑ j, τ j)).trace.re := by
      filter_upwards [ae_isHermitian_sum_pi ν (fun j ↦ hHerm j.succ)] with τ hτ
      have hj := integral_trace_exp_add_le_trace_exp_log_integral_exp (hH.add hτ)
        (continuous_id.aestronglyMeasurable : AEStronglyMeasurable
          (fun X : Matrix n n ℂ ↦ X) (μ 0)) (hHerm 0) (hbound 0)
      have hadd : (H + CFC.log M) + ∑ j, τ j = (H + ∑ j, τ j) + CFC.log M := by abel
      rw [hadd]
      exact hj
    have hstep := integral_mono_ae hf.integral_prod_right hright hJ
    rw [hsplit]
    refine hstep.trans ?_
    have hh := ih (H := H + CFC.log M) ν (fun j ↦ hHerm j.succ) (fun j ↦ hbound j.succ)
      (hH.add IsSelfAdjoint.log.isHermitian)
    convert hh using 1
    apply congrArg (fun K : Matrix n n ℂ ↦ (NormedSpace.exp K).trace.re)
    rw [Fin.sum_univ_succ]
    change H + (CFC.log M + ∑ j, CFC.log (∫ X, NormedSpace.exp X ∂ν j)) =
      (H + CFC.log M) + ∑ j, CFC.log (∫ X, NormedSpace.exp X ∂ν j)
    abel

/-- The trace-exponential bound for bounded independent Hermitian random matrices
on an arbitrary probability space. This is the bounded form of Tropp, Lemma 3.4;
the actual joint product law and all required integrability are derived. -/
theorem integral_trace_exp_sum_le_of_iIndepFun
    {Ω n : Type*} [MeasurableSpace Ω] [Fintype n] [DecidableEq n] [Nonempty n]
    {P : Measure Ω} [IsProbabilityMeasure P] {m : ℕ}
    (X : Fin m → Ω → Matrix n n ℂ) (hXm : ∀ j, AEMeasurable (X j) P)
    (hIndep : ProbabilityTheory.iIndepFun X P)
    (hHerm : ∀ j, ∀ᵐ ω ∂P, (X j ω).IsHermitian) {R : ℝ}
    (hbound : ∀ j, ∀ᵐ ω ∂P, ‖X j ω‖ ≤ R) {H : Matrix n n ℂ} (hH : H.IsHermitian) :
    (∫ ω, (NormedSpace.exp (H + ∑ j, X j ω)).trace.re ∂P) ≤
      (NormedSpace.exp (H + ∑ j, CFC.log (∫ ω, NormedSpace.exp (X j ω) ∂P))).trace.re := by
  let μ (j : Fin m) := P.map (X j)
  have hμ (j : Fin m) : IsProbabilityMeasure (μ j) :=
    (Measure.isProbabilityMeasure_map_iff (hXm j)).mpr inferInstance
  let _ (j : Fin m) : IsProbabilityMeasure (μ j) := hμ j
  have hμHerm (j : Fin m) : ∀ᵐ A ∂μ j, A.IsHermitian :=
    (ae_map_iff (hXm j) (by
      simpa only [Matrix.IsHermitian, id_eq] using
        (isClosed_eq continuous_id.matrix_conjTranspose continuous_id).measurableSet)).mpr (hHerm j)
  have hμbound (j : Fin m) : ∀ᵐ A ∂μ j, ‖A‖ ≤ R :=
    (ae_map_iff (hXm j)
      (isClosed_le continuous_norm continuous_const).measurableSet).mpr (hbound j)
  have hprod := integral_trace_exp_sum_pi_le m μ hμHerm hμbound hH
  have hjoint := hIndep.map_fun_eq_pi_map hXm
  have hjmeas : AEMeasurable (fun ω j ↦ X j ω) P := .of_eval hXm
  have hG : Continuous (fun σ : Fin m → Matrix n n ℂ ↦
      (NormedSpace.exp (H + ∑ j, σ j)).trace.re) :=
    Complex.continuous_re.comp (NormedSpace.exp_continuous.comp
      (continuous_const.add (by fun_prop))).matrix_trace
  have hmap := integral_map hjmeas hG.aestronglyMeasurable
  rw [hjoint] at hmap
  calc
    _ = (∫ σ, (NormedSpace.exp (H + ∑ j, σ j)).trace.re ∂Measure.pi μ) := hmap.symm
    _ ≤ (NormedSpace.exp (H + ∑ j, CFC.log (∫ A, NormedSpace.exp A ∂μ j))).trace.re := hprod
    _ = _ := by
      congr 4
      apply Finset.sum_congr rfl
      intro j _
      dsimp [μ]
      rw [integral_map (hXm j) NormedSpace.exp_continuous.aestronglyMeasurable]

end Matrix
