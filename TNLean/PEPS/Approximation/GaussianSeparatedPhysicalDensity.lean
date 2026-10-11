/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.GaussianPhysicalSource
import TNLean.PEPS.Approximation.SeparatedPhysicalDensity
import TNLean.PEPS.Approximation.GaussianSourceIntegrability

/-!
# Expected full physical error of separated source terms

The one-block estimate controls the full physical operator after summing the
independent affected ket and bra indices. The coefficient is the square of
the affected physical dimension; exterior and discarded dimensions do not
appear. The actual original-source Gaussian law also gives integrability.

The input frames remain explicit; their identification with the original
corrected and crossing registers is supplied by the separate construction.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 409–549.
-/

/-!
Source: September 24, 2026, polynomial-PEPS manuscript, 04-compression.tex,
eq:compression-exterior-contraction.
Manuscript revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Independently formalized; no upstream Lean proof text reused.
-/


noncomputable section
open MeasureTheory QICLean.ComplexGaussian
open scoped TensorProduct Matrix ComplexConjugate
namespace TNLean.PEPS.PairEffect.SourceCircuit

open Classical in
/-- The full separated physical operator has integrable trace norm and the
expected error is bounded by the affected physical dimension squared times
the inverse-sample factor. Every Gaussian coefficient is indexed by an
original source occurrence and its actual fixed local ket and bra labels. -/
theorem integrable_gaussianSeparatedPhysicalDensity_and_integral_le
    {P₀ : Type} {a₀ b₀ : Layout P₀} (circuit : SourceCircuit a₀ b₀)
    (k : ℕ) (hk : 0 < k) (S : Finset (sourceLocations circuit))
    (ξ ζ : ∀ e : S, branchLabels circuit e.1.1)
    (lam : ∀ e : sourceLocations circuit, branchLabels circuit e.1 →
      Fin (min (sourceDims circuit e).1 (sourceDims circuit e).2) → ℝ)
    (hnonneg : ∀ e ξ j, 0 ≤ lam e ξ j) (hmass : ∀ e ξ, ∑ j, lam e ξ j = 1)
    {P Q X Y T U d e : Type} [Fintype X] [Fintype Y] [Fintype T] [Fintype U]
    [Fintype d] [Fintype e] {a a' b : Layout P} {c c' f : Layout Q}
    {D D' : Type} [NormedAddCommGroup D] [InnerProductSpace ℂ D]
    [NormedAddCommGroup D'] [InnerProductSpace ℂ D']
    (J : Mem b ≃ₗᵢ[ℂ] EuclideanSpace ℂ X ⊗[ℂ] D)
    (v : Word a b) (w : Word a' b)
    (F : EuclideanSpace ℂ (CorrectedSchmidtCoordinates circuit S × T) →ₗᵢ[ℂ] Mem a)
    (F' : EuclideanSpace ℂ (CorrectedSchmidtCoordinates circuit S × U) →ₗᵢ[ℂ] Mem a')
    (bD : OrthonormalBasis d ℂ D) (hv : v.IsAllowed) (hw : w.IsAllowed)
    (J' : Mem f ≃ₗᵢ[ℂ] EuclideanSpace ℂ Y ⊗[ℂ] D')
    (v' : Word c f) (w' : Word c' f)
    (G : EuclideanSpace ℂ T →ₗᵢ[ℂ] Mem c)
    (G' : EuclideanSpace ℂ U →ₗᵢ[ℂ] Mem c')
    (bD' : OrthonormalBasis e ℂ D') (hv' : v'.IsAllowed) (hw' : w'.IsAllowed)
    (tau : T → ℝ) (tau' : U → ℝ)
    (htau : ∀ t, 0 ≤ tau t) (htau' : ∀ u, 0 ≤ tau' u)
    (htausum : ∑ t, tau t = 1) (htau'sum : ∑ u, tau' u = 1) :
    let z := fun (q : CorrectedSchmidtCoordinates circuit S ×
        CorrectedSchmidtCoordinates circuit S) (ω : SourceGaussianSamples circuit k) ↦
      ∏ e : S, sourceCorrection k (lam e.1 (ξ e)) (lam e.1 (ζ e))
        (ω e.1 (ξ e, ζ e)) (q.1 e) (q.2 e)
    let M := fun ω ↦ Word.separatedPhysicalDensity J v w F F' tau tau'
      J' v' w' G G' bD bD' (fun q ↦ z q ω)
    Integrable (fun ω ↦ Matrix.rectangularTraceNorm (M ω)) (sourceGaussianLaw circuit k) ∧
      (∫ ω, Matrix.rectangularTraceNorm (M ω) ∂sourceGaussianLaw circuit k) ≤
        (Fintype.card X : ℝ) ^ 2 * (k : ℝ) ^ (-(S.card : ℝ) / 2) := by
  intro z M
  let Q := fun q : CorrectedSchmidtCoordinates circuit S ×
      CorrectedSchmidtCoordinates circuit S ↦
    Matrix.partialTraceRight (Matrix.vecMulVec
      (Word.separatedPhysicalCoordinates J v F tau J' v' G bD bD' q.1)
      (fun h ↦ conj (Word.separatedPhysicalCoordinates J w F' tau' J' w' G' bD bD' q.2 h)))
  have hM (ω : SourceGaussianSamples circuit k) : M ω = ∑ q, z q ω • Q q := by
    change Matrix.partialTraceRightLM (α := X × Y) (β := d × e)
      (∑ q, z q ω • Matrix.vecMulVec
        (Word.separatedPhysicalCoordinates J v F tau J' v' G bD bD' q.1)
        (fun h ↦ conj (Word.separatedPhysicalCoordinates J w F' tau' J' w' G' bD bD' q.2 h))) = _
    simp only [map_sum, map_smul, Q, Matrix.partialTraceRightLM, LinearMap.coe_mk,
      AddHom.coe_mk]
  have hm : Integrable (fun ω ↦ Matrix.rectangularTraceNorm (M ω))
      (sourceGaussianLaw circuit k) := by
    simp_rw [hM]
    exact integrable_rectangularTraceNorm_sourceCorrectionSum circuit k hk S ξ ζ lam hnonneg Q
  have hb (x y : X) : Integrable (fun ω ↦ Matrix.rectangularTraceNorm
      ((M ω).submatrix (fun i ↦ (x, i)) (fun j ↦ (y, j))))
      (sourceGaussianLaw circuit k) := by
    have he (ω : SourceGaussianSamples circuit k) :
        (M ω).submatrix (fun i ↦ (x, i)) (fun j ↦ (y, j)) =
          ∑ q, z q ω • (Q q).submatrix (fun i ↦ (x, i)) (fun j ↦ (y, j)) := by
      rw [hM]
      ext i j
      simp only [Matrix.submatrix_apply, Matrix.sum_apply, Matrix.smul_apply]
    simp_rw [he]
    exact integrable_rectangularTraceNorm_sourceCorrectionSum circuit k hk S ξ ζ lam hnonneg _
  refine ⟨hm, (Matrix.integral_rectangularTraceNorm_le_sum_submatrix M hb).trans ?_⟩
  calc
    _ ≤ ∑ _x : X, ∑ _y : X, (k : ℝ) ^ (-(S.card : ℝ) / 2) := by
      apply Finset.sum_le_sum
      intro x _
      apply Finset.sum_le_sum
      intro y _
      simpa only [M, Word.separatedPhysicalDensity_submatrix] using
        integral_rectangularTraceNorm_gaussianPhysicalSource_le circuit k hk S ξ ζ
          lam hnonneg hmass J x y v w F F' bD hv hw J' v' w' G G' bD' hv' hw'
          tau tau' htau htau' htausum htau'sum
    _ = _ := by simp [pow_two, mul_assoc]

end TNLean.PEPS.PairEffect.SourceCircuit
