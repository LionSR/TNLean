/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.BoundaryDecompositionComparison

/-!
# Coordinate matrices of exact boundary decompositions

Collecting the separate rectangular maps gives analysis and synthesis
matrices on the full finite coordinate space. Two decompositions over a
simultaneously spanning target family have inverse full coordinate changes,
including when their supports are proper idempotents.

## References

* Garre-Rubio--Lootens--Molnár, arXiv:2203.12563v3, `rawrels`,
  `eq:F_symbol2`, and `1Fsymbol`.
-/

open scoped Matrix BigOperators

namespace MPSTensor

/-- Synthesis with the target labels and bond coordinates collected into
one finite coordinate index. -/
def decompositionSynthesis {ι : Type*} {DB : ℕ} {D : ι → ℕ}
    (W : ∀ i, Matrix (Fin DB) (Fin (D i)) ℂ) :
    Matrix (Fin DB) ((i : ι) × Fin (D i)) ℂ :=
  fun x q ↦ W q.1 x q.2

/-- Analysis with the target labels and bond coordinates collected into
one finite coordinate index. -/
def decompositionAnalysis {ι : Type*} {DB : ℕ} {D : ι → ℕ}
    (V : ∀ i, Matrix (Fin (D i)) (Fin DB) ℂ) :
    Matrix ((i : ι) × Fin (D i)) (Fin DB) ℂ :=
  fun q x ↦ V q.1 q.2 x

/-- The packed synthesis-analysis product is the sum of the individual
support idempotents. -/
theorem decompositionSynthesis_mul_analysis
    {ι : Type*} [Fintype ι] {DB : ℕ} {D : ι → ℕ}
    (W : ∀ i, Matrix (Fin DB) (Fin (D i)) ℂ)
    (V : ∀ i, Matrix (Fin (D i)) (Fin DB) ℂ) :
    decompositionSynthesis W * decompositionAnalysis V = ∑ i, W i * V i := by
  ext x y
  simp [decompositionSynthesis, decompositionAnalysis, Matrix.mul_apply,
    Matrix.sum_apply, Fintype.sum_sigma]

/-- Packed biorthogonal analysis is a left inverse to packed synthesis. -/
theorem IsBiorthogonalDecomposition.analysis_mul_synthesis
    {ι : Type*} [Fintype ι] [DecidableEq ι] {d DB : ℕ} {D : ι → ℕ}
    {B : MPSTensor d DB} {A : ∀ i, MPSTensor d (D i)}
    {V : ∀ i, Matrix (Fin (D i)) (Fin DB) ℂ}
    {W : ∀ i, Matrix (Fin DB) (Fin (D i)) ℂ}
    (h : IsBiorthogonalDecomposition B A V W) :
    decompositionAnalysis V * decompositionSynthesis W = 1 := by
  ext ⟨i, x⟩ ⟨j, y⟩
  change (V i * W j) x y =
    (1 : Matrix ((i : ι) × Fin (D i)) ((i : ι) × Fin (D i)) ℂ) ⟨i, x⟩ ⟨j, y⟩
  by_cases hij : i = j
  · subst j
    rw [h.retract]
    simp [Matrix.one_apply]
  · rw [h.orthogonal i j hij,
      Matrix.one_apply_ne (fun he ↦ hij (congrArg Sigma.fst he))]
    rfl

/-- Exact decompositions with a common simultaneous target-word span have
inverse full changes of coordinates. Their common ambient support is
derived from the tensor reconstructions. Source: GLM23 `1Fsymbol`. -/
theorem IsBiorthogonalDecomposition.fullComparison
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    {d DB r : ℕ} {dim : Fin r → ℕ}
    {B : MPSTensor d DB} {A : ∀ c, MPSTensor d (dim c)}
    {f : ι → Fin r} {g : κ → Fin r}
    {V : ∀ i, Matrix (Fin (dim (f i))) (Fin DB) ℂ}
    {W : ∀ i, Matrix (Fin DB) (Fin (dim (f i))) ℂ}
    {V' : ∀ j, Matrix (Fin (dim (g j))) (Fin DB) ℂ}
    {W' : ∀ j, Matrix (Fin DB) (Fin (dim (g j))) ℂ}
    (h : IsBiorthogonalDecomposition B (fun i ↦ A (f i)) V W)
    (h' : IsBiorthogonalDecomposition B (fun j ↦ A (g j)) V' W')
    {L : ℕ} (hL : 0 < L) (hSpan : WordTupleSpanTop A L) :
    (decompositionAnalysis V' * decompositionSynthesis W) *
        (decompositionAnalysis V * decompositionSynthesis W') = 1 ∧
      (decompositionAnalysis V * decompositionSynthesis W') *
        (decompositionAnalysis V' * decompositionSynthesis W) = 1 ∧
      decompositionSynthesis W' *
        (decompositionAnalysis V' * decompositionSynthesis W) = decompositionSynthesis W ∧
      decompositionSynthesis W *
        (decompositionAnalysis V * decompositionSynthesis W') = decompositionSynthesis W' := by
  apply Matrix.comparison_of_common_support _ _ _ _
    h.analysis_mul_synthesis h'.analysis_mul_synthesis
  rw [decompositionSynthesis_mul_analysis, decompositionSynthesis_mul_analysis]
  exact h.support_eq_of_wordTupleSpanTop h' hL hSpan

end MPSTensor
