/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.UncleParentLimit
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Injective perturbations give injective two-site uncle tensors

If the one-site matrices \(T_i=\begin{pmatrix}A_i&R_i\\L_i&B_i\end{pmatrix}\)
span the full matrix algebra,
their span contains the identity. Contracting the first physical leg of
the two-site uncle tensor with the coefficients of that identity recovers
each original one-site matrix. Consequently the uncle matrices span the
full algebra as well.

This proves the injectivity input to the existing parent-projector limit;
the limit argument itself is reused. Arbitrary diagonal perturbations do
not enter the injectivity hypothesis. No genericity assertion is made.

## References

Fernández-González et al., arXiv:1210.6613, definition of injective
perturbation and Lemma "lemma:inj-perturbation",
`Papers/1210.6613/UncleHMPS.tex`, lines 973–1016. The source treats a
block-injective background with positive block dimensions. The algebraic
implication proved here needs only the stated full perturbation span and
also holds for zero-dimensional blocks; no extra hypothesis is imposed.
-/

open scoped Matrix BigOperators Topology

namespace MPSTensor

private theorem sum_smul_uncleBlockMatrix {ι : Type*} [Fintype ι] {a b : ℕ}
    (c : ι → ℂ) (A : ι → Matrix (Fin a) (Fin a) ℂ)
    (R : ι → Matrix (Fin a) (Fin b) ℂ) (L : ι → Matrix (Fin b) (Fin a) ℂ)
    (B : ι → Matrix (Fin b) (Fin b) ℂ) :
    (∑ i, c i • uncleBlockMatrix (A i) (R i) (L i) (B i)) =
      uncleBlockMatrix (∑ i, c i • A i) (∑ i, c i • R i)
        (∑ i, c i • L i) (∑ i, c i • B i) := by
  ext x y
  obtain ⟨x, rfl⟩ := finSumFinEquiv.surjective x
  obtain ⟨y, rfl⟩ := finSumFinEquiv.surjective y
  cases x <;> cases y <;>
    simp [uncleBlockMatrix, Matrix.reindex_apply, Matrix.submatrix_apply,
      Matrix.sum_apply, Matrix.smul_apply]

private theorem uncleBlockMatrix_one {a b : ℕ} :
    uncleBlockMatrix (1 : Matrix (Fin a) (Fin a) ℂ) 0 0
      (1 : Matrix (Fin b) (Fin b) ℂ) = 1 := by
  change Matrix.reindexAlgEquiv ℂ ℂ finSumFinEquiv
    (Matrix.fromBlocks (1 : Matrix (Fin a) (Fin a) ℂ) 0 0
      (1 : Matrix (Fin b) (Fin b) ℂ)) = 1
  rw [Matrix.fromBlocks_one, map_one]

/-- An injective perturbation gives an injective uncle tensor, as in
arXiv:1210.6613, Lemma "lemma:inj-perturbation", lines 973–1016.
The full one-site perturbation span supplies identity coefficients; their
contraction with the first uncle leg recovers the full one-site family.
The algebraic implication needs no separate block-injectivity or positive
dimension assumption. -/
theorem isInjective_uncleTensor_of_isInjective_perturbation {d a b : ℕ}
    (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (L : Fin d → Matrix (Fin b) (Fin a) ℂ)
    (hPert : Kraus.IsInjective (fun i ↦ uncleBlockMatrix (A i) (R i) (L i) (B i))) :
    Kraus.IsInjective (uncleTensor A B R L) := by
  classical
  have hId : (1 : Matrix (Fin (a + b)) (Fin (a + b)) ℂ) ∈
      Submodule.span ℂ (Set.range fun i ↦ uncleBlockMatrix (A i) (R i) (L i) (B i)) := by
    rw [hPert.span_eq_top]
    exact Submodule.mem_top
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hId
  rw [sum_smul_uncleBlockMatrix, ← uncleBlockMatrix_one] at hc
  have hBlocks : (∑ i, c i • A i) = 1 ∧ (∑ i, c i • R i) = 0 ∧
      (∑ i, c i • L i) = 0 ∧ (∑ i, c i • B i) = 1 := by
    apply Matrix.fromBlocks_inj.mp
    exact (Matrix.reindexAlgEquiv ℂ ℂ finSumFinEquiv).injective hc
  obtain ⟨hA, hR, hL, hB⟩ := hBlocks
  have hContract (j : Fin d) :
      (∑ i, c i • uncleTensor A B R L ((decodeBlockEquiv d 2).symm ![i, j])) =
        uncleBlockMatrix (A j) (R j) (L j) (B j) := by
    simp only [uncleTensor, decodeBlock_decodeBlockEquiv_symm, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    rw [sum_smul_uncleBlockMatrix]
    congr 1 <;>
      simp only [smul_add, ← Matrix.smul_mul, Finset.sum_add_distrib, ← Matrix.sum_mul,
        hA, hR, hL, hB, Matrix.one_mul, Matrix.zero_mul, zero_add, add_zero]
  apply top_unique
  rw [← hPert.span_eq_top]
  apply Submodule.span_le.mpr
  rintro _ ⟨j, rfl⟩
  rw [← hContract j]
  exact Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem _ (c i)
    (Submodule.subset_span ⟨(decodeBlockEquiv d 2).symm ![i, j], rfl⟩)

/-- The source injective-perturbation condition discharges the injectivity
input of the existing two-site uncle interaction limit. Source:
arXiv:1210.6613, Lemma "lemma:inj-perturbation" and Theorem
"thm:unclehamiltonian", lines 910–1016. -/
theorem tendsto_parentInteractionES_twoBlockPerturbation_of_isInjective_perturbation
    {d a b : ℕ} (A P : MPSTensor d a) (B Q : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (L : Fin d → Matrix (Fin b) (Fin a) ℂ)
    (hPert : Kraus.IsInjective (fun i ↦ uncleBlockMatrix (A i) (R i) (L i) (B i))) :
    Filter.Tendsto (fun ε : ℂ => LinearMap.toContinuousLinearMap
      (parentInteractionES (twoBlockPerturbation A P B Q R L ε) 2))
      (𝓝[≠] 0) (𝓝 (uncleInteractionES A B R L)) :=
  tendsto_parentInteractionES_twoBlockPerturbation A P B Q R L
    (isInjective_uncleTensor_of_isInjective_perturbation A B R L hPert)

/-- The source injective-perturbation condition gives the uncle-Hamiltonian
limit at each fixed periodic length. Source: arXiv:1210.6613,
Lemma "lemma:inj-perturbation" and Theorem "thm:unclehamiltonian",
lines 910–1016. -/
theorem tendsto_parentHamiltonianES_twoBlockPerturbation_of_isInjective_perturbation
    {d a b : ℕ} (A P : MPSTensor d a) (B Q : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (L : Fin d → Matrix (Fin b) (Fin a) ℂ)
    (hPert : Kraus.IsInjective (fun i ↦ uncleBlockMatrix (A i) (R i) (L i) (B i)))
    {N : ℕ} (hN : 2 ≤ N) :
    Filter.Tendsto (fun ε : ℂ => LinearMap.toContinuousLinearMap
      (parentHamiltonianES (twoBlockPerturbation A P B Q R L ε) 2 N))
      (𝓝[≠] 0) (𝓝 (uncleHamiltonianES A B R L N)) :=
  tendsto_parentHamiltonianES_twoBlockPerturbation A P B Q R L
    (isInjective_uncleTensor_of_isInjective_perturbation A B R L hPert) hN

end MPSTensor
