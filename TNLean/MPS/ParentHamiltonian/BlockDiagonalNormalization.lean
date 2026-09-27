/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.BlockSumGroundSpace
import TNLean.MPS.ParentHamiltonian.NormalBlockPrimitiveGauges

/-!
# Parent Hamiltonians under independent block normalization

Replacing every normal block by a normalized primitive representative leaves
the local ground spaces of a weighted direct sum unchanged. Consequently,
the periodic parent Hamiltonians themselves are equal at every range and
volume. This is the normalization used before the block-injective gap
argument in Nachtergaele, arXiv:cond-mat/9410110, equations (3.1)--(3.2b),
and Section 6.
-/

open scoped ComplexOrder

namespace MPSTensor

variable {d r : ℕ} {dim : Fin r → ℕ}

/-- Equal block ground spaces give equal assembled ground spaces, independently
of the nonzero block coefficients. This follows from the local direct-sum
identity in PGVWC07, Theorem 12, proof lines 1430--1434. -/
theorem groundSpace_toTensorFromBlocks_eq_of_block_groundSpace_eq
    (μ ν : Fin r → ℂ) (A B : (j : Fin r) → MPSTensor d (dim j))
    (hμ : ∀ j, μ j ≠ 0) (hν : ∀ j, ν j ≠ 0) {L : ℕ}
    (hGS : ∀ j, groundSpace (A j) L = groundSpace (B j) L) :
    groundSpace (toTensorFromBlocks (d := d) (μ := μ) A) L =
      groundSpace (toTensorFromBlocks (d := d) (μ := ν) B) L := by
  simp only [groundSpace_toTensorFromBlocks_eq_iSup μ A hμ,
    groundSpace_toTensorFromBlocks_eq_iSup ν B hν, hGS]

/-- Independent replacements preserving the block ground spaces preserve the
periodic parent Hamiltonian. The parent interaction is the orthogonal
projection onto the complement of the local ground space, as in
Nachtergaele, arXiv:cond-mat/9410110, equation (3.12). -/
theorem parentHamiltonianES_toTensorFromBlocks_eq_of_block_groundSpace_eq
    (μ ν : Fin r → ℂ) (A B : (j : Fin r) → MPSTensor d (dim j))
    (hμ : ∀ j, μ j ≠ 0) (hν : ∀ j, ν j ≠ 0) {L : ℕ}
    (hGS : ∀ j, groundSpace (A j) L = groundSpace (B j) L) (N : ℕ) :
    parentHamiltonianES (toTensorFromBlocks (d := d) (μ := μ) A) L N =
      parentHamiltonianES (toTensorFromBlocks (d := d) (μ := ν) B) L N :=
  parentHamiltonianES_eq_of_groundSpace_eq
    (groundSpace_toTensorFromBlocks_eq_of_block_groundSpace_eq μ ν A B hμ hν hGS) N

/-- Normalizing inequivalent normal blocks preserves the entire family of
periodic parent Hamiltonians of their weighted direct sum. This is the
normalization in Nachtergaele, arXiv:cond-mat/9410110,
equations (3.1)--(3.2b), before the gap argument of Section 6. -/
theorem exists_isPrimitiveMPS_family_parentHamiltonianES_eq_of_isNormal
    [∀ j, NeZero (dim j)]
    (μ : Fin r → ℂ) (A : (j : Fin r) → MPSTensor d (dim j))
    (hμ : ∀ j, μ j ≠ 0) (hNormal : ∀ j, Kraus.IsNormal (A j))
    (hDistinct : ∀ i j, i ≠ j → ∀ h : dim j = dim i,
      ¬ GaugePhaseEquiv (h ▸ A j) (A i)) :
    ∃ (B : (j : Fin r) → MPSTensor d (dim j))
      (ρ : ∀ j, Matrix (Fin (dim j)) (Fin (dim j)) ℂ),
      (∀ j, IsPrimitiveMPS (B j) (ρ j)) ∧ (∀ j, (ρ j).PosDef) ∧
      (∀ i j, i ≠ j → ∀ h : dim j = dim i,
        ¬ GaugePhaseEquiv (h ▸ B j) (B i)) ∧
      (∀ L N, parentHamiltonianES (toTensorFromBlocks (d := d) (μ := μ) A) L N =
        parentHamiltonianES (toTensorFromBlocks (d := d) (μ := μ) B) L N) := by
  exact (exists_isPrimitiveMPS_family_of_isNormal A hNormal hDistinct).elim
    fun B ⟨ρ, hP, hρ, hGS, hDistinctB⟩ ↦
      ⟨B, ρ, hP, hρ, hDistinctB, fun L N ↦
        parentHamiltonianES_toTensorFromBlocks_eq_of_block_groundSpace_eq
          μ μ A B hμ hμ (fun j ↦ hGS j L) N⟩

end MPSTensor
