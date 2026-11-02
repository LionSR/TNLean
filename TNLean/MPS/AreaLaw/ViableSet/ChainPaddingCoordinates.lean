/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ViableSet.ChainPadding
import TNLean.MPS.AreaLaw.ViableSet.PrefixColumn

/-!
# Tensor coordinates of the actual padded Hamiltonian

The original embedded sum acts on the prefix factor. The actual sum of
appended-site penalties acts on its complement. The supported-operator
factorization identifies these matrices in the same cut coordinates used
for viable-set columns.

Source: algebraic product-ancilla accuracy reduction for LVV13,
arXiv:1307.5143v1, final induction, lines 652--678.
-/

open Matrix
open scoped BigOperators InnerProductSpace ComplexOrder MatrixOrder Kronecker

namespace TNLean.MPS.AreaLaw

/-- Restricting a glued configuration to the original sites gives its left
configuration in the original chain numbering. -/
theorem restrict_prefix_cutEquiv_symm {L N q : ℕ} (hi : L ≤ N)
    (a : Entropy.RegionConfig (fun _ : Fin N ↦ q) (leftBlock N L))
    (b : (v : {v : Fin N // v ∉ leftBlock N L}) → Fin q) :
    ((Entropy.cutEquiv (fun _ : Fin N ↦ q) (leftBlock N L)).symm (a, b)) ∘ Fin.castLE hi =
      (leftConfigOfFinEquiv hi).symm a := by
  funext v
  rw [Function.comp_apply, Entropy.cutEquiv_symm_apply_mem _ _
    (show Fin.castLE hi v ∈ leftBlock N L from mem_leftBlock.mpr v.isLt)]
  rfl

/-- In the prefix cut coordinates the actually placed old operator is its
original-coordinate relabelling tensored with the identity. The right basis
configuration specifies the slice used by the supported-operator factorization. -/
theorem cutOperator_embedOp_prefix {L N q : ℕ} (hi : L ≤ N)
    (b0 : (v : {v : Fin N // v ∉ leftBlock N L}) → Fin q)
    (X : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) :
    Entropy.cutOperator (n := fun _ : Fin N ↦ q) (leftBlock N L)
      (QuantumCircuit.embedOp (Fin.castLE hi) X) =
      Matrix.reindex (leftConfigOfFinEquiv hi) (leftConfigOfFinEquiv hi) X ⊗ₖ 1 := by
  classical
  have hrange : Set.range (Fin.castLE hi) = (leftBlock N L : Set (Fin N)) := by
    ext v
    constructor
    · rintro ⟨w, rfl⟩
      exact mem_leftBlock.mpr w.isLt
    · intro hv
      exact ⟨⟨v.val, mem_leftBlock.mp hv⟩, Fin.ext rfl⟩
  have hmem : QuantumCircuit.embedOp (Fin.castLE hi) X ∈
      QuantumCircuit.supportedOperators q (leftBlock N L : Set (Fin N)) := by
    simpa only [hrange] using
      QuantumCircuit.embedOp_mem_supportedOperators (Fin.castLE_injective hi) X
  have hs := QuantumCircuit.isSupportedOn_of_mem_supportedOperators hmem
  rw [hs.cutOperator_eq_kronecker_one (le_refl _) b0]
  congr 1
  ext a a'
  change QuantumCircuit.embedOp (Fin.castLE hi) X
    ((Entropy.cutEquiv (fun _ : Fin N ↦ q) (leftBlock N L)).symm (a, b0))
    ((Entropy.cutEquiv (fun _ : Fin N ↦ q) (leftBlock N L)).symm (a', b0)) =
      X ((leftConfigOfFinEquiv hi).symm a) ((leftConfigOfFinEquiv hi).symm a')
  have hoff : QuantumCircuit.AgreeOff (Fin.castLE hi)
      ((Entropy.cutEquiv (fun _ : Fin N ↦ q) (leftBlock N L)).symm (a, b0))
      ((Entropy.cutEquiv (fun _ : Fin N ↦ q) (leftBlock N L)).symm (a', b0)) := by
    intro v hv
    have hvB : v ∉ leftBlock N L := by
      intro h
      exact hv ⟨v.val, mem_leftBlock.mp h⟩ (Fin.ext rfl)
    rw [Entropy.cutEquiv_symm_apply_not_mem _ _ hvB,
      Entropy.cutEquiv_symm_apply_not_mem _ _ hvB]
  rw [QuantumCircuit.embedOp_apply, ite_eq_left hoff,
    restrict_prefix_cutEquiv_symm hi a b0, restrict_prefix_cutEquiv_symm hi a' b0]

/-- The actual sum of appended-site penalties acts on the complementary
factor as the corresponding product-basis penalty. -/
theorem cutOperator_appended_penalty {L N q : ℕ} (z : Fin q)
    (a0 : Entropy.RegionConfig (fun _ : Fin N ↦ q) (leftBlock N L)) :
    Entropy.cutOperator (n := fun _ : Fin N ↦ q) (leftBlock N L)
      (∑ v : {v : Fin N // v ∉ leftBlock N L},
        QuantumCircuit.siteOp v.val (QuantumCircuit.siteBasisPenalty z)) =
      (1 : Matrix _ _ ℂ) ⊗ₖ QuantumCircuit.productBasisPenalty
        (fun _ : {v : Fin N // v ∉ leftBlock N L} ↦ z) := by
  classical
  have hmem : (∑ v : {v : Fin N // v ∉ leftBlock N L},
        QuantumCircuit.siteOp v.val (QuantumCircuit.siteBasisPenalty z)) ∈
      QuantumCircuit.supportedOperators q (↑((leftBlock N L)ᶜ) : Set (Fin N)) := by
    apply Submodule.sum_mem
    intro v _
    apply QuantumCircuit.supportedOperators_mono _
      (QuantumCircuit.siteOp_mem_supportedOperators v.val _)
    exact Set.singleton_subset_iff.mpr (Finset.mem_compl.mpr v.property)
  have hs := QuantumCircuit.isSupportedOn_of_mem_supportedOperators hmem
  rw [hs.cutOperator_eq_one_kronecker disjoint_compl_left a0]
  congr 1
  rw [QuantumCircuit.productBasisPenalty_eq_diagonal]
  ext b b'
  simp only [Entropy.cutOperator, Matrix.reindex_apply, Matrix.submatrix_apply,
    Matrix.sum_apply, QuantumCircuit.siteBasisPenalty, QuantumCircuit.siteOp_diagonal]
  by_cases hbb : b = b'
  · subst b'
    simp only [diagonal_apply_eq]
    apply Finset.sum_congr rfl
    intro v _
    rw [Entropy.cutEquiv_symm_apply_not_mem _ _ v.property]
  · have hglue : (Entropy.cutEquiv (fun _ : Fin N ↦ q) (leftBlock N L)).symm (a0, b) ≠
        (Entropy.cutEquiv (fun _ : Fin N ↦ q) (leftBlock N L)).symm (a0, b') := by
      intro heq
      exact hbb (congrArg Prod.snd
        ((Entropy.cutEquiv (fun _ : Fin N ↦ q) (leftBlock N L)).symm.injective heq))
    simp only [diagonal_apply_ne _ hglue, diagonal_apply_ne _ hbb, Finset.sum_const_zero]

end TNLean.MPS.AreaLaw
