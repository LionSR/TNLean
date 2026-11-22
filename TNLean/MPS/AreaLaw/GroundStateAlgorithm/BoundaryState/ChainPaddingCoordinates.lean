/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.GroundStateAlgorithm.BoundaryState.ChainPadding
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
    (a : (ManyBody.RegionConfig (fun _ ↦ Fin q) (leftBlock N L)))
    (b : (v : {v : Fin N // v ∉ leftBlock N L}) → Fin q) :
    ((ManyBody.cutEquiv (fun _ ↦ Fin q) (leftBlock N L)).symm (a, b)) ∘ Fin.castLE hi =
      (leftConfigOfFinEquiv hi).symm a := by
  funext v
  rw [Function.comp_apply, ManyBody.cutEquiv_symm_apply_mem _ _
    (show Fin.castLE hi v ∈ leftBlock N L from mem_leftBlock.mpr v.isLt)]
  rfl

/-- In the prefix cut coordinates the actually placed old operator is its
original-coordinate relabelling tensored with the identity. The right basis
configuration specifies the slice used by the supported-operator factorization. -/
theorem cutOperator_placeAlong_castLEEmb {L N q : ℕ} (hi : L ≤ N)
    (b0 : (v : {v : Fin N // v ∉ leftBlock N L}) → Fin q)
    (X : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) :
    ManyBody.cutOperator (X := fun _ ↦ Fin q) (leftBlock N L)
      (ManyBody.placeAlong (X := fun _ ↦ Fin q) (Fin.castLEEmb hi) X) =
      Matrix.reindex (leftConfigOfFinEquiv hi) (leftConfigOfFinEquiv hi) X ⊗ₖ 1 := by
  classical
  have hmap : Finset.univ.map (Fin.castLEEmb hi) = leftBlock N L := by
    ext v
    simp only [Finset.mem_map, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨w, rfl⟩
      exact mem_leftBlock.mpr w.isLt
    · intro hv
      exact ⟨⟨v.val, mem_leftBlock.mp hv⟩, Fin.ext rfl⟩
  have hmem : ManyBody.placeAlong (X := fun _ ↦ Fin q) (Fin.castLEEmb hi) X ∈
      ManyBody.supportedOperators (fun _ ↦ Fin q) (leftBlock N L : Finset (Fin N)) := by
    rw [← hmap]
    exact ManyBody.placeAlong_mem_supportedOperators (X := fun _ ↦ Fin q) (Fin.castLEEmb hi) X
  rw [ManyBody.IsSupportedOn.cutOperator_eq_kronecker_one hmem (le_refl _) b0]
  congr 1
  ext a a'
  change ManyBody.placeAlong (X := fun _ ↦ Fin q) (Fin.castLEEmb hi) X
    ((ManyBody.cutEquiv (fun _ ↦ Fin q) (leftBlock N L)).symm (a, b0))
    ((ManyBody.cutEquiv (fun _ ↦ Fin q) (leftBlock N L)).symm (a', b0)) =
      X ((leftConfigOfFinEquiv hi).symm a) ((leftConfigOfFinEquiv hi).symm a')
  have hoff : ∀ v, (∀ u, Fin.castLEEmb hi u ≠ v) →
      (ManyBody.cutEquiv (fun _ ↦ Fin q) (leftBlock N L)).symm (a, b0) v =
        (ManyBody.cutEquiv (fun _ ↦ Fin q) (leftBlock N L)).symm (a', b0) v := by
    intro v hv
    have hvB : v ∉ leftBlock N L := by
      intro h
      exact hv ⟨v.val, mem_leftBlock.mp h⟩ (Fin.ext rfl)
    rw [ManyBody.cutEquiv_symm_apply_not_mem _ _ hvB,
      ManyBody.cutEquiv_symm_apply_not_mem _ _ hvB]
  rw [ManyBody.placeAlong_apply, ite_eq_left hoff]
  exact congrArg₂ X (restrict_prefix_cutEquiv_symm hi a b0)
    (restrict_prefix_cutEquiv_symm hi a' b0)

/-- The actual sum of appended-site penalties acts on the complementary
factor as the corresponding product-basis penalty. -/
theorem cutOperator_appended_penalty {L N q : ℕ} (z : Fin q)
    (a0 : (ManyBody.RegionConfig (fun _ ↦ Fin q) (leftBlock N L))) :
    ManyBody.cutOperator (X := fun _ ↦ Fin q) (leftBlock N L)
      (∑ v : {v : Fin N // v ∉ leftBlock N L},
        ManyBody.placeAt (X := fun _ ↦ Fin q) v.val (ManyBody.siteBasisPenalty z)) =
      (1 : Matrix _ _ ℂ) ⊗ₖ ManyBody.productBasisPenalty
        (fun _ : {v : Fin N // v ∉ leftBlock N L} ↦ z) := by
  have hdiag (t : Fin N) (f : Fin q → ℂ) :
      ManyBody.placeAt (X := fun _ ↦ Fin q) t (diagonal f) =
        diagonal fun x : Fin N → Fin q ↦ f (x t) := by
    ext x y
    rw [ManyBody.placeAt_apply, diagonal_apply, diagonal_apply]
    by_cases hxy : x = y
    · subst hxy
      simp
    · rw [ite_eq_right hxy]
      split_ifs with h1 h2
      · refine absurd (funext fun u ↦ ?_) hxy
        by_cases hu : u = t
        · subst hu
          exact h2
        · exact h1 u hu
      · rfl
      · rfl
  classical
  have hmem : (∑ v : {v : Fin N // v ∉ leftBlock N L},
        ManyBody.placeAt (X := fun _ ↦ Fin q) v.val (ManyBody.siteBasisPenalty z)) ∈
      ManyBody.supportedOperators (fun _ ↦ Fin q) ((leftBlock N L)ᶜ : Finset (Fin N)) := by
    apply sum_mem
    intro v _
    apply ManyBody.supportedOperators_mono _
      (ManyBody.placeAt_mem_supportedOperators (X := fun _ ↦ Fin q) v.val _)
    exact Finset.singleton_subset_iff.mpr (Finset.mem_compl.mpr v.property)
  rw [ManyBody.IsSupportedOn.cutOperator_eq_one_kronecker hmem disjoint_compl_left a0]
  congr 1
  rw [ManyBody.productBasisPenalty_eq_diagonal]
  ext b b'
  simp only [ManyBody.cutOperator, Matrix.reindex_apply, Matrix.submatrix_apply,
    Matrix.sum_apply, ManyBody.siteBasisPenalty, hdiag]
  by_cases hbb : b = b'
  · subst b'
    simp only [diagonal_apply_eq]
    apply Finset.sum_congr rfl
    intro v _
    rw [ManyBody.cutEquiv_symm_apply_not_mem _ _ v.property]
  · have hglue : (ManyBody.cutEquiv (fun _ ↦ Fin q) (leftBlock N L)).symm (a0, b) ≠
        (ManyBody.cutEquiv (fun _ ↦ Fin q) (leftBlock N L)).symm (a0, b') := by
      intro heq
      exact hbb (congrArg Prod.snd
        ((ManyBody.cutEquiv (fun _ ↦ Fin q) (leftBlock N L)).symm.injective heq))
    simp only [diagonal_apply_ne _ hglue, diagonal_apply_ne _ hbb, Finset.sum_const_zero]

end TNLean.MPS.AreaLaw
