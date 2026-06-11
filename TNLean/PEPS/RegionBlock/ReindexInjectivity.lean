import TNLean.PEPS.RegionBlock.Insertion

/-!
# Blocked-region injectivity transports along a bond-dimension reindex

The final comparison of the normal PEPS Fundamental Theorem reads the gauge-absorbed second
tensor over the first tensor's bonds (`reindexTensor`).  This file records that the
bond-dimension reindex preserves blocked-region linear independence: the blocked family of the
reindexed tensor is the original family precomposed with the boundary-configuration cast
bijection, and linear independence is invariant under reindexing the index type
(arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1519--1571 of
`Papers/1804.04964/paper_normal.tex`).

## References

* [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected entangled pair states
  generating the same state*, arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1519--1571
  of `Papers/1804.04964/paper_normal.tex`](https://arxiv.org/abs/1804.04964)
-/

open scoped BigOperators

namespace TNLean
namespace PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ}

/-- The boundary configurations of a reindexed tensor correspond to those of the original tensor
by casting every open leg across the bond-dimension equality. -/
noncomputable def regionBoundaryConfigCastEquiv (T : Tensor G d) {bd : Edge G → ℕ}
    (h : bd = T.bondDim) (R : Finset V) :
    RegionBoundaryConfig (G := G) (reindexTensor (G := G) T h) R ≃
      RegionBoundaryConfig (G := G) T R where
  toFun bdry := fun f => Fin.cast (congr_fun h f.1) (bdry f)
  invFun bdry := fun f => Fin.cast (congr_fun h f.1).symm (bdry f)
  left_inv bdry := by
    funext f
    apply Fin.eq_of_val_eq
    simp
  right_inv bdry := by
    funext f
    apply Fin.eq_of_val_eq
    simp

/-- **A bond-dimension reindex preserves blocked-region linear independence.**

If the blocked family of `T` over `R` is linearly independent, so is the blocked family of the
reindexed tensor: the latter is the former precomposed with the boundary-configuration cast
bijection.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1519--1571 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem regionBlockedTensorInjective_reindexTensor (T : Tensor G d) {bd : Edge G → ℕ}
    (h : bd = T.bondDim) (R : Finset V)
    (hT : RegionBlockedTensorInjective (G := G) T R) :
    RegionBlockedTensorInjective (G := G) (reindexTensor (G := G) T h) R := by
  rw [RegionBlockedTensorInjective] at hT ⊢
  have hfam : regionBlockedTensorFamily (G := G) (reindexTensor (G := G) T h) R =
      regionBlockedTensorFamily (G := G) T R ∘ (regionBoundaryConfigCastEquiv T h R) := by
    funext bdry τ
    exact regionBlockedWeight_reindexTensor (G := G) T h R bdry τ
  rw [hfam]
  exact (linearIndependent_equiv (regionBoundaryConfigCastEquiv T h R)).mpr hT

end PEPS
end TNLean
