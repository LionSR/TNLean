/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.QCA.BipartiteSupportAlgebra
import QICLean.Algebra.SkolemNoetherUnitary

/-!
# Reindexing the factors of a finite support algebra

Independent coordinate equivalences on the two factors transport the
least left support algebra by the corresponding first-factor equivalence.
This identifies a computed finite MPU support factor with the same
canonical QCA factor in its integer-site configuration coordinates.

Source context: GNVW, arXiv:0910.3675v2, support-algebra Lemma 7;
arXiv:1703.09188, Appendix, lines 2322–2334.
-/

namespace Matrix

variable {m n m' n' : Type*} [Fintype m] [Fintype n] [Fintype m'] [Fintype n']
  [DecidableEq m] [DecidableEq n] [DecidableEq m'] [DecidableEq n']

/-- The least left support algebra is independent of independent
coordinate choices on its two finite factors. Source context:
arXiv:1703.09188, Appendix support factors, lines 2322–2334. -/
theorem leftSupportAlgebra_map_matrixReindexStarAlgEquiv
    (A : StarSubalgebra ℂ (Matrix (m × n) (m × n) ℂ)) (e : m ≃ m') (f : n ≃ n') :
    leftSupportAlgebra (A.map (matrixReindexStarAlgEquiv (e.prodCongr f)).toStarAlgHom) =
      (leftSupportAlgebra A).map (matrixReindexStarAlgEquiv e).toStarAlgHom := by
  apply le_antisymm
  · apply (left_support_algebra_le_iff _ _).mpr
    intro X hX i j
    obtain ⟨Y, hY, rfl⟩ := hX
    change bipartiteSlice (Matrix.reindex (e.prodCongr f) (e.prodCongr f) Y) i j ∈ _
    rw [bipartiteSlice_reindex_prod]
    exact ⟨_, bipartite_slice_mem_left_support_algebra A hY (f.symm i) (f.symm j), rfl⟩
  · apply StarSubalgebra.map_le_iff_le_comap.mpr
    apply (left_support_algebra_le_iff _ _).mpr
    intro X hX i j
    change (matrixReindexStarAlgEquiv e) (bipartiteSlice X i j) ∈
      leftSupportAlgebra (A.map (matrixReindexStarAlgEquiv (e.prodCongr f)).toStarAlgHom)
    have h := bipartite_slice_mem_left_support_algebra
      (A.map (matrixReindexStarAlgEquiv (e.prodCongr f)).toStarAlgHom)
      (show (matrixReindexStarAlgEquiv (e.prodCongr f)) X ∈
        A.map (matrixReindexStarAlgEquiv (e.prodCongr f)).toStarAlgHom from ⟨X, hX, rfl⟩)
      (f i) (f j)
    change bipartiteSlice (Matrix.reindex (e.prodCongr f) (e.prodCongr f) X) (f i) (f j) ∈ _ at h
    simp only [bipartiteSlice_reindex_prod, Equiv.symm_apply_apply] at h
    exact h

end Matrix
