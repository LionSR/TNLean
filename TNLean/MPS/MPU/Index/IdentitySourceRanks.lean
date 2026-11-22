/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Operator.Unitary.Identity
import TNLean.MPS.Operator.Unitary.SourceCuts
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Source cuts and ranks of the identity tensor

Both source cuts are identity matrices after removing the unique bond coordinate. Their
ranks equal the physical dimension, including when that dimension is zero.
-/

namespace MPOTensor

/-- Both source cuts of the bond-one identity tensor are the identity after
removing their unique virtual coordinates.

Formalization identity used to realize equation `eq:SF_u1_u3` in
arXiv:1703.09188, lines 2009--2016; the paper does not state this intermediate
source-cut formula. -/
theorem sourceCutM₁_identityMPUTensor (d : ℕ) :
    sourceCutM₁ (identityMPUTensor d) =
      Matrix.reindex (Equiv.prodUnique (Fin d) (Fin 1)).symm
        (Equiv.uniqueProd (Fin d) (Fin 1)).symm
        (1 : Matrix (Fin d) (Fin d) ℂ) := by
  ext ⟨i, β⟩ ⟨α, j⟩
  have hαβ : α = β := Subsingleton.elim _ _
  by_cases hij : i = j
  · simp [sourceCutM₁, identityMPUTensor, idTensor, Matrix.reindex_apply,
      Matrix.one_apply, hij, hαβ]
  · simp [sourceCutM₁, identityMPUTensor, idTensor, Matrix.reindex_apply,
      hij, hαβ]

/-- The second source cut of the bond-one identity tensor is the same
reindexed identity as its first source cut.

Formalization identity used to realize equation `eq:SF_u1_u3` in
arXiv:1703.09188, lines 2009--2016; the paper does not state this intermediate
source-cut formula. -/
theorem sourceCutM₂_identityMPUTensor (d : ℕ) :
    sourceCutM₂ (identityMPUTensor d) =
      Matrix.reindex (Equiv.uniqueProd (Fin d) (Fin 1)).symm
        (Equiv.prodUnique (Fin d) (Fin 1)).symm
        (1 : Matrix (Fin d) (Fin d) ℂ) := by
  ext ⟨α, i⟩ ⟨j, β⟩
  have hαβ : α = β := Subsingleton.elim _ _
  by_cases hij : i = j <;>
    simp [sourceCutM₂, identityMPUTensor, idTensor, Matrix.reindex_apply,
      Matrix.one_apply, hij, hαβ]

/-- The right source rank of the bond-one identity tensor is its physical
dimension.

Formalization rank identity used to realize equation `eq:SF_u1_u3` in
arXiv:1703.09188, lines 2009--2016; the paper does not state this intermediate
identity. -/
theorem rightRank_identityMPUTensor (d : ℕ) :
    r[identityMPUTensor d] = d := by
  rw [rightRank, sourceCutM₁_identityMPUTensor, Matrix.rank_reindex,
    Matrix.rank_one]
  simp

/-- The left source rank of the bond-one identity tensor is its physical
dimension.

Formalization rank identity used to realize equation `eq:SF_u1_u3` in
arXiv:1703.09188, lines 2009--2016; the paper does not state this intermediate
identity. -/
theorem leftRank_identityMPUTensor (d : ℕ) :
    ℓ[identityMPUTensor d] = d := by
  rw [leftRank, sourceCutM₂_identityMPUTensor, Matrix.rank_reindex,
    Matrix.rank_one]
  simp

end MPOTensor
