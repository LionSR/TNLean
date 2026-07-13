/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.Core.BlockingInfrastructure
import TNLean.MPS.SharedInfra.SectorDecomposition

/-!
# Physical blocking of sector decompositions

This file packages physical blocking for a BNT sector decomposition.  Blocking
by `p` sites leaves the representative and copy indices unchanged, replaces
each representative `A_j` by `A_j^[p]`, and replaces each copy weight
`μ_{j,q}` by `μ_{j,q}^p`.

The two-layer representative and copy-weight structure comes from
arXiv:1606.00608, `eq:II_ABasicTensors` and `decBSV`, lines 283--301.  Physical
blocking of this structure is an auxiliary construction for the planned formal
proof of Appendix C.3, Lemma L, lines 1835--1858; it is not a separate
construction stated there.  This file does not assert that the full predicate
`IsBNTCanonicalForm` is preserved by blocking, since that requires separate
proofs for representative distinctness and eventual linear independence.

## Main results

* `SectorDecomposition.blockTensor` is the sector decomposition obtained by
  physical blocking.
* `SectorDecomposition.coeff_blockTensor` identifies its coefficient with the
  original coefficient at the corresponding unblocked length.
* `SectorDecomposition.sameMPV₂_blockTensor_toTensor` proves that assembling
  the blocked decomposition gives the same MPV family as blocking the assembled
  tensor.
-/

open scoped Matrix BigOperators

namespace MPSTensor.SectorDecomposition

variable {d : ℕ}

/-- The sector decomposition obtained by blocking `p` physical sites.

The representative family becomes `A_j^[p]`, while every copy weight becomes
`μ_{j,q}^p`.  The underlying two-layer decomposition is
arXiv:1606.00608, `eq:II_ABasicTensors` and `decBSV`, lines 283--301.  The
blocked form is an auxiliary construction for the planned formal proof of
Appendix C.3, Lemma L, lines 1835--1858. -/
noncomputable def blockTensor (P : SectorDecomposition d) (p : ℕ) :
    SectorDecomposition (blockPhysDim d p) where
  basisCount := P.basisCount
  basisDim := P.basisDim
  basis := fun j ↦ MPSTensor.blockTensor (P.basis j) p
  sectors :=
    { copies := P.copies
      copies_pos := P.copies_pos
      weight := fun j q ↦ (P.weight j q) ^ p
      weight_ne_zero := fun j q ↦ pow_ne_zero p (P.weight_ne_zero j q) }

@[simp]
theorem blockTensor_basis (P : SectorDecomposition d) (p : ℕ)
    (j : Fin P.basisCount) :
    (P.blockTensor p).basis j = MPSTensor.blockTensor (P.basis j) p :=
  rfl

@[simp]
theorem blockTensor_weight (P : SectorDecomposition d) (p : ℕ)
    (j : Fin P.basisCount) (q : Fin (P.copies j)) :
    (P.blockTensor p).weight j q = (P.weight j q) ^ p :=
  rfl

@[simp]
theorem blockTensor_copies (P : SectorDecomposition d) (p : ℕ) :
    (P.blockTensor p).copies = P.copies :=
  rfl

@[simp]
theorem blockTensor_totalCopies (P : SectorDecomposition d) (p : ℕ) :
    (P.blockTensor p).totalCopies = P.totalCopies :=
  rfl

@[simp]
theorem blockTensor_flatDim (P : SectorDecomposition d) (p : ℕ) :
    (P.blockTensor p).flatDim = P.flatDim :=
  rfl

@[simp]
theorem blockTensor_totalDim (P : SectorDecomposition d) (p : ℕ) :
    (P.blockTensor p).totalDim = P.totalDim :=
  rfl

@[simp]
theorem blockTensor_flatWeight (P : SectorDecomposition d) (p : ℕ)
    (s : Fin P.totalCopies) :
    (P.blockTensor p).flatWeight s = (P.flatWeight s) ^ p :=
  rfl

@[simp]
theorem blockTensor_flatBasis (P : SectorDecomposition d) (p : ℕ)
    (s : Fin P.totalCopies) :
    (P.blockTensor p).flatBasis s = MPSTensor.blockTensor (P.flatBasis s) p :=
  rfl

/-- The coefficient of the blocked decomposition at length `N` is the
coefficient of the original decomposition at length `N * p`.

This is the copy-weight identity
`∑_q (μ_{j,q}^p)^N = ∑_q μ_{j,q}^{Np}` for the two-layer coefficients in
arXiv:1606.00608, `eq:II_ABasicTensors` and `decBSV`, lines 283--301.  It is an
auxiliary identity for the planned formal proof of Appendix C.3, Lemma L,
lines 1835--1858. -/
theorem coeff_blockTensor (P : SectorDecomposition d) (p N : ℕ)
    (j : Fin P.basisCount) :
    (P.blockTensor p).coeff N j = P.coeff (N * p) j := by
  change (∑ q : Fin (P.copies j), ((P.weight j q) ^ p) ^ N) =
    ∑ q : Fin (P.copies j), (P.weight j q) ^ (N * p)
  rw [Nat.mul_comm N p]
  simp only [pow_mul]

/-- Blocking the tensor assembled from a sector decomposition gives the same
MPV family as assembling its blocked representatives with powered copy
weights.

The two-layer expansion is arXiv:1606.00608, `eq:II_ABasicTensors` and
`decBSV`, lines 283--301.  This blocked form is an auxiliary identity for the
planned formal proof of Appendix C.3, Lemma L, lines 1835--1858. -/
theorem sameMPV₂_blockTensor_toTensor (P : SectorDecomposition d) (p : ℕ) :
    SameMPV₂
      (MPSTensor.blockTensor P.toTensor p)
      (P.blockTensor p).toTensor := by
  change SameMPV₂
    (MPSTensor.blockTensor
      (toTensorFromBlocks (d := d) P.flatWeight P.flatBasis) p)
    (toTensorFromBlocks (d := blockPhysDim d p)
      (fun s ↦ (P.flatWeight s) ^ p)
      (fun s ↦ MPSTensor.blockTensor (P.flatBasis s) p))
  exact sameMPV₂_blockTensor_toTensorFromBlocks P.flatWeight P.flatBasis p

end MPSTensor.SectorDecomposition
