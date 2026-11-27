/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.CanonicalForm.NormalBlocks.Blocking
import TNLean.MPS.Transfer.Irreducible.PhysicalReindexTransport
import TNLean.MPS.CanonicalForm.BNTPresentation.LeftCanonical

/-!
# Physical blocking of sector decompositions

This file packages physical blocking for a BNT sector decomposition.  Blocking
by `p` sites leaves the representative and copy indices unchanged, replaces
each representative `A_j` by `A_j^[p]`, and replaces each copy weight
`μ_{j,q}` by `μ_{j,q}^p`.

The two-layer representative and copy-weight structure comes from
arXiv:1606.00608, `eq:II_ABasicTensors` and `decBSV`, lines 283--301.  Physical
blocking of this structure is an auxiliary construction used in Appendix C.3,
Lemma L, lines 1835--1858; it is not a separate construction stated there.
Positive blocking preserves the presentation in left-canonical gauge
`IsLeftCanonicalBNTPresentation`.

## Main results

* `SectorDecomposition.blockTensor` is the sector decomposition obtained by
  physical blocking.
* `SectorDecomposition.coeff_blockTensor` identifies its coefficient with the
  original coefficient at the corresponding unblocked length.
* `SectorDecomposition.sameMPV₂_blockTensor_toTensor` proves that assembling
  the blocked decomposition gives the same MPV family as blocking the assembled
  tensor.
* Positive physical blocking preserves BNT canonical form.
-/

open MPTensor

open scoped Matrix BigOperators
open Filter
open Kraus (blockPhysDim length_wordOfBlock evalWord_blockTensor)

namespace MPSTensor.SectorDecomposition

variable {d : ℕ}

section ReindexPhysical

variable {α α' : Type*}

/-- Reindex the physical alphabet of every representative in a sector
decomposition. The representative labels, multiplicities, weights, and bond
dimensions are unchanged.

Source: arXiv:1606.00608, the harmless physical-basis identifications used in
the canonical-form blocking at lines 317--345. -/
noncomputable def reindexPhysical (P : SectorDecomposition α)
    (e : α' ≃ α) : SectorDecomposition α' where
  basisCount := P.basisCount
  basisDim := P.basisDim
  basis := fun j ↦ Kraus.reindexPhysical e (P.basis j)
  sectors := P.sectors

@[simp]
theorem reindexPhysical_basis (P : SectorDecomposition α)
    (e : α' ≃ α) (j : Fin P.basisCount) :
    (P.reindexPhysical e).basis j = Kraus.reindexPhysical e (P.basis j) :=
  rfl

@[simp]
theorem reindexPhysical_totalDim (P : SectorDecomposition α)
    (e : α' ≃ α) :
    (P.reindexPhysical e).totalDim = P.totalDim :=
  rfl

@[simp]
theorem reindexPhysical_totalCopies (P : SectorDecomposition α)
    (e : α' ≃ α) :
    (P.reindexPhysical e).totalCopies = P.totalCopies :=
  rfl

@[simp]
theorem reindexPhysical_flatDim (P : SectorDecomposition α)
    (e : α' ≃ α) (s : Fin P.totalCopies) :
    (P.reindexPhysical e).flatDim s = P.flatDim s :=
  rfl

/-- Assembling a physically reindexed sector decomposition is the same as
physically reindexing its assembled tensor.

Source: arXiv:1606.00608, canonical-form blocking at lines 317--345. -/
theorem reindexPhysical_toTensor (P : SectorDecomposition α)
    (e : α' ≃ α) :
    (P.reindexPhysical e).toTensor = Kraus.reindexPhysical e P.toTensor :=
  rfl

/-- A bijective relabelling of the physical alphabet preserves BNT canonical
form.

Source: arXiv:1606.00608, the physical-basis identifications implicit in the
blocking passage at lines 317--345. -/
theorem IsLeftCanonicalBNTPresentation.reindexPhysical {d' : ℕ}
    {P : SectorDecomposition (Fin d)} (hCF : IsLeftCanonicalBNTPresentation P)
    (e : Fin d' ≃ Fin d) :
    IsLeftCanonicalBNTPresentation (P.reindexPhysical e) := by
  refine IsLeftCanonicalBNTPresentation.of_irreducible_selfOverlap
    hCF.basisCount_pos hCF.basis_dim_pos
    (fun j ↦ (Kraus.isIrreducibleFamily_reindexPhysical_equiv e (P.basis j)).2
      (hCF.basis_irreducible j))
    (fun j ↦ (Kraus.isTP_reindexPhysical_iff e (P.basis j)).2 (hCF.basis_left_canonical j))
    ?_ ?_
  · change ∀ j : Fin P.basisCount,
      Tendsto (fun N : ℕ ↦ mpvOverlap
        (Kraus.reindexPhysical e (P.basis j))
        (Kraus.reindexPhysical e (P.basis j)) N) atTop (nhds 1)
    intro j
    refine (hCF.basis_normalized_self_overlap j).congr' ?_
    filter_upwards with N
    exact (mpvOverlap_reindexPhysical_equiv e (P.basis j) (P.basis j)).symm
  · change ∃ N₀ : ℕ, ∀ N > N₀,
      LinearIndependent ℂ (fun j : Fin P.basisCount ↦
        mpvState (Kraus.reindexPhysical e (P.basis j)) N)
    obtain ⟨N₀, hLI⟩ := hCF.eventually_li
    refine ⟨N₀, fun N hN ↦ ?_⟩
    exact linearIndependent_mpvState_reindexPhysical_equiv e P.basis (hLI N hN)

end ReindexPhysical

/-- The sector decomposition obtained by blocking `p` physical sites.

The representative family becomes `A_j^[p]`, while every copy weight becomes
`μ_{j,q}^p`.  The underlying two-layer decomposition is
arXiv:1606.00608, `eq:II_ABasicTensors` and `decBSV`, lines 283--301.  The
blocked form is an auxiliary construction for the planned formal proof of
Appendix C.3, Lemma L, lines 1835--1858. -/
noncomputable def blockTensor (P : SectorDecomposition (Fin d)) (p : ℕ) :
    SectorDecomposition (Fin (blockPhysDim d p)) where
  basisCount := P.basisCount
  basisDim := P.basisDim
  basis := fun j ↦ Kraus.blockTensor (P.basis j) p
  sectors :=
    { copies := P.copies
      copies_pos := P.copies_pos
      weight := fun j q ↦ (P.weight j q) ^ p
      weight_ne_zero := fun j q ↦ pow_ne_zero p (P.weight_ne_zero j q) }

@[simp]
theorem blockTensor_basis (P : SectorDecomposition (Fin d)) (p : ℕ)
    (j : Fin P.basisCount) :
    (P.blockTensor p).basis j = Kraus.blockTensor (P.basis j) p :=
  rfl

@[simp]
theorem blockTensor_weight (P : SectorDecomposition (Fin d)) (p : ℕ)
    (j : Fin P.basisCount) (q : Fin (P.copies j)) :
    (P.blockTensor p).weight j q = (P.weight j q) ^ p :=
  rfl

@[simp]
theorem blockTensor_copies (P : SectorDecomposition (Fin d)) (p : ℕ) :
    (P.blockTensor p).copies = P.copies :=
  rfl

@[simp]
theorem blockTensor_totalCopies (P : SectorDecomposition (Fin d)) (p : ℕ) :
    (P.blockTensor p).totalCopies = P.totalCopies :=
  rfl

@[simp]
theorem blockTensor_flatDim (P : SectorDecomposition (Fin d)) (p : ℕ) :
    (P.blockTensor p).flatDim = P.flatDim :=
  rfl

@[simp]
theorem blockTensor_totalDim (P : SectorDecomposition (Fin d)) (p : ℕ) :
    (P.blockTensor p).totalDim = P.totalDim :=
  rfl

@[simp]
theorem blockTensor_flatWeight (P : SectorDecomposition (Fin d)) (p : ℕ)
    (s : Fin P.totalCopies) :
    (P.blockTensor p).flatWeight s = (P.flatWeight s) ^ p :=
  rfl

@[simp]
theorem blockTensor_flatBasis (P : SectorDecomposition (Fin d)) (p : ℕ)
    (s : Fin P.totalCopies) :
    (P.blockTensor p).flatBasis s = Kraus.blockTensor (P.flatBasis s) p :=
  rfl

/-- Blocking a block-diagonal sector tensor is exactly the block-diagonal
tensor of the blocked representatives with powered copy weights.

Source: arXiv:1606.00608, canonical-form blocking at lines 317--345. -/
theorem blockTensor_toTensor (P : SectorDecomposition (Fin d)) (p : ℕ) :
    Kraus.blockTensor P.toTensor p = (P.blockTensor p).toTensor := by
  change Kraus.blockTensor
      (toTensorFromBlocks (α := Fin d) P.flatWeight P.flatBasis) p =
    toTensorFromBlocks (α := Fin (blockPhysDim d p))
      (fun s ↦ (P.flatWeight s) ^ p)
      (fun s ↦ Kraus.blockTensor (P.flatBasis s) p)
  funext i
  change Kraus.evalWord
      (toTensorFromBlocks (α := Fin d) P.flatWeight P.flatBasis)
      (Kraus.wordOfBlock d p i) = _
  have h := evalWord_toTensorFromBlocks_eq_reindex_blockDiagonal
    P.flatWeight P.flatBasis (Kraus.wordOfBlock d p i)
  rw [h]
  simp only [toTensorFromBlocks, length_wordOfBlock]
  rfl

/-- The coefficient of the blocked decomposition at length `N` is the
coefficient of the original decomposition at length `N * p`.

This is the copy-weight identity
`∑_q (μ_{j,q}^p)^N = ∑_q μ_{j,q}^{Np}` for the two-layer coefficients in
arXiv:1606.00608, `eq:II_ABasicTensors` and `decBSV`, lines 283--301.  It is an
auxiliary identity for the planned formal proof of Appendix C.3, Lemma L,
lines 1835--1858. -/
theorem coeff_blockTensor (P : SectorDecomposition (Fin d)) (p N : ℕ)
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
theorem sameMPV₂_blockTensor_toTensor (P : SectorDecomposition (Fin d)) (p : ℕ) :
    SameMPV₂
      (Kraus.blockTensor P.toTensor p)
      (P.blockTensor p).toTensor := by
  change SameMPV₂
    (Kraus.blockTensor
      (toTensorFromBlocks (α := Fin d) P.flatWeight P.flatBasis) p)
    (toTensorFromBlocks (α := Fin (blockPhysDim d p))
      (fun s ↦ (P.flatWeight s) ^ p)
      (fun s ↦ Kraus.blockTensor (P.flatBasis s) p))
  exact sameMPV₂_blockTensor_toTensorFromBlocks P.flatWeight P.flatBasis p

/-- Positive physical blocking preserves BNT canonical form.

The primitive transfer map of each normal representative makes every positive
blocked representative irreducible. The canonical equivalence between blocked
configurations of length `N` and original configurations of length `N * p`
transports eventual linear independence.

Source: arXiv:1606.00608, canonical-form blocking at lines 317--345, and
arXiv:2011.12127, lines 1815--1850. -/
theorem IsLeftCanonicalBNTPresentation.blockTensor
    {P : SectorDecomposition (Fin d)} (hCF : IsLeftCanonicalBNTPresentation P)
    {p : ℕ} (hp : 0 < p) :
    IsLeftCanonicalBNTPresentation (P.blockTensor p) := by
  classical
  have hPrimitive : ∀ j : Fin P.basisCount,
      _root_.IsPrimitive (Kraus.transferMap (P.basis j)) :=
    fun j ↦ (hCF.basis_normal j).primitive_transfer
  have hData : HasBNTSectorData (P.blockTensor p) := by
    obtain ⟨N₀, hLI⟩ := hCF.eventually_li
    refine ⟨N₀, ?_⟩
    intro N hN
    change LinearIndependent ℂ (fun j : Fin P.basisCount ↦
      mpvState (Kraus.blockTensor (P.basis j) p) N)
    let e := Kraus.blockedConfigEquiv d N p
    apply linearIndependent_mpvState_of_configEquiv e
      (fun j ↦ Kraus.blockTensor (P.basis j) p) P.basis
    · intro j σ
      change mpv (Kraus.blockTensor (P.basis j) p) (e.symm σ) =
        mpv (P.basis j) σ
      simp only [mpv, MPTensor.coeff, evalWord_blockTensor]
      rw [← Kraus.ofFn_blockedConfigEquiv d N p (e.symm σ)]
      simp [e]
    · have hNp : N₀ < N * p := by
        exact lt_of_lt_of_le hN (Nat.le_mul_of_pos_right N hp)
      exact hLI (N * p) hNp
  refine IsLeftCanonicalBNTPresentation.of_irreducible_selfOverlap
    hCF.basisCount_pos hCF.basis_dim_pos
    ?_ ?_ ?_ hData
  · intro j
    let : NeZero (P.basisDim j) := ⟨(hCF.basis_dim_pos j).ne'⟩
    exact (Kraus.isIrreducibleFamily_reindexPhysical_equiv (Kraus.decodeBlockEquiv _ _) _).2
      (Kraus.isIrreducibleFamily_block_of_tp_primitive_irr (P.basis j)
        (hCF.basis_left_canonical j) (hPrimitive j) (hCF.basis_irreducible j) hp)
  · intro j
    exact (Kraus.isTP_reindexPhysical_iff (Kraus.decodeBlockEquiv _ _) _).2
      (Kraus.IsTP.block (A := P.basis j) (hCF.basis_left_canonical j) p)
  · change ∀ j : Fin P.basisCount,
      Tendsto (fun N : ℕ ↦ mpvOverlap
        (Kraus.blockTensor (P.basis j) p)
        (Kraus.blockTensor (P.basis j) p) N) atTop (nhds 1)
    intro j
    let : NeZero (P.basisDim j) := ⟨(hCF.basis_dim_pos j).ne'⟩
    have hMul : Tendsto (fun a : ℕ ↦ a * p) atTop atTop := by
      refine tendsto_atTop.2 fun b ↦ ?_
      filter_upwards [eventually_ge_atTop b] with a ha
      exact ha.trans (Nat.le_mul_of_pos_right a hp)
    refine ((hCF.basis_normalized_self_overlap j).comp hMul).congr' ?_
    filter_upwards with N
    exact (mpvOverlap_blockTensor_self_eq (P.basis j) p N).symm

end MPSTensor.SectorDecomposition
