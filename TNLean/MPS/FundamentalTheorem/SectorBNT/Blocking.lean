/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.CanonicalForm.SectorComparison.PrimitiveBlocks
import TNLean.MPS.Core.PhysicalReindexTransport
import TNLean.MPS.FundamentalTheorem.SectorBNT.Basic
import TNLean.MPS.Periodic.NormalizedSelfOverlap

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
Positive blocking preserves the full predicate `IsBNTCanonicalForm`.

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

open scoped Matrix BigOperators
open Filter

namespace MPSTensor.SectorDecomposition

variable {d : ℕ}

/-- Reindex the physical alphabet of every representative in a sector
decomposition. The representative labels, multiplicities, weights, and bond
dimensions are unchanged.

Source: arXiv:1606.00608, the harmless physical-basis identifications used in
the canonical-form blocking at lines 317--345. -/
noncomputable def reindexPhysical {d' : ℕ} (P : SectorDecomposition d)
    (e : Fin d' ≃ Fin d) : SectorDecomposition d' where
  basisCount := P.basisCount
  basisDim := P.basisDim
  basis := fun j ↦ MPSTensor.reindexPhysical e (P.basis j)
  sectors := P.sectors

@[simp]
theorem reindexPhysical_basis {d' : ℕ} (P : SectorDecomposition d)
    (e : Fin d' ≃ Fin d) (j : Fin P.basisCount) :
    (P.reindexPhysical e).basis j = MPSTensor.reindexPhysical e (P.basis j) :=
  rfl

@[simp]
theorem reindexPhysical_totalDim {d' : ℕ} (P : SectorDecomposition d)
    (e : Fin d' ≃ Fin d) :
    (P.reindexPhysical e).totalDim = P.totalDim :=
  rfl

@[simp]
theorem reindexPhysical_totalCopies {d' : ℕ} (P : SectorDecomposition d)
    (e : Fin d' ≃ Fin d) :
    (P.reindexPhysical e).totalCopies = P.totalCopies :=
  rfl

@[simp]
theorem reindexPhysical_flatDim {d' : ℕ} (P : SectorDecomposition d)
    (e : Fin d' ≃ Fin d) (s : Fin P.totalCopies) :
    (P.reindexPhysical e).flatDim s = P.flatDim s :=
  rfl

/-- Assembling a physically reindexed sector decomposition is the same as
physically reindexing its assembled tensor.

Source: arXiv:1606.00608, canonical-form blocking at lines 317--345. -/
theorem reindexPhysical_toTensor {d' : ℕ} (P : SectorDecomposition d)
    (e : Fin d' ≃ Fin d) :
    (P.reindexPhysical e).toTensor = MPSTensor.reindexPhysical e P.toTensor :=
  rfl

/-- A bijective relabelling of the physical alphabet preserves BNT canonical
form.

Source: arXiv:1606.00608, the physical-basis identifications implicit in the
blocking passage at lines 317--345. -/
theorem IsBNTCanonicalForm.reindexPhysical {d' : ℕ}
    {P : SectorDecomposition d} (hCF : IsBNTCanonicalForm P)
    (e : Fin d' ≃ Fin d) :
    IsBNTCanonicalForm (P.reindexPhysical e) where
  basis_dim_pos := hCF.basis_dim_pos
  basis_irreducible := fun j ↦
    (isIrreducibleTensor_reindexPhysical_equiv e (P.basis j)).2
      (hCF.basis_irreducible j)
  basis_left_canonical := fun j ↦
    (leftCanonical_reindexPhysical_equiv e (P.basis j)).2
      (hCF.basis_left_canonical j)
  basis_normalized_self_overlap := by
    change ∀ j : Fin P.basisCount,
      Tendsto (fun N : ℕ ↦ mpvOverlap
        (MPSTensor.reindexPhysical e (P.basis j))
        (MPSTensor.reindexPhysical e (P.basis j)) N) atTop (nhds 1)
    intro j
    refine (hCF.basis_normalized_self_overlap j).congr' ?_
    filter_upwards with N
    exact (mpvOverlap_reindexPhysical_equiv e (P.basis j) (P.basis j)).symm
  bnt_data := by
    change ∃ N₀ : ℕ, ∀ N > N₀,
      LinearIndependent ℂ (fun j : Fin P.basisCount ↦
        mpvState (MPSTensor.reindexPhysical e (P.basis j)) N)
    obtain ⟨N₀, hLI⟩ := hCF.bnt_data
    refine ⟨N₀, fun N hN ↦ ?_⟩
    exact linearIndependent_mpvState_reindexPhysical_equiv e P.basis (hLI N hN)
  basis_distinct := by
    change ∀ j k : Fin P.basisCount, j ≠ k →
      ∀ hdim : P.basisDim j = P.basisDim k,
        ¬ GaugePhaseEquiv
          (cast (congr_arg (MPSTensor d') hdim)
            (MPSTensor.reindexPhysical e (P.basis j)))
          (MPSTensor.reindexPhysical e (P.basis k))
    intro j k hjk hdim hGauge
    apply hCF.basis_distinct j k hjk hdim
    rw [← MPSTensor.reindexPhysical_cast_dim e hdim (P.basis j)] at hGauge
    exact (gaugePhaseEquiv_reindexPhysical_equiv e _ _).1 hGauge
  weight_norm_le_one := hCF.weight_norm_le_one
  weight_unit_exists := hCF.weight_unit_exists

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

/-- Blocking a block-diagonal sector tensor is exactly the block-diagonal
tensor of the blocked representatives with powered copy weights.

Source: arXiv:1606.00608, canonical-form blocking at lines 317--345. -/
theorem blockTensor_toTensor (P : SectorDecomposition d) (p : ℕ) :
    MPSTensor.blockTensor P.toTensor p = (P.blockTensor p).toTensor := by
  change MPSTensor.blockTensor
      (toTensorFromBlocks (d := d) P.flatWeight P.flatBasis) p =
    toTensorFromBlocks (d := blockPhysDim d p)
      (fun s ↦ (P.flatWeight s) ^ p)
      (fun s ↦ MPSTensor.blockTensor (P.flatBasis s) p)
  funext i
  rw [MPSTensor.blockTensor]
  rw [evalWord_toTensorFromBlocks_eq_reindex_blockDiagonal]
  simp only [toTensorFromBlocks, length_wordOfBlock]
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

/-- Positive physical blocking preserves BNT canonical form.

The primitive transfer map obtained from irreducibility, left-canonicality,
and normalized self-overlap makes every positive blocked representative
irreducible. The canonical equivalence between blocked configurations of
length `N` and original configurations of length `N * p` transports eventual
linear independence. That independence also prevents two distinct blocked
representatives from becoming gauge-phase equivalent.

Source: arXiv:1606.00608, canonical-form blocking at lines 317--345, and
arXiv:2011.12127, lines 1815--1850. -/
theorem IsBNTCanonicalForm.blockTensor
    {P : SectorDecomposition d} (hCF : IsBNTCanonicalForm P)
    {p : ℕ} (hp : 0 < p) :
    IsBNTCanonicalForm (P.blockTensor p) := by
  classical
  have hPrimitive : ∀ j : Fin P.basisCount,
      _root_.IsPrimitive (transferMap (P.basis j)) := by
    intro j
    letI : NeZero (P.basisDim j) := ⟨(hCF.basis_dim_pos j).ne'⟩
    exact
      (isPrimitive_and_isNormal_of_irreducible_leftCanonical_selfOverlap_tendsto_one
        (P.basis j) (hCF.basis_irreducible j) (hCF.basis_left_canonical j)
          (hCF.basis_normalized_self_overlap j)).1
  have hData : HasBNTSectorData (P.blockTensor p) := by
    obtain ⟨N₀, hLI⟩ := hCF.bnt_data
    refine ⟨N₀, ?_⟩
    intro N hN
    change LinearIndependent ℂ (fun j : Fin P.basisCount ↦
      mpvState (MPSTensor.blockTensor (P.basis j) p) N)
    let e := blockedConfigEquiv d N p
    apply linearIndependent_mpvState_of_configEquiv e
      (fun j ↦ MPSTensor.blockTensor (P.basis j) p) P.basis
    · intro j σ
      change mpv (MPSTensor.blockTensor (P.basis j) p) (e.symm σ) =
        mpv (P.basis j) σ
      simp only [mpv, MPSTensor.coeff, evalWord_blockTensor]
      rw [← ofFn_blockedConfigEquiv d N p (e.symm σ)]
      simp [e]
    · have hNp : N₀ < N * p := by
        exact lt_of_lt_of_le hN (Nat.le_mul_of_pos_right N hp)
      exact hLI (N * p) hNp
  refine
    { basis_dim_pos := hCF.basis_dim_pos
      basis_irreducible := ?_
      basis_left_canonical := ?_
      basis_normalized_self_overlap := ?_
      bnt_data := hData
      basis_distinct := ?_
      weight_norm_le_one := ?_
      weight_unit_exists := ?_ }
  · intro j
    letI : NeZero (P.basisDim j) := ⟨(hCF.basis_dim_pos j).ne'⟩
    exact isIrreducibleTensor_blockTensor_of_tp_primitive_irr
      (P.basis j) (hCF.basis_left_canonical j) (hPrimitive j)
        (hCF.basis_irreducible j) hp
  · intro j
    exact leftCanonical_blockTensor (P.basis j) p (hCF.basis_left_canonical j)
  · change ∀ j : Fin P.basisCount,
      Tendsto (fun N : ℕ ↦ mpvOverlap
        (MPSTensor.blockTensor (P.basis j) p)
        (MPSTensor.blockTensor (P.basis j) p) N) atTop (nhds 1)
    intro j
    letI : NeZero (P.basisDim j) := ⟨(hCF.basis_dim_pos j).ne'⟩
    have hMul : Tendsto (fun a : ℕ ↦ a * p) atTop atTop := by
      refine tendsto_atTop.2 fun b ↦ ?_
      filter_upwards [eventually_ge_atTop b] with a ha
      exact ha.trans (Nat.le_mul_of_pos_right a hp)
    refine ((hCF.basis_normalized_self_overlap j).comp hMul).congr' ?_
    filter_upwards with N
    exact (mpvOverlap_blockTensor_self_eq (P.basis j) p N).symm
  · intro j k hjk hdim hGauge
    obtain ⟨X, ζ, _, hX⟩ := hGauge
    obtain ⟨N₀, hLI⟩ := hData
    let N := N₀ + 1
    have hState : mpvState ((P.blockTensor p).basis k) N =
        (ζ ^ N) • mpvState ((P.blockTensor p).basis j) N := by
      ext σ
      change mpv ((P.blockTensor p).basis k) σ =
        ζ ^ N * mpv ((P.blockTensor p).basis j) σ
      rw [mpv_eq_pow_mul_of_gaugePhase _ _ X ζ hX N σ,
        mpv_cast_dim hdim ((P.blockTensor p).basis j) N σ]
    have hEq : (1 : ℂ) • mpvState ((P.blockTensor p).basis k) N =
        (ζ ^ N) • mpvState ((P.blockTensor p).basis j) N := by
      simpa using hState
    have hkj : k = j :=
      (hLI N (by omega)).eq_of_smul_apply_eq_smul_apply 1 (ζ ^ N) k j one_ne_zero hEq
    exact hjk hkj.symm
  · intro j q
    rw [blockTensor_weight, norm_pow]
    exact pow_le_one₀ (norm_nonneg _) (hCF.weight_norm_le_one j q)
  · obtain ⟨j, q, hq⟩ := hCF.weight_unit_exists
    refine ⟨j, q, ?_⟩
    rw [blockTensor_weight, norm_pow, hq, one_pow]

end MPSTensor.SectorDecomposition
