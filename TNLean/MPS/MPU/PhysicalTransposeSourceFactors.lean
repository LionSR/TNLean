/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.EvenFamilySourceGauges
import TNLean.MPS.MPU.SourceFactorsPhysicalAdjoint

/-!
# Physical transposition of actual normalized source factors

Physical transposition exchanges the physical input and output without
reflecting the virtual word. It is exactly physical adjunction followed by
entrywise conjugation. The actual canonical data therefore retain the same
real diagonal boundary, and the two source ranks are exchanged.

At square source ranks the actual adjoint factor record followed by its
entrywise conjugate gives normalized factors for the transpose. Their gates
are exactly the transposes of the original shifted and unshifted gates,
respectively. Square ranks are also derived from actual even-chain transpose
symmetry, using the even-family virtual comparison, not assumed normalization
or gate witnesses.

Source: arXiv:1703.09188, `prop:local-char-transposition`,
`UUtransposetrick`, lines 1258–1288. This module supplies the physical and
source-factor transport, not the local equivalence criterion.

**Scope restriction (canonical source factors):** The factor construction uses
the recorded weight of a reduced canonical presentation and square source
ranks. The latter follow here from actual even-chain transpose symmetry.
Arbitrary ambient presentations remain the separate restriction in
`docs/paper-gaps/mpu_canonical_form_full_support.tex`.
-/

open scoped Matrix BigOperators

namespace MPOTensor

/-- Physical input-output exchange as actual adjunction followed by entrywise
conjugation. Source: CPSV17, transposition subsection, lines 1258–1288. -/
def physicalTransposeTensor {d D : ℕ} (U : MPOTensor d D) : MPOTensor d D :=
  MPOTensor.mapStar (MPOTensor.physicalAdjointTensor U)

/-- Physical transposition exchanges the two physical letters and preserves
the virtual matrix orientation. Source: CPSV17, lines 1258–1267. -/
@[simp] theorem physicalTransposeTensor_apply {d D : ℕ} (U : MPOTensor d D)
    (i j : Fin d) : physicalTransposeTensor U i j = U j i := by
  ext α β
  simp [physicalTransposeTensor, MPOTensor.mapStar, MPOTensor.physicalAdjointTensor,
    Matrix.map_apply]

/-- Physical transposition is an involution. Source: CPSV17,
`prop:local-char-transposition`, lines 1266–1276. -/
@[simp] theorem physicalTransposeTensor_physicalTransposeTensor
    {d D : ℕ} (U : MPOTensor d D) :
    physicalTransposeTensor (physicalTransposeTensor U) = U := by
  funext i j
  rw [physicalTransposeTensor_apply, physicalTransposeTensor_apply]

/-- Closing the transposed physical tensor transposes the actual periodic
operator, at every length. Source: CPSV17, lines 1258–1276. -/
theorem mpo_physicalTransposeTensor {d D : ℕ} (U : MPOTensor d D) (N : ℕ) :
    mpo (physicalTransposeTensor U) N = (mpo U N)ᵀ := by
  rw [physicalTransposeTensor, mpo_map_star, mpo_physicalAdjointTensor_eq_conjTranspose]
  ext σ τ
  simp only [Matrix.map_apply, Matrix.conjTranspose_apply, Matrix.transpose_apply,
    starRingEnd_apply, star_star]

/-- Transposition exchanges the two source cuts' ranks. Source: CPSV17,
the zero-index observation preceding `prop:local-char-transposition`,
lines 1258–1264. -/
theorem source_ranks_physicalTransposeTensor {d D : ℕ} (U : MPOTensor d D) :
    r[physicalTransposeTensor U] = ℓ[U] ∧ ℓ[physicalTransposeTensor U] = r[U] :=
  ⟨(source_ranks_mapStar (MPOTensor.physicalAdjointTensor U)).1.trans
      (rightRank_physicalAdjointTensor U),
    (source_ranks_mapStar (MPOTensor.physicalAdjointTensor U)).2.trans
      (leftRank_physicalAdjointTensor U)⟩

/-- The canonical presentation and its real diagonal boundary transport
through the actual physical transpose. Source: CPSV17, lines 1258–1288,
using the canonical boundary of `Erightleft`, lines 269–281. -/
noncomputable def IsMPUCanonicalFormII.physicalTransposeTensor
    {d D : ℕ} {U : MPOTensor d D} (hU : IsMPUCanonicalFormII U) :
    IsMPUCanonicalFormII (MPOTensor.physicalTransposeTensor U) :=
  hU.physicalAdjointTensor.mapStar

/-- Simplicity transports through physical transposition by the actual
exchanged-rank product. Source: CPSV17, `ThmFund1`, lines 563–601, as used
in the transposition comparison, lines 1258–1288. -/
theorem IsMPUCanonicalFormII.isMPUSimple_physicalTransposeTensor
    {d D : ℕ} {U : MPOTensor d D} (hU : IsMPUCanonicalFormII U)
    (hsimple : IsMPUSimple U) : IsMPUSimple (MPOTensor.physicalTransposeTensor U) := by
  apply (hU.physicalTransposeTensor.isMPUSimple_tfae.out 1 2).mpr
  simpa only [(source_ranks_physicalTransposeTensor U).1,
    (source_ranks_physicalTransposeTensor U).2, mul_comm] using
    (hU.isMPUSimple_tfae.out 1 2).mp hsimple

/-- Actual even-chain transpose symmetry forces both source ranks to equal
the physical dimension. The possible virtual sign does not change cut rank.
Source: CPSV17, the observation before `prop:local-char-transposition`,
lines 1258–1264. -/
theorem IsMPUCanonicalFormII.sourceRanks_eq_phys_of_even_mpo_eq_transpose
    {d D : ℕ} {U : MPOTensor d D} (hU : IsMPUCanonicalFormII U)
    (hsimple : IsMPUSimple U)
    (hTR : ∀ N : ℕ, 1 < N → Even N → mpo U N = (mpo U N)ᵀ) :
    r[U] = d ∧ ℓ[U] = d := by
  have hEq : ∀ N : ℕ, 1 < N → Even N →
      mpo U N = mpo (MPOTensor.physicalTransposeTensor U) N := by
    intro N hN heven
    rw [mpo_physicalTransposeTensor]
    exact hTR N hN heven
  have hranks := hU.source_ranks_eq_of_mpo_eq_even hU.physicalTransposeTensor hEq
  have hbalanced : ℓ[U] = r[U] := by
    simpa only [(source_ranks_physicalTransposeTensor U).1] using hranks.1
  have hprod := (hU.isMPUSimple_tfae.out 1 2).mp hsimple
  rw [← hbalanced] at hprod
  have hℓ : ℓ[U] = d := (mul_self_inj (Nat.zero_le _) (Nat.zero_le _)).mp hprod
  exact ⟨hbalanced.symm.trans hℓ, hℓ⟩

namespace SourceFactors

/-- Actual physical-transpose factors: take the already normalized adjoint
factors and conjugate every entry. The real diagonal weight is unchanged.
Source: CPSV17, `UUtransposetrick` and its proof, lines 1266–1288. -/
noncomputable def physicalTranspose {d D : ℕ} {U : MPOTensor d D}
    (hU : IsMPUCanonicalFormII U) (hsimple : IsMPUSimple U)
    (S : SourceFactors U hU.ρ) (hr : r[U] = d) (hl : ℓ[U] = d) :
    SourceFactors (MPOTensor.physicalTransposeTensor U) hU.ρ := by
  let T := (SourceFactors.physicalAdjoint hU hsimple S hr hl).mapStar
  have hρ : hU.ρ.map (starRingEnd ℂ) = hU.ρ :=
    MPSTensor.map_star_eq_self_of_posDef_isDiag hU.ρ_posDef hU.ρ_isDiag
  have hweight : sourceWeight (d := d) hU.ρ =
      sourceWeight (d := d) (hU.ρ.map (starRingEnd ℂ)) :=
    congrArg (sourceWeight (d := d)) hρ.symm
  exact {
    X₁ := T.X₁
    Y₁ := T.Y₁
    Z₁ := T.Z₁
    X₂ := T.X₂
    Y₂ := T.Y₂
    Z₂ := T.Z₂
    sourceCutM₁_eq := T.sourceCutM₁_eq
    sourceCutM₂_eq := T.sourceCutM₂_eq
    X₁_weighted_isometry := by rw [hweight]; exact T.X₁_weighted_isometry
    X₂_isometry := T.X₂_isometry
    Y₁_mul_Z₁ := T.Y₁_mul_Z₁
    Y₂_mul_Z₂ := T.Y₂_mul_Z₂ }

/-- The actual transposed factors' unshifted gate is the original shifted
gate transposed, in the canonical exchanged-rank coordinates. Source:
CPSV17, `UUtransposetrick`, lines 1270–1283. -/
theorem sourceU_physicalTranspose {d D : ℕ} {U : MPOTensor d D}
    (hU : IsMPUCanonicalFormII U) (hsimple : IsMPUSimple U)
    (S : SourceFactors U hU.ρ) (hr : r[U] = d) (hl : ℓ[U] = d) :
    sourceU (MPOTensor.physicalTransposeTensor U) (physicalTranspose hU hsimple S hr hl) =
      Matrix.reindex
        (Equiv.prodCongr (finCongr (source_ranks_physicalTransposeTensor U).2.symm)
          (finCongr (source_ranks_physicalTransposeTensor U).1.symm))
        (Equiv.refl _) (sourceV U S)ᵀ := by
  change sourceU (MPOTensor.mapStar (MPOTensor.physicalAdjointTensor U))
    ((SourceFactors.physicalAdjoint hU hsimple S hr hl).mapStar) = _
  rw [SourceFactors.sourceU_mapStar, SourceFactors.sourceU_physicalAdjoint]
  ext ⟨l, r⟩ ⟨i, j⟩
  simp [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.map_apply,
    Matrix.conjTranspose_apply, Matrix.transpose_apply]

/-- The actual transposed factors' shifted gate is the original unshifted
gate transposed. Source: CPSV17, `UUtransposetrick`, lines 1270–1283. -/
theorem sourceV_physicalTranspose {d D : ℕ} {U : MPOTensor d D}
    (hU : IsMPUCanonicalFormII U) (hsimple : IsMPUSimple U)
    (S : SourceFactors U hU.ρ) (hr : r[U] = d) (hl : ℓ[U] = d) :
    sourceV (MPOTensor.physicalTransposeTensor U) (physicalTranspose hU hsimple S hr hl) =
      Matrix.reindex (Equiv.refl _)
        (Equiv.prodCongr (finCongr (source_ranks_physicalTransposeTensor U).1.symm)
          (finCongr (source_ranks_physicalTransposeTensor U).2.symm))
        (sourceU U S)ᵀ := by
  change sourceV (MPOTensor.mapStar (MPOTensor.physicalAdjointTensor U))
    ((SourceFactors.physicalAdjoint hU hsimple S hr hl).mapStar) = _
  rw [SourceFactors.sourceV_mapStar, SourceFactors.sourceV_physicalAdjoint]
  ext ⟨i, j⟩ ⟨r, l⟩
  simp [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.map_apply,
    Matrix.conjTranspose_apply, Matrix.transpose_apply]

end SourceFactors

/-- Supply actual physical-transpose factors directly from even-chain
transpose symmetry; square source ranks are derived, not extra inputs.
Source: CPSV17, `prop:local-char-transposition`, lines 1258–1288. -/
noncomputable def IsMPUCanonicalFormII.sourceFactors_physicalTranspose_of_even_mpo_eq_transpose
    {d D : ℕ} {U : MPOTensor d D} (hU : IsMPUCanonicalFormII U)
    (hsimple : IsMPUSimple U) (S : SourceFactors U hU.ρ)
    (hTR : ∀ N : ℕ, 1 < N → Even N → mpo U N = (mpo U N)ᵀ) :
    SourceFactors (MPOTensor.physicalTransposeTensor U) hU.ρ :=
  SourceFactors.physicalTranspose hU hsimple S
    (hU.sourceRanks_eq_phys_of_even_mpo_eq_transpose hsimple hTR).1
    (hU.sourceRanks_eq_phys_of_even_mpo_eq_transpose hsimple hTR).2

end MPOTensor
