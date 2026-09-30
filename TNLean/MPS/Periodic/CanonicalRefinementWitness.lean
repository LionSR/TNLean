/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.FundamentalTheorem.SectorBNT.UnblockedPowerSumCoefficients
import TNLean.MPS.CanonicalForm.PhaseClassSectorData
import TNLean.MPS.Periodic.IrreducibleFormPeriods
import TNLean.MPS.Core.PositiveLengthMPVDimension
import TNLean.MPS.Periodic.NormalCanonicalPeriodOne
import TNLean.MPS.Periodic.BlockedIrreducibleForm

/-!
# Active irreducible representative of an arbitrary tensor

An arbitrary tensor has a positive-length trace decomposition into normalized
periodic irreducible blocks. Empty-word equality is deliberately absent: zero
composition factors can contribute to the bond dimension without contributing
to any positive-length trace. The equal-case theorem can recover that missing
dimension when the tensor is compared with a literal nondegenerate target.

Source: arXiv:1708.00029, lines 238--275 and Theorem 3.8, lines 643--693.
-/

open scoped Matrix BigOperators Matrix.Norms.Operator

namespace MPSTensor

variable {d : ℕ}

/-- Trace preservation gives spectral radius one for a periodic block.
Source: arXiv:1708.00029, lines 252--258. -/
theorem IsPeriodic.spectral_radius_one {D m : ℕ}
    {A : MPSTensor d D} (hA : IsPeriodic m A) :
    spectralRadius ℂ
      ((Module.End.toContinuousLinearMap (Matrix (Fin D) (Fin D) ℂ))
        (Kraus.transferMap (d := d) (D := D) A)) = 1 := by
  let : NeZero D := ⟨hA.bondDim_ne_zero⟩
  exact (Kraus.isPositiveMap_mapLM A).spectralRadius_eq_one_of_tracePreserving
    (Kraus.isTracePreservingMap_mapLM_of_isTP A hA.leftCanonical)

/-- The active irreducible factors of an arbitrary tensor, grouped by
gauge-phase class, form a sector decomposition of no larger bond dimension.
Its periodic vectors agree with the original tensor at every positive length.
Source: arXiv:1708.00029, lines 238--275. -/
theorem exists_active_irreducible_sectorDecomposition {D : ℕ}
    (A : MPSTensor d D) :
    ∃ P : SectorDecomposition d,
      P.totalDim ≤ D ∧
      (∀ j, 0 < P.basisDim j) ∧
      (∃ per : Fin P.basisCount → ℕ,
        ∀ j, IsPeriodic (per j) (P.basis j)) ∧
      (∀ i j, i ≠ j → ¬ HetRepeatedBlocks (P.basis i) (P.basis j)) ∧
      SameMPV₂Pos A P.toTensor := by
  classical
  obtain ⟨g, dimRep, R, per, copies, α, hDim, hPer, hCopies, hα, hDistinct,
    hMPV, hBound⟩ := exists_irreducible_expansion A
  let P : SectorDecomposition d :=
    { basisCount := g
      basisDim := dimRep
      basis := R
      sectors :=
        { copies := copies
          copies_pos := hCopies
          weight := α
          weight_ne_zero := hα } }
  have hTotal : P.totalDim = ∑ j : Fin g, copies j * dimRep j := by
    calc
      P.totalDim =
          ∑ x : (j : Fin g) × Fin (copies j), dimRep x.1 := by
        change (∑ s : Fin (∑ j : Fin g, copies j),
          dimRep ((finSigmaFinEquiv.symm s).1)) =
            ∑ x : (j : Fin g) × Fin (copies j), dimRep x.1
        symm
        simpa using
          (Equiv.sum_comp (finSigmaFinEquiv (m := g) (n := copies))
            (fun s : Fin (∑ j : Fin g, copies j) =>
              dimRep ((finSigmaFinEquiv.symm s).1)))
      _ = ∑ j : Fin g, ∑ _q : Fin (copies j), dimRep j := by
        rw [Fintype.sum_sigma]
      _ = ∑ j : Fin g, copies j * dimRep j := by simp
  refine ⟨P, hTotal.trans_le hBound, hDim, ⟨per, hPer⟩, ?_, ?_⟩
  · intro i j hij hRep
    obtain ⟨hd, hr⟩ := hRep
    exact (not_repeatedBlocks_of_not_gaugePhaseEquiv
      (hDistinct i j hij hd)) hr
  · intro N hN σ
    rw [hMPV N hN σ, P.mpv_toTensor_eq_sum_coeff]
    rfl

/-- Equal positive-length vectors determine the total bond dimension of
nonrepeated periodic sector decompositions. This is the dimension consequence
of the literal equal-case fundamental theorem, including multiplicity matching.
Source: arXiv:1708.00029, Theorem 3.8, lines 643--693. -/
theorem SectorDecomposition.totalDim_eq_of_periodic_sameMPV₂Pos
    (P Q : SectorDecomposition d)
    (perP : Fin P.basisCount → ℕ)
    (hPPer : ∀ j, IsPeriodic (perP j) (P.basis j))
    (perQ : Fin Q.basisCount → ℕ)
    (hQPer : ∀ j, IsPeriodic (perQ j) (Q.basis j))
    (hPDistinct : ∀ i j, i ≠ j → ¬ HetRepeatedBlocks (P.basis i) (P.basis j))
    (hQDistinct : ∀ i j, i ≠ j → ¬ HetRepeatedBlocks (Q.basis i) (Q.basis j))
    (hSame : SameMPV₂Pos P.toTensor Q.toTensor) :
    P.totalDim = Q.totalDim := by
  classical
  obtain ⟨_, _, _, _, perm, _, _, _, _, _, hRep, _, hCopies, _⟩ :=
    fundamentalTheorem_periodic_equalCase_derivedPeriods P Q
      (fun j => (hPPer j).irreducible)
      (fun j => (hPPer j).spectral_radius_one)
      (fun j => (hQPer j).irreducible)
      (fun j => (hQPer j).spectral_radius_one)
      hPDistinct hQDistinct hSame
  have hMatchDim : ∀ j : Fin Q.basisCount,
      P.basisDim (perm.symm j) = Q.basisDim j := by
    intro j
    simpa using (hRep (perm.symm j)).dim_eq
  have hMatchCopies : (j : Fin Q.basisCount) →
      Fin (Q.copies j) ≃ Fin (P.copies (perm.symm j)) := by
    intro j
    let τ := Classical.choose (Classical.choose_spec (hCopies (perm.symm j)))
    simpa using τ.symm
  exact SectorDecomposition.totalDim_eq_of_match perm.symm hMatchDim hMatchCopies

/-- A literal irreducible-form target occupying the full bond dimension
excludes discarded zero composition factors from an equal positive-length
presentation. The original tensor therefore has an all-length irreducible
representative. Source: arXiv:1708.00029, Theorem 3.8, lines 643--693,
applied to the trace reduction at lines 238--275. -/
theorem exists_active_irreducible_sectorDecomposition_of_equal_target
    {D : ℕ} (A : MPSTensor d D) (Q : SectorDecomposition d)
    (hQDim : Q.totalDim = D)
    (hQPer : ∃ per : Fin Q.basisCount → ℕ,
      ∀ j, IsPeriodic (per j) (Q.basis j))
    (hQDistinct : ∀ i j, i ≠ j →
      ¬ HetRepeatedBlocks (Q.basis i) (Q.basis j))
    (hSame : SameMPV₂Pos A Q.toTensor) :
    ∃ P : SectorDecomposition d,
      P.totalDim = D ∧
      (∀ j, 0 < P.basisDim j) ∧
      (∃ per : Fin P.basisCount → ℕ,
        ∀ j, IsPeriodic (per j) (P.basis j)) ∧
      (∀ i j, i ≠ j → ¬ HetRepeatedBlocks (P.basis i) (P.basis j)) ∧
      SameMPV₂ A P.toTensor := by
  classical
  obtain ⟨P, hPBound, hPDim, ⟨perP, hPPer⟩, hPDistinct, hPSame⟩ :=
    exists_active_irreducible_sectorDecomposition A
  obtain ⟨perQ, hQPer⟩ := hQPer
  have hPDimEq : P.totalDim = D :=
    (SectorDecomposition.totalDim_eq_of_periodic_sameMPV₂Pos
      P Q perP hPPer perQ hQPer hPDistinct hQDistinct
      (hPSame.symm.trans hSame)).trans hQDim
  exact ⟨P, hPDimEq, hPDim, ⟨perP, hPPer⟩, hPDistinct,
    sameMPV₂_of_sameMPV₂Pos_of_bondDim_eq A P.toTensor hPSame hPDimEq.symm⟩

/-- Grouping the blocks of an all-length irreducible-form presentation by
gauge-phase classes gives a literal sector decomposition with the same full
bond dimension. Source: arXiv:1708.00029, irreducible form at lines 238--275
and equal-case representatives at lines 643--693. -/
theorem IsIrreducibleForm.exists_full_sectorDecomposition
    {D : ℕ} {B : MPSTensor d D} (hB : IsIrreducibleForm B) :
    ∃ Q : SectorDecomposition d,
      Q.totalDim = D ∧
      (∃ per : Fin Q.basisCount → ℕ,
        ∀ j, IsPeriodic (per j) (Q.basis j)) ∧
      (∀ i j, i ≠ j → ¬ HetRepeatedBlocks (Q.basis i) (Q.basis j)) ∧
      SameMPV₂Pos B Q.toTensor := by
  classical
  have hμ : ∀ j, hB.μ j ≠ 0 := by
    intro j
    exact Complex.ne_zero_of_re_pos (hB.weight_pos j).1
  let Q := collapsedBntSectorDecomp hB.μ hB.blocks hμ
  have hDimSum : ∑ j : Fin hB.r, hB.dim j = D := by
    have h0 := hB.sameMPV 0 (Fin.elim0)
    rw [mpv_toTensorFromBlocks_eq_sum] at h0
    simp only [mpv_zero_length, pow_zero, one_smul] at h0
    exact_mod_cast h0.symm
  have hClassDim : ∀ j q,
      hB.dim ((mpvPhaseClassData hB.blocks).enum j q) =
        hB.dim ((mpvPhaseClassData hB.blocks).repr j) := by
    intro j q
    exact (dim_eq_of_mpvBlockPhaseEquiv_of_isPeriodic
      (hB.periodic ((mpvPhaseClassData hB.blocks).repr j))
      (hB.periodic ((mpvPhaseClassData hB.blocks).enum j q))
      ((mpvPhaseClassData hB.blocks).enum_phase j q)).symm
  have hQDim : Q.totalDim = D :=
    (collapsedBntSectorDecomp_totalDim_eq_sum_dim hB.μ hB.blocks hμ hClassDim).trans hDimSum
  refine ⟨Q, hQDim, ?_, ?_, ?_⟩
  · let classes := mpvPhaseClassData hB.blocks
    exact ⟨fun j => hB.period (classes.repr j),
      fun j => hB.periodic (classes.repr j)⟩
  · intro i j hij hRep
    exact (not_repeatedBlocks_of_not_gaugePhaseEquiv
      ((mpvPhaseClassData hB.blocks).blocks_not_equiv i j hij hRep.1)) hRep.2
  · exact hB.sameMPV.toSameMPV₂Pos.trans
      (collapsedBntSectorDecomp_sameMPV₂Pos hB.μ hB.blocks hμ).symm

/-- Any sector decomposition with periodic basis can be written with positive
real weights by absorbing the phase of each copy weight into that copy's
periodic block. The represented tensor and its bond dimension are unchanged.
Source: arXiv:1708.00029, irreducible form at lines 252--271. -/
noncomputable def SectorDecomposition.toIsIrreducibleForm
    (P : SectorDecomposition d)
    (per : Fin P.basisCount → ℕ)
    (hPer : ∀ j, IsPeriodic (per j) (P.basis j)) :
    IsIrreducibleForm P.toTensor := by
  classical
  let μ := P.flatWeight
  let blocks := P.flatBasis
  have hμ : ∀ s, μ s ≠ 0 := by
    intro s
    exact P.weight_ne_zero _ _
  refine
    { r := P.totalCopies
      dim := P.flatDim
      blocks := phaseNormalizedBlocks μ blocks
      μ := positiveRealWeights μ
      period := fun s => per (P.flatIndexEquiv.symm s).1
      periodic := ?_
      weight_pos := ?_
      sameMPV := ?_ }
  · intro s
    exact isPeriodic_smul_of_norm_one (phase_norm_one (hμ s))
      (blocks s) (hPer _)
  · intro s
    constructor
    · simpa [positiveRealWeights] using norm_pos_iff.mpr (hμ s)
    · simp [positiveRealWeights]
  · exact sameMPV₂_toTensorFromBlocks_phaseNormalized hμ

/-- Equal positive-length matrix-product vectors of two all-length
irreducible-form tensors force equality of their bond dimensions. Zero
summands cannot be hidden in either presentation.
Source: arXiv:1708.00029, Theorem 3.8, lines 643--693. -/
theorem IsIrreducibleForm.bondDim_eq_of_sameMPV₂Pos
    {D₁ D₂ : ℕ} {A : MPSTensor d D₁} {B : MPSTensor d D₂}
    (hA : IsIrreducibleForm A) (hB : IsIrreducibleForm B)
    (hSame : SameMPV₂Pos A B) : D₁ = D₂ := by
  obtain ⟨P, hPDim, ⟨perP, hPPer⟩, hPDistinct, hAP⟩ :=
    hA.exists_full_sectorDecomposition
  obtain ⟨Q, hQDim, ⟨perQ, hQPer⟩, hQDistinct, hBQ⟩ :=
    hB.exists_full_sectorDecomposition
  have hPQ : SameMPV₂Pos P.toTensor Q.toTensor :=
    hAP.symm.trans (hSame.trans hBQ)
  have hDim := SectorDecomposition.totalDim_eq_of_periodic_sameMPV₂Pos
    P Q perP hPPer perQ hQPer hPDistinct hQDistinct hPQ
  exact hPDim.symm.trans (hDim.trans hQDim)

/-- A refinement root with the same positive-length vectors as a literal
irreducible-form blocked target has an irreducible-form representative on the
original bond space. The equal-case theorem rules out any zero composition
factor of the root, and positive blocking of the representative gives full
matrix-product-vector equality with the target.

Source: arXiv:1708.00029, Theorem 4.1 forward argument, lines 735--810;
the dimension step uses Theorem 3.8, lines 643--693. -/
theorem exists_irreducibleForm_refinement_root
    {D p : ℕ} (A : MPSTensor d D)
    (C : MPSTensor (blockPhysDim d p) D)
    (hC : IsIrreducibleForm C) (hp : 0 < p)
    (hSame : SameMPV₂Pos (blockTensor A p) C) :
    ∃ (P : SectorDecomposition d) (_hPForm : IsIrreducibleForm P.toTensor),
      P.totalDim = D ∧
      (∃ per : Fin P.basisCount → ℕ,
        ∀ j, IsPeriodic (per j) (P.basis j)) ∧
      SameMPV₂ A P.toTensor ∧
      SameMPV₂ (blockTensor P.toTensor p) C := by
  classical
  obtain ⟨P, _, _, ⟨per, hPer⟩, _, hAP⟩ :=
    exists_active_irreducible_sectorDecomposition A
  let hPForm : IsIrreducibleForm P.toTensor :=
    P.toIsIrreducibleForm per hPer
  have hBlockPForm : IsIrreducibleForm (blockTensor P.toTensor p) :=
    hPForm.blockTensor_isIrreducibleForm hp
  have hBlockSame : SameMPV₂Pos (blockTensor P.toTensor p) C :=
    (sameMPV₂Pos_blockTensor A P.toTensor hAP p hp).symm.trans hSame
  have hDim : P.totalDim = D :=
    hBlockPForm.bondDim_eq_of_sameMPV₂Pos hC hBlockSame
  refine ⟨P, hPForm, hDim, ⟨per, hPer⟩, ?_, ?_⟩
  · exact sameMPV₂_of_sameMPV₂Pos_of_bondDim_eq A P.toTensor hAP hDim.symm
  · exact sameMPV₂_of_sameMPV₂Pos_of_bondDim_eq
      (blockTensor P.toTensor p) C hBlockSame hDim

/-- The canonical refinement root on the original bond space, with the
sector bookkeeping suppressed. Source: arXiv:1708.00029, Theorem 4.1,
lines 735--810. -/
theorem exists_irreducibleForm_refinement_root_tensor
    {D p : ℕ} (A : MPSTensor d D)
    (C : MPSTensor (blockPhysDim d p) D)
    (hC : IsIrreducibleForm C) (hp : 0 < p)
    (hSame : SameMPV₂Pos (blockTensor A p) C) :
    ∃ (A' : MPSTensor d D) (_hA' : IsIrreducibleForm A'),
      SameMPV₂ A A' ∧ SameMPV₂ (blockTensor A' p) C := by
  obtain ⟨P, hPForm, hDim, _, hAP, hBlock⟩ :=
    exists_irreducibleForm_refinement_root A C hC hp hSame
  subst D
  exact ⟨P.toTensor, hPForm, hAP, hBlock⟩

end MPSTensor
