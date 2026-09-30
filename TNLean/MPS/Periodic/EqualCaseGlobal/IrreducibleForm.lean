/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Periodic.EqualCaseGlobal.Canonical

/-!
# Equal-case fundamental theorem without trace-preserving normalization

Blockwise Perron similarities transfer the canonical equal-case theorem to
irreducible form while preserving the multiplicity gauge.
Source: arXiv:1708.00029, `eq:unital` and `thm:bdequal`, lines 313–332 and 643–693.
-/

open scoped Matrix BigOperators

namespace MPSTensor

variable {d : ℕ}

/-! ## Removing the trace-preserving restriction -/

/-- **Fundamental theorem for matrix product states, equal case, irreducible
form.**

This is the preceding theorem without the left-canonical normalization of the
blocks, that is, over the source's irreducible form rather than over the
trace-preserving normalization of `eq:unital`. The similarity produced here is
invertible; unitarity is a feature of the normalized form and is not asserted.

The proof normalizes each representative by its positive-definite adjoint
Perron fixed point, which is the source construction at
arXiv:1708.00029, lines 313--332 (equation `eq:unital`, line 316). That
similarity is blockwise, so it leaves every multiplicity entry, every
multiplicity power sum, and the multiplicity gauge itself unchanged; the
multiplicity gauge is scalar on each block and therefore commutes with the
block-diagonal normalizing similarity. Only the global similarity between the
two tensors is conjugated.

Source: arXiv:1708.00029, theorem `thm:bdequal`, lines 643--693, over the
irreducible forms `eq:bdnr`, line 294, and `eq:Bbdnr`, line 582.

The periods are received as input here, together with witnesses that each block
is spectrally periodic of the given period, whereas the source derives the
period of a block from irreducibility and spectral radius one at lines
257--258, citing Wolf. This is the working form; the source statement, with the
periods produced from the source's two conditions on the blocks, is
`fundamentalTheorem_periodic_equalCase_derivedPeriods`. See
`docs/paper-gaps/dccsp17_periodic_overlap_route_alignment.tex`, section "The
periods of an irreducible-form block: restriction eliminated". -/
theorem fundamentalTheorem_periodic_equalCase_irreducibleForm
    (P Q : SectorDecomposition d)
    (periodP : Fin P.basisCount → ℕ) (periodQ : Fin Q.basisCount → ℕ)
    (hPerP : ∀ j, IsSpectrallyPeriodic (periodP j) (P.basis j))
    (hPerQ : ∀ k, IsSpectrallyPeriodic (periodQ k) (Q.basis k))
    (hNonRepP : ∀ i j, i ≠ j → ¬ HetRepeatedBlocks (P.basis i) (P.basis j))
    (hNonRepQ : ∀ i j, i ≠ j → ¬ HetRepeatedBlocks (Q.basis i) (Q.basis j))
    (hSame : SameMPV₂Pos P.toTensor Q.toTensor) :
    ∃ (perm : Fin P.basisCount ≃ Fin Q.basisCount) (ξ : Fin P.basisCount → ℂ)
      (z : (j : Fin P.basisCount) → Fin (P.copies j) → ℂ),
      (∀ j, ‖ξ j‖ = 1) ∧
      (∀ j, periodP j = periodQ (perm j)) ∧
      (∀ j, ScalarGaugeEquiv (ξ j) (P.basis j) (Q.basis (perm j))) ∧
      (∀ j, HetRepeatedBlocks (P.basis j) (Q.basis (perm j))) ∧
      (∀ j, Matrix.diagonal (z j) ^ periodP j = 1) ∧
      (∀ j, ∃ (_hCopies : P.copies j = Q.copies (perm j))
              (τ : Fin (P.copies j) ≃ Fin (Q.copies (perm j))),
            Matrix.diagonal (z j) * Matrix.diagonal (fun q => ξ j * P.weight j q) =
              Matrix.diagonal (fun q => Q.weight (perm j) (τ q))) ∧
      ∃ (Y : Matrix (Fin P.totalDim) (Fin Q.totalDim) ℂ)
        (Y' : Matrix (Fin Q.totalDim) (Fin P.totalDim) ℂ),
        Y * Y' = 1 ∧ Y' * Y = 1 ∧
        blockScalarMatrix P.flatDim (P.flatCopyScalar z) ^
          (Finset.univ.lcm periodP) = 1 ∧
        (∀ i : Fin d,
          blockScalarMatrix P.flatDim (P.flatCopyScalar z) * P.toTensor i =
            P.toTensor i * blockScalarMatrix P.flatDim (P.flatCopyScalar z)) ∧
        (∀ i : Fin d,
          blockScalarMatrix P.flatDim (P.flatCopyScalar z) * P.toTensor i =
            Y * Q.toTensor i * Y') ∧
        SameMPV₂Pos P.toTensor
          (fun i =>
            blockScalarMatrix P.flatDim (P.flatCopyScalar z) * P.toTensor i) := by
  classical
  -- normalize both bases by the blockwise Perron similarity
  obtain ⟨basisP, hGaugeP, hPeriodicP, -⟩ :=
    P.exists_isPeriodic_replaceBasis periodP hPerP
  obtain ⟨basisQ, hGaugeQ, hPeriodicQ, -⟩ :=
    Q.exists_isPeriodic_replaceBasis periodQ hPerQ
  have hRepP : ∀ j, HetRepeatedBlocks (P.basis j) (basisP j) := fun j =>
    (hGaugeP j).toHetRepeatedBlocks
  have hRepQ : ∀ k, HetRepeatedBlocks (Q.basis k) (basisQ k) := fun k =>
    (hGaugeQ k).toHetRepeatedBlocks
  choose XPb hXPb using hGaugeP
  choose XQb hXQb using hGaugeQ
  set GP : GL (Fin P.totalDim) ℂ :=
    globalGaugeOfBlocks (matched_block_gauge (Q := P) XPb) with hGPdef
  set GQ : GL (Fin Q.totalDim) ℂ :=
    globalGaugeOfBlocks (matched_block_gauge (Q := Q) XQb) with hGQdef
  set XP : Matrix (Fin P.totalDim) (Fin P.totalDim) ℂ :=
    (GP : Matrix (Fin P.totalDim) (Fin P.totalDim) ℂ) with hXPdef
  set XP' : Matrix (Fin P.totalDim) (Fin P.totalDim) ℂ :=
    ((GP⁻¹ : GL (Fin P.totalDim) ℂ) :
      Matrix (Fin P.totalDim) (Fin P.totalDim) ℂ) with hXP'def
  set XQ : Matrix (Fin Q.totalDim) (Fin Q.totalDim) ℂ :=
    (GQ : Matrix (Fin Q.totalDim) (Fin Q.totalDim) ℂ) with hXQdef
  set XQ' : Matrix (Fin Q.totalDim) (Fin Q.totalDim) ℂ :=
    ((GQ⁻¹ : GL (Fin Q.totalDim) ℂ) :
      Matrix (Fin Q.totalDim) (Fin Q.totalDim) ℂ) with hXQ'def
  have hXPmul : XP * XP' = 1 := by rw [hXPdef, hXP'def]; simp
  have hXPmul' : XP' * XP = 1 := by rw [hXPdef, hXP'def]; simp
  have hXQmul : XQ * XQ' = 1 := by rw [hXQdef, hXQ'def]; simp
  have hXQmul' : XQ' * XQ = 1 := by rw [hXQdef, hXQ'def]; simp
  have hPconj : ∀ i : Fin d,
      (P.replaceBasis basisP).toTensor i = XP * P.toTensor i * XP' :=
    toTensorFromBlocks_eq_globalGaugeOfBlocks_conj (d := d) P.flatWeight
      P.flatBasis (P.replaceBasis basisP).flatBasis
      (matched_block_gauge (Q := P) XPb)
      (fun s i => hXPb (P.flatIndexEquiv.symm s).1 i)
  have hQconj : ∀ i : Fin d,
      (Q.replaceBasis basisQ).toTensor i = XQ * Q.toTensor i * XQ' :=
    toTensorFromBlocks_eq_globalGaugeOfBlocks_conj (d := d) Q.flatWeight
      Q.flatBasis (Q.replaceBasis basisQ).flatBasis
      (matched_block_gauge (Q := Q) XQb)
      (fun s i => hXQb (Q.flatIndexEquiv.symm s).1 i)
  have hGP : GaugeEquiv P.toTensor (P.replaceBasis basisP).toTensor :=
    ⟨GP, hPconj⟩
  have hGQ : GaugeEquiv Q.toTensor (Q.replaceBasis basisQ).toTensor :=
    ⟨GQ, hQconj⟩
  -- transport the hypotheses to the normalized decompositions
  have hNonRepP' : ∀ i j, i ≠ j →
      ¬ HetRepeatedBlocks ((P.replaceBasis basisP).basis i)
        ((P.replaceBasis basisP).basis j) := by
    intro i j hij hRep
    exact hNonRepP i j hij ((hRepP i).trans (hRep.trans (hRepP j).symm))
  have hNonRepQ' : ∀ i j, i ≠ j →
      ¬ HetRepeatedBlocks ((Q.replaceBasis basisQ).basis i)
        ((Q.replaceBasis basisQ).basis j) := by
    intro i j hij hRep
    exact hNonRepQ i j hij ((hRepQ i).trans (hRep.trans (hRepQ j).symm))
  have hSame' : SameMPV₂Pos (P.replaceBasis basisP).toTensor
      (Q.replaceBasis basisQ).toTensor := by
    intro N hN σ
    calc mpv (P.replaceBasis basisP).toTensor σ = mpv P.toTensor σ :=
          (GaugeEquiv.sameMPV hGP N σ).symm
      _ = mpv Q.toTensor σ := hSame N hN σ
      _ = mpv (Q.replaceBasis basisQ).toTensor σ := GaugeEquiv.sameMPV hGQ N σ
  obtain ⟨perm, ξ, z, hξ, hPeriodEq, hScalar, hMatch', hZdiag, hBlock, hEqual⟩ :=
    fundamentalTheorem_periodic_equalCase_sectorDecomposition
      (P.replaceBasis basisP) (Q.replaceBasis basisQ) periodP periodQ
      hPeriodicP hPeriodicQ hNonRepP' hNonRepQ' hSame'
  have hzm : ∀ j q, z j q ^ periodP j = 1 := by
    intro j q
    have hd := hZdiag j
    rw [Matrix.diagonal_pow] at hd
    have := congrArg (fun M : Matrix (Fin (P.copies j)) (Fin (P.copies j)) ℂ =>
      M q q) hd
    simpa [Matrix.diagonal_apply_eq, Pi.pow_apply] using this
  -- the multiplicity gauge is unchanged: it is scalar on each block
  set Z : Matrix (Fin P.totalDim) (Fin P.totalDim) ℂ :=
    blockScalarMatrix P.flatDim (P.flatCopyScalar z) with hZdef
  have hZcomm : Z * XP = XP * Z := by
    rw [hZdef, hXPdef, hGPdef]
    exact blockScalarMatrix_globalGaugeOfBlocks_comm _ _
  have hZP : ∀ i : Fin d, Z * P.toTensor i = P.toTensor i * Z := by
    intro i
    rw [hZdef]
    exact (blockScalarMatrix_mul_toTensorFromBlocks _ P.flatWeight P.flatBasis i).trans
      (toTensorFromBlocks_mul_blockScalarMatrix _ P.flatWeight P.flatBasis i).symm
  have hglobal : ∃ (Y : Matrix (Fin P.totalDim) (Fin Q.totalDim) ℂ)
      (Y' : Matrix (Fin Q.totalDim) (Fin P.totalDim) ℂ),
      Y * Y' = 1 ∧ Y' * Y = 1 ∧ Z ^ (Finset.univ.lcm periodP) = 1 ∧
      (∀ i : Fin d, Z * (XP * P.toTensor i * XP') =
        Y * (XQ * Q.toTensor i * XQ') * Y') := by
    obtain ⟨Y, Y', h1, h2, -, h3, -, h5, -⟩ := hEqual
    refine ⟨Y, Y', h1, h2, h3, fun i => ?_⟩
    rw [← hPconj i, ← hQconj i]
    exact h5 i
  obtain ⟨Y, Y', hYY', hY'Y, hZLpow, hgauge⟩ := hglobal
  have hmove : ∀ K : Matrix (Fin P.totalDim) (Fin P.totalDim) ℂ,
      Z * (XP * K) = XP * (Z * K) := by
    intro K
    rw [← Matrix.mul_assoc, hZcomm, Matrix.mul_assoc]
  have hcancel : ∀ M : Matrix (Fin P.totalDim) (Fin P.totalDim) ℂ,
      XP' * (XP * M * XP') * XP = M := by
    intro M
    simp only [Matrix.mul_assoc]
    rw [hXPmul', mul_one, ← Matrix.mul_assoc, hXPmul', one_mul]
  refine ⟨perm, ξ, z, hξ, hPeriodEq, ?_, ?_, hZdiag, hBlock,
    XP' * Y * XQ, XQ' * Y' * XP, ?_, ?_, hZLpow, hZP, ?_, ?_⟩
  · exact fun j =>
      ((hScalar j).of_gaugeEquiv_left ⟨XPb j, hXPb j⟩).of_gaugeEquiv_right
        ⟨XQb (perm j), hXQb (perm j)⟩
  · exact fun j => (hRepP j).trans ((hMatch' j).trans (hRepQ (perm j)).symm)
  · simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc XQ XQ', hXQmul, Matrix.one_mul,
      ← Matrix.mul_assoc Y Y', hYY', Matrix.one_mul]
    exact hXPmul'
  · simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc XP XP', hXPmul, Matrix.one_mul,
      ← Matrix.mul_assoc Y' Y, hY'Y, Matrix.one_mul]
    exact hXQmul'
  · intro i
    have h : XP * (Z * P.toTensor i) * XP' =
        Y * (XQ * Q.toTensor i * XQ') * Y' := by
      rw [← hgauge i]
      simp only [Matrix.mul_assoc]
      exact (hmove (P.toTensor i * XP')).symm
    calc Z * P.toTensor i
        = XP' * (XP * (Z * P.toTensor i) * XP') * XP := (hcancel _).symm
      _ = XP' * (Y * (XQ * Q.toTensor i * XQ') * Y') * XP := by rw [h]
      _ = XP' * Y * XQ * Q.toTensor i * (XQ' * Y' * XP) := by
          simp only [Matrix.mul_assoc]
  · exact sameMPV₂Pos_blockScalarMatrix_mul_toTensor P z periodP hzm
      (fun j N σ hnd => by
        rw [GaugeEquiv.sameMPV ⟨XPb j, hXPb j⟩ N σ]
        exact pgvwc07_stateVector_eq_zero_of_not_dvd (basisP j) (hPeriodicP j) hnd σ)

end MPSTensor
