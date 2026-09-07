/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Periodic.EqualCaseGlobal
import TNLean.MPS.Periodic.PeriodExistence

/-!
# The periodic fundamental theorems over the source's irreducible form

The source states its two fundamental theorems for tensors in irreducible form,
where a block is required only to have an irreducible transfer map of spectral
radius one (arXiv:1708.00029, lines 248--261).  The period of a block is
derived from those two conditions at lines 257--258 and appears in the
conclusion of the theorems, not among their hypotheses.

This file restates the proportional case (arXiv:1708.00029, Theorem 3.4, lines
613--623) and the equal case (Theorem 3.8, lines 643--693) over exactly those
two conditions, producing the periods rather than receiving them.  The periods
come from
`MPSTensor.exists_isSpectrallyPeriodic_of_irreducible_of_spectralRadius_one`.

## Main results

* `MPSTensor.fundamentalTheorem_periodic_proportional_irreducibleForm`
* `MPSTensor.fundamentalTheorem_periodic_equalCase_derivedPeriods`

## References

* De las Cuevas, Cirac, Schuch, Pérez-García, arXiv:1708.00029, Theorems 3.4
  and 3.8.
-/

open scoped Matrix BigOperators Matrix.Norms.Operator

namespace MPSTensor

variable {d : ℕ}

/-- **Fundamental theorem for matrix product states, proportional case, over
the source's irreducible form.**

The two block families are required only to be irreducible with transfer maps
of spectral radius one, which is the source's irreducible form at
arXiv:1708.00029, lines 248--261.  The periods are produced by the theorem,
as at lines 257--258, together with the witnesses that each block is spectrally
periodic of the produced period; the matching bijection then equates the
periods of matched blocks.

Source: arXiv:1708.00029, theorem `thm:bd`, lines 613--623, over the
irreducible forms `eq:bdnr`, line 294, and `eq:Bbdnr`, line 582. -/
theorem fundamentalTheorem_periodic_proportional_irreducibleForm
    (P Q : SectorDecomposition d)
    (hIrrP : ∀ j, Kraus.IsIrreducibleFamily (P.basis j))
    (hRadP : ∀ j,
      spectralRadius ℂ
        ((Module.End.toContinuousLinearMap
            (Matrix (Fin (P.basisDim j)) (Fin (P.basisDim j)) ℂ))
          (Kraus.transferMap (d := d) (D := P.basisDim j) (P.basis j))) = 1)
    (hIrrQ : ∀ k, Kraus.IsIrreducibleFamily (Q.basis k))
    (hRadQ : ∀ k,
      spectralRadius ℂ
        ((Module.End.toContinuousLinearMap
            (Matrix (Fin (Q.basisDim k)) (Fin (Q.basisDim k)) ℂ))
          (Kraus.transferMap (d := d) (D := Q.basisDim k) (Q.basis k))) = 1)
    (hNonRepP : ∀ i j, i ≠ j → ¬ HetRepeatedBlocks (P.basis i) (P.basis j))
    (hNonRepQ : ∀ i j, i ≠ j → ¬ HetRepeatedBlocks (Q.basis i) (Q.basis j))
    (hProp : NonzeroProportionalMPV₂ P.toTensor Q.toTensor) :
    ∃ (periodP : Fin P.basisCount → ℕ) (periodQ : Fin Q.basisCount → ℕ),
      (∀ j, IsSpectrallyPeriodic (periodP j) (P.basis j)) ∧
      (∀ k, IsSpectrallyPeriodic (periodQ k) (Q.basis k)) ∧
      PeriodicBasisMatchingWitness P.basis Q.basis periodP periodQ := by
  choose periodP hPerP using fun j =>
    exists_isSpectrallyPeriodic_of_irreducible_of_spectralRadius_one
      (hIrrP j) (hRadP j)
  choose periodQ hPerQ using fun k =>
    exists_isSpectrallyPeriodic_of_irreducible_of_spectralRadius_one
      (hIrrQ k) (hRadQ k)
  exact ⟨periodP, periodQ, hPerP, hPerQ,
    fundamentalTheorem_periodic_proportional_sectorDecomposition P Q periodP periodQ
      hPerP hPerQ hNonRepP hNonRepQ hProp⟩

/-- **Fundamental theorem for matrix product states, equal case, over the
source's irreducible form.**

The two block families are required only to be irreducible with transfer maps
of spectral radius one, which is the source's irreducible form at
arXiv:1708.00029, lines 248--261.  The periods are produced by the theorem, as
at lines 257--258, together with the witnesses that each block is spectrally
periodic of the produced period; every later clause speaks about those same
periods.

Source: arXiv:1708.00029, theorem `thm:bdequal`, lines 643--693, over the
irreducible forms `eq:bdnr`, line 294, and `eq:Bbdnr`, line 582. -/
theorem fundamentalTheorem_periodic_equalCase_derivedPeriods
    (P Q : SectorDecomposition d)
    (hIrrP : ∀ j, Kraus.IsIrreducibleFamily (P.basis j))
    (hRadP : ∀ j,
      spectralRadius ℂ
        ((Module.End.toContinuousLinearMap
            (Matrix (Fin (P.basisDim j)) (Fin (P.basisDim j)) ℂ))
          (Kraus.transferMap (d := d) (D := P.basisDim j) (P.basis j))) = 1)
    (hIrrQ : ∀ k, Kraus.IsIrreducibleFamily (Q.basis k))
    (hRadQ : ∀ k,
      spectralRadius ℂ
        ((Module.End.toContinuousLinearMap
            (Matrix (Fin (Q.basisDim k)) (Fin (Q.basisDim k)) ℂ))
          (Kraus.transferMap (d := d) (D := Q.basisDim k) (Q.basis k))) = 1)
    (hNonRepP : ∀ i j, i ≠ j → ¬ HetRepeatedBlocks (P.basis i) (P.basis j))
    (hNonRepQ : ∀ i j, i ≠ j → ¬ HetRepeatedBlocks (Q.basis i) (Q.basis j))
    (hSame : SameMPV₂Pos P.toTensor Q.toTensor) :
    ∃ (periodP : Fin P.basisCount → ℕ) (periodQ : Fin Q.basisCount → ℕ),
      (∀ j, IsSpectrallyPeriodic (periodP j) (P.basis j)) ∧
      (∀ k, IsSpectrallyPeriodic (periodQ k) (Q.basis k)) ∧
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
  choose periodP hPerP using fun j =>
    exists_isSpectrallyPeriodic_of_irreducible_of_spectralRadius_one
      (hIrrP j) (hRadP j)
  choose periodQ hPerQ using fun k =>
    exists_isSpectrallyPeriodic_of_irreducible_of_spectralRadius_one
      (hIrrQ k) (hRadQ k)
  exact ⟨periodP, periodQ, hPerP, hPerQ,
    fundamentalTheorem_periodic_equalCase_irreducibleForm P Q periodP periodQ
      hPerP hPerQ hNonRepP hNonRepQ hSame⟩

end MPSTensor
