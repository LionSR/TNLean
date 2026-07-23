/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.CyclicActiveMarkovDecomposition
import TNLean.MPS.MPDO.PhysicalSupportSALTransport
import TNLean.MPS.MPDO.SALArbitraryCut

/-!
# Saturated area law from cyclic-active Markov decompositions

This file combines the all-cut quantum-Markov decomposition in physical-sector
coordinates with the entropy criterion for saturation of the area law and
isometric physical-basis transport.

## Main statement

- `MPOTensor.PhysicalSectorFactorization.isSAL_of_isSourceZCL`: an injective
  source-ZCL tensor with a positive physical-sector factorization satisfies SAL.

## Reference

* arXiv:1606.00608, Appendix C.2, Proposition 4to2, lines 1597--1619.
-/

open scoped Matrix ComplexOrder

namespace MPOTensor.PhysicalSectorFactorization

variable {d D : ℕ} {K : MPOTensor d D}

/-- An injective tensor with source zero correlation length satisfies the
saturated area law when it admits a physical-sector factorization with
positive semidefinite neighboring operators.

The proof constructs the quantum-Markov decomposition of every admissible
one-site cut in physical-sector coordinates, applies the all-cut entropy
criterion there, and descends through the isometric physical-coordinate map.

Source: arXiv:1606.00608, Appendix C.2, Proposition `4to2`, lines
1597--1619.

**Scope restriction (physical-sector factorization):** The source assumes a
single translation-invariant commuting positive bond, whereas this theorem
assumes its physical-sector factorization explicitly. The missing construction
from the source hypothesis is recorded in
`docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`. -/
theorem isSAL_of_isSourceZCL
    (F : PhysicalSectorFactorization K) [NeZero D]
    (hK : K.IsInjective)
    (hpos : ∀ q h, (F.neighboringOperator q h).PosSemidef)
    (hZCL : K.IsSourceZCL) :
    IsSAL K := by
  have hCoordinateMPDO : IsMPDO F.sectorCoordinateTensor := by
    intro N hN
    letI : NeZero N := ⟨ne_of_gt hN⟩
    exact F.mpo_sectorCoordinateTensor_posSemidef hpos
  have hCoordinateTrace : ∀ N, 0 < N →
      (mpo F.sectorCoordinateTensor N).trace ≠ 0 := by
    intro N hN
    exact ne_of_gt (F.trace_mpo_sectorCoordinateTensor_pos_of_isSourceZCL
      hpos hZCL hN)
  have hCoordinateSAL : IsSAL F.sectorCoordinateTensor := by
    apply isSAL_of_quantumMarkovDecomposition_tripartite_m
      F.sectorCoordinateTensor hCoordinateMPDO hCoordinateTrace
    intro N m hm1 hmN
    let A := m - 1
    let C := N - m - 1
    have htotal : A + C + 2 = N := by
      dsimp only [A, C]
      omega
    have hMarkov :=
      F.exists_hayashiMarkovDecomposition_cyclicActiveCut_of_isSourceZCL
        hK hpos hZCL A C
    let nAmbient : {n : ℕ // A + 1 + C ≤ n} := ⟨N, by omega⟩
    let nCut : {n : ℕ // A + 1 + C ≤ n} := ⟨A + C + 2, by omega⟩
    have hn : nAmbient = nCut := Subtype.ext htotal.symm
    have hReducedBlockState :
        F.sectorCoordinateTensor.reducedBlockState N (A + 1 + C) (by omega) =
          F.sectorCoordinateTensor.reducedBlockState
            (A + C + 2) (A + 1 + C) (by omega) := by
      simpa only [nAmbient, nCut] using congrArg
        (fun n : {n : ℕ // A + 1 + C ≤ n} ↦
          F.sectorCoordinateTensor.reducedBlockState n.1 (A + 1 + C) n.2) hn
    change Nonempty (Entropy.QuantumMarkovDecomposition
      ((F.sectorCoordinateTensor.reducedBlockState N (A + 1 + C) _).submatrix
        (tripartiteSplitEquiv
          (Fintype.card F.SectorSiteIndex) A 1 C).symm
        (tripartiteSplitEquiv
          (Fintype.card F.SectorSiteIndex) A 1 C).symm))
    rw [hReducedBlockState]
    exact hMarkov
  apply isSAL_of_changePhysicalBasis_isSAL_of_isometry
    F.physicalCoordinateMatrix F.physicalCoordinateMatrix_isometry K
  rw [← F.sectorCoordinateTensor_eq_changePhysicalBasis]
  exact hCoordinateSAL

end MPOTensor.PhysicalSectorFactorization
