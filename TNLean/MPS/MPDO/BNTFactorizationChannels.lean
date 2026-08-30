/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.BNTChannelComposition
import TNLean.MPS.MPDO.PhysicalSectorPhysicalTransport

/-!
# Blocked renormalization channels from representative trace factorizations

This file combines the one-factorization channel construction of
Proposition C.7 with the projector-controlled assembly across the outer
basis-of-normal-tensors sectors.  Given a neighboring trace factorization for
every common-weight absorbed representative, the two-site blocking of the
complete tensor is a renormalization fixed point via trace-preserving
completely positive maps.  The outer supports are constructed here rather
than assumed, so the hypotheses are exactly the per-representative
factorization data together with the standing layer orthogonality and
one-site spanning conditions.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Appendix C.2, Proposition `prop2to5`, lines 1810--1817, the closing proof
  at lines 1821--1825, and the weight commonization at lines 1646--1665
-/

open scoped Matrix ComplexOrder

namespace MPOTensor

namespace PhysicalSectorFactorization.NeighboringTraceFactorization

variable {d D : ℕ} {K : MPOTensor d D}

/-- A physical-sector factorization with a single sector and a positive
semidefinite neighboring operator of unit trace has a neighboring trace
factorization with both coefficient families identically one.

This packages the coarsest sector labeling: after merging all labels into
one, the rank-one trace condition reduces to unit normalization of the sole
neighboring operator.

Source: arXiv:1606.00608, Appendix C.2, lines 1389--1403. -/
noncomputable def ofOneSector (F : PhysicalSectorFactorization K)
    (hOne : F.sectorCount = 1)
    (hPos : ∀ k h, (F.neighboringOperator k h).PosSemidef)
    (hTrace : ∀ k h, (F.neighboringOperator k h).trace = 1) :
    NeighboringTraceFactorization F where
  neighboringOperator_pos := hPos
  a := fun _ ↦ 1
  b := fun _ ↦ 1
  trace_neighboringOperator := by
    intro k h
    rw [hTrace k h]
    norm_num
  sum_mul := by simp [hOne]

end PhysicalSectorFactorization.NeighboringTraceFactorization

variable {d : ℕ}

/-- An exact canonical BNT reconstruction with copy-independent absorbed
weights is, after two-site blocking, a renormalization fixed point via
trace-preserving completely positive maps, whenever every absorbed
representative carries a physical-sector factorization with a neighboring
trace factorization and the absorbed layers satisfy the unstarred
orthogonality identities.

The proof first constructs the pairwise orthogonal two-sided outer physical
supports, realizing the projection onto each local subspace at source lines
1815--1816, and then assembles the per-representative channels across those
supports.  The per-representative channels are supplied by the
one-factorization construction of Proposition C.7 together with the
twice-applied channel observation at lines 1821--1825.

**Scope restriction (supplied per-representative factorizations):** the
neighboring trace factorizations of the absorbed representatives are assumed
here. The printed route to Proposition `prop2to5` obtains them from saturation
of the area law and zero correlation length through Proposition `prop2to3`,
but that representativewise assertion is false under the complete standing
hypotheses. Thus this theorem proves the conditional channel construction but
does not prove Proposition `prop2to5`. The counterexample does not exclude
different channel maps, so the bare conclusion of `prop2to5` is neither proved
nor refuted. See
<https://sirui-lu.com/QICLean/paper-gaps/cpgsv17_pf_rank_one.pdf>.

Source: arXiv:1606.00608, Appendix C.2, Proposition `prop2to5`, lines
1810--1817; the closing proof at lines 1821--1825; and the weight
commonization at lines 1646--1665. -/
theorem blockTwo_isRFPViaTS_of_bntLayerOrthogonal_of_physicalSectorFactorization_of_commonWeight
    (S : MPSTensor.SectorDecomposition (d * d))
    (hWeight : ∀ (j : Fin S.basisCount) (q q' : Fin (S.copies j)),
      S.weight j q = S.weight j q')
    (M : MPOTensor d S.totalDim)
    (G : GL (Fin S.totalDim) ℂ)
    (hG : ∀ i, M.toMPSTensor i =
      (G : Matrix (Fin S.totalDim) (Fin S.totalDim) ℂ) * S.toTensor i *
        (↑(G⁻¹) : Matrix (Fin S.totalDim) (Fin S.totalDim) ℂ))
    (hSpan : MPSTensor.WordTupleSpanTop S.basis 1)
    (hLayer : IsBNTLayerOrthogonal
      (fun s ↦ commonWeightAbsorbedBasisMPOTensor S hWeight s))
    (F : (s : Fin S.basisCount) → PhysicalSectorFactorization
      (commonWeightAbsorbedBasisMPOTensor S hWeight s))
    (hTrace : ∀ s,
      PhysicalSectorFactorization.NeighboringTraceFactorization (F s)) :
    IsRFPViaTS (blockTwo M) := by
  obtain ⟨P, hProj, hOrth, hSupport⟩ :=
    exists_pairwise_orthogonal_twoSided_physicalSupport_commonWeightAbsorbedBasis
      S hWeight hSpan F
      (fun s k h ↦ (hTrace s).neighboringOperator_pos k h) hLayer
  exact blockTwo_isRFPViaTS_of_commonWeightAbsorbedBNTChannels_of_orthogonalSupports
    S hWeight M G hG P hProj hOrth hSupport
    (fun s ↦ (hTrace s).blockTwo_isRFPViaTS)

/-- The coarsened single-sector special case: if every absorbed
representative carries a physical-sector factorization with one sector whose
sole neighboring operator is positive semidefinite of unit trace, then the
two-site blocking of the complete tensor is a renormalization fixed point
via trace-preserving completely positive maps.

This is the extreme case of sector coarsening, in which all outer-pair
labels of each representative are merged into one; the explicit
active-spanning tensor realizes exactly this situation after merging its
four selected sectors.

**Scope restriction (supplied per-representative factorizations):** the
single-sector factorizations are assumed here. They do not follow in general
from saturation of the area law and zero correlation length, because the
printed representative-factorization assertion is false under the complete
standing hypotheses. This theorem proves the conditional channel construction
but does not decide whether different channels establish the bare source
conclusion. See
<https://sirui-lu.com/QICLean/paper-gaps/cpgsv17_pf_rank_one.pdf>.

Source: arXiv:1606.00608, Appendix C.2, Proposition `prop2to5`, lines
1810--1817, and lines 1389--1403. -/
theorem blockTwo_isRFPViaTS_of_bntLayerOrthogonal_of_oneSectorFactorization_of_commonWeight
    (S : MPSTensor.SectorDecomposition (d * d))
    (hWeight : ∀ (j : Fin S.basisCount) (q q' : Fin (S.copies j)),
      S.weight j q = S.weight j q')
    (M : MPOTensor d S.totalDim)
    (G : GL (Fin S.totalDim) ℂ)
    (hG : ∀ i, M.toMPSTensor i =
      (G : Matrix (Fin S.totalDim) (Fin S.totalDim) ℂ) * S.toTensor i *
        (↑(G⁻¹) : Matrix (Fin S.totalDim) (Fin S.totalDim) ℂ))
    (hSpan : MPSTensor.WordTupleSpanTop S.basis 1)
    (hLayer : IsBNTLayerOrthogonal
      (fun s ↦ commonWeightAbsorbedBasisMPOTensor S hWeight s))
    (F : (s : Fin S.basisCount) → PhysicalSectorFactorization
      (commonWeightAbsorbedBasisMPOTensor S hWeight s))
    (hOne : ∀ s, (F s).sectorCount = 1)
    (hPos : ∀ s k h, ((F s).neighboringOperator k h).PosSemidef)
    (hUnit : ∀ s k h, ((F s).neighboringOperator k h).trace = 1) :
    IsRFPViaTS (blockTwo M) :=
  blockTwo_isRFPViaTS_of_bntLayerOrthogonal_of_physicalSectorFactorization_of_commonWeight
    S hWeight M G hG hSpan hLayer F
    (fun s ↦ .ofOneSector (F s) (hOne s) (hPos s) (hUnit s))

end MPOTensor
