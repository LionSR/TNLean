/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.PhysicalSectorVirtualTransport

/-!
# Virtual compression of physical-sector factorizations

A rectangular change of virtual coordinates is a virtual-matrix transport
whose left matrix is the adjoint of its right matrix.  The neighboring
contraction therefore inserts the range matrix of the coordinate map.

## References

* arXiv:1606.00608, Section 2.3, equation `II_Aiplusk1`, lines 195--219
* arXiv:1606.00608, Appendix C.2, equations `AppUkU=rl` and `etarl`,
  lines 1381--1450
-/

open scoped Matrix

namespace MPOTensor.PhysicalSectorFactorization

variable {d D E : ℕ} {K : MPOTensor d D} {L : MPOTensor d E}

/-- Transport a physical-sector factorization through a rectangular virtual
compression.

The physical-sector decomposition and physical isometry are unchanged.  The
coordinate map and its adjoint are absorbed into the right and left virtual
tensor families, respectively.

Source context: arXiv:1606.00608, Section 2.3, equation `II_Aiplusk1`, lines
195--219, and Appendix C.2, equation `AppUkU=rl`, lines 1381--1388. -/
noncomputable def ofVirtualCompression (F : PhysicalSectorFactorization K)
    (V : Matrix (Fin D) (Fin E) ℂ)
    (hCompression : ∀ i : Fin (d * d),
      L.toMPSTensor i = Vᴴ * K.toMPSTensor i * V) :
    PhysicalSectorFactorization L :=
  F.ofVirtualMatrices Vᴴ V hCompression

/-- Virtual compression replaces the ordinary neighboring contraction by the
matrix-weighted contraction through `V * Vᴴ`.

No positivity is asserted: positivity of the ordinary neighboring contraction
does not by itself establish positivity after inserting the range matrix.

Source context: arXiv:1606.00608, Section 2.3, equation `II_Aiplusk1`, lines
195--219, and Appendix C.2, equation `etarl`, lines 1441--1445. -/
@[simp] theorem ofVirtualCompression_neighboringOperator
    (F : PhysicalSectorFactorization K) (V : Matrix (Fin D) (Fin E) ℂ)
    (hCompression : ∀ i : Fin (d * d),
      L.toMPSTensor i = Vᴴ * K.toMPSTensor i * V)
    (k h : Fin F.sectorCount) :
    (F.ofVirtualCompression V hCompression).neighboringOperator k h =
      F.neighboringOperatorWithMatrix (V * Vᴴ) k h :=
  F.ofVirtualMatrices_neighboringOperator Vᴴ V hCompression k h

end MPOTensor.PhysicalSectorFactorization
