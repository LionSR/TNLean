/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Circuit.Gates.Permutation
import TNLean.Circuit.SitewiseTensorSupport
import TNLean.PEPS.Approximation.SheetSwapCorrection

/-!
# Support of the regional swap in paired site coordinates

Pairing the two local coordinates at each site identifies the two-copy space
with a single configuration space of local dimension `q * q`. In these
coordinates, the regional sheet swap acts only on its original region.

## References

* OpenAI, *Polynomial PEPS approximation of gapped square-grid ground states*
  (September 24, 2026), `02-information.tex`, lines 416–424 and 513–524,
  revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

open Matrix QuantumCircuit

namespace TNLean.PEPS.EncodedFrame

/-- The actual sheet swap is supported on its original region after pairing
the two configuration values at every site. Empty regions, empty site types,
and zero local dimension are included.

Source: polynomial-PEPS manuscript, `02-information.tex`, lines 416–424 and 513–524. -/
theorem reindex_sheetSwapOp_mem_supportedOperators
    {ι : Type*} [Fintype ι] [DecidableEq ι] (q : ℕ) (R : Finset ι) :
    Matrix.reindex (sitePairConfigurationEquiv ι q q)
        (sitePairConfigurationEquiv ι q q) (sheetSwapOp q R) ∈
      supportedOperators (q * q) (R : Set ι) := by
  classical
  rw [Matrix.reindex_apply, sheetSwapOp, Matrix.toMatrix_toPEquiv_submatrix]
  apply IsLocalPerm.permMatrix_mem_supportedOperators
  constructor
  done

end TNLean.PEPS.EncodedFrame
