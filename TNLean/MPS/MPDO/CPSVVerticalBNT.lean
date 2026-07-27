/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.CPSVOriginalSpaceLemmaL
import TNLean.MPS.MPDO.SectorCompressionSeparation

/-!
# Sector-compression separation for a literal CPSV canonical form

This file proves the finite-chain sector-compression separation step in the
vertical canonical-form argument for matrix product density operators.  The
proof applies physical first-site Lemma L in the original bond coordinates of
a literal CPSV canonical form.

## Main statement

* `MPSTensor.IsCPSVCanonicalForm.exists_sectorCompression_ne_zero_of_corner`:
  every nonzero vertical corner has a nonzero finite-chain compression.

## References

* Cirac--Perez-Garcia--Schuch--Verstraete, arXiv:1606.00608, Appendix C.3,
  Lemma L, lines 1835--1858, and Proposition 4.13, lines 1898--1902.
-/

open scoped Matrix

namespace MPSTensor.IsCPSVCanonicalForm

variable {d D : ℕ}

/-- A nonzero vertical corner of a literal CPSV canonical-form tensor has a
nonzero first-site sector compression at some finite chain length.

If every compression vanished, the resulting equality of first-site actions
would make the two-sided insertion by the corner matrix zero by Lemma L.  This
would force the original vertical corner to vanish.  The theorem is the
separation step used for $0 \ne P_{\alpha,k}H^{(N)}P_{\alpha,k}$ in the proof
of Proposition 4.13 of arXiv:1606.00608, lines 1898--1902, using Appendix C.3,
Lemma L, lines 1835--1858. -/
theorem exists_sectorCompression_ne_zero_of_corner
    (M : MPOTensor d D)
    (hCanonical : MPSTensor.IsCPSVCanonicalForm M.toMPSTensor)
    (P : Matrix (Fin d) (Fin d) ℂ)
    (hcorner : ∃ v, P * MPOTensor.verticalTensor M v * P ≠ 0) :
    ∃ N, MPOTensor.sectorCompression M P N ≠ 0 := by
  exact MPOTensor.exists_sectorCompression_ne_zero_of_corner_of_insertedTensor_eq M
    (hCanonical.insertedTensor_eq_of_firstSiteActionAgree M.toMPSTensor) P hcorner

end MPSTensor.IsCPSVCanonicalForm
