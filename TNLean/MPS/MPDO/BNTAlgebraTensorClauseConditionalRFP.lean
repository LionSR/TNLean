/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.BNTAlgebraTensorClauseConditionalPhysicalMaps
import TNLean.MPS.MPDO.BNTAlgebraTensorClauseConditionalUnitary

/-!
# Conditional RFP maps from positive-tail reflected targets

For every paired one-site and two-site BNT sector, a common positive-tail
reflected target gives a unitary conjugacy.  Selecting these unitaries
simultaneously and applying the physical trace-preserving completely positive
maps gives the renormalization identities of Definition 4.1.

The declarations in this file retain the positive-tail reflected targets as
hypotheses.  Their derivation from the tensor-attached algebra product law,
literal CPSV canonical form, and MPDO positivity is given in
`BNTAlgebraTensorClauseReflectedTarget`.

## Main results

* `UnitarySectorConjugacy.ofPositiveTailReflectedTarget`
* `isRFPViaTS_of_positive_tail_reflected_target`

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Appendix C.4, lines 2048--2085
-/

noncomputable section

namespace MPOTensor

namespace BNTAlgebraTensorClause.TwoSiteExactSectorGauge

variable {d D : ℕ} {M : MPOTensor d D} {H : BNTAlgebraTensorClause M}

/-- Positive-tail reflected-target identities for all sectors determine
simultaneous unitary conjugacies between the paired one-site and two-site BNT
tensors.

**Scope restriction (conditional reflected targets):** The reflected-target
identities are assumed rather than derived from the tensor-attached algebra
product law.  This is the comparison omitted from the Appendix C.4 invocation
of Proposition 4.13; see
`docs/paper-gaps/cpsv16_two_site_sector_unitary_gauge_gap.tex`.

Source comparison: arXiv:1606.00608, Proposition 4.13, lines 1903--1908,
applied at Appendix C.4, lines 2048--2057. -/
noncomputable def UnitarySectorConjugacy.ofPositiveTailReflectedTarget
    (S : TwoSiteExactSectorGauge H)
    (hCanonical : MPSTensor.IsCPSVCanonicalForm M.toMPSTensor)
    (hM : IsMPDO M)
    (hTarget : ∀ γ : Fin H.labelCount,
      HasIdentityPositiveTailReflectedTarget S γ) :
    UnitarySectorConjugacy S := by
  let hUnitary (γ : Fin H.labelCount) :=
    S.exists_unitary_sector_conjugacy_of_positive_tail_reflected_target
      hCanonical hM γ (hTarget γ)
  exact {
    unitary := fun γ ↦ Classical.choose (hUnitary γ)
    tensor_eq := fun γ i ↦ Classical.choose_spec (hUnitary γ) i
  }

/-- Positive-tail reflected-target identities for every sector give the
trace-preserving completely positive maps and the two renormalization
identities of Definition 4.1.

**Scope restriction (conditional reflected targets):** This theorem assumes
the reflected-target identities.  The unconditional implication (ii) to (i)
of Theorem 4.14 is obtained by deriving these identities through the
mixed-prefix comparison documented in
`docs/paper-gaps/cpsv16_two_site_sector_unitary_gauge_gap.tex`.

**Local fix (zero-sector complement):** The physical channels used here have
the trace-restoring completion on discarded zero-sector complements documented
in `docs/paper-gaps/cpgsv17_vertical_isometry_zero_sector.tex`.  The additional
terms vanish on the one-site and blocked two-site tensor images.

Source comparison: arXiv:1606.00608, Definition 4.1, lines 638--660, and
Appendix C.4, lines 2048--2085. -/
theorem isRFPViaTS_of_positive_tail_reflected_target
    (S : TwoSiteExactSectorGauge H)
    (hCanonical : MPSTensor.IsCPSVCanonicalForm M.toMPSTensor)
    (hM : IsMPDO M)
    (hTarget : ∀ γ : Fin H.labelCount,
      HasIdentityPositiveTailReflectedTarget S γ) :
    IsRFPViaTS M :=
  (UnitarySectorConjugacy.ofPositiveTailReflectedTarget
    S hCanonical hM hTarget).isRFPViaTS

end BNTAlgebraTensorClause.TwoSiteExactSectorGauge

end MPOTensor
