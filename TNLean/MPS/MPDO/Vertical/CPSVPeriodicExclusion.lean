/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.CanonicalForm.NormalBlocks.ProjectorClosureSpectral
import TNLean.MPS.MPDO.Vertical.CPSVOriginalSpaceLemmaL
import TNLean.MPS.MPDO.Vertical.CyclicProjector
import TNLean.MPS.MPDO.Vertical.VerticalReduction
import TNLean.MPS.MPDO.Vertical.VerticalBNT

/-!
# Periodic exclusion for literal CPSV canonical form

This file proves the periodic-sector step of arXiv:1606.00608,
Proposition 4.13, lines 1888--1893, for the literal CPSV canonical-form
predicate.  It then combines periodic exclusion with the invariant-projector
closure from lines 1873--1887 to obtain spectrally normalized vertical
corners with their ambient isometries.

The source prints noncommutation at every length, but its contradiction is
pointwise.  The formal statement therefore preserves the source-faithful
existential length supplied by Lemma L.

The final decomposition stops before gauge-equivalent normal corners are
grouped into a vertical BNT and before the source's final normalization and
coisometry statement.  See
`docs/paper-gaps/cpgsv17_vertical_cf_grouping.tex`.

## Vertical BNT grouping for a literal CPSV canonical form

This file proves the finite-chain sector-compression separation step and uses
it to group the normal vertical sectors of a literal CPSV canonical-form tensor
by matrix-product-vector phase class.

### Main statement

* `MPTensor.IsCPSVCanonicalForm.exists_sectorCompression_ne_zero_of_corner`:
  every nonzero vertical corner has a nonzero finite-chain compression.
* `MPTensor.IsCPSVCanonicalForm.exists_verticalBNTGrouping_with_isometry`:
  the literal vertical sectors grouped into BNT representatives with positive
  coefficients.

### References

* Cirac--Perez-Garcia--Schuch--Verstraete, arXiv:1606.00608, Appendix C.3,
  Lemma L, lines 1835--1858, and Proposition 4.13, lines 1898--1902.
-/

section

open scoped Matrix BigOperators ComplexOrder

namespace MPTensor.IsCPSVCanonicalForm

open MPSTensor

open MPOTensor

variable {d D : ℕ}

/-- A displaced idempotent for a tensor in literal CPSV canonical form fails
to commute with the generated density operator at some chain length.

If commutation held at every length, idempotence would give equality of the
one-sided first-site actions.  The original-space Lemma L then gives the
forbidden letterwise identity.

**Local fix (noncommuting length):** the source prints noncommutation at every
length, but its contradiction is pointwise and only needs the existential length
proved here; see `docs/paper-gaps/cpgsv17_periodic_sector_projector.tex`.

Source: arXiv:1606.00608, Proposition 4.13, lines 1888--1893. -/
theorem exists_not_commute_of_displaced
    (M : MPOTensor d D)
    (hCanonical : IsCPSVCanonicalForm M)
    {Q : Matrix (Fin d) (Fin d) ℂ}
    (hQidem : IsIdempotentElem Q)
    (hdisp : M.ketLeftMul Q ≠ (M.ketLeftMul Q).braRightMul Q) :
    ∃ N : ℕ,
      ¬ Commute (MPOTensor.firstSiteMatrix Q N)
        (MPOTensor.mpo M (N + 1)) := by
  exact exists_not_commute_of_displaced_of_insertedTensor_eq M
    (hCanonical.insertedTensor_eq_of_firstSiteActionAgree M) hQidem hdisp

end MPTensor.IsCPSVCanonicalForm

namespace MPOTensor

variable {d D : ℕ}

/-- The vertically viewed tensor of an MPDO in literal CPSV canonical form has
no nontrivial periodic vectors.

A periodic vector supplies a displaced projector invariant under one full
period.  Literal Lemma L gives a chain length where the projector does not
commute with the density operator.  Full-period invariance gives commutation
with the corresponding power, while positivity removes that power.

**Local fix (noncommuting length):** the all-length inequality printed at source
line 1889 is replaced by the existential consequence of literal Lemma L, which is
sufficient at lines 1890--1893; see
`docs/paper-gaps/cpgsv17_periodic_sector_projector.tex`.

Source: arXiv:1606.00608, Proposition 4.13, lines 1888--1893. -/
theorem hasNoPeriodicVectors_verticalTensor_of_cpsvCanonicalForm
    (M : MPOTensor d D)
    (hM : M.IsMPDO)
    (hCanonical : MPTensor.IsCPSVCanonicalForm M) :
    MPSTensor.HasNoPeriodicVectors (verticalTensor M) := by
  exact hasNoPeriodicVectors_verticalTensor_of_exists_not_commute_of_displaced M hM
    fun hQidem hdisp => hCanonical.exists_not_commute_of_displaced M hQidem hdisp

end MPOTensor

namespace MPTensor.IsCPSVCanonicalForm

open MPSTensor

open MPOTensor

variable {d D : ℕ}

/-- Literal CPSV canonical form and MPDO positivity give spectrally normalized
nonzero vertical corners with their physical isometries retained.

The dimensions and coefficients are positive, the blocks are normal, the
embeddings are orthogonal isometries, and both intertwining identities,
corner compression, and letterwise reconstruction hold exactly.

This is the normal-corner intermediate needed between the periodic exclusion
at lines 1889--1893 and the grouped vertical representation used at line 1898
of arXiv:1606.00608, Proposition 4.13.  It does not group gauge-equivalent
corners into a vertical BNT or prove the final normalization and coisometry
statement; see
`docs/paper-gaps/cpgsv17_vertical_cf_grouping.tex`. -/
theorem exists_normal_verticalBlockDecomp_with_isometry
    (M : MPOTensor d D)
    (hCanonical : IsCPSVCanonicalForm M)
    (hM : M.IsMPDO) :
    ∃ (r : ℕ) (dim : Fin r → ℕ) (μ : Fin r → ℂ)
      (blocks : (k : Fin r) → MPSTensor (D * D) (dim k))
      (V : (k : Fin r) → Matrix (Fin d) (Fin (dim k)) ℂ),
      (∀ k, 0 < dim k) ∧
      (∀ k, (0 : ℂ) < μ k) ∧
      (∀ k, IsNormalTensor (blocks k)) ∧
      (∀ k, (V k)ᴴ * V k = 1) ∧
      (∀ k l, k ≠ l → (V k)ᴴ * V l = 0) ∧
      (∀ k v, verticalTensor M v * V k = V k * (μ k • blocks k v)) ∧
      (∀ k v, (V k)ᴴ * verticalTensor M v = (μ k • blocks k v) * (V k)ᴴ) ∧
      (∀ k v, μ k • blocks k v = (V k)ᴴ * verticalTensor M v * V k) ∧
      ∀ v, verticalTensor M v =
        ∑ k, V k * (μ k • blocks k v) * (V k)ᴴ := by
  obtain ⟨r, dim, μ, blocks, V, hdim, hμ, hnormal, hiso, horth,
    hintertwine, hintertwineStar, hcorner, hreconstruct, _hMPV, _hdimSum⟩ :=
    exists_normalTensor_blockDecomp_with_isometry_of_hasInvariantProjectorClosure
      (verticalTensor M)
      (hCanonical.hasInvariantProjectorClosure_verticalTensor M hM)
      (MPOTensor.hasNoPeriodicVectors_verticalTensor_of_cpsvCanonicalForm
        M hM hCanonical)
  exact ⟨r, dim, μ, blocks, V, hdim, hμ, hnormal, hiso, horth,
    hintertwine, hintertwineStar, hcorner, hreconstruct⟩

end MPTensor.IsCPSVCanonicalForm

end

section

open scoped Matrix

namespace MPTensor.IsCPSVCanonicalForm

open MPSTensor

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
    (hCanonical : MPTensor.IsCPSVCanonicalForm M)
    (P : Matrix (Fin d) (Fin d) ℂ)
    (hcorner : ∃ v, P * MPOTensor.verticalTensor M v * P ≠ 0) :
    ∃ N, MPOTensor.sectorCompression M P N ≠ 0 := by
  exact MPOTensor.exists_sectorCompression_ne_zero_of_corner_of_insertedTensor_eq M
    (hCanonical.insertedTensor_eq_of_firstSiteActionAgree M) P hcorner

/-- Group the normal vertical corners of an MPDO in literal CPSV canonical
form by their gauge-phase classes while retaining their physical isometries.

The representatives satisfy the BNT characterization of arXiv:1606.00608,
lines 1135--1148.  Every effective grouped coefficient is positive by the
sector-compression argument in Proposition 4.13, lines 1895--1902.

The theorem stops at grouping.  The proportional Gram identity, normalized
grouped-sector maps, and final coisometry from lines 1903--1921 are proved
without a canonical-form hypothesis in
`MPOTensor.grouped_sector_gram_eq_pos_smul_one_of_dressing`,
`MPOTensor.exists_normalized_grouped_sector_maps_of_dressing`, and
`MPOTensor.verticalCF_of_cpsvCanonicalForm`. -/
theorem exists_verticalBNTGrouping_with_isometry
    (M : MPOTensor d D)
    (hCanonical : MPTensor.IsCPSVCanonicalForm M)
    (hM : MPOTensor.IsMPDO M) :
    MPOTensor.HasVerticalBNTGroupingWithIsometry M := by
  exact MPOTensor.exists_verticalBNTGrouping_with_isometry_of_decomposition M hM
    (hCanonical.exists_normal_verticalBlockDecomp_with_isometry M hM)
    (hCanonical.exists_sectorCompression_ne_zero_of_corner M)

end MPTensor.IsCPSVCanonicalForm

end
