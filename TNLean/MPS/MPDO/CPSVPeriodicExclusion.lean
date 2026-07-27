/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.CanonicalForm.ProjectorClosureSpectral
import TNLean.MPS.MPDO.CPSVOriginalSpaceLemmaL
import TNLean.MPS.MPDO.CyclicProjector
import TNLean.MPS.MPDO.VerticalReduction

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
-/

open scoped Matrix BigOperators ComplexOrder

namespace MPSTensor.IsCPSVCanonicalForm

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
    (hCanonical : IsCPSVCanonicalForm M.toMPSTensor)
    {Q : Matrix (Fin d) (Fin d) ℂ}
    (hQidem : IsIdempotentElem Q)
    (hdisp : M.ketLeftMul Q ≠ (M.ketLeftMul Q).braRightMul Q) :
    ∃ N : ℕ,
      ¬ Commute (MPOTensor.firstSiteMatrix Q N)
        (MPOTensor.mpo M (N + 1)) := by
  exact exists_not_commute_of_displaced_of_insertedTensor_eq M
    (hCanonical.insertedTensor_eq_of_firstSiteActionAgree M.toMPSTensor) hQidem hdisp

end MPSTensor.IsCPSVCanonicalForm

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
    (hCanonical : MPSTensor.IsCPSVCanonicalForm M.toMPSTensor) :
    MPSTensor.HasNoPeriodicVectors (verticalTensor M) := by
  exact hasNoPeriodicVectors_verticalTensor_of_exists_not_commute_of_displaced M hM
    fun hQidem hdisp => hCanonical.exists_not_commute_of_displaced M hQidem hdisp

end MPOTensor

namespace MPSTensor.IsCPSVCanonicalForm

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
    (hCanonical : IsCPSVCanonicalForm M.toMPSTensor)
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

end MPSTensor.IsCPSVCanonicalForm
