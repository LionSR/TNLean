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

Source: arXiv:1606.00608, Proposition 4.13, lines 1888--1893.  The existential
length is the pointwise correction recorded in
`docs/paper-gaps/cpgsv17_periodic_sector_projector.tex`. -/
theorem exists_not_commute_of_displaced
    (M : MPOTensor d D)
    (hCanonical : IsCPSVCanonicalForm M.toMPSTensor)
    {Q : Matrix (Fin d) (Fin d) ℂ}
    (hQidem : IsIdempotentElem Q)
    (hdisp : M.ketLeftMul Q ≠ (M.ketLeftMul Q).braRightMul Q) :
    ∃ N : ℕ,
      ¬ Commute (MPOTensor.firstSiteMatrix Q N)
        (MPOTensor.mpo M (N + 1)) := by
  classical
  by_contra hnone
  simp only [not_exists, not_not] at hnone
  apply hdisp
  have hAct : FirstSiteActionAgree M.toMPSTensor
      (ketLeftAction Q) (ketLeftBraRightAction Q) := by
    apply firstSiteActionAgree_ketLeft_ketLeftBraRight M Q
    intro N ρ
    have hQ1idem : firstSiteMatrix Q N * firstSiteMatrix Q N =
        firstSiteMatrix Q N := by
      rw [firstSiteMatrix_mul_firstSiteMatrix, hQidem]
    have hOneSided : firstSiteMatrix Q N * mpo M (N + 1) =
        firstSiteMatrix Q N * mpo M (N + 1) * firstSiteMatrix Q N := by
      calc
        firstSiteMatrix Q N * mpo M (N + 1) =
            firstSiteMatrix Q N * firstSiteMatrix Q N * mpo M (N + 1) := by
              rw [hQ1idem]
        _ = firstSiteMatrix Q N *
            (firstSiteMatrix Q N * mpo M (N + 1)) := by rw [Matrix.mul_assoc]
        _ = firstSiteMatrix Q N *
            (mpo M (N + 1) * firstSiteMatrix Q N) := by rw [(hnone N).eq]
        _ = firstSiteMatrix Q N * mpo M (N + 1) *
            firstSiteMatrix Q N := by rw [Matrix.mul_assoc]
    have h2 := Matrix.ext_iff.mpr hOneSided
      (Fin.cons (ρ 0).divNat fun n => (ρ (Fin.succ n)).divNat)
      (Fin.cons (ρ 0).modNat fun n => (ρ (Fin.succ n)).modNat)
    rw [mul_firstSiteMatrix_apply] at h2
    simp only [firstSiteMatrix_mul_apply] at h2
    simp only [Fin.cons_zero, Function.comp_def, Fin.cons_succ] at h2
    rw [h2]
    simp only [Finset.sum_mul]
    exact Finset.sum_comm
  have hInsert := hCanonical.insertedTensor_eq_of_firstSiteActionAgree M.toMPSTensor hAct
  have hTensor : (M.ketLeftMul Q).toMPSTensor =
      ((M.ketLeftMul Q).braRightMul Q).toMPSTensor := by
    rw [← insertedTensor_ketLeftAction_toMPSTensor,
      ← insertedTensor_ketLeftBraRightAction_toMPSTensor]
    exact hInsert
  funext i j
  have hij := congrFun hTensor (finProdFinEquiv (i, j))
  simpa [MPOTensor.toMPSTensor] using hij

end MPSTensor.IsCPSVCanonicalForm

namespace MPOTensor

variable {d D : ℕ}

/-- The vertically viewed tensor of an MPDO in literal CPSV canonical form has
no nontrivial periodic vectors.

A periodic vector supplies a displaced projector invariant under one full
period.  Literal Lemma L gives a chain length where the projector does not
commute with the density operator.  Full-period invariance gives commutation
with the corresponding power, while positivity removes that power.

Source: arXiv:1606.00608, Proposition 4.13, lines 1888--1893. -/
theorem hasNoPeriodicVectors_verticalTensor_of_cpsvCanonicalForm
    (M : MPOTensor d D)
    (hM : M.IsMPDO)
    (hCanonical : MPSTensor.IsCPSVCanonicalForm M.toMPSTensor) :
    MPSTensor.HasNoPeriodicVectors (verticalTensor M) := by
  intro n V B ρ r hV hint hirr hρ hr hfix μ hμ hnorm
  by_contra hne
  obtain ⟨p, Q, hp, hQherm, hQidem, hword, hdisp⟩ :=
    exists_displaced_invariant_projector_of_periodic_vector M V B ρ r hV hint
      hirr hρ hr hfix μ hμ hnorm hne
  obtain ⟨N, hN⟩ := hCanonical.exists_not_commute_of_displaced M hQidem hdisp
  apply hN
  have hCommPow : Commute (firstSiteMatrix Q N) (mpo M (N + 1) ^ p) := by
    have h := firstSiteMatrix_mul_mpo_comm (stackedTensor M p)
      (hM.stackedTensor p) hQherm (stackedTensor_ketLeftMul_invariant M hword) N
    rwa [mpo_stackedTensor] at h
  exact mpo_commute_of_commute_pow M hM (N + 1) (by omega) hp hCommPow

end MPOTensor

namespace MPSTensor.IsCPSVCanonicalForm

open MPOTensor

variable {d D : ℕ}

/-- Literal CPSV canonical form and MPDO positivity give spectrally normalized
nonzero vertical corners with their physical isometries retained.

The dimensions and coefficients are positive, the blocks are normal, the
embeddings are orthogonal isometries, and both intertwining identities,
corner compression, and letterwise reconstruction hold exactly.

This is the normal-corner part of arXiv:1606.00608, Proposition 4.13,
lines 1894--1898.  It does not group gauge-equivalent corners into a vertical
BNT or prove the final normalization and coisometry statement; see
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
