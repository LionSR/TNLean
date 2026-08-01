/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.BNTAlgebraTensorClauseConditionalGram

/-!
# Conditional unitary conjugacy for exact two-site sectors

An exact invertible sector gauge whose Gram matrix is a positive scalar
multiple of the identity can be normalized to a unitary matrix without
changing its conjugation action.  Composing this normalization with the
conditional Gram identity gives unitary conjugacy under an identity-dressed
marked realization.

The marked realization is assumed here, not constructed from the BNT algebra
clause.  Thus the final theorem is conditional and does not establish the
unconditional conclusion of Appendix C.4.

## Main results

* `TwoSiteExactSectorGauge.exists_unitary_sector_conjugacy_of_gauge_gram_eq_pos_smul_one`
* `TwoSiteExactSectorGauge.exists_unitary_sector_conjugacy_of_identityMarkedRealization`

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Proposition 4.13, lines 1903--1908, and Appendix C.4, lines 2053--2057
-/

open scoped Matrix ComplexOrder

noncomputable section

namespace MPOTensor

namespace BNTAlgebraTensorClause.TwoSiteExactSectorGauge

variable {d D : ℕ} {M : MPOTensor d D} {H : BNTAlgebraTensorClause M}

/-- A positive scalar Gram identity normalizes an exact sector gauge to a
unitary matrix with the same conjugation action.

Source: arXiv:1606.00608, Proposition 4.13, lines 1903--1908, applied at
Appendix C.4, lines 2053--2057. -/
theorem exists_unitary_sector_conjugacy_of_gauge_gram_eq_pos_smul_one
    (S : TwoSiteExactSectorGauge H) (γ : Fin H.labelCount)
    (ω : ℝ) (hω : 0 < ω)
    (hGram :
      (S.gauge γ : Matrix (Fin (S.decomposition.bondDim (S.relabel γ)))
          (Fin (S.decomposition.bondDim (S.relabel γ))) ℂ)ᴴ * S.gauge γ =
        (ω : ℂ) • 1) :
    ∃ U : Matrix.unitaryGroup
        (Fin (S.decomposition.bondDim (S.relabel γ))) ℂ,
      ∀ i : Fin (D * D),
        S.decomposition.tensor (S.relabel γ) i =
          (U : Matrix (Fin (S.decomposition.bondDim (S.relabel γ)))
            (Fin (S.decomposition.bondDim (S.relabel γ))) ℂ) *
          (cast (congrArg (MPSTensor (D * D)) (S.bondDim_eq γ))
            (H.tensor γ)) i *
          (U : Matrix (Fin (S.decomposition.bondDim (S.relabel γ)))
            (Fin (S.decomposition.bondDim (S.relabel γ))) ℂ)ᴴ := by
  let U : Matrix.unitaryGroup
      (Fin (S.decomposition.bondDim (S.relabel γ))) ℂ :=
    ⟨((Real.sqrt ω : ℂ))⁻¹ •
        (S.gauge γ : Matrix (Fin (S.decomposition.bondDim (S.relabel γ)))
          (Fin (S.decomposition.bondDim (S.relabel γ))) ℂ),
      Matrix.smul_mem_unitaryGroup_of_conjTranspose_mul_self_eq_smul_one
        hω hGram⟩
  refine ⟨U, fun i ↦ ?_⟩
  rw [S.tensor_eq γ i]
  simpa [U] using
    (Matrix.normalized_conj_eq_conj_inv_of_gram_eq_smul_one
      ((cast (congrArg (MPSTensor (D * D)) (S.bondDim_eq γ))
        (H.tensor γ)) i) (S.gauge γ) hω hGram).symm

/-- Under the conditional identity-dressed marked realization, every exact
two-site sector is unitarily conjugate to its matched one-site tensor.

**Scope restriction (conditional identity-dressed marked realization):** The
theorem assumes the physical-letter realization implicit at CPSV16 Appendix
C.4, line 2048; it is not derived from the algebra clause and does not establish
the unconditional line-2057 conclusion.  See
`docs/paper-gaps/cpsv16_two_site_sector_unitary_gauge_gap.tex`.

Source comparison: arXiv:1606.00608, Proposition 4.13, lines 1903--1908,
applied at Appendix C.4, lines 2048--2057. -/
theorem exists_unitary_sector_conjugacy_of_identityMarkedRealization
    (S : TwoSiteExactSectorGauge H)
    (hCanonical : MPSTensor.IsCPSVCanonicalForm M.toMPSTensor)
    (hM : IsMPDO M) (γ : Fin H.labelCount)
    (fId : Fin (S.decomposition.bondDim (S.relabel γ) *
        S.decomposition.bondDim (S.relabel γ)) →
      Fin ((d * d) * (d * d)) → ℂ)
    (hPhysical : ∀ u,
      MPSTensor.linearMarkedTensor fId (blockTwo M).toMPSTensor u =
        horizontalSlice
          (gramDressing (1 : GL (Fin (S.decomposition.bondDim (S.relabel γ))) ℂ)
            (cast (congrArg (MPSTensor (D * D)) (S.bondDim_eq γ))
              (H.tensor γ))) u.divNat u.modNat)
    (hTarget : ∀ (N : ℕ)
      (r s : Fin (S.decomposition.bondDim (S.relabel γ)))
      (σ τ : Fin N → Fin (d * d)),
      markedChainCoefficient
          (gramDressing
            (1 : GL (Fin (S.decomposition.bondDim (S.relabel γ))) ℂ)
            (cast (congrArg (MPSTensor (D * D)) (S.bondDim_eq γ))
              (H.tensor γ)))
          (blockTwo M) r s (List.ofFn σ) (List.ofFn τ) =
        markedChainCoefficient
          (reflectedAdjoint
            (cast (congrArg (MPSTensor (D * D)) (S.bondDim_eq γ))
              (H.tensor γ)))
          (adjointTensor (blockTwo M)) r s
          (List.ofFn σ).reverse (List.ofFn τ).reverse) :
    ∃ U : Matrix.unitaryGroup
        (Fin (S.decomposition.bondDim (S.relabel γ))) ℂ,
      ∀ i : Fin (D * D),
        S.decomposition.tensor (S.relabel γ) i =
          (U : Matrix (Fin (S.decomposition.bondDim (S.relabel γ)))
            (Fin (S.decomposition.bondDim (S.relabel γ))) ℂ) *
          (cast (congrArg (MPSTensor (D * D)) (S.bondDim_eq γ))
            (H.tensor γ)) i *
          (U : Matrix (Fin (S.decomposition.bondDim (S.relabel γ)))
            (Fin (S.decomposition.bondDim (S.relabel γ))) ℂ)ᴴ := by
  obtain ⟨ω, hω, hGram⟩ :=
    S.gauge_gram_eq_pos_smul_one_of_identityMarkedRealization
      hCanonical hM γ fId hPhysical hTarget
  exact S.exists_unitary_sector_conjugacy_of_gauge_gram_eq_pos_smul_one
    γ ω hω hGram

end BNTAlgebraTensorClause.TwoSiteExactSectorGauge

end MPOTensor
