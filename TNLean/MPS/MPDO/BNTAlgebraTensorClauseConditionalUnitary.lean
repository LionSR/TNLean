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

The physical-letter part of the marked realization is constructed from the
exact sector gauge, while the declarations here retain the positive-tail
reflected target as a hypothesis.  The mixed-prefix argument in
`BNTAlgebraTensorClauseReflectedTarget` derives that target under the standing
canonical-form and positivity assumptions.

## Main results

* `TwoSiteExactSectorGauge.exists_unitary_sector_conjugacy_of_gauge_gram_eq_pos_smul_one`
* `TwoSiteExactSectorGauge.exists_unitary_sector_conjugacy_of_identityMarkedRealization`
* `TwoSiteExactSectorGauge.exists_unitary_sector_conjugacy_of_positive_tail_reflected_target`

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

/-- A complete identity-dressed marked realization makes every exact two-site
sector unitarily conjugate to its matched one-site tensor.

**Scope restriction (packaged conditional form):** This form accepts all three
parts of the marked realization.  The physical-letter part follows from the
oblique compression, while the target-only theorem below gives the sharper
hypothesis.  The mixed-prefix theorem derives the reflected target from the
algebra clause under the standing assumptions; see
`docs/paper-gaps/cpsv16_two_site_sector_unitary_gauge_gap.tex`.

Source comparison: arXiv:1606.00608, Proposition 4.13, lines 1903--1908,
applied at Appendix C.4, lines 2048--2057. -/
theorem exists_unitary_sector_conjugacy_of_identityMarkedRealization
    (S : TwoSiteExactSectorGauge H)
    (hCanonical : MPSTensor.IsCPSVCanonicalForm M.toMPSTensor)
    (hM : IsMPDO M) (γ : Fin H.labelCount)
    (R : IdentityMarkedRealization S γ) :
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
      hCanonical hM γ R
  exact S.exists_unitary_sector_conjugacy_of_gauge_gram_eq_pos_smul_one
    γ ω hω hGram

/-- Under the conditional positive-tail reflected target, every exact two-site
sector is unitarily conjugate to its matched one-site tensor.  The
physical-letter coefficients are constructed from the exact sector gauge.

**Scope restriction (conditional reflected target):** The target is a
hypothesis of this theorem.  Its derivation from the tensor-attached algebra
clause by the mixed-prefix comparison is documented in
`docs/paper-gaps/cpsv16_two_site_sector_unitary_gauge_gap.tex`.

Source comparison: arXiv:1606.00608, Proposition 4.13, lines 1903--1908,
applied at Appendix C.4, lines 2048--2057. -/
theorem exists_unitary_sector_conjugacy_of_positive_tail_reflected_target
    (S : TwoSiteExactSectorGauge H)
    (hCanonical : MPSTensor.IsCPSVCanonicalForm M.toMPSTensor)
    (hM : IsMPDO M) (γ : Fin H.labelCount)
    (hTarget : HasIdentityPositiveTailReflectedTarget S γ) :
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
    S.gauge_gram_eq_pos_smul_one_of_positive_tail_reflected_target
      hCanonical hM γ hTarget
  exact S.exists_unitary_sector_conjugacy_of_gauge_gram_eq_pos_smul_one
    γ ω hω hGram

end BNTAlgebraTensorClause.TwoSiteExactSectorGauge

end MPOTensor
