/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Algebra.MatrixGramUnitary
import TNLean.MPS.MPDO.BNTAlgebraTensorClauseSpectrum

/-!
# Unitary normalization of exact two-site sector gauges

An exact invertible sector gauge whose Gram matrix is a positive scalar
multiple of the identity can be normalized to a unitary matrix without
changing its conjugation action.

## Main results

* `TwoSiteExactSectorGauge.exists_unitary_sector_conjugacy_of_gauge_gram_eq_pos_smul_one`

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

end BNTAlgebraTensorClause.TwoSiteExactSectorGauge

end MPOTensor
