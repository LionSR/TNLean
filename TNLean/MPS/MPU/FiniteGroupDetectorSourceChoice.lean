/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.FiniteGroupDetectorTruncatedInterval
import TNLean.MPS.MPU.NormalizedSourceDecompositionUniqueness
import TNLean.MPS.MPU.SourceFactorsPhysicalAdjoint

/-!
# Unitarity for every normalized choice of source endpoints

Endpoint calibration must be allowed to select normalized source factors,
rather than being tied to the compact-SVD choice. The existing normalized
source-decomposition uniqueness theorem identifies any such choice by two
unitary endpoint coordinate changes. These changes act on the endpoint
outputs of the native contraction at every bulk length and preserve its
unitarity, then its physical placement on a common chain.

Source: FBC25, arXiv:2502.20257, `lem:deco`, lines 1052–1066, and
`eq:truncsym`, lines 2062–2100. This derives unitarity of the actual supplied
normalized record; it does not derive the physical endpoint identifications
or the domain-wall calibration equations required by GS24 `detectG`.
-/

open Matrix
open scoped Matrix Kronecker

namespace MPOTensor.FiniteGroupDetector

variable {d D : ℕ}

private theorem truncatedSymmetryOfEndpoints_mul_outputs (U : MPOTensor d D)
    (Y₂ : Matrix (Fin ℓ[U]) (Fin d × Fin D) ℂ)
    (Y₁ : Matrix (Fin r[U]) (Fin D × Fin d) ℂ)
    (C : Matrix (Fin ℓ[U]) (Fin ℓ[U]) ℂ)
    (B : Matrix (Fin r[U]) (Fin r[U]) ℂ) (N : ℕ) :
    truncatedSymmetryOfEndpoints U (C * Y₂) (B * Y₁) N =
      (C ⊗ₖ ((1 : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ) ⊗ₖ B)) *
        truncatedSymmetryOfEndpoints U Y₂ Y₁ N := by
  classical
  ext ⟨l, p, r⟩ ⟨a, q, b⟩
  simp only [truncatedSymmetryOfEndpoints, Matrix.mul_apply, Fintype.sum_prod_type,
    Matrix.kroneckerMap_apply, Matrix.one_apply, mul_ite, ite_mul,
    mul_zero, zero_mul, one_mul, Finset.sum_ite_irrel, Finset.sum_const_zero,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Fintype.sum_last_two_first_four]
  exact Finset.sum_congr₂ fun s _ t _ ↦ Finset.sum_congr₂ fun α _ β _ ↦ by ring

/-- Every normalized source record of a simple canonical tensor has a
unitary native contraction at every length. Endpoint unitary choices are
derived from source-decomposition uniqueness, not assumed.
Source: FBC25 `lem:deco` and `eq:truncsym`, lines 1052–1066 and 2062–2100. -/
theorem sourceRecord_truncatedSymmetry_isUnitaryBetween
    {U : MPOTensor d D} (hU : IsMPUCanonicalFormII U) (hsimple : IsMPUSimple U)
    (S : SourceFactors U hU.ρ) (N : ℕ) : (S.truncatedSymmetry N).IsUnitaryBetween := by
  classical
  let S₀ := sourceFactors U hU.ρ hU.ρ_posDef
  obtain ⟨W₁, W₂, _, hY₁, _, hY₂⟩ :=
    exists_unitary_source_gauges_of_isometric_second_factors
      (X₁ := S₀.X₁) (Xt₁ := S.X₁) (Y₁ := S₀.Y₁) (Yt₁ := S.Y₁)
      (X₂ := S₀.X₂) (Xt₂ := S.X₂) (Y₂ := S₀.Y₂) (Yt₂ := S.Y₂)
      (Lt₁ := S.X₁ᴴ * sourceWeight (d := d) hU.ρ) (R₁ := S₀.Z₁)
      (Lt₂ := S.X₂ᴴ) (R₂ := S₀.Z₂)
      S₀.sourceCutM₁_eq.symm S.sourceCutM₁_eq.symm
      S₀.sourceCutM₂_eq.symm S.sourceCutM₂_eq.symm
      S.X₁_weighted_isometry S₀.Y₁_mul_Z₁ S.X₂_isometry S₀.Y₂_mul_Z₂
      (hU.sourceFactors_sourceU_isUnitaryBetween hsimple S₀)
      (hU.sourceFactors_sourceU_isUnitaryBetween hsimple S) S₀.X₂_isometry S.X₂_isometry
  have hW₁ : (star (W₁ : Matrix (Fin r[U]) (Fin r[U]) ℂ)).IsUnitaryBetween :=
    (Matrix.isUnitaryBetween_iff_mem_unitaryGroup _).mpr (Unitary.star_mem W₁.property)
  have hW₂ : (star (W₂ : Matrix (Fin ℓ[U]) (Fin ℓ[U]) ℂ)).IsUnitaryBetween :=
    (Matrix.isUnitaryBetween_iff_mem_unitaryGroup _).mpr (Unitary.star_mem W₂.property)
  have hI : (1 : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ).IsUnitaryBetween := by
    simp [Matrix.IsUnitaryBetween, Matrix.IsIsometry, Matrix.IsCoisometry]
  change (truncatedSymmetryOfEndpoints U S.Y₂ S.Y₁ N).IsUnitaryBetween
  rw [hY₁, hY₂, truncatedSymmetryOfEndpoints_mul_outputs]
  exact (hW₂.kronecker _ _ (hI.kronecker _ _ hW₁)).mul _ _
    (hU.truncatedSymmetry_isUnitaryBetween hsimple N)

/-- Any normalized source choice gives unitary physical intervals after
the explicit endpoint identifications, permitting local calibration to
choose its source coordinates. Source: FBC25 `eq:truncsym`. -/
theorem sourceRecord_physicalTruncatedInterval_mem_unitaryGroup
    {U : MPOTensor d D} (hU : IsMPUCanonicalFormII U) (hsimple : IsMPUSimple U)
    (S : SourceFactors U hU.ρ) (el : Fin ℓ[U] ≃ Fin d) (er : Fin r[U] ≃ Fin d)
    (k l n L : ℕ) (h : k + 1 + l + 1 + n = L) :
    physicalTruncatedInterval U el er S.Y₂ S.Y₁ k l n h ∈ unitaryGroup (Fin L → Fin d) ℂ := by
  apply (Matrix.isUnitaryBetween_iff_mem_unitaryGroup _).mp
  exact physicalTruncatedInterval_isUnitaryBetween U el er _ _ k l n h
    (sourceRecord_truncatedSymmetry_isUnitaryBetween hU hsimple S l)

end MPOTensor.FiniteGroupDetector
