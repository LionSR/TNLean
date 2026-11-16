/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.TruncatedSymmetryUnitarity
import TNLean.MPS.Symmetry.MPOSymmetry.DomainWallString

/-!
# Native endpoint contractions on a common finite physical chain

The endpoint contraction is the existing `truncatedSymmetryOfEndpoints` of
arXiv:2502.20257, `eq:truncsym`, lines 2062–2100. This file reindexes its
output endpoint coordinates by supplied physical identifications and extends
it by identities on the exterior of a finite chain. Its equality with a
string operator is an entrywise contraction identity, valid on every vector.

**Scope restriction (explicit endpoint identifications):** the equivalences
from the two source endpoint spaces to the physical one-site space are
inputs. Their existence is not deduced from finite order or from the product
of source ranks. The string endpoints are the actual supplied source
triangles; they are not automatically the canonical domain-wall endpoints.
See the coordinate restriction in
https://sirui-lu.com/TNLean/paper-gaps/fbc25_truncated_symmetry_endpoint_unitarity_scope.pdf
and the detector scope in arXiv:2405.00439, `detectG`, lines 2108–2117.
-/

open Matrix
open scoped Matrix

namespace MPOTensor.FiniteGroupDetector

variable {d D L : ℕ}

/-- Group the physical endpoint and bulk coordinates into one window,
retaining the two exterior configurations, on a chain of fixed length.
Source context: FBC25 `eq:truncsym` and GS24 `detectG`. -/
def intervalWindowEquiv (k l n : ℕ) (h : k + 1 + l + 1 + n = L) :
    (((Fin k → Fin d) × (Fin d × (Fin l → Fin d) × Fin d)) × (Fin n → Fin d)) ≃
      (Fin L → Fin d) :=
  ((Equiv.prodAssoc _ _ _).trans
    (Equiv.prodCongr (Equiv.refl _)
      ((Equiv.prodAssoc _ _ _).trans
        (Equiv.prodCongr (Equiv.refl _) (Equiv.prodAssoc _ _ _))))).trans (wallConfig h)

/-- The left string endpoint obtained from the actual source triangle,
with its source coordinate identified explicitly with a physical output.
Source: FBC25 `eq:truncsym`, lines 2062–2100. -/
def sourceStringLeftEndpoint (U : MPOTensor d D) (el : Fin ℓ[U] ≃ Fin d)
    (Y₂ : Matrix (Fin ℓ[U]) (Fin d × Fin D) ℂ) :
    Fin d → Fin d → Matrix (Fin 1) (Fin D) ℂ :=
  fun a a' _ α ↦ Y₂ (el.symm a) (a', α)

/-- The right string endpoint obtained from the actual source triangle.
Source: FBC25 `eq:truncsym`, lines 2062–2100. -/
def sourceStringRightEndpoint (U : MPOTensor d D) (er : Fin r[U] ≃ Fin d)
    (Y₁ : Matrix (Fin r[U]) (Fin D × Fin d) ℂ) :
    Fin d → Fin d → Matrix (Fin D) (Fin 1) ℂ :=
  fun b b' β _ ↦ Y₁ (er.symm b) (β, b')

/-- The native endpoint contraction, with explicit physical endpoint
coordinates and identity action outside its interval. All intervals on
the same length `L` are matrices on exactly the same configuration space.
This is a spatial placement of FBC25 `eq:truncsym`, not a new contraction. -/
noncomputable def physicalTruncatedInterval (U : MPOTensor d D)
    (el : Fin ℓ[U] ≃ Fin d) (er : Fin r[U] ≃ Fin d)
    (Y₂ : Matrix (Fin ℓ[U]) (Fin d × Fin D) ℂ)
    (Y₁ : Matrix (Fin r[U]) (Fin D × Fin d) ℂ)
    (k l n : ℕ) (h : k + 1 + l + 1 + n = L) :
    Matrix (Fin L → Fin d) (Fin L → Fin d) ℂ :=
  Matrix.reindex (intervalWindowEquiv k l n h) (intervalWindowEquiv k l n h)
    (((1 : Matrix (Fin k → Fin d) (Fin k → Fin d) ℂ) ⊗ₖ
      Matrix.reindex (Equiv.prodCongr el (Equiv.prodCongr (Equiv.refl _) er)) (Equiv.refl _)
        (truncatedSymmetryOfEndpoints U Y₂ Y₁ l)) ⊗ₖ
          (1 : Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ))

/-- Entries of the physical placement are the native contraction times
the two exterior identities. Source: FBC25 `eq:truncsym`. -/
theorem physicalTruncatedInterval_apply_wallConfig (U : MPOTensor d D)
    (el : Fin ℓ[U] ≃ Fin d) (er : Fin r[U] ≃ Fin d)
    (Y₂ : Matrix (Fin ℓ[U]) (Fin d × Fin D) ℂ)
    (Y₁ : Matrix (Fin r[U]) (Fin D × Fin d) ℂ)
    (k l n : ℕ) (h : k + 1 + l + 1 + n = L)
    (p p' : Fin k → Fin d) (a a' : Fin d) (μ μ' : Fin l → Fin d)
    (b b' : Fin d) (q q' : Fin n → Fin d) :
    physicalTruncatedInterval U el er Y₂ Y₁ k l n h
        (wallConfig h (p, a, μ, b, q)) (wallConfig h (p', a', μ', b', q')) =
      (if p = p' then 1 else 0) * (if q = q' then 1 else 0) *
        truncatedSymmetryOfEndpoints U Y₂ Y₁ l (el.symm a, μ, er.symm b) (a', μ', b') := by
  classical
  by_cases hp : p = p' <;> by_cases hq : q = q' <;>
    simp [physicalTruncatedInterval, intervalWindowEquiv, Matrix.reindex_apply,
      Matrix.kroneckerMap_apply, Matrix.one_apply, hp, hq]

/-- The physical placement is exactly a string whose endpoint tensors are
the actual source triangles. This identity holds on all multiwall vectors
and is independent of any ground-state or normality assumption.
Source: FBC25 `eq:truncsym` and GS24 `eq:DWophysG`. -/
theorem physicalTruncatedInterval_eq_stringOperator (U : MPOTensor d D)
    (el : Fin ℓ[U] ≃ Fin d) (er : Fin r[U] ≃ Fin d)
    (Y₂ : Matrix (Fin ℓ[U]) (Fin d × Fin D) ℂ)
    (Y₁ : Matrix (Fin r[U]) (Fin D × Fin d) ℂ)
    (k l n : ℕ) (h : k + 1 + l + 1 + n = L) :
    physicalTruncatedInterval U el er Y₂ Y₁ k l n h =
      stringOperator U (sourceStringLeftEndpoint U el Y₂)
        (sourceStringRightEndpoint U er Y₁) k l n h := by
  classical
  ext τ σ
  obtain ⟨⟨p, a, μ, b, q⟩, rfl⟩ := (wallConfig h).surjective τ
  obtain ⟨⟨p', a', μ', b', q'⟩, rfl⟩ := (wallConfig h).surjective σ
  rw [physicalTruncatedInterval_apply_wallConfig]
  simp [stringOperator, stringKernel, Matrix.submatrix_apply,
    truncatedSymmetryOfEndpoints, sourceStringLeftEndpoint, sourceStringRightEndpoint,
    Matrix.mul_apply, Finset.sum_mul, mul_assoc]

/-- Coordinate reindexing and exterior identities preserve the native
contraction's two-sided unitarity. Source: FBC25 `eq:truncsym`. -/
theorem physicalTruncatedInterval_isUnitaryBetween (U : MPOTensor d D)
    (el : Fin ℓ[U] ≃ Fin d) (er : Fin r[U] ≃ Fin d)
    (Y₂ : Matrix (Fin ℓ[U]) (Fin d × Fin D) ℂ)
    (Y₁ : Matrix (Fin r[U]) (Fin D × Fin d) ℂ)
    (k l n : ℕ) (h : k + 1 + l + 1 + n = L)
    (hT : (truncatedSymmetryOfEndpoints U Y₂ Y₁ l).IsUnitaryBetween) :
    (physicalTruncatedInterval U el er Y₂ Y₁ k l n h).IsUnitaryBetween := by
  classical
  have hleft : (1 : Matrix (Fin k → Fin d) (Fin k → Fin d) ℂ).IsUnitaryBetween := by
    simp [Matrix.IsUnitaryBetween, Matrix.IsIsometry, Matrix.IsCoisometry]
  have hright : (1 : Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ).IsUnitaryBetween := by
    simp [Matrix.IsUnitaryBetween, Matrix.IsIsometry, Matrix.IsCoisometry]
  exact ((hleft.kronecker _ _ (hT.reindex _ _ _)).kronecker _ _ hright).reindex _ _ _

/-- Simple canonical-form-II source factors give actual unitary interval
operators on the common physical chain after the supplied endpoint
identifications. No unitarity hypothesis for those intervals is added.
Source: FBC25 `eq:truncsym`, lines 2062–2101, with explicit coordinates. -/
theorem sourceFactors_physicalTruncatedInterval_mem_unitaryGroup
    {U : MPOTensor d D} (hU : IsMPUCanonicalFormII U) (hsimple : IsMPUSimple U)
    (el : Fin ℓ[U] ≃ Fin d) (er : Fin r[U] ≃ Fin d)
    (k l n : ℕ) (h : k + 1 + l + 1 + n = L) :
    physicalTruncatedInterval U el er (sourceFactors U hU.ρ hU.ρ_posDef).Y₂
      (sourceFactors U hU.ρ hU.ρ_posDef).Y₁ k l n h ∈ unitaryGroup (Fin L → Fin d) ℂ := by
  apply (Matrix.isUnitaryBetween_iff_mem_unitaryGroup _).mp
  exact physicalTruncatedInterval_isUnitaryBetween U el er _ _ k l n h
    (hU.truncatedSymmetry_isUnitaryBetween hsimple l)

end MPOTensor.FiniteGroupDetector
