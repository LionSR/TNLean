/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.Orthogonal

/-!
# Exact kernel and gap transport under an isometric conjugacy

If \(Q=UPU^{-1}\) for a linear isometric equivalence \(U\), then
\(\ker Q=U(\ker P)\), and \(U\) carries their orthogonal complements
onto one another. Every real norm-gap bound \(\delta\) is consequently
preserved in both directions. Positivity, finite dimensionality, and
nonzero-dimensional Hilbert spaces are not required.

This is the operator transport used when exchanging the two endpoints in
GLM23, arXiv:2203.12563, Section 5, lines 1695–1777.
-/

open scoped InnerProductSpace

namespace LinearIsometryEquiv

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- An isometric conjugacy gives the pointwise intertwining equation
\(U(Px)=Q(Ux)\). -/
theorem map_apply_eq_of_conj
    (U : E ≃ₗᵢ[ℂ] F) (P : E →ₗ[ℂ] E) (Q : F →ₗ[ℂ] F)
    (hPQ : U.toLinearEquiv.conj P = Q) (x : E) :
    U (P x) = Q (U x) := by
  have h := LinearMap.congr_fun hPQ (U x)
  change U (P (U.symm (U x))) = Q (U x) at h
  simpa only [U.symm_apply_apply] using h

/-- Kernel membership is preserved and reflected by an isometric
conjugacy. -/
theorem mem_ker_iff_of_conj
    (U : E ≃ₗᵢ[ℂ] F) (P : E →ₗ[ℂ] E) (Q : F →ₗ[ℂ] F)
    (hPQ : U.toLinearEquiv.conj P = Q) (x : E) :
    x ∈ LinearMap.ker P ↔ U x ∈ LinearMap.ker Q := by
  change P x = 0 ↔ Q (U x) = 0
  rw [← U.map_apply_eq_of_conj P Q hPQ x]
  exact U.map_eq_zero_iff.symm

/-- The conjugated operator has exactly the isometric image of the
original kernel, including in zero-dimensional spaces. -/
theorem ker_eq_map_of_conj
    (U : E ≃ₗᵢ[ℂ] F) (P : E →ₗ[ℂ] E) (Q : F →ₗ[ℂ] F)
    (hPQ : U.toLinearEquiv.conj P = Q) :
    LinearMap.ker Q = (LinearMap.ker P).map U.toLinearMap := by
  ext y
  constructor
  · intro hy
    obtain ⟨x, rfl⟩ := U.surjective y
    exact ⟨x, (U.mem_ker_iff_of_conj P Q hPQ x).mpr hy, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact (U.mem_ker_iff_of_conj P Q hPQ x).mp hx

/-- An isometric conjugacy preserves and reflects membership in the
orthogonal complement of the operator kernel. -/
theorem mem_orthogonal_ker_iff_of_conj
    (U : E ≃ₗᵢ[ℂ] F) (P : E →ₗ[ℂ] E) (Q : F →ₗ[ℂ] F)
    (hPQ : U.toLinearEquiv.conj P = Q) (x : E) :
    x ∈ (LinearMap.ker P)ᗮ ↔ U x ∈ (LinearMap.ker Q)ᗮ := by
  constructor
  · intro hx
    apply ((LinearMap.ker Q).mem_orthogonal (U x)).mpr
    intro y hy
    obtain ⟨z, rfl⟩ := U.surjective y
    rw [U.inner_map_map]
    exact ((LinearMap.ker P).mem_orthogonal x).mp hx z
      ((U.mem_ker_iff_of_conj P Q hPQ z).mpr hy)
  · intro hx
    apply ((LinearMap.ker P).mem_orthogonal x).mpr
    intro z hz
    simpa only [U.inner_map_map] using
      ((LinearMap.ker Q).mem_orthogonal (U x)).mp hx (U z)
        ((U.mem_ker_iff_of_conj P Q hPQ z).mp hz)

/-- The norm-gap bound \(\delta\|x\|\le\|Px\|\) on
\((\ker P)^\perp\) is equivalent to the bound with exactly the same
\(\delta\) for an isometrically conjugated operator. -/
theorem norm_gap_iff_of_conj
    (U : E ≃ₗᵢ[ℂ] F) (P : E →ₗ[ℂ] E) (Q : F →ₗ[ℂ] F)
    (hPQ : U.toLinearEquiv.conj P = Q) (δ : ℝ) :
    (∀ x ∈ (LinearMap.ker P)ᗮ, δ * ‖x‖ ≤ ‖P x‖) ↔
      ∀ y ∈ (LinearMap.ker Q)ᗮ, δ * ‖y‖ ≤ ‖Q y‖ := by
  constructor
  · intro hGap y hy
    obtain ⟨x, rfl⟩ := U.surjective y
    rw [← U.map_apply_eq_of_conj P Q hPQ x, U.norm_map, U.norm_map]
    exact hGap x ((U.mem_orthogonal_ker_iff_of_conj P Q hPQ x).mpr hy)
  · intro hGap x hx
    have h := hGap (U x) ((U.mem_orthogonal_ker_iff_of_conj P Q hPQ x).mp hx)
    simpa only [← U.map_apply_eq_of_conj P Q hPQ x, U.norm_map] using h

end LinearIsometryEquiv
