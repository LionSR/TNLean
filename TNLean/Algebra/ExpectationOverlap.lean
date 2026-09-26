/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.InnerProductSpace.Symmetric

/-!
# Expectations in two overlapping unit vectors

For a symmetric operator `T` and unit vectors `φ, ψ`, the difference of the
expectations of `T` is controlled by the overlap and the two variances:
`|⟨φ|ψ⟩| |⟨T⟩_φ - ⟨T⟩_ψ| ≤ ‖(T - ⟨T⟩_φ)φ‖ + ‖(T - ⟨T⟩_ψ)ψ‖`.

This is the estimate (`eq:ldp_expectation_overlap`, chapter entry
`lem:ldp_expectation_overlap`) used in the chapter's proof of the depth lower
bound for normal matrix product states, arXiv:2307.01696, Theorem 1. There it
replaces the source's trace-distance and fidelity argument in the Supplemental
Material, "Proof of Theorem 1" (eqs. (auxdp), (auxdp3), (inequax)).
-/

open scoped InnerProductSpace

namespace LinearMap.IsSymmetric

/-- For a symmetric operator `T` and unit vectors `φ, ψ`,
`|⟨φ|ψ⟩| |⟨T⟩_φ - ⟨T⟩_ψ| ≤ ‖(T - ⟨T⟩_φ)φ‖ + ‖(T - ⟨T⟩_ψ)ψ‖`.

This is the estimate `lem:ldp_expectation_overlap` used in the chapter's proof
of the depth lower bound of arXiv:2307.01696, Theorem 1, where it replaces the
source's trace-distance and fidelity argument (Supplemental Material,
"Proof of Theorem 1", eqs. (auxdp), (auxdp3), (inequax)). -/
theorem norm_inner_mul_norm_sub_le {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] {T : E →ₗ[ℂ] E} (hT : T.IsSymmetric) {φ ψ : E}
    (hφ : ‖φ‖ = 1) (hψ : ‖ψ‖ = 1) :
    ‖⟪φ, ψ⟫_ℂ‖ * ‖⟪φ, T φ⟫_ℂ - ⟪ψ, T ψ⟫_ℂ‖ ≤
      ‖T φ - ⟪φ, T φ⟫_ℂ • φ‖ + ‖T ψ - ⟪ψ, T ψ⟫_ℂ • ψ‖ := by
  set a := ⟪φ, T φ⟫_ℂ
  set b := ⟪ψ, T ψ⟫_ℂ
  have ha : starRingEnd ℂ a = a := by
    simp only [a, ← hT φ φ]
    exact hT.conj_inner_sym φ φ
  have hid : (a - b) * ⟪φ, ψ⟫_ℂ =
      ⟪φ, T ψ - b • ψ⟫_ℂ - ⟪T φ - a • φ, ψ⟫_ℂ := by
    rw [inner_sub_right, inner_sub_left, inner_smul_right, inner_smul_left, ha,
      hT φ ψ]
    ring
  calc ‖⟪φ, ψ⟫_ℂ‖ * ‖a - b‖ = ‖(a - b) * ⟪φ, ψ⟫_ℂ‖ := by
        rw [norm_mul, mul_comm]
    _ = ‖⟪φ, T ψ - b • ψ⟫_ℂ - ⟪T φ - a • φ, ψ⟫_ℂ‖ := by rw [hid]
    _ ≤ ‖⟪φ, T ψ - b • ψ⟫_ℂ‖ + ‖⟪T φ - a • φ, ψ⟫_ℂ‖ := norm_sub_le _ _
    _ ≤ ‖φ‖ * ‖T ψ - b • ψ‖ + ‖T φ - a • φ‖ * ‖ψ‖ :=
        add_le_add (norm_inner_le_norm _ _) (norm_inner_le_norm _ _)
    _ = ‖T φ - a • φ‖ + ‖T ψ - b • ψ‖ := by rw [hφ, hψ]; ring

end LinearMap.IsSymmetric
