/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.FiniteGroupUnitaryAverage
import TNLean.Algebra.PermutationMatrixUnitary

/-!
# Fixed vectors of finite permutation averages

For a permutation representation of a finite group, the normalized matrix
average is an orthogonal projector. Its fixed vectors are exactly the functions
constant on each group orbit. The characterization is obtained from Mathlib's
`Representation.averageMap`, keeping explicit the inverse in matrix pullback.
-/

open scoped BigOperators Matrix

namespace TNLean.Algebra

variable {H I : Type*} [Group H] [Fintype H] [Fintype I] [DecidableEq I]

/-- A normalized average of a finite permutation representation is an
orthogonal projector on the full complex function space. -/
theorem isStarProjection_inv_card_smul_sum_permMatrixHom (ρ : H →* Equiv.Perm I) :
    IsStarProjection ((Fintype.card H : ℂ)⁻¹ •
      ∑ h : H, Matrix.permMatrixHom (R := ℂ) (ρ h)) := by
  let σ : H →* Matrix.unitaryGroup I ℂ :=
    { toFun h := ⟨Matrix.permMatrixHom (ρ h), (ρ h)⁻¹.permMatrix_mem_unitaryGroup⟩
      map_one' := Subtype.ext (by
        change Matrix.permMatrixHom (ρ 1) = 1
        rw [map_one, map_one])
      map_mul' h k := Subtype.ext (by
        change Matrix.permMatrixHom (ρ (h * k)) = _
        rw [map_mul, map_mul]; rfl) }
  exact isStarProjection_inv_card_smul_sum σ

/-- A vector is fixed by the normalized permutation average if and only if
its coefficients are invariant under every permutation in the representation. -/
theorem inv_card_smul_sum_permMatrixHom_mulVec_eq_self_iff
    (ρ : H →* Equiv.Perm I) (v : I → ℂ) :
    ((Fintype.card H : ℂ)⁻¹ • ∑ h : H, Matrix.permMatrixHom (R := ℂ) (ρ h)) *ᵥ v = v ↔
      ∀ h i, v (ρ h i) = v i := by
  let _ : Invertible (Fintype.card H : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
  let σ : Representation ℂ H (I → ℂ) :=
    Matrix.toLinAlgEquiv'.toMonoidHom.comp ((Matrix.permMatrixHom (R := ℂ)).comp ρ)
  have hmatrix (h : H) : Matrix.permMatrixHom (R := ℂ) (ρ h) *ᵥ v =
      fun i => v (ρ h⁻¹ i) := by
    change (ρ h)⁻¹.permMatrix ℂ *ᵥ v = _
    rw [Matrix.permMatrix_mulVec, ← map_inv]
    rfl
  have havg : σ.averageMap v =
      ((Fintype.card H : ℂ)⁻¹ • ∑ h : H, Matrix.permMatrixHom (R := ℂ) (ρ h)) *ᵥ v := by
    simp [Representation.averageMap, GroupAlgebra.average, σ,
      Matrix.smul_mulVec, Matrix.sum_mulVec, Finset.smul_sum]
  rw [← havg]
  constructor
  · intro h h₀ i
    have hf := σ.averageMap_invariant v h₀⁻¹
    rw [h] at hf
    change Matrix.permMatrixHom (R := ℂ) (ρ h₀⁻¹) *ᵥ v = v at hf
    rw [hmatrix, inv_inv] at hf
    exact congrFun hf i
  · intro h
    apply σ.averageMap_id
    intro h₀
    change Matrix.permMatrixHom (R := ℂ) (ρ h₀) *ᵥ v = v
    rw [hmatrix]
    exact funext (h h₀⁻¹)

end TNLean.Algebra
