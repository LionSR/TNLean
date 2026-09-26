/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic.LinearCombination

/-!
# Anticommuting invertible operators force even dimension

Two invertible endomorphisms `f` and `g` of a finite-dimensional vector space over a
field of characteristic zero with `f g = -g f` exist only in even dimension: taking
determinants gives `det f det g = (-1)^n det g det f`.  Every operator commuting with
both leaves each of its eigenspaces invariant, and the restrictions still
anticommute, so every eigenspace of such an operator has even dimension.

This is the linear-algebra step behind the degeneracy of the entanglement spectrum
in a non-trivial symmetry-protected topological phase (arXiv:2011.12127, §III.A,
paragraph "Entanglement spectrum and edge modes").

## Main results

* `Module.End.even_finrank_of_anticommute` : anticommuting invertible endomorphisms
  force even dimension
* `Matrix.even_finrank_eigenspace_of_anticommute` : every eigenspace of a matrix
  commuting with two anticommuting invertible matrices has even dimension
-/

open Module

namespace Module.End

variable {K V : Type*} [Field K] [CharZero K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

omit [FiniteDimensional K V] in
/-- Two invertible endomorphisms satisfying `f g = -g f` exist only in even
dimension: the determinant identity `det f det g = (-1)^n det g det f` forces
`(-1)^n = 1`. -/
theorem even_finrank_of_anticommute {f g : End K V} (hf : IsUnit f) (hg : IsUnit g)
    (h : f * g = -(g * f)) : Even (finrank K V) := by
  have hdet := congrArg LinearMap.det h
  rw [show -(g * f) = (-1 : K) • (g * f) by rw [neg_one_smul], LinearMap.det_smul,
    map_mul, map_mul] at hdet
  have hne : LinearMap.det f * LinearMap.det g ≠ 0 :=
    mul_ne_zero (LinearMap.isUnit_det f hf).ne_zero (LinearMap.isUnit_det g hg).ne_zero
  have hpow : (-1 : K) ^ finrank K V = 1 := by
    apply mul_right_cancel₀ hne
    linear_combination -hdet
  exact (neg_one_pow_eq_one_iff_even (by norm_num)).mp hpow

omit [CharZero K] in
/-- Restricting to an invariant subspace preserves invertibility in finite dimension:
the restriction of an injective endomorphism is injective, hence bijective. -/
theorem isUnit_restrict_of_isUnit {f : End K V} (hf : IsUnit f) {W : Submodule K V}
    (hW : Set.MapsTo f W W) : IsUnit (f.restrict hW) := by
  rw [Module.End.isUnit_iff] at hf ⊢
  have hinj : Function.Injective (f.restrict hW) := by
    intro x y hxy
    exact Subtype.ext (hf.1 (congrArg Subtype.val hxy :))
  exact ⟨hinj, LinearMap.injective_iff_surjective.mp hinj⟩

/-- Every eigenspace of an endomorphism commuting with two anticommuting invertible
endomorphisms has even dimension. -/
theorem even_finrank_eigenspace_of_anticommute {T f g : End K V} (hf : IsUnit f)
    (hg : IsUnit g) (hTf : Commute T f) (hTg : Commute T g) (h : f * g = -(g * f))
    (μ : K) : Even (finrank K (T.eigenspace μ)) := by
  have hmf := mapsTo_genEigenspace_of_comm hTf μ 1
  have hmg := mapsTo_genEigenspace_of_comm hTg μ 1
  refine even_finrank_of_anticommute (isUnit_restrict_of_isUnit hf hmf)
    (isUnit_restrict_of_isUnit hg hmg) ?_
  ext x
  simp only [Module.End.mul_apply, LinearMap.neg_apply, Submodule.coe_neg]
  exact congrArg (fun F : End K V => F x) h

end Module.End

namespace Matrix

variable {K n : Type*} [Field K] [CharZero K] [Fintype n] [DecidableEq n]

/-- Every eigenspace of a matrix `Λ` commuting with two anticommuting invertible
matrices `X` and `Y` has even dimension. -/
theorem even_finrank_eigenspace_of_anticommute {Λ X Y : Matrix n n K} (hX : IsUnit X)
    (hY : IsUnit Y) (hΛX : Commute Λ X) (hΛY : Commute Λ Y) (hXY : X * Y = -(Y * X))
    (μ : K) : Even (finrank K (Module.End.eigenspace (Matrix.toLin' Λ) μ)) := by
  refine Module.End.even_finrank_eigenspace_of_anticommute
    (f := Matrix.toLin' X) (g := Matrix.toLin' Y) ?_ ?_ ?_ ?_ ?_ μ
  · exact hX.map (Matrix.toLinAlgEquiv' (R := K) (n := n))
  · exact hY.map (Matrix.toLinAlgEquiv' (R := K) (n := n))
  · exact hΛX.map (Matrix.toLinAlgEquiv' (R := K) (n := n))
  · exact hΛY.map (Matrix.toLinAlgEquiv' (R := K) (n := n))
  · have := congrArg (Matrix.toLinAlgEquiv' (R := K) (n := n)) hXY
    rw [map_mul, map_neg, map_mul] at this
    exact this

end Matrix
