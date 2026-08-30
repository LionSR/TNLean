/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Rank-one factorization

This file packages the basis-free factorization of a linear map with one-dimensional range,
its matrix form, and the product-index reshape used for rectangular tensor-network factors.

The product-index orientation follows the factorization step in arXiv:1706.07329v2,
Proposition 20: a row index `(b, a)` contributes `W b a`, while a column index `(b', a')`
contributes `V a' b'`.
-/

@[expose] public section

open Module

namespace LinearMap

variable {K M₁ M₂ : Type*} [DivisionRing K]
  [AddCommGroup M₁] [Module K M₁] [AddCommGroup M₂] [Module K M₂]

/-- A linear map whose range is one-dimensional is a scalar functional followed by scalar
multiplication of a nonzero range vector. The preimage `x` normalizes the chosen factors:
`φ x = 1` and `f x = y`.

This is basis-free: the only choice is a linear equivalence between the scalar field and the
one-dimensional range. -/
theorem exists_smulRight_of_finrank_range_eq_one (f : M₁ →ₗ[K] M₂)
    (hrank : finrank K (LinearMap.range f) = 1) :
    ∃ (φ : M₁ →ₗ[K] K) (y : M₂) (x : M₁),
      φ ≠ 0 ∧ y ≠ 0 ∧ φ x = 1 ∧ f x = y ∧ f = φ.smulRight y := by
  let e : K ≃ₗ[K] LinearMap.range f :=
    (Module.nonempty_linearEquiv_of_finrank_eq_one hrank).some
  let φ : M₁ →ₗ[K] K := e.symm.toLinearMap.comp f.rangeRestrict
  let y : M₂ := (e 1 : LinearMap.range f)
  have he_one : e 1 ≠ 0 := by
    intro h
    exact one_ne_zero (e.injective (h.trans e.map_zero.symm))
  have hy : y ≠ 0 := by
    intro h
    apply he_one
    exact Subtype.ext h
  obtain ⟨x, hx⟩ := (e 1 : LinearMap.range f).property
  have hφx : φ x = 1 := by
    change e.symm (f.rangeRestrict x) = 1
    rw [show f.rangeRestrict x = e 1 by exact Subtype.ext hx]
    exact e.symm_apply_apply 1
  have hφ : φ ≠ 0 := by
    intro h
    have := LinearMap.congr_fun h x
    simp [hφx] at this
  refine ⟨φ, y, x, hφ, hy, hφx, hx, ?_⟩
  ext z
  change f z = (e.symm (f.rangeRestrict z)) • (e 1 : LinearMap.range f)
  have hs : f.rangeRestrict z = e.symm (f.rangeRestrict z) • e 1 := by
    calc
      f.rangeRestrict z = e (e.symm (f.rangeRestrict z)) := (e.apply_symm_apply _).symm
      _ = e.symm (f.rangeRestrict z) • e 1 := by
        simpa using e.map_smul (e.symm (f.rangeRestrict z)) (1 : K)
  exact congrArg Subtype.val hs

end LinearMap

namespace Matrix

variable {K m n : Type*} [Field K]

/-- A matrix of rank one is an outer product of two nonzero vectors. -/
theorem exists_eq_vecMulVec_of_rank_eq_one [Finite m] [Fintype n]
    (M : Matrix m n K) (hrank : M.rank = 1) :
    ∃ (w : m → K) (v : n → K), w ≠ 0 ∧ v ≠ 0 ∧ M = Matrix.vecMulVec w v := by
  classical
  let _ := Fintype.ofFinite m
  have hrange : finrank K (LinearMap.range (Matrix.toLin' M)) = 1 := by
    rw [← Matrix.toLin_eq_toLin', ← M.rank_eq_finrank_range_toLin
      (Pi.basisFun K m) (Pi.basisFun K n)]
    exact hrank
  obtain ⟨φ, y, _x, _hφ, _hy, _hφx, _hfx, hfac⟩ :=
    LinearMap.exists_smulRight_of_finrank_range_eq_one (Matrix.toLin' M) hrange
  let w : m → K := (Pi.basisFun K m).repr y
  let v : n → K := φ ∘ Pi.basisFun K n
  have hM : M = Matrix.vecMulVec w v := by
    rw [← LinearMap.toMatrix'_toLin' M]
    change LinearMap.toMatrix (Pi.basisFun K n) (Pi.basisFun K m) (Matrix.toLin' M) = _
    rw [hfac, LinearMap.toMatrix_smulRight]
  have hw : w ≠ 0 := by
    intro hw
    have hzero : M = 0 := by rw [hM, hw, Matrix.zero_vecMulVec]
    have : (0 : Matrix m n K).rank = 1 := hzero ▸ hrank
    simp at this
  have hv : v ≠ 0 := by
    intro hv
    have hzero : M = 0 := by
      rw [hM, hv]
      ext
      simp [Matrix.vecMulVec_apply]
    have : (0 : Matrix m n K).rank = 1 := hzero ▸ hrank
    simp at this
  exact ⟨w, v, hw, hv, hM⟩

/-- A rank-one matrix on the product index `D_B × D_A` reshapes into rectangular factors
`W : D_B × D_A` and `V : D_A × D_B`. The index order is explicit in both the outer-product
identity and its entrywise form. -/
theorem exists_rectangular_factors_of_rank_eq_one
    {D_A D_B : Type*} [Fintype D_A] [Fintype D_B]
    (M : Matrix (D_B × D_A) (D_B × D_A) K) (hrank : M.rank = 1) :
    ∃ (W : Matrix D_B D_A K) (V : Matrix D_A D_B K),
      W ≠ 0 ∧ V ≠ 0 ∧
      M = Matrix.vecMulVec (fun p ↦ W p.1 p.2) (fun p ↦ V p.2 p.1) ∧
      ∀ b a b' a', M (b, a) (b', a') = W b a * V a' b' := by
  obtain ⟨w, v, hw, hv, hM⟩ := M.exists_eq_vecMulVec_of_rank_eq_one hrank
  let W : Matrix D_B D_A K := fun b a ↦ w (b, a)
  let V : Matrix D_A D_B K := fun a b ↦ v (b, a)
  have hW : W ≠ 0 := by
    intro h
    apply hw
    funext p
    have hp := congrFun (congrFun h p.1) p.2
    exact hp
  have hV : V ≠ 0 := by
    intro h
    apply hv
    funext p
    have hp := congrFun (congrFun h p.2) p.1
    exact hp
  refine ⟨W, V, hW, hV, ?_, ?_⟩
  · simpa [W, V] using hM
  · intro b a b' a'
    simpa [W, V, Matrix.vecMulVec_apply] using congrFun (congrFun hM (b, a)) (b', a')

end Matrix
