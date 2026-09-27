/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.UnitaryGroup
import QICLean.Algebra.MatrixUnitaryBetween

/-!
# Extending an isometry to a unitary along a placement of basis vectors

An isometry `V : ℂ^κ → ℂ^ι` and an injective placement `e : κ ↪ ι` of basis vectors give a unitary
`U` on `ℂ^ι` whose column at `e k` is the column `k` of `V`: the columns of `V` are orthonormal,
and any orthonormal family extends to an orthonormal basis.

## Main declarations

* `Matrix.exists_mem_unitaryGroup_apply_embedding_eq` — the unitary extension.

## References

* arXiv:2307.01696, eq. (11): the unitary on the `q` sites of a block implementing the isometric
  factor `V` of the polar decomposition on inputs whose central sites are in `|0⟩`.
-/

namespace Matrix

/-- **Unitary implementing an isometry.** An isometry `V : ℂ^κ → ℂ^ι` and an injective placement
`e : κ ↪ ι` of the basis vectors of `ℂ^κ` among those of `ℂ^ι` give a unitary `U` on `ℂ^ι` with
`U |e k⟩ = V |k⟩` for every `k`.

arXiv:2307.01696, eq. (11): the unitary `U` on the `q` sites of a block implements the isometry
`V` on inputs whose central sites are in `|0⟩`; the placement `e` is `|γ, δ⟩ ↦ |γ⟩_L |0⟩_C |δ⟩_R`
there. -/
theorem exists_mem_unitaryGroup_apply_embedding_eq {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [DecidableEq κ] {V : Matrix ι κ ℂ} (hV : V.IsIsometry) (e : κ ↪ ι) :
    ∃ U ∈ Matrix.unitaryGroup ι ℂ, ∀ i k, U i (e k) = V i k := by
  classical
  let E := EuclideanSpace ℂ ι
  let col : κ → E := fun k => WithLp.toLp 2 (fun i => V i k)
  let v : ι → E := Function.extend e col 0
  have hv_e : ∀ k, v (e k) = col k := fun k => e.injective.extend_apply col 0 k
  have key : ∀ k k', inner ℂ (col k) (col k') = if k = k' then 1 else 0 := fun k k' => by
    have h := congrFun (congrFun hV k) k'
    rw [Matrix.mul_apply, Matrix.one_apply] at h
    rw [← h, PiLp.inner_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [col, RCLike.inner_apply, Matrix.conjTranspose_apply, mul_comm]
  have hv : Orthonormal ℂ ((Set.range e).domRestrict v) := by
    rw [orthonormal_iff_ite]
    rintro ⟨x, hx⟩ ⟨y, hy⟩
    obtain ⟨k, rfl⟩ := hx
    obtain ⟨k', rfl⟩ := hy
    simp only [Set.domRestrict_apply, hv_e, key]
    simp [Subtype.ext_iff]
  obtain ⟨bb, hbb⟩ := hv.exists_orthonormalBasis_extension_of_card_eq
    (by simp [E, finrank_euclideanSpace])
  refine ⟨Matrix.of fun x y => (bb y : E) x, ?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff']
    ext y z
    have h := (orthonormal_iff_ite.mp bb.orthonormal) y z
    rw [PiLp.inner_apply] at h
    simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.of_apply, Matrix.one_apply]
    rw [← h]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp [RCLike.inner_apply, mul_comm]
  · intro i k
    have := hbb (e k) ⟨k, rfl⟩
    simp [this, hv_e, col]

end Matrix
