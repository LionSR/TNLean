/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Algebra.MatrixGramUnitary
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
  let : Finite κ := Finite.of_injective e e.injective
  let J : Matrix ι κ ℂ := (1 : Matrix ι ι ℂ).submatrix id e
  have hJ : Jᴴ * J = 1 := by
    rw [show Jᴴ = (1 : Matrix ι ι ℂ).submatrix e id by simp [J]]
    change (1 : Matrix ι ι ℂ).submatrix e (Equiv.refl ι) *
      (1 : Matrix ι ι ℂ).submatrix (Equiv.refl ι) e = 1
    rw [Matrix.submatrix_mul_equiv, Matrix.one_mul]
    exact Matrix.submatrix_one e e.injective
  obtain ⟨U, hU⟩ := Matrix.exists_unitary_mul_eq_of_conjTranspose_mul_eq V J
    ((show Vᴴ * V = 1 from hV).trans hJ.symm)
  refine ⟨U, U.property, fun i k => ?_⟩
  have h := congrArg (fun M : Matrix ι κ ℂ => M i k) hU
  simpa [J, Matrix.mul_apply, Matrix.one_apply] using h.symm

end Matrix
