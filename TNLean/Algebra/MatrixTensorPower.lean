/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Algebra.MatrixUnitaryBetween

/-!
# Tensor powers of rectangular matrices

The `M`-fold tensor power `W^{⊗M}` of a rectangular complex matrix `W : Matrix ι κ ℂ`, as a
matrix indexed by configurations `Fin M → ι` and `Fin M → κ`. For square families the
finite Kronecker product `Matrix.finKronecker` covers the same construction; this file
allows different row and column index types, as needed for the isometry
`W : |j⟩ ↦ |ω_j⟩` of arXiv:2307.01696, the paragraph after eq. (19).

## Main declarations

* `Matrix.tensorPower` — the matrix `W^{⊗M}` with entries `∏ₖ W (p k) (s k)`.
* `Matrix.IsIsometry.tensorPower` — the tensor power of an isometry is an isometry.
-/

open scoped BigOperators Matrix

namespace Matrix

/-- The `M`-fold tensor power `W^{⊗M}` of a matrix `W`, as a matrix indexed by
configurations of `M` sites: its entry at `(p, s)` is `∏ₖ W (p k) (s k)`
(arXiv:2307.01696, the map `W^{⊗M}` in the paragraph after eq. (19)). -/
def tensorPower {ι κ : Type*} (M : ℕ) (W : Matrix ι κ ℂ) : Matrix (Fin M → ι) (Fin M → κ) ℂ :=
  Matrix.of fun p s => ∏ k, W (p k) (s k)

/-- The tensor power of an isometry is an isometry, so `W^{⊗M}` in arXiv:2307.01696,
the paragraph after eq. (19), is an isometry from `(ℂ^b)^{⊗M}` to the bonds. -/
theorem IsIsometry.tensorPower {ι κ : Type*} [Fintype ι] [DecidableEq κ] (M : ℕ)
    {W : Matrix ι κ ℂ} (hW : W.IsIsometry) : (Matrix.tensorPower M W).IsIsometry := by
  ext s t
  have hWe : ∀ a c, ∑ i, star (W i a) * W i c = if a = c then 1 else 0 := fun a c => by
    have := congrFun (congrFun hW a) c
    simpa [Matrix.mul_apply, Matrix.one_apply] using this
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.tensorPower, Matrix.of_apply,
    star_prod, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun k i => star (W i (s k)) * W i (t k))]
  simp_rw [hWe, Matrix.one_apply]
  by_cases h : s = t
  · subst h; simp
  · obtain ⟨k, hk⟩ := Function.ne_iff.1 h
    rw [ite_eq_right_iff.2 fun h' => absurd h' h]
    exact Finset.prod_eq_zero (Finset.mem_univ k) (ite_eq_right_iff.2 fun h' => absurd h' hk)

end Matrix
