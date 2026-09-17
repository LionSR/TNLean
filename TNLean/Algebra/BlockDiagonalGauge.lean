/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import Mathlib.Algebra.DirectSum.LinearMap
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Split coordinates give block-diagonal matrices

Let `V` be an internal direct sum of subspaces `W k`, each preserved by every member of a family
of endomorphisms `f i`, and let `ψ k` be coordinates on `W k`. Then the coordinates of `V`
assembled from the `ψ k` turn every `f i` into a block *diagonal* matrix, with diagonal block `k`
the matrix of the restriction of `f i` to `W k`.

This is the split refinement of the composition-series triangular gauge
(`TNLean/Algebra/FlagBlockTriangular.lean`): when the invariant flag splits, the strictly
upper-triangular part of the gauged matrices disappears.

## Main results

* `LinearMap.toMatrix_ofEquivFun`: the matrix of an endomorphism in the basis attached to a
  coordinate isomorphism is the matrix of the conjugated endomorphism.
* `exists_linearEquiv_blockDiagonal_of_isInternal`: the split gauge.
-/

open scoped Matrix

/-- The matrix of an endomorphism in the basis attached to a coordinate isomorphism `e` is the
standard matrix of the endomorphism conjugated by `e`. -/
theorem LinearMap.toMatrix_ofEquivFun {R M ι : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [Fintype ι] [DecidableEq ι] (e : M ≃ₗ[R] (ι → R)) (g : M →ₗ[R] M) :
    LinearMap.toMatrix (Module.Basis.ofEquivFun e) (Module.Basis.ofEquivFun e) g =
      LinearMap.toMatrix' (e.conj g) := by
  ext i j
  rw [LinearMap.toMatrix_apply, LinearMap.toMatrix'_apply, Module.Basis.ofEquivFun_repr_apply,
    Module.Basis.coe_ofEquivFun, LinearEquiv.conj_apply_apply]

/-- **The split gauge**. If `V` is the internal direct sum of subspaces `W k` preserved by every
endomorphism `f i`, then the coordinates assembled from coordinates `ψ k` on the summands turn
every `f i` into a block-diagonal matrix whose `k`-th diagonal block is the matrix of the
restriction of `f i` to `W k`. -/
theorem exists_linearEquiv_blockDiagonal_of_isInternal {K V γ ι : Type*} [Field K]
    [AddCommGroup V] [Module K V] [Fintype ι] [DecidableEq ι] {W : ι → Submodule K V}
    (hW : DirectSum.IsInternal W) (n : ι → ℕ) (ψ : ∀ k, W k ≃ₗ[K] (Fin (n k) → K))
    (f : γ → Module.End K V) (hf : ∀ (i : γ) (k : ι), Set.MapsTo (f i) (W k) (W k)) :
    ∃ e : V ≃ₗ[K] ((Σ k : ι, Fin (n k)) → K), ∀ i : γ,
      LinearMap.toMatrix' (e.conj (f i)) =
        Matrix.blockDiagonal' fun k =>
          LinearMap.toMatrix' ((ψ k).conj ((f i).restrict (hf i k))) := by
  classical
  set b : ∀ k, Module.Basis (Fin (n k)) K (W k) := fun k => Module.Basis.ofEquivFun (ψ k) with hb
  refine ⟨(hW.collectedBasis b).equivFun, fun i => ?_⟩
  rw [← LinearMap.toMatrix_ofEquivFun, Module.Basis.ofEquivFun_equivFun,
    LinearMap.toMatrix_directSum_collectedBasis_eq_blockDiagonal' hW hW b b (hf i)]
  exact congrArg Matrix.blockDiagonal' (funext fun k => by rw [hb, LinearMap.toMatrix_ofEquivFun])
