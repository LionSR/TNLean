/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.GroupTheory.Perm.Basic
import TNLean.PEPS.GInjective
import TNLean.MPS.Defs

/-!
# G-injectivity of matrix product state tensors

**Source.** Schuch, Cirac, Pérez-García 2010 (arXiv:1001.3807), Definition `def:2d-Ug-inj`,
`Papers/1001.3807/paper_v3.tex` lines 1278–1296, together with the map
`𝒫(A) = ∑ A^i_{αβ} |i⟩(αβ|` from the virtual to the physical system, lines 501–507, whose
two-leg case is the matrix product state.
Review: arXiv:2011.12127, `Papers/2011.12127/TN-Review-main.tex` lines 1196–1206, which calls
a matrix product state `G`-injective when its tensor carries a symmetry `G` on the virtual
level.

**Formalized here.** The map `𝒫(A)` of a matrix product state tensor, and the representation
`U_g ⊗ Ū_g` of `G` on the two virtual legs induced by a permutation representation
`g ↦ U_g`, so that the project predicate `TNLean.PEPS.IsGInjective` applies to matrix product
state tensors. A tensor whose entries are invariant under the permutations of both virtual
legs is invariant under this representation.

## Main definitions

* `MPSTensor.siteMap`: the map `𝒫(A)` from the virtual to the physical system.
* `MPSTensor.pairPermRep`: the representation `U_g ⊗ Ū_g` on the two virtual legs.

## Main results

* `MPSTensor.siteMap_comp_pairPermRep`: invariance of `𝒫(A)` from invariance of the entries.

## References

- [arXiv:1001.3807](https://arxiv.org/abs/1001.3807) -- N. Schuch, J. I. Cirac,
  D. Pérez-García, *PEPS as ground states: degeneracy and topology*
-/

open scoped BigOperators

namespace MPSTensor

variable {d D : ℕ}

/-- Source: arXiv:1001.3807, `Papers/1001.3807/paper_v3.tex` lines 501–507. The map
`𝒫(A) = ∑ A^i_{αβ} |i⟩(αβ|` of a matrix product state tensor, from the two virtual legs to the
physical system. -/
def siteMap (A : MPSTensor d D) : ((Fin D × Fin D) → ℂ) →ₗ[ℂ] (Fin d → ℂ) :=
  Matrix.mulVecLin (Matrix.of fun (i : Fin d) (c : Fin D × Fin D) => A i c.1 c.2)

theorem siteMap_apply (A : MPSTensor d D) (x : (Fin D × Fin D) → ℂ) (i : Fin d) :
    siteMap A x i = ∑ c : Fin D × Fin D, A i c.1 c.2 * x c := by
  simp [siteMap, Matrix.mulVec, dotProduct]

variable {G : Type*} [Group G]

/-- The representation `U_g ⊗ Ū_g` of `G` on the two virtual legs, for a permutation
representation `g ↦ U_g` of `G` on the bond basis: `(U_g ⊗ Ū_g x)(α, β) = x(g⁻¹α, g⁻¹β)`. -/
def pairPermRep (π : G →* Equiv.Perm (Fin D)) : Representation ℂ G ((Fin D × Fin D) → ℂ) where
  toFun g := LinearMap.funLeft ℂ ℂ fun c => ((π g)⁻¹ c.1, (π g)⁻¹ c.2)
  map_one' := by
    refine LinearMap.ext fun x => funext fun c => ?_
    simp [LinearMap.funLeft]
  map_mul' g h := by
    refine LinearMap.ext fun x => funext fun c => ?_
    simp [LinearMap.funLeft, Equiv.Perm.mul_apply]

theorem pairPermRep_apply (π : G →* Equiv.Perm (Fin D)) (g : G) (x : (Fin D × Fin D) → ℂ)
    (c : Fin D × Fin D) : pairPermRep π g x c = x ((π g)⁻¹ c.1, (π g)⁻¹ c.2) := rfl

/-- If every matrix `A^i` is invariant under relabelling both virtual legs by `π g`, then
`𝒫(A)` is invariant under `U_g ⊗ Ū_g`, condition i of arXiv:1001.3807,
Definition `def:2d-Ug-inj`. -/
theorem siteMap_comp_pairPermRep (A : MPSTensor d D) (π : G →* Equiv.Perm (Fin D))
    (hA : ∀ g i α β, A i (π g α) (π g β) = A i α β) (g : G) :
    siteMap A ∘ₗ pairPermRep π g = siteMap A := by
  refine LinearMap.ext fun x => funext fun i => ?_
  simp only [LinearMap.comp_apply, siteMap_apply, pairPermRep_apply]
  let σ : Fin D × Fin D ≃ Fin D × Fin D := Equiv.prodCongr (π g) (π g)
  rw [← Equiv.sum_comp σ]
  refine Finset.sum_congr rfl fun c _ => ?_
  simp [σ, hA]

end MPSTensor
