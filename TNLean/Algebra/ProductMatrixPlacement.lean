/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.ManyBody.Sites.Placement

/-!
# Products of site maps and placed operators

For site maps `m v : X v → Y v` (matrices with rows indexed by `X v` and columns by `Y v`), the
product `⊗_v m_v` is a matrix from the configurations of `Y` to those of `X`, with entries
`∏_v m_v(σ_v, τ_v)`. When every map is square it is QICLean's product operator `prodOp`. In
the coordinates of the cut along a region it is the tensor product of the products over the
region and over its complement, so a regional intertwining identity extends through it.

## Main definitions

* `ManyBody.prodMatrix`: the product `⊗_v m_v` of site maps.

## Main results

* `ManyBody.reindex_cutEquiv_prodMatrix`: the product splits across a cut.
* `ManyBody.prodMatrix_eq_place`: a product of site maps equal to the identity outside a
  region is the placement of the regional product.
* `ManyBody.prodMatrix_mul_place`: a regional intertwining identity extends through the full
  product.
* `ManyBody.place_mul_prodMatrix_eq_zero_iff`: a nonzero complementary product cancels.

## Implementation notes

QICLean's `prodOp` takes square site matrices; these statements need site maps between
different spaces (a physical site map from virtual to physical indices). QICLean#1108
generalizes `prodOp` to rectangular site maps. The names and signatures here are those of
#1108 with `prodOp` spelled `prodMatrix`, so that the next pin deletes this module by that one
renaming.
-/

open Matrix
open scoped Kronecker

namespace ManyBody

variable {V : Type*} [Fintype V] {X Y Z : V → Type*}

/-- The product `⊗_v m_v` of site maps, with entries `∏_v m_v(σ_v, τ_v)`. -/
def prodMatrix (m : (v : V) → Matrix (X v) (Y v) ℂ) : Matrix (Config X) (Config Y) ℂ :=
  Matrix.of fun σ τ ↦ ∏ v, m v (σ v) (τ v)

@[simp]
theorem prodMatrix_apply (m : (v : V) → Matrix (X v) (Y v) ℂ) (σ : Config X) (τ : Config Y) :
    prodMatrix m σ τ = ∏ v, m v (σ v) (τ v) :=
  rfl

/-- A product of nonzero site maps is nonzero. -/
theorem prodMatrix_ne_zero (m : (v : V) → Matrix (X v) (Y v) ℂ) (hm : ∀ v, m v ≠ 0) :
    prodMatrix m ≠ 0 := by
  classical
  have hentry (v : V) : ∃ a b, m v a b ≠ 0 := by
    by_contra! h
    exact hm v (Matrix.ext h)
  choose a b hab using hentry
  intro h
  have := congrFun (congrFun h a) b
  simp only [prodMatrix_apply, Matrix.zero_apply] at this
  exact Finset.prod_ne_zero_iff.mpr (fun v _ ↦ hab v) this

variable [DecidableEq V] {D : Finset V}

/-- Products of site maps compose sitewise. -/
theorem prodMatrix_mul [∀ v, Fintype (Y v)] (m : (v : V) → Matrix (X v) (Y v) ℂ)
    (m' : (v : V) → Matrix (Y v) (Z v) ℂ) :
    prodMatrix m * prodMatrix m' = prodMatrix fun v ↦ m v * m' v := by
  ext σ τ
  simp only [prodMatrix, Matrix.mul_apply, Matrix.of_apply, Fintype.prod_sum,
    Finset.prod_mul_distrib]

/-- In the coordinates of the cut along `D`, the product of site maps is the tensor product of
the products over `D` and over its complement. -/
theorem reindex_cutEquiv_prodMatrix (m : (v : V) → Matrix (X v) (Y v) ℂ) :
    reindex (cutEquiv X D) (cutEquiv Y D) (prodMatrix m) =
      prodMatrix (X := fun w : {v // v ∈ D} ↦ X w.1) (Y := fun w ↦ Y w.1) (fun w ↦ m w.1) ⊗ₖ
        prodMatrix (X := fun w : {v // v ∉ D} ↦ X w.1) (Y := fun w ↦ Y w.1)
          (fun w ↦ m w.1) := by
  ext ⟨a, c⟩ ⟨b, e⟩
  simp only [reindex_apply, submatrix_apply, prodMatrix_apply, kroneckerMap_apply]
  rw [← Fintype.prod_subtype_mul_prod_subtype (· ∈ D)]
  congr 1
  · refine Finset.prod_congr (by convert rfl) fun w _ ↦ ?_
    rw [cutEquiv_symm_apply_mem _ _ w.2, cutEquiv_symm_apply_mem _ _ w.2]
  · refine Finset.prod_congr (by convert rfl) fun w _ ↦ ?_
    rw [cutEquiv_symm_apply_not_mem _ _ w.2, cutEquiv_symm_apply_not_mem _ _ w.2]

private theorem prodMatrix_eq_reindex_kronecker (m : (v : V) → Matrix (X v) (Y v) ℂ) :
    prodMatrix m = reindex (cutEquiv X D).symm (cutEquiv Y D).symm
      (prodMatrix (X := fun w : {v // v ∈ D} ↦ X w.1) (Y := fun w ↦ Y w.1) (fun w ↦ m w.1) ⊗ₖ
        prodMatrix (X := fun w : {v // v ∉ D} ↦ X w.1) (Y := fun w ↦ Y w.1)
          (fun w ↦ m w.1)) := by
  rw [← reindex_cutEquiv_prodMatrix]
  simp

variable [∀ v, DecidableEq (X v)]

/-- A product of square site matrices equal to the identity outside `D` is the placement of
the product over `D`. -/
theorem prodMatrix_eq_place (m : (v : V) → Matrix (X v) (X v) ℂ) (hm : ∀ v ∉ D, m v = 1) :
    prodMatrix m = place D (prodMatrix (X := fun w : {v // v ∈ D} ↦ X w.1) fun w ↦ m w.1) := by
  rw [prodMatrix_eq_reindex_kronecker (D := D) m, place]
  congr 2
  have : (fun w : {v // v ∉ D} ↦ m w) = fun w : {v // v ∉ D} ↦ (1 : Matrix (X w.1) (X w.1) ℂ) :=
    funext fun w ↦ hm w.1 w.2
  rw [this]
  exact prodOp_one

variable [∀ v, Fintype (X v)]

/-- An intertwining identity on a region extends through the product of all site maps. -/
theorem prodMatrix_mul_place [∀ v, Fintype (Y v)] [∀ v, DecidableEq (Y v)]
    (m : (v : V) → Matrix (X v) (Y v) ℂ) {K : Matrix (RegionConfig X D) (RegionConfig X D) ℂ}
    {K' : Matrix (RegionConfig Y D) (RegionConfig Y D) ℂ}
    (h : prodMatrix (X := fun w : {v // v ∈ D} ↦ X w.1) (Y := fun w ↦ Y w.1) (fun w ↦ m w.1) *
        K' =
      K * prodMatrix (X := fun w : {v // v ∈ D} ↦ X w.1) (Y := fun w ↦ Y w.1)
        (fun w ↦ m w.1)) :
    prodMatrix m * place D K' = place D K * prodMatrix m := by
  rw [prodMatrix_eq_reindex_kronecker (D := D) m, place, place]
  simp only [reindex_apply, submatrix_mul_equiv, ← mul_kronecker_mul, Matrix.one_mul,
    Matrix.mul_one, h]

/-- A nonzero complementary product of site maps cancels from a placed operator times the
full product. -/
theorem place_mul_prodMatrix_eq_zero_iff (m : (v : V) → Matrix (X v) (Y v) ℂ)
    (K : Matrix (RegionConfig X D) (RegionConfig X D) ℂ)
    (hm : prodMatrix (X := fun w : {v // v ∉ D} ↦ X w.1) (Y := fun w ↦ Y w.1)
      (fun w ↦ m w.1) ≠ 0) :
    place D K * prodMatrix m = 0 ↔
      K * prodMatrix (X := fun w : {v // v ∈ D} ↦ X w.1) (Y := fun w ↦ Y w.1)
        (fun w ↦ m w.1) = 0 := by
  have hsplit : place D K * prodMatrix m = reindex (cutEquiv X D).symm (cutEquiv Y D).symm
      ((K * prodMatrix (X := fun w : {v // v ∈ D} ↦ X w.1) (Y := fun w ↦ Y w.1)
        (fun w ↦ m w.1)) ⊗ₖ
        prodMatrix (X := fun w : {v // v ∉ D} ↦ X w.1) (Y := fun w ↦ Y w.1)
          (fun w ↦ m w.1)) := by
    rw [prodMatrix_eq_reindex_kronecker (D := D) m, place]
    simp only [reindex_apply, submatrix_mul_equiv, ← mul_kronecker_mul, Matrix.one_mul]
  rw [hsplit]
  constructor
  · intro h
    obtain ⟨τ, ρ, hτρ⟩ : ∃ τ ρ, prodMatrix (X := fun w : {v // v ∉ D} ↦ X w.1)
        (Y := fun w ↦ Y w.1) (fun w ↦ m w.1) τ ρ ≠ 0 := by
      by_contra! hz
      exact hm (Matrix.ext hz)
    ext α β
    have hz := congrFun (congrFun h ((cutEquiv X D).symm (α, τ)))
      ((cutEquiv Y D).symm (β, ρ))
    simp only [reindex_apply, submatrix_apply, Equiv.symm_symm, Equiv.apply_symm_apply,
      kroneckerMap_apply, Matrix.zero_apply] at hz
    exact (mul_eq_zero.mp hz).resolve_right hτρ
  · intro h
    rw [h]
    simp

end ManyBody
