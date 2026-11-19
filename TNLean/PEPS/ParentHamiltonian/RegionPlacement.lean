/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.ManyBody.Sites.Subregion
import QICLean.Analysis.MatrixFramePerturbation
import Mathlib.Algebra.Star.StarProjection

/-!
# Regional operators placed in the global configuration space

A regional matrix `K` on the configurations of a region `R` acts on the global configurations
`(v : V) → Out v` as its placement `ManyBody.place R K = K ⊗ 1`. This module collects the facts
about placements that the PEPS patch and parent-Hamiltonian arguments use beyond QICLean's
algebraic placement lemmas: the operator-norm bound on vectors, continuity, orthogonal
projections, the action on the slices of a vector over the complementary configurations, and
the supports of products, differences and commutators of placements. The site spaces `Out v`
may differ from vertex to vertex, and no range or commutation assumption is made.

## References

The continuity and norm bound are used in the regularized variational problem
of OpenAI, Polynomial PEPS approximation of gapped square-grid ground states,
September 24, 2026, `03-patches.tex`, lines 68–99,
commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

open scoped BigOperators Matrix Kronecker Matrix.Norms.L2Operator
open ManyBody (Config RegionConfig ComplConfig cutEquiv place)

namespace TNLean.PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Out : V → Type*} [∀ v, DecidableEq (Out v)]

/-- The slice of a global vector at a complementary configuration `τ`: the regional vector
`α ↦ x (α, τ)` in the coordinates of the cut along `R`. -/
abbrev placeSlice (R : Finset V) (τ : ComplConfig Out R) :
    (Config Out → ℂ) →ₗ[ℂ] (RegionConfig Out R → ℂ) :=
  LinearMap.funLeft ℂ ℂ fun α ↦ (cutEquiv Out R).symm (α, τ)

/-- A placed regional matrix obeys the local Euclidean operator bound. -/
theorem norm_place_mulVec_le [∀ v, Fintype (Out v)] (R : Finset V)
    (K : Matrix (RegionConfig Out R) (RegionConfig Out R) ℂ)
    (ξ : EuclideanSpace ℂ (Config Out)) :
    ‖WithLp.toLp 2 (place R K *ᵥ ξ)‖ ≤ ‖K‖ * ‖ξ‖ :=
  (Matrix.l2_opNorm_mulVec (place R K) ξ).trans
    (mul_le_mul_of_nonneg_right (ManyBody.norm_place_le K) (norm_nonneg ξ))

/-- Placing regional matrices is continuous. -/
theorem continuous_place [∀ v, Finite (Out v)] (R : Finset V) :
    Continuous (place (X := Out) R) := by
  have := fun v ↦ Fintype.ofFinite (Out v)
  exact (ManyBody.placeHom (X := Out) R).toLinearMap.continuous_of_finiteDimensional

/-- Placement preserves orthogonal projections. -/
theorem isStarProjection_place [∀ v, Fintype (Out v)] (R : Finset V)
    {K : Matrix (RegionConfig Out R) (RegionConfig Out R) ℂ} (hK : IsStarProjection K) :
    IsStarProjection (place R K) :=
  hK.map (ManyBody.placeHom (X := Out) R)

/-- Coefficients of a placed matrix in the coordinates of the cut along its region. -/
theorem place_cutEquiv_symm_apply (R : Finset V)
    (K : Matrix (RegionConfig Out R) (RegionConfig Out R) ℂ)
    (α β : RegionConfig Out R) (τ ρ : ComplConfig Out R) :
    place R K ((cutEquiv Out R).symm (α, τ)) ((cutEquiv Out R).symm (β, ρ)) =
      if τ = ρ then K α β else 0 := by
  classical
  simp [place, Matrix.reindex_apply, Matrix.one_apply, mul_ite]

/-- Every complementary slice sees exactly the original regional matrix. -/
theorem placeSlice_mulVec_place [∀ v, Fintype (Out v)] (R : Finset V)
    (K : Matrix (RegionConfig Out R) (RegionConfig Out R) ℂ)
    (x : Config Out → ℂ) (τ : ComplConfig Out R) :
    placeSlice R τ (place R K *ᵥ x) = K *ᵥ placeSlice R τ x := by
  classical
  funext α
  change (∑ η, place R K ((cutEquiv Out R).symm (α, τ)) η * x η) = _
  calc
    _ = ∑ p : RegionConfig Out R × ComplConfig Out R,
        place R K ((cutEquiv Out R).symm (α, τ)) ((cutEquiv Out R).symm p) *
          x ((cutEquiv Out R).symm p) :=
      (Equiv.sum_comp (cutEquiv Out R).symm _).symm
    _ = _ := by
      simp [Fintype.sum_prod_type, place_cutEquiv_symm_apply, Matrix.mulVec, dotProduct,
        ite_mul]

/-- A vector is fixed by a placed matrix exactly when every complementary slice is fixed. -/
theorem place_mulVec_eq_self_iff [∀ v, Fintype (Out v)] (R : Finset V)
    (K : Matrix (RegionConfig Out R) (RegionConfig Out R) ℂ) (x : Config Out → ℂ) :
    place R K *ᵥ x = x ↔ ∀ τ, K *ᵥ placeSlice R τ x = placeSlice R τ x := by
  constructor
  · intro h τ
    rw [← placeSlice_mulVec_place, h]
  · intro h
    funext η
    obtain ⟨⟨α, τ⟩, rfl⟩ := (cutEquiv Out R).symm.surjective η
    exact congrFun ((placeSlice_mulVec_place R K x τ).trans (h τ)) α

/-- Products of placements are supported on the union of the regions. -/
theorem exists_place_mul_union [∀ v, Fintype (Out v)] (R S : Finset V)
    (K : Matrix (RegionConfig Out R) (RegionConfig Out R) ℂ)
    (L : Matrix (RegionConfig Out S) (RegionConfig Out S) ℂ) :
    ∃ M : Matrix (RegionConfig Out (R ∪ S)) (RegionConfig Out (R ∪ S)) ℂ,
      place R K * place S L = place (R ∪ S) M :=
  ⟨ManyBody.subregionPlace Finset.subset_union_left K *
      ManyBody.subregionPlace Finset.subset_union_right L, by
    rw [ManyBody.place_mul, ManyBody.place_subregionPlace, ManyBody.place_subregionPlace]⟩

/-- Differences of placements are supported on the union of the regions. -/
theorem exists_place_sub_union (R S : Finset V)
    (K : Matrix (RegionConfig Out R) (RegionConfig Out R) ℂ)
    (L : Matrix (RegionConfig Out S) (RegionConfig Out S) ℂ) :
    ∃ M : Matrix (RegionConfig Out (R ∪ S)) (RegionConfig Out (R ∪ S)) ℂ,
      place R K - place S L = place (R ∪ S) M :=
  ⟨ManyBody.subregionPlace Finset.subset_union_left K -
      ManyBody.subregionPlace Finset.subset_union_right L, by
    rw [ManyBody.place_sub, ManyBody.place_subregionPlace, ManyBody.place_subregionPlace]⟩

/-- Commutators of placements are supported on the union of the regions. -/
theorem exists_place_commutator_union [∀ v, Fintype (Out v)] (R S : Finset V)
    (K : Matrix (RegionConfig Out R) (RegionConfig Out R) ℂ)
    (L : Matrix (RegionConfig Out S) (RegionConfig Out S) ℂ) :
    ∃ M : Matrix (RegionConfig Out (R ∪ S)) (RegionConfig Out (R ∪ S)) ℂ,
      place R K * place S L - place S L * place R K = place (R ∪ S) M := by
  set K' := ManyBody.subregionPlace (X := Out) Finset.subset_union_left K
  set L' := ManyBody.subregionPlace (X := Out) (Finset.subset_union_right (s₁ := R)) L
  refine ⟨K' * L' - L' * K', ?_⟩
  rw [ManyBody.place_sub, ManyBody.place_mul, ManyBody.place_mul,
    ManyBody.place_subregionPlace, ManyBody.place_subregionPlace]

end TNLean.PEPS
