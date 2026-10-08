/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.GInjective

/-!
# G-isometry under changes of coordinate labels

Permuting orthonormal virtual and physical basis labels preserves G-isometry,
provided the virtual permutation intertwines the representations. This includes
enumerating finite physical alphabets and grouping fine boundary bonds into
coarse legs. No Gram identity for the transported map is assumed.

Source: Schuch, Cirac, and Pérez-García, arXiv:1001.3807, Definition 6.1 and
Observations 6.5–6.6, lines 1692–1700 and 1825–1920.
-/

open scoped BigOperators Matrix

namespace TNLean.PEPS

variable {G : Type*} [Group G]
variable {ι κ ι' κ' : Type*} [Fintype ι] [Fintype κ] [Fintype ι'] [Fintype κ']

/-- G-isometry is unchanged by coordinate-label bijections intertwining the
virtual actions. Source: SCP10, Definition 6.1 and Observations 6.5–6.6. -/
theorem IsGIsometric.of_coordinateEquiv
    {ρ : Representation ℂ G (ι → ℂ)} {ρ' : Representation ℂ G (ι' → ℂ)}
    {T : (ι → ℂ) →ₗ[ℂ] (κ → ℂ)} {T' : (ι' → ℂ) →ₗ[ℂ] (κ' → ℂ)}
    (hT : IsGIsometric ρ T) (e : ι' ≃ ι) (f : κ' ≃ κ)
    (hρ : ∀ g x, (ρ' g x) ∘ e.symm = ρ g (x ∘ e.symm))
    (hmap : ∀ x, (T' x) ∘ f.symm = T (x ∘ e.symm)) :
    IsGIsometric ρ' T' := by
  have hmem (x : ι' → ℂ) (hx : x ∈ ρ'.invariants) :
      x ∘ e.symm ∈ ρ.invariants := by
    intro g
    rw [← hρ, hx g]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro g
    apply LinearMap.ext
    intro x
    apply f.symm.surjective.injective_comp_right
    simp only [LinearMap.comp_apply, hmap, hρ]
    exact LinearMap.congr_fun (hT.invariant g) (x ∘ e.symm)
  · intro x hx hz
    have hzero : T (x ∘ e.symm) = 0 := by rw [← hmap, hz]; rfl
    have h := hT.injOn_invariants _ (hmem x hx) hzero
    exact e.symm.surjective.injective_comp_right h
  · obtain ⟨c, hc, hinner⟩ := hT.exists_inner_eq
    refine ⟨c, hc, fun x hx y hy => ?_⟩
    have hv : star (x ∘ e.symm) ⬝ᵥ (y ∘ e.symm) = star x ⬝ᵥ y :=
      Equiv.sum_comp e.symm (fun i => star (x i) * y i)
    have hp : star ((T' x) ∘ f.symm) ⬝ᵥ ((T' y) ∘ f.symm) =
        star (T' x) ⬝ᵥ T' y :=
      Equiv.sum_comp f.symm (fun i => star (T' x i) * T' y i)
    rw [← hp, hmap, hmap, hinner _ (hmem x hx) _ (hmem y hy), hv]

end TNLean.PEPS
