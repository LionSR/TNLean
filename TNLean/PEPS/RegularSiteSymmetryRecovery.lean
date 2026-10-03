/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.RegularSiteGram
import TNLean.PEPS.GInjectiveRangeEquivalence

/-!
# Recovering regular virtual permutation symmetries from a G-injective site

The physical vectors of a regular G-injective site distinguish the simultaneous
translation orbits of its virtual group labels. For at least two virtual legs,
the permutations of group labels that leave every physical site vector unchanged
are consequently exactly the left translations by group elements.

These are auxiliary reconstruction results derived from the definition of
G-injectivity in Schuch, Cirac, and Pérez-García, arXiv:1001.3807,
Definition 5.1, `Papers/1001.3807/paper_v3.tex`, lines 1278–1296.
They classify simultaneous permutations of the group basis. They do not
assert a Fundamental Theorem for arbitrary complex virtual changes of basis.

## References

- [arXiv:1001.3807](https://arxiv.org/abs/1001.3807) -- N. Schuch, J. I. Cirac,
  D. Pérez-García, *PEPS as ground states: degeneracy and topology*
-/

namespace TNLean.PEPS

open scoped Matrix

section Averaging

variable {G W P : Type*} [Group G] [Fintype G]
variable [AddCommGroup W] [Module ℂ W] [AddCommGroup P] [Module ℂ P]

/-- Equality of physical images under a G-injective map is precisely equality
after averaging over its virtual symmetry. Auxiliary consequence of SCP10,
Definition 5.1, lines 1278–1296. -/
theorem IsGInjective.averageMap_eq_iff_apply_eq
    {ρ : Representation ℂ G W} {T : W →ₗ[ℂ] P} (hT : IsGInjective ρ T) (x y : W) :
    ρ.averageMap x = ρ.averageMap y ↔ T x = T y := by
  rw [← sub_eq_zero, ← map_sub, ← LinearMap.mem_ker, ← hT.ker_eq_ker_averageMap,
    LinearMap.mem_ker, map_sub, sub_eq_zero]

end Averaging

section RegularSite

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {κ : Type*}
attribute [local instance] Representation.invertibleFintypeCardComplex

private theorem regularLegProjector_self (η : ι → G) :
    regularLegProjector ι η η = (Fintype.card G : ℂ)⁻¹ := by
  classical
  obtain ⟨i⟩ := ‹Nonempty ι›
  have hfix (g : G) : η = g • η ↔ g = 1 := by
    constructor
    · intro h
      have hi := congrFun h i
      change η i = g * η i at hi
      exact mul_right_cancel (hi.symm.trans (one_mul (η i)).symm)
    · rintro rfl
      simp
  simp [regularLegProjector_apply, hfix]

omit [DecidableEq G] in
/-- A regular G-injective tensor distinguishes precisely the simultaneous
translation orbits of its virtual configurations. Auxiliary consequence of
SCP10, Definition 5.1, lines 1278–1296. -/
theorem IsGInjective.regularSite_coeff_eq_iff_common_translation
    {a : (ι → G) → κ → ℂ}
    (ha : IsGInjective (regularLegRepresentation ι) (regularSiteMap a))
    (η θ : ι → G) :
    a η = a θ ↔ ∃ g : G, η = g • θ := by
  classical
  constructor
  · intro h
    have hphysical : regularSiteMap a (Pi.single η 1) =
        regularSiteMap a (Pi.single θ 1) := by
      change (Matrix.of fun s ξ ↦ a ξ s) *ᵥ Pi.single η 1 =
        (Matrix.of fun s ξ ↦ a ξ s) *ᵥ Pi.single θ 1
      rw [Matrix.mulVec_single_one, Matrix.mulVec_single_one]
      exact h
    have havg := (ha.averageMap_eq_iff_apply_eq (Pi.single η 1) (Pi.single θ 1)).mpr
      hphysical
    have hentry := congrFun havg η
    change regularLegProjector ι η η = regularLegProjector ι η θ at hentry
    by_contra hnot
    have hzero : regularLegProjector ι η θ = 0 := by
      rw [regularLegProjector_apply]
      simp only [not_exists] at hnot
      simp [hnot]
    rw [regularLegProjector_self, hzero] at hentry
    exact (inv_ne_zero (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)) hentry
  · rintro ⟨g, rfl⟩
    exact funext (ha.regularSiteMap_translation g θ)

omit [Nonempty ι] [DecidableEq G] in
/-- On at least two virtual legs, a simultaneous relabelling leaves a regular
G-injective site unchanged exactly when it is a left group translation.
Auxiliary reconstruction result from SCP10, Definition 5.1, lines 1278–1296. -/
theorem IsGInjective.regularSite_relabelling_invariant_iff [Nontrivial ι]
    {a : (ι → G) → κ → ℂ}
    (ha : IsGInjective (regularLegRepresentation ι) (regularSiteMap a)) (e : G → G) :
    (∀ η : ι → G, a (e ∘ η) = a η) ↔ ∃ g : G, ∀ h : G, e h = g * h := by
  classical
  constructor
  · intro he
    obtain ⟨i, j, hij⟩ := exists_pair_ne ι
    refine ⟨e 1, fun h ↦ ?_⟩
    let η : ι → G := fun k ↦ if k = j then h else 1
    obtain ⟨g, hg⟩ := (ha.regularSite_coeff_eq_iff_common_translation (e ∘ η) η).mp
      (he η)
    have hi : e 1 = g := by
      have hi := congrFun hg i
      change e (η i) = g * η i at hi
      simpa [η, hij] using hi
    have hj := congrFun hg j
    change e (η j) = g * η j at hj
    simpa [η, ← hi] using hj
  · rintro ⟨g, hg⟩ η
    have hη : e ∘ η = g • η := funext fun i ↦ hg (η i)
    rw [hη]
    exact funext (ha.regularSiteMap_translation g η)

end RegularSite

end TNLean.PEPS
