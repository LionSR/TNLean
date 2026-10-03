/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.GInjectiveTorusSectors
import TNLean.PEPS.RegularMatrixEquiv

/-!
# Independent torus closures for regular G-injective tensors

The regular averaging projector is a canonical isometric site map. The native regular
matrices are semi-regular, so the general semi-regular closure theorem gives nonvanishing
and independence for every regular G-injective site map, without a local isometry
assumption.

**Scope restriction (regular virtual representation):** the commuting-family independence
result is the regular-representation part of Schuch, Cirac, and Pérez-García,
arXiv:1001.3807, Theorem 5.9, source lines 1582–1621. Identification with the
parent-Hamiltonian ground space remains separate; see
`docs/paper-gaps/rmp_peps_quantum_double_g_isometry.tex`. Independence for
noncommuting classes is an auxiliary extension of the closure-vector argument, not a
ground-state assertion. Rectangular and size-one tori are algebraic extensions.

## References

- [arXiv:1001.3807](https://arxiv.org/abs/1001.3807) -- N. Schuch, J. I. Cirac,
  D. Pérez-García, *PEPS as ground states: degeneracy and topology*
-/

open scoped BigOperators Matrix
open Matrix LinearMap Representation GroupAlgebra

namespace TNLean.PEPS

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]
attribute [local instance] Representation.invertibleFintypeCardComplex

/-- The regular averaging projector is an isometric site map with factor one.
Source: SCP10, Definition 6.1, lines 1692–1700. -/
theorem isGIsometric_regularAveragingSite :
    IsGIsometric (torusLegRep (leftRegularMatrix G))
      (siteMap (averagingSite (leftRegularMatrix G))) := by
  rw [siteMap_averagingSite]
  let ρ := torusLegRep (leftRegularMatrix G)
  have hinv : ∀ g, ρ.averageMap ∘ₗ ρ g = ρ.averageMap := by
    intro g
    simpa only [siteMap_averagingSite] using averagingSite_invariant (leftRegularMatrix G) g
  apply isGIsometric_of_coordinateAdjoint_comp hinv (show (0 : ℝ) < 1 by norm_num)
  simp only [Complex.ofReal_one, one_smul]
  apply LinearMap.ext
  intro x
  apply dotProduct_eq
  intro y
  have hAvg := averageMap_dotProduct_of_unitary ρ torusLegRep_leftRegularMatrix_unitary
  have h := coordinateAdjoint_dotProduct ρ.averageMap (star y) (ρ.averageMap x)
  rw [hAvg, ρ.averageMap_id _ (ρ.averageMap_invariant x)] at h
  simpa only [LinearMap.comp_apply, star_star, dotProduct_comm] using h

variable {width height : ℕ} [NeZero width] [NeZero height]
variable {Phys : Type*} [Fintype Phys]

omit [Fintype Phys] in
/-- Every actual regular G-injective closure vector is nonzero, including noncommuting
closure pairs. No ground-space membership is asserted. -/
theorem IsGInjective.torusGClosure_ne_zero [Finite Phys]
    {a : G → G → G → G → Phys → ℂ}
    (ha : IsGInjective (torusLegRep (leftRegularMatrix G)) (siteMap a)) (g h : G) :
    torusGClosure (width := width) (height := height) (leftRegularMatrix G) a g h ≠ 0 :=
  ha.torusGClosure_ne_zero_of_isSemiRegular isSemiRegular_leftRegularMatrix g h

omit [Fintype Phys] in
/-- The actual class-indexed closure vectors of a regular G-injective tensor are linearly
independent. Independence for noncommuting classes is an auxiliary extension of the
closure-vector argument of SCP10, Theorem 5.9. -/
theorem IsGInjective.linearIndependent_torusGClosureClass [Finite Phys]
    {a : G → G → G → G → Phys → ℂ}
    (ha : IsGInjective (torusLegRep (leftRegularMatrix G)) (siteMap a)) :
    LinearIndependent ℂ (torusGClosureClass (width := width) (height := height)
      (leftRegularMatrix G) a ha.invariant) :=
  ha.linearIndependent_torusGClosureClass_of_isSemiRegular isSemiRegular_leftRegularMatrix

omit [Fintype Phys] in
/-- The commuting pair classes give independent actual closures of every regular
G-injective tensor. This proves the regular-representation independence component of
SCP10, Theorem 5.9, lines 1582–1621, without an isometry hypothesis. -/
theorem IsGInjective.linearIndependent_torusGClosureClass_commuting [Finite Phys]
    {a : G → G → G → G → Phys → ℂ}
    (ha : IsGInjective (torusLegRep (leftRegularMatrix G)) (siteMap a)) :
    LinearIndependent ℂ (fun C : CommutingPairConjugacyClass G =>
      torusGClosureClass (width := width) (height := height)
        (leftRegularMatrix G) a ha.invariant C.1) :=
  ha.linearIndependent_torusGClosureClass_commuting_of_isSemiRegular
    isSemiRegular_leftRegularMatrix

end TNLean.PEPS
