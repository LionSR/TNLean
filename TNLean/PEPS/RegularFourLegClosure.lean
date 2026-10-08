/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.RegularTwoByTwoNonzero

/-!
# Native closures of four-coordinate regular tensors

The four-coordinate and native tensor conventions are identified explicitly.
Every native closure vector is nonzero, including every commuting closure.
Source: SCP10, arXiv:1001.3807, Theorem 5.9, lines 1582–1621.
-/

noncomputable section
open scoped BigOperators Matrix
namespace TNLean.PEPS
variable {G P : Type*} [Group G] [Fintype G] [DecidableEq G] [Fintype P]

/-- Four-coordinate regular G-isometry gives native four-leg G-isometry by
an exact coordinate bijection. Source: SCP10, Definitions 5.1 and 6.1. -/
theorem IsGIsometric.torusLegRep_of_regularFourLeg
    {a : (Fin 4 → G) → P → ℂ}
    (ha : IsGIsometric (regularLegRepresentation (Fin 4)) (regularSiteMap a)) :
    IsGIsometric (torusLegRep (leftRegularMatrix G))
      (siteMap (fun t r d l => a ![t, r, d, l])) := by
  refine ha.of_coordinateEquiv (finFourArrowEquiv G).symm (Equiv.refl P) ?_ ?_
  · intro g x
    funext η
    simp only [Function.comp_apply, Equiv.symm_symm, regularLegRepresentation_apply,
      torusLegRep_leftRegularMatrix_apply, finFourArrowEquiv_smul]
  · intro x
    funext s
    change (∑ η : G × G × G × G, a ![η.1, η.2.1, η.2.2.1, η.2.2.2] s * x η) =
      ∑ η : Fin 4 → G, a η s * x (finFourArrowEquiv G η)
    rw [← (finFourArrowEquiv G).sum_comp]
    apply Finset.sum_congr rfl
    intro η _
    congr 2
    exact (finFourArrowEquiv G).symm_apply_apply η

variable {width height : ℕ} [NeZero width] [NeZero height]

/-- Every actual native closure is nonzero. Commutation is needed for the
parent-ground-space interpretation, not for this nonvanishing result.
Source: SCP10, regular-isometric specialization of Theorem 5.9. -/
theorem IsGIsometric.regularFourLegClosure_ne_zero
    {a : (Fin 4 → G) → P → ℂ}
    (ha : IsGIsometric (regularLegRepresentation (Fin 4)) (regularSiteMap a)) (g h : G) :
    torusGClosure (width := width) (height := height) (leftRegularMatrix G)
      (fun t r d l => a ![t, r, d, l]) g h ≠ 0 :=
  ha.torusLegRep_of_regularFourLeg.torusGClosure_ne_zero g h

end TNLean.PEPS
