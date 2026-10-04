/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.GInjectiveTorusProjector
import TNLean.PEPS.PairConjugacyOperators
import TNLean.PEPS.TorusProjectorExtraction

/-!
# Independent torus closures for semi-regular G-injective tensors

A local G-injective left inverse sends the actual torus closures to canonical
averaging-projector closures. Applying the explicit physical extraction to these
canonical closures gives their simultaneous-conjugacy operators, multiplied by one
nonzero scalar. The operators are independent for a semi-regular virtual representation;
therefore the actual closure vectors are independent as well.

Source: Schuch, Cirac, and Pérez-García, arXiv:1001.3807, the independence argument
of Theorem 5.9, `Papers/1001.3807/paper_v3.tex`, lines 1582–1621. The commuting-family
result proves this independence component with its semi-regular hypothesis. Independence
for all pair classes, including noncommuting pairs, is an auxiliary extension. Rectangular
and size-one tori are algebraic extensions. No parent-Hamiltonian ground-space assertion
is made; that separate part of the source theorem remains open, as recorded in
`docs/paper-gaps/rmp_peps_quantum_double_g_isometry.tex`.

## References

- [arXiv:1001.3807](https://arxiv.org/abs/1001.3807) -- N. Schuch, J. I. Cirac,
  D. Pérez-García, *PEPS as ground states: degeneracy and topology*
-/

open scoped BigOperators Matrix

namespace TNLean.PEPS

variable {G : Type*} [Group G] [Finite G]
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {width height : ℕ} [NeZero width] [NeZero height]
variable {Phys : Type*} [Finite Phys]

/-- Actual class-indexed closures of a semi-regular G-injective tensor are independent.
The noncommuting classes form an auxiliary extension of the independence argument in
SCP10, Theorem 5.9, lines 1582–1621; no ground-space membership is asserted. -/
theorem IsGInjective.linearIndependent_torusGClosureClass_of_isSemiRegular
    {U : G →* Matrix V V ℂ} {a : V → V → V → V → Phys → ℂ}
    (ha : IsGInjective (torusLegRep U) (siteMap a))
    (hU : Representation.IsSemiRegular (Matrix.toLinAlgEquiv'.toMonoidHom.comp U)) :
    LinearIndependent ℂ (torusGClosureClass (width := width) (height := height)
      U a ha.invariant) := by
  classical
  let _ := Fintype.ofFinite G
  let _ := Fintype.ofFinite Phys
  obtain ⟨F, hF⟩ := ha.exists_torusGClosure_averagingSite
    (width := width) (height := height)
  let α : ℂ := (Fintype.card G : ℂ)⁻¹ ^ Fintype.card (TorusVertex width height)
  have hα : α ≠ 0 := pow_ne_zero _ (inv_ne_zero (Nat.cast_ne_zero.mpr Fintype.card_ne_zero))
  let E := α⁻¹ • torusProjectorExtraction (width := width) (height := height) U
  have hclass : (E.comp (torusPhysicalMap F)) ∘
      torusGClosureClass (width := width) (height := height) U a ha.invariant =
      pairConjugacyClassKroneckerOperator U := by
    funext C
    refine Quotient.inductionOn C (fun p => ?_)
    change α⁻¹ • torusProjectorExtraction U
      (torusPhysicalMap F (torusGClosure U a p.1 p.2)) = _
    rw [hF, torusProjectorExtraction_torusGClosure U hU]
    change α⁻¹ • (α • _) =
      pairConjugacyClassKroneckerOperator U (pairConjugacyClass G p)
    rw [pairConjugacyClassKroneckerOperator_pairConjugacyClass U p]
    rw [smul_smul, inv_mul_cancel₀ hα, one_smul]
  apply LinearIndependent.of_comp (E.comp (torusPhysicalMap F))
  rw [hclass]
  exact linearIndependent_pairConjugacyClassKroneckerOperator U hU

/-- Every actual closure of a semi-regular G-injective tensor is nonzero. This includes
noncommuting closure pairs without claiming ground-space membership. Source: SCP10,
Theorem 5.9, lines 1582–1621, and the same auxiliary all-pair argument. -/
theorem IsGInjective.torusGClosure_ne_zero_of_isSemiRegular
    {U : G →* Matrix V V ℂ} {a : V → V → V → V → Phys → ℂ}
    (ha : IsGInjective (torusLegRep U) (siteMap a))
    (hU : Representation.IsSemiRegular (Matrix.toLinAlgEquiv'.toMonoidHom.comp U))
    (g h : G) :
    torusGClosure (width := width) (height := height) U a g h ≠ 0 := by
  exact (ha.linearIndependent_torusGClosureClass_of_isSemiRegular hU).ne_zero
    (pairConjugacyClass G (g, h))

/-- Commuting pair classes give independent actual closures of every semi-regular
G-injective tensor. This is the independence component of SCP10, Theorem 5.9,
lines 1582–1621, without a local isometry or global Gram assumption. -/
theorem IsGInjective.linearIndependent_torusGClosureClass_commuting_of_isSemiRegular
    {U : G →* Matrix V V ℂ} {a : V → V → V → V → Phys → ℂ}
    (ha : IsGInjective (torusLegRep U) (siteMap a))
    (hU : Representation.IsSemiRegular (Matrix.toLinAlgEquiv'.toMonoidHom.comp U)) :
    LinearIndependent ℂ (fun C : CommutingPairConjugacyClass G =>
      torusGClosureClass (width := width) (height := height) U a ha.invariant C.1) :=
  (ha.linearIndependent_torusGClosureClass_of_isSemiRegular hU).comp
    Subtype.val Subtype.val_injective

end TNLean.PEPS
