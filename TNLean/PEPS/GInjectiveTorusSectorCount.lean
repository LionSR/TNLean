/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.GInjectiveTorusSectors
import TNLean.PEPS.PairConjugacyCentralizer
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Dimension of the commuting G-injective torus closure space

For a semi-regular virtual representation, the commuting class-labelled
torus closure vectors of a G-injective tensor are linearly independent.
Their span therefore has dimension equal to the sum of the numbers of
conjugacy classes of centralizers, one summand for each conjugacy class
of the group.

Source: Schuch, Cirac, and Pérez-García, arXiv:1001.3807, Theorem 5.9 and
the discussion following its proof, `Papers/1001.3807/paper_v3.tex`,
lines 1582–1621. This is the dimension of the actual commuting closure
span. Identification of this span with the parent-Hamiltonian ground
space remains a separate assertion. Rectangular and size-one tori are
algebraic extensions of the source's square-torus contraction.
-/

open scoped BigOperators

namespace TNLean.PEPS

variable {G : Type*} [Group G] [Finite G]
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {width height : ℕ} [NeZero width] [NeZero height]
variable {Phys : Type*} [Finite Phys]

omit [Finite G] [Finite Phys] in
/-- Commuting pair representatives and commuting pair classes give the same
set of actual torus vectors. Source: SCP10, Definition 5.8 and Theorem 5.9,
lines 1560–1589. -/
theorem range_torusGClosure_commuting_eq_range_torusGClosureClass
    (U : G →* Matrix V V ℂ) (a : V → V → V → V → Phys → ℂ)
    (ha : ∀ x, siteMap a ∘ₗ torusLegRep U x = siteMap a) :
    Set.range (fun p : {p : G × G // Commute p.1 p.2} ↦
      torusGClosure (width := width) (height := height) U a p.1.1 p.1.2) =
      Set.range (fun C : CommutingPairConjugacyClass G ↦
        torusGClosureClass (width := width) (height := height) U a ha C.1) := by
  ext ψ
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨⟨pairConjugacyClass G p.1, p.2⟩, rfl⟩
  · rintro ⟨⟨C, hC⟩, rfl⟩
    revert hC
    refine Quotient.inductionOn C (fun p ↦ ?_)
    intro hC
    exact ⟨⟨p, hC⟩, rfl⟩

/-- The dimension of the actual commuting closure span is the number of
commuting pair-conjugacy classes. This is the dimension component of SCP10,
Theorem 5.9, lines 1582–1621; the ground-space identification is separate. -/
theorem IsGInjective.finrank_span_torusGClosureClass_commuting_of_isSemiRegular
    {U : G →* Matrix V V ℂ} {a : V → V → V → V → Phys → ℂ}
    (ha : IsGInjective (torusLegRep U) (siteMap a))
    (hU : Representation.IsSemiRegular (Matrix.toLinAlgEquiv'.toMonoidHom.comp U)) :
    Module.finrank ℂ (Submodule.span ℂ (Set.range
      (fun C : CommutingPairConjugacyClass G ↦
        torusGClosureClass (width := width) (height := height) U a ha.invariant C.1))) =
      Nat.card (CommutingPairConjugacyClass G) := by
  let _ := Fintype.ofFinite (CommutingPairConjugacyClass G)
  simpa only [Nat.card_eq_fintype_card] using
    finrank_span_eq_card
      (ha.linearIndependent_torusGClosureClass_commuting_of_isSemiRegular
        (width := width) (height := height) hU)

open Classical in
/-- The dimension of the actual commuting closure span is the centralizer
sum counting quantum-double sector labels. Source: SCP10, Theorem 5.9 and
the discussion following its proof, lines 1582–1621. -/
theorem IsGInjective.finrank_span_torusGClosureClass_commuting_eq_sum_card_centralizer
    [Fintype G]
    {U : G →* Matrix V V ℂ} {a : V → V → V → V → Phys → ℂ}
    (ha : IsGInjective (torusLegRep U) (siteMap a))
    (hU : Representation.IsSemiRegular (Matrix.toLinAlgEquiv'.toMonoidHom.comp U)) :
    Module.finrank ℂ (Submodule.span ℂ (Set.range
      (fun C : CommutingPairConjugacyClass G ↦
        torusGClosureClass (width := width) (height := height) U a ha.invariant C.1))) =
      ∑ C : ConjClasses G, Nat.card (ConjClasses (Subgroup.centralizer ({C.out} : Set G))) := by
  rw [ha.finrank_span_torusGClosureClass_commuting_of_isSemiRegular hU,
    card_commutingPairConjugacyClass_eq_sum_card_centralizer]

open Classical in
/-- The span of all commuting-pair torus closures has the centralizer-sum
dimension, without a choice of pair-class representatives. Source: SCP10,
Theorem 5.9 and the discussion following its proof, lines 1582–1621. -/
theorem IsGInjective.finrank_span_torusGClosure_commuting_eq_sum_card_centralizer
    [Fintype G]
    {U : G →* Matrix V V ℂ} {a : V → V → V → V → Phys → ℂ}
    (ha : IsGInjective (torusLegRep U) (siteMap a))
    (hU : Representation.IsSemiRegular (Matrix.toLinAlgEquiv'.toMonoidHom.comp U)) :
    Module.finrank ℂ (Submodule.span ℂ (Set.range
      (fun p : {p : G × G // Commute p.1 p.2} ↦
        torusGClosure (width := width) (height := height) U a p.1.1 p.1.2))) =
      ∑ C : ConjClasses G, Nat.card (ConjClasses (Subgroup.centralizer ({C.out} : Set G))) := by
  rw [range_torusGClosure_commuting_eq_range_torusGClosureClass U a ha.invariant]
  exact ha.finrank_span_torusGClosureClass_commuting_eq_sum_card_centralizer hU

end TNLean.PEPS
