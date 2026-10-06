/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.DependentTorusClosureIndependence
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Exact dimension of the actual four-cut intersection

For four independently chosen G-injective blocks with eight separately typed
semi-regular bonds, commuting class-labelled closures form a basis of the
actual four-cut intersection. Its dimension is the number of simultaneous
conjugacy classes of commuting pairs. Spanning is the already derived
four-cut theorem, and independence is obtained from the true physical local
inverses and bond trace-dual functionals.

Source: SCP10, arXiv:1001.3807, Theorems 5.5 and 5.9, lines 1421–1513 and
1582–1621. This proves the four-block closure-space dimension, not its
identification with a microscopic plaquette parent kernel on arbitrary tori.
-/

noncomputable section
namespace TNLean.PEPS.DependentTorus

local notation "tail" => (torusLabelledBondTail (width := 2) (height := 2))
local notation "head" => (torusLabelledBondHead (width := 2) (height := 2))

variable {G : Type*} [Group G] [Finite G]
variable (D : Bond → Type*) [∀ e, Fintype (D e)] [∀ e, DecidableEq (D e)]
variable {Phys : Vertex → Type*}

/-- Commuting representatives and commuting classes yield the same set of
actual dependent-dimensional closures. Source: SCP10, Definition 5.8. -/
theorem range_closure_commuting_eq_range_closureClass
    (U : (e : Bond) → G →* Matrix (D e) (D e) ℂ)
    (A : (v : Vertex) → LocalConfig D v → Phys v → ℂ)
    (hA : ∀ v g, DependentBondNetwork.localSiteMap tail head D A v ∘ₗ
      DependentBondNetwork.incidentRepresentation tail head D U v g =
        DependentBondNetwork.localSiteMap tail head D A v) :
    Set.range (fun p : {p : G × G // Commute p.1 p.2} => closure D U A p.1.1 p.1.2) =
      Set.range (fun C : CommutingPairConjugacyClass G => closureClass D U A hA C.1) := by
  ext ψ
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨⟨pairConjugacyClass G p.1, p.2⟩, rfl⟩
  · rintro ⟨⟨C, hC⟩, rfl⟩
    revert hC
    refine Quotient.inductionOn C (fun p => ?_)
    intro hC
    exact ⟨⟨p, hC⟩, rfl⟩

/-- The commuting closure span has precisely one dimension per simultaneous
conjugacy class of commuting pairs. Each bond and physical space may differ.
Source: the closure-space component of SCP10, Theorem 5.9. -/
theorem finrank_commutingClosureSpan [∀ v, Finite (Phys v)]
    (U : (e : Bond) → G →* Matrix (D e) (D e) ℂ)
    (hU : ∀ e, Representation.IsSemiRegular (Matrix.toLinAlgEquiv'.toMonoidHom.comp (U e)))
    (A : (v : Vertex) → LocalConfig D v → Phys v → ℂ)
    (hA : ∀ v, IsGInjective (DependentBondNetwork.incidentRepresentation tail head D U v)
      (DependentBondNetwork.localSiteMap tail head D A v)) :
    Module.finrank ℂ (commutingClosureSpan D U A) = Nat.card (CommutingPairConjugacyClass G) := by
  let := Fintype.ofFinite (CommutingPairConjugacyClass G)
  rw [commutingClosureSpan,
    range_closure_commuting_eq_range_closureClass D U A (fun v => (hA v).invariant)]
  simpa only [Nat.card_eq_fintype_card] using
    finrank_span_eq_card (linearIndependent_closureClass_commuting D U hU A hA)

/-- The source's actual four-cut intersection has exact commuting-class dimension,
with eight independent semi-regular bond representations and four independent
G-injective physical tensors. No spanning or independence premise is assumed.
Source: SCP10, Theorem 5.5 and the closure independence in Theorem 5.9.
The microscopic parent-to-four-cut identification is a separate theorem. -/
theorem finrank_fourCutSpace [∀ v, Finite (Phys v)]
    (U : (e : Bond) → G →* Matrix (D e) (D e) ℂ)
    (hU : ∀ e, Representation.IsSemiRegular (Matrix.toLinAlgEquiv'.toMonoidHom.comp (U e)))
    (A : (v : Vertex) → LocalConfig D v → Phys v → ℂ)
    (hA : ∀ v, IsGInjective (DependentBondNetwork.incidentRepresentation tail head D U v)
      (DependentBondNetwork.localSiteMap tail head D A v)) :
    Module.finrank ℂ (fourCutSpace D A) = Nat.card (CommutingPairConjugacyClass G) := by
  rw [fourCutSpace_eq_commutingClosureSpan D U hU A hA,
    finrank_commutingClosureSpan D U hU A hA]

end TNLean.PEPS.DependentTorus
