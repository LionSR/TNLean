/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.NativeTorusClosureIndependence
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Exact dimension of nonuniform native torus closure spans

On every native torus with both periods at least three, separately represented
semi-regular bonds and unrelated G-injective site tensors give one independent
closure state for each simultaneous-conjugacy class of commuting pairs.
Every bond and every physical alphabet retains its actual dimension.

Source: SCP10, arXiv:1001.3807, Theorem 5.9. This module proves the exact
closure-span dimension; identification with the actual microscopic parent
kernel is established separately.
-/

noncomputable section
namespace TNLean.PEPS.NativeTorus

variable {width height : ℕ} [NeZero width] [NeZero height]
variable [Fact (2 < width)] [Fact (2 < height)]

local instance : Fact (1 < width) := ⟨by have := Fact.out (p := 2 < width); omega⟩
local instance : Fact (1 < height) := ⟨by have := Fact.out (p := 2 < height); omega⟩

local notation "Vertex" => TorusVertex width height
local notation "Bond" => Edge (torusGraph width height)
local notation "tail" => (graphEdgeTail (Γ := torusGraph width height))
local notation "head" => (graphEdgeHead (Γ := torusGraph width height))

variable {G : Type*} [Group G] [Finite G]
variable (D : Edge (torusGraph width height) → Type*) [∀ e, Fintype (D e)] [∀ e, DecidableEq (D e)]
variable {Phys : TorusVertex width height → Type*}

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

end TNLean.PEPS.NativeTorus
