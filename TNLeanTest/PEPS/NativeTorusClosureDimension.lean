/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.NativeTorusClosureDimension

/-!
# Regression checks for native nonuniform closure independence

The statements retain arbitrary torus periods, independently typed bonds,
independently typed physical sites, and the source's ordered-edge orientation.
-/

noncomputable section
namespace TNLean.PEPS.NativeTorus

variable {width height : ℕ} [NeZero width] [NeZero height]
variable [Fact (2 < width)] [Fact (2 < height)]

local instance : Fact (1 < width) := ⟨by have := Fact.out (p := 2 < width); omega⟩
local instance : Fact (1 < height) := ⟨by have := Fact.out (p := 2 < height); omega⟩

variable {G : Type*} [Group G] [Finite G]
variable (D : Edge (torusGraph width height) → Type*)
variable [∀ e, Fintype (D e)] [∀ e, DecidableEq (D e)]
variable {Phys : TorusVertex width height → Type*} [∀ v, Finite (Phys v)]

example
    (U : (e : Edge (torusGraph width height)) → G →* Matrix (D e) (D e) ℂ)
    (hU : ∀ e, Representation.IsSemiRegular (Matrix.toLinAlgEquiv'.toMonoidHom.comp (U e)))
    (A : (v : TorusVertex width height) → LocalConfig D v → Phys v → ℂ)
    (hA : ∀ v, IsGInjective
      (DependentBondNetwork.incidentRepresentation graphEdgeTail graphEdgeHead D U v)
      (DependentBondNetwork.localSiteMap graphEdgeTail graphEdgeHead D A v)) :
    Module.finrank ℂ (commutingClosureSpan D U A) = Nat.card (CommutingPairConjugacyClass G) :=
  finrank_commutingClosureSpan D U hU A hA

example (g h : G) (v : TorusVertex width height) (hv : v.1 + 1 = 0) :
    torusClosureEdgeAssignment g h (torusRightEdge v) = h⁻¹ := by
  simp only [torusClosureEdgeAssignment_right, torusHorizontalClosureElement, hv, ↓reduceIte]

example (g h : G) (v : TorusVertex width height) (hv : v.2 + 1 = 0) :
    torusClosureEdgeAssignment g h (torusUpEdge v) = g := by
  simp only [torusClosureEdgeAssignment_up, torusVerticalClosureElement, hv, ↓reduceIte]

end TNLean.PEPS.NativeTorus
