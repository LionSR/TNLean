/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.TorusTranslationInvariant
import TNLean.PEPS.RegularWalkHolonomy
/-!
# Literal updates of one native directed bond

An assigned directed transport determines the ordered coefficient even when
its native positive step crosses a torus seam. These auxiliary coordinate
identities support SCP10, Section 6.6, lines 2340–2423; they do not assert that
an arbitrary update is a physical operation.
-/
noncomputable section
namespace TNLean.PEPS
variable {width height : ℕ} [NeZero width] [NeZero height]
variable [Fact (2 < width)] [Fact (2 < height)]
local instance directedUpdateWidthOne : Fact (1 < width) :=
  ⟨by have := Fact.out (p := 2 < width); omega⟩
local instance directedUpdateHeightOne : Fact (1 < height) :=
  ⟨by have := Fact.out (p := 2 < height); omega⟩
local notation "X" => TorusVertex width height
local notation "Γₜ" => torusGraph width height
variable {G : Type*} [Group G]
private def nextVertex (axis : Bool) (p : X) : X :=
  if axis then (p.1, p.2 + 1) else (p.1 + 1, p.2)
private theorem stepAdj (axis : Bool) (p : X) : (Γₜ).Adj p (nextVertex axis p) := by
  cases axis
  · exact torusGraph_adj_right p.1 p.2
  · exact torusGraph_adj_up p.1 p.2
/-- Positive rightward (`false`) or upward (`true`) native transport.
Source: SCP10, oriented string operators, lines 2340–2423. -/
def torusDirectedBondTransport (axis : Bool) (u : Edge Γₜ → G) (p : X) : G :=
  regularDirectedTransport u (stepAdj axis p)
/-- Replace one directed transport, converting it to its native ordered coefficient.
Source: SCP10, the elementary string operation, lines 2340–2423. -/
def torusDirectedBondUpdate (axis : Bool) (p : X) (t : G) (u : Edge Γₜ → G)
    (e : Edge Γₜ) : G :=
  if e = Edge.ofAdj (stepAdj axis p) then
    if p < nextVertex axis p then t else t⁻¹
  else u e
/-- Exactly the selected transport changes in its own axis, with seam inversions included.
Source: SCP10, oriented elementary movement, lines 2340–2423. -/
theorem torusDirectedBondTransport_update_same (axis : Bool) (p q : X) (t : G)
    (u : Edge Γₜ → G) :
    torusDirectedBondTransport axis (torusDirectedBondUpdate axis p t u) q =
      if q = p then t else torusDirectedBondTransport axis u q := by
  by_cases hq : q = p
  · subst q
    simp only [torusDirectedBondTransport, regularDirectedTransport,
      torusDirectedBondUpdate, ite_true]
    split_ifs <;> simp
  · have hn : Edge.ofAdj (stepAdj axis q) ≠ Edge.ofAdj (stepAdj axis p) := by
      cases axis
      · exact (torusRightEdge_injective (width := width) (height := height)).ne hq
      · exact (torusUpEdge_injective (width := width) (height := height)).ne hq
    have he : torusDirectedBondUpdate axis p t u (Edge.ofAdj (stepAdj axis q)) =
        u (Edge.ofAdj (stepAdj axis q)) := by
      simp only [torusDirectedBondUpdate, ite_eq_right hn]
    simp only [torusDirectedBondTransport, regularDirectedTransport, he, ite_eq_right hq]
/-- Updating one axis retains every transport in the other axis.
Source: SCP10, literal string movement, lines 2340–2423. -/
theorem torusDirectedBondTransport_update_other (axis : Bool) (p q : X) (t : G)
    (u : Edge Γₜ → G) :
    torusDirectedBondTransport (!axis) (torusDirectedBondUpdate axis p t u) q =
      torusDirectedBondTransport (!axis) u q := by
  have hn : Edge.ofAdj (stepAdj (!axis) q) ≠ Edge.ofAdj (stepAdj axis p) := by
    cases axis
    · exact (torusRightEdge_ne_torusUpEdge p q).symm
    · exact torusRightEdge_ne_torusUpEdge q p
  have he : torusDirectedBondUpdate axis p t u (Edge.ofAdj (stepAdj (!axis) q)) =
      u (Edge.ofAdj (stepAdj (!axis) q)) := by
    simp only [torusDirectedBondUpdate, ite_eq_right hn]
  simp only [torusDirectedBondTransport, regularDirectedTransport, he]
/-- Both axes obey the literal single-edge update rule. -/
theorem torusDirectedBondTransport_update (axis ax : Bool) (p q : X) (t : G)
    (u : Edge Γₜ → G) :
    torusDirectedBondTransport ax (torusDirectedBondUpdate axis p t u) q =
      if ax = axis ∧ q = p then t else torusDirectedBondTransport ax u q := by
  cases axis <;> cases ax
  · simpa using torusDirectedBondTransport_update_same false p q t u
  · simpa using torusDirectedBondTransport_update_other false p q t u
  · simpa using torusDirectedBondTransport_update_other true p q t u
  · simpa using torusDirectedBondTransport_update_same true p q t u
/-- Every other ordered bond coefficient is retained literally.
Source: SCP10, the elementary string operation, lines 2340–2423. -/
theorem torusDirectedBondUpdate_eq_of_ne (axis : Bool) (p : X) (t : G)
    (u : Edge Γₜ → G) (e : Edge Γₜ) (he : e ≠ Edge.ofAdj (stepAdj axis p)) :
    torusDirectedBondUpdate axis p t u e = u e := by
  simp only [torusDirectedBondUpdate, ite_eq_right he]
end TNLean.PEPS
