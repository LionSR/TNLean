/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Graph.Torus.TorusLatticeGraph
import TNLean.Network.DependentBond.DependentBondCut

/-!
# The native labelled bonds and four seam cuts

Every vertex anchors one rightward horizontal bond and one downward vertical
bond. The direction flag belongs to the edge identifier and is independent
of the head/tail endpoint flag. In particular, periods two retain parallel
edges and periods one retain both incidences of each self edge.

These edge maps instantiate the dependent-dimensional contraction model for
SCP10, Theorem 5.5. The four seam cuts at period two each remove four edges.
-/

namespace TNLean.PEPS

/-- Actual native bond IDs; false is horizontal and true is vertical. -/
abbrev TorusLabelledBond (width height : ℕ) := TorusVertex width height × Bool

variable {width height : ℕ}

/-- Horizontal bonds point right; vertical bonds point down from their upper endpoint. -/
def torusLabelledBondTail (e : TorusLabelledBond width height) : TorusVertex width height :=
  if e.2 then (e.1.1, e.1.2 + 1) else e.1

/-- The head is the right neighbor on a horizontal bond and the lower endpoint
on a vertical bond. -/
def torusLabelledBondHead (e : TorusLabelledBond width height) : TorusVertex width height :=
  if e.2 then e.1 else (e.1.1 + 1, e.1.2)

variable [NeZero width] [NeZero height]

/-- The edge set opened by one horizontal and one vertical seam. -/
def torusSeamCutBonds (c : ZMod width) (r : ZMod height) :
    Finset (TorusLabelledBond width height) :=
  Finset.univ.filter fun e ↦ if e.2 then e.1.2 + 1 = r else e.1.1 + 1 = c

@[simp]
theorem mem_torusSeamCutBonds_horizontal (c : ZMod width) (r : ZMod height)
    (v : TorusVertex width height) :
    (v, false) ∈ torusSeamCutBonds c r ↔ v.1 + 1 = c := by
  simp [torusSeamCutBonds]

@[simp]
theorem mem_torusSeamCutBonds_vertical (c : ZMod width) (r : ZMod height)
    (v : TorusVertex width height) :
    (v, true) ∈ torusSeamCutBonds c r ↔ v.2 + 1 = r := by
  simp [torusSeamCutBonds]

/-- The four-block source model has eight actual labelled edges. -/
theorem card_torusLabelledBond_two : Fintype.card (TorusLabelledBond 2 2) = 8 := by
  simp [TorusLabelledBond, TorusVertex]

/-- Each source cut opens four of the eight native edges. -/
theorem card_torusSeamCutBonds_two (c r : ZMod 2) : (torusSeamCutBonds c r).card = 4 := by
  fin_cases c <;> fin_cases r <;> decide

/-- Every bond remains uncut in the cut based at its anchoring vertex. This
is the geometric coverage used to derive full bond support from all four cuts. -/
theorem torusLabelledBond_not_mem_own_cut (e : TorusLabelledBond 2 2) :
    e ∉ torusSeamCutBonds e.1.1 e.1.2 := by
  rcases e with ⟨v, b⟩
  cases b <;> simp

/-- The unique incidence of each direction and endpoint polarity at a vertex.
The two flags distinguish all four incidences even on the one-by-one torus. -/
def torusIncidentEndpoint (v : TorusVertex width height) (z : Bool × Bool) :
    TNLean.Network.DependentBondNetwork.IncidentEndpoint torusLabelledBondTail
      torusLabelledBondHead v :=
  match z with
  | (false, false) => ⟨((v, false), false), rfl⟩
  | (false, true) => ⟨(((v.1 - 1, v.2), false), true), by
      simp [TNLean.Network.DependentBondNetwork.endpointVertex, torusLabelledBondHead]⟩
  | (true, false) => ⟨(((v.1, v.2 - 1), true), false), by
      simp [TNLean.Network.DependentBondNetwork.endpointVertex, torusLabelledBondTail]⟩
  | (true, true) => ⟨((v, true), true), rfl⟩

/-- Actual native incidence fibers have exactly the four direction/polarity choices. -/
def torusIncidentEndpointEquiv (v : TorusVertex width height) :
    TNLean.Network.DependentBondNetwork.IncidentEndpoint torusLabelledBondTail
        torusLabelledBondHead v ≃
      Bool × Bool where
  toFun p := (p.1.1.2, p.1.2)
  invFun := torusIncidentEndpoint v
  left_inv p := by
    rcases p with ⟨⟨⟨w, d⟩, b⟩, hp⟩
    cases d <;> cases b
    all_goals
      simp only [TNLean.Network.DependentBondNetwork.endpointVertex, torusLabelledBondHead,
        torusLabelledBondTail, Bool.false_eq_true, ↓reduceIte] at hp
      subst v
      apply Subtype.ext
      simp [torusIncidentEndpoint, TNLean.Network.DependentBondNetwork.endpointVertex,
        torusLabelledBondHead, torusLabelledBondTail]
  right_inv z := by rcases z with ⟨d, b⟩; cases d <;> cases b <;> rfl

/-- Every local tensor has four distinct incident endpoint indices. -/
theorem card_torusIncidentEndpoint (v : TorusVertex width height) :
    Fintype.card (TNLean.Network.DependentBondNetwork.IncidentEndpoint
      torusLabelledBondTail torusLabelledBondHead v) = 4 := by
  rw [Fintype.card_congr (torusIncidentEndpointEquiv v)]
  decide

/-- The actual source cut boundary consists of eight distinct endpoint incidences. -/
theorem card_torusCutEndpoint_two (c r : ZMod 2) :
    Fintype.card (TNLean.Network.DependentBondNetwork.CutEndpoint (torusSeamCutBonds c r)) = 8 := by
  simp [TNLean.Network.DependentBondNetwork.CutEndpoint, card_torusSeamCutBonds_two]

section GroupLabels
variable {G : Type*} [Group G]

/-- The standard commuting closure labels in the single edge-indexed model. -/
def torusLabelledClosure (g h : G) (e : TorusLabelledBond width height) : G :=
  if e.2 then if e.1.2 + 1 = 0 then g else 1
  else if e.1.1 + 1 = 0 then h else 1

/-- The same closure labels placed on any chosen pair of seams. -/
def torusLabelledClosureAt (g h : G) (c : ZMod width) (r : ZMod height)
    (e : TorusLabelledBond width height) : G :=
  if e.2 then if e.1.2 + 1 = r then g else 1
  else if e.1.1 + 1 = c then h else 1

/-- Shifted closure labels are identity on all bonds outside the selected cut. -/
theorem torusLabelledClosureAt_eq_one_of_not_mem
    (g h : G) (c : ZMod width) (r : ZMod height)
    (e : TorusLabelledBond width height) (he : e ∉ torusSeamCutBonds c r) :
    torusLabelledClosureAt g h c r e = 1 := by
  rcases e with ⟨v, b⟩
  cases b <;> simp_all [torusLabelledClosureAt]

end GroupLabels

end TNLean.PEPS
