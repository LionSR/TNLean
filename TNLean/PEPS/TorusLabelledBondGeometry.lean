/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.TorusBondFlatConnection
import TNLean.PEPS.TorusBondClosureSeamMovement
import TNLean.PEPS.DependentBondCut

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
    DependentBondNetwork.IncidentEndpoint torusLabelledBondTail torusLabelledBondHead v :=
  match z with
  | (false, false) => ⟨((v, false), false), rfl⟩
  | (false, true) => ⟨(((v.1 - 1, v.2), false), true), by
      simp [DependentBondNetwork.endpointVertex, torusLabelledBondHead]⟩
  | (true, false) => ⟨(((v.1, v.2 - 1), true), false), by
      simp [DependentBondNetwork.endpointVertex, torusLabelledBondTail]⟩
  | (true, true) => ⟨((v, true), true), rfl⟩

/-- Actual native incidence fibers have exactly the four direction/polarity choices. -/
def torusIncidentEndpointEquiv (v : TorusVertex width height) :
    DependentBondNetwork.IncidentEndpoint torusLabelledBondTail torusLabelledBondHead v ≃
      Bool × Bool where
  toFun p := (p.1.1.2, p.1.2)
  invFun := torusIncidentEndpoint v
  left_inv p := by
    rcases p with ⟨⟨⟨w, d⟩, b⟩, hp⟩
    cases d <;> cases b
    all_goals
      simp only [DependentBondNetwork.endpointVertex, torusLabelledBondHead,
        torusLabelledBondTail, Bool.false_eq_true, ↓reduceIte] at hp
      subst v
      apply Subtype.ext
      simp [torusIncidentEndpoint, DependentBondNetwork.endpointVertex,
        torusLabelledBondHead, torusLabelledBondTail]
  right_inv z := by rcases z with ⟨d, b⟩; cases d <;> cases b <;> rfl

/-- Every local tensor has four distinct incident endpoint indices. -/
theorem card_torusIncidentEndpoint (v : TorusVertex width height) :
    Fintype.card (DependentBondNetwork.IncidentEndpoint
      torusLabelledBondTail torusLabelledBondHead v) = 4 := by
  rw [Fintype.card_congr (torusIncidentEndpointEquiv v)]
  decide

/-- The actual source cut boundary consists of eight distinct endpoint incidences. -/
theorem card_torusCutEndpoint_two (c r : ZMod 2) :
    Fintype.card (DependentBondNetwork.CutEndpoint (torusSeamCutBonds c r)) = 8 := by
  simp [DependentBondNetwork.CutEndpoint, card_torusSeamCutBonds_two]

section GroupLabels
variable {G : Type*} [Group G]

/-- Horizontal and vertical parts of a single edge-indexed label assignment. -/
def torusLabelledBondPair (p : TorusLabelledBond width height → G) :
    TorusBondLabels width height G :=
  (fun v ↦ p (v, false), fun v ↦ p (v, true))

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

/-- Commuting labels may be moved to any edge cut before choosing the dimensions
or representations of the actual bonds. -/
theorem exists_torusLabelledClosureGauge (g h : G) (hgh : Commute g h)
    (c : ZMod width) (r : ZMod height) :
    ∃ q : TorusVertex width height → G, ∀ e,
      q (torusLabelledBondHead e) * torusLabelledClosure g h e *
          (q (torusLabelledBondTail e))⁻¹ = torusLabelledClosureAt g h c r e := by
  obtain ⟨q, hq⟩ := exists_torusBondGauge_eq_closureAt g h hgh c r
  refine ⟨q, ?_⟩
  rintro ⟨v, b⟩
  cases b
  · have hv := congrFun (congrArg Prod.fst hq) v
    simpa only [torusBondGauge, torusBondClosureLabels, torusBondClosureLabelsAt,
      torusLabelledBondHead, torusLabelledBondTail, torusLabelledClosure,
      torusLabelledClosureAt, Bool.false_eq_true, ↓reduceIte] using hv
  · have hv := congrFun (congrArg Prod.snd hq) v
    simpa only [torusBondGauge, torusBondClosureLabels, torusBondClosureLabelsAt,
      torusLabelledBondHead, torusLabelledBondTail, torusLabelledClosure,
      torusLabelledClosureAt, ↓reduceIte] using hv

/-- The native labelled-torus classification expressed directly on edge IDs.
It is independent of the dimension of the representation on any edge. -/
theorem exists_torusLabelledBondGauge_eq_closure
    (p : TorusLabelledBond width height → G)
    (hp : IsTorusBondFlat (torusLabelledBondPair p)) :
    ∃ (q : TorusVertex width height → G) (g h : G), Commute g h ∧
      ∀ e, q (torusLabelledBondHead e) * p e * (q (torusLabelledBondTail e))⁻¹ =
        torusLabelledClosure g h e := by
  obtain ⟨q, g, h, hgh, heq⟩ := exists_torusBondGauge_eq_closure (torusLabelledBondPair p) hp
  refine ⟨q, g, h, hgh, ?_⟩
  rintro ⟨v, b⟩
  cases b
  · have hv := congrFun (congrArg Prod.fst heq) v
    simpa only [torusBondGauge, torusLabelledBondPair, torusBondClosureLabels,
      torusLabelledBondHead, torusLabelledBondTail, torusLabelledClosure,
      Bool.false_eq_true, ↓reduceIte] using hv
  · have hv := congrFun (congrArg Prod.snd heq) v
    simpa only [torusBondGauge, torusLabelledBondPair, torusBondClosureLabels,
      torusLabelledBondHead, torusLabelledBondTail, torusLabelledClosure, ↓reduceIte] using hv

/-- Relative labels on the four uncut edges satisfy their native plaquette equation. -/
theorem torusPlaquette_flat_of_uncut_relative
    (p : TorusLabelledBond 2 2 → G) (q : TorusVertex 2 2 → G) (c r : ZMod 2)
    (hp : ∀ e, e ∉ torusSeamCutBonds c r →
      p e = q (torusLabelledBondHead e) * (q (torusLabelledBondTail e))⁻¹) :
    (torusLabelledBondPair p).2 (c + 1, r) * (torusLabelledBondPair p).1 (c, r + 1) =
      (torusLabelledBondPair p).1 (c, r) * (torusLabelledBondPair p).2 (c, r) := by
  change p ((c + 1, r), true) * p ((c, r + 1), false) =
    p ((c, r), false) * p ((c, r), true)
  rw [hp ((c + 1, r), true) (by simp), hp ((c, r + 1), false) (by simp),
    hp ((c, r), false) (by simp), hp ((c, r), true) (by simp)]
  simp only [torusLabelledBondHead, torusLabelledBondTail, Bool.false_eq_true,
    ↓reduceIte, mul_assoc, inv_mul_cancel_left]

end GroupLabels

end TNLean.PEPS
