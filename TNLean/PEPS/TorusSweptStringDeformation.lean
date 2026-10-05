/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.RegularSweptPatchDeformation
import TNLean.PEPS.RegularTorusCut

/-!
# Literal swept-string assignments on a translated torus patch

The four columns and three displayed rows use a lower-left reference vertex.
The first sweep contains the two central vertices of the middle row; the second
adds the two central vertices of the bottom row. The initial second string is
continued one row below the displayed patch so that its partner remains outside
the swept vertices. The assignments specify directed rightward and upward
transports first, and invert the ordered edge coefficient at a periodic seam.

Source: SCP10, arXiv:1001.3807, lines 2361–2386 and the figure
`fluxon-braiding-virtuallevel`.

**Scope restriction (finite torus gauge presentations):** These auxiliary
actual contraction identities use width at least five and height at least four.
The four partner endpoint loops and the prescribed physical braiding route are
not identified here. Crossing coefficients change under the sweep; no
boundary-preserving action is asserted. See
`docs/paper-gaps/rmp_peps_quantum_double_g_isometry.tex`.
-/

namespace TNLean.PEPS
variable {width height : ℕ} [NeZero width] [NeZero height]
variable [Fact (4 < width)] [Fact (3 < height)]
local instance sweptStringWidthTwo : Fact (2 < width) :=
  ⟨by have := Fact.out (p := 4 < width); omega⟩
local instance sweptStringHeightTwo : Fact (2 < height) :=
  ⟨by have := Fact.out (p := 3 < height); omega⟩
local instance sweptStringWidthOne : Fact (1 < width) :=
  ⟨by have := Fact.out (p := 4 < width); omega⟩
local instance sweptStringHeightOne : Fact (1 < height) :=
  ⟨by have := Fact.out (p := 3 < height); omega⟩
local notation "X" => TorusVertex width height
local notation "Γₜ" => torusGraph width height
variable {G : Type*} [Group G]

/-- The actual twelve displayed vertices. Source: SCP10, lines 2361–2386. -/
def torusSweptStringPatch (v : X) : Finset X :=
  {v.1, v.1 + 1, v.1 + 2, v.1 + 3} ×ˢ {v.2, v.2 + 1, v.2 + 2}

/-- The central middle-row sweep, optionally including the central bottom row.
Source: SCP10, successive panels of the virtual figure, lines 2361–2386. -/
def torusSweptStringVertices (v : X) (second : Bool) : Finset X :=
  {v.1 + 1, v.1 + 2} ×ˢ (if second then {v.2, v.2 + 1} else {v.2 + 1})

/-- The original rightward transport on the second string, including its
continuation below the displayed patch. Source: SCP10, lines 2361–2386. -/
def torusSweptStringInitialRight (v : X) (h : G) (p : X) : G :=
  if p.1 = v.1 + 1 ∧ p.2 ∈ ({v.2 - 1, v.2, v.2 + 1} : Finset (ZMod height))
  then h⁻¹ else 1

/-- The original upward transports across the first string.
Source: SCP10, lines 2361–2386. -/
def torusSweptStringInitialUp (v : X) (g : G) (p : X) : G :=
  if p.1 ∈ ({v.1, v.1 + 1, v.1 + 2, v.1 + 3} : Finset (ZMod width)) ∧ p.2 = v.2 + 1
  then g else 1

/-- The literal initial ordered coefficients, with the seam orientation derived
from the native coordinate order. Source: SCP10, lines 2361–2386. -/
noncomputable def torusSweptStringInitialOperators (v : X) (g h : G) : Edge Γₜ → G :=
  fun e => match torusEdgeEquiv.symm e with
  | .inl p => if p.1.val < (p.1 + 1).val then torusSweptStringInitialRight v h p
    else (torusSweptStringInitialRight v h p)⁻¹
  | .inr p => if p.2.val < (p.2 + 1).val then torusSweptStringInitialUp v g p
    else (torusSweptStringInitialUp v g p)⁻¹

/-- The first and final literal assignments after sweeping the selected vertices.
Source: SCP10, successive panels in lines 2361–2386. -/
noncomputable def torusSweptStringOperators (v : X) (second : Bool) (g h : G) : Edge Γₜ → G :=
  regularSweptPatchOperators (torusSweptStringVertices v second) g
    (torusSweptStringInitialOperators v g h)

omit [Fact (4 < width)] [Fact (3 < height)] in
private theorem right_lt (p : X) : p < (p.1 + 1, p.2) ↔ p.1.val < (p.1 + 1).val := by
  change toLex (p.1.val, p.2.val) < toLex ((p.1 + 1).val, p.2.val) ↔ _
  simp [Prod.Lex.toLex_lt_toLex]

omit [Fact (4 < width)] [Fact (3 < height)] in
private theorem up_lt (p : X) : p < (p.1, p.2 + 1) ↔ p.2.val < (p.2 + 1).val := by
  change toLex (p.1.val, p.2.val) < toLex (p.1.val, (p.2 + 1).val) ↔ _
  simp [Prod.Lex.toLex_lt_toLex]

/-- The initial rightward table is independent of whether the edge crosses a seam.
Source: SCP10, lines 2361–2386. -/
theorem torusSweptStringInitialOperators_right_transport (v p : X) (g h : G) :
    regularDirectedTransport (torusSweptStringInitialOperators v g h)
      (torusGraph_adj_right p.1 p.2) = torusSweptStringInitialRight v h p := by
  have he : torusEdgeEquiv.symm (Edge.ofAdj (torusGraph_adj_right p.1 p.2)) = Sum.inl p :=
    torusEdgeEquiv.symm_apply_apply (Sum.inl p)
  simp only [regularDirectedTransport, right_lt, torusSweptStringInitialOperators, he]
  split_ifs <;> simp

/-- The initial upward table is independent of whether the edge crosses a seam.
Source: SCP10, lines 2361–2386. -/
theorem torusSweptStringInitialOperators_up_transport (v p : X) (g h : G) :
    regularDirectedTransport (torusSweptStringInitialOperators v g h)
      (torusGraph_adj_up p.1 p.2) = torusSweptStringInitialUp v g p := by
  have he : torusEdgeEquiv.symm (Edge.ofAdj (torusGraph_adj_up p.1 p.2)) = Sum.inr p :=
    torusEdgeEquiv.symm_apply_apply (Sum.inr p)
  simp only [regularDirectedTransport, up_lt, torusSweptStringInitialOperators, he]
  split_ifs <;> simp

/-- The complete directed rightward table after either sweep includes all
entering, leaving, internal and disjoint edges. Source: SCP10, lines 2361–2386. -/
theorem torusSweptStringOperators_right_transport (v p : X) (second : Bool) (g h : G) :
    let S := torusSweptStringVertices v second
    let D := torusSweptStringInitialRight v h p
    regularDirectedTransport (torusSweptStringOperators v second g h)
      (torusGraph_adj_right p.1 p.2) =
      if (p.1 + 1, p.2) ∈ S then
        if p ∈ S then g * D * g⁻¹ else g * D
      else if p ∈ S then D * g⁻¹ else D := by
  dsimp only
  unfold torusSweptStringOperators
  rw [regularDirectedTransport_regularSweptPatchOperators,
    torusSweptStringInitialOperators_right_transport]

/-- The complete directed upward table after either sweep includes all crossing
edges of the displayed patch. Source: SCP10, lines 2361–2386. -/
theorem torusSweptStringOperators_up_transport (v p : X) (second : Bool) (g h : G) :
    let S := torusSweptStringVertices v second
    let D := torusSweptStringInitialUp v g p
    regularDirectedTransport (torusSweptStringOperators v second g h)
      (torusGraph_adj_up p.1 p.2) =
      if (p.1, p.2 + 1) ∈ S then
        if p ∈ S then g * D * g⁻¹ else g * D
      else if p ∈ S then D * g⁻¹ else D := by
  dsimp only
  unfold torusSweptStringOperators
  rw [regularDirectedTransport_regularSweptPatchOperators,
    torusSweptStringInitialOperators_up_transport]

omit [NeZero width] [NeZero height] [Fact (4 < width)] [Fact (3 < height)] in
private theorem operator_eq_directed {Y : Type*} [LinearOrder Y] {Λ : SimpleGraph Y}
    (u : Edge Λ → G) {a b : Y} (hab : Λ.Adj a b) :
    u (Edge.ofAdj hab) =
      if a < b then regularDirectedTransport u hab
      else (regularDirectedTransport u hab)⁻¹ := by
  by_cases h : a < b <;> simp [regularDirectedTransport, h]

/-- The ordered coefficient is the directed rightward table, inverted exactly
at the horizontal seam. Source: SCP10, lines 2361–2386. -/
theorem torusSweptStringOperators_right_ordered (v p : X) (second : Bool) (g h : G) :
    let S := torusSweptStringVertices v second
    let D := torusSweptStringInitialRight v h p
    let T := if (p.1 + 1, p.2) ∈ S then
      if p ∈ S then g * D * g⁻¹ else g * D
      else if p ∈ S then D * g⁻¹ else D
    torusSweptStringOperators v second g h (torusRightEdge p) =
      if p.1.val < (p.1 + 1).val then T else T⁻¹ := by
  dsimp only
  simp only [torusRightEdge]
  rw [operator_eq_directed (torusSweptStringOperators v second g h)
    (torusGraph_adj_right p.1 p.2)]
  simp only [right_lt, torusSweptStringOperators_right_transport]

/-- The ordered coefficient is the directed upward table, inverted exactly
at the vertical seam. Source: SCP10, lines 2361–2386. -/
theorem torusSweptStringOperators_up_ordered (v p : X) (second : Bool) (g h : G) :
    let S := torusSweptStringVertices v second
    let D := torusSweptStringInitialUp v g p
    let T := if (p.1, p.2 + 1) ∈ S then
      if p ∈ S then g * D * g⁻¹ else g * D
      else if p ∈ S then D * g⁻¹ else D
    torusSweptStringOperators v second g h (torusUpEdge p) =
      if p.2.val < (p.2 + 1).val then T else T⁻¹ := by
  dsimp only
  simp only [torusUpEdge]
  rw [operator_eq_directed (torusSweptStringOperators v second g h)
    (torusGraph_adj_up p.1 p.2)]
  simp only [up_lt, torusSweptStringOperators_up_transport]


/-- The second sweep adds precisely the two central bottom vertices.
Source: SCP10, final virtual panel in lines 2361–2386. -/
def torusSweptStringBottomVertices (v : X) : Finset X :=
  {v.1 + 1, v.1 + 2} ×ˢ {v.2}

omit [NeZero width] [NeZero height] [Fact (4 < width)] [Fact (3 < height)] in
private theorem sweep_disjoint {Y : Type*} [LinearOrder Y] {Λ : SimpleGraph Y}
    (R S : Finset Y) (hd : Disjoint R S) (g : G) (u : Edge Λ → G) :
    regularSweptPatchOperators S g (regularSweptPatchOperators R g u) =
      regularSweptPatchOperators (R ∪ S) g u := by
  funext e
  have hh : ¬ (e.1.2 ∈ R ∧ e.1.2 ∈ S) :=
    fun h => (Finset.disjoint_left.mp hd) h.1 h.2
  have ht : ¬ (e.1.1 ∈ R ∧ e.1.1 ∈ S) :=
    fun h => (Finset.disjoint_left.mp hd) h.1 h.2
  by_cases hrh : e.1.2 ∈ R <;> by_cases hsh : e.1.2 ∈ S <;>
    by_cases hrt : e.1.1 ∈ R <;> by_cases hst : e.1.1 ∈ S <;>
    simp_all [regularSweptPatchOperators, mul_assoc]

/-- The full sweep is the composition of the middle-row and bottom-row sweeps.
Source: SCP10, the two successive virtual panels in lines 2361–2386. -/
theorem torusSweptStringOperators_second_eq_sweep (v : X) (g h : G) :
    torusSweptStringOperators v true g h =
      regularSweptPatchOperators (torusSweptStringBottomVertices v) g
        (torusSweptStringOperators v false g h) := by
  have hd : Disjoint (torusSweptStringVertices v false) (torusSweptStringBottomVertices v) := by
    apply Finset.disjoint_left.mpr
    intro p hp hq
    have hp' : p.2 = v.2 + 1 := by
      simpa [torusSweptStringVertices] using (Finset.mem_product.mp hp).2
    have hq' : p.2 = v.2 := by
      simpa [torusSweptStringBottomVertices] using (Finset.mem_product.mp hq).2
    have hn : v.2 + 1 ≠ v.2 := by simp
    exact hn (hp'.symm.trans hq')
  have hs : torusSweptStringVertices v true =
      torusSweptStringVertices v false ∪ torusSweptStringBottomVertices v := by
    ext p
    simp [torusSweptStringVertices, torusSweptStringBottomVertices, Prod.ext_iff]
    tauto
  unfold torusSweptStringOperators
  rw [hs]
  exact (sweep_disjoint _ _ hd g _).symm

variable [Fintype G]

/-- Both displayed sweeps preserve the actual closed coefficient vector from
local regular invariance alone. Source: SCP10, lines 2361–2386. -/
theorem stateCoeff_torusSweptStringOperators {d : ℕ}
    (a : (p : X) → (IncidentEdge Γₜ p → G) → Fin d → ℂ)
    (ha : ∀ x p η s, a p (fun e => x * η e) s = a p η s)
    (v : X) (second : Bool) (g h : G) :
    stateCoeff (groupBondTensor (regularTwistedSite a
      (torusSweptStringInitialOperators v g h))) =
    stateCoeff (groupBondTensor (regularTwistedSite a
      (torusSweptStringOperators v second g h))) :=
  stateCoeff_regularSweptPatchOperators a ha (torusSweptStringVertices v second) g _

/-- The two successive panels have equal actual closed coefficient vectors.
Crossing bonds are included; no boundary-column equality is asserted.
Source: SCP10, lines 2361–2386. -/
theorem stateCoeff_torusSweptStringOperators_first_eq_second {d : ℕ}
    (a : (p : X) → (IncidentEdge Γₜ p → G) → Fin d → ℂ)
    (ha : ∀ x p η s, a p (fun e => x * η e) s = a p η s)
    (v : X) (g h : G) :
    stateCoeff (groupBondTensor (regularTwistedSite a
      (torusSweptStringOperators v false g h))) =
    stateCoeff (groupBondTensor (regularTwistedSite a
      (torusSweptStringOperators v true g h))) :=
  (stateCoeff_torusSweptStringOperators a ha v false g h).symm.trans
    (stateCoeff_torusSweptStringOperators a ha v true g h)

end TNLean.PEPS
