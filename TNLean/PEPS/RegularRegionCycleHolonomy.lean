/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.RegularWalkHolonomy
import TNLean.PEPS.RegularRegionTreeGauge
import Mathlib.GroupTheory.FreeGroup.Basic

/-!
# Actual walk words in the residual region cycles

A chosen spanning tree identifies the native internal edges outside the tree.
Assign identity operators to tree edges and free generators to the other edges.
The reverse-ordered holonomy of an actual induced-region walk is then a concrete
free-group word in those generators. Evaluation at any residual cycle tuple
recovers its actual holonomy. In particular the original bond assignment, after
the normalized tree gauge, is evaluation at its native cycle residuals.

Source: Schuch, Cirac, and Pérez-García, arXiv:1001.3807, seam deformation in
`eq:2d:move-strings`, local source lines 1622–1647, and accessible complement
cycle coordinates, lines 1935–1990. No geometric boundary-word relation or
factorization of a tensor is assumed.

## References

- [arXiv:1001.3807](https://arxiv.org/abs/1001.3807) -- N. Schuch, J. I. Cirac,
  D. Pérez-García, *PEPS as ground states: degeneracy and topology*
-/

namespace TNLean.PEPS

variable {V : Type*} [LinearOrder V] {Γ : SimpleGraph V}
variable {G : Type*} [Group G]

/-- The original native internal edges outside a chosen region tree. -/
abbrev RegionCycleEdge (R : Finset V) (T : SimpleGraph {v : V // v ∈ R}) :=
  {e : {e : Edge Γ // e.1.1 ∈ R ∧ e.1.2 ∈ R} //
    ¬ T.Adj ⟨e.1.1.1, e.2.1⟩ ⟨e.1.1.2, e.2.2⟩}

/-- Restriction of the original native operators to the edges of the induced
region graph, using the existing internal-edge equivalence. -/
def regularRegionInternalOperators (R : Finset V) (u : Edge Γ → G) :
    Edge (Γ.induce (R : Set V)) → G :=
  fun e => u (inducedRegionEdgeEquiv R e).1

/-- A cycle tuple supplies the operators outside the tree, while each tree edge
has identity operator. The edges are those of the actual induced region graph. -/
def regularRegionCycleOperators (R : Finset V) (T : SimpleGraph {v : V // v ∈ R})
    [DecidableRel T.Adj] (z : RegionCycleEdge (Γ := Γ) R T → G) :
    Edge (Γ.induce (R : Set V)) → G :=
  fun e => if he : T.Adj e.1.1 e.1.2 then 1 else
    z ⟨inducedRegionEdgeEquiv R e, he⟩

/-- The group word obtained from the actual walk, with one free generator per
native non-tree edge. Source: SCP10, complement cycle records, lines 1935–1990. -/
def regularRegionCycleWord (R : Finset V) (T : SimpleGraph {v : V // v ∈ R})
    [DecidableRel T.Adj] {v w : {v : V // v ∈ R}}
    (p : (Γ.induce (R : Set V)).Walk v w) : FreeGroup (RegionCycleEdge (Γ := Γ) R T) :=
  regularWalkHolonomy (regularRegionCycleOperators R T FreeGroup.of) p

/-- Concatenation of actual region walks concatenates their cycle words in
reverse traversal order. -/
theorem regularRegionCycleWord_append (R : Finset V)
    (T : SimpleGraph {v : V // v ∈ R}) [DecidableRel T.Adj]
    {v w t : {v : V // v ∈ R}} (p : (Γ.induce (R : Set V)).Walk v w)
    (q : (Γ.induce (R : Set V)).Walk w t) :
    regularRegionCycleWord R T (p.append q) =
      regularRegionCycleWord R T q * regularRegionCycleWord R T p :=
  regularWalkHolonomy_append _ p q

/-- Reversing the actual region walk inverts its cycle word. -/
theorem regularRegionCycleWord_reverse (R : Finset V)
    (T : SimpleGraph {v : V // v ∈ R}) [DecidableRel T.Adj]
    {v w : {v : V // v ∈ R}} (p : (Γ.induce (R : Set V)).Walk v w) :
    regularRegionCycleWord R T p.reverse = (regularRegionCycleWord R T p)⁻¹ :=
  regularWalkHolonomy_reverse _ p

/-- Group homomorphisms commute with the actual ordered walk transport. -/
private theorem regularWalkHolonomy_map {H : Type*} [Group H] (f : G →* H)
    (u : Edge Γ → G) {v w : V} (p : Γ.Walk v w) :
    f (regularWalkHolonomy u p) = regularWalkHolonomy (fun e => f (u e)) p := by
  have hstep {v w : V} (h : Γ.Adj v w) :
      f (regularDirectedTransport u h) = regularDirectedTransport (fun e => f (u e)) h := by
    unfold regularDirectedTransport
    split_ifs <;> simp only [map_inv]
  induction p with
  | nil => simp only [regularWalkHolonomy_nil, map_one]
  | cons h p ih => rw [regularWalkHolonomy_cons, map_mul, ih, hstep, regularWalkHolonomy_cons]

/-- Evaluating the constructed word at a cycle tuple gives its actual residual
holonomy. Source: SCP10, accessible cycle coordinates, lines 1935–1990. -/
theorem regularRegionCycleWord_eval (R : Finset V) (T : SimpleGraph {v : V // v ∈ R})
    [DecidableRel T.Adj] (z : RegionCycleEdge (Γ := Γ) R T → G)
    {v w : {v : V // v ∈ R}} (p : (Γ.induce (R : Set V)).Walk v w) :
    FreeGroup.lift z (regularRegionCycleWord R T p) =
      regularWalkHolonomy (regularRegionCycleOperators R T z) p := by
  unfold regularRegionCycleWord
  rw [regularWalkHolonomy_map]
  congr 1
  funext e
  unfold regularRegionCycleOperators
  split_ifs <;> simp only [map_one, FreeGroup.lift_apply_of]

/-- Simultaneous conjugation of a cycle tuple conjugates the evaluated actual
walk word. Source: SCP10, conjugated accessible cycle labels, lines 1935–1990. -/
theorem regularRegionCycleWord_eval_conj (R : Finset V)
    (T : SimpleGraph {v : V // v ∈ R}) [DecidableRel T.Adj]
    (z : RegionCycleEdge (Γ := Γ) R T → G) (x : G)
    {v w : {v : V // v ∈ R}} (p : (Γ.induce (R : Set V)).Walk v w) :
    FreeGroup.lift (fun e => x * z e * x⁻¹) (regularRegionCycleWord R T p) =
      x * FreeGroup.lift z (regularRegionCycleWord R T p) * x⁻¹ := by
  rw [regularRegionCycleWord_eval, regularRegionCycleWord_eval]
  have hop : regularRegionCycleOperators R T (fun e => x * z e * x⁻¹) =
      regularVertexGaugeOperators (fun _ => x⁻¹) (regularRegionCycleOperators R T z) := by
    funext e
    unfold regularRegionCycleOperators regularVertexGaugeOperators
    split_ifs with he <;> simp [he]
  rw [hop, regularWalkHolonomy_gauge]
  simp only [inv_inv]

variable [Fintype G]

/-- The normalized tree gauge turns the original native edge assignment into
identity tree operators and its existing cycle residuals. Source: SCP10,
regular blocking and complement cycle records, lines 1765–1920 and 1935–1990. -/
theorem regularRegionCycleOperators_treeGauge (R : Finset V)
    (T : SimpleGraph {v : V // v ∈ R}) [DecidableRel T.Adj]
    (hT : T ≤ Γ.induce (R : Set V)) (htree : T.IsTree) (o : {v // v ∈ R})
    (u : Edge Γ → G) :
    regularVertexGaugeOperators (regularRegionTreeGauge R T hT htree o u).1
        (regularRegionInternalOperators R u) =
      regularRegionCycleOperators R T (regularRegionTreeCycleResidual R T hT htree o u) := by
  funext e
  unfold regularRegionCycleOperators
  split_ifs with he
  · exact regularRegionGaugeResidual_eq_one_of_tree R T hT htree o u
      (inducedRegionEdgeEquiv R e) he
  · rfl

/-- Evaluation of an actual cycle word equals the tree-gauged original walk
holonomy, with only its endpoint gauges remaining. Source: SCP10,
seam deformation and complement cycle records, lines 1622–1647 and 1935–1990. -/
theorem regularRegionCycleWord_eval_treeResidual (R : Finset V)
    (T : SimpleGraph {v : V // v ∈ R}) [DecidableRel T.Adj]
    (hT : T ≤ Γ.induce (R : Set V)) (htree : T.IsTree) (o : {v // v ∈ R})
    (u : Edge Γ → G) {v w : {v : V // v ∈ R}}
    (p : (Γ.induce (R : Set V)).Walk v w) :
    FreeGroup.lift (regularRegionTreeCycleResidual R T hT htree o u)
        (regularRegionCycleWord R T p) =
      ((regularRegionTreeGauge R T hT htree o u).1 w)⁻¹ *
        regularWalkHolonomy (regularRegionInternalOperators R u) p *
          (regularRegionTreeGauge R T hT htree o u).1 v := by
  rw [regularRegionCycleWord_eval, ← regularRegionCycleOperators_treeGauge,
    regularWalkHolonomy_gauge]

/-- At the normalized root, an actual closed-walk holonomy is exactly the
evaluation of its constructed cycle word. Source: SCP10, accessible complement
cycle records, lines 1935–1990. -/
theorem regularRegionCycleWord_eval_rootLoop (R : Finset V)
    (T : SimpleGraph {v : V // v ∈ R}) [DecidableRel T.Adj]
    (hT : T ≤ Γ.induce (R : Set V)) (htree : T.IsTree) (o : {v // v ∈ R})
    (u : Edge Γ → G) (p : (Γ.induce (R : Set V)).Walk o o) :
    FreeGroup.lift (regularRegionTreeCycleResidual R T hT htree o u)
        (regularRegionCycleWord R T p) =
      regularWalkHolonomy (regularRegionInternalOperators R u) p := by
  rw [regularRegionCycleWord_eval_treeResidual, regularRegionTreeGauge_root,
    inv_one, one_mul, mul_one]

/-- The original holonomy is recovered from the evaluated cycle word and the
endpoint tree gauges. Source: SCP10, lines 1622–1647 and 1935–1990. -/
theorem regularWalkHolonomy_eq_cycleWord_eval (R : Finset V)
    (T : SimpleGraph {v : V // v ∈ R}) [DecidableRel T.Adj]
    (hT : T ≤ Γ.induce (R : Set V)) (htree : T.IsTree) (o : {v // v ∈ R})
    (u : Edge Γ → G) {v w : {v : V // v ∈ R}}
    (p : (Γ.induce (R : Set V)).Walk v w) :
    regularWalkHolonomy (regularRegionInternalOperators R u) p =
      (regularRegionTreeGauge R T hT htree o u).1 w *
        FreeGroup.lift (regularRegionTreeCycleResidual R T hT htree o u)
          (regularRegionCycleWord R T p) *
        ((regularRegionTreeGauge R T hT htree o u).1 v)⁻¹ := by
  rw [regularRegionCycleWord_eval_treeResidual]
  group

end TNLean.PEPS
