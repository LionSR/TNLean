import TNLean.PEPS.Defs
import Mathlib.Logic.Equiv.Prod
import Mathlib.Combinatorics.SimpleGraph.Maps

/-!
# Fine bond labels grouped by quotient edges

A block assignment determines a simple quotient graph. The virtual label of a
quotient edge is a dependent tuple indexed by every fine edge over that edge.
-/

open ManyBody (Edge)

namespace TNLean.PEPS.PartitionBonds

variable {V B : Type*} [LinearOrder V] [LinearOrder B] {G : SimpleGraph V}
variable (block : V → B)

/-- Fine edges with endpoints in distinct blocks. -/
abbrev Crossing := {e : Edge G // block e.1.1 ≠ block e.1.2}

/-- Fine edges wholly inside a single block. -/
abbrev Internal := {e : Edge G // block e.1.1 = block e.1.2}

/-- The coarse edge seen by a crossing fine edge, sorted using the order on blocks. -/
def project (e : Crossing (G := G) block) : Edge (G.map block) :=
  Edge.ofAdj (SimpleGraph.map_adj_apply' e.1.2.2 e.2)

/-- Every edge of the simple quotient has at least one original fine bond. -/
theorem project_surjective : Function.Surjective (project (G := G) block) := by
  intro q
  obtain ⟨_, u, v, huv, hu, hv⟩ := (SimpleGraph.map_adj' block G _ _).mp q.2.2
  let e := Edge.ofAdj huv
  have ends : (block e.1.1 = q.1.1 ∧ block e.1.2 = q.1.2) ∨
      (block e.1.1 = q.1.2 ∧ block e.1.2 = q.1.1) := by
    rcases Edge.ofAdj_endpoints huv with ⟨h, h'⟩ | ⟨h, h'⟩
    · exact .inl ⟨(congrArg block h).trans hu, (congrArg block h').trans hv⟩
    · exact .inr ⟨(congrArg block h).trans hv, (congrArg block h').trans hu⟩
  have cross : block e.1.1 ≠ block e.1.2 := by
    rcases ends with ⟨h, h'⟩ | ⟨h, h'⟩ <;> rw [h, h']
    · exact q.2.1.ne
    · exact q.2.1.ne.symm
  exact ⟨⟨e, cross⟩, Edge.ofAdj_eq_of_endpoints _ q ends⟩

/-- Parallel fine bonds remain distinct members of the same coarse-edge fiber. -/
abbrev Fiber (q : Edge (G.map block)) := {e : Crossing (G := G) block // project block e = q}

/-- Group crossing labels by their coarse edge; evaluation at the original fine edge
is the inverse. The label type may depend on the individual fine edge. -/
def crossingLabels (L : Edge G → Type*) :
    ((e : Crossing block) → L e.1) ≃
      ((q : Edge (G.map block)) → (e : Fiber block q) → L e.1.1) where
  toFun x _ e := x e.1
  invFun y e := y (project block e) ⟨e, rfl⟩
  left_inv _ := rfl
  right_inv y := by
    funext q e
    obtain ⟨e, rfl⟩ := e
    rfl

/-- Split a global virtual configuration into internal fine labels and bundled
crossing labels. Specialize the family to `Fin (A.bondDim e)` for a PEPS tensor. -/
def globalLabels (L : Edge G → Type*) :
    ((e : Edge G) → L e) ≃ ((e : Internal block) → L e.1) ×
      ((q : Edge (G.map block)) → (e : Fiber block q) → L e.1.1) :=
  (Equiv.piEquivPiSubtypeProd (fun e : Edge G => block e.1.1 = block e.1.2) L).trans
    (Equiv.prodCongr (Equiv.refl _) (crossingLabels block L))

end TNLean.PEPS.PartitionBonds
