/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Algebra.Group.Defs
import Mathlib.Data.Quot

/-!
# Multiplicative coboundaries on recurrent directed graphs

An edge weight on a directed graph is a vertex coboundary when it is the ratio
of vertex weights at the endpoints of every edge. This file proves that trivial
weight around every closed directed walk is sufficient when every directed edge
admits a directed return walk.

The proof chooses one vertex in each reachability component and defines the
vertex weight by multiplication along a walk from that vertex. Trivial closed
walk weights make this choice independent of the walk.

## Implementation notes

The local `DirectedWalk` is a type-valued walk over an ordinary proposition-
valued relation. This connects directly to relations such as
`MPOTensor.IsSectorEdge` and allows a walk to be eliminated into its weight in
an arbitrary monoid. In contrast, `Relation.ReflTransGen` is proposition-valued
and therefore cannot in general be eliminated into such data, while
`Quiver.Path` would first require replacing the proposition-valued relation by
a quiver of edge types.

`TNLean.Algebra.FiniteCycleCoboundary` treats the complementary special case of
one finite cycle. A future MPDO specialization should prove the correspondence
between `Relation.ReflTransGen` (hence `MPOTensor.SectorReaches`) and
`DirectedWalk`, then apply the closed-walk theorem below to the sector phases.
-/

namespace TNLean.Algebra

variable {V G : Type*} (r : V → V → Prop)

/-- A finite directed walk, including the walk of length zero. -/
inductive DirectedWalk : V → V → Type _
  | nil (a : V) : DirectedWalk a a
  | cons {a b c : V} (hab : r a b) (w : DirectedWalk b c) : DirectedWalk a c

namespace DirectedWalk

/-- Concatenation of directed walks. -/
def append {a b c : V} : DirectedWalk r a b → DirectedWalk r b c → DirectedWalk r a c
  | .nil _, q => q
  | .cons hab p, q => .cons hab (p.append q)

@[simp]
theorem nil_append {a b : V} (w : DirectedWalk r a b) : append r (nil a) w = w := rfl

@[simp]
theorem append_nil {a b : V} (w : DirectedWalk r a b) : append r w (nil b) = w := by
  induction w with
  | nil => rfl
  | cons hab w ih => simp [append, ih]

@[simp]
theorem append_assoc {a b c d : V} (u : DirectedWalk r a b) (v : DirectedWalk r b c)
    (w : DirectedWalk r c d) :
    append r (append r u v) w = append r u (append r v w) := by
  induction u with
  | nil => rfl
  | cons hab u ih => simp [append, ih]

/-- The product of an edge-weight family along a directed walk. -/
def weight (r : V → V → Prop) [Monoid G] (κ : V → V → G)
    {a b : V} : DirectedWalk r a b → G
  | .nil _ => 1
  | @DirectedWalk.cons _ _ a b _ hab w => κ a b * weight r κ w

@[simp]
theorem weight_nil [Monoid G] (κ : V → V → G) (a : V) :
    weight r κ (nil a) = 1 := rfl

@[simp]
theorem weight_cons [Monoid G] (κ : V → V → G) {a b c : V} (hab : r a b)
    (w : DirectedWalk r b c) :
    weight r κ (cons hab w) = κ a b * weight r κ w := rfl

@[simp]
theorem weight_append [Monoid G] (κ : V → V → G) {a b c : V}
    (u : DirectedWalk r a b) (v : DirectedWalk r b c) :
    weight r κ (append r u v) = weight r κ u * weight r κ v := by
  induction u with
  | nil => simp
  | cons hab u ih => simp [append, ih, mul_assoc]

private theorem weight_transport_start [Monoid G] (κ : V → V → G)
    {a a' b : V} (h : a = a') (w : DirectedWalk r a b) :
    weight r κ (h ▸ w) = weight r κ w := by
  cases h
  rfl

/-- Reachability by a finite directed walk. -/
def Reaches (a b : V) : Prop := Nonempty (DirectedWalk r a b)

theorem reaches_refl (a : V) : Reaches r a a := ⟨nil a⟩

theorem reaches_of_edge {a b : V} (hab : r a b) : Reaches r a b :=
  ⟨cons hab (nil b)⟩

theorem Reaches.trans {a b c : V} : Reaches r a b → Reaches r b c → Reaches r a c := by
  rintro ⟨u⟩ ⟨v⟩
  exact ⟨append r u v⟩

/-- If every edge admits a return walk, every walk admits a return walk. -/
theorem reaches_reverse_of_edge_returns
    (hreturn : ∀ {a b : V}, r a b → Reaches r b a) {a b : V}
    (w : DirectedWalk r a b) : Reaches r b a := by
  induction w with
  | nil a => exact reaches_refl r a
  | @cons a b c hab w ih => exact Reaches.trans r ih (hreturn hab)

/-- Reachability is an equivalence relation when every edge admits a return
walk. -/
def reachabilitySetoid (hreturn : ∀ {a b : V}, r a b → Reaches r b a) : Setoid V where
  r := Reaches r
  iseqv := {
    refl := reaches_refl r
    symm := by
      rintro a b ⟨w⟩
      exact reaches_reverse_of_edge_returns r hreturn w
    trans := fun {_ _ _} hab hbc => Reaches.trans r hab hbc
  }

private theorem weight_eq_of_same_endpoints [Group G] (κ : V → V → G)
    (hreturn : ∀ {a b : V}, r a b → Reaches r b a)
    (hclosed : ∀ (a : V) (w : DirectedWalk r a a), weight r κ w = 1)
    {a b : V} (u v : DirectedWalk r a b) : weight r κ u = weight r κ v := by
  obtain ⟨q⟩ := reaches_reverse_of_edge_returns r hreturn u
  have hu := hclosed a (append r u q)
  have hv := hclosed a (append r v q)
  simp only [weight_append] at hu hv
  exact mul_right_cancel (hu.trans hv.symm)

/-- **Closed-walk criterion for a multiplicative coboundary.** Suppose every
directed edge admits a directed return walk. If the product of the edge weights
around every closed directed walk is one, then there are vertex weights whose
ratio across each directed edge is the prescribed edge weight. -/
theorem exists_vertex_of_closedWalk_weight_eq_one [Group G]
    (κ : V → V → G)
    (hreturn : ∀ {a b : V}, r a b → Reaches r b a)
    (hclosed : ∀ (a : V) (w : DirectedWalk r a a), weight r κ w = 1) :
    ∃ z : V → G, ∀ {a b : V}, r a b → κ a b = (z a)⁻¹ * z b := by
  classical
  let s := reachabilitySetoid r hreturn
  let root : V → V := fun a => (⟦a⟧ : Quotient s).out
  have hroot_reaches : ∀ a : V, Reaches r (root a) a := by
    intro a
    exact Quotient.mk_out a
  let path : (a : V) → DirectedWalk r (root a) a :=
    fun a => Classical.choice (hroot_reaches a)
  let z : V → G := fun a => weight r κ (path a)
  refine ⟨z, ?_⟩
  intro a b hab
  have hquot : (⟦a⟧ : Quotient s) = ⟦b⟧ :=
    Quotient.sound (reaches_of_edge r hab)
  have hroot : root a = root b := congrArg Quotient.out hquot
  let edgeWalk : DirectedWalk r a b := cons hab (nil b)
  let candidate : DirectedWalk r (root b) b := hroot ▸ append r (path a) edgeWalk
  have hweight := weight_eq_of_same_endpoints r κ hreturn hclosed (path b) candidate
  have hcandidate : weight r κ candidate = z a * κ a b := by
    rw [show candidate = hroot ▸ append r (path a) edgeWalk from rfl,
      weight_transport_start]
    simp [edgeWalk, z]
  rw [hcandidate] at hweight
  have hz : z b = z a * κ a b := hweight
  rw [hz]
  simp

end DirectedWalk

end TNLean.Algebra
