/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Algebra.BigOperators.Fin
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
one finite cycle. Reachability by a directed walk is equivalent to the
reflexive transitive closure of the edge relation; this permits direct use with
relations defined through `Relation.ReflTransGen`.

A nonempty closed walk also determines a finite cyclic family of vertices.
Every consecutive pair is an edge, including the final return to the initial
vertex, and the cyclic product of the edge weights equals the walk weight.
-/

namespace TNLean.Algebra

open scoped BigOperators

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

/-- The number of edges in a directed walk. -/
@[reducible] def edgeCount {a b : V} : DirectedWalk r a b → ℕ
  | .nil _ => 0
  | .cons _ w => edgeCount w + 1

@[simp] theorem edgeCount_nil (a : V) : edgeCount r (.nil a) = 0 := rfl

@[simp] theorem edgeCount_cons {a b c : V} (hab : r a b) (w : DirectedWalk r b c) :
    edgeCount r (.cons hab w) = edgeCount r w + 1 := rfl

/-- The vertex at a position of a directed walk, including both endpoints. -/
def vertexAt {a b : V} (w : DirectedWalk r a b) :
    Fin (edgeCount r w + 1) → V :=
  match w with
  | .nil a => fun _ => a
  | .cons (a := a) _ w => Fin.cases a (fun i => vertexAt w i)

@[simp] theorem vertexAt_nil (a : V) (i : Fin 1) :
    vertexAt r (.nil a) i = a := rfl

@[simp] theorem vertexAt_cons_zero {a b c : V} (hab : r a b)
    (w : DirectedWalk r b c) :
    vertexAt r (.cons hab w) 0 = a := rfl

@[simp] theorem vertexAt_cons_succ {a b c : V} (hab : r a b)
    (w : DirectedWalk r b c) (i : Fin (edgeCount r w + 1)) :
    vertexAt r (.cons hab w) i.succ = vertexAt r w i := rfl

@[simp] theorem vertexAt_zero {a b : V} (w : DirectedWalk r a b) :
    vertexAt r w 0 = a := by
  cases w <;> rfl

@[simp] theorem vertexAt_last {a b : V} (w : DirectedWalk r a b) :
    vertexAt r w (Fin.last (edgeCount r w)) = b := by
  induction w with
  | nil => rfl
  | @cons a b c hab w ih =>
      change Fin.cases a (fun i => vertexAt r w i)
        (Fin.last (edgeCount r w + 1)) = c
      rw [show Fin.last (edgeCount r w + 1) = (Fin.last (edgeCount r w)).succ by
        ext
        simp]
      exact ih

/-- Consecutive positions in a directed walk are related by an edge. -/
theorem vertexAt_edge {a b : V} (w : DirectedWalk r a b)
    (i : Fin (edgeCount r w)) :
    r (vertexAt r w i.castSucc) (vertexAt r w i.succ) := by
  induction w with
  | nil => exact Fin.elim0 i
  | @cons a b c hab w ih =>
      refine Fin.cases ?_ (fun j => ?_) i
      · change r a (Fin.cases a (fun i => vertexAt r w i) 1)
        have hone : (1 : Fin (edgeCount r w + 2)) =
            (0 : Fin (edgeCount r w + 1)).succ := by
          ext
          simp
        rw [hone]
        rw [Fin.cases_succ, vertexAt_zero]
        exact hab
      · change r
          (Fin.cases a (fun i => vertexAt r w i) j.succ.castSucc)
          (Fin.cases a (fun i => vertexAt r w i) j.succ.succ)
        simp only [Fin.cases_succ]
        exact ih j

/-- A nonempty closed walk, written as its cyclic list of source vertices. -/
def closedConsVertices {a b : V} (hab : r a b) (w : DirectedWalk r b a) :
    Fin (edgeCount r w + 1) → V :=
  fun i => vertexAt r (.cons hab w) i.castSucc

@[simp] theorem closedConsVertices_zero {a b : V} (hab : r a b)
    (w : DirectedWalk r b a) :
    closedConsVertices r hab w 0 = a := rfl

private theorem castSucc_add_one_eq_succ_of_ne_last {N : ℕ}
    (i : Fin (N + 1)) (hi : i ≠ Fin.last N) :
    (i + 1).castSucc = i.succ := by
  apply Fin.ext
  have hi' : i.val < N := by
    have hine : i.val ≠ N := by
      intro heq
      apply hi
      ext
      exact heq
    omega
  have hone : (1 : Fin (N + 1)).val = 1 := by
    rw [Fin.val_one']
    exact Nat.mod_eq_of_lt (by omega)
  calc
    ↑(i + 1).castSucc = ↑(i + 1) := Fin.val_castSucc _
    _ = (i.val + (1 : Fin (N + 1)).val) % (N + 1) := Fin.val_add _ _
    _ = (i.val + 1) % (N + 1) := by rw [hone]
    _ = i.val + 1 := Nat.mod_eq_of_lt (by omega)
    _ = ↑i.succ := (Fin.val_succ i).symm

private theorem castSucc_add_one_eq_zero_of_eq_last {N : ℕ}
    (i : Fin (N + 1)) (hi : i = Fin.last N) :
    (i + 1).castSucc = (0 : Fin (N + 2)) := by
  subst i
  apply Fin.ext
  calc
    ↑(Fin.last N + 1).castSucc = ↑(Fin.last N + 1) := Fin.val_castSucc _
    _ = ((Fin.last N).val + (1 : Fin (N + 1)).val) % (N + 1) :=
      Fin.val_add _ _
    _ = 0 := by
      cases N <;> simp [Nat.mod_self]
    _ = ↑(0 : Fin (N + 2)) := rfl

/-- The vertex following the initial vertex is the target of the distinguished
first edge. -/
@[simp] theorem closedConsVertices_zero_add_one {a b : V} (hab : r a b)
    (w : DirectedWalk r b a) :
    closedConsVertices r hab w (0 + 1) = b := by
  cases w with
  | nil =>
      rw [show (0 + 1 : Fin 1) = 0 from Subsingleton.elim _ _,
        closedConsVertices_zero]
  | @cons b c a hbc w =>
      unfold closedConsVertices
      rw [castSucc_add_one_eq_succ_of_ne_last]
      · simp only [vertexAt_cons_succ, vertexAt_zero]
      · intro h
        have := congrArg Fin.val h
        simp at this

/-- Consecutive cyclic vertices of a nonempty closed walk are related by an edge. -/
theorem closedConsVertices_edge {a b : V} (hab : r a b)
    (w : DirectedWalk r b a) (i : Fin (edgeCount r w + 1)) :
    r (closedConsVertices r hab w i)
      (closedConsVertices r hab w (i + 1)) := by
  by_cases hi : i = Fin.last (edgeCount r w)
  · have hedge := vertexAt_edge r (.cons hab w) i
    change r (vertexAt r (.cons hab w) i.castSucc)
      (vertexAt r (.cons hab w) (i + 1).castSucc)
    rw [castSucc_add_one_eq_zero_of_eq_last i hi, vertexAt_zero]
    have hisucc : i.succ = Fin.last (edgeCount r w + 1) := by
      subst i
      ext
      simp
    rw [hisucc, vertexAt_last] at hedge
    exact hedge
  · have hedge := vertexAt_edge r (.cons hab w) i
    change r (vertexAt r (.cons hab w) i.castSucc)
      (vertexAt r (.cons hab w) (i + 1).castSucc)
    rw [castSucc_add_one_eq_succ_of_ne_last i hi]
    exact hedge

/-- The weight of a walk is the product of the weights of its linearly ordered edges. -/
theorem weight_eq_fin_prod_vertexAt [CommMonoid G] (κ : V → V → G)
    {a b : V} (w : DirectedWalk r a b) :
    weight r κ w = ∏ i : Fin (edgeCount r w),
      κ (vertexAt r w i.castSucc) (vertexAt r w i.succ) := by
  induction w with
  | nil => simp [edgeCount]
  | @cons a b c hab w ih =>
      rw [weight_cons]
      change κ a b * weight r κ w = ∏ i : Fin (edgeCount r w + 1),
        κ (vertexAt r (.cons hab w) i.castSucc)
          (vertexAt r (.cons hab w) i.succ)
      rw [Fin.prod_univ_succ]
      rw [ih]
      congr 1
      change κ a b = κ a (vertexAt r w 0)
      rw [vertexAt_zero]

/-- The weight of a nonempty closed walk is the cyclic product of the weights
of its consecutive edges. -/
theorem weight_closedCons_eq_fin_prod [CommMonoid G] (κ : V → V → G)
    {a b : V} (hab : r a b) (w : DirectedWalk r b a) :
    weight r κ (.cons hab w) = ∏ i : Fin (edgeCount r w + 1),
      κ (closedConsVertices r hab w i)
        (closedConsVertices r hab w (i + 1)) := by
  rw [weight_eq_fin_prod_vertexAt]
  apply Finset.prod_congr rfl
  intro i _
  congr 1
  unfold closedConsVertices
  by_cases hi : i = Fin.last (edgeCount r w)
  · rw [castSucc_add_one_eq_zero_of_eq_last i hi, vertexAt_zero]
    have hisucc : i.succ = Fin.last (edgeCount r w + 1) := by
      subst i
      ext
      simp
    rw [hisucc, vertexAt_last]
  · rw [castSucc_add_one_eq_succ_of_ne_last i hi]

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

/-- Reachability by a directed walk is equivalent to membership in the
reflexive transitive closure of the edge relation. -/
theorem reaches_iff_reflTransGen {a b : V} :
    Reaches r a b ↔ Relation.ReflTransGen r a b := by
  constructor
  · rintro ⟨w⟩
    induction w with
    | nil => exact .refl
    | cons hab w ih => exact ih.head hab
  · intro h
    induction h with
    | refl => exact ⟨nil _⟩
    | tail hab hbc ih =>
      obtain ⟨w⟩ := ih
      exact ⟨append r w (cons hbc (nil _))⟩

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
