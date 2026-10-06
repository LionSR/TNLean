/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.TorusGClosure

/-!
# Group-label compatibility across torus closure seams

The horizontal bonds point east, whereas a vertical bond is indexed by its head
and points from the upper neighbour to that head. For a bra network with closures
`(g,h)` and a ket network with closures `(g',h')`, local regular-label compatibility
therefore has opposite orders in the horizontal and vertical equations.

Away from the two seams these equations equate neighbouring vertex labels. The
ordinary rectangular grid is connected, so every local label is one common group
element `x`. The seam equations are exactly `h*x=x*h'` and `g*x=x*g'`.
Conversely these equations give a compatible constant labelling. Thus the finite
sum over local labels reduces to the sum over simultaneous closure intertwiners.

Source: Schuch, Cirac, and Pérez-García, arXiv:1001.3807, Definition 5.6 and the
invariance assertion after Definition 5.8, source lines 1515–1525 and 1575–1580.
This is an auxiliary group-coordinate statement for twisted torus contractions;
it asserts neither the ground-space theorem nor the full physical entropy theorem.
-/

namespace TNLean.PEPS

variable {G : Type*} [Group G]
variable {width height : ℕ} [NeZero width] [NeZero height]

/-- The group element on a horizontal seam bond in SCP10,
`eq:2d:peps-with-ug-uh`, lines 1515–1525. -/
def torusHorizontalClosureElement (h : G) (v : TorusVertex width height) : G :=
  if v.1 + 1 = 0 then h else 1

/-- The group element on a vertical seam bond, indexed by its head, in SCP10,
`eq:2d:peps-with-ug-uh`, lines 1515–1525. -/
def torusVerticalClosureElement (g : G) (v : TorusVertex width height) : G :=
  if v.2 + 1 = 0 then g else 1

omit [NeZero width] [NeZero height] in
/-- The horizontal group seam element gives the matrix closure in SCP10,
`eq:2d:peps-with-ug-uh`, under any group representation. -/
theorem torusHorizontalClosure_eq_map_element {V : Type*} [Fintype V] [DecidableEq V]
    (U : G →* Matrix V V ℂ) (h : G) (v : TorusVertex width height) :
    torusHorizontalClosure U h v = U (torusHorizontalClosureElement h v) := by
  unfold torusHorizontalClosure torusHorizontalClosureElement
  split_ifs <;> simp

omit [NeZero width] [NeZero height] in
/-- The vertical group seam element gives the downward-oriented matrix closure
in SCP10, `eq:2d:peps-with-ug-uh`, under any group representation. -/
theorem torusVerticalClosure_eq_map_element {V : Type*} [Fintype V] [DecidableEq V]
    (U : G →* Matrix V V ℂ) (g : G) (v : TorusVertex width height) :
    torusVerticalClosure U g v = U (torusVerticalClosureElement g v) := by
  unfold torusVerticalClosure torusVerticalClosureElement
  split_ifs <;> simp

/-- Compatibility of regular site translations between bra and ket torus
closures. The vertical bond runs from the upper neighbour to the current
vertex. Source: SCP10, `eq:2d:peps-with-ug-uh`, lines 1515–1525. -/
def IsTorusClosureCompatible (g h g' h' : G)
    (q : TorusVertex width height → G) : Prop :=
  ∀ v, torusHorizontalClosureElement h v * q v =
      q (v.1 + 1, v.2) * torusHorizontalClosureElement h' v ∧
    torusVerticalClosureElement g v * q (v.1, v.2 + 1) =
      q v * torusVerticalClosureElement g' v

instance [DecidableEq G] (g h g' h' : G) (q : TorusVertex width height → G) :
    Decidable (IsTorusClosureCompatible g h g' h' q) :=
  inferInstanceAs (Decidable (∀ v,
    torusHorizontalClosureElement h v * q v =
        q (v.1 + 1, v.2) * torusHorizontalClosureElement h' v ∧
      torusVerticalClosureElement g v * q (v.1, v.2 + 1) =
        q v * torusVerticalClosureElement g' v))

private theorem zmod_eq_zero_of_nonseam {n : ℕ} [NeZero n] {α : Type*}
    (f : ZMod n → α) (hf : ∀ z, z + 1 ≠ 0 → f (z + 1) = f z) (z : ZMod n) :
    f z = f 0 := by
  have hk (k : ℕ) (hk : k < n) : f (k : ZMod n) = f 0 := by
    induction k with
    | zero => simp
    | succ k ih =>
      have hne : ((k + 1 : ℕ) : ZMod n) ≠ 0 := by
        intro hz
        have hv := congrArg ZMod.val hz
        rw [ZMod.val_natCast_of_lt hk, ZMod.val_zero] at hv
        omega
      have h := hf (k : ZMod n) (by simpa only [Nat.cast_add, Nat.cast_one] using hne)
      simpa only [Nat.cast_add, Nat.cast_one] using h.trans (ih (by omega))
  simpa only [ZMod.natCast_zmod_val] using hk z.val (ZMod.val_lt z)

omit [Group G] in
/-- Equality of neighbouring labels on all bonds away from the two closure seams.
Source: SCP10, the local contraction argument in Theorem 5.9, lines 1582–1621. -/
def IsTorusNonseamCompatible {α : Type*} (q : TorusVertex width height → α) : Prop :=
  ∀ v, (v.1 + 1 ≠ 0 → q (v.1 + 1, v.2) = q v) ∧
    (v.2 + 1 ≠ 0 → q v = q (v.1, v.2 + 1))

omit [Group G] in
/-- Local equalities away from the closure seams force one common vertex label.
Source: SCP10, Theorem 5.9, lines 1582–1621. This also holds for circumference one. -/
theorem IsTorusNonseamCompatible.eq_origin {α : Type*}
    {q : TorusVertex width height → α} (hq : IsTorusNonseamCompatible q)
    (v : TorusVertex width height) : q v = q (0, 0) := by
  have hh (b : ZMod height) (a : ZMod width) : q (a, b) = q (0, b) := by
    exact zmod_eq_zero_of_nonseam (fun a => q (a, b))
      (fun z hz => (hq (z, b)).1 hz) a
  have hv (a : ZMod width) (b : ZMod height) : q (a, b) = q (a, 0) := by
    exact zmod_eq_zero_of_nonseam (fun b => q (a, b))
      (fun z hz => ((hq (a, z)).2 hz).symm) b
  exact (hh v.2 v.1).trans (hv 0 v.2)

/-- Compatible local translations are constant, including when either torus
dimension is one. Source: SCP10, invariance argument after Definition 5.8,
lines 1575–1580. -/
theorem IsTorusClosureCompatible.eq_origin {g h g' h' : G}
    {q : TorusVertex width height → G} (hq : IsTorusClosureCompatible g h g' h' q)
    (v : TorusVertex width height) : q v = q (0, 0) := by
  apply IsTorusNonseamCompatible.eq_origin (q := q) _ v
  intro z
  constructor
  · intro hz
    simpa [torusHorizontalClosureElement, hz] using (hq z).1.symm
  · intro hz
    simpa [torusVerticalClosureElement, hz] using (hq z).2.symm

/-- Local torus compatibility is precisely a constant simultaneous
intertwiner of the two closure labels. Source: SCP10, Definition 5.8 and its
following invariance assertion, lines 1560–1580. -/
theorem isTorusClosureCompatible_iff_exists_intertwiner (g h g' h' : G)
    (q : TorusVertex width height → G) :
    IsTorusClosureCompatible g h g' h' q ↔
      ∃ x : G, (∀ v, q v = x) ∧ h * x = x * h' ∧ g * x = x * g' := by
  constructor
  · intro hq
    refine ⟨q (0, 0), hq.eq_origin, ?_, ?_⟩
    · simpa [torusHorizontalClosureElement, hq.eq_origin] using (hq (-1, 0)).1
    · simpa [torusVerticalClosureElement, hq.eq_origin] using (hq (0, -1)).2
  · rintro ⟨x, hx, hh, hg⟩ v
    constructor
    · simp only [hx, torusHorizontalClosureElement]
      split_ifs <;> simp_all
    · simp only [hx, torusVerticalClosureElement]
      split_ifs <;> simp_all

open scoped BigOperators in
/-- Source: SCP10, pair-conjugacy invariance, lines 1575–1580. The sum of local
compatibility indicators is the sum of simultaneous closure intertwiners. -/
theorem sum_torusClosureCompatible_eq_sum_intertwiner [Fintype G] [DecidableEq G]
    (g h g' h' : G) :
    (∑ q : TorusVertex width height → G,
      if IsTorusClosureCompatible g h g' h' q then (1 : ℂ) else 0) =
      ∑ x : G, if h * x = x * h' ∧ g * x = x * g' then (1 : ℂ) else 0 := by
  classical
  refine (Fintype.sum_of_injective (fun x : G => fun _ : TorusVertex width height => x)
    (fun x y hxy => congrFun hxy (0, 0)) _ _ ?_ ?_).symm
  · intro q hq
    split_ifs with hc
    · exact (hq ⟨q (0, 0), (funext hc.eq_origin).symm⟩).elim
    · rfl
  · intro x
    have hc : IsTorusClosureCompatible g h g' h' (fun _ : TorusVertex width height => x) ↔
        h * x = x * h' ∧ g * x = x * g' := by
      rw [isTorusClosureCompatible_iff_exists_intertwiner]
      constructor
      · rintro ⟨y, hy, hh, hg⟩
        simpa only [← hy (0, 0)] using And.intro hh hg
      · intro h
        exact ⟨x, fun _ => rfl, h⟩
    simp only [hc]

end TNLean.PEPS
