/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.TorusGaugedRouteStep
import TNLean.PEPS.RegularActualTwoChordTransport
import TNLean.PEPS.TorusDirectedBondUpdate
import TNLean.PEPS.TorusActualPlaquetteVacancy

/-!
# Actual four-direction elementary flux operations

At each position and along each axis, the native six-site patch supplies its
spanning path, root and two remaining chords. A fixed original-spin unitary
and its adjoint act on the normalized coordinates derived from every actual
input. The vacancy and literal one-bond descriptions are derived separately.

Source: SCP10, arXiv:1001.3807, Theorem 6.16, lines 2271–2305, and the
four-endpoint route, lines 2340–2423.

**Scope restriction (finite torus and regular action):** Both periods are at
least four. All positions and periodic seams are allowed. These are elementary
route operations, not the complete prescribed braid. See
`docs/paper-gaps/rmp_peps_quantum_double_g_isometry.tex`.
-/
noncomputable section
open scoped Matrix
namespace TNLean.PEPS
variable {width height : ℕ} [NeZero width] [NeZero height]
variable [Fact (3 < width)] [Fact (3 < height)]
local instance actualRouteWidthTwo : Fact (2 < width) :=
  ⟨by have := Fact.out (p := 3 < width); omega⟩
local instance actualRouteHeightTwo : Fact (2 < height) :=
  ⟨by have := Fact.out (p := 3 < height); omega⟩
local instance actualRouteWidthOne : Fact (1 < width) :=
  ⟨by have := Fact.out (p := 3 < width); omega⟩
local instance actualRouteHeightOne : Fact (1 < height) :=
  ⟨by have := Fact.out (p := 3 < height); omega⟩
local notation "X" => TorusVertex width height
local notation "Γₜ" => torusGraph width height
private abbrev R (horizontal : Bool) (p : X) := torusRouteStepRegion horizontal p
private abbrev RV (horizontal : Bool) (p : X) := {x : X // x ∈ R horizontal p}
private def T (horizontal : Bool) (p : X) : SimpleGraph (RV horizontal p) := by
  cases horizontal
  · exact verticalTwoPlaquetteTree p
  · exact translatedTwoPlaquetteTree p
local instance actualRouteTreeDecidableAdj (horizontal : Bool) (p : X) :
    DecidableRel (T horizontal p).Adj := by
  classical
  exact fun _ _ => inferInstance
private def φ (horizontal : Bool) (p : X) :
    twoPlaquetteGraph ≃g (Γₜ).induce (R horizontal p : Set X) := by
  cases horizontal
  · exact verticalTwoPlaquetteIso p
  · exact translatedTwoPlaquetteIso p
private theorem tree_le (horizontal : Bool) (p : X) :
    T horizontal p ≤ (Γₜ).induce (R horizontal p : Set X) := by
  cases horizontal
  · exact verticalTwoPlaquetteTree_le p
  · exact translatedTwoPlaquetteTree_le p
private theorem tree_isTree (horizontal : Bool) (p : X) : (T horizontal p).IsTree := by
  cases horizontal
  · exact verticalTwoPlaquetteTree_isTree p
  · exact translatedTwoPlaquetteTree_isTree p
private def chord (horizontal : Bool) (p : X) (i : Fin 2) :
    RegionCycleEdge (Γ := Γₜ) (R horizontal p) (T horizontal p) := by
  cases horizontal
  · exact verticalTwoPlaquetteCycleBond p i
  · exact translatedTwoPlaquetteCycleBond p i
private theorem chord_ne (horizontal : Bool) (p : X) :
    chord horizontal p 0 ≠ chord horizontal p 1 := by
  cases horizontal
  · exact (verticalTwoPlaquetteCycleBond_injective p).ne (by decide)
  · exact (translatedTwoPlaquetteCycleBond_injective p).ne (by decide)
variable {G : Type*} [Group G] [Fintype G]

/-- The actual forward or reverse cycle operation in the derived native patch.
Source: SCP10, Theorem 6.16, lines 2271–2305. -/
def torusActualRouteFluxMove (horizontal reverse : Bool) (p : X)
    (u : Edge Γₜ → G) : Edge Γₜ → G :=
  regularActualCycleDirectionalPermutation (R horizontal p) (T horizontal p)
    (tree_le horizontal p) (tree_isTree horizontal p) (φ horizontal p 0)
    (regularTwoCycleMove (chord horizontal p 0) (chord horizontal p 1)
      (chord_ne horizontal p)) reverse u

private def offset (horizontal : Bool) (p : X) (x y : ℕ) : X :=
  if horizontal then (p.1 + x, p.2 + y) else (p.1 + y, p.2 + x)

private theorem coordinates (horizontal : Bool) (p : X) (i : Fin 6) :
    (φ horizontal p i).1 = offset horizontal p (![0,1,2,2,1,0] i)
      (![0,0,0,1,1,1] i) := by
  cases horizontal
  · exact verticalTwoPlaquetteIso_apply p i
  · exact translatedTwoPlaquetteIso_vertex_coordinates p i

private theorem treeAdj (horizontal : Bool) (p : X) {i j : Fin 6}
    (h : twoPlaquetteTree.Adj i j) :
    (T horizontal p).Adj (φ horizontal p i) (φ horizontal p j) := by
  cases horizontal
  · change twoPlaquetteTree.Adj
      ((verticalTwoPlaquetteIso p).symm (verticalTwoPlaquetteIso p i))
      ((verticalTwoPlaquetteIso p).symm (verticalTwoPlaquetteIso p j))
    simpa only [RelIso.symm_apply_apply] using h
  · change twoPlaquetteTree.Adj
      ((translatedTwoPlaquetteVertexEquiv p).symm (translatedTwoPlaquetteVertexEquiv p i))
      ((translatedTwoPlaquetteVertexEquiv p).symm (translatedTwoPlaquetteVertexEquiv p j))
    simpa only [Equiv.symm_apply_apply] using h

private theorem mappedAdj (horizontal : Bool) (p : X) {i j : Fin 6}
    (h : twoPlaquetteGraph.Adj i j) : (Γₜ).Adj (φ horizontal p i).1 (φ horizontal p j).1 :=
  SimpleGraph.induce_adj.mp ((φ horizontal p).map_rel_iff'.mpr h)

private def next (ax : Bool) (q : X) : X :=
  if ax then (q.1, q.2 + 1) else (q.1 + 1, q.2)
private theorem step (ax : Bool) (q : X) : (Γₜ).Adj q (next ax q) := by
  cases ax
  · exact torusGraph_adj_right q.1 q.2
  · exact torusGraph_adj_up q.1 q.2

omit [Fintype G] in
private theorem mappedTransport (horizontal : Bool) (p : X) (u : Edge Γₜ → G)
    (i j : Fin 6) (h : (Γₜ).Adj (φ horizontal p i).1 (φ horizontal p j).1)
    (ax rev : Bool) (q : X)
    (hi : (φ horizontal p i).1 = if rev then next ax q else q)
    (hj : (φ horizontal p j).1 = if rev then q else next ax q) :
    regularDirectedTransport u h =
      if rev then (torusDirectedBondTransport ax u q)⁻¹ else torusDirectedBondTransport ax u q := by
  cases rev
  · exact regularDirectedTransport_eq_of_endpoints u h (step ax q) hi hj
  · exact (regularDirectedTransport_eq_of_endpoints u h (step ax q).symm hi hj).trans
      (regularDirectedTransport_symm u (step ax q))

omit [Fintype G] in
private theorem transportTable (horizontal : Bool) (p : X) (u : Edge Γₜ → G) :
    (regularDirectedTransport u (mappedAdj horizontal p (by decide : twoPlaquetteGraph.Adj 0 1)) =
      torusDirectedBondTransport (!horizontal) u p) ∧
    (regularDirectedTransport u (mappedAdj horizontal p (by decide : twoPlaquetteGraph.Adj 1 2)) =
      torusDirectedBondTransport (!horizontal) u (offset horizontal p 1 0)) ∧
    (regularDirectedTransport u (mappedAdj horizontal p (by decide : twoPlaquetteGraph.Adj 2 3)) =
      torusDirectedBondTransport horizontal u (offset horizontal p 2 0)) ∧
    (regularDirectedTransport u (mappedAdj horizontal p (by decide : twoPlaquetteGraph.Adj 3 4)) =
      (torusDirectedBondTransport (!horizontal) u (offset horizontal p 1 1))⁻¹) ∧
    (regularDirectedTransport u (mappedAdj horizontal p (by decide : twoPlaquetteGraph.Adj 4 5)) =
      (torusDirectedBondTransport (!horizontal) u (offset horizontal p 0 1))⁻¹) ∧
    (regularDirectedTransport u (mappedAdj horizontal p (by decide : twoPlaquetteGraph.Adj 0 5)) =
      torusDirectedBondTransport horizontal u p) ∧
    (regularDirectedTransport u (mappedAdj horizontal p (by decide : twoPlaquetteGraph.Adj 1 4)) =
      torusDirectedBondTransport horizontal u (offset horizontal p 1 0)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine mappedTransport horizontal p u 0 1 _ (!horizontal) false
      p ?_ ?_ <;> rw [coordinates] <;>
      cases horizontal <;> norm_num [offset, next, add_assoc]
  · refine mappedTransport horizontal p u 1 2 _ (!horizontal) false
      (offset horizontal p 1 0) ?_ ?_ <;> rw [coordinates] <;>
      cases horizontal <;> norm_num [offset, next, add_assoc]
  · refine mappedTransport horizontal p u 2 3 _ horizontal false
      (offset horizontal p 2 0) ?_ ?_ <;> rw [coordinates] <;>
      cases horizontal <;> norm_num [offset, next, add_assoc]
  · refine mappedTransport horizontal p u 3 4 _ (!horizontal) true
      (offset horizontal p 1 1) ?_ ?_ <;> rw [coordinates] <;>
      cases horizontal <;> norm_num [offset, next, add_assoc]
  · refine mappedTransport horizontal p u 4 5 _ (!horizontal) true
      (offset horizontal p 0 1) ?_ ?_ <;> rw [coordinates] <;>
      cases horizontal <;> norm_num [offset, next, add_assoc]
  · refine mappedTransport horizontal p u 0 5 _ horizontal false
      p ?_ ?_ <;> rw [coordinates] <;>
      cases horizontal <;> norm_num [offset, next, add_assoc]
  · refine mappedTransport horizontal p u 1 4 _ horizontal false
      (offset horizontal p 1 0) ?_ ?_ <;> rw [coordinates] <;>
      cases horizontal <;> norm_num [offset, next, add_assoc]

private theorem chord_zero (horizontal : Bool) (p : X) :
    Edge.ofAdj (mappedAdj horizontal p (by decide : twoPlaquetteGraph.Adj 0 5)) =
      (chord horizontal p 0).1.1 := by
  cases horizontal
  · rw [show (chord false p 0).1.1 = _ from verticalTwoPlaquetteCycleBond_eq_right p 0]
    apply Edge.ofAdj_eq_ofAdj _ _
    apply Or.inl
    constructor <;> rw [coordinates] <;> norm_num [offset]
  · rw [show (chord true p 0).1.1 = _ from translatedTwoPlaquetteCycleBond_eq_up p 0]
    apply Edge.ofAdj_eq_ofAdj _ _
    apply Or.inl
    constructor <;> rw [coordinates] <;> norm_num [offset]

private theorem chord_one (horizontal : Bool) (p : X) :
    Edge.ofAdj (mappedAdj horizontal p (by decide : twoPlaquetteGraph.Adj 1 4)) =
      (chord horizontal p 1).1.1 := by
  cases horizontal
  · rw [show (chord false p 1).1.1 = _ from verticalTwoPlaquetteCycleBond_eq_right p 1]
    apply Edge.ofAdj_eq_ofAdj _ _
    apply Or.inl
    constructor <;> rw [coordinates] <;> norm_num [offset]
  · rw [show (chord true p 1).1.1 = _ from translatedTwoPlaquetteCycleBond_eq_up p 1]
    apply Edge.ofAdj_eq_ofAdj _ _
    apply Or.inl
    constructor <;> rw [coordinates] <;> norm_num [offset]

private theorem chord_order (horizontal : Bool) (p : X) :
    (φ horizontal p 1).1 < (φ horizontal p 4).1 ↔
      (φ horizontal p 0).1 < (φ horizontal p 5).1 := by
  simp only [coordinates]
  cases horizontal
  · norm_num [offset]
    change toLex (p.1.val, (p.2 + 1).val) < toLex ((p.1 + 1).val, (p.2 + 1).val) ↔
      toLex (p.1.val, p.2.val) < toLex ((p.1 + 1).val, p.2.val)
    have hn : p.1.val ≠ (p.1 + 1).val := by
      intro h
      have H := ZMod.val_injective width h
      have H0 : (0 : ZMod width) = 1 :=
        add_left_cancel (show p.1 + 0 = p.1 + 1 by simpa only [add_zero] using H)
      exact one_ne_zero H0.symm
    simp only [Prod.Lex.toLex_lt_toLex, hn, false_and, or_false]
  · norm_num [offset]
    change toLex ((p.1 + 1).val, p.2.val) < toLex ((p.1 + 1).val, (p.2 + 1).val) ↔
      toLex (p.1.val, p.2.val) < toLex (p.1.val, (p.2 + 1).val)
    simp only [Prod.Lex.toLex_lt_toLex, lt_self_iff_false, false_or, true_and]

private def faceLoop (horizontal reverse : Bool) (p : X) :
    (Γₜ).Walk (φ horizontal p (if reverse then 0 else 1)).1
      (φ horizontal p (if reverse then 0 else 1)).1 := by
  cases reverse
  · exact .cons (mappedAdj horizontal p (by decide : twoPlaquetteGraph.Adj 1 2))
      (.cons (mappedAdj horizontal p (by decide : twoPlaquetteGraph.Adj 2 3))
        (.cons (mappedAdj horizontal p (by decide : twoPlaquetteGraph.Adj 3 4))
          (.cons (mappedAdj horizontal p (by decide : twoPlaquetteGraph.Adj 1 4)).symm .nil)))
  · exact .cons (mappedAdj horizontal p (by decide : twoPlaquetteGraph.Adj 0 1))
      (.cons (mappedAdj horizontal p (by decide : twoPlaquetteGraph.Adj 1 4))
        (.cons (mappedAdj horizontal p (by decide : twoPlaquetteGraph.Adj 4 5))
          (.cons (mappedAdj horizontal p (by decide : twoPlaquetteGraph.Adj 0 5)).symm .nil)))

omit [Fintype G] in
private theorem positiveRight (u : Edge Γₜ → G) (q : X) :
    torusDirectedBondTransport false u q =
      regularDirectedTransport u (torusGraph_adj_right q.1 q.2) := rfl
omit [Fintype G] in
private theorem positiveUp (u : Edge Γₜ → G) (q : X) :
    torusDirectedBondTransport true u q =
      regularDirectedTransport u (torusGraph_adj_up q.1 q.2) := rfl

omit [Fintype G] in
private theorem faceLoop_vacant (horizontal reverse : Bool) (p : X) (u : Edge Γₜ → G)
    (hv : regularWalkHolonomy u (torusPlaquetteWalk
      (if reverse then p else offset horizontal p 1 0)) = 1) :
    regularWalkHolonomy u (faceLoop horizontal reverse p) = 1 := by
  rcases transportTable horizontal p u with ⟨h01, h12, h23, h34, h45, h05, h14⟩
  cases reverse
  · simp only [faceLoop, regularWalkHolonomy_cons, regularWalkHolonomy_nil, one_mul]
    rw [regularDirectedTransport_symm u
      (mappedAdj horizontal p (by decide : twoPlaquetteGraph.Adj 1 4)), h12, h23, h34, h14]
    rw [regularWalkHolonomy_torusPlaquetteWalk] at hv
    cases horizontal
    · have H := congrArg Inv.inv hv
      simpa only [offset, ite_false, Bool.not_false, Bool.false_eq_true,
        positiveRight, positiveUp, Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat,
        mul_inv_rev, inv_inv, inv_one,
        add_zero, Prod.fst, Prod.snd, mul_assoc, add_assoc, one_add_one_eq_two] using H
    · simpa only [offset, ite_true, ite_false, Bool.false_eq_true, Bool.not_true,
        positiveRight, positiveUp, Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat,
        mul_inv_rev, inv_inv, inv_one,
        add_zero, Prod.fst, Prod.snd, mul_assoc, add_assoc, one_add_one_eq_two] using hv
  · simp only [faceLoop, regularWalkHolonomy_cons, regularWalkHolonomy_nil, one_mul]
    rw [regularDirectedTransport_symm u
      (mappedAdj horizontal p (by decide : twoPlaquetteGraph.Adj 0 5)), h01, h14, h45, h05]
    rw [regularWalkHolonomy_torusPlaquetteWalk] at hv
    cases horizontal
    · have H := congrArg Inv.inv hv
      simpa only [offset, ite_false, Bool.not_false, Bool.false_eq_true,
        positiveRight, positiveUp, Nat.cast_zero, Nat.cast_one, add_zero,
        Prod.fst, Prod.snd, mul_inv_rev, inv_inv, inv_one, mul_assoc] using H
    · simpa only [offset, ite_true, ite_false, Bool.false_eq_true, Bool.not_true,
        positiveRight, positiveUp, Nat.cast_zero, Nat.cast_one, add_zero,
        Prod.fst, Prod.snd, mul_assoc] using hv

omit [Fintype G] in
/-- The three original directed transports determine the replacement.
The forward axes give rightward and upward motion; the inverse axes give
leftward and downward motion. Source: SCP10, Theorem 6.16, lines 2271–2305. -/
def torusActualRouteFluxReplacement (horizontal reverse : Bool) (p : X)
    (u : Edge Γₜ → G) : G :=
  if reverse then
    (torusDirectedBondTransport (!horizontal) u (offset horizontal p 1 1))⁻¹ *
      torusDirectedBondTransport horizontal u (offset horizontal p 2 0) *
      torusDirectedBondTransport (!horizontal) u (offset horizontal p 1 0)
  else
    torusDirectedBondTransport (!horizontal) u (offset horizontal p 0 1) *
      torusDirectedBondTransport horizontal u p *
      (torusDirectedBondTransport (!horizontal) u p)⁻¹

omit [Fintype G] in
/-- Replace precisely the shared middle bond, retaining all other actual
operators and correcting its ordering at a periodic seam.
Source: SCP10, Theorem 6.16, lines 2271–2305. -/
def torusActualRouteFluxUpdate (horizontal reverse : Bool) (p : X)
    (u : Edge Γₜ → G) : Edge Γₜ → G :=
  torusDirectedBondUpdate horizontal (offset horizontal p 1 0)
    (torusActualRouteFluxReplacement horizontal reverse p u) u

omit [Fintype G] in
/-- The actual update has the four literal directed formulas at the shared bond.
Source: SCP10, Theorem 6.16, lines 2271–2305. -/
theorem torusActualRouteFluxUpdate_formula (horizontal reverse : Bool) (p : X)
    (u : Edge Γₜ → G) :
    torusActualRouteFluxUpdate horizontal reverse p u =
      if horizontal then
        if reverse then torusDirectedBondUpdate true (p.1 + 1, p.2)
          ((torusDirectedBondTransport false u (p.1 + 1, p.2 + 1))⁻¹ *
            torusDirectedBondTransport true u (p.1 + 2, p.2) *
            torusDirectedBondTransport false u (p.1 + 1, p.2)) u
        else torusDirectedBondUpdate true (p.1 + 1, p.2)
          (torusDirectedBondTransport false u (p.1, p.2 + 1) *
            torusDirectedBondTransport true u p *
            (torusDirectedBondTransport false u p)⁻¹) u
      else
        if reverse then torusDirectedBondUpdate false (p.1, p.2 + 1)
          ((torusDirectedBondTransport true u (p.1 + 1, p.2 + 1))⁻¹ *
            torusDirectedBondTransport false u (p.1, p.2 + 2) *
            torusDirectedBondTransport true u (p.1, p.2 + 1)) u
        else torusDirectedBondUpdate false (p.1, p.2 + 1)
          (torusDirectedBondTransport true u (p.1 + 1, p.2) *
            torusDirectedBondTransport false u p *
            (torusDirectedBondTransport true u p)⁻¹) u := by
  cases horizontal <;> cases reverse <;>
    simp [torusActualRouteFluxUpdate, torusActualRouteFluxReplacement, offset]

omit [Fintype G] in
/-- The vacancy condition refers to the actual target plaquette coordinates.
Source: SCP10, Theorem 6.16, lines 2271–2305. -/
theorem torusActualRouteVacancy_iff (horizontal reverse : Bool) (p : X)
    (u : Edge Γₜ → G) :
    (regularWalkHolonomy u (torusPlaquetteWalk
      (if reverse then p else offset horizontal p 1 0)) = 1) ↔
    regularWalkHolonomy u (torusPlaquetteWalk
      (if reverse then p else if horizontal then (p.1 + 1, p.2) else (p.1, p.2 + 1))) = 1 := by
  have hp : offset horizontal p 1 0 =
      if horizontal then (p.1 + 1, p.2) else (p.1, p.2 + 1) := by
    cases horizontal <;> simp [offset]
  cases reverse
  · change regularWalkHolonomy u (torusPlaquetteWalk (offset horizontal p 1 0)) = 1 ↔ _
    rw [hp]
    rfl
  · rfl

/-- The vacant target face derives the literal replacement from the actual
assignment. No supplied tree background or residual identity is required.
Source: SCP10, Theorem 6.16, lines 2271–2305. -/
theorem torusActualRouteFluxMove_transport_of_vacancy (horizontal reverse : Bool)
    (p : X) (u : Edge Γₜ → G)
    (hv : regularWalkHolonomy u (torusPlaquetteWalk
      (if reverse then p else offset horizontal p 1 0)) = 1) :
    torusDirectedBondTransport horizontal (torusActualRouteFluxMove horizontal reverse p u)
      (offset horizontal p 1 0) = torusActualRouteFluxReplacement horizontal reverse p u := by
  have h01 := treeAdj horizontal p (by decide : twoPlaquetteTree.Adj 0 1)
  have h12 := treeAdj horizontal p (by decide : twoPlaquetteTree.Adj 1 2)
  have h23 := treeAdj horizontal p (by decide : twoPlaquetteTree.Adj 2 3)
  have h34 := treeAdj horizontal p (by decide : twoPlaquetteTree.Adj 3 4)
  have h45 := treeAdj horizontal p (by decide : twoPlaquetteTree.Adj 4 5)
  rcases transportTable horizontal p u with ⟨d01, d12, d23, d34, d45, d05, d14⟩
  have hm := (transportTable horizontal p
    (torusActualRouteFluxMove horizontal reverse p u)).2.2.2.2.2.2
  have Hvac := faceLoop_vacant horizontal reverse p u hv
  cases reverse
  · have H := regularActualTwoChord_forwardTransport (R horizontal p) (T horizontal p)
      (tree_le horizontal p) (tree_isTree horizontal p) (φ horizontal p 0) u
      (φ horizontal p 0) (φ horizontal p 1) (φ horizontal p 2)
      (φ horizontal p 3) (φ horizontal p 4) (φ horizontal p 5)
      h01 h12 h23 h34 h45
      (mappedAdj horizontal p (by decide : twoPlaquetteGraph.Adj 0 5))
      (mappedAdj horizontal p (by decide : twoPlaquetteGraph.Adj 1 4))
      (chord horizontal p 0) (chord horizontal p 1) (chord_ne horizontal p)
      (chord_zero horizontal p) (chord_one horizontal p) (chord_order horizontal p) Hvac
    change regularDirectedTransport (torusActualRouteFluxMove horizontal false p u) _ = _ at H
    rw [hm, d45, d05, d01] at H
    simpa only [torusActualRouteFluxReplacement, Bool.false_eq_true, ite_false, inv_inv] using H
  · have H := regularActualTwoChord_reverseTransport (R horizontal p) (T horizontal p)
      (tree_le horizontal p) (tree_isTree horizontal p) (φ horizontal p 0) u
      (φ horizontal p 0) (φ horizontal p 1) (φ horizontal p 2)
      (φ horizontal p 3) (φ horizontal p 4) (φ horizontal p 5)
      h01 h12 h23 h34 h45
      (mappedAdj horizontal p (by decide : twoPlaquetteGraph.Adj 0 5))
      (mappedAdj horizontal p (by decide : twoPlaquetteGraph.Adj 1 4))
      (chord horizontal p 0) (chord horizontal p 1) (chord_ne horizontal p)
      (chord_zero horizontal p) (chord_one horizontal p) (chord_order horizontal p) Hvac
    change regularDirectedTransport (torusActualRouteFluxMove horizontal true p u) _ = _ at H
    rw [hm, d34, d23, d12] at H
    exact H

private theorem middleChord (horizontal : Bool) (p : X) :
    (chord horizontal p 1).1.1 = Edge.ofAdj (step horizontal (offset horizontal p 1 0)) := by
  rw [← chord_one horizontal p]
  apply Edge.ofAdj_eq_ofAdj _ _
  apply Or.inl
  constructor <;> rw [coordinates] <;> cases horizontal <;>
    norm_num [offset, next, add_assoc]

/-- Actual target vacancy identifies the physical coordinate operation with
the literal one-bond update, including all exterior and crossing coefficients.
Source: SCP10, Theorem 6.16, lines 2271–2305. -/
theorem torusActualRouteFluxMove_eq_update_of_vacancy (horizontal reverse : Bool)
    (p : X) (u : Edge Γₜ → G)
    (hv : regularWalkHolonomy u (torusPlaquetteWalk
      (if reverse then p else offset horizontal p 1 0)) = 1) :
    torusActualRouteFluxMove horizontal reverse p u =
      torusActualRouteFluxUpdate horizontal reverse p u := by
  funext e
  by_cases he : e = Edge.ofAdj (step horizontal (offset horizontal p 1 0))
  · subst e
    apply regularDirectedTransport_injective_on_edge
      (step horizontal (offset horizontal p 1 0))
    change torusDirectedBondTransport horizontal
      (torusActualRouteFluxMove horizontal reverse p u) (offset horizontal p 1 0) =
      torusDirectedBondTransport horizontal
        (torusActualRouteFluxUpdate horizontal reverse p u) (offset horizontal p 1 0)
    rw [torusActualRouteFluxMove_transport_of_vacancy horizontal reverse p u hv]
    simp only [torusActualRouteFluxUpdate, torusDirectedBondTransport_update_same, ite_true]
  · have hn : e ≠ (chord horizontal p 1).1.1 := by simpa only [middleChord] using he
    rw [show torusActualRouteFluxMove horizontal reverse p u e = u e from
      regularActualTwoChordPermutation_eq_of_ne (R horizontal p) (T horizontal p)
        (tree_le horizontal p) (tree_isTree horizontal p) (φ horizontal p 0)
        (chord horizontal p 0) (chord horizontal p 1) (chord_ne horizontal p) reverse u e hn]
    exact (torusDirectedBondUpdate_eq_of_ne horizontal (offset horizontal p 1 0)
      (torusActualRouteFluxReplacement horizontal reverse p u) u e he).symm

/-- The same original-spin unitary and its adjoint act before every actual
assignment and every boundary column in either direction. Source: SCP10,
Theorem 6.16, lines 2271–2305. -/
theorem IsGIsometric.exists_unitary_torusActualRouteFluxMove {d : ℕ}
    {a : (v : X) → (IncidentEdge Γₜ v → G) → Fin d → ℂ}
    (ha : ∀ v, IsGIsometric (regularLegRepresentation (IncidentEdge Γₜ v))
      (regularSiteMap (a v))) (horizontal : Bool) (p : X) :
    ∃ W : Matrix (RV horizontal p → Fin d) (RV horizontal p → Fin d) ℂ,
      W ∈ Matrix.unitaryGroup (RV horizontal p → Fin d) ℂ ∧
      regionLocalTerm (R horizontal p) W ∈ Matrix.unitaryGroup (X → Fin d) ℂ ∧
      (∀ (reverse : Bool) (u : Edge Γₜ → G)
          (θ : {e : Edge Γₜ // IsRegionBoundaryEdge (R horizontal p) e} → G),
        (if reverse then W.conjTranspose else W) *ᵥ
          openRegionWeight (groupBondTensor (regularTwistedSite a u)) (R horizontal p)
            (fun f => Fintype.equivFin G (θ f)) =
        openRegionWeight (groupBondTensor (regularTwistedSite a
          (torusActualRouteFluxMove horizontal reverse p u))) (R horizontal p)
          (fun f => Fintype.equivFin G (θ f))) ∧
      ∀ (reverse : Bool) (u : Edge Γₜ → G),
        (if reverse then (regionLocalTerm (R horizontal p) W).conjTranspose
          else regionLocalTerm (R horizontal p) W) *ᵥ
          stateCoeff (groupBondTensor (regularTwistedSite a u)) =
        stateCoeff (groupBondTensor (regularTwistedSite a
          (torusActualRouteFluxMove horizontal reverse p u))) :=
  exists_unitary_regularActualCycleBidirectionalPermutation (R horizontal p) (T horizontal p)
    (tree_le horizontal p) (tree_isTree horizontal p) (φ horizontal p 0) a ha
    (regularTwoCycleMove (chord horizontal p 0) (chord horizontal p 1) (chord_ne horizontal p))
    (regularTwoCycleMove_conjugation _ _ _)

/-- One original-spin unitary per axis and position implements every vacant-face
move, and its adjoint every reverse move, on the literal actual assignment.
The unitary is chosen before all operators, boundary configurations and vacancy
proofs. Source: SCP10, Theorem 6.16, lines 2271–2305. -/
theorem IsGIsometric.exists_unitary_torusActualRouteFluxUpdate {d : ℕ}
    {a : (v : X) → (IncidentEdge Γₜ v → G) → Fin d → ℂ}
    (ha : ∀ v, IsGIsometric (regularLegRepresentation (IncidentEdge Γₜ v))
      (regularSiteMap (a v))) (horizontal : Bool) (p : X) :
    ∃ W : Matrix (RV horizontal p → Fin d) (RV horizontal p → Fin d) ℂ,
      W ∈ Matrix.unitaryGroup (RV horizontal p → Fin d) ℂ ∧
      regionLocalTerm (R horizontal p) W ∈ Matrix.unitaryGroup (X → Fin d) ℂ ∧
      (∀ (reverse : Bool) (u : Edge Γₜ → G),
        regularWalkHolonomy u (torusPlaquetteWalk
          (if reverse then p else offset horizontal p 1 0)) = 1 →
        ∀ θ : {e : Edge Γₜ // IsRegionBoundaryEdge (R horizontal p) e} → G,
          (if reverse then W.conjTranspose else W) *ᵥ
            openRegionWeight (groupBondTensor (regularTwistedSite a u)) (R horizontal p)
              (fun f => Fintype.equivFin G (θ f)) =
          openRegionWeight (groupBondTensor (regularTwistedSite a
            (torusActualRouteFluxUpdate horizontal reverse p u))) (R horizontal p)
            (fun f => Fintype.equivFin G (θ f))) ∧
      ∀ (reverse : Bool) (u : Edge Γₜ → G),
        regularWalkHolonomy u (torusPlaquetteWalk
          (if reverse then p else offset horizontal p 1 0)) = 1 →
        (if reverse then (regionLocalTerm (R horizontal p) W).conjTranspose
          else regionLocalTerm (R horizontal p) W) *ᵥ
          stateCoeff (groupBondTensor (regularTwistedSite a u)) =
        stateCoeff (groupBondTensor (regularTwistedSite a
          (torusActualRouteFluxUpdate horizontal reverse p u))) := by
  obtain ⟨W, hW, hglobal, hlocal, hact⟩ :=
    IsGIsometric.exists_unitary_torusActualRouteFluxMove ha horizontal p
  refine ⟨W, hW, hglobal, ?_, ?_⟩
  · intro reverse u hv θ
    rw [← torusActualRouteFluxMove_eq_update_of_vacancy horizontal reverse p u hv]
    exact hlocal reverse u θ
  · intro reverse u hv
    rw [← torusActualRouteFluxMove_eq_update_of_vacancy horizontal reverse p u hv]
    exact hact reverse u

end TNLean.PEPS
