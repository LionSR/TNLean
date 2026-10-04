/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.RegularClosedGauge
import Mathlib.Combinatorics.SimpleGraph.Walk.Operations

/-!
# Nonabelian transport along native graph walks

An ordered bond operator transports from its smaller endpoint to its larger
endpoint; the reverse step uses its inverse. Along a walk, the first step acts
first, so its operator is the rightmost factor. Endpoint gauges telescope in
this ordered product. Closed-walk holonomies therefore change by conjugation.
These identities require no commutativity or finiteness assumptions.

Source: Schuch, Cirac, and Pérez-García, arXiv:1001.3807, seam deformation in
`eq:2d:move-strings`, local source lines 1622–1647, and the accessible complement
cycle argument, lines 1935–1990. This module supplies walk words; it does not
assume a relation between complement holonomies and boundary transports.

## References

- [arXiv:1001.3807](https://arxiv.org/abs/1001.3807) -- N. Schuch, J. I. Cirac,
  D. Pérez-García, *PEPS as ground states: degeneracy and topology*
-/

namespace TNLean.PEPS

variable {V : Type*} [LinearOrder V] {Γ : SimpleGraph V}
variable {G : Type*} [Group G]

/-- Transport along an adjacent pair in the native ordered-edge convention.
The reverse of the ordered orientation uses the inverse operator. -/
def regularDirectedTransport (u : Edge Γ → G) {v w : V} (h : Γ.Adj v w) : G :=
  if v < w then u (Edge.ofAdj h) else (u (Edge.ofAdj h))⁻¹

/-- A step from the tail to the head uses the assigned bond operator. -/
theorem regularDirectedTransport_of_lt (u : Edge Γ → G) {v w : V}
    (h : Γ.Adj v w) (hvw : v < w) :
    regularDirectedTransport u h = u ⟨(v, w), hvw, h⟩ := by
  simp only [regularDirectedTransport, ite_eq_left hvw, Edge.ofAdj_of_lt h hvw]

/-- A step from the head to the tail uses the inverse bond operator. -/
theorem regularDirectedTransport_of_gt (u : Edge Γ → G) {v w : V}
    (h : Γ.Adj v w) (hwv : w < v) :
    regularDirectedTransport u h = (u ⟨(w, v), hwv, h.symm⟩)⁻¹ := by
  simp only [regularDirectedTransport, ite_eq_right (not_lt.mpr hwv.le),
    Edge.ofAdj_of_gt h hwv]

/-- Reversing a single step inverts its operator. -/
theorem regularDirectedTransport_symm (u : Edge Γ → G) {v w : V}
    (h : Γ.Adj v w) : regularDirectedTransport u h.symm = (regularDirectedTransport u h)⁻¹ := by
  rcases lt_or_gt_of_ne h.ne with hvw | hwv
  · rw [regularDirectedTransport_of_lt u h hvw,
      regularDirectedTransport_of_gt u h.symm hvw]
  · rw [regularDirectedTransport_of_gt u h hwv,
      regularDirectedTransport_of_lt u h.symm hwv, inv_inv]

/-- A gauge changes a single-step operator only at its two endpoints.
Source: SCP10, seam deformation, lines 1622–1647. -/
theorem regularDirectedTransport_gauge (u : Edge Γ → G) (k : V → G)
    {v w : V} (h : Γ.Adj v w) :
    regularDirectedTransport (regularVertexGaugeOperators k u) h =
      (k w)⁻¹ * regularDirectedTransport u h * k v := by
  rcases lt_or_gt_of_ne h.ne with hvw | hwv
  · rw [regularDirectedTransport_of_lt _ h hvw, regularDirectedTransport_of_lt u h hvw]
    rfl
  · rw [regularDirectedTransport_of_gt _ h hwv, regularDirectedTransport_of_gt u h hwv]
    unfold regularVertexGaugeOperators
    group

/-- Reverse-ordered product of the directed bond operators along an actual graph
walk. The first traversed edge acts first and is therefore the rightmost factor. -/
def regularWalkHolonomy (u : Edge Γ → G) {v w : V} : Γ.Walk v w → G
  | .nil => 1
  | .cons h p => regularWalkHolonomy u p * regularDirectedTransport u h

/-- The empty walk has identity transport. -/
@[simp]
theorem regularWalkHolonomy_nil (u : Edge Γ → G) (v : V) :
    regularWalkHolonomy u (.nil : Γ.Walk v v) = 1 := rfl

/-- The initial step is the rightmost factor of a nonempty walk's transport. -/
theorem regularWalkHolonomy_cons (u : Edge Γ → G) {v w z : V}
    (h : Γ.Adj v w) (p : Γ.Walk w z) :
    regularWalkHolonomy u (.cons h p) = regularWalkHolonomy u p * regularDirectedTransport u h :=
  rfl

/-- Appending a walk multiplies its transport on the left. -/
theorem regularWalkHolonomy_append (u : Edge Γ → G) {v w z : V}
    (p : Γ.Walk v w) (q : Γ.Walk w z) :
    regularWalkHolonomy u (p.append q) = regularWalkHolonomy u q * regularWalkHolonomy u p := by
  induction p with
  | nil => simp only [SimpleGraph.Walk.nil_append, regularWalkHolonomy_nil, mul_one]
  | cons h p ih =>
    simp only [SimpleGraph.Walk.cons_append, regularWalkHolonomy_cons, ih, mul_assoc]

/-- Reversing a walk inverts its transport. -/
theorem regularWalkHolonomy_reverse (u : Edge Γ → G) {v w : V} (p : Γ.Walk v w) :
    regularWalkHolonomy u p.reverse = (regularWalkHolonomy u p)⁻¹ := by
  induction p with
  | nil => simp only [SimpleGraph.Walk.reverse_nil, regularWalkHolonomy_nil, inv_one]
  | cons h p ih =>
    rw [SimpleGraph.Walk.reverse_cons, regularWalkHolonomy_append, regularWalkHolonomy_cons,
      regularWalkHolonomy_nil, one_mul, regularDirectedTransport_symm, ih,
      regularWalkHolonomy_cons, mul_inv_rev]

/-- Endpoint gauges telescope along any native walk.
Source: SCP10, seam deformation, lines 1622–1647, and complement cycle records,
lines 1935–1990. -/
theorem regularWalkHolonomy_gauge (u : Edge Γ → G) (k : V → G)
    {v w : V} (p : Γ.Walk v w) :
    regularWalkHolonomy (regularVertexGaugeOperators k u) p =
      (k w)⁻¹ * regularWalkHolonomy u p * k v := by
  induction p with
  | nil => simp only [regularWalkHolonomy_nil, mul_one, inv_mul_cancel]
  | cons h p ih =>
    rw [regularWalkHolonomy_cons, ih, regularDirectedTransport_gauge, regularWalkHolonomy_cons]
    group

/-- A closed-walk holonomy transforms by conjugation at its base vertex. -/
theorem regularWalkHolonomy_gauge_loop (u : Edge Γ → G) (k : V → G)
    {v : V} (p : Γ.Walk v v) :
    regularWalkHolonomy (regularVertexGaugeOperators k u) p =
      (k v)⁻¹ * regularWalkHolonomy u p * k v := regularWalkHolonomy_gauge u k p

/-- A native gradient has endpoint transport, independently of the chosen walk. -/
theorem regularWalkHolonomy_gradient (k : V → G) {v w : V} (p : Γ.Walk v w) :
    regularWalkHolonomy (fun e => k e.1.2 * (k e.1.1)⁻¹) p = k w * (k v)⁻¹ := by
  have hstep {v w : V} (h : Γ.Adj v w) :
      regularDirectedTransport (fun e => k e.1.2 * (k e.1.1)⁻¹) h = k w * (k v)⁻¹ := by
    rcases lt_or_gt_of_ne h.ne with hvw | hwv
    · rw [regularDirectedTransport_of_lt _ h hvw]
    · rw [regularDirectedTransport_of_gt _ h hwv]
      group
  induction p with
  | nil => simp only [regularWalkHolonomy_nil, mul_inv_cancel]
  | cons h p ih =>
    rw [regularWalkHolonomy_cons, ih, hstep]
    group

/-- Every closed walk in a native gradient has identity holonomy. -/
theorem regularWalkHolonomy_gradient_loop (k : V → G) {v : V} (p : Γ.Walk v v) :
    regularWalkHolonomy (fun e => k e.1.2 * (k e.1.1)⁻¹) p = 1 := by
  rw [regularWalkHolonomy_gradient, mul_inv_cancel]

end TNLean.PEPS
