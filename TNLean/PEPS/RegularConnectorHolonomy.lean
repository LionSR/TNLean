/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.RegularWalkHolonomy
import TNLean.Algebra.ConjClassesConjugation

/-!
# Flux loops compared along actual connecting walks

A loop at one vertex can be compared with another loop by following an actual
walk from a common base vertex, traversing the loop, and returning along the
reverse walk. Its transport is conjugated by the connecting transport. The
conjugacy class is unchanged. Traversing two such based loops gives the product
of their transported fluxes, in the reverse order of traversal.

Source: Schuch, Cirac, and Pérez-García, arXiv:1001.3807, the joint-flux and
alignment discussion, local source lines 2387–2415. These are auxiliary walk
identities. They do not identify a particular torus path with the paper's braid.
-/

namespace TNLean.PEPS

variable {V : Type*} [LinearOrder V] {Γ : SimpleGraph V}
variable {G : Type*} [Group G]

/-- Following a connecting walk, traversing a loop, and returning conjugates
the loop transport by the inverse connecting transport.
Source: SCP10, joint-flux alignment, lines 2387–2415; auxiliary walk identity. -/
theorem regularWalkHolonomy_transportLoop (u : Edge Γ → G) {o v : V}
    (p : Γ.Walk o v) (l : Γ.Walk v v) :
    regularWalkHolonomy u ((p.append l).append p.reverse) =
      (regularWalkHolonomy u p)⁻¹ * regularWalkHolonomy u l *
        regularWalkHolonomy u p := by
  simp only [regularWalkHolonomy_append, regularWalkHolonomy_reverse, mul_assoc]

/-- Transport to a common base vertex leaves the measured conjugacy class
unchanged. Source: SCP10, lines 2387–2415; auxiliary walk identity. -/
theorem regularWalkHolonomy_transportLoop_conjClass (u : Edge Γ → G) {o v : V}
    (p : Γ.Walk o v) (l : Γ.Walk v v) :
    ConjClasses.mk (regularWalkHolonomy u ((p.append l).append p.reverse)) =
      ConjClasses.mk (regularWalkHolonomy u l) := by
  rw [regularWalkHolonomy_transportLoop]
  simpa only [inv_inv] using
    ConjClasses.mk_conjugate (regularWalkHolonomy u l) (regularWalkHolonomy u p)⁻¹

/-- Traversing the second transported loop before the first gives the first
based flux times the second based flux. Both connecting walks are actual graph
walks. Source: SCP10, joint-flux product, lines 2387–2415; auxiliary walk identity. -/
theorem regularWalkHolonomy_twoTransportedLoops (u : Edge Γ → G) {o v w : V}
    (p : Γ.Walk o v) (a : Γ.Walk v v) (q : Γ.Walk o w) (b : Γ.Walk w w) :
    regularWalkHolonomy u
      (((q.append b).append q.reverse).append ((p.append a).append p.reverse)) =
      ((regularWalkHolonomy u p)⁻¹ * regularWalkHolonomy u a *
        regularWalkHolonomy u p) *
      ((regularWalkHolonomy u q)⁻¹ * regularWalkHolonomy u b *
        regularWalkHolonomy u q) := by
  rw [regularWalkHolonomy_append, regularWalkHolonomy_transportLoop,
    regularWalkHolonomy_transportLoop]

end TNLean.PEPS
