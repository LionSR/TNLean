/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.Compression.SourceGateRoot
import TNLean.Lattice.Compression.DistributedOperatorContraction
import Mathlib.Data.Fintype.Prod
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic

/-! # Dimensions and original-gate locality of the source density network

At each original nonempty gate occurrence, the star shares the complete
ordered ket and bra label. A source sample link shares one sample index.
The root is selected from the recorded participant set, so every constructed
link joins participants of its original gate. The original party type need
not be finite or nonempty.

The uniform dimension estimate is conditional on a supplied bound for the
original branch counts. It is an auxiliary finite-cardinality estimate.

Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 565–588.
-/

namespace TNLean.PEPS.PairEffect.SourceCircuit
open TNLean.PEPS.Approximation
variable {P : Type} {a b : Layout P}

open Classical in
/-- A density star at an original occurrence has the square of that gate's
branch count; a source sample link has exactly the sample size.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 565–579. -/
theorem card_alphabet_source_density (w : SourceCircuit a b) (k : ℕ)
    (e : DistributedOperatorContraction.Link
      (Finset.univ : Finset w.nonemptyGateLocations)
      (fun g ↦ w.participants g.1) (sourceGateRoot w)) :
    Fintype.card (DistributedOperatorContraction.alphabet
      (Finset.univ : Finset w.nonemptyGateLocations)
      (fun g ↦ w.participants g.1) (sourceGateRoot w)
      (fun g ↦ w.branchLabels g.1 × w.branchLabels g.1) k e) =
      match e.1.2 with
      | Sum.inl _ => Fintype.card (w.branchLabels e.1.1.1) ^ 2
      | Sum.inr _ => k := by
  simpa only [Fintype.card_prod, pow_two] using!
    DistributedOperatorContraction.card_alphabet
      (Finset.univ : Finset w.nonemptyGateLocations)
      (fun g ↦ w.participants g.1) (sourceGateRoot w)
      (fun g ↦ w.branchLabels g.1 × w.branchLabels g.1) k e

open Classical in
/-- A supplied uniform bound on the original branch counts bounds every
constructed density link by the maximum of its square and the sample size.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 565–579. -/
theorem card_alphabet_source_density_le (w : SourceCircuit a b) (k M : ℕ)
    (hM : ∀ g : w.nonemptyGateLocations, Fintype.card (w.branchLabels g.1) ≤ M)
    (e : DistributedOperatorContraction.Link
      (Finset.univ : Finset w.nonemptyGateLocations)
      (fun g ↦ w.participants g.1) (sourceGateRoot w)) :
    Fintype.card (DistributedOperatorContraction.alphabet
      (Finset.univ : Finset w.nonemptyGateLocations)
      (fun g ↦ w.participants g.1) (sourceGateRoot w)
      (fun g ↦ w.branchLabels g.1 × w.branchLabels g.1) k e) ≤ max (M ^ 2) k := by
  exact DistributedOperatorContraction.card_alphabet_le
    (Finset.univ : Finset w.nonemptyGateLocations)
    (fun g ↦ w.participants g.1) (sourceGateRoot w)
    (fun g ↦ w.branchLabels g.1 × w.branchLabels g.1) k (M ^ 2)
    (fun g _ ↦ by
      simpa only [Fintype.card_prod, pow_two] using mul_le_mul' (hM g) (hM g)) e

open Classical in
/-- Both endpoints of each density-network link belong to its original gate's
participant set. Root membership is derived from the recorded nonempty gate.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 581–588. -/
theorem distributedLinkParties_source_subset (w : SourceCircuit a b)
    (e : DistributedOperatorContraction.Link
      (Finset.univ : Finset w.nonemptyGateLocations)
      (fun g ↦ w.participants g.1) (sourceGateRoot w)) :
    distributedLinkParties (sourceGateRoot w) e.1 ⊆ w.participants e.1.1.1 :=
  distributedLinkParties_subset (Finset.univ : Finset w.nonemptyGateLocations)
    (fun g ↦ w.participants g.1) (sourceGateRoot w)
    (fun g _ ↦ sourceGateRoot_mem w g) e.2

end TNLean.PEPS.PairEffect.SourceCircuit
