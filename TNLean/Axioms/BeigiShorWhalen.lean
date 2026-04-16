/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.RFP.Defs
import TNLean.MPS.ParentHamiltonian.Defs
import TNLean.MPS.Periodic.Defs

/-!
# Beigi–Shor–Whalen theorem (axiomatized)

This module records the **Beigi–Shor–Whalen theorem** (CMP 312, 2012) as a
trusted external axiom. The theorem characterizes the ground spaces of
frustration-free commuting nearest-neighbor Hamiltonians on a 1D chain of
qudits with finite degeneracy: such ground spaces are spanned by
product-like states `U^{⊗N} |φ⟩^{⊗N}` on consecutive pairs of sites, with
locally orthogonal two-site support.

For the MPS development in this library (arXiv:1606.00608 §3.3, Theorem 3.10)
we need the specialized consequence that — for a normal, left-canonical MPS
tensor — the commuting nearest-neighbor parent Hamiltonian condition is
equivalent to the renormalization fixed-point condition on the transfer map.
This is the direct downstream usage of the Beigi–Shor–Whalen ground-space
characterization.

To avoid a circular file dependency with
`TNLean/MPS/ParentHamiltonian/Commuting.lean`, the nearest-neighbor
commuting condition `IsNNCPH A N` is expressed in this file via its
unfolded definition: pairwise commutativity of the two-site `localTerm`
projectors.

## Status

The statement `Axioms.beigi_shor_whalen` below is introduced as an **axiom**
(not a proved theorem). It is the only new axiom introduced by the
`TNLean/Axioms/BeigiShorWhalen.lean` module. Downstream, it is consumed by
`MPSTensor.rfp_implies_nncph` and `MPSTensor.nncph_implies_rfp` in
`TNLean/MPS/ParentHamiltonian/Commuting.lean`.

## TODO

Replace `Axioms.beigi_shor_whalen` with a Lean proof that internalizes the
full Beigi–Shor–Whalen argument: a classification of 1D commuting
nearest-neighbor projective Hamiltonians with finite ground-space
degeneracy, exhibiting the ground space as the span of product-of-pairs
states with the appropriate local-orthogonality structure. The CMP paper
uses quasi-local unitary rotations together with a careful analysis of the
support of commuting local projectors. Formalization is expected to
require:

1. A tensor-product / local-support API on `NSiteSpace d N` beyond the
   current `Cfg`-based representation.
2. An encoding of the local orthogonality of the two-site amplitudes (the
   `ProductPairBridge` witnesses in
   `TNLean/MPS/RFP/CommutingBridge.lean` provide a partial scaffold).
3. A translation from the Beigi–Shor–Whalen ground-space decomposition to
   the RFP idempotence equation `transferMap A ∘ transferMap A =
   transferMap A` via zero correlation length.

## References

* Beigi, Shor, Whalen, "The Quantum Double Model as a Commuting Hamiltonian
  Model" (title and journal as listed for CMP 312 (2012) 435–460) —
  ground-space structure of 1D commuting nearest-neighbor Hamiltonians with
  finite degeneracy.
* Cirac, Pérez-García, Schuch, Verstraete, "Matrix Product States and
  Projected Entangled Pair States: Concepts, Symmetries, and Theorems",
  arXiv:1606.00608 §3.3 Theorem 3.10, Appendix B and Appendix D.2.
-/

open scoped Matrix BigOperators

namespace Axioms

/-- **Beigi–Shor–Whalen theorem** (CMP 312 (2012) 435–460), specialized to the
MPS setting of arXiv:1606.00608 §3.3.

For a normal MPS tensor `A` in left-canonical form, the renormalization
fixed-point condition `MPSTensor.IsRFP A` is equivalent to the condition
that the two-site parent-Hamiltonian `localTerm` projectors pairwise commute
on every finite periodic chain of length at least `2`.

Unfolded on the NNCPH side, the commutativity condition is exactly
`MPSTensor.IsNNCPH A N` (as defined in
`TNLean/MPS/ParentHamiltonian/Commuting.lean`); stating it here in
unfolded form avoids a circular import between this axiom module and the
file that consumes it.

**Mathematical content.** The forward direction (RFP ⟹ NNCPH) follows from
the product-of-entangled-pairs decomposition of Appendix B (Lemma B.1): an
RFP tensor generates a product-of-pairs state whose parent Hamiltonian
projects onto independent bond projectors, and these commute. The backward
direction (NNCPH ⟹ RFP) is the non-trivial consequence of the
Beigi–Shor–Whalen classification: a 1D frustration-free commuting
nearest-neighbor Hamiltonian with finitely degenerate ground space has
ground states of the form `U^{⊗N} |φ⟩^{⊗N}` with pairwise locally
orthogonal two-site amplitudes. For a left-canonical MPS realization, this
structural form forces zero correlation length and hence transfer-map
idempotence.

This axiom combines both directions into a single statement that is
consumed, in both directions, by
`MPSTensor.rfp_implies_nncph` and `MPSTensor.nncph_implies_rfp` in
`TNLean/MPS/ParentHamiltonian/Commuting.lean`.

See the module docstring for the formalization plan. -/
axiom beigi_shor_whalen {d D : ℕ} [NeZero D]
    (A : MPSTensor d D) (_hNT : MPSTensor.IsNormal A)
    (_hLeft : MPSTensor.IsLeftCanonical A) :
    MPSTensor.IsRFP A ↔
      ∀ N : ℕ, 2 ≤ N → ∀ i j : Fin N,
        MPSTensor.localTerm A 2 N i * MPSTensor.localTerm A 2 N j =
          MPSTensor.localTerm A 2 N j * MPSTensor.localTerm A 2 N i

end Axioms
