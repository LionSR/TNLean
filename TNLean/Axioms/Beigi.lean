/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.RFP.Defs
import TNLean.MPS.ParentHamiltonian.Defs
import TNLean.MPS.ParentHamiltonian.GroundSpace
import TNLean.MPS.Periodic.Defs

/-!
# Beigi's ground-space theorem (axiomatized) and the RFP--NNCPH split

This module states two axioms that isolate the commutativity side of the
RFP--NNCPH comparison used in the proof of Theorem 3.10 of arXiv:1606.00608.
Following the proof in Section 3.3 of that paper, the two directions have very
different external provenance and so are stated here as **separate** axioms with
**separate** citations:

* `Axioms.rfp_to_nncph_commute` — RFP ⟹ the NNCPH commutation equations. Per
  arXiv:1606.00608 Section 3.3 (source line 1307), the proof derives this
  implication from the structural characterization theorem. It is therefore
  **not** gated on [Beigi 2012]; it is gated on the structural characterization
  of RFP tensors in arXiv:1606.00608, source lines 543--555.
* `Axioms.beigi_nncph_to_rfp` — all-chain nearest-neighbor commuting
  parent-Hamiltonian ground spaces ⟹ RFP. This is the present axiom-backed
  reverse implication. Per arXiv:1606.00608 Section 3.3 (line 1307): *"To prove
  the reverse, we will use [Beigi]"*. It is gated on S. Beigi,
  *J. Phys. A: Math. Theor.* **45** (2012) 025306 — the ground-space
  theorem for nearest-neighbor commuting 1D Hamiltonians with finite
  degeneracy.

To avoid a circular file dependency with `TNLean/MPS/ParentHamiltonian/Commuting.lean`,
the nearest-neighbor ground-space condition is expressed in this file via its
unfolded definition: pairwise commutativity of the two-site `localTerm`
projectors, the zero-energy equation for the periodic MPS vector, and the
kernel-spanning equation by the BNT vectors for every \(N>2\).

**Scope restriction (ground-state theorem):** The source theorem states a
three-way equivalence for tensors in canonical form. The reverse axiom below now
consumes the source parent-Hamiltonian ground-space condition, but it remains an
axiom-backed stand-in for Beigi's ground-space theorem and the identification of
the resulting locally orthogonal states with the BNT of the original tensor.
Documented in `docs/paper-gaps/cpsv16_nncph_ground_state_scope.tex`.

## Status

The two statements `Axioms.rfp_to_nncph_commute` and
`Axioms.beigi_nncph_to_rfp` below are introduced as **axioms** (not as
proved theorems). They are the two axioms introduced in this file. They are used
in the proofs of
`MPSTensor.rfp_implies_nncph` and `MPSTensor.nncph_implies_rfp` in
`TNLean/MPS/ParentHamiltonian/Commuting.lean`, respectively.

## TODO

Replace `Axioms.rfp_to_nncph_commute` with a Lean proof that uses the
structural characterization theorem in arXiv:1606.00608, source lines
543--555. The structural
construction in
`TNLean/MPS/RFP/CommutingBridge.lean` (`ProductPairBridge`) already
encodes the key combinatorial content; the missing piece is the
extraction of a `ProductPairBridge A` witness from `IsRFP A` and
normality. In that construction one may pass to a normalized
representative only for building the witness and establishing the NNCPH
conclusion, whose content is insensitive to this scaling; this is not
a claim that `IsRFP` itself is preserved under rescaling. This is
internal to the library.

Replace `Axioms.beigi_nncph_to_rfp` with a Lean proof that internalizes
S. Beigi's (2012) classification of ground spaces of nearest-neighbor
commuting Hamiltonians in 1D with finite degeneracy, exhibiting the
ground space as the span of locally orthogonal product-of-pairs
states. Formalization is expected to require:

1. A tensor-product and local-support formalism for `NSiteSpace d N` beyond the
   current `Cfg`-based representation.
2. A translation from the ground-space decomposition of [Beigi] to the
   RFP idempotence equation `transferMap A ∘ transferMap A =
   transferMap A` via zero correlation length.

## References

* S. Beigi, *J. Phys. A: Math. Theor.* **45** (2012) 025306 —
  ground-space characterization of 1D nearest-neighbor commuting
  Hamiltonians with finite degeneracy (the single-author paper
  explicitly cited as `\bibitem{Beigi}` in the source of
  arXiv:1606.00608).
* Cirac, Pérez-García, Schuch, Verstraete, "Matrix Product States and
  Projected Entangled Pair States: Concepts, Symmetries, and Theorems",
  arXiv:1606.00608 Section 3.3, the pure-state main theorem, the structural
  characterization theorem, Appendix B, and Appendix D.2.
-/

open scoped Matrix BigOperators

namespace Axioms

/-- **RFP ⟹ NNCPH commutation equations** in arXiv:1606.00608 Section 3.3
Theorem 3.10.

For a normal MPS tensor `A` in RFP, the two-site parent-Hamiltonian
`localTerm` projectors pairwise commute on every finite periodic chain
of length at least `2`.

Unfolded on the NNCPH side, the commutativity condition is exactly
`MPSTensor.IsNNCPH A N` (as defined in
`TNLean/MPS/ParentHamiltonian/Commuting.lean`); stating it here in
unfolded form avoids a circular import between this axiom module and
the file that consumes it.

**Citation.** This direction is derived in arXiv:1606.00608 Section 3.3
(source line 1307) from the structural characterization theorem (source lines
543--555). It does **not** depend on S. Beigi (2012). A structural
construction for the product-of-entangled-pairs form lives in
`TNLean/MPS/RFP/CommutingBridge.lean` as `ProductPairBridge`.

See the module docstring for the formalization plan. -/
axiom rfp_to_nncph_commute {d D : ℕ} [NeZero D]
    (A : MPSTensor d D) (_hNT : MPSTensor.IsNormal A)
    (_hRFP : MPSTensor.IsRFP A) :
    ∀ N : ℕ, 2 ≤ N → ∀ i j : Fin N,
      MPSTensor.localTerm A 2 N i * MPSTensor.localTerm A 2 N j =
        MPSTensor.localTerm A 2 N j * MPSTensor.localTerm A 2 N i

/-- All-chain NNCPH ground spaces ⟹ RFP, the present axiom-backed form of the
**NNCPH ⟹ RFP** direction of arXiv:1606.00608 Section 3.3 Theorem 3.10, gated on
[Beigi 2012].

For a normal left-canonical tensor `B` with BNT components `A_j`, assume that
for every chain length `N > 2`:

* the length-two parent terms commute;
* `V^{(N)}(B)` has zero energy for the nearest-neighbor parent Hamiltonian; and
* `ker H_2^{(N)}(B)` is spanned by the vectors `V^{(N)}(A_j)`.

Then the transfer map `transferMap B` is idempotent.

**Citation.** This is the only direction that uses the external result of
S. Beigi, *J. Phys. A: Math. Theor.* **45** (2012) 025306. Per
arXiv:1606.00608 Section 3.3 (source line 1307): *"To prove the reverse, we will
use [Beigi] where it is shown that the ground space of any nearest-neighbor
commuting Hamiltonian in a 1D spin chain with a finite (independent of system
size) degeneracy `g` is spanned by `g` states of the form … that are locally
orthogonal."* The source then identifies those states with the BNT of the
original tensor and applies the structural RFP characterization.

See the module docstring for the formalization plan. -/
axiom beigi_nncph_to_rfp {d D : ℕ} [NeZero D]
    (B : MPSTensor d D) {r : ℕ} {dim : Fin r → ℕ}
    (A : (j : Fin r) → MPSTensor d (dim j))
    (_hNT : MPSTensor.IsNormal B) (_hLeft : MPSTensor.IsLeftCanonical B)
    (_hNNCPH :
      ∀ N : ℕ, 2 < N → ∀ i j : Fin N,
        MPSTensor.localTerm B 2 N i * MPSTensor.localTerm B 2 N j =
          MPSTensor.localTerm B 2 N j * MPSTensor.localTerm B 2 N i)
    (_hZeroEnergy :
      ∀ N : ℕ, 2 < N → MPSTensor.IsFrustrationFree B 2 N (MPSTensor.mpv B))
    (_hGroundSpaceSpanning :
      ∀ N : ℕ, 2 < N →
        LinearMap.ker (MPSTensor.parentHamiltonian B 2 N) =
          MPSTensor.bntMPSVectorSpan A N) :
    MPSTensor.IsRFP B

end Axioms
