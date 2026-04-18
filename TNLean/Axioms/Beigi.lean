/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.RFP.Defs
import TNLean.MPS.ParentHamiltonian.Defs
import TNLean.MPS.Periodic.Defs

/-!
# Beigi's ground-space theorem (axiomatized) and the RFP ⟺ NNCPH split

This module records two axioms that together realize the equivalence
`IsRFP A ⇔ IsNNCPH A N` used in the proof of Theorem 3.10 of
arXiv:1606.00608. Following the proof in §3.3 of that paper, the two
directions have very different external provenance and so are
recorded here as **separate** axioms with **separate** citations:

* `Axioms.rfp_to_nncph_commute` — RFP ⟹ NNCPH. Per
  arXiv:1606.00608 §3.3 (line 1307 of the source): *"The implication
  RFP ⟹ NNCPH is trivial from Theorem [charact-MPS]"*. It is
  therefore **not** gated on [Beigi 2012]; it is gated only on
  Theorem 3.10 of arXiv:1606.00608 (the full structural
  characterization of RFPs via product-of-entangled-pairs).
* `Axioms.beigi_nncph_to_rfp` — NNCPH ⟹ RFP. This is the
  non-trivial direction. Per arXiv:1606.00608 §3.3 (line 1307): *"To
  prove the reverse, we will use [Beigi]"*. It is gated on S. Beigi,
  *J. Phys. A: Math. Theor.* **45** (2012) 025306 — the ground-space
  theorem for nearest-neighbor commuting 1D Hamiltonians with finite
  degeneracy.

To avoid a circular file dependency with
`TNLean/MPS/ParentHamiltonian/Commuting.lean`, the nearest-neighbor
commuting condition `IsNNCPH A N` is expressed in this file via its
unfolded definition: pairwise commutativity of the two-site `localTerm`
projectors.

## Status

The two statements `Axioms.rfp_to_nncph_commute` and
`Axioms.beigi_nncph_to_rfp` below are introduced as **axioms** (not as
proved theorems). They are the two axioms introduced by
`TNLean/Axioms/Beigi.lean`. Downstream, they are consumed by
`MPSTensor.rfp_implies_nncph` and `MPSTensor.nncph_implies_rfp` in
`TNLean/MPS/ParentHamiltonian/Commuting.lean`, respectively.

## TODO

Replace `Axioms.rfp_to_nncph_commute` with a Lean proof that uses the
product-of-entangled-pairs structural form (Appendix B of
arXiv:1606.00608). The scaffolding in
`TNLean/MPS/RFP/CommutingBridge.lean` (`ProductPairBridge`) already
encodes the key combinatorial content; the missing piece is the
extraction of a `ProductPairBridge A` witness from `IsRFP A` and
normality. In that construction one may pass to a normalized
representative only for building the witness / establishing the NNCPH
conclusion, whose content is insensitive to this scaling; this is not
a claim that `IsRFP` itself is preserved under rescaling. This is
internal to the library.

Replace `Axioms.beigi_nncph_to_rfp` with a Lean proof that internalizes
S. Beigi's (2012) classification of ground spaces of nearest-neighbor
commuting Hamiltonians in 1D with finite degeneracy, exhibiting the
ground space as the span of locally orthogonal product-of-pairs
states. Formalization is expected to require:

1. A tensor-product / local-support API on `NSiteSpace d N` beyond the
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
  arXiv:1606.00608 §3.3 Theorem 3.10, Appendix B and Appendix D.2.
-/

open scoped Matrix BigOperators

namespace Axioms

/-- **RFP ⟹ NNCPH** direction of arXiv:1606.00608 §3.3 Theorem 3.10.

For a normal MPS tensor `A` in RFP, the two-site parent-Hamiltonian
`localTerm` projectors pairwise commute on every finite periodic chain
of length at least `2`.

Unfolded on the NNCPH side, the commutativity condition is exactly
`MPSTensor.IsNNCPH A N` (as defined in
`TNLean/MPS/ParentHamiltonian/Commuting.lean`); stating it here in
unfolded form avoids a circular import between this axiom module and
the file that consumes it.

**Citation.** This direction is attributed in arXiv:1606.00608 §3.3
(source line 1307) as *"trivial from Theorem [charact-MPS]"*, i.e.,
from Theorem 3.10 itself. It does **not** depend on S. Beigi (2012);
it depends only on the product-of-entangled-pairs structural form
(Appendix B of arXiv:1606.00608). A scaffold for that structural form
lives in `TNLean/MPS/RFP/CommutingBridge.lean` as
`ProductPairBridge`.

See the module docstring for the formalization plan. -/
axiom rfp_to_nncph_commute {d D : ℕ} [NeZero D]
    (A : MPSTensor d D) (_hNT : MPSTensor.IsNormal A)
    (_hRFP : MPSTensor.IsRFP A) :
    ∀ N : ℕ, 2 ≤ N → ∀ i j : Fin N,
      MPSTensor.localTerm A 2 N i * MPSTensor.localTerm A 2 N j =
        MPSTensor.localTerm A 2 N j * MPSTensor.localTerm A 2 N i

/-- **NNCPH ⟹ RFP** direction of arXiv:1606.00608 §3.3 Theorem 3.10,
the non-trivial implication gated on [Beigi 2012].

For a normal MPS tensor `A` in left-canonical form, if the two-site
parent-Hamiltonian `localTerm` projectors pairwise commute on every
finite periodic chain of length at least `2`, then the transfer map
`transferMap A` is idempotent (equivalently, `MPSTensor.IsRFP A`
holds).

**Citation.** This is the only direction that uses the external
result of S. Beigi, *J. Phys. A: Math. Theor.* **45** (2012) 025306.
Per arXiv:1606.00608 §3.3 (source line 1307): *"To prove the reverse,
we will use [Beigi] where it is shown that the ground space of any
nearest-neighbor commuting Hamiltonian in a 1D spin chain with a
finite (independent of system size) degeneracy `g` is spanned by `g`
states of the form … that are locally orthogonal."*

See the module docstring for the formalization plan. -/
axiom beigi_nncph_to_rfp {d D : ℕ} [NeZero D]
    (A : MPSTensor d D) (_hNT : MPSTensor.IsNormal A)
    (_hLeft : MPSTensor.IsLeftCanonical A)
    (_hNNCPH :
      ∀ N : ℕ, 2 ≤ N → ∀ i j : Fin N,
        MPSTensor.localTerm A 2 N i * MPSTensor.localTerm A 2 N j =
          MPSTensor.localTerm A 2 N j * MPSTensor.localTerm A 2 N i) :
    MPSTensor.IsRFP A

end Axioms
