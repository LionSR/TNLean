/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.Commuting
import TNLean.MPS.RFP.AppendixBStructuralData

/-!
# Appendix B commuting parent-Hamiltonian bridge

This module connects Appendix B structural extraction data to the generic
parent-Hamiltonian interfaces. It contains the RFP-specific conditional bridge
theorems, while `TNLean.MPS.ParentHamiltonian.Commuting` remains independent of
the RFP layer.

## Main statements

* `rfp_implies_nncph_of_appendixBExtraction`
* `rfp_implies_nncph_ground_state_of_appendixBExtraction`
* `rfp_implies_hasNNCPHGroundSpaces_of_appendixBExtraction_of_groundSpaceSpanning`

## References

The statements implement the conditional Appendix B route for Theorem 3.10(i)⇒(iii)
of Cirac, Pérez-García, Schuch, and Verstraete, arXiv:1606.00608.
-/

open scoped Matrix BigOperators

namespace MPSTensor

variable {d D : ℕ}

/-- Conditional internal theorem for Theorem 3.10(i)⟹(iii).

A normal left-canonical RFP tensor has the Appendix B structural form
\(A^i = X\Lambda U^iX^{-1}\) by `AppendixBStructuralData.ofRFP`. If the
associated two-site amplitude gives the even-chain physical-pair factorization
and the two-site parent terms are identified with commuting
idempotents, then the nearest-neighbor parent Hamiltonian is commuting on every
finite chain of length greater than two.

This theorem does not use an external commutation assumption.  The extraction
hypothesis includes a physical-pair coefficient factorization; the later theorem
`rfp_implies_nncph_of_leftCanonical` obtains the commutation conclusion directly
from the Appendix B structural datum. -/
theorem rfp_implies_nncph_of_appendixBExtraction (A : MPSTensor d D) [NeZero D]
    (hRFP : IsTransferIdempotent A) (hNT : Kraus.IsNormal A) (hLeft : IsLeftCanonical A)
    (hExtract : AppendixBProductPairExtraction
      (AppendixBStructuralData.ofRFP A hNT hRFP hLeft))
    (N : ℕ) (hN : 2 < N) :
    IsNNCPH A N :=
  hExtract.commuting_twoSite_localTerms N hN

/-- Conditional ground-vector form of Theorem 3.10(i)⟹(iii).

Under the same Appendix B conditional hypotheses used for
`rfp_implies_nncph_of_appendixBExtraction`, the nearest-neighbor parent terms
commute and the periodic MPS vector \(V^{(N)}(A)\) has zero energy. This adds
only the standard parent-Hamiltonian frustration-free equation; it does not
assert the source ground-space spanning clause from Definition 3.9.

**Scope restriction (ground vector):** The source implication uses the full
nearest-neighbor commuting parent Hamiltonian condition, including the
ground-space spanning clause. This theorem proves only the ground-vector
zero-energy equation under the Appendix B extraction hypothesis. Documented in
`docs/paper-gaps/cpsv16_nncph_ground_state_scope.tex`. -/
theorem rfp_implies_nncph_ground_state_of_appendixBExtraction
    (A : MPSTensor d D) [NeZero D]
    (hRFP : IsTransferIdempotent A) (hNT : Kraus.IsNormal A) (hLeft : IsLeftCanonical A)
    (hExtract : AppendixBProductPairExtraction
      (AppendixBStructuralData.ofRFP A hNT hRFP hLeft))
    (N : ℕ) (hN : 2 < N) :
    IsNNCPHGroundState A N :=
  have hNN := rfp_implies_nncph_of_appendixBExtraction A hRFP hNT hLeft hExtract N hN
  hNN.isNNCPHGroundState (by omega)

/-- Conditional full source form of Theorem 3.10(i)⟹(iii).

Under the Appendix B conditional hypotheses used above, a normal
left-canonical RFP tensor has the all-chain commutation and zero-energy
equations for nearest-neighbor parent terms. If, in addition, the
Definition 3.9 ground-space spanning equation is supplied for a chosen BNT
family \(A_j\), then the full all-chain NNCPH ground-space condition holds.

This theorem does not use an external commutation assumption; beyond the conditional
Appendix B hypotheses, it assumes the source ground-space spanning clause.

**Scope restriction (spanning clause assumed):** The source implication proves
the ground-space spanning equation; this theorem assumes it via
`HasParentHamiltonianGroundSpaceSpanning`. Documented in
`docs/paper-gaps/cpsv16_nncph_ground_state_scope.tex`. -/
theorem rfp_implies_hasNNCPHGroundSpaces_of_appendixBExtraction_of_groundSpaceSpanning
    (B : MPSTensor d D) [NeZero D]
    (hRFP : IsTransferIdempotent B) (hNT : Kraus.IsNormal B) (hLeft : IsLeftCanonical B)
    (hExtract : AppendixBProductPairExtraction
      (AppendixBStructuralData.ofRFP B hNT hRFP hLeft))
    {r : ℕ} {dim : Fin r → ℕ} {A : (j : Fin r) → MPSTensor d (dim j)}
    (hSpan : HasParentHamiltonianGroundSpaceSpanning B 2 A) :
    HasNNCPHGroundSpaces B A :=
  hExtract.toProductPairBridge.hasNNCPHGroundSpaces_of_groundSpaceSpanning hSpan

end MPSTensor
