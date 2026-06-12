/- 
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.ParentHamiltonian.Basic
import TNLean.MPS.Periodic.Defs
import TNLean.MPS.RFP.CommutingBridge
import TNLean.MPS.RFP.Defs
import TNLean.MPS.RFP.StructuralForm
import TNLean.Axioms.Beigi

/-!
# Commuting parent Hamiltonians

This file records the commutativity clauses for parent Hamiltonians and the
length-two specialization used in the nearest-neighbor commuting parent
Hamiltonian part of arXiv:1606.00608.

## Main definitions

* `MPSTensor.IsCommutingParentHam A L N` — the local terms of the parent
  Hamiltonian on `N` sites with block length `L` mutually commute.
* `MPSTensor.IsNNCPH A N` — length-two commutativity of the translated parent
  interaction terms.
* `MPSTensor.IsNNCPHGroundState A N` — the nearest-neighbor local terms commute
  and annihilate the periodic MPS vector.

## Main results

* `MPSTensor.IsCommutingParentHam.ham_comm_localTerm` — if local terms commute,
  the full Hamiltonian commutes with each local term.
* `MPSTensor.ProductPairBridge.isNNCPH` — if the two-site local terms are
  projectors `pᵢ` with `pᵢpⱼ = pⱼpᵢ`, then the parent Hamiltonian satisfies
  `hᵢhⱼ = hⱼhᵢ`.
* `MPSTensor.rfp_implies_nncph_of_appendixBExtraction` — a conditional theorem
  deriving NNCPH from the Appendix B structural form
  `Aᵢ = XΛUᵢX⁻¹`, the even-chain product-of-pairs factorization, and the
  two-site projector identities, without invoking
  `Axioms.rfp_to_nncph_commute`.
* `MPSTensor.rfp_implies_nncph` — construction for the RFP `⟹` NNCPH direction of
  Theorem 3.10.
* `MPSTensor.rfp_implies_nncph_ground_state` — the same direction with the
  frustration-free ground-state condition for the MPS vector included.
* `MPSTensor.nncph_implies_rfp` — construction for the NNCPH `⟹` RFP direction of
  Theorem 3.10.

## References

* arXiv:1606.00608, Section 3.3 Definition 3.9, Theorem 3.10
* S. Beigi, *J. Phys. A: Math. Theor.* **45** (2012) 025306 —
  ground-space characterization for commuting nearest-neighbor
  Hamiltonians in 1D (consumed only in the `NNCPH ⟹ RFP` direction)
-/

open scoped Matrix BigOperators

namespace MPSTensor

variable {d D : ℕ}

/-- A parent Hamiltonian has **commuting** local terms when the translated
interaction projectors commute.

See arXiv:1606.00608, Definition 3.9. The source writes the local translated
condition as $[\tau_j(P_L),P_L]=0$ for the interacting translates; this
predicate records the resulting pairwise commutativity of the translated local
terms. The source definition of a parent Hamiltonian also includes the
ground-space spanning condition. -/
def IsCommutingParentHam (A : MPSTensor d D) (L N : ℕ) : Prop :=
  ∀ i j : Fin N,
    localTerm A L N i * localTerm A L N j = localTerm A L N j * localTerm A L N i

/-- **Nearest-neighbor commuting parent Hamiltonian** (NNCPH): the length-two
commutativity clause for the translated parent interaction terms.

See arXiv:1606.00608, Definition 3.9. The source definition of a parent
Hamiltonian also includes the ground-space spanning condition, which is not part
of this predicate. -/
def IsNNCPH (A : MPSTensor d D) (N : ℕ) : Prop :=
  IsCommutingParentHam A 2 N

/-- The ground-state condition for a nearest-neighbor commuting
parent Hamiltonian: the length-two local terms commute and annihilate the
periodic MPS vector V^{(N)}(A).

See arXiv:1606.00608, Theorem 3.10(iii), source line 539. This predicate records
the commutativity and annihilation equations for the MPS vector. The full source
parent-Hamiltonian condition also includes the ground-space spanning assertion
from Definition 3.9, and Theorem 3.10 also includes the canonical-form and
zero-correlation-length equivalences.

**Scope restriction (ground vector):** This is the zero-energy ground-vector
clause for the canonical parent interaction, not the full source ground-space
spanning condition. Documented in
`docs/paper-gaps/cpsv16_nncph_ground_state_scope.tex`. -/
def IsNNCPHGroundState (A : MPSTensor d D) (N : ℕ) : Prop :=
  IsNNCPH A N ∧ IsFrustrationFree A 2 N (mpv A)

/-- NNCPH is a special case of commuting parent Hamiltonian. -/
theorem IsNNCPH.isCommutingParentHam {A : MPSTensor d D} {N : ℕ} (h : IsNNCPH A N) :
    IsCommutingParentHam A 2 N :=
  h

/-- A nearest-neighbor commuting parent-Hamiltonian ground state has commuting
length-two local terms. -/
theorem IsNNCPHGroundState.isNNCPH {A : MPSTensor d D} {N : ℕ}
    (h : IsNNCPHGroundState A N) :
    IsNNCPH A N :=
  h.1

/-- A nearest-neighbor commuting parent-Hamiltonian ground state is
frustration-free for the length-two parent Hamiltonian. -/
theorem IsNNCPHGroundState.isFrustrationFree {A : MPSTensor d D} {N : ℕ}
    (h : IsNNCPHGroundState A N) :
    IsFrustrationFree A 2 N (mpv A) :=
  h.2

/-- If the length-two parent terms commute and N ≥ 2, then the periodic MPS
vector is a ground state of a nearest-neighbor commuting parent Hamiltonian. -/
theorem IsNNCPH.isNNCPHGroundState {A : MPSTensor d D} {N : ℕ}
    (h : IsNNCPH A N) (hN : 2 ≤ N) :
    IsNNCPHGroundState A N :=
  ⟨h, parentHamiltonian_frustrationFree A 2 N hN⟩

/-- If the two-site parent terms are idempotents `pᵢ` with
`pᵢpⱼ = pⱼpᵢ`, then the nearest-neighbor parent Hamiltonian is commuting on
that finite chain. -/
theorem HasProductPairLocalProjectors.isNNCPH {A : MPSTensor d D} {N : ℕ}
    (hPair : HasProductPairLocalProjectors A N) :
    IsNNCPH A N :=
  hPair.commuting_twoSite_localTerms

/-- The product-of-pairs equations and the two-site projector identities give
NNCPH on each finite chain. -/
theorem ProductPairBridge.isNNCPH {A : MPSTensor d D} (hBridge : ProductPairBridge A)
    (N : ℕ) :
    IsNNCPH A N :=
  (hBridge.localProjectors N).isNNCPH

/-- Conditional internal theorem for Theorem 3.10(i)⟹(iii).

A normal left-canonical RFP tensor has the Appendix B structural form
`Aᵢ = XΛUᵢX⁻¹` by `AppendixBStructuralData.ofRFP`. If the associated two-site
amplitude gives the even-chain factorization and the two-site parent terms are
identified with commuting idempotents, then the nearest-neighbor parent
Hamiltonian is commuting on every finite chain.

This theorem does not use `Axioms.rfp_to_nncph_commute`; it states the precise
conditional theorem left after the structural form has been internalized. -/
theorem rfp_implies_nncph_of_appendixBExtraction (A : MPSTensor d D) [NeZero D]
    (hRFP : IsRFP A) (hNT : IsNormal A) (hLeft : IsLeftCanonical A)
    (hExtract : AppendixBProductPairExtraction
      (AppendixBStructuralData.ofRFP A hNT hRFP hLeft))
    (N : ℕ) :
    IsNNCPH A N :=
  commuting_twoSite_localTerms_of_rfp_of_appendixBExtraction
    A hNT hRFP hLeft hExtract N

/-- The commuting condition is symmetric: if `h i j` holds, then `h j i` holds. -/
theorem IsCommutingParentHam.symm {A : MPSTensor d D} {L N : ℕ}
    (h : IsCommutingParentHam A L N) (i j : Fin N) :
    localTerm A L N j * localTerm A L N i = localTerm A L N i * localTerm A L N j :=
  (h i j).symm

/-- If the parent Hamiltonian commutes, then the Hamiltonian commutes with
each local term. -/
theorem IsCommutingParentHam.ham_comm_localTerm {A : MPSTensor d D} {L N : ℕ}
    (_h : IsCommutingParentHam A L N) (i : Fin N) :
    parentHamiltonian A L N * localTerm A L N i =
      localTerm A L N i * parentHamiltonian A L N := by
  simp only [parentHamiltonian, Finset.sum_mul, Finset.mul_sum]
  congr 1
  ext j : 1
  exact _h j i

/-- **Theorem 3.10(i)⟹(iii)** (arXiv:1606.00608): RFP implies NNCPH.
A normal renormalization fixed-point tensor has a nearest-neighbor
commuting parent Hamiltonian.

Per arXiv:1606.00608 Section 3.3 (source line 1307), this direction is
*"trivial from Theorem [charact-MPS]"*; it therefore does not depend
on S. Beigi (2012). It is conditioned only on the product-of-entangled-pairs
structural form (Appendix B), stated here as
`Axioms.rfp_to_nncph_commute`. -/
theorem rfp_implies_nncph (A : MPSTensor d D) [NeZero D]
    (hRFP : IsRFP A) (hNT : IsNormal A)
    (N : ℕ) (hN : 2 ≤ N) :
    IsNNCPH A N := by
  classical
  unfold IsNNCPH IsCommutingParentHam
  intro i j
  exact Axioms.rfp_to_nncph_commute A hNT hRFP N hN i j

/-- **Theorem 3.10(i)⟹(iii)** (arXiv:1606.00608), ground-vector form:
RFP implies that the periodic MPS vector is a ground state of a
nearest-neighbor commuting parent Hamiltonian on every chain of length at least
two.

This theorem adds the frustration-free ground-vector equation to
`rfp_implies_nncph`.

**Scope restriction (ground vector):** The source theorem states the
three-way equivalence for canonical-form tensors and requires the full
parent-Hamiltonian ground-space condition. This theorem proves only the
commutation and zero-energy equations for $V^{(N)}(A)$. Documented in
`docs/paper-gaps/cpsv16_nncph_ground_state_scope.tex`. -/
theorem rfp_implies_nncph_ground_state (A : MPSTensor d D) [NeZero D]
    (hRFP : IsRFP A) (hNT : IsNormal A)
    (N : ℕ) (hN : 2 ≤ N) :
    IsNNCPHGroundState A N :=
  (rfp_implies_nncph A hRFP hNT N hN).isNNCPHGroundState hN

/-- **Theorem 3.10(iii)⟹(i)** (arXiv:1606.00608): NNCPH implies RFP.
Gated on S. Beigi, *J. Phys. A: Math. Theor.* **45** (2012) 025306 —
the ground-space characterization of commuting nearest-neighbor 1D
Hamiltonians with finite degeneracy (`Axioms.beigi_nncph_to_rfp`).

**Scope restriction (ground-space input):** The source hypothesis is that
$|V^{(N)}(A)\rangle$ is a ground state of a nearest-neighbor commuting parent
Hamiltonian for every $N>2$, including the parent-Hamiltonian ground-space
condition. The present theorem takes as hypothesis only the translated
length-two commutativity equations. Documented in
`docs/paper-gaps/cpsv16_nncph_ground_state_scope.tex`.

Note: with the present Lean definition, `IsRFP` is a normalization-sensitive
idempotence equation for `transferMap A`, whereas `IsNNCPH` is invariant under
nonzero scalar rescaling of the tensor. A final theorem should therefore include
a normalization hypothesis, such as `IsLeftCanonical A`, before applying the
commuting-Hamiltonian ground-space characterization. -/
theorem nncph_implies_rfp (A : MPSTensor d D) [NeZero D]
    (hNNCPH : ∀ N, 2 ≤ N → IsNNCPH A N)
    (hNT : IsNormal A)
    (hLeft : IsLeftCanonical A) :
    IsRFP A := by
  refine Axioms.beigi_nncph_to_rfp A hNT hLeft ?_
  intro N hN i j
  exact hNNCPH N hN i j

end MPSTensor
