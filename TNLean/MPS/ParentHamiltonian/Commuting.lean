/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.ParentHamiltonian.Basic
import TNLean.MPS.BNT.Basic
import TNLean.MPS.Periodic.Defs
import TNLean.MPS.RFP.CommutingBridge
import TNLean.MPS.RFP.Defs
import TNLean.MPS.RFP.StructuralForm
import TNLean.Axioms.Beigi

/-!
# Commuting parent Hamiltonians

This file records the commutation equations for parent Hamiltonians, the
length-two specialization used in the nearest-neighbor commuting parent
Hamiltonian part of arXiv:1606.00608, and the source ground-space spanning
clause from Definition 3.9.

## Main definitions

* `MPSTensor.IsCommutingParentHam A L N` — the local terms of the parent
  Hamiltonian on \(N\) sites with block length \(L\) mutually commute.
* `MPSTensor.IsNNCPH A N` — length-two commutativity of the translated parent
  interaction terms.
* `MPSTensor.IsNNCPHGroundState A N` — the length-two local terms commute and
  annihilate the periodic MPS vector \(V^{(N)}(A)\): it is the conjunction of
  `IsNNCPH A N` and `IsFrustrationFree A 2 N (mpv A)`.
* `MPSTensor.HasParentHamiltonianGroundSpaceSpanning B L A` — the Definition
  3.9 condition that the kernel of \(H_L^{(N)}\) is spanned by the BNT vectors
  \(V^{(N)}(A_j)\) for every \(N>L\).
* `MPSTensor.HasNNCPHGroundSpace B A N` — the fixed-chain nearest-neighbor
  form: length-two commutation, zero energy of \(V^{(N)}(B)\), and the
  ground-space spanning equation.
* `MPSTensor.HasNNCPHGroundSpaces B A` — the all-chain source condition:
  `HasNNCPHGroundSpace B A N` for every \(N>2\).

## Main results

* `MPSTensor.IsCommutingParentHam.ham_comm_localTerm` — if local terms commute,
  the full Hamiltonian commutes with each local term.
* `MPSTensor.ProductPairBridge.isNNCPH` — if the two-site local terms are
  projectors \(pᵢ\) with \(pᵢpⱼ = pⱼpᵢ\), then the parent Hamiltonian satisfies
  \(hᵢhⱼ = hⱼhᵢ\).
* `MPSTensor.rfp_implies_nncph_of_appendixBExtraction` — a conditional theorem
  deriving NNCPH from the Appendix B structural form
  \(Aᵢ = XΛUᵢX⁻¹\), the even-chain product-of-pairs factorization, and the
  two-site projector identities, without invoking
  `Axioms.rfp_to_nncph_commute`.
* `MPSTensor.rfp_implies_nncph_ground_state_of_appendixBExtraction` — the same
  conditional theorem with the zero-energy equation for \(V^{(N)}(A)\) included.
* `MPSTensor.rfp_implies_hasNNCPHGroundSpaces_of_appendixBExtraction_of_groundSpaceSpanning` —
  the same Appendix B conditional theorem upgraded to the full all-chain
  Definition 3.9 condition once the ground-space spanning equation is supplied.
* `MPSTensor.rfp_implies_nncph` — construction of the length-two commutation
  equations in the RFP \(\Longrightarrow\) NNCPH direction, using the
  structural characterization theorem of arXiv:1606.00608, source lines
  543--555.
* `MPSTensor.rfp_implies_nncph_ground_state` — the same direction with the
  zero-energy ground-vector equation for the MPS vector included, but without
  the source ground-space spanning assertion.
* `MPSTensor.hasNNCPHGroundSpaces_iff_forall_isNNCPH_and_groundSpaceSpanning` —
  the all-chain source condition is equivalently all-chain nearest-neighbor
  commutation together with the Definition 3.9 ground-space spanning clause.
* `MPSTensor.nncph_implies_rfp` — axiom-backed reverse implication from the
  all-chain NNCPH ground-space condition to RFP.

## References

* arXiv:1606.00608, Section 3.3 Definition 3.9, Theorem 3.10
* S. Beigi, *J. Phys. A: Math. Theor.* **45** (2012) 025306 —
  ground-space characterization for commuting nearest-neighbor
  Hamiltonians in 1D (consumed only in the NNCPH \(\Longrightarrow\) RFP direction)
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
ground-space spanning condition by the periodic MPS vectors of the BNT
components. -/
def IsCommutingParentHam (A : MPSTensor d D) (L N : ℕ) : Prop :=
  ∀ i j : Fin N,
    localTerm A L N i * localTerm A L N j = localTerm A L N j * localTerm A L N i

/-- **Nearest-neighbor commuting parent Hamiltonian** (NNCPH): the length-two
commutation equations for the translated parent interaction terms.

See arXiv:1606.00608, Definition 3.9. The source nearest-neighbor condition
also fixes \(L=2\) and includes the parent-Hamiltonian ground-space spanning
condition, which is not part of this predicate. -/
def IsNNCPH (A : MPSTensor d D) (N : ℕ) : Prop :=
  IsCommutingParentHam A 2 N

/-- The commutation and zero-energy equations for the nearest-neighbor
commuting parent-Hamiltonian statement: the length-two local terms commute and
annihilate the periodic MPS vector V^{(N)}(A).

See arXiv:1606.00608, Theorem 3.10(iii), source line 539. This predicate records
the commutativity and annihilation equations for the MPS vector. The full source
parent-Hamiltonian condition also includes the ground-space spanning assertion
from Definition 3.9: for \(N>L\), the ground space is spanned by the periodic
MPS vectors associated to the BNT components. Theorem 3.10 also includes the
canonical-form and zero-correlation-length equivalences.

**Scope restriction (ground vector):** This predicate is exactly
`IsNNCPH A N ∧ IsFrustrationFree A 2 N (mpv A)`: the length-two commutation
equation and the zero-energy equation for \(V^{(N)}(A)\). It is not the full
source ground-space spanning condition. Documented in
`docs/paper-gaps/cpsv16_nncph_ground_state_scope.tex`. -/
def IsNNCPHGroundState (A : MPSTensor d D) (N : ℕ) : Prop :=
  IsNNCPH A N ∧ IsFrustrationFree A 2 N (mpv A)

/-- Source Definition 3.9 parent-Hamiltonian ground-space spanning clause.

Given a canonical-form tensor \(B\) with BNT components \(A_j\), the source says
that \(H_L^{(N)}\) is a parent Hamiltonian when, for every \(N>L\), the kernel
of \(H_L^{(N)}\) is spanned by \(|V^{(N)}(A_j)\rangle\).

The predicate records only this spanning equation; a theorem using it must
separately supply the hypothesis that the family \(A_j\) is the BNT family of
\(B\).

See arXiv:1606.00608, Definition 3.9, source lines 522--524. -/
def HasParentHamiltonianGroundSpaceSpanning (B : MPSTensor d D) (L : ℕ)
    {r : ℕ} {dim : Fin r → ℕ} (A : (j : Fin r) → MPSTensor d (dim j)) : Prop :=
  ∀ N : ℕ, L < N → LinearMap.ker (parentHamiltonian B L N) = bntMPSVectorSpan A N

/-- Fixed-chain nearest-neighbor commuting parent-Hamiltonian ground-space
condition from arXiv:1606.00608, Definition 3.9 and Theorem 3.10(iii).

For a canonical-form tensor \(B\) with BNT components \(A_j\), this packages
the three finite-chain equations:
\[
  h_i h_j=h_j h_i,\qquad
  h_iV^{(N)}(B)=0,\qquad
  \ker H_2^{(N)}(B)=\operatorname{span}\{V^{(N)}(A_j)\}_j .
\]
The source theorem quantifies this condition over all \(N>2\).  This definition
only records the condition for one fixed chain length; it does not assert that
the displayed spanning equation has been proved for any tensor. -/
def HasNNCPHGroundSpace (B : MPSTensor d D)
    {r : ℕ} {dim : Fin r → ℕ} (A : (j : Fin r) → MPSTensor d (dim j))
    (N : ℕ) : Prop :=
  IsNNCPHGroundState B N ∧
    LinearMap.ker (parentHamiltonian B 2 N) = bntMPSVectorSpan A N

/-- All-chain nearest-neighbor commuting parent-Hamiltonian ground-space
condition.

This is the source quantification in arXiv:1606.00608, Theorem 3.10(iii):
for every \(N>2\), the nearest-neighbor parent terms commute, the periodic MPS
vector has zero energy, and the ground space of \(H_2^{(N)}\) is spanned by the
BNT vectors. It packages only the condition; it does not prove the spanning
equation for any tensor. -/
def HasNNCPHGroundSpaces (B : MPSTensor d D)
    {r : ℕ} {dim : Fin r → ℕ} (A : (j : Fin r) → MPSTensor d (dim j)) : Prop :=
  ∀ N : ℕ, 2 < N → HasNNCPHGroundSpace B A N

/-- The nearest-neighbor commuting condition is a special case of the commuting
parent Hamiltonian (length two). -/
theorem IsNNCPH.isCommutingParentHam {A : MPSTensor d D} {N : ℕ} (h : IsNNCPH A N) :
    IsCommutingParentHam A 2 N :=
  h

/-- The zero-energy nearest-neighbor ground-vector condition includes commuting
length-two local terms. -/
theorem IsNNCPHGroundState.isNNCPH {A : MPSTensor d D} {N : ℕ}
    (h : IsNNCPHGroundState A N) :
    IsNNCPH A N :=
  h.1

/-- The zero-energy nearest-neighbor ground-vector condition includes the
frustration-free equation for the length-two parent Hamiltonian. -/
theorem IsNNCPHGroundState.isFrustrationFree {A : MPSTensor d D} {N : ℕ}
    (h : IsNNCPHGroundState A N) :
    IsFrustrationFree A 2 N (mpv A) :=
  h.2

/-- If the length-two parent terms commute and N ≥ 2, then the periodic MPS
vector satisfies the NNCPH commutation and zero-energy condition. This does not
assert the source ground-space spanning condition. -/
theorem IsNNCPH.isNNCPHGroundState {A : MPSTensor d D} {N : ℕ}
    (h : IsNNCPH A N) (hN : 2 ≤ N) :
    IsNNCPHGroundState A N :=
  ⟨h, parentHamiltonian_frustrationFree A 2 N hN⟩

/-- The full fixed-chain NNCPH ground-space condition includes the
commutation and zero-energy equations. -/
theorem HasNNCPHGroundSpace.isNNCPHGroundState {B : MPSTensor d D}
    {r : ℕ} {dim : Fin r → ℕ} {A : (j : Fin r) → MPSTensor d (dim j)}
    {N : ℕ} (h : HasNNCPHGroundSpace B A N) :
    IsNNCPHGroundState B N :=
  h.1

/-- The full fixed-chain NNCPH ground-space condition includes length-two
translated parent-term commutation. -/
theorem HasNNCPHGroundSpace.isNNCPH {B : MPSTensor d D}
    {r : ℕ} {dim : Fin r → ℕ} {A : (j : Fin r) → MPSTensor d (dim j)}
    {N : ℕ} (h : HasNNCPHGroundSpace B A N) :
    IsNNCPH B N :=
  h.isNNCPHGroundState.isNNCPH

/-- The full fixed-chain NNCPH ground-space condition includes zero energy of
the periodic MPS vector. -/
theorem HasNNCPHGroundSpace.isFrustrationFree {B : MPSTensor d D}
    {r : ℕ} {dim : Fin r → ℕ} {A : (j : Fin r) → MPSTensor d (dim j)}
    {N : ℕ} (h : HasNNCPHGroundSpace B A N) :
    IsFrustrationFree B 2 N (mpv B) :=
  h.isNNCPHGroundState.isFrustrationFree

/-- The full fixed-chain NNCPH ground-space condition contains the BNT
ground-space spanning equation. -/
theorem HasNNCPHGroundSpace.groundSpaceSpanning {B : MPSTensor d D}
    {r : ℕ} {dim : Fin r → ℕ} {A : (j : Fin r) → MPSTensor d (dim j)}
    {N : ℕ} (h : HasNNCPHGroundSpace B A N) :
    LinearMap.ker (parentHamiltonian B 2 N) = bntMPSVectorSpan A N :=
  h.2

/-- Quantifying the fixed-chain NNCPH ground-space condition over \(N>2\)
supplies the nearest-neighbor instance of the parent-Hamiltonian spanning
predicate. -/
theorem HasNNCPHGroundSpace.hasParentHamiltonianGroundSpaceSpanning
    {B : MPSTensor d D}
    {r : ℕ} {dim : Fin r → ℕ} {A : (j : Fin r) → MPSTensor d (dim j)}
    (h : ∀ N : ℕ, 2 < N → HasNNCPHGroundSpace B A N) :
    HasParentHamiltonianGroundSpaceSpanning B 2 A := by
  intro N hN
  exact (h N hN).groundSpaceSpanning

/-- The all-chain NNCPH ground-space condition gives the fixed-chain condition. -/
theorem HasNNCPHGroundSpaces.hasNNCPHGroundSpace {B : MPSTensor d D}
    {r : ℕ} {dim : Fin r → ℕ} {A : (j : Fin r) → MPSTensor d (dim j)}
    {N : ℕ} (h : HasNNCPHGroundSpaces B A) (hN : 2 < N) :
    HasNNCPHGroundSpace B A N :=
  h N hN

/-- The all-chain source condition contains the parent-Hamiltonian
ground-space spanning clause. -/
theorem HasNNCPHGroundSpaces.hasParentHamiltonianGroundSpaceSpanning
    {B : MPSTensor d D}
    {r : ℕ} {dim : Fin r → ℕ} {A : (j : Fin r) → MPSTensor d (dim j)}
    (h : HasNNCPHGroundSpaces B A) :
    HasParentHamiltonianGroundSpaceSpanning B 2 A := by
  exact HasNNCPHGroundSpace.hasParentHamiltonianGroundSpaceSpanning h

/-- The all-chain NNCPH ground-space condition is exactly the all-chain
commutation-and-zero-energy condition together with the source ground-space
spanning clause.

This is the formal unpacking of arXiv:1606.00608, Definition 3.9 and
Theorem 3.10(iii): the theorem statement quantifies over \(N>2\), while
Definition 3.9 supplies the spanning equation for the nearest-neighbor
parent Hamiltonian. -/
theorem hasNNCPHGroundSpaces_iff_forall_isNNCPHGroundState_and_groundSpaceSpanning
    {B : MPSTensor d D}
    {r : ℕ} {dim : Fin r → ℕ} {A : (j : Fin r) → MPSTensor d (dim j)} :
    HasNNCPHGroundSpaces B A ↔
      (∀ N : ℕ, 2 < N → IsNNCPHGroundState B N) ∧
        HasParentHamiltonianGroundSpaceSpanning B 2 A := by
  constructor
  · intro h
    exact
      ⟨fun N hN => (h N hN).isNNCPHGroundState,
        h.hasParentHamiltonianGroundSpaceSpanning⟩
  · rintro ⟨hGround, hSpan⟩ N hN
    exact ⟨hGround N hN, hSpan N hN⟩

/-- The all-chain NNCPH ground-space condition is equivalently the all-chain
nearest-neighbor commutation equations together with the source ground-space
spanning clause.

For \(N>2\), the zero-energy equation for \(V^{(N)}(B)\) follows from the
parent-Hamiltonian construction, so it need not be assumed separately once the
length-two commuting condition and Definition 3.9 spanning equation are given.

See arXiv:1606.00608, Definition 3.9 and Theorem 3.10(iii). -/
theorem hasNNCPHGroundSpaces_iff_forall_isNNCPH_and_groundSpaceSpanning
    {B : MPSTensor d D}
    {r : ℕ} {dim : Fin r → ℕ} {A : (j : Fin r) → MPSTensor d (dim j)} :
    HasNNCPHGroundSpaces B A ↔
      (∀ N : ℕ, 2 < N → IsNNCPH B N) ∧
        HasParentHamiltonianGroundSpaceSpanning B 2 A := by
  constructor
  · intro h
    exact
      ⟨fun N hN => (h N hN).isNNCPH,
        h.hasParentHamiltonianGroundSpaceSpanning⟩
  · rintro ⟨hComm, hSpan⟩ N hN
    exact ⟨(hComm N hN).isNNCPHGroundState (le_of_lt hN), hSpan N hN⟩

/-- If each BNT vector is killed by the parent Hamiltonian, then their span is
contained in the parent-Hamiltonian kernel.

This is the easy inclusion in the source spanning equation
\[
  \ker H_L^{(N)}(B)
  =
  \operatorname{span}\{V^{(N)}(A_j):j=1,\ldots,g\}
\]
from arXiv:1606.00608, Definition 3.9, source lines 522--524. -/
theorem bntMPSVectorSpan_le_ker_parentHamiltonian_of_forall_annihilates
    {B : MPSTensor d D} {r : ℕ} {dim : Fin r → ℕ}
    {A : (j : Fin r) → MPSTensor d (dim j)} {L N : ℕ}
    (h : ∀ j : Fin r, parentHamiltonian B L N (mpv (A j)) = 0) :
    bntMPSVectorSpan A N ≤ LinearMap.ker (parentHamiltonian B L N) := by
  rw [bntMPSVectorSpan]
  refine Submodule.span_le.mpr ?_
  intro v hv
  rcases hv with ⟨j, rfl⟩
  exact LinearMap.mem_ker.mpr (h j)

/-- If each BNT vector is frustration-free for the parent Hamiltonian, then the
BNT span is contained in the parent-Hamiltonian kernel.

This records the zero-energy half of the source parent-Hamiltonian ground-space
spanning condition from arXiv:1606.00608, Definition 3.9, source lines
522--524. The reverse inclusion is the hard spanning direction. -/
theorem bntMPSVectorSpan_le_ker_parentHamiltonian_of_forall_frustrationFree
    {B : MPSTensor d D} {r : ℕ} {dim : Fin r → ℕ}
    {A : (j : Fin r) → MPSTensor d (dim j)} {L N : ℕ}
    (h : ∀ j : Fin r, IsFrustrationFree B L N (mpv (A j))) :
    bntMPSVectorSpan A N ≤ LinearMap.ker (parentHamiltonian B L N) := by
  refine bntMPSVectorSpan_le_ker_parentHamiltonian_of_forall_annihilates ?_
  intro j
  simp only [parentHamiltonian, LinearMap.sum_apply]
  exact Finset.sum_eq_zero fun i _ => h j i

/-- If the two-site parent terms are idempotents \(pᵢ\) with
\(pᵢpⱼ = pⱼpᵢ\), then the nearest-neighbor parent Hamiltonian is commuting on
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

/-- Product-of-pairs data and the ground-space spanning equation give the full
all-chain nearest-neighbor parent-Hamiltonian condition.

The product-of-pairs data supply the translated length-two commutation
equations. The usual parent-Hamiltonian frustration-free equation gives
zero energy of \(V^{(N)}(B)\). The separate hypothesis
`HasParentHamiltonianGroundSpaceSpanning B 2 A` supplies the remaining
Definition 3.9 ground-space spanning clause from arXiv:1606.00608,
source lines 522--524. -/
theorem ProductPairBridge.hasNNCPHGroundSpaces_of_groundSpaceSpanning
    {B : MPSTensor d D} (hBridge : ProductPairBridge B)
    {r : ℕ} {dim : Fin r → ℕ} {A : (j : Fin r) → MPSTensor d (dim j)}
    (hSpan : HasParentHamiltonianGroundSpaceSpanning B 2 A) :
    HasNNCPHGroundSpaces B A := by
  intro N hN
  exact ⟨(hBridge.isNNCPH N).isNNCPHGroundState (le_of_lt hN), hSpan N hN⟩

/-- Conditional internal theorem for Theorem 3.10(i)⟹(iii).

A normal left-canonical RFP tensor has the Appendix B structural form
\(Aᵢ = XΛUᵢX⁻¹\) by `AppendixBStructuralData.ofRFP`. If the associated two-site
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

/-- Conditional ground-vector form of Theorem 3.10(i)⟹(iii).

Under the same Appendix B product-of-pairs extraction used for
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
    (hRFP : IsRFP A) (hNT : IsNormal A) (hLeft : IsLeftCanonical A)
    (hExtract : AppendixBProductPairExtraction
      (AppendixBStructuralData.ofRFP A hNT hRFP hLeft))
    (N : ℕ) (hN : 2 ≤ N) :
    IsNNCPHGroundState A N :=
  (rfp_implies_nncph_of_appendixBExtraction A hRFP hNT hLeft hExtract N).isNNCPHGroundState
    hN

/-- Conditional full source form of Theorem 3.10(i)⟹(iii).

Under the Appendix B product-of-pairs extraction used above, a normal
left-canonical RFP tensor has the all-chain commutation and zero-energy
equations for nearest-neighbor parent terms. If, in addition, the
Definition 3.9 ground-space spanning equation is supplied for a chosen BNT
family \(A_j\), then the full all-chain NNCPH ground-space condition holds.

This theorem does not use `Axioms.rfp_to_nncph_commute`; the remaining input is
exactly the source ground-space spanning clause.

**Scope restriction (spanning clause assumed):** The source implication proves
the ground-space spanning equation; this theorem assumes it via
`HasParentHamiltonianGroundSpaceSpanning`. Documented in
`docs/paper-gaps/cpsv16_nncph_ground_state_scope.tex`. -/
theorem rfp_implies_hasNNCPHGroundSpaces_of_appendixBExtraction_of_groundSpaceSpanning
    (B : MPSTensor d D) [NeZero D]
    (hRFP : IsRFP B) (hNT : IsNormal B) (hLeft : IsLeftCanonical B)
    (hExtract : AppendixBProductPairExtraction
      (AppendixBStructuralData.ofRFP B hNT hRFP hLeft))
    {r : ℕ} {dim : Fin r → ℕ} {A : (j : Fin r) → MPSTensor d (dim j)}
    (hSpan : HasParentHamiltonianGroundSpaceSpanning B 2 A) :
    HasNNCPHGroundSpaces B A :=
  hExtract.toProductPairBridge.hasNNCPHGroundSpaces_of_groundSpaceSpanning hSpan

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

/-- **Theorem 3.10(i)⟹(iii)** (arXiv:1606.00608): RFP implies the NNCPH
commutation equations.
A normal renormalization fixed-point tensor has commuting length-two parent
terms.

Per arXiv:1606.00608 Section 3.3, the proof passage at source line 1307
derives this direction from the structural characterization theorem, so it does
not depend on S. Beigi (2012). It is conditioned on that source theorem
(source lines 543--555), stated here as `Axioms.rfp_to_nncph_commute`. -/
theorem rfp_implies_nncph (A : MPSTensor d D) [NeZero D]
    (hRFP : IsRFP A) (hNT : IsNormal A)
    (N : ℕ) (hN : 2 ≤ N) :
    IsNNCPH A N := by
  classical
  unfold IsNNCPH IsCommutingParentHam
  intro i j
  exact Axioms.rfp_to_nncph_commute A hNT hRFP N hN i j

/-- **Theorem 3.10(i)⟹(iii)** (arXiv:1606.00608), ground-vector form:
RFP implies that the periodic MPS vector satisfies the zero-energy equation for
commuting nearest-neighbor parent terms on every chain of length at least two.

This theorem adds the frustration-free ground-vector equation to
`rfp_implies_nncph`.

**Scope restriction (ground vector):** The source theorem states the
three-way equivalence for canonical-form tensors and requires the full
parent-Hamiltonian ground-space condition, namely spanning by the periodic MPS
vectors of the BNT components. This theorem proves only the commutation and
zero-energy equations for \(V^{(N)}(A)\). Documented in
`docs/paper-gaps/cpsv16_nncph_ground_state_scope.tex`. -/
theorem rfp_implies_nncph_ground_state (A : MPSTensor d D) [NeZero D]
    (hRFP : IsRFP A) (hNT : IsNormal A)
    (N : ℕ) (hN : 2 ≤ N) :
    IsNNCPHGroundState A N :=
  (rfp_implies_nncph A hRFP hNT N hN).isNNCPHGroundState hN

/-- **Theorem 3.10(iii)⟹(i)** (arXiv:1606.00608): all-chain
nearest-neighbor commuting parent-Hamiltonian ground spaces imply RFP in the
present axiom-backed theorem.
Gated on S. Beigi, *J. Phys. A: Math. Theor.* **45** (2012) 025306 —
the ground-space characterization of commuting nearest-neighbor 1D
Hamiltonians with finite degeneracy (`Axioms.beigi_nncph_to_rfp`).

The hypothesis `IsBNT B r dim A` identifies the family \(A_j\) as the BNT of
the original tensor \(B\). The hypothesis `HasNNCPHGroundSpaces B A` is the
source all-chain condition: for every \(N>2\), the length-two translated parent
terms commute, the periodic MPS vector \(V^{(N)}(B)\) has zero energy, and
\[
  \ker H_2^{(N)}(B)=\operatorname{span}\{V^{(N)}(A_j):j=1,\ldots,g\}.
\]

Note: with the present Lean definition, `IsRFP` is a normalization-sensitive
idempotence equation for `transferMap A`, whereas `IsNNCPH` is invariant under
nonzero scalar rescaling of the tensor. A final theorem should therefore include
a normalization hypothesis, such as `IsLeftCanonical A`, before applying the
commuting-Hamiltonian ground-space characterization. -/
theorem nncph_implies_rfp (B : MPSTensor d D) [NeZero D]
    {r : ℕ} {dim : Fin r → ℕ} (A : (j : Fin r) → MPSTensor d (dim j))
    (hBNT : IsBNT B r dim A)
    (hNNCPH : HasNNCPHGroundSpaces B A)
    (hNT : IsNormal B)
    (hLeft : IsLeftCanonical B) :
    IsRFP B := by
  refine Axioms.beigi_nncph_to_rfp B A hBNT hNT hLeft ?_ ?_ ?_
  · intro N hN i j
    exact (hNNCPH N hN).isNNCPH i j
  · intro N hN
    exact (hNNCPH N hN).isFrustrationFree
  · intro N hN
    exact (hNNCPH N hN).groundSpaceSpanning

end MPSTensor
