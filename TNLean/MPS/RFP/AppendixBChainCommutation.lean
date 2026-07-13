/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.ParentHamiltonian.LocalSupportTransport
import TNLean.MPS.ParentHamiltonian.Martingale.OverlapReduction
import TNLean.MPS.RFP.AppendixBCommutation

/-!
# Appendix B commutation on finite periodic chains

The Appendix B basic-vector form gives commutation of the two adjacent
length-two support projectors on a three-site window.  This file transports
that local equation around a periodic chain and obtains the finite-chain family
of commuting parent interactions used in the RFP-to-NNCPH direction.

The chain length is restricted to (N>2), exactly as in arXiv:1606.00608,
Theorem 3.10.  The case (N=2) is not part of the source statement: its two
cyclic windows traverse the same pair of sites in opposite orders.
-/

namespace MPSTensor

variable {d D : ℕ}

/-- The canonical two-site parent interactions supplied by an Appendix B
structural datum satisfy the algebraic and kernel-intersection clauses of
Definition D.2 on the three-site MPS ground space, provided the tensor is
injective.

The two operators are the canonical parent interaction \(q_2(A)\), placed on
the \(AX\) and \(XB\) faces. Their commutation was obtained from the adjacent
virtual-bond projectors. The remaining kernel equation is the standard
three-site MPS intersection property. The result type records idempotence,
commutation, and the kernel equation; orthogonality of these concrete
interactions follows separately from the definition of \(q_2(A)\).

This theorem relates the Appendix B basic-vector construction to the separate
condition in Appendix D. It is not the argument printed for the implication
RFP \(\Rightarrow\) NNCPH: arXiv:1606.00608, lines 1305--1307, calls that
implication an immediate consequence of the structural characterization.

Source: arXiv:1606.00608, Theorem 3.11, lines 543--578; Definition D.2,
lines 2205--2218; and the proof of Theorem 3.10, lines 1305--1307. -/
theorem AppendixBStructuralData.hasAppendixD2ParentCommutingHamiltonian
    {A : MPSTensor d D} (hStruct : AppendixBStructuralData A)
    (hA : IsInjective A) :
    HasAppendixD2ParentCommutingHamiltonian (d := d) (groundSpace A 3)
      hStruct.appendixBQAXOnCoeffSpace hStruct.appendixBQXBOnCoeffSpace := by
  refine
    { left_idempotent := hStruct.appendixBQAXOnCoeffSpace_idempotent
      right_idempotent := hStruct.appendixBQXBOnCoeffSpace_idempotent
      commute_lifts := hStruct.hasOverlappingTwoSiteCommutation.commute_lifts
      kernel_intersection := ?_ }
  rw [hStruct.appendixBQAXOnCoeffSpace_eq_parentInteraction]
  rw [hStruct.appendixBQXBOnCoeffSpace_eq_parentInteraction]
  exact groundSpace_three_eq_adjacent_twoSite_parent_kernels hA

/-- A normal left-canonical RFP tensor supplies the three-site algebraic and
kernel-intersection datum of arXiv:1606.00608, Definition D.2.

Injectivity is not an additional hypothesis: it follows from normality, the RFP
identity, and left-canonical normalization. This is a local Appendix D
corollary of the Appendix B structural form. It is logically separate from the
one-sentence proof of RFP \(\Rightarrow\) NNCPH at source lines 1305--1307.

**Scope restriction (left-canonical local datum):** The source structural
theorem is stated for tensors in canonical form. This result uses the proved
left-canonical specialization recorded in
`docs/paper-gaps/cpsv16_nncph_ground_state_scope.tex`.

Source: arXiv:1606.00608, Theorems 3.10--3.11, lines 534--578 and
1305--1307; Definition D.2, lines 2205--2218. -/
theorem rfp_hasAppendixD2ParentCommutingHamiltonian_of_leftCanonical
    (A : MPSTensor d D) [NeZero D]
    (hRFP : IsRFP A) (hNT : IsNormal A) (hLeft : IsLeftCanonical A) :
    let hStruct := AppendixBStructuralData.ofRFP A hNT hRFP hLeft
    HasAppendixD2ParentCommutingHamiltonian (d := d) (groundSpace A 3)
      hStruct.appendixBQAXOnCoeffSpace hStruct.appendixBQXBOnCoeffSpace := by
  dsimp only
  exact AppendixBStructuralData.hasAppendixD2ParentCommutingHamiltonian
    (AppendixBStructuralData.ofRFP A hNT hRFP hLeft)
    (rfp_nt_structural_of_leftCanonical A hNT hRFP hLeft)

/-- The Appendix B structural datum gives commutation of adjacent translated
length-two parent interactions on every periodic chain of length (N>2).

Source: arXiv:1606.00608, Definition 3.9, source lines 517--524; Theorem 3.10,
source lines 534--540; and the structural characterization and basic-vector
form, source lines 543--578. -/
theorem AppendixBStructuralData.adjacent_twoSite_localTerms_commute
    {A : MPSTensor d D} (hStruct : AppendixBStructuralData A)
    {N : ℕ} (hN : 2 < N) (i : Fin N) :
    localTerm A 2 N i * localTerm A 2 N (cyclicForwardSite i 1) =
      localTerm A 2 N (cyclicForwardSite i 1) * localTerm A 2 N i :=
  localTerm_adjacent_twoSite_commute_of_threeSite_zero_one_commute
    (hStruct.localTerm_two_three_zero_one_commute_of_overlapping
      hStruct.hasOverlappingTwoSiteCommutation)
    (by omega) i

/-- The Appendix B structural datum supplies the commuting local-projector
family on every periodic chain of length (N>2).

The projectors are the translated canonical length-two parent interactions.
Their idempotency is general; their commutation follows from the source
three-site projector equation and cyclic transport.

Source: arXiv:1606.00608, Definition 3.9, source lines 517--524; Theorem 3.10,
source lines 534--540; and the structural characterization and basic-vector
form, source lines 543--578. -/
noncomputable def AppendixBStructuralData.hasProductPairLocalProjectors
    {A : MPSTensor d D} (hStruct : AppendixBStructuralData A)
    {N : ℕ} (hN : 2 < N) :
    HasProductPairLocalProjectors A N :=
  HasProductPairLocalProjectors.of_adjacent_twoSite_commute (by omega)
    (hStruct.adjacent_twoSite_localTerms_commute hN)

/-- The Appendix B structural datum satisfies the nearest-neighbor commutation
equations on every periodic chain of length (N>2).

Source: arXiv:1606.00608, Definition 3.9, source lines 517--524; Theorem 3.10,
source lines 534--540; and the structural characterization and basic-vector
form, source lines 543--578. -/
theorem AppendixBStructuralData.isNNCPH
    {A : MPSTensor d D} (hStruct : AppendixBStructuralData A)
    {N : ℕ} (hN : 2 < N) :
    IsNNCPH A N :=
  (hStruct.hasProductPairLocalProjectors hN).isNNCPH

/-- A normal left-canonical renormalization fixed-point tensor has commuting
length-two parent interactions on every periodic chain of length (N>2).

This internalizes the commutation part of arXiv:1606.00608,
Theorem 3.10(i) implies (iii), in the left-canonical scope used by the proved
Appendix B structural theorem.  It does not use
`Axioms.rfp_to_nncph_commute` and does not assert the ground-space spanning
clause of Definition 3.9.

**Scope restriction (left-canonical commutation):** The source theorem is stated
for tensors in canonical form.  This theorem assumes the left-canonical gauge
used by the proved Appendix B structural theorem.  The removal of this extra
hypothesis is recorded in
`docs/paper-gaps/cpsv16_nncph_ground_state_scope.tex`.

Source: arXiv:1606.00608, Theorem 3.10, source lines 534--540; structural
characterization and basic-vector form, source lines 543--578. -/
theorem rfp_implies_nncph_of_leftCanonical
    (A : MPSTensor d D) [NeZero D]
    (hRFP : IsRFP A) (hNT : IsNormal A) (hLeft : IsLeftCanonical A)
    (N : ℕ) (hN : 2 < N) :
    IsNNCPH A N :=
  (AppendixBStructuralData.ofRFP A hNT hRFP hLeft).isNNCPH hN

/-- Ground-vector form of `rfp_implies_nncph_of_leftCanonical`.

The translated parent terms commute and annihilate the periodic MPS vector.
The source ground-space spanning clause remains separate.

**Scope restriction (ground vector):** The source implication includes the
ground-space spanning equation and is stated in canonical-form scope.  This
theorem proves the commutation and zero-energy equations under an explicit
left-canonical hypothesis.  The two restrictions are recorded in
`docs/paper-gaps/cpsv16_nncph_ground_state_scope.tex`.

Source: arXiv:1606.00608, Definition 3.9, source lines 517--524, and
Theorem 3.10, source lines 534--540. -/
theorem rfp_implies_nncph_ground_state_of_leftCanonical
    (A : MPSTensor d D) [NeZero D]
    (hRFP : IsRFP A) (hNT : IsNormal A) (hLeft : IsLeftCanonical A)
    (N : ℕ) (hN : 2 < N) :
    IsNNCPHGroundState A N :=
  (rfp_implies_nncph_of_leftCanonical A hRFP hNT hLeft N hN).isNNCPHGroundState
    (by omega)

end MPSTensor
