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
