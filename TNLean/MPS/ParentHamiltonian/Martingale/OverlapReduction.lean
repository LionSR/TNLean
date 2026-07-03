/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.ParentHamiltonian.Commuting
import TNLean.MPS.ParentHamiltonian.Martingale.Transport

/-!
# Overlap reduction for commuting parent-Hamiltonian local terms

For a finite periodic parent Hamiltonian, local terms with disjoint cyclic
supports commute by locality.  Hence the source commutation condition for
interacting translates reduces the all-pairs commuting condition to the pairs
whose cyclic supports overlap.
-/

namespace MPSTensor

variable {d D : ℕ}

/-- To prove that a finite periodic parent Hamiltonian has commuting local
terms, it suffices to check pairs of translated local terms with overlapping
cyclic supports.

The disjoint pairs commute by locality, as recorded in the coefficient-space
non-overlap lemma. This is the finite-chain reduction behind the source
condition \([\tau_j(P_L),P_L]=0\) for interacting translates in
arXiv:1606.00608, Definition 3.9. -/
theorem isCommutingParentHam_of_cyclicWindowsOverlap_commute
    {A : MPSTensor d D} {L N : ℕ} (hLN : L ≤ N)
    (hOverlap : ∀ i j : Fin N, cyclicWindowsOverlap N L i j →
      localTerm A L N i * localTerm A L N j =
        localTerm A L N j * localTerm A L N i) :
    IsCommutingParentHam A L N := by
  intro i j
  by_cases hij : cyclicWindowsOverlap N L i j
  · exact hOverlap i j hij
  · exact localTerm_commute_of_cyclic_windows_disjoint A hLN
      (CyclicWindowsDisjoint.of_not_cyclicWindowsOverlap hij)

/-- Nearest-neighbor specialization of the overlap reduction for the source
NNCPH commutation equations. -/
theorem isNNCPH_of_twoSite_cyclicWindowsOverlap_commute
    {A : MPSTensor d D} {N : ℕ} (hN : 2 ≤ N)
    (hOverlap : ∀ i j : Fin N, cyclicWindowsOverlap N 2 i j →
      localTerm A 2 N i * localTerm A 2 N j =
        localTerm A 2 N j * localTerm A 2 N i) :
    IsNNCPH A N :=
  isCommutingParentHam_of_cyclicWindowsOverlap_commute (A := A) (L := 2) hN hOverlap

/-- Overlapping length-two cyclic-window commutation supplies the
local-projector hypotheses used by the conditional Appendix B extraction.

The idempotency part is the general translated-parent-term idempotency; the
overlap reduction supplies the missing all-pairs commutation equations. -/
noncomputable def HasProductPairLocalProjectors.of_twoSite_cyclicWindowsOverlap_commute
    {A : MPSTensor d D} {N : ℕ} (hN : 2 ≤ N)
    (hOverlap : ∀ i j : Fin N, cyclicWindowsOverlap N 2 i j →
      localTerm A 2 N i * localTerm A 2 N j =
        localTerm A 2 N j * localTerm A 2 N i) :
    HasProductPairLocalProjectors A N :=
  HasProductPairLocalProjectors.of_commuting_localTerms
    (isNNCPH_of_twoSite_cyclicWindowsOverlap_commute (A := A) hN hOverlap)

/-- Construct the conditional Appendix B extraction from the coefficient
factorization and the overlapping length-two cyclic-window commutation
equations on every chain.

This is only the locality reduction from overlapping pairs to all pairs; the
source \(Q_{AX},Q_{XB}\) projectors and their lifted commutator remain separate
inputs to the proof of the overlap hypotheses. -/
noncomputable def AppendixBProductPairExtraction.ofCoreTensorFactorizationAndOverlapCommutation
    {A : MPSTensor d D} {hStruct : AppendixBStructuralData A}
    (hCore : ∀ N, 0 < N → ∀ σ : Cfg d (2 * N),
      mpv hStruct.coreTensor σ = productPairState hStruct.twoSiteAmplitude N σ)
    (hOverlap : ∀ N, 2 ≤ N → ∀ i j : Fin N, cyclicWindowsOverlap N 2 i j →
      localTerm A 2 N i * localTerm A 2 N j =
        localTerm A 2 N j * localTerm A 2 N i) :
    AppendixBProductPairExtraction hStruct :=
  AppendixBProductPairExtraction.ofCoreTensorFactorization hCore
    (fun N hN =>
      HasProductPairLocalProjectors.of_twoSite_cyclicWindowsOverlap_commute
        (A := A) hN (hOverlap N hN))

end MPSTensor
