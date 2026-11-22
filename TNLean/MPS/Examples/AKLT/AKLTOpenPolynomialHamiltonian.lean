/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Examples.AKLT.AKLTOpenBoundary
import TNLean.MPS.Examples.AKLT.AKLTPolynomialHamiltonian

/-!
# The open bilinear-biquadratic AKLT Hamiltonian

Summing the local spin-two projector identity over the nonwrapping bonds
identifies the physical open-chain Hamiltonian with twice the projector parent,
shifted by \(-2(N-1)/3\). This provides the physical-Hamiltonian interpretation
of the four-dimensional edge space in arXiv:2011.12127, lines 1171--1174.
The Hamiltonian polynomial is printed in arXiv:quant-ph/0608197,
`Papers/quant-ph_0608197/MPSarchive.tex`, lines 340--349, equation `HAKLT`.

**Scope restriction (chain length):** The ground-energy and four-dimensional
ground-space theorems assume `2 ≤ N`; the one-site chain is outside these
classification results. See `docs/paper-gaps/rmp_example_parent_hamiltonian_scope.tex`.
-/

open scoped Matrix BigOperators ComplexOrder

noncomputable section

namespace MPSTensor

/-- The bilinear-biquadratic AKLT Hamiltonian with no bond joining the last
site to the first. Source: arXiv:quant-ph/0608197, equation `HAKLT`, with
open boundaries as in arXiv:2011.12127, lines 1171--1174. -/
def akltOpenHamiltonian (N : ℕ) : NSiteSpace 3 N →ₗ[ℂ] NSiteSpace 3 N :=
  ∑ i : NonwrappingStart 2 N,
    (spinExchange spinOneOperator i.1 (cyclicForwardSite i.1 1) +
      (1 / 3 : ℂ) • (spinExchange spinOneOperator i.1 (cyclicForwardSite i.1 1) ∘ₗ
        spinExchange spinOneOperator i.1 (cyclicForwardSite i.1 1)))

/-- The starts of the two-site windows of the open chain, as the indices of the terms of the
parent interaction on the open chain. -/
private def twoSiteStartEquiv (N : ℕ) : Fin (N + 1 - 2) ≃ NonwrappingStart 2 N where
  toFun i := ⟨⟨i.val, by have := i.isLt; omega⟩, by
    change i.val + 2 ≤ N
    have := i.isLt
    omega⟩
  invFun i := ⟨i.1.val, by have := i.2; omega⟩
  left_inv _ := rfl
  right_inv _ := rfl

private theorem card_twoSite_nonwrappingStart (N : ℕ) :
    Fintype.card (NonwrappingStart 2 N) = N - 1 :=
  (Fintype.card_congr (twoSiteStartEquiv N).symm).trans
    ((Fintype.card_fin _).trans (by omega))

/-- The operator of the two-site parent Hamiltonian of the open AKLT chain is the sum of the
translated local terms over the nonwrapping starts. -/
private theorem toLin'_hamiltonian_parentChainInteraction_aklt {N : ℕ} (hN : 2 ≤ N) :
    Matrix.toLin' (parentChainInteraction akltTensor 2 N).hamiltonian =
      ∑ i : NonwrappingStart 2 N, localTerm akltTensor 2 N i.1 := by
  rw [ManyBody.Interaction.hamiltonian, map_sum]
  refine Fintype.sum_equiv (twoSiteStartEquiv N) _ _ fun i ↦ ?_
  have hi : i.val + 2 ≤ N := by have := i.isLt; omega
  have hw : ManyBody.chainWindow i.val hi =
      ManyBody.ringWindow hN ((twoSiteStartEquiv N i).1) := by
    ext j
    have hj : i.val + j.val < N := by have := j.isLt; omega
    rw [ManyBody.val_chainWindow, ManyBody.ringWindow_apply, Fin.val_add, Fin.val_castLE]
    exact (Nat.mod_eq_of_lt hj).symm
  have : NeZero N := ⟨by omega⟩
  rw [localTerm_eq_toLin'_term akltTensor 2, ManyBody.Interaction.ofPlaceAlong_term,
    ManyBody.Interaction.translationInvariant_term_of_le _ hN, hw]

/-- The exact open-chain shift is \(2(N-1)/3\), one contribution per
nonwrapping bond. This follows from the local spin-two projector identity
of arXiv:quant-ph/0608197, equation `HAKLT`. -/
theorem akltOpenHamiltonian_add_eq_parent {N : ℕ} (hN : 2 ≤ N) :
    akltOpenHamiltonian N + (2 * (N - 1) / 3 : ℂ) • LinearMap.id =
      (2 : ℂ) • Matrix.toLin' (parentChainInteraction akltTensor 2 N).hamiltonian := by
  rw [toLin'_hamiltonian_parentChainInteraction_aklt hN]
  refine LinearMap.ext fun ψ => ?_
  ext σ
  simp only [akltOpenHamiltonian,
    LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply,
    LinearMap.sum_apply, LinearMap.comp_apply,
    Finset.sum_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    aklt_localTerm_two_apply hN, Finset.mul_sum, Finset.sum_add_distrib]
  simp only [show ∀ x y z : ℂ, 2 * (1 / 2 * (x + y + z)) = x + y + z from
      fun x y z => by ring, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    card_twoSite_nonwrappingStart, nsmul_eq_mul]
  push_cast [Nat.cast_sub (by omega : 1 ≤ N)]
  ring

/-- The shifted open-chain polynomial Hamiltonian, transported to the \(\ell^2\) space of
coefficient vectors, is positive.
Source: arXiv:2011.12127, lines 1171--1174; the energy shift is derived here. -/
theorem akltOpenHamiltonian_add_isPositive {N : ℕ} (hN : 2 ≤ N) :
    ((WithLp.linearEquiv 2 ℂ (NSiteSpace 3 N)).symm.toLinearMap ∘ₗ
      (akltOpenHamiltonian N + (2 * (N - 1) / 3 : ℂ) • LinearMap.id) ∘ₗ
        (WithLp.linearEquiv 2 ℂ (NSiteSpace 3 N)).toLinearMap).IsPositive := by
  rw [akltOpenHamiltonian_add_eq_parent hN]
  exact (Matrix.isPositive_toEuclideanLin_iff.mpr
    (posSemidef_hamiltonian_parentChainInteraction akltTensor 2 N)).smul_of_nonneg
    (by norm_num [Complex.le_def])

/-- Every eigenvalue is bounded below by the open-chain ground energy.
Source: arXiv:2011.12127, lines 1171--1174; the value is derived from the
local projector identity. -/
theorem akltOpenHamiltonian_eigenvalue_ge {N : ℕ} (hN : 2 ≤ N) {μ : ℂ}
    (hμ : Module.End.HasEigenvalue (akltOpenHamiltonian N) μ) :
    -(2 * (N - 1) / 3 : ℂ) ≤ μ := by
  obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
  have hpos : 0 ≤ μ + (2 * (N - 1) / 3 : ℂ) :=
    (akltOpenHamiltonian_add_isPositive hN).nonneg_of_apply_eq_smul
      (v := (WithLp.linearEquiv 2 ℂ (NSiteSpace 3 N)).symm v)
      ((LinearEquiv.map_ne_zero_iff _).mpr hv.2)
      (by simp [Module.End.mem_eigenspace_iff.1 hv.1, add_smul])
  rw [← sub_nonneg, sub_neg_eq_add]
  exact hpos

/-- The lowest-energy space of the open polynomial Hamiltonian is exactly
the open AKLT matrix-product space. Source: arXiv:2011.12127, lines 1171--1174. -/
theorem akltOpenHamiltonian_eigenspace_eq_groundSpace {N : ℕ} (hN : 2 ≤ N) :
    Module.End.eigenspace (akltOpenHamiltonian N) (-(2 * (N - 1) / 3) : ℂ) =
      (groundSpaceES akltTensor N).map
        (WithLp.linearEquiv 2 ℂ (NSiteSpace 3 N)).toLinearMap := by
  rw [← aklt_ker_hamiltonian_parentChainInteraction_two_eq_groundSpaceES hN]
  ext v
  have hv := LinearMap.congr_fun (akltOpenHamiltonian_add_eq_parent hN) v
  simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply] at hv
  rw [Module.End.mem_eigenspace_iff, Submodule.mem_map_equiv, LinearMap.mem_ker,
    ← (WithLp.linearEquiv 2 ℂ (NSiteSpace 3 N)).map_eq_zero_iff,
    ← smul_eq_zero_iff_right (by norm_num : (2 : ℂ) ≠ 0)]
  change _ ↔ (2 : ℂ) • Matrix.toLin' (parentChainInteraction akltTensor 2 N).hamiltonian v = 0
  rw [← hv, neg_smul, ← sub_eq_zero, sub_neg_eq_add]

/-- The open polynomial AKLT Hamiltonian has four ground states for every
\(N\ge2\). Source: arXiv:2011.12127, lines 1171--1174. -/
theorem akltOpenHamiltonian_groundSpace_finrank {N : ℕ} (hN : 2 ≤ N) :
    Module.finrank ℂ
      (Module.End.eigenspace (akltOpenHamiltonian N) (-(2 * (N - 1) / 3) : ℂ)) = 4 := by
  rw [akltOpenHamiltonian_eigenspace_eq_groundSpace hN,
    ← aklt_ker_hamiltonian_parentChainInteraction_two_eq_groundSpaceES hN,
    LinearEquiv.finrank_map_eq]
  exact aklt_finrank_ker_hamiltonian_parentChainInteraction_two hN

/-- The lower energy bound is attained on the open AKLT chain.
Source: arXiv:2011.12127, lines 1171--1174; the value is derived here. -/
theorem akltOpenHamiltonian_hasEigenvalue {N : ℕ} (hN : 2 ≤ N) :
    Module.End.HasEigenvalue (akltOpenHamiltonian N) (-(2 * (N - 1) / 3) : ℂ) := by
  rw [Module.End.hasEigenvalue_iff]
  intro h
  have hd := akltOpenHamiltonian_groundSpace_finrank hN
  rw [h] at hd
  norm_num at hd

end MPSTensor
