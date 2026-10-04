/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Examples.AKLTOpenBoundary
import TNLean.MPS.Examples.AKLTPolynomialHamiltonian

/-!
# The open bilinear-biquadratic AKLT Hamiltonian

Summing the local spin-two projector identity over the nonwrapping bonds
identifies the physical open-chain Hamiltonian with twice the projector parent,
shifted by \(-2(N-1)/3\). This provides the physical-Hamiltonian interpretation
of the four-dimensional edge space in arXiv:2011.12127, lines 1171--1174.
The Hamiltonian polynomial is printed in arXiv:quant-ph/0608197,
`Papers/quant-ph_0608197/MPSarchive.tex`, lines 340--349, equation `HAKLT`.
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

/-- The same open AKLT Hamiltonian on the standard physical Hilbert space.
Source: arXiv:2011.12127, lines 1171--1174. -/
def akltOpenHamiltonianES (N : ℕ) :
    EuclideanSpace ℂ (Cfg 3 N) →ₗ[ℂ] EuclideanSpace ℂ (Cfg 3 N) :=
  (WithLp.linearEquiv 2 ℂ (NSiteSpace 3 N)).symm.toLinearMap ∘ₗ
    akltOpenHamiltonian N ∘ₗ (WithLp.linearEquiv 2 ℂ (NSiteSpace 3 N)).toLinearMap

private theorem card_twoSite_nonwrappingStart (N : ℕ) :
    Fintype.card (NonwrappingStart 2 N) = N - 1 := by
  let e : NonwrappingStart 2 N ≃ Fin (N - 1) :=
    { toFun := fun i => ⟨i.1.val, by have := i.2; omega⟩
      invFun := fun i => ⟨⟨i.val, by have := i.isLt; omega⟩, by
        change i.val + 2 ≤ N
        have := i.isLt
        omega⟩
      left_inv := by intro i; rfl
      right_inv := by intro i; rfl }
  exact (Fintype.card_congr e).trans (Fintype.card_fin _)

/-- The exact open-chain shift is \(2(N-1)/3\), one contribution per
nonwrapping bond. This follows from the local spin-two projector identity
of arXiv:quant-ph/0608197, equation `HAKLT`. -/
theorem akltOpenHamiltonianES_add_eq_parent {N : ℕ} (hN : 2 ≤ N) :
    akltOpenHamiltonianES N + (2 * (N - 1) / 3 : ℂ) • LinearMap.id =
      (2 : ℂ) • openParentHamiltonianES akltTensor 2 N := by
  refine LinearMap.ext fun ψ => ?_
  apply (WithLp.linearEquiv 2 ℂ (NSiteSpace 3 N)).injective
  ext σ
  simp only [akltOpenHamiltonianES, akltOpenHamiltonian, openParentHamiltonianES,
    localTermES, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply,
    LinearMap.sum_apply, LinearMap.comp_apply, map_add, map_smul, map_sum,
    LinearEquiv.coe_toLinearMap, LinearEquiv.apply_symm_apply,
    Finset.sum_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    aklt_localTerm_two_apply hN, Finset.mul_sum, Finset.sum_add_distrib]
  simp only [show ∀ x y z : ℂ, 2 * (1 / 2 * (x + y + z)) = x + y + z from
      fun x y z => by ring, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    card_twoSite_nonwrappingStart, nsmul_eq_mul]
  push_cast [Nat.cast_sub (by omega : 1 ≤ N)]
  ring

/-- The shifted open-chain polynomial Hamiltonian is positive.
Source: arXiv:2011.12127, lines 1171--1174; the energy shift is derived here. -/
theorem akltOpenHamiltonianES_add_isPositive {N : ℕ} (hN : 2 ≤ N) :
    (akltOpenHamiltonianES N + (2 * (N - 1) / 3 : ℂ) • LinearMap.id).IsPositive := by
  rw [akltOpenHamiltonianES_add_eq_parent hN]
  exact (openParentHamiltonianES_isPositive akltTensor 2 N).smul_of_nonneg
    (by norm_num [Complex.le_def])

/-- Every eigenvalue is bounded below by the open-chain ground energy.
Source: arXiv:2011.12127, lines 1171--1174; the value is derived from the
local projector identity. -/
theorem akltOpenHamiltonianES_eigenvalue_ge {N : ℕ} (hN : 2 ≤ N) {μ : ℂ}
    (hμ : Module.End.HasEigenvalue (akltOpenHamiltonianES N) μ) :
    -(2 * (N - 1) / 3 : ℂ) ≤ μ := by
  obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
  have hpos : 0 ≤ μ + (2 * (N - 1) / 3 : ℂ) :=
    (akltOpenHamiltonianES_add_isPositive hN).nonneg_of_apply_eq_smul (v := v)
      hv.2 (by simp [Module.End.mem_eigenspace_iff.1 hv.1, add_smul])
  rw [← sub_nonneg, sub_neg_eq_add]
  exact hpos

/-- The lowest-energy space of the open polynomial Hamiltonian is exactly
the open AKLT matrix-product space. Source: arXiv:2011.12127, lines 1171--1174. -/
theorem akltOpenHamiltonianES_eigenspace_eq_groundSpaceES {N : ℕ} (hN : 2 ≤ N) :
    Module.End.eigenspace (akltOpenHamiltonianES N) (-(2 * (N - 1) / 3) : ℂ) =
      groundSpaceES akltTensor N := by
  rw [← aklt_ker_openParentHamiltonianES_two_eq_groundSpaceES hN]
  ext v
  have hv := LinearMap.congr_fun (akltOpenHamiltonianES_add_eq_parent hN) v
  simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply] at hv
  rw [Module.End.mem_eigenspace_iff, LinearMap.mem_ker,
    ← smul_eq_zero_iff_right (by norm_num : (2 : ℂ) ≠ 0), ← hv,
    neg_smul, ← sub_eq_zero, sub_neg_eq_add]

/-- The open polynomial AKLT Hamiltonian has four ground states for every
\(N\ge2\). Source: arXiv:2011.12127, lines 1171--1174. -/
theorem akltOpenHamiltonianES_groundSpace_finrank {N : ℕ} (hN : 2 ≤ N) :
    Module.finrank ℂ
      (Module.End.eigenspace (akltOpenHamiltonianES N) (-(2 * (N - 1) / 3) : ℂ)) = 4 := by
  rw [akltOpenHamiltonianES_eigenspace_eq_groundSpaceES hN,
    ← aklt_ker_openParentHamiltonianES_two_eq_groundSpaceES hN]
  exact aklt_finrank_ker_openParentHamiltonianES_two hN

/-- The lower energy bound is attained on the open AKLT chain.
Source: arXiv:2011.12127, lines 1171--1174; the value is derived here. -/
theorem akltOpenHamiltonianES_hasEigenvalue {N : ℕ} (hN : 2 ≤ N) :
    Module.End.HasEigenvalue (akltOpenHamiltonianES N) (-(2 * (N - 1) / 3) : ℂ) := by
  rw [Module.End.hasEigenvalue_iff]
  intro h
  have hd := akltOpenHamiltonianES_groundSpace_finrank hN
  rw [h] at hd
  norm_num at hd

end MPSTensor
