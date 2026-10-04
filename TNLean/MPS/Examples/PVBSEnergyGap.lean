/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Examples.PVBSHamiltonian
import TNLean.MPS.Examples.PVBSPeriodicGroundSpace

/-!
# Uniform periodic PVBS gap from particle number

The periodic decomposition into the positive critical parent and particle number
bounds the energy away from the vacuum. The conclusion uses the existing norm-gap
formulation on the orthogonal complement of the actual Hamiltonian kernel.

**Scope restriction (one species, zero phase, periodic boundary):** the general
multi-species thermodynamic gap conjecture is not asserted. See
`docs/paper-gaps/bn12_pvbs_periodic_gap.tex`.

-/

open scoped Matrix BigOperators InnerProductSpace ComplexConjugate

namespace MPSTensor

/-- The PVBS energy splits into a multiple of the critical energy and the
hopping-imbalance coefficient times the particle-number expectation. -/
theorem parentHamiltonianES_pvbs_energy_decomposition (μ : ℝ) {N : ℕ} (hN : 2 ≤ N)
    (v : EuclideanSpace ℂ (Cfg 2 N)) :
    (⟪v, parentHamiltonianES (pvbsTensor (μ : ℂ)) 2 N v⟫_ℂ).re =
      (2 * μ / (1 + μ ^ 2)) * (⟪v, parentHamiltonianES (pvbsTensor 1) 2 N v⟫_ℂ).re +
      ((μ - 1) ^ 2 / (1 + μ ^ 2)) *
        ∑ σ : Cfg 2 N, (∑ i : Fin N, ((σ i).val : ℝ)) * ‖v σ‖ ^ 2 := by
  let w : EuclideanSpace ℂ (Cfg 2 N) :=
    WithLp.toLp 2 (fun σ => (∑ i : Fin N, ((σ i).val : ℂ)) * v σ)
  have hw : (⟪v, w⟫_ℂ).re =
      ∑ σ : Cfg 2 N, (∑ i : Fin N, ((σ i).val : ℝ)) * ‖v σ‖ ^ 2 := by
    simp only [PiLp.inner_apply, RCLike.inner_apply, Complex.re_sum]
    apply Finset.sum_congr rfl
    intro σ _
    change (((∑ i : Fin N, ((σ i).val : ℂ)) * v σ) * conj (v σ)).re = _
    rw [mul_assoc, Complex.mul_conj]
    simp [Complex.sq_norm]
  have hH : parentHamiltonianES (pvbsTensor (μ : ℂ)) 2 N v =
      ((2 * μ / (1 + μ ^ 2) : ℝ) : ℂ) •
        parentHamiltonianES (pvbsTensor 1) 2 N v +
      (((μ - 1) ^ 2 / (1 + μ ^ 2) : ℝ) : ℂ) • w := by
    ext σ
    simpa only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, mul_assoc] using
      parentHamiltonianES_pvbs_decomposition μ hN v σ
  rw [hH, inner_add_right, inner_smul_right, inner_smul_right]
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, hw]

private theorem one_le_particle_count {N : ℕ} {σ : Cfg 2 N} (hσ : σ ≠ 0) :
    (1 : ℝ) ≤ ∑ i : Fin N, ((σ i).val : ℝ) := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hσ
  have hp : 0 < (σ i).val := Nat.pos_of_ne_zero fun h => hi (Fin.ext h)
  have h1 : (1 : ℝ) ≤ (σ i).val := by exact_mod_cast Nat.succ_le_of_lt hp
  exact h1.trans (Finset.single_le_sum (fun j _ => Nat.cast_nonneg ((σ j).val))
    (Finset.mem_univ i))

/-- A state with zero vacuum amplitude has particle-number expectation at least
its squared norm. -/
theorem pvbs_particle_number_ge_norm_sq {N : ℕ} (v : EuclideanSpace ℂ (Cfg 2 N))
    (hv : v 0 = 0) :
    ‖v‖ ^ 2 ≤ ∑ σ : Cfg 2 N, (∑ i : Fin N, ((σ i).val : ℝ)) * ‖v σ‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  apply Finset.sum_le_sum
  intro σ _
  by_cases hσ : σ = 0
  · simp [hσ, hv]
  · simpa using mul_le_mul_of_nonneg_right (one_le_particle_count hσ) (sq_nonneg ‖v σ‖)

/-- The actual periodic PVBS energy controls the norm on the vacuum-orthogonal
space, with a constant independent of the ring length. -/
theorem parentHamiltonianES_pvbs_energy_lower_bound (μ : ℝ) (hμ : 0 ≤ μ)
    {N : ℕ} (hN : 2 ≤ N) (v : EuclideanSpace ℂ (Cfg 2 N)) (hv : v 0 = 0) :
    ((μ - 1) ^ 2 / (1 + μ ^ 2)) * ‖v‖ ^ 2 ≤
      (⟪v, parentHamiltonianES (pvbsTensor (μ : ℂ)) 2 N v⟫_ℂ).re := by
  rw [parentHamiltonianES_pvbs_energy_decomposition μ hN]
  have ha : 0 ≤ 2 * μ / (1 + μ ^ 2) := by positivity
  have hc : 0 ≤ (μ - 1) ^ 2 / (1 + μ ^ 2) := by positivity
  have hcrit := (parentHamiltonianES_isPositive (pvbsTensor 1) 2 N).re_inner_nonneg_right v
  have hn := mul_le_mul_of_nonneg_left (pvbs_particle_number_ge_norm_sq v hv) hc
  exact hn.trans (le_add_of_nonneg_left (mul_nonneg ha hcrit))

/-- Orthogonality to the actual parent kernel implies zero vacuum amplitude. -/
theorem pvbs_zero_of_mem_orthogonal_parent_kernel (q : ℂ) {N : ℕ} (hN : 2 ≤ N)
    {v : EuclideanSpace ℂ (Cfg 2 N)}
    (hv : v ∈ (LinearMap.ker (parentHamiltonianES (pvbsTensor q) 2 N))ᗮ) : v 0 = 0 := by
  let e := WithLp.linearEquiv 2 ℂ (NSiteSpace 2 N)
  have hraw := pvbsVacuum_mem_chainGroundSpace q hN
  rw [← ker_parentHamiltonian_eq_chainGroundSpace _ (by omega) hN] at hraw
  have hΩ : e.symm (pvbsVacuum N) ∈
      LinearMap.ker (parentHamiltonianES (pvbsTensor q) 2 N) := by
    rw [LinearMap.mem_ker]
    simpa [parentHamiltonianES, e] using congrArg e.symm (LinearMap.mem_ker.mp hraw)
  rw [Submodule.mem_orthogonal] at hv
  have h := hv (e.symm (pvbsVacuum N)) hΩ
  simpa [e, pvbsVacuum, PiLp.inner_apply, RCLike.inner_apply, Pi.single_apply] using h

/-- The periodic one-species PVBS parent has the uniform norm-gap bound
`(μ - 1)² / (1 + μ²)` for nonnegative real hopping. The bound is positive
when the hopping is noncritical. -/
theorem parentHamiltonianES_pvbs_gap (μ : ℝ) (hμ : 0 ≤ μ) {N : ℕ} (hN : 2 ≤ N) :
    ∀ v ∈ (LinearMap.ker (parentHamiltonianES (pvbsTensor (μ : ℂ)) 2 N))ᗮ,
      ((μ - 1) ^ 2 / (1 + μ ^ 2)) * ‖v‖ ≤
        ‖parentHamiltonianES (pvbsTensor (μ : ℂ)) 2 N v‖ := by
  intro v hv
  have henergy := parentHamiltonianES_pvbs_energy_lower_bound μ hμ hN v
    (pvbs_zero_of_mem_orthogonal_parent_kernel (μ : ℂ) hN hv)
  have hCS := @re_inner_le_norm ℂ _ _ _ _ v
    (parentHamiltonianES (pvbsTensor (μ : ℂ)) 2 N v)
  by_cases hv0 : v = 0
  · simp [hv0]
  · have hmul : ((μ - 1) ^ 2 / (1 + μ ^ 2)) * ‖v‖ * ‖v‖ ≤
        ‖parentHamiltonianES (pvbsTensor (μ : ℂ)) 2 N v‖ * ‖v‖ := by
      calc
        _ = ((μ - 1) ^ 2 / (1 + μ ^ 2)) * ‖v‖ ^ 2 := by ring
        _ ≤ (⟪v, parentHamiltonianES (pvbsTensor (μ : ℂ)) 2 N v⟫_ℂ).re := henergy
        _ ≤ ‖v‖ * ‖parentHamiltonianES (pvbsTensor (μ : ℂ)) 2 N v‖ := hCS
        _ = _ := mul_comm _ _
    exact le_of_mul_le_mul_right hmul (norm_pos_iff.mpr hv0)

end MPSTensor
