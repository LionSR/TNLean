/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Examples.PVBSLocalInteraction
import TNLean.MPS.ParentHamiltonian.CyclicWindowPermutation
import TNLean.MPS.ParentHamiltonian.Martingale.Transport

/-!
# Periodic PVBS Hamiltonian and particle number

Periodic summation cancels the asymmetric boundary fields. The resulting
Hamiltonian is a nonnegative multiple of the critical PVBS parent Hamiltonian
plus `(μ - 1)² / (1 + μ²)` times particle number. This identity retains the
two oriented windows when the ring has exactly two sites.

## References

Bachmann–Nachtergaele, arXiv:1112.4097, Section II, equations (4)–(8),
restricted here to one species with zero phase.
-/

open scoped Matrix BigOperators InnerProductSpace

namespace MPSTensor

/-- The actual translated PVBS interaction has the occupation/hopping formula
at every cyclic bond, including either orientation of a two-site ring. -/
theorem localTermES_pvbs_two_apply (μ : ℝ) {N : ℕ} (hN : 2 ≤ N) (i : Fin N)
    (v : EuclideanSpace ℂ (Cfg 2 N)) (σ : Cfg 2 N) :
    localTermES (pvbsTensor (μ : ℂ)) 2 i v σ =
      (((μ : ℂ) ^ 2 * (σ i).val + (σ (cyclicForwardSite i 1)).val) * v σ -
        (μ : ℂ) * (if σ i = σ (cyclicForwardSite i 1) then 0
          else v (σ ∘ Equiv.swap i (cyclicForwardSite i 1)))) / (1 + (μ : ℂ) ^ 2) := by
  rw [localTermES_apply _ 2 i hN]
  change parentInteraction (pvbsTensor (μ : ℂ)) 2
    (fun τ => v (cyclicCfg (Fin.pos i) 2 i τ σ)) (extractWindow 2 i σ) = _
  rw [parentInteraction_pvbs_two_apply,
    cyclicCfg_extractWindow (Fin.pos i) hN,
    cyclicCfg_extractWindow_comp_swap_of_le (Fin.pos i) hN]
  simp [extractWindow, cyclicForwardSite, Nat.mod_eq_of_lt i.isLt, mul_ite]
  split_ifs <;> simp_all

/-- Relative to the critical interaction, the local change is a diagonal
occupation field with different weights at the two ends of the bond. -/
theorem localTermES_pvbs_decomposition (μ : ℝ) {N : ℕ} (hN : 2 ≤ N) (i : Fin N)
    (v : EuclideanSpace ℂ (Cfg 2 N)) (σ : Cfg 2 N) :
    localTermES (pvbsTensor (μ : ℂ)) 2 i v σ =
      ((2 * μ / (1 + μ ^ 2) : ℝ) : ℂ) * localTermES (pvbsTensor 1) 2 i v σ +
        ( (((μ ^ 2 - μ) / (1 + μ ^ 2) : ℝ) : ℂ) * (σ i).val +
          (((1 - μ) / (1 + μ ^ 2) : ℝ) : ℂ) * (σ (cyclicForwardSite i 1)).val ) *
            v σ := by
  have hdreal : 0 < 1 + μ ^ 2 := by positivity
  have hd : (1 + (μ : ℂ) ^ 2) ≠ 0 := by exact_mod_cast hdreal.ne'
  rw [localTermES_pvbs_two_apply μ hN]
  have h := localTermES_pvbs_two_apply 1 hN i v σ
  norm_num only [Complex.ofReal_one, one_pow, one_mul] at h
  rw [h]
  push_cast
  field_simp
  ring

/-- On a periodic ring, the PVBS Hamiltonian is the sum of a positive multiple
of the critical parent and the squared hopping imbalance times particle number. -/
theorem parentHamiltonianES_pvbs_decomposition (μ : ℝ) {N : ℕ} (hN : 2 ≤ N)
    (v : EuclideanSpace ℂ (Cfg 2 N)) (σ : Cfg 2 N) :
    parentHamiltonianES (pvbsTensor (μ : ℂ)) 2 N v σ =
      ((2 * μ / (1 + μ ^ 2) : ℝ) : ℂ) *
        parentHamiltonianES (pvbsTensor 1) 2 N v σ +
      ((((μ - 1) ^ 2 / (1 + μ ^ 2) : ℝ) : ℂ) *
        (∑ i : Fin N, ((σ i).val : ℂ))) * v σ := by
  let : NeZero N := ⟨by omega⟩
  have hshift : ∑ i : Fin N, ((σ (cyclicForwardSite i 1)).val : ℂ) =
      ∑ i : Fin N, ((σ i).val : ℂ) := by
    simp_rw [← cyclicSuccessorEquiv_apply]
    exact Equiv.sum_comp (cyclicSuccessorEquiv N) (fun i => ((σ i).val : ℂ))
  rw [parentHamiltonianES_eq_sum_localTermES,
    parentHamiltonianES_eq_sum_localTermES]
  simp only [LinearMap.sum_apply, WithLp.ofLp_sum, Finset.sum_apply,
    localTermES_pvbs_decomposition μ hN, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.sum_mul, hshift]
  push_cast
  ring

end MPSTensor
