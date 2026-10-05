/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Examples.PVBSHamiltonian
import TNLean.Algebra.OneMagnon

/-!
# Critical PVBS dynamics in the one-particle sector

The double-occupation projector vanishes on every one-particle vector.
The remaining critical local interaction is one half of identity minus site
exchange, so the actual periodic parent Hamiltonian acts by the cycle Laplacian.

## References

Bachmann–Nachtergaele, arXiv:1112.4097, Section II, the one-particle
dispersion after equation (8), specialized to one species and zero phase.
-/

open scoped Matrix BigOperators InnerProductSpace

namespace MPSTensor

/-- On the full one-particle sector, the critical PVBS local term is the singlet
exchange term. This identity uses the actual canonical parent interaction. -/
theorem localTermES_pvbs_critical_oneMagnon {N : ℕ} (hN : 2 ≤ N)
    (f : Fin N → ℂ) (i : Fin N) (σ : Cfg 2 N) :
    localTermES (pvbsTensor 1) 2 i (WithLp.toLp 2 (SpinChain.oneMagnon f)) σ =
      (SpinChain.oneMagnon f σ -
        SpinChain.oneMagnon f (σ ∘ Equiv.swap i (cyclicForwardSite i 1))) / 2 := by
  let : NeZero N := ⟨by omega⟩
  have hn : cyclicForwardSite i 1 ≠ i := by
    rw [← cyclicSuccessorEquiv_apply]
    exact cyclicSuccessorEquiv_ne hN i
  have h := localTermES_pvbs_two_apply 1 hN i (WithLp.toLp 2 (SpinChain.oneMagnon f)) σ
  norm_num only [Complex.ofReal_one, one_pow, one_mul] at h
  rw [h]
  change (((((σ i).val : ℂ) + (σ (cyclicForwardSite i 1)).val) *
    SpinChain.oneMagnon f σ -
      (if σ i = σ (cyclicForwardSite i 1) then 0 else
        SpinChain.oneMagnon f (σ ∘ Equiv.swap i (cyclicForwardSite i 1)))) / 2) = _
  simp_rw [SpinChain.oneMagnon_comp_swap]
  by_cases hσ : ∃ j, σ = SpinChain.singleDown j
  · obtain ⟨j, rfl⟩ := hσ
    simp only [SpinChain.oneMagnon_singleDown, Function.comp_apply]
    by_cases hi : i = j
    · subst j
      simp [SpinChain.singleDown, hn]
    · by_cases hj : cyclicForwardSite i 1 = j
      · subst j
        simp [SpinChain.singleDown, hi]
      · simp [SpinChain.singleDown, hi, hj, Ne.symm hi, Ne.symm hj,
          Equiv.swap_apply_def]
  · have hnot : ∀ j, σ ≠ SpinChain.singleDown j := by simpa using hσ
    have hz (g : Fin N → ℂ) : SpinChain.oneMagnon g σ = 0 :=
      SpinChain.oneMagnon_eq_zero_of_not_singleDown g hnot
    simp [hz]

/-- The actual critical periodic PVBS parent acts by the normalized cycle
Laplacian on one-particle coefficients, including the two-site ring. -/
theorem parentHamiltonianES_pvbs_critical_oneMagnon {N : ℕ} [NeZero N] (hN : 2 ≤ N)
    (f : Fin N → ℂ) :
    parentHamiltonianES (pvbsTensor 1) 2 N (WithLp.toLp 2 (SpinChain.oneMagnon f)) =
      WithLp.toLp 2 (SpinChain.oneMagnon (fun j =>
        f j - (f (cyclicSuccessorEquiv N j) + f ((cyclicSuccessorEquiv N).symm j)) / 2)) := by
  rw [parentHamiltonianES_eq_sum_localTermES]
  ext σ
  simp only [LinearMap.sum_apply, WithLp.ofLp_sum, Finset.sum_apply,
    localTermES_pvbs_critical_oneMagnon hN, ← Finset.sum_div]
  simp_rw [← cyclicSuccessorEquiv_apply]
  exact SpinChain.oneMagnon_edge_sum (cyclicSuccessorEquiv N)
    (cyclicSuccessorEquiv_ne hN) f σ

/-- At critical hopping, the uniform one-particle vector is a periodic ground
state on every ring of at least two sites. -/
theorem parentHamiltonianES_pvbs_critical_uniformParticle {N : ℕ} (hN : 2 ≤ N) :
    parentHamiltonianES (pvbsTensor 1) 2 N
      (WithLp.toLp 2 (SpinChain.oneMagnon (fun _ : Fin N => (1 : ℂ)))) = 0 := by
  let : NeZero N := ⟨by omega⟩
  rw [parentHamiltonianES_pvbs_critical_oneMagnon hN]
  ext σ
  norm_num [SpinChain.oneMagnon]

end MPSTensor
