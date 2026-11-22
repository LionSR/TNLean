/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Examples.PVBS.PVBSEnergyGap
import TNLean.MPS.Examples.PVBS.PVBSCriticalMagnon

/-!
# Exact periodic gap of the one-species PVBS model

The uniform one-particle vector is a zero-energy vector of the critical parent.
The periodic occupation decomposition therefore makes it an eigenvector with
energy `(μ - 1)² / (1 + μ²)` for real hopping μ. For positive noncritical μ,
this attains the uniform lower bound and determines the exact finite-ring gap.
At μ = 1 it joins the ground space; no zero finite-volume gap above the enlarged
kernel is asserted.

## References

 Bachmann–Nachtergaele, arXiv:1112.4097, Section II, the one-particle
dispersion following equation (8). The general multi-species thermodynamic
formula is a conjecture there and is not claimed here.

**Scope restriction (one species, zero phase, periodic boundary):** the general
multi-species thermodynamic gap conjecture is not asserted. See
`docs/paper-gaps/bn12_pvbs_periodic_gap.tex`.

The Hamiltonian is the Hamiltonian of the parent interaction on the ring
(`parentRingInteraction`), acting through `Matrix.toEuclideanLin`.
-/

open scoped Matrix BigOperators InnerProductSpace

namespace MPSTensor

private theorem particle_number_uniformParticle {N : ℕ} (σ : Cfg 2 N) :
    (∑ i : Fin N, ((σ i).val : ℂ)) *
      SpinChain.oneMagnon (fun _ : Fin N => (1 : ℂ)) σ =
        SpinChain.oneMagnon (fun _ : Fin N => (1 : ℂ)) σ := by
  by_cases hσ : ∃ j, σ = SpinChain.singleDown j
  · obtain ⟨j, rfl⟩ := hσ
    simp only [SpinChain.oneMagnon_singleDown, mul_one]
    have hval (i : Fin N) : ((SpinChain.singleDown j i).val : ℂ) =
        if i = j then 1 else 0 := by
      by_cases hi : i = j <;> simp [SpinChain.singleDown, hi]
    simp [hval]
  · simp [SpinChain.oneMagnon_eq_zero_of_not_singleDown
      (fun _ : Fin N => (1 : ℂ)) (by simpa using hσ)]

/-- The uniform one-particle mode has exactly the hopping-imbalance energy,
independently of the ring length. -/
theorem toEuclideanLin_hamiltonian_parentRingInteraction_pvbs_uniformParticle (μ : ℝ) {N : ℕ}
    (hN : 2 ≤ N) :
    haveI : NeZero N := ⟨by omega⟩;
    Matrix.toEuclideanLin (parentRingInteraction (pvbsTensor (μ : ℂ)) 2 N).hamiltonian
      (WithLp.toLp 2 (SpinChain.oneMagnon (fun _ : Fin N => (1 : ℂ)))) =
      (((μ - 1) ^ 2 / (1 + μ ^ 2) : ℝ) : ℂ) •
        WithLp.toLp 2 (SpinChain.oneMagnon (fun _ : Fin N => (1 : ℂ))) := by
  have : NeZero N := ⟨by omega⟩
  ext σ
  rw [toEuclideanLin_hamiltonian_parentRingInteraction_pvbs_decomposition μ hN,
    toEuclideanLin_hamiltonian_parentRingInteraction_pvbs_critical_uniformParticle hN]
  simp only [PiLp.zero_apply, mul_zero, zero_add, PiLp.smul_apply, smul_eq_mul]
  change _ * _ * SpinChain.oneMagnon (fun _ : Fin N => (1 : ℂ)) σ = _
  rw [mul_assoc, particle_number_uniformParticle]

/-- Any gap of the noncritical periodic PVBS Hamiltonian above its zero ground
energy is at most the energy of its uniform one-particle mode. -/
theorem hamiltonian_parentRingInteraction_pvbs_gap_le (μ : ℝ) (hμ : μ ≠ 1) {N : ℕ}
    (hN : 2 ≤ N) {γ : ℝ} (hgap : haveI : NeZero N := ⟨by omega⟩; ManyBody.IsGapped
      (parentRingInteraction (pvbsTensor (μ : ℂ)) 2 N).hamiltonian 0 γ) :
    γ ≤ (μ - 1) ^ 2 / (1 + μ ^ 2) := by
  have : NeZero N := ⟨by omega⟩
  let v : EuclideanSpace ℂ (Cfg 2 N) :=
    WithLp.toLp 2 (SpinChain.oneMagnon (fun _ : Fin N => (1 : ℂ)))
  have hvne : v ≠ 0 := by
    intro h
    have hz := congrArg (fun w : EuclideanSpace ℂ (Cfg 2 N) =>
      w (SpinChain.singleDown (⟨0, by omega⟩ : Fin N))) h
    simp [v] at hz
  have hc : 0 < (μ - 1) ^ 2 / (1 + μ ^ 2) :=
    div_pos (sq_pos_of_ne_zero (sub_ne_zero.mpr hμ)) (by positivity)
  have heig : Matrix.toEuclideanLin (parentRingInteraction (pvbsTensor (μ : ℂ)) 2 N).hamiltonian v =
      (((μ - 1) ^ 2 / (1 + μ ^ 2) : ℝ) : ℂ) • v :=
    toEuclideanLin_hamiltonian_parentRingInteraction_pvbs_uniformParticle μ hN
  rcases hgap.2 _ (Module.End.hasEigenvalue_of_hasEigenvector
    ⟨Module.End.mem_eigenspace_iff.mpr heig, hvne⟩) with h | h
  · exact absurd (Complex.ofReal_injective h) hc.ne'
  · simpa only [zero_add] using Complex.real_le_real.mp h

/-- The finite periodic one-species, zero-phase PVBS gap is exactly
`(μ - 1)² / (1 + μ²)` for every positive noncritical hopping and every ring
of at least two sites: the Hamiltonian is gapped above its zero ground energy
with this constant, and with no larger one. -/
theorem hamiltonian_parentRingInteraction_pvbs_gap_exact (μ : ℝ) (hμ : 0 < μ) (hμne : μ ≠ 1) :
    0 < (μ - 1) ^ 2 / (1 + μ ^ 2) ∧ ∀ (N : ℕ) (hN : 2 ≤ N),
      haveI : NeZero N := ⟨by omega⟩;
      ManyBody.IsGapped (parentRingInteraction (pvbsTensor (μ : ℂ)) 2 N).hamiltonian 0
        ((μ - 1) ^ 2 / (1 + μ ^ 2)) ∧
      ∀ γ : ℝ, ManyBody.IsGapped (parentRingInteraction (pvbsTensor (μ : ℂ)) 2 N).hamiltonian 0 γ →
        γ ≤ (μ - 1) ^ 2 / (1 + μ ^ 2) := by
  refine ⟨div_pos (sq_pos_of_ne_zero (sub_ne_zero.mpr hμne)) (by positivity), ?_⟩
  intro N hN
  exact ⟨isGapped_hamiltonian_parentRingInteraction_pvbs μ hμ.le hN,
    fun _ hgap => hamiltonian_parentRingInteraction_pvbs_gap_le μ hμne hN hgap⟩

end MPSTensor
