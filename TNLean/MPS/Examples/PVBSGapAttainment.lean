/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Examples.PVBSEnergyGap
import TNLean.Algebra.OneMagnon

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

-/

open scoped Matrix BigOperators InnerProductSpace

namespace MPSTensor

private theorem localTermES_pvbs_critical_uniformParticle {N : ℕ} (hN : 2 ≤ N)
    (i : Fin N) (σ : Cfg 2 N) :
    localTermES (pvbsTensor 1) 2 i
      (WithLp.toLp 2 (SpinChain.oneMagnon (fun _ : Fin N => (1 : ℂ)))) σ = 0 := by
  let : NeZero N := ⟨by omega⟩
  have hn : cyclicForwardSite i 1 ≠ i := by
    rw [← cyclicSuccessorEquiv_apply]
    exact cyclicSuccessorEquiv_ne hN i
  have hswap : SpinChain.oneMagnon (fun _ : Fin N => (1 : ℂ))
      (σ ∘ Equiv.swap i (cyclicForwardSite i 1)) =
      SpinChain.oneMagnon (fun _ : Fin N => (1 : ℂ)) σ := by
    rw [SpinChain.oneMagnon_comp_swap]
    rfl
  have h := localTermES_pvbs_two_apply 1 hN i
    (WithLp.toLp 2 (SpinChain.oneMagnon (fun _ : Fin N => (1 : ℂ)))) σ
  norm_num only [Complex.ofReal_one, one_pow, one_mul] at h
  rw [h]
  change (((((σ i).val : ℂ) + (σ (cyclicForwardSite i 1)).val) *
    SpinChain.oneMagnon (fun _ : Fin N => (1 : ℂ)) σ -
      (if σ i = σ (cyclicForwardSite i 1) then 0 else
        SpinChain.oneMagnon (fun _ : Fin N => (1 : ℂ))
          (σ ∘ Equiv.swap i (cyclicForwardSite i 1)))) / 2) = 0
  rw [hswap]
  by_cases hσ : ∃ j, σ = SpinChain.singleDown j
  · obtain ⟨j, rfl⟩ := hσ
    simp only [SpinChain.oneMagnon_singleDown, mul_one]
    by_cases hi : i = j
    · subst j
      simp [SpinChain.singleDown, hn]
    · by_cases hj : cyclicForwardSite i 1 = j
      · simp [SpinChain.singleDown, hi, hj]
      · simp [SpinChain.singleDown, hi, hj]
  · have hz := SpinChain.oneMagnon_eq_zero_of_not_singleDown
      (fun _ : Fin N => (1 : ℂ)) (by simpa using hσ)
    simp [hz]

/-- At critical hopping, the uniform one-particle vector is a periodic ground
state on every ring of at least two sites. -/
theorem parentHamiltonianES_pvbs_critical_uniformParticle {N : ℕ} (hN : 2 ≤ N) :
    parentHamiltonianES (pvbsTensor 1) 2 N
      (WithLp.toLp 2 (SpinChain.oneMagnon (fun _ : Fin N => (1 : ℂ)))) = 0 := by
  rw [parentHamiltonianES_eq_sum_localTermES]
  ext σ
  simp only [LinearMap.sum_apply, WithLp.ofLp_sum, Finset.sum_apply, PiLp.zero_apply]
  exact Finset.sum_eq_zero fun i _ => localTermES_pvbs_critical_uniformParticle hN i σ

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
theorem parentHamiltonianES_pvbs_uniformParticle (μ : ℝ) {N : ℕ} (hN : 2 ≤ N) :
    parentHamiltonianES (pvbsTensor (μ : ℂ)) 2 N
      (WithLp.toLp 2 (SpinChain.oneMagnon (fun _ : Fin N => (1 : ℂ)))) =
      (((μ - 1) ^ 2 / (1 + μ ^ 2) : ℝ) : ℂ) •
        WithLp.toLp 2 (SpinChain.oneMagnon (fun _ : Fin N => (1 : ℂ))) := by
  ext σ
  rw [parentHamiltonianES_pvbs_decomposition μ hN,
    parentHamiltonianES_pvbs_critical_uniformParticle hN]
  simp only [PiLp.zero_apply, mul_zero, zero_add, PiLp.smul_apply, smul_eq_mul]
  change _ * _ * SpinChain.oneMagnon (fun _ : Fin N => (1 : ℂ)) σ = _
  rw [mul_assoc, particle_number_uniformParticle]

/-- Any norm-gap bound for the noncritical periodic PVBS Hamiltonian is at most
the energy of its uniform one-particle mode. -/
theorem parentHamiltonianES_pvbs_gap_le (μ : ℝ) (hμ : μ ≠ 1) {N : ℕ} (hN : 2 ≤ N)
    {γ : ℝ} (hgap : ∀ v ∈
      (LinearMap.ker (parentHamiltonianES (pvbsTensor (μ : ℂ)) 2 N))ᗮ,
      γ * ‖v‖ ≤ ‖parentHamiltonianES (pvbsTensor (μ : ℂ)) 2 N v‖) :
    γ ≤ (μ - 1) ^ 2 / (1 + μ ^ 2) := by
  let v : EuclideanSpace ℂ (Cfg 2 N) :=
    WithLp.toLp 2 (SpinChain.oneMagnon (fun _ : Fin N => (1 : ℂ)))
  have hvne : v ≠ 0 := by
    intro h
    have hz := congrArg (fun w : EuclideanSpace ℂ (Cfg 2 N) =>
      w (SpinChain.singleDown (⟨0, by omega⟩ : Fin N))) h
    simp [v] at hz
  have hc : 0 < (μ - 1) ^ 2 / (1 + μ ^ 2) :=
    div_pos (sq_pos_of_ne_zero (sub_ne_zero.mpr hμ)) (by positivity)
  have heig := parentHamiltonianES_pvbs_uniformParticle μ hN
  have horth : v ∈ (LinearMap.ker (parentHamiltonianES (pvbsTensor (μ : ℂ)) 2 N))ᗮ := by
    rw [Submodule.mem_orthogonal]
    intro w hw
    have h := (parentHamiltonianES_isPositive (pvbsTensor (μ : ℂ)) 2 N).isSymmetric w v
    rw [LinearMap.mem_ker.mp hw, inner_zero_left, heig, inner_smul_right] at h
    exact (mul_eq_zero.mp h.symm).resolve_left (Complex.ofReal_ne_zero.mpr hc.ne')
  have hh := hgap v horth
  rw [heig, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc] at hh
  exact le_of_mul_le_mul_right hh (norm_pos_iff.mpr hvne)

/-- The finite periodic one-species, zero-phase PVBS gap is exactly
`(μ - 1)² / (1 + μ²)` for every positive noncritical hopping and every ring
of at least two sites. This is both a uniform lower bound and the largest
possible norm-gap constant for the actual positive parent Hamiltonian. -/
theorem parentHamiltonianES_pvbs_gap_exact (μ : ℝ) (hμ : 0 < μ) (hμne : μ ≠ 1) :
    0 < (μ - 1) ^ 2 / (1 + μ ^ 2) ∧ ∀ N : ℕ, 2 ≤ N →
      (∀ v ∈ (LinearMap.ker (parentHamiltonianES (pvbsTensor (μ : ℂ)) 2 N))ᗮ,
        ((μ - 1) ^ 2 / (1 + μ ^ 2)) * ‖v‖ ≤
          ‖parentHamiltonianES (pvbsTensor (μ : ℂ)) 2 N v‖) ∧
      ∀ γ : ℝ, (∀ v ∈
        (LinearMap.ker (parentHamiltonianES (pvbsTensor (μ : ℂ)) 2 N))ᗮ,
        γ * ‖v‖ ≤ ‖parentHamiltonianES (pvbsTensor (μ : ℂ)) 2 N v‖) →
          γ ≤ (μ - 1) ^ 2 / (1 + μ ^ 2) := by
  refine ⟨div_pos (sq_pos_of_ne_zero (sub_ne_zero.mpr hμne)) (by positivity), ?_⟩
  intro N hN
  exact ⟨parentHamiltonianES_pvbs_gap μ hμ.le hN,
    fun _ hgap => parentHamiltonianES_pvbs_gap_le μ hμne hN hgap⟩

end MPSTensor
