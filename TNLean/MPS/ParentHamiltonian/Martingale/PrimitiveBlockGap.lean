/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.BlockDiagonalProjectorDecay
import TNLean.MPS.ParentHamiltonian.PrimitiveBlockOpenGroundSpace
import TNLean.MPS.ParentHamiltonian.Martingale.PeriodicGapFromDivisibleOpen
import TNLean.MPS.ParentHamiltonian.Martingale.GroupedC3

/-!
# A uniform gap for parent Hamiltonians of primitive block sums

A finite family of inequivalent normalized primitive tensors admits parent
interactions with a uniform positive periodic gap. The interaction length may
be chosen above any prescribed bound. The proof combines the uniform
three-interval projector estimate, the grouped open-chain martingale bound,
and the finite-range comparison for periodic chains.

## References

* Nachtergaele, arXiv:cond-mat/9410110, Theorem 2.1(ii), lines 1130--1139,
  and Section 6, Lemma `commutation` (ii).
* The finite-range periodic comparison is recorded in
  `docs/paper-gaps/knabe88_finite_range_coefficient.tex`.
-/

open Filter
open scoped Topology ComplexOrder

namespace MPSTensor

variable {d r : ℕ} {dim : Fin r → ℕ} [NeZero d] [∀ j, NeZero (dim j)]

/-- Inequivalent normalized primitive blocks admit a uniformly gapped parent
interaction above every prescribed lower bound on its range. This combines
Nachtergaele's grouped estimate, Theorem 2.1(ii), with the finite-range
periodic comparison. The chosen range is twice a sufficiently large overlap
length; no assertion about every shorter admissible range is made here. -/
theorem exists_ge_parentHamiltonianES_toTensorFromBlocks_gap_of_isPrimitiveMPS
    (μ : Fin r → ℂ) (A : (j : Fin r) → MPSTensor d (dim j))
    (hμ : ∀ j, μ j ≠ 0)
    (ρ : ∀ j, Matrix (Fin (dim j)) (Fin (dim j)) ℂ)
    (hP : ∀ j, IsPrimitiveMPS (A j) (ρ j)) (hρ : ∀ j, (ρ j).PosDef)
    (hDistinct : ∀ i j, i ≠ j → ∀ h : dim j = dim i,
      ¬ GaugePhaseEquiv (h ▸ A j) (A i)) (Rmin : ℕ) :
    ∃ R : ℕ, Rmin ≤ R ∧ 0 < R ∧ ∃ γ : ℝ, 0 < γ ∧
      ∀ᶠ N : ℕ in atTop, ∀ v ∈
        (LinearMap.ker (parentHamiltonianES
          (toTensorFromBlocks (d := d) (μ := μ) A) R N))ᗮ,
        γ * ‖v‖ ≤ ‖parentHamiltonianES
          (toTensorFromBlocks (d := d) (μ := μ) A) R N v‖ := by
  obtain ⟨L₀, hL₀, hKernel⟩ :=
    exists_ker_openParentHamiltonianES_toTensorFromBlocks_eq_groundSpaceES_of_isPrimitiveMPS
      μ A hμ ρ hP hρ hDistinct
  obtain ⟨p, hp, hDefect⟩ := ((eventually_ge_atTop (max L₀ Rmin)).and
    (eventually_toTensorFromBlocks_projector_defect_le μ A hμ ρ hP hρ hDistinct
      (η := (1 / 2 : ℝ)) (by norm_num))).exists
  have hεlt : (1 / 2 : ℝ) < 1 / Real.sqrt 2 :=
    (lt_div_iff₀ (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2))).2
      (by linarith [Real.sqrt_two_lt_three_halves])
  have hγ : 0 < (1 - (1 / 2 : ℝ) * Real.sqrt 2) ^ 2 :=
    sq_pos_of_pos (by linarith [Real.sqrt_two_lt_three_halves])
  have hOpen := (eventually_ge_atTop (2 : ℕ)).mono fun M hM ↦
    openParentHamiltonianES_norm_gap_of_grouped_c3
      (toTensorFromBlocks (d := d) (μ := μ) A) (p := p) (by omega) hM
      (by norm_num) hεlt
      (grouped_martingaleDifference_norm_le_of_projector_defect
        (toTensorFromBlocks (d := d) (μ := μ) A) (by omega) hM
        (fun n hn ↦ hKernel (2 * p) n (by omega) hn) (by norm_num)
        (fun K ↦ hDefect K p (by omega)))
  obtain ⟨γ, hγpos, hPeriodic⟩ :=
    exists_parentHamiltonianES_gap_of_eventually_divisible_openParentHamiltonianES_gap
      (toTensorFromBlocks (d := d) (μ := μ) A) (by omega : 1 ≤ p)
      (by omega : 1 ≤ 2 * p) hγ hOpen
  exact ⟨2 * p, by omega, by omega, γ, hγpos, hPeriodic⟩

/-- A weighted direct sum of inequivalent normalized primitive blocks admits
an interaction range with a uniform positive periodic gap. This is the
existence-of-range consequence of Nachtergaele's Theorem 2.1(ii) and the
three-interval estimate of Section 6. -/
theorem exists_parentHamiltonianES_toTensorFromBlocks_gap_of_isPrimitiveMPS
    (μ : Fin r → ℂ) (A : (j : Fin r) → MPSTensor d (dim j))
    (hμ : ∀ j, μ j ≠ 0)
    (ρ : ∀ j, Matrix (Fin (dim j)) (Fin (dim j)) ℂ)
    (hP : ∀ j, IsPrimitiveMPS (A j) (ρ j)) (hρ : ∀ j, (ρ j).PosDef)
    (hDistinct : ∀ i j, i ≠ j → ∀ h : dim j = dim i,
      ¬ GaugePhaseEquiv (h ▸ A j) (A i)) :
    ∃ R : ℕ, 0 < R ∧ ∃ γ : ℝ, 0 < γ ∧
      ∀ᶠ N : ℕ in atTop, ∀ v ∈
        (LinearMap.ker (parentHamiltonianES
          (toTensorFromBlocks (d := d) (μ := μ) A) R N))ᗮ,
        γ * ‖v‖ ≤ ‖parentHamiltonianES
          (toTensorFromBlocks (d := d) (μ := μ) A) R N v‖ := by
  exact (exists_ge_parentHamiltonianES_toTensorFromBlocks_gap_of_isPrimitiveMPS
    μ A hμ ρ hP hρ hDistinct 0).imp fun _ h ↦ h.2

end MPSTensor
