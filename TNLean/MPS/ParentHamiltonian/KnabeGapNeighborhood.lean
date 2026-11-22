/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.OpenGapContinuity
import TNLean.MPS.ParentHamiltonian.Martingale.FiniteRangeKnabeGap
import TNLean.Wielandt.SpanGrowth.CumulativeSpan

/-!
# Parameter neighborhoods with a uniform nearest-neighbor gap

A strict finite-window Knabe estimate is stable along a continuous family
of one-site injective tensors. Consequently one positive periodic gap bound
works in a whole parameter neighborhood and for every sufficiently long
chain. This is a local ingredient of the compact-parameter gap argument in
arXiv:1010.3732, Appendix A.
-/

open scoped Topology ComplexOrder

namespace MPSTensor

/-- A strict nearest-neighbor Knabe window at one parameter yields a gap
uniform over a neighborhood and all chains beyond the same length threshold.
Source: arXiv:1010.3732, Appendix A; the finite-size estimate is the
nearest-neighbor case of Knabe's inequality. -/
theorem eventually_hamiltonian_parentRingInteraction_gap_of_strict_openGap
    {X : Type*} [TopologicalSpace X] {d D m : ℕ} [NeZero D]
    (A : X → MPSTensor d D) (hA : Continuous A)
    (hInj : ∀ x, Kraus.IsInjective (A x)) (hm : 2 ≤ m) {x₀ : X}
    {γ : ℝ} (hnum : 1 < (m : ℝ) * γ)
    (hgap : ∀ μ : ℂ, Module.End.HasEigenvalue
      (Matrix.toEuclideanLin (parentChainInteraction (A x₀) 2 (m + 1)).hamiltonian) μ →
        μ = 0 ∨ (γ : ℂ) ≤ μ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ x in 𝓝 x₀, ∀ (N : ℕ) (hN : 2 * m ≤ N),
      haveI : NeZero N := ⟨by omega⟩;
      ∀ μ : ℂ, Module.End.HasEigenvalue
        (Matrix.toEuclideanLin (parentRingInteraction (A x) 2 N).hamiltonian) μ →
          μ = 0 ∨ (δ : ℂ) ≤ μ := by
  have hmpos : 0 < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  have hthreshold : 1 / (m : ℝ) < γ := (div_lt_iff₀ hmpos).2 (by simpa [mul_comm] using hnum)
  obtain ⟨γ', hγ'lower, hγ'upper⟩ := exists_between hthreshold
  have hγpos : 0 < γ := (div_pos zero_lt_one hmpos).trans hthreshold
  have hgap' : ∀ v ∈ (groundSpaceES (A x₀) (m + 1))ᗮ,
      γ * ‖v‖ ≤
        ‖Matrix.toEuclideanLin (parentChainInteraction (A x₀) 2 (m + 1)).hamiltonian v‖ := by
    rw [← ker_hamiltonian_parentChainInteraction_eq_groundSpaceES_of_isNBlkInjective
      (Kraus.isNBlkInjective_one_of_isInjective (hInj x₀)) (by omega) (by omega)]
    exact (ManyBody.forall_hasEigenvalue_iff_norm
      (posSemidef_hamiltonian_parentChainInteraction (A x₀) 2 (m + 1))).mp hgap
  have hnear := eventually_hamiltonian_parentChainInteraction_gap A hA
    (fun x => isNBlkInjective_of_le one_pos
      (Kraus.isNBlkInjective_one_of_isInjective (hInj x)) (by omega))
    (fun x => isNBlkInjective_of_le one_pos
      (Kraus.isNBlkInjective_one_of_isInjective (hInj x)) (by omega)) hγpos hγ'upper hgap'
  have hnum' : ((2 : ℝ) - 1) ^ 2 < (m : ℝ) * γ' := by
    have h := (div_lt_iff₀ hmpos).1 hγ'lower
    norm_num at *
    nlinarith
  let δ : ℝ := ((m : ℝ) * γ' - ((2 : ℝ) - 1) ^ 2) / ((m : ℝ) - 2 + 1)
  refine ⟨δ, ?_, ?_⟩
  · apply div_pos (sub_pos.mpr hnum')
    have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  · filter_upwards [hnear] with x hx N hN
    refine (hamiltonian_parentRingInteraction_gap_of_hamiltonian_parentChainInteraction_gap (A x)
      (R := 2) (m := m) (by omega) hm hnum' ?_).2 N hN
    refine (ManyBody.forall_hasEigenvalue_iff_norm
      (posSemidef_hamiltonian_parentChainInteraction (A x) 2 _)).mpr ?_
    rw [show m + 2 - 1 = m + 1 by omega,
      ker_hamiltonian_parentChainInteraction_eq_groundSpaceES_of_isNBlkInjective
        (Kraus.isNBlkInjective_one_of_isInjective (hInj x)) (by omega) (by omega)]
    exact hx

end MPSTensor
