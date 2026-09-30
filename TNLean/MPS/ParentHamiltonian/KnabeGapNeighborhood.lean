/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.OpenGapContinuity
import TNLean.MPS.ParentHamiltonian.Martingale.FiniteRangeKnabeGap
import TNLean.MPS.Core.Blocking

/-!
# Parameter neighborhoods with a uniform nearest-neighbor gap

A strict finite-window Knabe estimate is stable along a continuous family
of one-site injective tensors. Consequently one positive periodic gap bound
works in a whole parameter neighborhood and for every sufficiently long
chain. This is a local ingredient of the compact-parameter gap argument in
arXiv:1010.3732, Appendix A.
-/

open scoped Topology

namespace MPSTensor

/-- One-site injectivity supplies the fixed-length injectivity hypotheses in
the finite-window continuity argument. Source: arXiv:1010.3732, Appendix A. -/
private theorem isNBlkInjective_of_one_site {d D L : ℕ}
    {A : MPSTensor d D} (hA : Kraus.IsInjective A) (hL : 0 < L) :
    Kraus.IsNBlkInjective A L := by
  simpa using isNBlkInjective_mul_of_isNBlkInjective A hL
    (Kraus.isNBlkInjective_one_of_isInjective hA)

/-- A strict nearest-neighbor Knabe window at one parameter yields a gap
uniform over a neighborhood and all chains beyond the same length threshold.
Source: arXiv:1010.3732, Appendix A; the finite-size estimate is the
nearest-neighbor case of Knabe's inequality. -/
theorem eventually_parentHamiltonianES_gap_of_strict_openGap
    {X : Type*} [TopologicalSpace X] {d D m : ℕ} [NeZero D]
    (A : X → MPSTensor d D) (hA : Continuous A)
    (hInj : ∀ x, Kraus.IsInjective (A x)) (hm : 2 ≤ m) {x₀ : X}
    {γ : ℝ} (hnum : 1 < (m : ℝ) * γ)
    (hgap : ∀ v ∈ (groundSpaceES (A x₀) (m + 1))ᗮ,
      γ * ‖v‖ ≤ ‖openParentHamiltonianES (A x₀) 2 (m + 1) v‖) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ x in 𝓝 x₀, ∀ N : ℕ, 2 * m ≤ N →
      ∀ v ∈ (LinearMap.ker (parentHamiltonianES (A x) 2 N))ᗮ,
        δ * ‖v‖ ≤ ‖parentHamiltonianES (A x) 2 N v‖ := by
  have hmpos : 0 < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  have hthreshold : 1 / (m : ℝ) < γ := (div_lt_iff₀ hmpos).2 (by simpa [mul_comm] using hnum)
  obtain ⟨γ', hγ'lower, hγ'upper⟩ := exists_between hthreshold
  have hγpos : 0 < γ := (div_pos zero_lt_one hmpos).trans hthreshold
  have hnear := eventually_openParentHamiltonianES_gap A hA (by omega : 2 ≤ m + 1)
    (fun x => isNBlkInjective_of_one_site (hInj x) (by omega))
    (fun x => isNBlkInjective_of_one_site (hInj x) (by omega)) hγpos hγ'upper hgap
  have hnum' : ((2 : ℝ) - 1) ^ 2 < (m : ℝ) * γ' := by
    have h := (div_lt_iff₀ hmpos).1 hγ'lower
    norm_num at *
    nlinarith
  let δ := ((m : ℝ) * γ' - ((2 : ℝ) - 1) ^ 2) / ((m : ℝ) - 2 + 1)
  refine ⟨δ, ?_, ?_⟩
  · apply div_pos (sub_pos.mpr hnum')
    have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  · filter_upwards [hnear] with x hx
    apply (parentHamiltonianES_gap_of_openParentHamiltonianES_gap (A x)
      (R := 2) (m := m) (by omega) hm hnum' ?_).2
    rw [show m + 2 - 1 = m + 1 by omega,
      ker_openParentHamiltonianES_eq_groundSpaceES_of_isNBlkInjective
        (Kraus.isNBlkInjective_one_of_isInjective (hInj x)) (by omega) (by omega)]
    exact hx

end MPSTensor
