/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.QCA.StateSpace
import Mathlib.Analysis.Convex.Combination
/-!
# Finite convex decompositions of pure quasi-local states

The space of normalized positive quasi-local states is convex over the real
numbers. A pure state that is a finite convex combination of states must equal
one of the constituent states. Purity is taken among all states; translation
invariance is not assumed.

These are elementary consequences of the state and purity conventions.

## References

* Nachtergaele, *The spectral gap for some spin chains with discrete symmetry breaking*, Commun.
  Math. Phys. 175 (1996), arXiv:cond-mat/9410110, lines 854--887 and 1469--1482.
-/

open scoped ComplexOrder
namespace SpinChain
attribute [local instance] CStarMatrix.instNorm CStarMatrix.instNormedAddCommGroup
  CStarMatrix.instNormedRing CStarMatrix.instCStarRing
variable {d : ℕ} [NeZero d]
/-- The normalized positive quasi-local states form a real convex set.
Source: Nachtergaele, arXiv:cond-mat/9410110, lines 854--887. -/
theorem convex_quasiLocalStateSpace : Convex ℝ (quasiLocalStateSpace d) := by
  intro φ hφ ψ hψ a b ha hb hab
  have hunit : (a • φ + b • ψ) 1 = 1 := by
    simp only [add_apply, smul_apply, hφ.2.1, hψ.2.1,
      ← add_smul, hab, one_smul]
  refine ⟨le_antisymm ?_ ?_, hunit, ?_⟩
  · calc
      ‖a • φ + b • ψ‖ ≤ ‖a • φ‖ + ‖b • ψ‖ := ContinuousLinearMap.opNorm_add_le (a • φ) (b • ψ)
      _ ≤ ‖a‖ * ‖φ‖ + ‖b‖ * ‖ψ‖ := add_le_add (ContinuousLinearMap.opNorm_smul_le a φ)
        (ContinuousLinearMap.opNorm_smul_le b ψ)
      _ = 1 := by rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg ha,
        abs_of_nonneg hb, hφ.1, hψ.1, mul_one, mul_one, hab]
  · have hnorm : ‖(1 : QuasiLocalAlgebra d)‖ = 1 := by
      simpa only [map_one, norm_one] using
        norm_quasiLocalObservable d ∅ (1 : LocalAlgebra d ∅)
    simpa only [hunit, norm_one, hnorm, mul_one] using (a • φ + b • ψ).le_opNorm 1
  · intro X
    simpa only [add_apply, smul_apply] using
      add_nonneg (smul_nonneg ha (hφ.2.2 X)) (smul_nonneg hb (hψ.2.2 X))
/-- A pure state in a finite convex combination equals one of its constituent states.
Purity is taken in the full quasi-local state space; no translation-invariance
condition is imposed. Source: Nachtergaele, arXiv:cond-mat/9410110,
lines 854--887 and 1469--1482, the extreme-point meaning of purity. -/
theorem exists_eq_of_isPureQuasiLocalState_of_finite_decomposition
    (φ : QuasiLocalAlgebra d →L[ℂ] ℂ) (hPure : IsPureQuasiLocalState d φ)
    {ι : Type*} [Fintype ι] (ω : ι → QuasiLocalAlgebra d →L[ℂ] ℂ)
    (hω : ∀ i, ω i ∈ quasiLocalStateSpace d) (w : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hSum : ∑ i, w i = 1)
    (hdecomp : φ = ∑ i, w i • ω i) : ∃ i, φ = ω i := by
  have hmem : φ ∈ convexHull ℝ (Set.range ω) := by
    rw [hdecomp]
    exact (convex_convexHull ℝ (Set.range ω)).sum_mem (fun i _ => hw i) hSum
      (fun i _ => subset_convexHull ℝ (Set.range ω) (Set.mem_range_self i))
  have hsub : convexHull ℝ (Set.range ω) ⊆ quasiLocalStateSpace d :=
    convexHull_min (Set.range_subset_iff.mpr hω) convex_quasiLocalStateSpace
  obtain ⟨i, hi⟩ := extremePoints_convexHull_subset
    (inter_extremePoints_subset_extremePoints_of_subset hsub ⟨hmem, hPure⟩)
  exact ⟨i, hi.symm⟩

end SpinChain
