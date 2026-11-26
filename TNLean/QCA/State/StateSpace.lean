/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.QCA.QuasiLocal.QuasiLocal
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Convex.Combination

/-!
# States and pure states of the quasi-local observable algebra

A state is a normalized norm-one continuous complex-linear functional that
is nonnegative on every adjoint square. A pure state is an extreme point of
the convex set of all such states. No translation invariance is required of
a state, or of states appearing in a convex decomposition.

Positivity is expressed on adjoint squares, without choosing an order on the
completed algebra.

It also contains the following results.

* `SpinChain.convex_quasiLocalStateSpace`,
  `SpinChain.exists_eq_of_isPureQuasiLocalState_of_finite_decomposition`: finite convex
  decompositions of pure quasi-local states.

## References

* Nachtergaele, *The spectral gap for some spin chains with discrete symmetry breaking*, Commun.
  Math. Phys. 175 (1996), arXiv:cond-mat/9410110, lines 854--887 and 1469--1482: state and
  purity conventions.
-/

open scoped ComplexOrder

namespace SpinChain

section StateSpace

variable (d : ℕ) [NeZero d]

/-- The normalized positive state functionals on the quasi-local algebra.
Source: Nachtergaele, arXiv:cond-mat/9410110, lines 854--887. -/
def quasiLocalStateSpace : Set (QuasiLocalAlgebra d →L[ℂ] ℂ) :=
  {ω | ‖ω‖ = 1 ∧ ω 1 = 1 ∧ ∀ X, 0 ≤ ω (star X * X)}

/-- Purity is extremality among all normalized positive states, not only
among translation-invariant states. Source: Nachtergaele,
arXiv:cond-mat/9410110, lines 854--887 and 1469--1482. -/
def IsPureQuasiLocalState (ω : QuasiLocalAlgebra d →L[ℂ] ℂ) : Prop :=
  ω ∈ (quasiLocalStateSpace d).extremePoints ℝ

variable {d}

/-- If a state decomposes nontrivially into two states, every adjoint square
of zero expectation also has zero expectation in the left constituent.
Source: Nachtergaele, arXiv:cond-mat/9410110, lines 860--868,
the face property of zero-energy states. -/
theorem quasiLocalState_left_apply_eq_zero_of_convex_decomposition
    (φ ψ ω : QuasiLocalAlgebra d →L[ℂ] ℂ)
    (hφ : φ ∈ quasiLocalStateSpace d) (hψ : ψ ∈ quasiLocalStateSpace d)
    {t : ℝ} (ht₀ : 0 < t) (ht₁ : t < 1)
    (hdecomp : (1 - t) • φ + t • ψ = ω)
    (X : QuasiLocalAlgebra d) (hzero : ω (star X * X) = 0) :
    φ (star X * X) = 0 := by
  have hφpos := hφ.2.2 X
  have hψpos := hψ.2.2 X
  have hφre : 0 ≤ (φ (star X * X)).re := hφpos.1
  have hψre : 0 ≤ (ψ (star X * X)).re := hψpos.1
  have heq := congrArg (fun f : QuasiLocalAlgebra d →L[ℂ] ℂ => (f (star X * X)).re) hdecomp
  simp only [add_apply, smul_apply,
    Complex.add_re, Complex.smul_re, smul_eq_mul, hzero, Complex.zero_re] at heq
  apply Complex.ext
  · change (φ (star X * X)).re = 0
    nlinarith [mul_nonneg ht₀.le hψre]
  · exact hφpos.2.symm

/-- A projection of expectation one in a nontrivial convex combination of
states also has expectation one in its left constituent.
Source: Nachtergaele, arXiv:cond-mat/9410110, lines 860--868,
the face property of zero-energy states. -/
theorem quasiLocalState_left_projection_eq_one_of_convex_decomposition
    (φ ψ ω : QuasiLocalAlgebra d →L[ℂ] ℂ)
    (hφ : φ ∈ quasiLocalStateSpace d) (hψ : ψ ∈ quasiLocalStateSpace d)
    (hω : ω ∈ quasiLocalStateSpace d) {t : ℝ} (ht₀ : 0 < t) (ht₁ : t < 1)
    (hdecomp : (1 - t) • φ + t • ψ = ω) (P : QuasiLocalAlgebra d)
    (hP : IsStarProjection P) (hωP : ω P = 1) : φ P = 1 := by
  have hQ := hP.one_sub
  have hzero : ω (star (1 - P) * (1 - P)) = 0 := by
    rw [hQ.isSelfAdjoint.star_eq, hQ.isIdempotentElem.eq, map_sub, hω.2.1, hωP, sub_self]
  have hφQ := quasiLocalState_left_apply_eq_zero_of_convex_decomposition
    φ ψ ω hφ hψ ht₀ ht₁ hdecomp (1 - P) hzero
  rw [hQ.isSelfAdjoint.star_eq, hQ.isIdempotentElem.eq, map_sub, hφ.2.1] at hφQ
  exact (sub_eq_zero.mp hφQ).symm

/-- A state uniquely determined among all states by expectation-one
support projections is pure. Source: Nachtergaele, arXiv:cond-mat/9410110,
lines 860--887, the face and extreme-point characterization of pure ground states. -/
theorem isPureQuasiLocalState_of_unique_supported_state
    (ω : QuasiLocalAlgebra d →L[ℂ] ℂ) (hω : ω ∈ quasiLocalStateSpace d)
    {ι : Type*} (P : ι → QuasiLocalAlgebra d) (hP : ∀ i, IsStarProjection (P i))
    (hωP : ∀ i, ω (P i) = 1)
    (hUnique : ∀ φ ∈ quasiLocalStateSpace d, (∀ i, φ (P i) = 1) → φ = ω) :
    IsPureQuasiLocalState d ω := by
  refine ⟨hω, ?_⟩
  intro φ hφ ψ hψ hseg
  rw [openSegment_eq_image] at hseg
  obtain ⟨t, ht, hdecomp⟩ := hseg
  apply hUnique φ hφ
  intro i
  exact quasiLocalState_left_projection_eq_one_of_convex_decomposition
    φ ψ ω hφ hψ hω ht.1 ht.2 hdecomp (P i) (hP i) (hωP i)

end StateSpace

section FinitePureStateDecomposition

/-!
## Finite convex decompositions of pure quasi-local states

The space of normalized positive quasi-local states is convex over the real
numbers. A pure state that is a finite convex combination of states must equal
one of the constituent states. Purity is taken among all states; translation
invariance is not assumed.

These are elementary consequences of the state and purity conventions.

### References

* Nachtergaele, *The spectral gap for some spin chains with discrete symmetry breaking*, Commun.
  Math. Phys. 175 (1996), arXiv:cond-mat/9410110, lines 854--887 and 1469--1482.
-/

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

end FinitePureStateDecomposition

end SpinChain
