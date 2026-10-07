/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.RegularizedPatchCoordinate
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# First variation at the actual regularized minimum

The curve conjugating one indexed density by `exp(t B)` is feasible for every
real `t` when `B` is skew-Hermitian. Exact covariance differentiates its filter
without differentiating a matrix power. Fermat's theorem for the squared norm
then gives the genuine ordered-product first-variation identity at every
feasible minimizer. No minimizing selection or nesting is assumed.

Source: OpenAI `03-patches.tex`, lines 134–153, commit
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

/-!
## Original proof provenance

Source: September 24, 2026,
https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/build/sections/03-patches.tex
sec:patches, prop:patch, and eq:patch-variational-problem.
Independently formalized; no upstream Lean proof text reused.

Provenance-ID: regularizedpatchstationarity8767-tnlean.peps.regularizedpatchunitarycurve
Downstream declaration: TNLean.PEPS.regularizedPatchUnitaryCurve

Provenance-ID: regularizedpatchstationarity8767-output-derivative
Downstream declaration: TNLean.PEPS.hasDerivAt_regularizedPatchOutput_coordinateUpdate

Provenance-ID: regularizedpatchstationarity8767-tnlean.peps.regularizedpatchfirstvariation_eq_zero
Downstream declaration: TNLean.PEPS.regularizedPatchFirstVariation_eq_zero
-/

open scoped BigOperators Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Matrix

namespace TNLean.PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Out : V → Type*} [∀ v, Fintype (Out v)]
variable {m : ℕ} (regions : Fin m → Finset V)

open Classical in
/-- The unitary exponential along a skew-Hermitian regional generator. -/
noncomputable def regularizedPatchUnitaryCurve (j : Fin m)
    (B : Matrix ((v : regions j) → Out v.1) ((v : regions j) → Out v.1) ℂ)
    (hB : star B = -B) (t : ℝ) :
    unitary (Matrix ((v : regions j) → Out v.1) ((v : regions j) → Out v.1) ℂ) := by
  classical
  let _ : NormedAlgebra ℚ
      (Matrix ((v : regions j) → Out v.1) ((v : regions j) → Out v.1) ℂ) :=
    NormedAlgebra.restrictScalars ℚ ℂ _
  refine ⟨NormedSpace.exp (t • B), NormedSpace.exp_mem_unitary_of_mem_skewAdjoint ?_⟩
  rw [skewAdjoint.mem_iff]
  simp [hB]

open Classical in
/-- The true filtered output along a coordinate-unitary curve has derivative
obtained by inserting the local commutator in its original position. -/
theorem hasDerivAt_regularizedPatchOutput_coordinateUpdate
    (a : Fin m → ℝ) {b : ℝ} (hb : 0 < b)
    (Ω : EuclideanSpace ℂ ((v : (Finset.univ : Finset V)) → Out v.1))
    {x : ∀ j, Matrix ((v : regions j) → Out v.1) ((v : regions j) → Out v.1) ℂ}
    (hx : x ∈ regularizedPatchDomain regions) (j : Fin m)
    (B : Matrix ((v : regions j) → Out v.1) ((v : regions j) → Out v.1) ℂ)
    (hB : star B = -B) :
    HasDerivAt (fun t : ℝ ↦ regularizedPatchOutput regions a b Ω
      (regularizedPatchCoordinateUpdate regions x j
        (regularizedPatchUnitaryCurve regions j B hB t)))
      (regularizedPatchInsertion regions a b Ω x j
        (B * (x j + b • 1) ^ (-(a j) / 2) - (x j + b • 1) ^ (-(a j) / 2) * B)) 0 := by
  classical
  let F := (x j + b • 1) ^ (-(a j) / 2)
  have he : HasDerivAt (fun t : ℝ ↦ NormedSpace.exp (t • B)) B 0 := by
    simpa using hasDerivAt_exp_smul_const (𝕂 := ℝ) B 0
  have hc : HasDerivAt (fun t : ℝ ↦ NormedSpace.exp (t • B) * F *
      star (NormedSpace.exp (t • B))) (B * F - F * B) 0 := by
    convert! (he.mul_const F).mul he.star using 1
    simp [hB, sub_eq_add_neg]
  let C := (regularizedPatchInsertion regions a b Ω x j).toContinuousLinearMap.restrictScalars ℝ
  have hd := C.hasFDerivAt.comp_hasDerivAt 0 hc
  convert! hd using 1
  · funext t
    exact regularizedPatchOutput_coordinateUpdate regions a hb Ω hx j
      (regularizedPatchUnitaryCurve regions j B hB t)

open Classical in
/-- Every actual feasible minimizer has zero real pairing with the ordered
insertion of each skew-Hermitian commutator. This is a first variation, and does
not assert commutation of local densities or different filters. -/
theorem regularizedPatchFirstVariation_eq_zero
    (a : Fin m → ℝ) {b : ℝ} (hb : 0 < b)
    (Ω : EuclideanSpace ℂ ((v : (Finset.univ : Finset V)) → Out v.1))
    {x : ∀ j, Matrix ((v : regions j) → Out v.1) ((v : regions j) → Out v.1) ℂ}
    (hx : x ∈ regularizedPatchDomain regions)
    (hmin : IsMinOn (regularizedPatchObjective regions a b Ω) (regularizedPatchDomain regions) x)
    (j : Fin m)
    (B : Matrix ((v : regions j) → Out v.1) ((v : regions j) → Out v.1) ℂ)
    (hB : star B = -B) :
    (inner ℂ (regularizedPatchOutput regions a b Ω x)
      (regularizedPatchInsertion regions a b Ω x j
        (B * (x j + b • 1) ^ (-(a j) / 2) - (x j + b • 1) ^ (-(a j) / 2) * B))).re = 0 := by
  classical
  let γ := fun t : ℝ ↦ regularizedPatchCoordinateUpdate regions x j
    (regularizedPatchUnitaryCurve regions j B hB t)
  have hγ : γ 0 = x := by
    simp [γ, regularizedPatchUnitaryCurve, regularizedPatchCoordinateUpdate]
  have hm : IsLocalMin (fun t : ℝ ↦ ‖regularizedPatchOutput regions a b Ω (γ t)‖ ^ 2) 0 := by
    apply IsMinOn.isLocalMin (s := Set.univ) _ Filter.univ_mem
    intro t _
    change ‖regularizedPatchOutput regions a b Ω (γ 0)‖ ^ 2 ≤
      ‖regularizedPatchOutput regions a b Ω (γ t)‖ ^ 2
    rw [hγ]
    exact pow_le_pow_left₀ (norm_nonneg _) (hmin
      (regularizedPatchCoordinateUpdate_mem regions hx j
        (regularizedPatchUnitaryCurve regions j B hB t))) 2
  have hd := (hasDerivAt_regularizedPatchOutput_coordinateUpdate regions a hb Ω hx j B hB).norm_sq
  have hz := hm.hasDerivAt_eq_zero hd
  rw [show regularizedPatchCoordinateUpdate regions x j
    (regularizedPatchUnitaryCurve regions j B hB 0) = x from hγ] at hz
  simpa only [PiLp.inner_apply, Complex.re_sum, real_inner_eq_re_inner (𝕜 := ℂ),
    RCLike.re_to_complex] using (mul_eq_zero.mp hz).resolve_left
    (by norm_num : (2 : ℝ) ≠ 0)

end TNLean.PEPS
