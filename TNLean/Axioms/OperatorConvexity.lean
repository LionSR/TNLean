/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.Channel.Basic
import TNLean.Channel.Schwarz.OperatorJensenAux
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Order
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Operator convexity and concavity boundary

This module collects the remaining axioms for the **operator Jensen
inequalities** for matrix powers and logarithms under positive maps, and the
**Lieb concavity theorem**.  It also contains the now-proved concave real-power
Jensen theorem, since downstream files already import this boundary module.

Mathlib 4.31 proves the operator concavity inputs for `x ↦ x ^ p`,
`0 ≤ p ≤ 1`, and for `log`, via `CFC.concaveOn_rpow` and
`CFC.concaveOn_log`.  It also provides the Löwner integral representation
`a ^ p = ∫ t in Ioi 0, cfcₙ (Real.rpowIntegrand₀₁ p t) a ∂μ` for
`p ∈ (0, 1)` (`CFC.exists_measure_nnrpow_eq_integral_cfcₙ_rpowIntegrand₀₁`),
together with the operator concavity of each integrand
(`CFC.concaveOn_cfc_rpowIntegrand₀₁`) and its explicit resolvent form
`cfc (Real.rpowIntegrand₀₁ p t) a = t ^ (p - 1) • 1 - t ^ p • (t • 1 + a)⁻¹`.
The concave real-power Jensen inequality is proved below by integrating the
pointwise positive-map inequality for the Löwner integrand.  The convex,
logarithmic, and Lieb statements remain axioms because the corresponding
positive-map Jensen or joint-concavity arguments are not yet formalized.
Operator convexity of `x ↦ x ^ p` for `1 ≤ p ≤ 2`, the scalar input of the
convex case, is available as `CFC.convexOn_rpow` in
`TNLean.Analysis.RpowConvexity`.

## Axioms

The following results are standard in matrix analysis:

* `posMap_rpow_concave_jensen` — Jensen inequality for concave `rpow`,
  now a theorem.
* `posMap_rpow_convex_jensen` — Jensen inequality for convex `rpow`.
* `posMap_log_concave_jensen` — Jensen inequality for concave `log`.
* `lieb_concavity_axiom` — Lieb concavity theorem.

The trace concavity/convexity statements for `A ↦ Re Tr(A^p)` that used to
live here (`trace_rpow_concave_axiom`, `trace_rpow_convex_axiom`) have been
discharged: see `TNLean.Analysis.OperatorConvexity` for the genuine proofs
via the spectral theorem and the scalar Jensen inequality.

## Status

The concave real-power declaration is now proved.  Three declarations remain
axioms: the convex real-power Jensen inequality, the logarithmic Jensen
inequality, and Lieb's joint concavity theorem.  Mathlib 4.31 supplies the
C-star functional-calculus concavity inputs and the Löwner integral
representation for the power case.  Earlier status notes recorded the integral
representation as missing; that is no longer accurate.

The remaining Mathlib or local formalization gaps are:

* General operator Jensen inequality for positive maps beyond the concave
  real-power integrand route (the
  Hansen--Pedersen / Davis--Choi inequality `T(f A) ≤ f(T A)` for operator
  concave `f` with `f 0 ≥ 0` and positive subunital `T`): absent from Mathlib.
  For the concave `rpow` case the pointwise Löwner-integrand inequality and
  the ordered Bochner integral assembly are now sufficient, and the theorem
  below uses them directly.
* Monotonicity of the matrix-valued Bochner integral in the Loewner order is
  now available: `TNLean.Channel.Basic` supplies the closed Loewner-order
  topology on finite matrices, Mathlib supplies the ordered Bochner theorem
  `integral_mono_ae`, and `TNLean.Channel.Schwarz.OperatorJensenAux` records
  the positive-semidefinite integral specialization as
  `integral_nonneg_matrix_of_ae`.  Pulling a positive linear map through the
  integral can use `ContinuousLinearMap.integral_comp_comm` after packaging the
  finite-dimensional map as a continuous linear map.  The pointwise
  positive-map resolvent estimate and its spectral reduction to
  `povm_resolvent_inv_le` are available as
  `TNLean.OperatorJensen.positiveMap_resolvent_inv_le`, and the corresponding
  single-integrand Jensen inequality is
  `TNLean.OperatorJensen.positiveMap_rpowIntegrand₀₁_jensen`.  The theorem
  `posMap_rpow_concave_jensen` below performs the corresponding
  Löwner-integral assembly.
* Operator convexity of `rpow` over `[1, 2]`, the scalar input of
  `posMap_rpow_convex_jensen`, is now available as `CFC.convexOn_rpow` in
  `TNLean.Analysis.RpowConvexity`; the convex axiom therefore shares the single
  remaining positive-map Jensen obstruction with the concave one.
* Lieb concavity integral representation: absent from Mathlib.

## Proof plan

1. **Concave Jensen for `rpow`, `p ∈ [0, 1]`**: with the integral
   representation now in Mathlib, the route reduces to the per-integrand
   bound `T(cfc (rpowIntegrand₀₁ p t) A) ≤ cfc (rpowIntegrand₀₁ p t) (T A)`
   for each `t > 0`, followed by integration.  Using the resolvent form
   `cfc (rpowIntegrand₀₁ p t) a = t ^ (p - 1) • 1 - t ^ p • (t • 1 + a)⁻¹`,
   the per-integrand difference is
   `cfc (rpowIntegrand₀₁ p t) (T A) - T(cfc (rpowIntegrand₀₁ p t) A) =
     t ^ (p - 1) • (1 - T 1) + t ^ p • (T ((t • 1 + A)⁻¹) - (t • 1 + T A)⁻¹)`,
   which is positive semidefinite precisely because of the operator resolvent
   inequality `(t • 1 + T A)⁻¹ ≤ T ((t • 1 + A)⁻¹) + t⁻¹ • (1 - T 1)` for a
   positive subunital map `T`.  Diagonalizing `A = ∑ i, λ i • P i` over its
   spectral projections and setting `B i = T (P i)` (positive semidefinite,
   with `∑ i, B i = T 1 ≤ 1`), this resolvent inequality is now proved as
   `TNLean.OperatorJensen.positiveMap_resolvent_inv_le`; the displayed
   integrand inequality itself is
   `TNLean.OperatorJensen.positiveMap_rpowIntegrand₀₁_jensen`.  The proof below
   integrates this pointwise bound using Mathlib's ordered Bochner monotonicity
   theorem, the local positive-semidefinite integral specialization in
   `TNLean.Channel.Schwarz.OperatorJensenAux`, and the commutation of `T` with
   the integral.
2. **Operator convexity of `rpow` for `p ∈ [1, 2]`**: use the
   decomposition `x^p = x · x^{p-1}` for `p ∈ [1, 2]` (Mathlib's
   `rpowIntegrand₁₂`), reducing to concavity of `x^{p-1}` for
   `p - 1 ∈ [0, 1]` and the same operator Jensen step.
3. **Concave Jensen for `log`**: combine `CFC.concaveOn_log` with the
   unital operator Jensen theorem.
4. **Lieb concavity**: requires the integral representation
   `A^s B^{1-s} = (sin πs/π) ∫₀^∞ t^{s-1} A(A+tB)⁻¹ B dt` and
   resolvent monotonicity.

The convex `rpow` and logarithmic cases still need the corresponding
positive-map Jensen input.  Lieb concavity remains a separate integral
representation problem.

## References

* [R. Bhatia, *Matrix Analysis*, Springer GTM 169, Chapter V]
* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Theorem 5.1]
* [F. Hansen, G. K. Pedersen, *Jensen's operator inequality*, 2003]
* [E. H. Lieb, *Convex trace functions and the Wigner--Yanase--Dyson
  conjecture*, 1973]
-/

open scoped Matrix ComplexOrder MatrixOrder NNReal
open Matrix
open MeasureTheory

noncomputable section

variable {D : ℕ}

local notation "Mat" => Matrix (Fin D) (Fin D) ℂ

private local instance instAxiomOCNormedRing : NormedRing Mat :=
  Matrix.instL2OpNormedRing
private local instance instAxiomOCNormedAlgebra : NormedAlgebra ℂ Mat :=
  Matrix.instL2OpNormedAlgebra

/-! ## Jensen inequality axioms for positive maps -/

private lemma cfcₙ_rpowIntegrand₀₁_eq_cfc
    {B : Mat} (hB : 0 ≤ B) {p t : ℝ}
    (hp : p ∈ Set.Ioo (0 : ℝ) 1) (ht : 0 < t) :
    cfcₙ (Real.rpowIntegrand₀₁ p t) B =
      cfc (Real.rpowIntegrand₀₁ p t) B := by
  rw [cfcₙ_eq_cfc (hf := ?_) (hf0 := by simp)]
  exact (Real.continuousOn_rpowIntegrand₀₁_Ici hp ht).mono (by grind)

private lemma positiveMap_rpowIntegrand₀₁_cfcₙ_jensen
    {T : Mat →ₗ[ℂ] Mat} (hT : IsPositiveMap T)
    (hSub : T 1 ≤ (1 : Mat)) {A : Mat} (hA : 0 ≤ A)
    {p t : ℝ} (hp : p ∈ Set.Ioo (0 : ℝ) 1) (ht : 0 < t) :
    T (cfcₙ (Real.rpowIntegrand₀₁ p t) A) ≤
      cfcₙ (Real.rpowIntegrand₀₁ p t) (T A) := by
  have hApsd : A.PosSemidef := Matrix.nonneg_iff_posSemidef.mp hA
  have hTApsd : (T A).PosSemidef := hT A hApsd
  have hTA : 0 ≤ T A := Matrix.nonneg_iff_posSemidef.mpr hTApsd
  have hpoint :=
    TNLean.OperatorJensen.positiveMap_rpowIntegrand₀₁_jensen
      hT hSub hApsd hp ht
  simpa [cfcₙ_rpowIntegrand₀₁_eq_cfc hA hp ht,
    cfcₙ_rpowIntegrand₀₁_eq_cfc hTA hp ht] using hpoint

/-- **Operator Jensen for concave `rpow`** (Wolf Theorem 5.1, `p ∈ [0, 1]`).

For a positive subunital map `T` and `p ∈ [0, 1]`:
  `T(A ^ p) ≤ (T A) ^ p`.

Follows from operator concavity of `rpow` (Bhatia, Chapter V) combined with
the Hansen--Pedersen operator Jensen inequality for positive subunital maps.

References:
* Wolf, Theorem 5.1
* Hansen--Pedersen, *Jensen's operator inequality*, 2003 -/
theorem posMap_rpow_concave_jensen
    {T : Mat →ₗ[ℂ] Mat} (hT : IsPositiveMap T) (hSub : T 1 ≤ (1 : Mat))
    {p : ℝ} (hp : p ∈ Set.Icc (0 : ℝ) 1) {A : Mat} (hA : 0 ≤ A) :
    T (A ^ p) ≤ (T A) ^ p := by
  classical
  have hApsd : A.PosSemidef := Matrix.nonneg_iff_posSemidef.mp hA
  have hTApsd : (T A).PosSemidef := hT A hApsd
  have hTA : 0 ≤ T A := Matrix.nonneg_iff_posSemidef.mpr hTApsd
  by_cases hp0 : p = 0
  · subst p
    simpa [CFC.rpow_zero A hA, CFC.rpow_zero (T A) hTA] using hSub
  by_cases hp1 : p = 1
  · subst p
    simp [CFC.rpow_one A hA, CFC.rpow_one (T A) hTA]
  have hpIoo : p ∈ Set.Ioo (0 : ℝ) 1 := by
    exact ⟨lt_of_le_of_ne hp.1 (Ne.symm hp0), lt_of_le_of_ne hp.2 hp1⟩
  let q : ℝ≥0 := ⟨p, hpIoo.1.le⟩
  have hqcoe : (q : ℝ) = p := rfl
  have hqpos : 0 < q := by exact_mod_cast hpIoo.1
  have hqIoo : q ∈ Set.Ioo (0 : ℝ≥0) 1 := by
    constructor
    · exact hqpos
    · exact_mod_cast hpIoo.2
  obtain ⟨μ, hμ⟩ :=
    CFC.exists_measure_nnrpow_eq_integral_cfcₙ_rpowIntegrand₀₁ Mat hqIoo
  let ν := μ.restrict (Set.Ioi (0 : ℝ))
  have hAint :=
    hμ A (by simpa using hA)
  have hTAint :=
    hμ (T A) (by simpa using hTA)
  have hAintν :
      Integrable (fun t => cfcₙ (Real.rpowIntegrand₀₁ q t) A) ν := by
    simpa [ν, MeasureTheory.IntegrableOn] using hAint.1
  have hTAintν :
      Integrable (fun t => cfcₙ (Real.rpowIntegrand₀₁ q t) (T A)) ν := by
    simpa [ν, MeasureTheory.IntegrableOn] using hTAint.1
  have hT_Aintν :
      Integrable (fun t => T (cfcₙ (Real.rpowIntegrand₀₁ q t) A)) ν := by
    simpa [LinearMap.coe_toContinuousLinearMap'] using
      (LinearMap.toContinuousLinearMap T).integrable_comp hAintν
  have hmono :
      (fun t => T (cfcₙ (Real.rpowIntegrand₀₁ q t) A)) ≤ᵐ[ν]
        fun t => cfcₙ (Real.rpowIntegrand₀₁ q t) (T A) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have htpos : 0 < t := ht
    have hpoint :=
      positiveMap_rpowIntegrand₀₁_cfcₙ_jensen
        hT hSub hA hpIoo htpos
    convert hpoint using 2 <;> simp [hqcoe]
  have hintegral_mono :
      (∫ t, T (cfcₙ (Real.rpowIntegrand₀₁ q t) A) ∂ν) ≤
        ∫ t, cfcₙ (Real.rpowIntegrand₀₁ q t) (T A) ∂ν :=
    integral_mono_ae hT_Aintν hTAintν hmono
  have hT_integral :
      T (∫ t, cfcₙ (Real.rpowIntegrand₀₁ q t) A ∂ν) =
        ∫ t, T (cfcₙ (Real.rpowIntegrand₀₁ q t) A) ∂ν := by
    simpa [LinearMap.coe_toContinuousLinearMap'] using
      ((LinearMap.toContinuousLinearMap T).integral_comp_comm hAintν).symm
  have hA_rpow : A ^ p = A ^ q := by
    have h := CFC.nnrpow_eq_rpow (a := A) hqpos
    rw [hqcoe] at h
    exact h.symm
  have hTA_rpow : (T A) ^ q = (T A) ^ p := by
    have h := CFC.nnrpow_eq_rpow (a := T A) hqpos
    rw [hqcoe] at h
    exact h
  calc
    T (A ^ p) = T (A ^ q) := by rw [hA_rpow]
    _ = T (∫ t, cfcₙ (Real.rpowIntegrand₀₁ q t) A ∂ν) := by
      rw [hAint.2]
    _ = ∫ t, T (cfcₙ (Real.rpowIntegrand₀₁ q t) A) ∂ν := hT_integral
    _ ≤ ∫ t, cfcₙ (Real.rpowIntegrand₀₁ q t) (T A) ∂ν := hintegral_mono
    _ = (T A) ^ q := by
      rw [hTAint.2]
    _ = (T A) ^ p := hTA_rpow

/-- **Operator Jensen for convex `rpow`** (Wolf Theorem 5.1, `p ∈ [1, 2]`).

For a positive subunital map `T` and `p ∈ [1, 2]`:
  `(T A) ^ p ≤ T(A ^ p)`.

Follows from operator convexity of `rpow` (Bhatia, Chapter V) combined with
the Hansen--Pedersen operator Jensen inequality for positive subunital maps.

References:
* Wolf, Theorem 5.1
* Hansen--Pedersen, *Jensen's operator inequality*, 2003 -/
axiom posMap_rpow_convex_jensen
    {T : Mat →ₗ[ℂ] Mat} (hT : IsPositiveMap T) (hSub : T 1 ≤ (1 : Mat))
    {p : ℝ} (hp : p ∈ Set.Icc (1 : ℝ) 2) {A : Mat} (hA : 0 ≤ A) :
    (T A) ^ p ≤ T (A ^ p)

/-- **Operator Jensen for concave `log`** (Wolf Theorem 5.1, log case).

For a positive **unital** map `T` and positive-definite `A`:
  `T(log A) ≤ log(T A)`.

Follows from operator concavity of `log` (Bhatia, Chapter V) combined with
the operator Jensen inequality. Requires unitality (`T 1 = 1`), not
merely subunitality.

References:
* Wolf, Theorem 5.1
* Hansen--Pedersen, *Jensen's operator inequality*, 2003 -/
axiom posMap_log_concave_jensen
    {T : Mat →ₗ[ℂ] Mat} (hT : IsPositiveMap T) (hUnit : T 1 = (1 : Mat))
    {A : Mat} (hA : A.PosDef) :
    T (CFC.log A) ≤ CFC.log (T A)

/-! ## Lieb concavity axiom -/

/-- **Lieb concavity theorem** (Lieb 1973, Ando 1979).

For `s ∈ [0, 1]`, any matrix `K`, and PD matrices `A₁, A₂, B₁, B₂`:
  the map `(A, B) ↦ Tr(K† A^s K B^{1−s})` is jointly concave.

Requires the integral representation
`A^s B^{1-s} = (sin πs / π) ∫₀^∞ t^{s-1} A(A + tB)⁻¹ B dt`
and resolvent monotonicity, which are not yet in Mathlib.

References:
* Lieb, *Convex trace functions*, Adv. Math. 11, 1973
* Ando, *Concavity of certain maps on positive definite matrices*, 1979 -/
axiom lieb_concavity_axiom
    {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1)
    {A₁ A₂ B₁ B₂ K : Mat}
    (hA₁ : A₁.PosDef) (hA₂ : A₂.PosDef)
    (hB₁ : B₁.PosDef) (hB₂ : B₂.PosDef)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    t * (trace (Kᴴ * A₁ ^ s * K * B₁ ^ (1 - s))).re +
      (1 - t) * (trace (Kᴴ * A₂ ^ s * K * B₂ ^ (1 - s))).re ≤
    (trace (Kᴴ * (t • A₁ + (1 - t) • A₂) ^ s * K *
      (t • B₁ + (1 - t) • B₂) ^ (1 - s))).re

end
