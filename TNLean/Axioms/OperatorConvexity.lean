/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.Channel.Basic
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Order
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Axiomatized operator convexity and concavity

This module collects the axioms for the **operator Jensen inequalities** for
matrix powers and logarithms under positive maps, and the **Lieb concavity
theorem**.

Mathlib 4.31 proves the operator concavity inputs for `x ↦ x ^ p`,
`0 ≤ p ≤ 1`, and for `log`, via `CFC.concaveOn_rpow` and
`CFC.concaveOn_log`.  It also provides the Löwner integral representation
`a ^ p = ∫ t in Ioi 0, cfcₙ (Real.rpowIntegrand₀₁ p t) a ∂μ` for
`p ∈ (0, 1)` (`CFC.exists_measure_nnrpow_eq_integral_cfcₙ_rpowIntegrand₀₁`),
together with the operator concavity of each integrand
(`CFC.concaveOn_cfc_rpowIntegrand₀₁`) and its explicit resolvent form
`cfc (Real.rpowIntegrand₀₁ p t) a = t ^ (p - 1) • 1 - t ^ p • (t • 1 + a)⁻¹`.
The axioms below remain because those inputs are not yet accompanied by a
Hansen--Pedersen / Davis--Choi operator Jensen theorem for arbitrary positive
subunital or unital maps, or by Lieb's joint concavity theorem.  Operator
convexity of `x ↦ x ^ p` for `1 ≤ p ≤ 2`, the scalar input of the convex
case, is now available as `CFC.convexOn_rpow` in
`TNLean.Analysis.RpowConvexity`.

## Axioms

The following results are standard in matrix analysis.  They are axiomatized
here because the positive-map Jensen and Lieb-concavity parts of the argument
are not yet available in Mathlib:

* `posMap_rpow_concave_jensen` — Jensen inequality for concave `rpow`.
* `posMap_rpow_convex_jensen` — Jensen inequality for convex `rpow`.
* `posMap_log_concave_jensen` — Jensen inequality for concave `log`.
* `lieb_concavity_axiom` — Lieb concavity theorem.

The trace concavity/convexity statements for `A ↦ Re Tr(A^p)` that used to
live here (`trace_rpow_concave_axiom`, `trace_rpow_convex_axiom`) have been
discharged: see `TNLean.Analysis.OperatorConvexity` for the genuine proofs
via the spectral theorem and the scalar Jensen inequality.

## Status

All four declarations remain axioms.  Mathlib 4.31 supplies the C-star
functional-calculus concavity inputs and the Löwner integral representation
for the first and third statements, but not the positive-map Jensen theorem
needed to obtain the displayed inequalities.  Earlier status notes recorded
the integral representation as missing; that is no longer accurate, and the
sole remaining obstruction for the `rpow` and `log` Jensen axioms is the
operator Jensen step itself.

The remaining Mathlib or local formalization gaps are:

* General operator Jensen inequality for positive maps (the
  Hansen--Pedersen / Davis--Choi inequality `T(f A) ≤ f(T A)` for operator
  concave `f` with `f 0 ≥ 0` and positive subunital `T`): absent from Mathlib.
  For the concave `rpow` case the pointwise Löwner-integrand inequality is now
  available in `TNLean.Channel.Schwarz.OperatorJensenAux` as
  `TNLean.OperatorJensen.positiveMap_rpowIntegrand₀₁_jensen`; see the proof
  plan below.
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
  `TNLean.OperatorJensen.positiveMap_rpowIntegrand₀₁_jensen`.  The remaining
  proof work for the concave power case is the Löwner-integral assembly.
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
   integrand inequality itself is now
   `TNLean.OperatorJensen.positiveMap_rpowIntegrand₀₁_jensen`.  What remains is
   to integrate this pointwise bound using Mathlib's ordered Bochner
   monotonicity theorem, the local positive-semidefinite integral specialization in
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

The concave `rpow` case has now been reduced to the Löwner-integral assembly
from the pointwise integrand inequality.  The convex `rpow` and logarithmic
cases still need the corresponding positive-map Jensen input.

## References

* [R. Bhatia, *Matrix Analysis*, Springer GTM 169, Chapter V]
* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Theorem 5.1]
* [F. Hansen, G. K. Pedersen, *Jensen's operator inequality*, 2003]
* [E. H. Lieb, *Convex trace functions and the Wigner--Yanase--Dyson
  conjecture*, 1973]
-/

open scoped Matrix ComplexOrder MatrixOrder
open Matrix

noncomputable section

variable {D : ℕ}

local notation "Mat" => Matrix (Fin D) (Fin D) ℂ

private local instance instAxiomOCNormedRing : NormedRing Mat :=
  Matrix.instL2OpNormedRing
private local instance instAxiomOCNormedAlgebra : NormedAlgebra ℂ Mat :=
  Matrix.instL2OpNormedAlgebra

/-! ## Jensen inequality axioms for positive maps -/

/-- **Operator Jensen for concave `rpow`** (Wolf Theorem 5.1, `p ∈ [0, 1]`).

For a positive subunital map `T` and `p ∈ [0, 1]`:
  `T(A ^ p) ≤ (T A) ^ p`.

Follows from operator concavity of `rpow` (Bhatia, Chapter V) combined with
the Hansen--Pedersen operator Jensen inequality for positive subunital maps.

References:
* Wolf, Theorem 5.1
* Hansen--Pedersen, *Jensen's operator inequality*, 2003 -/
axiom posMap_rpow_concave_jensen
    {T : Mat →ₗ[ℂ] Mat} (hT : IsPositiveMap T) (hSub : T 1 ≤ (1 : Mat))
    {p : ℝ} (hp : p ∈ Set.Icc (0 : ℝ) 1) {A : Mat} (hA : 0 ≤ A) :
    T (A ^ p) ≤ (T A) ^ p

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
