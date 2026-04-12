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

This module collects the axioms for **operator convexity/concavity** of matrix
power and logarithm functions, the **operator Jensen inequality** for positive
maps, and the **Lieb concavity theorem**. These results are deferred pending
upstream Mathlib work in `CFC.Rpow.Order` and `CFC.ExpLog.Order`.

## Core axioms

* `rpow_operator_concave` — operator concavity of `x ↦ x ^ p` for `p ∈ [0, 1]`.
* `rpow_operator_convex` — operator convexity of `x ↦ x ^ p` for `p ∈ [1, 2]`.
* `log_operator_concave` — operator concavity of `log`.

## Derived axioms

The following results follow mathematically from the core axioms combined with
trace monotonicity, the operator Jensen inequality (Hansen--Pedersen), and
Lieb's integral representation. They are axiomatized here because the
connecting infrastructure is not available in Mathlib:

* `trace_rpow_concave_axiom` — trace concavity of `rpow` for `p ∈ [0, 1]`.
* `trace_rpow_convex_axiom` — trace convexity of `rpow` for `p ∈ [1, 2]`.
* `posMap_rpow_concave_jensen` — Jensen inequality for concave `rpow`.
* `posMap_rpow_convex_jensen` — Jensen inequality for convex `rpow`.
* `posMap_log_concave_jensen` — Jensen inequality for concave `log`.
* `lieb_concavity_axiom` — Lieb concavity theorem.

## Status

All results are axiomatized. The specific Mathlib TODOs blocking proofs:

* `CFC.Rpow.Order`: operator concavity of `rpow` over `[0, 1]`,
  operator convexity of `rpow` over `[1, 2]`.
* `CFC.ExpLog.Order`: operator concavity of `log`.
* General operator Jensen inequality for positive maps: absent from Mathlib.
* Lieb concavity integral representation: absent from Mathlib.

## Proof plan

1. **Operator concavity of `rpow` for `p ∈ [0, 1]`**: follows from the
   integral representation `a ^ p = C_p ∫ t^{p-1} a(a + t)⁻¹ dt` (already
   in Mathlib as `exists_measure_nnrpow_eq_integral_cfcₙ_rpowIntegrand₀₁`),
   once the integrand is shown to be operator concave (parallel to the
   existing monotonicity proof in `CFC.Rpow.IntegralRepresentation`).
2. **Operator convexity of `rpow` for `p ∈ [1, 2]`**: uses the
   decomposition `x^p = x · x^{p-1}` for `p ∈ [1, 2]`, reducing to
   concavity of `x^{p-1}` for `p - 1 ∈ [0, 1]`.
3. **Operator concavity of `log`**: follows from rpow concavity via the
   limit `log x = lim_{p → 0} (x^p - 1)/p`.
4. **Jensen inequality for positive maps**: follows from operator
   concavity/convexity via the Hansen--Pedersen 2×2 matrix block trick.
5. **Lieb concavity**: requires the integral representation
   `A^s B^{1-s} = (sin πs/π) ∫₀^∞ t^{s-1} A(A+tB)⁻¹ B dt` and
   resolvent monotonicity.

## References

* [R. Bhatia, *Matrix Analysis*, Springer GTM 169, Chapter V]
* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Thm. 5.1]
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
private local instance instAxiomOCCStarRing : CStarRing Mat :=
  Matrix.instCStarRing
private local instance instAxiomOCPartialOrder : PartialOrder Mat :=
  Matrix.instPartialOrder
private local instance instAxiomOCStarOrderedRing : StarOrderedRing Mat :=
  Matrix.instStarOrderedRing
private local instance instAxiomOCNonnegSpectrumClass : NonnegSpectrumClass ℝ Mat :=
  Matrix.instNonnegSpectrumClass
private local instance instAxiomOCCStarAlgebra : CStarAlgebra Mat :=
  CStarAlgebra.mk

/-! ## Core operator concavity/convexity axioms -/

/-- **Operator concavity of `rpow` for `p ∈ [0, 1]`** (Bhatia, Ch. V).

For PSD matrices `A₁, A₂` and `t ∈ [0, 1]`:
  `t • A₁ ^ p + (1 − t) • A₂ ^ p ≤ (t • A₁ + (1 − t) • A₂) ^ p`.

This is listed as a Mathlib TODO in `CFC.Rpow.Order`. -/
axiom rpow_operator_concave
    {p : ℝ} (hp : p ∈ Set.Icc (0 : ℝ) 1)
    {A₁ A₂ : Mat} (hA₁ : 0 ≤ A₁) (hA₂ : 0 ≤ A₂)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    t • (A₁ ^ p) + (1 - t) • (A₂ ^ p) ≤ (t • A₁ + (1 - t) • A₂) ^ p

/-- **Operator convexity of `rpow` for `p ∈ [1, 2]`** (Bhatia, Ch. V).

For PSD matrices `A₁, A₂` and `t ∈ [0, 1]`:
  `(t • A₁ + (1 − t) • A₂) ^ p ≤ t • A₁ ^ p + (1 − t) • A₂ ^ p`.

This is listed as a Mathlib TODO in `CFC.Rpow.Order`. -/
axiom rpow_operator_convex
    {p : ℝ} (hp : p ∈ Set.Icc (1 : ℝ) 2)
    {A₁ A₂ : Mat} (hA₁ : 0 ≤ A₁) (hA₂ : 0 ≤ A₂)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (t • A₁ + (1 - t) • A₂) ^ p ≤ t • (A₁ ^ p) + (1 - t) • (A₂ ^ p)

/-- **Operator concavity of `log`** (Bhatia, Ch. V).

For PD matrices `A₁, A₂` and `t ∈ [0, 1]`:
  `t • log(A₁) + (1 − t) • log(A₂) ≤ log(t • A₁ + (1 − t) • A₂)`.

This is listed as a Mathlib TODO in `CFC.ExpLog.Order`. -/
axiom log_operator_concave
    {A₁ A₂ : Mat} (hA₁ : A₁.PosDef) (hA₂ : A₂.PosDef)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    t • CFC.log A₁ + (1 - t) • CFC.log A₂ ≤ CFC.log (t • A₁ + (1 - t) • A₂)

/-! ## Trace concavity/convexity axioms -/

/-- **Trace concavity of `rpow`** for `p ∈ [0, 1]`.

For PSD matrices `A₁, A₂` and `t ∈ [0, 1]`:
  `t · Re Tr(A₁ ^ p) + (1 − t) · Re Tr(A₂ ^ p) ≤
     Re Tr((t • A₁ + (1 − t) • A₂) ^ p)`.

Follows from `rpow_operator_concave` composed with trace monotonicity on
the Loewner order. -/
axiom trace_rpow_concave_axiom
    {p : ℝ} (hp : p ∈ Set.Icc (0 : ℝ) 1)
    {A₁ A₂ : Mat} (hA₁ : 0 ≤ A₁) (hA₂ : 0 ≤ A₂)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    t * (trace (A₁ ^ p)).re + (1 - t) * (trace (A₂ ^ p)).re ≤
      (trace ((t • A₁ + (1 - t) • A₂) ^ p)).re

/-- **Trace convexity of `rpow`** for `p ∈ [1, 2]`.

For PSD matrices `A₁, A₂` and `t ∈ [0, 1]`:
  `Re Tr((t • A₁ + (1 − t) • A₂) ^ p) ≤
     t · Re Tr(A₁ ^ p) + (1 − t) · Re Tr(A₂ ^ p)`.

Follows from `rpow_operator_convex` composed with trace monotonicity on
the Loewner order. -/
axiom trace_rpow_convex_axiom
    {p : ℝ} (hp : p ∈ Set.Icc (1 : ℝ) 2)
    {A₁ A₂ : Mat} (hA₁ : 0 ≤ A₁) (hA₂ : 0 ≤ A₂)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (trace ((t • A₁ + (1 - t) • A₂) ^ p)).re ≤
      t * (trace (A₁ ^ p)).re + (1 - t) * (trace (A₂ ^ p)).re

/-! ## Jensen inequality axioms for positive maps -/

/-- **Operator Jensen for concave `rpow`** (Wolf Thm. 5.1, `p ∈ [0, 1]`).

For a positive subunital map `T` and `p ∈ [0, 1]`:
  `T(A ^ p) ≤ (T A) ^ p`.

Follows from `rpow_operator_concave` combined with the Hansen--Pedersen
operator Jensen inequality for positive subunital maps. The Jensen inequality
is not in Mathlib, so this is axiomatized as well.

References:
* Wolf, Thm. 5.1
* Hansen--Pedersen, *Jensen's operator inequality*, 2003 -/
axiom posMap_rpow_concave_jensen
    {T : Mat →ₗ[ℂ] Mat} (hT : IsPositiveMap T) (hSub : T 1 ≤ (1 : Mat))
    {p : ℝ} (hp : p ∈ Set.Icc (0 : ℝ) 1) {A : Mat} (hA : 0 ≤ A) :
    T (A ^ p) ≤ (T A) ^ p

/-- **Operator Jensen for convex `rpow`** (Wolf Thm. 5.1, `p ∈ [1, 2]`).

For a positive subunital map `T` and `p ∈ [1, 2]`:
  `(T A) ^ p ≤ T(A ^ p)`.

Follows from `rpow_operator_convex` combined with the Hansen--Pedersen
operator Jensen inequality for positive subunital maps.

References:
* Wolf, Thm. 5.1
* Hansen--Pedersen, *Jensen's operator inequality*, 2003 -/
axiom posMap_rpow_convex_jensen
    {T : Mat →ₗ[ℂ] Mat} (hT : IsPositiveMap T) (hSub : T 1 ≤ (1 : Mat))
    {p : ℝ} (hp : p ∈ Set.Icc (1 : ℝ) 2) {A : Mat} (hA : 0 ≤ A) :
    (T A) ^ p ≤ T (A ^ p)

/-- **Operator Jensen for concave `log`** (Wolf Thm. 5.1, log case).

For a positive **unital** map `T` and positive-definite `A`:
  `T(log A) ≤ log(T A)`.

Follows from `log_operator_concave` combined with the operator Jensen
inequality. Requires unitality (`T 1 = 1`), not merely subunitality.

References:
* Wolf, Thm. 5.1
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
