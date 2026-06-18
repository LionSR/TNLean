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
`CFC.concaveOn_log`.  The axioms below remain because those concavity
statements are not yet accompanied by a Hansen--Pedersen operator Jensen
theorem for arbitrary positive subunital or unital maps, by operator
convexity of `x ↦ x ^ p` for `1 ≤ p ≤ 2`, or by Lieb's joint concavity
theorem.

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
functional-calculus concavity inputs for the first and third statements, but
not the positive-map Jensen theorem needed to obtain the displayed
inequalities.

The remaining Mathlib or local formalization gaps are:

* General operator Jensen inequality for positive maps.
* `CFC.Rpow.Order`: operator convexity of `rpow` over `[1, 2]`.
* Lieb concavity integral representation: absent from Mathlib.

## Proof plan

1. **Concave Jensen for `rpow`, `p ∈ [0, 1]`**: combine
   `CFC.concaveOn_rpow` with the Hansen--Pedersen block-matrix proof of
   operator Jensen for positive subunital maps.  The finite-POVM compression
   half of this route is recorded in
   `TNLean.Channel.Schwarz.OperatorJensenAux`.
2. **Operator convexity of `rpow` for `p ∈ [1, 2]`**: use the
   decomposition `x^p = x · x^{p-1}` for `p ∈ [1, 2]`, reducing to
   concavity of `x^{p-1}` for `p - 1 ∈ [0, 1]`.
3. **Concave Jensen for `log`**: combine `CFC.concaveOn_log` with the
   unital Hansen--Pedersen Jensen theorem.
4. **Lieb concavity**: requires the integral representation
   `A^s B^{1-s} = (sin πs/π) ∫₀^∞ t^{s-1} A(A+tB)⁻¹ B dt` and
   resolvent monotonicity.

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
private local instance instAxiomOCCStarRing : CStarRing Mat :=
  Matrix.instCStarRing
private local instance instAxiomOCPartialOrder : PartialOrder Mat :=
  Matrix.instPartialOrder
private local instance instAxiomOCStarOrderedRing : StarOrderedRing Mat :=
  Matrix.instStarOrderedRing
private local instance instAxiomOCCStarAlgebra : CStarAlgebra Mat :=
  CStarAlgebra.mk

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
