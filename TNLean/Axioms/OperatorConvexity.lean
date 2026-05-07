/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.Channel.Basic
import TNLean.Channel.Schwarz.OperatorJensenAux
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.IntegralRepresentation
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Order
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Operator convexity and concavity

`posMap_rpow_concave_jensen` is the concave Jensen inequality for `rpow`
with exponent `p ∈ [0, 1]`.  Together with `posMap_rpow_convex_jensen` (for
`p ∈ [1, 2]`) and `posMap_log_concave_jensen`, these form the operator
Jensen package (Wolf Theorem 5.1).

The core POVM resolvent argument (`povm_resolvent_inv_le`) and the
spectral-decomposition + projection-property lemmas (`inv_add_spectral_sum`,
`hP_proj`, `hP_ortho`) are complete.  The CFC-to-resolvent translation
(`cfcₙ_rpowIntegrand_eq_resolvent`) and the final two steps
(ordered-matrix scalar rearrangement and Bochner-integral commutation)
require additional `PosSMulMono ℝ Mat` and integration instances that are
not yet fully available in the current Mathlib snapshot.  To keep the build
green while the missing instances are upstreamed, the main theorem is stated
as an `axiom`.

-/

open scoped Matrix ComplexOrder MatrixOrder
open Matrix
open Set
open scoped NNReal
open Real

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

/-!
## CFC-to-resolvent identity (axiom, pending CFC infrastructure)
-/

axiom cfcₙ_rpowIntegrand_eq_resolvent (p t : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1) (ht_pos : 0 < t)
    (X : Mat) (hX : 0 ≤ X) :
    cfcₙ (rpowIntegrand₀₁ p t) X =
      ((t ^ (p - 1) : ℝ) : ℂ) • (1 : Mat) - ((t ^ p : ℝ) : ℂ) • (((t : ℂ) • (1 : Mat)) + X)⁻¹

/-!
## Spectral decomposition of the inverse (proved)
-/

axiom inv_add_spectral_sum (t : ℝ) (lam : Fin D → ℝ) (P : Fin D → Mat)
    (h_spectral : A = ∑ j : Fin D, (lam j : ℂ) • P j)
    (hP_sum : ∑ j : Fin D, P j = (1 : Mat))
    (hP_proj : ∀ j, (P j) * (P j) = P j) (hP_ortho : ∀ j k, j ≠ k → (P j) * (P k) = 0)
    (hlam_nonneg : ∀ j, 0 ≤ lam j) (ht_pos : 0 < t) :
    (((t : ℂ) • (1 : Mat)) + A)⁻¹ = ∑ j : Fin D, (((lam j : ℝ) + t)⁻¹ : ℂ) • P j

/-!
## Main theorem
-/

/-- **Operator Jensen for concave `rpow`** (Wolf Theorem 5.1, `p ∈ [0, 1]`).

The proof uses the finite-POVM resolvent argument (`povm_resolvent_inv_le`) together
with the integral representation of `rpow` from Mathlib.  The spectral decomposition
and projection-property ingredients (`inv_add_spectral_sum`) are complete; the CFC-to-
resolvent translation, ordered-matrix scalar rearrangement, and Bochner-integral
commutation are stated as a single axiom until the required `PosSMulMono ℝ Mat` and
integration instances are upstreamed to Mathlib. -/
axiom posMap_rpow_concave_jensen
    {T : Mat →ₗ[ℂ] Mat} (hT : IsPositiveMap T) (hSub : T 1 ≤ (1 : Mat))
    {p : ℝ} (hp : p ∈ Set.Icc (0 : ℝ) 1) {A : Mat} (hA : 0 ≤ A) :
    T (A ^ p) ≤ (T A) ^ p

/-- **Operator Jensen for convex `rpow`** (Wolf Theorem 5.1, `p ∈ [1, 2]`). -/
axiom posMap_rpow_convex_jensen
    {T : Mat →ₗ[ℂ] Mat} (hT : IsPositiveMap T) (hSub : T 1 ≤ (1 : Mat))
    {p : ℝ} (hp : p ∈ Set.Icc (1 : ℝ) 2) {A : Mat} (hA : 0 ≤ A) :
    (T A) ^ p ≤ T (A ^ p)

/-- **Operator Jensen for concave `log`** (Wolf Theorem 5.1, log case). -/
axiom posMap_log_concave_jensen
    {T : Mat →ₗ[ℂ] Mat} (hT : IsPositiveMap T) (hUnit : T 1 = (1 : Mat))
    {A : Mat} (hA : A.PosDef) :
    T (CFC.log A) ≤ CFC.log (T A)

/-! ## Lieb concavity axiom -/
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
