/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import TNLean.Algebra.MatrixAux

/-!
# The order-two sandwiched trace functional

This file introduces only the order-two trace functional
\[
  \operatorname{Tr}\!\left[
    \left(\omega^{-1/4}\rho\,\omega^{-1/4}\right)^2
  \right],
\]
which is the expression inside the logarithm in the order-two sandwiched
Rényi divergence for trace-one states. Negative powers vanish on the zero
eigenspace, in accordance with the support convention of the source.

The logarithmic comparison with quantum relative entropy requires the
monotonicity in the order of the sandwiched Rényi divergence. That analytic
result is not asserted here.

## Main definitions

* `TNLean.sandwichedRenyiTwoTrace` — the order-two sandwiched trace functional.

## Main results

* `TNLean.sandwichedRenyiTwoTrace_nonneg` — positivity on
  positive-semidefinite arguments.
* `TNLean.posDef_quarter_inv_sq` — the faithful identity
  \(\omega^{-1/4}\omega^{-1/4}=\omega^{-1/2}\).
* `TNLean.sandwichedRenyiTwoTrace_eq_weighted` — the equivalent weighted
  Hilbert--Schmidt trace expression for faithful \(\omega\).

## References

* Müller-Lennert, Dupuis, Szehr, Fehr, and Tomamichel,
  *On quantum Rényi entropies: a new generalization and some properties*,
  arXiv:1306.3142v4, Definition 2.
* Beigi, *Sandwiched Rényi divergence satisfies data processing inequality*,
  arXiv:1306.5920, Theorem 7.
-/

open scoped Matrix ComplexOrder MatrixOrder
open Matrix

namespace TNLean

noncomputable section

variable {D : ℕ}

local notation "Mat" => Matrix (Fin D) (Fin D) ℂ

open scoped Matrix.Norms.L2Operator

private local instance instRenyiTwoNormedRing : NormedRing Mat :=
  Matrix.instL2OpNormedRing
private local instance instRenyiTwoNormedAlgebra : NormedAlgebra ℂ Mat :=
  Matrix.instL2OpNormedAlgebra
private local instance instRenyiTwoCStarRing : CStarRing Mat :=
  Matrix.instCStarRing
private local instance instRenyiTwoPartialOrder : PartialOrder Mat :=
  Matrix.instPartialOrder
private local instance instRenyiTwoStarOrderedRing : StarOrderedRing Mat :=
  Matrix.instStarOrderedRing
private local instance instRenyiTwoCStarAlgebra : CStarAlgebra Mat :=
  CStarAlgebra.mk

/-- The order-two sandwiched trace functional
\(\operatorname{Re}\operatorname{Tr}[(\omega^{-1/4}\rho\omega^{-1/4})^2]\).

For positive-semidefinite matrices the real part is redundant. The definition
uses the source's convention that a negative power is zero on the zero
eigenspace; see Müller-Lennert et al., arXiv:1306.3142v4, Definition 2 and
lines 94--96. -/
noncomputable def sandwichedRenyiTwoTrace (ρ ω : Mat) : ℝ :=
  let q := ω ^ (-(1 / 4 : ℝ))
  (Matrix.trace ((q * ρ * q) * (q * ρ * q))).re

/-- The order-two sandwiched trace functional is nonnegative on
positive-semidefinite arguments.

This is the positivity of the expression in Müller-Lennert et al.,
arXiv:1306.3142v4, Definition 2, specialized to order two. -/
theorem sandwichedRenyiTwoTrace_nonneg
    {ρ ω : Mat} (hρ : ρ.PosSemidef) (_hω : ω.PosSemidef) :
    0 ≤ sandwichedRenyiTwoTrace ρ ω := by
  let q := ω ^ (-(1 / 4 : ℝ))
  have hq : q.PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp CFC.rpow_nonneg
  have hX : (q * ρ * q).PosSemidef := by
    simpa only [hq.isHermitian.eq] using hρ.mul_mul_conjTranspose_same q
  exact (Complex.nonneg_iff.mp (hX.trace_mul_nonneg hX)).1

/-- For a positive-definite matrix, two inverse quarter-powers multiply to the
inverse square root.

This is the exponent identity used in the order-two specialization of
Müller-Lennert et al., arXiv:1306.3142v4, Definition 2. -/
theorem posDef_quarter_inv_sq
    {ω : Mat} (hω : ω.PosDef) :
    ω ^ (-(1 / 4 : ℝ)) * ω ^ (-(1 / 4 : ℝ)) = ω ^ (-(1 / 2 : ℝ)) := by
  rw [← CFC.rpow_add hω.isUnit]
  congr 1
  ring

/-- For faithful \(\omega\), the order-two sandwiched trace is
\(\operatorname{Re}\operatorname{Tr}
  (\rho\omega^{-1/2}\rho\omega^{-1/2})\).

This is the weighted Hilbert--Schmidt form of the order-two expression in
Müller-Lennert et al., arXiv:1306.3142v4, Definition 2. -/
theorem sandwichedRenyiTwoTrace_eq_weighted
    {ρ ω : Mat} (hω : ω.PosDef) :
    sandwichedRenyiTwoTrace ρ ω =
      (Matrix.trace (ρ * ω ^ (-(1 / 2 : ℝ)) * ρ * ω ^ (-(1 / 2 : ℝ)))).re := by
  rw [sandwichedRenyiTwoTrace]
  let q := ω ^ (-(1 / 4 : ℝ))
  have hq : q * q = ω ^ (-(1 / 2 : ℝ)) := posDef_quarter_inv_sq hω
  have hcycle :
      Matrix.trace ((q * ρ * q) * (q * ρ * q)) =
        Matrix.trace (ρ * (q * q) * ρ * (q * q)) := by
    calc
      Matrix.trace ((q * ρ * q) * (q * ρ * q)) =
          Matrix.trace (q * (ρ * q * q * ρ * q)) := by
            congr 1
            simp only [Matrix.mul_assoc]
      _ = Matrix.trace ((ρ * q * q * ρ * q) * q) :=
        Matrix.trace_mul_comm q _
      _ = Matrix.trace (ρ * (q * q) * ρ * (q * q)) := by
        congr 1
        simp only [Matrix.mul_assoc]
  rw [hcycle, hq]

end

end TNLean
