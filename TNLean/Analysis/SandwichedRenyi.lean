/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Analysis.SandwichedRenyiTwo

/-!
# The sandwiched Rényi trace functional

For a real order \(\alpha\), this file defines the total trace functional
\[
  \operatorname{Re}\operatorname{Tr}\!\left[
    \left(\omega^{(1-\alpha)/(2\alpha)}
      \rho\,\omega^{(1-\alpha)/(2\alpha)}\right)^\alpha
  \right].
\]
On positive-semidefinite \(\rho\) and positive-definite \(\omega\), this is the
unnormalized trace term entering the faithful sandwiched Rényi divergence. When
\(\rho\) is a density matrix, it is the quantity inside the logarithm. The
intended range here is \(1\leq\alpha\leq2\). No trace-one assumption is needed
for the algebraic properties proved below.

Continuous-functional-calculus real powers are total: in particular, negative
powers vanish at a zero eigenvalue. For \(\alpha>1\), within the present
\(1\leq\alpha\leq2\) application, finite divergence requires
\(\operatorname{supp}\rho\subseteq\operatorname{supp}\omega\), equivalently
\(\ker\omega\subseteq\ker\rho\). On positive-semidefinite inputs satisfying
this inclusion, the zero-on-kernel convention is the generalized inverse. If
the inclusion fails, the divergence is infinite, whereas the totalized CFC
value remains finite and is not the divergence trace term. We prove only
nonnegativity on the faithful domain and the exact order-one and order-two
endpoints; no assertion about continuity, interpolation, monotonicity, limits,
derivatives, logarithmic divergence, or comparison with Umegaki relative
entropy is made.

## Main definitions

* `TNLean.sandwichedRenyiTrace` — the total sandwiched Rényi trace functional.

## Main results

* `TNLean.sandwichedRenyiTrace_nonneg` — faithful-domain nonnegativity.
* `TNLean.sandwichedRenyiTrace_one` — the exact order-one endpoint.
* `TNLean.sandwichedRenyiTrace_two` — the exact order-two endpoint.

## References

* Müller-Lennert, Dupuis, Szehr, Fehr, and Tomamichel,
  *On quantum Rényi entropies: a new generalization and some properties*,
  arXiv:1306.3142v4, Definition 2 and Theorem 5.
* Beigi, *Sandwiched Rényi divergence satisfies data processing inequality*,
  arXiv:1306.5920, Equation (2) and Theorem 7.
-/

open scoped Matrix ComplexOrder MatrixOrder
open Matrix

namespace TNLean

noncomputable section

variable {D : ℕ}

local notation "Mat" => Matrix (Fin D) (Fin D) ℂ

open scoped Matrix.Norms.L2Operator

private local instance instRenyiNormedRing : NormedRing Mat :=
  Matrix.instL2OpNormedRing
private local instance instRenyiNormedAlgebra : NormedAlgebra ℂ Mat :=
  Matrix.instL2OpNormedAlgebra
private local instance instRenyiCStarRing : CStarRing Mat :=
  Matrix.instCStarRing
private local instance instRenyiPartialOrder : PartialOrder Mat :=
  Matrix.instPartialOrder
private local instance instRenyiStarOrderedRing : StarOrderedRing Mat :=
  Matrix.instStarOrderedRing
private local instance instRenyiCStarAlgebra : CStarAlgebra Mat :=
  CStarAlgebra.mk

/-- The total sandwiched Rényi trace functional
\[
  \operatorname{Re}\operatorname{Tr}\!\left[
    \left(\omega^{(1-\alpha)/(2\alpha)}
      \rho\,\omega^{(1-\alpha)/(2\alpha)}\right)^\alpha
  \right].
\]
For positive-semidefinite \(\rho\), positive-definite \(\omega\), and
\(1\leq\alpha\leq2\), this is the unnormalized trace term used in the faithful
sandwiched Rényi divergence of Müller-Lennert et al., arXiv:1306.3142v4,
Definition 2, and Beigi, arXiv:1306.5920, Equation (2). For trace-one \(\rho\),
it is the quantity inside the logarithm. The definition is total for every real
\(\alpha\), including \(\alpha=0\), and for singular \(\omega\). For
\(\alpha>1\), within the present \(1\leq\alpha\leq2\) application, finite
divergence requires
\(\operatorname{supp}\rho\subseteq\operatorname{supp}\omega\). On
positive-semidefinite inputs satisfying this inclusion, the zero-on-kernel
powers implement the generalized inverse. If the inclusion fails, the finite
totalized CFC value is not the divergence trace term. -/
noncomputable def sandwichedRenyiTrace (α : ℝ) (ρ ω : Mat) : ℝ :=
  let q := ω ^ ((1 - α) / (2 * α))
  (Matrix.trace ((q * ρ * q) ^ α)).re

/-- The sandwiched Rényi trace functional is nonnegative when \(\rho\) is
positive semidefinite and \(\omega\) is positive definite.

This is the faithful-domain positivity of the trace expression in
Müller-Lennert et al., arXiv:1306.3142v4, Definition 2, and Beigi,
arXiv:1306.5920, Equation (2). It holds for every real order because the
continuous-functional-calculus real power is positive semidefinite. -/
theorem sandwichedRenyiTrace_nonneg
    {α : ℝ} {ρ ω : Mat} (hρ : ρ.PosSemidef) (_hω : ω.PosDef) :
    0 ≤ sandwichedRenyiTrace α ρ ω := by
  let q := ω ^ ((1 - α) / (2 * α))
  have hq : q.PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp CFC.rpow_nonneg
  have hX : (q * ρ * q).PosSemidef := by
    simpa only [hq.isHermitian.eq] using hρ.mul_mul_conjTranspose_same q
  have hpow_nonneg : 0 ≤ (q * ρ * q) ^ α := by
    rw [CFC.rpow_eq_cfc_real hX.nonneg]
    exact cfc_nonneg fun x hx ↦
      Real.rpow_nonneg (spectrum_nonneg_of_nonneg hX.nonneg hx) α
  have hpow : ((q * ρ * q) ^ α).PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp hpow_nonneg
  exact (Complex.nonneg_iff.mp hpow.trace_nonneg).1

/-- At order one, the sandwiched Rényi trace functional is
\(\operatorname{Re}\operatorname{Tr}(\rho)\).

This is the \(\alpha=1\) endpoint of the expression in Müller-Lennert et al.,
arXiv:1306.3142v4, Definition 2. -/
theorem sandwichedRenyiTrace_one
    {ρ ω : Mat} (hρ : ρ.PosSemidef) (hω : ω.PosDef) :
    sandwichedRenyiTrace 1 ρ ω = (Matrix.trace ρ).re := by
  rw [sandwichedRenyiTrace]
  rw [show (1 - (1 : ℝ)) / (2 * 1) = 0 by norm_num]
  rw [CFC.rpow_zero ω hω.posSemidef.nonneg]
  simp only [Matrix.one_mul, Matrix.mul_one]
  rw [CFC.rpow_one ρ hρ.nonneg]

/-- At order two, the general sandwiched Rényi trace functional agrees exactly
with `sandwichedRenyiTwoTrace`.

This is the \(\alpha=2\) endpoint of Müller-Lennert et al.,
arXiv:1306.3142v4, Definition 2, and Beigi, arXiv:1306.5920, Equation (2). -/
theorem sandwichedRenyiTrace_two
    {ρ ω : Mat} (hρ : ρ.PosSemidef) (_hω : ω.PosDef) :
    sandwichedRenyiTrace 2 ρ ω = sandwichedRenyiTwoTrace ρ ω := by
  rw [sandwichedRenyiTrace, sandwichedRenyiTwoTrace]
  rw [show (1 - (2 : ℝ)) / (2 * 2) = -(1 / 4 : ℝ) by norm_num]
  let q := ω ^ (-(1 / 4 : ℝ))
  have hq : q.PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp CFC.rpow_nonneg
  have hX : (q * ρ * q).PosSemidef := by
    simpa only [hq.isHermitian.eq] using hρ.mul_mul_conjTranspose_same q
  change (Matrix.trace ((q * ρ * q) ^ (2 : ℝ))).re =
    (Matrix.trace ((q * ρ * q) * (q * ρ * q))).re
  rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num,
    CFC.rpow_natCast (q * ρ * q) 2 hX.nonneg, pow_two]

end

end TNLean
