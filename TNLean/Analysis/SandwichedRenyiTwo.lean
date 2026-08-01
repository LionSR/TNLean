/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import TNLean.Algebra.MatrixAux
import TNLean.Algebra.FrobeniusHilbert
import TNLean.Analysis.CfcConjugation
import TNLean.Analysis.Entropy
import TNLean.Analysis.SupportCompression
import TNLean.Analysis.SupportLogJensen
import Mathlib.LinearAlgebra.Matrix.Vec

/-!
# The order-two sandwiched trace functional

This file introduces only the order-two trace functional
\[
  \operatorname{Tr}\!\left[
    \left(\omega^{-1/4}\rho\,\omega^{-1/4}\right)^2
  \right],
\]
which is the expression inside the logarithm in the order-two sandwiched
Rényi divergence for trace-one states satisfying
\(\operatorname{supp}\rho\subseteq\operatorname{supp}\omega\). Negative powers
vanish on the zero eigenspace. Outside this support domain the totalized trace
functional below remains finite, whereas the sandwiched divergence is infinite.

A support-aware logarithmic Jensen argument proves the comparison with
quantum relative entropy directly for faithful references. Compression to the
reference support gives the singular-reference theorem in
`TNLean.Analysis.SupportCompressedEntropy`.

## Main definitions

* `TNLean.sandwichedRenyiTwoTrace` — the order-two sandwiched trace functional.
* `TNLean.RelativeModularHalfMoment.operator` and
  `TNLean.RelativeModularHalfMoment.vector` — the operator and vector in the
  relative-modular half-moment construction.

## Main results

* `TNLean.sandwichedRenyiTwoTrace_nonneg` — positivity on
  positive-semidefinite arguments.
* `TNLean.sandwichedRenyiTwoTrace_conj_unitary` — invariance under unitary
  conjugation of both arguments.
* `TNLean.sandwichedRenyiTwoTrace_submatrix_equiv` — invariance under simultaneous
  reindexing of both arguments.
* `TNLean.posDef_rpow_neg_quarter_mul_self` — the faithful identity
  \(\omega^{-1/4}\omega^{-1/4}=\omega^{-1/2}\).
* `TNLean.sandwichedRenyiTwoTrace_eq_weighted` — a cyclically reordered trace
  expression for faithful \(\omega\); when \(\rho\) is Hermitian, its common
  value is the squared Hilbert--Schmidt norm of the sandwiched matrix.
* `TNLean.RelativeModularHalfMoment.log_expectation_eq_half_quantumRelativeEntropy` —
  the exact logarithmic half-moment identity.
* `TNLean.RelativeModularHalfMoment.expectation_sq_le_sandwichedRenyiTwoTrace` —
  the Hilbert--Schmidt bound for the ordinary half moment.
* `TNLean.quantumRelativeEntropy_le_log_sandwichedRenyiTwoTrace_posDef` — the
  direct logarithmic comparison for a faithful reference.

## References

* Müller-Lennert, Dupuis, Szehr, Fehr, and Tomamichel,
  *On quantum Rényi entropies: a new generalization and some properties*,
  arXiv:1306.3142v4, Definitions 2 and 5, and Lemma 19 (used in the proof of
  Theorem 7).
* Beigi, *Sandwiched Rényi divergence satisfies data processing inequality*,
  arXiv:1306.5920, Theorem 7.
-/

open scoped Matrix ComplexOrder MatrixOrder
open Matrix

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

namespace Matrix.PosSemidef

/-- Sandwiching a positive-semidefinite matrix between equal real powers of a
positive-semidefinite matrix preserves positive semidefiniteness. -/
theorem rpow_mul_mul_rpow
    {ρ ω : Mat} (hρ : ρ.PosSemidef) (hω : ω.PosSemidef) (r : ℝ) :
    (ω ^ r * ρ * ω ^ r).PosSemidef := by
  have hωr_nonneg : 0 ≤ ω ^ r := by
    rw [CFC.rpow_eq_cfc_real hω.nonneg]
    exact cfc_nonneg fun x hx ↦
      Real.rpow_nonneg (spectrum_nonneg_of_nonneg hω.nonneg hx) r
  have hωr : (ω ^ r).PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp hωr_nonneg
  simpa only [hωr.isHermitian.eq] using hρ.mul_mul_conjTranspose_same (ω ^ r)

end Matrix.PosSemidef

namespace TNLean

/-- The order-two sandwiched trace functional
\(\operatorname{Re}\operatorname{Tr}[(\omega^{-1/4}\rho\omega^{-1/4})^2]\).

For positive-semidefinite matrices the real part is redundant. When the
matrices have trace one and
\(\operatorname{supp}\rho\subseteq\operatorname{supp}\omega\), its logarithm
is the order-two sandwiched Rényi divergence. The negative power is zero on the
zero eigenspace, so this totalized functional remains finite outside that
support domain and must not there be identified with the divergence; see
Müller-Lennert et al., arXiv:1306.3142v4, Definition 2 and lines 94--96. -/
noncomputable def sandwichedRenyiTwoTrace
    {n : Type*} [Fintype n] [DecidableEq n]
    (ρ ω : Matrix n n ℂ) : ℝ :=
  let q := ω ^ (-(1 / 4 : ℝ))
  (Matrix.trace ((q * ρ * q) * (q * ρ * q))).re

/-- The order-two sandwiched trace functional is invariant under simultaneous
unitary conjugation of its state and reference arguments. -/
theorem sandwichedRenyiTwoTrace_conj_unitary
    {n : Type*} [Fintype n] [DecidableEq n]
    {ρ ω : Matrix n n ℂ} (hω : ω.PosSemidef)
    (U : unitary (Matrix n n ℂ)) :
    sandwichedRenyiTwoTrace
        ((U : Matrix n n ℂ) * ρ * star (U : Matrix n n ℂ))
        ((U : Matrix n n ℂ) * ω * star (U : Matrix n n ℂ)) =
      sandwichedRenyiTwoTrace ρ ω := by
  let q := ω ^ (-(1 / 4 : ℝ))
  let Umat : Matrix n n ℂ := U
  have hq :
      (Umat * ω * star Umat) ^ (-(1 / 4 : ℝ)) =
        Umat * q * star Umat := by
    exact Matrix.rpow_conj_unitary hω (-(1 / 4 : ℝ)) U
  have hU : star Umat * Umat = 1 := Unitary.coe_star_mul_self U
  rw [sandwichedRenyiTwoTrace, sandwichedRenyiTwoTrace]
  change (Matrix.trace
      (((Umat * ω * star Umat) ^ (-(1 / 4 : ℝ)) *
          (Umat * ρ * star Umat) *
          (Umat * ω * star Umat) ^ (-(1 / 4 : ℝ))) *
        ((Umat * ω * star Umat) ^ (-(1 / 4 : ℝ)) *
          (Umat * ρ * star Umat) *
          (Umat * ω * star Umat) ^ (-(1 / 4 : ℝ))))).re = _
  rw [hq]
  have hsandwich :
      (Umat * q * star Umat) * (Umat * ρ * star Umat) *
          (Umat * q * star Umat) =
        Umat * (q * ρ * q) * star Umat := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (star Umat) Umat, hU, Matrix.one_mul,
      ← Matrix.mul_assoc (star Umat) Umat, hU, Matrix.one_mul]
  rw [hsandwich]
  have hsquare :
      (Umat * (q * ρ * q) * star Umat) *
          (Umat * (q * ρ * q) * star Umat) =
        Umat * ((q * ρ * q) * (q * ρ * q)) * star Umat := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (star Umat) Umat, hU, Matrix.one_mul]
  rw [hsquare, Matrix.trace_mul_cycle, hU, Matrix.one_mul]

/-- The order-two sandwiched trace functional is invariant under simultaneous
reindexing of its state and reference arguments. -/
theorem sandwichedRenyiTwoTrace_submatrix_equiv
    {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    {ρ ω : Matrix m m ℂ} (hω : ω.PosSemidef) (e : m ≃ n) :
    sandwichedRenyiTwoTrace
        (ρ.submatrix e.symm e.symm) (ω.submatrix e.symm e.symm) =
      sandwichedRenyiTwoTrace ρ ω := by
  have hq :
      (ω.submatrix e.symm e.symm) ^ (-(1 / 4 : ℝ)) =
        (ω ^ (-(1 / 4 : ℝ))).submatrix e.symm e.symm := by
    rw [CFC.rpow_eq_cfc_real (hω.submatrix e.symm).nonneg,
      CFC.rpow_eq_cfc_real hω.nonneg]
    exact Matrix.cfc_submatrix_equiv hω.isHermitian (fun x : ℝ => x ^ (-(1 / 4 : ℝ))) e
  rw [sandwichedRenyiTwoTrace, sandwichedRenyiTwoTrace, hq,
    Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv,
    Matrix.submatrix_mul_equiv, Matrix.trace_submatrix_equiv]

/-- The order-two sandwiched trace functional is nonnegative on
positive-semidefinite arguments.

This is the positivity of the expression in Müller-Lennert et al.,
arXiv:1306.3142v4, Definition 2, specialized to order two. -/
theorem sandwichedRenyiTwoTrace_nonneg
    {ρ ω : Mat} (hρ : ρ.PosSemidef) (hω : ω.PosSemidef) :
    0 ≤ sandwichedRenyiTwoTrace ρ ω := by
  let q := ω ^ (-(1 / 4 : ℝ))
  have hX : (q * ρ * q).PosSemidef :=
    _root_.Matrix.PosSemidef.rpow_mul_mul_rpow hρ hω (-(1 / 4 : ℝ))
  exact (Complex.nonneg_iff.mp (hX.trace_mul_nonneg hX)).1

/-- For a positive-definite matrix, two inverse quarter-powers multiply to the
inverse square root.

This is the exponent identity used in the order-two specialization of
Müller-Lennert et al., arXiv:1306.3142v4, Definition 2. -/
theorem posDef_rpow_neg_quarter_mul_self
    {ω : Mat} (hω : ω.PosDef) :
    ω ^ (-(1 / 4 : ℝ)) * ω ^ (-(1 / 4 : ℝ)) = ω ^ (-(1 / 2 : ℝ)) := by
  rw [← CFC.rpow_add hω.isUnit]
  congr 1
  ring

/-- For faithful \(\omega\), the order-two sandwiched trace satisfies the
algebraic identity
\(\operatorname{Re}\operatorname{Tr}
  (\rho\omega^{-1/2}\rho\omega^{-1/2})\).

No Hermiticity assumption on \(\rho\) is needed for this cyclic trace identity.
When \(\rho\) is Hermitian, in particular when it is positive semidefinite,
\(\omega^{-1/4}\rho\omega^{-1/4}\) is Hermitian, and the common value is its
squared Hilbert--Schmidt norm. This is the order-two expression in
Müller-Lennert et al., arXiv:1306.3142v4, Definition 2. -/
theorem sandwichedRenyiTwoTrace_eq_weighted
    {ρ ω : Mat} (hω : ω.PosDef) :
    sandwichedRenyiTwoTrace ρ ω =
      (Matrix.trace (ρ * ω ^ (-(1 / 2 : ℝ)) * ρ * ω ^ (-(1 / 2 : ℝ)))).re := by
  rw [sandwichedRenyiTwoTrace]
  let q := ω ^ (-(1 / 4 : ℝ))
  have hq : q * q = ω ^ (-(1 / 2 : ℝ)) :=
    posDef_rpow_neg_quarter_mul_self hω
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

namespace RelativeModularHalfMoment

/-- The square root of the state in the relative-modular half-moment construction. -/
noncomputable def sqrtState (ρ : Mat) : Mat :=
  CFC.sqrt ρ

/-- The inverse square root of the reference in the relative-modular half-moment construction. -/
noncomputable def referenceInvSqrt (ω : Mat) : Mat :=
  ω ^ (-(1 / 2 : ℝ))

/-- The positive relative-modular operator used in the order-two half-moment argument. -/
noncomputable def operator (ρ ω : Mat) : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ :=
  Matrix.kronecker (Matrix.transpose (sqrtState ρ)) (referenceInvSqrt ω)

/-- The vectorized square root of the state in the relative-modular half-moment argument. -/
noncomputable def vector (ρ : Mat) : Fin D × Fin D → ℂ :=
  Matrix.vec (sqrtState ρ)

private theorem real_inner_eq_complex_re (x y : EuclideanSpace ℂ (Fin D × Fin D)) :
    inner ℝ x y = (inner ℂ x y).re := by
  simp [PiLp.inner_apply, RCLike.inner_apply, Complex.inner]

/-- The state square root is positive semidefinite. -/
theorem sqrtState_posSemidef (ρ : Mat) : (sqrtState ρ).PosSemidef :=
  Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg ρ)

/-- The inverse square root of a faithful reference is positive definite. -/
theorem referenceInvSqrt_posDef {ω : Mat} (hω : ω.PosDef) :
    (referenceInvSqrt ω).PosDef := by
  have hT : (referenceInvSqrt ω).PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp CFC.rpow_nonneg
  apply hT.posDef_iff_isUnit.mpr
  apply IsUnit.of_mul_eq_one (ω ^ (1 / 2 : ℝ))
  rw [referenceInvSqrt, ← CFC.rpow_add hω.isUnit]
  convert CFC.rpow_zero ω using 1
  norm_num

/-- The relative-modular half-moment operator is positive semidefinite. -/
theorem operator_posSemidef (ρ ω : Mat) : (operator ρ ω).PosSemidef :=
  (sqrtState_posSemidef ρ).transpose.kronecker
    (Matrix.nonneg_iff_posSemidef.mp CFC.rpow_nonneg)

/-- The squared norm of the vectorized state square root is the trace of the state. -/
theorem vector_norm_sq {ρ : Mat} (hρ : ρ.PosSemidef) :
    star (vector ρ) ⬝ᵥ vector ρ = ρ.trace := by
  rw [vector, Matrix.star_vec_dotProduct_vec]
  have hR := sqrtState_posSemidef ρ
  rw [hR.isHermitian.eq, sqrtState, CFC.sqrt_mul_sqrt_self ρ hρ.nonneg]

/-- A trace-one state has a unit vectorized square root. -/
theorem vector_unit {ρ : Mat} (hρ : ρ.PosSemidef) (hρtr : ρ.trace = 1) :
    star (vector ρ) ⬝ᵥ vector ρ = (1 : ℂ) := by
  rw [vector_norm_sq hρ, hρtr]

/-- For a faithful reference, the vectorized state square root lies in the support of the
relative-modular half-moment operator. -/
theorem supportProj_mulVec_vector {ρ ω : Mat} (hω : ω.PosDef) :
    (operator_posSemidef ρ ω).supportProj *ᵥ vector ρ = vector ρ := by
  let R := sqrtState ρ
  have hR : R.PosSemidef := sqrtState_posSemidef ρ
  have hT : (referenceInvSqrt ω).PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp CFC.rpow_nonneg
  have hsupport :
      (operator_posSemidef ρ ω).supportProj =
        Matrix.kronecker hR.transpose.supportProj hT.supportProj :=
    hR.transpose.supportProj_kronecker hT
  rw [hsupport, (referenceInvSqrt_posDef hω).supportProj_eq_one]
  rw [vector, Matrix.kronecker, Matrix.kronecker_mulVec_vec]
  simp only [Matrix.one_mul]
  have hPRt : hR.transpose.supportProj * Matrix.transpose R = Matrix.transpose R :=
    hR.transpose.isHermitian.supportProj_mul_self
  have hRPt : R * hR.transpose.supportProjᵀ = R := by
    have ht := congrArg Matrix.transpose hPRt
    simpa only [Matrix.transpose_mul, Matrix.transpose_transpose] using ht
  rw [hRPt]

/-- Applying the relative-modular half-moment operator to the vectorized state square root
produces the vectorized weighted state. -/
theorem operator_mulVec_vector {ρ ω : Mat} (hρ : ρ.PosSemidef) :
    operator ρ ω *ᵥ vector ρ = Matrix.vec (referenceInvSqrt ω * ρ) := by
  rw [operator, vector, Matrix.kronecker, Matrix.kronecker_mulVec_vec,
    Matrix.transpose_transpose, Matrix.mul_assoc, sqrtState,
    CFC.sqrt_mul_sqrt_self ρ hρ.nonneg]

/-- The ordinary relative-modular moment is the real Hilbert--Schmidt pairing of the state
square root with its reference-weighted sandwich. -/
theorem expectation_eq_frobenius_inner (ρ ω : Mat) :
    (star (vector ρ) ⬝ᵥ (operator ρ ω *ᵥ vector ρ)).re =
      inner ℝ
        (Matrix.frobeniusEquivEuclidean (Fin D) (Fin D) (sqrtState ρ))
        (Matrix.frobeniusEquivEuclidean (Fin D) (Fin D)
          (sqrtState ρ * referenceInvSqrt ω * sqrtState ρ)) := by
  let R := sqrtState ρ
  let T := referenceInvSqrt ω
  have hR : R.PosSemidef := sqrtState_posSemidef ρ
  rw [operator, vector, Matrix.kronecker, Matrix.kronecker_mulVec_vec,
    Matrix.star_vec_dotProduct_vec, real_inner_eq_complex_re,
    Matrix.inner_frobeniusEquivEuclidean, hR.isHermitian.eq,
    Matrix.transpose_transpose]
  calc
    (Matrix.trace (R * (T * R * R))).re =
        (Matrix.trace ((R * T * R) * R)).re := by
      simp only [Matrix.mul_assoc]
    _ = (Matrix.trace (R * (R * T * R))).re := by
      rw [Matrix.trace_mul_comm]

/-- The squared Hilbert--Schmidt norm of the reference-weighted square-root sandwich is the
order-two sandwiched trace. -/
theorem frobenius_inner_sandwich_self_eq_sandwichedRenyiTwoTrace
    {ρ ω : Mat} (hρ : ρ.PosSemidef) (hω : ω.PosDef) :
    inner ℝ
        (Matrix.frobeniusEquivEuclidean (Fin D) (Fin D)
          (sqrtState ρ * referenceInvSqrt ω * sqrtState ρ))
        (Matrix.frobeniusEquivEuclidean (Fin D) (Fin D)
          (sqrtState ρ * referenceInvSqrt ω * sqrtState ρ)) =
      sandwichedRenyiTwoTrace ρ ω := by
  let R := sqrtState ρ
  let T := referenceInvSqrt ω
  have hR : R.PosSemidef := sqrtState_posSemidef ρ
  have hRR : R * R = ρ := CFC.sqrt_mul_sqrt_self ρ hρ.nonneg
  have hT : T.PosSemidef := Matrix.nonneg_iff_posSemidef.mp CFC.rpow_nonneg
  rw [real_inner_eq_complex_re, Matrix.inner_frobeniusEquivEuclidean,
    Matrix.conjTranspose_mul,
    Matrix.conjTranspose_mul, hR.isHermitian.eq, hT.isHermitian.eq,
    sandwichedRenyiTwoTrace_eq_weighted hω]
  change (Matrix.trace ((R * (T * R)) * (R * T * R))).re = _
  calc
    (Matrix.trace ((R * (T * R)) * (R * T * R))).re =
        (Matrix.trace (R * (T * (R * R) * T * R))).re := by
      congr 1
      simp only [Matrix.mul_assoc]
    _ = (Matrix.trace (R * (T * ρ * T * R))).re := by rw [hRR]
    _ = (Matrix.trace ((T * ρ * T * R) * R)).re := by
      rw [Matrix.trace_mul_comm]
    _ = (Matrix.trace ((T * ρ * T) * ρ)).re := by
      rw [← hRR]
      simp only [Matrix.mul_assoc]
    _ = (Matrix.trace (ρ * (T * ρ * T))).re := by
      rw [Matrix.trace_mul_comm]
    _ = (Matrix.trace (ρ * T * ρ * T)).re := by
      simp only [Matrix.mul_assoc]

/-- The square of the ordinary relative-modular moment is at most the order-two sandwiched
trace. -/
theorem expectation_sq_le_sandwichedRenyiTwoTrace
    {ρ ω : Mat} (hρ : ρ.PosSemidef) (hω : ω.PosDef) (hρtr : ρ.trace = 1) :
    ((star (vector ρ) ⬝ᵥ (operator ρ ω *ᵥ vector ρ)).re) ^ 2 ≤
      sandwichedRenyiTwoTrace ρ ω := by
  let X := Matrix.frobeniusEquivEuclidean (Fin D) (Fin D) (sqrtState ρ)
  let Y := Matrix.frobeniusEquivEuclidean (Fin D) (Fin D)
    (sqrtState ρ * referenceInvSqrt ω * sqrtState ρ)
  have hXX : inner ℝ X X = 1 := by
    rw [real_inner_eq_complex_re, Matrix.inner_frobeniusEquivEuclidean]
    rw [(sqrtState_posSemidef ρ).isHermitian.eq, sqrtState,
      CFC.sqrt_mul_sqrt_self ρ hρ.nonneg, hρtr]
    simp
  have hYY : inner ℝ Y Y = sandwichedRenyiTwoTrace ρ ω :=
    frobenius_inner_sandwich_self_eq_sandwichedRenyiTwoTrace hρ hω
  have hcs := real_inner_mul_inner_self_le X Y
  rw [hXX, hYY, one_mul] at hcs
  rw [pow_two, expectation_eq_frobenius_inner ρ ω]
  exact hcs

/-- The logarithmic expectation of the relative-modular half-moment operator is one half of
Umegaki relative entropy. -/
theorem log_expectation_eq_half_quantumRelativeEntropy
    {ρ ω : Mat} (hρ : ρ.PosSemidef) (hω : ω.PosDef) :
    (star (vector ρ) ⬝ᵥ (CFC.log (operator ρ ω) *ᵥ vector ρ)).re =
      (1 / 2 : ℝ) * quantumRelativeEntropy ρ ω := by
  let R := sqrtState ρ
  let T := referenceInvSqrt ω
  have hR : R.PosSemidef := sqrtState_posSemidef ρ
  have hRR : R * R = ρ := by
    exact CFC.sqrt_mul_sqrt_self ρ hρ.nonneg
  have hT : T.PosSemidef := Matrix.nonneg_iff_posSemidef.mp CFC.rpow_nonneg
  have hTpd : T.PosDef := referenceInvSqrt_posDef hω
  have hlogOperator :
      CFC.log (operator ρ ω) =
        Matrix.kronecker (CFC.log (Matrix.transpose R)) hT.supportProj +
          Matrix.kronecker hR.transpose.supportProj (CFC.log T) := by
    rw [operator, Matrix.kronecker]
    exact Matrix.log_kronecker_posSemidef hR.transpose hT
  have hlogT : CFC.log T = (-(1 / 2 : ℝ)) • CFC.log ω := by
    exact Matrix.PosDef.cfc_log_rpow hω (-(1 / 2 : ℝ))
  have hlogR : CFC.log R = (1 / 2 : ℝ) • CFC.log ρ := by
    exact Matrix.PosSemidef.cfc_log_sqrt hρ
  have hlogRt : CFC.log (Matrix.transpose R) = Matrix.transpose (CFC.log R) := by
    rw [CFC.log, CFC.log, ← Matrix.cfc_transpose hR.isHermitian Real.log]
  have htermR :
      (star (vector ρ) ⬝ᵥ
          ((Matrix.kronecker (CFC.log (Matrix.transpose R)) hT.supportProj) *ᵥ
            vector ρ)).re =
        (1 / 2 : ℝ) * (Matrix.trace (ρ * CFC.log ρ)).re := by
    rw [hTpd.supportProj_eq_one, vector, Matrix.kronecker,
      Matrix.kronecker_mulVec_vec]
    simp only [Matrix.one_mul]
    rw [Matrix.star_vec_dotProduct_vec, hlogRt, hlogR]
    simp only [Matrix.transpose_transpose]
    rw [hR.isHermitian.eq, ← Matrix.mul_assoc, hRR, Matrix.mul_smul,
      Matrix.trace_smul]
    simp
  have htermW :
      (star (vector ρ) ⬝ᵥ
          ((Matrix.kronecker hR.transpose.supportProj (CFC.log T)) *ᵥ
            vector ρ)).re =
        (-(1 / 2 : ℝ)) * (Matrix.trace (ρ * CFC.log ω)).re := by
    rw [vector, Matrix.kronecker, Matrix.kronecker_mulVec_vec,
      Matrix.star_vec_dotProduct_vec]
    have hPRt : hR.transpose.supportProj * Matrix.transpose R = Matrix.transpose R :=
      hR.transpose.isHermitian.supportProj_mul_self
    have hRPt : R * hR.transpose.supportProjᵀ = R := by
      have ht := congrArg Matrix.transpose hPRt
      simpa only [Matrix.transpose_mul, Matrix.transpose_transpose] using ht
    rw [Matrix.mul_assoc (CFC.log T) R hR.transpose.supportProjᵀ, hRPt,
      hR.isHermitian.eq]
    calc
      (Matrix.trace (R * (CFC.log T * R))).re =
          (Matrix.trace ((R * CFC.log T) * R)).re := by
        rw [Matrix.mul_assoc]
      _ = (Matrix.trace (R * (R * CFC.log T))).re := by
        rw [Matrix.trace_mul_comm]
      _ = (Matrix.trace (ρ * CFC.log T)).re := by
        rw [← Matrix.mul_assoc, hRR]
      _ = (-(1 / 2 : ℝ)) * (Matrix.trace (ρ * CFC.log ω)).re := by
        rw [hlogT, Matrix.mul_smul, Matrix.trace_smul]
        simp
  rw [hlogOperator, Matrix.add_mulVec, dotProduct_add, Complex.add_re,
    htermR, htermW, quantumRelativeEntropy_eq_trace_mul_log_sub]
  ring

end RelativeModularHalfMoment

open RelativeModularHalfMoment

/-- For a positive-semidefinite trace-one state and a faithful reference,
Umegaki relative entropy is bounded by the logarithm of the order-two
sandwiched trace.

This is the finite-dimensional faithful-reference comparison
\[
  D(\rho\Vert\omega)
    \leq \log\operatorname{Tr}(\rho\,\omega^{-1/2}\rho\,\omega^{-1/2}).
\]
It is the direct order-two endpoint of the auxiliary-divergence argument in
Müller-Lennert et al., arXiv:1306.3142v4, Definition 5 and Lemma 19 (used in
the proof of Theorem 7).
The proof applies the support-aware Jensen inequality to the relative modular
operator \((\sqrt\rho)^T\otimes\omega^{-1/2}\) and then uses
Hilbert--Schmidt Cauchy--Schwarz on \(R\) and \(R\omega^{-1/2}R\). -/
theorem quantumRelativeEntropy_le_log_sandwichedRenyiTwoTrace_posDef
    {ρ ω : Mat} (hρ : ρ.PosSemidef) (hω : ω.PosDef) (hρtr : ρ.trace = 1) :
    quantumRelativeEntropy ρ ω ≤ Real.log (sandwichedRenyiTwoTrace ρ ω) := by
  have hvnorm := vector_unit hρ hρtr
  have hsupport := supportProj_mulVec_vector (ρ := ρ) hω
  have hj := (operator_posSemidef ρ ω).re_dotProduct_cfc_log_mulVec_le_log
    hvnorm hsupport
  have hhalf_le_logm :
      (1 / 2 : ℝ) * quantumRelativeEntropy ρ ω ≤
        Real.log ((star (vector ρ) ⬝ᵥ (operator ρ ω *ᵥ vector ρ)).re) := by
    rw [← log_expectation_eq_half_quantumRelativeEntropy hρ hω]
    exact hj
  have hm_sq_le := expectation_sq_le_sandwichedRenyiTwoTrace hρ hω hρtr
  have hv_ne : vector ρ ≠ 0 := by
    intro hv0
    rw [hv0] at hvnorm
    norm_num at hvnorm
  have hm_pos_complex : (0 : ℂ) <
      star (vector ρ) ⬝ᵥ (operator ρ ω *ᵥ vector ρ) :=
    Matrix.PosSemidef.dotProduct_mulVec_pos_of_supportProj_fixed
      (operator_posSemidef ρ ω) hv_ne hsupport
  have hm_pos : 0 < (star (vector ρ) ⬝ᵥ (operator ρ ω *ᵥ vector ρ)).re :=
    (Complex.lt_def.mp hm_pos_complex).1
  let m := (star (vector ρ) ⬝ᵥ (operator ρ ω *ᵥ vector ρ)).re
  have hlog_sq_le : Real.log (m ^ 2) ≤ Real.log (sandwichedRenyiTwoTrace ρ ω) :=
    Real.log_le_log (sq_pos_of_pos hm_pos) hm_sq_le
  have htwolog_eq : 2 * Real.log m = Real.log (m ^ 2) := by
    rw [pow_two, Real.log_mul hm_pos.ne' hm_pos.ne']
    ring
  have hD_le_twolog : quantumRelativeEntropy ρ ω ≤ 2 * Real.log m := by
    nlinarith
  calc
    quantumRelativeEntropy ρ ω ≤ 2 * Real.log m := hD_le_twolog
    _ = Real.log (m ^ 2) := htwolog_eq
    _ ≤ Real.log (sandwichedRenyiTwoTrace ρ ω) := hlog_sq_le

end TNLean

end
