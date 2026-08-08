/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.LinearAlgebra.Projectivization.Basic
import TNLean.Algebra.OrthogonalProjection

/-!
# Projective rays as normalized pure-state matrices

This module identifies a ray in a finite-dimensional complex Hilbert space with
its normalized rank-one matrix. This is the pure-state model and transition
probability used in Wolf, Chapter 1, lines 277--285.

The pinned Mathlib provides `Projectivization.Basic`, `Projectivization.Action`,
and semilinear `Projectivization.map`, but it does not yet provide the
`TransitionProbability`, projective unitary, coordinate-conjugation, or Wigner
rigidity modules available in the separately staged `zblore/csd-lean4`
development. Accordingly, this module supplies only the finite-coordinate
ray-to-matrix identification and its two elementary actions; it does not restate or prove
Wigner rigidity.

## Main declarations

* `Projectivization.pureStateMatrix`
* `Projectivization.transitionProbability`
* `Projectivization.transitionProbability_mk`
* `Projectivization.trace_pureStateMatrix_mul_pureStateMatrix`
* `Projectivization.pureStateMatrix_injective`
* `Projectivization.pureStateMatrix_unitaryAction`
* `Projectivization.pureStateMatrix_coordinateConjugation`
-/

open scoped ComplexConjugate LinearAlgebra.Projectivization Matrix
open ComplexConjugate

namespace Projectivization

variable {d : ℕ}

/-- The normalized rank-one matrix
$|v\rangle\langle v|/\langle v,v\rangle$ of a vector. It is defined at
zero by the ambient field's inverse-of-zero convention, while the projective
identification uses it only for nonzero representatives. -/
noncomputable def normalizedPureStateMatrix (v : Fin d → ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  (star v ⬝ᵥ v)⁻¹ • Matrix.vecMulVec v (star v)
private theorem normalizedPureStateMatrix_smul (v : Fin d → ℂ) (c : ℂ) (hc : c ≠ 0) :
    normalizedPureStateMatrix (c • v) = normalizedPureStateMatrix v := by
  classical
  ext i j
  simp only [normalizedPureStateMatrix, Matrix.smul_apply, Pi.star_apply, Pi.smul_apply,
    Matrix.vecMulVec_apply, dotProduct, star_smul, star_mul, smul_eq_mul]
  rw [show (∑ x, star (v x) * star c * (c * v x)) =
      star c * c * ∑ x, star (v x) * v x by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    ring]
  have hsc : star c ≠ 0 := star_ne_zero.mpr hc
  field_simp [hsc]

/-- The normalized pure-state matrix $|v\rangle\langle v|/\langle v,v\rangle$
associated with a projective ray. This is Wolf's pure-state realization in
Chapter 1, lines 277--285. -/
noncomputable def pureStateMatrix (p : ℙ ℂ (Fin d → ℂ)) : Matrix (Fin d) (Fin d) ℂ :=
  p.lift (fun v ↦ normalizedPureStateMatrix v)
    (fun a b c h ↦ by
      have hc : c ≠ 0 := by
        intro hc
        apply a.property
        simp [h, hc]
      simpa [h] using normalizedPureStateMatrix_smul (b : Fin d → ℂ) c hc)

/-- The pure-state matrix of a ray constructed from a nonzero vector. -/
@[simp]
theorem pureStateMatrix_mk (v : Fin d → ℂ) (hv : v ≠ 0) :
    pureStateMatrix (Projectivization.mk ℂ v hv) = normalizedPureStateMatrix v :=
  rfl

private theorem star_dot_self_ne_zero (v : Fin d → ℂ) (hv : v ≠ 0) :
    star v ⬝ᵥ v ≠ 0 := by
  rw [dotProduct_comm]
  let w : EuclideanSpace ℂ (Fin d) := WithLp.toLp 2 v
  have hw : w ≠ 0 := by simpa [w] using hv
  rw [← EuclideanSpace.inner_eq_star_dotProduct w w]
  exact inner_self_ne_zero (𝕜 := ℂ) |>.mpr hw
private theorem normalizedPureStateMatrix_isOrthogonalProjection
    (v : Fin d → ℂ) (hv : v ≠ 0) :
    IsOrthogonalProjection (normalizedPureStateMatrix v) := by
  classical
  have hs := star_dot_self_ne_zero v hv
  constructor
  · rw [Matrix.IsHermitian, normalizedPureStateMatrix, Matrix.conjTranspose_smul,
      Matrix.conjTranspose_vecMulVec]
    simp only [star_star]
    congr 1
    have hself : star (star v ⬝ᵥ v) = star v ⬝ᵥ v := by
      change (starRingEnd ℂ) (∑ i, star (v i) * v i) = ∑ i, star (v i) * v i
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [map_mul]
      simp only [starRingEnd_apply, star_star]
      ring
    change (starRingEnd ℂ) ((star v ⬝ᵥ v)⁻¹) = (star v ⬝ᵥ v)⁻¹
    rw [map_inv₀, starRingEnd_apply, hself]
  · rw [normalizedPureStateMatrix, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.vecMulVec_mul_vecMulVec]
    ext i j
    simp only [Matrix.smul_apply, Matrix.vecMulVec_apply, Pi.smul_apply, Pi.star_apply,
      smul_eq_mul]
    field_simp
private theorem trace_normalizedPureStateMatrix (v : Fin d → ℂ) (hv : v ≠ 0) :
    Matrix.trace (normalizedPureStateMatrix v) = 1 := by
  have hs := star_dot_self_ne_zero v hv
  rw [normalizedPureStateMatrix, Matrix.trace_smul, Matrix.trace_vecMulVec,
    dotProduct_comm v (star v)]
  change (star v ⬝ᵥ v)⁻¹ * (star v ⬝ᵥ v) = 1
  exact inv_mul_cancel₀ hs

private theorem pureStateMatrix_eq_normalizedPureStateMatrix_rep (p : ℙ ℂ (Fin d → ℂ)) :
    pureStateMatrix p = normalizedPureStateMatrix p.rep := by
  conv_lhs => rw [← p.mk_rep]
  rfl

/-- The projective transition probability, written as the normalized squared
overlap of representatives. Its value is real and lies in $[0,1]$; the complex
form used here matches the matrix trace in Wolf, Chapter 1, line 280. -/
noncomputable def transitionProbability (p q : ℙ ℂ (Fin d → ℂ)) : ℂ :=
  ((star p.rep ⬝ᵥ q.rep) * (star q.rep ⬝ᵥ p.rep)) /
    ((star p.rep ⬝ᵥ p.rep) * (star q.rep ⬝ᵥ q.rep))

/-- The trace of the product of two pure-state matrices is their projective
transition probability, as in Wolf's Wigner-theorem hypothesis. -/
theorem trace_pureStateMatrix_mul_pureStateMatrix
    (p q : ℙ ℂ (Fin d → ℂ)) :
    Matrix.trace (pureStateMatrix p * pureStateMatrix q) = transitionProbability p q := by
  classical
  rw [pureStateMatrix_eq_normalizedPureStateMatrix_rep,
    pureStateMatrix_eq_normalizedPureStateMatrix_rep]
  simp only [normalizedPureStateMatrix, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.vecMulVec_mul_vecMulVec, Matrix.trace_smul, Matrix.trace_vecMulVec, dotProduct_smul,
    smul_eq_mul, transitionProbability]
  rw [dotProduct_comm p.rep (star q.rep)]
  field_simp

/-- The transition probability evaluated on arbitrary nonzero representatives.
This is the representative-invariance formula underlying the projective
definition. -/
@[simp]
theorem transitionProbability_mk (v w : Fin d → ℂ) (hv : v ≠ 0) (hw : w ≠ 0) :
    transitionProbability (Projectivization.mk ℂ v hv) (Projectivization.mk ℂ w hw) =
      ((star v ⬝ᵥ w) * (star w ⬝ᵥ v)) /
        ((star v ⬝ᵥ v) * (star w ⬝ᵥ w)) := by
  rw [← trace_pureStateMatrix_mul_pureStateMatrix, pureStateMatrix_mk,
    pureStateMatrix_mk]
  simp only [normalizedPureStateMatrix, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.vecMulVec_mul_vecMulVec, Matrix.trace_smul, Matrix.trace_vecMulVec,
    dotProduct_smul, smul_eq_mul]
  rw [dotProduct_comm v (star w)]
  field_simp

private theorem normalizedPureStateMatrix_mulVec_self (v : Fin d → ℂ) (hv : v ≠ 0) :
    normalizedPureStateMatrix v *ᵥ v = v := by
  classical
  have hs := star_dot_self_ne_zero v hv
  rw [normalizedPureStateMatrix, Matrix.smul_mulVec, Matrix.vecMulVec_mulVec]
  ext i
  simp only [Pi.smul_apply, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op,
    smul_eq_mul]
  field_simp

/-- Distinct projective rays give distinct normalized pure-state matrices. -/
theorem pureStateMatrix_injective :
    Function.Injective
      (pureStateMatrix : ℙ ℂ (Fin d → ℂ) → Matrix (Fin d) (Fin d) ℂ) := by
  intro p q hpq
  rw [← p.mk_rep, ← q.mk_rep, Projectivization.mk_eq_mk_iff']
  let c : ℂ := (star q.rep ⬝ᵥ q.rep)⁻¹ * (star q.rep ⬝ᵥ p.rep)
  refine ⟨c, ?_⟩
  have hmatrix : normalizedPureStateMatrix q.rep = normalizedPureStateMatrix p.rep := by
    simpa only [pureStateMatrix_eq_normalizedPureStateMatrix_rep] using hpq.symm
  have hfix : normalizedPureStateMatrix q.rep *ᵥ p.rep = p.rep := by
    rw [hmatrix]
    exact normalizedPureStateMatrix_mulVec_self p.rep p.rep_nonzero
  ext i
  have hi := congrFun hfix i
  simpa only [normalizedPureStateMatrix, Matrix.smul_mulVec, Matrix.vecMulVec_mulVec,
    Pi.smul_apply, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op,
    smul_eq_mul, c, mul_comm, mul_assoc] using hi


/-- The action of a unitary matrix on projective rays. -/
noncomputable def unitaryAction (U : Matrix.unitaryGroup (Fin d) ℂ)
    (p : ℙ ℂ (Fin d → ℂ)) : ℙ ℂ (Fin d → ℂ) :=
  p.map (Matrix.UnitaryGroup.toLinearEquiv U).toLinearMap
    (Matrix.UnitaryGroup.toLinearEquiv U).injective
private theorem normalizedPureStateMatrix_unitary (U : Matrix.unitaryGroup (Fin d) ℂ)
    (v : Fin d → ℂ) :
    normalizedPureStateMatrix ((U : Matrix (Fin d) (Fin d) ℂ) *ᵥ v) =
      (U : Matrix (Fin d) (Fin d) ℂ) * normalizedPureStateMatrix v *
        (U : Matrix (Fin d) (Fin d) ℂ)ᴴ := by
  classical
  have hU : (U : Matrix (Fin d) (Fin d) ℂ)ᴴ *
      (U : Matrix (Fin d) (Fin d) ℂ) = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using Matrix.UnitaryGroup.star_mul_self U
  have hinner : star ((U : Matrix (Fin d) (Fin d) ℂ) *ᵥ v) ⬝ᵥ
      ((U : Matrix (Fin d) (Fin d) ℂ) *ᵥ v) = star v ⬝ᵥ v := by
    rw [Matrix.star_dotProduct_mulVec (U : Matrix (Fin d) (Fin d) ℂ)
      ((U : Matrix (Fin d) (Fin d) ℂ) *ᵥ v) v, Matrix.mulVec_mulVec,
      hU, Matrix.one_mulVec]
  rw [normalizedPureStateMatrix, normalizedPureStateMatrix, hinner, Matrix.mul_smul,
    Matrix.smul_mul, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, ← Matrix.star_mulVec]

/-- Unitary action on rays becomes conjugation of pure-state matrices,
$P \mapsto U P U^\dagger$, as in Wolf, Chapter 1, line 277. -/
theorem pureStateMatrix_unitaryAction (U : Matrix.unitaryGroup (Fin d) ℂ)
    (p : ℙ ℂ (Fin d → ℂ)) :
    pureStateMatrix (unitaryAction U p) =
      (U : Matrix (Fin d) (Fin d) ℂ) * pureStateMatrix p *
        (U : Matrix (Fin d) (Fin d) ℂ)ᴴ := by
  induction p using Projectivization.ind with
  | h v hv =>
      rw [unitaryAction, Projectivization.map_mk, pureStateMatrix_mk,
        pureStateMatrix_mk]
      exact normalizedPureStateMatrix_unitary U v


/-- Coordinatewise complex conjugation on projective rays. -/
noncomputable def coordinateConjugation (p : ℙ ℂ (Fin d → ℂ)) :
    ℙ ℂ (Fin d → ℂ) :=
  p.map (starLinearEquiv ℂ).toLinearMap (starLinearEquiv ℂ).injective
private theorem normalizedPureStateMatrix_star (v : Fin d → ℂ) :
    normalizedPureStateMatrix (star v) = (normalizedPureStateMatrix v)ᵀ := by
  classical
  rw [normalizedPureStateMatrix, normalizedPureStateMatrix, Matrix.transpose_smul,
    Matrix.transpose_vecMulVec]
  simp only [star_star]
  rw [dotProduct_comm v (star v)]

/-- Coordinate conjugation of a ray becomes transposition of its pure-state
matrix, $P \mapsto P^{\mathsf T}$, as in Wolf, Chapter 1, lines 277 and 283. -/
theorem pureStateMatrix_coordinateConjugation (p : ℙ ℂ (Fin d → ℂ)) :
    pureStateMatrix (coordinateConjugation p) = (pureStateMatrix p)ᵀ := by
  induction p using Projectivization.ind with
  | h v hv =>
      rw [coordinateConjugation, Projectivization.map_mk, pureStateMatrix_mk,
        pureStateMatrix_mk]
      change normalizedPureStateMatrix (star v) = (normalizedPureStateMatrix v)ᵀ
      exact normalizedPureStateMatrix_star v

/-- A normalized pure-state matrix is an orthogonal projection. -/
theorem isOrthogonalProjection_pureStateMatrix (p : ℙ ℂ (Fin d → ℂ)) :
    IsOrthogonalProjection (pureStateMatrix p) := by
  induction p using Projectivization.ind with
  | h v hv => exact normalizedPureStateMatrix_isOrthogonalProjection v hv

/-- A normalized pure-state matrix has trace one. -/
theorem trace_pureStateMatrix (p : ℙ ℂ (Fin d → ℂ)) :
    Matrix.trace (pureStateMatrix p) = 1 := by
  induction p using Projectivization.ind with
  | h v hv => exact trace_normalizedPureStateMatrix v hv

end Projectivization
