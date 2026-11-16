/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ViableSet.BoundarySDP.RationalTensorApproximation
import TNLean.MPS.Chain.BlockTensor
import TNLean.MPS.Preparation.IsometricChain

/-!
# Sequential contraction of rational open-chain tensors

For one physical configuration, propagate a rational row through the
selected site matrices, from left to right. Each intermediate row is
materialized before the next multiplication. Thus the evaluation uses
row-matrix multiplication rather than expansion over virtual paths.

Padding the varying virtual spaces with zeros permits one fixed row
dimension throughout the contraction. Taking the final zero coordinate
and multiplying by the scalar cap gives the physical coefficient,
including at length zero.
-/

open Matrix
open scoped BigOperators Matrix

namespace TNLean.MPS.AreaLaw

namespace RationalRectMatrixCode

/-- Multiply a rational row by a rectangular rational matrix. -/
def rowMul {m n : Type*} [Fintype m] (v : m → ℚ × ℚ)
    (A : RationalRectMatrixCode m n) : n → ℚ × ℚ :=
  fun j ↦ ∑ i, RationalComplexCode.mul (v i) (A i j)

/-- Decoding a rational row multiplication gives ordinary complex row-matrix
multiplication. -/
theorem decode_rowMul {m n : Type*} [Fintype m] (v : m → ℚ × ℚ)
    (A : RationalRectMatrixCode m n) :
    (fun j ↦ decodeRationalComplex (rowMul v A j)) =
      Matrix.vecMul (fun i ↦ decodeRationalComplex (v i)) (decode A) := by
  funext j
  simp only [rowMul, decodeRationalComplex_fintype_sum, RationalComplexCode.decode_mul,
    Matrix.vecMul, dotProduct, decode]

/-- Successively multiply a row by a list of square site matrices. Each new
row is stored as a finite vector before the next site is processed. -/
def rowProduct {D : ℕ} (v : Fin D → ℚ × ℚ)
    (As : List (RationalRectMatrixCode (Fin D) (Fin D))) : Fin D → ℚ × ℚ :=
  As.foldl (fun row A ↦
    let next := Vector.ofFn (rowMul row A)
    fun j ↦ next[j.val]) v

@[simp] theorem rowProduct_nil {D : ℕ} (v : Fin D → ℚ × ℚ) :
    rowProduct v [] = v := rfl

/-- The first matrix is applied before the remaining suffix. The finite-vector
storage of the intermediate row preserves its entries. -/
@[simp] theorem rowProduct_cons {D : ℕ} (v : Fin D → ℚ × ℚ)
    (A : RationalRectMatrixCode (Fin D) (Fin D))
    (As : List (RationalRectMatrixCode (Fin D) (Fin D))) :
    rowProduct v (A :: As) = rowProduct (rowMul v A) As := by
  simp [rowProduct]

/-- Sequential rational row propagation decodes to the ordered complex matrix
product, without changing its evaluation order. -/
theorem decode_rowProduct {D : ℕ} (v : Fin D → ℚ × ℚ)
    (As : List (RationalRectMatrixCode (Fin D) (Fin D))) :
    (fun j ↦ decodeRationalComplex (rowProduct v As j)) =
      Matrix.vecMul (fun i ↦ decodeRationalComplex (v i)) ((As.map decode).prod) := by
  induction As generalizing v with
  | nil => simp
  | cons A As ih =>
    rw [rowProduct_cons, ih, decode_rowMul, List.map_cons, List.prod_cons,
      Matrix.vecMul_vecMul]

end RationalRectMatrixCode

namespace OBCChainTensor

/-- Rational site entries, padded with zero to the advertised square virtual
space. Only the actual bond dimensions and the explicit rational entries are
used by this computation. -/
def zeroPadRationalParameters {q D n : ℕ} (A : OBCChainTensor q D n)
    (P : ParameterIndex A → ℚ × ℚ) (p : Fin n) (i : Fin q) :
    RationalRectMatrixCode (Fin D) (Fin D) := fun a c ↦
  if ha : a.val < A.bondDim p.castSucc then
    if hc : c.val < A.bondDim p.succ then P ⟨p, i, ⟨a.val, ha⟩, ⟨c.val, hc⟩⟩ else 0
  else 0

/-- Zero-padding commutes with decoding every rational local entry. -/
theorem decode_zeroPadRationalParameters {q D n : ℕ} (A : OBCChainTensor q D n)
    (P : ParameterIndex A → ℚ × ℚ)
    (hP : ∀ e, decodeRationalComplex (P e) = parameters A e)
    (p : Fin n) (i : Fin q) :
    RationalRectMatrixCode.decode (zeroPadRationalParameters A P p i) =
      _root_.OBCChainTensor.zeroPad A p i := by
  ext a c
  simp only [RationalRectMatrixCode.decode, zeroPadRationalParameters,
    _root_.OBCChainTensor.zeroPad, Matrix.zeroPad]
  split_ifs with ha hc
  · exact hP ⟨p, i, ⟨a.val, ha⟩, ⟨c.val, hc⟩⟩
  · exact decodeRationalComplex_zero
  · exact decodeRationalComplex_zero

/-- Rational left-to-right evaluation of one physical coefficient, including
the scalar cap. The initial row is the zero-coordinate basis row. -/
def coefficientOfRationalParameters {q D n : ℕ} (A : OBCChainTensor q D n)
    (cap : ℚ × ℚ) (P : ParameterIndex A → ℚ × ℚ) (σ : Fin n → Fin q) : ℚ × ℚ :=
  RationalComplexCode.mul cap
    ((RationalRectMatrixCode.rowProduct
      (fun a : Fin D ↦ if a.val = 0 then (1, 0) else 0)
      (List.ofFn fun p : Fin n ↦ zeroPadRationalParameters A P p (σ p)))
        ⟨0, A.bondBound_pos⟩)

/-- Decoding the sequential rational evaluation gives the actual open-chain
coefficient times the decoded cap. The boundary entry, rather than the trace
of a square-chain product, also gives the correct value for an empty chain. -/
theorem decode_coefficientOfRationalParameters {q D n : ℕ} (A : OBCChainTensor q D n)
    (cap : ℚ × ℚ) (P : ParameterIndex A → ℚ × ℚ)
    (hP : ∀ e, decodeRationalComplex (P e) = parameters A e)
    (σ : Fin n → Fin q) :
    decodeRationalComplex (coefficientOfRationalParameters A cap P σ) =
      decodeRationalComplex cap * A.coeff σ := by
  let e : Fin D → ℚ × ℚ := fun a ↦ if a.val = 0 then (1, 0) else 0
  have he : (fun a ↦ decodeRationalComplex (e a)) =
      Pi.single (⟨0, A.bondBound_pos⟩ : Fin D) (1 : ℂ) := by
    funext a
    simp only [e, Pi.single_apply]
    by_cases ha : a.val = 0
    · have heq : a = (⟨0, A.bondBound_pos⟩ : Fin D) := Fin.ext ha
      simp [heq]
    · have heq : a ≠ (⟨0, A.bondBound_pos⟩ : Fin D) := by
        intro heq
        exact ha (congrArg Fin.val heq)
      simp [ha, heq]
  have hsites :
      (List.ofFn fun p : Fin n ↦ zeroPadRationalParameters A P p (σ p)).map
          RationalRectMatrixCode.decode =
        List.ofFn (fun p : Fin n ↦ _root_.OBCChainTensor.zeroPad A p (σ p)) := by
    rw [List.map_ofFn]
    congr 1
    funext p
    exact decode_zeroPadRationalParameters A P hP p (σ p)
  have hrow := RationalRectMatrixCode.decode_rowProduct e
    (List.ofFn fun p : Fin n ↦ zeroPadRationalParameters A P p (σ p))
  rw [he, hsites, ← MPSChainTensor.eval_eq_prod_ofFn,
    Matrix.single_one_vecMul] at hrow
  rw [coefficientOfRationalParameters, RationalComplexCode.decode_mul,
    congrFun hrow ⟨0, A.bondBound_pos⟩, A.coeff_eq_eval_zeroPad]
  rfl

end OBCChainTensor

/-- Correctness of sequential rational contraction for a represented physical
left-block vector. The explicit rational coordinates encode the representation's
own scalar and local tensor entries. -/
theorem RationalLeftOpenMPSRepresentation.decode_coefficientOfRationalParameters
    {L q k b : ℕ} {v : LeftBlockVector L q k}
    (R : RationalLeftOpenMPSRepresentation b v) (cap : ℚ × ℚ)
    (P : OBCChainTensor.ParameterIndex R.tensor → ℚ × ℚ)
    (hcap : decodeRationalComplex cap = R.scalar)
    (hP : ∀ e, decodeRationalComplex (P e) = OBCChainTensor.parameters R.tensor e)
    (σ : Fin k → Fin q) :
    decodeRationalComplex (OBCChainTensor.coefficientOfRationalParameters R.tensor cap P σ) =
      v (leftConfigOfFin σ) := by
  rw [OBCChainTensor.decode_coefficientOfRationalParameters R.tensor cap P hP σ,
    hcap, R.coeff_eq]

end TNLean.MPS.AreaLaw
