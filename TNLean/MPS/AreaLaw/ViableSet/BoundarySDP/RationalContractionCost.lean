/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ViableSet.BoundarySDP.RationalContraction
import Mathlib.Control.Monad.Writer
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Algebra.Group.Nat.Defs

/-!
# Arithmetic counts for sequential rational tensor contraction

The evaluator records one unit for each rational addition, subtraction, or
multiplication that it performs. Complex addition uses two such operations,
and complex multiplication uses six. Each intermediate row is evaluated in
full before the next matrix is applied, so previously computed entries are
shared by all subsequent scalar products.
-/

namespace TNLean.MPS.AreaLaw.RationalContractionCost

/-- Rational computations together with their accumulated arithmetic count. -/
abbrev Arithmetic := WriterT (Multiplicative ℕ) Id

/-- One rational addition with its arithmetic count. -/
def rationalAdd (x y : ℚ) : Arithmetic ℚ := WriterT.mk (x + y, Multiplicative.ofAdd 1)

/-- One rational subtraction with its arithmetic count. -/
def rationalSub (x y : ℚ) : Arithmetic ℚ := WriterT.mk (x - y, Multiplicative.ofAdd 1)

/-- One rational multiplication with its arithmetic count. -/
def rationalMul (x y : ℚ) : Arithmetic ℚ := WriterT.mk (x * y, Multiplicative.ofAdd 1)

/-- Complex addition performed as two counted rational additions. -/
def complexAdd (x y : ℚ × ℚ) : Arithmetic (ℚ × ℚ) := do
  let real ← rationalAdd x.1 y.1
  let imag ← rationalAdd x.2 y.2
  pure (real, imag)

/-- Complex multiplication performed as four counted rational multiplications,
one subtraction, and one addition. -/
def complexMul (x y : ℚ × ℚ) : Arithmetic (ℚ × ℚ) := do
  let ac ← rationalMul x.1 y.1
  let bd ← rationalMul x.2 y.2
  let ad ← rationalMul x.1 y.2
  let bc ← rationalMul x.2 y.1
  let real ← rationalSub ac bd
  let imag ← rationalAdd ad bc
  pure (real, imag)

/-- The counted complex addition has the usual rational value and uses exactly
two rational operations. -/
@[simp] theorem run_complexAdd (x y : ℚ × ℚ) :
    (complexAdd x y).run = (RationalComplexCode.add x y, Multiplicative.ofAdd 2) := rfl

/-- The counted complex multiplication has the usual rational value and uses
exactly six rational operations. -/
@[simp] theorem run_complexMul (x y : ℚ × ℚ) :
    (complexMul x y).run = (RationalComplexCode.mul x y, Multiplicative.ofAdd 6) := rfl

/-- The value and accumulated count of a sequential composition. -/
@[simp] theorem run_bind {α β : Type} (x : Arithmetic α) (f : α → Arithmetic β) :
    (x >>= f).run =
      ((f x.run.1).run.1, x.run.2 * (f x.run.1).run.2) := rfl

/-- Returning an already computed value performs no arithmetic operation. -/
@[simp] theorem run_pure {α : Type} (x : α) :
    (pure x : Arithmetic α).run = (x, Multiplicative.ofAdd 0) := rfl

/-- Evaluate a complex scalar product from left to right, starting with zero. -/
def dot : (D : ℕ) → (Fin D → ℚ × ℚ) → (Fin D → ℚ × ℚ) → Arithmetic (ℚ × ℚ)
  | 0, _, _ => pure (0, 0)
  | D + 1, v, w => do
    let previous ← dot D (fun i ↦ v i.castSucc) (fun i ↦ w i.castSucc)
    let term ← complexMul (v (Fin.last D)) (w (Fin.last D))
    complexAdd previous term

/-- A scalar product over `D` complex coordinates performs exactly `8D`
rational operations and returns the usual rational scalar product. -/
@[simp] theorem run_dot (D : ℕ) (v w : Fin D → ℚ × ℚ) :
    (dot D v w).run =
      (∑ i, RationalComplexCode.mul (v i) (w i), Multiplicative.ofAdd (8 * D)) := by
  induction D with
  | zero => simp [dot, WriterT.run_pure]; rfl
  | succ D ih =>
    simp only [dot, run_bind, ih, run_complexMul, run_complexAdd]
    simp [Fin.sum_univ_castSucc, RationalComplexCode.add, Nat.mul_add]
    rfl

/-- Evaluating every entry of a finite vector adds the counts of its entries.
Here each entry has the same prescribed count. -/
theorem run_vectorOfFnM {α : Type} {D c : ℕ}
    (f : Fin D → Arithmetic α) (v : Fin D → α)
    (h : ∀ i, (f i).run = (v i, Multiplicative.ofAdd c)) :
    (Vector.ofFnM f).run = (Vector.ofFn v, Multiplicative.ofAdd (D * c)) := by
  induction D with
  | zero => simp [Vector.ofFnM_zero]; rfl
  | succ D ih =>
    rw [Vector.ofFnM_succ]
    simp only [run_bind, ih (fun i ↦ f i.castSucc) (fun i ↦ v i.castSucc)
      (fun i ↦ h i.castSucc), h, run_pure]
    rw [Vector.ofFn_succ]
    congr 1
    change D * c + c + 0 = (D + 1) * c
    simp [Nat.add_mul]

/-- Evaluate every entry of a row-matrix product once and store the row before
returning its coordinate function. -/
def rowMul {D : ℕ} (v : Fin D → ℚ × ℚ)
    (A : RationalRectMatrixCode (Fin D) (Fin D)) : Arithmetic (Fin D → ℚ × ℚ) := do
  let row ← Vector.ofFnM fun j ↦ dot D v (fun i ↦ A i j)
  pure fun j ↦ row[j.val]

/-- The stored row has the ordinary rational value and its evaluation performs
exactly `8D²` rational operations. -/
@[simp] theorem run_rowMul {D : ℕ} (v : Fin D → ℚ × ℚ)
    (A : RationalRectMatrixCode (Fin D) (Fin D)) :
    (rowMul v A).run =
      (RationalRectMatrixCode.rowMul v A, Multiplicative.ofAdd (8 * D ^ 2)) := by
  have hvector := run_vectorOfFnM
    (fun j : Fin D ↦ dot D v (fun i ↦ A i j))
    (fun j ↦ ∑ i, RationalComplexCode.mul (v i) (A i j))
    (fun j ↦ run_dot D v (fun i ↦ A i j))
  simp only [rowMul, run_bind, hvector, run_pure, Vector.getElem_ofFn]
  congr 1
  change D * (8 * D) + 0 = 8 * D ^ 2
  simp [pow_two, Nat.mul_assoc, Nat.mul_comm]

/-- Propagate the stored row through a list of site matrices, performing and
counting each row multiplication before evaluating the next site. -/
def rowProduct {D : ℕ} (v : Fin D → ℚ × ℚ)
    (As : List (RationalRectMatrixCode (Fin D) (Fin D))) :
    Arithmetic (Fin D → ℚ × ℚ) :=
  match As with
  | [] => pure v
  | A :: As => do
    let next ← rowMul v A
    rowProduct next As

/-- The counted row propagation agrees with sequential rational contraction and
performs exactly `8nD²` rational operations for a list of length `n`. -/
@[simp] theorem run_rowProduct {D : ℕ} (v : Fin D → ℚ × ℚ)
    (As : List (RationalRectMatrixCode (Fin D) (Fin D))) :
    (rowProduct v As).run =
      (RationalRectMatrixCode.rowProduct v As,
        Multiplicative.ofAdd (8 * As.length * D ^ 2)) := by
  induction As generalizing v with
  | nil => simp [rowProduct]; rfl
  | cons A As ih =>
    simp only [rowProduct, run_bind, run_rowMul, ih,
      RationalRectMatrixCode.rowProduct_cons, List.length_cons]
    congr 1
    change 8 * D ^ 2 + 8 * As.length * D ^ 2 = 8 * (As.length + 1) * D ^ 2
    simp [Nat.mul_add, Nat.add_mul, Nat.add_comm]

/-- Return one contracted coordinate and multiply it by the rational scalar cap. -/
def contract {D : ℕ} (cap : ℚ × ℚ) (v : Fin D → ℚ × ℚ)
    (As : List (RationalRectMatrixCode (Fin D) (Fin D))) (j : Fin D) :
    Arithmetic (ℚ × ℚ) := do
  let row ← rowProduct v As
  complexMul cap (row j)

/-- The final scalar multiplication adds exactly six rational operations to
the sequential contraction count. -/
@[simp] theorem run_contract {D : ℕ} (cap : ℚ × ℚ) (v : Fin D → ℚ × ℚ)
    (As : List (RationalRectMatrixCode (Fin D) (Fin D))) (j : Fin D) :
    (contract cap v As j).run =
      (RationalComplexCode.mul cap (RationalRectMatrixCode.rowProduct v As j),
        Multiplicative.ofAdd (8 * As.length * D ^ 2 + 6)) := by
  simp only [contract, run_bind, run_rowProduct, run_complexMul]
  rfl

/-- Evaluate one physical coefficient of rational open-chain tensor data while
counting the rational operations in its sequential contraction. -/
def coefficientOfRationalParameters {q D n : ℕ} (A : OBCChainTensor q D n)
    (cap : ℚ × ℚ) (P : OBCChainTensor.ParameterIndex A → ℚ × ℚ)
    (σ : Fin n → Fin q) : Arithmetic (ℚ × ℚ) :=
  contract cap (fun a : Fin D ↦ if a.val = 0 then (1, 0) else 0)
    (List.ofFn fun p : Fin n ↦ OBCChainTensor.zeroPadRationalParameters A P p (σ p))
    ⟨0, A.bondBound_pos⟩

/-- The counted coefficient evaluator returns the actual sequential rational
coefficient and performs exactly `8nD²+6` rational arithmetic operations.
Only rational additions, subtractions, and multiplications are counted. -/
@[simp] theorem run_coefficientOfRationalParameters {q D n : ℕ}
    (A : OBCChainTensor q D n) (cap : ℚ × ℚ)
    (P : OBCChainTensor.ParameterIndex A → ℚ × ℚ) (σ : Fin n → Fin q) :
    (coefficientOfRationalParameters A cap P σ).run =
      (OBCChainTensor.coefficientOfRationalParameters A cap P σ,
        Multiplicative.ofAdd (8 * n * D ^ 2 + 6)) := by
  simpa only [coefficientOfRationalParameters, OBCChainTensor.coefficientOfRationalParameters,
    List.length_ofFn] using run_contract cap
    (fun a : Fin D ↦ if a.val = 0 then (1, 0) else 0)
    (List.ofFn fun p : Fin n ↦ OBCChainTensor.zeroPadRationalParameters A P p (σ p))
    ⟨0, A.bondBound_pos⟩

end TNLean.MPS.AreaLaw.RationalContractionCost
