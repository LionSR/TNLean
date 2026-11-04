/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ViableSet.BoundarySDP.RationalGramContraction
import TNLean.MPS.AreaLaw.ViableSet.BoundarySDP.LocalOperatorExpansion
import TNLean.Algebra.FinSumPermutation

/-!
# Rational matrix elements of two-site operators

Expand an operator supported on two distinct sites in the local matrix-unit
basis. Each of the fourth power of the physical dimension many summands
is evaluated by sequential weighted mixed-transfer contraction. Only the
rational local operator entries and the two rational MPS representations
are used in this calculation.
-/

open Matrix
open scoped BigOperators Kronecker InnerProductSpace Matrix

namespace TNLean.MPS.AreaLaw

namespace RationalRectMatrixCode

/-- Rational coordinates of one physical matrix unit. -/
def matrixUnit {q : ℕ} (a b : Fin q) : RationalRectMatrixCode (Fin q) (Fin q) :=
  fun s t ↦ if s = a ∧ t = b then (1, 0) else 0

@[simp] theorem decode_matrixUnit {q : ℕ} (a b : Fin q) :
    decode (matrixUnit a b) = Matrix.single a b 1 := by
  ext s t
  by_cases hs : s = a
  · subst s
    by_cases ht : t = b
    · subst t
      simp [decode, matrixUnit]
    · simp [decode, matrixUnit, ht, Ne.symm ht]
  · simp [decode, matrixUnit, hs, Ne.symm hs]

end RationalRectMatrixCode

/-- Rational matrix units at the two chosen sites and identities elsewhere. -/
def twoSiteMatrixUnitCodeFactors {q n : ℕ} (p r : Fin n) (a b c d : Fin q) :
    Fin n → RationalRectMatrixCode (Fin q) (Fin q) := fun j ↦
  if j = p then RationalRectMatrixCode.matrixUnit a b else
    if j = r then RationalRectMatrixCode.matrixUnit c d else RationalRectMatrixCode.identity q

/-- Decoding the rational factors gives exactly the product factors in the
two-site operator expansion. -/
theorem decode_twoSiteMatrixUnitCodeFactors {q n : ℕ} (p r : Fin n) (a b c d : Fin q) :
    (fun j ↦ RationalRectMatrixCode.decode (twoSiteMatrixUnitCodeFactors p r a b c d j)) =
      twoSiteMatrixUnitFactors p r a b c d := by
  funext j
  simp only [twoSiteMatrixUnitCodeFactors, twoSiteMatrixUnitFactors]
  split_ifs <;> simp

private theorem sum_flat_twoSiteLabels {q : ℕ} {α : Type*} [AddCommMonoid α]
    (f : Fin q → Fin q → Fin q → Fin q → α) :
    (∑ i : Fin ((q * q) * (q * q)),
      let uv := (finProdFinEquiv : Fin (q * q) × Fin (q * q) ≃ Fin ((q * q) * (q * q))).symm i
      let ab := (finProdFinEquiv : Fin q × Fin q ≃ Fin (q * q)).symm uv.1
      let cd := (finProdFinEquiv : Fin q × Fin q ≃ Fin (q * q)).symm uv.2
      f ab.1 ab.2 cd.1 cd.2) = ∑ a, ∑ b, ∑ c, ∑ d, f a b c d := by
  let e := (finProdFinEquiv : Fin q × Fin q ≃ Fin (q * q))
  calc
    _ = ∑ uv : Fin (q * q) × Fin (q * q),
        f (e.symm uv.1).1 (e.symm uv.1).2 (e.symm uv.2).1 (e.symm uv.2).2 :=
      (finProdFinEquiv : Fin (q * q) × Fin (q * q) ≃ Fin ((q * q) * (q * q))).symm.sum_comp _
    _ = ∑ ab : Fin q × Fin q, ∑ v : Fin (q * q),
        f ab.1 ab.2 (e.symm v).1 (e.symm v).2 := by
      rw [Fintype.sum_prod_type]
      exact e.symm.sum_comp (fun ab ↦ ∑ v, f ab.1 ab.2 (e.symm v).1 (e.symm v).2)
    _ = ∑ ab : Fin q × Fin q, ∑ cd : Fin q × Fin q, f ab.1 ab.2 cd.1 cd.2 := by
      apply Finset.sum_congr rfl
      intro ab _
      exact e.symm.sum_comp (fun cd ↦ f ab.1 ab.2 cd.1 cd.2)
    _ = _ := by simp only [Fintype.sum_prod_type]

namespace OBCChainTensor

/-- Evaluate the matrix-unit expansion of a two-site matrix element. The
single finite sum has exactly the fourth power of the physical dimension
many terms, each using the sequential weighted-overlap evaluator. -/
def twoSiteMatrixElementOfRationalParameters {q Da Db n : ℕ}
    (A : OBCChainTensor q Da n) (B : OBCChainTensor q Db n)
    (capA capB : ℚ × ℚ)
    (PA : ParameterIndex A → ℚ × ℚ) (PB : ParameterIndex B → ℚ × ℚ)
    (p r : Fin n)
    (K : RationalRectMatrixCode (Fin q × Fin q) (Fin q × Fin q)) : ℚ × ℚ :=
  ∑ i : Fin ((q * q) * (q * q)),
    let uv := (finProdFinEquiv : Fin (q * q) × Fin (q * q) ≃ Fin ((q * q) * (q * q))).symm i
    let ab := (finProdFinEquiv : Fin q × Fin q ≃ Fin (q * q)).symm uv.1
    let cd := (finProdFinEquiv : Fin q × Fin q ≃ Fin (q * q)).symm uv.2
    RationalComplexCode.mul (K (ab.1, cd.1) (ab.2, cd.2))
      (weightedOverlapOfRationalParameters A B capA capB PA PB
        (twoSiteMatrixUnitCodeFactors p r ab.1 ab.2 cd.1 cd.2))

/-- Decoding the finite rational sum gives its four physical-index sums. -/
theorem decode_twoSiteMatrixElementOfRationalParameters_eq_sum {q Da Db n : ℕ}
    (A : OBCChainTensor q Da n) (B : OBCChainTensor q Db n)
    (capA capB : ℚ × ℚ)
    (PA : ParameterIndex A → ℚ × ℚ) (PB : ParameterIndex B → ℚ × ℚ)
    (p r : Fin n)
    (K : RationalRectMatrixCode (Fin q × Fin q) (Fin q × Fin q)) :
    decodeRationalComplex (twoSiteMatrixElementOfRationalParameters A B capA capB PA PB p r K) =
      ∑ a : Fin q, ∑ b : Fin q, ∑ c : Fin q, ∑ d : Fin q,
        decodeRationalComplex (K (a, c) (b, d)) *
          decodeRationalComplex (weightedOverlapOfRationalParameters A B capA capB PA PB
            (twoSiteMatrixUnitCodeFactors p r a b c d)) := by
  simp only [twoSiteMatrixElementOfRationalParameters, decodeRationalComplex_fintype_sum,
    RationalComplexCode.decode_mul]
  exact sum_flat_twoSiteLabels (q := q) (α := ℂ) (fun a b c d ↦
    decodeRationalComplex (K (a, c) (b, d)) *
      decodeRationalComplex (weightedOverlapOfRationalParameters A B capA capB PA PB
        (twoSiteMatrixUnitCodeFactors p r a b c d)))

/-- The sequential rational calculation gives the matrix element of the
actual supported operator. The rational local coefficients encode the
operator entries in any fixed reference configuration. -/
theorem decode_twoSiteMatrixElementOfRationalParameters {q Da Db n : ℕ}
    (A : OBCChainTensor q Da n) (B : OBCChainTensor q Db n)
    (capA capB : ℚ × ℚ)
    (PA : ParameterIndex A → ℚ × ℚ) (PB : ParameterIndex B → ℚ × ℚ)
    (hPA : ∀ e, decodeRationalComplex (PA e) = parameters A e)
    (hPB : ∀ e, decodeRationalComplex (PB e) = parameters B e)
    {p r : Fin n} (hpr : p ≠ r) (σ₀ : Fin n → Fin q)
    (X : Matrix (Fin n → Fin q) (Fin n → Fin q) ℂ)
    (hX : Entropy.IsSupportedOn X {p, r})
    (K : RationalRectMatrixCode (Fin q × Fin q) (Fin q × Fin q))
    (hK : ∀ a b c d, decodeRationalComplex (K (a, c) (b, d)) =
      X (twoSiteConfig σ₀ p r a c) (twoSiteConfig σ₀ p r b d)) :
    decodeRationalComplex (twoSiteMatrixElementOfRationalParameters A B capA capB PA PB p r K) =
      (star (decodeRationalComplex capA) * decodeRationalComplex capB) *
        (star A.coeff ⬝ᵥ (X *ᵥ B.coeff)) := by
  rw [decode_twoSiteMatrixElementOfRationalParameters_eq_sum]
  simp_rw [decode_weightedOverlapOfRationalParameters_eq_productOperator A B capA capB PA PB
    hPA hPB, decode_twoSiteMatrixUnitCodeFactors, hK]
  conv_rhs => rw [supported_eq_sum_twoSiteMatrixUnitFactors hpr σ₀ hX]
  simp only [Matrix.sum_mulVec, Matrix.smul_mulVec, dotProduct_sum, dotProduct_smul,
    smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr₂
  intro a _ b _
  apply Finset.sum_congr₂
  intro c _ d _
  ring

/-- Evaluate the matrix element of a finite sum of two-site terms by adding
their sequential rational contractions. -/
def matrixElementOfLocalTerms {q Da Db n m : ℕ}
    (A : OBCChainTensor q Da n) (B : OBCChainTensor q Db n)
    (capA capB : ℚ × ℚ)
    (PA : ParameterIndex A → ℚ × ℚ) (PB : ParameterIndex B → ℚ × ℚ)
    (p r : Fin m → Fin n)
    (K : Fin m → RationalRectMatrixCode (Fin q × Fin q) (Fin q × Fin q)) : ℚ × ℚ :=
  ∑ i, twoSiteMatrixElementOfRationalParameters A B capA capB PA PB (p i) (r i) (K i)

/-- The rational sum gives the matrix element of the full sum of local
operators, with the scalar caps of both MPS representations included. -/
theorem decode_matrixElementOfLocalTerms {q Da Db n m : ℕ}
    (A : OBCChainTensor q Da n) (B : OBCChainTensor q Db n)
    (capA capB : ℚ × ℚ)
    (PA : ParameterIndex A → ℚ × ℚ) (PB : ParameterIndex B → ℚ × ℚ)
    (hPA : ∀ e, decodeRationalComplex (PA e) = parameters A e)
    (hPB : ∀ e, decodeRationalComplex (PB e) = parameters B e)
    (p r : Fin m → Fin n) (hpr : ∀ i, p i ≠ r i)
    (σ₀ : Fin n → Fin q)
    (X : Fin m → Matrix (Fin n → Fin q) (Fin n → Fin q) ℂ)
    (hX : ∀ i, Entropy.IsSupportedOn (X i) {p i, r i})
    (K : Fin m → RationalRectMatrixCode (Fin q × Fin q) (Fin q × Fin q))
    (hK : ∀ i a b c d, decodeRationalComplex (K i (a, c) (b, d)) =
      X i (twoSiteConfig σ₀ (p i) (r i) a c) (twoSiteConfig σ₀ (p i) (r i) b d)) :
    decodeRationalComplex (matrixElementOfLocalTerms A B capA capB PA PB p r K) =
      (star (decodeRationalComplex capA) * decodeRationalComplex capB) *
        (star A.coeff ⬝ᵥ ((∑ i, X i) *ᵥ B.coeff)) := by
  rw [matrixElementOfLocalTerms, decodeRationalComplex_fintype_sum]
  simp only [Matrix.sum_mulVec, dotProduct_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ ↦
    decode_twoSiteMatrixElementOfRationalParameters A B capA capB PA PB hPA hPB
      (hpr i) σ₀ (X i) (hX i) (K i) (hK i)

end OBCChainTensor

end TNLean.MPS.AreaLaw
