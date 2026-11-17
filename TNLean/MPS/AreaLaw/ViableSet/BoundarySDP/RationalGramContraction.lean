/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ViableSet.BoundarySDP.RationalContraction
import TNLean.MPS.Chain.WeightedOverlap
import TNLean.Algebra.FinSumPermutation
import Mathlib.LinearAlgebra.Matrix.Reindex

/-!
# Rational contraction of weighted overlaps

The virtual index of a mixed transfer matrix pairs one index from each
open chain. Contracting these matrices sequentially gives a weighted
matrix element, with an arbitrary one-site physical operator at every
site. Identity physical weights give the Gram inner product. The scalar
caps and the zero-length case are included.
-/

open Matrix
open scoped BigOperators Kronecker InnerProductSpace Matrix

namespace TNLean.MPS.AreaLaw

namespace RationalRectMatrixCode

/-- A weighted mixed transfer matrix on paired virtual coordinates, with one
finite physical-pair sum for each entry. -/
def weightedTransfer {q Da Db : ℕ}
    (A : Fin q → RationalRectMatrixCode (Fin Da) (Fin Da))
    (B : Fin q → RationalRectMatrixCode (Fin Db) (Fin Db))
    (W : RationalRectMatrixCode (Fin q) (Fin q)) :
    RationalRectMatrixCode (Fin (Da * Db)) (Fin (Da * Db)) := fun a c ↦
  let a' := (finProdFinEquiv : Fin Da × Fin Db ≃ Fin (Da * Db)).symm a
  let c' := (finProdFinEquiv : Fin Da × Fin Db ≃ Fin (Da * Db)).symm c
  ∑ i : Fin (q * q),
    let s := (finProdFinEquiv : Fin q × Fin q ≃ Fin (q * q)).symm i
    RationalComplexCode.mul
      (RationalComplexCode.mul (RationalComplexCode.conj (A s.1 a'.1 c'.1)) (W s.1 s.2))
      (B s.2 a'.2 c'.2)

/-- Decoding the rational mixed transfer gives the weighted complex transfer
matrix, with the paired virtual labels transported to a single finite index. -/
theorem decode_weightedTransfer {q Da Db : ℕ}
    (A : Fin q → RationalRectMatrixCode (Fin Da) (Fin Da))
    (B : Fin q → RationalRectMatrixCode (Fin Db) (Fin Db))
    (W : RationalRectMatrixCode (Fin q) (Fin q)) :
    decode (weightedTransfer A B W) =
      Matrix.reindexRingEquiv ℂ finProdFinEquiv
        (MPSChainTensor.weightedTransferMatrix (fun s ↦ decode (A s))
          (fun t ↦ decode (B t)) (decode W)) := by
  ext a c
  simp only [decode, weightedTransfer, decodeRationalComplex_fintype_sum,
    RationalComplexCode.decode_mul, RationalComplexCode.decode_conj,
    Matrix.coe_reindexRingEquiv, Matrix.reindex_apply, Matrix.submatrix_apply,
    MPSChainTensor.weightedTransferMatrix, Matrix.sum_apply,
    Matrix.smul_apply, smul_eq_mul, Matrix.kroneckerMap_apply,
    Matrix.map_apply, starRingEnd_apply]
  calc
    _ = ∑ s : Fin q × Fin q,
        star (decodeRationalComplex
          (A s.1 (finProdFinEquiv.symm a).1 (finProdFinEquiv.symm c).1)) *
          decodeRationalComplex (W s.1 s.2) *
          decodeRationalComplex
            (B s.2 (finProdFinEquiv.symm a).2 (finProdFinEquiv.symm c).2) :=
      (finProdFinEquiv : Fin q × Fin q ≃ Fin (q * q)).symm.sum_comp _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro s _
      ring

/-- Rational coordinates of the identity physical operator. -/
def identity (q : ℕ) : RationalRectMatrixCode (Fin q) (Fin q) :=
  fun s t ↦ if s = t then (1, 0) else 0

@[simp] theorem decode_identity (q : ℕ) : decode (identity q) = 1 := by
  ext s t
  by_cases h : s = t <;> simp [decode, identity, Matrix.one_apply, h]

end RationalRectMatrixCode

namespace OBCChainTensor

/-- The successive mixed transfer matrices obtained from the actual padded
rational entries of two open chains. -/
def weightedTransferSiteList {q Da Db n : ℕ}
    (A : OBCChainTensor q Da n) (B : OBCChainTensor q Db n)
    (PA : ParameterIndex A → ℚ × ℚ) (PB : ParameterIndex B → ℚ × ℚ)
    (W : Fin n → RationalRectMatrixCode (Fin q) (Fin q)) :
    List (RationalRectMatrixCode (Fin (Da * Db)) (Fin (Da * Db))) :=
  List.ofFn fun p ↦ RationalRectMatrixCode.weightedTransfer
    (zeroPadRationalParameters A PA p) (zeroPadRationalParameters B PB p) (W p)

/-- Sequential rational evaluation of a product-operator matrix element. The
initial and final virtual coordinate is the pair of the two boundary zeros. -/
def weightedOverlapOfRationalParameters {q Da Db n : ℕ}
    (A : OBCChainTensor q Da n) (B : OBCChainTensor q Db n)
    (capA capB : ℚ × ℚ)
    (PA : ParameterIndex A → ℚ × ℚ) (PB : ParameterIndex B → ℚ × ℚ)
    (W : Fin n → RationalRectMatrixCode (Fin q) (Fin q)) : ℚ × ℚ :=
  let j := finProdFinEquiv
    ((⟨0, A.bondBound_pos⟩ : Fin Da), (⟨0, B.bondBound_pos⟩ : Fin Db))
  RationalComplexCode.mul
    (RationalComplexCode.mul (RationalComplexCode.conj capA) capB)
    (RationalRectMatrixCode.rowProduct (Pi.single j (1, 0))
      (weightedTransferSiteList A B PA PB W) j)

/-- An empty chain contributes just the conjugate first cap times the
second cap, independently of the padded virtual dimensions. -/
@[simp] theorem weightedOverlapOfRationalParameters_zero {q Da Db : ℕ}
    (A : OBCChainTensor q Da 0) (B : OBCChainTensor q Db 0)
    (capA capB : ℚ × ℚ)
    (PA : ParameterIndex A → ℚ × ℚ) (PB : ParameterIndex B → ℚ × ℚ)
    (W : Fin 0 → RationalRectMatrixCode (Fin q) (Fin q)) :
    weightedOverlapOfRationalParameters A B capA capB PA PB W =
      RationalComplexCode.mul (RationalComplexCode.conj capA) capB := by
  simp [weightedOverlapOfRationalParameters, weightedTransferSiteList, RationalComplexCode.mul]

/-- Sequential mixed-transfer contraction decodes to the full weighted
configuration sum, including both scalar caps and empty chains. -/
theorem decode_weightedOverlapOfRationalParameters {q Da Db n : ℕ}
    (A : OBCChainTensor q Da n) (B : OBCChainTensor q Db n)
    (capA capB : ℚ × ℚ)
    (PA : ParameterIndex A → ℚ × ℚ) (PB : ParameterIndex B → ℚ × ℚ)
    (hPA : ∀ e, decodeRationalComplex (PA e) = parameters A e)
    (hPB : ∀ e, decodeRationalComplex (PB e) = parameters B e)
    (W : Fin n → RationalRectMatrixCode (Fin q) (Fin q)) :
    decodeRationalComplex (weightedOverlapOfRationalParameters A B capA capB PA PB W) =
      (star (decodeRationalComplex capA) * decodeRationalComplex capB) *
        ∑ σ : Fin n → Fin q, ∑ τ : Fin n → Fin q,
          (∏ p, RationalRectMatrixCode.decode (W p) (σ p) (τ p)) *
            star (A.coeff σ) * B.coeff τ := by
  let φ := Matrix.reindexRingEquiv ℂ
    (finProdFinEquiv : Fin Da × Fin Db ≃ Fin (Da * Db))
  let E := fun p ↦ MPSChainTensor.weightedTransferMatrix
    (_root_.OBCChainTensor.zeroPad A p) (_root_.OBCChainTensor.zeroPad B p)
      (RationalRectMatrixCode.decode (W p))
  let a : Fin Da := ⟨0, A.bondBound_pos⟩
  let b : Fin Db := ⟨0, B.bondBound_pos⟩
  let j := finProdFinEquiv (a, b)
  have he : (fun i ↦ decodeRationalComplex
      ((Pi.single j (1, 0) : Fin (Da * Db) → ℚ × ℚ) i)) =
      Pi.single j (1 : ℂ) := by
    funext i
    by_cases h : i = j <;> simp [h]
  have hsites : (weightedTransferSiteList A B PA PB W).map RationalRectMatrixCode.decode =
      List.ofFn (fun p ↦ φ (E p)) := by
    rw [weightedTransferSiteList, List.map_ofFn]
    congr 1
    funext p
    simp only [Function.comp_apply]
    have hA : (fun s ↦ RationalRectMatrixCode.decode (zeroPadRationalParameters A PA p s)) =
        _root_.OBCChainTensor.zeroPad A p :=
      funext fun s ↦ decode_zeroPadRationalParameters A PA hPA p s
    have hB : (fun t ↦ RationalRectMatrixCode.decode (zeroPadRationalParameters B PB p t)) =
        _root_.OBCChainTensor.zeroPad B p :=
      funext fun t ↦ decode_zeroPadRationalParameters B PB hPB p t
    rw [RationalRectMatrixCode.decode_weightedTransfer, hA, hB]
  have hmap : (List.ofFn fun p ↦ φ (E p)).prod = φ ((List.ofFn E).prod) := by
    simpa only [List.map_ofFn, Function.comp_def] using (map_list_prod φ (List.ofFn E)).symm
  have hrow := congrFun (RationalRectMatrixCode.decode_rowProduct (Pi.single j (1, 0))
    (weightedTransferSiteList A B PA PB W)) j
  rw [he, hsites, hmap, Matrix.single_one_vecMul] at hrow
  simp only [φ, Matrix.coe_reindexRingEquiv, Matrix.reindex_apply,
    Matrix.submatrix_apply, Matrix.row_apply, j, Equiv.symm_apply_apply] at hrow
  have hprod := MPSChainTensor.prod_weightedTransferMatrix_apply
    (_root_.OBCChainTensor.zeroPad A) (_root_.OBCChainTensor.zeroPad B)
    (fun p ↦ RationalRectMatrixCode.decode (W p)) a a b b
  have hprod' : (List.ofFn E).prod (a, b) (a, b) =
      ∑ σ : Fin n → Fin q, ∑ τ : Fin n → Fin q,
        (∏ p, RationalRectMatrixCode.decode (W p) (σ p) (τ p)) *
          star (A.coeff σ) * B.coeff τ := by
    refine hprod.trans ?_
    apply Finset.sum_congr₂
    intro σ _ τ _
    rw [← A.coeff_eq_eval_zeroPad σ, ← B.coeff_eq_eval_zeroPad τ]
  rw [hprod'] at hrow
  rw [weightedOverlapOfRationalParameters, RationalComplexCode.decode_mul,
    RationalComplexCode.decode_mul, RationalComplexCode.decode_conj, hrow]

/-- The configuration expansion is the matrix element of the product of the
decoded one-site operators. -/
theorem decode_weightedOverlapOfRationalParameters_eq_productOperator {q Da Db n : ℕ}
    (A : OBCChainTensor q Da n) (B : OBCChainTensor q Db n)
    (capA capB : ℚ × ℚ)
    (PA : ParameterIndex A → ℚ × ℚ) (PB : ParameterIndex B → ℚ × ℚ)
    (hPA : ∀ e, decodeRationalComplex (PA e) = parameters A e)
    (hPB : ∀ e, decodeRationalComplex (PB e) = parameters B e)
    (W : Fin n → RationalRectMatrixCode (Fin q) (Fin q)) :
    decodeRationalComplex (weightedOverlapOfRationalParameters A B capA capB PA PB W) =
      (star (decodeRationalComplex capA) * decodeRationalComplex capB) *
        (star A.coeff ⬝ᵥ
          (Matrix.rectKronecker (fun p ↦ RationalRectMatrixCode.decode (W p)) *ᵥ B.coeff)) := by
  rw [decode_weightedOverlapOfRationalParameters A B capA capB PA PB hPA hPB W]
  congr 1
  simp only [dotProduct, Matrix.mulVec, Matrix.rectKronecker_apply, Pi.star_apply,
    Finset.mul_sum]
  apply Finset.sum_congr₂
  intro σ _ τ _
  ring

/-- The Gram evaluator is the weighted contraction with the identity at each
physical site. -/
def gramOfRationalParameters {q Da Db n : ℕ}
    (A : OBCChainTensor q Da n) (B : OBCChainTensor q Db n)
    (capA capB : ℚ × ℚ)
    (PA : ParameterIndex A → ℚ × ℚ) (PB : ParameterIndex B → ℚ × ℚ) : ℚ × ℚ :=
  weightedOverlapOfRationalParameters A B capA capB PA PB
    (fun _ ↦ RationalRectMatrixCode.identity q)

/-- Decoding the Gram contraction gives the actual inner product of the two
physical coefficient vectors, with both scalar caps included. -/
theorem decode_gramOfRationalParameters {q Da Db n : ℕ}
    (A : OBCChainTensor q Da n) (B : OBCChainTensor q Db n)
    (capA capB : ℚ × ℚ)
    (PA : ParameterIndex A → ℚ × ℚ) (PB : ParameterIndex B → ℚ × ℚ)
    (hPA : ∀ e, decodeRationalComplex (PA e) = parameters A e)
    (hPB : ∀ e, decodeRationalComplex (PB e) = parameters B e) :
    decodeRationalComplex (gramOfRationalParameters A B capA capB PA PB) =
      ⟪(WithLp.toLp 2 (fun σ ↦ decodeRationalComplex capA * A.coeff σ) :
          EuclideanSpace ℂ (Fin n → Fin q)),
        WithLp.toLp 2 (fun τ ↦ decodeRationalComplex capB * B.coeff τ)⟫_ℂ := by
  rw [gramOfRationalParameters,
    decode_weightedOverlapOfRationalParameters_eq_productOperator A B capA capB PA PB hPA hPB]
  simp only [RationalRectMatrixCode.decode_identity, Matrix.rectKronecker_one,
    Matrix.one_mulVec, EuclideanSpace.inner_eq_star_dotProduct,
    dotProduct, Pi.star_apply, star_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  ring

end OBCChainTensor

/-- The same contraction gives the Gram inner product of represented physical
left-block vectors, after the natural identification with numbered configurations. -/
theorem RationalLeftOpenMPSRepresentation.decode_gramOfRationalParameters
    {L q k ba bb : ℕ} {v w : LeftBlockVector L q k}
    (A : RationalLeftOpenMPSRepresentation ba v) (B : RationalLeftOpenMPSRepresentation bb w)
    (hk : k ≤ L) (capA capB : ℚ × ℚ)
    (PA : OBCChainTensor.ParameterIndex A.tensor → ℚ × ℚ)
    (PB : OBCChainTensor.ParameterIndex B.tensor → ℚ × ℚ)
    (hcapA : decodeRationalComplex capA = A.scalar)
    (hcapB : decodeRationalComplex capB = B.scalar)
    (hPA : ∀ e, decodeRationalComplex (PA e) = OBCChainTensor.parameters A.tensor e)
    (hPB : ∀ e, decodeRationalComplex (PB e) = OBCChainTensor.parameters B.tensor e) :
    decodeRationalComplex
      (OBCChainTensor.gramOfRationalParameters A.tensor B.tensor capA capB PA PB) =
        ⟪v, w⟫_ℂ := by
  rw [OBCChainTensor.decode_gramOfRationalParameters A.tensor B.tensor capA capB PA PB hPA hPB]
  let e := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (leftConfigOfFinEquiv (q := q) hk).symm
  have hA : WithLp.toLp 2 (fun σ ↦ decodeRationalComplex capA * A.tensor.coeff σ) = e v := by
    ext σ
    change decodeRationalComplex capA * A.tensor.coeff σ = v (leftConfigOfFin σ)
    rw [hcapA, A.coeff_eq]
  have hB : WithLp.toLp 2 (fun τ ↦ decodeRationalComplex capB * B.tensor.coeff τ) = e w := by
    ext τ
    change decodeRationalComplex capB * B.tensor.coeff τ = w (leftConfigOfFin τ)
    rw [hcapB, B.coeff_eq]
  rw [hA, hB, e.inner_map_map]

end TNLean.MPS.AreaLaw
