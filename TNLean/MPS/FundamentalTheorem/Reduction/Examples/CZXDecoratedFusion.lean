/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import TNLean.MPS.FundamentalTheorem.Reduction.Examples.CZXDecoratedTensor

/-!
# The decorated CZX matrix product unitary: fusion tensors and the anomaly `ω = -1`

**Source.** Garre-Rubio, Schuch 2024 (arXiv:2405.00439), Section III.A, eq. `eq:Ured` and
eq. `eq:Uanomal`, `Papers/2405.00439/MPU-DW.tex` lines 412–558: for an MPU `U` of order two,
fusion tensors `(V, V̂)` reduce two stacked layers of the tensor to one (`eq:Ured`), and the two
ways of fusing three layers differ by a sign `ω` (`eq:Uanomal`). Section III.D, lines
1136–1244, computes the fusion tensors of the decorated CZX tensor,
`V = -|−̂⟩ ⊗ |+̂⟩` and `V̂ = ⟨1| ⊗ ⟨0|` with `|±̂⟩ = |0⟩ ± |1⟩`, and states `ω = -1`.

**Formalized here.** With the printed fusion tensors: both equations of `eq:Ured` for every
number of intermediate sites, and `eq:Uanomal` on three sites with `ω = -1`. The layers are
ordered by the matrix product of operators: the first factor of `MPOTensor.mulTensor` is the
upper layer of the source's figures, and a bond of two layers is ordered (upper, lower).
The fusion tensor `V` is contracted with the right bonds of a double-layer site and `V̂` with
the left bonds.

The source reaches `ω = -1` a second way, through the action tensors on the product states
`|0⟩^{⊗ N}` and `|1⟩^{⊗ N}` and the relation `L_0 / L_1 = ω` (lines 1246–1339); that
computation is not formalized here.

## Main definitions

* `CZXCompression.czxDecoratedSquare`: the double-layer tensor, in the pair alphabet.
* `CZXCompression.czxFusionV`, `CZXCompression.czxFusionVHat`: the printed fusion tensors.
* `CZXCompression.czxDecoratedCube`, `CZXCompression.czxAssocLeft`,
  `CZXCompression.czxAssocRight`: the triple-layer tensor and the two partial fusions of
  `eq:Uanomal`.

## Main results

* `CZXCompression.czxFusion_split`: the first equation of `eq:Ured`.
* `CZXCompression.czxFusion_contract`: the second equation of `eq:Ured`.
* `CZXCompression.czxDecorated_associator_eq_neg_one`: `eq:Uanomal` with `ω = -1`.

## References

- [arXiv:2405.00439](https://arxiv.org/abs/2405.00439) -- J. Garre-Rubio, N. Schuch,
  *Domain wall excitations for anomalous matrix product unitary symmetries*
-/

noncomputable section

open scoped BigOperators Matrix Kronecker

namespace CZXCompression

open MPSTensor

/-! ### The double-layer tensor -/

/-- The integer matrices of the double-layer tensor `∑_m T^{s m} ⊗ T^{m t}` in the pair
alphabet, with the letters `(0,0), (0,1), (1,0), (1,1)` in this order. -/
def czxDecoratedSquareInt : Fin 4 → Matrix (Fin 4) (Fin 4) ℤ
  | 0 => !![0, -1, 0, 0; 0, 1, 0, 0; 0, -1, 0, 0; 0, 1, 0, 0]
  | 1 => 0
  | 2 => 0
  | 3 => !![0, 0, -1, 0; 0, 0, -1, 0; 0, 0, 1, 0; 0, 0, 1, 0]

/-- The double-layer tensor of the decorated CZX operator, in the pair-alphabet view.

Source: arXiv:2405.00439, `Papers/2405.00439/MPU-DW.tex` lines 426–477 (the two stacked layers
on the left of `eq:Ured`). -/
def czxDecoratedSquare : MPSTensor 4 4 :=
  (MPOTensor.mulTensor czxDecoratedTensor czxDecoratedTensor).toMPSTensor

theorem czxDecoratedSquare_eq (a : Fin 4) :
    czxDecoratedSquare a = complexOfInt (czxDecoratedSquareInt a) := by
  have h : czxDecoratedSquare a = complexOfInt (mulIntTensor czxDecoratedIntTensor
      czxDecoratedIntTensor (Fin.divNat (m := 2) (n := 2) a) (Fin.modNat (m := 2) (n := 2) a)) :=
    mulTensor_complexOfRing _ czxDecoratedIntTensor czxDecoratedIntTensor _ _
  have hint : ∀ b : Fin 4, mulIntTensor czxDecoratedIntTensor czxDecoratedIntTensor
      (Fin.divNat (m := 2) (n := 2) b) (Fin.modNat (m := 2) (n := 2) b) =
        czxDecoratedSquareInt b := by
    decide
  rw [h, hint]

/-! ### The fusion tensors -/

/-- The integer column of `V = -|−̂⟩ ⊗ |+̂⟩`, bonds ordered (upper, lower). -/
def czxFusionVInt : Matrix (Fin 4) (Fin 1) ℤ := !![-1; -1; 1; 1]

/-- The integer row of `V̂ = ⟨1| ⊗ ⟨0|`, bonds ordered (upper, lower). -/
def czxFusionVHatInt : Matrix (Fin 1) (Fin 4) ℤ := !![0, 0, 1, 0]

/-- The fusion tensor `V = -|−̂⟩ ⊗ |+̂⟩`, contracted with the right bonds of two layers.

Source: arXiv:2405.00439, `Papers/2405.00439/MPU-DW.tex` lines 1234–1244. -/
def czxFusionV : Matrix (Fin 4) (Fin 1) ℂ := complexOfInt czxFusionVInt

/-- The fusion tensor `V̂ = ⟨1| ⊗ ⟨0|`, contracted with the left bonds of two layers.

Source: arXiv:2405.00439, `Papers/2405.00439/MPU-DW.tex` lines 1225–1232. -/
def czxFusionVHat : Matrix (Fin 1) (Fin 4) ℂ := complexOfInt czxFusionVHatInt

/-- The integer weights `δ_{s t}` of the letters `(s, t)` of the pair alphabet. -/
def pairDeltaInt : Fin 4 → ℤ := ![1, 0, 0, 1]

/-- The weight `δ_{s t}` of the letter `(s, t)`: the identity operator on one site. -/
def pairDelta (a : Fin 4) : ℂ := pairDeltaInt a

private theorem czxDecoratedSquareInt_mul (a b : Fin 4) :
    czxDecoratedSquareInt a * czxDecoratedSquareInt b =
      czxDecoratedSquareInt a * czxFusionVInt * czxFusionVHatInt * czxDecoratedSquareInt b := by
  revert a b
  decide

private theorem czxFusionInt_contract_letter (a : Fin 4) :
    czxFusionVHatInt * czxDecoratedSquareInt a * czxFusionVInt = pairDeltaInt a • 1 := by
  revert a
  decide

/-- The case of no site of the second equation of `eq:Ured`: `V̂ V = 1`.

Source: arXiv:2405.00439, `Papers/2405.00439/MPU-DW.tex` lines 426–477 (`m = 0`). -/
theorem czxFusionVHat_mul_czxFusionV : czxFusionVHat * czxFusionV = 1 := by
  rw [czxFusionVHat, czxFusionV, ← complexOfInt_mul, ← complexOfInt_one]
  congr 1
  decide

/-- The case of no intermediate site of the first equation of `eq:Ured`: two neighboring
double-layer sites factor through the fusion tensors, `S^a S^b = S^a V V̂ S^b`.

Source: arXiv:2405.00439, `Papers/2405.00439/MPU-DW.tex` lines 426–477 (`m = 0`). -/
theorem czxDecoratedSquare_mul (a b : Fin 4) :
    czxDecoratedSquare a * czxDecoratedSquare b =
      czxDecoratedSquare a * czxFusionV * czxFusionVHat * czxDecoratedSquare b := by
  rw [czxDecoratedSquare_eq, czxDecoratedSquare_eq, czxFusionV, czxFusionVHat,
    ← complexOfInt_mul, ← complexOfInt_mul, ← complexOfInt_mul, ← complexOfInt_mul,
    czxDecoratedSquareInt_mul]

/-- The case of one site of the second equation of `eq:Ured`: `V̂ S^{(s,t)} V = δ_{s t}`. -/
theorem czxFusion_contract_letter (a : Fin 4) :
    czxFusionVHat * czxDecoratedSquare a * czxFusionV = pairDelta a • 1 := by
  rw [czxDecoratedSquare_eq, czxFusionV, czxFusionVHat, ← complexOfInt_mul, ← complexOfInt_mul,
    czxFusionInt_contract_letter, complexOfInt_zsmul, complexOfInt_one, pairDelta]

/-- **The second equation of `eq:Ured`**: fused by `V̂` on the left and `V` on the right, a
double-layer word is the identity operator, `V̂ S^{(s₁,t₁)} ⋯ S^{(s_m,t_m)} V = ∏_k δ_{s_k t_k}`,
for every `m ≥ 0`.

Source: arXiv:2405.00439, `Papers/2405.00439/MPU-DW.tex` lines 426–477, with the fusion
tensors of lines 1225–1244. -/
theorem czxFusion_contract (w : List (Fin 4)) :
    czxFusionVHat * Kraus.evalWord czxDecoratedSquare w * czxFusionV =
      (w.map pairDelta).prod • 1 := by
  induction w with
  | nil => simp [czxFusionVHat_mul_czxFusionV]
  | cons a w ih =>
    cases w with
    | nil => simpa using czxFusion_contract_letter a
    | cons b w =>
      have key : czxFusionVHat * Kraus.evalWord czxDecoratedSquare (a :: b :: w) * czxFusionV =
          (czxFusionVHat * czxDecoratedSquare a * czxFusionV) *
            (czxFusionVHat * Kraus.evalWord czxDecoratedSquare (b :: w) * czxFusionV) := by
        rw [Kraus.evalWord_cons, Kraus.evalWord_cons, ← Matrix.mul_assoc (czxDecoratedSquare a),
          czxDecoratedSquare_mul]
        simp only [Matrix.mul_assoc]
      rw [key, ih, czxFusion_contract_letter, smul_mul_smul_comm, Matrix.one_mul]
      simp

/-- **The first equation of `eq:Ured`**: a double-layer word of `m + 2` sites factors through
the fusion tensors at its two ends, the `m` intermediate sites acting as the identity,
`S^a S^{(s₁,t₁)} ⋯ S^{(s_m,t_m)} S^b = (∏_k δ_{s_k t_k}) S^a V V̂ S^b`, for every `m ≥ 0`.

Source: arXiv:2405.00439, `Papers/2405.00439/MPU-DW.tex` lines 426–477, with the fusion
tensors of lines 1225–1244. -/
theorem czxFusion_split (a b : Fin 4) (w : List (Fin 4)) :
    Kraus.evalWord czxDecoratedSquare (a :: (w ++ [b])) =
      (w.map pairDelta).prod •
        (czxDecoratedSquare a * czxFusionV * czxFusionVHat * czxDecoratedSquare b) := by
  induction w generalizing a with
  | nil =>
    simp only [List.nil_append, Kraus.evalWord_cons, Kraus.evalWord_nil, Matrix.mul_one,
      List.map_nil, List.prod_nil, one_smul, czxDecoratedSquare_mul]
  | cons c w ih =>
    have hc : czxDecoratedSquare a *
        (czxDecoratedSquare c * czxFusionV * czxFusionVHat * czxDecoratedSquare b) =
          pairDelta c •
            (czxDecoratedSquare a * czxFusionV * czxFusionVHat * czxDecoratedSquare b) := by
      calc
        _ = czxDecoratedSquare a * czxDecoratedSquare c * czxFusionV * czxFusionVHat *
            czxDecoratedSquare b := by simp only [Matrix.mul_assoc]
        _ = czxDecoratedSquare a * czxFusionV *
            (czxFusionVHat * czxDecoratedSquare c * czxFusionV) * czxFusionVHat *
              czxDecoratedSquare b := by
          rw [czxDecoratedSquare_mul]
          simp only [Matrix.mul_assoc]
        _ = _ := by
          rw [czxFusion_contract_letter, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul,
            Matrix.smul_mul]
    rw [List.cons_append, Kraus.evalWord_cons, ih, Matrix.mul_smul, hc, smul_smul,
      List.map_cons, List.prod_cons, mul_comm]

/-! ### The anomaly -/

/-- The triple-layer tensor, the first factor being the upper layer; its bond is ordered
((upper, middle), lower). -/
def czxDecoratedCube : MPOTensor 2 (2 * 2 * 2) :=
  MPOTensor.mulTensor (MPOTensor.mulTensor czxDecoratedTensor czxDecoratedTensor)
    czxDecoratedTensor

/-- The integer matrices of the triple-layer tensor. -/
def czxDecoratedCubeInt (i j : Fin 2) : Matrix (Fin (2 * 2 * 2)) (Fin (2 * 2 * 2)) ℤ :=
  mulIntTensor (mulIntTensor czxDecoratedIntTensor czxDecoratedIntTensor) czxDecoratedIntTensor
    i j

theorem czxDecoratedCube_eq (i j : Fin 2) :
    czxDecoratedCube i j = complexOfInt (czxDecoratedCubeInt i j) := by
  have h2 : MPOTensor.mulTensor czxDecoratedTensor czxDecoratedTensor = fun i j =>
      complexOfInt (mulIntTensor czxDecoratedIntTensor czxDecoratedIntTensor i j) :=
    funext₂ fun i j => mulTensor_complexOfRing _ czxDecoratedIntTensor czxDecoratedIntTensor i j
  rw [czxDecoratedCube, h2]
  exact mulTensor_complexOfRing _ _ czxDecoratedIntTensor i j

/-- The integer matrix of `V̂ ⊗ 1`. -/
def czxAssocLeftInt : Matrix (Fin 2) (Fin (2 * 2 * 2)) ℤ :=
  (czxFusionVHatInt ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℤ)).submatrix (fun β => (0, β))
    finProdFinEquiv.symm

/-- The integer matrix of `1 ⊗ V`. -/
def czxAssocRightInt : Matrix (Fin (2 * 2 * 2)) (Fin 2) ℤ :=
  ((1 : Matrix (Fin 2) (Fin 2) ℤ) ⊗ₖ czxFusionVInt).submatrix
    (finProdFinEquiv.symm ∘ MPOTensor.mulTensorAssocEquiv 2 2 2) (fun α => (α, 0))

/-- The left end of `eq:Uanomal`: `V̂` fuses the left bonds of the upper two layers, the left
bond of the lower layer staying free.

Source: arXiv:2405.00439, `Papers/2405.00439/MPU-DW.tex` lines 481–499. -/
def czxAssocLeft : Matrix (Fin 2) (Fin (2 * 2 * 2)) ℂ :=
  (czxFusionVHat ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)).submatrix (fun β => (0, β))
    finProdFinEquiv.symm

/-- The right end of `eq:Uanomal`: `V` fuses the right bonds of the lower two layers, the right
bond of the upper layer staying free.

Source: arXiv:2405.00439, `Papers/2405.00439/MPU-DW.tex` lines 481–499. -/
def czxAssocRight : Matrix (Fin (2 * 2 * 2)) (Fin 2) ℂ :=
  ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ czxFusionV).submatrix
    (finProdFinEquiv.symm ∘ MPOTensor.mulTensorAssocEquiv 2 2 2) (fun α => (α, 0))

theorem czxAssocLeft_eq : czxAssocLeft = complexOfInt czxAssocLeftInt := by
  ext β x
  simp only [czxAssocLeft, czxAssocLeftInt, czxFusionVHat, Matrix.submatrix_apply,
    Matrix.kroneckerMap_apply, Matrix.one_apply, complexOfInt_apply]
  split_ifs <;> simp

theorem czxAssocRight_eq : czxAssocRight = complexOfInt czxAssocRightInt := by
  ext x α
  simp only [czxAssocRight, czxAssocRightInt, czxFusionV, Matrix.submatrix_apply,
    Matrix.kroneckerMap_apply, Matrix.one_apply, complexOfInt_apply]
  split_ifs <;> simp

private theorem czxDecorated_associator_int : ∀ i₀ j₀ i₁ j₁ i₂ j₂ : Fin 2,
    czxAssocLeftInt * czxDecoratedCubeInt i₀ j₀ * czxDecoratedCubeInt i₁ j₁ *
        czxDecoratedCubeInt i₂ j₂ * czxAssocRightInt =
      -(czxDecoratedIntTensor i₀ j₀ * czxDecoratedIntTensor i₁ j₁ *
        czxDecoratedIntTensor i₂ j₂) := by
  decide

/-- **The anomaly of the decorated CZX operator is `ω = -1`** (`eq:Uanomal` on three sites):
fusing the upper two of three stacked layers by `V̂` at the left end and the lower two by `V` at
the right end gives `-1` times the single layer.

Source: arXiv:2405.00439, `Papers/2405.00439/MPU-DW.tex` lines 481–499 (`eq:Uanomal`) and
lines 1128–1136 ("the CZX symmetry ..., which has an anomaly, i.e., `ω = -1`"), with the fusion
tensors of lines 1225–1244. -/
theorem czxDecorated_associator_eq_neg_one (i₀ j₀ i₁ j₁ i₂ j₂ : Fin 2) :
    czxAssocLeft * czxDecoratedCube i₀ j₀ * czxDecoratedCube i₁ j₁ * czxDecoratedCube i₂ j₂ *
        czxAssocRight =
      (-1 : ℂ) • (czxDecoratedTensor i₀ j₀ * czxDecoratedTensor i₁ j₁ *
        czxDecoratedTensor i₂ j₂) := by
  rw [czxAssocLeft_eq, czxAssocRight_eq, czxDecoratedCube_eq, czxDecoratedCube_eq,
    czxDecoratedCube_eq, neg_one_smul]
  simp only [czxDecoratedTensor, ← complexOfInt_mul, ← complexOfInt_neg]
  rw [czxDecorated_associator_int]

end CZXCompression
