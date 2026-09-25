/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.ScalarThreeCocycleCyclicInvariant
import TNLean.MPS.Examples.AnomalousCondensation.AnomalousCondensationZ2Z2Defect
import TNLean.MPS.MPDO.SimpleScaling
import TNLean.MPS.Symmetry.MPOSymmetry.Associator

/-!
# The anomaly class of the diagonal `ℤ₂` of the anomalous `ℤ₂ × ℤ₂` symmetry

The two-qubit tensors `M_e, M_x, M_y, M_xy` of `AnomalousCondensationZ2Z2` realize the mixed
type-II class `(−1)^{a₁ b₂ c₂}` of `ℤ₂ × ℤ₂` of Garre-Rubio, Lootens, Molnár
(arXiv:2203.12563, `Papers/2203.12563/REsubmission.tex` lines 1845--1888), up to the on-site
dressing of `AnomalousCondensationZ2Z2Instance`.  Their periodic operators multiply as
`U_g U_h = λ(g,h)^L U_{gh}` with the sign `λ(g,h) = (−1)^{g₁ h₂}` (`mpo_symTensor_mul`).  The
two-cocycle `λ` is not symmetric, so on odd rings `U_x U_y = −U_y U_x`, and no rescaling of the
four tensors turns them into an exact representation of `ℤ₂ × ℤ₂` on every nonempty chain.

The diagonal element `xy` generates a subgroup `ℤ₂` on which the family can be made exact:
`U_xy U_xy = (−1)^L U_e`, so the rescaled tensor `i M_xy` squares to the identity on every ring.
This file computes the anomaly three-cochain `ω` of the representation `1 ↦ M_e`,
`g ↦ i M_xy` of `ℤ₂`, in the sense of arXiv:2502.20257 (display preceding `eq:3-cocycle`), and
shows that its class is nontrivial for every choice of fusion tensors.  This agrees with the
value of the mixed cocycle at the diagonal: the gauge-invariant product
`ω(g,1,g) ω(g,g,g)` of `(−1)^{a₁ b₂ c₂}` at `g = (1,1)` is `−1`.

For the fusion tensors that are trivial whenever a factor is the identity and are the
compression witnesses `(xyXyLeft, xyXyRight)` of the block `(xy, xy)` for `(g, g)`, the two
fusion trees of the triple product of `g` agree up to the sign `−1` against every nonempty
word, so `ω(g,g,g) = −1`, while `ω(g,1,g) = 1`.

**Scope restriction (diagonal subgroup):** the statements of this file concern the
restriction of the anomalous `ℤ₂ × ℤ₂` symmetry to its diagonal subgroup `{e, xy}`, rescaled by
the phase `i` on the generator.  The full four-element family is only a projective
representation, so the anomaly three-cochain of the full group is not defined for it, and no
statement about the class of the full `ℤ₂ × ℤ₂` family is made.  Neither source prints the
two-qubit tensors used here.  Documented in
`docs/paper-gaps/glm23_z2z2_diagonal_anomaly_scope.tex`, with the two routes to the full group
(blocking two sites, or a projective anomaly cochain).

## Main definitions

* `Z2Z2Condensation.diagFamily`: the `ℤ₂`-indexed family `1 ↦ M_e`, `g ↦ i M_xy`.
* `Z2Z2Condensation.diagFusionData`: the fusion tensors described above.

## Main results

* `Z2Z2Condensation.diagFamily_isNormalRepresentation`
* `Z2Z2Condensation.diagFusionData_omega_gen_gen_gen`: `ω(g,g,g) = −1`.
* `Z2Z2Condensation.cyclicInvariant_omega_diag`: `ω(g,1,g) ω(g,g,g) = −1` for every choice of
  fusion tensors.
* `Z2Z2Condensation.not_isTrivialGaugeClass_omega_diag`: the anomaly class of the diagonal
  `ℤ₂` is nontrivial for every choice of fusion tensors.

## References
- [arXiv:2203.12563](https://arxiv.org/abs/2203.12563) -- Garre-Rubio, Lootens, Molnár,
  *Classifying phases protected by matrix product operator symmetries using matrix product
  states*
- [arXiv:2502.20257](https://arxiv.org/abs/2502.20257) -- Franco Rubio, Bochniak, Cirac,
  *Symmetry defects and gauging for quantum states with matrix product unitary symmetries*

## Provenance
The tensors `M_g` are representatives constructed in this development of the mixed type-II
class, recorded with their exact checks in
`Notes/OpenProblemsTN/checks/asym_z2z2_typeIII_data.md`, Sections 1--3.
-/

noncomputable section

open scoped Matrix Kronecker
open TNLean.Algebra MPOTensor MPSTensor

namespace Z2Z2Condensation

/-! ### The family -/

/-- The bond dimension attached to a label of the diagonal `ℤ₂`: one for the identity and two
for the generator `xy`. -/
def diagBondDim (a : Fin 2) : ℕ := if a = 0 then 1 else 2

/-- The tensor attached to a label of the diagonal `ℤ₂`: `M_e` for the identity and `i M_xy`
for the generator. -/
def diagLabelTensor : (a : Fin 2) → MPOTensor 4 (diagBondDim a)
  | ⟨0, _⟩ => eTensor
  | ⟨1, _⟩ => Complex.I • xyTensor
  | ⟨n + 2, h⟩ => absurd h (by omega)

/-- **The diagonal `ℤ₂` of the anomalous `ℤ₂ × ℤ₂` symmetry**: the identity is represented by
the bond-one tensor `M_e` and the generator by `i M_xy`, the tensor of the diagonal element
`xy = (1,1)` rescaled by the phase `i`.

This is the restriction of the projective `ℤ₂ × ℤ₂` family `symTensor` to the subgroup
`{e, xy}`, under the scope restriction of the module docstring. -/
def diagFamily : GroupFamily (Multiplicative (Fin 2)) 4 where
  bondDim x := diagBondDim x.toAdd
  bondDim_pos x := by unfold diagBondDim; split <;> norm_num
  tensor x := diagLabelTensor x.toAdd

/-- The generator of the diagonal `ℤ₂`, written multiplicatively. -/
def diagGen : Multiplicative (Fin 2) := Multiplicative.ofAdd 1

/-- The generator of the diagonal `ℤ₂` has order two. -/
theorem diagGen_pow_two : diagGen ^ 2 = 1 := by decide

private theorem forall_z2 {P : Multiplicative (Fin 2) → Prop}
    (h0 : P (Multiplicative.ofAdd 0)) (h1 : P (Multiplicative.ofAdd 1)) : ∀ x, P x := by
  intro x
  fin_cases x
  exacts [h0, h1]

/-! ### The representation -/

private theorem I_pow_mul_I_pow_mul_neg_one_pow (N : ℕ) :
    Complex.I ^ N * Complex.I ^ N * (-1 : ℂ) ^ N = 1 := by
  rw [← mul_pow, ← mul_pow, Complex.I_mul_I]
  norm_num

/-- **The diagonal `ℤ₂` is represented exactly with normal tensors**: both tensors are
normal, and the periodic operators satisfy `U_e U_e = U_e`, `U_e (i U_xy) = (i U_xy) U_e =
i U_xy` and `(i U_xy)(i U_xy) = U_e` on every nonempty chain, the last because
`U_xy U_xy = (−1)^L U_e` (`mpo_xy_mul_xy`). -/
theorem diagFamily_isNormalRepresentation : diagFamily.IsNormalRepresentation where
  isNormal := by
    refine forall_z2 eMPS_isNormal ?_
    change Kraus.IsNormal (Complex.I • xyMPS)
    exact (isNormal_smul_iff Complex.I_ne_zero _).2 xyMPS_isNormal
  operator_mul := by
    refine forall_z2 (forall_z2 ?_ ?_) (forall_z2 ?_ ?_) <;> intro N hN
    · exact mpo_e_mul_e N hN
    · change mpo eTensor N * mpo (Complex.I • xyTensor) N = mpo (Complex.I • xyTensor) N
      rw [mpo_smul, Matrix.mul_smul, mpo_e_mul_xy N hN]
    · change mpo (Complex.I • xyTensor) N * mpo eTensor N = mpo (Complex.I • xyTensor) N
      rw [mpo_smul, Matrix.smul_mul, mpo_xy_mul_e N hN]
    · change mpo (Complex.I • xyTensor) N * mpo (Complex.I • xyTensor) N = mpo eTensor N
      rw [mpo_smul, Matrix.smul_mul, Matrix.mul_smul, mpo_xy_mul_xy N hN, smul_smul, smul_smul,
        I_pow_mul_I_pow_mul_neg_one_pow, one_smul]

/-! ### The fusion tensors -/

/-- The left fusion tensors attached to a pair of labels: the identity when a label is the
identity, and the left compression witness of the block `(xy, xy)` for two generators. -/
def diagLabelV : (a b : Fin 2) →
    Matrix (Fin (diagBondDim (a + b))) (Fin (diagBondDim a * diagBondDim b)) ℂ
  | ⟨0, _⟩, ⟨0, _⟩ => (1 : Matrix (Fin 1) (Fin 1) ℂ)
  | ⟨0, _⟩, ⟨1, _⟩ => (1 : Matrix (Fin 2) (Fin 2) ℂ)
  | ⟨1, _⟩, ⟨0, _⟩ => (1 : Matrix (Fin 2) (Fin 2) ℂ)
  | ⟨1, _⟩, ⟨1, _⟩ => xyXyLeft
  | ⟨n + 2, h⟩, _ => absurd h (by omega)
  | _, ⟨n + 2, h⟩ => absurd h (by omega)

/-- The right fusion tensors attached to a pair of labels: the identity when a label is the
identity, and the right compression witness of the block `(xy, xy)` for two generators. -/
def diagLabelW : (a b : Fin 2) →
    Matrix (Fin (diagBondDim a * diagBondDim b)) (Fin (diagBondDim (a + b))) ℂ
  | ⟨0, _⟩, ⟨0, _⟩ => (1 : Matrix (Fin 1) (Fin 1) ℂ)
  | ⟨0, _⟩, ⟨1, _⟩ => (1 : Matrix (Fin 2) (Fin 2) ℂ)
  | ⟨1, _⟩, ⟨0, _⟩ => (1 : Matrix (Fin 2) (Fin 2) ℂ)
  | ⟨1, _⟩, ⟨1, _⟩ => xyXyRight
  | ⟨n + 2, h⟩, _ => absurd h (by omega)
  | _, ⟨n + 2, h⟩ => absurd h (by omega)

/-- **Fusion tensors of the diagonal `ℤ₂`**: trivial whenever a factor is the identity, and
the compression witnesses of the block `(xy, xy)` for two generators.  The phases `i · i = −1`
of the two generators cancel the weight `−1` carried by the target of that block.

Source: arXiv:2502.20257, equations `eq:fusion_1` and `eq:fusion_2`; the witnesses are those of
`Notes/OpenProblemsTN/checks/asym_z2z2_typeIII_data.md`, Section 5. -/
def diagFusionData : diagFamily.FusionData where
  V x y := diagLabelV x.toAdd y.toAdd
  W x y := diagLabelW x.toAdd y.toAdd
  isReduction := by
    refine forall_z2 (forall_z2 ?_ ?_) (forall_z2 ?_ ?_)
    · change MPSTensor.IsReduction eEStacked (eMPS : MPSTensor 16 (1 * 1)) 1 1
      exact MPSTensor.IsReduction.of_eq (funext eEStacked_eq)
    · change MPSTensor.IsReduction (mulTensor eTensor (Complex.I • xyTensor)).toMPSTensor
        ((Complex.I • xyTensor : MPOTensor 4 (1 * 2))).toMPSTensor 1 1
      refine MPSTensor.IsReduction.of_eq ?_
      rw [mulTensor_smul_right]
      funext a
      exact congrArg (Complex.I • ·) (eXyStacked_eq a)
    · change MPSTensor.IsReduction (mulTensor (Complex.I • xyTensor) eTensor).toMPSTensor
        ((Complex.I • xyTensor : MPOTensor 4 (2 * 1))).toMPSTensor 1 1
      refine MPSTensor.IsReduction.of_eq ?_
      rw [mulTensor_smul_left]
      funext a
      exact congrArg (Complex.I • ·) (xyEStacked_eq a)
    · change MPSTensor.IsReduction
        (mulTensor (Complex.I • xyTensor) (Complex.I • xyTensor)).toMPSTensor eMPS
        xyXyLeft xyXyRight
      have h := xyXy_isReduction.smul (-1)
      rw [mulTensor_smul_smul, Complex.I_mul_I]
      convert h using 2 with a a
      · rfl
      · change eMPS a = (-1 : ℂ) • ((-1 : ℂ) • eMPS a)
        rw [smul_smul]
        norm_num

/-! ### The two fusion trees of three generators -/

/-- The `8 × 8` integer matrix whose only nonzero column is `k`, with entries `v`. -/
def columnInt (k : Fin (2 * 2 * 2)) (v : Fin (2 * 2 * 2) → ℤ) :
    Matrix (Fin (2 * 2 * 2)) (Fin (2 * 2 * 2)) ℤ :=
  Matrix.of fun r c ↦ if c = k then v r else 0

/-- The integer matrices of the unscaled triple product `M_xy M_xy M_xy` over the pair
alphabet, bond ordered ((first, second), third).  Every letter has at most one nonzero
column. -/
def diagCubeInt : Fin 16 → Matrix (Fin (2 * 2 * 2)) (Fin (2 * 2 * 2)) ℤ
  | 3 => columnInt 5 ![1, -1, 1, -1, -1, 1, -1, 1]
  | 6 => columnInt 2 ![1, 1, -1, -1, 1, 1, -1, -1]
  | 9 => columnInt 5 ![1, -1, 1, -1, -1, 1, -1, 1]
  | 12 => columnInt 2 ![1, 1, -1, -1, 1, 1, -1, -1]
  | _ => 0

private theorem diagSquare_int :
    mulIntTensor xyIntTensor xyIntTensor = fun o j ↦ xyXyInt (finProdFinEquiv (o, j)) := by
  funext o j
  revert_decide_kernel o j

private theorem diagCube_int (a : Fin 16) :
    mulIntTensor (mulIntTensor xyIntTensor xyIntTensor) xyIntTensor (@Fin.divNat 4 4 a)
      (@Fin.modNat 4 4 a) =
      diagCubeInt a := by
  rw [diagSquare_int]
  revert_decide_kernel a

/-- The unscaled triple product `M_xy M_xy M_xy` over the pair alphabet. -/
def diagCube : MPSTensor 16 (2 * 2 * 2) := fun a ↦ complexOfInt (diagCubeInt a)

/-- The triple product of the generator tensor `i M_xy` is `i³ = −i` times the unscaled triple
product of `M_xy`. -/
theorem tripleTensor_gen_toMPSTensor :
    (diagFamily.tripleTensor diagGen diagGen diagGen).toMPSTensor =
      fun a ↦ (Complex.I * Complex.I * Complex.I) • diagCube a := by
  change (mulTensor (mulTensor (Complex.I • xyTensor) (Complex.I • xyTensor))
    (Complex.I • xyTensor)).toMPSTensor = _
  rw [mulTensor_smul_smul, mulTensor_smul_smul]
  have h2 : mulTensor xyTensor xyTensor = fun i j ↦
      complexOfInt (mulIntTensor xyIntTensor xyIntTensor i j) :=
    funext₂ fun i j ↦ mulTensor_complexOfRing _ xyIntTensor xyIntTensor i j
  funext a
  change (Complex.I * Complex.I * Complex.I) • mulTensor (mulTensor xyTensor xyTensor) xyTensor
      a.divNat a.modNat = _
  rw [h2, diagCube, ← diagCube_int]
  congr 1
  exact mulTensor_complexOfRing _ _ xyIntTensor _ _

/-- The integer matrix of `xyXyLeft ⊗ 1`, the left boundary of the tree fusing the first two
generators first. -/
def diagLeftTreeInt : Matrix (Fin 2) (Fin (2 * 2 * 2)) ℤ :=
  !![0, 0, 1, 0, 0, 0, 0, 0; 0, 0, 0, 1, 0, 0, 0, 0]

/-- The integer matrix of `1 ⊗ xyXyLeft`, the left boundary of the tree fusing the last two
generators first. -/
def diagRightTreeInt : Matrix (Fin 2) (Fin (2 * 2 * 2)) ℤ :=
  !![0, 1, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 1, 0, 0]

private theorem assocInv_two_two_two :
    mulTensorAssocInvMatrix 2 2 2 = (1 : Matrix (Fin 8) (Fin 8) ℂ) := by
  have he : (mulTensorAssocEquiv 2 2 2).symm = Equiv.refl (Fin 8) := Equiv.ext (by decide)
  rw [mulTensorAssocInvMatrix, he, Equiv.toPEquiv_refl, PEquiv.toMatrix_refl]

private theorem assocInv_two_one_two :
    mulTensorAssocInvMatrix 2 1 2 = (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
  have he : (mulTensorAssocEquiv 2 1 2).symm = Equiv.refl (Fin 4) := Equiv.ext (by decide)
  rw [mulTensorAssocInvMatrix, he, Equiv.toPEquiv_refl, PEquiv.toMatrix_refl]

private theorem castMat_gen_gen_gen :
    diagFamily.castMat (mul_assoc diagGen diagGen diagGen).symm =
      (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  rw [GroupFamily.castMat_apply]
  fin_cases i <;> fin_cases j <;> rfl

private theorem castMat_gen_one_gen :
    diagFamily.castMat (mul_assoc diagGen 1 diagGen).symm = (1 : Matrix (Fin 1) (Fin 1) ℂ) := by
  ext i j
  rw [GroupFamily.castMat_apply]
  fin_cases i; fin_cases j
  rfl

/-- The left fusion tree of `(g,g,g)`, which fuses the first two factors first, is the integer
matrix `diagLeftTreeInt`. -/
theorem diagFusionData_leftV_gen_gen_gen :
    diagFusionData.leftV diagGen diagGen diagGen = complexOfInt diagLeftTreeInt := by
  change (1 : Matrix (Fin 2) (Fin 2) ℂ) *
    kronId (complexOfInt !![(0 : ℤ), 1, 0, 0]) 2 = _
  rw [Matrix.one_mul, kronId_complexOfRing]
  congr 1
  decide

/-- The right fusion tree of `(g,g,g)`, which fuses the last two factors first, is the integer
matrix `diagRightTreeInt`. -/
theorem diagFusionData_rightV_gen_gen_gen :
    diagFusionData.rightV diagGen diagGen diagGen = complexOfInt diagRightTreeInt := by
  rw [GroupFamily.FusionData.rightV, castMat_gen_gen_gen]
  change (1 : Matrix (Fin 2) (Fin 2) ℂ) * ((1 : Matrix (Fin 2) (Fin 2) ℂ) *
      idKron 2 (complexOfInt !![(0 : ℤ), 1, 0, 0]) * mulTensorAssocInvMatrix 2 2 2) = _
  rw [assocInv_two_two_two, Matrix.one_mul, Matrix.one_mul, Matrix.mul_one, idKron_complexOfRing]
  congr 1
  decide

/-- Every letter of the triple product, together with the matching letter of `−M_xy`, is the
pair at the letter `3`, the pair at the letter `6`, or zero. -/
private theorem diagLetter_cases (a : Fin 16) :
    (diagCubeInt a = diagCubeInt 3 ∧ negXYIntMPS a = negXYIntMPS 3) ∨
      (diagCubeInt a = diagCubeInt 6 ∧ negXYIntMPS a = negXYIntMPS 6) ∨
      (diagCubeInt a = 0 ∧ negXYIntMPS a = 0) := by
  revert a
  decide +kernel

private theorem diag_letter_int (a : Fin 16) :
    diagLeftTreeInt * diagCubeInt a = -(diagRightTreeInt * diagCubeInt a) := by
  rcases diagLetter_cases a with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h]
  · decide +kernel
  · decide +kernel
  · rw [Matrix.mul_zero, Matrix.mul_zero, neg_zero]

private theorem diag_left_pair_int (a b : Fin 16) :
    diagLeftTreeInt * diagCubeInt a * diagCubeInt b =
      negXYIntMPS a * diagLeftTreeInt * diagCubeInt b := by
  rcases diagLetter_cases a with ⟨ha, hs⟩ | ⟨ha, hs⟩ | ⟨ha, hs⟩ <;> rw [ha, hs] <;>
    rcases diagLetter_cases b with ⟨hb, -⟩ | ⟨hb, -⟩ | ⟨hb, -⟩ <;> rw [hb] <;>
    decide +kernel

/-- The pair identity for the right tree follows from that for the left tree and the
single-letter comparison. -/
private theorem diag_right_pair_int (a b : Fin 16) :
    diagRightTreeInt * diagCubeInt a * diagCubeInt b =
      negXYIntMPS a * diagRightTreeInt * diagCubeInt b := by
  have ha : diagRightTreeInt * diagCubeInt a = -(diagLeftTreeInt * diagCubeInt a) := by
    rw [diag_letter_int, neg_neg]
  have hb : diagRightTreeInt * diagCubeInt b = -(diagLeftTreeInt * diagCubeInt b) := by
    rw [diag_letter_int, neg_neg]
  rw [ha, Matrix.neg_mul, diag_left_pair_int, Matrix.mul_assoc, Matrix.mul_assoc, hb,
    Matrix.mul_neg]

private theorem diag_pair_int (a b : Fin 16) :
    diagLeftTreeInt * diagCubeInt a * diagCubeInt b =
        negXYIntMPS a * diagLeftTreeInt * diagCubeInt b ∧
      diagRightTreeInt * diagCubeInt a * diagCubeInt b =
        negXYIntMPS a * diagRightTreeInt * diagCubeInt b :=
  ⟨diag_left_pair_int a b, diag_right_pair_int a b⟩

private theorem diag_pair (L : Matrix (Fin 2) (Fin (2 * 2 * 2)) ℤ)
    (hL : ∀ a b : Fin 16, L * diagCubeInt a * diagCubeInt b =
      negXYIntMPS a * L * diagCubeInt b) (a b : Fin 16) :
    complexOfInt L * diagCube a * diagCube b =
      ((-1 : ℂ) • xyMPS) a * complexOfInt L * diagCube b := by
  rw [negXYMPS_eq]
  simp only [diagCube]
  rw [← complexOfInt_mul, ← complexOfInt_mul, ← complexOfInt_mul, ← complexOfInt_mul, hL]

private theorem diag_letter (a : Fin 16) :
    complexOfInt diagLeftTreeInt * diagCube a =
      (-1 : ℂ) • (complexOfInt diagRightTreeInt * diagCube a) := by
  simp only [diagCube]
  rw [← complexOfInt_mul, ← complexOfInt_mul, diag_letter_int, complexOfInt_neg, neg_one_smul]

/-- The two fusion trees of three generators agree up to the sign `−1` against every nonempty
word of the unscaled triple product. -/
theorem diag_leftTree_evalWord (w : List (Fin 16)) (hw : w ≠ []) :
    complexOfInt diagLeftTreeInt * Kraus.evalWord diagCube w =
      (-1 : ℂ) • (complexOfInt diagRightTreeInt * Kraus.evalWord diagCube w) := by
  induction w with
  | nil => exact absurd rfl hw
  | cons a w ih =>
      cases w with
      | nil => simpa using diag_letter a
      | cons b w =>
          have ih' := ih (List.cons_ne_nil _ _)
          rw [Kraus.evalWord_cons] at ih'
          calc
            _ = complexOfInt diagLeftTreeInt * diagCube a * diagCube b *
                Kraus.evalWord diagCube w := by
              simp only [Kraus.evalWord_cons, Matrix.mul_assoc]
            _ = ((-1 : ℂ) • xyMPS) a * (complexOfInt diagLeftTreeInt *
                (diagCube b * Kraus.evalWord diagCube w)) := by
              rw [diag_pair _ fun a b ↦ (diag_pair_int a b).1]
              simp only [Matrix.mul_assoc]
            _ = (-1 : ℂ) • (complexOfInt diagRightTreeInt * diagCube a * diagCube b *
                Kraus.evalWord diagCube w) := by
              rw [ih', diag_pair _ fun a b ↦ (diag_pair_int a b).2, Matrix.mul_smul]
              simp only [Matrix.mul_assoc]
            _ = _ := by simp only [Kraus.evalWord_cons, Matrix.mul_assoc]

/-- The comparison of the two fusion trees survives a rescaling of the triple product. -/
theorem diag_leftTree_evalWord_smul (c : ℂ) (w : List (Fin 16)) (hw : w ≠ []) :
    complexOfInt diagLeftTreeInt * (c • Kraus.evalWord diagCube w) =
      (-1 : ℂ) • (complexOfInt diagRightTreeInt * (c • Kraus.evalWord diagCube w)) := by
  rw [Matrix.mul_smul, Matrix.mul_smul, diag_leftTree_evalWord w hw, smul_comm]

/-- **The associator of three generators is `−1`**: with the fusion tensors of
`diagFusionData`, the tree fusing the first two generators first equals `−1` times the tree
fusing the last two first, against every nonempty word of the triple product.

Source: arXiv:2502.20257, display preceding `eq:3-cocycle`; the value is that of the mixed
type-II cocycle of arXiv:2203.12563, `Papers/2203.12563/REsubmission.tex` line 1848, at the
diagonal element. -/
theorem diagFusionData_isAssociator_gen_gen_gen :
    diagFusionData.IsAssociator diagGen diagGen diagGen (-1) := by
  unfold GroupFamily.FusionData.IsAssociator
  rw [diagFusionData_leftV_gen_gen_gen, diagFusionData_rightV_gen_gen_gen]
  refine ⟨1, fun w hw ↦ ?_⟩
  have hB : Kraus.evalWord (diagFamily.tripleTensor diagGen diagGen diagGen).toMPSTensor w =
      (Complex.I * Complex.I * Complex.I) ^ w.length • Kraus.evalWord diagCube w := by
    rw [tripleTensor_gen_toMPSTensor]
    exact Kraus.evalWord_smul _ _ w
  rw [hB]
  exact diag_leftTree_evalWord_smul _ w (List.ne_nil_of_length_pos hw)

/-- `ω(g,g,g) = −1` for the fusion tensors of `diagFusionData`. -/
theorem diagFusionData_omega_gen_gen_gen :
    diagFusionData.omega diagGen diagGen diagGen = -1 := by
  apply Units.ext
  rw [← GroupFamily.FusionData.eq_omega_of_isAssociator diagFamily_isNormalRepresentation
    diagFusionData_isAssociator_gen_gen_gen]
  simp

/-- `ω(g,1,g) = 1` for the fusion tensors of `diagFusionData`, which are trivial whenever a
factor is the identity: both fusion trees are `xyXyLeft`. -/
theorem diagFusionData_omega_gen_one_gen : diagFusionData.omega diagGen 1 diagGen = 1 := by
  have hL : diagFusionData.leftV diagGen 1 diagGen = xyXyLeft := by
    change xyXyLeft * kronId (1 : Matrix (Fin 2) (Fin 2) ℂ) 2 = xyXyLeft
    rw [kronId_one, Matrix.mul_one]
  have hR : diagFusionData.rightV diagGen 1 diagGen = xyXyLeft := by
    rw [GroupFamily.FusionData.rightV, castMat_gen_one_gen]
    change (1 : Matrix (Fin 1) (Fin 1) ℂ) * (xyXyLeft *
        idKron 2 (1 : Matrix (Fin 2) (Fin 2) ℂ) * mulTensorAssocInvMatrix 2 1 2) = xyXyLeft
    rw [idKron_one, Matrix.mul_one, assocInv_two_one_two, Matrix.mul_one, Matrix.one_mul]
  have h : diagFusionData.IsAssociator diagGen 1 diagGen 1 := by
    unfold GroupFamily.FusionData.IsAssociator
    rw [hR, ← hL]
    exact MPSTensor.IsDressedProportional.refl _ _
  apply Units.ext
  rw [← GroupFamily.FusionData.eq_omega_of_isAssociator diagFamily_isNormalRepresentation h]
  simp

/-! ### The anomaly class -/

/-- The gauge-invariant product `ω(g,1,g) ω(g,g,g)` of the fusion tensors of
`diagFusionData` is `−1`. -/
theorem cyclicInvariant_diagFusionData :
    ScalarThreeCochain.cyclicInvariant diagFusionData.omega diagGen 2 = -1 := by
  simp only [ScalarThreeCochain.cyclicInvariant, Finset.prod_range_succ, Finset.prod_range_zero,
    one_mul, pow_zero, pow_one, diagFusionData_omega_gen_one_gen,
    diagFusionData_omega_gen_gen_gen]

/-- **For every choice of fusion tensors of the diagonal `ℤ₂`**, the gauge-invariant product
`ω(g,1,g) ω(g,g,g)` is `−1`.

Source: arXiv:2502.20257, `eq:omegagauge`. -/
theorem cyclicInvariant_omega_diag (fd : diagFamily.FusionData) :
    ScalarThreeCochain.cyclicInvariant fd.omega diagGen 2 = -1 := by
  rw [(GroupFamily.FusionData.omega_cohomologousTo diagFamily_isNormalRepresentation
    diagFusionData fd).cyclicInvariant_eq diagGen_pow_two, cyclicInvariant_diagFusionData]

/-- **The diagonal `ℤ₂` of the anomalous `ℤ₂ × ℤ₂` symmetry is anomalous**: for every choice
of fusion tensors, the anomaly three-cocycle of the representation `1 ↦ M_e`, `g ↦ i M_xy` is
not cohomologous to the trivial one.  The statement concerns the subgroup `{e, xy}` only,
under the scope restriction of the module docstring.

Source: arXiv:2502.20257, `eq:omegagauge` and the sentence following it; the class is the
restriction to the diagonal of the mixed type-II class of arXiv:2203.12563,
`Papers/2203.12563/REsubmission.tex` lines 1845--1872. -/
theorem not_isTrivialGaugeClass_omega_diag (fd : diagFamily.FusionData) :
    ¬ ScalarThreeCochain.IsTrivialGaugeClass fd.omega := by
  refine ScalarThreeCochain.not_isTrivialGaugeClass_of_cyclicInvariant_ne_one
    diagGen_pow_two ?_
  rw [cyclicInvariant_omega_diag]
  intro h
  have := congrArg Units.val h
  norm_num at this

end Z2Z2Condensation
