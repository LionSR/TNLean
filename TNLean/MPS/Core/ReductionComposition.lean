/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Core.Reduction
import TNLean.MPS.MPDO.OperatorProduct

/-!
# Composition of rectangular reductions

Rectangular reductions (`MPSTensor.IsReduction`) compose in three ways that are
used when fusion tensors of matrix product operators are stacked into fusion
trees.

* Transitivity: a reduction from `C` to `B` followed by one from `B` to `A` is a
  reduction from `C` to `A`.
* Transport along an intertwiner: if the letters of two tensors are intertwined
  by an invertible matrix, a reduction of one transports to the other.  The
  associator of the product of three matrix product operators is the instance
  used here.
* A factor of a product of matrix product operators that does not take part in
  the reduction: a reduction of `X` onto `A` gives a reduction of the product
  `X · P` onto `A · P` by `V ⊗ 1` and `W ⊗ 1`, and of `P · X` onto `P · A` by
  `1 ⊗ V` and `1 ⊗ W`.

These are the fusion-tree manipulations underlying the definition of the anomaly
three-cocycle of a group of matrix product unitaries in arXiv:2502.20257,
equation `eq:3-cocycle` and the display preceding it (`main.tex` lines
1506--1540), where products of fusion tensors with identity strands appear.

## Main definitions

* `MPOTensor.kronId`: the Kronecker product `V ⊗ 1` on the product bond space
  `Fin (m * D)`.
* `MPOTensor.idKron`: the Kronecker product `1 ⊗ V` on `Fin (D * m)`.
* `MPOTensor.mulTensorAssocInvMatrix`: the inverse of the bond associator.

## Main results

* `MPSTensor.IsReduction.trans`
* `MPSTensor.IsReduction.of_intertwine`
* `MPSTensor.IsReduction.mulTensor_assoc_left`,
  `MPSTensor.IsReduction.mulTensor_assoc_right`
* `MPSTensor.IsReduction.mulTensor_kronId`,
  `MPSTensor.IsReduction.mulTensor_idKron`
-/

open scoped Matrix Kronecker

namespace MPSTensor

namespace IsReduction

variable {d D₁ D₂ D₃ : ℕ}

/-- Reductions compose: a reduction from `C` to `B` followed by a reduction
from `B` to `A` is a reduction from `C` to `A`.

Source: the composition of reductions is implicit in the fusion trees of
arXiv:2502.20257, display preceding `eq:3-cocycle`, `main.tex` lines
1506--1535. -/
theorem trans {C : MPSTensor d D₃} {B : MPSTensor d D₂} {A : MPSTensor d D₁}
    {V₁ : Matrix (Fin D₂) (Fin D₃) ℂ} {W₁ : Matrix (Fin D₃) (Fin D₂) ℂ}
    {V₂ : Matrix (Fin D₁) (Fin D₂) ℂ} {W₂ : Matrix (Fin D₂) (Fin D₁) ℂ}
    (h₁ : IsReduction C B V₁ W₁) (h₂ : IsReduction B A V₂ W₂) :
    IsReduction C A (V₂ * V₁) (W₁ * W₂) := by
  rw [iff_forall_evalWord]
  intro w
  rw [← h₂.evalWord w, ← h₁.evalWord w]
  simp only [Matrix.mul_assoc]

/-- An intertwining relation between letters extends to all words. -/
theorem evalWord_mul_of_intertwine {B' : MPSTensor d D₂} {B : MPSTensor d D₃}
    {P : Matrix (Fin D₂) (Fin D₃) ℂ} (hB : ∀ i, B' i * P = P * B i)
    (w : List (Fin d)) :
    Kraus.evalWord B' w * P = P * Kraus.evalWord B w := by
  induction w with
  | nil => simp
  | cons i w ih =>
      rw [Kraus.evalWord_cons, Kraus.evalWord_cons, Matrix.mul_assoc, ih,
        ← Matrix.mul_assoc, hB i, Matrix.mul_assoc]

/-- A reduction transports along an invertible intertwiner of letters: if
`B' i P = P B i` with `P Q = 1` and `Q P = 1`, then a reduction `(V, W)` from
`B` to `A` gives the reduction `(V Q, P W)` from `B'` to `A`.

Source: this is the change of bond basis used when the associator of three
stacked matrix product operators is inserted in a fusion tree,
arXiv:2502.20257, display preceding `eq:3-cocycle`, `main.tex` lines
1506--1535. -/
theorem of_intertwine {B' : MPSTensor d D₂} {B : MPSTensor d D₃}
    {A : MPSTensor d D₁} {V : Matrix (Fin D₁) (Fin D₃) ℂ}
    {W : Matrix (Fin D₃) (Fin D₁) ℂ} {P : Matrix (Fin D₂) (Fin D₃) ℂ}
    {Q : Matrix (Fin D₃) (Fin D₂) ℂ} (hQP : Q * P = 1)
    (hB : ∀ i, B' i * P = P * B i) (h : IsReduction B A V W) :
    IsReduction B' A (V * Q) (P * W) := by
  rw [iff_forall_evalWord]
  intro w
  calc
    V * Q * Kraus.evalWord B' w * (P * W) =
        V * Q * (Kraus.evalWord B' w * P) * W := by simp only [Matrix.mul_assoc]
    _ = V * (Q * P) * Kraus.evalWord B w * W := by
        rw [evalWord_mul_of_intertwine hB]; simp only [Matrix.mul_assoc]
    _ = Kraus.evalWord A w := by rw [hQP, Matrix.mul_one, h.evalWord]

end IsReduction

end MPSTensor

namespace MPOTensor

variable {d D₁ D₂ D₃ : ℕ}

/-! ### Kronecker products with an identity factor -/

/-- The Kronecker product `V ⊗ 1_D` of a rectangular matrix with the identity,
on the product bond spaces encoded by `finProdFinEquiv`, matching the bond
convention of `mulTensor`.

Source: the identity strands beside a fusion tensor in arXiv:2502.20257,
display preceding `eq:3-cocycle`, `main.tex` lines 1506--1535. -/
noncomputable def kronId {m n : ℕ} (V : Matrix (Fin m) (Fin n) ℂ) (D : ℕ) :
    Matrix (Fin (m * D)) (Fin (n * D)) ℂ :=
  (V ⊗ₖ (1 : Matrix (Fin D) (Fin D) ℂ)).submatrix
    finProdFinEquiv.symm finProdFinEquiv.symm

/-- The Kronecker product `1_D ⊗ V` of the identity with a rectangular matrix,
on the product bond spaces encoded by `finProdFinEquiv`, matching the bond
convention of `mulTensor`.

Source: the identity strands beside a fusion tensor in arXiv:2502.20257,
display preceding `eq:3-cocycle`, `main.tex` lines 1506--1535. -/
noncomputable def idKron {m n : ℕ} (D : ℕ) (V : Matrix (Fin m) (Fin n) ℂ) :
    Matrix (Fin (D * m)) (Fin (D * n)) ℂ :=
  ((1 : Matrix (Fin D) (Fin D) ℂ) ⊗ₖ V).submatrix
    finProdFinEquiv.symm finProdFinEquiv.symm

/-- `kronId` is multiplicative. -/
theorem kronId_mul {m n p : ℕ} (V : Matrix (Fin m) (Fin n) ℂ)
    (V' : Matrix (Fin n) (Fin p) ℂ) (D : ℕ) :
    kronId V D * kronId V' D = kronId (V * V') D := by
  rw [kronId, kronId, kronId, Matrix.submatrix_mul_equiv, ← Matrix.mul_kronecker_mul,
    Matrix.mul_one]

/-- `idKron` is multiplicative. -/
theorem idKron_mul {m n p : ℕ} (D : ℕ) (V : Matrix (Fin m) (Fin n) ℂ)
    (V' : Matrix (Fin n) (Fin p) ℂ) :
    idKron D V * idKron D V' = idKron D (V * V') := by
  rw [idKron, idKron, idKron, Matrix.submatrix_mul_equiv, ← Matrix.mul_kronecker_mul,
    Matrix.mul_one]

/-- `kronId` sends the identity to the identity. -/
@[simp] theorem kronId_one (m D : ℕ) :
    kronId (1 : Matrix (Fin m) (Fin m) ℂ) D = 1 := by
  rw [kronId, Matrix.one_kronecker_one, Matrix.submatrix_one_equiv]

/-- `idKron` sends the identity to the identity. -/
@[simp] theorem idKron_one (D m : ℕ) :
    idKron D (1 : Matrix (Fin m) (Fin m) ℂ) = 1 := by
  rw [idKron, Matrix.one_kronecker_one, Matrix.submatrix_one_equiv]

/-- Identity factors on different sides commute:
`(V ⊗ 1)(1 ⊗ U) = (1 ⊗ U)(V ⊗ 1)`. -/
theorem kronId_mul_idKron {m n m' n' : ℕ} (V : Matrix (Fin m) (Fin n) ℂ)
    (U : Matrix (Fin m') (Fin n') ℂ) :
    kronId V m' * idKron n U = idKron m U * kronId V n' := by
  rw [kronId, kronId, idKron, idKron, Matrix.submatrix_mul_equiv,
    Matrix.submatrix_mul_equiv, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
  simp

/-! ### Word evaluation of a product tensor on arbitrary pair words -/

/-- Word evaluation of the doubled-index view of a product tensor on an
arbitrary pair word: the sum over the contracted middle configurations of
Kronecker products of the doubled-index word evaluations of the two factors.

Source: arXiv:1606.00608, lines 986--993 of
`Papers/1606.00608/MPDO-22-12-17-2.tex`. -/
theorem evalWord_toMPSTensor_mulTensor_ofFn (M : MPOTensor d D₁) (N : MPOTensor d D₂)
    {L : ℕ} (u : Fin L → Fin (d * d)) :
    Kraus.evalWord (mulTensor M N).toMPSTensor (List.ofFn u) =
      (∑ ρ : Fin L → Fin d,
        Kraus.evalWord M.toMPSTensor
            (List.ofFn fun k ↦ finProdFinEquiv ((u k).divNat, ρ k)) ⊗ₖ
          Kraus.evalWord N.toMPSTensor
            (List.ofFn fun k ↦ finProdFinEquiv (ρ k, (u k).modNat))).submatrix
        finProdFinEquiv.symm finProdFinEquiv.symm := by
  rw [evalWord_toMPSTensor_ofFn, evalWord_mulTensor]
  simp only [evalWord_toMPSTensor_pairConfig]

/-! ### Reductions and products of matrix product operators -/

/-- **A factor that does not take part in a reduction, on the right.** If
`(V, W)` reduces `X` onto `A`, then `(V ⊗ 1, W ⊗ 1)` reduces the product
`X · P` onto `A · P`.

Source: a fusion tensor with a parallel identity strand, arXiv:2502.20257,
display preceding `eq:3-cocycle`, `main.tex` lines 1506--1535. -/
theorem _root_.MPSTensor.IsReduction.mulTensor_kronId {X : MPOTensor d D₂}
    {A : MPOTensor d D₁} (P : MPOTensor d D₃) {V : Matrix (Fin D₁) (Fin D₂) ℂ}
    {W : Matrix (Fin D₂) (Fin D₁) ℂ}
    (h : MPSTensor.IsReduction X.toMPSTensor A.toMPSTensor V W) :
    MPSTensor.IsReduction (mulTensor X P).toMPSTensor (mulTensor A P).toMPSTensor
      (kronId V D₃) (kronId W D₃) := by
  rw [MPSTensor.IsReduction.iff_forall_evalWord]
  intro w
  obtain ⟨L, u, rfl⟩ : ∃ L, ∃ u : Fin L → Fin (d * d), w = List.ofFn u :=
    ⟨_, _, (List.ofFn_get w).symm⟩
  rw [evalWord_toMPSTensor_mulTensor_ofFn, evalWord_toMPSTensor_mulTensor_ofFn,
    kronId, kronId, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv,
    Matrix.mul_sum, Matrix.sum_mul]
  congr 1
  refine Finset.sum_congr rfl fun ρ _ ↦ ?_
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, h.evalWord,
    Matrix.one_mul, Matrix.mul_one]

/-- **A factor that does not take part in a reduction, on the left.** If
`(V, W)` reduces `X` onto `A`, then `(1 ⊗ V, 1 ⊗ W)` reduces the product
`P · X` onto `P · A`.

Source: a fusion tensor with a parallel identity strand, arXiv:2502.20257,
display preceding `eq:3-cocycle`, `main.tex` lines 1506--1535. -/
theorem _root_.MPSTensor.IsReduction.mulTensor_idKron {X : MPOTensor d D₂}
    {A : MPOTensor d D₁} (P : MPOTensor d D₃) {V : Matrix (Fin D₁) (Fin D₂) ℂ}
    {W : Matrix (Fin D₂) (Fin D₁) ℂ}
    (h : MPSTensor.IsReduction X.toMPSTensor A.toMPSTensor V W) :
    MPSTensor.IsReduction (mulTensor P X).toMPSTensor (mulTensor P A).toMPSTensor
      (idKron D₃ V) (idKron D₃ W) := by
  rw [MPSTensor.IsReduction.iff_forall_evalWord]
  intro w
  obtain ⟨L, u, rfl⟩ : ∃ L, ∃ u : Fin L → Fin (d * d), w = List.ofFn u :=
    ⟨_, _, (List.ofFn_get w).symm⟩
  rw [evalWord_toMPSTensor_mulTensor_ofFn, evalWord_toMPSTensor_mulTensor_ofFn,
    idKron, idKron, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv,
    Matrix.mul_sum, Matrix.sum_mul]
  congr 1
  refine Finset.sum_congr rfl fun ρ _ ↦ ?_
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, h.evalWord,
    Matrix.one_mul, Matrix.mul_one]

/-! ### The bond associator -/

/-- The inverse of `mulTensorAssocMatrix`, with rows indexed by the
right-associated bond space and columns by the left-associated bond space.

Source: arXiv:1606.00608, lines 995--999; arXiv:1511.08090, Section
``Associativity and the pentagon equation'', lines 237--251 of the source. -/
noncomputable def mulTensorAssocInvMatrix (D₁ D₂ D₃ : ℕ) :
    Matrix (Fin (D₁ * (D₂ * D₃))) (Fin (D₁ * D₂ * D₃)) ℂ :=
  (mulTensorAssocEquiv D₁ D₂ D₃).symm.toPEquiv.toMatrix

/-- The bond associator followed by its inverse is the identity. -/
@[simp] theorem mulTensorAssocMatrix_mul_invMatrix (D₁ D₂ D₃ : ℕ) :
    mulTensorAssocMatrix D₁ D₂ D₃ * mulTensorAssocInvMatrix D₁ D₂ D₃ = 1 := by
  rw [mulTensorAssocMatrix, mulTensorAssocInvMatrix, ← PEquiv.toMatrix_trans,
    ← Equiv.toPEquiv_trans, Equiv.self_trans_symm, Equiv.toPEquiv_refl,
    PEquiv.toMatrix_refl]

/-- The inverse bond associator followed by the associator is the identity. -/
@[simp] theorem mulTensorAssocInvMatrix_mul_matrix (D₁ D₂ D₃ : ℕ) :
    mulTensorAssocInvMatrix D₁ D₂ D₃ * mulTensorAssocMatrix D₁ D₂ D₃ = 1 := by
  rw [mulTensorAssocMatrix, mulTensorAssocInvMatrix, ← PEquiv.toMatrix_trans,
    ← Equiv.toPEquiv_trans, Equiv.symm_trans_self, Equiv.toPEquiv_refl,
    PEquiv.toMatrix_refl]

/-- The inverse associator intertwines the letters of the two
parenthesizations of a triple product in the opposite direction. -/
theorem assocInvMatrix_mul_mulTensor (M : MPOTensor d D₁) (N : MPOTensor d D₂)
    (P : MPOTensor d D₃) (i l : Fin d) :
    mulTensorAssocInvMatrix D₁ D₂ D₃ * mulTensor (mulTensor M N) P i l =
      mulTensor M (mulTensor N P) i l * mulTensorAssocInvMatrix D₁ D₂ D₃ := by
  have h := congrArg (fun X ↦ mulTensorAssocInvMatrix D₁ D₂ D₃ * X *
    mulTensorAssocInvMatrix D₁ D₂ D₃) (mulTensor_mul_assocMatrix M N P i l)
  simp only [← Matrix.mul_assoc, mulTensorAssocInvMatrix_mul_matrix, Matrix.one_mul] at h
  simpa only [Matrix.mul_assoc, mulTensorAssocMatrix_mul_invMatrix, Matrix.mul_one] using h

/-- **Associativity transport, right to left.** A reduction `(V, W)` of the
right-associated product `M · (N · P)` gives the reduction
`(V a⁻¹, a W)` of the left-associated product `(M · N) · P`, where `a` is the
bond associator.

Source: arXiv:2502.20257, display preceding `eq:3-cocycle`, `main.tex` lines
1506--1535; the associator is that of arXiv:1606.00608, lines 995--999. -/
theorem _root_.MPSTensor.IsReduction.mulTensor_assoc_left {M : MPOTensor d D₁}
    {N : MPOTensor d D₂} {P : MPOTensor d D₃} {D : ℕ} {A : MPSTensor (d * d) D}
    {V : Matrix (Fin D) (Fin (D₁ * (D₂ * D₃))) ℂ}
    {W : Matrix (Fin (D₁ * (D₂ * D₃))) (Fin D) ℂ}
    (h : MPSTensor.IsReduction (mulTensor M (mulTensor N P)).toMPSTensor A V W) :
    MPSTensor.IsReduction (mulTensor (mulTensor M N) P).toMPSTensor A
      (V * mulTensorAssocInvMatrix D₁ D₂ D₃) (mulTensorAssocMatrix D₁ D₂ D₃ * W) :=
  h.of_intertwine (mulTensorAssocInvMatrix_mul_matrix D₁ D₂ D₃)
    (fun i ↦ mulTensor_mul_assocMatrix M N P i.divNat i.modNat)

/-- **Associativity transport, left to right.** A reduction `(V, W)` of the
left-associated product `(M · N) · P` gives the reduction `(V a, a⁻¹ W)` of the
right-associated product `M · (N · P)`, where `a` is the bond associator.

Source: arXiv:2502.20257, display preceding `eq:3-cocycle`, `main.tex` lines
1506--1535; the associator is that of arXiv:1606.00608, lines 995--999. -/
theorem _root_.MPSTensor.IsReduction.mulTensor_assoc_right {M : MPOTensor d D₁}
    {N : MPOTensor d D₂} {P : MPOTensor d D₃} {D : ℕ} {A : MPSTensor (d * d) D}
    {V : Matrix (Fin D) (Fin (D₁ * D₂ * D₃)) ℂ}
    {W : Matrix (Fin (D₁ * D₂ * D₃)) (Fin D) ℂ}
    (h : MPSTensor.IsReduction (mulTensor (mulTensor M N) P).toMPSTensor A V W) :
    MPSTensor.IsReduction (mulTensor M (mulTensor N P)).toMPSTensor A
      (V * mulTensorAssocMatrix D₁ D₂ D₃) (mulTensorAssocInvMatrix D₁ D₂ D₃ * W) :=
  h.of_intertwine (mulTensorAssocMatrix_mul_invMatrix D₁ D₂ D₃)
    (fun i ↦ (assocInvMatrix_mul_mulTensor M N P i.divNat i.modNat).symm)

end MPOTensor
