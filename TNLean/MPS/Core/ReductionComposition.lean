/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Core.Reduction
import TNLean.MPS.Core.ReductionUniqueness
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

The second half of the file treats the scalar comparison of two reductions.
`MPSTensor.IsDressedProportional B X Y z` says that `X B^w = z Y B^w` for all
sufficiently long words `w`; two reductions onto the same normal tensor are
related in this way by a unique nonzero scalar
(`MPSTensor.IsReduction.exists_isDressedProportional`,
`MPSTensor.IsDressedProportional.eq_of_forall_exists_ne_zero`), and the relation
is compatible with the three compositions above.
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

/-- A reduction transports along an intertwiner of letters with a left inverse:
if `B' i P = P B i` and `Q P = 1`, then a reduction `(V, W)` from `B` to `A`
gives the reduction `(V Q, P W)` from `B'` to `A`.

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
        rw [Kraus.evalWord_intertwine _ _ _ hB]; simp only [Matrix.mul_assoc]
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

end MPOTensor

namespace MPSTensor.IsReduction

open MPOTensor

variable {d D₁ D₂ D₃ : ℕ}

/-- **A factor that does not take part in a reduction, on the right.** If
`(V, W)` reduces `X` onto `A`, then `(V ⊗ 1, W ⊗ 1)` reduces the product
`X · P` onto `A · P`.

Source: a fusion tensor with a parallel identity strand, arXiv:2502.20257,
display preceding `eq:3-cocycle`, `main.tex` lines 1506--1535. -/
theorem mulTensor_kronId {X : MPOTensor d D₂}
    {A : MPOTensor d D₁} (P : MPOTensor d D₃) {V : Matrix (Fin D₁) (Fin D₂) ℂ}
    {W : Matrix (Fin D₂) (Fin D₁) ℂ}
    (h : MPSTensor.IsReduction X.toMPSTensor A.toMPSTensor V W) :
    MPSTensor.IsReduction (mulTensor X P).toMPSTensor (mulTensor A P).toMPSTensor
      (kronId V D₃) (kronId W D₃) := by
  rw [MPSTensor.IsReduction.iff_forall_evalWord]
  intro w
  obtain ⟨L, u, rfl⟩ := List.exists_eq_ofFn w
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
theorem mulTensor_idKron {X : MPOTensor d D₂}
    {A : MPOTensor d D₁} (P : MPOTensor d D₃) {V : Matrix (Fin D₁) (Fin D₂) ℂ}
    {W : Matrix (Fin D₂) (Fin D₁) ℂ}
    (h : MPSTensor.IsReduction X.toMPSTensor A.toMPSTensor V W) :
    MPSTensor.IsReduction (mulTensor P X).toMPSTensor (mulTensor P A).toMPSTensor
      (idKron D₃ V) (idKron D₃ W) := by
  rw [MPSTensor.IsReduction.iff_forall_evalWord]
  intro w
  obtain ⟨L, u, rfl⟩ := List.exists_eq_ofFn w
  rw [evalWord_toMPSTensor_mulTensor_ofFn, evalWord_toMPSTensor_mulTensor_ofFn,
    idKron, idKron, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv,
    Matrix.mul_sum, Matrix.sum_mul]
  congr 1
  refine Finset.sum_congr rfl fun ρ _ ↦ ?_
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, h.evalWord,
    Matrix.one_mul, Matrix.mul_one]

end MPSTensor.IsReduction

namespace MPOTensor

variable {d D₁ D₂ D₃ : ℕ}

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

end MPOTensor

namespace MPSTensor.IsReduction

open MPOTensor

variable {d D₁ D₂ D₃ : ℕ}

/-- **Associativity transport, right to left.** A reduction `(V, W)` of the
right-associated product `M · (N · P)` gives the reduction
`(V a⁻¹, a W)` of the left-associated product `(M · N) · P`, where `a` is the
bond associator.

Source: arXiv:2502.20257, display preceding `eq:3-cocycle`, `main.tex` lines
1506--1535; the associator is that of arXiv:1606.00608, lines 995--999. -/
theorem mulTensor_assoc_left {M : MPOTensor d D₁}
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
theorem mulTensor_assoc_right {M : MPOTensor d D₁}
    {N : MPOTensor d D₂} {P : MPOTensor d D₃} {D : ℕ} {A : MPSTensor (d * d) D}
    {V : Matrix (Fin D) (Fin (D₁ * D₂ * D₃)) ℂ}
    {W : Matrix (Fin (D₁ * D₂ * D₃)) (Fin D) ℂ}
    (h : MPSTensor.IsReduction (mulTensor (mulTensor M N) P).toMPSTensor A V W) :
    MPSTensor.IsReduction (mulTensor M (mulTensor N P)).toMPSTensor A
      (V * mulTensorAssocMatrix D₁ D₂ D₃) (mulTensorAssocInvMatrix D₁ D₂ D₃ * W) :=
  h.of_intertwine (mulTensorAssocMatrix_mul_invMatrix D₁ D₂ D₃)
    (fun i ↦ (assocInvMatrix_mul_mulTensor M N P i.divNat i.modNat).symm)

end MPSTensor.IsReduction

/-! ### Boundary-dressed proportionality -/

namespace MPSTensor

variable {d D D' m k : ℕ}

/-- Two left boundaries `X, Y` of a tensor `B` are boundary-dressed proportional
with scalar `z` when `X B^w = z Y B^w` for every sufficiently long word `w`.
This is the form in which two reductions onto the same normal tensor are
compared in Molnár--Ge--Schuch--Cirac, arXiv:1706.07329v2, Theorem 22,
`cornerproblem.tex` lines 3156--3162, and in which the anomaly three-cocycle is
defined in arXiv:2502.20257, display preceding `eq:3-cocycle`, `main.tex` lines
1506--1535. -/
def IsDressedProportional (B : MPSTensor d D) (X Y : Matrix (Fin m) (Fin D) ℂ)
    (z : ℂ) : Prop :=
  ∃ N : ℕ, ∀ w : List (Fin d), N ≤ w.length →
    X * Kraus.evalWord B w = z • (Y * Kraus.evalWord B w)

namespace IsDressedProportional

variable {B : MPSTensor d D} {X Y Z : Matrix (Fin m) (Fin D) ℂ} {z z' : ℂ}

/-- Every left boundary is dressed proportional to itself with scalar one. -/
theorem refl (B : MPSTensor d D) (X : Matrix (Fin m) (Fin D) ℂ) :
    IsDressedProportional B X X 1 :=
  ⟨0, fun w _ ↦ by rw [one_smul]⟩

/-- Dressed proportionality composes, multiplying the scalars. -/
theorem trans (h₁ : IsDressedProportional B X Y z) (h₂ : IsDressedProportional B Y Z z') :
    IsDressedProportional B X Z (z * z') := by
  obtain ⟨N₁, h₁⟩ := h₁
  obtain ⟨N₂, h₂⟩ := h₂
  refine ⟨max N₁ N₂, fun w hw ↦ ?_⟩
  rw [h₁ w (le_of_max_le_left hw), h₂ w (le_of_max_le_right hw), smul_smul]

/-- Dressed proportionality with a nonzero scalar is symmetric. -/
theorem symm (h : IsDressedProportional B X Y z) (hz : z ≠ 0) :
    IsDressedProportional B Y X z⁻¹ := by
  obtain ⟨N, h⟩ := h
  refine ⟨N, fun w hw ↦ ?_⟩
  rw [h w hw, smul_smul, inv_mul_cancel₀ hz, one_smul]

/-- Dressed proportionality is preserved by a common left factor. -/
theorem mul_left (h : IsDressedProportional B X Y z) (C : Matrix (Fin k) (Fin m) ℂ) :
    IsDressedProportional B (C * X) (C * Y) z := by
  obtain ⟨N, h⟩ := h
  refine ⟨N, fun w hw ↦ ?_⟩
  rw [Matrix.mul_assoc, h w hw, Matrix.mul_smul, Matrix.mul_assoc]

/-- Dressed proportionality transports along an invertible intertwiner of
letters, in the same way as `MPSTensor.IsReduction.of_intertwine`. -/
theorem of_intertwine {B' : MPSTensor d D'} {P : Matrix (Fin D') (Fin D) ℂ}
    {Q : Matrix (Fin D) (Fin D') ℂ} (hPQ : P * Q = 1) (hQP : Q * P = 1)
    (hB : ∀ i, B' i * P = P * B i) (h : IsDressedProportional B X Y z) :
    IsDressedProportional B' (X * Q) (Y * Q) z := by
  obtain ⟨N, h⟩ := h
  have hQ : ∀ w, Q * Kraus.evalWord B' w = Kraus.evalWord B w * Q := fun w ↦ by
    calc
      Q * Kraus.evalWord B' w = Q * (Kraus.evalWord B' w * P) * Q := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, hPQ, Matrix.mul_one]
      _ = Kraus.evalWord B w * Q := by
          rw [Kraus.evalWord_intertwine _ _ _ hB, ← Matrix.mul_assoc, hQP,
            Matrix.one_mul]
  refine ⟨N, fun w hw ↦ ?_⟩
  rw [Matrix.mul_assoc, hQ, ← Matrix.mul_assoc, h w hw, Matrix.smul_mul, Matrix.mul_assoc,
    ← hQ, Matrix.mul_assoc]

/-- **Pulling a dressed proportionality back along a reduction.** If `(V, W)`
reduces `B` onto `A` with equal positive-length matrix product vectors, and
`X A^w = z Y A^w` for long words, then `X V B^w = z Y V B^w` for long words.

The proof inserts the reduced block `W A^c V` in the interior of a long word,
which is allowed once both exterior buffers exceed the residual nilpotency
bound (Molnár--Ge--Schuch--Cirac, arXiv:1706.07329v2, Lemma `B_expand`,
`cornerproblem.tex` lines 3993--4005, in the corrected form of
`MPSTensor.IsReduction.evalWord_mul_reduced_exterior_eq_evalWord_append`). -/
theorem pullback {D_A : ℕ} {A : MPSTensor d D_A} {V : Matrix (Fin D_A) (Fin D) ℂ}
    {W : Matrix (Fin D) (Fin D_A) ℂ} {X Y : Matrix (Fin m) (Fin D_A) ℂ}
    (hR : IsReduction B A V W) (hSame : SameMPV₂Pos B A)
    (h : IsDressedProportional A X Y z) :
    IsDressedProportional B (X * V) (Y * V) z := by
  obtain ⟨N, h⟩ := h
  have hBound := hR.bondDim_isReductionResidualNilpotencyBound hSame
  refine ⟨N + 2 * D + 1, fun w hw ↦ ?_⟩
  let p := w.take D
  let r := w.drop D
  let c := r.take (w.length - 2 * D)
  let q := r.drop (w.length - 2 * D)
  have hpLen : p.length = D := by simp [p, List.length_take]; omega
  have hrLen : r.length = w.length - D := by simp [r, List.length_drop]
  have hcLen : c.length = w.length - 2 * D := by
    simp [c, hrLen, List.length_take]; omega
  have hqLen : q.length = D := by simp [q, hrLen]; omega
  have hsplit : p ++ c ++ q = w := by
    simp only [p, r, c, q, List.take_append_drop, List.append_assoc]
  have hc : c ≠ [] := by
    intro hc0
    rw [hc0] at hcLen
    simp at hcLen
    omega
  have hext := hR.evalWord_mul_reduced_exterior_eq_evalWord_append hBound p c q hc
    (by omega) (by omega)
  have hV : V * Kraus.evalWord B w = Kraus.evalWord A (p ++ c) * (V * Kraus.evalWord B q) := by
    rw [← hsplit, ← hext, Kraus.evalWord_append, ← hR.evalWord p]
    simp only [Matrix.mul_assoc]
  have hpc : N ≤ (p ++ c).length := by simp only [List.length_append]; omega
  rw [Matrix.mul_assoc, hV, ← Matrix.mul_assoc, h _ hpc, Matrix.smul_mul, Matrix.mul_assoc,
    ← hV, Matrix.mul_assoc]

/-- **Uniqueness of the dressed scalar.** If `X` is dressed proportional to `Y`
with two scalars, and `X B^w` is nonzero for arbitrarily long words, then the
two scalars agree. -/
theorem eq_of_forall_exists_ne_zero (h : IsDressedProportional B X Y z)
    (h' : IsDressedProportional B X Y z')
    (hX : ∀ N : ℕ, ∃ w : List (Fin d), N ≤ w.length ∧ X * Kraus.evalWord B w ≠ 0) :
    z = z' := by
  obtain ⟨N, h⟩ := h
  obtain ⟨N', h'⟩ := h'
  obtain ⟨w, hw, hne⟩ := hX (max N N')
  have e₁ := h w (le_of_max_le_left hw)
  have e₂ := h' w (le_of_max_le_right hw)
  by_contra hzz
  apply hne
  have hY : Y * Kraus.evalWord B w = 0 := by
    have : (z - z') • (Y * Kraus.evalWord B w) = 0 := by
      rw [sub_smul, ← e₁, ← e₂, sub_self]
    exact (smul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hzz)
  rw [e₁, hY, smul_zero]

end IsDressedProportional

namespace IsReduction

variable {D_A : ℕ} {B : MPSTensor d D} {A : MPSTensor d D_A}
  {V V' : Matrix (Fin D_A) (Fin D) ℂ} {W W' : Matrix (Fin D) (Fin D_A) ℂ}

/-- The left boundary of a reduction onto a normal tensor of positive bond
dimension is nonzero against arbitrarily long words: `V B^w W = A^w`, and a
normal tensor has nonzero words of every multiple of its injectivity length. -/
theorem exists_mul_evalWord_ne_zero (h : IsReduction B A V W) (hA : Kraus.IsNormal A)
    (hD : 0 < D_A) (N : ℕ) :
    ∃ w : List (Fin d), N ≤ w.length ∧ V * Kraus.evalWord B w ≠ 0 := by
  obtain ⟨L, hL, hinj⟩ := hA
  obtain ⟨σ, hσ⟩ := exists_evalWord_ne_zero_of_isNBlkInjective hD.ne'
    (isNBlkInjective_mul_of_isNBlkInjective A (Nat.succ_pos N) hinj)
  refine ⟨List.ofFn σ, ?_, fun h0 ↦ hσ ?_⟩
  · rw [List.length_ofFn]; nlinarith
  · rw [← h.evalWord, h0, Matrix.zero_mul]

/-- **Two reductions onto a normal tensor are dressed proportional**
(Molnár--Ge--Schuch--Cirac, arXiv:1706.07329v2, Theorem 22, `cornerproblem.tex`
lines 3156--3162): given equal positive-length matrix product vectors, the left
boundaries of two reductions of `B` onto a normal `A` agree against long words
up to a nonzero scalar. -/
theorem exists_isDressedProportional (h : IsReduction B A V W)
    (h' : IsReduction B A V' W') (hA : Kraus.IsNormal A) (hSame : SameMPV₂Pos B A) :
    ∃ z : ℂ, z ≠ 0 ∧ IsDressedProportional B V V' z := by
  obtain ⟨z, hz, hw⟩ := h.exists_boundary_dressed_proportional_of_nilpotencyLength_le h' hA
    hSame (le_max_left _ _) (le_max_right _ _)
  exact ⟨z, hz, 2 * max (reductionResidualNilpotencyLength B A V W)
    (reductionResidualNilpotencyLength B A V' W') + 1, fun w hlen ↦ (hw w (by omega)).1⟩

end IsReduction

end MPSTensor

namespace MPOTensor

variable {d D₁ D₂ D₃ m : ℕ}

/-- The left boundary `X ⊗ 1` against a word of a product tensor. -/
theorem kronId_mul_evalWord_toMPSTensor_mulTensor_ofFn (M : MPOTensor d D₁)
    (P : MPOTensor d D₂) (X : Matrix (Fin m) (Fin D₁) ℂ) {L : ℕ}
    (u : Fin L → Fin (d * d)) :
    kronId X D₂ * Kraus.evalWord (mulTensor M P).toMPSTensor (List.ofFn u) =
      (∑ ρ : Fin L → Fin d,
        (X * Kraus.evalWord M.toMPSTensor
            (List.ofFn fun k ↦ finProdFinEquiv ((u k).divNat, ρ k))) ⊗ₖ
          Kraus.evalWord P.toMPSTensor
            (List.ofFn fun k ↦ finProdFinEquiv (ρ k, (u k).modNat))).submatrix
        finProdFinEquiv.symm finProdFinEquiv.symm := by
  rw [evalWord_toMPSTensor_mulTensor_ofFn, kronId, Matrix.submatrix_mul_equiv,
    Matrix.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun ρ _ ↦ ?_
  rw [← Matrix.mul_kronecker_mul, Matrix.one_mul]

/-- The left boundary `1 ⊗ X` against a word of a product tensor. -/
theorem idKron_mul_evalWord_toMPSTensor_mulTensor_ofFn (P : MPOTensor d D₂)
    (M : MPOTensor d D₁) (X : Matrix (Fin m) (Fin D₁) ℂ) {L : ℕ}
    (u : Fin L → Fin (d * d)) :
    idKron D₂ X * Kraus.evalWord (mulTensor P M).toMPSTensor (List.ofFn u) =
      (∑ ρ : Fin L → Fin d,
        Kraus.evalWord P.toMPSTensor
            (List.ofFn fun k ↦ finProdFinEquiv ((u k).divNat, ρ k)) ⊗ₖ
          (X * Kraus.evalWord M.toMPSTensor
            (List.ofFn fun k ↦ finProdFinEquiv (ρ k, (u k).modNat)))).submatrix
        finProdFinEquiv.symm finProdFinEquiv.symm := by
  rw [evalWord_toMPSTensor_mulTensor_ofFn, idKron, Matrix.submatrix_mul_equiv,
    Matrix.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun ρ _ ↦ ?_
  rw [← Matrix.mul_kronecker_mul, Matrix.one_mul]

/-- Dressed proportionality on a factor extends to the product with a factor
on the right, through `X ⊗ 1`. -/
theorem _root_.MPSTensor.IsDressedProportional.mulTensor_kronId {M : MPOTensor d D₁}
    (P : MPOTensor d D₂) {X Y : Matrix (Fin m) (Fin D₁) ℂ} {z : ℂ}
    (h : MPSTensor.IsDressedProportional M.toMPSTensor X Y z) :
    MPSTensor.IsDressedProportional (mulTensor M P).toMPSTensor (kronId X D₂)
      (kronId Y D₂) z := by
  obtain ⟨N, h⟩ := h
  refine ⟨N, fun w hw ↦ ?_⟩
  obtain ⟨L, u, rfl⟩ := List.exists_eq_ofFn w
  rw [List.length_ofFn] at hw
  rw [kronId_mul_evalWord_toMPSTensor_mulTensor_ofFn,
    kronId_mul_evalWord_toMPSTensor_mulTensor_ofFn]
  have h' : ∀ σ : Fin L → Fin (d * d), X * Kraus.evalWord M.toMPSTensor (List.ofFn σ) =
      z • (Y * Kraus.evalWord M.toMPSTensor (List.ofFn σ)) := fun σ ↦
    h _ (by rw [List.length_ofFn]; exact hw)
  simp only [h', Matrix.smul_kronecker, ← Finset.smul_sum]
  rfl

/-- Dressed proportionality on a factor extends to the product with a factor
on the left, through `1 ⊗ X`. -/
theorem _root_.MPSTensor.IsDressedProportional.mulTensor_idKron {M : MPOTensor d D₁}
    (P : MPOTensor d D₂) {X Y : Matrix (Fin m) (Fin D₁) ℂ} {z : ℂ}
    (h : MPSTensor.IsDressedProportional M.toMPSTensor X Y z) :
    MPSTensor.IsDressedProportional (mulTensor P M).toMPSTensor (idKron D₂ X)
      (idKron D₂ Y) z := by
  obtain ⟨N, h⟩ := h
  refine ⟨N, fun w hw ↦ ?_⟩
  obtain ⟨L, u, rfl⟩ := List.exists_eq_ofFn w
  rw [List.length_ofFn] at hw
  rw [idKron_mul_evalWord_toMPSTensor_mulTensor_ofFn,
    idKron_mul_evalWord_toMPSTensor_mulTensor_ofFn]
  have h' : ∀ σ : Fin L → Fin (d * d), X * Kraus.evalWord M.toMPSTensor (List.ofFn σ) =
      z • (Y * Kraus.evalWord M.toMPSTensor (List.ofFn σ)) := fun σ ↦
    h _ (by rw [List.length_ofFn]; exact hw)
  simp only [h', Matrix.kronecker_smul, ← Finset.smul_sum]
  rfl

/-- An intertwiner of the letters of two tensors, tensored with the identity,
intertwines the letters of their products with a common factor on the right. -/
theorem mulTensor_mul_kronId_of_intertwine {X' : MPOTensor d D₁} {X : MPOTensor d D₂}
    (R : MPOTensor d D₃) {P : Matrix (Fin D₁) (Fin D₂) ℂ}
    (hX : ∀ i l, X' i l * P = P * X i l) (i l : Fin d) :
    mulTensor X' R i l * kronId P D₃ = kronId P D₃ * mulTensor X R i l := by
  rw [mulTensor_apply, mulTensor_apply, kronId, Matrix.submatrix_mul_equiv,
    Matrix.submatrix_mul_equiv, Matrix.sum_mul, Matrix.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, hX, Matrix.mul_one,
    Matrix.one_mul]

end MPOTensor

namespace MPOTensor

/-! ### Coherence of the bond associator -/

/-- `f ⊗ 1` of a permutation matrix is the permutation matrix of the product equivalence. -/
theorem kronId_toPEquiv {m n : ℕ} (f : Fin m ≃ Fin n) (D : ℕ) :
    kronId f.toPEquiv.toMatrix D =
      (finProdFinEquiv.symm.trans ((Equiv.prodCongr f (Equiv.refl (Fin D))).trans
        finProdFinEquiv)).toPEquiv.toMatrix := by
  ext x y
  obtain ⟨⟨x1, x2⟩, rfl⟩ := finProdFinEquiv.surjective x
  obtain ⟨⟨y1, y2⟩, rfl⟩ := finProdFinEquiv.surjective y
  simp [kronId, PEquiv.toMatrix_apply, Matrix.one_apply, Option.mem_def, Prod.ext_iff]
  split_ifs <;> simp_all

/-- `1 ⊗ f` of a permutation matrix is the permutation matrix of the product equivalence. -/
theorem idKron_toPEquiv {m n : ℕ} (D : ℕ) (f : Fin m ≃ Fin n) :
    idKron D f.toPEquiv.toMatrix =
      (finProdFinEquiv.symm.trans ((Equiv.prodCongr (Equiv.refl (Fin D)) f).trans
        finProdFinEquiv)).toPEquiv.toMatrix := by
  ext x y
  obtain ⟨⟨x1, x2⟩, rfl⟩ := finProdFinEquiv.surjective x
  obtain ⟨⟨y1, y2⟩, rfl⟩ := finProdFinEquiv.surjective y
  simp [idKron, PEquiv.toMatrix_apply, Matrix.one_apply, Option.mem_def, Prod.ext_iff]
  split_ifs <;> simp_all

/-- **Pentagon identity of the bond associator.** The two ways of
reassociating four bond spaces from `((a b) c) e` to `a (b (c e))` agree.

Source: arXiv:1511.08090, Section ``Associativity and the pentagon equation'',
lines 237--251 of the source. -/
theorem assocInv_pentagon (a b c e : ℕ) :
    idKron a (mulTensorAssocInvMatrix b c e) * mulTensorAssocInvMatrix a (b * c) e *
        kronId (mulTensorAssocInvMatrix a b c) e =
      mulTensorAssocInvMatrix a b (c * e) * mulTensorAssocInvMatrix (a * b) c e := by
  simp only [mulTensorAssocInvMatrix, kronId_toPEquiv, idKron_toPEquiv,
    ← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans]
  congr 2
  ext x
  obtain ⟨⟨x1, x2⟩, rfl⟩ := finProdFinEquiv.surjective x
  obtain ⟨⟨x3, x4⟩, rfl⟩ := finProdFinEquiv.surjective x2
  obtain ⟨⟨x5, x6⟩, rfl⟩ := finProdFinEquiv.surjective x4
  simp [mulTensorAssocEquiv]

/-- Naturality of the inverse bond associator in its first slot. -/
theorem assocInv_mul_kronId_kronId {m n : ℕ} (X : Matrix (Fin m) (Fin n) ℂ) (b c : ℕ) :
    mulTensorAssocInvMatrix m b c * kronId (kronId X b) c =
      kronId X (b * c) * mulTensorAssocInvMatrix n b c := by
  rw [mulTensorAssocInvMatrix, mulTensorAssocInvMatrix, PEquiv.toMatrix_toPEquiv_mul,
    PEquiv.mul_toMatrix_toPEquiv]
  ext x y
  obtain ⟨⟨x1, x2⟩, rfl⟩ := finProdFinEquiv.surjective x
  obtain ⟨⟨x3, x4⟩, rfl⟩ := finProdFinEquiv.surjective x2
  obtain ⟨⟨y1, y2⟩, rfl⟩ := finProdFinEquiv.surjective y
  obtain ⟨⟨y3, y4⟩, rfl⟩ := finProdFinEquiv.surjective y1
  simp [kronId, mulTensorAssocEquiv, Matrix.one_apply]
  split_ifs <;> simp_all

/-- Naturality of the inverse bond associator in its middle slot. -/
theorem assocInv_mul_kronId_idKron {m n : ℕ} (a c : ℕ) (X : Matrix (Fin m) (Fin n) ℂ) :
    mulTensorAssocInvMatrix a m c * kronId (idKron a X) c =
      idKron a (kronId X c) * mulTensorAssocInvMatrix a n c := by
  rw [mulTensorAssocInvMatrix, mulTensorAssocInvMatrix, PEquiv.toMatrix_toPEquiv_mul,
    PEquiv.mul_toMatrix_toPEquiv]
  ext x y
  obtain ⟨⟨x1, x2⟩, rfl⟩ := finProdFinEquiv.surjective x
  obtain ⟨⟨x3, x4⟩, rfl⟩ := finProdFinEquiv.surjective x2
  obtain ⟨⟨y1, y2⟩, rfl⟩ := finProdFinEquiv.surjective y
  obtain ⟨⟨y3, y4⟩, rfl⟩ := finProdFinEquiv.surjective y1
  simp [kronId, idKron, mulTensorAssocEquiv, Matrix.one_apply, mul_comm]
  split_ifs <;> simp_all

/-- Naturality of the inverse bond associator in its last slot. -/
theorem assocInv_mul_idKron {m n : ℕ} (a b : ℕ) (X : Matrix (Fin m) (Fin n) ℂ) :
    mulTensorAssocInvMatrix a b m * idKron (a * b) X =
      idKron a (idKron b X) * mulTensorAssocInvMatrix a b n := by
  rw [mulTensorAssocInvMatrix, mulTensorAssocInvMatrix, PEquiv.toMatrix_toPEquiv_mul,
    PEquiv.mul_toMatrix_toPEquiv]
  ext x y
  obtain ⟨⟨x1, x2⟩, rfl⟩ := finProdFinEquiv.surjective x
  obtain ⟨⟨x3, x4⟩, rfl⟩ := finProdFinEquiv.surjective x2
  obtain ⟨⟨y1, y2⟩, rfl⟩ := finProdFinEquiv.surjective y
  obtain ⟨⟨y3, y4⟩, rfl⟩ := finProdFinEquiv.surjective y1
  simp [idKron, mulTensorAssocEquiv, Matrix.one_apply]
  split_ifs <;> simp_all

end MPOTensor

namespace MPOTensor

/-! ### Reassociated forms for rewriting right-associated products -/

variable {m n : ℕ}

/-- `assocInv_mul_kronId_kronId` against a trailing factor. -/
theorem assocInv_mul_kronId_kronId_assoc {p : ℕ} (X : Matrix (Fin m) (Fin n) ℂ) (b c : ℕ)
    (Z : Matrix (Fin (n * b * c)) (Fin p) ℂ) :
    mulTensorAssocInvMatrix m b c * (kronId (kronId X b) c * Z) =
      kronId X (b * c) * (mulTensorAssocInvMatrix n b c * Z) := by
  rw [← Matrix.mul_assoc, assocInv_mul_kronId_kronId, Matrix.mul_assoc]

/-- `assocInv_mul_kronId_idKron` against a trailing factor. -/
theorem assocInv_mul_kronId_idKron_assoc {p : ℕ} (a c : ℕ) (X : Matrix (Fin m) (Fin n) ℂ)
    (Z : Matrix (Fin (a * n * c)) (Fin p) ℂ) :
    mulTensorAssocInvMatrix a m c * (kronId (idKron a X) c * Z) =
      idKron a (kronId X c) * (mulTensorAssocInvMatrix a n c * Z) := by
  rw [← Matrix.mul_assoc, assocInv_mul_kronId_idKron, Matrix.mul_assoc]

/-- `assocInv_mul_idKron` against a trailing factor. -/
theorem assocInv_mul_idKron_assoc {p : ℕ} (a b : ℕ) (X : Matrix (Fin m) (Fin n) ℂ)
    (Z : Matrix (Fin (a * b * n)) (Fin p) ℂ) :
    mulTensorAssocInvMatrix a b m * (idKron (a * b) X * Z) =
      idKron a (idKron b X) * (mulTensorAssocInvMatrix a b n * Z) := by
  rw [← Matrix.mul_assoc, assocInv_mul_idKron, Matrix.mul_assoc]

/-- `kronId_mul_idKron` against a trailing factor. -/
theorem kronId_mul_idKron_assoc {m' n' p : ℕ} (V : Matrix (Fin m) (Fin n) ℂ)
    (U : Matrix (Fin m') (Fin n') ℂ) (Z : Matrix (Fin (n * n')) (Fin p) ℂ) :
    kronId V m' * (idKron n U * Z) = idKron m U * (kronId V n' * Z) := by
  rw [← Matrix.mul_assoc, kronId_mul_idKron, Matrix.mul_assoc]

/-- `assocInv_pentagon` against a trailing factor. -/
theorem assocInv_pentagon_assoc {p : ℕ} (a b c e : ℕ)
    (Z : Matrix (Fin (a * b * c * e)) (Fin p) ℂ) :
    idKron a (mulTensorAssocInvMatrix b c e) * (mulTensorAssocInvMatrix a (b * c) e *
        (kronId (mulTensorAssocInvMatrix a b c) e * Z)) =
      mulTensorAssocInvMatrix a b (c * e) * (mulTensorAssocInvMatrix (a * b) c e * Z) := by
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, assocInv_pentagon, Matrix.mul_assoc]

end MPOTensor
