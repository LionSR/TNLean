/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Core.ReductionComposition
import TNLean.MPS.MPDO.ActionTensor

/-!
# Reductions of action tensors

The action tensor `T · A` of a matrix product operator on a matrix product state
(`MPOTensor.actTensor`) carries two bond factors, the operator bond and the state bond. This
file transports rectangular reductions through either factor, reassociates iterated action
tensors, and lifts left-dressed proportionality relations through an action tensor.

* A reduction `(V, W)` of the state `B` onto `A` gives the reduction `(1 ⊗ V, 1 ⊗ W)` of
  `T · B` onto `T · A`: the action tensor of `T` on the inner state reduces first.
* A reduction `(V, W)` of the operator `X` onto `Y`, read on the pair alphabet, gives the
  reduction `(V ⊗ 1, W ⊗ 1)` of `X · B` onto `Y · B`: a fusion tensor acts on the operator
  legs of the action tensor.
* The bond associator intertwines `(M N) · A` with `M · (N · A)`.
* Dressed proportionality `V B^w = z V' B^w` on long words
  (`MPSTensor.IsDressedProportional`) lifts, with the same scalar, to the action tensor.

These are the manipulations of arXiv:2502.20257, equation `eq:defL` (`main.tex` lines
1875--1913), where the L-symbols compare the two reductions of the action of `g` after `h`
onto the state, one through two action tensors and one through the fusion tensor of `(g, h)`
followed by the action tensor of `gh`; and of arXiv:2203.12563, `sec:PBC`, lines 1091--1129,
where the same comparison is made on words longer than the nilpotency length. No L-symbol is
defined here.

## Main results

* `MPSTensor.IsReduction.actTensor_idKron`, `MPSTensor.IsReduction.actTensor_kronId`
* `MPOTensor.actTensor_mulTensor`, `MPOTensor.actTensor_mulTensor_mul_assocMatrix`
* `MPSTensor.IsReduction.actTensor_assoc_left`, `MPSTensor.IsReduction.actTensor_assoc_right`
* `MPOTensor.actTensor_mul_kronId_of_intertwine`
* `MPSTensor.IsDressedProportional.actTensor_idKron`,
  `MPSTensor.IsDressedProportional.actTensor_kronId`
-/

open scoped Matrix Kronecker

namespace MPOTensor

variable {d D₁ D₂ D₃ : ℕ}

/-! ### Reductions through one bond factor -/

/-- **Reducing the state inside an action tensor.** If `(V, W)` reduces `B` onto `A`, then
`(1 ⊗ V, 1 ⊗ W)` reduces the action tensor `T · B` onto `T · A`.

Source: arXiv:2502.20257, `eq:defL`, `main.tex` lines 1875--1913 (the action tensor of `h`
applied first, with an identity strand on the operator leg of `g`). -/
theorem _root_.MPSTensor.IsReduction.actTensor_idKron (T : MPOTensor d D₃)
    {B : MPSTensor d D₂} {A : MPSTensor d D₁} {V : Matrix (Fin D₁) (Fin D₂) ℂ}
    {W : Matrix (Fin D₂) (Fin D₁) ℂ} (h : MPSTensor.IsReduction B A V W) :
    MPSTensor.IsReduction (actTensor T B) (actTensor T A) (idKron D₃ V) (idKron D₃ W) := by
  rw [MPSTensor.IsReduction.iff_forall_evalWord]
  intro w
  obtain ⟨L, σ, rfl⟩ := List.exists_eq_ofFn w
  rw [evalWord_actTensor, evalWord_actTensor, idKron, idKron, Matrix.submatrix_mul_equiv,
    Matrix.submatrix_mul_equiv, Matrix.mul_sum, Matrix.sum_mul]
  congr 1
  refine Finset.sum_congr rfl fun τ _ ↦ ?_
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, h.evalWord,
    Matrix.one_mul, Matrix.mul_one]

/-- **Reducing the operator inside an action tensor.** If `(V, W)` reduces the pair-alphabet
view of `X` onto that of `Y`, then `(V ⊗ 1, W ⊗ 1)` reduces the action tensor `X · B` onto
`Y · B`.

Source: arXiv:2502.20257, `eq:defL`, `main.tex` lines 1875--1913 (the fusion tensor of
`(g, h)` applied to the operator legs, with an identity strand on the state leg). -/
theorem _root_.MPSTensor.IsReduction.actTensor_kronId {X : MPOTensor d D₂}
    {Y : MPOTensor d D₁} (B : MPSTensor d D₃) {V : Matrix (Fin D₁) (Fin D₂) ℂ}
    {W : Matrix (Fin D₂) (Fin D₁) ℂ}
    (h : MPSTensor.IsReduction X.toMPSTensor Y.toMPSTensor V W) :
    MPSTensor.IsReduction (actTensor X B) (actTensor Y B) (kronId V D₃) (kronId W D₃) := by
  rw [MPSTensor.IsReduction.iff_forall_evalWord]
  intro w
  obtain ⟨L, σ, rfl⟩ := List.exists_eq_ofFn w
  rw [evalWord_actTensor, evalWord_actTensor, kronId, kronId, Matrix.submatrix_mul_equiv,
    Matrix.submatrix_mul_equiv, Matrix.mul_sum, Matrix.sum_mul]
  congr 1
  refine Finset.sum_congr rfl fun τ _ ↦ ?_
  have hw := h.evalWord (List.ofFn fun k ↦ finProdFinEquiv (σ k, τ k))
  simp only [evalWord_toMPSTensor_pairConfig] at hw
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, hw, Matrix.one_mul,
    Matrix.mul_one]

/-! ### Reassociation -/

/-- **Associativity of the action.** The action tensor of a product `M N` on `A`, reindexed by
the bond associator, is the action tensor of `M` on the action tensor of `N` on `A`.

Source: arXiv:2203.12563, `sec:PBC`, line 1091 (the product `(g × h) · x = g · (h · x)`);
the associator is that of arXiv:1606.00608, lines 995--999. -/
theorem actTensor_mulTensor (M : MPOTensor d D₁) (N : MPOTensor d D₂) (A : MPSTensor d D₃)
    (i : Fin d) :
    actTensor (mulTensor M N) A i =
      (actTensor M (actTensor N A) i).submatrix
        (mulTensorAssocEquiv D₁ D₂ D₃) (mulTensorAssocEquiv D₁ D₂ D₃) := by
  rw [actTensor_apply, actTensor_apply]
  ext x y
  rcases finProdFinEquiv.surjective x with ⟨⟨x₁₂, x₃⟩, rfl⟩
  rcases finProdFinEquiv.surjective x₁₂ with ⟨⟨x₁, x₂⟩, rfl⟩
  rcases finProdFinEquiv.surjective y with ⟨⟨y₁₂, y₃⟩, rfl⟩
  rcases finProdFinEquiv.surjective y₁₂ with ⟨⟨y₁, y₂⟩, rfl⟩
  simp only [Matrix.submatrix_apply, Matrix.sum_apply, mulTensor_apply, actTensor_apply,
    mulTensorAssocEquiv, Equiv.trans_apply, Equiv.prodCongr_apply, Prod.map_apply,
    Equiv.refl_apply, Equiv.prodAssoc_apply]
  simp only [Equiv.symm_apply_apply, Matrix.kroneckerMap_apply, Matrix.submatrix_apply,
    Equiv.coe_refl, Prod.map_apply, id_eq]
  simp only [Matrix.sum_apply, Matrix.kronecker_apply]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [mul_assoc]

/-- The bond associator intertwines the letters of `(M N) · A` and `M · (N · A)`. -/
theorem actTensor_mulTensor_mul_assocMatrix (M : MPOTensor d D₁) (N : MPOTensor d D₂)
    (A : MPSTensor d D₃) (i : Fin d) :
    actTensor (mulTensor M N) A i * mulTensorAssocMatrix D₁ D₂ D₃ =
      mulTensorAssocMatrix D₁ D₂ D₃ * actTensor M (actTensor N A) i := by
  rw [actTensor_mulTensor, mulTensorAssocMatrix, PEquiv.mul_toMatrix_toPEquiv,
    PEquiv.toMatrix_toPEquiv_mul]
  ext x y
  simp

/-- The inverse bond associator intertwines the letters of `(M N) · A` and `M · (N · A)` in the
opposite direction. -/
theorem assocInvMatrix_mul_actTensor_mulTensor (M : MPOTensor d D₁) (N : MPOTensor d D₂)
    (A : MPSTensor d D₃) (i : Fin d) :
    mulTensorAssocInvMatrix D₁ D₂ D₃ * actTensor (mulTensor M N) A i =
      actTensor M (actTensor N A) i * mulTensorAssocInvMatrix D₁ D₂ D₃ := by
  have h := congrArg (fun X ↦ mulTensorAssocInvMatrix D₁ D₂ D₃ * X *
    mulTensorAssocInvMatrix D₁ D₂ D₃) (actTensor_mulTensor_mul_assocMatrix M N A i)
  simp only [← Matrix.mul_assoc, mulTensorAssocInvMatrix_mul_matrix, Matrix.one_mul] at h
  simpa only [Matrix.mul_assoc, mulTensorAssocMatrix_mul_invMatrix, Matrix.mul_one] using h

/-- **Associativity transport, iterated to product.** A reduction `(V, W)` of `M · (N · A)`
gives the reduction `(V a⁻¹, a W)` of `(M N) · A`, where `a` is the bond associator.

Source: arXiv:2502.20257, `eq:defL`, `main.tex` lines 1875--1913. -/
theorem _root_.MPSTensor.IsReduction.actTensor_assoc_left {M : MPOTensor d D₁}
    {N : MPOTensor d D₂} {A : MPSTensor d D₃} {D : ℕ} {Z : MPSTensor d D}
    {V : Matrix (Fin D) (Fin (D₁ * (D₂ * D₃))) ℂ}
    {W : Matrix (Fin (D₁ * (D₂ * D₃))) (Fin D) ℂ}
    (h : MPSTensor.IsReduction (actTensor M (actTensor N A)) Z V W) :
    MPSTensor.IsReduction (actTensor (mulTensor M N) A) Z
      (V * mulTensorAssocInvMatrix D₁ D₂ D₃) (mulTensorAssocMatrix D₁ D₂ D₃ * W) :=
  h.of_intertwine (mulTensorAssocInvMatrix_mul_matrix D₁ D₂ D₃)
    (actTensor_mulTensor_mul_assocMatrix M N A)

/-- **Associativity transport, product to iterated.** A reduction `(V, W)` of `(M N) · A`
gives the reduction `(V a, a⁻¹ W)` of `M · (N · A)`, where `a` is the bond associator.

Source: arXiv:2502.20257, `eq:defL`, `main.tex` lines 1875--1913. -/
theorem _root_.MPSTensor.IsReduction.actTensor_assoc_right {M : MPOTensor d D₁}
    {N : MPOTensor d D₂} {A : MPSTensor d D₃} {D : ℕ} {Z : MPSTensor d D}
    {V : Matrix (Fin D) (Fin (D₁ * D₂ * D₃)) ℂ}
    {W : Matrix (Fin (D₁ * D₂ * D₃)) (Fin D) ℂ}
    (h : MPSTensor.IsReduction (actTensor (mulTensor M N) A) Z V W) :
    MPSTensor.IsReduction (actTensor M (actTensor N A)) Z
      (V * mulTensorAssocMatrix D₁ D₂ D₃) (mulTensorAssocInvMatrix D₁ D₂ D₃ * W) :=
  h.of_intertwine (mulTensorAssocMatrix_mul_invMatrix D₁ D₂ D₃)
    (fun i ↦ (assocInvMatrix_mul_actTensor_mulTensor M N A i).symm)

/-! ### Intertwiners of the operator factor -/

/-- An intertwiner `P` of the letters of two operator tensors, tensored with the identity on
the state bond, intertwines the letters of their action tensors on a common state. -/
theorem actTensor_mul_kronId_of_intertwine {X' : MPOTensor d D₁} {X : MPOTensor d D₂}
    (B : MPSTensor d D₃) {P : Matrix (Fin D₁) (Fin D₂) ℂ}
    (hX : ∀ i l, X' i l * P = P * X i l) (i : Fin d) :
    actTensor X' B i * kronId P D₃ = kronId P D₃ * actTensor X B i := by
  rw [actTensor_apply, actTensor_apply, kronId, Matrix.submatrix_mul_equiv,
    Matrix.submatrix_mul_equiv, Matrix.sum_mul, Matrix.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, hX, Matrix.mul_one,
    Matrix.one_mul]

/-! ### Lifting dressed proportionality -/

/-- **Lifting a dressed proportionality through the operator bond.** If
`V B^w = z V' B^w` for long words, then `(1 ⊗ V) (T · B)^w = z (1 ⊗ V') (T · B)^w` for
words of the same lengths.

Source: arXiv:2203.12563, `sec:PBC`, lines 1091--1129: the L-symbols are phase factors
between reductions on words longer than the nilpotency length, and they are compared inside
further action tensors. -/
theorem _root_.MPSTensor.IsDressedProportional.actTensor_idKron (T : MPOTensor d D₃)
    {B : MPSTensor d D₂} {m : ℕ} {V V' : Matrix (Fin m) (Fin D₂) ℂ} {z : ℂ}
    (h : MPSTensor.IsDressedProportional B V V' z) :
    MPSTensor.IsDressedProportional (actTensor T B) (idKron D₃ V) (idKron D₃ V') z := by
  obtain ⟨N, h⟩ := h
  refine ⟨N, fun w hw ↦ ?_⟩
  obtain ⟨L, σ, rfl⟩ := List.exists_eq_ofFn w
  rw [List.length_ofFn] at hw
  rw [evalWord_actTensor, idKron, idKron, Matrix.submatrix_mul_equiv,
    Matrix.submatrix_mul_equiv]
  rw [Matrix.mul_sum, Matrix.mul_sum]
  have key : ∀ τ : Fin L → Fin d,
      ((1 : Matrix (Fin D₃) (Fin D₃) ℂ) ⊗ₖ V) *
          (evalWord T (List.ofFn σ) (List.ofFn τ) ⊗ₖ Kraus.evalWord B (List.ofFn τ)) =
        z • (((1 : Matrix (Fin D₃) (Fin D₃) ℂ) ⊗ₖ V') *
          (evalWord T (List.ofFn σ) (List.ofFn τ) ⊗ₖ Kraus.evalWord B (List.ofFn τ))) := by
    intro τ
    rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
      h _ (by rw [List.length_ofFn]; exact hw), Matrix.kronecker_smul]
  simp only [key, ← Finset.smul_sum]
  rfl

/-- **Lifting a dressed proportionality through the state bond.** If the pair-alphabet view
of `X` satisfies `V X^u = z V' X^u` for long pair words, then
`(V ⊗ 1) (X · B)^w = z (V' ⊗ 1) (X · B)^w` for words of the same lengths.

Source: arXiv:2203.12563, `sec:PBC`, lines 1028 and 1091--1129: the three-cocycle, defined
by fusion tensors on long words, is compared with the L-symbols inside the action on the
state. -/
theorem _root_.MPSTensor.IsDressedProportional.actTensor_kronId {X : MPOTensor d D₂}
    (B : MPSTensor d D₃) {m : ℕ} {V V' : Matrix (Fin m) (Fin D₂) ℂ} {z : ℂ}
    (h : MPSTensor.IsDressedProportional X.toMPSTensor V V' z) :
    MPSTensor.IsDressedProportional (actTensor X B) (kronId V D₃) (kronId V' D₃) z := by
  obtain ⟨N, h⟩ := h
  refine ⟨N, fun w hw ↦ ?_⟩
  obtain ⟨L, σ, rfl⟩ := List.exists_eq_ofFn w
  rw [List.length_ofFn] at hw
  rw [evalWord_actTensor, kronId, kronId, Matrix.submatrix_mul_equiv,
    Matrix.submatrix_mul_equiv]
  rw [Matrix.mul_sum, Matrix.mul_sum]
  have key : ∀ τ : Fin L → Fin d,
      (V ⊗ₖ (1 : Matrix (Fin D₃) (Fin D₃) ℂ)) *
          (evalWord X (List.ofFn σ) (List.ofFn τ) ⊗ₖ Kraus.evalWord B (List.ofFn τ)) =
        z • ((V' ⊗ₖ (1 : Matrix (Fin D₃) (Fin D₃) ℂ)) *
          (evalWord X (List.ofFn σ) (List.ofFn τ) ⊗ₖ Kraus.evalWord B (List.ofFn τ))) := by
    intro τ
    have hu := h (List.ofFn fun k ↦ finProdFinEquiv (σ k, τ k))
      (by rw [List.length_ofFn]; exact hw)
    simp only [evalWord_toMPSTensor_pairConfig] at hu
    rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, hu, Matrix.smul_kronecker]
  simp only [key, ← Finset.smul_sum]
  rfl

end MPOTensor
