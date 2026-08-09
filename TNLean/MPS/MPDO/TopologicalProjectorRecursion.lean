/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.FinSum
import TNLean.MPS.MPDO.TopologicalProjectors

/-!
# Recursive fusion histories for the topological projector

This file records the left-associated fusion histories and their terminal bond spaces in the
recursive operator of arXiv:1606.00608, lines 999--1010.  A list is written in reverse order:
if `previous` describes a chain and `β :: previous` is formed, then the sector `β` is appended
at the right end of that chain.  This convention makes the iterated product tensor and the
sequential fusion coisometry structurally recursive.

## Main definitions

* `FusionHistory`: intermediate labels and multiplicity indices in a left-associated fusion.
* `FusionHistoryIndex`: a fusion history together with the bond index of its final label.
* `fusionChainTensor`: the corresponding left-associated product tensor.
* `fusionHistoryWeight`: the product of the diagonal structure coefficients along a history.
* `recursiveProjectorQ`: the recursive operator on the history-indexed terminal bond spaces.
* `sequentialFusionCoisometry`: the sequential circuit from the product bond space onto those
  terminal bond spaces.

## References

* arXiv:1606.00608, Theorem 4.14(iii) and lines 999--1010.
-/

open scoped Matrix Kronecker

namespace MPOTensor.BNTFusionCoisometryFamily

universe u

variable {Λ : Type u} [Fintype Λ] [DecidableEq Λ] {p : ℕ}

/-- The data of a left-associated fusion history with prescribed final label.

Source: arXiv:1606.00608, Theorem 4.14(iii), lines 986--993, and the recursive operator at
lines 999--1010. -/
def FusionHistoryData (Fam : BNTFusionCoisometryFamily Λ p) (α : Λ) :
    List Λ → Λ → Type u
  | [], γ => ULift.{u} (Fin (if γ = α then 1 else 0))
  | β :: previous, γ =>
      (δ : Λ) × FusionHistoryData Fam α previous δ × Fin (Fam.chi.dim δ β γ)

/-- A left-associated fusion history.  The list is the reverse of the labels appended after
the initial label `α`; each step records the new final label and the corresponding diagonal
index of the structure matrix.

Source: arXiv:1606.00608, Theorem 4.14(iii), lines 986--993, and the recursive operator at
lines 999--1010. -/
abbrev FusionHistory (Fam : BNTFusionCoisometryFamily Λ p)
    (α : Λ) (previous : List Λ) : Type u :=
  (γ : Λ) × FusionHistoryData Fam α previous γ

/-- The final label of a left-associated fusion history.

Source: arXiv:1606.00608, the sequential fusion circuit at lines 999--1010. -/
abbrev fusionHistoryFinalLabel (Fam : BNTFusionCoisometryFamily Λ p)
    (α : Λ) (previous : List Λ) (h : FusionHistory Fam α previous) : Λ :=
  h.1

/-- The final label of an explicitly constructed history is its first coordinate. -/
@[simp] theorem fusionHistoryFinalLabel_mk
    (Fam : BNTFusionCoisometryFamily Λ p) (α γ : Λ) (previous : List Λ)
    (h : FusionHistoryData Fam α previous γ) :
    fusionHistoryFinalLabel Fam α previous ⟨γ, h⟩ = γ :=
  rfl

/-- An empty fusion history ends at its initial label. -/
@[simp] theorem fusionHistoryFinalLabel_empty
    (Fam : BNTFusionCoisometryFamily Λ p) (α : Λ) (h : FusionHistory Fam α []) :
    fusionHistoryFinalLabel Fam α [] h = α := by
  change h.1 = α
  by_contra hne
  have hlt := h.2.down.isLt
  simp [FusionHistoryData, hne] at hlt

/-- A nonempty fusion history ends at its explicitly recorded final label. -/
@[simp] theorem fusionHistoryFinalLabel_cons
    (Fam : BNTFusionCoisometryFamily Λ p) (α β : Λ) (previous : List Λ)
    (h : FusionHistory Fam α (β :: previous)) :
    fusionHistoryFinalLabel Fam α (β :: previous) h = h.1 :=
  rfl

/-- The fusion histories with prescribed final label form a finite type. -/
noncomputable instance fusionHistoryDataFintype
    (Fam : BNTFusionCoisometryFamily Λ p) (α : Λ) :
    (previous : List Λ) → (γ : Λ) → Fintype (FusionHistoryData Fam α previous γ)
  | [], γ =>
      Fintype.ofEquiv (Fin (if γ = α then 1 else 0)) Equiv.ulift.symm
  | β :: previous, γ =>
      letI (δ : Λ) : Fintype (FusionHistoryData Fam α previous δ) :=
        fusionHistoryDataFintype Fam α previous δ
      @Sigma.instFintype Λ
        (fun δ => FusionHistoryData Fam α previous δ × Fin (Fam.chi.dim δ β γ))
        _ _

/-- The left-associated fusion histories form a finite type. -/
noncomputable instance fusionHistoryFintype
    (Fam : BNTFusionCoisometryFamily Λ p) (α : Λ) (previous : List Λ) :
    Fintype (FusionHistory Fam α previous) :=
  inferInstance

/-- Equality of left-associated fusion histories is decidable. -/
noncomputable instance fusionHistoryDecidableEq
    (Fam : BNTFusionCoisometryFamily Λ p) (α : Λ) (previous : List Λ) :
    DecidableEq (FusionHistory Fam α previous) :=
  Classical.decEq _

/-- A fusion history together with the terminal bond index carried by its final label.

Source: arXiv:1606.00608, the terminal matrices in the recursive operator at lines 999--1010.
-/
abbrev FusionHistoryIndex (Fam : BNTFusionCoisometryFamily Λ p)
    (α : Λ) (previous : List Λ) : Type u :=
  (h : FusionHistory Fam α previous) ×
    Fin (Fam.bondDim (fusionHistoryFinalLabel Fam α previous h))

/-- The bond dimension of the left-associated product tensor attached to a reverse fusion list.

Source: arXiv:1606.00608, lines 999--1010. -/
def fusionChainBondDim (Fam : BNTFusionCoisometryFamily Λ p) (α : Λ) : List Λ → ℕ
  | [] => Fam.bondDim α
  | β :: previous => fusionChainBondDim Fam α previous * Fam.bondDim β

/-- The left-associated product tensor attached to a reverse fusion list.

Source: arXiv:1606.00608, recursive application of the fusion identity at lines 999--1010.
-/
noncomputable def fusionChainTensor (Fam : BNTFusionCoisometryFamily Λ p) (α : Λ) :
    (previous : List Λ) → MPOTensor p (fusionChainBondDim Fam α previous)
  | [] => Fam.tensor α
  | β :: previous => mulTensor (fusionChainTensor Fam α previous) (Fam.tensor β)

/-- The product of the diagonal structure coefficients selected by a fusion history.

Source: arXiv:1606.00608, the recursively nested structure matrices in the operator at
lines 999--1010. -/
noncomputable def fusionHistoryWeight (Fam : BNTFusionCoisometryFamily Λ p) (α : Λ) :
    (previous : List Λ) → (γ : Λ) → FusionHistoryData Fam α previous γ → ℂ
  | [], _, _ => 1
  | β :: previous, γ, ⟨δ, h, k⟩ =>
      fusionHistoryWeight Fam α previous δ h * Fam.chi.entry δ β γ k

/-- The recursive operator on the direct sum of terminal bond spaces.  Its block at a history
is the prescribed terminal matrix multiplied by every diagonal structure coefficient selected
along that history.

Source: arXiv:1606.00608, the operator $Q$ at lines 999--1010. -/
noncomputable def recursiveProjectorQ
    (Fam : BNTFusionCoisometryFamily Λ p)
    (P : ∀ γ : Λ,
      Matrix (Fin (Fam.bondDim γ)) (Fin (Fam.bondDim γ)) ℂ)
    (α : Λ) (previous : List Λ) :
    Matrix (FusionHistoryIndex Fam α previous) (FusionHistoryIndex Fam α previous) ℂ :=
  Matrix.blockDiagonal' fun h : FusionHistory Fam α previous =>
    fusionHistoryWeight Fam α previous h.1 h.2 • P h.1

/-- In the length-independent case, every coefficient accumulated along a fusion history is
one.

Source: arXiv:1606.00608, line 1010. -/
theorem fusionHistoryWeight_eq_one_of_lengthIndependent
    (Fam : BNTFusionCoisometryFamily Λ p)
    (c : BNTLabelCoefficientFamily Λ)
    (hχ : c.HasPositiveLengthChiTracePowerForm Fam.chi)
    (hLI : c.LengthIndependent) (α : Λ) :
    ∀ (previous : List Λ) (γ : Λ) (h : FusionHistoryData Fam α previous γ),
      fusionHistoryWeight Fam α previous γ h = 1
  | [], _, _ => rfl
  | β :: previous, γ, ⟨δ, h, k⟩ => by
      rw [fusionHistoryWeight,
        fusionHistoryWeight_eq_one_of_lengthIndependent Fam c hχ hLI α previous δ h,
        hχ.entry_eq_one_of_lengthIndependent Fam.posEntries hLI δ β γ k, one_mul]

/-- In the length-independent case, the recursive operator is the unweighted direct sum of
its terminal matrices.

Source: arXiv:1606.00608, lines 999--1010. -/
theorem recursiveProjectorQ_eq_unweighted
    (Fam : BNTFusionCoisometryFamily Λ p)
    (c : BNTLabelCoefficientFamily Λ)
    (hχ : c.HasPositiveLengthChiTracePowerForm Fam.chi)
    (hLI : c.LengthIndependent)
    (P : ∀ γ : Λ,
      Matrix (Fin (Fam.bondDim γ)) (Fin (Fam.bondDim γ)) ℂ)
    (α : Λ) (previous : List Λ) :
    recursiveProjectorQ Fam P α previous =
      Matrix.blockDiagonal' fun h : FusionHistory Fam α previous =>
        P (fusionHistoryFinalLabel Fam α previous h) := by
  unfold recursiveProjectorQ
  congr 1
  funext h
  rw [fusionHistoryWeight_eq_one_of_lengthIndependent Fam c hχ hLI α previous h.1 h.2,
    one_smul]

/-- In the length-independent case, the recursive operator is a self-adjoint idempotent when
each terminal matrix is a self-adjoint idempotent.

Source: arXiv:1606.00608, lines 999--1010. -/
theorem recursiveProjectorQ_isStarProjection
    (Fam : BNTFusionCoisometryFamily Λ p)
    (c : BNTLabelCoefficientFamily Λ)
    (hχ : c.HasPositiveLengthChiTracePowerForm Fam.chi)
    (hLI : c.LengthIndependent)
    (P : ∀ γ : Λ,
      Matrix (Fin (Fam.bondDim γ)) (Fin (Fam.bondDim γ)) ℂ)
    (hP : ∀ γ : Λ, IsStarProjection (P γ))
    (α : Λ) (previous : List Λ) :
    IsStarProjection (recursiveProjectorQ Fam P α previous) := by
  rw [recursiveProjectorQ_eq_unweighted Fam c hχ hLI]
  rw [isStarProjection_iff']
  constructor
  · rw [← Matrix.blockDiagonal'_mul]
    congr 1
    funext h
    exact (hP (fusionHistoryFinalLabel Fam α previous h)).isIdempotentElem.eq
  · rw [Matrix.star_eq_conjTranspose, Matrix.blockDiagonal'_conjTranspose]
    congr 1
    funext h
    simpa [Matrix.star_eq_conjTranspose] using
      (hP (fusionHistoryFinalLabel Fam α previous h)).isSelfAdjoint.star_eq

/-- The unique history at the empty fusion list identifies its terminal bond space with the
bond space of the initial label. -/
private noncomputable def emptyFusionHistoryIndexEquiv
    (Fam : BNTFusionCoisometryFamily Λ p) (α : Λ) :
    FusionHistoryIndex Fam α [] ≃ Fin (Fam.bondDim α) where
  toFun x := Fin.cast
    (congrArg Fam.bondDim (fusionHistoryFinalLabel_empty Fam α x.1)) x.2
  invFun x := ⟨⟨α, ULift.up ⟨0, by simp⟩⟩, x⟩
  left_inv := by
    rintro ⟨⟨γ, h⟩, b⟩
    have hγα := fusionHistoryFinalLabel_empty Fam α ⟨γ, h⟩
    change γ = α at hγα
    subst γ
    have hh : h = ULift.up ⟨0, by simp⟩ := by
      apply ULift.ext
      apply Fin.ext
      have hlt : h.down.val < 1 := by simpa using h.down.isLt
      exact Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hlt)
    subst h
    rfl
  right_inv := by
    intro b
    rfl

/-- With an empty appended-label list, the recursive bond dimension of the one-site
base tensor is the bond dimension of the initial label. -/
private def emptyFusionBondEquiv
    (Fam : BNTFusionCoisometryFamily Λ p) (α : Λ) :
    Fin (fusionChainBondDim Fam α []) ≃ Fin (Fam.bondDim α) :=
  Equiv.refl _

/-- Reindexing which appends the new bond coordinate to each preceding fusion history. -/
private def appendHistoryBondEquiv
    (Fam : BNTFusionCoisometryFamily Λ p) (α β : Λ) (previous : List Λ) :
    FusionHistoryIndex Fam α previous × Fin (Fam.bondDim β) ≃
      (h : FusionHistory Fam α previous) ×
        Fin (Fam.bondDim (fusionHistoryFinalLabel Fam α previous h) * Fam.bondDim β) :=
  (Equiv.sigmaProdDistrib
      (fun h : FusionHistory Fam α previous =>
        Fin (Fam.bondDim (fusionHistoryFinalLabel Fam α previous h)))
      (Fin (Fam.bondDim β))).trans
    (Equiv.sigmaCongrRight fun _ => finProdFinEquiv)

/-- Tensoring a history-indexed block diagonal matrix with a common bond matrix, then applying
the append-bond reindexing, preserves the history blocks. -/
private theorem appendHistoryBond_sum_blockDiagonal
    (Fam : BNTFusionCoisometryFamily Λ p) (α β : Λ) (previous : List Λ)
    (X : ∀ h : FusionHistory Fam α previous, Fin p →
      Matrix (Fin (Fam.bondDim (fusionHistoryFinalLabel Fam α previous h)))
        (Fin (Fam.bondDim (fusionHistoryFinalLabel Fam α previous h))) ℂ)
    (Y : Fin p → Matrix (Fin (Fam.bondDim β)) (Fin (Fam.bondDim β)) ℂ) :
    (∑ j : Fin p, (Matrix.blockDiagonal' fun h => X h j) ⊗ₖ Y j).submatrix
        (appendHistoryBondEquiv Fam α β previous).symm
        (appendHistoryBondEquiv Fam α β previous).symm =
      Matrix.blockDiagonal' fun h =>
        (∑ j : Fin p, X h j ⊗ₖ Y j).submatrix
          finProdFinEquiv.symm finProdFinEquiv.symm := by
  ext ⟨h, z⟩ ⟨h', z'⟩
  by_cases hh' : h = h'
  · subst h'
    simp [appendHistoryBondEquiv, Equiv.sigmaCongrRight_symm,
      Equiv.sigmaCongrRight_apply, Matrix.blockDiagonal'_apply_eq, Matrix.sum_apply]
  · simp [appendHistoryBondEquiv, Equiv.sigmaCongrRight_symm,
      Equiv.sigmaCongrRight_apply, Matrix.blockDiagonal'_apply_ne _ _ _ hh',
      Matrix.sum_apply]

/-- Reindexing which adjoins one fusion label and one multiplicity coordinate to a preceding
history. -/
private def appendFusionOutputEquiv
    (Fam : BNTFusionCoisometryFamily Λ p) (α β : Λ) (previous : List Λ) :
    ((h : FusionHistory Fam α previous) ×
        ((γ : Λ) × Fin (Fam.chi.dim
          (fusionHistoryFinalLabel Fam α previous h) β γ) × Fin (Fam.bondDim γ))) ≃
      FusionHistoryIndex Fam α (β :: previous) where
  toFun
    | ⟨⟨δ, h⟩, ⟨γ, k, b⟩⟩ => ⟨⟨γ, ⟨δ, h, k⟩⟩, b⟩
  invFun
    | ⟨⟨γ, ⟨δ, h, k⟩⟩, b⟩ => ⟨⟨δ, h⟩, ⟨γ, k, b⟩⟩
  left_inv := by
    rintro ⟨⟨δ, h⟩, ⟨γ, k, b⟩⟩
    rfl
  right_inv := by
    rintro ⟨⟨γ, ⟨δ, h, k⟩⟩, b⟩
    rfl

@[simp] private theorem appendFusionOutputEquiv_apply
    (Fam : BNTFusionCoisometryFamily Λ p) (α β γ : Λ) (previous : List Λ)
    (h : FusionHistory Fam α previous)
    (m : Fin (Fam.chi.dim (fusionHistoryFinalLabel Fam α previous h) β γ))
    (b : Fin (Fam.bondDim γ)) :
    appendFusionOutputEquiv Fam α β previous ⟨h, ⟨γ, m, b⟩⟩ =
      ⟨⟨γ, ⟨h.1, h.2, m⟩⟩, b⟩ :=
  rfl

@[simp] private theorem appendFusionOutputEquiv_symm_apply
    (Fam : BNTFusionCoisometryFamily Λ p) (α β δ γ : Λ) (previous : List Λ)
    (h : FusionHistoryData Fam α previous δ) (m : Fin (Fam.chi.dim δ β γ))
    (b : Fin (Fam.bondDim γ)) :
    (appendFusionOutputEquiv Fam α β previous).symm ⟨⟨γ, ⟨δ, h, m⟩⟩, b⟩ =
      ⟨⟨δ, h⟩, ⟨γ, m, b⟩⟩ :=
  rfl

/-- Flattening the nested fusion blocks after one appended label gives the recursive blocks
indexed by the extended histories. -/
private theorem appendFusionOutput_blockDiagonal
    (Fam : BNTFusionCoisometryFamily Λ p) (α β : Λ) (previous : List Λ)
    (T : ∀ γ : Λ,
      Matrix (Fin (Fam.bondDim γ)) (Fin (Fam.bondDim γ)) ℂ) :
    (Matrix.blockDiagonal' fun h : FusionHistory Fam α previous =>
        fusionHistoryWeight Fam α previous h.1 h.2 •
          Matrix.blockDiagonal' fun γ =>
            Fam.chi.matrix h.1 β γ ⊗ₖ T γ).submatrix
      (appendFusionOutputEquiv Fam α β previous).symm
      (appendFusionOutputEquiv Fam α β previous).symm =
    recursiveProjectorQ Fam T α (β :: previous) := by
  classical
  funext ⟨⟨γ, x⟩, b⟩ ⟨⟨γ', y⟩, b'⟩
  change ((δ : Λ) × FusionHistoryData Fam α previous δ ×
    Fin (Fam.chi.dim δ β γ)) at x
  change ((δ : Λ) × FusionHistoryData Fam α previous δ ×
    Fin (Fam.chi.dim δ β γ')) at y
  rcases x with ⟨δ, h, m⟩
  rcases y with ⟨δ', h', m'⟩
  change Fin (Fam.bondDim γ) at b
  change Fin (Fam.bondDim γ') at b'
  simp only [Matrix.submatrix_apply, appendFusionOutputEquiv_symm_apply]
  by_cases hh : (⟨δ, h⟩ : FusionHistory Fam α previous) = ⟨δ', h'⟩
  · cases hh
    by_cases hγ : γ = γ'
    · subst γ'
      by_cases hm : m = m'
      · subst m'
        simp only [recursiveProjectorQ, fusionHistoryWeight,
          Matrix.blockDiagonal'_apply_eq]
        simp only [Matrix.smul_apply, Matrix.blockDiagonal'_apply_eq, smul_eq_mul]
        simp [DiagonalChiFamily.matrix, Matrix.kroneckerMap_apply, mul_assoc]
      · have hext :
          (⟨δ, h, m⟩ : FusionHistoryData Fam α (β :: previous) γ) ≠ ⟨δ, h, m'⟩ := by
          intro heq
          cases heq
          exact hm rfl
        have hhistory :
            (⟨γ, ⟨δ, h, m⟩⟩ : FusionHistory Fam α (β :: previous)) ≠
              ⟨γ, ⟨δ, h, m'⟩⟩ := by
          intro heq
          cases heq
          exact hext rfl
        simp only [recursiveProjectorQ]
        rw [Matrix.blockDiagonal'_apply_eq,
          Matrix.blockDiagonal'_apply_ne _ _ _ hhistory,
          Matrix.smul_apply, Matrix.blockDiagonal'_apply_eq, smul_eq_mul]
        simp [DiagonalChiFamily.matrix, Matrix.kroneckerMap_apply, hm]
    · have hext :
          (⟨γ, ⟨δ, h, m⟩⟩ : FusionHistory Fam α (β :: previous)) ≠
            ⟨γ', ⟨δ, h, m'⟩⟩ := by
          intro heq
          exact hγ (congrArg Sigma.fst heq)
      simp only [recursiveProjectorQ]
      rw [Matrix.blockDiagonal'_apply_eq]
      rw [Matrix.smul_apply, Matrix.blockDiagonal'_apply_ne _ _ _ hγ, smul_eq_mul, mul_zero,
        Matrix.blockDiagonal'_apply_ne _ _ _ hext]
  · have hext :
        (⟨γ, ⟨δ, h, m⟩⟩ : FusionHistory Fam α (β :: previous)) ≠
          ⟨γ', ⟨δ', h', m'⟩⟩ := by
        intro heq
        cases heq
        exact hh rfl
    simp [recursiveProjectorQ, fusionHistoryFinalLabel,
      Matrix.blockDiagonal'_apply, hh, hext]

/-- The first circuit stage when a label is appended: the preceding sequential coisometry
tensored with the identity on the new bond space. -/
private noncomputable def appendFusionFirstStage
    (Fam : BNTFusionCoisometryFamily Λ p) (α β : Λ) (previous : List Λ)
    (W : Matrix (FusionHistoryIndex Fam α previous)
      (Fin (fusionChainBondDim Fam α previous)) ℂ) :
    Matrix
      ((h : FusionHistory Fam α previous) ×
        Fin (Fam.bondDim (fusionHistoryFinalLabel Fam α previous h) * Fam.bondDim β))
      (Fin (fusionChainBondDim Fam α previous * Fam.bondDim β)) ℂ :=
  (W ⊗ₖ (1 : Matrix (Fin (Fam.bondDim β)) (Fin (Fam.bondDim β)) ℂ)).submatrix
    (appendHistoryBondEquiv Fam α β previous).symm finProdFinEquiv.symm

/-- If a coisometry gives the recursive fusion blocks for every letter of a tensor, its tensor
product with the identity gives the corresponding history-indexed product letters after one
label is appended. -/
private theorem appendFusionFirstStage_apply
    (Fam : BNTFusionCoisometryFamily Λ p) (α β : Λ) (previous : List Λ)
    (A : MPOTensor p (fusionChainBondDim Fam α previous))
    (W : Matrix (FusionHistoryIndex Fam α previous)
      (Fin (fusionChainBondDim Fam α previous)) ℂ)
    (hW : ∀ i j : Fin p,
      W * A i j * Wᴴ =
        recursiveProjectorQ Fam (fun γ => Fam.tensor γ i j) α previous)
    (i k : Fin p) :
    appendFusionFirstStage Fam α β previous W * mulTensor A (Fam.tensor β) i k *
        (appendFusionFirstStage Fam α β previous W)ᴴ =
      Matrix.blockDiagonal' fun h : FusionHistory Fam α previous =>
        fusionHistoryWeight Fam α previous h.1 h.2 •
          mulTensor (Fam.tensor (fusionHistoryFinalLabel Fam α previous h))
            (Fam.tensor β) i k := by
  unfold appendFusionFirstStage
  rw [mulTensor_apply, Matrix.conjTranspose_submatrix,
    Matrix.submatrix_mul_equiv _ _ _ finProdFinEquiv.symm _,
    Matrix.submatrix_mul_equiv _ _ _ finProdFinEquiv.symm _,
    Matrix.mul_sum, Matrix.sum_mul]
  simp_rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
    Matrix.one_mul, Matrix.conjTranspose_one, Matrix.mul_one, hW]
  unfold recursiveProjectorQ
  rw [appendHistoryBond_sum_blockDiagonal]
  congr 1
  funext h
  ext x y
  simp only [Matrix.submatrix_apply, finProdFinEquiv_symm_apply, mulTensor_apply,
    Matrix.sum_apply, Matrix.smul_apply, Matrix.kroneckerMap_apply, smul_eq_mul,
    Finset.mul_sum, mul_assoc]

/-- Exact reconstruction through the first stage of an appended fusion step. -/
private theorem appendFusionFirstStage_reconstruction
    (Fam : BNTFusionCoisometryFamily Λ p) (α β : Λ) (previous : List Λ)
    (A : MPOTensor p (fusionChainBondDim Fam α previous))
    (W : Matrix (FusionHistoryIndex Fam α previous)
      (Fin (fusionChainBondDim Fam α previous)) ℂ)
    (hW : ∀ i j : Fin p,
      A i j = Wᴴ * recursiveProjectorQ Fam (fun γ => Fam.tensor γ i j) α previous * W)
    (i k : Fin p) :
    mulTensor A (Fam.tensor β) i k =
      (appendFusionFirstStage Fam α β previous W)ᴴ *
        (Matrix.blockDiagonal' fun h : FusionHistory Fam α previous =>
          fusionHistoryWeight Fam α previous h.1 h.2 •
            mulTensor (Fam.tensor (fusionHistoryFinalLabel Fam α previous h))
              (Fam.tensor β) i k) *
        appendFusionFirstStage Fam α β previous W := by
  have hdiag :
      Matrix.blockDiagonal' (fun h : FusionHistory Fam α previous =>
          fusionHistoryWeight Fam α previous h.1 h.2 •
            mulTensor (Fam.tensor (fusionHistoryFinalLabel Fam α previous h))
              (Fam.tensor β) i k) =
        (∑ j : Fin p,
          recursiveProjectorQ Fam (fun γ => Fam.tensor γ i j) α previous ⊗ₖ
            Fam.tensor β j k).submatrix
          (appendHistoryBondEquiv Fam α β previous).symm
          (appendHistoryBondEquiv Fam α β previous).symm := by
    let X := fun h : FusionHistory Fam α previous => fun j : Fin p =>
      fusionHistoryWeight Fam α previous h.1 h.2 •
        Fam.tensor (fusionHistoryFinalLabel Fam α previous h) i j
    let Y := fun j : Fin p => Fam.tensor β j k
    have hblock := appendHistoryBond_sum_blockDiagonal Fam α β previous X Y
    calc
      Matrix.blockDiagonal' (fun h : FusionHistory Fam α previous =>
          fusionHistoryWeight Fam α previous h.1 h.2 •
            mulTensor (Fam.tensor (fusionHistoryFinalLabel Fam α previous h))
              (Fam.tensor β) i k) =
          Matrix.blockDiagonal' (fun h =>
            (∑ j : Fin p, X h j ⊗ₖ Y j).submatrix
              finProdFinEquiv.symm finProdFinEquiv.symm) := by
        congr 1
        funext h
        ext x y
        simp only [X, Y, mulTensor_apply, Matrix.submatrix_apply,
          finProdFinEquiv_symm_apply, Matrix.sum_apply, Matrix.smul_apply,
          Matrix.kroneckerMap_apply, smul_eq_mul]
        simpa only [mul_comm, mul_left_comm, mul_assoc] using
          (Fintype.sum_mul_mul_eq_mul_sum_mul
            (fusionHistoryWeight Fam α previous h.1 h.2)
            (fun j => Fam.tensor β j k x.modNat y.modNat)
            (fun j => Fam.tensor (fusionHistoryFinalLabel Fam α previous h)
              i j x.divNat y.divNat)).symm
      _ = _ := by
        rw [← hblock]
        unfold recursiveProjectorQ X Y
        rfl
  unfold appendFusionFirstStage
  rw [hdiag, Matrix.conjTranspose_submatrix]
  rw [Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv,
    Matrix.mul_sum, Matrix.sum_mul]
  simp_rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
    Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one, ← hW]
  rfl

/-- The second circuit stage when a label is appended: the direct sum of the active fusion
coisometries over all preceding histories. -/
private noncomputable def appendFusionSecondStage
    (Fam : BNTFusionCoisometryFamily Λ p) (α β : Λ) (previous : List Λ) :
    Matrix (FusionHistoryIndex Fam α (β :: previous))
      ((h : FusionHistory Fam α previous) ×
        Fin (Fam.bondDim (fusionHistoryFinalLabel Fam α previous h) * Fam.bondDim β)) ℂ :=
  (Matrix.blockDiagonal' fun h : FusionHistory Fam α previous =>
      Fam.fusionCoisometry (fusionHistoryFinalLabel Fam α previous h) β).submatrix
    (appendFusionOutputEquiv Fam α β previous).symm (Equiv.refl _)

/-- The second append stage applies the fusion identity in every preceding-history block and
thereby produces the recursive blocks indexed by the extended histories. -/
private theorem appendFusionSecondStage_apply
    (Fam : BNTFusionCoisometryFamily Λ p) (α β : Λ) (previous : List Λ)
    (i k : Fin p) :
    appendFusionSecondStage Fam α β previous *
        (Matrix.blockDiagonal' fun h : FusionHistory Fam α previous =>
          fusionHistoryWeight Fam α previous h.1 h.2 •
            mulTensor (Fam.tensor (fusionHistoryFinalLabel Fam α previous h))
              (Fam.tensor β) i k) *
        (appendFusionSecondStage Fam α β previous)ᴴ =
      recursiveProjectorQ Fam (fun γ => Fam.tensor γ i k) α (β :: previous) := by
  unfold appendFusionSecondStage
  rw [Matrix.conjTranspose_submatrix]
  rw [show
    (Matrix.blockDiagonal' fun h : FusionHistory Fam α previous =>
      fusionHistoryWeight Fam α previous h.1 h.2 •
        mulTensor (Fam.tensor (fusionHistoryFinalLabel Fam α previous h))
          (Fam.tensor β) i k) =
      (Matrix.blockDiagonal' fun h : FusionHistory Fam α previous =>
        fusionHistoryWeight Fam α previous h.1 h.2 •
          mulTensor (Fam.tensor (fusionHistoryFinalLabel Fam α previous h))
            (Fam.tensor β) i k).submatrix (Equiv.refl _) (Equiv.refl _) by
      rfl]
  rw [
    Matrix.submatrix_mul_equiv _ _ _ (Equiv.refl _) _,
    Matrix.submatrix_mul_equiv _ _ _ (Equiv.refl _) _,
    Matrix.blockDiagonal'_conjTranspose, ← Matrix.blockDiagonal'_mul,
    ← Matrix.blockDiagonal'_mul]
  have hBlocks :
      (Matrix.blockDiagonal' fun h : FusionHistory Fam α previous =>
        Fam.fusionCoisometry (fusionHistoryFinalLabel Fam α previous h) β *
          (fusionHistoryWeight Fam α previous h.1 h.2 •
            mulTensor (Fam.tensor (fusionHistoryFinalLabel Fam α previous h))
              (Fam.tensor β) i k) *
          (Fam.fusionCoisometry (fusionHistoryFinalLabel Fam α previous h) β)ᴴ) =
        Matrix.blockDiagonal' fun h : FusionHistory Fam α previous =>
          fusionHistoryWeight Fam α previous h.1 h.2 •
            Matrix.blockDiagonal' fun γ =>
              Fam.chi.matrix (fusionHistoryFinalLabel Fam α previous h) β γ ⊗ₖ
                Fam.tensor γ i k := by
    apply congrArg Matrix.blockDiagonal'
    funext h
    rw [Matrix.mul_smul, Matrix.smul_mul, Fam.fusion]
  rw [hBlocks]
  exact appendFusionOutput_blockDiagonal Fam α β previous
    (fun γ => Fam.tensor γ i k)

/-- Exact reconstruction through the second stage of an appended fusion step. -/
private theorem appendFusionSecondStage_reconstruction
    (Fam : BNTFusionCoisometryFamily Λ p) (α β : Λ) (previous : List Λ)
    (i k : Fin p) :
    (Matrix.blockDiagonal' fun h : FusionHistory Fam α previous =>
        fusionHistoryWeight Fam α previous h.1 h.2 •
          mulTensor (Fam.tensor (fusionHistoryFinalLabel Fam α previous h))
            (Fam.tensor β) i k) =
      (appendFusionSecondStage Fam α β previous)ᴴ *
        recursiveProjectorQ Fam (fun γ => Fam.tensor γ i k) α (β :: previous) *
        appendFusionSecondStage Fam α β previous := by
  have hQ := appendFusionOutput_blockDiagonal Fam α β previous
    (fun γ => Fam.tensor γ i k)
  unfold appendFusionSecondStage
  rw [← hQ, Matrix.conjTranspose_submatrix,
    Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv]
  change (Matrix.blockDiagonal' fun h : FusionHistory Fam α previous =>
      fusionHistoryWeight Fam α previous h.1 h.2 •
        mulTensor (Fam.tensor (fusionHistoryFinalLabel Fam α previous h))
          (Fam.tensor β) i k) =
    (Matrix.blockDiagonal' fun h : FusionHistory Fam α previous =>
      Fam.fusionCoisometry (fusionHistoryFinalLabel Fam α previous h) β)ᴴ *
      (Matrix.blockDiagonal' fun h : FusionHistory Fam α previous =>
        fusionHistoryWeight Fam α previous h.1 h.2 •
          Matrix.blockDiagonal' fun γ =>
            Fam.chi.matrix h.1 β γ ⊗ₖ Fam.tensor γ i k) *
      Matrix.blockDiagonal' fun h : FusionHistory Fam α previous =>
        Fam.fusionCoisometry (fusionHistoryFinalLabel Fam α previous h) β
  rw [Matrix.blockDiagonal'_conjTranspose,
    ← Matrix.blockDiagonal'_mul, ← Matrix.blockDiagonal'_mul]
  congr 1
  funext h
  rw [Matrix.mul_smul, Matrix.smul_mul, Fam.reconstruction]

/-- The sequential active fusion coisometry for a left-associated chain.

Source: arXiv:1606.00608, the sequential circuit $\widetilde U_N$ at lines 999--1010. -/
noncomputable def sequentialFusionCoisometry
    (Fam : BNTFusionCoisometryFamily Λ p) (α : Λ) :
    (previous : List Λ) → Matrix (FusionHistoryIndex Fam α previous)
      (Fin (fusionChainBondDim Fam α previous)) ℂ
  | [] => (1 : Matrix (Fin (Fam.bondDim α)) (Fin (Fam.bondDim α)) ℂ).submatrix
      (emptyFusionHistoryIndexEquiv Fam α) (emptyFusionBondEquiv Fam α)
  | β :: previous =>
      appendFusionSecondStage Fam α β previous *
        appendFusionFirstStage Fam α β previous
          (sequentialFusionCoisometry Fam α previous)

/-- Tensoring a coisometry with the identity and applying the canonical bond reindexings again
gives a coisometry. -/
private theorem appendFusionFirstStage_mul_conjTranspose
    (Fam : BNTFusionCoisometryFamily Λ p) (α β : Λ) (previous : List Λ)
    (W : Matrix (FusionHistoryIndex Fam α previous)
      (Fin (fusionChainBondDim Fam α previous)) ℂ)
    (hW : W * Wᴴ = 1) :
    appendFusionFirstStage Fam α β previous W *
        (appendFusionFirstStage Fam α β previous W)ᴴ = 1 := by
  unfold appendFusionFirstStage
  rw [Matrix.conjTranspose_submatrix,
    Matrix.submatrix_mul_equiv _ _ _ finProdFinEquiv.symm _,
    Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul, hW,
    Matrix.conjTranspose_one, Matrix.mul_one, Matrix.one_kronecker_one,
    Matrix.submatrix_one_equiv]

/-- The direct sum of the active fusion coisometries, followed by the history reindexing, is a
coisometry. -/
private theorem appendFusionSecondStage_mul_conjTranspose
    (Fam : BNTFusionCoisometryFamily Λ p) (α β : Λ) (previous : List Λ) :
    appendFusionSecondStage Fam α β previous *
        (appendFusionSecondStage Fam α β previous)ᴴ = 1 := by
  unfold appendFusionSecondStage
  rw [Matrix.conjTranspose_submatrix,
    Matrix.submatrix_mul_equiv _ _ _ (Equiv.refl _) _,
    Matrix.blockDiagonal'_conjTranspose, ← Matrix.blockDiagonal'_mul]
  simp_rw [Fam.coisometry]
  calc
    _ = (1 : Matrix _ _ ℂ).submatrix
        (appendFusionOutputEquiv Fam α β previous).symm
        (appendFusionOutputEquiv Fam α β previous).symm := by
      congr 1
      exact Matrix.blockDiagonal'_one
    _ = 1 := Matrix.submatrix_one_equiv _

/-- The sequential active fusion map is a coisometry onto the direct sum indexed by complete
fusion histories.

Source: arXiv:1606.00608, the sequential circuit $\widetilde U_N$ at lines 999--1010.

**Local fix (active fusion orientation):** Each factor uses the retained-row coisometry
orientation recorded in `docs/paper-gaps/cpsv16_figure11_fusion_coisometry.tex`. -/
theorem sequentialFusionCoisometry_mul_conjTranspose
    (Fam : BNTFusionCoisometryFamily Λ p) (α : Λ) :
    ∀ previous : List Λ,
      sequentialFusionCoisometry Fam α previous *
          (sequentialFusionCoisometry Fam α previous)ᴴ = 1
  | [] => by
      ext x y
      simp only [sequentialFusionCoisometry, Matrix.mul_apply]
      rw [Finset.sum_eq_single
        ((emptyFusionBondEquiv Fam α).symm ((emptyFusionHistoryIndexEquiv Fam α) x))]
      · simp [Matrix.one_apply, eq_comm]
      · intro z _ hz
        simp only [Matrix.submatrix_apply, Matrix.conjTranspose_apply,
          RCLike.star_def, mul_eq_zero, map_eq_zero]
        left
        simp only [Matrix.one_apply, ite_eq_right_iff]
        intro hxz
        exfalso
        apply hz
        apply (emptyFusionBondEquiv Fam α).injective
        simpa using hxz.symm
      · simp
  | β :: previous => by
      let W := sequentialFusionCoisometry Fam α previous
      let F := appendFusionFirstStage Fam α β previous W
      let S := appendFusionSecondStage Fam α β previous
      change (S * F) * (S * F)ᴴ = 1
      rw [Matrix.conjTranspose_mul]
      calc
        (S * F) * (Fᴴ * Sᴴ) = S * (F * Fᴴ) * Sᴴ := by
          simp only [Matrix.mul_assoc]
        _ = S * Sᴴ := by
          rw [appendFusionFirstStage_mul_conjTranspose Fam α β previous W
            (sequentialFusionCoisometry_mul_conjTranspose Fam α previous)]
          rw [Matrix.mul_one]
        _ = 1 := appendFusionSecondStage_mul_conjTranspose Fam α β previous

/-- At the empty fusion list, the recursive block is the initial terminal matrix expressed in
the history coordinates. -/
private theorem recursiveProjectorQ_empty
    (Fam : BNTFusionCoisometryFamily Λ p) (α : Λ)
    (T : ∀ γ : Λ,
      Matrix (Fin (Fam.bondDim γ)) (Fin (Fam.bondDim γ)) ℂ) :
    recursiveProjectorQ Fam T α [] =
      (T α).submatrix (emptyFusionHistoryIndexEquiv Fam α)
        (emptyFusionHistoryIndexEquiv Fam α) := by
  let e := emptyFusionHistoryIndexEquiv Fam α
  funext x y
  calc
    recursiveProjectorQ Fam T α [] x y =
        recursiveProjectorQ Fam T α [] (e.symm (e x)) (e.symm (e y)) := by
      rw [e.symm_apply_apply, e.symm_apply_apply]
    _ = T α (e x) (e y) := by
      simp [recursiveProjectorQ, fusionHistoryWeight, e,
        emptyFusionHistoryIndexEquiv, Matrix.blockDiagonal'_apply_eq]
    _ = (T α).submatrix (emptyFusionHistoryIndexEquiv Fam α)
          (emptyFusionHistoryIndexEquiv Fam α) x y :=
      rfl

/-- The sequential fusion coisometry carries each product letter to the corresponding
recursive history block.

Source: arXiv:1606.00608, the recursive operator and sequential circuit at lines 999--1010.

**Local fix (Figure-11 fusion coisometry):** The source embedding is the adjoint of the
retained-row coisometry used here.  See
`docs/paper-gaps/cpsv16_figure11_fusion_coisometry.tex`.
-/
theorem sequentialFusionCoisometry_mul_fusionChainTensor_mul_conjTranspose
    (Fam : BNTFusionCoisometryFamily Λ p) (α : Λ) :
    ∀ (previous : List Λ) (i k : Fin p),
      sequentialFusionCoisometry Fam α previous * fusionChainTensor Fam α previous i k *
          (sequentialFusionCoisometry Fam α previous)ᴴ =
        recursiveProjectorQ Fam (fun γ => Fam.tensor γ i k) α previous
  | [], i, k => by
      unfold sequentialFusionCoisometry fusionChainTensor
      rw [show Fam.tensor α i k =
        (Fam.tensor α i k).submatrix (emptyFusionBondEquiv Fam α)
          (emptyFusionBondEquiv Fam α) by rfl]
      rw [Matrix.conjTranspose_submatrix,
        Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv,
        Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
      exact (recursiveProjectorQ_empty Fam α (fun γ => Fam.tensor γ i k)).symm
  | β :: previous, i, k => by
      let W := sequentialFusionCoisometry Fam α previous
      let F := appendFusionFirstStage Fam α β previous W
      let S := appendFusionSecondStage Fam α β previous
      change (S * F) *
          mulTensor (fusionChainTensor Fam α previous) (Fam.tensor β) i k *
          (S * F)ᴴ =
        recursiveProjectorQ Fam (fun γ => Fam.tensor γ i k) α (β :: previous)
      rw [Matrix.conjTranspose_mul]
      calc
        (S * F) *
              mulTensor (fusionChainTensor Fam α previous) (Fam.tensor β) i k *
              (Fᴴ * Sᴴ) =
            S * (F *
              mulTensor (fusionChainTensor Fam α previous) (Fam.tensor β) i k * Fᴴ) *
              Sᴴ := by
          simp only [Matrix.mul_assoc]
        _ = S *
              (Matrix.blockDiagonal' fun h : FusionHistory Fam α previous =>
                fusionHistoryWeight Fam α previous h.1 h.2 •
                  mulTensor (Fam.tensor (fusionHistoryFinalLabel Fam α previous h))
                    (Fam.tensor β) i k) * Sᴴ := by
          rw [appendFusionFirstStage_apply Fam α β previous
            (fusionChainTensor Fam α previous) W
            (sequentialFusionCoisometry_mul_fusionChainTensor_mul_conjTranspose
              Fam α previous)]
        _ = recursiveProjectorQ Fam (fun γ => Fam.tensor γ i k) α (β :: previous) :=
          appendFusionSecondStage_apply Fam α β previous i k

/-- The sequential fusion coisometry reconstructs every product letter from the recursive
history blocks.

Source: arXiv:1606.00608, the recursive operator and sequential circuit at lines 999--1010,
and Appendix C.4, lines 2020--2029.

**Local fix (Figure-11 fusion coisometry):** Exact reverse fusion uses the active-support
reconstruction, with the source embedding equal to the adjoint of the retained-row coisometry.
See `docs/paper-gaps/cpsv16_figure11_fusion_coisometry.tex`.
-/
theorem fusionChainTensor_eq_conjTranspose_mul_recursiveProjectorQ_mul
    (Fam : BNTFusionCoisometryFamily Λ p) (α : Λ) :
    ∀ (previous : List Λ) (i k : Fin p),
      fusionChainTensor Fam α previous i k =
        (sequentialFusionCoisometry Fam α previous)ᴴ *
          recursiveProjectorQ Fam (fun γ => Fam.tensor γ i k) α previous *
          sequentialFusionCoisometry Fam α previous
  | [], i, k => by
      unfold sequentialFusionCoisometry fusionChainTensor
      rw [recursiveProjectorQ_empty]
      rw [Matrix.conjTranspose_submatrix,
        Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv,
        Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
      rfl
  | β :: previous, i, k => by
      let W := sequentialFusionCoisometry Fam α previous
      let F := appendFusionFirstStage Fam α β previous W
      let S := appendFusionSecondStage Fam α β previous
      change mulTensor (fusionChainTensor Fam α previous) (Fam.tensor β) i k =
        (S * F)ᴴ * recursiveProjectorQ Fam (fun γ => Fam.tensor γ i k) α
          (β :: previous) * (S * F)
      rw [Matrix.conjTranspose_mul]
      calc
        mulTensor (fusionChainTensor Fam α previous) (Fam.tensor β) i k =
            Fᴴ *
              (Matrix.blockDiagonal' fun h : FusionHistory Fam α previous =>
                fusionHistoryWeight Fam α previous h.1 h.2 •
                  mulTensor (Fam.tensor (fusionHistoryFinalLabel Fam α previous h))
                    (Fam.tensor β) i k) * F :=
          appendFusionFirstStage_reconstruction Fam α β previous
            (fusionChainTensor Fam α previous) W
            (fusionChainTensor_eq_conjTranspose_mul_recursiveProjectorQ_mul
              Fam α previous) i k
        _ = Fᴴ * (Sᴴ *
              recursiveProjectorQ Fam (fun γ => Fam.tensor γ i k) α
                (β :: previous) * S) * F := by
          rw [appendFusionSecondStage_reconstruction Fam α β previous i k]
        _ = (Fᴴ * Sᴴ) *
              recursiveProjectorQ Fam (fun γ => Fam.tensor γ i k) α
                (β :: previous) * (S * F) := by
          simp only [Matrix.mul_assoc]

/-- Closing the physical operator letter after sequential fusion gives the recursive operator
whose terminal blocks are the fixed-label physical-trace transfers.

Source: arXiv:1606.00608, the terminal matrices in the recursive operator at lines 999--1010.
-/
theorem sequentialFusionCoisometry_mul_physTraceTransfer_mul_conjTranspose
    (Fam : BNTFusionCoisometryFamily Λ p) (α : Λ) (previous : List Λ) :
    sequentialFusionCoisometry Fam α previous *
          physTraceTransfer (fusionChainTensor Fam α previous) *
          (sequentialFusionCoisometry Fam α previous)ᴴ =
      recursiveProjectorQ Fam (fun γ => physTraceTransfer (Fam.tensor γ)) α previous := by
  rw [physTraceTransfer, Matrix.mul_sum, Matrix.sum_mul]
  simp_rw [sequentialFusionCoisometry_mul_fusionChainTensor_mul_conjTranspose Fam α]
  unfold recursiveProjectorQ physTraceTransfer
  ext ⟨h, b⟩ ⟨h', b'⟩
  by_cases hh : h = h'
  · subst h'
    simp only [Matrix.sum_apply, Matrix.blockDiagonal'_apply_eq, Matrix.smul_apply,
      Finset.smul_sum]
  · simp only [Matrix.sum_apply, Matrix.blockDiagonal'_apply_ne _ _ _ hh,
      Finset.sum_const_zero]

/-- The physical-trace transfer of a product chain is reconstructed from the recursively
fused terminal transfers.

Source: arXiv:1606.00608, the terminal matrices and sequential circuit at lines 999--1010,
and Appendix C.4, lines 2020--2029.

**Local fix (Figure-11 fusion coisometry):** Exact reverse fusion uses the active-support
reconstruction, with the source embedding equal to the adjoint of the retained-row coisometry.
See `docs/paper-gaps/cpsv16_figure11_fusion_coisometry.tex`.
-/
theorem physTraceTransfer_fusionChainTensor_eq_conjTranspose_mul_recursiveProjectorQ_mul
    (Fam : BNTFusionCoisometryFamily Λ p) (α : Λ) (previous : List Λ) :
    physTraceTransfer (fusionChainTensor Fam α previous) =
      (sequentialFusionCoisometry Fam α previous)ᴴ *
        recursiveProjectorQ Fam (fun γ => physTraceTransfer (Fam.tensor γ)) α previous *
        sequentialFusionCoisometry Fam α previous := by
  have hQ :
      (∑ i : Fin p,
        recursiveProjectorQ Fam (fun γ => Fam.tensor γ i i) α previous) =
        recursiveProjectorQ Fam (fun γ => physTraceTransfer (Fam.tensor γ)) α previous := by
    unfold recursiveProjectorQ physTraceTransfer
    ext ⟨h, b⟩ ⟨h', b'⟩
    by_cases hh : h = h'
    · subst h'
      simp only [Matrix.sum_apply, Matrix.blockDiagonal'_apply_eq, Matrix.smul_apply,
        Finset.smul_sum]
    · simp only [Matrix.sum_apply, Matrix.blockDiagonal'_apply_ne _ _ _ hh,
        Finset.sum_const_zero]
  rw [physTraceTransfer]
  simp_rw [fusionChainTensor_eq_conjTranspose_mul_recursiveProjectorQ_mul Fam α]
  rw [← hQ, Matrix.mul_sum, Matrix.sum_mul]

end MPOTensor.BNTFusionCoisometryFamily
