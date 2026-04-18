/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.Channel.Peripheral.Spectrum
import TNLean.Channel.Peripheral.ClosureFixedPoint
import TNLean.Channel.Peripheral.PeriodicityRemoval
import TNLean.Channel.Schwarz.Basic
import TNLean.QPF.Uniqueness
import Mathlib.Analysis.CStarAlgebra.Projection
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# Cyclic decomposition of periodic irreducible channels

This file formalizes the algebraic pieces of Wolf, *Quantum Channels & Operations*,
Theorem 6.6, for transfer maps of Kraus families.

The arguments are organized in three steps:

1. a peripheral eigenvector of an irreducible unital Schwarz map can be normalized to a
   unitary;
2. a finite-order peripheral unitary admits spectral projections that are cyclically permuted by
   the channel;
3. the `m`-th power of the channel preserves each cyclic sector, and abstract irreducibility /
   primitivity hypotheses can be transferred to the resulting corner restrictions.

To keep the statements algebraic, the peripheral cycle is represented by an abstract primitive
root `γ` with `IsPrimitiveRoot γ m` rather than by the analytic expression
`Complex.exp (2 * π * Complex.I / m)`.
-/

open scoped Matrix ComplexOrder MatrixOrder BigOperators
open Matrix Finset Complex

/-- The ambient matrix algebra `M_D(ℂ)`. -/
abbrev MatrixAlg (D : ℕ) := Matrix (Fin D) (Fin D) ℂ

/-- Linear endomorphisms of `M_D(ℂ)`. -/
abbrev MatrixEnd (D : ℕ) := MatrixAlg D →ₗ[ℂ] MatrixAlg D

/-- `T` preserves the corner algebra `P · M_D(ℂ) · P`. -/
def PreservesCorner {D : ℕ} (P : MatrixAlg D) (T : MatrixEnd D) : Prop :=
  ∀ X : MatrixAlg D, P * T (P * X * P) * P = T (P * X * P)

/-- The corner algebra `P · M_D(ℂ) · P`, viewed as a `ℂ`-submodule of the ambient matrix
algebra. -/
def cornerSubmodule {D : ℕ} (P : MatrixAlg D) : Submodule ℂ (MatrixAlg D) where
  carrier := {X | P * X * P = X}
  zero_mem' := by simp only [Set.mem_setOf_eq, mul_zero, zero_mul]
  add_mem' {X Y} hX hY := by
    have hX' : P * X * P = X := by simpa using hX
    have hY' : P * Y * P = Y := by simpa using hY
    calc
      P * (X + Y) * P = P * X * P + P * Y * P := by
        simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
      _ = X + Y := by simp only [hX', hY']
  smul_mem' c X hX := by
    have hX' : P * X * P = X := by simpa using hX
    calc
      P * (c • X) * P = c • (P * X * P) := by
        rw [Matrix.mul_smul, smul_mul_assoc, Matrix.mul_assoc]
      _ = c • X := by simp only [hX']

/-- Restriction of `T` to an invariant corner `P · M_D(ℂ) · P`. -/
def cornerRestriction {D : ℕ} (P : MatrixAlg D) (T : MatrixEnd D)
    (hInv : PreservesCorner P T) :
    cornerSubmodule P →ₗ[ℂ] cornerSubmodule P where
  toFun X := ⟨T X.1, by
    have hX : P * X.1 * P = X.1 := by
      exact X.2
    simpa [hX] using hInv X.1⟩
  map_add' X Y := by
    apply Subtype.ext
    ext i j
    simp only [Submodule.coe_add, map_add, add_apply]
  map_smul' c X := by
    apply Subtype.ext
    ext i j
    simp only [SetLike.val_smul, map_smul, smul_apply, smul_eq_mul, RingHom.id_apply]

/-- Ambient reformulation of irreducibility for the restriction of `T` to the corner
`P · M_D(ℂ) · P`. -/
def IsIrreducibleOnCorner {D : ℕ} (P : MatrixAlg D) (T : MatrixEnd D) : Prop :=
  ∀ Q : MatrixAlg D,
    IsOrthogonalProjection Q →
    Q * P = Q →
    P * Q = Q →
    PreservesCorner Q T →
    Q = 0 ∨ Q = P

/-- Shared ambient compression map used to represent `M_n(ℂ)` inside a projection corner. -/
noncomputable def cornerCompressionExpand
    {D n : ℕ} (Umat : MatrixAlg D)
    {S T : Type*} [Fintype S] [DecidableEq S] [Fintype T] [DecidableEq T]
    (eST : Fin D ≃ S ⊕ T) (eS : S ≃ Fin n) :
    Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] MatrixAlg D :=
  let fromBlocksTL : Matrix S S ℂ →ₗ[ℂ] Matrix (S ⊕ T) (S ⊕ T) ℂ :=
    { toFun := fun M => Matrix.fromBlocks M 0 0 0
      map_add' := fun M₁ M₂ => by
        ext i j; cases i <;> cases j <;> simp [Matrix.fromBlocks, Matrix.add_apply]
      map_smul' := fun c M => by
        ext i j; cases i <;> cases j <;> simp [Matrix.fromBlocks, Matrix.smul_apply] }
  let conjUmat : MatrixAlg D →ₗ[ℂ] MatrixAlg D :=
    { toFun := fun Y => Umat * Y * Umatᴴ
      map_add' := fun Y₁ Y₂ => by simp [Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun c Y => by simp }
  conjUmat ∘ₗ
    (Matrix.reindexLinearEquiv ℂ ℂ eST.symm eST.symm).toLinearMap ∘ₗ
    fromBlocksTL ∘ₗ
    (Matrix.reindexLinearEquiv ℂ ℂ eS.symm eS.symm).toLinearMap

lemma cornerCompressionExpand_apply
    {D n : ℕ} (Umat : MatrixAlg D)
    {S T : Type*} [Fintype S] [DecidableEq S] [Fintype T] [DecidableEq T]
    (eST : Fin D ≃ S ⊕ T) (eS : S ≃ Fin n)
    (M : Matrix (Fin n) (Fin n) ℂ) :
    cornerCompressionExpand Umat eST eS M =
      Umat *
        Matrix.reindexLinearEquiv ℂ ℂ eST.symm eST.symm
          (Matrix.fromBlocks (Matrix.reindexLinearEquiv ℂ ℂ eS.symm eS.symm M)
            (0 : Matrix S T ℂ) (0 : Matrix T S ℂ) (0 : Matrix T T ℂ)) * Umatᴴ := rfl

lemma cornerCompressionExpand_mem
    {D n : ℕ} (P Pdiag Umat : MatrixAlg D)
    {S T : Type*} [Fintype S] [DecidableEq S] [Fintype T] [DecidableEq T]
    (eST : Fin D ≃ S ⊕ T) (eS : S ≃ Fin n)
    (P0 : Matrix (S ⊕ T) (S ⊕ T) ℂ)
    (hP0 : P0 = Matrix.fromBlocks (1 : Matrix S S ℂ) 0 0 (0 : Matrix T T ℂ))
    (hP_decomp : P = Umat * Pdiag * Umatᴴ)
    (hPdiag_back : Matrix.reindexLinearEquiv ℂ ℂ eST.symm eST.symm P0 = Pdiag)
    (hU'U : Umatᴴ * Umat = 1) :
    ∀ M : Matrix (Fin n) (Fin n) ℂ,
      P * cornerCompressionExpand Umat eST eS M * P =
        cornerCompressionExpand Umat eST eS M := by
  intro M
  rw [cornerCompressionExpand_apply Umat eST eS M]
  set Y_ST : Matrix (S ⊕ T) (S ⊕ T) ℂ :=
    Matrix.fromBlocks (Matrix.reindexLinearEquiv ℂ ℂ eS.symm eS.symm M)
      (0 : Matrix S T ℂ) (0 : Matrix T S ℂ) (0 : Matrix T T ℂ)
  set Y_D : MatrixAlg D := Matrix.reindexLinearEquiv ℂ ℂ eST.symm eST.symm Y_ST
  have hP0_Y : P0 * Y_ST * P0 = Y_ST := by
    rw [hP0]
    simp [Y_ST, Matrix.fromBlocks_multiply]
  have hPdiag_Y : Pdiag * Y_D * Pdiag = Y_D := by
    calc
      Pdiag * Y_D * Pdiag
          = Matrix.reindexLinearEquiv ℂ ℂ eST.symm eST.symm P0 *
              Matrix.reindexLinearEquiv ℂ ℂ eST.symm eST.symm Y_ST *
              Matrix.reindexLinearEquiv ℂ ℂ eST.symm eST.symm P0 := by
            rw [hPdiag_back]
      _ = Matrix.reindexLinearEquiv ℂ ℂ eST.symm eST.symm (P0 * Y_ST) *
              Matrix.reindexLinearEquiv ℂ ℂ eST.symm eST.symm P0 := by
            rw [Matrix.reindexLinearEquiv_mul (R := ℂ) (A := ℂ)
              eST.symm eST.symm eST.symm P0 Y_ST]
      _ = Matrix.reindexLinearEquiv ℂ ℂ eST.symm eST.symm (P0 * Y_ST * P0) := by
            rw [Matrix.reindexLinearEquiv_mul (R := ℂ) (A := ℂ)
              eST.symm eST.symm eST.symm (P0 * Y_ST) P0]
      _ = Matrix.reindexLinearEquiv ℂ ℂ eST.symm eST.symm Y_ST := by rw [hP0_Y]
      _ = Y_D := rfl
  change P * (Umat * Y_D * Umatᴴ) * P = Umat * Y_D * Umatᴴ
  calc
    P * (Umat * Y_D * Umatᴴ) * P
        = (Umat * Pdiag * Umatᴴ) * (Umat * Y_D * Umatᴴ) *
            (Umat * Pdiag * Umatᴴ) := by rw [← hP_decomp]
    _ = Umat * (Pdiag * (Umatᴴ * Umat) * Y_D * (Umatᴴ * Umat) * Pdiag) * Umatᴴ := by
          simp [Matrix.mul_assoc]
    _ = Umat * (Pdiag * Y_D * Pdiag) * Umatᴴ := by rw [hU'U]; simp
    _ = Umat * Y_D * Umatᴴ := by rw [hPdiag_Y]

/-- Conjugate-transpose intertwining for the shared corner-compression map:
`expand Mᴴ = (expand M)ᴴ`. This is the star-preservation identity of the
compression isometry; together with `cornerCompressionExpand_mul` it makes the
image of the compression a ∗-subalgebra of the ambient corner. -/
lemma cornerCompressionExpand_conjTranspose
    {D n : ℕ} (Umat : MatrixAlg D)
    {S T : Type*} [Fintype S] [DecidableEq S] [Fintype T] [DecidableEq T]
    (eST : Fin D ≃ S ⊕ T) (eS : S ≃ Fin n)
    (M : Matrix (Fin n) (Fin n) ℂ) :
    (cornerCompressionExpand Umat eST eS M)ᴴ =
      cornerCompressionExpand Umat eST eS Mᴴ := by
  rw [cornerCompressionExpand_apply Umat eST eS M,
    cornerCompressionExpand_apply Umat eST eS Mᴴ]
  simp only [Matrix.reindexLinearEquiv_apply]
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  congr 1
  rw [Matrix.conjTranspose_reindex, Matrix.fromBlocks_conjTranspose,
    Matrix.conjTranspose_zero, Matrix.conjTranspose_zero,
    Matrix.conjTranspose_zero, Matrix.conjTranspose_reindex]

/-- Multiplicativity of the shared corner-compression map:
`expand (M₁ * M₂) = expand M₁ * expand M₂`.  Uses the isometry identity
`Umatᴴ * Umat = 1` to collapse the middle factor of the product. -/
lemma cornerCompressionExpand_mul
    {D n : ℕ} (Umat : MatrixAlg D)
    {S T : Type*} [Fintype S] [DecidableEq S] [Fintype T] [DecidableEq T]
    (eST : Fin D ≃ S ⊕ T) (eS : S ≃ Fin n)
    (hU'U : Umatᴴ * Umat = 1)
    (M₁ M₂ : Matrix (Fin n) (Fin n) ℂ) :
    cornerCompressionExpand Umat eST eS (M₁ * M₂) =
      cornerCompressionExpand Umat eST eS M₁ *
        cornerCompressionExpand Umat eST eS M₂ := by
  rw [cornerCompressionExpand_apply Umat eST eS (M₁ * M₂),
    cornerCompressionExpand_apply Umat eST eS M₁,
    cornerCompressionExpand_apply Umat eST eS M₂]
  simp only [Matrix.reindexLinearEquiv_apply]
  set Y₁ : MatrixAlg D :=
    Matrix.reindex eST.symm eST.symm
      (Matrix.fromBlocks (Matrix.reindex eS.symm eS.symm M₁)
        (0 : Matrix S T ℂ) (0 : Matrix T S ℂ) (0 : Matrix T T ℂ))
  set Y₂ : MatrixAlg D :=
    Matrix.reindex eST.symm eST.symm
      (Matrix.fromBlocks (Matrix.reindex eS.symm eS.symm M₂)
        (0 : Matrix S T ℂ) (0 : Matrix T S ℂ) (0 : Matrix T T ℂ))
  have hY₁Y₂ :
      Matrix.reindex eST.symm eST.symm
          (Matrix.fromBlocks
            (Matrix.reindex eS.symm eS.symm (M₁ * M₂))
            (0 : Matrix S T ℂ) (0 : Matrix T S ℂ) (0 : Matrix T T ℂ)) =
        Y₁ * Y₂ := by
    have hReindexMul :
        Matrix.reindex eS.symm eS.symm M₁ *
            Matrix.reindex eS.symm eS.symm M₂ =
          Matrix.reindex eS.symm eS.symm (M₁ * M₂) := by
      simpa using
        Matrix.reindexLinearEquiv_mul (R := ℂ) (A := ℂ)
          eS.symm eS.symm eS.symm M₁ M₂
    have hFromBlocksMul :
        Matrix.fromBlocks (Matrix.reindex eS.symm eS.symm M₁)
            (0 : Matrix S T ℂ) (0 : Matrix T S ℂ) (0 : Matrix T T ℂ) *
          Matrix.fromBlocks (Matrix.reindex eS.symm eS.symm M₂)
            (0 : Matrix S T ℂ) (0 : Matrix T S ℂ) (0 : Matrix T T ℂ) =
          Matrix.fromBlocks
            (Matrix.reindex eS.symm eS.symm M₁ *
              Matrix.reindex eS.symm eS.symm M₂)
            (0 : Matrix S T ℂ) (0 : Matrix T S ℂ) (0 : Matrix T T ℂ) := by
      simp [Matrix.fromBlocks_multiply]
    have hReindexMul2 :
        Y₁ * Y₂ =
          Matrix.reindex eST.symm eST.symm
            (Matrix.fromBlocks (Matrix.reindex eS.symm eS.symm M₁)
              (0 : Matrix S T ℂ) (0 : Matrix T S ℂ) (0 : Matrix T T ℂ) *
            Matrix.fromBlocks (Matrix.reindex eS.symm eS.symm M₂)
              (0 : Matrix S T ℂ) (0 : Matrix T S ℂ) (0 : Matrix T T ℂ)) := by
      simpa [Y₁, Y₂] using
        (Matrix.reindexLinearEquiv_mul (R := ℂ) (A := ℂ)
          eST.symm eST.symm eST.symm _ _).symm
    rw [hReindexMul2, hFromBlocksMul, hReindexMul]
  rw [hY₁Y₂]
  calc
    Umat * (Y₁ * Y₂) * Umatᴴ
        = Umat * Y₁ * (Umatᴴ * Umat) * Y₂ * Umatᴴ := by
          rw [hU'U]
          simp [Matrix.mul_assoc]
    _ = Umat * Y₁ * Umatᴴ * (Umat * Y₂ * Umatᴴ) := by
          simp [Matrix.mul_assoc]

/-- Shared corner-compression builder landing in `cornerSubmodule P`. -/
noncomputable def cornerCompressionLinearMap
    {D n : ℕ} (P Pdiag Umat : MatrixAlg D)
    {S T : Type*} [Fintype S] [DecidableEq S] [Fintype T] [DecidableEq T]
    (eST : Fin D ≃ S ⊕ T) (eS : S ≃ Fin n)
    (P0 : Matrix (S ⊕ T) (S ⊕ T) ℂ)
    (hP0 : P0 = Matrix.fromBlocks (1 : Matrix S S ℂ) 0 0 (0 : Matrix T T ℂ))
    (hP_decomp : P = Umat * Pdiag * Umatᴴ)
    (hPdiag_back : Matrix.reindexLinearEquiv ℂ ℂ eST.symm eST.symm P0 = Pdiag)
    (hU'U : Umatᴴ * Umat = 1) :
    Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] cornerSubmodule P :=
  { toFun := fun M =>
      ⟨cornerCompressionExpand Umat eST eS M,
        cornerCompressionExpand_mem (P := P) (Pdiag := Pdiag) Umat eST eS P0
          hP0 hP_decomp hPdiag_back hU'U M⟩
    map_add' := fun M₁ M₂ => by
      apply Subtype.ext
      exact (cornerCompressionExpand Umat eST eS).map_add M₁ M₂
    map_smul' := fun c M => by
      apply Subtype.ext
      exact (cornerCompressionExpand Umat eST eS).map_smul c M }

/-- Inverse direction of the shared corner compression:
`X ↦ reindex eS eS ((reindex eST eST (Umatᴴ * X * Umat)).toBlocks₁₁)`.
Together with `cornerCompressionExpand` this pairs up into the `LinearEquiv`
`cornerCompressionLinearEquiv`. -/
noncomputable def cornerCompressionInvFun
    {D n : ℕ} (Umat : MatrixAlg D)
    {S T : Type*} [Fintype S] [DecidableEq S] [Fintype T] [DecidableEq T]
    (eST : Fin D ≃ S ⊕ T) (eS : S ≃ Fin n) :
    MatrixAlg D → Matrix (Fin n) (Fin n) ℂ := fun X =>
  Matrix.reindexLinearEquiv ℂ ℂ eS eS
    ((Matrix.reindexLinearEquiv ℂ ℂ eST eST (Umatᴴ * X * Umat)).toBlocks₁₁)

lemma cornerCompressionInvFun_expand
    {D n : ℕ} (Umat : MatrixAlg D)
    {S T : Type*} [Fintype S] [DecidableEq S] [Fintype T] [DecidableEq T]
    (eST : Fin D ≃ S ⊕ T) (eS : S ≃ Fin n)
    (hU'U : Umatᴴ * Umat = 1)
    (M : Matrix (Fin n) (Fin n) ℂ) :
    cornerCompressionInvFun Umat eST eS (cornerCompressionExpand Umat eST eS M) = M := by
  set Y_ST : Matrix (S ⊕ T) (S ⊕ T) ℂ :=
    Matrix.fromBlocks (Matrix.reindexLinearEquiv ℂ ℂ eS.symm eS.symm M)
      (0 : Matrix S T ℂ) (0 : Matrix T S ℂ) (0 : Matrix T T ℂ)
  set Y_D : MatrixAlg D := Matrix.reindexLinearEquiv ℂ ℂ eST.symm eST.symm Y_ST with hY_D_def
  have hcollapse : Umatᴴ * (Umat * Y_D * Umatᴴ) * Umat = Y_D := by
    calc
      Umatᴴ * (Umat * Y_D * Umatᴴ) * Umat
          = (Umatᴴ * Umat) * Y_D * (Umatᴴ * Umat) := by simp [Matrix.mul_assoc]
      _ = Y_D := by rw [hU'U]; simp
  have hreindex_Y :
      Matrix.reindexLinearEquiv ℂ ℂ eST eST Y_D = Y_ST := by
    change Matrix.reindexLinearEquiv ℂ ℂ eST eST
        (Matrix.reindexLinearEquiv ℂ ℂ eST.symm eST.symm Y_ST) = Y_ST
    rw [Matrix.reindexLinearEquiv_comp_apply, Equiv.symm_trans_self,
      Matrix.reindexLinearEquiv_refl_refl]
    rfl
  simp only [cornerCompressionInvFun]
  rw [cornerCompressionExpand_apply Umat eST eS M]
  rw [show Umatᴴ * (Umat *
      Matrix.reindexLinearEquiv ℂ ℂ eST.symm eST.symm Y_ST * Umatᴴ) * Umat = Y_D from by
        simpa [hY_D_def] using hcollapse]
  rw [hreindex_Y]
  have htoBlocks :
      Y_ST.toBlocks₁₁ = Matrix.reindexLinearEquiv ℂ ℂ eS.symm eS.symm M := by
    simp [Y_ST, Matrix.toBlocks_fromBlocks₁₁]
  rw [htoBlocks]
  change Matrix.reindexLinearEquiv ℂ ℂ eS eS
    (Matrix.reindexLinearEquiv ℂ ℂ eS.symm eS.symm M) = M
  rw [Matrix.reindexLinearEquiv_comp_apply, Equiv.symm_trans_self,
    Matrix.reindexLinearEquiv_refl_refl]
  rfl

lemma cornerCompressionExpand_invFun
    {D n : ℕ} (P Pdiag Umat : MatrixAlg D)
    {S T : Type*} [Fintype S] [DecidableEq S] [Fintype T] [DecidableEq T]
    (eST : Fin D ≃ S ⊕ T) (eS : S ≃ Fin n)
    (P0 : Matrix (S ⊕ T) (S ⊕ T) ℂ)
    (hP0 : P0 = Matrix.fromBlocks (1 : Matrix S S ℂ) 0 0 (0 : Matrix T T ℂ))
    (hPdiag_UPU : Pdiag = Umatᴴ * P * Umat)
    (hPdiag_std : Matrix.reindexLinearEquiv ℂ ℂ eST eST Pdiag = P0)
    (_hU'U : Umatᴴ * Umat = 1) (hUU : Umat * Umatᴴ = 1)
    (X : cornerSubmodule P) :
    cornerCompressionExpand Umat eST eS (cornerCompressionInvFun Umat eST eS X.1) = X.1 := by
  set Y : MatrixAlg D := Umatᴴ * X.1 * Umat
  set Y_ST : Matrix (S ⊕ T) (S ⊕ T) ℂ :=
    Matrix.reindexLinearEquiv ℂ ℂ eST eST Y
  have hPXP : P * X.1 * P = X.1 := X.2
  have hPdiagY : Pdiag * Y * Pdiag = Y := by
    rw [hPdiag_UPU]
    change (Umatᴴ * P * Umat) * (Umatᴴ * X.1 * Umat) * (Umatᴴ * P * Umat) =
      Umatᴴ * X.1 * Umat
    calc
      (Umatᴴ * P * Umat) * (Umatᴴ * X.1 * Umat) * (Umatᴴ * P * Umat)
          = Umatᴴ * (P * (Umat * Umatᴴ) * X.1 * (Umat * Umatᴴ) * P) * Umat := by
              simp [Matrix.mul_assoc]
      _ = Umatᴴ * (P * X.1 * P) * Umat := by rw [hUU]; simp
      _ = Umatᴴ * X.1 * Umat := by rw [hPXP]
  have hP0_YST : P0 * Y_ST * P0 = Y_ST := by
    have hp0_eq : P0 = Matrix.reindexLinearEquiv ℂ ℂ eST eST Pdiag := hPdiag_std.symm
    rw [hp0_eq]
    change Matrix.reindexLinearEquiv ℂ ℂ eST eST Pdiag *
        Matrix.reindexLinearEquiv ℂ ℂ eST eST Y *
        Matrix.reindexLinearEquiv ℂ ℂ eST eST Pdiag =
      Matrix.reindexLinearEquiv ℂ ℂ eST eST Y
    rw [Matrix.reindexLinearEquiv_mul (R := ℂ) (A := ℂ)
          eST eST eST Pdiag Y,
        Matrix.reindexLinearEquiv_mul (R := ℂ) (A := ℂ)
          eST eST eST (Pdiag * Y) Pdiag, hPdiagY]
  have hY_ST_block :
      Y_ST = Matrix.fromBlocks Y_ST.toBlocks₁₁ (0 : Matrix S T ℂ)
        (0 : Matrix T S ℂ) (0 : Matrix T T ℂ) := by
    have hkey : Matrix.fromBlocks Y_ST.toBlocks₁₁ (0 : Matrix S T ℂ)
        (0 : Matrix T S ℂ) (0 : Matrix T T ℂ) =
        Matrix.fromBlocks Y_ST.toBlocks₁₁ Y_ST.toBlocks₁₂
          Y_ST.toBlocks₂₁ Y_ST.toBlocks₂₂ := by
      rw [(Matrix.fromBlocks_toBlocks Y_ST).symm] at hP0_YST
      simp only [hP0, Matrix.fromBlocks_multiply, Matrix.one_mul, Matrix.mul_one,
        Matrix.zero_mul, Matrix.mul_zero, add_zero] at hP0_YST
      exact hP0_YST
    exact (hkey.trans (Matrix.fromBlocks_toBlocks Y_ST)).symm
  simp only [cornerCompressionInvFun]
  rw [cornerCompressionExpand_apply Umat eST eS]
  have hround :
      Matrix.reindexLinearEquiv ℂ ℂ eS.symm eS.symm
        (Matrix.reindexLinearEquiv ℂ ℂ eS eS Y_ST.toBlocks₁₁) = Y_ST.toBlocks₁₁ := by
    rw [Matrix.reindexLinearEquiv_comp_apply, Equiv.self_trans_symm,
      Matrix.reindexLinearEquiv_refl_refl]
    rfl
  rw [hround]
  rw [show Matrix.fromBlocks Y_ST.toBlocks₁₁ (0 : Matrix S T ℂ)
        (0 : Matrix T S ℂ) (0 : Matrix T T ℂ) = Y_ST from hY_ST_block.symm]
  have hround₂ :
      Matrix.reindexLinearEquiv ℂ ℂ eST.symm eST.symm Y_ST = Y := by
    change Matrix.reindexLinearEquiv ℂ ℂ eST.symm eST.symm
      (Matrix.reindexLinearEquiv ℂ ℂ eST eST Y) = Y
    rw [Matrix.reindexLinearEquiv_comp_apply, Equiv.self_trans_symm,
      Matrix.reindexLinearEquiv_refl_refl]
    rfl
  rw [hround₂]
  change Umat * (Umatᴴ * X.1 * Umat) * Umatᴴ = X.1
  calc
    Umat * (Umatᴴ * X.1 * Umat) * Umatᴴ
        = (Umat * Umatᴴ) * X.1 * (Umat * Umatᴴ) := by simp [Matrix.mul_assoc]
    _ = X.1 := by rw [hUU]; simp

/-- Shared corner-compression **linear equivalence**, promoting
`cornerCompressionLinearMap` to `Matrix (Fin n) (Fin n) ℂ ≃ₗ[ℂ] cornerSubmodule P`
using `cornerCompressionInvFun` as the inverse.  The forward direction is the
linear map built from the spectral diagonalisation of `P`; the inverse strips
the ambient unitary conjugation and extracts the top-left `S × S` block. -/
noncomputable def cornerCompressionLinearEquiv
    {D n : ℕ} (P Pdiag Umat : MatrixAlg D)
    {S T : Type*} [Fintype S] [DecidableEq S] [Fintype T] [DecidableEq T]
    (eST : Fin D ≃ S ⊕ T) (eS : S ≃ Fin n)
    (P0 : Matrix (S ⊕ T) (S ⊕ T) ℂ)
    (hP0 : P0 = Matrix.fromBlocks (1 : Matrix S S ℂ) 0 0 (0 : Matrix T T ℂ))
    (hP_decomp : P = Umat * Pdiag * Umatᴴ)
    (hPdiag_UPU : Pdiag = Umatᴴ * P * Umat)
    (hPdiag_std : Matrix.reindexLinearEquiv ℂ ℂ eST eST Pdiag = P0)
    (hPdiag_back : Matrix.reindexLinearEquiv ℂ ℂ eST.symm eST.symm P0 = Pdiag)
    (hU'U : Umatᴴ * Umat = 1) (hUU : Umat * Umatᴴ = 1) :
    Matrix (Fin n) (Fin n) ℂ ≃ₗ[ℂ] cornerSubmodule P :=
  let toLM :=
    cornerCompressionLinearMap (P := P) (Pdiag := Pdiag) Umat eST eS P0 hP0
      hP_decomp hPdiag_back hU'U
  { toLM with
    invFun := fun X => cornerCompressionInvFun Umat eST eS X.1
    left_inv := fun M => by
      change cornerCompressionInvFun Umat eST eS
        (cornerCompressionExpand Umat eST eS M) = M
      exact cornerCompressionInvFun_expand Umat eST eS hU'U M
    right_inv := fun X => by
      apply Subtype.ext
      change cornerCompressionExpand Umat eST eS
        (cornerCompressionInvFun Umat eST eS X.1) = X.1
      exact cornerCompressionExpand_invFun (P := P) (Pdiag := Pdiag) Umat eST eS P0
        hP0 hPdiag_UPU hPdiag_std hU'U hUU X }

/-- **Compression isometry for a projection (existence form).**

Given an orthogonal projection `P : M_D(ℂ)` of rank `n = trace P`, there is a linear
isomorphism between `M_n(ℂ)` and the corner submodule `P · M_D(ℂ) · P`, constructed
from the eigendecomposition of `P` via `Matrix.IsHermitian.eigenvectorUnitary`,
`Matrix.reindexLinearEquiv`, and `Matrix.fromBlocks`.

This is the projector analog of the isometry `φ` already constructed inside
`exists_compressedTensor_of_supported_projection` in `MPS/CanonicalForm/CyclicSectors`.
The public API is exposed through the `noncomputable def`s `cornerRank` and
`cornerSubmoduleMatrixLinearEquiv` together with the companion lemma
`cornerRank_eq_trace`. -/
private lemma exists_cornerSubmodule_matrixLinearEquiv_aux {D : ℕ}
    (P : MatrixAlg D) (hP : IsOrthogonalProjection P) :
    ∃ (n : ℕ) (_ : Matrix (Fin n) (Fin n) ℂ ≃ₗ[ℂ] cornerSubmodule P),
      (n : ℂ) = Matrix.trace P := by
  classical
  -- Spectral diagonalization of `P`.
  have hHerm : P.IsHermitian := hP.1
  let U := hHerm.eigenvectorUnitary
  let Umat : MatrixAlg D := (U : MatrixAlg D)
  have hUU : Umat * Umatᴴ = 1 :=
    by simpa [Matrix.star_eq_conjTranspose] using Unitary.mul_star_self_of_mem U.prop
  have hU'U : Umatᴴ * Umat = 1 :=
    by simpa [Matrix.star_eq_conjTranspose] using Matrix.UnitaryGroup.star_mul_self U
  have trace_conj : ∀ M : MatrixAlg D, Matrix.trace (Umatᴴ * M * Umat) = Matrix.trace M := by
    intro M
    rw [Matrix.mul_assoc, Matrix.trace_mul_comm Umatᴴ (M * Umat),
      Matrix.mul_assoc, hUU, Matrix.mul_one]
  let Pdiag : MatrixAlg D := Umatᴴ * P * Umat
  let f : Fin D → ℂ := fun j => (↑(hHerm.eigenvalues j) : ℂ)
  have hPdiag_eq : Pdiag = Matrix.diagonal f := by
    have h := hHerm.conjStarAlgAut_star_eigenvectorUnitary
    simpa [Pdiag, f, Unitary.conjStarAlgAut_star_apply] using h
  have hPdiag_idem : Pdiag * Pdiag = Pdiag := by
    change Umatᴴ * P * Umat * (Umatᴴ * P * Umat) = Umatᴴ * P * Umat
    calc
      Umatᴴ * P * Umat * (Umatᴴ * P * Umat)
          = Umatᴴ * (P * (Umat * Umatᴴ) * P) * Umat := by
              simp only [Matrix.mul_assoc]
      _ = Umatᴴ * (P * P) * Umat := by rw [hUU, Matrix.mul_one]
      _ = Umatᴴ * P * Umat := by rw [hP.2]
  have hf01 : ∀ j : Fin D, f j = 0 ∨ f j = 1 := by
    intro j
    have hDiag_idem : Matrix.diagonal f * Matrix.diagonal f = Matrix.diagonal f := by
      simpa [hPdiag_eq] using hPdiag_idem
    have hfun : (fun k => f k * f k) = f := by
      apply Matrix.diagonal_injective
      simpa [Matrix.diagonal_mul_diagonal] using hDiag_idem
    have hfj : f j * f j = f j := congrFun hfun j
    have hfj' : f j * (f j - 1) = 0 := by
      calc f j * (f j - 1) = f j * f j - f j := by ring
        _ = 0 := by simpa using sub_eq_zero.mpr hfj
    rcases mul_eq_zero.mp hfj' with h0 | h1
    · exact Or.inl h0
    · exact Or.inr (sub_eq_zero.mp h1)
  let p : Fin D → Prop := fun j => f j = 1
  haveI : DecidablePred p := fun _ => inferInstance
  let S := { j : Fin D // p j }
  let T := { j : Fin D // ¬ p j }
  let n := Fintype.card S
  have hfT : ∀ t : T, f t.1 = 0 := fun t => (hf01 t.1).resolve_right t.2
  let eST : Fin D ≃ (S ⊕ T) := (Equiv.sumCompl p).symm
  let eS : S ≃ Fin n := Fintype.equivFin S
  -- Trace identity `(n : ℂ) = tr P`.
  have htrace : (n : ℂ) = Matrix.trace P := by
    have hPtr : Matrix.trace P = Matrix.trace Pdiag := by
      change Matrix.trace P = Matrix.trace (Umatᴴ * P * Umat)
      rw [trace_conj]
    rw [hPtr, hPdiag_eq, Matrix.trace_diagonal]
    have hfsum : ∑ j : Fin D, f j = ∑ j : Fin D, if p j then (1 : ℂ) else 0 := by
      refine Finset.sum_congr rfl (fun j _ => ?_)
      show f j = if p j then 1 else 0
      by_cases hp : p j
      · simp [hp, show f j = 1 from hp]
      · simp [hp, show f j = 0 from (hf01 j).resolve_right hp]
    rw [hfsum, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
    have : n = (Finset.univ.filter p).card := Fintype.card_subtype p
    exact_mod_cast this
  refine ⟨n, ?_, htrace⟩
  -- `P0` in the `S ⊕ T` basis is the identity-plus-zero block.
  let P0 : Matrix (S ⊕ T) (S ⊕ T) ℂ :=
    Matrix.fromBlocks (1 : Matrix S S ℂ) 0 0 (0 : Matrix T T ℂ)
  have hPdiag_std :
      Matrix.reindexLinearEquiv ℂ ℂ eST eST Pdiag = P0 := by
    change Matrix.reindex eST eST Pdiag = P0
    rw [hPdiag_eq, show Matrix.reindex eST eST (Matrix.diagonal f) =
        Matrix.diagonal (f ∘ eST.symm) from by simp [Matrix.reindex_apply]]
    ext x y
    cases x with
    | inl s =>
        cases y with
        | inl s' =>
            by_cases h : s = s'
            · subst h; simpa [p, P0] using s.2
            · simp [P0, Matrix.fromBlocks_apply₁₁, h]
        | inr t => simp [P0, Matrix.fromBlocks_apply₁₂]
    | inr t =>
        cases y with
        | inl s => simp [P0, Matrix.fromBlocks_apply₂₁]
        | inr t' =>
            by_cases h : t = t'
            · subst h; simpa [p, P0] using hfT t
            · simp [P0, Matrix.fromBlocks_apply₂₂, h]
  -- Forward and inverse maps for the compression equiv.
  have hP_decomp : P = Umat * Pdiag * Umatᴴ := by
    change P = Umat * (Umatᴴ * P * Umat) * Umatᴴ
    calc
      P = (Umat * Umatᴴ) * P * (Umat * Umatᴴ) := by rw [hUU]; simp
      _ = Umat * (Umatᴴ * P * Umat) * Umatᴴ := by simp [Matrix.mul_assoc]
  have hPdiag_back :
      Matrix.reindexLinearEquiv ℂ ℂ eST.symm eST.symm P0 = Pdiag := by
    have h := congrArg
      (Matrix.reindexLinearEquiv ℂ ℂ eST.symm eST.symm) hPdiag_std
    have hid := (Matrix.reindexLinearEquiv_comp_apply (R := ℂ) (A := ℂ)
      eST eST eST.symm eST.symm Pdiag)
    rw [Equiv.self_trans_symm, Matrix.reindexLinearEquiv_refl_refl,
      LinearEquiv.refl_apply] at hid
    exact h.symm.trans hid
  -- Package the compression as a `LinearEquiv` using the shared
  -- `cornerCompressionLinearEquiv` builder.
  exact cornerCompressionLinearEquiv (P := P) (Pdiag := Pdiag) Umat eST eS P0
    rfl hP_decomp rfl hPdiag_std hPdiag_back hU'U hUU

/-- The rank of an orthogonal projection `P : M_D(ℂ)`, defined so that
`cornerSubmoduleMatrixLinearEquiv` produces an isometry `M_{cornerRank P hP}(ℂ) ≃ₗ
cornerSubmodule P` and `cornerRank_eq_trace` witnesses `(cornerRank P hP : ℂ) = tr P`. -/
noncomputable def cornerRank {D : ℕ} (P : MatrixAlg D)
    (hP : IsOrthogonalProjection P) : ℕ :=
  (exists_cornerSubmodule_matrixLinearEquiv_aux P hP).choose

/-- **Compression isometry for a projection.**

For an orthogonal projection `P : M_D(ℂ)`, the corner algebra `P · M_D(ℂ) · P` is
linearly isomorphic to the matrix algebra `M_{cornerRank P hP}(ℂ)` via the
spectral diagonalisation of `P`. This is the projector analog of the compression
isometry used inside `exists_compressedTensor_of_supported_projection` in
`MPS/CanonicalForm/CyclicSectors`. -/
noncomputable def cornerSubmoduleMatrixLinearEquiv {D : ℕ}
    (P : MatrixAlg D) (hP : IsOrthogonalProjection P) :
    Matrix (Fin (cornerRank P hP)) (Fin (cornerRank P hP)) ℂ ≃ₗ[ℂ] cornerSubmodule P :=
  (exists_cornerSubmodule_matrixLinearEquiv_aux P hP).choose_spec.choose

/-- The rank of the corner submodule equals the trace of the projection. -/
lemma cornerRank_eq_trace {D : ℕ} (P : MatrixAlg D) (hP : IsOrthogonalProjection P) :
    (cornerRank P hP : ℂ) = Matrix.trace P :=
  (exists_cornerSubmodule_matrixLinearEquiv_aux P hP).choose_spec.choose_spec

namespace MPSTensor

private noncomputable def minEigenvalue {D : ℕ} [Nonempty (Fin D)]
    {H : MatrixAlg D} (hH : H.IsHermitian) : ℝ :=
  (Finset.univ.image hH.eigenvalues).min' (Finset.Nonempty.image Finset.univ_nonempty _)

private lemma minEigenvalue_le {D : ℕ} [Nonempty (Fin D)]
    {H : MatrixAlg D} (hH : H.IsHermitian) (i : Fin D) :
    minEigenvalue hH ≤ hH.eigenvalues i :=
  Finset.min'_le _ _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)

private lemma diagonal_sub_smul_one {D : ℕ} (v : Fin D → ℝ) (c : ℝ) :
    Matrix.diagonal (fun j => (↑(v j) : ℂ)) - (↑c : ℂ) • (1 : MatrixAlg D) =
      Matrix.diagonal (fun j => (↑(v j - c) : ℂ)) := by
  ext i j
  by_cases h : i = j
  · subst h
    have hone : ((↑c : ℂ) • (1 : MatrixAlg D)) i i = ↑c := by
      change ((↑c : ℂ) • ((1 : MatrixAlg D) i)) i = ↑c
      rw [Pi.smul_apply, Matrix.one_apply_eq]
      simp only [smul_eq_mul, mul_one]
    rw [Matrix.sub_apply, Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq, hone]
    simp only [ofReal_sub]
  · have hone : ((↑c : ℂ) • (1 : MatrixAlg D)) i j = 0 := by
      change ((↑c : ℂ) • ((1 : MatrixAlg D) i)) j = 0
      rw [Pi.smul_apply, Matrix.one_apply_ne h]
      simp only [smul_eq_mul, mul_zero]
    rw [Matrix.sub_apply, Matrix.diagonal_apply_ne _ h, Matrix.diagonal_apply_ne _ h, hone]
    simp only [sub_self]

private lemma hermitian_sub_scalar_spectral
    {D : ℕ} {H : MatrixAlg D} (hH : H.IsHermitian) (c : ℝ) :
    H - (↑c : ℂ) • 1 =
      (↑hH.eigenvectorUnitary : MatrixAlg D) *
      Matrix.diagonal (fun j => (↑(hH.eigenvalues j - c) : ℂ)) *
      (↑hH.eigenvectorUnitary : MatrixAlg D)ᴴ := by
  set U : MatrixAlg D := ↑hH.eigenvectorUnitary
  have hUU : U * Uᴴ = 1 := by
    simpa [U] using eig_mul_conj hH
  have h_cI : (↑c : ℂ) • (1 : MatrixAlg D) = U * ((↑c : ℂ) • 1) * Uᴴ := by
    calc
      (↑c : ℂ) • (1 : MatrixAlg D) = (↑c : ℂ) • (U * Uᴴ) := by rw [hUU]
      _ = U * ((↑c : ℂ) • 1) * Uᴴ := by
          rw [Matrix.mul_smul, Matrix.mul_one, smul_mul_assoc]
  calc
    H - (↑c : ℂ) • 1
        = U * Matrix.diagonal (fun j => ↑(hH.eigenvalues j)) * Uᴴ -
            U * ((↑c : ℂ) • 1) * Uᴴ := by
              conv_lhs =>
                rw [spectral_decomp_eq hH]
                rw [h_cI]
    _ = U * (Matrix.diagonal (fun j => ↑(hH.eigenvalues j)) - (↑c : ℂ) • 1) * Uᴴ := by
          noncomm_ring
    _ = U * Matrix.diagonal (fun j => ↑(hH.eigenvalues j - c)) * Uᴴ := by
          congr 1
          congr 1
          exact diagonal_sub_smul_one hH.eigenvalues c

private theorem hermitian_fixed_eq_scalar_of_irreducible_unital
    {r D : ℕ} [NeZero D]
    (K : Fin r → MatrixAlg D)
    (hUnital : KadisonSchwarz.IsUnitalKraus (d := r) (D := D) K)
    (hIrr : IsIrreducibleMap (transferMap (d := r) (D := D) K))
    (H : MatrixAlg D) (hH : H.IsHermitian)
    (hfix : transferMap (d := r) (D := D) K H = H) :
    ∃ c : ℂ, H = c • 1 := by
  classical
  haveI : Nonempty (Fin D) := ⟨⟨0, NeZero.pos D⟩⟩
  set c0 : ℝ := minEigenvalue hH
  set U : MatrixAlg D := (↑hH.eigenvectorUnitary : MatrixAlg D)
  have hU_unit : IsUnit U := by
    apply (Matrix.isUnit_iff_isUnit_det U).2
    simpa [U] using Matrix.UnitaryGroup.det_isUnit hH.eigenvectorUnitary
  have hshift_eq :
      H - (c0 : ℂ) • 1 =
        U * Matrix.diagonal (fun i : Fin D => (↑(hH.eigenvalues i - c0) : ℂ)) * Uᴴ := by
    simpa [U] using hermitian_sub_scalar_spectral hH c0
  have hshift_psd : (H - (c0 : ℂ) • 1).PosSemidef := by
    rw [hshift_eq]
    have hdiag_psd :
        (Matrix.diagonal (fun i : Fin D => (↑(hH.eigenvalues i - c0) : ℂ))).PosSemidef := by
      rw [Matrix.posSemidef_diagonal_iff]
      intro i
      exact_mod_cast sub_nonneg.mpr (minEigenvalue_le hH i)
    exact (Matrix.IsUnit.posSemidef_star_right_conjugate_iff hU_unit).2 hdiag_psd
  have hone_fix : transferMap (d := r) (D := D) K (1 : MatrixAlg D) = 1 := by
    simpa [MPSTensor.transferMap_apply, KadisonSchwarz.krausMap,
      KadisonSchwarz.IsUnitalKraus] using hUnital
  have hshift_fix :
      transferMap (d := r) (D := D) K (H - (c0 : ℂ) • 1) = H - (c0 : ℂ) • 1 := by
    calc
      transferMap (d := r) (D := D) K (H - (c0 : ℂ) • 1)
          = transferMap (d := r) (D := D) K H -
              transferMap (d := r) (D := D) K ((c0 : ℂ) • (1 : MatrixAlg D)) := by
              rw [LinearMap.map_sub]
      _ = transferMap (d := r) (D := D) K H -
            (c0 : ℂ) • transferMap (d := r) (D := D) K 1 := by
              rw [LinearMap.map_smul]
      _ = H - (c0 : ℂ) • 1 := by simp only [hfix, hone_fix, Complex.coe_smul]
  have hone_psd : (1 : MatrixAlg D).PosSemidef := by
    simpa using (Matrix.PosDef.one (n := Fin D) (R := ℂ)).posSemidef
  rcases posSemidef_fixedPoint_unique_of_irreducible (A := K) hIrr
      (1 : MatrixAlg D) (H - (c0 : ℂ) • 1) hone_psd one_ne_zero hshift_psd hone_fix hshift_fix with
    ⟨d, hd⟩
  refine ⟨d + c0, ?_⟩
  calc
    H = (H - (c0 : ℂ) • 1) + (c0 : ℂ) • 1 := by abel
    _ = d • 1 + (c0 : ℂ) • 1 := by rw [hd]
    _ = (d + c0) • 1 := by simp only [Complex.coe_smul, add_smul]

/-- For an irreducible unital Kraus map, every fixed point is a scalar multiple
of the identity matrix. -/
theorem fixed_eq_scalar_of_irreducible_unital
    {r D : ℕ} [NeZero D]
    (K : Fin r → MatrixAlg D)
    (hUnital : KadisonSchwarz.IsUnitalKraus (d := r) (D := D) K)
    (hIrr : IsIrreducibleMap (transferMap (d := r) (D := D) K))
    (X : MatrixAlg D)
    (hfix : transferMap (d := r) (D := D) K X = X) :
    ∃ c : ℂ, X = c • 1 := by
  have hfix_map : Kraus.map K X = X := by
    simpa [Kraus.map, MPSTensor.transferMap_apply] using hfix
  have hfix_star_map : Kraus.map K Xᴴ = Xᴴ := by
    calc
      Kraus.map K Xᴴ = (Kraus.map K X)ᴴ := by
        simpa using (Kraus.map_conjTranspose K X).symm
      _ = Xᴴ := by rw [hfix_map]
  have hfix_star : transferMap (d := r) (D := D) K Xᴴ = Xᴴ := by
    simpa [Kraus.map, MPSTensor.transferMap_apply] using hfix_star_map
  have hHerm_fix : transferMap (d := r) (D := D) K (X + Xᴴ) = X + Xᴴ := by
    calc
      transferMap (d := r) (D := D) K (X + Xᴴ)
          = transferMap (d := r) (D := D) K X + transferMap (d := r) (D := D) K Xᴴ := by
              simpa using (transferMap (d := r) (D := D) K).map_add X Xᴴ
      _ = X + Xᴴ := by simp only [hfix, hfix_star]
  have hSkew_fix :
      transferMap (d := r) (D := D) K (Complex.I • (X - Xᴴ)) = Complex.I • (X - Xᴴ) := by
    calc
      transferMap (d := r) (D := D) K (Complex.I • (X - Xᴴ))
          = Complex.I • transferMap (d := r) (D := D) K (X - Xᴴ) := by
              simp only [map_smul, transferMap_apply]
      _ = Complex.I • (transferMap (d := r) (D := D) K X - transferMap (d := r) (D := D) K Xᴴ) := by
              simpa using congrArg (fun M => Complex.I • M)
                ((transferMap (d := r) (D := D) K).map_sub X Xᴴ)
      _ = Complex.I • (X - Xᴴ) := by simp only [hfix, hfix_star]
  have hHerm_herm : (X + Xᴴ).IsHermitian := by
    simp only [IsHermitian, conjTranspose_add, conjTranspose_conjTranspose, add_comm]
  have hSkew_herm : (Complex.I • (X - Xᴴ)).IsHermitian := by
    refine Matrix.IsHermitian.ext ?_
    intro i j
    change star (Complex.I * (X j i - star (X i j))) = Complex.I * (X i j - star (X j i))
    simp only [Complex.star_def, StarMul.star_mul, star_sub, Complex.conj_I,
      Complex.conj_conj]
    ring
  rcases hermitian_fixed_eq_scalar_of_irreducible_unital
      (K := K) hUnital hIrr (X + Xᴴ) hHerm_herm hHerm_fix with ⟨a, ha⟩
  rcases hermitian_fixed_eq_scalar_of_irreducible_unital
      (K := K) hUnital hIrr (Complex.I • (X - Xᴴ)) hSkew_herm hSkew_fix with ⟨b, hb⟩
  refine ⟨(1 / 2 : ℂ) * (a - Complex.I * b), ?_⟩
  have hrecon :
      (X + Xᴴ) - Complex.I • (Complex.I • (X - Xᴴ)) = (2 : ℂ) • X := by
    calc
      (X + Xᴴ) - Complex.I • (Complex.I • (X - Xᴴ)) = (X + Xᴴ) + (X - Xᴴ) := by
            simp only [
              sub_eq_add_neg, smul_add, smul_neg, smul_smul, I_mul_I, neg_smul,
              one_smul, neg_add_rev, add_right_inj
            ]
            abel
      _ = (2 : ℂ) • X := by
            ext i j
            simp only [
              sub_eq_add_neg, add_apply, conjTranspose_apply, RCLike.star_def,
              neg_apply, add_left_comm, add_assoc, add_neg_cancel, add_zero,
              smul_apply, smul_eq_mul, two_mul
            ]
  calc
    X = (1 / 2 : ℂ) • ((2 : ℂ) • X) := by
      simp only [
        one_div, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, inv_smul_smul₀
      ]
    _ = (1 / 2 : ℂ) • ((X + Xᴴ) - Complex.I • (Complex.I • (X - Xᴴ))) := by
          rw [← hrecon]
    _ = (1 / 2 : ℂ) • ((a • (1 : MatrixAlg D)) - Complex.I • (b • (1 : MatrixAlg D))) := by
          rw [ha, hb]
    _ = ((1 / 2 : ℂ) * (a - Complex.I * b)) • (1 : MatrixAlg D) := by
          ext i j
          by_cases hij : i = j
          · subst hij
            simp only [
              one_div, sub_eq_add_neg, smul_apply, add_apply, one_apply_eq, smul_eq_mul,
              mul_one, neg_apply, mul_comm, mul_left_comm, one_mul
            ]
          · simp only [
              one_div, smul_apply, sub_apply, ne_eq, hij, not_false_eq_true, one_apply_ne,
              smul_eq_mul, mul_zero, sub_self
            ]

section PeripheralUnitary

/-- A peripheral eigenvalue of an irreducible unital Schwarz transfer map admits a unitary
matrix eigenvector.

This is the unitary part of Wolf Theorem 6.6. The formulation is stated for transfer maps of
Kraus families because the available Kadison--Schwarz / multiplicative-domain API is implemented
at that level. -/
theorem exists_peripheral_unitary_of_irreducible_schwarz
    {r D : ℕ} [NeZero D]
    (K : Fin r → MatrixAlg D)
    (hUnital : KadisonSchwarz.IsUnitalKraus (d := r) (D := D) K)
    (ρ : MatrixAlg D) (hρ : ρ.PosDef)
    (hρfix : Kraus.adjointMap K ρ = ρ)
    (hIrr : IsIrreducibleMap (transferMap (d := r) (D := D) K))
    {γ : ℂ}
    (hγ : γ ∈ peripheralEigenvalues (transferMap (d := r) (D := D) K)) :
    ∃ U : Matrix.unitaryGroup (Fin D) ℂ,
      transferMap (d := r) (D := D) K (U : MatrixAlg D) = γ • (U : MatrixAlg D) := by
  classical
  haveI : Nonempty (Fin D) := ⟨⟨0, NeZero.pos D⟩⟩
  rcases hγ with ⟨hγ_eig, hγ_norm⟩
  rcases hγ_eig.exists_hasEigenvector with ⟨X, hX_eigvec⟩
  have hX_mem : X ∈ Module.End.eigenspace (transferMap (d := r) (D := D) K) γ :=
    (Module.End.hasEigenvector_iff.mp hX_eigvec).1
  have hX_ne : X ≠ 0 := (Module.End.hasEigenvector_iff.mp hX_eigvec).2
  have hEig_transfer : transferMap (d := r) (D := D) K X = γ • X :=
    (Module.End.mem_eigenspace_iff).1 hX_mem
  have hEig_map : Kraus.map K X = γ • X := by
    simpa [Kraus.map, MPSTensor.transferMap_apply] using hEig_transfer
  have hUnital' : Kraus.IsUnital K := by
    simpa [Kraus.IsUnital, KadisonSchwarz.IsUnitalKraus] using hUnital
  have hKS_map :
      Kraus.map K (Xᴴ * X) = (Kraus.map K X)ᴴ * Kraus.map K X :=
    Kraus.ks_equality_of_peripheral_eigenvector_of_fixedPoint
      K hUnital' hρ hρfix X γ hEig_map hγ_norm
  have hγ_star_mul : star γ * γ = 1 := by
    rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self]
    simp only [normSq_eq_norm_sq, hγ_norm, one_pow, ofReal_one]
  have hγ_starRing_mul : (starRingEnd ℂ) γ * γ = 1 := by
    simpa [Complex.star_def] using hγ_star_mul
  have hXX_fix_map : Kraus.map K (Xᴴ * X) = Xᴴ * X := by
    calc
      Kraus.map K (Xᴴ * X) = (Kraus.map K X)ᴴ * Kraus.map K X := hKS_map
      _ = (γ • X)ᴴ * (γ • X) := by rw [hEig_map]
      _ = ((starRingEnd ℂ) γ * γ) • (Xᴴ * X) := by
            simp only [
              conjTranspose_smul, RCLike.star_def, Algebra.mul_smul_comm,
              Algebra.smul_mul_assoc, smul_smul, mul_comm
            ]
      _ = Xᴴ * X := by simp only [hγ_starRing_mul, one_smul]
  have hXX_fix : transferMap (d := r) (D := D) K (Xᴴ * X) = Xᴴ * X := by
    simpa [Kraus.map, MPSTensor.transferMap_apply] using hXX_fix_map
  have hXX_psd : (Xᴴ * X).PosSemidef := by
    simpa using Matrix.posSemidef_conjTranspose_mul_self X
  have hXX_ne : Xᴴ * X ≠ 0 := by
    intro h
    apply hX_ne
    exact Matrix.conjTranspose_mul_self_eq_zero.mp h
  have hone_psd : (1 : MatrixAlg D).PosSemidef := by
    simpa using (Matrix.PosDef.one (n := Fin D) (R := ℂ)).posSemidef
  have hone_fix : transferMap (d := r) (D := D) K (1 : MatrixAlg D) = 1 := by
    simpa [MPSTensor.transferMap_apply, KadisonSchwarz.krausMap,
      KadisonSchwarz.IsUnitalKraus] using hUnital
  rcases posSemidef_fixedPoint_unique_of_irreducible (A := K) hIrr
      (1 : MatrixAlg D) (Xᴴ * X) hone_psd one_ne_zero hXX_psd hone_fix hXX_fix with ⟨c, hXX_scalar⟩
  have hc_ne0 : c ≠ 0 := by
    intro hc0
    apply hXX_ne
    simp only [hXX_scalar, hc0, zero_smul]
  have hc_nonneg : 0 ≤ c := by
    have hscalar_psd : (c • (1 : MatrixAlg D)).PosSemidef := by
      simpa [hXX_scalar] using hXX_psd
    have hdiag_psd : (Matrix.diagonal (fun _ : Fin D => c)).PosSemidef := by
      simpa [Matrix.smul_one_eq_diagonal] using hscalar_psd
    have hdiag_nonneg := (Matrix.posSemidef_diagonal_iff).1 hdiag_psd
    exact hdiag_nonneg ⟨0, NeZero.pos D⟩
  have hc_eq_real : c = (c.re : ℂ) := by
    exact Complex.ext rfl (by simpa using (Complex.nonneg_iff.mp hc_nonneg).2.symm)
  have hcre_nonneg : 0 ≤ c.re := (Complex.nonneg_iff.mp hc_nonneg).1
  have hcre_ne0 : c.re ≠ 0 := by
    intro h0
    apply hc_ne0
    calc
      c = (c.re : ℂ) := hc_eq_real
      _ = 0 := by simp only [h0, ofReal_zero]
  have hcre_pos : 0 < c.re := lt_of_le_of_ne hcre_nonneg (Ne.symm hcre_ne0)
  set a : ℂ := (Real.sqrt c.re : ℂ)
  have ha_ne0 : a ≠ 0 := by
    have hsqrt_ne : ((Real.sqrt c.re : ℂ)) ≠ 0 := by
      exact_mod_cast Real.sqrt_ne_zero'.mpr hcre_pos
    simpa [a] using hsqrt_ne
  have hstar_a : star a = a := by
    simp only [RCLike.star_def, conj_ofReal, a]
  have hstar_a_inv : (starRingEnd ℂ) a⁻¹ = a⁻¹ := by
    rw [map_inv₀]
    simpa [Complex.star_def] using hstar_a
  have hstar_a_inv' : star a⁻¹ = a⁻¹ := by
    simpa [Complex.star_def] using hstar_a_inv
  have hc_eq_sq : c = a * a := by
    calc
      c = (c.re : ℂ) := hc_eq_real
      _ = (((Real.sqrt c.re) ^ 2 : ℝ) : ℂ) := by
            simp only [Real.sq_sqrt hcre_nonneg]
      _ = a * a := by
            rw [pow_two]
            simp only [ofReal_mul, a]
  refine ⟨⟨a⁻¹ • X, by
    rw [Matrix.mem_unitaryGroup_iff']
    calc
      (a⁻¹ • X)ᴴ * (a⁻¹ • X) = ((a⁻¹ * a⁻¹) * c) • (1 : MatrixAlg D) := by
            rw [conjTranspose_smul, smul_mul_assoc, mul_smul_comm, smul_smul, hXX_scalar, smul_smul,
              hstar_a_inv']
      _ = 1 := by
            have hscalar : ((a⁻¹ * a⁻¹) * c : ℂ) = 1 := by
              calc
                (a⁻¹ * a⁻¹) * c = (a⁻¹ * a⁻¹) * (a * a) := by rw [hc_eq_sq]
                _ = 1 := by field_simp [ha_ne0]
            simp only [hscalar, one_smul]⟩, ?_⟩
  calc
    transferMap (d := r) (D := D) K (a⁻¹ • X) = a⁻¹ • transferMap (d := r) (D := D) K X := by
          simp only [map_smul, transferMap_apply]
    _ = a⁻¹ • (γ • X) := by rw [hEig_transfer]
    _ = γ • (a⁻¹ • X) := by simp only [smul_smul, mul_comm]

/-- Powers of a peripheral unitary remain peripheral eigenvectors. -/
theorem map_powers_of_peripheral_unitary
    {r D : ℕ} [NeZero D]
    (K : Fin r → MatrixAlg D)
    (hUnital : KadisonSchwarz.IsUnitalKraus (d := r) (D := D) K)
    (ρ : MatrixAlg D) (hρ : ρ.PosDef)
    (hρfix : Kraus.adjointMap K ρ = ρ)
    {γ : ℂ}
    (hγ : γ ∈ peripheralEigenvalues (transferMap (d := r) (D := D) K))
    (U : Matrix.unitaryGroup (Fin D) ℂ)
    (hU : transferMap (d := r) (D := D) K (U : MatrixAlg D) = γ • (U : MatrixAlg D)) :
    ∀ k : ℕ,
      transferMap (d := r) (D := D) K ((U : MatrixAlg D) ^ k) =
        γ ^ k • ((U : MatrixAlg D) ^ k) := by
  intro k
  have hγnorm : ‖γ‖ = 1 := hγ.2
  have hU_map : Kraus.map K (U : MatrixAlg D) = γ • (U : MatrixAlg D) := by
    simpa [Kraus.map, MPSTensor.transferMap_apply] using hU
  have hU_kraus : KadisonSchwarz.krausMap (d := r) (D := D) K (U : MatrixAlg D) =
      γ • (U : MatrixAlg D) := by
    simpa [KadisonSchwarz.krausMap, MPSTensor.transferMap_apply] using hU
  have hUnital' : Kraus.IsUnital K := by
    simpa [Kraus.IsUnital, KadisonSchwarz.IsUnitalKraus] using hUnital
  have hKS_map :
      Kraus.map K ((U : MatrixAlg D)ᴴ * (U : MatrixAlg D)) =
        (Kraus.map K (U : MatrixAlg D))ᴴ * Kraus.map K (U : MatrixAlg D) :=
    Kraus.ks_equality_of_peripheral_eigenvector_of_fixedPoint
      K hUnital' hρ hρfix (U : MatrixAlg D) γ hU_map hγnorm
  have hKS_kraus :
      KadisonSchwarz.krausMap (d := r) (D := D) K ((U : MatrixAlg D)ᴴ * (U : MatrixAlg D)) =
        (KadisonSchwarz.krausMap (d := r) (D := D) K (U : MatrixAlg D))ᴴ *
          KadisonSchwarz.krausMap (d := r) (D := D) K (U : MatrixAlg D) := by
    simpa [Kraus.map, KadisonSchwarz.krausMap] using hKS_map
  have hpow_kraus :
      KadisonSchwarz.krausMap (d := r) (D := D) K ((U : MatrixAlg D) ^ k) =
        γ ^ k • ((U : MatrixAlg D) ^ k) :=
    KadisonSchwarz.krausMap_pow_of_ks_equality
      (K := K) hUnital (U : MatrixAlg D) γ hU_kraus hKS_kraus k
  simpa [KadisonSchwarz.krausMap, MPSTensor.transferMap_apply] using hpow_kraus

/-- A generator of the peripheral cycle can be normalized to have exact order `m`. -/
theorem exists_normalized_peripheral_unitary_of_irreducible_schwarz
    {r D m : ℕ} [NeZero D] [NeZero m]
    (K : Fin r → MatrixAlg D)
    (hUnital : KadisonSchwarz.IsUnitalKraus (d := r) (D := D) K)
    (ρ : MatrixAlg D) (hρ : ρ.PosDef)
    (hρfix : Kraus.adjointMap K ρ = ρ)
    (hIrr : IsIrreducibleMap (transferMap (d := r) (D := D) K))
    {γ : ℂ} (hγprim : IsPrimitiveRoot γ m)
    (hγ : γ ∈ peripheralEigenvalues (transferMap (d := r) (D := D) K)) :
    ∃ U : Matrix.unitaryGroup (Fin D) ℂ,
      transferMap (d := r) (D := D) K (U : MatrixAlg D) = γ • (U : MatrixAlg D) ∧
      ((U : MatrixAlg D) ^ m = 1) := by
  classical
  haveI : Nonempty (Fin D) := ⟨⟨0, NeZero.pos D⟩⟩
  obtain ⟨U, hU⟩ :=
    exists_peripheral_unitary_of_irreducible_schwarz
      (K := K) hUnital ρ hρ hρfix hIrr hγ
  have hPow :
      ∀ k : ℕ,
        transferMap (d := r) (D := D) K ((U : MatrixAlg D) ^ k) =
          γ ^ k • ((U : MatrixAlg D) ^ k) :=
    map_powers_of_peripheral_unitary
      (K := K) hUnital ρ hρ hρfix hγ U hU
  have hUm_fix :
      transferMap (d := r) (D := D) K ((U : MatrixAlg D) ^ m) = (U : MatrixAlg D) ^ m := by
    calc
      transferMap (d := r) (D := D) K ((U : MatrixAlg D) ^ m)
          = γ ^ m • ((U : MatrixAlg D) ^ m) := hPow m
      _ = (U : MatrixAlg D) ^ m := by simp only [hγprim.pow_eq_one, one_smul]
  rcases fixed_eq_scalar_of_irreducible_unital
      (K := K) hUnital hIrr ((U : MatrixAlg D) ^ m) hUm_fix with ⟨α, hUm_scalar⟩
  have hUm_unitary : (((U : MatrixAlg D) ^ m)ᴴ * ((U : MatrixAlg D) ^ m)) = 1 := by
    simpa using Matrix.UnitaryGroup.star_mul_self (U ^ m)
  have hα_unit_mul : α * (starRingEnd ℂ) α = 1 := by
    let i0 : Fin D := ⟨0, NeZero.pos D⟩
    have hscalar_mat : ((α • (1 : MatrixAlg D))ᴴ * (α • (1 : MatrixAlg D)) : MatrixAlg D) = 1 := by
      simpa [hUm_scalar] using hUm_unitary
    have hentry := congrFun (congrFun hscalar_mat i0) i0
    simpa using hentry
  have hα_unit : star α * α = 1 := by
    simpa [Complex.star_def, mul_comm] using hα_unit_mul
  have hα_sq : ‖α‖ ^ 2 = 1 := by
    have hnormSqC : (↑(Complex.normSq α) : ℂ) = 1 := by
      calc
        (↑(Complex.normSq α) : ℂ) = star α * α := by
          rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self]
        _ = 1 := hα_unit
    have hnormSq : Complex.normSq α = 1 := by
      exact_mod_cast hnormSqC
    simpa [Complex.normSq_eq_norm_sq] using hnormSq
  have hα_norm : ‖α‖ = 1 := by
    have hnonneg : 0 ≤ ‖α‖ := norm_nonneg α
    nlinarith
  set β : ℂ := α⁻¹ ^ (m⁻¹ : ℂ)
  have hβm : β ^ m = α⁻¹ := by
    simpa [β] using (Complex.cpow_nat_inv_pow (α⁻¹) (NeZero.ne m))
  have hβ_norm_pow : ‖β‖ ^ m = 1 := by
    calc
      ‖β‖ ^ m = ‖β ^ m‖ := by rw [norm_pow]
      _ = ‖α⁻¹‖ := by simp only [hβm, norm_inv]
      _ = 1 := by simp only [norm_inv, hα_norm, inv_one]
  have hβ_norm : ‖β‖ = 1 := by
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg β) (NeZero.ne m)).1 hβ_norm_pow
  have hβ_unit : star β * β = 1 := by
    rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self]
    simp only [normSq_eq_norm_sq, hβ_norm, one_pow, ofReal_one]
  have hβ_starRing_mul : (starRingEnd ℂ) β * β = 1 := by
    simpa [Complex.star_def] using hβ_unit
  have hU_star_mul : ((U : MatrixAlg D)ᴴ * (U : MatrixAlg D)) = 1 :=
    Matrix.UnitaryGroup.star_mul_self U
  refine ⟨⟨β • (U : MatrixAlg D), by
    rw [Matrix.mem_unitaryGroup_iff']
    calc
      (β • (U : MatrixAlg D))ᴴ * (β • (U : MatrixAlg D)) =
          ((starRingEnd ℂ) β * β) • ((U : MatrixAlg D)ᴴ * (U : MatrixAlg D)) := by
            simp only [
              conjTranspose_smul, RCLike.star_def, Algebra.mul_smul_comm,
              Algebra.smul_mul_assoc, smul_smul, mul_comm
            ]
      _ = 1 := by rw [hβ_starRing_mul, hU_star_mul]; simp only [one_smul]⟩, ?_, ?_⟩
  · calc
      transferMap (d := r) (D := D) K (β • (U : MatrixAlg D))
          = β • transferMap (d := r) (D := D) K (U : MatrixAlg D) := by
              simp only [map_smul, transferMap_apply]
      _ = β • (γ • (U : MatrixAlg D)) := by rw [hU]
      _ = γ • (β • (U : MatrixAlg D)) := by simp only [smul_smul, mul_comm]
  · calc
      (β • (U : MatrixAlg D)) ^ m = β ^ m • ((U : MatrixAlg D) ^ m) := by
            simpa using smul_pow β (U : MatrixAlg D) m
      _ = β ^ m • (α • (1 : MatrixAlg D)) := by rw [hUm_scalar]
      _ = ((β ^ m) * α) • (1 : MatrixAlg D) := by rw [smul_smul]
      _ = 1 := by
            have hα_ne0 : α ≠ 0 := by
              intro h0
              simp only [h0, star_zero, mul_zero, zero_ne_one] at hα_unit
            simp only [hβm, ne_eq, hα_ne0, not_false_eq_true, inv_mul_cancel₀, one_smul]

end PeripheralUnitary

end MPSTensor

section CyclicProjections

variable {D m : ℕ} [NeZero m]

/-- The Fourier-type spectral projection associated with the `k`-th peripheral phase. -/
private noncomputable def cyclicProjection {γ : ℂ}
    (U : Matrix.unitaryGroup (Fin D) ℂ) (k : Fin m) : MatrixAlg D :=
  ((↑m : ℂ)⁻¹) • Finset.sum (Finset.range m)
    (fun j => ((((star γ) ^ (k : ℕ)) ^ j : ℂ)) • ((U : MatrixAlg D) ^ j))

/-- Index of `(1 : Fin m)` as a natural number; used as the "next cyclic step" index. -/
private abbrev cyclicOneIdx (m : ℕ) [NeZero m] : ℕ := ((1 : Fin m) : ℕ)

/-- A primitive root has unit modulus, written as `star γ * γ = 1`. -/
private lemma star_mul_self_of_primitiveRoot {γ : ℂ} (hγprim : IsPrimitiveRoot γ m) :
    star γ * γ = 1 := by
  have hm0 : m ≠ 0 := NeZero.ne m
  have hγ_norm : ‖γ‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hγprim.pow_eq_one hm0
  rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self]
  simp only [normSq_eq_norm_sq, hγ_norm, one_pow, ofReal_one]

/-- A primitive root has unit modulus, written as `γ * star γ = 1`. -/
private lemma self_mul_star_of_primitiveRoot {γ : ℂ} (hγprim : IsPrimitiveRoot γ m) :
    γ * star γ = 1 := by
  simpa [mul_comm] using star_mul_self_of_primitiveRoot (m := m) hγprim

/-- For a primitive root, complex conjugation agrees with inversion. -/
private lemma star_eq_inv_of_primitiveRoot {γ : ℂ} (hγprim : IsPrimitiveRoot γ m) :
    star γ = γ⁻¹ := by
  exact eq_inv_of_mul_eq_one_right (self_mul_star_of_primitiveRoot (m := m) hγprim)

/-- The phase `γ ^ n` cancels against its conjugate power. -/
private lemma pow_mul_star_pow_of_primitiveRoot {γ : ℂ} (hγprim : IsPrimitiveRoot γ m)
    (n : ℕ) : γ ^ n * (star γ) ^ n = 1 := by
  simpa [mul_pow] using congrArg (fun z : ℂ => z ^ n)
    (self_mul_star_of_primitiveRoot (m := m) hγprim)

/-- The conjugate phase `(star γ) ^ n` cancels against `γ ^ n`. -/
private lemma star_pow_mul_pow_of_primitiveRoot {γ : ℂ} (hγprim : IsPrimitiveRoot γ m)
    (n : ℕ) : (star γ) ^ n * γ ^ n = 1 := by
  simpa [mul_pow] using congrArg (fun z : ℂ => z ^ n)
    (star_mul_self_of_primitiveRoot (m := m) hγprim)

/-- The distinguished index `((1 : Fin m) : ℕ)` still represents the exponent `1`. -/
private lemma pow_oneIdx_of_primitiveRoot {γ : ℂ} (hγprim : IsPrimitiveRoot γ m) :
    γ ^ cyclicOneIdx (m := m) = γ := by
  by_cases hm1 : m = 1
  · subst hm1
    simp only [
      IsPrimitiveRoot.one_right_iff.mp hγprim, cyclicOneIdx, Fin.isValue, Fin.val_eq_zero,
      pow_zero
    ]
  · have hm0 : m ≠ 0 := NeZero.ne m
    have hm_gt : 1 < m := Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨hm0, hm1⟩
    simp only [cyclicOneIdx, Fin.coe_ofNat_eq_mod, Nat.mod_eq_of_lt hm_gt, pow_one]

/-- The distinguished index `((1 : Fin m) : ℕ)` leaves the unitary unchanged. -/
private lemma unitary_pow_oneIdx_of_pow_eq_one
    (U : Matrix.unitaryGroup (Fin D) ℂ) (hUm : ((U : MatrixAlg D) ^ m) = 1) :
    ((U : MatrixAlg D) ^ cyclicOneIdx (m := m)) = (U : MatrixAlg D) := by
  by_cases hm1 : m = 1
  · subst hm1
    have hUeq : (U : MatrixAlg D) = 1 := by simpa using hUm
    simp only [hUeq, cyclicOneIdx, Fin.isValue, Fin.val_eq_zero, pow_zero]
  · have hm0 : m ≠ 0 := NeZero.ne m
    have hm_gt : 1 < m := Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨hm0, hm1⟩
    simp only [cyclicOneIdx, Fin.coe_ofNat_eq_mod, Nat.mod_eq_of_lt hm_gt, pow_one]

omit [NeZero m] in
/-- Finite geometric sums on `Fin m` collapse when the `m`-th power is `1`. -/
private lemma sum_powers_fin_of_pow_eq_one (x : ℂ) (hxpow : x ^ m = 1) :
    ∑ k : Fin m, x ^ (k : ℕ) = if x = 1 then (m : ℂ) else 0 := by
  by_cases hx : x = 1
  · subst hx
    rw [if_pos rfl, Fin.sum_univ_eq_sum_range]
    simp only [one_pow, sum_const, card_range, nsmul_eq_mul, mul_one]
  · rw [if_neg hx, Fin.sum_univ_eq_sum_range]
    have hmul : (Finset.sum (Finset.range m) fun i => x ^ i) * (x - 1) = 0 := by
      simpa [hxpow] using (geom_sum_mul x m)
    exact (mul_eq_zero.mp hmul).resolve_right (sub_ne_zero.mpr hx)

/-- The Fourier coefficients for the projection sum vanish away from the zero mode. -/
private lemma coeff_sum_proj_of_primitiveRoot {γ : ℂ} (hγprim : IsPrimitiveRoot γ m)
    (j : ℕ) (hj : j < m) :
    ∑ k : Fin m, ((((star γ) ^ (k : ℕ)) ^ j : ℂ)) = if j = 0 then (m : ℂ) else 0 := by
  have hγinv_prim : IsPrimitiveRoot (γ⁻¹) m := hγprim.inv
  have hpowm : ((((star γ) ^ j : ℂ)) ^ m) = 1 := by
    calc
      ((((star γ) ^ j : ℂ)) ^ m) = (star γ : ℂ) ^ (j * m) := by rw [← pow_mul]
      _ = (star γ : ℂ) ^ (m * j) := by rw [Nat.mul_comm]
      _ = (((star γ : ℂ) ^ m) ^ j) := by rw [pow_mul]
      _ = 1 := by
          rw [star_eq_inv_of_primitiveRoot (m := m) hγprim]
          simp only [inv_pow, hγprim.pow_eq_one, inv_one, one_pow]
  have hrewrite :
      ∑ k : Fin m, ((((star γ) ^ (k : ℕ)) ^ j : ℂ)) =
        ∑ k : Fin m, ((((star γ) ^ j) ^ (k : ℕ) : ℂ)) := by
    apply Finset.sum_congr rfl
    intro k hk
    calc
      ((((star γ) ^ (k : ℕ)) ^ j : ℂ)) = (star γ : ℂ) ^ ((k : ℕ) * j) := by rw [← pow_mul]
      _ = (star γ : ℂ) ^ (j * (k : ℕ)) := by rw [Nat.mul_comm]
      _ = ((((star γ) ^ j) ^ (k : ℕ) : ℂ)) := by rw [pow_mul]
  rw [hrewrite, sum_powers_fin_of_pow_eq_one (m := m) ((star γ) ^ j) hpowm]
  by_cases hj0 : j = 0
  · subst hj0
    simp only [RCLike.star_def, pow_zero, ↓reduceIte]
  · have hne : ((star γ) ^ j : ℂ) ≠ 1 := by
      intro hpow
      have hdvd : m ∣ j :=
        (hγinv_prim.pow_eq_one_iff_dvd j).mp (by
          simpa [star_eq_inv_of_primitiveRoot (m := m) hγprim] using hpow)
      exact hj0 (Nat.eq_zero_of_dvd_of_lt hdvd hj)
    rw [if_neg hne, if_neg hj0]

/-- Convert the spectral reconstruction coefficients to a finite geometric sum. -/
private lemma cyclic_projection_step1_coeff_sum_spec_geometric {γ : ℂ}
    (hγprim : IsPrimitiveRoot γ m) (j : ℕ) :
    ∑ k : Fin m, (γ ^ (k : ℕ) * ((((star γ) ^ (k : ℕ)) ^ j : ℂ))) =
      if γ * (star γ) ^ j = 1 then (m : ℂ) else 0 := by
  have hpowm : (γ * (star γ) ^ j) ^ m = 1 := by
    calc
      (γ * (star γ) ^ j) ^ m = γ ^ m * ((((star γ) ^ j : ℂ)) ^ m) := by
        rw [mul_pow]
      _ = γ ^ m * (((star γ : ℂ) ^ m) ^ j) := by
        congr 1
        calc
          ((((star γ) ^ j : ℂ)) ^ m) = (star γ : ℂ) ^ (j * m) := by
            rw [← pow_mul]
          _ = (star γ : ℂ) ^ (m * j) := by
            rw [Nat.mul_comm]
          _ = (((star γ : ℂ) ^ m) ^ j) := by
            rw [pow_mul]
      _ = 1 := by
        rw [star_eq_inv_of_primitiveRoot (m := m) hγprim]
        simp only [hγprim.pow_eq_one, inv_pow, inv_one, one_pow, mul_one]
  have hrewrite :
      ∑ k : Fin m, (γ ^ (k : ℕ) * ((((star γ) ^ (k : ℕ)) ^ j : ℂ))) =
        ∑ k : Fin m, (γ * (star γ) ^ j) ^ (k : ℕ) := by
    apply Finset.sum_congr rfl
    intro k hk
    calc
      γ ^ (k : ℕ) * ((((star γ) ^ (k : ℕ)) ^ j : ℂ))
          = γ ^ (k : ℕ) * ((((star γ) ^ j) ^ (k : ℕ) : ℂ)) := by
              congr 1
              calc
                ((((star γ) ^ (k : ℕ)) ^ j : ℂ)) =
                    (star γ : ℂ) ^ ((k : ℕ) * j) := by
                  rw [← pow_mul]
                _ = (star γ : ℂ) ^ (j * (k : ℕ)) := by
                  rw [Nat.mul_comm]
                _ = ((((star γ) ^ j) ^ (k : ℕ) : ℂ)) := by
                  rw [pow_mul]
      _ = (γ * (star γ) ^ j) ^ (k : ℕ) := by
        rw [mul_pow]
  rw [hrewrite, sum_powers_fin_of_pow_eq_one (m := m) (γ * (star γ) ^ j) hpowm]

/-- The Fourier coefficients for the spectral expansion isolate the `oneIdx` mode. -/
private lemma coeff_sum_spec_of_primitiveRoot {γ : ℂ} (hγprim : IsPrimitiveRoot γ m)
    (j : ℕ) (hj : j < m) :
    ∑ k : Fin m, (γ ^ (k : ℕ) * ((((star γ) ^ (k : ℕ)) ^ j : ℂ))) =
      if j = cyclicOneIdx (m := m) then (m : ℂ) else 0 := by
  have honeIdx_lt : cyclicOneIdx (m := m) < m := by
    simpa [cyclicOneIdx] using ((1 : Fin m).is_lt)
  have honeIdx_mem : cyclicOneIdx (m := m) ∈ Finset.range m := by
    exact Finset.mem_range.mpr honeIdx_lt
  rw [cyclic_projection_step1_coeff_sum_spec_geometric (m := m) hγprim j]
  by_cases hjeq : j = cyclicOneIdx (m := m)
  · subst hjeq
    have hx : γ * (star γ) ^ cyclicOneIdx (m := m) = 1 := by
      calc
        γ * (star γ) ^ cyclicOneIdx (m := m) =
            γ ^ cyclicOneIdx (m := m) * (star γ) ^ cyclicOneIdx (m := m) := by
          rw [pow_oneIdx_of_primitiveRoot (m := m) hγprim]
        _ = 1 := pow_mul_star_pow_of_primitiveRoot (m := m) hγprim (cyclicOneIdx (m := m))
    rw [if_pos hx, if_pos rfl]
  · have hne : γ * (star γ) ^ j ≠ 1 := by
      intro hx
      have hpoweq : γ ^ cyclicOneIdx (m := m) = γ ^ j := by
        calc
          γ ^ cyclicOneIdx (m := m) = γ := pow_oneIdx_of_primitiveRoot (m := m) hγprim
          _ = γ * 1 := by simp only [mul_one]
          _ = γ * ((star γ) ^ j * γ ^ j) := by
                rw [star_pow_mul_pow_of_primitiveRoot (m := m) hγprim j]
          _ = (γ * (star γ) ^ j) * γ ^ j := by rw [mul_assoc]
          _ = 1 * γ ^ j := by rw [hx]
          _ = γ ^ j := by simp only [one_mul]
      have hidxeq : cyclicOneIdx (m := m) = j :=
        hγprim.injOn_pow honeIdx_mem (by simp only [coe_range, Set.mem_Iio, hj]) hpoweq
      exact hjeq hidxeq.symm
    rw [if_neg hne, if_neg hjeq]

/-- Multiplying by `γ` shifts the conjugate phase by one cyclic step. -/
private lemma base_cyclic_of_primitiveRoot {γ : ℂ} (hγprim : IsPrimitiveRoot γ m)
    (k : Fin m) : ((star γ) ^ (((k + 1 : Fin m) : ℕ)) : ℂ) * γ = (star γ) ^ (k : ℕ) := by
  have hm0 : m ≠ 0 := NeZero.ne m
  have hm_pos : 0 < m := Nat.pos_of_ne_zero hm0
  by_cases hk : (k : ℕ) + 1 < m
  · have hval : (((k + 1 : Fin m) : ℕ)) = (k : ℕ) + 1 := by
      simp only [Fin.val_add, Fin.coe_ofNat_eq_mod, Nat.add_mod_mod, Nat.mod_eq_of_lt hk]
    rw [hval, pow_succ, mul_assoc, star_mul_self_of_primitiveRoot (m := m) hγprim]
    simp only [RCLike.star_def, mul_one]
  · have hk_eq : (k : ℕ) + 1 = m := by
      have hle : m ≤ (k : ℕ) + 1 := by
        exact Nat.le_of_not_gt (by simpa using hk)
      exact le_antisymm (Nat.succ_le_of_lt k.is_lt) hle
    have hval0 : (((k + 1 : Fin m) : ℕ)) = 0 := by
      simp only [Fin.val_add, Fin.coe_ofNat_eq_mod, Nat.add_mod_mod, hk_eq, Nat.mod_self]
    rw [hval0, pow_zero, one_mul]
    have hkval : (k : ℕ) = m - 1 := Nat.eq_sub_of_add_eq hk_eq
    rw [hkval]
    have hpowm_star : (star γ : ℂ) ^ m = 1 := by
      rw [star_eq_inv_of_primitiveRoot (m := m) hγprim]
      simp only [inv_pow, hγprim.pow_eq_one, inv_one]
    have hmul : (star γ : ℂ) ^ (m - 1) * star γ = 1 := by
      calc
        (star γ : ℂ) ^ (m - 1) * star γ = (star γ : ℂ) ^ ((m - 1) + 1) := by
          simp only [RCLike.star_def, pow_succ]
        _ = 1 := by
          have hm' : (m - 1) + 1 = m := Nat.sub_add_cancel (Nat.succ_le_of_lt hm_pos)
          simpa [hm'] using hpowm_star
    have hpred : (star γ : ℂ) ^ (m - 1) = γ := by
      calc
        (star γ : ℂ) ^ (m - 1) = (star γ : ℂ)⁻¹ := eq_inv_of_mul_eq_one_left hmul
        _ = γ := by rw [star_eq_inv_of_primitiveRoot (m := m) hγprim, inv_inv]
    simpa using hpred.symm

/-- The cyclic projections are permuted by the peripheral map. -/
private lemma cyclic_action_of_cyclicProjection
    (T : MatrixEnd D) {γ : ℂ} (hγprim : IsPrimitiveRoot γ m)
    (U : Matrix.unitaryGroup (Fin D) ℂ)
    (hPow : ∀ k : ℕ, T ((U : MatrixAlg D) ^ k) = γ ^ k • ((U : MatrixAlg D) ^ k)) :
    ∀ k : Fin m, T (cyclicProjection (m := m) (γ := γ) U (k + 1)) =
      cyclicProjection (m := m) (γ := γ) U k := by
  intro k
  dsimp [cyclicProjection]
  calc
    T (((↑m : ℂ)⁻¹) • Finset.sum (Finset.range m)
        (fun j => ((((star γ) ^ (((k + 1 : Fin m) : ℕ))) ^ j : ℂ)) • ((U : MatrixAlg D) ^ j)))
        = (↑m : ℂ)⁻¹ • Finset.sum (Finset.range m)
            (fun j => ((((star γ) ^ (((k + 1 : Fin m) : ℕ))) ^ j : ℂ)) •
              T ((U : MatrixAlg D) ^ j)) := by
            simp only [RCLike.star_def, map_smul, map_sum]
    _ = (↑m : ℂ)⁻¹ • Finset.sum (Finset.range m)
          (fun j => (((((star γ) ^ (((k + 1 : Fin m) : ℕ))) ^ j : ℂ) * γ ^ j)) •
            ((U : MatrixAlg D) ^ j)) := by
          congr 2
          ext j
          rw [hPow j, smul_smul]
    _ = (↑m : ℂ)⁻¹ • Finset.sum (Finset.range m)
          (fun j => ((((star γ) ^ (k : ℕ)) ^ j : ℂ)) • ((U : MatrixAlg D) ^ j)) := by
          congr 2
          ext j
          have hcoef :
              ((((star γ) ^ (((k + 1 : Fin m) : ℕ))) ^ j : ℂ) * γ ^ j) =
                ((((star γ) ^ (k : ℕ)) ^ j : ℂ)) := by
            calc
              ((((star γ) ^ (((k + 1 : Fin m) : ℕ))) ^ j : ℂ) * γ ^ j)
                  = ((((star γ) ^ (((k + 1 : Fin m) : ℕ)) : ℂ) * γ) ^ j : ℂ) := by
                      rw [← mul_pow]
              _ = ((((star γ) ^ (k : ℕ)) ^ j : ℂ)) := by
                      rw [base_cyclic_of_primitiveRoot (m := m) hγprim k]
          rw [hcoef]

/-- The coefficients in the spectral sum satisfy the recursive step relation. -/
private lemma coeff_step_of_primitiveRoot {γ : ℂ} (hγprim : IsPrimitiveRoot γ m)
    (k : Fin m) (j : ℕ) :
    γ ^ (k : ℕ) * ((((star γ) ^ (k : ℕ)) ^ (j + 1) : ℂ)) =
      ((((star γ) ^ (k : ℕ)) ^ j : ℂ)) := by
  calc
    γ ^ (k : ℕ) * ((((star γ) ^ (k : ℕ)) ^ (j + 1) : ℂ))
        = γ ^ (k : ℕ) * (((star γ) ^ (k : ℕ)) * (((star γ) ^ (k : ℕ)) ^ j)) := by
            rw [pow_succ']
    _ = (γ ^ (k : ℕ) * ((star γ) ^ (k : ℕ))) * (((star γ) ^ (k : ℕ)) ^ j) := by
            rw [mul_assoc]
    _ = ((((star γ) ^ (k : ℕ)) ^ j : ℂ)) := by
            rw [pow_mul_star_pow_of_primitiveRoot (m := m) hγprim (k : ℕ)]
            simp only [RCLike.star_def, one_mul]

/-- The last coefficient in the spectral sum closes the cyclic recursion. -/
private lemma coeff_last_of_primitiveRoot {γ : ℂ} (hγprim : IsPrimitiveRoot γ m)
    (k : Fin m) : ((((star γ) ^ (k : ℕ)) ^ (m - 1) : ℂ)) = γ ^ (k : ℕ) := by
  have hm0 : m ≠ 0 := NeZero.ne m
  have hm_pos : 0 < m := Nat.pos_of_ne_zero hm0
  have hpowm : ((((star γ) ^ (k : ℕ) : ℂ)) ^ m) = 1 := by
    calc
      ((((star γ) ^ (k : ℕ) : ℂ)) ^ m) = (star γ : ℂ) ^ ((k : ℕ) * m) := by rw [← pow_mul]
      _ = (star γ : ℂ) ^ (m * (k : ℕ)) := by rw [Nat.mul_comm]
      _ = (((star γ : ℂ) ^ m) ^ (k : ℕ)) := by rw [pow_mul]
      _ = 1 := by
          rw [star_eq_inv_of_primitiveRoot (m := m) hγprim]
          simp only [inv_pow, hγprim.pow_eq_one, inv_one, one_pow]
  have hmul : ((((star γ) ^ (k : ℕ) : ℂ)) ^ (m - 1)) * ((star γ) ^ (k : ℕ)) = 1 := by
    calc
      ((((star γ) ^ (k : ℕ) : ℂ)) ^ (m - 1)) * ((star γ) ^ (k : ℕ))
          = (((star γ) ^ (k : ℕ) : ℂ)) ^ ((m - 1) + 1) := by
              simp only [RCLike.star_def, pow_succ]
      _ = 1 := by
          have hm' : (m - 1) + 1 = m := Nat.sub_add_cancel (Nat.succ_le_of_lt hm_pos)
          simpa [hm'] using hpowm
  calc
    ((((star γ) ^ (k : ℕ) : ℂ)) ^ (m - 1)) = (((star γ) ^ (k : ℕ) : ℂ))⁻¹ :=
      eq_inv_of_mul_eq_one_left hmul
    _ = γ ^ (k : ℕ) := by
      rw [star_eq_inv_of_primitiveRoot (m := m) hγprim, inv_pow]
      simp only [inv_inv]

/-- Move the unitary through the Fourier sum, leaving the cyclically shifted coefficients. -/
private lemma cyclic_projection_step2_left_mul_shifted_sum {γ : ℂ}
    (hγprim : IsPrimitiveRoot γ m)
    (U : Matrix.unitaryGroup (Fin D) ℂ) (hUm : ((U : MatrixAlg D) ^ m) = 1)
    (k : Fin m) :
    (U : MatrixAlg D) * cyclicProjection (m := m) (γ := γ) U k =
      (↑m : ℂ)⁻¹ •
        (Finset.sum (Finset.range (m - 1))
            (fun j => (γ ^ (k : ℕ) *
              ((((star γ) ^ (k : ℕ)) ^ (j + 1) : ℂ))) •
                ((U : MatrixAlg D) ^ (j + 1))) +
          γ ^ (k : ℕ) • (1 : MatrixAlg D)) := by
  let a : ℕ → ℂ := fun j => ((((star γ) ^ (k : ℕ)) ^ j : ℂ))
  have hm0 : m ≠ 0 := NeZero.ne m
  have hm_pos : 0 < m := Nat.pos_of_ne_zero hm0
  have hm_pred_succ : (m - 1) + 1 = m := Nat.sub_add_cancel (Nat.succ_le_of_lt hm_pos)
  dsimp [cyclicProjection]
  change
    (U : MatrixAlg D) *
        ((↑m : ℂ)⁻¹ • Finset.sum (Finset.range m) (fun j => a j • ((U : MatrixAlg D) ^ j))) =
      (↑m : ℂ)⁻¹ •
        (Finset.sum (Finset.range (m - 1))
            (fun j => (γ ^ (k : ℕ) * a (j + 1)) • ((U : MatrixAlg D) ^ (j + 1))) +
          γ ^ (k : ℕ) • (1 : MatrixAlg D))
  calc
    (U : MatrixAlg D) *
        ((↑m : ℂ)⁻¹ • Finset.sum (Finset.range m) (fun j => a j • ((U : MatrixAlg D) ^ j)))
        = (↑m : ℂ)⁻¹ •
            ((U : MatrixAlg D) *
              Finset.sum (Finset.range m) (fun j => a j • ((U : MatrixAlg D) ^ j))) := by
              rw [Matrix.mul_smul]
    _ = (↑m : ℂ)⁻¹ • Finset.sum (Finset.range m)
          (fun j => a j • ((U : MatrixAlg D) * ((U : MatrixAlg D) ^ j))) := by
          congr 1
          simp only [mul_sum, Algebra.mul_smul_comm]
    _ = (↑m : ℂ)⁻¹ • Finset.sum (Finset.range m)
          (fun j => a j • ((U : MatrixAlg D) ^ (j + 1))) := by
          congr 2
          ext j
          rw [pow_succ']
    _ = (↑m : ℂ)⁻¹ •
          (Finset.sum (Finset.range (m - 1)) (fun j => a j • ((U : MatrixAlg D) ^ (j + 1))) +
            a (m - 1) • ((U : MatrixAlg D) ^ m)) := by
          have hsplit :
              Finset.sum (Finset.range m) (fun j => a j • ((U : MatrixAlg D) ^ (j + 1))) =
                Finset.sum (Finset.range (m - 1))
                  (fun j => a j • ((U : MatrixAlg D) ^ (j + 1))) +
                  a (m - 1) • ((U : MatrixAlg D) ^ m) := by
            simpa [hm_pred_succ] using
              (Finset.sum_range_succ
                (fun j : ℕ => a j • ((U : MatrixAlg D) ^ (j + 1)))
                (m - 1))
          rw [hsplit]
    _ = (↑m : ℂ)⁻¹ •
          (Finset.sum (Finset.range (m - 1))
              (fun j => (γ ^ (k : ℕ) * a (j + 1)) • ((U : MatrixAlg D) ^ (j + 1))) +
            γ ^ (k : ℕ) • (1 : MatrixAlg D)) := by
          congr 2
          · apply Finset.sum_congr rfl
            intro j hj
            have ha : a j = γ ^ (k : ℕ) * a (j + 1) := by
              dsimp [a]
              exact (coeff_step_of_primitiveRoot (m := m) hγprim k j).symm
            rw [ha]
          · change
              ((((star γ) ^ (k : ℕ)) ^ (m - 1) : ℂ)) • ((U : MatrixAlg D) ^ m) =
                γ ^ (k : ℕ) • (1 : MatrixAlg D)
            rw [coeff_last_of_primitiveRoot (m := m) hγprim k, hUm]

/-- Reassemble the shifted Fourier sum as scalar multiplication of the cyclic projection. -/
private lemma cyclic_projection_step3_shifted_sum_eq_smul {γ : ℂ}
    (U : Matrix.unitaryGroup (Fin D) ℂ) (k : Fin m) :
    (↑m : ℂ)⁻¹ •
      (Finset.sum (Finset.range (m - 1))
          (fun j => (γ ^ (k : ℕ) *
            ((((star γ) ^ (k : ℕ)) ^ (j + 1) : ℂ))) •
              ((U : MatrixAlg D) ^ (j + 1))) +
        γ ^ (k : ℕ) • (1 : MatrixAlg D)) =
      γ ^ (k : ℕ) • cyclicProjection (m := m) (γ := γ) U k := by
  let a : ℕ → ℂ := fun j => ((((star γ) ^ (k : ℕ)) ^ j : ℂ))
  have hm0 : m ≠ 0 := NeZero.ne m
  have hm_pos : 0 < m := Nat.pos_of_ne_zero hm0
  have hm_pred_succ : (m - 1) + 1 = m := Nat.sub_add_cancel (Nat.succ_le_of_lt hm_pos)
  have hdecomp :
      Finset.sum (Finset.range (m - 1))
          (fun j => a (j + 1) • ((U : MatrixAlg D) ^ (j + 1))) + 1 =
        Finset.sum (Finset.range m) (fun j => a j • ((U : MatrixAlg D) ^ j)) := by
    simpa [hm_pred_succ, a] using
      (Finset.sum_range_succ' (fun j : ℕ => a j • ((U : MatrixAlg D) ^ j)) (m - 1)).symm
  have hfactor :
      Finset.sum (Finset.range (m - 1))
          (fun j => (γ ^ (k : ℕ) * a (j + 1)) • ((U : MatrixAlg D) ^ (j + 1))) =
        γ ^ (k : ℕ) • Finset.sum (Finset.range (m - 1))
          (fun j => a (j + 1) • ((U : MatrixAlg D) ^ (j + 1))) := by
    calc
      Finset.sum (Finset.range (m - 1))
          (fun j => (γ ^ (k : ℕ) * a (j + 1)) • ((U : MatrixAlg D) ^ (j + 1)))
          = Finset.sum (Finset.range (m - 1))
              (fun j => γ ^ (k : ℕ) • (a (j + 1) • ((U : MatrixAlg D) ^ (j + 1)))) := by
                apply Finset.sum_congr rfl
                intro j hj
                rw [smul_smul]
      _ = γ ^ (k : ℕ) • Finset.sum (Finset.range (m - 1))
              (fun j => a (j + 1) • ((U : MatrixAlg D) ^ (j + 1))) := by
                rw [Finset.smul_sum]
  dsimp [cyclicProjection]
  change
    (↑m : ℂ)⁻¹ •
      (Finset.sum (Finset.range (m - 1))
          (fun j => (γ ^ (k : ℕ) * a (j + 1)) • ((U : MatrixAlg D) ^ (j + 1))) +
        γ ^ (k : ℕ) • (1 : MatrixAlg D)) =
      γ ^ (k : ℕ) •
        ((↑m : ℂ)⁻¹ • Finset.sum (Finset.range m) (fun j => a j • ((U : MatrixAlg D) ^ j)))
  calc
    (↑m : ℂ)⁻¹ •
        (Finset.sum (Finset.range (m - 1))
            (fun j => (γ ^ (k : ℕ) * a (j + 1)) • ((U : MatrixAlg D) ^ (j + 1))) +
          γ ^ (k : ℕ) • (1 : MatrixAlg D))
        = (↑m : ℂ)⁻¹ •
          (γ ^ (k : ℕ) •
            (Finset.sum (Finset.range (m - 1))
                (fun j => a (j + 1) • ((U : MatrixAlg D) ^ (j + 1))) +
              1)) := by
          rw [hfactor, smul_add]
          simp only [smul_smul, smul_add]
    _ = (↑m : ℂ)⁻¹ •
          (γ ^ (k : ℕ) •
            Finset.sum (Finset.range m) (fun j => a j • ((U : MatrixAlg D) ^ j))) := by
          rw [hdecomp]
    _ = γ ^ (k : ℕ) •
          ((↑m : ℂ)⁻¹ •
            Finset.sum (Finset.range m) (fun j => a j • ((U : MatrixAlg D) ^ j))) := by
          simp only [smul_smul, mul_comm]

/-- Left multiplication by `U` diagonalizes on the cyclic projections. -/
private lemma left_mul_cyclicProjection_eq {γ : ℂ} (hγprim : IsPrimitiveRoot γ m)
    (U : Matrix.unitaryGroup (Fin D) ℂ) (hUm : ((U : MatrixAlg D) ^ m) = 1) :
    ∀ k : Fin m,
      (U : MatrixAlg D) * cyclicProjection (m := m) (γ := γ) U k =
        γ ^ (k : ℕ) • cyclicProjection (m := m) (γ := γ) U k := by
  intro k
  calc
    (U : MatrixAlg D) * cyclicProjection (m := m) (γ := γ) U k =
        (↑m : ℂ)⁻¹ •
          (Finset.sum (Finset.range (m - 1))
              (fun j => (γ ^ (k : ℕ) *
                ((((star γ) ^ (k : ℕ)) ^ (j + 1) : ℂ))) •
                  ((U : MatrixAlg D) ^ (j + 1))) +
            γ ^ (k : ℕ) • (1 : MatrixAlg D)) := by
          exact cyclic_projection_step2_left_mul_shifted_sum (m := m) hγprim U hUm k
    _ = γ ^ (k : ℕ) • cyclicProjection (m := m) (γ := γ) U k := by
          exact cyclic_projection_step3_shifted_sum_eq_smul (m := m) (γ := γ) U k

omit [NeZero m] in
/-- Each cyclic projection commutes with the generating unitary. -/
private lemma commute_unitary_cyclicProjection {γ : ℂ}
    (U : Matrix.unitaryGroup (Fin D) ℂ) :
    ∀ k : Fin m, Commute (U : MatrixAlg D) (cyclicProjection (m := m) (γ := γ) U k) := by
  intro k
  dsimp [cyclicProjection]
  refine (Commute.sum_right (Finset.range m)
    (fun j : ℕ => ((((star γ) ^ (k : ℕ)) ^ j : ℂ)) • ((U : MatrixAlg D) ^ j))
    (U : MatrixAlg D) ?_).smul_right ((↑m : ℂ)⁻¹)
  intro j hj
  exact ((Commute.refl (U : MatrixAlg D)).pow_right j).smul_right _

/-- Right multiplication by `U` has the same eigenvalue on each cyclic projection. -/
private lemma right_mul_cyclicProjection_eq {γ : ℂ} (hγprim : IsPrimitiveRoot γ m)
    (U : Matrix.unitaryGroup (Fin D) ℂ) (hUm : ((U : MatrixAlg D) ^ m) = 1) :
    ∀ k : Fin m,
      cyclicProjection (m := m) (γ := γ) U k * (U : MatrixAlg D) =
        γ ^ (k : ℕ) • cyclicProjection (m := m) (γ := γ) U k := by
  intro k
  rw [← (commute_unitary_cyclicProjection (m := m) (γ := γ) U k).eq]
  exact left_mul_cyclicProjection_eq (m := m) hγprim U hUm k

/-- The cyclic projections sum to the identity. -/
private lemma sum_cyclicProjection_eq_one {γ : ℂ} (hγprim : IsPrimitiveRoot γ m)
    (U : Matrix.unitaryGroup (Fin D) ℂ) :
    ∑ k : Fin m, cyclicProjection (m := m) (γ := γ) U k = 1 := by
  dsimp [cyclicProjection]
  calc
    ∑ k : Fin m, (↑m : ℂ)⁻¹ •
        Finset.sum (Finset.range m)
          (fun j => ((((star γ) ^ (k : ℕ)) ^ j : ℂ)) • ((U : MatrixAlg D) ^ j))
        = (↑m : ℂ)⁻¹ • ∑ k : Fin m,
            Finset.sum (Finset.range m)
              (fun j => ((((star γ) ^ (k : ℕ)) ^ j : ℂ)) • ((U : MatrixAlg D) ^ j)) := by
            symm
            rw [Finset.smul_sum]
    _ = (↑m : ℂ)⁻¹ • Finset.sum (Finset.range m)
          (fun j =>
            ∑ k : Fin m, ((((star γ) ^ (k : ℕ)) ^ j : ℂ)) • ((U : MatrixAlg D) ^ j)) := by
          refine congrArg (fun S => (↑m : ℂ)⁻¹ • S) ?_
          rw [Finset.sum_comm]
    _ = (↑m : ℂ)⁻¹ • Finset.sum (Finset.range m)
          (fun j =>
            (∑ k : Fin m, ((((star γ) ^ (k : ℕ)) ^ j : ℂ))) • ((U : MatrixAlg D) ^ j)) := by
          refine congrArg (fun S => (↑m : ℂ)⁻¹ • S) ?_
          apply Finset.sum_congr rfl
          intro j hj
          rw [← Finset.sum_smul]
    _ = (↑m : ℂ)⁻¹ • Finset.sum (Finset.range m)
          (fun j => (if j = 0 then (m : ℂ) else 0) • ((U : MatrixAlg D) ^ j)) := by
          refine congrArg (fun S => (↑m : ℂ)⁻¹ • S) ?_
          apply Finset.sum_congr rfl
          intro j hj
          rw [coeff_sum_proj_of_primitiveRoot (m := m) hγprim j (Finset.mem_range.mp hj)]
    _ = (↑m : ℂ)⁻¹ • ((m : ℂ) • ((U : MatrixAlg D) ^ 0)) := by
          rw [Finset.sum_eq_single 0]
          · simp only [↓reduceIte, pow_zero]
          · intro j hj hj0
            simp only [hj0, ↓reduceIte, zero_smul]
          · intro hm
            exfalso
            have hm0 : m ≠ 0 := NeZero.ne m
            exact hm (by simp only [mem_range, Nat.pos_of_ne_zero hm0])
    _ = 1 := by
          simp only [
            pow_zero, ne_eq, Nat.cast_eq_zero, NeZero.ne m, not_false_eq_true,
            inv_smul_smul₀
          ]

/-- Summing the cyclic projections against their phases reconstructs `U`. -/
private lemma unitary_eq_sum_cyclicProjection {γ : ℂ} (hγprim : IsPrimitiveRoot γ m)
    (U : Matrix.unitaryGroup (Fin D) ℂ) (hUm : ((U : MatrixAlg D) ^ m) = 1) :
    ∑ k : Fin m, γ ^ (k : ℕ) • cyclicProjection (m := m) (γ := γ) U k = (U : MatrixAlg D) := by
  have honeIdx_lt : cyclicOneIdx (m := m) < m := by
    simpa [cyclicOneIdx] using ((1 : Fin m).is_lt)
  have honeIdx_mem : cyclicOneIdx (m := m) ∈ Finset.range m := by
    exact Finset.mem_range.mpr honeIdx_lt
  dsimp [cyclicProjection]
  calc
    ∑ k : Fin m, γ ^ (k : ℕ) •
        ((↑m : ℂ)⁻¹ • Finset.sum (Finset.range m)
          (fun j => ((((star γ) ^ (k : ℕ)) ^ j : ℂ)) • ((U : MatrixAlg D) ^ j)))
        = (↑m : ℂ)⁻¹ • ∑ k : Fin m,
            Finset.sum (Finset.range m)
              (fun j =>
                (γ ^ (k : ℕ) * ((((star γ) ^ (k : ℕ)) ^ j : ℂ))) •
                  ((U : MatrixAlg D) ^ j)) := by
            calc
              ∑ k : Fin m, γ ^ (k : ℕ) •
                  ((↑m : ℂ)⁻¹ • Finset.sum (Finset.range m)
                    (fun j => ((((star γ) ^ (k : ℕ)) ^ j : ℂ)) • ((U : MatrixAlg D) ^ j)))
                  = ∑ k : Fin m, (↑m : ℂ)⁻¹ •
                      (γ ^ (k : ℕ) • Finset.sum (Finset.range m)
                        (fun j =>
                          ((((star γ) ^ (k : ℕ)) ^ j : ℂ)) • ((U : MatrixAlg D) ^ j))) := by
                      apply Finset.sum_congr rfl
                      intro k hk
                      simp only [RCLike.star_def, smul_smul, mul_comm]
              _ = (↑m : ℂ)⁻¹ • ∑ k : Fin m,
                      γ ^ (k : ℕ) • Finset.sum (Finset.range m)
                        (fun j =>
                          ((((star γ) ^ (k : ℕ)) ^ j : ℂ)) • ((U : MatrixAlg D) ^ j)) := by
                      symm
                      rw [Finset.smul_sum]
              _ = (↑m : ℂ)⁻¹ • ∑ k : Fin m,
                      Finset.sum (Finset.range m)
                        (fun j =>
                          (γ ^ (k : ℕ) * ((((star γ) ^ (k : ℕ)) ^ j : ℂ))) •
                            ((U : MatrixAlg D) ^ j)) := by
                      refine congrArg (fun S => (↑m : ℂ)⁻¹ • S) ?_
                      apply Finset.sum_congr rfl
                      intro k hk
                      rw [Finset.smul_sum]
                      apply Finset.sum_congr rfl
                      intro j hj
                      rw [smul_smul]
    _ = (↑m : ℂ)⁻¹ • Finset.sum (Finset.range m)
          (fun j =>
            ∑ k : Fin m,
              (γ ^ (k : ℕ) * ((((star γ) ^ (k : ℕ)) ^ j : ℂ))) • ((U : MatrixAlg D) ^ j)) := by
          refine congrArg (fun S => (↑m : ℂ)⁻¹ • S) ?_
          rw [Finset.sum_comm]
    _ = (↑m : ℂ)⁻¹ • Finset.sum (Finset.range m)
          (fun j =>
            (∑ k : Fin m, γ ^ (k : ℕ) * ((((star γ) ^ (k : ℕ)) ^ j : ℂ))) •
              ((U : MatrixAlg D) ^ j)) := by
          refine congrArg (fun S => (↑m : ℂ)⁻¹ • S) ?_
          apply Finset.sum_congr rfl
          intro j hj
          rw [← Finset.sum_smul]
    _ = (↑m : ℂ)⁻¹ • Finset.sum (Finset.range m)
          (fun j => (if j = cyclicOneIdx (m := m) then (m : ℂ) else 0) •
            ((U : MatrixAlg D) ^ j)) := by
          refine congrArg (fun S => (↑m : ℂ)⁻¹ • S) ?_
          apply Finset.sum_congr rfl
          intro j hj
          rw [coeff_sum_spec_of_primitiveRoot (m := m) hγprim j (Finset.mem_range.mp hj)]
    _ = (↑m : ℂ)⁻¹ • ((m : ℂ) • ((U : MatrixAlg D) ^ cyclicOneIdx (m := m))) := by
          rw [Finset.sum_eq_single (cyclicOneIdx (m := m))]
          · simp only [Fin.coe_ofNat_eq_mod, ↓reduceIte]
          · intro j hj hj0
            have hif : (if j = cyclicOneIdx (m := m) then (m : ℂ) else 0) = 0 := by
              by_cases hjeq : j = cyclicOneIdx (m := m)
              · exact (hj0 hjeq).elim
              · exact if_neg hjeq
            rw [hif]
            simp only [zero_smul]
          · intro hnot
            exact False.elim (hnot honeIdx_mem)
    _ = (U : MatrixAlg D) := by
          rw [unitary_pow_oneIdx_of_pow_eq_one (m := m) U hUm]
          simp only [ne_eq, Nat.cast_eq_zero, NeZero.ne m, not_false_eq_true, inv_smul_smul₀]

omit [NeZero m] in
/-- Distinct exponents of a primitive root stay distinct on `Fin m`. -/
private lemma pow_inj_of_primitiveRoot {γ : ℂ} (hγprim : IsPrimitiveRoot γ m) :
    ∀ {a b : Fin m}, γ ^ (a : ℕ) = γ ^ (b : ℕ) → a = b := by
  intro a b hab
  apply Fin.ext
  exact hγprim.injOn_pow
    (by simp only [coe_range, Set.mem_Iio, a.is_lt])
    (by simp only [coe_range, Set.mem_Iio, b.is_lt])
    hab

/-- The product of two cyclic projections is simultaneously a left eigenvector in both indices. -/
private lemma cyclic_projection_step4_mul_projection_eigen_relations {γ : ℂ}
    (hγprim : IsPrimitiveRoot γ m)
    (U : Matrix.unitaryGroup (Fin D) ℂ) (hUm : ((U : MatrixAlg D) ^ m) = 1)
    (k l : Fin m) :
    (U : MatrixAlg D) *
          (cyclicProjection (m := m) (γ := γ) U k *
            cyclicProjection (m := m) (γ := γ) U l) =
        γ ^ (k : ℕ) •
          (cyclicProjection (m := m) (γ := γ) U k *
            cyclicProjection (m := m) (γ := γ) U l) ∧
      (U : MatrixAlg D) *
          (cyclicProjection (m := m) (γ := γ) U k *
            cyclicProjection (m := m) (γ := γ) U l) =
        γ ^ (l : ℕ) •
          (cyclicProjection (m := m) (γ := γ) U k *
            cyclicProjection (m := m) (γ := γ) U l) := by
  constructor
  · calc
      (U : MatrixAlg D) *
          (cyclicProjection (m := m) (γ := γ) U k * cyclicProjection (m := m) (γ := γ) U l) =
        ((U : MatrixAlg D) * cyclicProjection (m := m) (γ := γ) U k) *
          cyclicProjection (m := m) (γ := γ) U l := by
            simp only [Matrix.mul_assoc]
      _ = (γ ^ (k : ℕ) • cyclicProjection (m := m) (γ := γ) U k) *
            cyclicProjection (m := m) (γ := γ) U l := by
              rw [left_mul_cyclicProjection_eq (m := m) hγprim U hUm k]
      _ = γ ^ (k : ℕ) •
            (cyclicProjection (m := m) (γ := γ) U k * cyclicProjection (m := m) (γ := γ) U l) := by
            simp only [Algebra.smul_mul_assoc]
  · calc
      (U : MatrixAlg D) *
          (cyclicProjection (m := m) (γ := γ) U k * cyclicProjection (m := m) (γ := γ) U l) =
        ((U : MatrixAlg D) * cyclicProjection (m := m) (γ := γ) U k) *
          cyclicProjection (m := m) (γ := γ) U l := by
            simp only [Matrix.mul_assoc]
      _ = (cyclicProjection (m := m) (γ := γ) U k * (U : MatrixAlg D)) *
            cyclicProjection (m := m) (γ := γ) U l := by
              rw [(commute_unitary_cyclicProjection (m := m) (γ := γ) U k).eq]
      _ = cyclicProjection (m := m) (γ := γ) U k *
            ((U : MatrixAlg D) * cyclicProjection (m := m) (γ := γ) U l) := by
              simp only [Matrix.mul_assoc]
      _ = cyclicProjection (m := m) (γ := γ) U k *
            (γ ^ (l : ℕ) • cyclicProjection (m := m) (γ := γ) U l) := by
              rw [left_mul_cyclicProjection_eq (m := m) hγprim U hUm l]
      _ = γ ^ (l : ℕ) •
            (cyclicProjection (m := m) (γ := γ) U k *
              cyclicProjection (m := m) (γ := γ) U l) := by
            simp only [Algebra.mul_smul_comm]

/-- Distinct cyclic projections are orthogonal. -/
private lemma mul_cyclicProjection_eq_zero_of_ne {γ : ℂ} (hγprim : IsPrimitiveRoot γ m)
    (U : Matrix.unitaryGroup (Fin D) ℂ) (hUm : ((U : MatrixAlg D) ^ m) = 1)
    {k l : Fin m} (hkl : k ≠ l) :
    cyclicProjection (m := m) (γ := γ) U k * cyclicProjection (m := m) (γ := γ) U l = 0 := by
  obtain ⟨hkEig, hlEig⟩ :=
    cyclic_projection_step4_mul_projection_eigen_relations (m := m) hγprim U hUm k l
  have hsub :
      (γ ^ (k : ℕ) - γ ^ (l : ℕ)) •
          (cyclicProjection (m := m) (γ := γ) U k *
            cyclicProjection (m := m) (γ := γ) U l) = 0 := by
    calc
      (γ ^ (k : ℕ) - γ ^ (l : ℕ)) •
          (cyclicProjection (m := m) (γ := γ) U k *
            cyclicProjection (m := m) (γ := γ) U l)
          = γ ^ (k : ℕ) •
              (cyclicProjection (m := m) (γ := γ) U k *
                cyclicProjection (m := m) (γ := γ) U l) -
              γ ^ (l : ℕ) •
                (cyclicProjection (m := m) (γ := γ) U k *
                  cyclicProjection (m := m) (γ := γ) U l) := by
                  simp only [sub_smul]
      _ = 0 := by rw [← hkEig, ← hlEig]; simp only [sub_self]
  have hneq : γ ^ (k : ℕ) - γ ^ (l : ℕ) ≠ 0 := by
    refine sub_ne_zero.mpr ?_
    intro hpow
    exact hkl (pow_inj_of_primitiveRoot (m := m) hγprim hpow)
  exact (smul_eq_zero.mp hsub).resolve_left hneq

/-- Each cyclic projection is idempotent. -/
private lemma idem_cyclicProjection {γ : ℂ} (hγprim : IsPrimitiveRoot γ m)
    (U : Matrix.unitaryGroup (Fin D) ℂ) (hUm : ((U : MatrixAlg D) ^ m) = 1) :
    ∀ k : Fin m,
      cyclicProjection (m := m) (γ := γ) U k * cyclicProjection (m := m) (γ := γ) U k =
        cyclicProjection (m := m) (γ := γ) U k := by
  intro k
  have hsingle :
      ∑ l : Fin m,
          cyclicProjection (m := m) (γ := γ) U k * cyclicProjection (m := m) (γ := γ) U l =
        cyclicProjection (m := m) (γ := γ) U k * cyclicProjection (m := m) (γ := γ) U k := by
    exact Finset.sum_eq_single_of_mem k (Finset.mem_univ k) (by
      intro l hl hne
      simpa using mul_cyclicProjection_eq_zero_of_ne (m := m) hγprim U hUm hne.symm)
  have hEq :
      cyclicProjection (m := m) (γ := γ) U k =
        cyclicProjection (m := m) (γ := γ) U k * cyclicProjection (m := m) (γ := γ) U k := by
    calc
      cyclicProjection (m := m) (γ := γ) U k =
          cyclicProjection (m := m) (γ := γ) U k * (1 : MatrixAlg D) := by simp only [mul_one]
      _ = cyclicProjection (m := m) (γ := γ) U k *
            (∑ l : Fin m, cyclicProjection (m := m) (γ := γ) U l) := by
              rw [sum_cyclicProjection_eq_one (m := m) hγprim U]
      _ = ∑ l : Fin m,
            cyclicProjection (m := m) (γ := γ) U k * cyclicProjection (m := m) (γ := γ) U l := by
              simp only [mul_sum]
      _ = cyclicProjection (m := m) (γ := γ) U k * cyclicProjection (m := m) (γ := γ) U k := hsingle
  exact hEq.symm

/-- The adjoint of a cyclic projection has the same left eigenvalue under `U`. -/
private lemma unitary_mul_star_cyclicProjection_eq {γ : ℂ} (hγprim : IsPrimitiveRoot γ m)
    (U : Matrix.unitaryGroup (Fin D) ℂ) (hUm : ((U : MatrixAlg D) ^ m) = 1) :
    ∀ k : Fin m,
      (U : MatrixAlg D) * (cyclicProjection (m := m) (γ := γ) U k)ᴴ =
        γ ^ (k : ℕ) • (cyclicProjection (m := m) (γ := γ) U k)ᴴ := by
  intro k
  have hstar :
      (U : MatrixAlg D)ᴴ * (cyclicProjection (m := m) (γ := γ) U k)ᴴ =
        star (γ ^ (k : ℕ)) • (cyclicProjection (m := m) (γ := γ) U k)ᴴ := by
    simpa [Matrix.conjTranspose_mul, Matrix.conjTranspose_smul] using
      congrArg Matrix.conjTranspose
        (right_mul_cyclicProjection_eq (m := m) hγprim U hUm k)
  have hU_mul_star : (U : MatrixAlg D) * (U : MatrixAlg D)ᴴ = 1 := by
    exact U.2.2
  have hpre :
      (cyclicProjection (m := m) (γ := γ) U k)ᴴ =
        star (γ ^ (k : ℕ)) • ((U : MatrixAlg D) * (cyclicProjection (m := m) (γ := γ) U k)ᴴ) := by
    calc
      (cyclicProjection (m := m) (γ := γ) U k)ᴴ = (1 : MatrixAlg D) * (cyclicProjection
          (m := m) (γ := γ) U k)ᴴ := by simp only [one_mul]
      _ = ((U : MatrixAlg D) * (U : MatrixAlg D)ᴴ) *
            (cyclicProjection (m := m) (γ := γ) U k)ᴴ := by rw [hU_mul_star]
      _ = (U : MatrixAlg D) * ((U : MatrixAlg D)ᴴ *
            (cyclicProjection (m := m) (γ := γ) U k)ᴴ) := by
              simp only [Matrix.mul_assoc]
      _ = (U : MatrixAlg D) *
            (star (γ ^ (k : ℕ)) • (cyclicProjection (m := m) (γ := γ) U k)ᴴ) := by
              rw [hstar]
      _ = star (γ ^ (k : ℕ)) • ((U : MatrixAlg D) *
            (cyclicProjection (m := m) (γ := γ) U k)ᴴ) := by
              rw [Matrix.mul_smul]
  have hunit : γ ^ (k : ℕ) * star (γ ^ (k : ℕ)) = 1 := by
    simpa using pow_mul_star_pow_of_primitiveRoot (m := m) hγprim (k : ℕ)
  have hmain :
      (U : MatrixAlg D) * (cyclicProjection (m := m) (γ := γ) U k)ᴴ =
        γ ^ (k : ℕ) • (cyclicProjection (m := m) (γ := γ) U k)ᴴ := by
    calc
      (U : MatrixAlg D) * (cyclicProjection (m := m) (γ := γ) U k)ᴴ =
          (1 : ℂ) • ((U : MatrixAlg D) * (cyclicProjection (m := m) (γ := γ) U k)ᴴ) := by
            simp only [one_smul]
      _ = (γ ^ (k : ℕ) * star (γ ^ (k : ℕ))) •
            ((U : MatrixAlg D) * (cyclicProjection (m := m) (γ := γ) U k)ᴴ) := by
              rw [← hunit]
      _ = γ ^ (k : ℕ) •
            (star (γ ^ (k : ℕ)) • ((U : MatrixAlg D) *
              (cyclicProjection (m := m) (γ := γ) U k)ᴴ)) := by
              rw [smul_smul]
      _ = γ ^ (k : ℕ) • (cyclicProjection (m := m) (γ := γ) U k)ᴴ := by rw [← hpre]
  exact hmain

/-- Distinct cyclic projections are orthogonal to the adjoint of the others. -/
private lemma mul_star_cyclicProjection_eq_zero_of_ne {γ : ℂ} (hγprim : IsPrimitiveRoot γ m)
    (U : Matrix.unitaryGroup (Fin D) ℂ) (hUm : ((U : MatrixAlg D) ^ m) = 1)
    {k l : Fin m} (hkl : k ≠ l) :
    cyclicProjection (m := m) (γ := γ) U l * (cyclicProjection (m := m) (γ := γ) U k)ᴴ = 0 := by
  have hlEig :
      (U : MatrixAlg D) *
          (cyclicProjection (m := m) (γ := γ) U l *
            (cyclicProjection (m := m) (γ := γ) U k)ᴴ) =
        γ ^ (l : ℕ) •
          (cyclicProjection (m := m) (γ := γ) U l *
            (cyclicProjection (m := m) (γ := γ) U k)ᴴ) := by
    calc
      (U : MatrixAlg D) *
          (cyclicProjection (m := m) (γ := γ) U l *
            (cyclicProjection (m := m) (γ := γ) U k)ᴴ) =
        ((U : MatrixAlg D) * cyclicProjection (m := m) (γ := γ) U l) *
          (cyclicProjection (m := m) (γ := γ) U k)ᴴ := by
            simp only [Matrix.mul_assoc]
      _ = (γ ^ (l : ℕ) • cyclicProjection (m := m) (γ := γ) U l) *
            (cyclicProjection (m := m) (γ := γ) U k)ᴴ := by
              rw [left_mul_cyclicProjection_eq (m := m) hγprim U hUm l]
      _ = γ ^ (l : ℕ) •
            (cyclicProjection (m := m) (γ := γ) U l *
              (cyclicProjection (m := m) (γ := γ) U k)ᴴ) := by
            simp only [Algebra.smul_mul_assoc]
  have hkEig :
      (U : MatrixAlg D) *
          (cyclicProjection (m := m) (γ := γ) U l *
            (cyclicProjection (m := m) (γ := γ) U k)ᴴ) =
        γ ^ (k : ℕ) •
          (cyclicProjection (m := m) (γ := γ) U l *
            (cyclicProjection (m := m) (γ := γ) U k)ᴴ) := by
    calc
      (U : MatrixAlg D) *
          (cyclicProjection (m := m) (γ := γ) U l *
            (cyclicProjection (m := m) (γ := γ) U k)ᴴ) =
        ((U : MatrixAlg D) * cyclicProjection (m := m) (γ := γ) U l) *
          (cyclicProjection (m := m) (γ := γ) U k)ᴴ := by
            simp only [Matrix.mul_assoc]
      _ = (cyclicProjection (m := m) (γ := γ) U l * (U : MatrixAlg D)) *
            (cyclicProjection (m := m) (γ := γ) U k)ᴴ := by
              rw [(commute_unitary_cyclicProjection (m := m) (γ := γ) U l).eq]
      _ = cyclicProjection (m := m) (γ := γ) U l *
            ((U : MatrixAlg D) * (cyclicProjection (m := m) (γ := γ) U k)ᴴ) := by
              simp only [Matrix.mul_assoc]
      _ = cyclicProjection (m := m) (γ := γ) U l *
            (γ ^ (k : ℕ) • (cyclicProjection (m := m) (γ := γ) U k)ᴴ) := by
              rw [unitary_mul_star_cyclicProjection_eq (m := m) hγprim U hUm k]
      _ = γ ^ (k : ℕ) •
            (cyclicProjection (m := m) (γ := γ) U l *
              (cyclicProjection (m := m) (γ := γ) U k)ᴴ) := by
            simp only [Algebra.mul_smul_comm]
  have hsub :
      (γ ^ (l : ℕ) - γ ^ (k : ℕ)) •
          (cyclicProjection (m := m) (γ := γ) U l *
            (cyclicProjection (m := m) (γ := γ) U k)ᴴ) = 0 := by
    calc
      (γ ^ (l : ℕ) - γ ^ (k : ℕ)) •
          (cyclicProjection (m := m) (γ := γ) U l *
            (cyclicProjection (m := m) (γ := γ) U k)ᴴ)
          = γ ^ (l : ℕ) •
              (cyclicProjection (m := m) (γ := γ) U l *
                (cyclicProjection (m := m) (γ := γ) U k)ᴴ) -
              γ ^ (k : ℕ) •
                (cyclicProjection (m := m) (γ := γ) U l *
                  (cyclicProjection (m := m) (γ := γ) U k)ᴴ) := by
                  simp only [sub_smul]
      _ = 0 := by rw [← hlEig, ← hkEig]; simp only [sub_self]
  have hneq : γ ^ (l : ℕ) - γ ^ (k : ℕ) ≠ 0 := by
    refine sub_ne_zero.mpr ?_
    intro hpow
    exact hkl.symm (pow_inj_of_primitiveRoot (m := m) hγprim hpow)
  exact (smul_eq_zero.mp hsub).resolve_left hneq

/-- Each cyclic projection is an orthogonal projection. -/
private lemma isOrthogonalProjection_cyclicProjection {γ : ℂ} (hγprim : IsPrimitiveRoot γ m)
    (U : Matrix.unitaryGroup (Fin D) ℂ) (hUm : ((U : MatrixAlg D) ^ m) = 1) :
    ∀ k : Fin m, IsOrthogonalProjection (cyclicProjection (m := m) (γ := γ) U k) := by
  intro k
  have hstar_eq :
      (cyclicProjection (m := m) (γ := γ) U k)ᴴ =
        cyclicProjection (m := m) (γ := γ) U k *
          (cyclicProjection (m := m) (γ := γ) U k)ᴴ := by
    calc
      (cyclicProjection (m := m) (γ := γ) U k)ᴴ =
          (1 : MatrixAlg D) * (cyclicProjection (m := m) (γ := γ) U k)ᴴ := by simp only [one_mul]
      _ = (∑ l : Fin m, cyclicProjection (m := m) (γ := γ) U l) *
            (cyclicProjection (m := m) (γ := γ) U k)ᴴ := by
              rw [sum_cyclicProjection_eq_one (m := m) hγprim U]
      _ = ∑ l : Fin m,
            cyclicProjection (m := m) (γ := γ) U l *
              (cyclicProjection (m := m) (γ := γ) U k)ᴴ := by
              simp only [sum_mul]
      _ = cyclicProjection (m := m) (γ := γ) U k *
            (cyclicProjection (m := m) (γ := γ) U k)ᴴ := by
          exact Finset.sum_eq_single_of_mem k (Finset.mem_univ k) (by
            intro l hl hne
            simpa using mul_star_cyclicProjection_eq_zero_of_ne (m := m) hγprim U hUm hne.symm)
  have hself_aux :
      cyclicProjection (m := m) (γ := γ) U k =
        cyclicProjection (m := m) (γ := γ) U k *
          (cyclicProjection (m := m) (γ := γ) U k)ᴴ := by
    simpa [Matrix.conjTranspose_mul] using congrArg Matrix.conjTranspose hstar_eq
  refine ⟨hstar_eq.trans hself_aux.symm, idem_cyclicProjection (m := m) hγprim U hUm k⟩

/-- Spectral projections of a finite-order peripheral unitary.

Here `γ` should be thought of as the canonical phase `exp(2π i / m)`, represented in Lean by
an abstract primitive root `hγprim : IsPrimitiveRoot γ m`. -/
theorem exists_cyclic_projections_of_peripheral_unitary
    (T : MatrixEnd D) {γ : ℂ}
    (hγprim : IsPrimitiveRoot γ m)
    (U : Matrix.unitaryGroup (Fin D) ℂ)
    (hUm : ((U : MatrixAlg D) ^ m) = 1)
    (hPow : ∀ k : ℕ, T ((U : MatrixAlg D) ^ k) = γ ^ k • ((U : MatrixAlg D) ^ k)) :
    ∃ P : Fin m → MatrixAlg D,
      (∀ k : Fin m, IsOrthogonalProjection (P k)) ∧
      (∑ k : Fin m, P k = 1) ∧
      ((U : MatrixAlg D) = ∑ k : Fin m, γ ^ (k : ℕ) • P k) ∧
      (∀ k : Fin m, T (P (k + 1)) = P k) := by
  classical
  let P : Fin m → MatrixAlg D := cyclicProjection (m := m) (γ := γ) U
  have hPproj : ∀ k : Fin m, IsOrthogonalProjection (P k) := by
    simpa [P] using isOrthogonalProjection_cyclicProjection (m := m) hγprim U hUm
  have hPsum : ∑ k : Fin m, P k = 1 := by
    simpa [P] using sum_cyclicProjection_eq_one (m := m) hγprim U
  have hUspec_sum : ∑ k : Fin m, γ ^ (k : ℕ) • P k = (U : MatrixAlg D) := by
    simpa [P] using unitary_eq_sum_cyclicProjection (m := m) hγprim U hUm
  have hcyclic : ∀ k : Fin m, T (P (k + 1)) = P k := by
    simpa [P] using cyclic_action_of_cyclicProjection (m := m) (T := T) hγprim U hPow
  exact ⟨P, hPproj, hPsum, hUspec_sum.symm, hcyclic⟩

end CyclicProjections

namespace MPSTensor

/-- Packaged version of Wolf Theorem 6.6 for transfer maps of irreducible unital Schwarz
maps, assuming the peripheral spectrum is generated by a primitive `m`-th root `γ`. -/
theorem exists_cyclic_decomposition_of_irreducible_schwarz
    {r D m : ℕ} [NeZero D] [NeZero m]
    (K : Fin r → MatrixAlg D)
    (hUnital : KadisonSchwarz.IsUnitalKraus (d := r) (D := D) K)
    (ρ : MatrixAlg D) (hρ : ρ.PosDef)
    (hρfix : Kraus.adjointMap K ρ = ρ)
    (hIrr : IsIrreducibleMap (transferMap (d := r) (D := D) K))
    {γ : ℂ} (hγprim : IsPrimitiveRoot γ m)
    (hperiph : peripheralEigenvalues (transferMap (d := r) (D := D) K) =
      Set.range (fun j : Fin m => γ ^ (j : ℕ))) :
    ∃ U : Matrix.unitaryGroup (Fin D) ℂ,
      ∃ P : Fin m → MatrixAlg D,
        transferMap (d := r) (D := D) K (U : MatrixAlg D) = γ • (U : MatrixAlg D) ∧
        (∀ k : ℕ,
          transferMap (d := r) (D := D) K ((U : MatrixAlg D) ^ k) =
            γ ^ k • ((U : MatrixAlg D) ^ k)) ∧
        ((U : MatrixAlg D) ^ m = 1) ∧
        (∀ k : Fin m, IsOrthogonalProjection (P k)) ∧
        (∑ k : Fin m, P k = 1) ∧
        ((U : MatrixAlg D) = ∑ k : Fin m, γ ^ (k : ℕ) • P k) ∧
        (∀ k : Fin m, transferMap (d := r) (D := D) K (P (k + 1)) = P k) := by
  have hγ : γ ∈ peripheralEigenvalues (transferMap (d := r) (D := D) K) := by
    rw [hperiph]
    by_cases hm1 : m = 1
    · subst hm1
      simp only [
        IsPrimitiveRoot.one_right_iff.mp hγprim, Fin.val_eq_zero, pow_zero, Set.range_const,
        Set.mem_singleton_iff
      ]
    · have hm0 : m ≠ 0 := NeZero.ne m
      have hm_gt : 1 < m := Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨hm0, hm1⟩
      exact ⟨⟨1, hm_gt⟩, by simp only [pow_one]⟩
  obtain ⟨U, hU, hUm⟩ :=
    exists_normalized_peripheral_unitary_of_irreducible_schwarz
      (K := K) hUnital ρ hρ hρfix hIrr hγprim hγ
  have hPow :
      ∀ k : ℕ,
        transferMap (d := r) (D := D) K ((U : MatrixAlg D) ^ k) =
          γ ^ k • ((U : MatrixAlg D) ^ k) :=
    map_powers_of_peripheral_unitary
      (K := K) hUnital ρ hρ hρfix hγ U hU
  obtain ⟨P, hPproj, hPsum, hUspec, hcyclic⟩ :=
    exists_cyclic_projections_of_peripheral_unitary
      (T := transferMap (d := r) (D := D) K) hγprim U hUm hPow
  exact ⟨U, P, hU, hPow, hUm, hPproj, hPsum, hUspec, hcyclic⟩

end MPSTensor

section PrimitivityOfSectors

variable {D m : ℕ} [NeZero m]

private def cyclicIndex (k : Fin m) (n : ℕ) : Fin m :=
  ⟨((k : ℕ) + n) % m, Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne m))⟩

@[simp] private lemma cyclicIndex_zero (k : Fin m) :
    cyclicIndex (m := m) k 0 = k := by
  ext
  simp only [cyclicIndex, add_zero, Nat.mod_eq_of_lt k.is_lt, Fin.eta]

private lemma cyclicIndex_succ (k : Fin m) (n : ℕ) :
    cyclicIndex (m := m) k (n + 1) = cyclicIndex k n + 1 := by
  ext
  change (((k : ℕ) + n) + 1) % m = ((((k : ℕ) + n) % m) + 1 % m) % m
  exact Nat.add_mod ((k : ℕ) + n) 1 m

@[simp] private lemma cyclicIndex_self (k : Fin m) :
    cyclicIndex (m := m) k m = k := by
  ext
  change ((k : ℕ) + m) % m = k
  rw [Nat.add_mod_right, Nat.mod_eq_of_lt k.is_lt]

/-- The `m`-th power of the channel preserves each cyclic corner `P_k · M_D(ℂ) · P_k`.

The cyclic permutation of the projections alone is not enough for this conclusion for a general
linear map. We therefore assume the left- and right-multiplicative-domain identities on the
sector projections, which are the abstract consequences needed from the multiplicative-domain
argument in Wolf Theorem 6.6. -/
theorem preserves_corner_pow_of_cyclic_decomp
    {T : MatrixEnd D}
    (P : Fin m → MatrixAlg D)
    (hPproj : ∀ k : Fin m, IsOrthogonalProjection (P k))
    (_hPsum : ∑ k : Fin m, P k = 1)
    (hcyclic : ∀ k : Fin m, T (P (k + 1)) = P k)
    (hMulLeft : ∀ k : Fin m, ∀ X : MatrixAlg D, T (P k * X) = T (P k) * T X)
    (hMulRight : ∀ k : Fin m, ∀ X : MatrixAlg D, T (X * P k) = T X * T (P k)) :
    ∀ k : Fin m, PreservesCorner (P k) (T ^ m) := by
  have hstep :
      ∀ n : ℕ, ∀ k : Fin m, ∀ X : MatrixAlg D,
        (T ^ n) (P (cyclicIndex k n) * X * P (cyclicIndex k n)) =
          P k * ((T ^ n) X) * P k := by
    intro n
    induction n with
    | zero =>
        intro k X
        simp only [pow_zero, cyclicIndex_zero, Module.End.one_apply]
    | succ n ih =>
        intro k X
        calc
          (T ^ (n + 1))
              (P (cyclicIndex k (n + 1)) * X * P (cyclicIndex k (n + 1)))
              = (T ^ n) (T (P (cyclicIndex k (n + 1)) * X * P (cyclicIndex k (n + 1)))) := by
                  simp only [pow_succ, Module.End.mul_apply]
          _ = (T ^ n) (T (P (cyclicIndex k n + 1) * X * P (cyclicIndex k n + 1))) := by
                  rw [cyclicIndex_succ k n]
          _ = (T ^ n) (P (cyclicIndex k n) * T X * P (cyclicIndex k n)) := by
                  congr 1
                  calc
                    T (P (cyclicIndex k n + 1) * X * P (cyclicIndex k n + 1))
                        = T (P (cyclicIndex k n + 1) * X) * T (P (cyclicIndex k n + 1)) := by
                            exact hMulRight (cyclicIndex k n + 1) (P (cyclicIndex k n + 1) * X)
                    _ = (T (P (cyclicIndex k n + 1)) * T X) * T (P (cyclicIndex k n + 1)) := by
                            rw [hMulLeft (cyclicIndex k n + 1) X]
                    _ = P (cyclicIndex k n) * T X * P (cyclicIndex k n) := by
                            rw [hcyclic (cyclicIndex k n)]
          _ = P k * ((T ^ n) (T X)) * P k := ih k (T X)
          _ = P k * ((T ^ (n + 1)) X) * P k := by
                  simp only [pow_succ, Module.End.mul_apply]
  intro k X
  have hmk : (T ^ m) (P k * X * P k) = P k * ((T ^ m) X) * P k := by
    simpa using hstep m k X
  rw [hmk]
  calc
    P k * (P k * ((T ^ m) X) * P k) * P k
        = (P k * P k) * ((T ^ m) X) * (P k * P k) := by
            simp only [Matrix.mul_assoc]
    _ = P k * ((T ^ m) X) * P k := by
            simp only [(hPproj k).2, Matrix.mul_assoc]

/-- Wolf Theorem 6.6 corollary: an orbit-sum lift from invariant corner subprojections to
ambient invariant projections implies irreducibility of the `m`-step dynamics on each cyclic
sector. -/
theorem isIrreducible_restriction_of_cyclic_decomp
    {T : MatrixEnd D}
    (hIrr : IsIrreducibleMap T)
    (P : Fin m → MatrixAlg D)
    (_hPproj : ∀ k : Fin m, IsOrthogonalProjection (P k))
    (_hPsum : ∑ k : Fin m, P k = 1)
    (_hcyclic : ∀ k : Fin m, T (P (k + 1)) = P k)
    (hLift :
      ∀ k : Fin m, ∀ Q : MatrixAlg D,
        IsOrthogonalProjection Q →
        Q * P k = Q →
        P k * Q = Q →
        PreservesCorner Q (T ^ m) →
        ∃ R : MatrixAlg D,
          IsOrthogonalProjection R ∧
          PreservesCorner R T ∧
          (Q = 0 ↔ R = 0) ∧
          (Q = P k ↔ R = 1)) :
    ∀ k : Fin m, IsIrreducibleOnCorner (P k) (T ^ m) := by
  intro k Q hQproj hQP hPQ hQinv
  rcases hLift k Q hQproj hQP hPQ hQinv with ⟨R, hRproj, hRinv, hQzero, hQfull⟩
  rcases hIrr R hRproj hRinv with hR0 | hR1
  · left
    exact hQzero.mpr hR0
  · right
    exact hQfull.mpr hR1
/-- Wolf Theorem 6.6 corollary: the `m`-step dynamics on each cyclic sector is primitive. -/
theorem isPrimitive_restriction_of_cyclic_decomp
    {T : MatrixEnd D} [NeZero D] {γ : ℂ}
    (hγprim : IsPrimitiveRoot γ m)
    (hperiph : peripheralEigenvalues T = Set.range (fun j : Fin m => γ ^ (j : ℕ)))
    (P : Fin m → MatrixAlg D)
    (hPproj : ∀ k : Fin m, IsOrthogonalProjection (P k))
    (hPsum : ∑ k : Fin m, P k = 1)
    (hcyclic : ∀ k : Fin m, T (P (k + 1)) = P k)
    (hMulLeft : ∀ k : Fin m, ∀ X : MatrixAlg D, T (P k * X) = T (P k) * T X)
    (hMulRight : ∀ k : Fin m, ∀ X : MatrixAlg D, T (X * P k) = T X * T (P k))
    (hPne : ∀ k : Fin m, P k ≠ 0) :
    ∀ k : Fin m,
      IsPrimitive
        (cornerRestriction (P k) (T ^ m)
          (preserves_corner_pow_of_cyclic_decomp
            (T := T) P hPproj hPsum hcyclic hMulLeft hMulRight k)) := by
  let hInv : ∀ k : Fin m, PreservesCorner (P k) (T ^ m) :=
    preserves_corner_pow_of_cyclic_decomp (T := T) P hPproj hPsum hcyclic hMulLeft hMulRight
  have hone_mem : (1 : ℂ) ∈ peripheralEigenvalues T := by
    rw [hperiph]
    exact ⟨0, by simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, pow_zero]⟩
  rcases hone_mem.1.exists_hasEigenvector with ⟨ρ, hρeig⟩
  have hρ_fix : T ρ = ρ := by
    exact (Module.End.HasEigenvector.apply_eq_smul hρeig).trans (by simp only [one_smul])
  have hρ_ne : ρ ≠ 0 := (Module.End.hasEigenvector_iff.mp hρeig).2
  have hper_pow : ∀ μ : ℂ, μ ∈ peripheralEigenvalues T → μ ^ m = 1 := by
    intro μ hμ
    rw [hperiph] at hμ
    rcases hμ with ⟨j, rfl⟩
    calc
      (γ ^ (j : ℕ)) ^ m = γ ^ ((j : ℕ) * m) := by rw [pow_mul]
      _ = γ ^ (m * (j : ℕ)) := by rw [Nat.mul_comm]
      _ = (γ ^ m) ^ (j : ℕ) := by rw [pow_mul]
      _ = 1 := by simp only [hγprim.pow_eq_one, one_pow]
  have hperiph_pow : peripheralEigenvalues (T ^ m) = {1} :=
    peripheralEigenvalues_pow_eq_singleton
      (E := T) (p := m) (hp := Nat.pos_of_ne_zero (NeZero.ne m))
      hper_pow ρ hρ_fix hρ_ne
  have hcyclic_pow : ∀ n : ℕ, ∀ k : Fin m, (T ^ n) (P (cyclicIndex k n)) = P k := by
    intro n
    induction n with
    | zero =>
        intro k
        simp only [pow_zero, cyclicIndex_zero, Module.End.one_apply]
    | succ n ih =>
        intro k
        calc
          (T ^ (n + 1)) (P (cyclicIndex k (n + 1)))
              = (T ^ n) (T (P (cyclicIndex k (n + 1)))) := by
                  simp only [pow_succ, Module.End.mul_apply]
          _ = (T ^ n) (T (P (cyclicIndex k n + 1))) := by
                  rw [cyclicIndex_succ k n]
          _ = (T ^ n) (P (cyclicIndex k n)) := by
                  rw [hcyclic (cyclicIndex k n)]
          _ = P k := ih k
  have hPk_fix : ∀ k : Fin m, (T ^ m) (P k) = P k := by
    intro k
    simpa using hcyclic_pow m k
  have hPk_corner : ∀ k : Fin m, P k ∈ cornerSubmodule (P k) := by
    intro k
    change P k * P k * P k = P k
    rw [Matrix.mul_assoc, (hPproj k).2, (hPproj k).2]
  have hcorner_fix : ∀ k : Fin m,
      cornerRestriction (P k) (T ^ m) (hInv k) ⟨P k, hPk_corner k⟩ = ⟨P k, hPk_corner k⟩ := by
    intro k
    apply Subtype.ext
    simpa using hPk_fix k
  have hcorner_ne : ∀ k : Fin m, (⟨P k, hPk_corner k⟩ : cornerSubmodule (P k)) ≠ 0 := by
    intro k hzero
    apply hPne k
    have hval := congrArg Subtype.val hzero
    simpa using hval
  have huniq : ∀ k : Fin m, ∀ μ : ℂ,
      Module.End.HasEigenvalue (cornerRestriction (P k) (T ^ m) (hInv k)) μ →
      ‖μ‖ = 1 → μ = 1 := by
    intro k μ hμeig hμnorm
    rcases hμeig.exists_hasEigenvector with ⟨X, hX⟩
    have hX_mem : X ∈ Module.End.eigenspace (cornerRestriction (P k) (T ^ m) (hInv k)) μ :=
      (Module.End.hasEigenvector_iff.mp hX).1
    have hX_ne : X ≠ 0 := (Module.End.hasEigenvector_iff.mp hX).2
    have hX_eq : cornerRestriction (P k) (T ^ m) (hInv k) X = μ • X :=
      (Module.End.mem_eigenspace_iff).1 hX_mem
    have hX_eq_val : (T ^ m) X.1 = μ • X.1 := congrArg Subtype.val hX_eq
    have hX_mem_ambient : X.1 ∈ Module.End.eigenspace (T ^ m) μ :=
      (Module.End.mem_eigenspace_iff).2 hX_eq_val
    have hX_ne_ambient : X.1 ≠ 0 := by
      intro h0
      apply hX_ne
      apply Subtype.ext
      simpa using h0
    have hX_eig_ambient : Module.End.HasEigenvector (T ^ m) μ X.1 :=
      (Module.End.hasEigenvector_iff).2 ⟨hX_mem_ambient, hX_ne_ambient⟩
    have hμ_ambient : μ ∈ peripheralEigenvalues (T ^ m) :=
      ⟨Module.End.hasEigenvalue_of_hasEigenvector hX_eig_ambient, hμnorm⟩
    rw [hperiph_pow] at hμ_ambient
    exact hμ_ambient
  intro k
  exact isPrimitive_of_unique_norm_one
    (cornerRestriction (P k) (T ^ m) (hInv k))
    ⟨P k, hPk_corner k⟩
    (hcorner_fix k)
    (hcorner_ne k)
    (huniq k)

section PermutationBlockStructure

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
/-- Permutation-based variant of `preserves_corner_pow_of_cyclic_decomp`.

This isolates the part of Wolf Thm. 6.16 that only needs a permutation action on blocks:
if `T` permutes a family of sector projections via a permutation `σ`, then the `orderOf σ`-th
iterate preserves each sector corner. -/
theorem preserves_corner_pow_orderOf_of_perm_decomp
    {T : MatrixEnd D}
    (σ : Equiv.Perm ι)
    (P : ι → MatrixAlg D)
    (hPproj : ∀ k : ι, IsOrthogonalProjection (P k))
    (hperm : ∀ k : ι, T (P (σ k)) = P k)
    (hMulLeft : ∀ k : ι, ∀ X : MatrixAlg D, T (P k * X) = T (P k) * T X)
    (hMulRight : ∀ k : ι, ∀ X : MatrixAlg D, T (X * P k) = T X * T (P k)) :
    ∀ k : ι, PreservesCorner (P k) (T ^ orderOf σ) := by
  have hstep :
      ∀ n : ℕ, ∀ k : ι, ∀ X : MatrixAlg D,
        (T ^ n) (P ((σ ^ n) k) * X * P ((σ ^ n) k)) =
          P k * ((T ^ n) X) * P k := by
    intro n
    induction n with
    | zero =>
        intro k X
        simp only [pow_zero, Equiv.Perm.coe_one, id_eq, Module.End.one_apply]
    | succ n ih =>
        intro k X
        calc
          (T ^ (n + 1)) (P ((σ ^ (n + 1)) k) * X * P ((σ ^ (n + 1)) k))
              = (T ^ n) (T (P ((σ ^ (n + 1)) k) * X * P ((σ ^ (n + 1)) k))) := by
                  simp only [
                    pow_succ, Equiv.Perm.coe_mul, Function.comp_apply,
                    Module.End.mul_apply
                  ]
          _ = (T ^ n) (T (P (σ ((σ ^ n) k)) * X * P (σ ((σ ^ n) k)))) := by
                  simp only [pow_succ', Equiv.Perm.coe_mul, Function.comp_apply]
          _ = (T ^ n) (P ((σ ^ n) k) * T X * P ((σ ^ n) k)) := by
                  congr 1
                  calc
                    T (P (σ ((σ ^ n) k)) * X * P (σ ((σ ^ n) k))
                        ) = T (P (σ ((σ ^ n) k)) * X) * T (P (σ ((σ ^ n) k))) := by
                              exact hMulRight (σ ((σ ^ n) k)) (P (σ ((σ ^ n) k)) * X)
                    _ = (T (P (σ ((σ ^ n) k))) * T X) * T (P (σ ((σ ^ n) k))) := by
                          rw [hMulLeft (σ ((σ ^ n) k)) X]
                    _ = P ((σ ^ n) k) * T X * P ((σ ^ n) k) := by
                          rw [hperm ((σ ^ n) k)]
          _ = P k * ((T ^ n) (T X)) * P k := ih k (T X)
          _ = P k * ((T ^ (n + 1)) X) * P k := by simp only [pow_succ, Module.End.mul_apply]
  intro k X
  have hmain :
      (T ^ orderOf σ) (P ((σ ^ orderOf σ) k) * X * P ((σ ^ orderOf σ) k)) =
        P k * ((T ^ orderOf σ) X) * P k := hstep (orderOf σ) k X
  have hσ : (σ ^ orderOf σ) = 1 := pow_orderOf_eq_one σ
  have hmk : (T ^ orderOf σ) (P k * X * P k) = P k * ((T ^ orderOf σ) X) * P k := by
    simpa [hσ] using hmain
  calc
    P k * (T ^ orderOf σ) (P k * X * P k) * P k
        = P k * (P k * ((T ^ orderOf σ) X) * P k) * P k := by rw [hmk]
    _ = (P k * P k) * ((T ^ orderOf σ) X) * (P k * P k) := by
            simp only [Matrix.mul_assoc]
    _ = P k * ((T ^ orderOf σ) X) * P k := by
            simp only [(hPproj k).2, Matrix.mul_assoc]
    _ = (T ^ orderOf σ) (P k * X * P k) := by rw [hmk]

end PermutationBlockStructure

end PrimitivityOfSectors
