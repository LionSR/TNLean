/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.CompactSVD
import TNLean.Algebra.MatrixUnitaryBetween
import TNLean.Analysis.MatrixSqrt
import TNLean.MPS.MPU.SourceCuts
import Mathlib.Analysis.Matrix.Order

/-!
# Source factorizations of a matrix product unitary tensor

This module constructs the six source factors $X_1,Y_1,Z_1,X_2,Y_2,Z_2$ from the two compact
singular-value decompositions of an `MPOTensor`, following arXiv:1703.09188, equations
`eq:sf-svd`--`YZ=1` (lines 479--506).

The row type of both source cuts is `(Fin D × Fin d)`, ordered as (left virtual, physical).
Consequently the paper's graphically written weight $I_d\otimes\rho$ is represented literally in
Lean as $\rho\otimes I_d$. The first factorization is normalized for this weight; the second is
normalized for the ordinary inner product.

## Main definitions

* `MPOTensor.sourceWeight`: the product-index matrix $\rho\otimes I_d$.
* `MPOTensor.SourceFactors`: the six factors together with their source-cut factorizations,
  normalization identities, and right-inverse identities.
* `MPOTensor.sourceFactors`: the factors obtained from compact SVD for a positive-definite
  source weight $\rho$.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017, arXiv:1703.09188], equations
  `eq:sf-svd`, `Y1Y1X1X1`, `Z1Z2`, and `YZ=1`, lines 479--506.
-/

open scoped ComplexOrder Kronecker Matrix

namespace MPOTensor

variable {d D : ℕ} (U : MPOTensor d D)

/-- The first source-cut weight in product-index order.

The paper writes this matrix as $I_d\otimes\rho$ according to its graphical leg order. Since
`sourceCutM₁` orders its row index as (left virtual, down physical), the literal Lean Kronecker
product is $\rho\otimes I_d$. This is arXiv:1703.09188, `Y1Y1X1X1` (lines 487--494). -/
noncomputable def sourceWeight (ρ : Matrix (Fin D) (Fin D) ℂ) :
    Matrix (Fin D × Fin d) (Fin D × Fin d) ℂ :=
  ρ ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ)

/-- A positive-definite virtual weight gives a positive-definite product-index source weight.
This supplies the square root and inverse square root used in arXiv:1703.09188,
`Y1Y1X1X1` and `Z1Z2` (lines 487--502). -/
theorem sourceWeight_posDef {ρ : Matrix (Fin D) (Fin D) ℂ} (hρ : ρ.PosDef) :
    (sourceWeight (d := d) ρ).PosDef :=
  hρ.kronecker Matrix.PosDef.one

private structure ProductCompactSVD {α β : Type*} [Fintype α] [Fintype β]
    (M : Matrix α β ℂ) (r : ℕ) where
  V : Matrix (Fin r) α ℂ
  U : Matrix (Fin r) β ℂ
  diagonal : Matrix (Fin r) (Fin r) ℂ
  inverseDiagonal : Matrix (Fin r) (Fin r) ℂ
  factorization : M = Vᴴ * diagonal * U
  V_coisometry : V.IsCoisometry
  U_coisometry : U.IsCoisometry
  diagonal_mul_inverseDiagonal : diagonal * inverseDiagonal = 1

private noncomputable def productCompactSVD
    {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    {m n r : ℕ} (M : Matrix α β ℂ) (MFin : Matrix (Fin m) (Fin n) ℂ)
    (rowEquiv : Fin m ≃ α) (colEquiv : Fin n ≃ β)
    (hM : Matrix.reindex rowEquiv colEquiv MFin = M) (hrank : MFin.rank = r) :
    ProductCompactSVD M r := by
  let S : Matrix.CompactSVD MFin := Classical.choice (Matrix.exists_compactSVD MFin)
  let rankEquiv : Fin MFin.rank ≃ Fin r := Equiv.cast (congrArg Fin hrank)
  let V : Matrix (Fin r) α ℂ := Matrix.reindex rankEquiv rowEquiv S.V
  let U' : Matrix (Fin r) β ℂ := Matrix.reindex rankEquiv colEquiv S.U
  let diagonal : Matrix (Fin r) (Fin r) ℂ :=
    Matrix.reindex rankEquiv rankEquiv S.diagonal
  let inverseDiagonal : Matrix (Fin r) (Fin r) ℂ :=
    Matrix.reindex rankEquiv rankEquiv S.inverseDiagonal
  have hV : V.IsCoisometry := by
    apply Matrix.IsCoisometry.reindex S.V
    exact S.V_mul_conjTranspose
  have hU : U'.IsCoisometry := by
    apply Matrix.IsCoisometry.reindex S.U
    exact S.U_mul_conjTranspose
  have hdiagonal : diagonal * inverseDiagonal = 1 := by
    change Matrix.reindexLinearEquiv ℂ ℂ rankEquiv rankEquiv S.diagonal *
      Matrix.reindexLinearEquiv ℂ ℂ rankEquiv rankEquiv S.inverseDiagonal = 1
    rw [Matrix.reindexLinearEquiv_mul, S.diagonal_mul_inverseDiagonal,
      Matrix.reindexLinearEquiv_one]
  have hfactorization : M = Vᴴ * diagonal * U' := by
    have hVstar :
        (Matrix.reindex rankEquiv rowEquiv S.V)ᴴ =
          Matrix.reindex rowEquiv rankEquiv S.Vᴴ :=
      Matrix.conjTranspose_reindex _ _ _
    calc
      M = Matrix.reindex rowEquiv colEquiv MFin := hM.symm
      _ = Matrix.reindex rowEquiv colEquiv (S.Vᴴ * S.diagonal * S.U) :=
        congrArg (Matrix.reindex rowEquiv colEquiv) S.factorization_diagonal
      _ = Vᴴ * diagonal * U' := by
        change Matrix.reindex _ _ (S.Vᴴ * S.diagonal * S.U) =
          (Matrix.reindex _ _ S.V)ᴴ * Matrix.reindex _ _ S.diagonal *
            Matrix.reindex _ _ S.U
        rw [hVstar]
        change Matrix.reindexLinearEquiv ℂ ℂ _ _ (S.Vᴴ * S.diagonal * S.U) =
          Matrix.reindexLinearEquiv ℂ ℂ _ _ S.Vᴴ *
            Matrix.reindexLinearEquiv ℂ ℂ _ _ S.diagonal *
            Matrix.reindexLinearEquiv ℂ ℂ _ _ S.U
        rw [Matrix.reindexLinearEquiv_mul, Matrix.reindexLinearEquiv_mul]
  exact ⟨V, U', diagonal, inverseDiagonal, hfactorization, hV, hU, hdiagonal⟩

private noncomputable def sourceSVD₁ :
    ProductCompactSVD (sourceCutM₁ U) r[U] :=
  productCompactSVD (sourceCutM₁ U) (sourceCutM₁Fin U)
    (finProdFinEquiv (m := D) (n := d)).symm
    (finProdFinEquiv (m := d) (n := D)).symm
    (by simp [sourceCutM₁Fin, Matrix.reindex_apply])
    (sourceCutM₁_rank_eq_sourceCutM₁Fin_rank U).symm

private noncomputable def sourceSVD₂ :
    ProductCompactSVD (sourceCutM₂ U) ℓ[U] :=
  productCompactSVD (sourceCutM₂ U) (sourceCutM₂Fin U)
    (finProdFinEquiv (m := D) (n := d)).symm
    (finProdFinEquiv (m := d) (n := D)).symm
    (by simp [sourceCutM₂Fin, Matrix.reindex_apply])
    (sourceCutM₂_rank_eq_sourceCutM₂Fin_rank U).symm

private theorem sourceSVD₁_V_vecMul_injective :
    Function.Injective (sourceSVD₁ U).V.vecMul := by
  intro x y hxy
  calc
    x = x ᵥ* (1 : Matrix (Fin r[U]) (Fin r[U]) ℂ) := (Matrix.vecMul_one x).symm
    _ = x ᵥ* ((sourceSVD₁ U).V * (sourceSVD₁ U).Vᴴ) := by
      rw [(sourceSVD₁ U).V_coisometry]
    _ = (x ᵥ* (sourceSVD₁ U).V) ᵥ* (sourceSVD₁ U).Vᴴ :=
      (Matrix.vecMul_vecMul _ _ _).symm
    _ = (y ᵥ* (sourceSVD₁ U).V) ᵥ* (sourceSVD₁ U).Vᴴ :=
      congrArg (fun z ↦ z ᵥ* (sourceSVD₁ U).Vᴴ) hxy
    _ = y ᵥ* ((sourceSVD₁ U).V * (sourceSVD₁ U).Vᴴ) :=
      Matrix.vecMul_vecMul _ _ _
    _ = y := by rw [(sourceSVD₁ U).V_coisometry, Matrix.vecMul_one]

private noncomputable def weightedSourceGram (ρ : Matrix (Fin D) (Fin D) ℂ) :
    Matrix (Fin r[U]) (Fin r[U]) ℂ :=
  (sourceSVD₁ U).V * sourceWeight (d := d) ρ * (sourceSVD₁ U).Vᴴ

private theorem weightedSourceGram_posDef {ρ : Matrix (Fin D) (Fin D) ℂ}
    (hρ : ρ.PosDef) : (weightedSourceGram U ρ).PosDef :=
  (sourceWeight_posDef (d := d) hρ).mul_mul_conjTranspose_same
    (sourceSVD₁_V_vecMul_injective U)

/-- The six source factors and their algebraic identities from arXiv:1703.09188,
`eq:sf-svd`--`YZ=1` (lines 479--506).

Here `X₁` has the paper's weighted normalization for $I_d\otimes\rho$ (represented as
`sourceWeight ρ`), while `X₂` has the ordinary isometry normalization. -/
structure SourceFactors (ρ : Matrix (Fin D) (Fin D) ℂ) where
  /-- The weighted left factor of the first source cut. -/
  X₁ : Matrix (Fin D × Fin d) (Fin r[U]) ℂ
  /-- The right factor of the first source cut. -/
  Y₁ : Matrix (Fin r[U]) (Fin d × Fin D) ℂ
  /-- The right inverse of `Y₁` defined by arXiv:1703.09188, `Z1Z2`. -/
  Z₁ : Matrix (Fin d × Fin D) (Fin r[U]) ℂ
  /-- The isometric left factor of the second source cut. -/
  X₂ : Matrix (Fin D × Fin d) (Fin ℓ[U]) ℂ
  /-- The right factor of the second source cut. -/
  Y₂ : Matrix (Fin ℓ[U]) (Fin d × Fin D) ℂ
  /-- The right inverse of `Y₂` defined by arXiv:1703.09188, `Z1Z2`. -/
  Z₂ : Matrix (Fin d × Fin D) (Fin ℓ[U]) ℂ
  /-- The exact first source-cut factorization, arXiv:1703.09188, `eq:sf-svd`. -/
  sourceCutM₁_eq : sourceCutM₁ U = X₁ * Y₁
  /-- The exact second source-cut factorization, arXiv:1703.09188, `eq:sf-svd`. -/
  sourceCutM₂_eq : sourceCutM₂ U = X₂ * Y₂
  /-- The weighted normalization $X_1^*(I_d\otimes\rho)X_1=I$,
  arXiv:1703.09188, `Y1Y1X1X1`. -/
  X₁_weighted_isometry : X₁ᴴ * sourceWeight (d := d) ρ * X₁ = 1
  /-- The normalization $X_2^*X_2=I$, arXiv:1703.09188, `Y1Y1X1X1`. -/
  X₂_isometry : X₂.IsIsometry
  /-- The right-inverse identity $Y_1Z_1=I$, arXiv:1703.09188, `YZ=1`. -/
  Y₁_mul_Z₁ : Y₁ * Z₁ = 1
  /-- The right-inverse identity $Y_2Z_2=I$, arXiv:1703.09188, `YZ=1`. -/
  Y₂_mul_Z₂ : Y₂ * Z₂ = 1

/-- Construct the paper's source factors from compact SVD and a positive-definite virtual weight.

For the first cut, if $V_1^*D_1U_1$ is the compact SVD and
$A=V_1(\rho\otimes I_d)V_1^*$, then
$X_1=V_1^*A^{-1/2}$, $Y_1=A^{1/2}D_1U_1$, and
$Z_1=U_1^*D_1^{-1}A^{-1/2}$. The second cut uses
$X_2=V_2^*$, $Y_2=D_2U_2$, and $Z_2=U_2^*D_2^{-1}$.
These are exactly arXiv:1703.09188, `Y1Y1X1X1` and `Z1Z2` (lines 487--502). -/
noncomputable def sourceFactors (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef) :
    SourceFactors U ρ := by
  let S₁ := sourceSVD₁ U
  let S₂ := sourceSVD₂ U
  let hA := weightedSourceGram_posDef U hρ
  let AinvSqrt := hA.posSemidef.supportInvSqrt
  let Asqrt := hA.isHermitian.cfc Real.sqrt
  let X₁ := S₁.Vᴴ * AinvSqrt
  let Y₁ := Asqrt * S₁.diagonal * S₁.U
  let Z₁ := S₁.Uᴴ * S₁.inverseDiagonal * AinvSqrt
  let X₂ := S₂.Vᴴ
  let Y₂ := S₂.diagonal * S₂.U
  let Z₂ := S₂.Uᴴ * S₂.inverseDiagonal
  have hcut₁ : sourceCutM₁ U = X₁ * Y₁ := by
    rw [S₁.factorization]
    change S₁.Vᴴ * S₁.diagonal * S₁.U =
      (S₁.Vᴴ * AinvSqrt) * (Asqrt * S₁.diagonal * S₁.U)
    calc
      S₁.Vᴴ * S₁.diagonal * S₁.U =
          S₁.Vᴴ * (1 : Matrix (Fin r[U]) (Fin r[U]) ℂ) * S₁.diagonal * S₁.U := by
        simp only [Matrix.mul_one]
      _ = S₁.Vᴴ * (AinvSqrt * Asqrt) * S₁.diagonal * S₁.U := by
        rw [hA.posSemidef.supportInvSqrt_mul_cfc_sqrt, hA.supportProj_eq_one]
      _ = (S₁.Vᴴ * AinvSqrt) * (Asqrt * S₁.diagonal * S₁.U) := by
        simp only [Matrix.mul_assoc]
  have hcut₂ : sourceCutM₂ U = X₂ * Y₂ := by
    rw [S₂.factorization]
    simp only [X₂, Y₂, Matrix.mul_assoc]
  have hX₁ : X₁ᴴ * sourceWeight (d := d) ρ * X₁ = 1 := by
    change (S₁.Vᴴ * AinvSqrt)ᴴ * sourceWeight (d := d) ρ *
      (S₁.Vᴴ * AinvSqrt) = 1
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      hA.posSemidef.supportInvSqrt_isHermitian.eq]
    calc
      AinvSqrt * S₁.V * sourceWeight (d := d) ρ * (S₁.Vᴴ * AinvSqrt) =
          AinvSqrt * weightedSourceGram U ρ * AinvSqrt := by
        simp [weightedSourceGram, S₁, AinvSqrt, Matrix.mul_assoc]
      _ = hA.posSemidef.supportProj :=
        hA.posSemidef.supportInvSqrt_mul_self_mul_supportInvSqrt
      _ = 1 := hA.supportProj_eq_one
  have hX₂ : X₂.IsIsometry := by
    exact S₂.V_coisometry.conjTranspose S₂.V
  have hY₁Z₁ : Y₁ * Z₁ = 1 := by
    change (Asqrt * S₁.diagonal * S₁.U) *
      (S₁.Uᴴ * S₁.inverseDiagonal * AinvSqrt) = 1
    calc
      (Asqrt * S₁.diagonal * S₁.U) *
          (S₁.Uᴴ * S₁.inverseDiagonal * AinvSqrt) =
        Asqrt * S₁.diagonal * (S₁.U * S₁.Uᴴ) * S₁.inverseDiagonal *
          AinvSqrt := by simp only [Matrix.mul_assoc]
      _ = Asqrt * (S₁.diagonal * S₁.inverseDiagonal) * AinvSqrt := by
        rw [S₁.U_coisometry, Matrix.mul_one]
        simp only [Matrix.mul_assoc]
      _ = Asqrt * AinvSqrt := by
        rw [S₁.diagonal_mul_inverseDiagonal, Matrix.mul_one]
      _ = hA.posSemidef.supportProj := hA.posSemidef.cfc_sqrt_mul_supportInvSqrt
      _ = 1 := hA.supportProj_eq_one
  have hY₂Z₂ : Y₂ * Z₂ = 1 := by
    change (S₂.diagonal * S₂.U) * (S₂.Uᴴ * S₂.inverseDiagonal) = 1
    calc
      (S₂.diagonal * S₂.U) * (S₂.Uᴴ * S₂.inverseDiagonal) =
          S₂.diagonal * (S₂.U * S₂.Uᴴ) * S₂.inverseDiagonal := by
        simp only [Matrix.mul_assoc]
      _ = S₂.diagonal * S₂.inverseDiagonal := by
        rw [S₂.U_coisometry, Matrix.mul_one]
      _ = 1 := S₂.diagonal_mul_inverseDiagonal
  exact ⟨X₁, Y₁, Z₁, X₂, Y₂, Z₂, hcut₁, hcut₂, hX₁, hX₂, hY₁Z₁, hY₂Z₂⟩

end MPOTensor
