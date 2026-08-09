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
import Mathlib.LinearAlgebra.Matrix.IsDiag

/-!
# Source factorizations of a matrix product unitary tensor

This module constructs the six source factors $X_1,Y_1,Z_1,X_2,Y_2,Z_2$ from the two compact
singular-value decompositions of an `MPOTensor`, following arXiv:1703.09188, equations
`eq:sf-svd`--`YZ=1` (lines 479--506).

The first source cut has row order (left virtual, down physical), while the second has row order
(left virtual, up physical). Both use the product type `(Fin D × Fin d)`. Consequently the paper's
graphically written weight $I_d\otimes\rho$ is represented literally in
Lean as $\rho\otimes I_d$. The first factorization is normalized for this weight; the second is
normalized for the ordinary inner product.

## Main definitions

* `MPOTensor.sourceWeight`: the product-index matrix $\rho\otimes I_d$.
* `MPOTensor.SourceCutSVD`, `MPOTensor.sourceSVD₁`, `MPOTensor.sourceSVD₂`: the two
  product-index compact singular-value decompositions.
* `MPOTensor.SourceFactors`: the six factors together with their source-cut factorizations,
  normalization identities, and right-inverse identities.
* `MPOTensor.sourceGram₁`: the positive normalization matrix for the first source cut.
* `MPOTensor.sourceX₁`, `sourceY₁`, `sourceZ₁`, `sourceX₂`, `sourceY₂`, `sourceZ₂`:
  the six source factors.
* `MPOTensor.sourceFactors`: the factors obtained from compact SVD for a positive-definite
  source weight $\rho$.

## Main results

* `MPOTensor.sourceWeight_posDef`, `MPOTensor.sourceGram₁_posDef`: positivity of the weight
  and first normalization matrix.
* `MPOTensor.sourceX₁_apply`, `sourceY₁_apply`, `sourceZ₁_apply`, `sourceX₂_apply`,
  `sourceY₂_apply`, `sourceZ₂_apply`: stable entry formulas for all six factors.
* `MPOTensor.sourceCutM₁_eq_sourceX₁_mul_sourceY₁`,
  `MPOTensor.sourceCutM₂_eq_sourceX₂_mul_sourceY₂`: the exact source-cut factorizations.
* `MPOTensor.sourceX₁_mul_sourceY₁_apply`, `MPOTensor.sourceX₂_mul_sourceY₂_apply`: the
  entry formulas identifying the two graphical source decompositions with the tensor entries.
* `MPOTensor.sourceX₁_weighted_isometry`, `MPOTensor.sourceX₂_isometry`: the two left-factor
  normalizations.
* `MPOTensor.sourceY₁_mul_sourceZ₁`, `MPOTensor.sourceY₂_mul_sourceZ₂`: the two right-inverse
  identities.

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

/-- A compact SVD transported to a product-index source cut and its paper rank.
This is the coordinate form of arXiv:1703.09188, `eq:sf-svd` (lines 479--486). -/
structure SourceCutSVD {α β : Type*} [Fintype α] [Fintype β]
    (M : Matrix α β ℂ) (r : ℕ) where
  /-- The left row-coisometry. -/
  V : Matrix (Fin r) α ℂ
  /-- The right row-coisometry. -/
  U : Matrix (Fin r) β ℂ
  /-- The strictly positive diagonal singular-value matrix. -/
  diagonal : Matrix (Fin r) (Fin r) ℂ
  /-- The inverse diagonal singular-value matrix. -/
  inverseDiagonal : Matrix (Fin r) (Fin r) ℂ
  /-- The compact SVD factorization. -/
  factorization : M = Vᴴ * diagonal * U
  /-- The left SVD matrix is a row coisometry. -/
  V_coisometry : V.IsCoisometry
  /-- The right SVD matrix is a row coisometry. -/
  U_coisometry : U.IsCoisometry
  /-- The singular-value matrix is diagonal. -/
  diagonal_isDiag : diagonal.IsDiag
  /-- Every retained singular value is strictly positive. -/
  diagonal_posDef : diagonal.PosDef
  /-- The inverse singular-value matrix is diagonal. -/
  inverseDiagonal_isDiag : inverseDiagonal.IsDiag
  /-- Every inverse singular value is strictly positive. -/
  inverseDiagonal_posDef : inverseDiagonal.PosDef
  /-- The diagonal singular-value matrix cancels its inverse. -/
  diagonal_mul_inverseDiagonal : diagonal * inverseDiagonal = 1

private noncomputable def productCompactSVD
    {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    {m n r : ℕ} (M : Matrix α β ℂ) (MFin : Matrix (Fin m) (Fin n) ℂ)
    (rowEquiv : Fin m ≃ α) (colEquiv : Fin n ≃ β)
    (hM : Matrix.reindex rowEquiv colEquiv MFin = M) (hrank : MFin.rank = r) :
    SourceCutSVD M r := by
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
  have hdiagonal_isDiag : diagonal.IsDiag := by
    change (S.diagonal.submatrix rankEquiv.symm rankEquiv.symm).IsDiag
    exact (Matrix.isDiag_diagonal _).submatrix rankEquiv.symm.injective
  have hdiagonal_posDef : diagonal.PosDef := by
    change (S.diagonal.submatrix rankEquiv.symm rankEquiv.symm).PosDef
    exact S.diagonal_posDef.submatrix rankEquiv.symm.injective
  have hinverseDiagonal_isDiag : inverseDiagonal.IsDiag := by
    change (S.inverseDiagonal.submatrix rankEquiv.symm rankEquiv.symm).IsDiag
    exact (Matrix.isDiag_diagonal _).submatrix rankEquiv.symm.injective
  have hinverseDiagonal_posDef : inverseDiagonal.PosDef := by
    change (S.inverseDiagonal.submatrix rankEquiv.symm rankEquiv.symm).PosDef
    exact S.inverseDiagonal_posDef.submatrix rankEquiv.symm.injective
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
  exact ⟨V, U', diagonal, inverseDiagonal, hfactorization, hV, hU,
    hdiagonal_isDiag, hdiagonal_posDef, hinverseDiagonal_isDiag,
    hinverseDiagonal_posDef, hdiagonal⟩

/-- The product-index compact SVD of the first source cut, with intermediate dimension $r$.
This is arXiv:1703.09188, `eq:sf-svd` for $\mathcal M_1$ (lines 479--486). -/
noncomputable def sourceSVD₁ :
    SourceCutSVD (sourceCutM₁ U) r[U] :=
  productCompactSVD (sourceCutM₁ U) (sourceCutM₁Fin U)
    (finProdFinEquiv (m := D) (n := d)).symm
    (finProdFinEquiv (m := d) (n := D)).symm
    (by simp [sourceCutM₁Fin, Matrix.reindex_apply])
    (sourceCutM₁_rank_eq_sourceCutM₁Fin_rank U).symm

/-- The product-index compact SVD of the second source cut, with intermediate dimension $\ell$.
This is arXiv:1703.09188, `eq:sf-svd` for $\mathcal M_2$ (lines 479--486). -/
noncomputable def sourceSVD₂ :
    SourceCutSVD (sourceCutM₂ U) ℓ[U] :=
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

/-- The positive normalization matrix $A=V_1(\rho\otimes I_d)V_1^*$ from
arXiv:1703.09188, `Y1Y1X1X1` (lines 487--494). -/
noncomputable def sourceGram₁ (ρ : Matrix (Fin D) (Fin D) ℂ) :
    Matrix (Fin r[U]) (Fin r[U]) ℂ :=
  (sourceSVD₁ U).V * sourceWeight (d := d) ρ * (sourceSVD₁ U).Vᴴ

/-- The first source normalization matrix is positive definite when $\rho$ is.
This justifies the inverse square root in arXiv:1703.09188, `Y1Y1X1X1` (lines 487--494). -/
theorem sourceGram₁_posDef {ρ : Matrix (Fin D) (Fin D) ℂ}
    (hρ : ρ.PosDef) : (sourceGram₁ U ρ).PosDef :=
  (sourceWeight_posDef (d := d) hρ).mul_mul_conjTranspose_same
    (sourceSVD₁_V_vecMul_injective U)

/-- The weighted factor $X_1=V_1^*A^{-1/2}$ from arXiv:1703.09188,
`Y1Y1X1X1` (lines 487--494). -/
noncomputable def sourceX₁ (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef) :
    Matrix (Fin D × Fin d) (Fin r[U]) ℂ :=
  (sourceSVD₁ U).Vᴴ * (sourceGram₁_posDef U hρ).posSemidef.supportInvSqrt

/-- The weighted factor $Y_1=A^{1/2}D_1U_1$ determined by
$\mathcal M_1=X_1Y_1$, arXiv:1703.09188, `eq:sf-svd`--`Y1Y1X1X1` (lines 479--494). -/
noncomputable def sourceY₁ (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef) :
    Matrix (Fin r[U]) (Fin d × Fin D) ℂ :=
  (sourceGram₁_posDef U hρ).isHermitian.cfc Real.sqrt *
    (sourceSVD₁ U).diagonal * (sourceSVD₁ U).U

/-- The factor $Z_1=U_1^*D_1^{-1}A^{-1/2}$ from arXiv:1703.09188,
`Z1Z2` (lines 495--502). -/
noncomputable def sourceZ₁ (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef) :
    Matrix (Fin d × Fin D) (Fin r[U]) ℂ :=
  (sourceSVD₁ U).Uᴴ * (sourceSVD₁ U).inverseDiagonal *
    (sourceGram₁_posDef U hρ).posSemidef.supportInvSqrt

/-- The ordinary factor $X_2=V_2^*$ from arXiv:1703.09188,
`Y1Y1X1X1` (lines 487--494). -/
noncomputable def sourceX₂ : Matrix (Fin D × Fin d) (Fin ℓ[U]) ℂ :=
  (sourceSVD₂ U).Vᴴ

/-- The ordinary factor $Y_2=D_2U_2$ determined by
$\mathcal M_2=X_2Y_2$, arXiv:1703.09188, `eq:sf-svd` (lines 479--494). -/
noncomputable def sourceY₂ : Matrix (Fin ℓ[U]) (Fin d × Fin D) ℂ :=
  (sourceSVD₂ U).diagonal * (sourceSVD₂ U).U

/-- The factor $Z_2=U_2^*D_2^{-1}$ from arXiv:1703.09188,
`Z1Z2` (lines 495--502). -/
noncomputable def sourceZ₂ : Matrix (Fin d × Fin D) (Fin ℓ[U]) ℂ :=
  (sourceSVD₂ U).Uᴴ * (sourceSVD₂ U).inverseDiagonal

/-- Entry formula for the weighted factor $X_1$ from arXiv:1703.09188,
`Y1Y1X1X1` (lines 487--494). -/
@[simp]
theorem sourceX₁_apply (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef)
    (a : Fin D × Fin d) (q : Fin r[U]) :
    sourceX₁ U ρ hρ a q = ∑ k,
      star ((sourceSVD₁ U).V k a) *
        (sourceGram₁_posDef U hρ).posSemidef.supportInvSqrt k q := by
  simp [sourceX₁, Matrix.mul_apply]

/-- Entry formula for the weighted factor $Y_1$ from arXiv:1703.09188,
`eq:sf-svd`--`Y1Y1X1X1` (lines 479--494). -/
@[simp]
theorem sourceY₁_apply (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef)
    (q : Fin r[U]) (b : Fin d × Fin D) :
    sourceY₁ U ρ hρ q b = ∑ k,
      (∑ l, (sourceGram₁_posDef U hρ).isHermitian.cfc Real.sqrt q l *
        (sourceSVD₁ U).diagonal l k) * (sourceSVD₁ U).U k b := by
  simp [sourceY₁, Matrix.mul_apply]

/-- Entry formula for the weighted factor $Z_1$ from arXiv:1703.09188,
`Z1Z2` (lines 495--502). -/
@[simp]
theorem sourceZ₁_apply (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef)
    (b : Fin d × Fin D) (q : Fin r[U]) :
    sourceZ₁ U ρ hρ b q = ∑ k,
      (∑ l, star ((sourceSVD₁ U).U l b) * (sourceSVD₁ U).inverseDiagonal l k) *
        (sourceGram₁_posDef U hρ).posSemidef.supportInvSqrt k q := by
  simp [sourceZ₁, Matrix.mul_apply]

/-- Entry formula for the ordinary factor $X_2$ from arXiv:1703.09188,
`Y1Y1X1X1` (lines 487--494). -/
@[simp]
theorem sourceX₂_apply (a : Fin D × Fin d) (q : Fin ℓ[U]) :
    sourceX₂ U a q = star ((sourceSVD₂ U).V q a) := rfl

/-- Entry formula for the ordinary factor $Y_2$ from arXiv:1703.09188,
`eq:sf-svd` (lines 479--494). -/
@[simp]
theorem sourceY₂_apply (q : Fin ℓ[U]) (b : Fin d × Fin D) :
    sourceY₂ U q b = ∑ k, (sourceSVD₂ U).diagonal q k * (sourceSVD₂ U).U k b := by
  simp [sourceY₂, Matrix.mul_apply]

/-- Entry formula for the ordinary factor $Z_2$ from arXiv:1703.09188,
`Z1Z2` (lines 495--502). -/
@[simp]
theorem sourceZ₂_apply (b : Fin d × Fin D) (q : Fin ℓ[U]) :
    sourceZ₂ U b q = ∑ k,
      star ((sourceSVD₂ U).U k b) * (sourceSVD₂ U).inverseDiagonal k q := by
  simp [sourceZ₂, Matrix.mul_apply]

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
  let hA := sourceGram₁_posDef U hρ
  let AinvSqrt := hA.posSemidef.supportInvSqrt
  let Asqrt := hA.isHermitian.cfc Real.sqrt
  let X₁ := sourceX₁ U ρ hρ
  let Y₁ := sourceY₁ U ρ hρ
  let Z₁ := sourceZ₁ U ρ hρ
  let X₂ := sourceX₂ U
  let Y₂ := sourceY₂ U
  let Z₂ := sourceZ₂ U
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
    simp only [X₂, Y₂, sourceX₂, sourceY₂, S₂, Matrix.mul_assoc]
  have hX₁ : X₁ᴴ * sourceWeight (d := d) ρ * X₁ = 1 := by
    change (S₁.Vᴴ * AinvSqrt)ᴴ * sourceWeight (d := d) ρ *
      (S₁.Vᴴ * AinvSqrt) = 1
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      hA.posSemidef.supportInvSqrt_isHermitian.eq]
    calc
      AinvSqrt * S₁.V * sourceWeight (d := d) ρ * (S₁.Vᴴ * AinvSqrt) =
          AinvSqrt * sourceGram₁ U ρ * AinvSqrt := by
        simp [sourceGram₁, S₁, AinvSqrt, Matrix.mul_assoc]
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


/-- The first exact source-cut factorization $\mathcal M_1=X_1Y_1$.
This is arXiv:1703.09188, `eq:sf-svd`, `XY`, and `SVDforms2` (lines 479--528). -/
theorem sourceCutM₁_eq_sourceX₁_mul_sourceY₁
    (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef) :
    sourceCutM₁ U = sourceX₁ U ρ hρ * sourceY₁ U ρ hρ :=
  (sourceFactors U ρ hρ).sourceCutM₁_eq

/-- The second exact source-cut factorization $\mathcal M_2=X_2Y_2$.
This is arXiv:1703.09188, `eq:sf-svd`, `XY`, and `SVDforms2` (lines 479--528). -/
theorem sourceCutM₂_eq_sourceX₂_mul_sourceY₂ :
    sourceCutM₂ U = sourceX₂ U * sourceY₂ U := by
  simpa [sourceX₂, sourceY₂, Matrix.mul_assoc] using (sourceSVD₂ U).factorization

/-- Entry form of the first graphical factorization, arXiv:1703.09188,
`X1Y1` and `SVDforms2` (lines 508--528). -/
@[simp]
theorem sourceX₁_mul_sourceY₁_apply
    (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef)
    (α : Fin D) (j : Fin d) (i : Fin d) (β : Fin D) :
    (sourceX₁ U ρ hρ * sourceY₁ U ρ hρ) (α, j) (i, β) = U i j α β := by
  rw [← sourceCutM₁_eq_sourceX₁_mul_sourceY₁ U ρ hρ]
  rfl

/-- Entry form of the second graphical factorization, arXiv:1703.09188,
`X2Y2` and `SVDforms2` (lines 508--528). -/
@[simp]
theorem sourceX₂_mul_sourceY₂_apply
    (α : Fin D) (i : Fin d) (j : Fin d) (β : Fin D) :
    (sourceX₂ U * sourceY₂ U) (α, i) (j, β) = U i j α β := by
  rw [← sourceCutM₂_eq_sourceX₂_mul_sourceY₂ U]
  rfl

/-- The weighted $X_1$ normalization, arXiv:1703.09188,
`Y1Y1X1X1` and its graphical form `X1X2b` (lines 487--524). -/
theorem sourceX₁_weighted_isometry
    (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef) :
    (sourceX₁ U ρ hρ)ᴴ * sourceWeight (d := d) ρ * sourceX₁ U ρ hρ = 1 :=
  (sourceFactors U ρ hρ).X₁_weighted_isometry

/-- The ordinary $X_2$ normalization, arXiv:1703.09188,
`Y1Y1X1X1` and its graphical form `X1X2b` (lines 487--524). -/
theorem sourceX₂_isometry : (sourceX₂ U).IsIsometry := by
  exact (sourceSVD₂ U).V_coisometry.conjTranspose (sourceSVD₂ U).V

/-- The weighted right-inverse identity $Y_1Z_1=I$ from arXiv:1703.09188,
`YZ=1` (lines 503--506). -/
theorem sourceY₁_mul_sourceZ₁
    (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef) :
    sourceY₁ U ρ hρ * sourceZ₁ U ρ hρ = 1 :=
  (sourceFactors U ρ hρ).Y₁_mul_Z₁

/-- The ordinary right-inverse identity $Y_2Z_2=I$ from arXiv:1703.09188,
`YZ=1` (lines 503--506). -/
theorem sourceY₂_mul_sourceZ₂ : sourceY₂ U * sourceZ₂ U = 1 := by
  rw [sourceY₂, sourceZ₂]
  calc
    ((sourceSVD₂ U).diagonal * (sourceSVD₂ U).U) *
        ((sourceSVD₂ U).Uᴴ * (sourceSVD₂ U).inverseDiagonal) =
      (sourceSVD₂ U).diagonal * ((sourceSVD₂ U).U * (sourceSVD₂ U).Uᴴ) *
        (sourceSVD₂ U).inverseDiagonal := by simp only [Matrix.mul_assoc]
    _ = (sourceSVD₂ U).diagonal * (sourceSVD₂ U).inverseDiagonal := by
      rw [(sourceSVD₂ U).U_coisometry, Matrix.mul_one]
    _ = 1 := (sourceSVD₂ U).diagonal_mul_inverseDiagonal

end MPOTensor
