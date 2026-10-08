/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.MatrixUnitaryConjCFC
import TNLean.MPS.MPU.SourceUV

/-!
# Source factors for an arbitrary choice of compact decompositions

The source factors of arXiv:1703.09188, `eq:sf-svd`, `Y1Y1X1X1` and `Z1Z2` (lines 479--502),
are written there for "a singular value decomposition" $\mathcal M_{1,2}=V^\dagger DU$ of the two
cut matrices, without fixing one. The library construction `MPOTensor.sourceFactors` uses one fixed
choice `sourceSVD₁`, `sourceSVD₂`. This module builds the factors from arbitrary compact
decompositions and shows that two choices change the factors and the gates by unitaries on the
two rank spaces (milestone M-E proposal, `ME.tex`, Lemmas 1.1, 1.2 and Theorem 1.3).

## Main definitions

* `MPOTensor.SourceCutSVD.relatingUnitary`: the unitary $x=C'C^\dagger$ relating two compact
  decompositions of one matrix.
* `MPOTensor.sourceGramOf`, `sourceX₁Of`, `sourceY₁Of`, `sourceZ₁Of`, `sourceX₂Of`, `sourceY₂Of`,
  `sourceZ₂Of`: the normalization matrix and the six source factors of supplied decompositions.
* `MPOTensor.sourceFactorsOf`: the factor datum of supplied decompositions.

## Main results

* `MPOTensor.SourceCutSVD.conjTranspose_mul_V_eq`, `conjTranspose_mul_U_eq`: two compact
  decompositions have the same column and row projections.
* `MPOTensor.SourceCutSVD.exists_unitary_relating`: they differ by a unitary.
* `MPOTensor.sourceFactors_eq_sourceFactorsOf`: the fixed choice is one instance.
* `MPOTensor.sourceX₁Of_eq_of_V_eq` and its five companions: the change of the factors.
* `MPOTensor.sourceU_sourceFactorsOf_eq_of_V_eq`, `sourceV_sourceFactorsOf_eq_of_V_eq`,
  `sourceU_sourceFactorsOf_eq`: the change of the gates.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017, arXiv:1703.09188], equations `eq:sf-svd`,
  `Y1Y1X1X1`, `Z1Z2`, lines 479--502.
* Milestone M-E proposal `ME.tex` (mpu-notes, programme `mpu-close`), Section 2.
-/

open scoped Matrix Kronecker ComplexOrder
open Matrix

namespace MPOTensor

namespace SourceCutSVD

variable {α β : Type*} [Fintype α] [Fintype β] {M : Matrix α β ℂ} {r : ℕ}

/-- The decomposition $M^\dagger=U^\dagger DV$ of the adjoint, obtained by exchanging the two
coisometries of a compact decomposition $M=V^\dagger DU$ (arXiv:1703.09188, `eq:sf-svd`). -/
noncomputable def conjTranspose (S : SourceCutSVD M r) : SourceCutSVD Mᴴ r where
  V := S.U
  U := S.V
  diagonal := S.diagonal
  inverseDiagonal := S.inverseDiagonal
  factorization := by
    have h := congrArg Matrix.conjTranspose S.factorization
    rwa [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      S.diagonal_posDef.isHermitian.eq, ← Matrix.mul_assoc] at h
  V_coisometry := S.U_coisometry
  U_coisometry := S.V_coisometry
  diagonal_isDiag := S.diagonal_isDiag
  diagonal_posDef := S.diagonal_posDef
  inverseDiagonal_isDiag := S.inverseDiagonal_isDiag
  inverseDiagonal_posDef := S.inverseDiagonal_posDef
  diagonal_mul_inverseDiagonal := S.diagonal_mul_inverseDiagonal

/-- The inverse singular-value matrix is also a left inverse. -/
theorem inverseDiagonal_mul_diagonal (S : SourceCutSVD M r) :
    S.inverseDiagonal * S.diagonal = 1 :=
  mul_eq_one_comm.mp S.diagonal_mul_inverseDiagonal

/-- The left factor is recovered from the matrix, $V^\dagger=MU^\dagger D^{-1}$
(ME.tex, proof of Lemma 1.1). -/
theorem conjTranspose_V_eq (S : SourceCutSVD M r) :
    S.Vᴴ = M * S.Uᴴ * S.inverseDiagonal := by
  have h : S.Vᴴ * S.diagonal * S.U * S.Uᴴ * S.inverseDiagonal = S.Vᴴ := by
    rw [Matrix.mul_assoc _ S.U, S.U_coisometry, Matrix.mul_one, Matrix.mul_assoc,
      S.diagonal_mul_inverseDiagonal, Matrix.mul_one]
  rw [← S.factorization] at h
  exact h.symm

/-- The column projection $V^\dagger V$ of a decomposition fixes the matrix. -/
theorem conjTranspose_mul_V_mul_self (S : SourceCutSVD M r) :
    S.Vᴴ * S.V * M = M := by
  have h : S.Vᴴ * S.V * (S.Vᴴ * S.diagonal * S.U) = S.Vᴴ * S.diagonal * S.U := by
    rw [Matrix.mul_assoc S.Vᴴ S.V, ← Matrix.mul_assoc S.V, ← Matrix.mul_assoc S.V,
      S.V_coisometry, Matrix.one_mul, ← Matrix.mul_assoc]
  rwa [← S.factorization] at h

/-- The identity $VM=DU$ of a compact decomposition. -/
theorem V_mul_self (S : SourceCutSVD M r) :
    S.V * M = S.diagonal * S.U := by
  have h : S.V * (S.Vᴴ * S.diagonal * S.U) = S.diagonal * S.U := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, S.V_coisometry, Matrix.one_mul]
  rwa [← S.factorization] at h

/-- The column projection of one decomposition fixes the left factor of another. -/
theorem conjTranspose_mul_V_mul_conjTranspose (S S' : SourceCutSVD M r) :
    S'.Vᴴ * S'.V * S.Vᴴ = S.Vᴴ := by
  rw [S.conjTranspose_V_eq, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    S'.conjTranspose_mul_V_mul_self]

/-- Two compact decompositions of one matrix have the same column projection,
$C'^\dagger C'=C^\dagger C$ (ME.tex, Lemma 1.1; arXiv:1703.09188, `eq:sf-svd`, lines 479--486). -/
theorem conjTranspose_mul_V_eq (S S' : SourceCutSVD M r) :
    S'.Vᴴ * S'.V = S.Vᴴ * S.V := by
  have h₁ : S'.Vᴴ * S'.V * (S.Vᴴ * S.V) = S.Vᴴ * S.V := by
    rw [← Matrix.mul_assoc, conjTranspose_mul_V_mul_conjTranspose]
  have h₂ : S.Vᴴ * S.V * (S'.Vᴴ * S'.V) = S'.Vᴴ * S'.V := by
    rw [← Matrix.mul_assoc, conjTranspose_mul_V_mul_conjTranspose]
  have hP : (S.Vᴴ * S.V)ᴴ = S.Vᴴ * S.V := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  have hP' : (S'.Vᴴ * S'.V)ᴴ = S'.Vᴴ * S'.V := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  have h₃ := congrArg Matrix.conjTranspose h₁
  rw [Matrix.conjTranspose_mul, hP, hP'] at h₃
  rw [← h₂, h₃]

/-- Two compact decompositions of one matrix have the same row projection,
$G'^\dagger G'=G^\dagger G$ (ME.tex, Lemma 1.1; arXiv:1703.09188, `eq:sf-svd`, lines 479--486). -/
theorem conjTranspose_mul_U_eq (S S' : SourceCutSVD M r) :
    S'.Uᴴ * S'.U = S.Uᴴ * S.U :=
  conjTranspose_mul_V_eq S.conjTranspose S'.conjTranspose

/-- The unitary $x=C'C^\dagger$ relating two compact decompositions of one matrix
(ME.tex, Lemma 1.1). -/
noncomputable def relatingUnitary (S S' : SourceCutSVD M r) : unitaryGroup (Fin r) ℂ :=
  ⟨S'.V * S.Vᴴ, by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, ← Matrix.mul_assoc, Matrix.mul_assoc S'.V S.Vᴴ,
      ← conjTranspose_mul_V_eq S S', ← Matrix.mul_assoc, S'.V_coisometry, Matrix.one_mul,
      S'.V_coisometry]⟩

/-- The relating unitary carries the first left factor to the second, $xC=C'$
(ME.tex, Lemma 1.1). -/
theorem relatingUnitary_mul_V (S S' : SourceCutSVD M r) :
    (relatingUnitary S S' : Matrix (Fin r) (Fin r) ℂ) * S.V = S'.V := by
  change S'.V * S.Vᴴ * S.V = S'.V
  rw [Matrix.mul_assoc, ← conjTranspose_mul_V_eq S S', ← Matrix.mul_assoc, S'.V_coisometry,
    Matrix.one_mul]

/-- If $C'=xC$ then $S'G'=xSG$ (ME.tex, Lemma 1.1). -/
theorem diagonal_mul_U_eq_of_V_eq {S S' : SourceCutSVD M r} {x : Matrix (Fin r) (Fin r) ℂ}
    (hx : S'.V = x * S.V) : S'.diagonal * S'.U = x * (S.diagonal * S.U) := by
  rw [← V_mul_self, ← V_mul_self, hx, Matrix.mul_assoc]

/-- Two compact decompositions of one matrix differ by a unitary on the rank space:
$C'=xC$ and $S'G'=xSG$ (ME.tex, Lemma 1.1; arXiv:1703.09188, `eq:sf-svd`, lines 479--486). -/
theorem exists_unitary_relating (S S' : SourceCutSVD M r) :
    ∃ x : Matrix.unitaryGroup (Fin r) ℂ,
      S'.V = (x : Matrix (Fin r) (Fin r) ℂ) * S.V ∧
        S'.diagonal * S'.U = (x : Matrix (Fin r) (Fin r) ℂ) * (S.diagonal * S.U) :=
  ⟨relatingUnitary S S', (relatingUnitary_mul_V S S').symm,
    diagonal_mul_U_eq_of_V_eq (relatingUnitary_mul_V S S').symm⟩

/-- The Gram identity $(DU)(DU)^\dagger=D^2$. -/
theorem diagonal_mul_U_mul_conjTranspose (S : SourceCutSVD M r) :
    S.diagonal * S.U * (S.diagonal * S.U)ᴴ = S.diagonal * S.diagonal := by
  rw [Matrix.conjTranspose_mul, S.diagonal_posDef.isHermitian.eq, Matrix.mul_assoc,
    ← Matrix.mul_assoc S.U, S.U_coisometry, Matrix.one_mul]

/-- The identity $U^\dagger D^{-1}=(DU)^\dagger D^{-2}$. -/
theorem conjTranspose_U_mul_inverseDiagonal_eq (S : SourceCutSVD M r) :
    S.Uᴴ * S.inverseDiagonal =
      (S.diagonal * S.U)ᴴ * (S.inverseDiagonal * S.inverseDiagonal) := by
  rw [Matrix.conjTranspose_mul, S.diagonal_posDef.isHermitian.eq, Matrix.mul_assoc,
    ← Matrix.mul_assoc S.diagonal, S.diagonal_mul_inverseDiagonal, Matrix.one_mul]

/-- If $C'=xC$ for a unitary $x$, then $G'^\dagger S'^{-1}=G^\dagger S^{-1}x^\dagger$
(ME.tex, proof of Theorem 1.3, the $Z$ factors). -/
theorem conjTranspose_mul_inverseDiagonal_eq {S S' : SourceCutSVD M r}
    {x : unitaryGroup (Fin r) ℂ} (hx : S'.V = (x : Matrix (Fin r) (Fin r) ℂ) * S.V) :
    S'.Uᴴ * S'.inverseDiagonal =
      S.Uᴴ * S.inverseDiagonal * (x : Matrix (Fin r) (Fin r) ℂ)ᴴ := by
  set X : Matrix (Fin r) (Fin r) ℂ := (x : Matrix (Fin r) (Fin r) ℂ)
  have hXX : Xᴴ * X = 1 := Matrix.conjTranspose_mul_unitary x
  have hE := diagonal_mul_U_eq_of_V_eq hx
  have hsq : S'.diagonal * S'.diagonal = X * (S.diagonal * S.diagonal) * Xᴴ := by
    rw [← diagonal_mul_U_mul_conjTranspose, hE, ← diagonal_mul_U_mul_conjTranspose,
      Matrix.conjTranspose_mul]
    simp only [Matrix.mul_assoc]
  have hright : S'.diagonal * S'.diagonal *
      (X * (S.inverseDiagonal * S.inverseDiagonal) * Xᴴ) = 1 := by
    rw [hsq]
    calc X * (S.diagonal * S.diagonal) * Xᴴ * (X * (S.inverseDiagonal * S.inverseDiagonal) * Xᴴ)
        = X * (S.diagonal * S.diagonal) * (Xᴴ * X) *
            (S.inverseDiagonal * S.inverseDiagonal) * Xᴴ := by
          simp only [Matrix.mul_assoc]
      _ = X * (S.diagonal * (S.diagonal * S.inverseDiagonal) * S.inverseDiagonal) * Xᴴ := by
          rw [hXX, Matrix.mul_one]
          simp only [Matrix.mul_assoc]
      _ = X * Xᴴ := by
          rw [S.diagonal_mul_inverseDiagonal, Matrix.mul_one, S.diagonal_mul_inverseDiagonal,
            Matrix.mul_one]
      _ = 1 := mul_eq_one_comm.mp hXX
  have hleft : S'.inverseDiagonal * S'.inverseDiagonal * (S'.diagonal * S'.diagonal) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc S'.inverseDiagonal S'.diagonal,
      S'.inverseDiagonal_mul_diagonal, Matrix.one_mul, S'.inverseDiagonal_mul_diagonal]
  have hinv : S'.inverseDiagonal * S'.inverseDiagonal =
      X * (S.inverseDiagonal * S.inverseDiagonal) * Xᴴ := by
    calc S'.inverseDiagonal * S'.inverseDiagonal =
          S'.inverseDiagonal * S'.inverseDiagonal * (S'.diagonal * S'.diagonal *
            (X * (S.inverseDiagonal * S.inverseDiagonal) * Xᴴ)) := by
          rw [hright, Matrix.mul_one]
      _ = X * (S.inverseDiagonal * S.inverseDiagonal) * Xᴴ := by
          rw [← Matrix.mul_assoc, hleft, Matrix.one_mul]
  calc S'.Uᴴ * S'.inverseDiagonal =
        (S'.diagonal * S'.U)ᴴ * (S'.inverseDiagonal * S'.inverseDiagonal) :=
        conjTranspose_U_mul_inverseDiagonal_eq S'
    _ = (S.diagonal * S.U)ᴴ * (Xᴴ * X) * (S.inverseDiagonal * S.inverseDiagonal) * Xᴴ := by
        rw [hE, hinv, Matrix.conjTranspose_mul]
        simp only [Matrix.mul_assoc]
    _ = S.Uᴴ * S.inverseDiagonal * Xᴴ := by
        rw [hXX, Matrix.mul_one, conjTranspose_U_mul_inverseDiagonal_eq S]

end SourceCutSVD

section Factors

variable {d D : ℕ} {U : MPOTensor d D}

/-- The left multiplication by a row coisometry is injective on row vectors. -/
private theorem vecMul_injective_of_isCoisometry {m k : Type*} [Fintype m] [Fintype k]
    [DecidableEq m] {V : Matrix m k ℂ} (hV : V.IsCoisometry) : Function.Injective V.vecMul := by
  intro x y hxy
  calc
    x = x ᵥ* (V * Vᴴ) := by rw [hV, Matrix.vecMul_one]
    _ = (x ᵥ* V) ᵥ* Vᴴ := (Matrix.vecMul_vecMul _ _ _).symm
    _ = (y ᵥ* V) ᵥ* Vᴴ := congrArg (fun z ↦ z ᵥ* Vᴴ) hxy
    _ = y ᵥ* (V * Vᴴ) := Matrix.vecMul_vecMul _ _ _
    _ = y := by rw [hV, Matrix.vecMul_one]

/-- The normalization matrix $H=C_1(I_d\otimes\rho)C_1^\dagger$ of a supplied decomposition
of the first cut, arXiv:1703.09188, `Y1Y1X1X1` (lines 487--494); ME.tex, Lemma 1.2. -/
noncomputable def sourceGramOf (S₁ : SourceCutSVD (sourceCutM₁ U) r[U])
    (ρ : Matrix (Fin D) (Fin D) ℂ) : Matrix (Fin r[U]) (Fin r[U]) ℂ :=
  S₁.V * sourceWeight (d := d) ρ * S₁.Vᴴ

/-- The normalization matrix of any decomposition is positive definite when $\rho$ is
(ME.tex, proof of Lemma 1.2; arXiv:1703.09188, `Y1Y1X1X1`, lines 487--494). -/
theorem sourceGramOf_posDef (S₁ : SourceCutSVD (sourceCutM₁ U) r[U])
    {ρ : Matrix (Fin D) (Fin D) ℂ} (hρ : ρ.PosDef) : (sourceGramOf S₁ ρ).PosDef :=
  (sourceWeight_posDef (d := d) hρ).mul_mul_conjTranspose_same
    (vecMul_injective_of_isCoisometry S₁.V_coisometry)

/-- The weighted factor $X_1=C_1^\dagger H^{-1/2}$ of a supplied decomposition,
arXiv:1703.09188, `Y1Y1X1X1` (lines 487--494); ME.tex, Lemma 1.2. -/
noncomputable def sourceX₁Of (S₁ : SourceCutSVD (sourceCutM₁ U) r[U])
    (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef) : Matrix (Fin d × Fin D) (Fin r[U]) ℂ :=
  S₁.Vᴴ * (sourceGramOf_posDef S₁ hρ).posSemidef.supportInvSqrt

/-- The weighted factor $Y_1=H^{1/2}S_1G_1$ of a supplied decomposition,
arXiv:1703.09188, `eq:sf-svd`--`Y1Y1X1X1` (lines 479--494); ME.tex, Lemma 1.2. -/
noncomputable def sourceY₁Of (S₁ : SourceCutSVD (sourceCutM₁ U) r[U])
    (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef) : Matrix (Fin r[U]) (Fin D × Fin d) ℂ :=
  (sourceGramOf_posDef S₁ hρ).isHermitian.cfc Real.sqrt * S₁.diagonal * S₁.U

/-- The factor $Z_1=G_1^\dagger S_1^{-1}H^{-1/2}$ of a supplied decomposition,
arXiv:1703.09188, `Z1Z2` (lines 495--502); ME.tex, Lemma 1.2. -/
noncomputable def sourceZ₁Of (S₁ : SourceCutSVD (sourceCutM₁ U) r[U])
    (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef) : Matrix (Fin D × Fin d) (Fin r[U]) ℂ :=
  S₁.Uᴴ * S₁.inverseDiagonal * (sourceGramOf_posDef S₁ hρ).posSemidef.supportInvSqrt

/-- The factor $X_2=C_2^\dagger$ of a supplied decomposition,
arXiv:1703.09188, `Y1Y1X1X1` (lines 487--494); ME.tex, Lemma 1.2. -/
noncomputable def sourceX₂Of (S₂ : SourceCutSVD (sourceCutM₂ U) ℓ[U]) :
    Matrix (Fin D × Fin d) (Fin ℓ[U]) ℂ :=
  S₂.Vᴴ

/-- The factor $Y_2=S_2G_2$ of a supplied decomposition,
arXiv:1703.09188, `eq:sf-svd` (lines 479--494); ME.tex, Lemma 1.2. -/
noncomputable def sourceY₂Of (S₂ : SourceCutSVD (sourceCutM₂ U) ℓ[U]) :
    Matrix (Fin ℓ[U]) (Fin d × Fin D) ℂ :=
  S₂.diagonal * S₂.U

/-- The factor $Z_2=G_2^\dagger S_2^{-1}$ of a supplied decomposition,
arXiv:1703.09188, `Z1Z2` (lines 495--502); ME.tex, Lemma 1.2. -/
noncomputable def sourceZ₂Of (S₂ : SourceCutSVD (sourceCutM₂ U) ℓ[U]) :
    Matrix (Fin d × Fin D) (Fin ℓ[U]) ℂ :=
  S₂.Uᴴ * S₂.inverseDiagonal

/-- The factor datum of supplied compact decompositions of the two cuts and a positive-definite
weight: the identities $M_1=X_1Y_1$, $M_2=X_2Y_2$, $X_1^\dagger(I\otimes\rho)X_1=I$,
$X_2^\dagger X_2=I$, $Y_1Z_1=I$, $Y_2Z_2=I$ hold for every choice
(ME.tex, Lemma 1.2; arXiv:1703.09188, `eq:sf-svd`, `Y1Y1X1X1`, `Z1Z2`, lines 479--502). -/
noncomputable def sourceFactorsOf (S₁ : SourceCutSVD (sourceCutM₁ U) r[U])
    (S₂ : SourceCutSVD (sourceCutM₂ U) ℓ[U]) (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef) :
    SourceFactors U ρ := by
  let hA := sourceGramOf_posDef S₁ hρ
  let AinvSqrt := hA.posSemidef.supportInvSqrt
  let Asqrt := hA.isHermitian.cfc Real.sqrt
  let X₁ := sourceX₁Of S₁ ρ hρ
  let Y₁ := sourceY₁Of S₁ ρ hρ
  let Z₁ := sourceZ₁Of S₁ ρ hρ
  let X₂ := sourceX₂Of S₂
  let Y₂ := sourceY₂Of S₂
  let Z₂ := sourceZ₂Of S₂
  have hcut₁ : sourceCutM₁ U = X₁ * Y₁ := by
    have h : S₁.Vᴴ * S₁.diagonal * S₁.U =
        (S₁.Vᴴ * AinvSqrt) * (Asqrt * S₁.diagonal * S₁.U) := by
      calc
        S₁.Vᴴ * S₁.diagonal * S₁.U =
            S₁.Vᴴ * (1 : Matrix (Fin r[U]) (Fin r[U]) ℂ) * S₁.diagonal * S₁.U := by
          simp only [Matrix.mul_one]
        _ = S₁.Vᴴ * (AinvSqrt * Asqrt) * S₁.diagonal * S₁.U := by
          rw [hA.posSemidef.supportInvSqrt_mul_cfc_sqrt, hA.supportProj_eq_one]
        _ = (S₁.Vᴴ * AinvSqrt) * (Asqrt * S₁.diagonal * S₁.U) := by
          simp only [Matrix.mul_assoc]
    rw [← S₁.factorization] at h
    exact h
  have hcut₂ : sourceCutM₂ U = X₂ * Y₂ := by
    have h := S₂.factorization
    rwa [Matrix.mul_assoc] at h
  have hX₁ : X₁ᴴ * sourceWeight (d := d) ρ * X₁ = 1 := by
    change (S₁.Vᴴ * AinvSqrt)ᴴ * sourceWeight (d := d) ρ * (S₁.Vᴴ * AinvSqrt) = 1
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      hA.posSemidef.supportInvSqrt_isHermitian.eq]
    calc
      AinvSqrt * S₁.V * sourceWeight (d := d) ρ * (S₁.Vᴴ * AinvSqrt) =
          AinvSqrt * sourceGramOf S₁ ρ * AinvSqrt := by
        simp [sourceGramOf, Matrix.mul_assoc]
      _ = hA.posSemidef.supportProj :=
        hA.posSemidef.supportInvSqrt_mul_self_mul_supportInvSqrt
      _ = 1 := hA.supportProj_eq_one
  have hX₂ : X₂.IsIsometry := S₂.V_coisometry.conjTranspose S₂.V
  have hY₁Z₁ : Y₁ * Z₁ = 1 := by
    change (Asqrt * S₁.diagonal * S₁.U) * (S₁.Uᴴ * S₁.inverseDiagonal * AinvSqrt) = 1
    calc
      (Asqrt * S₁.diagonal * S₁.U) * (S₁.Uᴴ * S₁.inverseDiagonal * AinvSqrt) =
        Asqrt * S₁.diagonal * (S₁.U * S₁.Uᴴ) * S₁.inverseDiagonal * AinvSqrt := by
        simp only [Matrix.mul_assoc]
      _ = Asqrt * (S₁.diagonal * S₁.inverseDiagonal) * AinvSqrt := by
        rw [S₁.U_coisometry, Matrix.mul_one]
        simp only [Matrix.mul_assoc]
      _ = Asqrt * AinvSqrt := by
        rw [S₁.diagonal_mul_inverseDiagonal, Matrix.mul_one]
      _ = hA.posSemidef.supportProj := hA.posSemidef.cfc_sqrt_mul_supportInvSqrt
      _ = 1 := hA.supportProj_eq_one
  have hY₂Z₂ : Y₂ * Z₂ = 1 := by
    change (S₂.diagonal * S₂.U) * (S₂.Uᴴ * S₂.inverseDiagonal) = 1
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc S₂.U, S₂.U_coisometry, Matrix.one_mul,
      S₂.diagonal_mul_inverseDiagonal]
  exact ⟨X₁, Y₁, Z₁, X₂, Y₂, Z₂, hcut₁, hcut₂, hX₁, hX₂, hY₁Z₁, hY₂Z₂⟩

section Fields

variable (S₁ : SourceCutSVD (sourceCutM₁ U) r[U]) (S₂ : SourceCutSVD (sourceCutM₂ U) ℓ[U])
  (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef)

/-- The first weighted factor of `sourceFactorsOf` (ME.tex, Lemma 1.2). -/
@[simp] theorem sourceFactorsOf_X₁ : (sourceFactorsOf S₁ S₂ ρ hρ).X₁ = sourceX₁Of S₁ ρ hρ := rfl

/-- The first right factor of `sourceFactorsOf` (ME.tex, Lemma 1.2). -/
@[simp] theorem sourceFactorsOf_Y₁ : (sourceFactorsOf S₁ S₂ ρ hρ).Y₁ = sourceY₁Of S₁ ρ hρ := rfl

/-- The first right inverse of `sourceFactorsOf` (ME.tex, Lemma 1.2). -/
@[simp] theorem sourceFactorsOf_Z₁ : (sourceFactorsOf S₁ S₂ ρ hρ).Z₁ = sourceZ₁Of S₁ ρ hρ := rfl

/-- The second left factor of `sourceFactorsOf` (ME.tex, Lemma 1.2). -/
@[simp] theorem sourceFactorsOf_X₂ : (sourceFactorsOf S₁ S₂ ρ hρ).X₂ = sourceX₂Of S₂ := rfl

/-- The second right factor of `sourceFactorsOf` (ME.tex, Lemma 1.2). -/
@[simp] theorem sourceFactorsOf_Y₂ : (sourceFactorsOf S₁ S₂ ρ hρ).Y₂ = sourceY₂Of S₂ := rfl

/-- The second right inverse of `sourceFactorsOf` (ME.tex, Lemma 1.2). -/
@[simp] theorem sourceFactorsOf_Z₂ : (sourceFactorsOf S₁ S₂ ρ hρ).Z₂ = sourceZ₂Of S₂ := rfl

end Fields

/-- The library's fixed factor datum is the instance of `sourceFactorsOf` at the fixed
decompositions `sourceSVD₁`, `sourceSVD₂` (ME.tex, Lemma 1.2). -/
theorem sourceFactors_eq_sourceFactorsOf (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef) :
    sourceFactors U ρ hρ = sourceFactorsOf (sourceSVD₁ U) (sourceSVD₂ U) ρ hρ := rfl

end Factors

section Change

variable {d D : ℕ} {U : MPOTensor d D}
  {S₁ S₁' : SourceCutSVD (sourceCutM₁ U) r[U]} {S₂ S₂' : SourceCutSVD (sourceCutM₂ U) ℓ[U]}
  {x₁ : unitaryGroup (Fin r[U]) ℂ} {x₂ : unitaryGroup (Fin ℓ[U]) ℂ}

/-- If $C_1'=x_1C_1$ then $H'=x_1Hx_1^\dagger$ (ME.tex, proof of Theorem 1.3). -/
theorem sourceGramOf_eq_of_V_eq (ρ : Matrix (Fin D) (Fin D) ℂ)
    (hx₁ : S₁'.V = (x₁ : Matrix (Fin r[U]) (Fin r[U]) ℂ) * S₁.V) :
    sourceGramOf S₁' ρ =
      (x₁ : Matrix (Fin r[U]) (Fin r[U]) ℂ) * sourceGramOf S₁ ρ *
        (x₁ : Matrix (Fin r[U]) (Fin r[U]) ℂ)ᴴ := by
  simp only [sourceGramOf, hx₁, Matrix.conjTranspose_mul, Matrix.mul_assoc]

/-- Change of decomposition for $X_1$: $X_1'=X_1x_1^\dagger$
(ME.tex, Theorem 1.3; arXiv:1703.09188, `Y1Y1X1X1`, lines 487--494). -/
theorem sourceX₁Of_eq_of_V_eq (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef)
    (hx₁ : S₁'.V = (x₁ : Matrix (Fin r[U]) (Fin r[U]) ℂ) * S₁.V) :
    sourceX₁Of S₁' ρ hρ = sourceX₁Of S₁ ρ hρ * (x₁ : Matrix (Fin r[U]) (Fin r[U]) ℂ)ᴴ := by
  rw [sourceX₁Of, sourceX₁Of,
    (sourceGramOf_posDef S₁ hρ).posSemidef.supportInvSqrt_eq_of_eq_unitary_conj
      (sourceGramOf_posDef S₁' hρ).posSemidef x₁ (sourceGramOf_eq_of_V_eq ρ hx₁),
    hx₁, Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc _ (x₁ : Matrix (Fin r[U]) (Fin r[U]) ℂ),
    Matrix.conjTranspose_mul_unitary, Matrix.one_mul]

/-- Change of decomposition for $Y_1$: $Y_1'=x_1Y_1$
(ME.tex, Theorem 1.3; arXiv:1703.09188, `eq:sf-svd`--`Y1Y1X1X1`, lines 479--494). -/
theorem sourceY₁Of_eq_of_V_eq (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef)
    (hx₁ : S₁'.V = (x₁ : Matrix (Fin r[U]) (Fin r[U]) ℂ) * S₁.V) :
    sourceY₁Of S₁' ρ hρ = (x₁ : Matrix (Fin r[U]) (Fin r[U]) ℂ) * sourceY₁Of S₁ ρ hρ := by
  rw [sourceY₁Of, sourceY₁Of,
    (sourceGramOf_posDef S₁ hρ).isHermitian.cfc_eq_of_eq_unitary_conj
      (sourceGramOf_posDef S₁' hρ).isHermitian x₁ (sourceGramOf_eq_of_V_eq ρ hx₁),
    Matrix.mul_assoc _ S₁'.diagonal, SourceCutSVD.diagonal_mul_U_eq_of_V_eq hx₁]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc _ (x₁ : Matrix (Fin r[U]) (Fin r[U]) ℂ),
    Matrix.conjTranspose_mul_unitary, Matrix.one_mul]

/-- Change of decomposition for $Z_1$: $Z_1'=Z_1x_1^\dagger$
(ME.tex, Theorem 1.3; arXiv:1703.09188, `Z1Z2`, lines 495--502). -/
theorem sourceZ₁Of_eq_of_V_eq (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef)
    (hx₁ : S₁'.V = (x₁ : Matrix (Fin r[U]) (Fin r[U]) ℂ) * S₁.V) :
    sourceZ₁Of S₁' ρ hρ = sourceZ₁Of S₁ ρ hρ * (x₁ : Matrix (Fin r[U]) (Fin r[U]) ℂ)ᴴ := by
  rw [sourceZ₁Of, sourceZ₁Of,
    (sourceGramOf_posDef S₁ hρ).posSemidef.supportInvSqrt_eq_of_eq_unitary_conj
      (sourceGramOf_posDef S₁' hρ).posSemidef x₁ (sourceGramOf_eq_of_V_eq ρ hx₁),
    SourceCutSVD.conjTranspose_mul_inverseDiagonal_eq hx₁]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc _ (x₁ : Matrix (Fin r[U]) (Fin r[U]) ℂ),
    Matrix.conjTranspose_mul_unitary, Matrix.one_mul]

/-- Change of decomposition for $X_2$: $X_2'=X_2x_2^\dagger$
(ME.tex, Theorem 1.3; arXiv:1703.09188, `Y1Y1X1X1`, lines 487--494). -/
theorem sourceX₂Of_eq_of_V_eq (hx₂ : S₂'.V = (x₂ : Matrix (Fin ℓ[U]) (Fin ℓ[U]) ℂ) * S₂.V) :
    sourceX₂Of S₂' = sourceX₂Of S₂ * (x₂ : Matrix (Fin ℓ[U]) (Fin ℓ[U]) ℂ)ᴴ := by
  rw [sourceX₂Of, sourceX₂Of, hx₂, Matrix.conjTranspose_mul]

/-- Change of decomposition for $Y_2$: $Y_2'=x_2Y_2$
(ME.tex, Theorem 1.3; arXiv:1703.09188, `eq:sf-svd`, lines 479--494). -/
theorem sourceY₂Of_eq_of_V_eq (hx₂ : S₂'.V = (x₂ : Matrix (Fin ℓ[U]) (Fin ℓ[U]) ℂ) * S₂.V) :
    sourceY₂Of S₂' = (x₂ : Matrix (Fin ℓ[U]) (Fin ℓ[U]) ℂ) * sourceY₂Of S₂ :=
  SourceCutSVD.diagonal_mul_U_eq_of_V_eq hx₂

/-- Change of decomposition for $Z_2$: $Z_2'=Z_2x_2^\dagger$
(ME.tex, Theorem 1.3; arXiv:1703.09188, `Z1Z2`, lines 495--502). -/
theorem sourceZ₂Of_eq_of_V_eq (hx₂ : S₂'.V = (x₂ : Matrix (Fin ℓ[U]) (Fin ℓ[U]) ℂ) * S₂.V) :
    sourceZ₂Of S₂' = sourceZ₂Of S₂ * (x₂ : Matrix (Fin ℓ[U]) (Fin ℓ[U]) ℂ)ᴴ :=
  SourceCutSVD.conjTranspose_mul_inverseDiagonal_eq hx₂

/-- Change of decomposition for the gate $u$: $u'=(x_2\otimes x_1)u$
(ME.tex, Theorem 1.3; arXiv:1703.09188, `uu`, lines 532--543). -/
theorem sourceU_sourceFactorsOf_eq_of_V_eq (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef)
    (hx₁ : S₁'.V = (x₁ : Matrix (Fin r[U]) (Fin r[U]) ℂ) * S₁.V)
    (hx₂ : S₂'.V = (x₂ : Matrix (Fin ℓ[U]) (Fin ℓ[U]) ℂ) * S₂.V) :
    SourceFactors.sourceU U (sourceFactorsOf S₁' S₂' ρ hρ) =
      ((x₂ : Matrix _ _ ℂ) ⊗ₖ (x₁ : Matrix _ _ ℂ)) *
        SourceFactors.sourceU U (sourceFactorsOf S₁ S₂ ρ hρ) := by
  ext ⟨l, q⟩ ⟨i₁, i₂⟩
  simp only [SourceFactors.sourceU_apply, sourceFactorsOf_Y₁, sourceFactorsOf_Y₂,
    sourceY₁Of_eq_of_V_eq ρ hρ hx₁, sourceY₂Of_eq_of_V_eq hx₂, Matrix.mul_apply,
    Fintype.sum_prod_type, Matrix.kroneckerMap_apply, Finset.sum_mul, Finset.mul_sum]
  conv_lhs =>
    rw [Finset.sum_comm]
    enter [2, q']
    rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦
    Finset.sum_congr rfl fun _ _ ↦ by ring

/-- Change of decomposition for the gate $v$: $v'=v(x_1^\dagger\otimes x_2^\dagger)$
(ME.tex, Theorem 1.3; arXiv:1703.09188, `vdagger`, lines 532--543). -/
theorem sourceV_sourceFactorsOf_eq_of_V_eq (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef)
    (hx₁ : S₁'.V = (x₁ : Matrix (Fin r[U]) (Fin r[U]) ℂ) * S₁.V)
    (hx₂ : S₂'.V = (x₂ : Matrix (Fin ℓ[U]) (Fin ℓ[U]) ℂ) * S₂.V) :
    SourceFactors.sourceV U (sourceFactorsOf S₁' S₂' ρ hρ) =
      SourceFactors.sourceV U (sourceFactorsOf S₁ S₂ ρ hρ) *
        (star (x₁ : Matrix _ _ ℂ) ⊗ₖ star (x₂ : Matrix _ _ ℂ)) := by
  ext ⟨j₁, j₂⟩ ⟨q, l⟩
  simp only [SourceFactors.sourceV_apply, sourceFactorsOf_X₁, sourceFactorsOf_X₂,
    sourceX₁Of_eq_of_V_eq ρ hρ hx₁, sourceX₂Of_eq_of_V_eq hx₂, Matrix.mul_apply,
    Fintype.sum_prod_type, Matrix.kroneckerMap_apply, Finset.sum_mul, Finset.mul_sum,
    Matrix.star_eq_conjTranspose]
  conv_lhs =>
    rw [Finset.sum_comm]
    enter [2, l']
    rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦
    Finset.sum_congr rfl fun _ _ ↦ by ring

/-- Change of decomposition for both gates with the named unitaries
$x_1=C_1'C_1^\dagger$ and $x_2=C_2'C_2^\dagger$ (ME.tex, Theorem 1.3). -/
theorem sourceU_sourceV_sourceFactorsOf_relatingUnitary
    (S₁ S₁' : SourceCutSVD (sourceCutM₁ U) r[U]) (S₂ S₂' : SourceCutSVD (sourceCutM₂ U) ℓ[U])
    (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef) :
    SourceFactors.sourceU U (sourceFactorsOf S₁' S₂' ρ hρ) =
        ((S₂.relatingUnitary S₂' : Matrix _ _ ℂ) ⊗ₖ (S₁.relatingUnitary S₁' : Matrix _ _ ℂ)) *
          SourceFactors.sourceU U (sourceFactorsOf S₁ S₂ ρ hρ) ∧
      SourceFactors.sourceV U (sourceFactorsOf S₁' S₂' ρ hρ) =
        SourceFactors.sourceV U (sourceFactorsOf S₁ S₂ ρ hρ) *
          (star (S₁.relatingUnitary S₁' : Matrix _ _ ℂ) ⊗ₖ
            star (S₂.relatingUnitary S₂' : Matrix _ _ ℂ)) :=
  ⟨sourceU_sourceFactorsOf_eq_of_V_eq ρ hρ (S₁.relatingUnitary_mul_V S₁').symm
      (S₂.relatingUnitary_mul_V S₂').symm,
    sourceV_sourceFactorsOf_eq_of_V_eq ρ hρ (S₁.relatingUnitary_mul_V S₁').symm
      (S₂.relatingUnitary_mul_V S₂').symm⟩

/-- Change of decomposition for the gates: two choices of compact decompositions give gates
related by unitaries, $u'=(x_2\otimes x_1)u$ and $v'=v(x_1^\dagger\otimes x_2^\dagger)$
(ME.tex, Theorem 1.3; arXiv:1703.09188, `eq:sf-svd` and `uuvv`, lines 479--543). -/
theorem sourceU_sourceFactorsOf_eq (S₁ S₁' : SourceCutSVD (sourceCutM₁ U) r[U])
    (S₂ S₂' : SourceCutSVD (sourceCutM₂ U) ℓ[U]) (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef) :
    ∃ (x₁ : Matrix.unitaryGroup (Fin r[U]) ℂ) (x₂ : Matrix.unitaryGroup (Fin ℓ[U]) ℂ),
      SourceFactors.sourceU U (sourceFactorsOf S₁' S₂' ρ hρ) =
        ((x₂ : Matrix _ _ ℂ) ⊗ₖ (x₁ : Matrix _ _ ℂ)) *
          SourceFactors.sourceU U (sourceFactorsOf S₁ S₂ ρ hρ) ∧
      SourceFactors.sourceV U (sourceFactorsOf S₁' S₂' ρ hρ) =
        SourceFactors.sourceV U (sourceFactorsOf S₁ S₂ ρ hρ) *
          (star (x₁ : Matrix _ _ ℂ) ⊗ₖ star (x₂ : Matrix _ _ ℂ)) :=
  ⟨_, _, sourceU_sourceV_sourceFactorsOf_relatingUnitary S₁ S₁' S₂ S₂' ρ hρ⟩

end Change

end MPOTensor
