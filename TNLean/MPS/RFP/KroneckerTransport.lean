/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.RFP.CommutingBridge

/-!
# Three-site transport of commuting pair matrices

This file contains the finite-dimensional matrix calculation used in the
Appendix B argument to transport two commuting adjacent pair operators through
a tensor cube of an isometry.  The calculation does not depend on the
particular virtual bond operator, but its exported names remain Appendix B
specific because they support that argument.
-/

open scoped Matrix Kronecker

namespace MPSTensor

/-- A pair matrix on the first two factors, with a possibly different
spectator type. -/
noncomputable def appendixBLeftPairMatrixAux
    {a b s : Type*} [Fintype s] [DecidableEq s]
    (B : Matrix (a × a) (b × b) ℂ) :
    Matrix (a × (a × s)) (b × (b × s)) ℂ :=
  Matrix.reindex (Equiv.prodAssoc a a s) (Equiv.prodAssoc b b s)
    (B ⊗ₖ (1 : Matrix s s ℂ))

/-- A pair matrix on the final two factors, with a possibly different
spectator type. -/
noncomputable def appendixBRightPairMatrixAux
    {s a b : Type*} [Fintype s] [DecidableEq s]
    (B : Matrix (a × a) (b × b) ℂ) :
    Matrix (s × (a × a)) (s × (b × b)) ℂ :=
  (1 : Matrix s s ℂ) ⊗ₖ B

/-- A square pair matrix on the first two factors. -/
noncomputable abbrev appendixBLeftPairMatrix
    {a : Type*} [Fintype a] [DecidableEq a]
    (B : Matrix (a × a) (a × a) ℂ) :=
  appendixBLeftPairMatrixAux (s := a) B

/-- A square pair matrix on the final two factors. -/
noncomputable abbrev appendixBRightPairMatrix
    {a : Type*} [Fintype a] [DecidableEq a]
    (B : Matrix (a × a) (a × a) ℂ) :=
  appendixBRightPairMatrixAux (s := a) B

/-- A right-associated Kronecker product of three matrices. -/
private noncomputable def tripleMatrix
    {a b c d e f : Type*}
    (A : Matrix a b ℂ) (B : Matrix c d ℂ) (C : Matrix e f ℂ) :
    Matrix (a × (c × e)) (b × (d × f)) ℂ :=
  A ⊗ₖ (B ⊗ₖ C)

/-- Reindexing carries a product of three matrices to the product of their
three compatible reindexings. -/
theorem reindex_three_mul
    {m n o p m' n' o' p' : Type*}
    [Fintype n] [Fintype n'] [Fintype o] [Fintype o']
    (em : m ≃ m') (en : n ≃ n') (eo : o ≃ o') (ep : p ≃ p')
    (M : Matrix m n ℂ) (N : Matrix n o ℂ) (P : Matrix o p ℂ) :
    Matrix.reindex em ep ((M * N) * P) =
      (Matrix.reindex em en M * Matrix.reindex en eo N) *
        Matrix.reindex eo ep P := by
  calc
    _ = Matrix.reindex em eo (M * N) * Matrix.reindex eo ep P := by
      simpa only [Matrix.coe_reindexLinearEquiv] using
        (Matrix.reindexLinearEquiv_mul ℂ ℂ em eo ep (M * N) P).symm
    _ = _ := by
      simpa only [Matrix.coe_reindexLinearEquiv] using congrArg
        (fun Q ↦ Q * Matrix.reindex eo ep P)
        (Matrix.reindexLinearEquiv_mul ℂ ℂ em en eo M N).symm

/-- Componentwise multiplication of right-associated triple matrices. -/
private theorem tripleMatrix_mul
    {a b c d e f g h i : Type*}
    [Fintype b] [Fintype e] [Fintype h]
    (A : Matrix a b ℂ) (A' : Matrix b c ℂ)
    (B : Matrix d e ℂ) (B' : Matrix e f ℂ)
    (C : Matrix g h ℂ) (C' : Matrix h i ℂ) :
    tripleMatrix A B C * tripleMatrix A' B' C' =
      tripleMatrix (A * A') (B * B') (C * C') := by
  simp only [tripleMatrix]
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]

/-- Transporting a pair matrix on the first two factors through a tensor cube
gives a three-factor matrix sandwich. -/
private theorem leftPairMatrix_transport
    {p v : Type*} [Fintype p] [DecidableEq p]
    [Fintype v]
    (U : Matrix p v ℂ) (B : Matrix (v × v) (v × v) ℂ) :
    appendixBLeftPairMatrix (((U ⊗ₖ U) * B) * (Uᴴ ⊗ₖ Uᴴ)) =
      ((tripleMatrix U U (1 : Matrix p p ℂ) *
        appendixBLeftPairMatrixAux (s := p) B) *
        tripleMatrix Uᴴ Uᴴ (1 : Matrix p p ℂ)) := by
  have h₁ :
      ((((U ⊗ₖ U) * B) * (Uᴴ ⊗ₖ Uᴴ)) ⊗ₖ (1 : Matrix p p ℂ)) =
        (((U ⊗ₖ U) * B) ⊗ₖ (1 : Matrix p p ℂ)) *
          ((Uᴴ ⊗ₖ Uᴴ) ⊗ₖ (1 : Matrix p p ℂ)) := by
    simpa only [mul_one] using
      Matrix.mul_kronecker_mul ((U ⊗ₖ U) * B) (Uᴴ ⊗ₖ Uᴴ)
        (1 : Matrix p p ℂ) (1 : Matrix p p ℂ)
  have h₂ :
      (((U ⊗ₖ U) * B) ⊗ₖ (1 : Matrix p p ℂ)) =
        ((U ⊗ₖ U) ⊗ₖ (1 : Matrix p p ℂ)) *
          (B ⊗ₖ (1 : Matrix p p ℂ)) := by
    simpa only [mul_one] using Matrix.mul_kronecker_mul (U ⊗ₖ U) B
      (1 : Matrix p p ℂ) (1 : Matrix p p ℂ)
  unfold appendixBLeftPairMatrix appendixBLeftPairMatrixAux
  rw [h₁, h₂]
  rw [reindex_three_mul (Equiv.prodAssoc p p p) (Equiv.prodAssoc v v p)
    (Equiv.prodAssoc v v p) (Equiv.prodAssoc p p p)]
  rw [Matrix.kronecker_assoc, Matrix.kronecker_assoc]
  rfl

/-- Transporting a pair matrix on the final two factors through a tensor cube
gives the analogous three-factor matrix sandwich. -/
private theorem rightPairMatrix_transport
    {p v : Type*} [Fintype p] [DecidableEq p]
    [Fintype v]
    (U : Matrix p v ℂ) (B : Matrix (v × v) (v × v) ℂ) :
    appendixBRightPairMatrix (((U ⊗ₖ U) * B) * (Uᴴ ⊗ₖ Uᴴ)) =
      ((tripleMatrix (1 : Matrix p p ℂ) U U *
        appendixBRightPairMatrixAux (s := p) B) *
        tripleMatrix (1 : Matrix p p ℂ) Uᴴ Uᴴ) := by
  have h₁ :
      (1 : Matrix p p ℂ) ⊗ₖ (((U ⊗ₖ U) * B) * (Uᴴ ⊗ₖ Uᴴ)) =
        ((1 : Matrix p p ℂ) ⊗ₖ ((U ⊗ₖ U) * B)) *
          ((1 : Matrix p p ℂ) ⊗ₖ (Uᴴ ⊗ₖ Uᴴ)) := by
    simpa only [one_mul] using Matrix.mul_kronecker_mul (1 : Matrix p p ℂ)
      (1 : Matrix p p ℂ)
      ((U ⊗ₖ U) * B) (Uᴴ ⊗ₖ Uᴴ)
  have h₂ :
      (1 : Matrix p p ℂ) ⊗ₖ ((U ⊗ₖ U) * B) =
        ((1 : Matrix p p ℂ) ⊗ₖ (U ⊗ₖ U)) *
          ((1 : Matrix p p ℂ) ⊗ₖ B) := by
    simpa only [one_mul] using Matrix.mul_kronecker_mul (1 : Matrix p p ℂ)
      (1 : Matrix p p ℂ)
      (U ⊗ₖ U) B
  unfold appendixBRightPairMatrix appendixBRightPairMatrixAux tripleMatrix
  rw [h₁, h₂]

/-- A map on the spectator factor commutes naturally past a pair matrix on the
first two factors. -/
private theorem leftPairMatrixAux_naturality
    {a s t : Type*} [Fintype a] [DecidableEq a]
    [Fintype s] [DecidableEq s] [Fintype t] [DecidableEq t]
    (B : Matrix (a × a) (a × a) ℂ) (V : Matrix s t ℂ) :
    appendixBLeftPairMatrixAux (s := s) B *
        tripleMatrix (1 : Matrix a a ℂ) (1 : Matrix a a ℂ) V =
      tripleMatrix (1 : Matrix a a ℂ) (1 : Matrix a a ℂ) V *
        appendixBLeftPairMatrixAux (s := t) B := by
  let es := Equiv.prodAssoc a a s
  let et := Equiv.prodAssoc a a t
  have hAssoc : tripleMatrix (1 : Matrix a a ℂ) (1 : Matrix a a ℂ) V =
      Matrix.reindex es et ((1 : Matrix (a × a) (a × a) ℂ) ⊗ₖ V) := by
    unfold tripleMatrix
    rw [← Matrix.kronecker_assoc (1 : Matrix a a ℂ) (1 : Matrix a a ℂ) V]
    simp only [Matrix.one_kronecker_one, es, et]
  rw [hAssoc]
  unfold appendixBLeftPairMatrixAux
  calc
    _ = Matrix.reindex es et
        ((B ⊗ₖ (1 : Matrix s s ℂ)) *
          ((1 : Matrix (a × a) (a × a) ℂ) ⊗ₖ V)) := by
      simpa only [es, et, Matrix.coe_reindexLinearEquiv] using
        Matrix.reindexLinearEquiv_mul ℂ ℂ es es et
          (B ⊗ₖ (1 : Matrix s s ℂ))
          ((1 : Matrix (a × a) (a × a) ℂ) ⊗ₖ V)
    _ = Matrix.reindex es et (B ⊗ₖ V) := by
      congr 1
      rw [← Matrix.mul_kronecker_mul]
      simp only [Matrix.mul_one, Matrix.one_mul]
    _ = Matrix.reindex es et
        (((1 : Matrix (a × a) (a × a) ℂ) ⊗ₖ V) *
          (B ⊗ₖ (1 : Matrix t t ℂ))) := by
      congr 1
      rw [← Matrix.mul_kronecker_mul]
      simp only [Matrix.mul_one, Matrix.one_mul]
    _ = _ := by
      simpa only [es, et, Matrix.coe_reindexLinearEquiv] using
        (Matrix.reindexLinearEquiv_mul ℂ ℂ es et et
          ((1 : Matrix (a × a) (a × a) ℂ) ⊗ₖ V)
          (B ⊗ₖ (1 : Matrix t t ℂ))).symm

/-- A map on the spectator factor commutes naturally past a pair matrix on the
final two factors. -/
private theorem rightPairMatrixAux_naturality
    {a s t : Type*} [Fintype a] [DecidableEq a]
    [Fintype s] [DecidableEq s] [Fintype t] [DecidableEq t]
    (B : Matrix (a × a) (a × a) ℂ) (V : Matrix s t ℂ) :
    appendixBRightPairMatrixAux (s := s) B *
        tripleMatrix V (1 : Matrix a a ℂ) (1 : Matrix a a ℂ) =
      tripleMatrix V (1 : Matrix a a ℂ) (1 : Matrix a a ℂ) *
        appendixBRightPairMatrixAux (s := t) B := by
  unfold appendixBRightPairMatrixAux tripleMatrix
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
  simp only [Matrix.one_kronecker_one, Matrix.one_mul, Matrix.mul_one]

/-- The product with the first transported pair on the left is the tensor-cube
sandwich of the corresponding virtual product. -/
private theorem transportedPairProduct_left
    {p v : Type*} [Fintype p] [DecidableEq p]
    [Fintype v] [DecidableEq v]
    (U : Matrix p v ℂ) (B : Matrix (v × v) (v × v) ℂ)
    (hU : Uᴴ * U = 1) :
    appendixBLeftPairMatrix (((U ⊗ₖ U) * B) * (Uᴴ ⊗ₖ Uᴴ)) *
        appendixBRightPairMatrix (((U ⊗ₖ U) * B) * (Uᴴ ⊗ₖ Uᴴ)) =
      tripleMatrix U U U *
          (appendixBLeftPairMatrix B * appendixBRightPairMatrix B) *
        tripleMatrix Uᴴ Uᴴ Uᴴ := by
  rw [leftPairMatrix_transport, rightPairMatrix_transport]
  let LA := tripleMatrix U U (1 : Matrix p p ℂ)
  let LHA := tripleMatrix Uᴴ Uᴴ (1 : Matrix p p ℂ)
  let RA := tripleMatrix (1 : Matrix p p ℂ) U U
  let RHA := tripleMatrix (1 : Matrix p p ℂ) Uᴴ Uᴴ
  let UL := tripleMatrix (1 : Matrix v v ℂ) (1 : Matrix v v ℂ) U
  let HL := tripleMatrix Uᴴ (1 : Matrix v v ℂ) (1 : Matrix v v ℂ)
  let LBp := appendixBLeftPairMatrixAux (s := p) B
  let RBp := appendixBRightPairMatrixAux (s := p) B
  let LBv := appendixBLeftPairMatrix B
  let RBv := appendixBRightPairMatrix B
  have hCross : LHA * RA = UL * HL := by
    dsimp [LHA, RA, UL, HL]
    rw [tripleMatrix_mul, tripleMatrix_mul]
    simp only [hU, Matrix.one_mul, Matrix.mul_one]
  have hOuterLeft : LA * UL = tripleMatrix U U U := by
    dsimp [LA, UL]
    rw [tripleMatrix_mul]
    simp only [Matrix.mul_one, Matrix.one_mul]
  have hOuterRight : HL * RHA = tripleMatrix Uᴴ Uᴴ Uᴴ := by
    dsimp [HL, RHA]
    rw [tripleMatrix_mul]
    simp only [Matrix.mul_one, Matrix.one_mul]
  change ((LA * LBp) * LHA) * ((RA * RBp) * RHA) =
    tripleMatrix U U U * (LBv * RBv) * tripleMatrix Uᴴ Uᴴ Uᴴ
  calc
    _ = LA * LBp * (LHA * RA) * RBp * RHA := by
      simp only [Matrix.mul_assoc]
    _ = LA * LBp * (UL * HL) * RBp * RHA := by rw [hCross]
    _ = LA * (LBp * UL) * (HL * RBp) * RHA := by
      simp only [Matrix.mul_assoc]
    _ = LA * (UL * LBv) * (RBv * HL) * RHA := by
      rw [leftPairMatrixAux_naturality (s := p) (t := v) B U,
        ← rightPairMatrixAux_naturality (s := v) (t := p) B Uᴴ]
    _ = (LA * UL) * (LBv * RBv) * (HL * RHA) := by
      simp only [Matrix.mul_assoc]
    _ = _ := by rw [hOuterLeft, hOuterRight]

/-- The reverse transported product is the tensor-cube sandwich of the reverse
virtual product. -/
private theorem transportedPairProduct_right
    {p v : Type*} [Fintype p] [DecidableEq p]
    [Fintype v] [DecidableEq v]
    (U : Matrix p v ℂ) (B : Matrix (v × v) (v × v) ℂ)
    (hU : Uᴴ * U = 1) :
    appendixBRightPairMatrix (((U ⊗ₖ U) * B) * (Uᴴ ⊗ₖ Uᴴ)) *
        appendixBLeftPairMatrix (((U ⊗ₖ U) * B) * (Uᴴ ⊗ₖ Uᴴ)) =
      tripleMatrix U U U *
          (appendixBRightPairMatrix B * appendixBLeftPairMatrix B) *
        tripleMatrix Uᴴ Uᴴ Uᴴ := by
  rw [leftPairMatrix_transport, rightPairMatrix_transport]
  let LA := tripleMatrix U U (1 : Matrix p p ℂ)
  let LHA := tripleMatrix Uᴴ Uᴴ (1 : Matrix p p ℂ)
  let RA := tripleMatrix (1 : Matrix p p ℂ) U U
  let RHA := tripleMatrix (1 : Matrix p p ℂ) Uᴴ Uᴴ
  let UF := tripleMatrix U (1 : Matrix v v ℂ) (1 : Matrix v v ℂ)
  let HF := tripleMatrix (1 : Matrix v v ℂ) (1 : Matrix v v ℂ) Uᴴ
  let LBp := appendixBLeftPairMatrixAux (s := p) B
  let RBp := appendixBRightPairMatrixAux (s := p) B
  let LBv := appendixBLeftPairMatrix B
  let RBv := appendixBRightPairMatrix B
  have hCross : RHA * LA = UF * HF := by
    dsimp [RHA, LA, UF, HF]
    rw [tripleMatrix_mul, tripleMatrix_mul]
    simp only [hU, Matrix.one_mul, Matrix.mul_one]
  have hOuterLeft : RA * UF = tripleMatrix U U U := by
    dsimp [RA, UF]
    rw [tripleMatrix_mul]
    simp only [Matrix.mul_one, Matrix.one_mul]
  have hOuterRight : HF * LHA = tripleMatrix Uᴴ Uᴴ Uᴴ := by
    dsimp [HF, LHA]
    rw [tripleMatrix_mul]
    simp only [Matrix.mul_one, Matrix.one_mul]
  change ((RA * RBp) * RHA) * ((LA * LBp) * LHA) =
    tripleMatrix U U U * (RBv * LBv) * tripleMatrix Uᴴ Uᴴ Uᴴ
  calc
    _ = RA * RBp * (RHA * LA) * LBp * LHA := by
      simp only [Matrix.mul_assoc]
    _ = RA * RBp * (UF * HF) * LBp * LHA := by rw [hCross]
    _ = RA * (RBp * UF) * (HF * LBp) * LHA := by
      simp only [Matrix.mul_assoc]
    _ = RA * (UF * RBv) * (LBv * HF) * LHA := by
      rw [rightPairMatrixAux_naturality (s := p) (t := v) B U,
        ← leftPairMatrixAux_naturality (s := v) (t := p) B Uᴴ]
    _ = (RA * UF) * (RBv * LBv) * (HF * LHA) := by
      simp only [Matrix.mul_assoc]
    _ = _ := by rw [hOuterLeft, hOuterRight]

/-- An isometric one-site matrix transports commuting adjacent pair matrices
to commuting adjacent pair matrices on the physical space. -/
theorem appendixB_transportedPairMatrices_comm
    {p v : Type*} [Fintype p] [DecidableEq p]
    [Fintype v] [DecidableEq v]
    (U : Matrix p v ℂ) (B : Matrix (v × v) (v × v) ℂ)
    (hU : Uᴴ * U = 1)
    (hB : appendixBLeftPairMatrix B * appendixBRightPairMatrix B =
      appendixBRightPairMatrix B * appendixBLeftPairMatrix B) :
    appendixBLeftPairMatrix (((U ⊗ₖ U) * B) * (Uᴴ ⊗ₖ Uᴴ)) *
        appendixBRightPairMatrix (((U ⊗ₖ U) * B) * (Uᴴ ⊗ₖ Uᴴ)) =
      appendixBRightPairMatrix (((U ⊗ₖ U) * B) * (Uᴴ ⊗ₖ Uᴴ)) *
        appendixBLeftPairMatrix (((U ⊗ₖ U) * B) * (Uᴴ ⊗ₖ Uᴴ)) := by
  rw [transportedPairProduct_left U B hU, transportedPairProduct_right U B hU, hB]

/-- Orthogonal one-site isometries make a left transported pair matrix from
one sector annihilate a right transported pair matrix from the other sector.

This is the cross-sector part of the common-isometry calculation: the shared
one-site factor contains `Uᴴ * V`, hence vanishes.

Source: arXiv:1606.00608, equation `eq:III_isometry`, lines 549--554. -/
theorem appendixB_leftTransportedPairMatrix_mul_right_eq_zero_of_orthogonal
    {p v w : Type*} [Fintype p] [DecidableEq p]
    [Fintype v] [Fintype w]
    (U : Matrix p v ℂ) (V : Matrix p w ℂ)
    (B : Matrix (v × v) (v × v) ℂ) (C : Matrix (w × w) (w × w) ℂ)
    (hUV : Uᴴ * V = 0) :
    appendixBLeftPairMatrix (((U ⊗ₖ U) * B) * (Uᴴ ⊗ₖ Uᴴ)) *
        appendixBRightPairMatrix (((V ⊗ₖ V) * C) * (Vᴴ ⊗ₖ Vᴴ)) = 0 := by
  rw [leftPairMatrix_transport, rightPairMatrix_transport]
  let LA := tripleMatrix U U (1 : Matrix p p ℂ)
  let LHA := tripleMatrix Uᴴ Uᴴ (1 : Matrix p p ℂ)
  let RA := tripleMatrix (1 : Matrix p p ℂ) V V
  let RHA := tripleMatrix (1 : Matrix p p ℂ) Vᴴ Vᴴ
  let LB := appendixBLeftPairMatrixAux (s := p) B
  let RC := appendixBRightPairMatrixAux (s := p) C
  have hCross : LHA * RA = 0 := by
    dsimp [LHA, RA]
    rw [tripleMatrix_mul]
    simp only [Matrix.mul_one, Matrix.one_mul, hUV]
    simp [tripleMatrix]
  change ((LA * LB) * LHA) * ((RA * RC) * RHA) = 0
  calc
    _ = LA * LB * (LHA * RA) * RC * RHA := by
      simp only [Matrix.mul_assoc]
    _ = 0 := by rw [hCross]; simp

/-- Orthogonal one-site isometries also make the reverse overlapping product
vanish.

Source: arXiv:1606.00608, equation `eq:III_isometry`, lines 549--554. -/
theorem appendixB_rightTransportedPairMatrix_mul_left_eq_zero_of_orthogonal
    {p v w : Type*} [Fintype p] [DecidableEq p]
    [Fintype v] [Fintype w]
    (U : Matrix p v ℂ) (V : Matrix p w ℂ)
    (B : Matrix (v × v) (v × v) ℂ) (C : Matrix (w × w) (w × w) ℂ)
    (hUV : Uᴴ * V = 0) :
    appendixBRightPairMatrix (((U ⊗ₖ U) * B) * (Uᴴ ⊗ₖ Uᴴ)) *
        appendixBLeftPairMatrix (((V ⊗ₖ V) * C) * (Vᴴ ⊗ₖ Vᴴ)) = 0 := by
  rw [rightPairMatrix_transport, leftPairMatrix_transport]
  let RA := tripleMatrix (1 : Matrix p p ℂ) U U
  let RHA := tripleMatrix (1 : Matrix p p ℂ) Uᴴ Uᴴ
  let LA := tripleMatrix V V (1 : Matrix p p ℂ)
  let LHA := tripleMatrix Vᴴ Vᴴ (1 : Matrix p p ℂ)
  let RB := appendixBRightPairMatrixAux (s := p) B
  let LC := appendixBLeftPairMatrixAux (s := p) C
  have hCross : RHA * LA = 0 := by
    dsimp [RHA, LA]
    rw [tripleMatrix_mul]
    simp only [Matrix.one_mul, Matrix.mul_one, hUV]
    simp [tripleMatrix]
  change ((RA * RB) * RHA) * ((LA * LC) * LHA) = 0
  calc
    _ = RA * RB * (RHA * LA) * LC * LHA := by
      simp only [Matrix.mul_assoc]
    _ = 0 := by rw [hCross]; simp

end MPSTensor
