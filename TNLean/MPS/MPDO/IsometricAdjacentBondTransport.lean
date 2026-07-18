/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.PhysicalSupportBondTransport

/-!
# Isometric transport of adjacent two-site bonds

If a one-site isometry includes a physical subspace into an ambient physical
space, conjugation of a product of two adjacent restricted bonds is exactly
the product of their two ambient lifts.  The shared physical index contracts
through the isometry identity.  No coisometry is used.

The calculation takes place on a three-site chain.  Thus it has no empty-chain
case and is the local input for transporting neighboring commutativity through
an orthogonal physical support.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Appendix C.2, equations `PjKiPj` and `generateMPDO`, lines 1733--1770
-/

open scoped Matrix BigOperators ComplexOrder Kronecker

open MPOTensor

namespace MPOTensor

variable {d e : ℕ}

open MPOTensor.PhysicalSectorFactorization

private theorem singleKrausMap_kronecker
    {a b c f : Type*} [Fintype a] [Fintype b] [Fintype c] [Fintype f]
    (A : Matrix a b ℂ) (C : Matrix c f ℂ)
    (X : Matrix b b ℂ) (Y : Matrix f f ℂ) :
    singleKrausMap (A ⊗ₖ C) (X ⊗ₖ Y) =
      singleKrausMap A X ⊗ₖ singleKrausMap C Y := by
  simp only [singleKrausMap_apply, Matrix.conjTranspose_kronecker]
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]

private theorem reindex_kronecker_assoc
    (V : Matrix (Fin d) (Fin e) ℂ) :
    Matrix.reindex (Equiv.prodAssoc (Fin d) (Fin d) (Fin d)).symm
        (Equiv.prodAssoc (Fin e) (Fin e) (Fin e)).symm
        (V ⊗ₖ (V ⊗ₖ V)) = (V ⊗ₖ V) ⊗ₖ V := by
  ext ⟨⟨i, j⟩, k⟩ ⟨⟨a, b⟩, c⟩
  simp [Matrix.reindex_apply, Matrix.kroneckerMap_apply]
  ring

private theorem reindex_leftPairMatrix
    (B : Matrix (Fin e × Fin e) (Fin e × Fin e) ℂ) :
    Matrix.reindex (Equiv.prodAssoc (Fin e) (Fin e) (Fin e)).symm
        (Equiv.prodAssoc (Fin e) (Fin e) (Fin e)).symm
        (leftPairMatrix B) =
      B ⊗ₖ (1 : Matrix (Fin e) (Fin e) ℂ) := by
  ext ⟨⟨i, j⟩, k⟩ ⟨⟨a, b⟩, c⟩
  simp [leftPairMatrix, Matrix.reindex_apply,
    Matrix.kroneckerMap_apply]

private theorem lift_leftPairMatrix
    (V : Matrix (Fin d) (Fin e) ℂ)
    (B : Matrix (Fin e × Fin e) (Fin e × Fin e) ℂ) :
    singleKrausMap (V ⊗ₖ (V ⊗ₖ V)) (leftPairMatrix B) =
      Matrix.reindex (Equiv.prodAssoc (Fin d) (Fin d) (Fin d))
        (Equiv.prodAssoc (Fin d) (Fin d) (Fin d))
        (singleKrausMap (V ⊗ₖ V) B ⊗ₖ singleKrausMap V 1) := by
  apply (Matrix.reindex
    (Equiv.prodAssoc (Fin d) (Fin d) (Fin d)).symm
    (Equiv.prodAssoc (Fin d) (Fin d) (Fin d)).symm).injective
  rw [Matrix.reindex_singleKrausMap
      (Equiv.prodAssoc (Fin e) (Fin e) (Fin e)).symm
      (Equiv.prodAssoc (Fin d) (Fin d) (Fin d)).symm,
    reindex_kronecker_assoc, reindex_leftPairMatrix,
    singleKrausMap_kronecker]
  ext
  simp [Matrix.reindex_apply]

private theorem singleKrausMap_mul
    {a b : Type*} [Fintype a] [Fintype b] [DecidableEq b]
    (V : Matrix a b ℂ) (hV : Vᴴ * V = 1)
    (X Y : Matrix b b ℂ) :
    singleKrausMap V (X * Y) =
      singleKrausMap V X * singleKrausMap V Y := by
  simp only [singleKrausMap_apply, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc Vᴴ V, hV]
  simp

private theorem kronecker_isometry
    {a b c f : Type*} [Fintype a] [Fintype c]
    [DecidableEq b] [DecidableEq f]
    (V : Matrix a b ℂ) (W : Matrix c f ℂ)
    (hV : Vᴴ * V = 1) (hW : Wᴴ * W = 1) :
    (V ⊗ₖ W)ᴴ * (V ⊗ₖ W) = 1 := by
  rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
    hV, hW]
  exact Matrix.one_kronecker_one

private theorem lift_pair_mul_firstProjection
    (V : Matrix (Fin d) (Fin e) ℂ) (hV : Vᴴ * V = 1)
    (B : Matrix (Fin e × Fin e) (Fin e × Fin e) ℂ) :
    singleKrausMap (V ⊗ₖ V) B *
        (singleKrausMap V 1 ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ)) =
      singleKrausMap (V ⊗ₖ V) B := by
  simp only [singleKrausMap_apply, Matrix.conjTranspose_kronecker,
    Matrix.mul_assoc]
  rw [← Matrix.mul_kronecker_mul]
  simp only [Matrix.mul_one]
  rw [← Matrix.mul_assoc Vᴴ V, hV]
  simp

private theorem secondProjection_mul_lift_pair
    (V : Matrix (Fin d) (Fin e) ℂ) (hV : Vᴴ * V = 1)
    (B : Matrix (Fin e × Fin e) (Fin e × Fin e) ℂ) :
    ((1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ singleKrausMap V 1) *
        singleKrausMap (V ⊗ₖ V) B =
      singleKrausMap (V ⊗ₖ V) B := by
  have hPV : (V * Vᴴ) * V = V := by
    simp only [Matrix.mul_assoc]
    rw [hV]
    simp
  have hQW :
      ((1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ (V * Vᴴ)) *
          (V ⊗ₖ V) = V ⊗ₖ V := by
    rw [← Matrix.mul_kronecker_mul, Matrix.one_mul, hPV]
  have hP : singleKrausMap V 1 = V * Vᴴ := by
    simp [singleKrausMap_apply]
  rw [hP]
  simp only [singleKrausMap_apply]
  calc
    _ = (((1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ
          (V * Vᴴ)) * (V ⊗ₖ V)) * B *
            (V ⊗ₖ V)ᴴ := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hQW]

private theorem lift_rightPairMatrix
    (V : Matrix (Fin d) (Fin e) ℂ)
    (B : Matrix (Fin e × Fin e) (Fin e × Fin e) ℂ) :
    singleKrausMap (V ⊗ₖ (V ⊗ₖ V)) (rightPairMatrix B) =
      singleKrausMap V 1 ⊗ₖ singleKrausMap (V ⊗ₖ V) B := by
  rw [rightPairMatrix, singleKrausMap_kronecker]

private theorem leftPair_mul_lastProjection
    (A : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    (P : Matrix (Fin d) (Fin d) ℂ) :
    leftPairMatrix A *
        ((1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ
          ((1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ P)) =
      Matrix.reindex (Equiv.prodAssoc (Fin d) (Fin d) (Fin d))
        (Equiv.prodAssoc (Fin d) (Fin d) (Fin d))
        (A ⊗ₖ P) := by
  let e := Equiv.prodAssoc (Fin d) (Fin d) (Fin d)
  apply (Matrix.reindex e.symm e.symm).injective
  change Matrix.reindexLinearEquiv ℂ ℂ e.symm e.symm
      (leftPairMatrix A *
        ((1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ
          ((1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ P))) = _
  rw [← Matrix.reindexLinearEquiv_mul ℂ ℂ e.symm e.symm e.symm]
  simp only [Matrix.coe_reindexLinearEquiv]
  rw [reindex_leftPairMatrix]
  have hQ :
      Matrix.reindex e.symm e.symm
          ((1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ
            ((1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ P)) =
        ((1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ
          (1 : Matrix (Fin d) (Fin d) ℂ)) ⊗ₖ P := by
    ext ⟨⟨i, j⟩, k⟩ ⟨⟨i', j'⟩, k'⟩
    simp [e, Matrix.reindex_apply, Matrix.kroneckerMap_apply,
      Matrix.one_apply]
    by_cases hi : i = i' <;> by_cases hj : j = j' <;> simp_all
  rw [hQ, ← Matrix.mul_kronecker_mul]
  ext
  simp [e, Matrix.reindex_apply, Matrix.kroneckerMap_apply]

private theorem firstProjection_mul_rightPair
    (P : Matrix (Fin d) (Fin d) ℂ)
    (A : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    (P ⊗ₖ ((1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ
        (1 : Matrix (Fin d) (Fin d) ℂ))) * rightPairMatrix A =
      P ⊗ₖ A := by
  rw [rightPairMatrix, ← Matrix.mul_kronecker_mul,
    Matrix.mul_one, Matrix.one_kronecker_one, Matrix.one_mul]

private theorem first_lastProjection_comm
    (P : Matrix (Fin d) (Fin d) ℂ) :
    ((1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ
        ((1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ P)) *
        (P ⊗ₖ ((1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ
          (1 : Matrix (Fin d) (Fin d) ℂ))) =
      (P ⊗ₖ ((1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ
          (1 : Matrix (Fin d) (Fin d) ℂ))) *
        ((1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ
          ((1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ P)) := by
  repeat' rw [← Matrix.mul_kronecker_mul]
  simp

private theorem leftPair_mul_firstProjection
    (A : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    (P : Matrix (Fin d) (Fin d) ℂ)
    (hA : A * (P ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ)) = A) :
    leftPairMatrix A *
        (P ⊗ₖ ((1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ
          (1 : Matrix (Fin d) (Fin d) ℂ))) =
      leftPairMatrix A := by
  apply (Matrix.reindex
    (Equiv.prodAssoc (Fin d) (Fin d) (Fin d)).symm
    (Equiv.prodAssoc (Fin d) (Fin d) (Fin d)).symm).injective
  change Matrix.reindexLinearEquiv ℂ ℂ
      (Equiv.prodAssoc (Fin d) (Fin d) (Fin d)).symm
      (Equiv.prodAssoc (Fin d) (Fin d) (Fin d)).symm
      (leftPairMatrix A *
        (P ⊗ₖ ((1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ
          (1 : Matrix (Fin d) (Fin d) ℂ)))) = _
  rw [← Matrix.reindexLinearEquiv_mul ℂ ℂ
      (Equiv.prodAssoc (Fin d) (Fin d) (Fin d)).symm
      (Equiv.prodAssoc (Fin d) (Fin d) (Fin d)).symm
      (Equiv.prodAssoc (Fin d) (Fin d) (Fin d)).symm]
  simp only [Matrix.coe_reindexLinearEquiv]
  rw [reindex_leftPairMatrix]
  have hQ :
      Matrix.reindex (Equiv.prodAssoc (Fin d) (Fin d) (Fin d)).symm
          (Equiv.prodAssoc (Fin d) (Fin d) (Fin d)).symm
          (P ⊗ₖ ((1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ
            (1 : Matrix (Fin d) (Fin d) ℂ))) =
        (P ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ)) ⊗ₖ
          (1 : Matrix (Fin d) (Fin d) ℂ) := by
    ext
    simp [Matrix.reindex_apply, Matrix.kroneckerMap_apply,
      Matrix.one_apply]
    split_ifs <;> simp_all
  rw [hQ, ← Matrix.mul_kronecker_mul, hA, Matrix.one_mul]

private theorem lastProjection_mul_rightPair
    (P : Matrix (Fin d) (Fin d) ℂ)
    (A : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    (hA : ((1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ P) * A = A) :
    ((1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ
        ((1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ P)) *
        rightPairMatrix A = rightPairMatrix A := by
  rw [rightPairMatrix, ← Matrix.mul_kronecker_mul,
    Matrix.one_mul, hA]

private theorem pair_product_transport
    (V : Matrix (Fin d) (Fin e) ℂ) (hV : Vᴴ * V = 1)
    (B C : Matrix (Fin e × Fin e) (Fin e × Fin e) ℂ) :
    singleKrausMap (V ⊗ₖ (V ⊗ₖ V))
        (leftPairMatrix B * rightPairMatrix C) =
      leftPairMatrix (singleKrausMap (V ⊗ₖ V) B) *
        rightPairMatrix (singleKrausMap (V ⊗ₖ V) C) := by
  let W₂ := V ⊗ₖ V
  let W₃ := V ⊗ₖ W₂
  let P := singleKrausMap V 1
  let B' := singleKrausMap W₂ B
  let C' := singleKrausMap W₂ C
  have hW₂ : W₂ᴴ * W₂ = 1 := kronecker_isometry V V hV hV
  have hW₃ : W₃ᴴ * W₃ = 1 := kronecker_isometry V W₂ hV hW₂
  have hB' : B' * (P ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ)) = B' :=
    lift_pair_mul_firstProjection V hV B
  have hC' : ((1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ P) * C' = C' :=
    secondProjection_mul_lift_pair V hV C
  let Q₀ := P ⊗ₖ ((1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ
    (1 : Matrix (Fin d) (Fin d) ℂ))
  let Q₂ := (1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ
    ((1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ P)
  have hleft :
      singleKrausMap W₃ (leftPairMatrix B) = leftPairMatrix B' * Q₂ := by
    rw [lift_leftPairMatrix]
    exact (leftPair_mul_lastProjection B' P).symm
  have hright :
      singleKrausMap W₃ (rightPairMatrix C) = Q₀ * rightPairMatrix C' := by
    rw [lift_rightPairMatrix]
    exact (firstProjection_mul_rightPair P C').symm
  calc
    singleKrausMap W₃ (leftPairMatrix B * rightPairMatrix C) =
        singleKrausMap W₃ (leftPairMatrix B) *
          singleKrausMap W₃ (rightPairMatrix C) :=
      singleKrausMap_mul W₃ hW₃ _ _
    _ = (leftPairMatrix B' * Q₂) * (Q₀ * rightPairMatrix C') := by
      rw [hleft, hright]
    _ = leftPairMatrix B' * (Q₂ * Q₀) * rightPairMatrix C' := by
      simp only [Matrix.mul_assoc]
    _ = leftPairMatrix B' * (Q₀ * Q₂) * rightPairMatrix C' := by
      rw [first_lastProjection_comm]
    _ = (leftPairMatrix B' * Q₀) *
        (Q₂ * rightPairMatrix C') := by
      simp only [Matrix.mul_assoc]
    _ = leftPairMatrix B' * rightPairMatrix C' := by
      rw [leftPair_mul_firstProjection B' P hB',
        lastProjection_mul_rightPair P C' hC']

private theorem reindex_sitewisePhysicalMatrix_three
    (V : Matrix (Fin d) (Fin e) ℂ) :
    Matrix.reindex (_root_.finThreeArrowEquiv (Fin d))
        (_root_.finThreeArrowEquiv (Fin e))
        (sitewisePhysicalMatrix V 3) = V ⊗ₖ (V ⊗ₖ V) := by
  ext ⟨i, j, k⟩ ⟨a, b, c⟩
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply,
    finThreeArrowEquiv_symm_apply, Nat.succ_eq_add_one, Nat.reduceAdd,
    Matrix.kroneckerMap_apply]
  change (∏ n : Fin 3, V (![i, j, k] n) (![a, b, c] n)) =
    V i a * (V j b * V k c)
  rw [Fin.prod_univ_succ, Fin.prod_univ_succ, Fin.prod_univ_succ]
  simp

private theorem reindex_embedLocalOperator_three_zero
    (B : Matrix (Fin 2 → Fin e) (Fin 2 → Fin e) ℂ) :
    Matrix.reindex (_root_.finThreeArrowEquiv (Fin e))
        (_root_.finThreeArrowEquiv (Fin e))
        (embedLocalOperator (d := e) 2 3 (by decide) (0 : Fin 3) B) =
      leftPairMatrix
        (Matrix.reindex (_root_.finTwoArrowEquiv (Fin e))
          (_root_.finTwoArrowEquiv (Fin e)) B) := by
  ext σ τ
  have hAgree :
      AgreesOutsideWindow (d := e) 2 (by decide) (0 : Fin 3)
          ((_root_.finThreeArrowEquiv (Fin e)).symm σ)
          ((_root_.finThreeArrowEquiv (Fin e)).symm τ) ↔
        τ.2.2 = σ.2.2 := by
    constructor
    · intro ha
      have h := congrFun ha (2 : Fin 3)
      simpa [AgreesOutsideWindow, MPSTensor.replaceWindow,
        MPSTensor.extractWindow] using h
    · intro ha
      funext i
      fin_cases i <;>
        simp [MPSTensor.replaceWindow, MPSTensor.extractWindow, ha]
  have hσ :
      MPSTensor.extractWindow 2 (0 : Fin 3)
          ((_root_.finThreeArrowEquiv (Fin e)).symm σ) =
        (_root_.finTwoArrowEquiv (Fin e)).symm (σ.1, σ.2.1) := by
    funext r
    fin_cases r <;> rfl
  have hτ :
      MPSTensor.extractWindow 2 (0 : Fin 3)
          ((_root_.finThreeArrowEquiv (Fin e)).symm τ) =
        (_root_.finTwoArrowEquiv (Fin e)).symm (τ.1, τ.2.1) := by
    funext r
    fin_cases r <;> rfl
  by_cases h : τ.2.2 = σ.2.2
  · have ha := hAgree.mpr h
    simp only [Fin.isValue, Matrix.reindex_apply, Matrix.submatrix_apply,
      embedLocalOperator_apply]
    rw [if_pos ha]
    simp only [leftPairMatrix]
    rw [hσ, hτ]
    change
      B ((_root_.finTwoArrowEquiv (Fin e)).symm (σ.1, σ.2.1))
          ((_root_.finTwoArrowEquiv (Fin e)).symm (τ.1, τ.2.1)) =
        B ((_root_.finTwoArrowEquiv (Fin e)).symm (σ.1, σ.2.1))
            ((_root_.finTwoArrowEquiv (Fin e)).symm (τ.1, τ.2.1)) *
          (if σ.2.2 = τ.2.2 then 1 else 0)
    rw [if_pos h.symm, mul_one]
  · have ha : ¬ AgreesOutsideWindow (d := e) 2 (by decide) (0 : Fin 3)
        ((_root_.finThreeArrowEquiv (Fin e)).symm σ)
        ((_root_.finThreeArrowEquiv (Fin e)).symm τ) :=
      fun ha ↦ h (hAgree.mp ha)
    simp only [Fin.isValue, Matrix.reindex_apply, Matrix.submatrix_apply,
      embedLocalOperator_apply]
    rw [if_neg ha]
    simp only [leftPairMatrix]
    change 0 = B _ _ * (if σ.2.2 = τ.2.2 then 1 else 0)
    rw [if_neg (fun hs ↦ h hs.symm), mul_zero]

private theorem reindex_embedLocalOperator_three_one
    (B : Matrix (Fin 2 → Fin e) (Fin 2 → Fin e) ℂ) :
    Matrix.reindex (_root_.finThreeArrowEquiv (Fin e))
        (_root_.finThreeArrowEquiv (Fin e))
        (embedLocalOperator (d := e) 2 3 (by decide) (1 : Fin 3) B) =
      rightPairMatrix
        (Matrix.reindex (_root_.finTwoArrowEquiv (Fin e))
          (_root_.finTwoArrowEquiv (Fin e)) B) := by
  ext σ τ
  have hAgree :
      AgreesOutsideWindow (d := e) 2 (by decide) (1 : Fin 3)
          ((_root_.finThreeArrowEquiv (Fin e)).symm σ)
          ((_root_.finThreeArrowEquiv (Fin e)).symm τ) ↔
        τ.1 = σ.1 := by
    constructor
    · intro ha
      have h := congrFun ha (0 : Fin 3)
      simpa [MPSTensor.replaceWindow, MPSTensor.extractWindow] using h
    · intro ha
      funext i
      fin_cases i <;>
        simp [MPSTensor.replaceWindow, MPSTensor.extractWindow, ha]
  have hσ :
      MPSTensor.extractWindow 2 (1 : Fin 3)
          ((_root_.finThreeArrowEquiv (Fin e)).symm σ) =
        (_root_.finTwoArrowEquiv (Fin e)).symm σ.2 := by
    funext r
    fin_cases r <;> rfl
  have hτ :
      MPSTensor.extractWindow 2 (1 : Fin 3)
          ((_root_.finThreeArrowEquiv (Fin e)).symm τ) =
        (_root_.finTwoArrowEquiv (Fin e)).symm τ.2 := by
    funext r
    fin_cases r <;> rfl
  by_cases h : τ.1 = σ.1
  · have ha := hAgree.mpr h
    simp only [Fin.isValue, Matrix.reindex_apply, Matrix.submatrix_apply,
      embedLocalOperator_apply]
    rw [if_pos ha]
    rw [hσ, hτ]
    change B _ _ = (if σ.1 = τ.1 then 1 else 0) * B _ _
    rw [if_pos h.symm, one_mul]
  · have ha : ¬ AgreesOutsideWindow (d := e) 2 (by decide) (1 : Fin 3)
        ((_root_.finThreeArrowEquiv (Fin e)).symm σ)
        ((_root_.finThreeArrowEquiv (Fin e)).symm τ) :=
      fun ha ↦ h (hAgree.mp ha)
    simp only [Fin.isValue, Matrix.reindex_apply, Matrix.submatrix_apply,
      embedLocalOperator_apply]
    rw [if_neg ha]
    simp only [rightPairMatrix, Matrix.kroneckerMap_apply,
      Matrix.one_apply]
    change 0 = (if σ.1 = τ.1 then 1 else 0) * B _ _
    rw [if_neg (fun hs ↦ h hs.symm), zero_mul]

private theorem reindex_embedLocalOperator_two_zero
    (B : Matrix (Fin 2 → Fin e) (Fin 2 → Fin e) ℂ) :
    Matrix.reindex (_root_.finTwoArrowEquiv (Fin e))
        (_root_.finTwoArrowEquiv (Fin e))
        (embedLocalOperator (d := e) 2 2 (by decide) (0 : Fin 2) B) =
      Matrix.reindex (_root_.finTwoArrowEquiv (Fin e))
        (_root_.finTwoArrowEquiv (Fin e)) B := by
  ext σ τ
  have hAgree : AgreesOutsideWindow (d := e) 2 (by decide) (0 : Fin 2)
      ((_root_.finTwoArrowEquiv (Fin e)).symm σ)
      ((_root_.finTwoArrowEquiv (Fin e)).symm τ) := by
    funext i
    fin_cases i <;>
      simp [MPSTensor.replaceWindow, MPSTensor.extractWindow,
        _root_.finTwoArrowEquiv]
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply,
    embedLocalOperator_apply]
  rw [if_pos hAgree]
  simp only [Fin.isValue, finTwoArrowEquiv_symm_apply]
  congr 1 <;> funext j <;> fin_cases j <;> rfl

private theorem reindex_embedLocalOperator_two_one
    (B : Matrix (Fin 2 → Fin e) (Fin 2 → Fin e) ℂ) :
    Matrix.reindex (_root_.finTwoArrowEquiv (Fin e))
        (_root_.finTwoArrowEquiv (Fin e))
        (embedLocalOperator (d := e) 2 2 (by decide) (1 : Fin 2) B) =
      swapPairMatrix
        (Matrix.reindex (_root_.finTwoArrowEquiv (Fin e))
          (_root_.finTwoArrowEquiv (Fin e)) B) := by
  ext σ τ
  have hAgree : AgreesOutsideWindow (d := e) 2 (by decide) (1 : Fin 2)
      ((_root_.finTwoArrowEquiv (Fin e)).symm σ)
      ((_root_.finTwoArrowEquiv (Fin e)).symm τ) := by
    funext i
    fin_cases i <;>
      simp [MPSTensor.replaceWindow, MPSTensor.extractWindow,
        _root_.finTwoArrowEquiv]
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply,
    embedLocalOperator_apply]
  rw [if_pos hAgree]
  simp only [Fin.isValue, finTwoArrowEquiv_symm_apply]
  congr 1 <;> funext j <;> fin_cases j <;> rfl

/-- On a two-site periodic chain, isometric conjugation carries the product
of the two oppositely oriented restricted bonds to the product of their
ambient lifts.

Source: arXiv:1606.00608, Appendix C.2, equations `PjKiPj` and
`generateMPDO`, lines 1733--1770. -/
theorem singleKrausMap_crossedTwoSiteBondProduct
    (V : Matrix (Fin d) (Fin e) ℂ) (hV : Vᴴ * V = 1)
    (B C : Matrix (Fin 2 → Fin e) (Fin 2 → Fin e) ℂ) :
    singleKrausMap (sitewisePhysicalMatrix V 2)
        (embedLocalOperator (d := e) 2 2 (by decide) (0 : Fin 2) B *
          embedLocalOperator (d := e) 2 2 (by decide) (1 : Fin 2) C) =
      embedLocalOperator (d := d) 2 2 (by decide) (0 : Fin 2)
          (singleKrausMap (sitewisePhysicalMatrix V 2) B) *
        embedLocalOperator (d := d) 2 2 (by decide) (1 : Fin 2)
          (singleKrausMap (sitewisePhysicalMatrix V 2) C) := by
  apply (Matrix.reindex (_root_.finTwoArrowEquiv (Fin d))
    (_root_.finTwoArrowEquiv (Fin d))).injective
  rw [Matrix.reindex_singleKrausMap
      (_root_.finTwoArrowEquiv (Fin e))
      (_root_.finTwoArrowEquiv (Fin d)),
    reindex_sitewisePhysicalMatrix_two]
  have hrestricted := Matrix.reindexLinearEquiv_mul ℂ ℂ
      (_root_.finTwoArrowEquiv (Fin e))
      (_root_.finTwoArrowEquiv (Fin e))
      (_root_.finTwoArrowEquiv (Fin e))
      (embedLocalOperator (d := e) 2 2 (by decide) (0 : Fin 2) B)
      (embedLocalOperator (d := e) 2 2 (by decide) (1 : Fin 2) C)
  simp only [Matrix.coe_reindexLinearEquiv] at hrestricted
  rw [← hrestricted, reindex_embedLocalOperator_two_zero,
    reindex_embedLocalOperator_two_one]
  have hambient := Matrix.reindexLinearEquiv_mul ℂ ℂ
      (_root_.finTwoArrowEquiv (Fin d))
      (_root_.finTwoArrowEquiv (Fin d))
      (_root_.finTwoArrowEquiv (Fin d))
      (embedLocalOperator (d := d) 2 2 (by decide) (0 : Fin 2)
        (singleKrausMap (sitewisePhysicalMatrix V 2) B))
      (embedLocalOperator (d := d) 2 2 (by decide) (1 : Fin 2)
        (singleKrausMap (sitewisePhysicalMatrix V 2) C))
  simp only [Matrix.coe_reindexLinearEquiv] at hambient
  rw [← hambient, reindex_embedLocalOperator_two_zero,
    reindex_embedLocalOperator_two_one,
    Matrix.reindex_singleKrausMap
      (_root_.finTwoArrowEquiv (Fin e))
      (_root_.finTwoArrowEquiv (Fin d)),
    Matrix.reindex_singleKrausMap
      (_root_.finTwoArrowEquiv (Fin e))
      (_root_.finTwoArrowEquiv (Fin d)),
    reindex_sitewisePhysicalMatrix_two]
  rw [singleKrausMap_mul _ (kronecker_isometry V V hV hV)]
  have hswap := swapPairMatrix_singleKraus_kronecker_self Vᴴ
    (Matrix.reindex (_root_.finTwoArrowEquiv (Fin e))
      (_root_.finTwoArrowEquiv (Fin e)) C)
  have hswap' :
      singleKrausMap (V ⊗ₖ V)
          (swapPairMatrix (Matrix.reindex
            (_root_.finTwoArrowEquiv (Fin e))
            (_root_.finTwoArrowEquiv (Fin e)) C)) =
        swapPairMatrix (singleKrausMap (V ⊗ₖ V)
          (Matrix.reindex (_root_.finTwoArrowEquiv (Fin e))
            (_root_.finTwoArrowEquiv (Fin e)) C)) := by
    simpa only [Matrix.conjTranspose_kronecker,
      Matrix.conjTranspose_conjTranspose] using hswap.symm
  rw [hswap']

/-- Isometric conjugation carries a product of two adjacent restricted bonds
to the product of their ambient two-site lifts.

Only the isometry identity is used.  In particular, the statement concerns a
three-site chain and requires neither a coisometry nor an empty-chain case.

Source: arXiv:1606.00608, Appendix C.2, equations `PjKiPj` and
`generateMPDO`, lines 1733--1770. -/
theorem singleKrausMap_adjacentBondProduct
    (V : Matrix (Fin d) (Fin e) ℂ) (hV : Vᴴ * V = 1)
    (B C : Matrix (Fin 2 → Fin e) (Fin 2 → Fin e) ℂ) :
    singleKrausMap (sitewisePhysicalMatrix V 3)
        (embedLocalOperator (d := e) 2 3 (by decide) (0 : Fin 3) B *
          embedLocalOperator (d := e) 2 3 (by decide) (1 : Fin 3) C) =
      embedLocalOperator (d := d) 2 3 (by decide) (0 : Fin 3)
          (singleKrausMap (sitewisePhysicalMatrix V 2) B) *
        embedLocalOperator (d := d) 2 3 (by decide) (1 : Fin 3)
          (singleKrausMap (sitewisePhysicalMatrix V 2) C) := by
  apply (Matrix.reindex (_root_.finThreeArrowEquiv (Fin d))
    (_root_.finThreeArrowEquiv (Fin d))).injective
  rw [Matrix.reindex_singleKrausMap
      (_root_.finThreeArrowEquiv (Fin e))
      (_root_.finThreeArrowEquiv (Fin d)),
    reindex_sitewisePhysicalMatrix_three]
  have hrestricted := Matrix.reindexLinearEquiv_mul ℂ ℂ
      (_root_.finThreeArrowEquiv (Fin e))
      (_root_.finThreeArrowEquiv (Fin e))
      (_root_.finThreeArrowEquiv (Fin e))
      (embedLocalOperator (d := e) 2 3 (by decide) (0 : Fin 3) B)
      (embedLocalOperator (d := e) 2 3 (by decide) (1 : Fin 3) C)
  simp only [Matrix.coe_reindexLinearEquiv] at hrestricted
  rw [← hrestricted]
  rw [reindex_embedLocalOperator_three_zero,
    reindex_embedLocalOperator_three_one]
  have hambient := Matrix.reindexLinearEquiv_mul ℂ ℂ
      (_root_.finThreeArrowEquiv (Fin d))
      (_root_.finThreeArrowEquiv (Fin d))
      (_root_.finThreeArrowEquiv (Fin d))
      (embedLocalOperator (d := d) 2 3 (by decide) (0 : Fin 3)
        (singleKrausMap (sitewisePhysicalMatrix V 2) B))
      (embedLocalOperator (d := d) 2 3 (by decide) (1 : Fin 3)
        (singleKrausMap (sitewisePhysicalMatrix V 2) C))
  simp only [Matrix.coe_reindexLinearEquiv] at hambient
  rw [← hambient]
  rw [reindex_embedLocalOperator_three_zero,
    reindex_embedLocalOperator_three_one,
    Matrix.reindex_singleKrausMap
      (_root_.finTwoArrowEquiv (Fin e))
      (_root_.finTwoArrowEquiv (Fin d)),
    Matrix.reindex_singleKrausMap
      (_root_.finTwoArrowEquiv (Fin e))
      (_root_.finTwoArrowEquiv (Fin d)),
    reindex_sitewisePhysicalMatrix_two]
  exact pair_product_transport V hV _ _

end MPOTensor
