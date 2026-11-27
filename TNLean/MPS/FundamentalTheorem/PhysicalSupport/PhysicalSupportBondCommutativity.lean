/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Channel.KrausMap.SingleKrausPositivity
import QICLean.Algebra.Unitary.MatrixUnitaryBetween
import TNLean.MPS.Operator.Simple.PlaceAlongRingWindowTwoSite
import TNLean.MPS.FundamentalTheorem.PhysicalSupport.PhysicalSupportBondTransport

/-!
# Commuting bonds on an isometric physical support

The positive commuting bond on an injective physical support is included into
the ambient physical space.  Its neighboring translates commute on every
periodic chain of length at least two.  The two-site crossed chain is treated
separately; every longer chain reduces by locality to the three-site
calculation.

No zero-length or one-site nearest-neighbor chain occurs.

It also contains the following results.

* `MPOTensor.singleKrausMap_crossedTwoSiteBondProduct`,
  `MPOTensor.singleKrausMap_adjacentBondProduct`: isometric transport of adjacent two-site bonds.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Appendix C.2, equations `PjKiPj` and `generateMPDO`, lines 1733--1770
-/

section IsometricAdjacentBondTransport

/-!
## Isometric transport of adjacent two-site bonds

If a one-site isometry includes a physical subspace into an ambient physical
space, conjugation of a product of two adjacent restricted bonds is exactly
the product of their two ambient lifts.  The shared physical index contracts
through the isometry identity.  No coisometry is used.

The calculation takes place on a three-site chain.  Thus it has no empty-chain
case and is the local input for transporting neighboring commutativity through
an orthogonal physical support.

### References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Appendix C.2, equations `PjKiPj` and `generateMPDO`, lines 1733--1770
-/

open scoped Matrix BigOperators ComplexOrder Kronecker

open MPOTensor ManyBody

namespace MPOTensor

variable {d e : ℕ}

open MPOTensor.PhysicalSectorFactorization

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
    Matrix.singleKrausMap_kronecker]
  ext
  simp [Matrix.reindex_apply]

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
  rw [rightPairMatrix, Matrix.singleKrausMap_kronecker]

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
  have hW₂ : W₂ᴴ * W₂ = 1 :=
    Matrix.IsIsometry.kronecker V V hV hV
  have hW₃ : W₃ᴴ * W₃ = 1 :=
    Matrix.IsIsometry.kronecker V W₂ hV hW₂
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
      Matrix.singleKrausMap_mul_of_isometry W₃ hW₃ _ _
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

private theorem reindex_placeAlong_ringWindow_three_zero
    (B : Matrix (Fin 2 → Fin e) (Fin 2 → Fin e) ℂ) :
    Matrix.reindex (_root_.finThreeArrowEquiv (Fin e))
        (_root_.finThreeArrowEquiv (Fin e))
        (placeAlong (X := fun _ ↦ Fin e) (ringWindow (by decide : 2 ≤ 3) (0 : Fin 3)) B) =
      leftPairMatrix
        (Matrix.reindex (_root_.finTwoArrowEquiv (Fin e))
          (_root_.finTwoArrowEquiv (Fin e)) B) := by
  ext σ τ
  have hAgree := forall_ringWindow_ne_imp_finThreeArrowEquiv_three_zero σ τ
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
    simp only [Fin.isValue, Matrix.reindex_apply, Matrix.submatrix_apply]
    rw [placeAlong_apply, ite_eq_left ha, ← MPSTensor.extractWindow_eq_comp_ringWindow,
      ← MPSTensor.extractWindow_eq_comp_ringWindow]
    simp only [leftPairMatrix]
    rw [hσ, hτ]
    change
      B ((_root_.finTwoArrowEquiv (Fin e)).symm (σ.1, σ.2.1))
          ((_root_.finTwoArrowEquiv (Fin e)).symm (τ.1, τ.2.1)) =
        B ((_root_.finTwoArrowEquiv (Fin e)).symm (σ.1, σ.2.1))
            ((_root_.finTwoArrowEquiv (Fin e)).symm (τ.1, τ.2.1)) *
          (if σ.2.2 = τ.2.2 then 1 else 0)
    rw [ite_eq_left h.symm, mul_one]
  · simp only [Fin.isValue, Matrix.reindex_apply, Matrix.submatrix_apply]
    rw [placeAlong_apply, ite_eq_right (hAgree.not.mpr h)]
    simp only [leftPairMatrix]
    change 0 = B _ _ * (if σ.2.2 = τ.2.2 then 1 else 0)
    rw [ite_eq_right (fun hs ↦ h hs.symm), mul_zero]

private theorem reindex_placeAlong_ringWindow_three_one
    (B : Matrix (Fin 2 → Fin e) (Fin 2 → Fin e) ℂ) :
    Matrix.reindex (_root_.finThreeArrowEquiv (Fin e))
        (_root_.finThreeArrowEquiv (Fin e))
        (placeAlong (X := fun _ ↦ Fin e) (ringWindow (by decide : 2 ≤ 3) (1 : Fin 3)) B) =
      rightPairMatrix
        (Matrix.reindex (_root_.finTwoArrowEquiv (Fin e))
          (_root_.finTwoArrowEquiv (Fin e)) B) := by
  ext σ τ
  have hAgree := forall_ringWindow_ne_imp_finThreeArrowEquiv_three_one σ τ
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
    simp only [Fin.isValue, Matrix.reindex_apply, Matrix.submatrix_apply]
    rw [placeAlong_apply, ite_eq_left ha, ← MPSTensor.extractWindow_eq_comp_ringWindow,
      ← MPSTensor.extractWindow_eq_comp_ringWindow]
    rw [hσ, hτ]
    change B _ _ = (if σ.1 = τ.1 then 1 else 0) * B _ _
    rw [ite_eq_left h.symm, one_mul]
  · simp only [Fin.isValue, Matrix.reindex_apply, Matrix.submatrix_apply]
    rw [placeAlong_apply, ite_eq_right (hAgree.not.mpr h)]
    simp only [rightPairMatrix, Matrix.kroneckerMap_apply,
      Matrix.one_apply]
    change 0 = (if σ.1 = τ.1 then 1 else 0) * B _ _
    rw [ite_eq_right (fun hs ↦ h hs.symm), zero_mul]

/-- On a two-site periodic chain, isometric conjugation carries the product
of the two oppositely oriented restricted bonds to the product of their
ambient lifts.

Source: arXiv:1606.00608, Appendix C.2, equations `PjKiPj` and
`generateMPDO`, lines 1733--1770. -/
theorem singleKrausMap_crossedTwoSiteBondProduct
    (V : Matrix (Fin d) (Fin e) ℂ) (hV : Vᴴ * V = 1)
    (B C : Matrix (Fin 2 → Fin e) (Fin 2 → Fin e) ℂ) :
    singleKrausMap (Matrix.piKronecker fun _ : Fin 2 ↦ V)
        (placeAlong (X := fun _ ↦ Fin e) (ringWindow le_rfl (0 : Fin 2)) B *
          placeAlong (X := fun _ ↦ Fin e) (ringWindow le_rfl (1 : Fin 2)) C) =
      placeAlong (X := fun _ ↦ Fin d) (ringWindow le_rfl (0 : Fin 2))
          (singleKrausMap (Matrix.piKronecker fun _ : Fin 2 ↦ V) B) *
        placeAlong (X := fun _ ↦ Fin d) (ringWindow le_rfl (1 : Fin 2))
          (singleKrausMap (Matrix.piKronecker fun _ : Fin 2 ↦ V) C) := by
  apply (Matrix.reindex (_root_.finTwoArrowEquiv (Fin d))
    (_root_.finTwoArrowEquiv (Fin d))).injective
  rw [Matrix.reindex_singleKrausMap
      (_root_.finTwoArrowEquiv (Fin e))
      (_root_.finTwoArrowEquiv (Fin d)),
    Matrix.reindex_piKronecker_two]
  have hrestricted := Matrix.reindexLinearEquiv_mul ℂ ℂ
      (_root_.finTwoArrowEquiv (Fin e))
      (_root_.finTwoArrowEquiv (Fin e))
      (_root_.finTwoArrowEquiv (Fin e))
      (placeAlong (X := fun _ ↦ Fin e) (ringWindow le_rfl (0 : Fin 2)) B)
      (placeAlong (X := fun _ ↦ Fin e) (ringWindow le_rfl (1 : Fin 2)) C)
  simp only [Matrix.coe_reindexLinearEquiv] at hrestricted
  rw [← hrestricted, reindex_placeAlong_ringWindow_two_zero,
    reindex_placeAlong_ringWindow_two_one]
  have hambient := Matrix.reindexLinearEquiv_mul ℂ ℂ
      (_root_.finTwoArrowEquiv (Fin d))
      (_root_.finTwoArrowEquiv (Fin d))
      (_root_.finTwoArrowEquiv (Fin d))
      (placeAlong (X := fun _ ↦ Fin d) (ringWindow le_rfl (0 : Fin 2))
        (singleKrausMap (Matrix.piKronecker fun _ : Fin 2 ↦ V) B))
      (placeAlong (X := fun _ ↦ Fin d) (ringWindow le_rfl (1 : Fin 2))
        (singleKrausMap (Matrix.piKronecker fun _ : Fin 2 ↦ V) C))
  simp only [Matrix.coe_reindexLinearEquiv] at hambient
  rw [← hambient, reindex_placeAlong_ringWindow_two_zero,
    reindex_placeAlong_ringWindow_two_one,
    Matrix.reindex_singleKrausMap
      (_root_.finTwoArrowEquiv (Fin e))
      (_root_.finTwoArrowEquiv (Fin d)),
    Matrix.reindex_singleKrausMap
      (_root_.finTwoArrowEquiv (Fin e))
      (_root_.finTwoArrowEquiv (Fin d)),
    Matrix.reindex_piKronecker_two]
  rw [Matrix.singleKrausMap_mul_of_isometry _
    (Matrix.IsIsometry.kronecker V V hV hV)]
  have hswap := swapPairMatrix_singleKraus_kronecker_self Vᴴ
    (Matrix.reindex (_root_.finTwoArrowEquiv (Fin e))
      (_root_.finTwoArrowEquiv (Fin e)) C)
  have hswap' :
      singleKrausMap (V ⊗ₖ V)
          (Matrix.reindex (Equiv.prodComm (Fin e) (Fin e))
            (Equiv.prodComm (Fin e) (Fin e))
            (Matrix.reindex (_root_.finTwoArrowEquiv (Fin e))
              (_root_.finTwoArrowEquiv (Fin e)) C)) =
        Matrix.reindex (Equiv.prodComm (Fin d) (Fin d))
          (Equiv.prodComm (Fin d) (Fin d))
          (singleKrausMap (V ⊗ₖ V)
            (Matrix.reindex (_root_.finTwoArrowEquiv (Fin e))
              (_root_.finTwoArrowEquiv (Fin e)) C)) := by
    simpa only [swapPairMatrix, Matrix.conjTranspose_kronecker,
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
    singleKrausMap (Matrix.piKronecker fun _ : Fin 3 ↦ V)
        (placeAlong (X := fun _ ↦ Fin e) (ringWindow (by decide : 2 ≤ 3) (0 : Fin 3)) B *
          placeAlong (X := fun _ ↦ Fin e) (ringWindow (by decide : 2 ≤ 3) (1 : Fin 3)) C) =
      placeAlong (X := fun _ ↦ Fin d) (ringWindow (by decide : 2 ≤ 3) (0 : Fin 3))
          (singleKrausMap (Matrix.piKronecker fun _ : Fin 2 ↦ V) B) *
        placeAlong (X := fun _ ↦ Fin d) (ringWindow (by decide : 2 ≤ 3) (1 : Fin 3))
          (singleKrausMap (Matrix.piKronecker fun _ : Fin 2 ↦ V) C) := by
  apply (Matrix.reindex (_root_.finThreeArrowEquiv (Fin d))
    (_root_.finThreeArrowEquiv (Fin d))).injective
  rw [Matrix.reindex_singleKrausMap
      (_root_.finThreeArrowEquiv (Fin e))
      (_root_.finThreeArrowEquiv (Fin d)),
    Matrix.reindex_piKronecker_three]
  have hrestricted := Matrix.reindexLinearEquiv_mul ℂ ℂ
      (_root_.finThreeArrowEquiv (Fin e))
      (_root_.finThreeArrowEquiv (Fin e))
      (_root_.finThreeArrowEquiv (Fin e))
      (placeAlong (X := fun _ ↦ Fin e) (ringWindow (by decide : 2 ≤ 3) (0 : Fin 3)) B)
      (placeAlong (X := fun _ ↦ Fin e) (ringWindow (by decide : 2 ≤ 3) (1 : Fin 3)) C)
  simp only [Matrix.coe_reindexLinearEquiv] at hrestricted
  rw [← hrestricted]
  rw [reindex_placeAlong_ringWindow_three_zero,
    reindex_placeAlong_ringWindow_three_one]
  have hambient := Matrix.reindexLinearEquiv_mul ℂ ℂ
      (_root_.finThreeArrowEquiv (Fin d))
      (_root_.finThreeArrowEquiv (Fin d))
      (_root_.finThreeArrowEquiv (Fin d))
      (placeAlong (X := fun _ ↦ Fin d) (ringWindow (by decide : 2 ≤ 3) (0 : Fin 3))
        (singleKrausMap (Matrix.piKronecker fun _ : Fin 2 ↦ V) B))
      (placeAlong (X := fun _ ↦ Fin d) (ringWindow (by decide : 2 ≤ 3) (1 : Fin 3))
        (singleKrausMap (Matrix.piKronecker fun _ : Fin 2 ↦ V) C))
  simp only [Matrix.coe_reindexLinearEquiv] at hambient
  rw [← hambient]
  rw [reindex_placeAlong_ringWindow_three_zero,
    reindex_placeAlong_ringWindow_three_one,
    Matrix.reindex_singleKrausMap
      (_root_.finTwoArrowEquiv (Fin e))
      (_root_.finTwoArrowEquiv (Fin d)),
    Matrix.reindex_singleKrausMap
      (_root_.finTwoArrowEquiv (Fin e))
      (_root_.finTwoArrowEquiv (Fin d)),
    Matrix.reindex_piKronecker_two]
  exact pair_product_transport V hV _ _

end MPOTensor

end IsometricAdjacentBondTransport

section PhysicalSupportBondCommutativity

open scoped Matrix BigOperators ComplexOrder
open ManyBody

namespace MPOTensor.PhysicalSupportRestrictionData

variable {d D : ℕ} {P : Matrix (Fin d) (Fin d) ℂ} {K : MPOTensor d D}

open MPOTensor.PhysicalSectorFactorization

/-- The two lifted neighboring bonds commute on a three-site chain.

Source: arXiv:1606.00608, Appendix C.2, equations `PjKiPj` and
`generateMPDO`, lines 1733--1770. -/
theorem liftedBond_three_zero_one_comm
    (F : PhysicalSupportRestrictionData P K)
    (data : CommutingBond F.supportDim) :
    placeAlong (X := fun _ ↦ Fin d) (ringWindow (by decide : 2 ≤ 3) (0 : Fin 3))
          (F.liftedBond data.bond) *
        placeAlong (X := fun _ ↦ Fin d) (ringWindow (by decide : 2 ≤ 3) (1 : Fin 3))
          (F.liftedBond data.bond) =
      placeAlong (X := fun _ ↦ Fin d) (ringWindow (by decide : 2 ≤ 3) (1 : Fin 3))
          (F.liftedBond data.bond) *
        placeAlong (X := fun _ ↦ Fin d) (ringWindow (by decide : 2 ≤ 3) (0 : Fin 3))
          (F.liftedBond data.bond) := by
  let A := placeAlong (X := fun _ ↦ Fin F.supportDim)
    (ringWindow (by decide : 2 ≤ 3) (0 : Fin 3)) data.bond
  let B := placeAlong (X := fun _ ↦ Fin F.supportDim)
    (ringWindow (by decide : 2 ≤ 3) (1 : Fin 3)) data.bond
  have hcomm : A * B = B * A := data.bond_comm (by decide) 0 1
  have hA : A.IsHermitian :=
    (posSemidef_placeAlong _ data.bond_pos).1
  have hB : B.IsHermitian :=
    (posSemidef_placeAlong _ data.bond_pos).1
  have hrestricted : (A * B).IsHermitian :=
    (hA.commute_iff hB).mp hcomm
  have hambient :
      (singleKrausMap (Matrix.piKronecker fun _ : Fin 3 ↦ F.inclusion) (A * B)).IsHermitian :=
    Matrix.isHermitian_mul_mul_conjTranspose
      (Matrix.piKronecker fun _ : Fin 3 ↦ F.inclusion) hrestricted
  rw [singleKrausMap_adjacentBondProduct
    F.inclusion F.inclusion_isometry data.bond data.bond] at hambient
  refine Commute.eq ((Matrix.IsHermitian.commute_iff ?_ ?_).mpr ?_)
  · exact (posSemidef_placeAlong _
      (F.liftedBond_pos data.bond_pos)).1
  · exact (posSemidef_placeAlong _
      (F.liftedBond_pos data.bond_pos)).1
  · exact hambient

/-- The two oppositely oriented lifted bonds commute on the two-site periodic
chain.

Source: arXiv:1606.00608, Appendix C.2, equations `PjKiPj` and
`generateMPDO`, lines 1733--1770. -/
theorem liftedBond_two_zero_one_comm
    (F : PhysicalSupportRestrictionData P K)
    (data : CommutingBond F.supportDim) :
    placeAlong (X := fun _ ↦ Fin d) (ringWindow (by decide : 2 ≤ 2) (0 : Fin 2))
          (F.liftedBond data.bond) *
        placeAlong (X := fun _ ↦ Fin d) (ringWindow (by decide : 2 ≤ 2) (1 : Fin 2))
          (F.liftedBond data.bond) =
      placeAlong (X := fun _ ↦ Fin d) (ringWindow (by decide : 2 ≤ 2) (1 : Fin 2))
          (F.liftedBond data.bond) *
        placeAlong (X := fun _ ↦ Fin d) (ringWindow (by decide : 2 ≤ 2) (0 : Fin 2))
          (F.liftedBond data.bond) := by
  let A := placeAlong (X := fun _ ↦ Fin F.supportDim)
    (ringWindow (by decide : 2 ≤ 2) (0 : Fin 2)) data.bond
  let B := placeAlong (X := fun _ ↦ Fin F.supportDim)
    (ringWindow (by decide : 2 ≤ 2) (1 : Fin 2)) data.bond
  have hcomm : A * B = B * A := data.bond_comm (by decide) 0 1
  have hA : A.IsHermitian :=
    (posSemidef_placeAlong _ data.bond_pos).1
  have hB : B.IsHermitian :=
    (posSemidef_placeAlong _ data.bond_pos).1
  have hrestricted : (A * B).IsHermitian :=
    (hA.commute_iff hB).mp hcomm
  have hambient :
      (singleKrausMap (Matrix.piKronecker fun _ : Fin 2 ↦ F.inclusion) (A * B)).IsHermitian :=
    Matrix.isHermitian_mul_mul_conjTranspose
      (Matrix.piKronecker fun _ : Fin 2 ↦ F.inclusion) hrestricted
  rw [singleKrausMap_crossedTwoSiteBondProduct
    F.inclusion F.inclusion_isometry data.bond data.bond] at hambient
  refine Commute.eq ((Matrix.IsHermitian.commute_iff ?_ ?_).mpr ?_)
  · exact (posSemidef_placeAlong _
      (F.liftedBond_pos data.bond_pos)).1
  · exact (posSemidef_placeAlong _
      (F.liftedBond_pos data.bond_pos)).1
  · exact hambient

/-- The lifted bond commutes with its translate by one site on every periodic
chain of length at least two.

Source: arXiv:1606.00608, Appendix C.2, equations `PjKiPj` and
`generateMPDO`, lines 1733--1770. -/
theorem liftedBond_zero_one_comm
    (F : PhysicalSupportRestrictionData P K)
    (data : CommutingBond F.supportDim)
    {N : ℕ} (hN : 2 ≤ N) :
    placeAlong (X := fun _ ↦ Fin d) (ringWindow hN ⟨0, by omega⟩)
          (F.liftedBond data.bond) *
        placeAlong (X := fun _ ↦ Fin d) (ringWindow hN ⟨1, by omega⟩)
          (F.liftedBond data.bond) =
      placeAlong (X := fun _ ↦ Fin d) (ringWindow hN ⟨1, by omega⟩)
          (F.liftedBond data.bond) *
        placeAlong (X := fun _ ↦ Fin d) (ringWindow hN ⟨0, by omega⟩)
          (F.liftedBond data.bond) := by
  by_cases htwo : N = 2
  · subst N
    exact F.liftedBond_two_zero_one_comm data
  · have hthree : 3 ≤ N := by omega
    let B := F.liftedBond data.bond
    have hzero := placeAlong_ringWindow_two_zero_nested (d := d)
      hthree ⟨0, by omega⟩ B
    have hone := placeAlong_ringWindow_two_one_nested (d := d)
      hthree ⟨0, by omega⟩ B
    have hsite : finRotate N ⟨0, by omega⟩ = ⟨1, by omega⟩ := by
      apply Fin.ext
      rw [coe_finRotate_mod]
      change 1 % N = 1
      exact Nat.mod_eq_of_lt (by omega)
    rw [hsite] at hone
    have hone' :
        placeAlong (X := fun _ ↦ Fin d) (ringWindow hthree ⟨0, by omega⟩)
            (placeAlong (X := fun _ ↦ Fin d) (ringWindow (by decide : 2 ≤ 3) (1 : Fin 3)) B) =
          placeAlong (X := fun _ ↦ Fin d) (ringWindow (by omega : 2 ≤ N) ⟨1, by omega⟩)
            B := by
      exact hone
    rw [← hzero, ← hone']
    rw [← placeAlong_mul, ← placeAlong_mul]
    exact congrArg
      (placeAlong (X := fun _ ↦ Fin d) (ringWindow hthree ⟨0, by omega⟩))
      (F.liftedBond_three_zero_one_comm data)

private theorem supportProjection_isOrthogonal
    (F : PhysicalSupportRestrictionData P K) : IsOrthogonalProjection P := by
  rw [← F.inclusion_range]
  constructor
  · exact Matrix.isHermitian_mul_conjTranspose_self F.inclusion
  · calc
      (F.inclusion * F.inclusionᴴ) *
          (F.inclusion * F.inclusionᴴ) =
        F.inclusion * (F.inclusionᴴ * F.inclusion) * F.inclusionᴴ := by
          simp only [Matrix.mul_assoc]
      _ = F.inclusion * F.inclusionᴴ := by
        rw [F.inclusion_isometry, Matrix.mul_one]

/-- A translation-invariant commuting bond on the restricted physical space
has a positive translation-invariant commuting lift to the ambient physical
space.

Source: arXiv:1606.00608, Appendix C.2, equations `PjKiPj` and
`generateMPDO`, lines 1733--1770. -/
noncomputable def liftedCommutingBond
    (F : PhysicalSupportRestrictionData P K)
    (data : CommutingBond F.supportDim) :
    CommutingBond d where
  bond := F.liftedBond data.bond
  bond_pos := F.liftedBond_pos data.bond_pos
  bond_comm := by
    intro N hN i j
    let G : GSNNCHData d N := {
      hN := hN
      sectorCount := 1
      multiplicity := fun _ ↦ 1
      sectorProjection := fun _ ↦ P
      sectorProjection_isOrthogonal := fun _ ↦ F.supportProjection_isOrthogonal
      sectorProjection_orthogonal := by
        intro x y hxy
        exact (hxy (Subsingleton.elim x y)).elim
      bond := fun _ ↦ F.liftedBond data.bond
      bond_pos := fun _ ↦ F.liftedBond_pos data.bond_pos
      bond_supported := fun _ ↦ F.liftedBond_supported data.bond
      neighboring_comm := fun _ ↦ F.liftedBond_zero_one_comm data hN }
    simpa [G, GSNNCHData.bondAt] using G.bondAt_comm (0 : Fin 1) i j


end MPOTensor.PhysicalSupportRestrictionData

end PhysicalSupportBondCommutativity
