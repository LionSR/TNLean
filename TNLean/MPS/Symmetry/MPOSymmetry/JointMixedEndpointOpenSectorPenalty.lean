/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.MPOSymmetry.JointMixedEndpointInnerConstraints
import TNLean.MPS.Symmetry.MPOSymmetry.JointMixedEndpointOneSidedSupport
import TNLean.MPS.ParentHamiltonian.Martingale.SiteProjectionEmbedding

/-!
# Active projection and inactive penalty of the actual joint open chain

For at least three sites, impose the full joint first boundary frame at
the first site, the shared physical 00 space at every interior site, and
the full joint last boundary frame at the last site. The corresponding
commuting bond constraints are the first frame times the next row-zero
selector, the inner column-zero times row-zero selectors, and the final
column-zero selector times the last frame.

Each bond constraint contains the actual local support. Consequently the
complement of their product is bounded by the actual open Hamiltonian.
This coefficient-one estimate is an auxiliary improvement obtained from
the commuting constraints; it is not attributed as a constant in GLM23.
No gap within the active range is asserted.

Source context: GLM23, arXiv:2203.12563, Section 5, lines 1695–1777.
-/

open scoped Matrix Kronecker BigOperators ComplexOrder InnerProductSpace

namespace MPSTensor.MPOSymmetry

noncomputable section

private theorem projection_listProd
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (P : List (E →ₗ[ℂ] E))
    (hP : ∀ p ∈ P, p.IsSymmetricProjection)
    (hcomm : P.Pairwise Commute) :
    P.prod.IsSymmetricProjection := by
  induction P with
  | nil => exact ⟨IsIdempotentElem.one, LinearMap.IsSymmetric.id⟩
  | cons p P ih =>
      rw [List.pairwise_cons] at hcomm
      rw [List.prod_cons]
      exact (hP p List.mem_cons_self).mul_of_commute
        (ih (fun q hq => hP q (List.mem_cons_of_mem p hq)) hcomm.2)
        (Commute.list_prod_right P p hcomm.1)

private theorem one_sub_projection_listProd_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (P : List (E →ₗ[ℂ] E))
    (hP : ∀ p ∈ P, p.IsSymmetricProjection)
    (hcomm : P.Pairwise Commute) :
    1 - P.prod ≤ (P.map fun p => 1 - p).sum := by
  induction P with
  | nil => simp
  | cons p P ih =>
      rw [List.pairwise_cons] at hcomm
      rw [List.prod_cons, List.map_cons, List.sum_cons]
      have htail := fun q hq => hP q (List.mem_cons_of_mem p hq)
      exact ((hP p List.mem_cons_self).one_sub_mul_le_add_one_sub
        (projection_listProd P htail hcomm.2)
        (Commute.list_prod_right P p hcomm.1)).trans
          (add_le_add_left (ih htail hcomm.2) _)

private theorem fixed_mul_iff
    {E : Type*} [AddCommGroup E] [Module ℂ E]
    {P Q : E →ₗ[ℂ] E} (hP : IsIdempotentElem P) (hQ : IsIdempotentElem Q)
    (hcomm : Commute P Q) (v : E) :
    (P * Q) v = v ↔ P v = v ∧ Q v = v := by
  constructor
  · intro hv
    constructor
    · calc
        P v = P ((P * Q) v) := congrArg P hv.symm
        _ = (P * P * Q) v := rfl
        _ = (P * Q) v := by rw [hP.eq]
        _ = v := hv
    · calc
        Q v = Q ((P * Q) v) := congrArg Q hv.symm
        _ = (Q * P * Q) v := rfl
        _ = (P * (Q * Q)) v := by rw [← hcomm.eq, mul_assoc]
        _ = (P * Q) v := by rw [hQ.eq]
        _ = v := hv
  · rintro ⟨hPv, hQv⟩
    change P (Q v) = v
    rw [hQv, hPv]

private theorem mem_range_projection_listProd_iff
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (P : List (E →ₗ[ℂ] E))
    (hP : ∀ p ∈ P, p.IsSymmetricProjection)
    (hcomm : P.Pairwise Commute) (v : E) :
    v ∈ LinearMap.range P.prod ↔ ∀ p ∈ P, p v = v := by
  induction P with
  | nil => simp
  | cons p P ih =>
      rw [List.pairwise_cons] at hcomm
      have htail := fun q hq => hP q (List.mem_cons_of_mem p hq)
      have htailProj := projection_listProd P htail hcomm.2
      rw [(projection_listProd (p :: P) hP (List.pairwise_cons.mpr hcomm)).isIdempotentElem.mem_range_iff,
        List.prod_cons, fixed_mul_iff (hP p List.mem_cons_self).isIdempotentElem
          htailProj.isIdempotentElem (Commute.list_prod_right P p hcomm.1),
        ← htailProj.isIdempotentElem.mem_range_iff, ih htail hcomm.2]
      simp only [List.mem_cons, forall_eq_or_imp]

variable {d₀ d₁ r : ℕ} {D₀ D₁ : Fin r → ℕ}

private theorem binaryDiagonal_projection {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ι → ℂ) (hf : ∀ i, f i = 0 ∨ f i = 1) :
    (Matrix.toEuclideanLin (Matrix.diagonal f)).IsSymmetricProjection := by
  constructor
  · ext v i
    simp only [Module.End.mul_apply, Matrix.toEuclideanLin, Matrix.toLpLin_apply,
      Matrix.mulVec_diagonal]
    rcases hf i with h | h <;> simp [h]
  · apply Matrix.isSymmetric_toEuclideanLin_iff.mpr
    apply Matrix.isHermitian_diagonal_of_self_adjoint
    funext i
    simp only [Pi.star_apply]
    rcases hf i with h | h <;> simp [h]

/-- Left site matrix on a nonwrapping bond: the full joint frame at the
left endpoint, and the column-zero selector at every later site.
Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
def jointMixedOpenLeftMatrix
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x)) (n : ℕ) (i : Fin (n + 2)) :
    Matrix (Fin (jointMixedPhysicalDim d₀ d₁ D₀ D₁))
      (Fin (jointMixedPhysicalDim d₀ d₁ D₀ D₁)) ℂ :=
  if i = 0 then jointMixedFirstFrameProjectionMatrix A₀ A₁
    else Matrix.diagonal jointMixedColumnWeight

/-- Right site matrix on a nonwrapping bond: the full joint frame at the
right endpoint, and the row-zero selector at every earlier site.
Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
def jointMixedOpenRightMatrix
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x)) (n : ℕ) (i : Fin (n + 2)) :
    Matrix (Fin (jointMixedPhysicalDim d₀ d₁ D₀ D₁))
      (Fin (jointMixedPhysicalDim d₀ d₁ D₀ D₁)) ℂ :=
  if i = Fin.last (n + 1) then jointMixedLastFrameProjectionMatrix A₀ A₁
    else Matrix.diagonal jointMixedRowWeight

/-- A commuting product constraint on one bond of an open chain with
at least three sites. There are exactly \(n+1\) interior physical sites.
Source context: arXiv:2203.12563, Section 5, lines 1695–1777. -/
def jointMixedOpenBondProjection
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x)) (n : ℕ) (i : Fin (n + 2)) :=
  siteMatrixES (jointMixedOpenLeftMatrix A₀ A₁ n i) i.castSucc *
    siteMatrixES (jointMixedOpenRightMatrix A₀ A₁ n i) i.succ

private theorem leftMatrix_projection
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x)) (n : ℕ) (i : Fin (n + 2)) :
    (Matrix.toEuclideanLin (jointMixedOpenLeftMatrix A₀ A₁ n i)).IsSymmetricProjection := by
  unfold jointMixedOpenLeftMatrix
  split_ifs
  · rw [toEuclideanLin_jointMixedFirstFrameProjectionMatrix]
    exact Submodule.isSymmetricProjection_starProjection _
  · exact binaryDiagonal_projection _ jointMixedColumnWeight_eq_zero_or_one

private theorem rightMatrix_projection
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x)) (n : ℕ) (i : Fin (n + 2)) :
    (Matrix.toEuclideanLin (jointMixedOpenRightMatrix A₀ A₁ n i)).IsSymmetricProjection := by
  unfold jointMixedOpenRightMatrix
  split_ifs
  · rw [toEuclideanLin_jointMixedLastFrameProjectionMatrix]
    exact Submodule.isSymmetricProjection_starProjection _
  · exact binaryDiagonal_projection _ jointMixedRowWeight_eq_zero_or_one

private theorem castSucc_ne_succ {n : ℕ} (i : Fin (n + 2)) : i.castSucc ≠ i.succ := by
  intro h
  have := congrArg Fin.val h
  simp only [Fin.val_castSucc, Fin.val_succ] at this
  omega

private theorem left_left_commute
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x)) (n : ℕ) (i j : Fin (n + 2)) :
    Commute (siteMatrixES (jointMixedOpenLeftMatrix A₀ A₁ n i) i.castSucc)
      (siteMatrixES (jointMixedOpenLeftMatrix A₀ A₁ n j) j.castSucc) := by
  by_cases hij : i = j
  · subst j
    exact Commute.refl _
  · exact commute_siteMatrixES_of_ne _ _ (fun h => hij (Fin.castSucc_injective _ h))

private theorem right_right_commute
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x)) (n : ℕ) (i j : Fin (n + 2)) :
    Commute (siteMatrixES (jointMixedOpenRightMatrix A₀ A₁ n i) i.succ)
      (siteMatrixES (jointMixedOpenRightMatrix A₀ A₁ n j) j.succ) := by
  by_cases hij : i = j
  · subst j
    exact Commute.refl _
  · exact commute_siteMatrixES_of_ne _ _ (fun h => hij (Fin.succ_injective _ h))

private theorem left_right_commute
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x)) (n : ℕ) (i j : Fin (n + 2)) :
    Commute (siteMatrixES (jointMixedOpenLeftMatrix A₀ A₁ n i) i.castSucc)
      (siteMatrixES (jointMixedOpenRightMatrix A₀ A₁ n j) j.succ) := by
  by_cases hij : i.castSucc = j.succ
  · have hv : i.val = j.val + 1 := congrArg Fin.val hij
    have hi : i ≠ 0 := by intro hi; subst i; simp at hv
    have hj : j ≠ Fin.last (n + 1) := by
      intro hj
      subst j
      have := i.isLt
      simp only [Fin.val_last] at hv
      omega
    simp only [jointMixedOpenLeftMatrix, if_neg hi, jointMixedOpenRightMatrix,
      if_neg hj, siteMatrixES_diagonal]
    exact (jointMixedRowSector_commute_columnSector j.succ i.castSucc).symm
  · exact commute_siteMatrixES_of_ne _ _ hij

/-- The bond constraints commute because the only overlapping nontrivial
factors are row-zero and column-zero selectors on an interior site.
Source context: arXiv:2203.12563, Section 5, lines 1695–1777. -/
theorem jointMixedOpenBondProjection_commute
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x)) (n : ℕ) (i j : Fin (n + 2)) :
    Commute (jointMixedOpenBondProjection A₀ A₁ n i)
      (jointMixedOpenBondProjection A₀ A₁ n j) :=
  ((left_left_commute A₀ A₁ n i j).mul_right
    (left_right_commute A₀ A₁ n i j)).mul_left
      ((left_right_commute A₀ A₁ n j i).symm.mul_right
        (right_right_commute A₀ A₁ n i j))

/-- Every actual open bond constraint is an orthogonal projection.
Source context: arXiv:2203.12563, Section 5, lines 1695–1777. -/
theorem jointMixedOpenBondProjection_isSymmetricProjection
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x)) (n : ℕ) (i : Fin (n + 2)) :
    (jointMixedOpenBondProjection A₀ A₁ n i).IsSymmetricProjection :=
  (siteMatrixES_isSymmetricProjection i.castSucc (leftMatrix_projection A₀ A₁ n i)).mul_of_commute
    (siteMatrixES_isSymmetricProjection i.succ (rightMatrix_projection A₀ A₁ n i))
    (commute_siteMatrixES_of_ne _ _ (castSucc_ne_succ i))

/-- The active projection of the actual joint open chain. Its range has the
full joint polar boundary frames and the unchanged shared 00 alphabet in
the interior. No choice of orthogonal block labels is involved.
Source context: arXiv:2203.12563, Section 5, lines 1695–1777. -/
def jointMixedOpenActiveProjection
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x)) (n : ℕ) :=
  (List.ofFn (jointMixedOpenBondProjection A₀ A₁ n)).prod

private theorem bondList_pairwise
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x)) (n : ℕ) :
    (List.ofFn (jointMixedOpenBondProjection A₀ A₁ n)).Pairwise Commute := by
  rw [List.pairwise_ofFn]
  exact fun i j _ => jointMixedOpenBondProjection_commute A₀ A₁ n i j

private theorem bondList_projection
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x)) (n : ℕ) :
    ∀ P ∈ List.ofFn (jointMixedOpenBondProjection A₀ A₁ n), P.IsSymmetricProjection := by
  intro P hP
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hP
  exact jointMixedOpenBondProjection_isSymmetricProjection A₀ A₁ n i

/-- The product defining the active range is an orthogonal projection.
Source context: arXiv:2203.12563, Section 5, lines 1695–1777. -/
theorem jointMixedOpenActiveProjection_isSymmetricProjection
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x)) (n : ℕ) :
    (jointMixedOpenActiveProjection A₀ A₁ n).IsSymmetricProjection :=
  projection_listProd _ (bondList_projection A₀ A₁ n) (bondList_pairwise A₀ A₁ n)

/-- The active range is exactly the common fixed space of its actual
one-site boundary and inner-phase constraints.
Source context: arXiv:2203.12563, Section 5, lines 1695–1777. -/
theorem mem_range_jointMixedOpenActiveProjection_iff_bonds
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x)) (n : ℕ)
    (v : EuclideanSpace ℂ (Cfg (jointMixedPhysicalDim d₀ d₁ D₀ D₁) (n + 3))) :
    v ∈ LinearMap.range (jointMixedOpenActiveProjection A₀ A₁ n) ↔
      ∀ i : Fin (n + 2),
        siteMatrixES (jointMixedOpenLeftMatrix A₀ A₁ n i) i.castSucc v = v ∧
        siteMatrixES (jointMixedOpenRightMatrix A₀ A₁ n i) i.succ v = v := by
  rw [jointMixedOpenActiveProjection, mem_range_projection_listProd_iff _
    (bondList_projection A₀ A₁ n) (bondList_pairwise A₀ A₁ n)]
  simp only [List.mem_ofFn, forall_exists_index, forall_apply_eq_imp_iff]
  apply forall_congr'
  intro i
  exact fixed_mul_iff
    (siteMatrixES_isSymmetricProjection i.castSucc (leftMatrix_projection A₀ A₁ n i)).isIdempotentElem
    (siteMatrixES_isSymmetricProjection i.succ (rightMatrix_projection A₀ A₁ n i)).isIdempotentElem
    (commute_siteMatrixES_of_ne _ _ (castSucc_ne_succ i)) v

private theorem twoSite_kronecker_eq_finKronecker {d : ℕ}
    (M K : Matrix (Fin d) (Fin d) ℂ) :
    (M ⊗ₖ K).submatrix (finTwoArrowEquiv _) (finTwoArrowEquiv _) =
      Matrix.finKronecker ![M, K] := by
  ext σ τ
  simp [Matrix.finKronecker_apply, Fin.prod_univ_two, finTwoArrowEquiv_apply]

private theorem diagonal_finKronecker {d m : ℕ} (f : Fin m → Fin d → ℂ) :
    Matrix.finKronecker (fun k => Matrix.diagonal (f k)) =
      Matrix.diagonal (fun σ => ∏ k, f k (σ k)) := by
  ext σ τ
  simp only [Matrix.finKronecker_apply]
  by_cases h : σ = τ
  · subst τ
    simp
  · obtain ⟨k, hk⟩ := Function.ne_iff.mp h
    rw [Matrix.diagonal_apply_ne _ h]
    exact Finset.prod_eq_zero (Finset.mem_univ k) (Matrix.diagonal_apply_ne _ hk)

private theorem innerProjection_eq_finKronecker :
    jointMixedTwoSiteInnerProjection d₀ d₁ D₀ D₁ =
      Matrix.toEuclideanLin (Matrix.finKronecker
        ![Matrix.diagonal (jointMixedColumnWeight (d₀ := d₀) (d₁ := d₁)
            (D₀ := D₀) (D₁ := D₁)), Matrix.diagonal jointMixedRowWeight]) := by
  have hdiag :
      Matrix.finKronecker
        ![Matrix.diagonal (jointMixedColumnWeight (d₀ := d₀) (d₁ := d₁)
            (D₀ := D₀) (D₁ := D₁)), Matrix.diagonal jointMixedRowWeight] =
        Matrix.diagonal (fun σ => jointMixedColumnWeight (σ 0) * jointMixedRowWeight (σ 1)) := by
    convert diagonal_finKronecker ![jointMixedColumnWeight, jointMixedRowWeight] using 1
    · congr 1
      funext k
      fin_cases k <;> rfl
    · simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [hdiag]
  unfold jointMixedTwoSiteInnerProjection jointMixedColumnSector jointMixedRowSector
  rw [Matrix.toEuclideanLin, Matrix.toEuclideanLin, Matrix.toEuclideanLin,
    ← Matrix.toLpLin_mul_same, Matrix.diagonal_mul_diagonal]
  rfl

private theorem cyclicForwardSite_castSucc_one {n : ℕ} (i : Fin (n + 2)) :
    cyclicForwardSite i.castSucc 1 = i.succ := by
  apply Fin.ext
  simp only [cyclicForwardSite, Fin.val_castSucc, Fin.val_succ]
  exact Nat.mod_eq_of_lt (by have := i.isLt; omega)

private theorem bondProjection_eq_periodicLocal
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x)) (n : ℕ) (i : Fin (n + 2)) :
    jointMixedOpenBondProjection A₀ A₁ n i = periodicLocalInteractionES
      (Matrix.toEuclideanLin (Matrix.finKronecker
        ![jointMixedOpenLeftMatrix A₀ A₁ n i, jointMixedOpenRightMatrix A₀ A₁ n i]))
          i.castSucc := by
  rw [periodicLocalInteractionES_twoSite_product (by omega),
    cyclicForwardSite_castSucc_one]
  rfl

private theorem one_sub_localBondProjection_le
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x)) (n : ℕ) (i : Fin (n + 2)) :
    1 - Matrix.toEuclideanLin (Matrix.finKronecker
      ![jointMixedOpenLeftMatrix A₀ A₁ n i, jointMixedOpenRightMatrix A₀ A₁ n i]) ≤
        (jointMixedEndpointParentInteraction A₀ A₁ 0).toLinearMap := by
  by_cases hi : i = 0
  · have hiLast : i ≠ Fin.last (n + 1) := by
      intro h
      have := congrArg Fin.val (hi.symm.trans h)
      simp at this
    simpa only [jointMixedOpenLeftMatrix, if_pos hi, jointMixedOpenRightMatrix,
      if_neg hiLast, jointMixedFirstOneSidedProjection,
      twoSite_kronecker_eq_finKronecker] using
      one_sub_jointMixedFirstOneSidedProjection_le_parentInteraction A₀ A₁
  · by_cases hiLast : i = Fin.last (n + 1)
    · simpa only [jointMixedOpenLeftMatrix, if_neg hi, jointMixedOpenRightMatrix,
        if_pos hiLast, jointMixedLastOneSidedProjection,
        twoSite_kronecker_eq_finKronecker] using
        one_sub_jointMixedLastOneSidedProjection_le_parentInteraction A₀ A₁
    · simpa only [jointMixedOpenLeftMatrix, if_neg hi, jointMixedOpenRightMatrix,
        if_neg hiLast, innerProjection_eq_finKronecker] using
        one_sub_jointMixedTwoSiteInnerProjection_le_parentInteraction A₀ A₁

/-- Each bond's complementary active constraint is charged to that actual
local interaction exactly once, including the two distinct boundary bonds.
Source context: arXiv:2203.12563, Section 5, lines 1695–1777. -/
theorem one_sub_jointMixedOpenBondProjection_le_localInteraction
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x)) (n : ℕ) (i : Fin (n + 2)) :
    1 - jointMixedOpenBondProjection A₀ A₁ n i ≤
      periodicLocalInteractionES
        (jointMixedEndpointParentInteraction A₀ A₁ 0).toLinearMap i.castSucc := by
  have h := periodicLocalInteractionES_mono (one_sub_localBondProjection_le A₀ A₁ n i)
    i.castSucc
  simpa only [periodicLocalInteractionES_sub, periodicLocalInteractionES_one (by omega),
    ← bondProjection_eq_periodicLocal] using h

private def openBondIndexEquiv (n : ℕ) : Fin (n + 2) ≃ NonwrappingStart 2 (n + 3) where
  toFun i := ⟨i.castSucc, by have := i.isLt; simp only [Fin.val_castSucc]; omega⟩
  invFun i := ⟨i.1.val, by have := i.2; omega⟩
  left_inv i := by apply Fin.ext; rfl
  right_inv i := by apply Subtype.ext; apply Fin.ext; rfl

private theorem openInteractionHamiltonian_eq_sum_bonds
    (h : EuclideanSpace ℂ (Cfg (jointMixedPhysicalDim d₀ d₁ D₀ D₁) 2) →ₗ[ℂ]
      EuclideanSpace ℂ (Cfg (jointMixedPhysicalDim d₀ d₁ D₀ D₁) 2)) (n : ℕ) :
    openInteractionHamiltonianES h (n + 3) =
      ∑ i : Fin (n + 2), periodicLocalInteractionES h i.castSucc := by
  unfold openInteractionHamiltonianES
  exact (Fintype.sum_equiv (openBondIndexEquiv n) _ _ (fun _ => rfl)).symm

/-- The actual open Hamiltonian controls the entire complement of the
derived active projection with coefficient one. This auxiliary bound
implies the coefficient-two estimate used in reducing-projection gap
transfer, but asserts no spectral gap inside the active range.
Source context: arXiv:2203.12563, Section 5, lines 1695–1777. -/
theorem one_sub_jointMixedOpenActiveProjection_le_openInteraction
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x)) (n : ℕ) :
    1 - jointMixedOpenActiveProjection A₀ A₁ n ≤
      openInteractionHamiltonianES
        (jointMixedEndpointParentInteraction A₀ A₁ 0).toLinearMap (n + 3) := by
  have h := one_sub_projection_listProd_le _
    (bondList_projection A₀ A₁ n) (bondList_pairwise A₀ A₁ n)
  simp only [List.map_ofFn, List.sum_ofFn, Function.comp_def] at h
  rw [openInteractionHamiltonian_eq_sum_bonds]
  exact h.trans (Finset.sum_le_sum fun i _ =>
    one_sub_jointMixedOpenBondProjection_le_localInteraction A₀ A₁ n i)

private theorem siteMatrixES_one {d m : ℕ} (k : Fin m) :
    siteMatrixES (1 : Matrix (Fin d) (Fin d) ℂ) k = 1 := by
  simp only [siteMatrixES, Pi.mulSingle_one, Matrix.finKronecker_one,
    Matrix.toEuclideanLin, Matrix.toLpLin_one]

private theorem commute_periodicLocal_of_commute {d m : ℕ}
    {P H : EuclideanSpace ℂ (Cfg d 2) →ₗ[ℂ] EuclideanSpace ℂ (Cfg d 2)}
    (hPH : Commute P H) (i : Fin m) :
    Commute (periodicLocalInteractionES P i) (periodicLocalInteractionES H i) := by
  apply (commute_iff_eq _ _).mpr
  rw [← periodicLocalInteractionES_mul, hPH.eq, periodicLocalInteractionES_mul]

private theorem firstFrame_commute_local
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x)) (n : ℕ) (j : Fin (n + 2)) :
    Commute (siteMatrixES (jointMixedFirstFrameProjectionMatrix A₀ A₁) (0 : Fin (n + 3)))
      (periodicLocalInteractionES
        (jointMixedEndpointParentInteraction A₀ A₁ 0).toLinearMap j.castSucc) := by
  by_cases hj : j = 0
  · subst j
    have h := commute_periodicLocal_of_commute
      (jointMixedFirstFrameAtZeroProjection_commute_parentInteraction A₀ A₁)
        (0 : Fin (n + 3))
    simpa only [jointMixedFirstFrameAtZeroProjection, twoSite_kronecker_eq_finKronecker,
      periodicLocalInteractionES_twoSite_product (by omega), siteMatrixES_one, mul_one] using h
  · apply commute_siteMatrixES_periodicLocalInteractionES_of_notMem _ (by omega)
    intro q hq
    have hval := congrArg Fin.val hq
    have hmod : (j.val + q.val) % (n + 3) = j.val + q.val :=
      Nat.mod_eq_of_lt (by have := j.isLt; have := q.isLt; omega)
    simp only [cyclicForwardSite, Fin.val_castSucc, Fin.val_zero, hmod] at hval
    have hjpos : 0 < j.val := by
      have hne : j.val ≠ 0 := fun h => hj (Fin.ext h)
      omega
    omega

private theorem lastFrame_commute_local
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x)) (n : ℕ) (j : Fin (n + 2)) :
    Commute (siteMatrixES (jointMixedLastFrameProjectionMatrix A₀ A₁)
      (Fin.last (n + 2)))
      (periodicLocalInteractionES
        (jointMixedEndpointParentInteraction A₀ A₁ 0).toLinearMap j.castSucc) := by
  by_cases hj : j = Fin.last (n + 1)
  · subst j
    have h := commute_periodicLocal_of_commute
      (jointMixedLastFrameAtOneProjection_commute_parentInteraction A₀ A₁)
        (Fin.last (n + 1)).castSucc
    simpa only [jointMixedLastFrameAtOneProjection, twoSite_kronecker_eq_finKronecker,
      periodicLocalInteractionES_twoSite_product (by omega), siteMatrixES_one, one_mul,
      cyclicForwardSite_castSucc_one, Fin.succ_last] using h
  · apply commute_siteMatrixES_periodicLocalInteractionES_of_notMem _ (by omega)
    intro q hq
    have hval := congrArg Fin.val hq
    have hmod : (j.val + q.val) % (n + 3) = j.val + q.val :=
      Nat.mod_eq_of_lt (by have := j.isLt; have := q.isLt; omega)
    simp only [cyclicForwardSite, Fin.val_castSucc, Fin.val_last, hmod] at hval
    have hjlt : j.val < n + 1 := by
      have hne : j.val ≠ n + 1 := fun h => hj (Fin.ext h)
      have := j.isLt
      omega
    have := q.isLt
    omega

private theorem leftConstraint_commute_local
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x)) (n : ℕ) (i j : Fin (n + 2)) :
    Commute (siteMatrixES (jointMixedOpenLeftMatrix A₀ A₁ n i) i.castSucc)
      (periodicLocalInteractionES
        (jointMixedEndpointParentInteraction A₀ A₁ 0).toLinearMap j.castSucc) := by
  by_cases hi : i = 0
  · subst i
    simpa only [jointMixedOpenLeftMatrix, if_pos rfl, Fin.castSucc_zero] using
      firstFrame_commute_local A₀ A₁ n j
  · simp only [jointMixedOpenLeftMatrix, if_neg hi, siteMatrixES_diagonal]
    exact jointMixedColumnSector_commute_periodicLocalInteraction_zero A₀ A₁
      (by omega) j.castSucc i.castSucc

private theorem rightConstraint_commute_local
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x)) (n : ℕ) (i j : Fin (n + 2)) :
    Commute (siteMatrixES (jointMixedOpenRightMatrix A₀ A₁ n i) i.succ)
      (periodicLocalInteractionES
        (jointMixedEndpointParentInteraction A₀ A₁ 0).toLinearMap j.castSucc) := by
  by_cases hi : i = Fin.last (n + 1)
  · subst i
    simpa only [jointMixedOpenRightMatrix, if_pos rfl, Fin.succ_last] using
      lastFrame_commute_local A₀ A₁ n j
  · simp only [jointMixedOpenRightMatrix, if_neg hi, siteMatrixES_diagonal]
    exact jointMixedRowSector_commute_periodicLocalInteraction_zero A₀ A₁
      (by omega) j.castSucc i.succ

/-- Each active bond constraint reduces every actual open-chain term.
The full boundary frames meet only their own boundary terms; elsewhere
the derived inner phase commutators or disjoint support apply.
Source context: arXiv:2203.12563, Section 5, lines 1695–1777. -/
theorem jointMixedOpenBondProjection_commute_localInteraction
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x)) (n : ℕ) (i j : Fin (n + 2)) :
    Commute (jointMixedOpenBondProjection A₀ A₁ n i)
      (periodicLocalInteractionES
        (jointMixedEndpointParentInteraction A₀ A₁ 0).toLinearMap j.castSucc) :=
  (leftConstraint_commute_local A₀ A₁ n i j).mul_left
    (rightConstraint_commute_local A₀ A₁ n i j)

/-- The explicitly derived active projection reduces the actual open
zero-parameter interaction. The commutator is a conclusion, not a premise.
Source context: arXiv:2203.12563, Section 5, lines 1695–1777. -/
theorem jointMixedOpenActiveProjection_commute_openInteraction
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x)) (n : ℕ) :
    Commute (jointMixedOpenActiveProjection A₀ A₁ n)
      (openInteractionHamiltonianES
        (jointMixedEndpointParentInteraction A₀ A₁ 0).toLinearMap (n + 3)) := by
  rw [openInteractionHamiltonian_eq_sum_bonds]
  apply Commute.sum_right
  intro j _
  apply Commute.list_prod_left
  intro P hP
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hP
  exact jointMixedOpenBondProjection_commute_localInteraction A₀ A₁ n i j

/-- The requested coefficient-two inactive penalty follows from the
stronger coefficient-one bound and positivity of the actual Hamiltonian.
Source context: arXiv:2203.12563, Section 5, lines 1695–1777. -/
theorem one_sub_jointMixedOpenActiveProjection_le_twice_openInteraction
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x)) (n : ℕ) :
    1 - jointMixedOpenActiveProjection A₀ A₁ n ≤
      (2 : ℂ) • openInteractionHamiltonianES
        (jointMixedEndpointParentInteraction A₀ A₁ 0).toLinearMap (n + 3) := by
  have hH : 0 ≤ openInteractionHamiltonianES
      (jointMixedEndpointParentInteraction A₀ A₁ 0).toLinearMap (n + 3) := by
    apply Finset.sum_nonneg
    intro i _
    exact LinearMap.nonneg_iff_isPositive.mpr
      (periodicLocalInteractionES_isPositive
        (jointMixedEndpointParentInteraction_isPositive A₀ A₁ 0) i.1)
  rw [two_smul]
  exact (one_sub_jointMixedOpenActiveProjection_le_openInteraction A₀ A₁ n).trans
    (le_add_of_nonneg_right hH)

end

end MPSTensor.MPOSymmetry
