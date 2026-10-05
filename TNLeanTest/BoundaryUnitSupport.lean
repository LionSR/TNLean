/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.BoundaryUnitSupport

/-!
# Boundary-unit support regression tests

The calibration length need not be one or smaller than the target length.
There are no nonzero-dimension assumptions. A bond-two idempotent MPO with
identity boundary fixes an injective scalar MPS at all positive lengths but
multiplies its empty-chain vector by two, so the positive-length restriction
cannot be dropped.
-/

set_option linter.hashCommand false

open scoped Matrix BigOperators

namespace BoundaryUnitSupportTest

variable {d D₁ D₂ n : ℕ}

-- The target may be shorter than the length at which injectivity and the unit are known.
example (T : MPOTensor d D₁) (A : MPSTensor d D₂)
    (h : MPOTensor.IsBoundaryCompatible T A) (hInj : Kraus.IsNBlkInjective A 3)
    (U : Matrix (Fin D₁) (Fin D₁) ℂ) (hU : MPOTensor.mpoWithBoundary T U 3 = 1)
    (X : Matrix (Fin D₂) (Fin D₂) ℂ) :
    MPOTensor.mpoWithBoundary T U 1 *ᵥ MPSTensor.mpvWithBoundary A X =
      (MPSTensor.mpvWithBoundary A X : (Fin 1 → Fin d) → ℂ) :=
  h.mpoWithBoundary_mulVec_eq_of_one_length_eq_one hInj (by omega) hU X Nat.one_pos

-- Zero state-bond dimension is allowed; its matrix algebra and boundary space are trivial.
example (T : MPOTensor d D₁) (A : MPSTensor d 0)
    (h : MPOTensor.IsBoundaryCompatible T A)
    (U : Matrix (Fin D₁) (Fin D₁) ℂ) (hU : MPOTensor.mpoWithBoundary T U 1 = 1)
    (X : Matrix (Fin 0) (Fin 0) ℂ) (hn : 0 < n) :
    MPOTensor.mpoWithBoundary T U n *ᵥ MPSTensor.mpvWithBoundary A X =
      (MPSTensor.mpvWithBoundary A X : (Fin n → Fin d) → ℂ) := by
  have hInj : Kraus.IsInjective A := Subsingleton.elim _ _
  exact h.mpoWithBoundary_mulVec_eq_of_one_site_eq_one hInj hU X hn

-- Physical and both virtual dimensions can simultaneously be zero.
example (T : MPOTensor 0 0) (A : MPSTensor 0 0) (hn : 0 < n) :
    MPOTensor.mpoWithBoundary T 0 n *ᵥ MPSTensor.mpvWithBoundary A 0 =
      (MPSTensor.mpvWithBoundary A 0 : (Fin n → Fin 0) → ℂ) := by
  have h : MPOTensor.IsBoundaryCompatible T A := by
    intro U X
    refine ⟨X, fun k hk ↦ ?_⟩
    funext σ
    exact Fin.elim0 (σ ⟨0, hk⟩)
  have hU : MPOTensor.mpoWithBoundary T 0 1 = 1 := by
    ext σ τ
    exact Fin.elim0 (σ 0)
  have hInj : Kraus.IsInjective A := Subsingleton.elim _ _
  exact h.mpoWithBoundary_mulVec_eq_of_one_site_eq_one hInj hU 0 hn

private def scalarMPS : MPSTensor 1 1 := fun _ ↦ 1

private theorem scalarMPS_isInjective : Kraus.IsInjective scalarMPS := by
  rw [Kraus.IsInjective]
  apply top_unique
  intro X _
  have hOne : (1 : Matrix (Fin 1) (Fin 1) ℂ) ∈
      Submodule.span ℂ (Set.range scalarMPS) :=
    Submodule.subset_span ⟨0, rfl⟩
  have hX : X = X 0 0 • (1 : Matrix (Fin 1) (Fin 1) ℂ) := by
    ext i j
    fin_cases i
    fin_cases j
    simp
  rw [hX]
  exact Submodule.smul_mem _ _ hOne

private def cornerMPO : MPOTensor 1 2 := fun _ _ ↦ Matrix.single 0 0 1

private theorem cornerMPO_evalWord_pos {k : ℕ} (hk : 0 < k)
    (σ τ : Fin k → Fin 1) :
    MPOTensor.evalWord cornerMPO (List.ofFn σ) (List.ofFn τ) =
      Matrix.single 0 0 1 := by
  cases k with
  | zero => omega
  | succ k =>
      induction k with
      | zero => simp [List.ofFn_succ, cornerMPO]
      | succ k ih =>
          rw [List.ofFn_succ (f := σ), List.ofFn_succ (f := τ), MPOTensor.evalWord_cons,
            ih (by omega) (fun i ↦ σ i.succ) (fun i ↦ τ i.succ)]
          simp [cornerMPO]

private theorem cornerMPO_boundary_pos (U : Matrix (Fin 2) (Fin 2) ℂ)
    {k : ℕ} (hk : 0 < k) :
    MPOTensor.mpoWithBoundary cornerMPO U k = U 0 0 • 1 := by
  ext σ τ
  have hστ : σ = τ := Subsingleton.elim _ _
  subst τ
  simp [MPOTensor.mpoWithBoundary, cornerMPO_evalWord_pos hk, Matrix.trace_mul_single]

private theorem cornerMPO_compatible : MPOTensor.IsBoundaryCompatible cornerMPO scalarMPS := by
  intro U X
  refine ⟨U 0 0 • X, fun k hk ↦ ?_⟩
  rw [cornerMPO_boundary_pos U hk]
  simp only [Matrix.smul_mulVec, Matrix.one_mulVec,
    MPSTensor.mpvWithBoundary_eq_groundSpaceMap, map_smul]

private theorem cornerMPO_one_site : MPOTensor.mpoWithBoundary cornerMPO 1 1 = 1 := by
  rw [cornerMPO_boundary_pos 1 Nat.one_pos]
  simp

-- The fixed-action conclusion is obtained from compatibility and a single-site unit.
example (X : Matrix (Fin 1) (Fin 1) ℂ) (hn : 0 < n) :
    MPOTensor.mpoWithBoundary cornerMPO 1 n *ᵥ MPSTensor.mpvWithBoundary scalarMPS X =
      (MPSTensor.mpvWithBoundary scalarMPS X : (Fin n → Fin 1) → ℂ) :=
  cornerMPO_compatible.mpoWithBoundary_mulVec_eq_of_one_site_eq_one
    scalarMPS_isInjective cornerMPO_one_site X hn

attribute [local instance] MPSTensor.groundSpaceES_hasOrthogonalProjection

-- The projection is the existing canonical ground-space projection, not an supplied variable.
example (hn : 0 < n) :
    Matrix.toEuclideanLin (MPOTensor.mpoWithBoundary cornerMPO 1 n) ∘ₗ
        (MPSTensor.groundSpaceES scalarMPS n).starProjection.toLinearMap =
      (MPSTensor.groundSpaceES scalarMPS n).starProjection.toLinearMap :=
  cornerMPO_compatible.toEuclideanLin_comp_groundSpaceES_starProjection_of_one_site
    scalarMPS_isInjective cornerMPO_one_site hn

-- At length zero the same MPO boundary has trace two, while the scalar state is nonzero.
example :
    MPOTensor.mpoWithBoundary cornerMPO 1 0 *ᵥ MPSTensor.mpvWithBoundary scalarMPS 1 ≠
      (MPSTensor.mpvWithBoundary scalarMPS 1 : (Fin 0 → Fin 1) → ℂ) := by
  intro h
  have hh := congrFun h (fun i ↦ Fin.elim0 i)
  norm_num [MPOTensor.mpoWithBoundary, MPSTensor.mpvWithBoundary, MPSTensor.mpv,
    MPSTensor.coeff, Matrix.mulVec, dotProduct, Matrix.trace, Fin.sum_univ_two] at hh

end BoundaryUnitSupportTest

/-- info: 'MPOTensor.IsBoundaryCompatible.mpoWithBoundary_mulVec_eq_of_one_length_eq_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MPOTensor.IsBoundaryCompatible.mpoWithBoundary_mulVec_eq_of_one_length_eq_one

/-- info: 'MPOTensor.IsBoundaryCompatible.mpoWithBoundary_mulVec_eq_of_one_site_eq_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MPOTensor.IsBoundaryCompatible.mpoWithBoundary_mulVec_eq_of_one_site_eq_one

/-- info: 'MPOTensor.IsBoundaryCompatible.toEuclideanLin_comp_groundSpaceES_starProjection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MPOTensor.IsBoundaryCompatible.toEuclideanLin_comp_groundSpaceES_starProjection

/-- info: 'MPOTensor.IsBoundaryCompatible.toEuclideanLin_comp_groundSpaceES_starProjection_of_one_site' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  MPOTensor.IsBoundaryCompatible.toEuclideanLin_comp_groundSpaceES_starProjection_of_one_site
