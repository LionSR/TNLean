/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Examples.ControlledZCombinedReductions
import TNLean.MPS.Symmetry.MPOSymmetry.LSymbolComputation
import TNLean.MPS.Symmetry.MPOSymmetry.SingleBlockLSymbolGauge

/-!
# Relative action L-symbols of the controlled-Z state

The two action trees are calculated with the explicit reductions of the combined family.
The reference product state has trivial L-symbol. The bond-three state's L-symbol differs
from the cluster factor system by a coboundary, giving its nontrivial relative class.
This is the action-tensor comparison needed after the split-index calculation in
arXiv:2502.20257, line 3970. Physical path invariance is a separate assertion.
-/

noncomputable section

open scoped Matrix Kronecker BigOperators
open MPOTensor MPOTensor.GroupFamily MPSTensor TNLean.Algebra

namespace ControlledZGauging

private def rationalAssocInv (m n k : ℕ) :
    Matrix (Fin (m * (n * k))) (Fin (m * n * k)) ℚ :=
  (finCongr (mul_assoc m n k).symm).toPEquiv.toMatrix

private theorem complexOfRing_rationalAssocInv (m n k : ℕ) :
    complexOfRing (Rat.castHom ℂ) (rationalAssocInv m n k) =
      mulTensorAssocInvMatrix m n k := by
  rw [mulTensorAssocInvMatrix_eq_finCongr]
  ext i j
  simp only [rationalAssocInv, complexOfRing_apply, PEquiv.toMatrix_apply]
  split_ifs <;> norm_num

private def rationalFusionV (g h : Multiplicative (ZMod 2 × ZMod 2)) :
    Matrix (Fin (combinedFamily.bondDim (g * h)))
      (Fin (combinedFamily.bondDim g * combinedFamily.bondDim h)) ℚ :=
  combinedFusionV g.toAdd.2 h.toAdd.2

/-- The rational action tree: act by the second element, then by the first. -/
def combinedRationalActTree {D : ℕ}
    (V : (g : Multiplicative (ZMod 2 × ZMod 2)) →
      Matrix (Fin D) (Fin (combinedFamily.bondDim g * D)) ℚ)
    (g h : Multiplicative (ZMod 2 × ZMod 2)) :=
  V g * (((1 : Matrix (Fin (combinedFamily.bondDim g))
    (Fin (combinedFamily.bondDim g)) ℚ) ⊗ₖ V h).submatrix
      finProdFinEquiv.symm finProdFinEquiv.symm) *
    rationalAssocInv (combinedFamily.bondDim g) (combinedFamily.bondDim h) D

set_option backward.isDefEq.respectTransparency false in
/-- The rational fusion-then-action tree. -/
def combinedRationalFuseTree {D : ℕ}
    (V : (g : Multiplicative (ZMod 2 × ZMod 2)) →
      Matrix (Fin D) (Fin (combinedFamily.bondDim g * D)) ℚ)
    (g h : Multiplicative (ZMod 2 × ZMod 2)) :=
  V (g * h) * ((rationalFusionV g h ⊗ₖ
    (1 : Matrix (Fin D) (Fin D) ℚ)).submatrix
      finProdFinEquiv.symm finProdFinEquiv.symm)

/-- The rational two-operator action on a state, in the same bond order as the trees. -/
def combinedRationalDoubleAction {D : ℕ} (g h : Multiplicative (ZMod 2 × ZMod 2))
    (A : Fin 2 → Matrix (Fin D) (Fin D) ℚ) (i : Fin 2) :
    Matrix (Fin (combinedFamily.bondDim g * combinedFamily.bondDim h * D))
      (Fin (combinedFamily.bondDim g * combinedFamily.bondDim h * D)) ℚ :=
  (∑ j, combinedRationalProduct g h i j ⊗ₖ A j).submatrix
    finProdFinEquiv.symm finProdFinEquiv.symm

/-- The scalar of the bond-three action trees for the chosen reductions. -/
def combinedStateLValue (g h : Multiplicative (ZMod 2 × ZMod 2)) : ℚ :=
  (-1) ^ (g.toAdd.1.val * h.toAdd.2.val) * 4 ^ (g.toAdd.2.val * h.toAdd.2.val)

set_option backward.isDefEq.respectTransparency false in
private theorem complexOfRing_combinedRationalDoubleAction {D : ℕ}
    (g h : Multiplicative (ZMod 2 × ZMod 2))
    (A : Fin 2 → Matrix (Fin D) (Fin D) ℚ) (i : Fin 2) :
    complexOfRing (Rat.castHom ℂ) (combinedRationalDoubleAction g h A i) =
      actTensor (mulTensor (combinedFamily.tensor g) (combinedFamily.tensor h))
        (fun j ↦ complexOfRing (Rat.castHom ℂ) (A j)) i := by
  simp only [combinedRationalDoubleAction, actTensor_apply, complexOfRing_submatrix,
    complexOfRing_sum, complexOfRing_kronecker, complexOfRing_combinedRationalProduct]

private theorem complexOfRing_combinedRationalActTree {D : ℕ} {A : MPSTensor 2 D}
    (ad : ActionData combinedFamily A)
    (V : (g : Multiplicative (ZMod 2 × ZMod 2)) →
      Matrix (Fin D) (Fin (combinedFamily.bondDim g * D)) ℚ)
    (hV : ∀ g, complexOfRing (Rat.castHom ℂ) (V g) = ad.V g)
    (g h : Multiplicative (ZMod 2 × ZMod 2)) :
    complexOfRing (Rat.castHom ℂ) (combinedRationalActTree V g h) = ad.actV g h := by
  simp only [combinedRationalActTree, ActionData.actV, complexOfRing_mul]
  rw [← idKron_complexOfRing, complexOfRing_rationalAssocInv, hV, hV]

private theorem complexOfRing_combinedRationalFuseTree {D : ℕ} {A : MPSTensor 2 D}
    (ad : ActionData combinedFamily A)
    (V : (g : Multiplicative (ZMod 2 × ZMod 2)) →
      Matrix (Fin D) (Fin (combinedFamily.bondDim g * D)) ℚ)
    (hV : ∀ g, complexOfRing (Rat.castHom ℂ) (V g) = ad.V g)
    (g h : Multiplicative (ZMod 2 × ZMod 2)) :
    complexOfRing (Rat.castHom ℂ) (combinedRationalFuseTree V g h) =
      ad.fuseV combinedFusionData g h := by
  simp only [combinedRationalFuseTree, ActionData.fuseV, complexOfRing_mul]
  rw [← kronId_complexOfRing, hV]
  rfl

private theorem combinedState_tree_local : ∀ g h : Multiplicative (ZMod 2 × ZMod 2),
    let V : (g : Multiplicative (ZMod 2 × ZMod 2)) →
      Matrix (Fin 3) (Fin (combinedFamily.bondDim g * 3)) ℚ :=
        fun g ↦ combinedStateV g.toAdd.1 g.toAdd.2
    ∀ i, combinedRationalActTree V g h * combinedRationalDoubleAction g h stateRational i =
      combinedStateLValue g h • (combinedRationalFuseTree V g h *
        combinedRationalDoubleAction g h stateRational i) := by
  refine Multiplicative.forall_zmod_two_prod ?_ ?_ ?_ ?_
  all_goals refine Multiplicative.forall_zmod_two_prod ?_ ?_ ?_ ?_ <;> decide +kernel

private theorem combinedZero_tree_local : ∀ g h : Multiplicative (ZMod 2 × ZMod 2),
    let V : (g : Multiplicative (ZMod 2 × ZMod 2)) →
      Matrix (Fin 1) (Fin (combinedFamily.bondDim g * 1)) ℚ :=
        fun g ↦ combinedZeroV g.toAdd.2
    ∀ i, combinedRationalActTree V g h * combinedRationalDoubleAction g h zeroRational i =
      combinedRationalFuseTree V g h * combinedRationalDoubleAction g h zeroRational i := by
  refine Multiplicative.forall_zmod_two_prod ?_ ?_ ?_ ?_
  all_goals refine Multiplicative.forall_zmod_two_prod ?_ ?_ ?_ ?_ <;> decide +kernel

/-- The actual action L-symbol of the bond-three state, for the displayed reductions. -/
theorem combinedStateActionData_lSymbol (g h : Multiplicative (ZMod 2 × ZMod 2)) :
    (combinedStateActionData.lSymbol combinedFusionData () g h : ℂ) =
      (combinedStateLValue g h : ℂ) := by
  symm
  apply ActionData.eq_lSymbol_of_isDressedProportional combinedFusionData
    combinedStateActionData stateTensor_isNormal (by decide)
    fixesMPV_combinedFamily_stateTensor g h
  let V : (g : Multiplicative (ZMod 2 × ZMod 2)) →
      Matrix (Fin 3) (Fin (combinedFamily.bondDim g * 3)) ℚ :=
    fun g ↦ combinedStateV g.toAdd.1 g.toAdd.2
  have hz := isDressedProportional_complexOfRing_of_forall_mul (Rat.castHom ℂ)
    (combinedRationalDoubleAction g h stateRational)
    (combinedRationalActTree V g h) (combinedRationalFuseTree V g h)
    (combinedStateLValue g h) (combinedState_tree_local g h)
  rw [complexOfRing_combinedRationalActTree combinedStateActionData V (fun _ ↦ rfl),
    complexOfRing_combinedRationalFuseTree combinedStateActionData V (fun _ ↦ rfl)] at hz
  simp only [complexOfRing_combinedRationalDoubleAction, complexOfRing_stateRational] at hz
  convert hz using 1
  rfl

/-- The same fusion data give L-symbol one for the invariant reference product state. -/
theorem combinedZeroActionData_lSymbol (g h : Multiplicative (ZMod 2 × ZMod 2)) :
    (combinedZeroActionData.lSymbol combinedFusionData () g h : ℂ) = 1 := by
  symm
  apply ActionData.eq_lSymbol_of_isDressedProportional combinedFusionData
    combinedZeroActionData zeroState_isNormal one_pos fixesMPV_combinedFamily_zeroState g h
  let V : (g : Multiplicative (ZMod 2 × ZMod 2)) →
      Matrix (Fin 1) (Fin (combinedFamily.bondDim g * 1)) ℚ :=
    fun g ↦ combinedZeroV g.toAdd.2
  have h1 : ∀ i, combinedRationalActTree V g h *
      combinedRationalDoubleAction g h zeroRational i =
      (1 : ℚ) • (combinedRationalFuseTree V g h *
        combinedRationalDoubleAction g h zeroRational i) := by
    simpa only [one_smul] using combinedZero_tree_local g h
  have hz := isDressedProportional_complexOfRing_of_forall_mul (Rat.castHom ℂ)
    (combinedRationalDoubleAction g h zeroRational)
    (combinedRationalActTree V g h) (combinedRationalFuseTree V g h) 1 h1
  rw [complexOfRing_combinedRationalActTree combinedZeroActionData V (fun _ ↦ rfl),
    complexOfRing_combinedRationalFuseTree combinedZeroActionData V (fun _ ↦ rfl)] at hz
  simp only [map_one, complexOfRing_combinedRationalDoubleAction,
    complexOfRing_zeroRational] at hz
  convert hz using 1

open scoped TNLean.Algebra.ScalarCohomology

/-- The relative factor system of the two invariant states for the displayed action data. -/
def combinedRelativeCocycle : ScalarCocycle (Multiplicative (ZMod 2 × ZMod 2)) :=
  fun p ↦ (-1) ^ (p.1.toAdd.1.val * p.2.toAdd.2.val) *
    (Units.mk0 (4 : ℂ) (by norm_num)) ^ (p.1.toAdd.2.val * p.2.toAdd.2.val)

private theorem combinedRelativeCocycle_val (g h : Multiplicative (ZMod 2 × ZMod 2)) :
    (combinedRelativeCocycle (g, h) : ℂ) = (combinedStateLValue g h : ℂ) := by
  simp [combinedRelativeCocycle, combinedStateLValue]

/-- The computed factor system is the ratio of the actual two action L-symbols. -/
theorem combinedRelativeCocycle_eq_lSymbol_div (g h : Multiplicative (ZMod 2 × ZMod 2)) :
    combinedRelativeCocycle (g, h) =
      combinedStateActionData.lSymbol combinedFusionData () g h /
        combinedZeroActionData.lSymbol combinedFusionData () g h := by
  apply Units.ext
  rw [Units.val_div_eq_div_val, combinedStateActionData_lSymbol,
    combinedZeroActionData_lSymbol, div_one, combinedRelativeCocycle_val]

/-- The one-cochain removing the normalization and transpose of the cluster factor system. -/
def combinedLClassGauge (g : Multiplicative (ZMod 2 × ZMod 2)) : ℂˣ :=
  (-1) ^ (g.toAdd.1.val * g.toAdd.2.val) *
    (Units.mk0 (2 : ℂ) (by norm_num)) ^ g.toAdd.2.val

set_option backward.isDefEq.respectTransparency false in
/-- The actual relative action factor system and the cluster factor system are cohomologous. -/
theorem combinedRelativeCocycle_div_cluster_isMulCoboundary :
    groupCohomology.IsMulCoboundary₂ (combinedRelativeCocycle / clusterOmega) := by
  apply (isMulCoboundary₂_div_iff _ _).2
  refine ⟨combinedLClassGauge, ?_⟩
  refine Multiplicative.forall_zmod_two_prod ?_ ?_ ?_ ?_
  all_goals refine Multiplicative.forall_zmod_two_prod ?_ ?_ ?_ ?_ <;>
    apply Units.ext <;>
    norm_num [combinedRelativeCocycle, combinedLClassGauge, clusterOmega,
      ZMod.val_zero, ZMod.val_one, ZMod.val_ofNat]

/-- The actual relative action factor system satisfies Mathlib's two-cocycle condition. -/
theorem combinedRelativeCocycle_isCocycle :
    groupCohomology.IsMulCocycle₂ combinedRelativeCocycle :=
  isMulCocycle₂_of_isMulCoboundary₂_div clusterOmega_isCocycle
    combinedRelativeCocycle_div_cluster_isMulCoboundary

/-- The relative action class is exactly the nontrivial class of the split-index bond. -/
theorem combinedRelativeCocycle_H2π_eq_cluster :
    groupCohomology.H2π _
        (groupCohomology.cocyclesOfIsMulCocycle₂ combinedRelativeCocycle_isCocycle) =
      groupCohomology.H2π _
        (groupCohomology.cocyclesOfIsMulCocycle₂ clusterOmega_isCocycle) :=
  (H2π_eq_iff_isMulCoboundary₂_div combinedRelativeCocycle_isCocycle
    clusterOmega_isCocycle).2 combinedRelativeCocycle_div_cluster_isMulCoboundary

/-- The two invariant states have a nontrivial relative action L-symbol class. This is the
algebraic invariant, without a conclusion about arbitrary physical gapped paths. -/
theorem combinedRelativeCocycle_H2π_ne_zero :
    groupCohomology.H2π _
      (groupCohomology.cocyclesOfIsMulCocycle₂ combinedRelativeCocycle_isCocycle) ≠ 0 := by
  rw [combinedRelativeCocycle_H2π_eq_cluster]
  exact cluster_isNontrivialSPT

/-- The relative L-symbol for arbitrary action reductions of the two states and arbitrary
common fusion reductions of their combined symmetry. -/
def combinedRelativeLSymbol (fd : FusionData combinedFamily)
    (ad : ActionData combinedFamily stateTensor) (bd : ActionData combinedFamily zeroState) :
    ScalarCocycle (Multiplicative (ZMod 2 × ZMod 2)) :=
  fun p ↦ ad.lSymbol fd () p.1 p.2 / bd.lSymbol fd () p.1 p.2

/-- Every choice of the actual reduction data gives the computed relative class. -/
theorem combinedRelativeLSymbol_div_computed_isMulCoboundary
    (fd : FusionData combinedFamily) (ad : ActionData combinedFamily stateTensor)
    (bd : ActionData combinedFamily zeroState) :
    groupCohomology.IsMulCoboundary₂
      (combinedRelativeLSymbol fd ad bd / combinedRelativeCocycle) := by
  have h := ActionData.relative_lSymbol_isMulCoboundary₂_div
    combinedFamily_isNormalRepresentation stateTensor_isNormal zeroState_isNormal
    (by decide) one_pos fixesMPV_combinedFamily_stateTensor fixesMPV_combinedFamily_zeroState
    combinedFusionData fd combinedStateActionData ad combinedZeroActionData bd
  simp only [← combinedRelativeCocycle_eq_lSymbol_div] at h
  convert h using 1
  rfl

/-- The relative L-symbol is a genuine two-cocycle for every choice of reduction data. -/
theorem combinedRelativeLSymbol_isCocycle (fd : FusionData combinedFamily)
    (ad : ActionData combinedFamily stateTensor) (bd : ActionData combinedFamily zeroState) :
    groupCohomology.IsMulCocycle₂ (combinedRelativeLSymbol fd ad bd) :=
  isMulCocycle₂_of_isMulCoboundary₂_div combinedRelativeCocycle_isCocycle
    (combinedRelativeLSymbol_div_computed_isMulCoboundary fd ad bd)

/-- The reduction-independent relative action class equals the nontrivial split-index
class. No physical path hypothesis or conclusion is introduced. -/
theorem combinedRelativeLSymbol_H2π_eq_cluster (fd : FusionData combinedFamily)
    (ad : ActionData combinedFamily stateTensor) (bd : ActionData combinedFamily zeroState) :
    groupCohomology.H2π _
        (groupCohomology.cocyclesOfIsMulCocycle₂ (combinedRelativeLSymbol_isCocycle fd ad bd)) =
      groupCohomology.H2π _
        (groupCohomology.cocyclesOfIsMulCocycle₂ clusterOmega_isCocycle) := by
  rw [← combinedRelativeCocycle_H2π_eq_cluster]
  exact (H2π_eq_iff_isMulCoboundary₂_div (combinedRelativeLSymbol_isCocycle fd ad bd)
    combinedRelativeCocycle_isCocycle).2
      (combinedRelativeLSymbol_div_computed_isMulCoboundary fd ad bd)

/-- All actual action and common fusion choices give a nontrivial relative L-symbol class. -/
theorem combinedRelativeLSymbol_H2π_ne_zero (fd : FusionData combinedFamily)
    (ad : ActionData combinedFamily stateTensor) (bd : ActionData combinedFamily zeroState) :
    groupCohomology.H2π _
      (groupCohomology.cocyclesOfIsMulCocycle₂
        (combinedRelativeLSymbol_isCocycle fd ad bd)) ≠ 0 := by
  rw [combinedRelativeLSymbol_H2π_eq_cluster]
  exact cluster_isNontrivialSPT

end ControlledZGauging
