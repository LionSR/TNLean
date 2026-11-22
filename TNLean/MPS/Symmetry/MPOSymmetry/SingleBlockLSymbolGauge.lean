/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.MPOSymmetry.AssociatorToolkit
import TNLean.MPS.Symmetry.MPOSymmetry.PermutedBlocksGauge

/-!
# Relative L-symbols of two invariant normal states

The existing gauge law for permuted blocks applies to a single invariant state by taking
one block. In the ratio of the L-symbols of two states, the common fusion gauge cancels.
Changing either action reduction therefore changes the relative factor system by a
two-coboundary. This is the relative version of arXiv:2502.20257, equation `eq:Lsymbgauge`.
-/

open scoped Matrix TNLean.Algebra.ScalarCohomology
open TNLean.Algebra MPSTensor

namespace MPOTensor.GroupFamily.ActionData

variable {G : Type} [Group G] {d D E : ℕ} {F : GroupFamily G d}
  {A : MPSTensor d D} {B : MPSTensor d E}

/-- View a single invariant state's action reductions as a one-block action. -/
def toBlockActionData (ad : ActionData F A) : BlockActionData F (fun _ : Unit ↦ A) where
  V g _ := ad.V g
  W g _ := ad.W g
  isReduction g _ := ad.isReduction g

/-- The one-block and single-state constructions give the same selected L-symbol. -/
theorem toBlockActionData_lSymbol (ad : ActionData F A) (fd : FusionData F) :
    ad.toBlockActionData.lSymbol fd = ad.lSymbol fd := by
  funext x g h
  have hc : castIndex (fun _ : Unit ↦ D) (mul_smul g h x) =
      (1 : Matrix (Fin D) (Fin D) ℂ) := by
    rw [castIndex]
    exact finCongr_toMatrix_eq_one _
  simp only [BlockActionData.lSymbol, BlockActionData.actV, BlockActionData.fuseV, hc,
    Matrix.one_mul, toBlockActionData, ActionData.lSymbol, ActionData.actV, ActionData.fuseV]

/-- A joint change of fusion and action reductions changes a single state's L-symbol by
the already established permuted-block gauge law. -/
theorem lSymbol_eq_blockGauge (hF : F.IsNormalRepresentation) (hA : Kraus.IsNormal A)
    (hD : 0 < D) (hinv : ∀ g, FixesMPV (F.tensor g) A)
    (fd fd' : FusionData F) (ad ad' : ActionData F A) :
    ad'.lSymbol fd' = LSymbol.gauge (fd.relativeScalar fd')
      (ad.toBlockActionData.relativeScalar ad'.toBlockActionData) (ad.lSymbol fd) := by
  have h := BlockActionData.lSymbol_eq_gauge hF (fun _ ↦ hA) (fun _ ↦ hD)
    (fun g _ ↦ hinv g) fd fd' ad.toBlockActionData ad'.toBlockActionData
  simpa only [toBlockActionData_lSymbol] using h

/-- The ratio of the action L-symbols of two invariant states is independent of every
choice of their action reductions and of their common fusion reductions, up to coboundary. -/
theorem relative_lSymbol_isMulCoboundary₂_div (hF : F.IsNormalRepresentation)
    (hA : Kraus.IsNormal A) (hB : Kraus.IsNormal B) (hD : 0 < D) (hE : 0 < E)
    (hinvA : ∀ g, FixesMPV (F.tensor g) A) (hinvB : ∀ g, FixesMPV (F.tensor g) B)
    (fd fd' : FusionData F) (ad ad' : ActionData F A) (bd bd' : ActionData F B) :
    groupCohomology.IsMulCoboundary₂
      ((fun p : G × G ↦ ad'.lSymbol fd' () p.1 p.2 / bd'.lSymbol fd' () p.1 p.2) /
        (fun p : G × G ↦ ad.lSymbol fd () p.1 p.2 / bd.lSymbol fd () p.1 p.2)) := by
  rw [lSymbol_eq_blockGauge hF hA hD hinvA fd fd' ad ad',
    lSymbol_eq_blockGauge hF hB hE hinvB fd fd' bd bd']
  apply (isMulCoboundary₂_div_iff _ _).2
  let γ := ad.toBlockActionData.relativeScalar ad'.toBlockActionData
  let η := bd.toBlockActionData.relativeScalar bd'.toBlockActionData
  refine ⟨fun g ↦ η g () / γ g (), ?_⟩
  intro g h
  have hu : h • () = () := Subsingleton.elim _ _
  simp only [LSymbol.gauge, hu]
  change (γ (g * h) () * fd.relativeScalar fd' (g, h) / (γ g () * γ h ())) *
      ad.lSymbol fd () g h /
      ((η (g * h) () * fd.relativeScalar fd' (g, h) / (η g () * η h ())) *
        bd.lSymbol fd () g h) = _
  apply Units.ext
  simp only [Units.val_mul, Units.val_div_eq_div_val, Units.val_inv_eq_inv_val]
  have hβ := (fd.relativeScalar fd' (g, h)).ne_zero
  have hγg := (γ g ()).ne_zero
  have hγh := (γ h ()).ne_zero
  have hγgh := (γ (g * h) ()).ne_zero
  have hηg := (η g ()).ne_zero
  have hηh := (η h ()).ne_zero
  have hηgh := (η (g * h) ()).ne_zero
  have hL := (bd.lSymbol fd () g h).ne_zero
  field_simp

end MPOTensor.GroupFamily.ActionData
