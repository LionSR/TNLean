/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Operator.PairAlphabet
import QICLean.Kraus.BlockingTransfer

/-!
# The doubled-index view and the pair alphabet

The doubled-index view `MPOTensor.toMPSTensor M` of an operator tensor is the tensor `M` on the
pair alphabet relabelled along `finProdFinEquiv : Fin d × Fin d ≃ Fin (d * d)`. This file proves
that the basic tensor predicates and coefficients agree on the two sides, so that a statement on
the pair alphabet can call a statement still phrased on the doubled index.

## Main results

* `MPOTensor.toMPSTensor_eq_reindexPhysical`: the doubled-index view is a physical relabelling.
* `MPOTensor.isInjective_toMPSTensor_iff`, `MPOTensor.isNormal_toMPSTensor_iff`,
  `MPOTensor.isTP_toMPSTensor_iff`, `MPOTensor.kraus_transferMap_toMPSTensor`: injectivity,
  normality, trace preservation and the transfer map agree.
* `MPOTensor.gaugeEquiv_toMPSTensor_iff`, `MPOTensor.sameMPV₂Pos_toMPSTensor_iff`: gauge
  equivalence and equality of positive-length coefficients agree.
* `MPOTensor.evalWord_toMPSTensor`, `MPOTensor.mpv_toMPSTensor_eq`: words and coefficients of
  the view are words and coefficients on the relabelled letters.

## Implementation notes

This module is removed together with `MPOTensor.toMPSTensor`; see
`docs/tensor_type_unification.md`, step T.2a.
-/

open scoped Matrix

namespace MPOTensor

variable {d D D₁ D₂ : ℕ}

/-- The doubled-index view is the tensor on the pair alphabet relabelled along the inverse of
`finProdFinEquiv`. -/
theorem toMPSTensor_eq_reindexPhysical (M : MPOTensor d D) :
    M.toMPSTensor = Kraus.reindexPhysical finProdFinEquiv.symm M := rfl

/-- Words of the doubled-index view are words over the pair alphabet. -/
theorem evalWord_toMPSTensor (M : MPOTensor d D) (w : List (Fin (d * d))) :
    Kraus.evalWord M.toMPSTensor w = Kraus.evalWord M (w.map finProdFinEquiv.symm) := by
  rw [toMPSTensor_eq_reindexPhysical, Kraus.evalWord_reindexPhysical]

/-- Coefficients of the doubled-index view are coefficients on the pair alphabet. -/
theorem mpv_toMPSTensor_eq (M : MPOTensor d D) {N : ℕ} (w : Fin N → Fin (d * d)) :
    MPTensor.mpv M.toMPSTensor w = MPTensor.mpv M fun k ↦ finProdFinEquiv.symm (w k) := by
  rw [toMPSTensor_eq_reindexPhysical, MPTensor.mpv_reindexPhysical]

/-- The doubled-index view is injective exactly when the tensor on the pair alphabet is. -/
theorem isInjective_toMPSTensor_iff (M : MPOTensor d D) :
    Kraus.IsInjective M.toMPSTensor ↔ Kraus.IsInjective M := by
  have h : Set.range M.toMPSTensor = Set.range M :=
    finProdFinEquiv.symm.surjective.range_comp M
  simp only [Kraus.IsInjective, h]

/-- The doubled-index view is normal exactly when the tensor on the pair alphabet is. -/
theorem isNormal_toMPSTensor_iff (M : MPOTensor d D) :
    Kraus.IsNormal M.toMPSTensor ↔ Kraus.IsNormal M := by
  have h : ∀ N : ℕ, Kraus.wordSpan M.toMPSTensor N = Kraus.wordSpan M N := by
    intro N
    let e : (Fin N → Fin (d * d)) ≃ (Fin N → Fin d × Fin d) :=
      Equiv.arrowCongr (Equiv.refl _) finProdFinEquiv.symm
    have hr : (Set.range fun σ : Fin N → Fin (d * d) ↦
        Kraus.evalWord M.toMPSTensor (List.ofFn σ)) =
        Set.range fun σ : Fin N → Fin d × Fin d ↦ Kraus.evalWord M (List.ofFn σ) := by
      rw [← e.surjective.range_comp]
      congr 1
      funext σ
      simp [e, evalWord_toMPSTensor, List.map_ofFn, Function.comp_def, Equiv.arrowCongr]
    simp only [Kraus.wordSpan, hr]
  simp only [Kraus.isNormal_iff, Kraus.IsNBlkInjective, h]

/-- The doubled-index view has the transfer map of the tensor on the pair alphabet. -/
theorem kraus_transferMap_toMPSTensor (M : MPOTensor d D) :
    Kraus.transferMap M.toMPSTensor = Kraus.transferMap M := by
  rw [toMPSTensor_eq_reindexPhysical, Kraus.transferMap_reindexPhysical_equiv]

/-- The doubled-index view is trace preserving exactly when the tensor on the pair alphabet
is. -/
theorem isTP_toMPSTensor_iff (M : MPOTensor d D) :
    Kraus.IsTP M.toMPSTensor ↔ Kraus.IsTP M := by
  rw [toMPSTensor_eq_reindexPhysical, Kraus.isTP_reindexPhysical_iff]

/-- Two doubled-index views are gauge equivalent exactly when the tensors on the pair alphabet
are. -/
theorem gaugeEquiv_toMPSTensor_iff (M N : MPOTensor d D) :
    MPTensor.GaugeEquiv M.toMPSTensor N.toMPSTensor ↔ MPTensor.GaugeEquiv M N := by
  simp only [MPTensor.GaugeEquiv, toMPSTensor_eq_reindexPhysical, Kraus.reindexPhysical]
  exact exists_congr fun X ↦
    (finProdFinEquiv.forall_congr_left (p := fun i ↦ N i = X * M i * X⁻¹)).symm

/-- Two doubled-index views have the same positive-length coefficients exactly when the tensors
on the pair alphabet have. -/
theorem sameMPV₂Pos_toMPSTensor_iff (M : MPOTensor d D₁) (N : MPOTensor d D₂) :
    MPTensor.SameMPV₂Pos M.toMPSTensor N.toMPSTensor ↔ MPTensor.SameMPV₂Pos M N := by
  refine forall_congr' fun L ↦ forall_congr' fun _ ↦ ?_
  let e : (Fin L → Fin (d * d)) ≃ (Fin L → Fin d × Fin d) :=
    Equiv.arrowCongr (Equiv.refl _) finProdFinEquiv.symm
  refine e.forall_congr fun σ ↦ ?_
  rw [mpv_toMPSTensor_eq, mpv_toMPSTensor_eq]
  rfl

end MPOTensor
