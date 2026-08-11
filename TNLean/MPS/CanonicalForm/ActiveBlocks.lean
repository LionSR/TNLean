/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.FinSum
import TNLean.MPS.CanonicalForm.Definitions

/-!
# Active blocks of a CPSV canonical form

This module restricts a literal CPSV canonical-form decomposition to the displayed blocks with
nonzero weight. Zero-weight blocks do not contribute to any positive-length matrix product
vector.

Source: arXiv:1606.00608, lines 237--301 and 1135--1146; arXiv:2011.12127,
lines 1831--1885.
-/
open scoped Matrix BigOperators

namespace MPSTensor

variable {d D : ℕ} {A : MPSTensor d D}

namespace CPSVCanonicalFormData

/-- A finite enumeration of the nonzero-weight displayed blocks. -/
noncomputable def activeEquiv (data : CPSVCanonicalFormData A) :
    Fin (Fintype.card data.Active) ≃ data.Active :=
  (Fintype.equivFin data.Active).symm

/-- Bond dimensions of the enumerated active blocks. -/
noncomputable def activeDim (data : CPSVCanonicalFormData A) :
    Fin (Fintype.card data.Active) → ℕ :=
  fun k => data.dim (data.activeEquiv k)

/-- Weights of the enumerated active blocks. -/
noncomputable def activeWeight (data : CPSVCanonicalFormData A) :
    Fin (Fintype.card data.Active) → ℂ :=
  fun k => data.weights (data.activeEquiv k)

/-- Normal tensors of the enumerated active blocks. -/
noncomputable def activeBlocks (data : CPSVCanonicalFormData A) :
    (k : Fin (Fintype.card data.Active)) → MPSTensor d (data.activeDim k) :=
  fun k => data.blocks (data.activeEquiv k)

end CPSVCanonicalFormData

/-- Removing zero-weight blocks preserves every positive-length matrix product vector.

Source: arXiv:1606.00608, eq. `II_CF1`, lines 237--246 and 271--301. -/
theorem sameMPV₂Pos_toTensorFromBlocks_active
    {r : ℕ} {dim : Fin r → ℕ}
    (μ : Fin r → ℂ) (blocks : (k : Fin r) → MPSTensor d (dim k))
    (e : Fin (Fintype.card {k : Fin r // μ k ≠ 0}) ≃ {k : Fin r // μ k ≠ 0}) :
    SameMPV₂Pos (toTensorFromBlocks (d := d) μ blocks)
      (toTensorFromBlocks (d := d) (fun k => μ (e k)) (fun k => blocks (e k))) := by
  classical
  intro N hN σ
  rw [mpv_toTensorFromBlocks_eq_sum, mpv_toTensorFromBlocks_eq_sum]
  simp only [smul_eq_mul]
  let f : Fin r → ℂ := fun k => μ k ^ N * mpv (blocks k) σ
  have hInactive : ∑ k : {k : Fin r // ¬ μ k ≠ 0}, f k = 0 := by
    apply Fintype.sum_eq_zero
    intro k
    simp [f, not_ne_iff.mp k.property, Nat.ne_of_gt hN]
  have hSplit :=
    Fintype.sum_subtype_add_sum_subtype (fun k : Fin r => μ k ≠ 0) f
  have hActiveSum : (∑ k : Fin r, f k) = ∑ k : {k : Fin r // μ k ≠ 0}, f k := by
    rw [hInactive, add_zero] at hSplit
    exact hSplit.symm
  change (∑ k : Fin r, f k) =
    ∑ k : Fin (Fintype.card {k : Fin r // μ k ≠ 0}), f (e k)
  rw [hActiveSum]
  exact (e.sum_comp (fun k : {k : Fin r // μ k ≠ 0} => f k)).symm

namespace CPSVCanonicalFormData

/-- Literal CPSV canonical-form data agree at every positive length with their active weighted
block sum.

This is the active part of the canonical-form and BNT decompositions in arXiv:1606.00608,
lines 237--301 and 1135--1146, and arXiv:2011.12127, lines 1831--1885. -/
theorem sameMPV₂Pos_activeBlocks (data : CPSVCanonicalFormData A) :
    SameMPV₂Pos A
      (toTensorFromBlocks (d := d) data.activeWeight data.activeBlocks) :=
  data.sameMPV₂Pos_toTensorFromBlocks.trans <| by
    change SameMPV₂Pos (toTensorFromBlocks (d := d) data.weights data.blocks)
      (toTensorFromBlocks (d := d) (fun k => data.weights (data.activeEquiv k))
        (fun k => data.blocks (data.activeEquiv k)))
    exact sameMPV₂Pos_toTensorFromBlocks_active data.weights data.blocks data.activeEquiv

end CPSVCanonicalFormData

end MPSTensor
