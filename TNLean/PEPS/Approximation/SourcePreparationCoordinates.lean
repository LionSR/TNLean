/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.CommonSourcePreparation
import Mathlib.LinearAlgebra.Multilinear.Curry

/-!
# Coordinates of an actual source preparation

The vector prepared in fixed pair slots is multilinear in the pair vectors.
Expanding each pair in endpoint bases therefore expands the preparation operator,
with a product of source coordinates for each assignment of basis vectors.

Source: polynomial-PEPS manuscript (September 24, 2026), Theorem 5.2,
`04-compression.tex`, source preparations and common spaces at lines 233–267,
and the source-entry expansion at lines 279–355.
-/

/-!
Source: September 24, 2026, polynomial-PEPS manuscript, 04-compression.tex,
eq:compression-source-gate.
Manuscript revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Independently formalized from the manuscript; no upstream Lean proof text reused.

Provenance-ID: 8769-source-density-coordinates-sourceinventory.slotlayout_cons
Downstream declaration: TNLean.PEPS.PairEffect.SourceInventory.slotLayout_cons

Provenance-ID: 8769-source-density-coordinates-sourceinventory.slotvector
Downstream declaration: TNLean.PEPS.PairEffect.SourceInventory.slotVector

Provenance-ID: 8769-source-density-coordinates-sourceinventory.slotvector_eq_vector
Downstream declaration: TNLean.PEPS.PairEffect.SourceInventory.slotVector_eq_vector

Provenance-ID: 8769-source-density-coordinates-sourceinventory.eval_prepareslots_eq_appendiso_symm
Downstream declaration: TNLean.PEPS.PairEffect.SourceInventory.eval_prepareSlots_eq_appendIso_symm

Provenance-ID: 8769-source-density-coordinates-sourceinventory.eval_prepareslots_sum_smul
Downstream declaration: TNLean.PEPS.PairEffect.SourceInventory.eval_prepareSlots_sum_smul

Provenance-ID: 8769-source-density-coordinates-sourceinventory.eval_prepareslots_eq_sum_basis
Downstream declaration: TNLean.PEPS.PairEffect.SourceInventory.eval_prepareSlots_eq_sum_basis
-/

noncomputable section

open scoped TensorProduct
open ContinuousLinearMap

namespace TNLean.PEPS.PairEffect.SourceInventory

variable {P : Type}

/-- The fixed layout separates the first pair from the remaining slots. -/
theorem slotLayout_cons (r : PairSource P) (R : SourceInventory P)
    (U V : Fin (r :: R).length → HSpace) :
    slotLayout (r :: R) U V =
      ⟨r.left, U 0⟩ :: ⟨r.right, V 0⟩ ::
        slotLayout R (fun i ↦ U i.succ) (fun i ↦ V i.succ) := by
  simp [slotLayout, ofSlots_cons, layout_cons, PairSource.layout]

/-- The source vector in fixed slots, as a multilinear function of the pair vectors.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 233–267 and 342–355. -/
def slotVector : (R : SourceInventory P) → (U V : Fin R.length → HSpace) →
    MultilinearMap ℂ (fun i ↦ U i ⊗[ℂ] V i) (Mem (slotLayout R U V))
  | [], U, V => MultilinearMap.constOfIsEmpty ℂ
      (fun i : Fin 0 ↦ U i ⊗[ℂ] V i) (1 : ℂ)
  | r :: R, U, V => by
      refine (Layout.memCongr (slotLayout_cons r R U V).symm).toLinearEquiv.toLinearMap
        |>.compMultilinearMap
        (LinearMap.uncurryLeft
        { toFun := fun η ↦
            ((assocL (U 0) (V 0)
              (Mem (slotLayout R (fun i ↦ U i.succ) (fun i ↦ V i.succ)))).toLinearMap.comp
                (TensorProduct.mk ℂ (U 0 ⊗[ℂ] V 0)
                  (Mem (slotLayout R (fun i ↦ U i.succ) (fun i ↦ V i.succ))) η)).compMultilinearMap
              (slotVector R (fun i ↦ U i.succ) (fun i ↦ V i.succ))
          map_add' := by
            intro x y
            ext η
            simp
          map_smul' := by
            intro c x
            ext η
            simp })

private theorem memCongr_apply_heq {a b : Layout P} (h : a = b) (x : Mem a) :
    HEq (Layout.memCongr h x) x := by
  cases h
  rfl

private theorem slotVector_cons_heq (r : PairSource P) (R : SourceInventory P)
    (U V : Fin (r :: R).length → HSpace) (η : ∀ i, U i ⊗[ℂ] V i) :
    HEq (slotVector (r :: R) U V η)
      (assocL (U 0) (V 0) (Mem (slotLayout R (fun i ↦ U i.succ) (fun i ↦ V i.succ)))
        (η 0 ⊗ₜ slotVector R (fun i ↦ U i.succ) (fun i ↦ V i.succ)
          (fun i ↦ η i.succ))) := by
  exact memCongr_apply_heq (slotLayout_cons r R U V).symm _

private theorem assocL_tmul_heq (U V : HSpace) {a b : Layout P} (h : a = b)
    (η : U ⊗[ℂ] V) {x : Mem a} {y : Mem b} (hxy : HEq x y) :
    HEq (assocL U V (Mem a) (η ⊗ₜ x)) (assocL U V (Mem b) (η ⊗ₜ y)) := by
  cases h
  exact heq_of_eq (congrArg (fun z ↦ assocL U V (Mem a) (η ⊗ₜ z)) (eq_of_heq hxy))

private theorem slotVector_heq_vector (R : SourceInventory P)
    (U V : Fin R.length → HSpace) (η : ∀ i, U i ⊗[ℂ] V i) :
    HEq (slotVector R U V η) (vector (ofSlots R U V η)) := by
  induction R with
  | nil => rfl
  | cons r R ih =>
    apply HEq.trans (slotVector_cons_heq r R U V η)
    have hv {S T : SourceInventory P} (h : S = T) : HEq (vector S) (vector T) := by
      cases h
      rfl
    exact (assocL_tmul_heq (U 0) (V 0)
      (layout_ofSlots_eq R (fun i ↦ U i.succ) (fun i ↦ V i.succ)
        (fun _ ↦ 0) (fun i ↦ η i.succ)) (η 0)
      (ih (fun i ↦ U i.succ) (fun i ↦ V i.succ) (fun i ↦ η i.succ))).trans
        (hv (ofSlots_cons r R U V η).symm)

/-- The multilinear source vector is the actual prepared vector transported to the
vector-independent layout. -/
theorem slotVector_eq_vector (R : SourceInventory P)
    (U V : Fin R.length → HSpace) (η : ∀ i, U i ⊗[ℂ] V i) :
    slotVector R U V η =
      Layout.memCongr (layout_ofSlots_eq R U V η (fun _ ↦ 0))
        (vector (ofSlots R U V η)) := by
  exact eq_of_heq ((slotVector_heq_vector R U V η).trans (memCongr_apply_heq _ _).symm)

private theorem transport_append {a b : Layout P} (h : a = b)
    (ℓ : Layout P) (x : Mem a) (y : Mem ℓ) :
    Layout.memCongr (congrArg (· ++ ℓ) h) ((appendIso a ℓ).symm (x ⊗ₜ y)) =
      (appendIso b ℓ).symm (Layout.memCongr h x ⊗ₜ y) := by
  cases h
  rfl

/-- Preparation in fixed slots tensors the actual multilinear source vector with the input. -/
theorem eval_prepareSlots_eq_appendIso_symm (R : SourceInventory P)
    (U V : Fin R.length → HSpace) (η : ∀ i, U i ⊗[ℂ] V i)
    (ℓ : Layout P) (x : Mem ℓ) :
    (prepareSlots R U V η ℓ).eval x =
      (appendIso (slotLayout R U V) ℓ).symm (slotVector R U V η ⊗ₜ x) := by
  rw [slotVector_eq_vector, prepareSlots, Word.eval_castLayouts]
  change Layout.memCongr (congrArg (· ++ ℓ) (layout_ofSlots_eq R U V η (fun _ ↦ 0)))
    (((ofSlots R U V η).prepare ℓ).eval x) = _
  rw [eval_prepare_eq_appendIso_symm]
  exact transport_append _ _ _ _

/-- A finite linear combination in every actual pair slot expands its preparation operator
as the sum over choices of one component from each slot. Source: polynomial-PEPS Theorem 5.2,
`04-compression.tex`, lines 279–355. -/
theorem eval_prepareSlots_sum_smul (R : SourceInventory P)
    (U V : Fin R.length → HSpace)
    {A : Fin R.length → Type} [∀ i, Fintype (A i)]
    (c : ∀ i, A i → ℂ) (η : ∀ i, A i → U i ⊗[ℂ] V i) (ℓ : Layout P) :
    (prepareSlots R U V (fun i ↦ ∑ a, c i a • η i a) ℓ).eval =
      ∑ a : ∀ i, A i,
        (∏ i, c i (a i)) • (prepareSlots R U V (fun i ↦ η i (a i)) ℓ).eval := by
  classical
  apply ContinuousLinearMap.ext
  intro x
  simp only [sum_apply, smul_apply, eval_prepareSlots_eq_appendIso_symm]
  rw [(slotVector R U V).map_sum]
  simp only [(slotVector R U V).map_smul_univ, TensorProduct.sum_tmul,
    ← TensorProduct.smul_tmul', map_sum, map_smul]

/-- Expanding the actual pair sources in endpoint orthonormal bases expands their preparation
operator with the product of the source coordinates. Source: polynomial-PEPS Theorem 5.2,
`04-compression.tex`, lines 253–267 and 342–355. -/
theorem eval_prepareSlots_eq_sum_basis (R : SourceInventory P)
    (U V : Fin R.length → HSpace)
    {A B : Fin R.length → Type} [∀ i, Fintype (A i)] [∀ i, Fintype (B i)]
    (bU : ∀ i, OrthonormalBasis (A i) ℂ (U i))
    (bV : ∀ i, OrthonormalBasis (B i) ℂ (V i))
    (η : ∀ i, U i ⊗[ℂ] V i) (ℓ : Layout P) :
    (prepareSlots R U V η ℓ).eval =
      ∑ a : ∀ i, A i × B i,
        (∏ i, ((bU i).tensorProduct (bV i)).repr (η i) (a i)) •
          (prepareSlots R U V (fun i ↦ bU i (a i).1 ⊗ₜ bV i (a i).2) ℓ).eval := by
  classical
  have h : η = fun i ↦ ∑ a, ((bU i).tensorProduct (bV i)).repr (η i) a •
      (bU i (a.1) ⊗ₜ bV i (a.2)) := by
    funext i
    simpa only [OrthonormalBasis.tensorProduct_apply'] using
      ((bU i).tensorProduct (bV i)).sum_repr (η i) |>.symm
  conv_lhs => rw [h, eval_prepareSlots_sum_smul]

end TNLean.PEPS.PairEffect.SourceInventory
