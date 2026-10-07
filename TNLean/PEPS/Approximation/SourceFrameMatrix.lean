/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.SourceBlockMatrix
import TNLean.PEPS.Approximation.SourceSlotMaps

/-!
# Joint contractions in source frames

Endpoint contractions map finite source coordinates into the actual private
halfspaces. The coordinate spaces may be proper subspaces: their images need not
span the private spaces. The complete matrix of prepared branches is still a
contraction on all coordinate and physical input vectors.

Source: polynomial-PEPS manuscript (September 24, 2026), Theorem 5.2,
`04-compression.tex`, Schmidt frames and free-input contractions,
lines 279–299 and 383–427.
-/

/-!
Source: September 24, 2026, polynomial-PEPS manuscript, 04-compression.tex,
eq:compression-block-contraction.
Manuscript revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Independently formalized from the manuscript; no upstream Lean proof text reused.

Provenance-ID: 8769-free-input-frame-word.sourceframematrix
Downstream declaration: TNLean.PEPS.PairEffect.Word.sourceFrameMatrix

Provenance-ID: 8769-free-input-frame-word.sourceframematrix_eq_freesourcematrix
Downstream declaration: TNLean.PEPS.PairEffect.Word.sourceFrameMatrix_eq_freeSourceMatrix

Provenance-ID: 8769-free-input-frame-word.norm_sourceframematrix_le_one
Downstream declaration: TNLean.PEPS.PairEffect.Word.norm_sourceFrameMatrix_le_one
-/

noncomputable section

open scoped TensorProduct Matrix Matrix.Norms.L2Operator
open ContinuousLinearMap

namespace TNLean.PEPS.PairEffect.Word

variable {P m n : Type} [Fintype m] [Fintype n]
    (R : SourceInventory P) (U V U' V' : Fin R.length → HSpace)
    (f : ∀ i, U i →L[ℂ] U' i) (g : ∀ i, V i →L[ℂ] V' i)
    {A B : Fin R.length → Type} [∀ i, Fintype (A i)] [∀ i, Fintype (B i)]
    (bU : ∀ i, OrthonormalBasis (A i) ℂ (U i))
    (bV : ∀ i, OrthonormalBasis (B i) ℂ (V i))
    (ℓ : Layout P) {ℓ' : Layout P}

/-- The complete matrix of an actual branch in the given endpoint frames.
The frame images need not span the private halfspaces. Source: polynomial-PEPS
Theorem 5.2, `04-compression.tex`, lines 279–299 and 383–427. -/
def sourceFrameMatrix (v : Word (SourceInventory.slotLayout R U' V' ++ ℓ) ℓ')
    (bIn : OrthonormalBasis n ℂ (Mem ℓ)) (bOut : OrthonormalBasis m ℂ (Mem ℓ')) :
    Matrix m ((∀ i, A i × B i) × n) ℂ :=
  fun k a ↦ v.preparedMatrix R U' V'
    (fun i ↦ f i (bU i (a.1 i).1) ⊗ₜ g i (bV i (a.1 i).2)) ℓ bIn bOut k a.2

/-- The frame matrix is the full free-input matrix of the actual endpoint-map
composition. The endpoint maps are fixed before the source vector is chosen.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 279–299 and 409–427. -/
theorem sourceFrameMatrix_eq_freeSourceMatrix
    (v : Word (SourceInventory.slotLayout R U' V' ++ ℓ) ℓ')
    (bIn : OrthonormalBasis n ℂ (Mem ℓ)) (bOut : OrthonormalBasis m ℂ (Mem ℓ')) :
    v.sourceFrameMatrix R U V U' V' f g bU bV ℓ bIn bOut =
      (Word.comp (mapSourceSlots R U V U' V' f g ℓ) v).freeSourceMatrix
        R U V bU bV ℓ bIn bOut := by
  classical
  ext k a
  obtain ⟨a, j⟩ := a
  simp only [sourceFrameMatrix, freeSourceMatrix_apply]
  have he : (Word.comp (mapSourceSlots R U V U' V' f g ℓ) v).eval ∘L
      (SourceInventory.prepareSlots R U V
        (fun i ↦ bU i (a i).1 ⊗ₜ bV i (a i).2) ℓ).eval =
    v.eval ∘L (SourceInventory.prepareSlots R U' V'
      (fun i ↦ f i (bU i (a i).1) ⊗ₜ g i (bV i (a i).2)) ℓ).eval := by
    change v.eval ∘L ((mapSourceSlots R U V U' V' f g ℓ).eval ∘L
      (SourceInventory.prepareSlots R U V
        (fun i ↦ bU i (a i).1 ⊗ₜ bV i (a i).2) ℓ).eval) = _
    rw [eval_mapSourceSlots_prepareSlots]
    simp only [TensorProduct.mapL_tmul]
  simp only [preparedMatrix, he]

open Classical in
/-- Endpoint contractions followed by an allowed word give a contraction on the
whole coordinate/input space, including proper source-frame subspaces.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 409–427. -/
theorem norm_sourceFrameMatrix_le_one
    (hf : ∀ i, ‖f i‖ ≤ 1) (hg : ∀ i, ‖g i‖ ≤ 1)
    (v : Word (SourceInventory.slotLayout R U' V' ++ ℓ) ℓ') (hv : v.IsAllowed)
    (bIn : OrthonormalBasis n ℂ (Mem ℓ)) (bOut : OrthonormalBasis m ℂ (Mem ℓ')) :
    ‖v.sourceFrameMatrix R U V U' V' f g bU bV ℓ bIn bOut‖ ≤ 1 := by
  classical
  rw [sourceFrameMatrix_eq_freeSourceMatrix]
  exact norm_freeSourceMatrix_le_one R U V bU bV ℓ
    (Word.comp (mapSourceSlots R U V U' V' f g ℓ) v)
    ⟨(mapSourceSlots_spec R U V U' V' f g hf hg ℓ).1, hv⟩ bIn bOut

end TNLean.PEPS.PairEffect.Word
