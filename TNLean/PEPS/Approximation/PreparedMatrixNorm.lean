/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.SourceGateDensity
import QICLean.Analysis.OrthonormalMatrixNorm

/-!
# Operator norms of prepared branches

Preparing normalized pair sources and then applying an allowed word is a
contraction. Its matrix in orthonormal input and output bases therefore has
Euclidean operator norm at most one. In particular, this holds for the operators
obtained by assigning a unit vector to every source half, including vectors
from an orthonormal family that spans only a proper subspace.

Source: polynomial-PEPS manuscript (September 24, 2026), Theorem 5.2,
`04-compression.tex`, source-gate expansion and source-entry separation,
lines 233–267 and 409–427.
-/

/-!
Source: September 24, 2026, polynomial-PEPS manuscript, 04-compression.tex,
eq:compression-source-gate.
Manuscript revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Independently formalized from the manuscript; no upstream Lean proof text reused.

Provenance-ID: 8769-source-density-norms-word.norm_preparedmatrix_le_one
Downstream declaration: TNLean.PEPS.PairEffect.Word.norm_preparedMatrix_le_one

Provenance-ID: 8769-source-density-norms-word.norm_preparedmatrix_tmul_le_one
Downstream declaration: TNLean.PEPS.PairEffect.Word.norm_preparedMatrix_tmul_le_one
-/

noncomputable section

open scoped InnerProductSpace TensorProduct Matrix.Norms.L2Operator
open ContinuousLinearMap

namespace TNLean.PEPS.PairEffect.Word

/-- Normalized source preparation followed by allowed operations has matrix
operator norm at most one in any orthonormal input and output bases.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 233–267 and 409–427. -/
theorem norm_preparedMatrix_le_one {P m n : Type} [Fintype m] [Fintype n] [DecidableEq n]
    (R : SourceInventory P) (U V : Fin R.length → HSpace)
    (η : ∀ i, U i ⊗[ℂ] V i) (hη : ∀ i, ‖η i‖ = 1) (ℓ : Layout P) {ℓ' : Layout P}
    (v : Word (SourceInventory.slotLayout R U V ++ ℓ) ℓ') (hv : v.IsAllowed)
    (bIn : OrthonormalBasis n ℂ (Mem ℓ)) (bOut : OrthonormalBasis m ℂ (Mem ℓ')) :
    ‖v.preparedMatrix R U V η ℓ bIn bOut‖ ≤ 1 := by
  classical
  let : DecidableEq n := Classical.decEq n
  have hp : (SourceInventory.prepareSlots R U V η ℓ).IsAllowed :=
    (isAllowed_castLayouts _ _ _).mpr
      ((SourceInventory.isAllowed_prepare_iff _ _).mpr
        (SourceInventory.isNormalized_ofSlots R U V η hη))
  change ‖LinearMap.toMatrix bIn.toBasis bOut.toBasis
    (v.eval.comp (SourceInventory.prepareSlots R U V η ℓ).eval).toLinearMap‖ ≤ 1
  exact (ContinuousLinearMap.norm_toMatrix_orthonormal
    (v.eval.comp (SourceInventory.prepareSlots R U V η ℓ).eval) bIn bOut).le.trans
      (norm_comp_le_one (v.norm_eval_le_one hv)
        ((SourceInventory.prepareSlots R U V η ℓ).norm_eval_le_one hp))

/-- Assigning a unit vector to each source half gives a contraction. This applies
both to orthonormal bases and to orthonormal families spanning proper subspaces.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 409–427. -/
theorem norm_preparedMatrix_tmul_le_one {P m n : Type}
    [Fintype m] [Fintype n] [DecidableEq n]
    (R : SourceInventory P) (U V : Fin R.length → HSpace)
    {A B : Fin R.length → Type}
    (u : ∀ i, A i → U i) (v : ∀ i, B i → V i)
    (hu : ∀ i a, ‖u i a‖ = 1) (hv : ∀ i b, ‖v i b‖ = 1)
    (ℓ : Layout P) {ℓ' : Layout P}
    (w : Word (SourceInventory.slotLayout R U V ++ ℓ) ℓ') (hw : w.IsAllowed)
    (bIn : OrthonormalBasis n ℂ (Mem ℓ)) (bOut : OrthonormalBasis m ℂ (Mem ℓ'))
    (a : ∀ i, A i × B i) :
    ‖w.preparedMatrix R U V (fun i ↦ u i (a i).1 ⊗ₜ[ℂ] v i (a i).2)
      ℓ bIn bOut‖ ≤ 1 := by
  apply norm_preparedMatrix_le_one R U V _ _ ℓ w hw bIn bOut
  exact fun i ↦ (TensorProduct.norm_tmul _ _).trans (by rw [hu, hv, one_mul])

end TNLean.PEPS.PairEffect.Word
