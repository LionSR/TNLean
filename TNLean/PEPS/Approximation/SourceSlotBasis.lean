/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.SourcePreparationCoordinates

/-!
# Orthonormal coordinates of all source registers

Tensoring the endpoint bases in the prescribed slot order gives an orthonormal
basis of the complete source memory. Tensoring this basis with the original
input basis gives orthonormal coordinates for all free inputs of the remaining
word, with columns equal to actual elementary source preparations.

Source: polynomial-PEPS manuscript (September 24, 2026), Theorem 5.2,
`04-compression.tex`, source-coordinate separation and contraction bounds,
lines 279–355 and 409–427.

Independently formalized from the manuscript; no upstream Lean proof text is
reused.
-/

noncomputable section

open scoped TensorProduct

namespace TNLean.PEPS.PairEffect.SourceInventory

variable {P : Type}

/-- The orthonormal basis of all source registers in the fixed slot order.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 279–355 and 409–427. -/
def slotBasis : (R : SourceInventory P) → (U V : Fin R.length → HSpace) →
    {A B : Fin R.length → Type} → [∀ i, Fintype (A i)] → [∀ i, Fintype (B i)] →
    (∀ i, OrthonormalBasis (A i) ℂ (U i)) →
    (∀ i, OrthonormalBasis (B i) ℂ (V i)) →
    OrthonormalBasis (∀ i, A i × B i) ℂ (Mem (slotLayout R U V))
  | [], _U, _V, A, B, _, _, _, _ =>
      (OrthonormalBasis.singleton Unit ℂ).reindex
        (Equiv.ofUnique Unit (∀ i : Fin 0, A i × B i))
  | r :: R, U, V, A, B, _, _, bU, bV =>
      ((((bU 0).tensorProduct (bV 0)).tensorProduct
        (slotBasis R (fun i ↦ U i.succ) (fun i ↦ V i.succ)
          (fun i ↦ bU i.succ) (fun i ↦ bV i.succ))).map
            ((TensorProduct.assocIsometry ℂ (U 0) (V 0)
              (Mem (slotLayout R (fun i ↦ U i.succ) (fun i ↦ V i.succ)))).trans
                (Layout.memCongr (slotLayout_cons r R U V).symm))).reindex
        (Fin.consEquiv (fun i ↦ A i × B i))

/-- A source basis vector is the actual joint vector of its endpoint assignments. -/
theorem slotBasis_apply (R : SourceInventory P) (U V : Fin R.length → HSpace)
    {A B : Fin R.length → Type} [∀ i, Fintype (A i)] [∀ i, Fintype (B i)]
    (bU : ∀ i, OrthonormalBasis (A i) ℂ (U i))
    (bV : ∀ i, OrthonormalBasis (B i) ℂ (V i)) (a : ∀ i, A i × B i) :
    slotBasis R U V bU bV a =
      slotVector R U V (fun i ↦ bU i (a i).1 ⊗ₜ bV i (a i).2) := by
  induction R with
  | nil =>
    change ((OrthonormalBasis.singleton Unit ℂ).reindex
      (Equiv.ofUnique Unit (∀ i : Fin 0, A i × B i))) a = (1 : ℂ)
    rw [OrthonormalBasis.reindex_apply, OrthonormalBasis.singleton_apply]
  | cons r R ih =>
    simp only [slotBasis, OrthonormalBasis.reindex_apply, Fin.consEquiv_symm_apply,
      OrthonormalBasis.map_apply, OrthonormalBasis.tensorProduct_apply', ih]
    rfl

/-- Orthonormal coordinates of all source registers followed by the physical input.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 409–427. -/
def preparedInputBasis (R : SourceInventory P) (U V : Fin R.length → HSpace)
    {A B : Fin R.length → Type} [∀ i, Fintype (A i)] [∀ i, Fintype (B i)]
    (bU : ∀ i, OrthonormalBasis (A i) ℂ (U i))
    (bV : ∀ i, OrthonormalBasis (B i) ℂ (V i)) (ℓ : Layout P)
    {n : Type} [Fintype n] (bIn : OrthonormalBasis n ℂ (Mem ℓ)) :
    OrthonormalBasis ((∀ i, A i × B i) × n) ℂ (Mem (slotLayout R U V ++ ℓ)) :=
  ((slotBasis R U V bU bV).tensorProduct bIn).map (appendIso (slotLayout R U V) ℓ).symm

/-- Each input-basis vector is obtained by an actual elementary source preparation. -/
theorem preparedInputBasis_apply (R : SourceInventory P) (U V : Fin R.length → HSpace)
    {A B : Fin R.length → Type} [∀ i, Fintype (A i)] [∀ i, Fintype (B i)]
    (bU : ∀ i, OrthonormalBasis (A i) ℂ (U i))
    (bV : ∀ i, OrthonormalBasis (B i) ℂ (V i)) (ℓ : Layout P)
    {n : Type} [Fintype n] (bIn : OrthonormalBasis n ℂ (Mem ℓ))
    (a : ∀ i, A i × B i) (j : n) :
    preparedInputBasis R U V bU bV ℓ bIn (a, j) =
      (prepareSlots R U V (fun i ↦ bU i (a i).1 ⊗ₜ bV i (a i).2) ℓ).eval (bIn j) := by
  simp only [preparedInputBasis, OrthonormalBasis.map_apply,
    OrthonormalBasis.tensorProduct_apply, slotBasis_apply,
    eval_prepareSlots_eq_appendIso_symm]

end TNLean.PEPS.PairEffect.SourceInventory
