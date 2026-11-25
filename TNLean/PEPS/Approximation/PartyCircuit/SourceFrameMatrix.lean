/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.PartyCircuit.SourceBlockMatrix
import TNLean.PEPS.Approximation.PartyCircuit.SourceSlotMaps

/-!
# Joint contractions in source frames

Endpoint contractions map finite source coordinates into the actual slot
registers. The coordinate spaces may be proper subspaces: their images need not
span the registers. The complete matrix of prepared branches is still a
contraction on all coordinate and physical input vectors.

Source: polynomial-PEPS manuscript (September 24, 2026), Theorem 5.2,
`04-compression.tex`, Schmidt frames and free-input contractions,
lines 279–299 and 383–427.

Independently formalized from the manuscript; no upstream Lean proof text is
reused.
-/

noncomputable section

open scoped Matrix Kronecker Matrix.Norms.L2Operator
open Matrix ManyBody

namespace QuantumCircuit.Party.Word

open SourceInventory

variable {P : Type} [Fintype P] [DecidableEq P] (R : SourceInventory P)
  (B B' : SlotBases R.length) (f : ∀ i, Matrix (B'.left i) (B.left i) ℂ)
  (g : ∀ i, Matrix (B'.right i) (B.right i) ℂ) (X : P → Type) [∀ p, Fintype (X p)]
  [∀ p, DecidableEq (X p)] {Y : P → Type} [∀ p, Fintype (Y p)]

/-- The complete matrix of an actual branch in the given endpoint frames: the columns of the
endpoint maps are the frame vectors. The frame images need not span the slot registers.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 279–299 and 383–427. -/
def sourceFrameMatrix (v : Word (slotSystem R B' X) Y) :
    Matrix (Config Y) ((∀ i, B.left i × B.right i) × Config X) ℂ :=
  fun k a ↦ v.preparedMatrix R B' (fun i ↦ EuclideanSpace.vecKron
    (Matrix.toEuclideanLin (f i) (EuclideanSpace.single (a.1 i).1 1))
    (Matrix.toEuclideanLin (g i) (EuclideanSpace.single (a.1 i).2 1))) X k a.2

omit [Fintype P] [DecidableEq P] in
/-- Two endpoint maps applied to a product vector give the product of the images. -/
private theorem pairMap_vecKron {α β α' β' : Type} [Fintype α] [DecidableEq α] [Fintype β]
    [DecidableEq β] (A : Matrix α' α ℂ) (A' : Matrix β' β ℂ) (x : EuclideanSpace ℂ α)
    (y : EuclideanSpace ℂ β) :
    EuclideanSpace.pairMap A A' (EuclideanSpace.vecKron x y) =
      EuclideanSpace.vecKron (Matrix.toEuclideanLin A x) (Matrix.toEuclideanLin A' y) := by
  ext ⟨c, d⟩
  change ((A ⊗ₖ A') *ᵥ fun z ↦ x z.1 * y z.2) (c, d) = (A *ᵥ x.ofLp) c * (A' *ᵥ y.ofLp) d
  simp only [mulVec, dotProduct, kroneckerMap_apply, Fintype.sum_prod_type, Finset.sum_mul,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by ring

omit [∀ p, Fintype (Y p)] in
/-- The frame matrix is the full free-input matrix of the actual endpoint-map
composition. The endpoint maps are fixed before the source vector is chosen.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 279–299 and 409–427. -/
theorem sourceFrameMatrix_eq_freeSourceMatrix (v : Word (slotSystem R B' X) Y) :
    v.sourceFrameMatrix R B B' f g X =
      Word.freeSourceMatrix R B X (PartyCircuit.comp (mapSourceSlots R B B' f g X) v) := by
  ext k ⟨a, j⟩
  rw [freeSourceMatrix_apply, preparedMatrix, Word.op_comp, Matrix.mul_assoc,
    op_mapSourceSlots_prepareSlots]
  simp only [pairMap_vecKron]
  rfl

/-- Endpoint contractions followed by an allowed word give a contraction on the
whole coordinate/input space, including proper source-frame subspaces.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 409–427. -/
theorem norm_sourceFrameMatrix_le_one (hf : ∀ i, ‖f i‖ ≤ 1) (hg : ∀ i, ‖g i‖ ≤ 1)
    (v : Word (slotSystem R B' X) Y) (hv : v.IsAllowed) :
    ‖v.sourceFrameMatrix R B B' f g X‖ ≤ 1 := by
  rw [sourceFrameMatrix_eq_freeSourceMatrix]
  exact norm_freeSourceMatrix_le_one R B X _ ⟨(mapSourceSlots_spec X R B B' f g hf hg).1, hv⟩

end QuantumCircuit.Party.Word
