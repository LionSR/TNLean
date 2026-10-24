/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.Compression.SourceCompressedDensity
import TNLean.Lattice.Compression.ActualPureSourceMatrix

/-! # Source replacement on the recorded product input

The source-replaced output on the original product input is a finite sum of
mixed products of the actual chronological source columns. The original
coefficients, source occurrences and independent ket and bra choices are
retained. The replacement matrices are arbitrary; no positivity or
normalization of the output is assumed.

Source: polynomial-PEPS manuscript (September 24, 2026), Theorem 5.2,
`04-compression.tex`, lines 279–355, 409–434 and 565–588.
-/

noncomputable section
open scoped Matrix ComplexConjugate
namespace TNLean.Lattice.PartyCircuit.SourceCircuit
variable {P : Type} {a b : Layout P}

/-- Source replacement on the recorded product input retains the actual
chronological column matrices and the original ket and bra coefficients.
The local replacement matrices may be arbitrary complex matrices.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 279–355,
409–434 and 565–588. -/
theorem sourceReplacedDensity_pure_eq_sum_actualColumns
    {m n : Type} [Fintype m] [Fintype n]
    (w : SourceCircuit a b) (ψ : ProductInput a)
    (Y : ∀ e : sourceLocations w, branchLabels w e.1 → branchLabels w e.1 →
      Matrix (Fin (sourceDims w e).1 × Fin (sourceDims w e).2)
        (Fin (sourceDims w e).1 × Fin (sourceDims w e).2) ℂ)
    (bIn : OrthonormalBasis n ℂ (Mem a)) (bOut : OrthonormalBasis m ℂ (Mem b)) :
    sourceReplacedDensity w Y bIn bOut
        (Matrix.vecMulVec (bIn.repr ψ.vector).ofLp
          (fun j ↦ conj (bIn.repr ψ.vector j))) =
      ∑ ξ, ∑ ζ,
        (coefficient (fun _ : P ↦ true) w ξ *
          conj (coefficient (fun _ : P ↦ true) w ζ)) •
          (w.partialSourceGlobalMatrix ψ ξ
              (bOut.map (Layout.mapOwnerIso (affectedOwner (fun _ : P ↦ true)) b)) *
            SourceInventory.productSourceMatrix (partialSlots (fun _ : P ↦ true) w)
              (fun i ↦ Y (partialSlotEquiv (fun _ : P ↦ true) w i).1
                (partialSlotChoice (fun _ : P ↦ true) w ξ i)
                (partialSlotChoice (fun _ : P ↦ true) w ζ i)) *
            (w.partialSourceGlobalMatrix ψ ζ
              (bOut.map (Layout.mapOwnerIso (affectedOwner (fun _ : P ↦ true)) b)))ᴴ) := by
  classical
  have hinput : (bIn.map (Layout.mapOwnerIso (affectedOwner (fun _ : P ↦ true)) a)).repr
      (Layout.mapOwnerIso (affectedOwner (fun _ : P ↦ true)) a ψ.vector) =
      bIn.repr ψ.vector := by
    change bIn.repr ((Layout.mapOwnerIso (affectedOwner (fun _ : P ↦ true)) a).symm
      (Layout.mapOwnerIso (affectedOwner (fun _ : P ↦ true)) a ψ.vector)) = _
    rw [LinearIsometryEquiv.symm_apply_apply]
  unfold sourceReplacedDensity Word.sourceOperatorDensity
  dsimp only
  apply Finset.sum_congr rfl
  intro ξ _
  apply Finset.sum_congr rfl
  intro ζ _
  apply congrArg (fun M ↦
    (coefficient (fun _ : P ↦ true) w ξ *
      conj (coefficient (fun _ : P ↦ true) w ζ)) • M)
  have h := sourceContraction_preparedDensityCoefficient_pure_eq_mul w ψ ξ ζ
    (bIn.map (Layout.mapOwnerIso (affectedOwner (fun _ : P ↦ true)) a))
    (bOut.map (Layout.mapOwnerIso (affectedOwner (fun _ : P ↦ true)) b))
    (fun i ↦ Y (partialSlotEquiv (fun _ : P ↦ true) w i).1
      (partialSlotChoice (fun _ : P ↦ true) w ξ i)
      (partialSlotChoice (fun _ : P ↦ true) w ζ i))
  dsimp only at h
  rw [hinput] at h
  exact h

end TNLean.Lattice.PartyCircuit.SourceCircuit
