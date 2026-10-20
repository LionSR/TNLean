/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.Compression.ActualPureSourceReplacement
import TNLean.Lattice.Compression.SourcePhysicalDensity
/-! # Physical source replacement on the recorded product input

Tracing the original private registers in the prepared-column expansion gives
the physical source-replaced operator. The replacement matrices remain arbitrary,
and the ket and bra choices remain independent. The trace is complex-linear;
no positivity or normalization is needed.

Source: polynomial-PEPS manuscript (September 24, 2026), Theorem 5.2,
`04-compression.tex`, lines 279–355, 338–383 and 565–588.
-/

noncomputable section
open scoped Matrix ComplexConjugate
namespace TNLean.PEPS.PairEffect.SourceCircuit
variable {P : Type} {a : Layout P}

/-- The physical source-replaced output on the recorded product input is the
sum of the physical traces of the actual mixed chronological source columns.
The source replacements are arbitrary complex matrices.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 338–383 and 565–588. -/
theorem physicalSourceReplacedDensity_pure_eq_sum_actualColumnTraces
    {n x g : Type} [Fintype n] [Fintype x] [Fintype g]
    (physical garbage : Layout P) (w : SourceCircuit a (physical ++ garbage))
    (ψ : ProductInput a)
    (Y : ∀ e : sourceLocations w, branchLabels w e.1 → branchLabels w e.1 →
      Matrix (Fin (sourceDims w e).1 × Fin (sourceDims w e).2)
        (Fin (sourceDims w e).1 × Fin (sourceDims w e).2) ℂ)
    (bIn : OrthonormalBasis n ℂ (Mem a))
    (bPhysical : OrthonormalBasis x ℂ (Mem physical))
    (bGarbage : OrthonormalBasis g ℂ (Mem garbage)) :
    let bOut := (bPhysical.tensorProduct bGarbage).map (appendIso physical garbage).symm
    let bMapped := bOut.map
      (Layout.mapOwnerIso (affectedOwner (fun _ : P ↦ true)) (physical ++ garbage))
    physicalSourceReplacedDensity physical garbage w Y bIn bPhysical bGarbage
        (Matrix.vecMulVec (bIn.repr ψ.vector).ofLp
          (fun j ↦ conj (bIn.repr ψ.vector j))) =
      ∑ ξ, ∑ ζ,
        (coefficient (fun _ : P ↦ true) w ξ *
          conj (coefficient (fun _ : P ↦ true) w ζ)) •
          Matrix.partialTraceRight
            (w.partialSourceGlobalMatrix ψ ξ bMapped *
              SourceInventory.productSourceMatrix (partialSlots (fun _ : P ↦ true) w)
                (fun i ↦ Y (partialSlotEquiv (fun _ : P ↦ true) w i).1
                  (partialSlotChoice (fun _ : P ↦ true) w ξ i)
                  (partialSlotChoice (fun _ : P ↦ true) w ζ i)) *
              (w.partialSourceGlobalMatrix ψ ζ bMapped)ᴴ) := by
  classical
  dsimp only
  change Matrix.partialTraceRight
    (sourceReplacedDensity w Y bIn
      ((bPhysical.tensorProduct bGarbage).map (appendIso physical garbage).symm)
      (Matrix.vecMulVec (bIn.repr ψ.vector).ofLp
        (fun j ↦ conj (bIn.repr ψ.vector j)))) = _
  simpa only [map_sum, map_smul, Matrix.partialTraceRightLM, LinearMap.coe_mk,
    AddHom.coe_mk] using congrArg (Matrix.partialTraceRightLM (α := x) (β := g))
      (sourceReplacedDensity_pure_eq_sum_actualColumns w ψ Y bIn
        ((bPhysical.tensorProduct bGarbage).map (appendIso physical garbage).symm))

end TNLean.PEPS.PairEffect.SourceCircuit
