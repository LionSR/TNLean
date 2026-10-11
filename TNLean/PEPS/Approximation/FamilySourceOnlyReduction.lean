/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import TNLean.PEPS.Approximation.FamilyPhysicalReadout
import TNLean.PEPS.Approximation.SourceOnlyReduction

/-! # Source-only physical density with original local dimensions

The physical register at party `p` has its original dimension `d p`.
The regional readout retains exactly the physical coordinates in the specified
region and discards the exterior physical registers and the actual private
memory. The source-only replacement uses the original gate-count upper bound.

Source: polynomial-PEPS 04-compression.tex, lines 137–151 and 199–251.
-/

/-!
Source: September 24, 2026, polynomial-PEPS manuscript, 04-compression.tex,
eq:compression-effect-circuit-error; Theorem 5.2, lines 137–151 and 199–251.
Manuscript revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Independently formalized; no upstream Lean proof text reused.
-/

noncomputable section
open ContinuousLinearMap
namespace TNLean.PEPS.PairEffect.OriginalCircuit
variable {P : Type} [Fintype P] [DecidableEq P]

/-- The actual source-only density reduction for arbitrary original local
physical dimensions, on the source's normalized whole-party product input.
No padding, equal-dimension premise or supplied readout identity is required.
Private dimensions are finite, as in the manuscript, and have no numerical bound.
Source: polynomial-PEPS 04-compression.tex, lines 137–151 and 199–251. -/
theorem rectangularTraceNorm_sourceOnly_family_regional_density_sub_le_half
    {r M : ℕ} {S ε : ℝ} (hε : 0 < ε) (d : P → ℕ)
    (H : P → HSpace) (x : ∀ p, H p) (hx : ∀ p, ‖x p‖ = 1)
    (priv : Layout P) [FiniteDimensional ℂ (Mem priv).carrier]
    (w : OriginalCircuit (ProductInput.wholePartyLayout H)
      (familyPhysicalOutputLayout d Finset.univ.toList priv))
    (hb : w.IsExpansionBounded r S) (hcount : w.nonprivateCount ≤ M) (A : Finset P) :
    let ψ := (ProductInput.ofAllParties H x hx).vector
    let K := familyRegionalPhysicalReadout d Finset.univ.toList (Finset.nodup_toList _)
      (fun p ↦ Finset.mem_toList.mpr (Finset.mem_univ p)) priv A
    Matrix.rectangularTraceNorm
      (w.produce.replacementPhysicalDensity (sourceGateBudget_pos hε M)
          w.isAllowed_produce ((w.isExpansionBounded_produce_iff r S).mpr hb) (isoL K) ψ -
        Matrix.partialTraceRight (Matrix.euclideanOuterProduct (K (w.eval ψ)) (K (w.eval ψ)))) ≤
      ε / 2 :=
  w.rectangularTraceNorm_sourceOnly_density_sub_le_half_of_count_le hε hb hcount
    (familyRegionalPhysicalReadout d Finset.univ.toList (Finset.nodup_toList _)
      (fun p ↦ Finset.mem_toList.mpr (Finset.mem_univ p)) priv A) _
    (ProductInput.norm_vector _).le
end TNLean.PEPS.PairEffect.OriginalCircuit
