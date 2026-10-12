/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.ActualSampledPartyContraction
import TNLean.PEPS.Approximation.PartyProductPartialTrace
import Mathlib.LinearAlgebra.Matrix.Reindex

/-! # Local output traces of the actual sampled contraction

Each chosen party output coordinate set is a product of retained and discarded
indices. Reindexing the actual global contraction into these two families and
tracing the discarded family equals the sampled sum of the products of the
local traces. The original joint sample is retained in every summand.

This is a coordinate identity for the specified output bases. Identifying
these bases with the physical and private register bases is a separate step.
The exterior owner remains in the product, and zero matrices and empty
coordinate sets are included.

Source: polynomial-PEPS manuscript (September 24, 2026), Theorem 5.2,
`04-compression.tex`, lines 409–434 and 565–588, especially 574–579.
-/

noncomputable section
open scoped Matrix
namespace TNLean.PEPS.PairEffect.SourceCircuit
variable {P : Type} [Fintype P] [DecidableEq P] {a b : Layout P}
variable {I X E : Option {_p : P // true = true} → Type}
variable [∀ q, Fintype (I q)] [∀ q, Fintype (X q)] [∀ q, Fintype (E q)]

open Classical in
/-- Tracing the discarded coordinate of each chosen party output basis factors
through the actual singleton restrictions. This concerns the specified coordinate
splitting; no identification with a physical output state is assumed.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 574–579. -/
theorem partialSourceGlobalMatrix_sampled_partialTrace_eq_sum_partyProduct
    (w : SourceCircuit a b) (ψ : ProductInput a) (k : ℕ)
    (lam : ∀ e : sourceLocations w, branchLabels w e.1 →
      Fin (min (sourceDims w e).1 (sourceDims w e).2) → ℝ)
    (L : ∀ e : sourceLocations w, branchLabels w e.1 →
      Matrix (Fin (sourceDims w e).1) (Fin (min (sourceDims w e).1 (sourceDims w e).2)) ℂ)
    (R : ∀ e : sourceLocations w, branchLabels w e.1 →
      Matrix (Fin (sourceDims w e).2) (Fin (min (sourceDims w e).1 (sourceDims w e).2)) ℂ)
    (ξ ζ : Choices (fun _ : P ↦ true) w) (ω : SourceGaussianSamples w k)
    (B : ∀ q, OrthonormalBasis (I q) ℂ
      (Mem (Layout.atParty q (w.allResidualSourceLayout ++ []))))
    (C : ∀ q, OrthonormalBasis (X q × E q) ℂ
      (Mem (Layout.atParty q (Layout.mapOwner (affectedOwner (fun _ : P ↦ true)) b))))
    (ps : List (Option {_p : P // true = true})) (hn : ps.Nodup)
    (hc : ∀ q, q ∈ ps) :
    Matrix.partialTraceRight
      ((w.partialSourceGlobalMatrix ψ ξ
          (partyGroupedBasis (Layout.mapOwner (affectedOwner (fun _ : P ↦ true)) b)
            C ps hn hc) *
        SourceInventory.productSourceMatrix (partialSlots (fun _ ↦ true) w)
          (fun i ↦ sampledSourceMatrix w k lam L R
            (partialSlotEquiv (fun _ ↦ true) w i).1
            (partialSlotChoice (fun _ ↦ true) w ξ i)
            (partialSlotChoice (fun _ ↦ true) w ζ i) ω) *
        (w.partialSourceGlobalMatrix ψ ζ
          (partyGroupedBasis (Layout.mapOwner (affectedOwner (fun _ : P ↦ true)) b)
            C ps hn hc))ᴴ).submatrix
          (Equiv.arrowProdEquivProdArrow (Option {_p : P // true = true}) X E).symm
          (Equiv.arrowProdEquivProdArrow (Option {_p : P // true = true}) X E).symm) =
      ((k : ℂ)⁻¹ ^ (partialSlots (fun _ ↦ true) w).length) •
        ∑ j : Fin (partialSlots (fun _ ↦ true) w).length → Fin k,
          dependentPhysicalProductFamilyMatrix (fun q ↦
            Matrix.partialTraceRight
              (w.partialSourcePartyMatrix ψ ξ B C q *
                LinearMap.toMatrix (B q).toBasis (B q).toBasis
                  (((sampledEndpointInputWord w k lam L R ξ ζ
                      (j ∘ (allSourceSlotEquiv w).symm) ω).restrict (partySelector q)
                    (sources_sampledEndpointInputWord w k lam L R ξ ζ
                      (j ∘ (allSourceSlotEquiv w).symm) ω)).eval.toLinearMap) *
                (w.partialSourcePartyMatrix ψ ζ B C q)ᴴ)) := by
  classical
  let e := Equiv.arrowProdEquivProdArrow (Option {_p : P // true = true}) X E
  let T := Matrix.partialTraceRightLM.comp
    (Matrix.reindexLinearEquiv ℂ ℂ e e).toLinearMap
  have ht (M : (q : Option {_p : P // true = true}) →
      Matrix (X q × E q) (X q × E q) ℂ) :
      T (dependentPhysicalProductFamilyMatrix M) =
        dependentPhysicalProductFamilyMatrix (fun q ↦ Matrix.partialTraceRight (M q)) := by
    change Matrix.partialTraceRight (fun xi yj ↦
      ∏ q, M q (xi.1 q, xi.2 q) (yj.1 q, yj.2 q)) = _
    exact partialTraceRight_partyProductMatrix M
  have h := congrArg T
    (partialSourceGlobalMatrix_sampled_eq_sum_partyProduct w ψ k lam L R ξ ζ ω B C ps hn hc)
  simp only [map_smul, map_sum, ht] at h
  exact h

end TNLean.PEPS.PairEffect.SourceCircuit
