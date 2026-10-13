/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.ActualMixedSourceMatrix
import TNLean.PEPS.Approximation.ActualSampledEndpointInputWord

/-! # Actual sampled source contraction in party coordinates

The literal sampled source matrix is expanded as a sum of endpoint-word
matrices. Each word is then contracted between the actual chronological ket
and bra columns. Its actual singleton restrictions give the party factors.
One global sample assignment is retained in each summand, shared by both
endpoints of every original source. The exterior owner remains in the product.

Source: polynomial-PEPS manuscript (September 24, 2026), Theorem 5.2,
`04-compression.tex`, lines 279–355, 409–434 and 565–588.
-/

noncomputable section
open scoped Matrix
namespace TNLean.PEPS.PairEffect

private theorem sandwich_average_of_summands
    {S T J : Type} [Fintype S] [Fintype J]
    (A B : Matrix T S ℂ) (X : Matrix S S ℂ) (c : ℂ)
    (U : J → Matrix S S ℂ) (H : J → Matrix T T ℂ)
    (hX : X = c • ∑ j, U j) (hH : ∀ j, A * U j * Bᴴ = H j) :
    A * X * Bᴴ = c • ∑ j, H j := by
  rw [hX]
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sum, Matrix.sum_mul, hH]

namespace SourceCircuit
variable {P : Type} [Fintype P] [DecidableEq P] {a b : Layout P}
variable {I O : Option {_p : P // true = true} → Type}
variable [∀ q, Fintype (I q)] [∀ q, Fintype (O q)]

open Classical in
/-- The actual sampled source contraction is a weighted sum of the actual
local mixed matrices, before any exterior scalar is absorbed or physical
register is traced out. Empty sample and source sets are included.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 279–355,
409–434 and 565–588. -/
theorem partialSourceGlobalMatrix_sampled_eq_sum_partyProduct
    (w : SourceCircuit a b) (ψ : ProductInput a) (k : ℕ)
    (lam : ∀ e : sourceLocations w, branchLabels w e.1 →
      Fin (min (sourceDims w e).1 (sourceDims w e).2) → ℝ)
    (E : ∀ e : sourceLocations w, branchLabels w e.1 →
      Matrix (Fin (sourceDims w e).1) (Fin (min (sourceDims w e).1 (sourceDims w e).2)) ℂ)
    (F : ∀ e : sourceLocations w, branchLabels w e.1 →
      Matrix (Fin (sourceDims w e).2) (Fin (min (sourceDims w e).1 (sourceDims w e).2)) ℂ)
    (ξ ζ : Choices (fun _ : P ↦ true) w) (ω : SourceGaussianSamples w k)
    (B : ∀ q, OrthonormalBasis (I q) ℂ
      (Mem (Layout.atParty q (w.allResidualSourceLayout ++ []))))
    (C : ∀ q, OrthonormalBasis (O q) ℂ
      (Mem (Layout.atParty q (Layout.mapOwner (affectedOwner (fun _ : P ↦ true)) b))))
    (ps : List (Option {_p : P // true = true})) (hn : ps.Nodup)
    (hc : ∀ q, q ∈ ps) :
    w.partialSourceGlobalMatrix ψ ξ
        (partyGroupedBasis (Layout.mapOwner (affectedOwner (fun _ : P ↦ true)) b)
          C ps hn hc) *
      SourceInventory.productSourceMatrix (partialSlots (fun _ ↦ true) w)
        (fun i ↦ sampledSourceMatrix w k lam E F
          (partialSlotEquiv (fun _ ↦ true) w i).1
          (partialSlotChoice (fun _ ↦ true) w ξ i)
          (partialSlotChoice (fun _ ↦ true) w ζ i) ω) *
      (w.partialSourceGlobalMatrix ψ ζ
        (partyGroupedBasis (Layout.mapOwner (affectedOwner (fun _ : P ↦ true)) b)
          C ps hn hc))ᴴ =
      ((k : ℂ)⁻¹ ^ (partialSlots (fun _ ↦ true) w).length) •
        ∑ j : Fin (partialSlots (fun _ ↦ true) w).length → Fin k,
          dependentPhysicalProductFamilyMatrix (fun q ↦
            w.partialSourcePartyMatrix ψ ξ B C q *
              LinearMap.toMatrix (B q).toBasis (B q).toBasis
                (((sampledEndpointInputWord w k lam E F ξ ζ
                    (j ∘ (allSourceSlotEquiv w).symm) ω).restrict (partySelector q)
                  (sources_sampledEndpointInputWord w k lam E F ξ ζ
                    (j ∘ (allSourceSlotEquiv w).symm) ω)).eval.toLinearMap) *
              (w.partialSourcePartyMatrix ψ ζ B C q)ᴴ) := by
  classical
  refine sandwich_average_of_summands _ _ _ _ _ _
    (sampledEndpointInputMatrix_average w k lam E F ξ ζ ω) ?_
  intro j
  exact partialSourceGlobalMatrix_mixed_word w ψ ξ ζ
    (sampledEndpointInputWord w k lam E F ξ ζ (j ∘ (allSourceSlotEquiv w).symm) ω)
    (sources_sampledEndpointInputWord w k lam E F ξ ζ
      (j ∘ (allSourceSlotEquiv w).symm) ω) B C ps hn hc

end SourceCircuit
end TNLean.PEPS.PairEffect
