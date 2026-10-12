/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.EndpointMatrixAverage
import TNLean.PEPS.Approximation.SampledEndpointFactors
import TNLean.PEPS.Approximation.ActualSourceInputBasis
import TNLean.PEPS.Approximation.AllSourceSlots

/-! # Actual sampled endpoint words

The endpoint maps associated with each sampled source matrix form an actual source-free word on
the fixed source layout. Its average has the literal source matrix coordinates. Source:
polynomial-PEPS, `04-compression.tex`, lines 565–588.

## References

* OpenAI, *Polynomial PEPS approximation of gapped square-grid ground states*
  (September 24, 2026), proof of Theorem 5.2, `04-compression.tex`,
  lines 253–267, 279–355 and 565–588.
-/

noncomputable section
namespace TNLean.PEPS.PairEffect.SourceCircuit
variable {P : Type} {a b : Layout P}

variable (w : SourceCircuit a b) (k : ℕ)
  (lam : ∀ e : sourceLocations w, branchLabels w e.1 →
    Fin (min (sourceDims w e).1 (sourceDims w e).2) → ℝ)
  (E : ∀ e : sourceLocations w, branchLabels w e.1 →
    Matrix (Fin (sourceDims w e).1) (Fin (min (sourceDims w e).1 (sourceDims w e).2)) ℂ)
  (F : ∀ e : sourceLocations w, branchLabels w e.1 →
    Matrix (Fin (sourceDims w e).2) (Fin (min (sourceDims w e).1 (sourceDims w e).2)) ℂ)

/-- The source-free operator word formed from the actual sampled endpoint
matrices, sharing the original gate's ket–bra choice and each source's sample
index at both endpoints. The sampled matrices need not be positive.
Source: polynomial-PEPS 04-compression.tex, lines 279–309 and 565–588. -/
def sampledEndpointWord (ξ ζ : Choices (fun _ => true) w)
    (j : w.sourceLocations → Fin k) (ω : SourceGaussianSamples w k) :
    Word w.allResidualSourceLayout w.allResidualSourceLayout :=
  SourceInventory.endpointMatrixWord (partialSlots (fun _ => true) w) w.allSourceU w.allSourceV
    (fun _i => EuclideanSpace.basisFun _ ℂ) (fun _i => EuclideanSpace.basisFun _ ℂ)
    (fun i => sampledEndpointLeft w k lam E (partialSlotEquiv (fun _ => true) w i).1
      (partialSlotChoice (fun _ => true) w ξ i, partialSlotChoice (fun _ => true) w ζ i)
      (j (allSourceSlotEquiv w i)) ω)
    (fun i => sampledEndpointRight w k lam F (partialSlotEquiv (fun _ => true) w i).1
      (partialSlotChoice (fun _ => true) w ξ i, partialSlotChoice (fun _ => true) w ζ i)
      (j (allSourceSlotEquiv w i)) ω)

/-- The literal sampled endpoint operator introduces no source.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 279–309 and 565–588. -/
theorem sources_sampledEndpointWord (ξ ζ : Choices (fun _ => true) w)
    (j : w.sourceLocations → Fin k) (ω : SourceGaussianSamples w k) :
    (sampledEndpointWord w k lam E F ξ ζ j ω).sources = [] := by
  exact SourceInventory.sources_endpointWord ..

/-- The actual sampled source product is the average of the literal sampled
endpoint words. This assertion concerns arbitrary sampled operators.
Source: polynomial-PEPS 04-compression.tex, lines 279–309 and 565–588. -/
theorem sampledEndpointWord_average (ξ ζ : Choices (fun _ => true) w)
    (ω : SourceGaussianSamples w k) (x y : w.allSourceLabels) :
    (∏ i, sampledSourceMatrix w k lam E F (partialSlotEquiv (fun _ => true) w i).1
      (partialSlotChoice (fun _ => true) w ξ i) (partialSlotChoice (fun _ => true) w ζ i)
      ω (x i) (y i)) =
    ((k : ℂ)⁻¹ ^ (partialSlots (fun _ => true) w).length) *
      ∑ j : Fin (partialSlots (fun _ => true) w).length → Fin k,
        w.allSourceBasis.repr
          ((sampledEndpointWord w k lam E F ξ ζ
            (j ∘ (allSourceSlotEquiv w).symm) ω).eval (w.allSourceBasis y)) x := by
  classical
  simp_rw [sampledSourceMatrix_eq_endpoint_average]
  simpa only [sampledEndpointWord,
    allSourceBasis, Function.comp_apply, Equiv.symm_apply_apply] using
    SourceInventory.endpointMatrixAverage_eq_product
      (partialSlots (fun _ => true) w) w.allSourceU w.allSourceV
      (fun _i => EuclideanSpace.basisFun _ ℂ) (fun _i => EuclideanSpace.basisFun _ ℂ) k
      (fun i j => sampledEndpointLeft w k lam E (partialSlotEquiv (fun _ => true) w i).1
        (partialSlotChoice (fun _ => true) w ξ i,
          partialSlotChoice (fun _ => true) w ζ i) j ω)
      (fun i j => sampledEndpointRight w k lam F (partialSlotEquiv (fun _ => true) w i).1
        (partialSlotChoice (fun _ => true) w ξ i,
          partialSlotChoice (fun _ => true) w ζ i) j ω) x y

end TNLean.PEPS.PairEffect.SourceCircuit
