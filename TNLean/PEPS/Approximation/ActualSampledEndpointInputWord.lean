/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.ActualSampledEndpointWord
import TNLean.PEPS.Approximation.SourceColumnContraction

/-! # Sampled endpoint matrices on the actual source input

The literal endpoint word is transported to the input of the recorded private
preparation, including its terminal scalar factor. In the actual input basis,
the product of sampled source matrices is the weighted sum of these word
matrices. Every summand uses one original global sample assignment, shared by
the two endpoints of each source. The ket and bra choices remain independent.

The identities include an empty sample set, an empty source inventory and
zero-dimensional source halfspaces. They impose no positivity, normalization
or contraction hypothesis.

Source: polynomial-PEPS manuscript (September 24, 2026), Theorem 5.2,
`04-compression.tex`, lines 253–267, 279–355 and 565–588.
-/

noncomputable section
open ContinuousLinearMap
namespace TNLean.PEPS.PairEffect.SourceCircuit
variable {P : Type} {a b : Layout P}

variable (w : SourceCircuit a b) (k : ℕ)
  (lam : ∀ e : sourceLocations w, branchLabels w e.1 →
    Fin (min (sourceDims w e).1 (sourceDims w e).2) → ℝ)
  (E : ∀ e : sourceLocations w, branchLabels w e.1 →
    Matrix (Fin (sourceDims w e).1) (Fin (min (sourceDims w e).1 (sourceDims w e).2)) ℂ)
  (F : ∀ e : sourceLocations w, branchLabels w e.1 →
    Matrix (Fin (sourceDims w e).2) (Fin (min (sourceDims w e).1 (sourceDims w e).2)) ℂ)

/-- The literal sampled endpoint word on the same unit-memory input as the
actual private preparation. Source: polynomial-PEPS Theorem 5.2,
`04-compression.tex`, lines 253–267, 279–355 and 565–588. -/
def sampledEndpointInputWord (ξ ζ : Choices (fun _ ↦ true) w)
    (j : w.sourceLocations → Fin k) (ω : SourceGaussianSamples w k) :
    Word (w.allResidualSourceLayout ++ []) (w.allResidualSourceLayout ++ []) :=
  (sampledEndpointWord w k lam E F ξ ζ j ω).castLayouts
    (List.append_nil _).symm (List.append_nil _).symm

/-- Transporting to the actual source input introduces no source preparation.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 253–267 and 565–588. -/
theorem sources_sampledEndpointInputWord (ξ ζ : Choices (fun _ ↦ true) w)
    (j : w.sourceLocations → Fin k) (ω : SourceGaussianSamples w k) :
    (sampledEndpointInputWord w k lam E F ξ ζ j ω).sources = [] :=
  (Word.sources_castLayouts ..).trans (sources_sampledEndpointWord ..)

/-- The canonical unit-memory transport preserves each sampled endpoint entry
in the literal source basis. Source: polynomial-PEPS Theorem 5.2,
`04-compression.tex`, lines 253–267, 279–355 and 565–588. -/
theorem actualSourceInputBasis_repr_sampledEndpointInputWord
    (ξ ζ : Choices (fun _ ↦ true) w) (j : w.sourceLocations → Fin k)
    (ω : SourceGaussianSamples w k) (x y : w.allSourceLabels) :
    w.actualSourceInputBasis.repr
        ((sampledEndpointInputWord w k lam E F ξ ζ j ω).eval
          (w.actualSourceInputBasis y)) x =
      w.allSourceBasis.repr
        ((sampledEndpointWord w k lam E F ξ ζ j ω).eval (w.allSourceBasis y)) x := by
  change w.allSourceBasis.repr
    ((Layout.memCongr (List.append_nil w.allResidualSourceLayout).symm).symm
      ((sampledEndpointInputWord w k lam E F ξ ζ j ω).eval
        (Layout.memCongr (List.append_nil w.allResidualSourceLayout).symm
          (w.allSourceBasis y)))) x = _
  simp only [sampledEndpointInputWord, Word.eval_castLayouts, comp_apply, isoL_apply,
    LinearIsometryEquiv.symm_apply_apply]

/-- The product of the actual sampled source matrices is the weighted sum of
the literal endpoint-word matrices in the actual source-input basis. One
global sample assignment is retained in each summand, including both endpoints
of every source. Empty sample sets and source inventories are included.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 279–355 and 565–588. -/
theorem sampledEndpointInputMatrix_average (ξ ζ : Choices (fun _ ↦ true) w)
    (ω : SourceGaussianSamples w k) :
    SourceInventory.productSourceMatrix (partialSlots (fun _ ↦ true) w)
        (fun i ↦ sampledSourceMatrix w k lam E F
          (partialSlotEquiv (fun _ ↦ true) w i).1
          (partialSlotChoice (fun _ ↦ true) w ξ i)
          (partialSlotChoice (fun _ ↦ true) w ζ i) ω) =
      ((k : ℂ)⁻¹ ^ (partialSlots (fun _ ↦ true) w).length) •
        ∑ j : Fin (partialSlots (fun _ ↦ true) w).length → Fin k,
          LinearMap.toMatrix w.actualSourceInputBasis.toBasis w.actualSourceInputBasis.toBasis
            (sampledEndpointInputWord w k lam E F ξ ζ
              (j ∘ (allSourceSlotEquiv w).symm) ω).eval.toLinearMap := by
  classical
  simp_rw [← matrix_repr_eval_eq_toMatrix]
  ext x y
  simpa only [SourceInventory.productSourceMatrix, Matrix.smul_apply, Matrix.sum_apply,
    smul_eq_mul,
    actualSourceInputBasis_repr_sampledEndpointInputWord] using
      sampledEndpointWord_average w k lam E F ξ ζ ω x y

end TNLean.PEPS.PairEffect.SourceCircuit
