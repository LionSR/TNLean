/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.ReceivingRegions
import TNLean.PEPS.AreaLaw.Scan.AugmentedPartition

/-!
# Augmented receiving regions of finite collar histories

Let X be the intersection of the chosen color with the target. For a completed
history, or immediately after its next fill and before its charge, let U be the
positive-depth part of the physical near region and Y the physical middle. The
augmented near region is C together with X ∪ U, the augmented middle is Y, and
the augmented far region is R together with the physical complement of
X ∪ (U ∪ Y). The physical sites enter the augmented domain by the left inclusion;
C and R are the two right-inclusion sites labelled false and true.

## Main statements

- `CollarScan.state_augmentedPartition_eq_target_near_middle`: the three
  augmented regions after a completed history.
- `CollarScan.oldChargeState_augmentedPartition_eq_target_near_middle`: the
  regions after the next fill and before its charge.

## References

OpenAI, *A two-dimensional area law from a global spectral gap*,
`08-scanner.tex`, lines 21–24 and 83–98, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

namespace TNLean.PEPS.AreaLaw.Scan.CollarScan

variable {I : Type*} [Fintype I] [LinearOrder I]

/-- The full augmented partition of an actual completed history consists of the
chosen-color target and positive near region with C, the actual middle, and their
physical complement with R. Source: OpenAI, A two-dimensional area law from a global
spectral gap, 08-scanner.tex, lines 21–24 and 83–98, at
openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a. -/
theorem state_augmentedPartition_eq_target_near_middle
    {Λ T : Finset (ℤ × ℤ)} (hT : T.Nonempty)
    (S : CollarScan (Site Λ) I)
    (hdepth : S.depth = fun x ↦ ambientDepth T hT x.val) {k : ℕ}
    (h : History S.K S.m S.M k) (g : Fin S.K) :
    let X : Finset (Site Λ) := S.A.filter fun x ↦ x.val ∈ T
    let σ : PhysicalPartition (Site Λ) := S.state h g
    let U : Finset (Site Λ) := positiveNear S.depth σ
    let Y : Finset (Site Λ) := middle σ
    augmentedPartition σ =
      ({ P := insert (Sum.inr false)
           ((X ∪ U).image (Sum.inl : Site Λ → Site Λ ⊕ Bool))
         Y := Y.image (Sum.inl : Site Λ → Site Λ ⊕ Bool)
         F := insert (Sum.inr true)
           (((X ∪ (U ∪ Y))ᶜ).image (Sum.inl : Site Λ → Site Λ ⊕ Bool)) } :
        TensorPower.ReplicaTransport.PYF (Site Λ ⊕ Bool)) := by
  simpa only [←(state_receiving_regions hT S hdepth h g).1,
    ←Finset.union_assoc, (state_receiving_regions hT S hdepth h g).2.1,
    ←(state_receiving_regions hT S hdepth h g).2.2] using
      (augmentedPartition_eq_images (S.state h g))

/-- The full augmented partition after an actual fill and before its charge consists
of the chosen-color target and positive near region with C, the actual middle, and their
physical complement with R. Source: OpenAI, A two-dimensional area law from a global
spectral gap, 08-scanner.tex, lines 21–24 and 83–98, at
openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a. -/
theorem oldChargeState_augmentedPartition_eq_target_near_middle
    {Λ T : Finset (ℤ × ℤ)} (hT : T.Nonempty)
    (S : CollarScan (Site Λ) I)
    (hdepth : S.depth = fun x ↦ ambientDepth T hT x.val) {k : ℕ}
    (h : History S.K S.m S.M k) (g : Fin S.K) :
    let X : Finset (Site Λ) := S.A.filter fun x ↦ x.val ∈ T
    let σ : PhysicalPartition (Site Λ) := S.oldChargeState h g
    let U : Finset (Site Λ) := positiveNear S.depth σ
    let Y : Finset (Site Λ) := middle σ
    augmentedPartition σ =
      ({ P := insert (Sum.inr false)
           ((X ∪ U).image (Sum.inl : Site Λ → Site Λ ⊕ Bool))
         Y := Y.image (Sum.inl : Site Λ → Site Λ ⊕ Bool)
         F := insert (Sum.inr true)
           (((X ∪ (U ∪ Y))ᶜ).image (Sum.inl : Site Λ → Site Λ ⊕ Bool)) } :
        TensorPower.ReplicaTransport.PYF (Site Λ ⊕ Bool)) := by
  simpa only [←(oldChargeState_receiving_regions hT S hdepth h g).1,
    ←Finset.union_assoc, (oldChargeState_receiving_regions hT S hdepth h g).2.1,
    ←(oldChargeState_receiving_regions hT S hdepth h g).2.2] using
      (augmentedPartition_eq_images (S.oldChargeState h g))


end TNLean.PEPS.AreaLaw.Scan.CollarScan
