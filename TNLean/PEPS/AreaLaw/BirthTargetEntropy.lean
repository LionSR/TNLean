/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.BoundaryEntropyAssembly
import QICLean.Entropy.FiniteProductInformation

/-!
# A boundary entropy estimate from information on birth targets

For an ordered two-family partition, each retained piece is contained in a
larger birth target. A mutual-information estimate for the target against the
whole union of the exterior and the earlier pieces of the same family passes
to the retained piece by discarding part of the first system. The existing
two-family entropy cancellation then gives the boundary estimate.

The ordered partition, target information estimates, residual-size estimate
and summable scale losses are explicit premises. Their geometric construction
and uniform dependence on the Hamiltonian parameters remain separate steps.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*, proof
of Theorem 1.1, `10-geometry.tex`, lines 838–852, immutable revision
`openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Independently formalized; no OpenAI Lean proof text is reused.
-/

open scoped BigOperators

namespace TNLean.PEPS.AreaLaw

/-- Discarding part of each birth target, followed by two-family cancellation,
turns the birth-target information estimates and the geometric scale sum into
a boundary entropy estimate. Source: proof of Theorem 1.1,
`10-geometry.tex`, lines 838–852, September 24, 2026, immutable source
`openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

For the source application `Y i = A ∩ T_i`. The birth targets need not be
pairwise disjoint: only their disjointness from the same-family past is used.
The partition, birth-target information bounds, residual-size bound and scale
sum are explicit premises. This statement does not construct them, prove their
uniformity, or establish the full ground-state area law. -/
theorem regionalEntropy_le_boundary_of_birth_information_estimates
    (Λ : Finset (ℤ × ℤ)) (q : ℕ) (hq : 1 ≤ q)
    (Ω : StateSpace Λ q) (hΩ : ‖Ω‖ = 1) (A : Finset (Site Λ))
    (P : Geometry.OrderedTwoFamilyPartition A)
    (Y : Fin P.pieceCount → Finset (Site Λ))
    (hYA : ∀ i, Y i ⊆ A)
    (hXY : ∀ i, P.piece i ⊆ Y i)
    (hYpast : ∀ i, Disjoint (Y i) (P.earlierSameFamily i))
    (n : Fin P.pieceCount → ℕ)
    (cD cI cS : ℝ) (hcI : 0 ≤ cI)
    (hMI : ∀ i,
      FiniteProduct.mutualInformation (fun _ : Site Λ ↦ Fin q) Ω (Y i)
        (Aᶜ ∪ P.earlierSameFamily i) ≤ cI * (n i : ℝ) ^ (-100 : ℝ))
    (hD : (P.residual.card : ℝ) ≤ cD * (edgeBoundary Λ A).card)
    (hS : (∑ i, (n i : ℝ) ^ (-100 : ℝ)) ≤ cS * (edgeBoundary Λ A).card) :
    regionalEntropy Λ q Ω A ≤
      (cD * Real.log q + cI * cS / 2) * (edgeBoundary Λ A).card := by
  exact regionalEntropy_le_boundary_of_partition_estimates Λ q hq Ω hΩ A P
    (fun i ↦ cI * (n i : ℝ) ^ (-100 : ℝ))
    (fun i ↦
      (FiniteProduct.mutualInformation_mono_left (fun _ : Site Λ ↦ Fin q) Ω
        (P.piece i) (Y i) (Aᶜ ∪ P.earlierSameFamily i) (hXY i)
        (Finset.disjoint_union_right.mpr
          ⟨disjoint_compl_right_iff.mpr (hYA i), hYpast i⟩)).trans (hMI i))
    cD (cI * cS) hD
    ((Finset.mul_sum Finset.univ (fun i ↦ (n i : ℝ) ^ (-100 : ℝ)) cI).symm.trans_le
      ((mul_le_mul_of_nonneg_left hS hcI).trans_eq
        (mul_assoc cI cS ((edgeBoundary Λ A).card : ℝ)).symm))

end TNLean.PEPS.AreaLaw
