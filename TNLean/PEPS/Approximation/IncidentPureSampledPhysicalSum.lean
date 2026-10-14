/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.ActualPureSampledPhysicalSum
import TNLean.PEPS.Approximation.IncidentSampledPhysicalFactor

/-! # Replacing sampled party factors by their incident constructions

Each local factor is constructed from the two original incident gate-label
assignments and the restriction of the common sample assignment to that
party's ordered source slots. The outer choice sums and joint sample sum
remain the original sums. Neither incident labels nor samples are extended
to unrelated positions. The exterior scalar is retained without cancellation.

This identity substitutes local factors in the existing physical sum. It does
not regroup the gate-label or sample indices, or assert a bond-dimension bound.

Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 253–267,
351–381 and 565–588.
-/

noncomputable section
open scoped Matrix ComplexConjugate
namespace TNLean.PEPS.PairEffect.SourceCircuit
open TNLean.PEPS.Approximation
attribute [local instance] Classical.propDecidable
variable {P : Type} [Fintype P] [DecidableEq P] {a : Layout P}
variable {I E : Option {_p : P // true = true} → Type}
variable [∀ q, Fintype (I q)] [∀ q, Fintype (E q)]

/-- The actual sampled physical sum is the same sum with each party matrix
constructed directly from its incident labels and incident sample indices.
The sampling coefficient and empty-gate squared modulus are unchanged,
including when their value is zero or the original party type is empty.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 253–267,
351–381 and 565–588. -/
theorem physicalSourceReplacedDensity_pure_sampled_eq_scalar_smul_incidentPhysicalSum
    (d : P → ℕ) (ps : List P) (hn : ps.Nodup) (hc : ∀ p, p ∈ ps)
    (garbage : Layout P) (w : SourceCircuit a (familyPhysicalLayout d ps ++ garbage))
    (ψ : ProductInput a) (k : ℕ)
    (lam : ∀ e : sourceLocations w, branchLabels w e.1 →
      Fin (min (sourceDims w e).1 (sourceDims w e).2) → ℝ)
    (L : ∀ e : sourceLocations w, branchLabels w e.1 →
      Matrix (Fin (sourceDims w e).1) (Fin (min (sourceDims w e).1 (sourceDims w e).2)) ℂ)
    (R : ∀ e : sourceLocations w, branchLabels w e.1 →
      Matrix (Fin (sourceDims w e).2) (Fin (min (sourceDims w e).1 (sourceDims w e).2)) ℂ)
    (ω : SourceGaussianSamples w k)
    (B : ∀ q, OrthonormalBasis (I q) ℂ
      (Mem (Layout.atParty q (w.allResidualSourceLayout ++ []))))
    (BG : ∀ q, OrthonormalBasis (E q) ℂ
      (Mem (Layout.atParty q
        (Layout.mapOwner (affectedOwner (fun _ : P ↦ true)) garbage))))
    {n J : Type} [Fintype n] [Fintype J]
    (bIn : OrthonormalBasis n ℂ (Mem a)) (bRef : OrthonormalBasis J ℂ (Mem garbage)) :
    let M := fun (ξ ζ : Choices (fun _ : P ↦ true) w)
      (j : Fin (partialSlots (fun _ ↦ true) w).length → Fin k) (p : P) ↦
      incidentSampledPhysicalFactor (I := I) (E := E)
        d ps hn hc garbage w ψ k lam L R p
        (originalGateLabelsAtOfAllChoices w p ξ)
        (originalGateLabelsAtOfAllChoices w p ζ) ω B BG
        (fun i ↦ j ((allSourceSlotEquiv w).symm (partialSlotEquiv
          (fun t ↦ partySelector (some ⟨p, rfl⟩)
            (affectedOwner (fun _ : P ↦ true) t)) w i).1))
    physicalSourceReplacedDensity (familyPhysicalLayout d ps) garbage w
        (fun e ξ ζ ↦ sampledSourceMatrix w k lam L R e ξ ζ ω)
        bIn (familyLabelledPhysicalBasis d ps hn hc) bRef
        (Matrix.vecMulVec (bIn.repr ψ.vector).ofLp
          (fun t ↦ conj (bIn.repr ψ.vector t))) =
      (((k : ℂ)⁻¹ ^ (partialSlots (fun _ ↦ true) w).length) *
        (w.emptyGateScalar * conj w.emptyGateScalar)) •
        ∑ ξ, ∑ ζ, (coefficient (fun _ : P ↦ true) w ξ *
          conj (coefficient (fun _ : P ↦ true) w ζ)) •
          ∑ j : Fin (partialSlots (fun _ ↦ true) w).length → Fin k,
            dependentPhysicalProductFamilyMatrix (M ξ ζ j) := by
  classical
  intro M
  have h := physicalSourceReplacedDensity_pure_sampled_eq_scalar_smul_physicalSum
    (I := I) (E := E) d ps hn hc garbage w ψ k lam L R ω B BG bIn bRef
  dsimp only at h
  simpa only [M, Function.comp_apply,
    sampledPhysicalFactor_eq_incidentSampledPhysicalFactor] using! h

end TNLean.PEPS.PairEffect.SourceCircuit
