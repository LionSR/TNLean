/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.ActualSampledPhysicalFactors
import TNLean.PEPS.Approximation.IncidentSourceWordComparison
import TNLean.PEPS.Approximation.IncidentSampledEndpointComparison

/-! # The sampled physical matrix determined by incident labels

Two independent assignments of original incident gate labels determine a local
physical matrix. The incident source words give its two source-to-output maps,
and the incident sampled endpoint word gives the middle input operator.
Tracing the prescribed private coordinates leaves the original physical index.

For labels extracted from genuine all-party choices, this matrix equals the
actual sampled physical factor. The comparison uses the same recorded input,
source and output bases, original source occurrences, restricted sample assignment,
and ordered-pair Gaussian arrays. No extension of incident labels is chosen.

Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 253–267,
279–355, 409–434 and 565–588, especially 574–579.
-/

noncomputable section
open scoped Matrix
namespace TNLean.PEPS.PairEffect.SourceCircuit

variable {P : Type} {a : Layout P}
variable {I E : Option {_p : P // true = true} → Type}
variable [∀ q, Fintype (I q)] [∀ q, Fintype (E q)]

/-- The coordinate matrix of an arbitrary word in prescribed orthonormal
input and output bases. Source: polynomial-PEPS Theorem 5.2,
`04-compression.tex`, lines 253–267 and 565–588. -/
private def wordCoordinateMatrix {Q J K : Type} [Fintype J] [Fintype K] [DecidableEq J]
    {a b : Layout Q} (u : Word a b)
    (B : OrthonormalBasis J ℂ (Mem a)) (C : OrthonormalBasis K ℂ (Mem b)) :
    Matrix K J ℂ :=
  LinearMap.toMatrix B.toBasis C.toBasis u.eval.toLinearMap

/-- Construct the local physical factor directly from two independent incident
label assignments. Its output index is the original physical index; the
private coordinates are traced in the prescribed basis. The construction
uses only singleton source-slot sample indices and requires no full branch
choices, sample extension, source-vector equality, positivity or normalization
hypothesis. Source: polynomial-PEPS Theorem 5.2,
`04-compression.tex`, lines 253–267, 279–355, 409–434 and 574–579. -/
def incidentSampledPhysicalFactor
    (d : P → ℕ) (ps : List P) (hn : ps.Nodup) (hc : ∀ p, p ∈ ps)
    (garbage : Layout P) (w : SourceCircuit a (familyPhysicalLayout d ps ++ garbage))
    (ψ : ProductInput a) (k : ℕ)
    (lam : ∀ e : sourceLocations w, branchLabels w e.1 →
      Fin (min (sourceDims w e).1 (sourceDims w e).2) → ℝ)
    (L : ∀ e : sourceLocations w, branchLabels w e.1 →
      Matrix (Fin (sourceDims w e).1) (Fin (min (sourceDims w e).1 (sourceDims w e).2)) ℂ)
    (R : ∀ e : sourceLocations w, branchLabels w e.1 →
      Matrix (Fin (sourceDims w e).2) (Fin (min (sourceDims w e).1 (sourceDims w e).2)) ℂ)
    (p : P) (η θ : OriginalGateLabelsAt w p) (ω : SourceGaussianSamples w k)
    (B : ∀ q, OrthonormalBasis (I q) ℂ
      (Mem (Layout.atParty q (w.allResidualSourceLayout ++ []))))
    (BG : ∀ q, OrthonormalBasis (E q) ℂ
      (Mem (Layout.atParty q
        (Layout.mapOwner (affectedOwner (fun _ : P ↦ true)) garbage))))
    (j : Fin (partialSlots
      (fun t ↦ partySelector (some ⟨p, rfl⟩)
        (affectedOwner (fun _ : P ↦ true) t)) w).length → Fin k) :
    Matrix (Fin (d p)) (Fin (d p)) ℂ :=
  let q : Option {_p : P // true = true} := some ⟨p, rfl⟩
  letI : DecidableEq (I q) := Classical.typeDecidableEq (I q)
  let bIn : OrthonormalBasis (I q) ℂ
      (Mem (Layout.atParty q (w.allResidualSourceLayout ++ []))) := B q
  let bOut : OrthonormalBasis (Fin (d p) × E q) ℂ
      (Mem (Layout.atParty q (Layout.mapOwner (affectedOwner (fun _ : P ↦ true))
        (familyPhysicalLayout d ps ++ garbage)))) :=
    selectedPhysicalPrivateBasis (E := E) d ps hn hc garbage BG q
  let Dη : Matrix (Fin (d p) × E q) (I q) ℂ :=
    wordCoordinateMatrix (incidentSourceWord w p ψ η) bIn bOut
  let Dθ : Matrix (Fin (d p) × E q) (I q) ℂ :=
    wordCoordinateMatrix (incidentSourceWord w p ψ θ) bIn bOut
  let Nηθ : Matrix (I q) (I q) ℂ :=
    wordCoordinateMatrix (incidentSampledEndpointWord w k lam L R p η θ j ω) bIn bIn
  Matrix.partialTraceRight (α := Fin (d p)) (β := E q) (Dη * Nηθ * Dθᴴ)

/-- At independently extracted incident labels, the directly constructed
physical factor equals the actual factor at the same original party. The
sample assignment is restricted to the singleton source slots, and the original
Gaussian arrays are unchanged at both endpoints.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 565–588,
especially 574–579. -/
theorem sampledPhysicalFactor_eq_incidentSampledPhysicalFactor
    (d : P → ℕ) (ps : List P) (hn : ps.Nodup) (hc : ∀ p, p ∈ ps)
    (garbage : Layout P) (w : SourceCircuit a (familyPhysicalLayout d ps ++ garbage))
    (ψ : ProductInput a) (k : ℕ)
    (lam : ∀ e : sourceLocations w, branchLabels w e.1 →
      Fin (min (sourceDims w e).1 (sourceDims w e).2) → ℝ)
    (L : ∀ e : sourceLocations w, branchLabels w e.1 →
      Matrix (Fin (sourceDims w e).1) (Fin (min (sourceDims w e).1 (sourceDims w e).2)) ℂ)
    (R : ∀ e : sourceLocations w, branchLabels w e.1 →
      Matrix (Fin (sourceDims w e).2) (Fin (min (sourceDims w e).1 (sourceDims w e).2)) ℂ)
    (p : P) (ξ ζ : Choices (fun _ : P ↦ true) w) (ω : SourceGaussianSamples w k)
    (B : ∀ q, OrthonormalBasis (I q) ℂ
      (Mem (Layout.atParty q (w.allResidualSourceLayout ++ []))))
    (BG : ∀ q, OrthonormalBasis (E q) ℂ
      (Mem (Layout.atParty q
        (Layout.mapOwner (affectedOwner (fun _ : P ↦ true)) garbage))))
    (j : w.sourceLocations → Fin k) :
    sampledPhysicalFactor (I := I) (E := E) d ps hn hc garbage w ψ k lam L R
        ξ ζ ω B BG j (some ⟨p, rfl⟩) =
      incidentSampledPhysicalFactor (I := I) (E := E) d ps hn hc garbage w ψ k lam L R p
        (originalGateLabelsAtOfAllChoices w p ξ)
        (originalGateLabelsAtOfAllChoices w p ζ) ω B BG
        (fun i ↦ j (partialSlotEquiv
          (fun t ↦ partySelector (some ⟨p, rfl⟩)
            (affectedOwner (fun _ : P ↦ true) t)) w i).1) := by
  classical
  let q : Option {_p : P // true = true} := some ⟨p, rfl⟩
  let bIn : OrthonormalBasis (I q) ℂ
      (Mem (Layout.atParty q (w.allResidualSourceLayout ++ []))) := B q
  let bOut : OrthonormalBasis (Fin (d p) × E q) ℂ
      (Mem (Layout.atParty q (Layout.mapOwner (affectedOwner (fun _ : P ↦ true))
        (familyPhysicalLayout d ps ++ garbage)))) :=
    selectedPhysicalPrivateBasis (E := E) d ps hn hc garbage BG q
  let columnMatrix (u : Mem (Layout.atParty q (w.allResidualSourceLayout ++ [])) →L[ℂ]
      Mem (Layout.atParty q (Layout.mapOwner (affectedOwner (fun _ : P ↦ true))
        (familyPhysicalLayout d ps ++ garbage)))) : Matrix (Fin (d p) × E q) (I q) ℂ :=
    Matrix.of (fun row col ↦ bOut.repr (u (bIn col)) row)
  conv_rhs =>
    dsimp only [incidentSampledPhysicalFactor, wordCoordinateMatrix, Classical.typeDecidableEq]
    rw [← matrix_repr_eval_eq_toMatrix bIn bOut
      (incidentSourceWord w p ψ (originalGateLabelsAtOfAllChoices w p ξ)).eval,
      ← matrix_repr_eval_eq_toMatrix bIn bOut
        (incidentSourceWord w p ψ (originalGateLabelsAtOfAllChoices w p ζ)).eval]
  change Matrix.partialTraceRight (α := Fin (d p)) (β := E q)
    (columnMatrix ((w.partialSourceWord ψ ξ).restrict (partySelector q)
        (sources_partialSourceWord w ψ ξ)).eval *
      LinearMap.toMatrix bIn.toBasis bIn.toBasis
        ((sampledEndpointInputWord w k lam L R ξ ζ j ω).restrict (partySelector q)
          (sources_sampledEndpointInputWord w k lam L R ξ ζ j ω)).eval.toLinearMap *
      (columnMatrix ((w.partialSourceWord ψ ζ).restrict (partySelector q)
        (sources_partialSourceWord w ψ ζ)).eval)ᴴ) =
    Matrix.partialTraceRight (α := Fin (d p)) (β := E q)
      (columnMatrix (incidentSourceWord w p ψ (originalGateLabelsAtOfAllChoices w p ξ)).eval *
        LinearMap.toMatrix bIn.toBasis bIn.toBasis
          (incidentSampledEndpointWord w k lam L R p
            (originalGateLabelsAtOfAllChoices w p ξ)
            (originalGateLabelsAtOfAllChoices w p ζ)
            (fun i ↦ j (partialSlotEquiv
              (fun t ↦ partySelector (some ⟨p, rfl⟩)
                (affectedOwner (fun _ : P ↦ true) t)) w i).1) ω).eval.toLinearMap *
        (columnMatrix
          (incidentSourceWord w p ψ (originalGateLabelsAtOfAllChoices w p ζ)).eval)ᴴ)
  rw [restrict_partialSourceWord_eval_eq_incidentSourceWord w p ψ ξ,
    restrict_partialSourceWord_eval_eq_incidentSourceWord w p ψ ζ,
    restrict_sampledEndpointInputWord_eval_eq_incidentSampledEndpointWord w k lam L R p ξ ζ j ω]

end TNLean.PEPS.PairEffect.SourceCircuit
