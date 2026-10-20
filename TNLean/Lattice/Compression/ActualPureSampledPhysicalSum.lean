/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.Compression.ActualPurePhysicalSourceReplacement
import TNLean.Lattice.Compression.ActualSourceColumnPhysicalTrace
import TNLean.Lattice.Compression.ActualSampledPhysicalScalar
/-! # The actual sampled physical sum on the recorded product input

The original physical source-replaced operator is the double chronological
choice sum of the sampled products of local physical matrices. Each summand
uses one original joint sample assignment at every endpoint. The common
exterior scalar is retained multiplicatively, without cancellation.

The local physical/private bases are constructed from the original physical
registers and arbitrary bases of the actual private registers. The reference
private basis used in the original physical trace is arbitrary. No positivity,
normalization, factorization premise, or nonempty-party hypothesis is required.

Source: polynomial-PEPS manuscript (September 24, 2026), Theorem 5.2,
`04-compression.tex`, lines 279–355, 409–434 and 565–588.
-/

noncomputable section
open scoped Matrix ComplexConjugate
namespace TNLean.PEPS.PairEffect

private theorem partialTraceRight_reindex_comp
    {S X X' E : Type} [Fintype E] (e : S ≃ X × E) (f : X ≃ X')
    (Z : Matrix S S ℂ) :
    Matrix.partialTraceRight
        (Z.submatrix (e.trans (f.prodCongr (Equiv.refl E))).symm
          (e.trans (f.prodCongr (Equiv.refl E))).symm) =
      (Matrix.partialTraceRight (Z.submatrix e.symm e.symm)).submatrix f.symm f.symm := by
  change Matrix.partialTraceRight
    ((Z.submatrix e.symm e.symm).submatrix (f.prodCongr (Equiv.refl E)).symm
      (f.prodCongr (Equiv.refl E)).symm) = _
  exact Matrix.partialTraceRight_submatrix_prod_equiv f (Equiv.refl E) _

namespace SourceCircuit
attribute [local instance] Classical.propDecidable
variable {P : Type} [Fintype P] [DecidableEq P] {a : Layout P}
variable {I E : Option {_p : P // true = true} → Type}
variable [∀ q, Fintype (I q)] [∀ q, Fintype (E q)]

/-- Source replacement by the actual sampled matrices, followed by the original
physical trace on the recorded product input, equals the double choice sum of
the actual sampled local physical products. The original exterior scalar is
retained, and no normalization or factorization identity is assumed.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 279–355,
409–434 and 565–588. -/
theorem physicalSourceReplacedDensity_pure_sampled_eq_scalar_smul_physicalSum
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
    let _C := selectedPhysicalPrivateBasis d ps hn hc garbage BG
    let M := fun (ξ ζ : Choices (fun _ : P ↦ true) w)
      (j : Fin (partialSlots (fun _ ↦ true) w).length → Fin k)
      (q : Option {_p : P // true = true}) ↦
      sampledPhysicalFactor d ps hn hc garbage w ψ k lam L R ξ ζ ω B BG
        (j ∘ (allSourceSlotEquiv w).symm) q
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
            dependentPhysicalProductFamilyMatrix (fun p : P ↦ M ξ ζ j (some ⟨p, rfl⟩)) := by
  classical
  intro _C M
  let physical := familyPhysicalLayout d ps
  let qs := selectedPartyOrder ps
  let G := partyGroupedBasis
    (Layout.mapOwner (affectedOwner (fun _ : P ↦ true)) (physical ++ garbage)) _C qs
    (selectedPartyOrder_nodup ps hn) (mem_selectedPartyOrder ps hc)
  let H := (((familyLabelledPhysicalBasis d ps hn hc).tensorProduct bRef).map
    (appendIso physical garbage).symm).map
      (Layout.mapOwnerIso (affectedOwner (fun _ : P ↦ true)) (physical ++ garbage))
  let e := Equiv.arrowProdEquivProdArrow (Option {_p : P // true = true})
    (selectedFamilyPhysicalIndex d) E
  let f := selectedFamilyPhysicalConfigEquiv d
  let α := ((k : ℂ)⁻¹ ^ (partialSlots (fun _ ↦ true) w).length) *
    (w.emptyGateScalar * conj w.emptyGateScalar)
  let X (ξ ζ : Choices (fun _ : P ↦ true) w) :=
    SourceInventory.productSourceMatrix (partialSlots (fun _ ↦ true) w)
      (fun i ↦ sampledSourceMatrix w k lam L R
        (partialSlotEquiv (fun _ ↦ true) w i).1
        (partialSlotChoice (fun _ ↦ true) w ξ i)
        (partialSlotChoice (fun _ ↦ true) w ζ i) ω)
  have hTrace (ξ ζ : Choices (fun _ : P ↦ true) w) :
      Matrix.partialTraceRight
          (w.partialSourceGlobalMatrix ψ ξ H * X ξ ζ *
            (w.partialSourceGlobalMatrix ψ ζ H)ᴴ) =
        α • ∑ j : Fin (partialSlots (fun _ ↦ true) w).length → Fin k,
          dependentPhysicalProductFamilyMatrix (fun p : P ↦ M ξ ζ j (some ⟨p, rfl⟩)) := by
    have hBridge := selectedPhysicalPrivateBasis_partialTrace_actualColumns
      d ps hn hc garbage BG bRef w ψ ξ ζ (X ξ ζ)
    have hFactors := partialSourceGlobalMatrix_sampled_partialTrace_eq_scalar_smul_physicalSum
      d ps hn hc garbage w ψ k lam L R ξ ζ ω B BG
    dsimp only at hBridge hFactors
    have hReindex := partialTraceRight_reindex_comp e f
      (w.partialSourceGlobalMatrix ψ ξ G * X ξ ζ *
        (w.partialSourceGlobalMatrix ψ ζ G)ᴴ)
    exact hBridge.symm.trans (hReindex.trans hFactors)
  have hBase := physicalSourceReplacedDensity_pure_eq_sum_actualColumnTraces
    physical garbage w ψ (fun e ξ ζ ↦ sampledSourceMatrix w k lam L R e ξ ζ ω)
    bIn (familyLabelledPhysicalBasis d ps hn hc) bRef
  dsimp only at hBase
  have hSum :
      (∑ ξ, ∑ ζ, (coefficient (fun _ : P ↦ true) w ξ *
        conj (coefficient (fun _ : P ↦ true) w ζ)) •
        Matrix.partialTraceRight
          (w.partialSourceGlobalMatrix ψ ξ H * X ξ ζ *
            (w.partialSourceGlobalMatrix ψ ζ H)ᴴ)) =
      ∑ ξ, ∑ ζ, (coefficient (fun _ : P ↦ true) w ξ *
        conj (coefficient (fun _ : P ↦ true) w ζ)) •
        (α • ∑ j : Fin (partialSlots (fun _ ↦ true) w).length → Fin k,
          dependentPhysicalProductFamilyMatrix (fun p : P ↦ M ξ ζ j (some ⟨p, rfl⟩))) := by
    simp_rw [hTrace]
    rfl
  refine hBase.trans (hSum.trans ?_)
  let N (ξ ζ : Choices (fun _ : P ↦ true) w) :
      Matrix ((p : P) → Fin (d p)) ((p : P) → Fin (d p)) ℂ :=
    ∑ j : Fin (partialSlots (fun _ ↦ true) w).length → Fin k,
      dependentPhysicalProductFamilyMatrix (fun p : P ↦ M ξ ζ j (some ⟨p, rfl⟩))
  change (∑ ξ, ∑ ζ, (coefficient (fun _ : P ↦ true) w ξ *
      conj (coefficient (fun _ : P ↦ true) w ζ)) • (α • N ξ ζ)) =
    α • ∑ ξ, ∑ ζ, (coefficient (fun _ : P ↦ true) w ξ *
      conj (coefficient (fun _ : P ↦ true) w ζ)) • N ξ ζ
  have hComm (ξ ζ : Choices (fun _ : P ↦ true) w)
      (N : Matrix ((p : P) → Fin (d p)) ((p : P) → Fin (d p)) ℂ) :
      (coefficient (fun _ : P ↦ true) w ξ *
        conj (coefficient (fun _ : P ↦ true) w ζ)) • (α • N) =
        α • ((coefficient (fun _ : P ↦ true) w ξ *
          conj (coefficient (fun _ : P ↦ true) w ζ)) • N) := smul_comm _ _ _
  simp_rw [hComm]
  simp only [Finset.smul_sum]

end SourceCircuit
end TNLean.PEPS.PairEffect
