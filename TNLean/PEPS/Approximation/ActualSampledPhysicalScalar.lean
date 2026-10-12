/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.ActualSampledPhysicalFactors
import TNLean.PEPS.Approximation.ActualSampledExteriorScalar

/-!
# The common exterior scalar in the sampled physical sum

The exterior entry of every actual sampled local trace is the same squared
modulus of the original empty-gate scalar. It can therefore be placed outside
the finite sum over the original joint sample assignments. The remaining
factors have the original physical indices, with the same joint assignment
used at all endpoints and independent ket and bra choices.

No scalar is divided out. Empty source inventories, empty original party sets,
zero scalars and zero-dimensional physical memories are included.

Source: polynomial-PEPS manuscript (September 24, 2026), Theorem 5.2,
`04-compression.tex`, lines 565–588, especially 574–579.
-/

noncomputable section
open scoped Matrix ComplexConjugate
namespace TNLean.PEPS.PairEffect.SourceCircuit
attribute [local instance] Classical.propDecidable
variable {P : Type} [Fintype P] [DecidableEq P] {a : Layout P}
variable {I E : Option {_p : P // true = true} → Type}
variable [∀ q, Fintype (I q)] [∀ q, Fintype (E q)]

/-- The actual sampled physical contraction is the original-party factor sum
multiplied by the common exterior scalar and the original averaging factor.
Each local endpoint matrix is the matrix of its actual sampled restriction.
No exterior coefficient or factorization is supplied as a hypothesis.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 565–588. -/
theorem partialSourceGlobalMatrix_sampled_partialTrace_eq_scalar_smul_physicalSum
    (d : P → ℕ) (ps : List P) (hn : ps.Nodup) (hc : ∀ p, p ∈ ps)
    (garbage : Layout P) (w : SourceCircuit a (familyPhysicalLayout d ps ++ garbage))
    (ψ : ProductInput a) (k : ℕ)
    (lam : ∀ e : sourceLocations w, branchLabels w e.1 →
      Fin (min (sourceDims w e).1 (sourceDims w e).2) → ℝ)
    (L : ∀ e : sourceLocations w, branchLabels w e.1 →
      Matrix (Fin (sourceDims w e).1) (Fin (min (sourceDims w e).1 (sourceDims w e).2)) ℂ)
    (R : ∀ e : sourceLocations w, branchLabels w e.1 →
      Matrix (Fin (sourceDims w e).2) (Fin (min (sourceDims w e).1 (sourceDims w e).2)) ℂ)
    (ξ ζ : Choices (fun _ : P ↦ true) w) (ω : SourceGaussianSamples w k)
    (B : ∀ q, OrthonormalBasis (I q) ℂ
      (Mem (Layout.atParty q (w.allResidualSourceLayout ++ []))))
    (BG : ∀ q, OrthonormalBasis (E q) ℂ
      (Mem (Layout.atParty q
        (Layout.mapOwner (affectedOwner (fun _ : P ↦ true)) garbage)))) :
    let C := selectedPhysicalPrivateBasis d ps hn hc garbage BG
    let bOut := partyGroupedBasis
      (Layout.mapOwner (affectedOwner (fun _ : P ↦ true))
        (familyPhysicalLayout d ps ++ garbage)) C (selectedPartyOrder ps)
      (selectedPartyOrder_nodup ps hn) (mem_selectedPartyOrder ps hc)
    let e := Equiv.arrowProdEquivProdArrow (Option {_p : P // true = true})
      (selectedFamilyPhysicalIndex d) E
    let M := fun (j : Fin (partialSlots (fun _ ↦ true) w).length → Fin k)
      (q : Option {_p : P // true = true}) ↦
      sampledPhysicalFactor d ps hn hc garbage w ψ k lam L R ξ ζ ω B BG
        (j ∘ (allSourceSlotEquiv w).symm) q
    (Matrix.partialTraceRight
      ((w.partialSourceGlobalMatrix ψ ξ bOut *
        SourceInventory.productSourceMatrix (partialSlots (fun _ ↦ true) w)
          (fun i ↦ sampledSourceMatrix w k lam L R
            (partialSlotEquiv (fun _ ↦ true) w i).1
            (partialSlotChoice (fun _ ↦ true) w ξ i)
            (partialSlotChoice (fun _ ↦ true) w ζ i) ω) *
        (w.partialSourceGlobalMatrix ψ ζ bOut)ᴴ).submatrix e.symm e.symm)).submatrix
      (selectedFamilyPhysicalConfigEquiv d).symm (selectedFamilyPhysicalConfigEquiv d).symm =
      (((k : ℂ)⁻¹ ^ (partialSlots (fun _ ↦ true) w).length) *
        (w.emptyGateScalar * conj w.emptyGateScalar)) •
        ∑ j : Fin (partialSlots (fun _ ↦ true) w).length → Fin k,
          dependentPhysicalProductFamilyMatrix (fun p : P ↦ M j (some ⟨p, rfl⟩)) := by
  classical
  intro C bOut e M
  have hNone (j : Fin (partialSlots (fun _ ↦ true) w).length → Fin k) :
      M j none = (w.emptyGateScalar * conj w.emptyGateScalar) •
        (1 : Matrix PUnit PUnit ℂ) := by
    have h := partialSourceWord_sampled_none_partialTrace_eq_scalar
      w ψ k lam L R ξ ζ (j ∘ (allSourceSlotEquiv w).symm) ω (B none) (C none)
    simpa only [M, sampledPhysicalFactor, partialSourcePartyMatrix, matrix_repr_eval_eq_toMatrix] using h
  have hEntry (j : Fin (partialSlots (fun _ ↦ true) w).length → Fin k) :
      M j none PUnit.unit PUnit.unit = w.emptyGateScalar * conj w.emptyGateScalar := by
    rw [hNone]
    simp only [Matrix.smul_apply, Matrix.one_apply, if_pos rfl, smul_eq_mul, mul_one]
  have h := partialSourceGlobalMatrix_sampled_partialTrace_eq_sum_physicalFactors
    d ps hn hc garbage w ψ k lam L R ξ ζ ω B BG
  dsimp only at h
  calc
    _ = ((k : ℂ)⁻¹ ^ (partialSlots (fun _ ↦ true) w).length) •
        ∑ j : Fin (partialSlots (fun _ ↦ true) w).length → Fin k,
          M j none PUnit.unit PUnit.unit •
            dependentPhysicalProductFamilyMatrix (fun p : P ↦ M j (some ⟨p, rfl⟩)) := h
    _ = _ := by
      simp_rw [hEntry]
      rw [← Finset.smul_sum, smul_smul]

end TNLean.PEPS.PairEffect.SourceCircuit
