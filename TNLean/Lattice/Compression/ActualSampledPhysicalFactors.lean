/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Tactic.Convert
import TNLean.Lattice.Compression.RestrictedMixedPhysicalTrace
import TNLean.Lattice.Compression.ActualSampledPartyPartialTrace
import TNLean.Lattice.Compression.SelectedPhysicalPrivateBasis
import TNLean.Lattice.Compression.SelectedPhysicalPartyGrouping
/-! # Actual sampled factors in the original physical coordinates

Choose the local output bases obtained from the original physical registers
and the actual private registers. After tracing the private coordinates, the
canonical configuration equivalence identifies the retained indices with the
original physical configurations. Each sampled summand is the exterior scalar
entry times the product of the local physical matrices.

The exterior scalar is retained even when there are no original parties. No
nonzero scalar, normalization, or identification with a replaced density is
assumed. Both source choices are independent, and each summand uses one common
original sample at every endpoint.

Source: polynomial-PEPS manuscript (September 24, 2026), Theorem 5.2,
`04-compression.tex`, lines 565–588, especially 574–579.
-/

noncomputable section
open scoped Matrix
namespace TNLean.PEPS.PairEffect.SourceCircuit

variable {P : Type} [Fintype P] [DecidableEq P] {a : Layout P}
variable {I E : Option {_p : P // true = true} → Type}
variable [∀ q, Fintype (I q)] [∀ q, Fintype (E q)]

open Classical in
/-- The actual local physical matrix for independent ket and bra choices and
one original sample assignment. Its physical basis is the original basis, and
its private coordinates are traced in the prescribed local private basis.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 574–579. -/
def sampledPhysicalFactor
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
        (Layout.mapOwner (affectedOwner (fun _ : P ↦ true)) garbage))))
    (j : w.sourceLocations → Fin k) (q : Option {_p : P // true = true}) :
    Matrix (selectedFamilyPhysicalIndex d q) (selectedFamilyPhysicalIndex d q) ℂ :=
  let C := selectedPhysicalPrivateBasis (E := E) d ps hn hc garbage BG
  restrictedMixedPhysicalTrace
    (Q := Option {_p : P // true = true}) (I := I q)
    (X := selectedFamilyPhysicalIndex d q) (E := E q)
    (a := w.allResidualSourceLayout ++ [])
    (b := Layout.mapOwner (affectedOwner (fun _ : P ↦ true))
      (familyPhysicalLayout d ps ++ garbage)) (partySelector q)
    (w.partialSourceWord ψ ξ) (w.partialSourceWord ψ ζ)
    (sampledEndpointInputWord w k lam L R ξ ζ j ω)
    (sources_partialSourceWord w ψ ξ) (sources_partialSourceWord w ψ ζ)
    (sources_sampledEndpointInputWord w k lam L R ξ ζ j ω) (B q) (C q)

/-- The exact physical-factor equality, formed on arbitrary matrices before
actual sampled words are substituted. Source: polynomial-PEPS Theorem 5.2,
`04-compression.tex`, lines 565–588. -/
private def sampledPhysicalFactorsEquality {J : Type} [Fintype J]
    (d : P → ℕ) (α : ℂ)
    (F : Matrix ((q : Option {_p : P // true = true}) → selectedFamilyPhysicalIndex d q)
      ((q : Option {_p : P // true = true}) → selectedFamilyPhysicalIndex d q) ℂ)
    (M : J → (q : Option {_p : P // true = true}) →
      Matrix (selectedFamilyPhysicalIndex d q) (selectedFamilyPhysicalIndex d q) ℂ) : Prop :=
  F.submatrix (selectedFamilyPhysicalConfigEquiv d).symm
      (selectedFamilyPhysicalConfigEquiv d).symm =
    α • ∑ j, M j none PUnit.unit PUnit.unit •
      dependentPhysicalProductFamilyMatrix (fun p : P ↦ M j (some ⟨p, rfl⟩))

omit [DecidableEq P] in
/-- Reindex an arbitrary sum of party products in the original physical
configurations. Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`,
lines 565–588. -/
private theorem sampledPhysicalFactorsEquality_of_partyProduct {J : Type} [Fintype J]
    (d : P → ℕ) {α : ℂ}
    {F : Matrix ((q : Option {_p : P // true = true}) → selectedFamilyPhysicalIndex d q)
      ((q : Option {_p : P // true = true}) → selectedFamilyPhysicalIndex d q) ℂ}
    {M : J → (q : Option {_p : P // true = true}) →
      Matrix (selectedFamilyPhysicalIndex d q) (selectedFamilyPhysicalIndex d q) ℂ}
    (h : F = α • ∑ j, dependentPhysicalProductFamilyMatrix (M j)) :
    sampledPhysicalFactorsEquality d α F M := by
  classical
  let T := (Matrix.reindexLinearEquiv ℂ ℂ
    (selectedFamilyPhysicalConfigEquiv d) (selectedFamilyPhysicalConfigEquiv d)).toLinearMap
  have ht (N : (q : Option {_p : P // true = true}) →
      Matrix (selectedFamilyPhysicalIndex d q) (selectedFamilyPhysicalIndex d q) ℂ) :
      T (dependentPhysicalProductFamilyMatrix N) =
        N none PUnit.unit PUnit.unit •
          dependentPhysicalProductFamilyMatrix (fun p : P ↦ N (some ⟨p, rfl⟩)) :=
    partyProductMatrix_selectedFamilyPhysicalConfig d N
  have hphysical := congrArg T h
  simp only [map_smul, map_sum, ht] at hphysical
  exact hphysical

open Classical in
/-- In the original physical configurations, the actual sampled coordinate
trace is a sum of products of local physical traces, retaining the exterior
scalar entry in every summand. The physical/private splitting is given by the
constructed bases on the actual registers; it is not an assumed column identity.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 565–588. -/
theorem partialSourceGlobalMatrix_sampled_partialTrace_eq_sum_physicalFactors
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
    let C : (q : Option {_p : P // true = true}) →
      OrthonormalBasis (selectedFamilyPhysicalIndex d q × E q) ℂ
        (Mem (Layout.atParty q (Layout.mapOwner (affectedOwner (fun _ : P ↦ true))
          (familyPhysicalLayout d ps ++ garbage)))) :=
      selectedPhysicalPrivateBasis (E := E) d ps hn hc garbage BG
    let bOut := partyGroupedBasis (I := fun q ↦ selectedFamilyPhysicalIndex d q × E q)
      (Layout.mapOwner (affectedOwner (fun _ : P ↦ true))
        (familyPhysicalLayout d ps ++ garbage)) C (selectedPartyOrder ps)
      (selectedPartyOrder_nodup ps hn) (mem_selectedPartyOrder ps hc)
    let e := Equiv.arrowProdEquivProdArrow (Option {_p : P // true = true})
      (selectedFamilyPhysicalIndex d) E
    let M : (Fin (partialSlots (fun _ ↦ true) w).length → Fin k) →
      (q : Option {_p : P // true = true}) →
        Matrix (selectedFamilyPhysicalIndex d q) (selectedFamilyPhysicalIndex d q) ℂ :=
      fun j q ↦ sampledPhysicalFactor (I := I) (E := E)
        d ps hn hc garbage w ψ k lam L R ξ ζ ω B BG
          (j ∘ (allSourceSlotEquiv w).symm) q
    sampledPhysicalFactorsEquality d
      ((k : ℂ)⁻¹ ^ (partialSlots (fun _ ↦ true) w).length)
      (Matrix.partialTraceRight
      ((w.partialSourceGlobalMatrix ψ ξ bOut *
        SourceInventory.productSourceMatrix (partialSlots (fun _ ↦ true) w)
          (fun i ↦ sampledSourceMatrix w k lam L R
            (partialSlotEquiv (fun _ ↦ true) w i).1
            (partialSlotChoice (fun _ ↦ true) w ξ i)
            (partialSlotChoice (fun _ ↦ true) w ζ i) ω) *
        (w.partialSourceGlobalMatrix ψ ζ bOut)ᴴ).submatrix e.symm e.symm)) M := by
  classical
  have h := partialSourceGlobalMatrix_sampled_partialTrace_eq_sum_partyProduct
    (I := I) (X := selectedFamilyPhysicalIndex d) (E := E)
    w ψ k lam L R ξ ζ ω B (selectedPhysicalPrivateBasis (E := E) d ps hn hc garbage BG)
    (selectedPartyOrder ps) (selectedPartyOrder_nodup ps hn) (mem_selectedPartyOrder ps hc)
  have hphysical := sampledPhysicalFactorsEquality_of_partyProduct d h
  simp only [sampledPhysicalFactor, restrictedMixedPhysicalTrace, partialSourcePartyMatrix]
    at hphysical ⊢
  convert hphysical using 1
  funext j q
  rfl

end TNLean.PEPS.PairEffect.SourceCircuit
