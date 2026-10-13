/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.ActualSampledPartyPartialTrace
import TNLean.PEPS.Approximation.SelectedPhysicalPrivateBasis
import TNLean.PEPS.Approximation.SelectedPhysicalPartyGrouping

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

/-- The mixed coordinate trace for arbitrary source-free words is formed before
the actual sampled words are substituted. Source: polynomial-PEPS Theorem 5.2,
`04-compression.tex`, lines 574–579. -/
private abbrev restrictedMixedPhysicalTrace {Q I X E : Type}
    [Fintype I] [Fintype X] [Fintype E] {a b : Layout Q} (f : Q → Bool)
    (u t : Word a b) (v : Word a a)
    (hu : u.sources = []) (ht : t.sources = []) (hv : v.sources = [])
    (B : OrthonormalBasis I ℂ (Mem (Layout.restrict f a)))
    (C : OrthonormalBasis (X × E) ℂ (Mem (Layout.restrict f b))) : Matrix X X ℂ := by
  classical
  exact Matrix.partialTraceRight (α := X) (β := E)
    (Matrix.of (fun row col ↦ C.repr ((u.restrict f hu).eval (B col)) row) *
      LinearMap.toMatrix B.toBasis B.toBasis (v.restrict f hv).eval.toLinearMap *
      (Matrix.of (fun row col ↦ C.repr ((t.restrict f ht).eval (B col)) row))ᴴ)

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
    (Matrix.partialTraceRight
      ((w.partialSourceGlobalMatrix ψ ξ bOut *
        SourceInventory.productSourceMatrix (partialSlots (fun _ ↦ true) w)
          (fun i ↦ sampledSourceMatrix w k lam L R
            (partialSlotEquiv (fun _ ↦ true) w i).1
            (partialSlotChoice (fun _ ↦ true) w ξ i)
            (partialSlotChoice (fun _ ↦ true) w ζ i) ω) *
        (w.partialSourceGlobalMatrix ψ ζ bOut)ᴴ).submatrix e.symm e.symm)).submatrix
      (selectedFamilyPhysicalConfigEquiv d).symm (selectedFamilyPhysicalConfigEquiv d).symm =
      ((k : ℂ)⁻¹ ^ (partialSlots (fun _ ↦ true) w).length) •
        ∑ j : Fin (partialSlots (fun _ ↦ true) w).length → Fin k,
          M j none PUnit.unit PUnit.unit •
            dependentPhysicalProductFamilyMatrix (fun p : P ↦ M j (some ⟨p, rfl⟩)) := by
  classical
  dsimp only
  let T := (Matrix.reindexLinearEquiv ℂ ℂ
    (selectedFamilyPhysicalConfigEquiv d) (selectedFamilyPhysicalConfigEquiv d)).toLinearMap
  have ht (M : (q : Option {_p : P // true = true}) →
      Matrix (selectedFamilyPhysicalIndex d q) (selectedFamilyPhysicalIndex d q) ℂ) :
      T (dependentPhysicalProductFamilyMatrix M) =
        M none PUnit.unit PUnit.unit •
          dependentPhysicalProductFamilyMatrix (fun p : P ↦ M (some ⟨p, rfl⟩)) :=
    partyProductMatrix_selectedFamilyPhysicalConfig d M
  have h := congrArg T
    (partialSourceGlobalMatrix_sampled_partialTrace_eq_sum_partyProduct
      (I := I) (X := selectedFamilyPhysicalIndex d) (E := E)
      w ψ k lam L R ξ ζ ω B (selectedPhysicalPrivateBasis (E := E) d ps hn hc garbage BG)
      (selectedPartyOrder ps) (selectedPartyOrder_nodup ps hn) (mem_selectedPartyOrder ps hc))
  simp only [map_smul, map_sum, ht] at h
  simpa only [sampledPhysicalFactor, restrictedMixedPhysicalTrace, partialSourcePartyMatrix] using h

end TNLean.PEPS.PairEffect.SourceCircuit
