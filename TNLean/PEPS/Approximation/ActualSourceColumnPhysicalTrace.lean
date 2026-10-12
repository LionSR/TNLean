/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.SelectedPhysicalPrivateTrace
import TNLean.PEPS.Approximation.ActualSourceColumnCoordinates
import Mathlib.Data.Matrix.Basis

/-! # Physical traces of actual mixed source columns

The constructed physical/private output basis and the original physical basis
with an arbitrary reference private basis give the same reduced mixed source
operator. This follows by expanding an arbitrary middle matrix into matrix
units and applying the mixed-vector trace identity to the actual ket and bra
columns. The middle matrix need not factor over parties or source slots.

No positivity, normalization, nonzero scalar, or nonempty-party hypothesis is
used. The physical dimensions and the two independent source choices retain
their original meanings, including zero-dimensional and empty cases.

Source: polynomial-PEPS manuscript (September 24, 2026), Theorem 5.2,
`04-compression.tex`, lines 279–355, 409–434 and 565–588.
-/

noncomputable section
open scoped Matrix ComplexConjugate
namespace TNLean.PEPS.PairEffect

private theorem mixed_single_eq_columns {S T : Type} [Fintype S] [DecidableEq S]
    (A B : Matrix T S ℂ) (s t : S) (γ : ℂ) :
    A * Matrix.single s t γ * Bᴴ =
      γ • Matrix.vecMulVec (fun r ↦ A r s) (fun r ↦ conj (B r t)) := by
  classical
  ext i j
  simp [Matrix.mul_apply, Matrix.single, Matrix.vecMulVec_apply,
    Matrix.conjTranspose_apply, Finset.sum_mul, ite_and, eq_comm,
    mul_assoc, mul_comm]

private theorem mixed_sandwich_eq_sum_columns {S T : Type} [Fintype S]
    (A B : Matrix T S ℂ) (X : Matrix S S ℂ) :
    A * X * Bᴴ = ∑ s, ∑ t,
      X s t • Matrix.vecMulVec (fun r ↦ A r s) (fun r ↦ conj (B r t)) := by
  classical
  calc
    A * X * Bᴴ = A * (∑ s, ∑ t, Matrix.single s t (X s t)) * Bᴴ :=
      congrArg (fun Y : Matrix S S ℂ ↦ A * Y * Bᴴ) (Matrix.matrix_eq_sum_single X)
    _ = ∑ s, ∑ t,
        X s t • Matrix.vecMulVec (fun r ↦ A r s) (fun r ↦ conj (B r t)) := by
      simp only [Matrix.mul_sum, Matrix.sum_mul, mixed_single_eq_columns]

namespace SourceCircuit
variable {P : Type} [Fintype P] [DecidableEq P] {a : Layout P}
variable {E : Option {_p : P // true = true} → Type} [∀ q, Fintype (E q)]

/-- The physical partial trace of an arbitrary matrix between the actual ket
and bra source columns is unchanged when the constructed private basis is
replaced by any reference private basis. The actual columns provide all vector
identifications used in the proof; no comparison identity is assumed.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 279–355,
409–434 and 565–588. -/
theorem selectedPhysicalPrivateBasis_partialTrace_actualColumns
    (d : P → ℕ) (ps : List P) (hn : ps.Nodup) (hc : ∀ p, p ∈ ps)
    (garbage : Layout P)
    (BG : ∀ q, OrthonormalBasis (E q) ℂ
      (Mem (Layout.atParty q
        (Layout.mapOwner (affectedOwner (fun _ : P ↦ true)) garbage))))
    {J : Type} [Fintype J] (bRef : OrthonormalBasis J ℂ (Mem garbage))
    (w : SourceCircuit a (familyPhysicalLayout d ps ++ garbage)) (ψ : ProductInput a)
    (ξ ζ : Choices (fun _ : P ↦ true) w) (X : Matrix w.allSourceLabels w.allSourceLabels ℂ) :
    let physical := familyPhysicalLayout d ps
    let qs := selectedPartyOrder ps
    let G := partyGroupedBasis
      (Layout.mapOwner (affectedOwner (fun _ : P ↦ true)) (physical ++ garbage))
      (selectedPhysicalPrivateBasis d ps hn hc garbage BG) qs
      (selectedPartyOrder_nodup ps hn) (mem_selectedPartyOrder ps hc)
    let H := (((familyLabelledPhysicalBasis d ps hn hc).tensorProduct bRef).map
      (appendIso physical garbage).symm).map
        (Layout.mapOwnerIso (affectedOwner (fun _ : P ↦ true)) (physical ++ garbage))
    let e := (Equiv.arrowProdEquivProdArrow (Option {_p : P // true = true})
      (selectedFamilyPhysicalIndex d) E).trans
        (Equiv.prodCongr (selectedFamilyPhysicalConfigEquiv d)
          (Equiv.refl ((q : Option {_p : P // true = true}) → E q)))
    Matrix.partialTraceRight
        ((w.partialSourceGlobalMatrix ψ ξ G * X *
          (w.partialSourceGlobalMatrix ψ ζ G)ᴴ).submatrix e.symm e.symm) =
      Matrix.partialTraceRight
        (w.partialSourceGlobalMatrix ψ ξ H * X * (w.partialSourceGlobalMatrix ψ ζ H)ᴴ) := by
  classical
  intro physical qs G H e
  let owner := Layout.mapOwnerIso (affectedOwner (fun _ : P ↦ true)) (physical ++ garbage)
  let v (η : Choices (fun _ : P ↦ true) w) (s : w.allSourceLabels) :=
    owner.symm ((w.partialSourceWord ψ η).eval (w.actualSourceInputBasis s))
  let TG := Matrix.partialTraceRightLM.comp (Matrix.reindexLinearEquiv ℂ ℂ e e).toLinearMap
  let TH : Matrix (((p : P) → Fin (d p)) × J) (((p : P) → Fin (d p)) × J) ℂ →ₗ[ℂ]
      Matrix ((p : P) → Fin (d p)) ((p : P) → Fin (d p)) ℂ := Matrix.partialTraceRightLM
  have hColumn (η : Choices (fun _ : P ↦ true) w) {K : Type} [Fintype K]
      (bOut : OrthonormalBasis K ℂ
        (Mem (Layout.mapOwner (affectedOwner (fun _ : P ↦ true)) (physical ++ garbage))))
      (r : K) (s : w.allSourceLabels) :
      w.partialSourceGlobalMatrix ψ η bOut r s =
        bOut.repr ((w.partialSourceWord ψ η).eval (w.actualSourceInputBasis s)) r := by
    rw [partialSourceGlobalMatrix_eq_toMatrix]
    simp only [LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis,
      OrthonormalBasis.coe_toBasis_repr_apply, ContinuousLinearMap.coe_coe]
  have hG (η : Choices (fun _ : P ↦ true) w)
      (r : (q : Option {_p : P // true = true}) → selectedFamilyPhysicalIndex d q × E q)
      (s : w.allSourceLabels) :
      w.partialSourceGlobalMatrix ψ η G r s = G.repr (owner (v η s)) r := by
    simpa only [v, LinearIsometryEquiv.apply_symm_apply] using hColumn η G r s
  have hH (η : Choices (fun _ : P ↦ true) w) (r : ((p : P) → Fin (d p)) × J)
      (s : w.allSourceLabels) :
      w.partialSourceGlobalMatrix ψ η H r s =
        ((familyLabelledPhysicalBasis d ps hn hc).tensorProduct bRef).repr
          (appendIso physical garbage (v η s)) r := by
    rw [hColumn]
    rfl
  have hTerm (s t : w.allSourceLabels) :
      TG (Matrix.vecMulVec (fun r ↦ w.partialSourceGlobalMatrix ψ ξ G r s)
        (fun r ↦ conj (w.partialSourceGlobalMatrix ψ ζ G r t))) =
      TH (Matrix.vecMulVec (fun r ↦ w.partialSourceGlobalMatrix ψ ξ H r s)
        (fun r ↦ conj (w.partialSourceGlobalMatrix ψ ζ H r t))) := by
    simp only [hG, hH]
    exact selectedPhysicalPrivateBasis_partialTrace_mixed d ps hn hc garbage BG bRef
      (v ξ s) (v ζ t)
  change TG (w.partialSourceGlobalMatrix ψ ξ G * X *
      (w.partialSourceGlobalMatrix ψ ζ G)ᴴ) =
    TH (w.partialSourceGlobalMatrix ψ ξ H * X * (w.partialSourceGlobalMatrix ψ ζ H)ᴴ)
  rw [mixed_sandwich_eq_sum_columns, mixed_sandwich_eq_sum_columns]
  simp only [map_sum, map_smul, hTerm]

end SourceCircuit
end TNLean.PEPS.PairEffect
