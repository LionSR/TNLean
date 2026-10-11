/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.PreparedSourceTransport
import TNLean.PEPS.Approximation.SourceCorrectedContractionIdentity
import TNLean.PEPS.Approximation.SourceGaussianDensity

/-!
# Actual corrected terms in Gaussian Schmidt coordinates

Each globally defined corrected term is expressed through the canonical partial
words. Selected sources are the actual endpoint Schmidt vectors, weighted by
entries of the actual centered Gaussian source matrices. Unselected sources
remain their original vectors, and every gate coefficient occurs once.

Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 338–434.
-/

/-!
Source: September 24, 2026, polynomial-PEPS manuscript, 04-compression.tex,
eq:compression-product-covariance.
Manuscript revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Independently formalized from the manuscript; no upstream Lean proof text reused.
-/

noncomputable section
open QICLean.ComplexGaussian
open scoped TensorProduct Matrix ComplexConjugate
namespace TNLean.PEPS.PairEffect.SourceCircuit
variable {P : Type} {a b : Layout P}

/-- Independent Schmidt indices at both endpoints of each selected partial slot.
The slot retains its original source occurrence. -/
abbrev PartialSchmidtCoordinates (A : P → Bool) (w : SourceCircuit a b)
    (S : Finset (sourceLocations w)) :=
  ∀ i : selectedPartialSlots A w S,
    Fin (min (sourceDims w (partialSlotEquiv A w i.1).1).1
      (sourceDims w (partialSlotEquiv A w i.1).1).2) ×
    Fin (min (sourceDims w (partialSlotEquiv A w i.1).1).1
      (sourceDims w (partialSlotEquiv A w i.1).1).2)

/-- Reindex Schmidt assignments by the original corrected source occurrences. -/
def partialSchmidtCoordinateEquiv (A : P → Bool) (w : SourceCircuit a b)
    (S : Finset (sourceLocations w))
    (hS : ∀ e ∈ S, A (endpoints w e).1 = true ∨ A (endpoints w e).2 = true) :
    PartialSchmidtCoordinates A w S ≃
      (∀ e : S, Fin (min (sourceDims w e.1).1 (sourceDims w e.1).2) ×
        Fin (min (sourceDims w e.1).1 (sourceDims w e.1).2)) :=
  Equiv.piCongrLeft
    (fun e : S ↦ Fin (min (sourceDims w e.1).1 (sourceDims w e.1).2) ×
      Fin (min (sourceDims w e.1).1 (sourceDims w e.1).2))
    (selectedPartialSlotEquiv A w S hS)

/-- Reindexing reads the same pair of endpoint indices at the corresponding occurrence. -/
theorem partialSchmidtCoordinateEquiv_apply (A : P → Bool) (w : SourceCircuit a b)
    (S : Finset (sourceLocations w))
    (hS : ∀ e ∈ S, A (endpoints w e).1 = true ∨ A (endpoints w e).2 = true)
    (u : PartialSchmidtCoordinates A w S) (i : selectedPartialSlots A w S) :
    partialSchmidtCoordinateEquiv A w S hS u (selectedPartialSlotEquiv A w S hS i) = u i :=
  Equiv.piCongrLeft_apply_apply _ _ _ _

variable (A : P → Bool) (w : SourceCircuit a b) (S : Finset (sourceLocations w))
    (E : ∀ e : sourceLocations w, branchLabels w e.1 →
      Matrix (Fin (sourceDims w e).1) (Fin (min (sourceDims w e).1 (sourceDims w e).2)) ℂ)
    (F : ∀ e : sourceLocations w, branchLabels w e.1 →
      Matrix (Fin (sourceDims w e).2) (Fin (min (sourceDims w e).1 (sourceDims w e).2)) ℂ)

open Classical in
/-- Insert the actual endpoint frame columns at selected slots, preserving the
original source vectors elsewhere. -/
def partialSchmidtSourceVectors (ξ : Choices A w) (u : PartialSchmidtCoordinates A w S)
    (i : Fin (partialSlots A w).length) :
    euc (Fin (sourceDims w (partialSlotEquiv A w i).1).1) ⊗[ℂ]
      euc (Fin (sourceDims w (partialSlotEquiv A w i).1).2) :=
  if h : i ∈ selectedPartialSlots A w S then
    WithLp.toLp 2 (fun x ↦ E (partialSlotEquiv A w i).1 (partialSlotChoice A w ξ i)
        x (u ⟨i, h⟩).1) ⊗ₜ[ℂ]
      WithLp.toLp 2 (fun x ↦ F (partialSlotEquiv A w i).1 (partialSlotChoice A w ξ i)
        x (u ⟨i, h⟩).2)
  else partialSlotVector A w ξ i

/-- The corrected circuit density is the actual Gaussian coefficient sum in
the original Schmidt frames. The equality holds for every sample and every
input matrix, before any norm or probability estimate.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 338–434. -/
theorem correctedSourceTerm_gaussian_eq_sum {m n : Type} [Fintype m] [Fintype n]
    (hS : ∀ e ∈ S, A (endpoints w e).1 = true ∨ A (endpoints w e).2 = true)
    (k : ℕ)
    (lam : ∀ e : sourceLocations w, branchLabels w e.1 →
      Fin (min (sourceDims w e).1 (sourceDims w e).2) → ℝ)
    (hsource : ∀ e ξ, ambientSchmidtVector (lam e ξ) (E e ξ) (F e ξ) =
      (sourceCoordinates w e ξ).ofLp)
    (ω : SourceGaussianSamples w k)
    (bIn : OrthonormalBasis n ℂ (Mem a)) (bOut : OrthonormalBasis m ℂ (Mem b))
    (ρ : Matrix n n ℂ) :
    let R := partialSlots A w
    let U := fun i : Fin R.length ↦ euc (Fin (sourceDims w (partialSlotEquiv A w i).1).1)
    let V := fun i : Fin R.length ↦ euc (Fin (sourceDims w (partialSlotEquiv A w i).1).2)
    correctedSourceTerm w S (sourceGaussianCorrection w k lam E F ω) bIn bOut ρ =
      ∑ ξ, ∑ ζ, (coefficient A w ξ * conj (coefficient A w ζ)) •
        ∑ u : PartialSchmidtCoordinates A w S, ∑ v : PartialSchmidtCoordinates A w S,
          (∏ i : selectedPartialSlots A w S,
            sourceCorrection k
              (lam (partialSlotEquiv A w i.1).1 (partialSlotChoice A w ξ i.1))
              (lam (partialSlotEquiv A w i.1).1 (partialSlotChoice A w ζ i.1))
              (ω (partialSlotEquiv A w i.1).1
                (partialSlotChoice A w ξ i.1, partialSlotChoice A w ζ i.1)) (u i) (v i)) •
            ((partialResidual A w ξ).preparedMatrix R U V
              (partialSchmidtSourceVectors A w S E F ξ u)
              (Layout.mapOwner (affectedOwner A) a)
              (bIn.map (Layout.mapOwnerIso (affectedOwner A) a))
              (bOut.map (Layout.mapOwnerIso (affectedOwner A) b)) * ρ *
              ((partialResidual A w ζ).preparedMatrix R U V
                (partialSchmidtSourceVectors A w S E F ζ v)
                (Layout.mapOwner (affectedOwner A) a)
                (bIn.map (Layout.mapOwnerIso (affectedOwner A) a))
                (bOut.map (Layout.mapOwnerIso (affectedOwner A) b)))ᴴ) := by
  classical
  dsimp only
  rw [correctedSourceTerm_eq_sourceContraction A w S hS]
  apply Finset.sum_congr rfl
  intro ξ _
  apply Finset.sum_congr rfl
  intro ζ _
  apply congrArg ((coefficient A w ξ * conj (coefficient A w ζ)) • ·)
  simp_rw [sourceGaussianCorrection_eq_transport w k lam E F hsource]
  let R := partialSlots A w
  let U := fun i : Fin R.length ↦ euc (Fin (sourceDims w (partialSlotEquiv A w i).1).1)
  let V := fun i : Fin R.length ↦ euc (Fin (sourceDims w (partialSlotEquiv A w i).1).2)
  let bU := fun i : Fin R.length ↦
    EuclideanSpace.basisFun (Fin (sourceDims w (partialSlotEquiv A w i).1).1) ℂ
  let bV := fun i : Fin R.length ↦
    EuclideanSpace.basisFun (Fin (sourceDims w (partialSlotEquiv A w i).1).2) ℂ
  let K := fun i : Fin R.length ↦ Fin (min (sourceDims w (partialSlotEquiv A w i).1).1
    (sourceDims w (partialSlotEquiv A w i).1).2)
  let uU := fun (ν : Choices A w) (i : Fin R.length) (j : K i) ↦
    (WithLp.toLp 2 (fun x ↦ E (partialSlotEquiv A w i).1
      (partialSlotChoice A w ν i) x j) : U i)
  let uV := fun (ν : Choices A w) (i : Fin R.length) (j : K i) ↦
    (WithLp.toLp 2 (fun x ↦ F (partialSlotEquiv A w i).1
      (partialSlotChoice A w ν i) x j) : V i)
  let M := fun i : Fin R.length ↦ sourceCorrection k
    (lam (partialSlotEquiv A w i).1 (partialSlotChoice A w ξ i))
    (lam (partialSlotEquiv A w i).1 (partialSlotChoice A w ζ i))
    (ω (partialSlotEquiv A w i).1 (partialSlotChoice A w ξ i, partialSlotChoice A w ζ i))
  exact
    (partialResidual A w ξ).sourceContraction_preparedDensityCoefficient_selected_frames
      R U V bU bV bU bV (uU ξ) (uV ξ) (uU ζ) (uV ζ)
      (partialSlotVector A w ξ) (partialSlotVector A w ζ) (selectedPartialSlots A w S) M
      (Layout.mapOwner (affectedOwner A) a) (partialResidual A w ζ)
      (bIn.map (Layout.mapOwnerIso (affectedOwner A) a))
      (bOut.map (Layout.mapOwnerIso (affectedOwner A) b)) ρ

end TNLean.PEPS.PairEffect.SourceCircuit
