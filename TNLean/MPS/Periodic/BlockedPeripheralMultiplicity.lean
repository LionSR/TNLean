/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Channel.Peripheral.GroupStructure
import QICLean.Channel.Peripheral.AdjointSpectrum
import QICLean.Channel.Irreducible.Ergodicity
import TNLean.MPS.Periodic.Defs

/-!
# Peripheral eigenspace multiplicities under adjunction

The Frobenius adjoint preserves the dimensions of eigenspaces, with complex
conjugation of the eigenvalue. This transfers the simple peripheral spectrum
of the unital adjoint of a periodic channel back to the channel itself.

Source: arXiv:1708.00029, Lemma `lem:blocking-arbitrary`, lines 765--806.
-/

open scoped Matrix ComplexOrder MatrixOrder BigOperators

namespace MPSTensor

variable {D : ℕ}

noncomputable section

local instance instPeriodicMatrixNormedAddCommGroup :
    NormedAddCommGroup (Matrix (Fin D) (Fin D) ℂ) :=
  Matrix.toMatrixNormedAddCommGroup (n := Fin D) (𝕜 := ℂ) 1
    (Matrix.PosDef.one (n := Fin D) (R := ℂ))

local instance instPeriodicMatrixInnerProductSpace :
    InnerProductSpace ℂ (Matrix (Fin D) (Fin D) ℂ) :=
  Matrix.toMatrixInnerProductSpace (n := Fin D) (𝕜 := ℂ) 1
    (Matrix.PosDef.one (n := Fin D) (R := ℂ)).posSemidef

/-- A linear map and its Frobenius adjoint have eigenspaces of equal dimension
at conjugate eigenvalues. -/
theorem finrank_eigenspace_adjoint_eq
    (E : Module.End ℂ (Matrix (Fin D) (Fin D) ℂ)) (μ : ℂ) :
    Module.finrank ℂ (E.eigenspace μ) =
      Module.finrank ℂ (Module.End.eigenspace E.adjoint (star μ)) := by
  have hAdj : (E - μ • 1).adjoint = E.adjoint - (star μ) • 1 := by
    simp only [← LinearMap.star_eq_adjoint, star_sub, star_smul, star_one]
  have hRank := LinearMap.finrank_range_adjoint (E - μ • 1)
  have hLeft := (E - μ • 1).finrank_range_add_finrank_ker
  have hRight := ((E - μ • 1).adjoint).finrank_range_add_finrank_ker
  rw [hAdj] at hRank hRight
  rw [Module.End.eigenspace_def, Module.End.eigenspace_def]
  omega

/-- The Kraus map of the conjugate-transposed family has the same
eigenspace dimensions at conjugate eigenvalues. -/
theorem finrank_eigenspace_conjTranspose_eq
    {d : ℕ} (K : Fin d → Matrix (Fin D) (Fin D) ℂ) (μ : ℂ) :
    Module.finrank ℂ (Module.End.eigenspace (Kraus.mapLM K) μ) =
      Module.finrank ℂ
        (Module.End.eigenspace (Kraus.mapLM fun i => (K i)ᴴ) (star μ)) := by
  rw [Kraus.mapLM_conjTranspose_eq_adjoint]
  exact finrank_eigenspace_adjoint_eq (Kraus.mapLM K) μ

/-- Every peripheral eigenspace of the transfer map of a periodic tensor
has dimension one. The transfer map is trace preserving, so the simple
peripheral spectrum of its unital adjoint is carried back by Frobenius
adjunction.
Source: arXiv:1708.00029, Section 2.1 and Lemma
`lem:blocking-arbitrary`, lines 765--806. -/
theorem IsPeriodic.finrank_peripheral_eigenspace_eq_one
    {d m : ℕ} (A : MPSTensor d D) (hA : IsPeriodic m A)
    {μ : ℂ} (hμ : μ ∈ peripheralEigenvalues (Kraus.mapLM A)) :
    Module.finrank ℂ (Module.End.eigenspace (Kraus.mapLM A) μ) = 1 := by
  have : NeZero D := ⟨hA.bondDim_ne_zero⟩
  let E := Kraus.mapLM A
  have hIrr : IsIrreducibleMap E :=
    Kraus.isIrreducibleMap_mapLM_of_isIrreducibleFamily A hA.irreducible
  have hE : IsChannel E := Kraus.isChannel_mapLM A hA.leftCanonical
  obtain ⟨ρ, _, hρpd, hρfix, _⟩ :=
    hE.exists_unique_density_fixedPoint_of_irreducible E hIrr (NeZero.pos D)
  let K : Fin d → Matrix (Fin D) (Fin D) ℂ := fun i => (A i)ᴴ
  have hUnital : KadisonSchwarz.IsUnitalKraus K := by
    unfold KadisonSchwarz.IsUnitalKraus
    simpa only [K, Matrix.conjTranspose_conjTranspose,
      IsLeftCanonical, Kraus.IsTP] using hA.leftCanonical
  have hρfix' : Kraus.adjointMap K ρ = ρ := by
    simpa only [K, E, Kraus.adjointMap_conjTranspose_eq_map,
      Kraus.mapLM_apply] using hρfix
  have hIrrK : IsIrreducibleMap (Kraus.mapLM K) :=
    Kraus.isIrreducibleMap_mapLM_conjTranspose A hIrr
  have hμK : star μ ∈ peripheralEigenvalues (Kraus.mapLM K) := by
    change star μ ∈ peripheralEigenvalues (Kraus.mapLM fun i => (A i)ᴴ)
    rw [Kraus.peripheralEigenvalues_mapLM_conjTranspose]
    exact ⟨μ, hμ, rfl⟩
  have hdimK := PeripheralSpectrum.peripheral_eigenvalue_multiplicity_one
    K hUnital ρ hρpd hρfix' hIrrK hμK
  rw [finrank_eigenspace_conjTranspose_eq A μ]
  exact hdimK

end
end MPSTensor
