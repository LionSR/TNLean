/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.MatrixOperatorSpace
import TNLean.Channel.Determinant.Bound
import TNLean.Channel.KrausMap
import TNLean.Channel.PerronFrobenius.Existence
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Spectral radius of positive maps — Wolf Proposition 6.1

**Wolf Proposition 6.1**: For a positive trace-preserving (or unital) map
$T: M_d(\mathbb{C}) \to M_d(\mathbb{C})$, the spectral radius is $1$, all eigenvalues
lie in the unit disk, and $1$ is an eigenvalue.

The eigenvalue modulus bound $|\lambda| \le 1$ is provided by
`IsPositiveMap.eigenvalue_norm_le_one_of_tracePreserving` in
`TNLean.Channel.Determinant.Bound`.  Eigenvalue-$1$ existence is proved here
using the Perron--Frobenius theorem (`exists_posSemidef_eigenvector`) together
with trace preservation.

The general $\varrho(T) \le \|T(\mathbf 1)\|_\infty$ bound for arbitrary
positive maps relies on the Russo--Dye theorem and is documented in
`docs/paper-gaps/wolf_prop61_russo_dye_factor.tex`.

## Main result

* `IsPositiveMap.eigenvalue_one_exists_of_tracePreserving`:
  nonzero PSD fixed point for positive trace-preserving maps.
* `spectralRadius_le_one_of_forall_eigenvalue_norm_le_one`: the norm-agnostic
  step transporting a pointwise eigenvalue bound to a spectral-radius bound,
  shared by every operator-norm choice used for this map.
* `Kraus.eigenvalue_norm_le_one_of_isTP`, `Kraus.spectralRadius_mapLM_le_one_of_isTP`:
  eigenvalue and spectral-radius bounds for trace-preserving Kraus maps.

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Proposition 6.1][Wolf2012Quantum]
-/

open scoped Matrix ComplexOrder
open Matrix

variable {D : ℕ}

namespace IsPositiveMap

/-- **Wolf Proposition 6.1** (eigenvalue-1 existence): For a positive trace-preserving
map on $M_D(\mathbb{C})$ with $D > 0$, there exists a nonzero PSD matrix $\rho$
such that $T(\rho) = \rho$.

This completes the trace-preserving case of Wolf's Proposition 6.1:
combined with `eigenvalue_norm_le_one_of_tracePreserving` (which gives
$|\lambda| \le 1$ for every eigenvalue), we get that the spectral radius is $1$
and $1$ is an eigenvalue.

The proof obtains a PSD eigenvector with eigenvalue $r > 0$ via
`exists_posSemidef_eigenvector` (Perron--Frobenius / Brouwer fixed point),
then forces $r = 1$ by trace preservation.

Source: Wolf, *Quantum Channels & Operations*, Proposition 6.1; local source
`Notes/WolfNoteTexSource/ch06_spectral_properties.tex`, lines 73--92. -/
theorem eigenvalue_one_exists_of_tracePreserving
    [NeZero D] {T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ}
    (hPos : IsPositiveMap T) (hTP : IsTracePreservingMap T) :
    ∃ ρ : Matrix (Fin D) (Fin D) ℂ, ρ.PosSemidef ∧ ρ ≠ 0 ∧ T ρ = ρ := by
  -- For a trace-preserving positive map, nonzero PSD matrices cannot be annihilated:
  -- if T(ρ) = 0 then trace preservation gives trace(ρ) = 0,
  -- but a nonzero PSD matrix has positive trace.
  have hNZ : ∀ {ρ : Matrix (Fin D) (Fin D) ℂ}, ρ.PosSemidef → ρ ≠ 0 → T ρ ≠ 0 := by
    intro ρ hρ_psd hρ_ne hzero
    have htr_zero : trace (T ρ) = 0 := by simp [hzero]
    rw [hTP ρ] at htr_zero
    have htr_pos : 0 < trace ρ := by
      have h_nonneg := hρ_psd.trace_nonneg
      have h_ne_zero : trace ρ ≠ 0 := mt hρ_psd.trace_eq_zero_iff.mp hρ_ne
      exact h_nonneg.lt_of_ne h_ne_zero.symm
    exact htr_pos.ne' htr_zero
  -- Get eigenvalue r > 0 with PSD eigenvector (Perron--Frobenius)
  obtain ⟨ρ, r, hρ_psd, hρ_ne, hr_pos, h_eig⟩ :=
    exists_posSemidef_eigenvector (D := D) T hPos (hNZ := hNZ)
  -- Trace preservation forces r = 1
  have hr_one : r = 1 := by
    have htr_eq : trace (T ρ) = trace ρ := hTP ρ
    rw [h_eig, trace_smul, smul_eq_mul] at htr_eq
    have htr_ne_zero : trace ρ ≠ 0 := mt hρ_psd.trace_eq_zero_iff.mp hρ_ne
    field_simp [htr_ne_zero] at htr_eq
    exact_mod_cast htr_eq
  refine ⟨ρ, hρ_psd, hρ_ne, ?_⟩
  simpa [hr_one, one_smul] using h_eig

end IsPositiveMap

/-- If every eigenvalue of a linear endomorphism of a finite-dimensional complex normed space
has modulus at most one, then its spectral radius (computed after transport to the induced
continuous linear map) is at most one.

This is the norm-agnostic step of Wolf Proposition 6.1's spectral-radius conclusion: only the
algebraic fact `spectrum = eigenvalues` and the identification of `spectrum` along the
`AlgEquiv` to continuous linear maps are used, so the same argument serves any choice of
operator norm on `V`. -/
theorem spectralRadius_le_one_of_forall_eigenvalue_norm_le_one
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
    (E : V →ₗ[ℂ] V) (h : ∀ μ, Module.End.HasEigenvalue E μ → ‖μ‖ ≤ 1) :
    spectralRadius ℂ (Module.End.toContinuousLinearMap V E) ≤ 1 := by
  have hSpec : spectrum ℂ (Module.End.toContinuousLinearMap V E) = spectrum ℂ E :=
    AlgEquiv.spectrum_eq (Module.End.toContinuousLinearMap V) E
  rw [spectralRadius]
  refine iSup₂_le fun μ hμ ↦ ?_
  have hμE : μ ∈ spectrum ℂ E := hSpec ▸ hμ
  have hEig : Module.End.HasEigenvalue E μ := Module.End.hasEigenvalue_iff_mem_spectrum.mpr hμE
  exact_mod_cast h μ hEig

/-!
## Spectral-radius bound for trace-preserving Kraus maps

A trace-preserving finite Kraus map has all eigenvalues in the closed unit
disk: it is a completely positive trace-preserving map, so
`IsPositiveMap.eigenvalue_norm_le_one_of_tracePreserving` applies once the
trivial zero-dimensional case is discharged separately.
-/

namespace Kraus

variable {d D : ℕ}

local notation "Mat" => Matrix (Fin D) (Fin D) ℂ

/-- Every eigenvalue of a trace-preserving finite Kraus map has modulus at most one.

This is the trace-preserving form of the spectral bound in Wolf, Proposition 6.1,
obtained from the positive-map bound after discharging the trivial
zero-dimensional case. -/
theorem eigenvalue_norm_le_one_of_isTP
    (K : Fin d → Mat) (hTP : IsTP K)
    (μ : ℂ) (hμ : Module.End.HasEigenvalue (mapLM K) μ) :
    ‖μ‖ ≤ 1 := by
  rcases eq_or_ne D 0 with hD0 | hD0
  · subst hD0
    obtain ⟨v, hv, hvne⟩ := hμ.exists_hasEigenvector
    exact absurd (Subsingleton.elim v 0) hvne
  · have : NeZero D := ⟨hD0⟩
    exact (isCPMap_mapLM K).isPositiveMap.eigenvalue_norm_le_one_of_tracePreserving
      (isTracePreservingMap_mapLM_of_isTP K hTP) μ hμ

section OperatorSpace

open scoped TNOperatorSpace

/-- A trace-preserving finite Kraus map has spectral radius at most one. -/
theorem spectralRadius_mapLM_le_one_of_isTP
    (K : Fin d → Mat) (hTP : IsTP K) :
    spectralRadius ℂ
      ((Module.End.toContinuousLinearMap (Matrix (Fin D) (Fin D) ℂ)) (mapLM K)) ≤ 1 :=
  spectralRadius_le_one_of_forall_eigenvalue_norm_le_one (mapLM K)
    (fun μ hμ ↦ eigenvalue_norm_le_one_of_isTP K hTP μ hμ)

end OperatorSpace

end Kraus
