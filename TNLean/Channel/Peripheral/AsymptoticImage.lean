/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.EigenspaceMap
import TNLean.Channel.Peripheral.CesaroRecurrence
import TNLean.Channel.FixedPoint.StationarySpan

/-!
# The asymptotic image — Wolf's proposition on `X_T`

Let `T : M_d(ℂ) → M_d(ℂ)` be a positive trace-preserving linear map and let

`X_T := span {X | ∃ φ : ℝ, T X = exp (i φ) • X}`

be the span of the peripheral eigenvectors of Wolf Equation (6.65).  Wolf's
proposition on the *asymptotic image* describes `X_T` through the peripheral
spectral projection `T_φ` of Wolf Equation (6.12):

1. `T_φ (M_d(ℂ)) = X_T`,
2. there are positive semidefinite `ρ_i` with `X_T = span {ρ_i}`,
3. `T (X_T) = X_T`.

The proof follows Wolf.  Clause 1 records that `X_T` is exactly the set of
fixed points of `T_φ`, which for a projection is its image.  Clause 2 applies
Wolf Corollary 6.5, Linearly independent stationary states
(`IsPositiveMap.fixedPointsSubmodule_spanned_by_stationaryDensities`), to
`T_φ`, which is itself positive and trace-preserving; this is the corollary
Wolf's own proof of the proposition invokes at this step.  Clause 3 expands an
element of `X_T` in peripheral eigenvectors: on the `μ`-eigenspace `T` acts as
multiplication by the unit phase `μ`, and a nonzero scalar maps an eigenspace
onto itself (`Module.End.map_eigenspace_of_ne_zero`).

## Main statements

* `IsPositiveMap.fixedPointsSubmodule_peripheralProjection`: `X_T` is the
  fixed-point space of `T_φ`.
* `IsPositiveMap.range_peripheralProjection_eq_iSup_eigenspace`: clause 1.
* `IsPositiveMap.span_stationaryDensity_peripheralProjection_eq_peripheralSubspace`
  and `IsPositiveMap.exists_posSemidef_span_eq_iSup_eigenspace`: clause 2.
* `IsPositiveMap.map_peripheralSubspace`: clause 3.
* `IsPositiveMap.asymptotic_image`: the three clauses together.

## References

* M. Wolf, *Quantum Channels & Operations: Guided Tour*, Proposition 6.12
  (Asymptotic image) and Equation (6.65); local source
  `Notes/WolfNoteTexSource/ch06_spectral_properties.tex`, lines 1568--1590.
* M. Wolf, *Quantum Channels & Operations: Guided Tour*, Corollary 6.5
  (Linearly independent stationary states); local source, lines 1204--1212.
-/

open scoped ComplexOrder
open Matrix

namespace IsPositiveMap

variable {D : ℕ} [NeZero D] {T : Module.End ℂ (Matrix (Fin D) (Fin D) ℂ)}

omit [NeZero D] in
/-- The peripheral subspace `X_T` is exactly the fixed-point space of the
peripheral spectral projection `T_φ`.  This is Wolf's observation that "`X_T`
coincides with the space of fixed points of `T_φ`"; local source
`Notes/WolfNoteTexSource/ch06_spectral_properties.tex`, lines 1568--1590. -/
theorem fixedPointsSubmodule_peripheralProjection
    (f : Module.End ℂ (Matrix (Fin D) (Fin D) ℂ)) :
    fixedPointsSubmodule f.peripheralProjection = f.peripheralSubspace := by
  ext X
  rw [mem_fixedPointsSubmodule, Module.End.peripheralProjection_apply_eq_self_iff]

/-- **Wolf, asymptotic image, clause 1**: `T_φ (M_d(ℂ)) = X_T`, where `X_T` is
the span of the peripheral eigenvectors of Wolf Equation (6.65).

The image of the projection `T_φ` is its fixed-point space, which is the
peripheral spectral subspace; for a positive trace-preserving map the
peripheral Jordan blocks are trivial (Wolf Proposition 6.2), so that subspace
is the span of the peripheral eigenspaces.

Source: Wolf Proposition 6.12, lines 1568--1590; local source
`Notes/WolfNoteTexSource/ch06_spectral_properties.tex`. -/
theorem range_peripheralProjection_eq_iSup_eigenspace
    (hPos : IsPositiveMap T) (hTP : IsTracePreservingMap T) :
    LinearMap.range T.peripheralProjection =
      ⨆ μ ∈ peripheralEigenvalues T, T.eigenspace μ := by
  rw [Module.End.range_peripheralProjection, hPos.peripheralSubspace_eq_iSup_eigenspace hTP]

/-- **Wolf, asymptotic image, clause 2**, spanning form: `X_T` is spanned by
the stationary density matrices of `T_φ`.

Wolf derives this from clause 1 together with Corollary 6.5: the peripheral
projection of a positive trace-preserving map is again positive and
trace-preserving, and Corollary 6.5 spans the fixed-point space of such a map
by stationary density matrices.

Source: Wolf Proposition 6.12, lines 1568--1590, and Corollary 6.5, lines
1204--1212; local source
`Notes/WolfNoteTexSource/ch06_spectral_properties.tex`. -/
theorem span_stationaryDensity_peripheralProjection_eq_peripheralSubspace
    (hPos : IsPositiveMap T) (hTP : IsTracePreservingMap T) :
    Submodule.span ℂ {ρ | IsStationaryDensity T.peripheralProjection ρ} =
      T.peripheralSubspace := by
  rw [fixedPointsSubmodule_spanned_by_stationaryDensities _
      (hPos.peripheralProjection_isPositiveMap hTP)
      (hPos.peripheralProjection_isTracePreservingMap hTP),
    fixedPointsSubmodule_peripheralProjection]

/-- **Wolf, asymptotic image, clause 2**: there exist positive semidefinite
matrices whose span is `X_T`.

Source: Wolf Proposition 6.12, lines 1568--1590; local source
`Notes/WolfNoteTexSource/ch06_spectral_properties.tex`. -/
theorem exists_posSemidef_span_eq_iSup_eigenspace
    (hPos : IsPositiveMap T) (hTP : IsTracePreservingMap T) :
    ∃ S : Set (Matrix (Fin D) (Fin D) ℂ), (∀ ρ ∈ S, ρ.PosSemidef) ∧
      Submodule.span ℂ S = ⨆ μ ∈ peripheralEigenvalues T, T.eigenspace μ :=
  ⟨{ρ | IsStationaryDensity T.peripheralProjection ρ},
    fun _ hρ ↦ IsStationaryDensity.posSemidef hρ, by
      rw [hPos.span_stationaryDensity_peripheralProjection_eq_peripheralSubspace hTP,
        hPos.peripheralSubspace_eq_iSup_eigenspace hTP]⟩

/-- **Wolf, asymptotic image, clause 3**: `T (X_T) = X_T`.

Expanding an element of `X_T` in peripheral eigenvectors reduces the claim to
one eigenspace at a time, and there `T` acts as multiplication by a unit
phase, which is invertible.

Source: Wolf Proposition 6.12, lines 1568--1590; local source
`Notes/WolfNoteTexSource/ch06_spectral_properties.tex`. -/
theorem map_peripheralSubspace
    (hPos : IsPositiveMap T) (hTP : IsTracePreservingMap T) :
    Submodule.map T T.peripheralSubspace = T.peripheralSubspace := by
  rw [hPos.peripheralSubspace_eq_iSup_eigenspace hTP, Submodule.map_iSup]
  refine iSup_congr fun μ ↦ ?_
  rw [Submodule.map_iSup]
  exact iSup_congr fun hμ ↦
    T.map_eigenspace_of_ne_zero (norm_ne_zero_iff.mp (by rw [hμ.2]; exact one_ne_zero))

/-- **Wolf Proposition 6.12 (Asymptotic image).**  For a positive trace-preserving
linear map `T` on `M_d(ℂ)`, write `X_T` for the span of the peripheral
eigenvectors of Wolf Equation (6.65).  Then

1. `T_φ (M_d(ℂ)) = X_T`,
2. there are positive semidefinite matrices whose span is `X_T`,
3. `T (X_T) = X_T`.

Source: Wolf Proposition 6.12, lines 1568--1590; local source
`Notes/WolfNoteTexSource/ch06_spectral_properties.tex`. -/
theorem asymptotic_image (hPos : IsPositiveMap T) (hTP : IsTracePreservingMap T) :
    (LinearMap.range T.peripheralProjection =
        ⨆ μ ∈ peripheralEigenvalues T, T.eigenspace μ) ∧
      (∃ S : Set (Matrix (Fin D) (Fin D) ℂ), (∀ ρ ∈ S, ρ.PosSemidef) ∧
        Submodule.span ℂ S = ⨆ μ ∈ peripheralEigenvalues T, T.eigenspace μ) ∧
      Submodule.map T (⨆ μ ∈ peripheralEigenvalues T, T.eigenspace μ) =
        ⨆ μ ∈ peripheralEigenvalues T, T.eigenspace μ :=
  ⟨hPos.range_peripheralProjection_eq_iSup_eigenspace hTP,
    hPos.exists_posSemidef_span_eq_iSup_eigenspace hTP, by
      rw [← hPos.peripheralSubspace_eq_iSup_eigenspace hTP, hPos.map_peripheralSubspace hTP]⟩

end IsPositiveMap
