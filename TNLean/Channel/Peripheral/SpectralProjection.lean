/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Channel.Peripheral.JordanBlocks
import TNLean.Channel.Peripheral.Spectrum
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable

/-!
# Peripheral spectral projections — Wolf Equations (6.11)–(6.13)

For a linear endomorphism `f` of a finite-dimensional complex vector space, the
**peripheral spectral subspace** is the sum of the maximal generalized
eigenspaces over the peripheral spectrum (the eigenvalues of modulus one), and
the **non-peripheral spectral subspace** is the corresponding sum over the
remaining eigenvalues.  The two subspaces are complementary, so there is a
linear projection onto the peripheral part: the **peripheral spectral
projection** `T_φ` of Wolf Equation (6.12), i.e. `Σ_{k:|λₖ|=1} Pₖ` in the
spectral decomposition of Wolf Equation (6.5).  Composing with `f` gives the
phase-weighted map `T_φ' = f ∘ T_φ` of Wolf Equation (6.13),
`Σ_{k:|λₖ|=1} λₖ Pₖ`; the identity `T_φ' = T T_φ` of Wolf Proposition 6.3(ii)
holds by construction.

For a positive trace-preserving map on matrices, Wolf Proposition 6.2 (trivial
Jordan blocks for the peripheral spectrum, proved in
`TNLean.Channel.Peripheral.JordanBlocks`) upgrades the peripheral subspace to
the span of the peripheral *eigenspaces*, which is the space `X_T` of Wolf
Equation (6.65).

## Main definitions

* `Module.End.peripheralSubspace`: sum of peripheral generalized eigenspaces.
* `Module.End.nonPeripheralSubspace`: sum of the remaining generalized
  eigenspaces.
* `Module.End.isCompl_peripheralSubspace_nonPeripheralSubspace`:
  complementarity of the two subspaces.
* `Module.End.peripheralProjection`: the projection `T_φ` onto the peripheral
  subspace along the non-peripheral subspace (Wolf (6.12)).
* `Module.End.peripheralWeightedProjection`: the map `T_φ' = T ∘ T_φ`
  (Wolf (6.13)).

## Main statements

* `Module.End.peripheralProjection_comp`: `T_φ` commutes with `T`.
* `Module.End.peripheralWeightedProjection_apply_of_mem_eigenspace`:
  `T_φ'` acts as `μ • id` on the peripheral `μ`-eigenspace (Wolf (6.13)).
* `IsPositiveMap.maxGenEigenspace_eq_eigenspace_of_norm_eq_one`: Wolf
  Proposition 6.2, subspace form.
* `IsPositiveMap.peripheralSubspace_eq_iSup_eigenspace`: Wolf Equation (6.65).

## References

* M. Wolf, *Quantum Channels & Operations: Guided Tour*, Equations (6.5),
  (6.11)--(6.13), (6.65) and Proposition 6.3(ii); local source
  `Notes/WolfNoteTexSource/ch06_spectral_properties.tex`, lines 128--256.
-/

open scoped Matrix ComplexOrder
open Matrix

namespace Module.End

variable {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

/-! ### The peripheral and non-peripheral spectral subspaces -/

/-- The **peripheral spectral subspace**: the sum of the maximal generalized
eigenspaces over the peripheral spectrum (the eigenvalues of modulus one).

This is the range of the spectral projection `Σ_{k:|λₖ|=1} Pₖ` of Wolf
Equation (6.12); for positive trace-preserving maps it coincides with the span
`X_T` of the peripheral eigenvectors of Wolf Equation (6.65). -/
noncomputable def peripheralSubspace (f : Module.End ℂ V) : Submodule ℂ V :=
  ⨆ μ ∈ peripheralEigenvalues f, f.maxGenEigenspace μ

/-- The **non-peripheral spectral subspace**: the sum of the maximal
generalized eigenspaces over the eigenvalues of modulus different from one. -/
noncomputable def nonPeripheralSubspace (f : Module.End ℂ V) : Submodule ℂ V :=
  ⨆ μ ∈ {μ | f.HasEigenvalue μ ∧ ‖μ‖ ≠ 1}, f.maxGenEigenspace μ

/-- The non-peripheral eigenvalue set of a finite-dimensional endomorphism is
finite. -/
theorem finite_hasEigenvalue_and_norm_ne_one (f : Module.End ℂ V) :
    {μ | f.HasEigenvalue μ ∧ ‖μ‖ ≠ 1}.Finite :=
  f.finite_hasEigenvalue.subset fun _ h ↦ h.1

omit [FiniteDimensional ℂ V] in
/-- The maximal generalized eigenspace of a non-eigenvalue is trivial. -/
theorem maxGenEigenspace_eq_bot_of_not_hasEigenvalue {f : Module.End ℂ V} {μ : ℂ}
    (h : ¬ f.HasEigenvalue μ) : f.maxGenEigenspace μ = ⊥ := by
  by_contra hne
  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).mp hne
  obtain ⟨k, hk⟩ := (f.mem_maxGenEigenspace μ x).mp hx
  apply h
  have hgen : f.HasGenEigenvalue μ k := (Submodule.ne_bot_iff _).mpr
    ⟨x, (Module.End.mem_genEigenspace).mpr ⟨k, le_refl _, LinearMap.mem_ker.mpr hk⟩, hx0⟩
  exact f.hasEigenvalue_of_hasGenEigenvalue hgen

/-- The generalized eigenspaces over the eigenvalues already span the whole
space (over an algebraically closed field, non-eigenvalues contribute trivial
summands). -/
theorem iSup_maxGenEigenspace_hasEigenvalue_eq_top (f : Module.End ℂ V) :
    ⨆ μ ∈ {μ | f.HasEigenvalue μ}, f.maxGenEigenspace μ = ⊤ := by
  apply top_unique
  rw [← f.iSup_maxGenEigenspace_eq_top]
  refine iSup_le fun μ ↦ ?_
  by_cases hμ : f.HasEigenvalue μ
  · exact le_biSup f.maxGenEigenspace hμ
  · rw [maxGenEigenspace_eq_bot_of_not_hasEigenvalue hμ]
    exact bot_le

/-- The peripheral and non-peripheral spectral subspaces are complementary:
the generalized eigenspaces are independent and span the whole space.  This is
the complementarity underlying the spectral projection of Wolf Equation
(6.12). -/
theorem isCompl_peripheralSubspace_nonPeripheralSubspace (f : Module.End ℂ V) :
    IsCompl f.peripheralSubspace f.nonPeripheralSubspace := by
  constructor
  · exact f.independent_maxGenEigenspace.disjoint_biSup_biSup'
      (Set.disjoint_left.mpr fun _ ⟨_, h1⟩ ⟨_, h2⟩ ↦ h2 h1)
      (peripheralEigenvalues_finite f)
  · rw [codisjoint_iff, peripheralSubspace, nonPeripheralSubspace, ← iSup_union]
    have hU : peripheralEigenvalues f ∪ {μ | f.HasEigenvalue μ ∧ ‖μ‖ ≠ 1} =
        {μ | f.HasEigenvalue μ} := by
      ext μ
      simp only [peripheralEigenvalues, Set.mem_union, Set.mem_setOf_eq]
      constructor
      · rintro (⟨h, -⟩ | ⟨h, -⟩) <;> exact h
      · intro h
        by_cases h1 : ‖μ‖ = 1
        · exact Or.inl ⟨h, h1⟩
        · exact Or.inr ⟨h, h1⟩
    rw [hU]
    exact f.iSup_maxGenEigenspace_hasEigenvalue_eq_top

/-! ### The peripheral spectral projection `T_φ` -/

/-- The **peripheral spectral projection** `T_φ`: the projection onto the
peripheral spectral subspace along the non-peripheral spectral subspace.  This
is `Σ_{k:|λₖ|=1} Pₖ` of Wolf Equation (6.12), written using the spectral
decomposition of Wolf Equation (6.5).

Source: Wolf, Equation (6.12); local source
`Notes/WolfNoteTexSource/ch06_spectral_properties.tex`, lines 213--224. -/
noncomputable def peripheralProjection (f : Module.End ℂ V) : Module.End ℂ V :=
  f.peripheralSubspace.projection f.nonPeripheralSubspace
    f.isCompl_peripheralSubspace_nonPeripheralSubspace

/-- The peripheral spectral projection takes values in the peripheral
subspace. -/
@[simp]
theorem peripheralProjection_apply_mem (f : Module.End ℂ V) (x : V) :
    f.peripheralProjection x ∈ f.peripheralSubspace :=
  Submodule.projection_apply_mem _ _

/-- The peripheral spectral projection fixes the peripheral subspace. -/
theorem peripheralProjection_apply_of_mem (f : Module.End ℂ V) {x : V}
    (hx : x ∈ f.peripheralSubspace) : f.peripheralProjection x = x :=
  Submodule.projection_apply_of_mem_left _ hx

/-- The fixed points of the peripheral spectral projection are exactly the
peripheral subspace. -/
@[simp]
theorem peripheralProjection_apply_eq_self_iff (f : Module.End ℂ V) (x : V) :
    f.peripheralProjection x = x ↔ x ∈ f.peripheralSubspace :=
  Submodule.projection_eq_self_iff _ _

/-- The kernel of the peripheral spectral projection is exactly the
non-peripheral subspace. -/
@[simp]
theorem peripheralProjection_apply_eq_zero_iff (f : Module.End ℂ V) {x : V} :
    f.peripheralProjection x = 0 ↔ x ∈ f.nonPeripheralSubspace :=
  Submodule.projection_apply_eq_zero_iff _

/-- The remainder after the peripheral spectral projection lies in the
non-peripheral subspace. -/
theorem sub_peripheralProjection_mem (f : Module.End ℂ V) (x : V) :
    x - f.peripheralProjection x ∈ f.nonPeripheralSubspace :=
  Submodule.sub_projection_mem _ _

/-- The range of the peripheral spectral projection is the peripheral
subspace: the first part of Wolf's *Asymptotic image* proposition. -/
@[simp]
theorem range_peripheralProjection (f : Module.End ℂ V) :
    LinearMap.range f.peripheralProjection = f.peripheralSubspace :=
  Submodule.range_projection _

/-- The peripheral spectral projection is idempotent: `T_φ² = T_φ`. -/
theorem isIdempotentElem_peripheralProjection (f : Module.End ℂ V) :
    IsIdempotentElem f.peripheralProjection :=
  Submodule.isIdempotentElem_projection _

@[simp]
theorem peripheralProjection_apply_peripheralProjection (f : Module.End ℂ V) (x : V) :
    f.peripheralProjection (f.peripheralProjection x) = f.peripheralProjection x :=
  f.peripheralProjection_apply_of_mem (f.peripheralProjection_apply_mem x)

omit [FiniteDimensional ℂ V] in
/-- The peripheral subspace is invariant under the endomorphism. -/
theorem map_peripheralSubspace_le (f : Module.End ℂ V) :
    Submodule.map f f.peripheralSubspace ≤ f.peripheralSubspace := by
  rw [Submodule.map_le_iff_le_comap, peripheralSubspace]
  refine iSup₂_le fun μ hμ ↦ ?_
  intro x hx
  rw [Submodule.mem_comap]
  exact le_biSup f.maxGenEigenspace hμ
    (f.mapsTo_maxGenEigenspace_of_comm (Commute.refl f) μ hx)

omit [FiniteDimensional ℂ V] in
/-- The non-peripheral subspace is invariant under the endomorphism. -/
theorem map_nonPeripheralSubspace_le (f : Module.End ℂ V) :
    Submodule.map f f.nonPeripheralSubspace ≤ f.nonPeripheralSubspace := by
  rw [Submodule.map_le_iff_le_comap, nonPeripheralSubspace]
  refine iSup₂_le fun μ hμ ↦ ?_
  intro x hx
  rw [Submodule.mem_comap]
  exact le_biSup f.maxGenEigenspace hμ
    (f.mapsTo_maxGenEigenspace_of_comm (Commute.refl f) μ hx)

/-- The peripheral spectral projection commutes with the endomorphism:
`T_φ T = T T_φ`.  On each peripheral spectral subspace `T Pₖ = λₖ Pₖ = Pₖ T`. -/
theorem peripheralProjection_comp (f : Module.End ℂ V) :
    f.peripheralProjection ∘ₗ f = f ∘ₗ f.peripheralProjection := by
  ext x
  have h1 : f (f.peripheralProjection x) ∈ f.peripheralSubspace :=
    f.map_peripheralSubspace_le
      (Submodule.mem_map_of_mem (f.peripheralProjection_apply_mem x))
  have h2 : f (x - f.peripheralProjection x) ∈ f.nonPeripheralSubspace :=
    f.map_nonPeripheralSubspace_le
      (Submodule.mem_map_of_mem (f.sub_peripheralProjection_mem x))
  have hdecomp : f x = f (f.peripheralProjection x) +
      f (x - f.peripheralProjection x) := by
    rw [← map_add, add_sub_cancel]
  simp only [LinearMap.comp_apply]
  rw [hdecomp, map_add, f.peripheralProjection_apply_of_mem h1,
    f.peripheralProjection_apply_eq_zero_iff.mpr h2, add_zero]

/-- The peripheral spectral projection commutes with the endomorphism,
`Commute` form. -/
theorem commute_peripheralProjection (f : Module.End ℂ V) :
    Commute f.peripheralProjection f := by
  simpa only [Commute, SemiconjBy, Module.End.mul_eq_comp]
    using f.peripheralProjection_comp

/-- The peripheral spectral projection commutes with every power of the
endomorphism. -/
theorem commute_peripheralProjection_pow (f : Module.End ℂ V) (n : ℕ) :
    Commute f.peripheralProjection (f ^ n) :=
  f.commute_peripheralProjection.pow_right n

/-! ### The phase-weighted peripheral spectral map `T_φ'` -/

/-- The **phase-weighted peripheral spectral map** `T_φ' := T ∘ T_φ` of Wolf
Equation (6.13).  Since `T_φ` projects onto the peripheral spectral subspace,
on each peripheral eigenspace of eigenvalue `λ` this map acts as `λ • id`,
while it vanishes on the non-peripheral subspace; it is therefore
`Σ_{k:|λₖ|=1} λₖ Pₖ` of the spectral decomposition.  The identity
`T_φ' = T T_φ` of Wolf Proposition 6.3(ii) holds by construction.

Source: Wolf, Equation (6.13) and Proposition 6.3(ii); local source
`Notes/WolfNoteTexSource/ch06_spectral_properties.tex`, lines 213--256. -/
noncomputable def peripheralWeightedProjection (f : Module.End ℂ V) : Module.End ℂ V :=
  f ∘ₗ f.peripheralProjection

/-- **Wolf Proposition 6.3(ii)**: `T_φ' = T T_φ`. -/
theorem peripheralWeightedProjection_eq_comp (f : Module.End ℂ V) :
    f.peripheralWeightedProjection = f ∘ₗ f.peripheralProjection := rfl

/-- The commuted form of Wolf Proposition 6.3(ii): `T_φ' = T_φ T`. -/
theorem peripheralWeightedProjection_eq_peripheralProjection_comp (f : Module.End ℂ V) :
    f.peripheralWeightedProjection = f.peripheralProjection ∘ₗ f := by
  rw [peripheralWeightedProjection, ← f.peripheralProjection_comp]

/-- The absorption identity `T_φ T_φ' = T_φ'`. -/
theorem peripheralProjection_comp_peripheralWeightedProjection (f : Module.End ℂ V) :
    f.peripheralProjection ∘ₗ f.peripheralWeightedProjection =
      f.peripheralWeightedProjection := by
  ext x
  rw [LinearMap.comp_apply, peripheralWeightedProjection, LinearMap.comp_apply,
    f.peripheralProjection_apply_of_mem (f.map_peripheralSubspace_le
      (Submodule.mem_map_of_mem (f.peripheralProjection_apply_mem x)))]

/-- The absorption identity `T_φ' T_φ = T_φ'`. -/
theorem peripheralWeightedProjection_comp_peripheralProjection (f : Module.End ℂ V) :
    f.peripheralWeightedProjection ∘ₗ f.peripheralProjection =
      f.peripheralWeightedProjection := by
  ext x
  simp only [LinearMap.comp_apply, peripheralWeightedProjection, LinearMap.comp_apply,
    peripheralProjection_apply_peripheralProjection]

/-- The peripheral spectral projection fixes peripheral generalized
eigenvectors. -/
theorem peripheralProjection_apply_of_mem_maxGenEigenspace (f : Module.End ℂ V) {μ : ℂ}
    (heig : f.HasEigenvalue μ) (hμ : ‖μ‖ = 1) {x : V} (hx : x ∈ f.maxGenEigenspace μ) :
    f.peripheralProjection x = x :=
  f.peripheralProjection_apply_of_mem
    (le_biSup f.maxGenEigenspace (⟨heig, hμ⟩ : μ ∈ peripheralEigenvalues f) hx)

/-- The peripheral spectral projection fixes peripheral eigenvectors. -/
theorem peripheralProjection_apply_of_mem_eigenspace (f : Module.End ℂ V) {μ : ℂ}
    (heig : f.HasEigenvalue μ) (hμ : ‖μ‖ = 1) {x : V} (hx : x ∈ f.eigenspace μ) :
    f.peripheralProjection x = x :=
  f.peripheralProjection_apply_of_mem_maxGenEigenspace heig hμ
    (Module.End.eigenspace_le_maxGenEigenspace hx)

/-- **Wolf Equation (6.13)**: on the peripheral `μ`-eigenspace, the
phase-weighted map `T_φ'` acts as `μ • id`. -/
theorem peripheralWeightedProjection_apply_of_mem_eigenspace (f : Module.End ℂ V) {μ : ℂ}
    (heig : f.HasEigenvalue μ) (hμ : ‖μ‖ = 1) {x : V} (hx : x ∈ f.eigenspace μ) :
    f.peripheralWeightedProjection x = μ • x := by
  rw [peripheralWeightedProjection, LinearMap.comp_apply,
    f.peripheralProjection_apply_of_mem_eigenspace heig hμ hx,
    (f.mem_eigenspace_iff).mp hx]

/-- **Wolf Equation (6.13)**, continued: the phase-weighted map `T_φ'`
vanishes on the non-peripheral spectral subspace. -/
theorem peripheralWeightedProjection_apply_of_mem_nonPeripheralSubspace (f : Module.End ℂ V)
    {x : V} (hx : x ∈ f.nonPeripheralSubspace) :
    f.peripheralWeightedProjection x = 0 := by
  rw [peripheralWeightedProjection, LinearMap.comp_apply,
    f.peripheralProjection_apply_eq_zero_iff.mpr hx, map_zero]

end Module.End

/-! ### Positive trace-preserving maps: trivial peripheral Jordan blocks -/

namespace IsPositiveMap

variable {D : ℕ} [NeZero D]
  {T : Module.End ℂ (Matrix (Fin D) (Fin D) ℂ)}

/-- **Wolf Proposition 6.2, subspace form**: for a positive trace-preserving
map, the maximal generalized eigenspace of a peripheral eigenvalue equals the
eigenspace (peripheral Jordan blocks are one-dimensional).

Source: Wolf, Proposition 6.2; local source
`Notes/WolfNoteTexSource/ch06_spectral_properties.tex`, lines 181--224. -/
theorem maxGenEigenspace_eq_eigenspace_of_norm_eq_one
    (hPos : IsPositiveMap T) (hTP : IsTracePreservingMap T) {μ : ℂ} (hμ : ‖μ‖ = 1) :
    T.maxGenEigenspace μ = T.eigenspace μ := by
  apply le_antisymm _ Module.End.eigenspace_le_maxGenEigenspace
  intro X hX
  obtain ⟨k, hk⟩ := (T.mem_maxGenEigenspace μ X).mp hX
  have h := hPos.peripheral_Jordan_trivial_of_tracePreserving hTP μ hμ k X hk
  rw [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply] at h
  exact Module.End.mem_eigenspace_iff.mpr (sub_eq_zero.mp h)

/-- **Wolf Equation (6.65) for positive trace-preserving maps**: the
peripheral spectral subspace is the span of the peripheral eigenspaces. -/
theorem peripheralSubspace_eq_iSup_eigenspace
    (hPos : IsPositiveMap T) (hTP : IsTracePreservingMap T) :
    T.peripheralSubspace = ⨆ μ ∈ peripheralEigenvalues T, T.eigenspace μ := by
  rw [Module.End.peripheralSubspace]
  exact biSup_congr fun μ hμ ↦ hPos.maxGenEigenspace_eq_eigenspace_of_norm_eq_one hTP hμ.2

end IsPositiveMap
