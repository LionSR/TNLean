/-
Copyright (c) 2025 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.ParentHamiltonian.Basic
import TNLean.MPS.ParentHamiltonian.CyclicWindow
import TNLean.Algebra.ScalarCommutant

/-!
# Unique ground state for injective MPS parent Hamiltonians

## Scouting report for Issue #386

After reading `UniqueGroundState.lean`, `CyclicWindow.lean`,
`IntersectionProperty.lean`, `GroundSpace.lean`, and `Martingale.lean`,
the current infrastructure appears to support only the following pieces:

1. `chainGroundSpace A L N` is literally the intersection of the cyclic-window
   pullbacks of `groundSpace A L`.
2. `mpv_mem_chainGroundSpace` already gives the easy inclusion
   `mpvSubmodule A N ≤ chainGroundSpace A L N`.
3. `contiguous_mem_groundSpace` plus the non-wrapping cyclic/contiguous
   comparison control the open-chain part of the argument.

What is still missing for the periodic uniqueness step is a *compatibility*
statement relating the witness matrices coming from different cyclic windows.
`groundSpace_intersection` only regrows adjacent non-wrapping windows; it does
not identify the boundary matrix obtained from one window with the boundary
matrix obtained from a wrapping window. That missing relation is exactly what
one needs to derive the commutation constraint `A i * X = X * A i`, and only
after that can `ScalarCommutant.isScalar_of_commute_span_eq_top` collapse
`X` to a scalar.

So the present gap is not the scalar-commutant step itself; it is the absence
of a periodic boundary-compatibility lemma connecting the cyclic-window
conditions in `chainGroundSpace` to a single global boundary matrix.

For an injective MPS tensor `A` on a periodic chain, the expected parent-Hamiltonian
ground space is spanned by the MPV state
`σ ↦ tr(A^{σ₀} ⋯ A^{σ_{N-1}})`.

## Overview

The proof combines the intersection property from `IntersectionProperty.lean`
with the periodic boundary condition:

1. **Open chain**: By iterated application of the intersection property,
   any state satisfying all local ground-space conditions has the form
   `ψ(σ) = tr(A^σ · X)` for some boundary matrix `X ∈ M_D(ℂ)`.
   This yields a `D²`-dimensional space.

2. **Periodic chain**: The wrapping window condition (connecting the last and
   first sites) constrains `X`. For injective `A`, the matrices `{A^i}` span
   `M_D(ℂ)`, so the commutation condition forces `X ∝ I`, yielding a
   one-dimensional ground space spanned by the MPV.

## Main results

* `MPSTensor.mpvSubmodule` — the subspace spanned by the MPV
* `MPSTensor.mpv_mem_groundSpace` — the MPV lies in the ground space
* `MPSTensor.chainGroundSpace` — the periodic-chain ground space as intersection
  of cyclic window ground submodules
* `MPSTensor.groundSpace_unique_periodic` — uniqueness on the periodic chain
* `MPSTensor.parentHamiltonian_unique_gs_injective` — uniqueness for `2L₀` sites
* `MPSTensor.parentHamiltonian_unique_gs_normal` — optimal uniqueness for `L₀+1` sites

## References

* [CPGSV21] arXiv:2011.12127, lines 2013–2094 (full argument)
* [FNW92] Sections 3–4
* [PGVWC07] arXiv:quant-ph/0608197, Sections 5–6
-/

open scoped Matrix BigOperators

namespace MPSTensor

variable {d D : ℕ}

/-! ### The MPV submodule -/

/-- The submodule spanned by the MPV state.

On the periodic chain, the MPV state is `σ ↦ tr(A^{σ₀} ⋯ A^{σ_{N-1}})`,
which corresponds to the ground-space map applied to the identity:
`mpv A = groundSpaceMap A N 1`. -/
noncomputable def mpvSubmodule (A : MPSTensor d D) (N : ℕ) :
    Submodule ℂ (NSiteSpace d N) :=
  Submodule.span ℂ {mpv A}

/-- The MPV is the ground-space map applied to the identity matrix. -/
theorem mpv_eq_groundSpaceMap_one (A : MPSTensor d D) (N : ℕ) :
    (mpv A : NSiteSpace d N) = groundSpaceMap A N 1 := by
  ext σ
  simp [mpv, coeff, groundSpaceMap_apply]

/-- The MPV state lies in the ground space `G_N(A)` for any `N`. -/
theorem mpv_mem_groundSpace (A : MPSTensor d D) (N : ℕ) :
    (mpv A : NSiteSpace d N) ∈ groundSpace A N := by
  rw [groundSpace, LinearMap.mem_range]
  exact ⟨1, by ext σ; simp [groundSpaceMap_apply, mpv, coeff]⟩

/-! ### Periodic chain ground space

On a periodic chain of `N` sites, the ground space of the parent Hamiltonian
is the set of states whose restriction to every cyclic window of `L` consecutive
sites lies in `G_L(A)`.

The full periodic-chain window restriction still depends on the chain-level
embedding API. We therefore expose only the chain ground-space interface for
now, and will define it from local window constraints once the operator
formalization lands. -/

-- TODO(parent-hamiltonian): define `chainGroundSpace` as the intersection of
-- cyclic window ground submodules once the periodic window embedding API lands.

/-- The periodic chain ground space: the set of states `ψ` on `N` sites such
that every cyclic window of `L` consecutive sites restricts into `G_L(A)`.

When `N = 0` or `L > N`, we return `⊤` as a degenerate convention. -/
noncomputable def chainGroundSpace (A : MPSTensor d D) (L N : ℕ) :
    Submodule ℂ (NSiteSpace d N) :=
  if hN : 0 < N ∧ L ≤ N then
    ⨅ (i : Fin N) (τ : Fin N → Fin d),
      (groundSpace A L).comap (cyclicRestrictₗ hN.1 L i τ)
  else ⊤

/-- The MPV state is in the chain ground space.

The proof uses trace cyclicity: for each cyclic window at position `i`, the
restriction of the MPV to that window equals `groundSpaceMap A L X_τ` where
`X_τ` is the product of `A`-matrices at outside positions.

**Status**: requires cyclic list decomposition and trace cyclicity argument. -/
theorem mpv_mem_chainGroundSpace (A : MPSTensor d D) (L N : ℕ)
    (hN : 0 < N) (hLN : L ≤ N) :
    (mpv A : NSiteSpace d N) ∈ chainGroundSpace A L N := by
  rw [chainGroundSpace, dif_pos ⟨hN, hLN⟩]
  simp only [Submodule.mem_iInf, Submodule.mem_comap]
  intro i τ
  simpa [cyclicRestrictₗ_apply, cyclicCfg, replaceWindow] using
    mpv_window_mem_groundSpace A L N hLN i τ

/-! ### Unique ground state -/

/-- A submodule has a unique ground state (up to scalar) if its dimension is exactly 1. -/
def HasUniqueGroundState {V : Type*} [AddCommGroup V] [Module ℂ V]
    (S : Submodule ℂ V) : Prop :=
  Module.finrank ℂ S = 1

/-- Characterization: a unique ground state is generated by a single nonzero vector. -/
theorem hasUniqueGroundState_iff_proportional {V : Type*} [AddCommGroup V] [Module ℂ V]
    {S : Submodule ℂ V} [FiniteDimensional ℂ S] :
    HasUniqueGroundState S ↔
      ∃ ψ₀ : S, ψ₀ ≠ 0 ∧ ∀ ψ : S, ∃ c : ℂ, ψ = c • ψ₀ := by
  constructor
  · intro hS
    have hpos : 0 < Module.finrank ℂ S := by
      rw [hS]
      norm_num
    obtain ⟨ψ₀, hψ₀⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hpos
    refine ⟨ψ₀, hψ₀, ?_⟩
    have hgen : ∀ ψ : S, ∃ c : ℂ, c • ψ₀ = ψ :=
      (finrank_eq_one_iff_of_nonzero' ψ₀ hψ₀).mp hS
    intro ψ
    obtain ⟨c, hc⟩ := hgen ψ
    exact ⟨c, hc.symm⟩
  · rintro ⟨ψ₀, hψ₀, hgen⟩
    exact (finrank_eq_one_iff_of_nonzero' ψ₀ hψ₀).2 fun ψ => by
      obtain ⟨c, hc⟩ := hgen ψ
      exact ⟨c, hc.symm⟩

/-! ### Uniqueness theorems -/

/-- On a periodic chain, the injective parent-Hamiltonian ground space should
coincide with the span of the MPV. -/
-- TODO(parent-hamiltonian): derive this from the cyclic-window definition of
-- `chainGroundSpace` and the proved open-chain intersection property.
theorem chainGroundSpace_eq_mpvSubmodule {A : MPSTensor d D} [NeZero D]
    (hA : IsInjective A) {L N : ℕ} (hN : 2 ≤ N) (hL : 1 < L) (hLN : L ≤ N) :
    chainGroundSpace A L N = mpvSubmodule A N := by
  have hN0 : 0 < N := by omega
  have hd : d ≠ 0 := by
    intro hd0
    have hrange : Set.range A = (∅ : Set (Matrix (Fin D) (Fin D) ℂ)) := by
      ext M
      simp [hd0]
    have hspan : (⊥ : Submodule ℂ (Matrix (Fin D) (Fin D) ℂ)) = ⊤ := by
      simpa [IsInjective, hrange] using hA
    have h10 : (1 : Matrix (Fin D) (Fin D) ℂ) = 0 := by
      have hmem : (1 : Matrix (Fin D) (Fin D) ℂ) ∈
          (⊥ : Submodule ℂ (Matrix (Fin D) (Fin D) ℂ)) := by
        rw [hspan]
        exact Submodule.mem_top
      simpa using hmem
    exact one_ne_zero h10
  haveI : NeZero d := ⟨hd⟩
  apply le_antisymm
  · intro ψ hψ
    rw [chainGroundSpace, dif_pos ⟨hN0, hLN⟩] at hψ
    simp only [Submodule.mem_iInf, Submodule.mem_comap] at hψ
    have hopen : ψ ∈ groundSpace A N := by
      apply contiguous_mem_groundSpace hA hL hLN
      intro s hs τ
      have hcyc :
          cyclicRestrictₗ hN0 L ⟨s, by omega⟩ τ ψ ∈ groundSpace A L :=
        hψ ⟨s, by omega⟩ τ
      rwa [cyclicRestrictₗ_eq_contiguousRestrictₗ hN0 hLN
        (i := ⟨s, by omega⟩) hs τ ψ] at hcyc
    rw [groundSpace, LinearMap.mem_range] at hopen
    obtain ⟨X, hX⟩ := hopen
    have hψX : ψ = groundSpaceMap A N X := hX.symm
    have hrot_window :
        ∀ (s : ℕ) (hs : s + L ≤ N) (τ : Fin N → Fin d),
          contiguousRestrictₗ s L hs τ (rotateLeftState hN0 ψ) ∈ groundSpace A L := by
      intro s hs τ
      have hs1 : s + 1 < N := by omega
      have hcyc :
          cyclicRestrictₗ hN0 L ⟨s + 1, hs1⟩ (rotateLeftCfg hN0 τ) ψ ∈ groundSpace A L :=
        hψ ⟨s + 1, hs1⟩ (rotateLeftCfg hN0 τ)
      rwa [← contiguousRestrictₗ_rotateLeftState_eq_cyclicRestrictₗ hN0
        (show 0 < L by omega) s hs τ ψ] at hcyc
    have hrot : rotateLeftState hN0 ψ ∈ groundSpace A N :=
      contiguous_mem_groundSpace hA hL hLN hrot_window
    rw [groundSpace, LinearMap.mem_range] at hrot
    obtain ⟨Y, hY⟩ := hrot
    have hrotY : rotateLeftState hN0 ψ = groundSpaceMap A N Y := hY.symm
    have hCompat : ∀ i : Fin d, Y * A i = A i * X := by
      intro i
      apply groundSpaceMap_injective hA (by omega : 0 < N - 1)
      ext σ
      calc
        groundSpaceMap A (N - 1) (Y * A i) σ
            = restrictFirst (rotateLeftState hN0 ψ) i σ := by
                rw [hrotY]
                simp only [restrictFirst_apply, groundSpaceMap_apply, evalWord_ofFn_cons]
                simpa [Matrix.mul_assoc] using
                  Matrix.trace_mul_cycle' (A i) (evalWord A (List.ofFn σ)) Y
        _ = groundSpaceMap A (N - 1) (A i * X) σ := by
              rw [rotateLeftState_apply, hψX, rotateLeftCfg_cons]
              simp [restrictFirst_apply, groundSpaceMap_apply, evalWord_ofFn_snoc,
                Matrix.mul_assoc]
    have hYX_span :
        ∀ M ∈ Submodule.span ℂ (Set.range A), Y * M = M * X := by
      intro M hM
      induction hM using Submodule.span_induction with
      | mem M hM =>
          rcases hM with ⟨i, rfl⟩
          exact hCompat i
      | zero => simp
      | add M₁ M₂ _ _ h₁ h₂ =>
          rw [Matrix.mul_add, add_mul, h₁, h₂]
      | smul c M _ hM =>
          simp [Algebra.mul_smul_comm, Algebra.smul_mul_assoc, hM]
    have hYX : Y = X := by
      have hone : Y * (1 : Matrix (Fin D) (Fin D) ℂ) = (1 : Matrix (Fin D) (Fin D) ℂ) * X :=
        hYX_span 1 (hA.span_eq_top ▸ Submodule.mem_top)
      simpa using hone
    have hcomm : ∀ i : Fin d, X * A i = A i * X := by
      intro i
      simpa [hYX] using hCompat i
    obtain ⟨c, hXscalar⟩ := Matrix.isScalar_of_commute_span_eq_top
      (Z := X) hA.span_eq_top (fun M hM => by
        rcases hM with ⟨i, rfl⟩
        exact hcomm i)
    have hXsmul : X = c • (1 : Matrix (Fin D) (Fin D) ℂ) := by
      rw [hXscalar]
      ext i j
      by_cases hij : i = j
      · subst hij
        simp [Matrix.scalar_apply]
      · simp [Matrix.scalar_apply, hij]
    have hψ_eq : ψ = c • (mpv A : NSiteSpace d N) := by
      calc
        ψ = groundSpaceMap A N X := hψX
        _ = groundSpaceMap A N (c • (1 : Matrix (Fin D) (Fin D) ℂ)) := by rw [hXsmul]
        _ = c • groundSpaceMap A N 1 := by simp
        _ = c • (mpv A : NSiteSpace d N) := by
              simp [mpv_eq_groundSpaceMap_one]
    exact Submodule.mem_span_singleton.mpr ⟨c, hψ_eq.symm⟩
  · rw [mpvSubmodule]
    refine Submodule.span_le.mpr ?_
    intro ψ hψ
    rcases hψ with rfl
    exact mpv_mem_chainGroundSpace A L N hN0 hLN

/-- **Unique ground state on the periodic chain** for injective MPS.

For an injective tensor `A` on a periodic chain of `N ≥ 2` sites, the chain ground
space is one-dimensional, spanned by the MPV.

The proof uses the intersection property iteratively:
1. From the intersection property, any state in the chain ground space has the form
   `ψ(σ) = tr(A^σ · X)` for some `X ∈ M_D(ℂ)`.
2. The wrapping window condition (window crossing the periodic boundary) constrains
   `X` to commute with all `A^i`.
3. For injective `A`, the center of `span{A^i} = M_D(ℂ)` consists only of scalars,
   so `X = c · I` and `ψ = c · mpv A`.

**Status**: The proof requires the periodic window condition to be fully formalized.
The intersection property (`groundSpace_intersection`) provides the key "invert-and-regrow"
step; the remaining ingredient is the periodic boundary argument. -/
-- TODO(parent-hamiltonian): finish after the periodic window embedding API
-- makes the wrapping-window condition available in `chainGroundSpace`.
theorem groundSpace_unique_periodic {A : MPSTensor d D} [NeZero D] (hA : IsInjective A)
    {L N : ℕ} (hN : 2 ≤ N) (hL : 1 < L) (hLN : L ≤ N) :
    HasUniqueGroundState (chainGroundSpace A L N) := by
  rw [HasUniqueGroundState, chainGroundSpace_eq_mpvSubmodule hA hN hL hLN]
  have hmpv : (mpv A : NSiteSpace d N) ≠ 0 := by
    intro hzero
    have hEq :
        groundSpaceMap A N (1 : Matrix (Fin D) (Fin D) ℂ) =
          groundSpaceMap A N (0 : Matrix (Fin D) (Fin D) ℂ) := by
      simpa [mpv_eq_groundSpaceMap_one A N] using hzero
    have h10 : (1 : Matrix (Fin D) (Fin D) ℂ) = 0 :=
      (groundSpaceMap_injective hA (by omega : 0 < N)) hEq
    exact one_ne_zero h10
  simpa [mpvSubmodule] using finrank_span_singleton (K := ℂ) hmpv

/-- **Unique ground state for `N`-block-injective tensors on `2N` sites**.

If `A` is `L₀`-block-injective (i.e., the blocked tensor `A^{[L₀]}` is injective),
with a nontrivial block length `L₀ > 0`, then the parent Hamiltonian with
interaction range `2L₀` on the periodic chain has a unique ground state.

**Status**: Depends on `groundSpace_unique_periodic` and the connection between
`chainGroundSpace` and `LinearMap.ker (parentHamiltonian A (2 * L₀) N)`, which
will be established when the operator API lands. -/
-- TODO(parent-hamiltonian): reduce this to `groundSpace_unique_periodic`
-- after connecting `chainGroundSpace` with the parent-Hamiltonian kernel.
theorem parentHamiltonian_unique_gs_injective {A : MPSTensor d D} [NeZero D]
    {L₀ : ℕ} (hA : IsNBlkInjective A L₀) (hL₀ : 0 < L₀)
    {N : ℕ} (hN : 2 * L₀ ≤ N) :
    HasUniqueGroundState (chainGroundSpace A (2 * L₀) N) := by
  sorry

/-- **Optimal unique ground state for normal tensors on `L₀ + 1` sites**.

If `A` is normal (hence `L₀`-block-injective for some `L₀`) and the blocked tensor
is in normal form with `L₀ > 0`, the interaction range can be reduced from `2L₀`
to `L₀ + 1` using the structure theory of normal MPS.

**Status**: Requires the normal-form analysis from the canonical form theory in
addition to the periodic boundary argument. -/
-- TODO(parent-hamiltonian): combine the normal-form range reduction with the
-- periodic uniqueness theorem once that theorem is formalized.
theorem parentHamiltonian_unique_gs_normal {A : MPSTensor d D} [NeZero D]
    {L₀ : ℕ} (hA : IsNormal A) (hInj : IsNBlkInjective A L₀) (hL₀ : 0 < L₀)
    {N : ℕ} (hN : L₀ + 1 ≤ N) :
    HasUniqueGroundState (chainGroundSpace A (L₀ + 1) N) := by
  sorry

end MPSTensor
