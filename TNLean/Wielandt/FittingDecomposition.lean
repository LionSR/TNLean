/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.LinearAlgebra.Eigenspace.Zero
import Mathlib.RingTheory.Nilpotent.Basic
import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-!
# Fitting Decomposition for Linear Endomorphisms

This file establishes a "Fitting-like" decomposition of a linear endomorphism
into nilpotent and invertible parts, as needed for the Quantum Wielandt bound
proof (arXiv:0909.5347, Lemma 2(b)).

## Mathematical background

The paper (arXiv:0909.5347) appeals to the Jordan Normal Form of a matrix `A₁`
to split `ℂ^D = V₀ ⊕ V_nonzero` where:
- `V₀` is the generalized eigenspace for eigenvalue 0 (the "nilpotent part")
- `V_nonzero` is the direct sum of generalized eigenspaces for nonzero eigenvalues
  (the "invertible part")
- `A₁` is nilpotent on `V₀` with nilpotency index ≤ dim(V₀) ≤ D
- `A₁` is invertible on `V_nonzero`

## Our approach

We deviate from the paper by using Mathlib's generalized eigenspace infrastructure
instead of formalizing the full Jordan Normal Form. This avoids a massive
formalization effort (JNF is not in Mathlib as of Feb 2026) while giving us
exactly the decomposition we need.

The key Mathlib results we build on:
1. `Module.End.iSup_maxGenEigenspace_eq_top` — generalized eigenspaces span `V`
2. `Module.End.independent_maxGenEigenspace` — they are linearly independent
3. `Module.End.isNilpotent_restrict_maxGenEigenspace_sub_algebraMap` —
   `(f - μ·1)` restricted to `maxGenEigenspace μ` is nilpotent
4. `IsNilpotent.isUnit_add_left_of_commute` — unit + nilpotent = unit

## Main results

- `isNilpotent_restrict_maxGenEigenspace_zero` : f is nilpotent on V₀
- `isUnit_restrict_maxGenEigenspace_of_ne_zero` : f is invertible on each
  nonzero generalized eigenspace
- `nilpotent_pow_eq_zero_of_finrank` : a nilpotent f satisfies f^(dim V) = 0
- `FittingDecomposition` : the combined decomposition structure

## References

* [Sanz, Pérez-García, Wolf, Cirac, *A quantum version of Wielandt's inequality*]
  (arXiv:0909.5347), Lemma 2(b), paragraph starting
  "Let us use the Jordan normal form..."
-/

namespace Wielandt

open Module

/-! ### Auxiliary: f maps its own generalized eigenspaces to themselves -/

/-- f maps its own generalized eigenspace for eigenvalue μ to itself.
This follows from `mapsTo_maxGenEigenspace_of_comm` with `Commute.refl`. -/
theorem mapsTo_maxGenEigenspace_self
    {K : Type*} {V : Type*}
    [CommRing K] [AddCommGroup V] [Module K V]
    (f : End K V) (μ : K) :
    Set.MapsTo f ↑(f.maxGenEigenspace μ) ↑(f.maxGenEigenspace μ) :=
  End.mapsTo_maxGenEigenspace_of_comm (Commute.refl f) μ

/-! ### Part 1: f is nilpotent on the zero generalized eigenspace -/

/-- **f is nilpotent on the generalized eigenspace for eigenvalue 0.**

On the generalized eigenspace for eigenvalue 0, the operator `f` itself is nilpotent.
This follows from `isNilpotent_restrict_maxGenEigenspace_sub_algebraMap`
with `μ = 0`, since `f - 0·1 = f`.

This corresponds to the "nilpotent block" in the Jordan decomposition used
in arXiv:0909.5347, Lemma 2(b). -/
theorem isNilpotent_restrict_maxGenEigenspace_zero
    {K : Type*} {V : Type*}
    [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (f : End K V) :
    IsNilpotent (f.restrict (mapsTo_maxGenEigenspace_self f 0)) := by
  -- Get nilpotency of (f - 0·1) on the zero eigenspace
  have h := End.isNilpotent_restrict_maxGenEigenspace_sub_algebraMap f 0
  simp only [map_zero, sub_zero] at h
  -- Extract the power and prove equality by ext
  obtain ⟨k, hk⟩ := h
  exact ⟨k, by ext ⟨v, hv⟩; exact congr_arg Subtype.val (LinearMap.congr_fun hk ⟨v, hv⟩)⟩

/-! ### Part 2: f is invertible on nonzero generalized eigenspaces -/

/-- **f is invertible on a generalized eigenspace for a nonzero eigenvalue.**

On the generalized eigenspace for eigenvalue `μ ≠ 0`, the operator `f` is invertible
(i.e., `IsUnit` as a `Module.End`). The proof decomposes `f = μ·1 + (f - μ·1)` where:
- `μ·1` is a unit (since `μ ≠ 0` in a field)
- `(f - μ·1)` is nilpotent (by `isNilpotent_restrict_maxGenEigenspace_sub_algebraMap`)
- They commute (since `μ·1` is central)

By `IsNilpotent.isUnit_add_left_of_commute`, their sum `f` is a unit.

This corresponds to the "invertible block" in arXiv:0909.5347, Lemma 2(b).
The paper states: "Hence, A₁ is invertible on [the nonzero eigenspace]." -/
theorem isUnit_restrict_maxGenEigenspace_of_ne_zero
    {K : Type*} {V : Type*}
    [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (f : End K V) (μ : K) (hμ : μ ≠ 0) :
    IsUnit (f.restrict (mapsTo_maxGenEigenspace_self f μ)) := by
  set W := f.maxGenEigenspace μ
  set hf_maps : Set.MapsTo f ↑W ↑W := mapsTo_maxGenEigenspace_self f μ
  -- Abbreviation for the scalar endomorphism
  set a := algebraMap K (End K V) μ
  set N := f - a
  -- MapsTo proofs
  have ha_maps : Set.MapsTo a ↑W ↑W := fun x hx => by
    change (algebraMap K (End K V) μ) x ∈ W
    rw [Module.algebraMap_end_eq_smul_id, LinearMap.smul_apply, LinearMap.id_apply]
    exact W.smul_mem μ hx
  -- Use the default MapsTo from Mathlib for N
  have hN_maps_default :=
    End.mapsTo_maxGenEigenspace_of_comm (Algebra.mul_sub_algebraMap_commutes f μ) μ
  -- Our own MapsTo for N (same proof essentially, but might be syntactically different)
  have hN_maps : Set.MapsTo N ↑W ↑W := fun x hx => by
    change (f - a) x ∈ W
    rw [LinearMap.sub_apply]
    exact W.sub_mem (hf_maps hx) (ha_maps hx)
  -- Step 1: N restricted to W is nilpotent (from Mathlib)
  have hnil : IsNilpotent (N.restrict hN_maps) := by
    obtain ⟨k, hk⟩ := End.isNilpotent_restrict_maxGenEigenspace_sub_algebraMap f μ
    exact ⟨k, by ext ⟨v, hv⟩; exact congr_arg Subtype.val (LinearMap.congr_fun hk ⟨v, hv⟩)⟩
  -- Step 2: a restricted to W is a unit
  have ha_apply : ∀ (v : V), a v = μ • v := fun v => by
    change (algebraMap K (End K V) μ) v = μ • v
    rw [Module.algebraMap_end_eq_smul_id, LinearMap.smul_apply, LinearMap.id_apply]
  have ha_restrict_eq : a.restrict ha_maps = algebraMap K (End K ↥W) μ := by
    ext ⟨v, hv⟩
    simp only [ha_apply, LinearMap.restrict_coe_apply,
      Module.algebraMap_end_eq_smul_id, LinearMap.smul_apply, LinearMap.id_apply,
      SetLike.val_smul]
  have ha_unit : IsUnit (a.restrict ha_maps) := by
    rw [ha_restrict_eq]
    exact (Ne.isUnit hμ).map (algebraMap K (End K ↥W))
  -- Step 3: They commute (a = algebraMap μ commutes with everything)
  have hcomm : Commute (N.restrict hN_maps) (a.restrict ha_maps) := by
    rw [ha_restrict_eq, Algebra.algebraMap_eq_smul_one]
    exact Commute.smul_right (Commute.one_right _) μ
  -- Step 4: f.restrict = a.restrict + N.restrict
  have hsum : f.restrict hf_maps = a.restrict ha_maps + N.restrict hN_maps := by
    ext ⟨v, hv⟩
    simp only [LinearMap.restrict_apply, LinearMap.add_apply]
    change f v = a v + (f - a) v
    simp [LinearMap.sub_apply]
  -- Step 5: Conclude: unit + nilpotent = unit
  rw [hsum]
  exact hnil.isUnit_add_left_of_commute ha_unit hcomm

/-! ### Part 3: Nilpotency index bound -/

open Polynomial in
/-- **A nilpotent endomorphism on a finite-dimensional space satisfies f^(dim V) = 0.**

If `f` is nilpotent, its characteristic polynomial equals `X^n` where `n = dim V`
(by `IsNilpotent.charpoly_eq_X_pow_finrank`). By Cayley-Hamilton
(`LinearMap.aeval_self_charpoly`), `f^n = 0`.

This gives the nilpotency index bound: the nilpotent part of the Fitting
decomposition satisfies `f^D = 0` on the zero generalized eigenspace,
where `D ≤ dim V`. This is used in arXiv:0909.5347, Lemma 2(b) to bound
the number of applications of A₁ needed to annihilate the nilpotent block. -/
theorem nilpotent_pow_eq_zero_of_finrank
    {K : Type*} {V : Type*}
    [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (f : End K V) (hf : IsNilpotent f) :
    f ^ (finrank K V) = 0 := by
  have hchar : f.charpoly = X ^ finrank K V :=
    hf.charpoly_eq_X_pow_finrank
  have hCH := LinearMap.aeval_self_charpoly f
  rw [hchar, map_pow, aeval_X] at hCH
  exact hCH

/-! ### Part 4: Generalized eigenspace decomposition -/

/-- **Generalized eigenspaces span the whole space over an algebraically closed field.**

This is a direct restatement of Mathlib's `Module.End.iSup_maxGenEigenspace_eq_top`
for convenient use in the Fitting decomposition context.

In the context of arXiv:0909.5347, this corresponds to the fact that every
matrix over ℂ can be put into Jordan normal form, which in particular implies
that generalized eigenspaces span the whole space. -/
theorem iSup_maxGenEigenspace_eq_top
    {K : Type*} {V : Type*}
    [Field K] [AddCommGroup V] [Module K V]
    [IsAlgClosed K] [FiniteDimensional K V]
    (f : End K V) :
    ⨆ μ, f.maxGenEigenspace μ = ⊤ :=
  End.iSup_maxGenEigenspace_eq_top f

/-- **Generalized eigenspaces are linearly independent.**

This is a direct restatement of Mathlib's `Module.End.independent_maxGenEigenspace`. -/
theorem independent_maxGenEigenspace
    {K : Type*} {V : Type*}
    [Field K] [AddCommGroup V] [Module K V]
    (f : End K V) :
    iSupIndep f.maxGenEigenspace :=
  End.independent_maxGenEigenspace f

/-! ### Part 5: Fitting decomposition structure -/

/-- **Fitting decomposition structure.**

Packages the invertible/nilpotent decomposition of a linear endomorphism
needed for Lemma 2(b) of arXiv:0909.5347.

The paper's proof states (paraphrasing): "Let us use the Jordan normal form
of A₁ to split ℂ^D into the subspace where A₁ acts invertibly and the
subspace where A₁ acts nilpotently." We formalize this without full JNF
by using Mathlib's generalized eigenspace decomposition.

## Fields
- `hNilpNilpotent` : f is nilpotent when restricted to the zero gen. eigenspace
- `hInvertible` : for each nonzero eigenvalue μ, f is invertible on
  `maxGenEigenspace f μ`
- `hSpan` : the generalized eigenspaces span all of V
- `hIndep` : the generalized eigenspaces are linearly independent -/
structure FittingDecomposition
    {K : Type*} {V : Type*}
    [Field K] [AddCommGroup V] [Module K V]
    [IsAlgClosed K] [FiniteDimensional K V]
    (f : End K V) : Prop where
  /-- f is nilpotent when restricted to the zero generalized eigenspace. -/
  hNilpNilpotent : IsNilpotent (f.restrict (mapsTo_maxGenEigenspace_self f 0))
  /-- For each nonzero eigenvalue μ, f is invertible on the corresponding
      generalized eigenspace. -/
  hInvertible : ∀ (μ : K), μ ≠ 0 →
    IsUnit (f.restrict (mapsTo_maxGenEigenspace_self f μ))
  /-- The generalized eigenspaces span all of V. -/
  hSpan : ⨆ μ, f.maxGenEigenspace μ = ⊤
  /-- The generalized eigenspaces are linearly independent. -/
  hIndep : iSupIndep f.maxGenEigenspace

/-- **Every endomorphism over an algebraically closed field admits a Fitting decomposition.**

This is the main construction: given any linear endomorphism `f` on a
finite-dimensional vector space over an algebraically closed field, we
produce the Fitting decomposition packaging the nilpotent/invertible split.

In the context of arXiv:0909.5347, this is applied to the Kraus operator `A₁`
which is known to have a nonzero eigenvalue. The decomposition allows the
proof of Lemma 2(b) to proceed by analyzing the invertible and nilpotent
parts separately. -/
theorem fittingDecomposition
    {K : Type*} {V : Type*}
    [Field K] [AddCommGroup V] [Module K V]
    [IsAlgClosed K] [FiniteDimensional K V]
    (f : End K V) : FittingDecomposition f where
  hNilpNilpotent := isNilpotent_restrict_maxGenEigenspace_zero f
  hInvertible μ hμ := isUnit_restrict_maxGenEigenspace_of_ne_zero f μ hμ
  hSpan := iSup_maxGenEigenspace_eq_top f
  hIndep := independent_maxGenEigenspace f

/-- **The nilpotent part of the Fitting decomposition satisfies f^n = 0,
where n = dim(nilpSpace).**

This combines the nilpotency on the zero generalized eigenspace with the
dimension bound from `nilpotent_pow_eq_zero_of_finrank`. -/
theorem nilpotent_pow_eq_zero_on_maxGenEigenspace_zero
    {K : Type*} {V : Type*}
    [Field K] [AddCommGroup V] [Module K V]
    [IsAlgClosed K] [FiniteDimensional K V]
    (f : End K V) :
    (f.restrict (mapsTo_maxGenEigenspace_self f 0)) ^
      (finrank K ↥(f.maxGenEigenspace 0)) = 0 :=
  nilpotent_pow_eq_zero_of_finrank _ (isNilpotent_restrict_maxGenEigenspace_zero f)

/-- **The dimension of the zero generalized eigenspace is at most the dimension of V.**

This provides the coarser bound needed in arXiv:0909.5347 where `D = dim V`
is used as the nilpotency index bound. -/
theorem maxGenEigenspace_zero_finrank_le
    {K : Type*} {V : Type*}
    [Field K] [AddCommGroup V] [Module K V]
    [IsAlgClosed K] [FiniteDimensional K V]
    (f : End K V) :
    finrank K ↥(f.maxGenEigenspace 0) ≤ finrank K V :=
  Submodule.finrank_le (f.maxGenEigenspace 0)

end Wielandt
