/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import TNLean.Algebra.BurnsideTheorem
import TNLean.MPS.CanonicalForm.Reduction
import TNLean.Wielandt.SpanGrowth.CumulativeSpan

import Mathlib.Algebra.Algebra.Subalgebra.Lattice
import Mathlib.RingTheory.Noetherian.Defs

/-!
# Burnside-style Bridge: Irreducibility → Normality

This file reduces the gap between `IsIrreducibleTensor` (no nontrivial invariant
orthogonal projection) and `IsNormal` (word products span `M_D(ℂ)`) to a single,
cleanly stated algebraic theorem: **Burnside's theorem for matrix algebras**.

Burnside's theorem (Jacobson density theorem) is formalized directly in this
project rather than imported from Mathlib.

## Main definitions

* `MPSTensor.algSpan A`: the unital subalgebra `Algebra.adjoin ℂ (Set.range A)`.
* `MPSTensor.IsInvariantSubmodule A W`: `W ≤ (Fin D → ℂ)` is invariant under all `A i`.
* `MPSTensor.IsIrreducibleAction A`: no nontrivial invariant submodule.

## Main results (all sorry-free)

### Part 1: Algebra span and cumulative span

* `algSpan_mem`, `evalWord_mem_algSpan`, `wordSpan_le_algSpan_toSubmodule`,
  `cumulativeSpan_le_algSpan_toSubmodule`: containment lemmas.
* `mul_mem_cumulativeSpan_add`: closure under multiplication (adding lengths).
* `mem_cumulativeSpan_of_mem_algSpan`: every element of `algSpan A` is in some
  `cumulativeSpan A N` (via `Algebra.adjoin_induction`).
* `exists_cumulativeSpan_eq_top_of_algSpan_eq_top`: `algSpan A = ⊤ → ∃ N,
  cumulativeSpan A N = ⊤` (via Noetherian chain stabilization).

### Part 2: Invariant submodule characterization

* `isIrreducibleTensor_of_isIrreducibleAction`: `IsIrreducibleTensor` follows from
  `IsIrreducibleAction` (range of an invariant orthogonal projection is invariant).

### Bridge summary

The complete chain from `IsIrreducibleTensor A` to `∃ N, cumulativeSpan A N = ⊤`:

1. `IsIrreducibleTensor A` → `IsIrreducibleAction A` (proved in `IrreducibleTensorAction.lean`)
2. `IsIrreducibleAction A` → `algSpan A = ⊤` (Burnside/Jacobson density, proved in
   `BurnsideTheorem.lean`)
3. `algSpan A = ⊤` → `∃ N, cumulativeSpan A N = ⊤` (proved in this file, Part 1)

**Important**: `∃ N, cumulativeSpan A N = ⊤` does NOT imply `IsNormal`.
Counterexample: `A₁ = e₁₂, A₂ = e₂₁` generates `M₂(ℂ)` but `wordSpan A n`
alternates. Aperiodicity (e.g., `IsPrimitiveMPS`) is needed for IsNormal.

## References

* Burnside (1905), Proc. London Math. Soc.
* arXiv:0909.5347, Proposition 3
-/

open scoped Matrix ComplexOrder BigOperators
open Matrix MPSTensor

namespace MPSTensor

variable {d D : ℕ}

/-! ## Part 1: Algebra span -/


/-- Every word evaluation lies in the algebra span. -/
theorem evalWord_mem_algSpan (A : MPSTensor d D) (w : List (Fin d)) :
    evalWord A w ∈ algSpan A := by
  induction w with
  | nil => exact (algSpan A).one_mem
  | cons i w ih => exact (algSpan A).mul_mem (algSpan_mem A i) ih

/-- The word span at any length is contained in the algebra span (as submodules). -/
theorem wordSpan_le_algSpan_toSubmodule (A : MPSTensor d D) (n : ℕ) :
    wordSpan A n ≤ (algSpan A).toSubmodule := by
  apply Submodule.span_le.mpr
  rintro M ⟨σ, rfl⟩
  exact evalWord_mem_algSpan A (List.ofFn σ)

/-- The cumulative span is contained in the algebra span. -/
theorem cumulativeSpan_le_algSpan_toSubmodule (A : MPSTensor d D) (n : ℕ) :
    cumulativeSpan A n ≤ (algSpan A).toSubmodule := by
  apply Submodule.span_le.mpr
  rintro M ⟨w, _, rfl⟩
  exact evalWord_mem_algSpan A w

/-! ### Multiplication closure for cumulative span -/

/-- Product of generators lands in the right cumulative span. -/
theorem evalWord_mul_evalWord_mem_cumulativeSpan
    (A : MPSTensor d D)
    {w₁ w₂ : List (Fin d)} {m n : ℕ}
    (hw₁ : w₁.length ≤ m) (hw₂ : w₂.length ≤ n) :
    evalWord A w₁ * evalWord A w₂ ∈ cumulativeSpan A (m + n) := by
  rw [← evalWord_append]
  apply mem_cumulativeSpan_generator
  rw [List.length_append]
  omega

/-- The cumulative span is closed under multiplication (adding lengths). -/
theorem mul_mem_cumulativeSpan_add (A : MPSTensor d D) {m n : ℕ}
    {x y : Matrix (Fin D) (Fin D) ℂ}
    (hx : x ∈ cumulativeSpan A m) (hy : y ∈ cumulativeSpan A n) :
    x * y ∈ cumulativeSpan A (m + n) := by
  -- `cumulativeSpan` is defined as a `span`, so we can use binary span induction.
  refine Submodule.span_induction₂
      (s := {M | ∃ w : List (Fin d), w.length ≤ m ∧ M = evalWord A w})
      (t := {M | ∃ w : List (Fin d), w.length ≤ n ∧ M = evalWord A w})
      (p := fun x y _ _ => x * y ∈ cumulativeSpan A (m + n))
      ?_ ?_ ?_ ?_ ?_ ?_ ?_
      (by simpa [cumulativeSpan] using hx)
      (by simpa [cumulativeSpan] using hy)
  · intro x y hx hy
    rcases hx with ⟨w₁, hw₁, rfl⟩
    rcases hy with ⟨w₂, hw₂, rfl⟩
    exact evalWord_mul_evalWord_mem_cumulativeSpan A hw₁ hw₂
  · intro y _hy
    simp [zero_mul]
  · intro x _hx
    simp [mul_zero]
  · intro x₁ x₂ y _ _ _ hx₁ hx₂
    simpa [add_mul] using (cumulativeSpan A (m + n)).add_mem hx₁ hx₂
  · intro x y₁ y₂ _ _ _ hy₁ hy₂
    simpa [mul_add] using (cumulativeSpan A (m + n)).add_mem hy₁ hy₂
  · intro r x y _ _ hxy
    simpa [smul_mul_assoc] using (cumulativeSpan A (m + n)).smul_mem r hxy
  · intro r x y _ _ hxy
    simpa [mul_smul_comm] using (cumulativeSpan A (m + n)).smul_mem r hxy

/-- Every element of the algebra span lies in some cumulative span.

Proven via `Algebra.adjoin_induction`. -/
theorem mem_cumulativeSpan_of_mem_algSpan (A : MPSTensor d D)
    {x : Matrix (Fin D) (Fin D) ℂ} (hx : x ∈ algSpan A) :
    ∃ N : ℕ, x ∈ cumulativeSpan A N := by
  induction hx using Algebra.adjoin_induction with
  | mem x hxS =>
    rcases hxS with ⟨i, rfl⟩
    refine ⟨1, ?_⟩
    simpa [evalWord] using
      (mem_cumulativeSpan_generator (A := A) (n := 1) (w := [i]) (by simp))
  | algebraMap r =>
    refine ⟨0, ?_⟩
    simpa [Algebra.algebraMap_eq_smul_one] using
      (cumulativeSpan A 0).smul_mem r (one_mem_cumulativeSpan A 0)
  | add x y _ _ ihx ihy =>
    rcases ihx with ⟨Nx, hNx⟩
    rcases ihy with ⟨Ny, hNy⟩
    refine ⟨max Nx Ny, ?_⟩
    exact (cumulativeSpan A (max Nx Ny)).add_mem
      ((cumulativeSpan_mono' A (le_max_left Nx Ny)) hNx)
      ((cumulativeSpan_mono' A (le_max_right Nx Ny)) hNy)
  | mul x y _ _ ihx ihy =>
    rcases ihx with ⟨Nx, hNx⟩
    rcases ihy with ⟨Ny, hNy⟩
    exact ⟨Nx + Ny, mul_mem_cumulativeSpan_add A hNx hNy⟩

/-- **From algebra span to cumulative span**: if the algebra generated by `{A i}`
is all of `M_D(ℂ)`, then the cumulative span reaches ⊤ at some finite level.

Uses the Noetherian property of finite-dimensional modules. -/
theorem exists_cumulativeSpan_eq_top_of_algSpan_eq_top (A : MPSTensor d D)
    (h : algSpan A = ⊤) :
    ∃ N : ℕ, cumulativeSpan A N = ⊤ := by
  -- Every matrix is in the algebra span, hence in some cumulative span
  have hmem : ∀ x : Matrix (Fin D) (Fin D) ℂ, x ∈ algSpan A := by
    intro x; rw [h]; exact Algebra.mem_top
  have hx : ∀ x : Matrix (Fin D) (Fin D) ℂ, ∃ N, x ∈ cumulativeSpan A N :=
    fun x => mem_cumulativeSpan_of_mem_algSpan A (hmem x)
  -- The module is Noetherian (finite-dimensional over a field)
  haveI : IsNoetherian ℂ (Matrix (Fin D) (Fin D) ℂ) :=
    isNoetherian_of_isNoetherianRing_of_finite ℂ _
  -- Construct the monotone chain as an order homomorphism
  let f : ℕ →o Submodule ℂ (Matrix (Fin D) (Fin D) ℂ) :=
    ⟨cumulativeSpan A, fun _ _ h => cumulativeSpan_mono' A h⟩
  -- Noetherian ⟹ the ascending chain stabilizes
  obtain ⟨N₀, hstab⟩ := (monotone_stabilizes_iff_noetherian.mpr ‹_›) f
  -- Show the stable value is ⊤.
  refine ⟨N₀, eq_top_iff.mpr ?_⟩
  intro x _
  rcases hx x with ⟨M, hM⟩
  rcases le_total M N₀ with hMN | hNM
  · exact (cumulativeSpan_mono' A hMN) hM
  · have heq : cumulativeSpan A M = cumulativeSpan A N₀ := (hstab M hNM).symm
    simpa [heq] using hM

/-! ## Part 2: Invariant submodule characterization -/


/-- Helper: if `(1 - P) * M * P = 0`, then `M * P = P * (M * P)`. -/
private theorem mul_proj_eq {P M : Matrix (Fin D) (Fin D) ℂ}
    (hinv : (1 - P) * M * P = 0) :
    M * P = P * (M * P) := by
  -- (1 - P) * M * P = ((1 - P) * M) * P = (M - P * M) * P
  --   = M * P - P * M * P = M * P - P * (M * P)
  have h1 : (M - P * M) * P = 0 := by rwa [sub_mul, one_mul] at hinv
  have h2 : M * P - P * M * P = 0 := by rwa [sub_mul] at h1
  have h3 : M * P - P * (M * P) = 0 := by rwa [mul_assoc] at h2
  exact sub_eq_zero.mp h3

/-- `IsIrreducibleAction` implies `IsIrreducibleTensor`.

If there are no nontrivial invariant submodules, then there are no
nontrivial invariant orthogonal projections. -/
theorem isIrreducibleTensor_of_isIrreducibleAction
    (A : MPSTensor d D) (hIrr : IsIrreducibleAction A) :
    IsIrreducibleTensor (d := d) (D := D) A := by
  intro ⟨P, horth, hne0, hne1, hinv⟩
  let V : Type := Fin D → ℂ
  let f : V →ₗ[ℂ] V := Matrix.toLin' P
  -- The range of `f` is an invariant submodule.
  set W : Submodule ℂ V := LinearMap.range f
  have hW_inv : IsInvariantSubmodule A W := by
    intro i v ⟨u, hu⟩
    have hAP : A i * P = P * (A i * P) := mul_proj_eq (hinv i)
    refine ⟨(A i * P).mulVec u, ?_⟩
    simp only [V, f, Matrix.toLin'_apply] at hu ⊢
    rw [Matrix.mulVec_mulVec, ← hAP, ← Matrix.mulVec_mulVec, hu]
  rcases hIrr W hW_inv with hW | hW
  · -- `W = ⊥`: the range is trivial, hence `P = 0`.
    apply hne0
    have hf0 : f = 0 := by
      have : f.range = ⊥ := by
        simpa [W] using hW
      exact (LinearMap.range_eq_bot).1 this
    have hP0 := congrArg LinearMap.toMatrix' hf0
    simpa [f, LinearMap.toMatrix'_toLin'] using hP0
  · -- `W = ⊤`: the range is all of `V`, hence `P = 1`.
    apply hne1
    have hsurj : Function.Surjective f := by
      have : f.range = ⊤ := by
        simpa [W] using hW
      exact (LinearMap.range_eq_top).1 this
    have hfid : f = LinearMap.id := by
      apply LinearMap.ext
      intro v
      rcases hsurj v with ⟨u, rfl⟩
      -- Simplify the goal and unfold `f`.
      simp only [f, LinearMap.id_apply]
      have hmul :
          (Matrix.toLin' P) ((Matrix.toLin' P) u) = (Matrix.toLin' (P * P)) u :=
        (Matrix.toLin'_mul_apply P P u).symm
      rw [horth.2] at hmul
      exact hmul
    have hP1 := congrArg LinearMap.toMatrix' hfid
    simpa [V, f, LinearMap.toMatrix'_toLin', LinearMap.toMatrix'_id] using hP1

/-! ## Part 3: Irreducible action → cumulative span -/

/-- `IsIrreducibleAction` implies the cumulative span reaches `⊤` at some finite level.

This is Burnside's theorem (`burnside_matrix`, proven in `TNLean.Algebra.BurnsideTheorem`)
combined with `exists_cumulativeSpan_eq_top_of_algSpan_eq_top`. -/
theorem exists_cumulativeSpan_eq_top_of_isIrreducibleAction [NeZero D]
    (A : MPSTensor d D) (hIrr : IsIrreducibleAction A) :
    ∃ N : ℕ, cumulativeSpan A N = ⊤ := by
  have hBurn : algSpan A = ⊤ := burnside_matrix (A := A) hIrr
  exact exists_cumulativeSpan_eq_top_of_algSpan_eq_top A hBurn

end MPSTensor
