/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import TNLean.Algebra.BurnsideTheorem
import TNLean.MPS.CanonicalFormReduction
import TNLean.Wielandt.CumulativeSpan

import Mathlib.Algebra.Algebra.Subalgebra.Lattice
import Mathlib.RingTheory.Noetherian.Defs

/-!
# Burnside-style Bridge: Irreducibility → Normality

This file reduces the gap between `IsIrreducibleTensor` (no nontrivial invariant
orthogonal projection) and `IsNormal` (word products span `M_D(ℂ)`) to a single,
cleanly stated algebraic theorem: **Burnside's theorem for matrix algebras**.

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
  -- Double induction on the spans
  refine Submodule.span_induction
    (p := fun x _ => x * y ∈ cumulativeSpan A (m + n)) ?_ ?_ ?_ ?_ hx
  · -- x is a generator: x = evalWord A w₁
    rintro x₀ ⟨w₁, hw₁, rfl⟩
    refine Submodule.span_induction
      (p := fun y _ => evalWord A w₁ * y ∈ cumulativeSpan A (m + n)) ?_ ?_ ?_ ?_ hy
    · rintro y₀ ⟨w₂, hw₂, rfl⟩
      exact evalWord_mul_evalWord_mem_cumulativeSpan A hw₁ hw₂
    · simp [mul_zero, (cumulativeSpan A (m + n)).zero_mem]
    · intro a b _ _ ha hb; rw [mul_add]; exact (cumulativeSpan A (m + n)).add_mem ha hb
    · intro r a _ ha; rw [mul_smul_comm]; exact (cumulativeSpan A (m + n)).smul_mem r ha
  · simp [zero_mul, (cumulativeSpan A (m + n)).zero_mem]
  · intro a b _ _ ha hb; rw [add_mul]; exact (cumulativeSpan A (m + n)).add_mem ha hb
  · intro r a _ ha; rw [smul_mul_assoc]; exact (cumulativeSpan A (m + n)).smul_mem r ha

/-- Every element of the algebra span lies in some cumulative span.

Proven via `Algebra.adjoin_induction`. -/
theorem mem_cumulativeSpan_of_mem_algSpan (A : MPSTensor d D)
    {x : Matrix (Fin D) (Fin D) ℂ} (hx : x ∈ algSpan A) :
    ∃ N : ℕ, x ∈ cumulativeSpan A N := by
  induction hx using Algebra.adjoin_induction with
  | mem x hxS =>
    obtain ⟨i, rfl⟩ := hxS
    exact ⟨1, wordSpan_le_cumulativeSpan A (le_refl 1)
      (Submodule.subset_span ⟨fun _ => i, by simp [evalWord]⟩)⟩
  | algebraMap r =>
    refine ⟨0, ?_⟩
    rw [Algebra.algebraMap_eq_smul_one]
    exact (cumulativeSpan A 0).smul_mem r (one_mem_cumulativeSpan A 0)
  | add x y _ _ ihx ihy =>
    obtain ⟨Nx, hNx⟩ := ihx
    obtain ⟨Ny, hNy⟩ := ihy
    exact ⟨max Nx Ny, (cumulativeSpan A (max Nx Ny)).add_mem
      (cumulativeSpan_mono' A (le_max_left Nx Ny) hNx)
      (cumulativeSpan_mono' A (le_max_right Nx Ny) hNy)⟩
  | mul x y _ _ ihx ihy =>
    obtain ⟨Nx, hNx⟩ := ihx
    obtain ⟨Ny, hNy⟩ := ihy
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
  -- Show the stable value is ⊤
  refine ⟨N₀, eq_top_iff.mpr (fun x _ => ?_)⟩
  obtain ⟨M, hM⟩ := hx x
  by_cases hle : N₀ ≤ M
  · -- M ≥ N₀: cumulativeSpan A M = cumulativeSpan A N₀ by stabilization
    have heq : cumulativeSpan A N₀ = cumulativeSpan A M := hstab M hle
    rw [heq]; exact hM
  · -- M < N₀: cumulativeSpan A M ≤ cumulativeSpan A N₀ by monotonicity
    exact cumulativeSpan_mono' A (by omega) hM

/-! ## Part 2: Invariant submodule characterization -/


/-- Helper: if `(1-P)*M*P = 0` and `P*P = P`, then `M * P = P * (M * P)`. -/
private theorem mul_proj_eq {P M : Matrix (Fin D) (Fin D) ℂ}
    (_hPP : P * P = P) (hinv : (1 - P) * M * P = 0) :
    M * P = P * (M * P) := by
  -- (1 - P) * M * P = ((1-P)*M)*P = (M - P*M)*P = M*P - P*M*P = 0
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
  -- The column space of P is an invariant submodule
  set W : Submodule ℂ (Fin D → ℂ) := LinearMap.range (Matrix.toLin' P)
  -- W is A-invariant
  have hW_inv : IsInvariantSubmodule A W := by
    intro i v ⟨u, hu⟩
    -- A_i * P = P * (A_i * P) (from (1-P)*A_i*P = 0 and P²=P)
    have hAP : A i * P = P * (A i * P) := mul_proj_eq horth.2 (hinv i)
    refine ⟨(A i * P).mulVec u, ?_⟩
    -- Goal: (toLin' P) ((A i * P).mulVec u) = (A i).mulVec v
    simp only [Matrix.toLin'_apply] at hu ⊢
    -- Now hu : P.mulVec u = v
    -- Goal: P.mulVec ((A i * P).mulVec u) = (A i).mulVec v
    rw [Matrix.mulVec_mulVec, ← hAP, ← Matrix.mulVec_mulVec, hu]
  -- Apply IsIrreducibleAction to get W = ⊥ or W = ⊤
  rcases hIrr W hW_inv with h | h
  · -- W = ⊥: range(toLin' P) = ⊥ means toLin' P = 0 means P = 0
    apply hne0
    rw [LinearMap.range_eq_bot] at h
    ext i j
    have h1 : Matrix.toLin' P (Pi.single j 1) = 0 :=
      LinearMap.ext_iff.mp h (Pi.single j 1)
    have h2 := congr_fun h1 i
    simp [Matrix.toLin'_apply, Matrix.mulVec] at h2
    simpa using h2
  · -- W = ⊤: range(toLin' P) = ⊤ means P is surjective
    apply hne1
    rw [LinearMap.range_eq_top] at h
    ext i j
    -- Get u with P *ᵥ u = e_j (the j-th standard basis vector)
    obtain ⟨u, hu⟩ := h (Pi.single j 1)
    -- P e_j = P (P u) = P² u = P u = e_j
    have hPu : P.mulVec u = Pi.single j 1 := by
      rw [← Matrix.toLin'_apply]; exact hu
    have hPPu : P.mulVec (P.mulVec u) = P.mulVec u := by
      rw [Matrix.mulVec_mulVec, horth.2]
    have key : P.mulVec (Pi.single j 1) = Pi.single j 1 := by
      rw [← hPu, hPPu, hPu]
    have h1 := congr_fun key i
    simp [Matrix.mulVec] at h1
    -- h1 : P i j = Pi.single j 1 i
    -- 1 i j = if i = j then 1 else 0 = Pi.single j 1 i
    simp [Matrix.one_apply, h1, Pi.single_apply]

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
