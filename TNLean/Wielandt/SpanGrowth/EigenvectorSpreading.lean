/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Kraus.Wielandt.SpanGrowth.EigenvectorSpreading
import TNLean.Wielandt.SpanGrowth.CumulativeSpan

/-!
# Eigenvector spreading for MPS tensors

This file preserves the established MPS tensor interface to the transfer-free
vector-spreading results in `Kraus` and proves the normal-tensor specialization.
-/

open scoped Matrix

namespace MPSTensor

variable {d D : ℕ}

/-- The span of all length-`n` word products applied to `φ`. -/
abbrev vectorSpreadSpan (A : MPSTensor d D) (φ : Fin D → ℂ) (n : ℕ) :
    Submodule ℂ (Fin D → ℂ) :=
  Kraus.vectorSpreadSpan A φ n

/-- Every evaluated word applied to `φ` belongs to the spread span at its length. -/
theorem evalWord_mulVec_mem_vectorSpreadSpan (A : MPSTensor d D) (φ : Fin D → ℂ)
    (w : List (Fin d)) :
    evalWord A w *ᵥ φ ∈ vectorSpreadSpan A φ w.length :=
  Kraus.evalWord_mulVec_mem_vectorSpreadSpan A φ w

/-- The span of all word products of length at most `n` applied to `φ`. -/
abbrev cumulativeVectorSpan (A : MPSTensor d D) (φ : Fin D → ℂ) (n : ℕ) :
    Submodule ℂ (Fin D → ℂ) :=
  Kraus.cumulativeVectorSpan A φ n

/-- Every word of length at most `n`, applied to `φ`, belongs to the cumulative span. -/
theorem mem_cumulativeVectorSpan_generator (A : MPSTensor d D) (φ : Fin D → ℂ) {n : ℕ}
    {w : List (Fin d)} (hw : w.length ≤ n) :
    evalWord A w *ᵥ φ ∈ cumulativeVectorSpan A φ n :=
  Kraus.mem_cumulativeVectorSpan_generator A φ hw

/-- Exact vector spread spans lie in every sufficiently large cumulative vector span. -/
theorem vectorSpreadSpan_le_cumulativeVectorSpan (A : MPSTensor d D) (φ : Fin D → ℂ)
    {m n : ℕ} (h : m ≤ n) :
    vectorSpreadSpan A φ m ≤ cumulativeVectorSpan A φ n :=
  Kraus.vectorSpreadSpan_le_cumulativeVectorSpan A φ h

/-- Cumulative vector spans increase with the length bound. -/
theorem cumulativeVectorSpan_mono (A : MPSTensor d D) (φ : Fin D → ℂ) (n : ℕ) :
    cumulativeVectorSpan A φ n ≤ cumulativeVectorSpan A φ (n + 1) :=
  Kraus.cumulativeVectorSpan_mono A φ n

/-- Cumulative vector spans are monotone in their length bound. -/
theorem cumulativeVectorSpan_mono' (A : MPSTensor d D) (φ : Fin D → ℂ) {n m : ℕ}
    (h : n ≤ m) : cumulativeVectorSpan A φ n ≤ cumulativeVectorSpan A φ m :=
  Kraus.cumulativeVectorSpan_mono' A φ h

/-- Equality at consecutive lengths forces equality at all later lengths. -/
theorem cumulativeVectorSpan_stable (A : MPSTensor d D) (φ : Fin D → ℂ) {n : ℕ}
    (h : cumulativeVectorSpan A φ n = cumulativeVectorSpan A φ (n + 1)) :
    ∀ m, n ≤ m → cumulativeVectorSpan A φ m = cumulativeVectorSpan A φ n :=
  Kraus.cumulativeVectorSpan_stable A φ h

/-- The anchor vector belongs to every cumulative vector span. -/
theorem phi_mem_cumulativeVectorSpan (A : MPSTensor d D) (φ : Fin D → ℂ) (n : ℕ) :
    φ ∈ cumulativeVectorSpan A φ n :=
  Kraus.phi_mem_cumulativeVectorSpan A φ n

/-- The dimension of a cumulative vector span is at most `D`. -/
theorem cumulativeVectorSpan_finrank_le (A : MPSTensor d D) (φ : Fin D → ℂ) (n : ℕ) :
    Module.finrank ℂ (cumulativeVectorSpan A φ n) ≤ D :=
  Kraus.cumulativeVectorSpan_finrank_le A φ n

/-- Strict growth of cumulative vector spans gives strict growth of dimensions. -/
theorem cumulativeVectorSpan_finrank_strict_mono (A : MPSTensor d D) (φ : Fin D → ℂ)
    {n : ℕ} (h : cumulativeVectorSpan A φ n < cumulativeVectorSpan A φ (n + 1)) :
    Module.finrank ℂ (cumulativeVectorSpan A φ n) <
      Module.finrank ℂ (cumulativeVectorSpan A φ (n + 1)) :=
  Kraus.cumulativeVectorSpan_finrank_strict_mono A φ h

/-- Full cumulative matrix span gives full cumulative vector span for a nonzero vector. -/
theorem cumulativeVectorSpan_eq_top_of_cumulativeSpan_eq_top
    (A : MPSTensor d D) (φ : Fin D → ℂ) (hφ : φ ≠ 0)
    {N : ℕ} (htop : cumulativeSpan A N = ⊤) :
    cumulativeVectorSpan A φ N = ⊤ :=
  Kraus.cumulativeVectorSpan_eq_top_of_cumulativeSpan_eq_top A φ hφ htop

/-- The initial cumulative vector span has positive dimension for a nonzero vector. -/
theorem cumulativeVectorSpan_finrank_pos (A : MPSTensor d D)
    (φ : Fin D → ℂ) (hφ : φ ≠ 0) :
    0 < Module.finrank ℂ (cumulativeVectorSpan A φ 0) :=
  Kraus.cumulativeVectorSpan_finrank_pos A φ hφ

/-- If a cumulative matrix span is full, the cumulative vector span is full by step `D - 1`. -/
theorem eigenvector_spreading_of_cumulativeSpan_eq_top [NeZero D]
    (A : MPSTensor d D) (φ : Fin D → ℂ) (hφ : φ ≠ 0)
    {N : ℕ} (hCum : cumulativeSpan A N = ⊤) :
    cumulativeVectorSpan A φ (D - 1) = ⊤ :=
  Kraus.eigenvector_spreading_of_cumulativeSpan_eq_top A φ hφ hCum

/-- **Lemma 2(a)**: If the channel is normal and `A` has an eigenvector
with nonzero eigenvalue, then `K_{D-1}(A, φ) = ℂ^D`.

Paper: `H_{D-1}(A, φ) = ℂ^D` (arXiv:0909.5347, Lemma 2(a)).

Deviation: we prove the cumulative conclusion `K_{D-1} = ⊤` instead of the paper's
single-level conclusion `H_{D-1} = ⊤`. This is enough for every downstream use in this
formalization.

The eigenvector data are kept in the statement to match the paper and downstream
theorems. The current cumulative proof uses only `hφ` together with
the normality witness. -/
theorem eigenvector_spreading [NeZero D]
    (A : MPSTensor d D) (φ : Fin D → ℂ) (hφ : φ ≠ 0)
    (_i₀ : Fin d) (_μ : ℂ) (_hμ : _μ ≠ 0)
    (_heig : A _i₀ *ᵥ φ = _μ • φ)
    (hNormal : IsNormal A) :
    cumulativeVectorSpan A φ (D - 1) = ⊤ := by
  obtain ⟨N, hN⟩ := cumulativeSpan_eq_top_of_isNormal A hNormal
  exact eigenvector_spreading_of_cumulativeSpan_eq_top A φ hφ hN

end MPSTensor
