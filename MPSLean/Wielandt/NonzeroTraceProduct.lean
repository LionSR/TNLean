/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: [Authors]
-/

import MPSLean.Wielandt.CumulativeSpan
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Nonzero Trace Product at Bounded Word Length (Lemma 1)

This file formalizes **Lemma 1** of arXiv:0909.5347
(Sanz, Pérez-García, Wolf, Cirac).

**Paper statement**: "If E_A is primitive, then there exists
A^(n) ∈ S_n(A) with n ≤ D² − d + 1 such that tr(A^(n)) ≠ 0."

We prove two results:
1. `cumulativeSpan_eq_top_of_isNormal_bound`: Under `IsNormal`,
   the cumulative span T_n reaches ⊤ by step D².
2. `exists_nonzero_trace_word`: There exists a word product of
   length ≤ D² with nonzero trace.

**Deviation from paper**: We use the coarser bound D² instead of
D² − d + 1 to simplify natural number arithmetic. The sharper bound
can be recovered by tracking dim(S_1) = d more carefully.

## References

- [Sanz, Pérez-García, Wolf, Cirac, *A quantum version of Wielandt's
  inequality*, arXiv:0909.5347](https://arxiv.org/abs/0909.5347),
  Lemma 1
-/

open scoped Matrix
open MPSTensor

namespace MPSTensor

variable {d D : ℕ}

/-! ### The cumulative span reaches ⊤ by step D²

The argument: if T_n ≠ T_{n+1} for all n < D², then dim(T_n)
strictly increases at each step, giving dim(T_{D²}) > D². But
dim(T_n) ≤ D² always, contradiction. So some T_n = T_{n+1}, and
by stabilization, either T_n = ⊤ or the span never reaches ⊤
(contradicting IsNormal). -/

/-- Auxiliary: either `cumulativeSpan` stabilizes by step `k`, or
its dimension has grown by at least `k` compared to step 0. -/
private theorem cumulativeSpan_dim_growth
    (A : MPSTensor d D) :
    ∀ k : ℕ,
      (∃ j, j < k ∧
        cumulativeSpan A j = cumulativeSpan A (j + 1)) ∨
      Module.finrank ℂ (cumulativeSpan A k) ≥
        Module.finrank ℂ (cumulativeSpan A 0) + k := by
  intro k
  induction k with
  | zero => right; simp
  | succ k ih =>
    rcases ih with ⟨j, hj, hstab⟩ | hgrow
    · left; exact ⟨j, by omega, hstab⟩
    · by_cases hstab :
          cumulativeSpan A k = cumulativeSpan A (k + 1)
      · left; exact ⟨k, by omega, hstab⟩
      · right
        have hlt : cumulativeSpan A k <
            cumulativeSpan A (k + 1) :=
          lt_of_le_of_ne (cumulativeSpan_mono A k) hstab
        have := cumulativeSpan_finrank_strict_mono A hlt
        omega

/-- If IsNormal holds, then `cumulativeSpan A (D ^ 2) = ⊤`.

Paper: The dimension-counting argument in Lemma 1 shows that
T_{D²−d+1}(A) = M_D(ℂ). We use the coarser bound D² to avoid
natural number subtraction.
(arXiv:0909.5347, Lemma 1 proof, paragraphs 1-3) -/
theorem cumulativeSpan_eq_top_of_isNormal_bound [NeZero D]
    (A : MPSTensor d D) (hN : IsNormal A) :
    cumulativeSpan A (D ^ 2) = ⊤ := by
  by_contra hne
  rcases cumulativeSpan_dim_growth A (D ^ 2 + 1) with
    ⟨j, hj, hstab⟩ | hgrow
  · -- T_j = T_{j+1} for some j < D² + 1 (so j ≤ D²)
    -- By stabilization, T_m = T_j for all m ≥ j
    have hstable := cumulativeSpan_stable A hstab
    -- Use IsNormal: ∃ N, wordSpan A N = ⊤
    obtain ⟨N, hNblk⟩ := hN
    -- wordSpan A N ≤ cumulativeSpan A (max N j) = T_j
    have hN_le : wordSpan A N ≤ cumulativeSpan A j := by
      calc wordSpan A N
          ≤ cumulativeSpan A (N ⊔ j) :=
            wordSpan_le_cumulativeSpan A le_sup_left
        _ = cumulativeSpan A j :=
            hstable _ le_sup_right
    -- So T_j = ⊤
    have : cumulativeSpan A j = ⊤ := eq_top_iff.mpr
      (le_trans
        (eq_top_iff.mp
          ((wordSpan_eq_top_iff_isNBlkInjective A N).mpr
            hNblk))
        hN_le)
    -- But T_{D²} = T_j = ⊤, contradiction
    rw [← hstable (D ^ 2) (by omega)] at this
    exact hne this
  · -- dim(T_{D²+1}) ≥ dim(T_0) + D² + 1 > D²
    have h1 := cumulativeSpan_finrank_le A (D ^ 2 + 1)
    omega

/-! ### Nonzero trace product exists -/

/-- If `cumulativeSpan A n = ⊤` and all word products of length
≤ `n` have zero trace, then `tr(1) = 0`.
This is the contrapositive of "some word product has nonzero
trace". -/
private theorem trace_one_eq_zero_of_all_traces_zero
    (A : MPSTensor d D) {n : ℕ}
    (htop : cumulativeSpan A n = ⊤)
    (hall : ∀ w : List (Fin d), w.length ≤ n →
      Matrix.trace (evalWord A w) = 0) :
    Matrix.trace (1 : Matrix (Fin D) (Fin D) ℂ) = 0 := by
  -- The trace linear map vanishes on all generators
  have hvanish : Set.EqOn
      (Matrix.traceLinearMap (Fin D) ℂ ℂ)
      (0 : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] ℂ)
      {M | ∃ w : List (Fin d), w.length ≤ n ∧
        M = evalWord A w} := by
    rintro M ⟨w, hw, rfl⟩
    simp only [Matrix.traceLinearMap_apply, LinearMap.zero_apply]
    exact hall w hw
  -- By LinearMap.eqOn_span, trace vanishes on all of cumulativeSpan
  have h1 : (1 : Matrix (Fin D) (Fin D) ℂ) ∈
      cumulativeSpan A n := by
    rw [htop]; exact Submodule.mem_top
  have := LinearMap.eqOn_span hvanish h1
  simp only [Matrix.traceLinearMap_apply,
    LinearMap.zero_apply] at this
  exact this

/-- `tr(1 : Matrix (Fin D) (Fin D) ℂ) = D`, and `D ≠ 0` when
`NeZero D`. -/
private theorem trace_one_ne_zero [NeZero D] :
    Matrix.trace (1 : Matrix (Fin D) (Fin D) ℂ) ≠ 0 := by
  rw [Matrix.trace_one]
  simp only [Fintype.card_fin, ne_eq, Nat.cast_eq_zero]
  exact NeZero.ne D

/-- **Lemma 1** (arXiv:0909.5347), part (a):
Under `IsNormal` (eventually full word span), the cumulative span
T_n must reach ⊤ = M_D(ℂ) by step D².

Paper: "If E_A is primitive, then T_{D²−d+1}(A) = M_D(ℂ)."
We use the coarser bound D² instead of D²−d+1. -/
theorem cumulativeSpan_eq_top [NeZero D]
    (A : MPSTensor d D) (hN : IsNormal A) :
    cumulativeSpan A (D ^ 2) = ⊤ :=
  cumulativeSpan_eq_top_of_isNormal_bound A hN

/-- **Lemma 1** (arXiv:0909.5347), main statement:
Under `IsNormal`, there exists a word `w` of length ≤ D² such
that `tr(evalWord A w) ≠ 0`.

Paper: "If E_A is primitive, then there exists A^(n) ∈ S_n(A)
with n ≤ D²−d+1 such that tr(A^(n)) ≠ 0."

Deviation: We use the coarser bound D² instead of D²−d+1 to
simplify natural number arithmetic. We also assume `IsNormal`
instead of `IsPrimitive`; the connection `IsPrimitive → IsNormal`
will come in a later file.
(arXiv:0909.5347, Lemma 1) -/
theorem exists_nonzero_trace_word [NeZero D]
    (A : MPSTensor d D) (hN : IsNormal A) :
    ∃ (w : List (Fin d)),
      w.length ≤ D ^ 2 ∧
        Matrix.trace (evalWord A w) ≠ 0 := by
  by_contra hall
  push_neg at hall
  have htop := cumulativeSpan_eq_top A hN
  have := trace_one_eq_zero_of_all_traces_zero A htop hall
  exact trace_one_ne_zero this

end MPSTensor
