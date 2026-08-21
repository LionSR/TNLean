/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.MPS.Core.Injectivity
import QICLean.Kraus.Wielandt.SpanGrowth.CumulativeSpan
import QICLean.MPS.Core.Word

/-!
# Cumulative word spans and TN injectivity

For an MPS tensor $A$, the exact word span $S_n(A)$ contains products of
length $n$, while the cumulative span $T_n(A)$ contains products of length at
most $n$. This file also relates these spaces to block injectivity and
normality.
-/

open scoped Matrix

namespace MPSTensor

variable {d D : ℕ}

/-! ### Word spans -/

/-- Cumulative word spans are monotone in their length bound. -/
theorem cumulativeSpan_mono' (A : MPSTensor d D) {n m : ℕ} (h : n ≤ m) :
    Kraus.cumulativeSpan A n ≤ Kraus.cumulativeSpan A m :=
  Kraus.cumulativeSpan_mono' A h

/-- The identity matrix belongs to every cumulative word span. -/
theorem one_mem_cumulativeSpan (A : MPSTensor d D) (n : ℕ) :
    (1 : Matrix (Fin D) (Fin D) ℂ) ∈ Kraus.cumulativeSpan A n :=
  Kraus.one_mem_cumulativeSpan A n

/-! ### Injectivity and normality -/

/-- Block injectivity at a positive length propagates to the next length. -/
theorem isNBlkInjective_succ_of_isNBlkInjective
    (A : MPSTensor d D) {L : ℕ} (hLpos : 0 < L)
    (hL : IsNBlkInjective A L) :
    IsNBlkInjective A (L + 1) := by
  change Kraus.wordSpan A L = ⊤ at hL
  change Kraus.wordSpan A (L + 1) = ⊤
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hLpos)
  have hprev_le : Kraus.wordSpan A n ≤ Kraus.wordSpan A (n + 1) := by
    rw [hL]
    exact le_top
  rw [Kraus.wordSpan_succ_eq_mul_left A (n + 1)]
  apply eq_top_iff.mpr
  calc
    ⊤ = Kraus.wordSpan A (n + 1) := hL.symm
    _ = Submodule.span ℂ (Set.range A) * Kraus.wordSpan A n :=
      Kraus.wordSpan_succ_eq_mul_left A n
    _ ≤ Submodule.span ℂ (Set.range A) * Kraus.wordSpan A (n + 1) :=
      mul_le_mul' le_rfl hprev_le

/-- Block injectivity at a positive length propagates to every greater length. -/
theorem isNBlkInjective_of_le {A : MPSTensor d D} {L m : ℕ}
    (hLpos : 0 < L) (hL : IsNBlkInjective A L) (hLm : L ≤ m) :
    IsNBlkInjective A m := by
  induction m, hLm using Nat.le_induction with
  | base => exact hL
  | succ m hLm ih =>
      exact isNBlkInjective_succ_of_isNBlkInjective A
        (lt_of_lt_of_le hLpos hLm) ih

/-- Exact word-span fullness is block injectivity. -/
theorem wordSpan_eq_top_iff_isNBlkInjective (A : MPSTensor d D) (N : ℕ) :
    Kraus.wordSpan A N = ⊤ ↔ IsNBlkInjective A N :=
  Iff.rfl

/-- Normality implies fullness of a cumulative word span. -/
theorem cumulativeSpan_eq_top_of_isNormal (A : MPSTensor d D)
    (hN : IsNormal A) : ∃ N, Kraus.cumulativeSpan A N = ⊤ := by
  obtain ⟨N, _hNpos, hN⟩ := hN
  exact ⟨N, eq_top_iff.mpr (le_trans
    (eq_top_iff.mp ((wordSpan_eq_top_iff_isNBlkInjective A N).mpr hN))
    (Kraus.wordSpan_le_cumulativeSpan A le_rfl))⟩

/-- Zero-block injectivity forces one-dimensional bond space. -/
theorem bondDim_eq_one_of_isNBlkInjective_zero [NeZero D]
    (A : MPSTensor d D) (hA : IsNBlkInjective A 0) :
    D = 1 := by
  by_contra hD_ne
  have hD_pos : 0 < D := NeZero.pos D
  have hD_ge : 2 ≤ D := by omega
  have htop : Kraus.wordSpan A 0 =
      (⊤ : Submodule ℂ (Matrix (Fin D) (Fin D) ℂ)) :=
    (wordSpan_eq_top_iff_isNBlkInjective A 0).mpr hA
  exact Kraus.wordSpan_zero_ne_top_of_two_le A hD_ge htop

end MPSTensor
