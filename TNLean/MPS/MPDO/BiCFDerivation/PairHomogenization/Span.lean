/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.MPDO.BiCFDerivation.Core

/-!
# Homogeneous word-tuple multiplication and identity padding

This module contains homogeneous word-tuple multiplication, identity padding,
cumulative-to-homogeneous conversion lemmas, and the finite-family all-length
to homogeneous reduction.  It is part of the pair-span homogenization layer
for MPDO biCF.
-/

open scoped Matrix BigOperators

namespace MPSTensor

variable {d : ℕ} {r : ℕ} {dim : Fin r → ℕ}

/-- A finite word pair belongs to the homogeneous pair span at its own length. -/
theorem pairEvalWordTuple_mem_span_pairWordTuple_length {D₁ D₂ : ℕ}
    (A : MPSTensor d D₁) (B : MPSTensor d D₂) (w : List (Fin d)) :
    pairEvalWordTuple A B w ∈
      Submodule.span ℂ (Set.range (pairWordTuple A B w.length)) := by
  apply Submodule.subset_span
  exact ⟨w.get, by simp [pairWordTuple, pairEvalWordTuple, List.ofFn_get]⟩

/-- Homogeneous pair spans are closed under componentwise multiplication, with
word lengths adding. -/
theorem pair_mul_mem_span_pairWordTuple_add {D₁ D₂ : ℕ}
    (A : MPSTensor d D₁) (B : MPSTensor d D₂) {L S : ℕ}
    {M N : Matrix (Fin D₁) (Fin D₁) ℂ × Matrix (Fin D₂) (Fin D₂) ℂ}
    (hM : M ∈ Submodule.span ℂ (Set.range (pairWordTuple A B L)))
    (hN : N ∈ Submodule.span ℂ (Set.range (pairWordTuple A B S))) :
    (M.1 * N.1, M.2 * N.2) ∈
      Submodule.span ℂ (Set.range (pairWordTuple A B (L + S))) := by
  classical
  let spanLS : Submodule ℂ
      (Matrix (Fin D₁) (Fin D₁) ℂ × Matrix (Fin D₂) (Fin D₂) ℂ) :=
    Submodule.span ℂ (Set.range (pairWordTuple A B (L + S)))
  have hleft_gen : ∀ u : Fin L → Fin d,
      ((pairWordTuple A B L u).1 * N.1, (pairWordTuple A B L u).2 * N.2) ∈
        spanLS := by
    intro u
    induction hN using Submodule.span_induction with
    | mem N' hNmem =>
        rcases hNmem with ⟨v, rfl⟩
        have hEq :
            ((pairWordTuple A B L u).1 * (pairWordTuple A B S v).1,
                (pairWordTuple A B L u).2 * (pairWordTuple A B S v).2) =
              pairWordTuple A B (L + S) (Fin.append u v) := by
          ext <;> simp [pairWordTuple, List.ofFn_fin_append, evalWord_append]
        rw [hEq]
        exact Submodule.subset_span ⟨Fin.append u v, rfl⟩
    | zero =>
        let PairMat := Matrix (Fin D₁) (Fin D₁) ℂ × Matrix (Fin D₂) (Fin D₂) ℂ
        have hzero :
            ((pairWordTuple A B L u).1 * (0 : PairMat).1,
              (pairWordTuple A B L u).2 * (0 : PairMat).2) = 0 := by
          simp [PairMat]
        rw [hzero]
        exact Submodule.zero_mem _
    | add N₁ N₂ _ _ hN₁ hN₂ =>
        have hEq :
            ((pairWordTuple A B L u).1 * (N₁ + N₂).1,
              (pairWordTuple A B L u).2 * (N₁ + N₂).2) =
              ((pairWordTuple A B L u).1 * N₁.1,
                (pairWordTuple A B L u).2 * N₁.2) +
              ((pairWordTuple A B L u).1 * N₂.1,
                (pairWordTuple A B L u).2 * N₂.2) := by
          ext <;> simp [Matrix.mul_add]
        rw [hEq]
        exact Submodule.add_mem _ hN₁ hN₂
    | smul a N _ hN =>
        have hEq :
            ((pairWordTuple A B L u).1 * (a • N).1,
              (pairWordTuple A B L u).2 * (a • N).2) =
              a • ((pairWordTuple A B L u).1 * N.1,
                (pairWordTuple A B L u).2 * N.2) := by
          ext <;> simp
        rw [hEq]
        exact Submodule.smul_mem _ a hN
  induction hM using Submodule.span_induction with
  | mem M hMmem =>
      rcases hMmem with ⟨u, rfl⟩
      exact hleft_gen u
  | zero =>
      have hzero :
          ((0 : Matrix (Fin D₁) (Fin D₁) ℂ × Matrix (Fin D₂) (Fin D₂) ℂ).1 * N.1,
            (0 : Matrix (Fin D₁) (Fin D₁) ℂ × Matrix (Fin D₂) (Fin D₂) ℂ).2 * N.2)
            = 0 := by
        simp
      rw [hzero]
      exact Submodule.zero_mem _
  | add M₁ M₂ _ _ hM₁ hM₂ =>
      have hEq : ((M₁ + M₂).1 * N.1, (M₁ + M₂).2 * N.2) =
          (M₁.1 * N.1, M₁.2 * N.2) + (M₂.1 * N.1, M₂.2 * N.2) := by
        ext <;> simp [Matrix.add_mul]
      rw [hEq]
      exact Submodule.add_mem _ hM₁ hM₂
  | smul a M _ hM =>
      have hEq : ((a • M).1 * N.1, (a • M).2 * N.2) =
          a • (M.1 * N.1, M.2 * N.2) := by
        ext <;> simp
      rw [hEq]
      exact Submodule.smul_mem _ a hM

/-- The simultaneous pair identity lies in the homogeneous span of length zero. -/
theorem pairIdentity_mem_pairWordTupleSpan_zero {D₁ D₂ : ℕ}
    (A : MPSTensor d D₁) (B : MPSTensor d D₂) :
      ((1 : Matrix (Fin D₁) (Fin D₁) ℂ), (1 : Matrix (Fin D₂) (Fin D₂) ℂ)) ∈
        Submodule.span ℂ (Set.range (pairWordTuple A B 0)) := by
  apply Submodule.subset_span
  refine ⟨(fun i : Fin 0 => Fin.elim0 i), ?_⟩
  ext <;> simp [pairWordTuple]

/-- Homogeneous identity padding is closed under adding word lengths. -/
theorem pairIdentity_mem_pairWordTupleSpan_add {D₁ D₂ : ℕ}
    (A : MPSTensor d D₁) (B : MPSTensor d D₂) {m n : ℕ}
    (hm :
      ((1 : Matrix (Fin D₁) (Fin D₁) ℂ), (1 : Matrix (Fin D₂) (Fin D₂) ℂ)) ∈
        Submodule.span ℂ (Set.range (pairWordTuple A B m)))
    (hn :
      ((1 : Matrix (Fin D₁) (Fin D₁) ℂ), (1 : Matrix (Fin D₂) (Fin D₂) ℂ)) ∈
        Submodule.span ℂ (Set.range (pairWordTuple A B n))) :
      ((1 : Matrix (Fin D₁) (Fin D₁) ℂ), (1 : Matrix (Fin D₂) (Fin D₂) ℂ)) ∈
        Submodule.span ℂ (Set.range (pairWordTuple A B (m + n))) := by
  simpa using
    pair_mul_mem_span_pairWordTuple_add (A := A) (B := B)
      (L := m) (S := n)
      (M := ((1 : Matrix (Fin D₁) (Fin D₁) ℂ), (1 : Matrix (Fin D₂) (Fin D₂) ℂ)))
      (N := ((1 : Matrix (Fin D₁) (Fin D₁) ℂ), (1 : Matrix (Fin D₂) (Fin D₂) ℂ)))
      hm hn

/-- Once the simultaneous pair identity is available at a period length, it is
available at every multiple of that period. -/
theorem pairIdentity_mem_pairWordTupleSpan_mul {D₁ D₂ : ℕ}
    (A : MPSTensor d D₁) (B : MPSTensor d D₂) {period : ℕ}
    (hperiod :
      ((1 : Matrix (Fin D₁) (Fin D₁) ℂ), (1 : Matrix (Fin D₂) (Fin D₂) ℂ)) ∈
        Submodule.span ℂ (Set.range (pairWordTuple A B period))) :
      ∀ k : ℕ,
        ((1 : Matrix (Fin D₁) (Fin D₁) ℂ), (1 : Matrix (Fin D₂) (Fin D₂) ℂ)) ∈
          Submodule.span ℂ (Set.range (pairWordTuple A B (k * period)))
  | 0 => by
      rw [Nat.zero_mul]
      exact pairIdentity_mem_pairWordTupleSpan_zero A B
  | k + 1 => by
      have hk :
          ((1 : Matrix (Fin D₁) (Fin D₁) ℂ), (1 : Matrix (Fin D₂) (Fin D₂) ℂ)) ∈
            Submodule.span ℂ (Set.range (pairWordTuple A B (k * period))) :=
        pairIdentity_mem_pairWordTupleSpan_mul (A := A) (B := B) hperiod k
      have hstep :=
        pairIdentity_mem_pairWordTupleSpan_add (A := A) (B := B)
          (m := k * period) (n := period) hk hperiod
      rw [Nat.succ_mul]
      exact hstep

/-- A residue-window padding certificate extends along any number of period
steps. This is the arithmetic shell needed by the corrected Burnside-Jacobson
identity-padding argument. -/
theorem pairIdentity_mem_pairWordTupleSpan_add_mul {D₁ D₂ : ℕ}
    (A : MPSTensor d D₁) (B : MPSTensor d D₂) {base period : ℕ}
    (hbase :
      ((1 : Matrix (Fin D₁) (Fin D₁) ℂ), (1 : Matrix (Fin D₂) (Fin D₂) ℂ)) ∈
        Submodule.span ℂ (Set.range (pairWordTuple A B base)))
    (hperiod :
      ((1 : Matrix (Fin D₁) (Fin D₁) ℂ), (1 : Matrix (Fin D₂) (Fin D₂) ℂ)) ∈
        Submodule.span ℂ (Set.range (pairWordTuple A B period))) :
      ∀ k : ℕ,
        ((1 : Matrix (Fin D₁) (Fin D₁) ℂ), (1 : Matrix (Fin D₂) (Fin D₂) ℂ)) ∈
          Submodule.span ℂ (Set.range (pairWordTuple A B (base + k * period))) := by
  intro k
  exact pairIdentity_mem_pairWordTupleSpan_add (A := A) (B := B)
    (m := base) (n := k * period) hbase
    (pairIdentity_mem_pairWordTupleSpan_mul (A := A) (B := B) hperiod k)

/-- If the homogeneous pair span is already full at length `n`, then it contains
the simultaneous pair identity at length `n`. -/
theorem pairIdentity_mem_pairWordTupleSpan_of_pairWordTupleSpanTop {D₁ D₂ : ℕ}
    (A : MPSTensor d D₁) (B : MPSTensor d D₂) {n : ℕ}
    (hSpan : PairWordTupleSpanTop A B n) :
      ((1 : Matrix (Fin D₁) (Fin D₁) ℂ), (1 : Matrix (Fin D₂) (Fin D₂) ℂ)) ∈
        Submodule.span ℂ (Set.range (pairWordTuple A B n)) := by
  rw [hSpan]
  exact Submodule.mem_top

/-- Full homogeneous pair span at a positive length propagates by one letter. -/
theorem pairWordTupleSpanTop_succ_of_pos {D₁ D₂ : ℕ}
    (A : MPSTensor d D₁) (B : MPSTensor d D₂) {T : ℕ}
    (hT : 0 < T) (hTop : PairWordTupleSpanTop A B T) :
    PairWordTupleSpanTop A B (T + 1) := by
  classical
  rcases T with _ | T
  · cases hT
  unfold PairWordTupleSpanTop
  apply eq_top_iff.mpr
  intro M _
  have hM : M ∈ Submodule.span ℂ (Set.range (pairWordTuple A B (T + 1))) := by
    rw [hTop]
    exact Submodule.mem_top
  have hle : Submodule.span ℂ (Set.range (pairWordTuple A B (T + 1))) ≤
      Submodule.span ℂ (Set.range (pairWordTuple A B ((T + 1) + 1))) := by
    apply Submodule.span_le.mpr
    rintro N ⟨w, rfl⟩
    let i : Fin d := w 0
    let tail : Fin T → Fin d := fun j => w j.succ
    have hletter : pairEvalWordTuple A B [i] ∈
        Submodule.span ℂ (Set.range (pairWordTuple A B 1)) :=
      pairEvalWordTuple_mem_span_pairWordTuple_length A B [i]
    have htail : pairEvalWordTuple A B (List.ofFn tail) ∈
        Submodule.span ℂ (Set.range (pairWordTuple A B (T + 1))) := by
      rw [hTop]
      exact Submodule.mem_top
    have hmul :=
      pair_mul_mem_span_pairWordTuple_add (A := A) (B := B)
        (L := 1) (S := T + 1)
        (M := pairEvalWordTuple A B [i])
        (N := pairEvalWordTuple A B (List.ofFn tail)) hletter htail
    rw [Nat.add_comm 1 (T + 1)] at hmul
    have hprod :
        ((pairEvalWordTuple A B [i]).1 * (pairEvalWordTuple A B (List.ofFn tail)).1,
          (pairEvalWordTuple A B [i]).2 * (pairEvalWordTuple A B (List.ofFn tail)).2) =
          pairWordTuple A B (T + 1) w := by
      ext <;> simp [pairWordTuple, pairEvalWordTuple, i, tail]
    simpa [hprod] using hmul
  exact hle hM

/-- Full homogeneous pair span at one positive length propagates to every later length. -/
theorem pairWordTupleSpanTop_of_le_of_pos {D₁ D₂ : ℕ}
    (A : MPSTensor d D₁) (B : MPSTensor d D₂) {S T : ℕ}
    (hS : 0 < S) (hST : S ≤ T) (hSpan : PairWordTupleSpanTop A B S) :
    PairWordTupleSpanTop A B T := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hST
  have hTopAdd : ∀ k : ℕ, PairWordTupleSpanTop A B (S + k) := by
    intro k
    induction k with
    | zero => simpa using hSpan
    | succ k ih =>
        simpa [Nat.add_assoc] using
          pairWordTupleSpanTop_succ_of_pos A B
            (Nat.lt_of_lt_of_le hS (Nat.le_add_right S k)) ih
  exact hTopAdd k

/-- If the homogeneous pair span is full at one positive length, then the
simultaneous pair identity lies in every sufficiently long homogeneous pair-word
span. -/
theorem pairIdentity_mem_pairWordTupleSpan_eventually_of_pairWordTupleSpanTop {D₁ D₂ : ℕ}
    (A : MPSTensor d D₁) (B : MPSTensor d D₂) {S : ℕ}
    (hS : 0 < S) (hSpan : PairWordTupleSpanTop A B S) :
    ∃ L : ℕ, ∀ n : ℕ, n ≥ L →
      ((1 : Matrix (Fin D₁) (Fin D₁) ℂ), (1 : Matrix (Fin D₂) (Fin D₂) ℂ)) ∈
        Submodule.span ℂ (Set.range (pairWordTuple A B n)) := by
  refine ⟨S, ?_⟩
  intro n hn
  exact pairIdentity_mem_pairWordTupleSpan_of_pairWordTupleSpanTop A B
    (pairWordTupleSpanTop_of_le_of_pos A B hS hn hSpan)

/-- A finite residue window plus one period supplies identity padding at every
sufficiently large length. -/
theorem pairIdentity_mem_pairWordTupleSpan_eventually_of_period_window {D₁ D₂ : ℕ}
    (A : MPSTensor d D₁) (B : MPSTensor d D₂)
    {start period : ℕ} (hperiod_pos : 0 < period)
    (hperiod :
      ((1 : Matrix (Fin D₁) (Fin D₁) ℂ), (1 : Matrix (Fin D₂) (Fin D₂) ℂ)) ∈
        Submodule.span ℂ (Set.range (pairWordTuple A B period)))
    (hwindow : ∀ r : ℕ, r < period →
      ((1 : Matrix (Fin D₁) (Fin D₁) ℂ), (1 : Matrix (Fin D₂) (Fin D₂) ℂ)) ∈
        Submodule.span ℂ (Set.range (pairWordTuple A B (start + r)))) :
    ∃ L : ℕ, ∀ n : ℕ, n ≥ L →
      ((1 : Matrix (Fin D₁) (Fin D₁) ℂ), (1 : Matrix (Fin D₂) (Fin D₂) ℂ)) ∈
        Submodule.span ℂ (Set.range (pairWordTuple A B n)) := by
  refine ⟨start, ?_⟩
  intro n hn
  let r := (n - start) % period
  let k := (n - start) / period
  have hr : r < period := by
    exact Nat.mod_lt _ hperiod_pos
  have hbase :
      ((1 : Matrix (Fin D₁) (Fin D₁) ℂ), (1 : Matrix (Fin D₂) (Fin D₂) ℂ)) ∈
        Submodule.span ℂ (Set.range (pairWordTuple A B (start + r))) :=
    hwindow r hr
  have hpad :=
    pairIdentity_mem_pairWordTupleSpan_add_mul (A := A) (B := B)
      (base := start + r) (period := period) hbase hperiod k
  have hlen : start + r + k * period = n := by
    dsimp [r, k]
    rw [Nat.add_assoc]
    rw [Nat.mul_comm ((n - start) / period) period]
    rw [Nat.mod_add_div]
    exact Nat.add_sub_of_le hn
  rw [← hlen]
  exact hpad

/-- A finite residue window of full homogeneous pair spans gives eventual
identity padding. -/
theorem pairIdentity_mem_pairWordTupleSpan_eventually_of_pairWordTupleSpanTop_period_window
    {D₁ D₂ : ℕ}
    (A : MPSTensor d D₁) (B : MPSTensor d D₂)
    {start period : ℕ} (hperiod_pos : 0 < period)
    (hperiod : PairWordTupleSpanTop A B period)
    (hwindow : ∀ r : ℕ, r < period → PairWordTupleSpanTop A B (start + r)) :
    ∃ L : ℕ, ∀ n : ℕ, n ≥ L →
      ((1 : Matrix (Fin D₁) (Fin D₁) ℂ), (1 : Matrix (Fin D₂) (Fin D₂) ℂ)) ∈
        Submodule.span ℂ (Set.range (pairWordTuple A B n)) :=
  pairIdentity_mem_pairWordTupleSpan_eventually_of_period_window
    (A := A) (B := B) hperiod_pos
    (pairIdentity_mem_pairWordTupleSpan_of_pairWordTupleSpanTop A B hperiod)
    (fun r hr =>
      pairIdentity_mem_pairWordTupleSpan_of_pairWordTupleSpanTop A B (hwindow r hr))

/-- For the Burnside–Jacobson all-words span argument, it suffices to produce
one period and a full residue window of homogeneous span-top certificates. -/
theorem pairIdentity_mem_pairWordTupleSpan_eventually_of_pairAllWordsSpanTop_period_window
    {D₁ D₂ : ℕ}
    (A : MPSTensor d D₁) (B : MPSTensor d D₂)
    (_hSpan : PairAllWordsSpanTop A B)
    {start period : ℕ} (hperiod_pos : 0 < period)
    (hperiod : PairWordTupleSpanTop A B period)
    (hwindow : ∀ r : ℕ, r < period → PairWordTupleSpanTop A B (start + r)) :
    ∃ L : ℕ, ∀ n : ℕ, n ≥ L →
      ((1 : Matrix (Fin D₁) (Fin D₁) ℂ), (1 : Matrix (Fin D₂) (Fin D₂) ℂ)) ∈
        Submodule.span ℂ (Set.range (pairWordTuple A B n)) :=
  pairIdentity_mem_pairWordTupleSpan_eventually_of_pairWordTupleSpanTop_period_window
    A B hperiod_pos hperiod hwindow

/-- **Cumulative pair span ⇒ homogeneous pair span, conditional on identity padding.**

From a full cumulative pair span up to length `S` (`hCum`) and the
simultaneous pair identity `(1, 1)` lying in the homogeneous pair-word span
at length `T - l` for every `l ≤ S` (`hPad`), the homogeneous pair-word span
at length `T` is the full product algebra.

The identity-padding hypothesis `hPad` cannot be derived from `hCum` alone.
The section *The homogeneous padding point* in
`docs/paper-gaps/nonperiodic_mps_bnt_comparison_inputs.tex` records the
obstruction: take `d = 1` and `D₁ = D₂ = 1` with `A₀ = 2` and `B₀ = 3`.
The cumulative pair span through length one is all of `ℂ ⊕ ℂ`, since
`(1, 1)` (the empty word) and `(2, 3)` (the length-one word) are linearly
independent. At each positive homogeneous length `n`, however, the
pair-word span is the line through `(2ⁿ, 3ⁿ)`, which does not contain
`(1, 1)`. The cumulative-to-homogeneous implication is therefore false in
general, so the hypothesis here is genuinely needed.

The source paper (arXiv:1606.00608, lines 317–345) instead obtains a
homogeneous fixed-length span by a different construction: after `3 D⁵`
blockings, the canonical-form tensor is block-injective, in the sense
that its length-`L` word products span the full direct-sum matrix
algebra. The argument there combines the original `D⁴` quantum Wielandt
bound for normal tensors with the Pérez-García–Verstraete–Wolf–Cirac
block-injective bound. A sharper MPS-specific Wielandt bound
`2 D² (6 + log₂ D)` was later proved by Michalek and is recorded in
arXiv:2011.12127, lines 1942–1945. Either bound, combined with an
arithmetic period-window construction, yields the identity-padding
certificates required by `hPad`.

(Maintainer note.) The hypothesis is stated explicitly because the
Wielandt-bound construction is not formalized here. The auxiliary results
`exists_pairTraceSeparatingAt_of_not_gaugePhaseEquiv_of_pairWordTupleSpanTop_period_window`
(single-pair, same-dimension case) and
`exists_forall_pairTraceSeparatingAt_of_isCanonicalFormBNT_of_identity_period_windows`
(canonical-form BNT family) reduce the missing implication to a
period-window hypothesis on the homogeneous pair span. A formal
Wielandt-bound theorem would produce that period-window hypothesis from
the canonical-form hypotheses and thereby establish `hPad`. -/
theorem pairWordTupleSpanTop_of_pairCumulativeWordTupleSpanTop_of_identity_padding
    {D₁ D₂ : ℕ} (A : MPSTensor d D₁) (B : MPSTensor d D₂) {S T : ℕ}
    (hST : S ≤ T)
    (hCum : PairCumulativeWordTupleSpanTop A B S)
    (hPad : ∀ l : ℕ, l ≤ S →
      ((1 : Matrix (Fin D₁) (Fin D₁) ℂ), (1 : Matrix (Fin D₂) (Fin D₂) ℂ)) ∈
        Submodule.span ℂ (Set.range (pairWordTuple A B (T - l)))) :
    PairWordTupleSpanTop A B T := by
  classical
  unfold PairWordTupleSpanTop
  apply eq_top_iff.mpr
  intro M _
  have hM : M ∈ pairCumulativeSpan A B S := by
    rw [hCum]
    exact Submodule.mem_top
  suffices hle : pairCumulativeSpan A B S ≤
      Submodule.span ℂ (Set.range (pairWordTuple A B T)) from hle hM
  apply Submodule.span_le.mpr
  rintro N ⟨w, hwS, rfl⟩
  have hwT : w.length ≤ T := le_trans hwS hST
  have hword :
      pairEvalWordTuple A B w ∈
        Submodule.span ℂ (Set.range (pairWordTuple A B w.length)) :=
    pairEvalWordTuple_mem_span_pairWordTuple_length A B w
  have hmul :=
    pair_mul_mem_span_pairWordTuple_add (A := A) (B := B)
      (L := w.length) (S := T - w.length)
      (M := pairEvalWordTuple A B w)
      (N := ((1 : Matrix (Fin D₁) (Fin D₁) ℂ), (1 : Matrix (Fin D₂) (Fin D₂) ℂ)))
      hword (hPad w.length hwS)
  have hlen : w.length + (T - w.length) = T := Nat.add_sub_of_le hwT
  have hprod :
      ((pairEvalWordTuple A B w).1 * (1 : Matrix (Fin D₁) (Fin D₁) ℂ),
        (pairEvalWordTuple A B w).2 * (1 : Matrix (Fin D₂) (Fin D₂) ℂ)) =
        pairEvalWordTuple A B w := by
    ext <;> simp
  rw [hlen] at hmul
  simpa [hprod] using hmul

/-- Trace-separation version of
`pairWordTupleSpanTop_of_pairCumulativeWordTupleSpanTop_of_identity_padding`. -/
theorem pairTraceSeparatingAt_of_pairTraceSeparatingUpTo_of_identity_padding
    {D₁ D₂ : ℕ} (A : MPSTensor d D₁) (B : MPSTensor d D₂) {S T : ℕ}
    (hST : S ≤ T)
    (hSep : PairTraceSeparatingUpTo A B S)
    (hPad : ∀ l : ℕ, l ≤ S →
      ((1 : Matrix (Fin D₁) (Fin D₁) ℂ), (1 : Matrix (Fin D₂) (Fin D₂) ℂ)) ∈
        Submodule.span ℂ (Set.range (pairWordTuple A B (T - l)))) :
    PairTraceSeparatingAt A B T :=
  pairTraceSeparatingAt_of_pairWordTupleSpanTop A B
    (pairWordTupleSpanTop_of_pairCumulativeWordTupleSpanTop_of_identity_padding
      A B hST (pairCumulativeWordTupleSpanTop_of_pairTraceSeparatingUpTo A B hSep) hPad)

/-! ### Homogeneous separation from all-length hypotheses

The declarations in this subsection convert all-length or cumulative separation
to one homogeneous length only after an explicit homogeneous identity-padding
hypothesis has already been supplied. They do not supply the finite-length
direct-sum input used in the David/Perez-Garcia BNT argument. For that input,
BNT applications should use fixed-length or period-window hypotheses.
-/

/-- **Cumulative-to-homogeneous implication.** From cumulative pair trace
separation and eventual identity padding, obtain a homogeneous pair
trace-separating length.

The hypothesis `hIdentity_pad` supplies the identity padding needed to combine
the cumulative separation with
`pairTraceSeparatingAt_of_pairTraceSeparatingUpTo_of_identity_padding`. -/
theorem exists_pairTraceSeparatingAt_of_pairTraceSeparatingUpTo_of_eventual_identity_padding
    {d D₁ D₂ : ℕ} (A : MPSTensor d D₁) (B : MPSTensor d D₂) {S : ℕ}
    (hSepUpTo : PairTraceSeparatingUpTo A B S)
    (hIdentity_pad : ∃ L : ℕ, ∀ n : ℕ, n ≥ L →
      ((1 : Matrix (Fin D₁) (Fin D₁) ℂ), (1 : Matrix (Fin D₂) (Fin D₂) ℂ)) ∈
        Submodule.span ℂ (Set.range (pairWordTuple A B n))) :
    ∃ T : ℕ, PairTraceSeparatingAt A B T := by
  obtain ⟨L, hPadAll⟩ := hIdentity_pad
  refine ⟨L + S, ?_⟩
  exact pairTraceSeparatingAt_of_pairTraceSeparatingUpTo_of_identity_padding
    A B (S := S) (T := L + S) (by omega) hSepUpTo
    (fun l hl => hPadAll (L + S - l) (by omega))

/-- All-words pair separation plus eventual homogeneous identity padding gives
one homogeneous pair-trace separating length.

This is the proved interface between the pair-product algebra density theorem
(`PairAllWordsSpanTop`) and the Burnside-Jacobson identity-padding theorem.
It records that once the two independent inputs are available, no additional
BNT-specific argument is needed to obtain `PairTraceSeparatingAt`.

This lemma is conditional on identity padding; it is not the
David/Perez-Garcia direct-sum input. In BNT applications the homogeneous
padding must be supplied by a fixed-length or period-window hypothesis. -/
theorem exists_pairTraceSeparatingAt_of_pairAllWordsSpanTop_of_identity_padding
    {D₁ D₂ : ℕ} (A : MPSTensor d D₁) (B : MPSTensor d D₂)
    (hSpan : PairAllWordsSpanTop A B)
    (hPad : ∃ L : ℕ, ∀ n : ℕ, n ≥ L →
      ((1 : Matrix (Fin D₁) (Fin D₁) ℂ), (1 : Matrix (Fin D₂) (Fin D₂) ℂ)) ∈
        Submodule.span ℂ (Set.range (pairWordTuple A B n))) :
    ∃ T : ℕ, PairTraceSeparatingAt A B T := by
  have hSepAll : PairTraceSeparatingAll A B :=
    pairTraceSeparatingAll_of_pairAllWordsSpanTop A B hSpan
  obtain ⟨S, hSepUpTo⟩ :=
    exists_pairTraceSeparatingUpTo_of_pairTraceSeparatingAll A B hSepAll
  exact exists_pairTraceSeparatingAt_of_pairTraceSeparatingUpTo_of_eventual_identity_padding
    A B hSepUpTo hPad

/-- A finite family of all-words pair-separation hypotheses and eventual identity
padding hypotheses admits one common homogeneous trace-separating length.

For finitely many ordered pairs of blocks, if each pair has trace separation over all
word lengths and the pair identity belongs to every sufficiently long homogeneous
pair-word span, then one word length separates all ordered pairs simultaneously.

This finite-family statement is conditional on homogeneous identity padding; it
does not supply the finite-length direct-sum input. -/
theorem exists_forall_pairTraceSeparatingAt_of_pairTraceSeparatingAll_of_identity_padding
    (A : (k : Fin r) → MPSTensor d (dim k))
    (hSep : ∀ k j : Fin r, j ≠ k → PairTraceSeparatingAll (A k) (A j))
    (hPad : ∀ k j : Fin r, j ≠ k → ∃ L : ℕ, ∀ n : ℕ, n ≥ L →
      ((1 : Matrix (Fin (dim k)) (Fin (dim k)) ℂ),
          (1 : Matrix (Fin (dim j)) (Fin (dim j)) ℂ)) ∈
        Submodule.span ℂ (Set.range (pairWordTuple (A k) (A j) n))) :
    ∃ T : ℕ, ∀ k j : Fin r, j ≠ k → PairTraceSeparatingAt (A k) (A j) T := by
  classical
  obtain ⟨S, hSepUpTo⟩ :=
    exists_forall_pairTraceSeparatingUpTo_of_forall_pairTraceSeparatingAll A hSep
  let Lij : Fin r × Fin r → ℕ := fun p =>
    if h : p.2 ≠ p.1 then Classical.choose (hPad p.1 p.2 h) else 0
  let L : ℕ := Finset.univ.sup Lij
  refine ⟨L + S, ?_⟩
  intro k j hjk
  have hPadBase : ∀ n : ℕ, n ≥ Lij (k, j) →
      ((1 : Matrix (Fin (dim k)) (Fin (dim k)) ℂ),
          (1 : Matrix (Fin (dim j)) (Fin (dim j)) ℂ)) ∈
        Submodule.span ℂ (Set.range (pairWordTuple (A k) (A j) n)) := by
    simpa [Lij, hjk] using Classical.choose_spec (hPad k j hjk)
  have hLij_le : Lij (k, j) ≤ L := by
    exact Finset.le_sup (s := Finset.univ) (f := Lij) (Finset.mem_univ (k, j))
  exact pairTraceSeparatingAt_of_pairTraceSeparatingUpTo_of_identity_padding
    (A k) (A j) (S := S) (T := L + S) (by omega) (hSepUpTo k j hjk)
    (fun l hl => hPadBase (L + S - l) (by omega))

end MPSTensor
