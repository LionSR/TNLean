/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.MPDO.BiCFDerivation.Core

/-!
# Pair-span homogenization for MPDO biCF

This module contains the homogeneous pair-span padding criteria and the
Burnside-Jacobson pair-algebra placeholders used to turn all-length pair trace
separation into a fixed homogeneous word length.
-/

open scoped Matrix BigOperators

namespace MPSTensor

variable {d : ℕ} {r : ℕ} {dim : Fin r → ℕ}

/-! ### Homogenizing cumulative pair spans -/

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

/-- A cumulative pair span can be homogenized once the simultaneous pair identity
is available at every padding length needed to reach the target length.

The padding hypothesis is the Burnside-Jacobson input deferred to a later step. -/
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

/-! ### Burnside–Jacobson homogenization: from non-equivalence to homogeneous separation

The theorems in this section bridge the gap between BNT block non-equivalence
(`¬ GaugePhaseEquiv A B` for injective blocks) and the existence of a homogeneous
length `T` at which `PairTraceSeparatingAt A B T` holds.

**Route A (spectral):**
`¬ GaugePhaseEquiv` → `spectralRadius(mixedTransfer) < 1` → `mpvOverlap → 0`.
This is the non-decaying overlap argument from the spectral-gap development.

**Route B (algebraic, this section):**
`¬ GaugePhaseEquiv` → `PairTraceSeparatingAll A B` → cumulative finite cutoff
→ homogenization via identity padding.  The identity-padding input is the
remaining Burnside–Jacobson algebraic step deferred to the pair algebra.
-/

/-- **BNT non-equivalence ⇒ all-length pair trace separation.**
For injective, left-canonical tensors `A, B` of the same dimension that are
not gauge-phase-equivalent, no nonzero pair of test matrices `(ΔA, ΔB)` can
annihilate the pair-trace pairing `tr(ΔA·evalWord A w) + tr(ΔB·evalWord B w)`
for all words `w`.

The proof should analyze the pair product algebra
`S := alg{(Aᵢ, Bᵢ) | i}` inside `M_{D}(ℂ) × M_{D}(ℂ)`.  Because `A` and `B`
are individually injective, the two coordinate projections of `S` are the full
matrix algebra.  A subdirect-product argument then leaves two possibilities:
either a coordinate kernel supplies the two axes and hence `S = M_D × M_D`, or
`S` is the graph of an algebra automorphism of `M_D`.  In the graph case,
Skolem–Noether turns the automorphism into a gauge equivalence, contradicting
the non-gauge-equivalence hypothesis.  The full-product conclusion is exactly
the statement that the pair word tuples over all word lengths span the full
product algebra.  By duality this is `PairTraceSeparatingAll`.

**Remaining formal gap (Burnside–Jacobson for the product algebra):**
The core algebraic step — that the subalgebra `A` of `M_D × M_D` generated by
`{(A_i, B_i)}` equals the full product algebra whenever the two injective
blocks are non-gauge-equivalent — is admitted below as `sorry` (the pair‑Burnside
lemma).  Once that lemma is proved, `exists_pairTraceSeparatingAt_of_not_gaugePhaseEquiv`
completes the homogenization chain. -/
theorem pairTraceSeparatingAll_of_injective_not_gaugePhaseEquiv
    {d D : ℕ} [NeZero D]
    (A B : MPSTensor d D)
    (hA_inj : IsInjective A) (hB_inj : IsInjective B)
    (hA_norm : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hB_norm : ∑ i : Fin d, (B i)ᴴ * B i = 1)
    (hNot : ¬ GaugePhaseEquiv A B) :
    PairTraceSeparatingAll A B := by
  -- Step 0: non-gauge-equivalence ⇒ the pair product algebra is the full M_D × M_D.
  -- This is the Burnside/Jacobson step for the pair product algebra; formal proof pending.
  have hPairSpanTop : PairAllWordsSpanTop A B := by
    -- The pair product algebra generated by {(A_i, B_i)} equals M_D × M_D.
    -- The planned proof is a subdirect-product argument: injectivity of the two
    -- blocks makes both coordinate projections full; non-fullness would force
    -- the subalgebra to be the graph of an algebra automorphism of M_D; and
    -- Skolem–Noether would turn that graph into `GaugePhaseEquiv A B`.
    sorry
  -- Step 1: duality ⇒ all-length trace separation
  exact pairTraceSeparatingAll_of_pairAllWordsSpanTop A B hPairSpanTop

/-- Placeholder for the Burnside–Jacobson identity-padding lemma.
Once proved, it supplies the missing input to
`pairTraceSeparatingAt_of_pairTraceSeparatingUpTo_of_identity_padding` and
thereby completes `exists_pairTraceSeparatingAt_of_not_gaugePhaseEquiv`.

The statement: for injective, non-gauge-equivalent tensors `A, B`, there
exists `L` such that the pair identity `(1, 1)` belongs to the homogeneous
pair word span at every length `≥ L` (or at least at an arithmetic progression
that covers all offsets needed for the padding argument). -/
theorem pairIdentity_mem_pairWordTupleSpan_eventually_of_not_gaugePhaseEquiv
    {d D : ℕ} [NeZero D]
    (A B : MPSTensor d D)
    (hA_inj : IsInjective A) (hB_inj : IsInjective B)
    (hNot : ¬ GaugePhaseEquiv A B) :
    ∃ L : ℕ, ∀ n : ℕ, n ≥ L →
      ((1 : Matrix (Fin D) (Fin D) ℂ), (1 : Matrix (Fin D) (Fin D) ℂ)) ∈
        Submodule.span ℂ (Set.range (pairWordTuple A B n)) := by
  sorry

/-- **Homogeneous pair trace separation from BNT non-equivalence (Route B).**
Under the same hypotheses, there exists a finite homogeneous length `S` such
that `PairTraceSeparatingAt A B S` holds.

The proof chains:
1. `¬ GaugePhaseEquiv` → `PairTraceSeparatingAll` (the lemma above)
2. `PairTraceSeparatingAll` → finite cumulative cutoff `S₀`
3. `PairTraceSeparatingUpTo` + Burnside–Jacobson identity padding
   → homogeneous `PairTraceSeparatingAt T`

The remaining blocker for step 3 is the identity-padding hypothesis: there
must exist a length `L` such that `(1, 1)` lies in the homogeneous pair word
span at every length `≥ L`.  This is the Burnside–Jacobson homogenization
step for the pair product algebra.  The theorem below states the full
conclusion with that step admitted. -/
theorem exists_pairTraceSeparatingAt_of_not_gaugePhaseEquiv
    {d D : ℕ} [NeZero D]
    (A B : MPSTensor d D)
    (hA_inj : IsInjective A) (hB_inj : IsInjective B)
    (hA_norm : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hB_norm : ∑ i : Fin d, (B i)ᴴ * B i = 1)
    (hNot : ¬ GaugePhaseEquiv A B) :
    ∃ T : ℕ, PairTraceSeparatingAt A B T := by
  -- Step 1: non-gauge-equivalence ⇒ all-length separation
  have hSepAll : PairTraceSeparatingAll A B :=
    pairTraceSeparatingAll_of_injective_not_gaugePhaseEquiv
      A B hA_inj hB_inj hA_norm hB_norm hNot
  -- Step 2: finite cumulative cutoff (Noetherian chain stabilization)
  obtain ⟨S, hSepUpTo⟩ := exists_pairTraceSeparatingUpTo_of_pairTraceSeparatingAll A B hSepAll
  -- Step 3: homogenize via identity padding.
  obtain ⟨L, hPadAll⟩ :=
    pairIdentity_mem_pairWordTupleSpan_eventually_of_not_gaugePhaseEquiv
      A B hA_inj hB_inj hNot
  refine ⟨L + S, ?_⟩
  exact pairTraceSeparatingAt_of_pairTraceSeparatingUpTo_of_identity_padding
    A B (S := S) (T := L + S) (by omega) hSepUpTo
    (fun l hl => hPadAll (L + S - l) (by omega))

end MPSTensor
