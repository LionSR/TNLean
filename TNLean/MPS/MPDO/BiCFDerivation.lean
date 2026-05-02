/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.MPDO.VerticalCF
import TNLean.PiAlgebra.Construction
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Prod
import Mathlib.RingTheory.Noetherian.Defs

/-!
# Finite-length sufficient conditions and obstructions for MPDO biCF

The `HorizontalCFData` structure in `VerticalCF.lean` states the block-injective
canonical-form property `biCF` as a hypothesis. This file states six complementary
facts about that field.

1. A clean **abstract sufficient condition**: if, after blocking to some fixed
   length `L`, the word-evaluation tuples
   `w ↦ (k ↦ evalWord (A k) (List.ofFn w))`
   span the full product algebra `∀ k, Matrix (Fin (dim k)) (Fin (dim k)) ℂ`,
   then the `biCF` conclusion follows from nondegeneracy of the product trace
   pairing.

2. A finite-dimensional **linear-independence criterion**: if the scalar word-entry
   family obtained by reading off every block matrix entry is linearly
   independent, then those tuple-valued word evaluations already span the full
   product algebra. This reduces biCF to a concrete linear-algebra condition.

3. An abstract **Proposition IV.3-style selector data criterion**: if each block is
   block-injective at some common length and a second finite family of words
   isolates the individual blocks (identity on one block, zero on the others),
   then concatenating the two families yields the preceding span condition.
   This captures the finite-length block-separation content of
   [CPGSV17], Proposition IV.3.

4. A **pairwise-to-global selector reduction**: if every ordered pair of
   distinct blocks admits a finite word polynomial that is the identity on the
   first block and zero on the second, then multiplying these pairwise
   separators gives full block-selector words.

5. A finite-dimensional **cumulative pair trace criterion**: if no nonzero pair
   trace functional vanishes on all finite pair words, then a finite cumulative
   word-length bound already detects every nonzero test pair.

6. A concrete **counterexample**: blockwise injectivity, left-canonical
   normalization, nonzero weights, and even pairwise distinct weights do **not**
   imply `biCF`. Thus the current `HorizontalCFData` fields other than `biCF`
   are insufficient for deriving that property.

This isolates the missing ingredient more precisely: one still needs a proved
finite-length block-separation theorem producing either the pairwise separators
of item (4), the selector data of item (3), or equivalently the word-entry
linear independence of item (2), from canonical-form/BNT data.
-/

open scoped Matrix BigOperators

namespace MPSTensor

variable {d : ℕ} {r : ℕ} {dim : Fin r → ℕ}

/-- The tuple of length-`L` word evaluations across all blocks. -/
def wordTuple
    (A : (k : Fin r) → MPSTensor d (dim k))
    (L : ℕ) (w : Fin L → Fin d) :
    (k : Fin r) → Matrix (Fin (dim k)) (Fin (dim k)) ℂ :=
  fun k => evalWord (A k) (List.ofFn w)

/-- Finite-length span condition on the product algebra of block matrices. -/
def WordTupleSpanTop
    (A : (k : Fin r) → MPSTensor d (dim k))
    (L : ℕ) : Prop :=
  Submodule.span ℂ (Set.range (wordTuple A L)) = ⊤

/-- Index type for a matrix entry inside a block family. -/
abbrev BlockEntryIndex (dim : Fin r → ℕ) :=
  Σ k : Fin r, Fin (dim k) × Fin (dim k)

/-- The value of a tuple of block matrices at a chosen block entry. -/
def blockEntryValue
    (M : (k : Fin r) → Matrix (Fin (dim k)) (Fin (dim k)) ℂ)
    (x : BlockEntryIndex dim) : ℂ :=
  M x.1 x.2.1 x.2.2

/-- The scalar word family obtained by reading off one chosen matrix entry of the
block-word tuple. -/
def wordEntryFamily
    (A : (k : Fin r) → MPSTensor d (dim k))
    (L : ℕ) : BlockEntryIndex dim → (Fin L → Fin d) → ℂ :=
  fun x w => blockEntryValue (wordTuple A L w) x

/-- The block-injective canonical-form property used by `HorizontalCFData`. -/
def HasBiCF
    (A : (k : Fin r) → MPSTensor d (dim k)) : Prop :=
  ∃ L : ℕ, ∀ (Δ : (k : Fin r) → Matrix (Fin (dim k)) (Fin (dim k)) ℂ),
    (∀ w : Fin L → Fin d,
        (∑ k : Fin r, Matrix.trace (Δ k * evalWord (A k) (List.ofFn w))) = 0) →
    ∀ k, Δ k = 0

/-- A finite-length spanning hypothesis implies `HasBiCF`. -/
theorem hasBiCF_of_wordTupleSpanTop
    (A : (k : Fin r) → MPSTensor d (dim k))
    {L : ℕ} (hSpan : WordTupleSpanTop A L) :
    HasBiCF A := by
  refine ⟨L, ?_⟩
  intro Δ hΔ
  have hΔzero : Δ = 0 := by
    apply piTrace_mul_right_eq_zero
    intro N
    have hZeroOnSpan :
        ∀ M : (k : Fin r) → Matrix (Fin (dim k)) (Fin (dim k)) ℂ,
          M ∈ Submodule.span ℂ (Set.range (wordTuple A L)) →
          (∑ k : Fin r, Matrix.trace (Δ k * M k)) = 0 := by
      intro M hM
      exact Submodule.span_induction (p := fun x _ =>
          (∑ k : Fin r, Matrix.trace (Δ k * x k)) = 0)
        (fun x hx => by
          rcases hx with ⟨w, rfl⟩
          simpa [wordTuple] using hΔ w)
        (by simp)
        (fun x y hx hy hxzero hyzero => by
          simp [Matrix.mul_add, Matrix.trace_add, hxzero, hyzero, Finset.sum_add_distrib])
        (fun a x hx hxzero => by
          simpa [Pi.smul_apply, Matrix.mul_smul, Matrix.trace_smul, Finset.mul_sum] using
            congrArg (fun z : ℂ => a * z) hxzero)
        hM
    exact hZeroOnSpan N (by rw [hSpan]; exact Submodule.mem_top)
  intro k
  simpa using congrArg (fun f => f k) hΔzero

/-- A finite family of words which isolates each block: for every `k`, one can
form a linear combination of those word evaluations that equals the identity on
block `k` and vanishes on all other blocks. -/
def HasBlockSelectorWords
    (A : (k : Fin r) → MPSTensor d (dim k))
    (S : ℕ) : Prop :=
  ∀ k : Fin r, ∃ c : (Fin S → Fin d) → ℂ,
    (∑ w : Fin S → Fin d, c w • evalWord (A k) (List.ofFn w)) = 1 ∧
    ∀ j : Fin r, j ≠ k →
      (∑ w : Fin S → Fin d, c w • evalWord (A j) (List.ofFn w)) = 0

/-- A length-`S` word polynomial which selects block `k` on a finite set of
other blocks. The tuple `M` lies in the span of simultaneous length-`S` word
evaluations, is the identity on `k`, and vanishes on every block in `targets`.

Taking `targets = Finset.univ.erase k` is the tuple-span form used to recover
coefficient-based `HasBlockSelectorWords`. Smaller target sets are useful for
assembling global selectors from pairwise block-separating word polynomials. -/
def HasBlockSelectorOn
    (A : (k : Fin r) → MPSTensor d (dim k))
    (k : Fin r) (S : ℕ) (targets : Finset (Fin r)) : Prop :=
  ∃ M : (j : Fin r) → Matrix (Fin (dim j)) (Fin (dim j)) ℂ,
    M ∈ Submodule.span ℂ (Set.range (wordTuple A S)) ∧
      M k = 1 ∧
      ∀ j : Fin r, j ∈ targets → M j = 0

/-- Pairwise finite block separation: for each ordered pair of distinct blocks,
there is a length-`S` word polynomial that is the identity on the first block
and zero on the second. -/
def HasPairBlockSeparatingWords
    (A : (k : Fin r) → MPSTensor d (dim k))
    (S : ℕ) : Prop :=
  ∀ k j : Fin r, j ≠ k → HasBlockSelectorOn A k S {j}

/-- The simultaneous length-`S` word evaluation of two blocks. -/
def pairWordTuple {D₁ D₂ : ℕ}
    (A : MPSTensor d D₁) (B : MPSTensor d D₂)
    (S : ℕ) (w : Fin S → Fin d) :
    Matrix (Fin D₁) (Fin D₁) ℂ × Matrix (Fin D₂) (Fin D₂) ℂ :=
  (evalWord A (List.ofFn w), evalWord B (List.ofFn w))

/-- Finite-length product-algebra span for a single ordered pair of blocks. -/
def PairWordTupleSpanTop {D₁ D₂ : ℕ}
    (A : MPSTensor d D₁) (B : MPSTensor d D₂) (S : ℕ) : Prop :=
  Submodule.span ℂ (Set.range (pairWordTuple A B S)) = ⊤

/-- Dual trace-separation criterion for a single ordered pair of blocks at a fixed
length.

This is the homogeneous finite-dimensional dual of pair product-span: no nonzero
pair of trace test matrices may annihilate all simultaneous length-`S` word
pairs.  The remaining BNT step is to prove such a finite `S` from block
non-equivalence. -/
def PairTraceSeparatingAt {D₁ D₂ : ℕ}
    (A : MPSTensor d D₁) (B : MPSTensor d D₂) (S : ℕ) : Prop :=
  ∀ ΔA : Matrix (Fin D₁) (Fin D₁) ℂ,
    ∀ ΔB : Matrix (Fin D₂) (Fin D₂) ℂ,
      (∀ w : Fin S → Fin d,
        Matrix.trace (ΔA * evalWord A (List.ofFn w)) +
          Matrix.trace (ΔB * evalWord B (List.ofFn w)) = 0) →
      ΔA = 0 ∧ ΔB = 0

/-- The simultaneous word evaluation of two blocks for an arbitrary finite word. -/
def pairEvalWordTuple {D₁ D₂ : ℕ}
    (A : MPSTensor d D₁) (B : MPSTensor d D₂)
    (w : List (Fin d)) :
    Matrix (Fin D₁) (Fin D₁) ℂ × Matrix (Fin D₂) (Fin D₂) ℂ :=
  (evalWord A w, evalWord B w)

/-- The cumulative span of pair word tuples of length at most `S`. -/
noncomputable def pairCumulativeSpan {D₁ D₂ : ℕ}
    (A : MPSTensor d D₁) (B : MPSTensor d D₂) (S : ℕ) :
    Submodule ℂ (Matrix (Fin D₁) (Fin D₁) ℂ × Matrix (Fin D₂) (Fin D₂) ℂ) :=
  Submodule.span ℂ
    {M | ∃ w : List (Fin d), w.length ≤ S ∧ M = pairEvalWordTuple A B w}

/-- Finite cumulative pair product-span: pair word tuples of length at most `S`
span the full product matrix algebra. -/
def PairCumulativeWordTupleSpanTop {D₁ D₂ : ℕ}
    (A : MPSTensor d D₁) (B : MPSTensor d D₂) (S : ℕ) : Prop :=
  pairCumulativeSpan A B S = ⊤

/-- Trace-separation by all pair word tuples of length at most `S`.

This finite cutoff form is weaker than the homogeneous criterion
`PairTraceSeparatingAt`, but it is the exact finite-dimensional consequence of
ruling out trace functionals that vanish on all word lengths. -/
def PairTraceSeparatingUpTo {D₁ D₂ : ℕ}
    (A : MPSTensor d D₁) (B : MPSTensor d D₂) (S : ℕ) : Prop :=
  ∀ ΔA : Matrix (Fin D₁) (Fin D₁) ℂ,
    ∀ ΔB : Matrix (Fin D₂) (Fin D₂) ℂ,
      (∀ w : List (Fin d), w.length ≤ S →
        Matrix.trace (ΔA * evalWord A w) +
          Matrix.trace (ΔB * evalWord B w) = 0) →
      ΔA = 0 ∧ ΔB = 0

/-- Infinite trace-separation by pair word tuples of all finite lengths. -/
def PairTraceSeparatingAll {D₁ D₂ : ℕ}
    (A : MPSTensor d D₁) (B : MPSTensor d D₂) : Prop :=
  ∀ ΔA : Matrix (Fin D₁) (Fin D₁) ℂ,
    ∀ ΔB : Matrix (Fin D₂) (Fin D₂) ℂ,
      (∀ w : List (Fin d),
        Matrix.trace (ΔA * evalWord A w) +
          Matrix.trace (ΔB * evalWord B w) = 0) →
      ΔA = 0 ∧ ΔB = 0

/-- The span of pair word tuples over all finite words. -/
noncomputable def pairAllWordsSpan {D₁ D₂ : ℕ}
    (A : MPSTensor d D₁) (B : MPSTensor d D₂) :
    Submodule ℂ (Matrix (Fin D₁) (Fin D₁) ℂ × Matrix (Fin D₂) (Fin D₂) ℂ) :=
  Submodule.span ℂ (Set.range (pairEvalWordTuple A B))

/-- All finite pair word tuples span the full product matrix algebra. -/
def PairAllWordsSpanTop {D₁ D₂ : ℕ}
    (A : MPSTensor d D₁) (B : MPSTensor d D₂) : Prop :=
  pairAllWordsSpan A B = ⊤

/-- Membership of a pair word tuple in the cumulative pair span. -/
theorem pairEvalWordTuple_mem_pairCumulativeSpan {D₁ D₂ : ℕ}
    (A : MPSTensor d D₁) (B : MPSTensor d D₂)
    {w : List (Fin d)} {S : ℕ} (hw : w.length ≤ S) :
    pairEvalWordTuple A B w ∈ pairCumulativeSpan A B S :=
  Submodule.subset_span ⟨w, hw, rfl⟩

/-- Cumulative pair spans are monotone in the cutoff. -/
theorem pairCumulativeSpan_mono {D₁ D₂ : ℕ}
    (A : MPSTensor d D₁) (B : MPSTensor d D₂)
    {S T : ℕ} (hST : S ≤ T) :
    pairCumulativeSpan A B S ≤ pairCumulativeSpan A B T := by
  apply Submodule.span_mono
  rintro M ⟨w, hw, rfl⟩
  exact ⟨w, le_trans hw hST, rfl⟩

/-- Cumulative trace separation is monotone in the cutoff. -/
theorem PairTraceSeparatingUpTo.mono {D₁ D₂ : ℕ}
    {A : MPSTensor d D₁} {B : MPSTensor d D₂}
    {S T : ℕ} (hSep : PairTraceSeparatingUpTo A B S) (hST : S ≤ T) :
    PairTraceSeparatingUpTo A B T := by
  intro ΔA ΔB hΔ
  exact hSep ΔA ΔB (fun w hw => hΔ w (le_trans hw hST))

/-- Homogeneous trace separation implies cumulative trace separation at the same cutoff. -/
theorem pairTraceSeparatingUpTo_of_pairTraceSeparatingAt {D₁ D₂ : ℕ}
    (A : MPSTensor d D₁) (B : MPSTensor d D₂) {S : ℕ}
    (hSep : PairTraceSeparatingAt A B S) :
    PairTraceSeparatingUpTo A B S := by
  intro ΔA ΔB hΔ
  exact hSep ΔA ΔB (fun w => by
    simpa using hΔ (List.ofFn w) (by simp))

private theorem exists_trace_repr {n : Type*} [Fintype n]
    (f : Matrix n n ℂ →ₗ[ℂ] ℂ) :
    ∃ Δ : Matrix n n ℂ, ∀ M : Matrix n n ℂ, f M = Matrix.trace (Δ * M) := by
  classical
  let Δ : Matrix n n ℂ := fun p q => f (Matrix.single q p (1 : ℂ))
  refine ⟨Δ, ?_⟩
  have hfg : f = (Matrix.traceLinearMap n ℂ ℂ).comp (LinearMap.mulLeft ℂ Δ) := by
    apply Matrix.ext_linearMap ℂ
    intro i j
    apply LinearMap.ext
    intro a
    simp only [LinearMap.comp_apply, Matrix.singleLinearMap_apply,
      Matrix.traceLinearMap_apply, LinearMap.mulLeft_apply]
    have hsingle : Matrix.single i j a = a • Matrix.single i j (1 : ℂ) := by
      ext p q
      by_cases hp : p = i <;> by_cases hq : q = j <;> simp [Matrix.single, hp, hq]
    calc
      f (Matrix.single i j a) = a * f (Matrix.single i j (1 : ℂ)) := by
        rw [hsingle, map_smul]
        rfl
      _ = Matrix.trace (Δ * Matrix.single i j a) := by
        rw [Matrix.trace_mul_single]
        simp [Δ, mul_comm]
  intro M
  simp [hfg]

private theorem exists_pair_trace_repr {m n : Type*} [Fintype m] [Fintype n]
    (f : (Matrix m m ℂ × Matrix n n ℂ) →ₗ[ℂ] ℂ) :
    ∃ ΔA : Matrix m m ℂ, ∃ ΔB : Matrix n n ℂ,
      ∀ M : Matrix m m ℂ × Matrix n n ℂ,
        f M = Matrix.trace (ΔA * M.1) + Matrix.trace (ΔB * M.2) := by
  classical
  obtain ⟨ΔA, hA⟩ := exists_trace_repr
    (f.comp (LinearMap.inl ℂ (Matrix m m ℂ) (Matrix n n ℂ)))
  obtain ⟨ΔB, hB⟩ := exists_trace_repr
    (f.comp (LinearMap.inr ℂ (Matrix m m ℂ) (Matrix n n ℂ)))
  refine ⟨ΔA, ΔB, ?_⟩
  intro M
  calc
    f M = ((f.comp (LinearMap.inl ℂ (Matrix m m ℂ) (Matrix n n ℂ))).coprod
        (f.comp (LinearMap.inr ℂ (Matrix m m ℂ) (Matrix n n ℂ)))) M := by
      exact (congrArg
        (fun g : (Matrix m m ℂ × Matrix n n ℂ) →ₗ[ℂ] ℂ => g M)
        (LinearMap.coprod_comp_inl_inr f)).symm
    _ = Matrix.trace (ΔA * M.1) + Matrix.trace (ΔB * M.2) := by
      rw [LinearMap.coprod_apply]
      change (f.comp (LinearMap.inl ℂ (Matrix m m ℂ) (Matrix n n ℂ))) M.1 +
          (f.comp (LinearMap.inr ℂ (Matrix m m ℂ) (Matrix n n ℂ))) M.2 = _
      rw [hA M.1, hB M.2]

private theorem pair_trace_zero_on_span {D₁ D₂ : ℕ}
    {Ω : Set (Matrix (Fin D₁) (Fin D₁) ℂ × Matrix (Fin D₂) (Fin D₂) ℂ)}
    (ΔA : Matrix (Fin D₁) (Fin D₁) ℂ)
    (ΔB : Matrix (Fin D₂) (Fin D₂) ℂ)
    (hΩ : ∀ M ∈ Ω, Matrix.trace (ΔA * M.1) + Matrix.trace (ΔB * M.2) = 0) :
    ∀ M : Matrix (Fin D₁) (Fin D₁) ℂ × Matrix (Fin D₂) (Fin D₂) ℂ,
      M ∈ Submodule.span ℂ Ω →
        Matrix.trace (ΔA * M.1) + Matrix.trace (ΔB * M.2) = 0 := by
  intro M hM
  induction hM using Submodule.span_induction with
  | mem M hMmem =>
      exact hΩ M hMmem
  | zero => simp
  | add M N _ _ hM hN =>
      calc
        Matrix.trace (ΔA * (M + N).1) + Matrix.trace (ΔB * (M + N).2)
            = (Matrix.trace (ΔA * M.1) + Matrix.trace (ΔB * M.2)) +
                (Matrix.trace (ΔA * N.1) + Matrix.trace (ΔB * N.2)) := by
              simp [Matrix.mul_add, Matrix.trace_add, add_assoc, add_left_comm]
        _ = 0 := by simp [hM, hN]
  | smul a M _ hM =>
      calc
        Matrix.trace (ΔA * (a • M).1) + Matrix.trace (ΔB * (a • M).2)
            = a * (Matrix.trace (ΔA * M.1) + Matrix.trace (ΔB * M.2)) := by
              simp [Matrix.trace_smul, mul_add]
        _ = 0 := by simp [hM]

/-- The pair trace-separation criterion is the dual form of pair product-span. -/
theorem pairWordTupleSpanTop_of_pairTraceSeparatingAt {D₁ D₂ : ℕ}
    (A : MPSTensor d D₁) (B : MPSTensor d D₂) {S : ℕ}
    (hSep : PairTraceSeparatingAt A B S) :
    PairWordTupleSpanTop A B S := by
  classical
  unfold PairWordTupleSpanTop
  by_contra hnot
  let W : Submodule ℂ
      (Matrix (Fin D₁) (Fin D₁) ℂ × Matrix (Fin D₂) (Fin D₂) ℂ) :=
    Submodule.span ℂ (Set.range (pairWordTuple A B S))
  have hlt : W < ⊤ := lt_of_le_of_ne le_top (by simpa [W] using hnot)
  obtain ⟨f, hfne, hfker⟩ := Submodule.exists_le_ker_of_lt_top W hlt
  obtain ⟨ΔA, ΔB, hf_repr⟩ := exists_pair_trace_repr f
  have hΔ : ΔA = 0 ∧ ΔB = 0 := by
    refine hSep ΔA ΔB ?_
    intro w
    have hwmem : pairWordTuple A B S w ∈ W :=
      Submodule.subset_span ⟨w, rfl⟩
    have hf0 : f (pairWordTuple A B S w) = 0 := hfker hwmem
    simpa [pairWordTuple, hf_repr] using hf0
  have hfzero : f = 0 := by
    apply LinearMap.ext
    intro M
    have hM := hf_repr M
    rw [hΔ.1, hΔ.2] at hM
    simpa using hM
  exact hfne hfzero

/-- Homogeneous pair product-span gives homogeneous trace separation. -/
theorem pairTraceSeparatingAt_of_pairWordTupleSpanTop {D₁ D₂ : ℕ}
    (A : MPSTensor d D₁) (B : MPSTensor d D₂) {S : ℕ}
    (hSpan : PairWordTupleSpanTop A B S) :
    PairTraceSeparatingAt A B S := by
  classical
  intro ΔA ΔB hΔ
  have hZeroOnSpan :
      ∀ M : Matrix (Fin D₁) (Fin D₁) ℂ × Matrix (Fin D₂) (Fin D₂) ℂ,
        M ∈ Submodule.span ℂ (Set.range (pairWordTuple A B S)) →
          Matrix.trace (ΔA * M.1) + Matrix.trace (ΔB * M.2) = 0 := by
    intro M hM
    exact pair_trace_zero_on_span ΔA ΔB
      (Ω := Set.range (pairWordTuple A B S))
      (by
        rintro M ⟨w, rfl⟩
        exact hΔ w)
      M hM
  constructor
  · apply trace_mul_right_eq_zero
    intro M
    have hpair := hZeroOnSpan (M, 0) (by rw [hSpan]; exact Submodule.mem_top)
    simpa using hpair
  · apply trace_mul_right_eq_zero
    intro N
    have hpair := hZeroOnSpan (0, N) (by rw [hSpan]; exact Submodule.mem_top)
    simpa using hpair

/-- Homogeneous pair product-span is equivalent to homogeneous trace separation. -/
theorem pairWordTupleSpanTop_iff_pairTraceSeparatingAt {D₁ D₂ : ℕ}
    (A : MPSTensor d D₁) (B : MPSTensor d D₂) {S : ℕ} :
    PairWordTupleSpanTop A B S ↔ PairTraceSeparatingAt A B S :=
  ⟨pairTraceSeparatingAt_of_pairWordTupleSpanTop A B,
    pairWordTupleSpanTop_of_pairTraceSeparatingAt A B⟩

/-- Cumulative trace separation is the dual form of cumulative pair product-span. -/
theorem pairCumulativeWordTupleSpanTop_of_pairTraceSeparatingUpTo {D₁ D₂ : ℕ}
    (A : MPSTensor d D₁) (B : MPSTensor d D₂) {S : ℕ}
    (hSep : PairTraceSeparatingUpTo A B S) :
    PairCumulativeWordTupleSpanTop A B S := by
  classical
  unfold PairCumulativeWordTupleSpanTop
  by_contra hnot
  let W : Submodule ℂ
      (Matrix (Fin D₁) (Fin D₁) ℂ × Matrix (Fin D₂) (Fin D₂) ℂ) :=
    pairCumulativeSpan A B S
  have hlt : W < ⊤ := lt_of_le_of_ne le_top (by simpa [W] using hnot)
  obtain ⟨f, hfne, hfker⟩ := Submodule.exists_le_ker_of_lt_top W hlt
  obtain ⟨ΔA, ΔB, hf_repr⟩ := exists_pair_trace_repr f
  have hΔ : ΔA = 0 ∧ ΔB = 0 := by
    refine hSep ΔA ΔB ?_
    intro w hw
    have hwmem : pairEvalWordTuple A B w ∈ W :=
      pairEvalWordTuple_mem_pairCumulativeSpan A B hw
    have hf0 : f (pairEvalWordTuple A B w) = 0 := hfker hwmem
    simpa [pairEvalWordTuple, hf_repr] using hf0
  have hfzero : f = 0 := by
    apply LinearMap.ext
    intro M
    have hM := hf_repr M
    rw [hΔ.1, hΔ.2] at hM
    simpa using hM
  exact hfne hfzero

/-- Cumulative pair product-span gives cumulative trace separation. -/
theorem pairTraceSeparatingUpTo_of_pairCumulativeWordTupleSpanTop {D₁ D₂ : ℕ}
    (A : MPSTensor d D₁) (B : MPSTensor d D₂) {S : ℕ}
    (hSpan : PairCumulativeWordTupleSpanTop A B S) :
    PairTraceSeparatingUpTo A B S := by
  classical
  intro ΔA ΔB hΔ
  have hZeroOnSpan :
      ∀ M : Matrix (Fin D₁) (Fin D₁) ℂ × Matrix (Fin D₂) (Fin D₂) ℂ,
        M ∈ pairCumulativeSpan A B S →
          Matrix.trace (ΔA * M.1) + Matrix.trace (ΔB * M.2) = 0 := by
    intro M hM
    exact pair_trace_zero_on_span ΔA ΔB
      (Ω := {M | ∃ w : List (Fin d), w.length ≤ S ∧ M = pairEvalWordTuple A B w})
      (by
        rintro M ⟨w, hw, rfl⟩
        exact hΔ w hw)
      M (by simpa [pairCumulativeSpan] using hM)
  constructor
  · apply trace_mul_right_eq_zero
    intro M
    have hpair := hZeroOnSpan (M, 0) (by rw [hSpan]; exact Submodule.mem_top)
    simpa using hpair
  · apply trace_mul_right_eq_zero
    intro N
    have hpair := hZeroOnSpan (0, N) (by rw [hSpan]; exact Submodule.mem_top)
    simpa using hpair

/-- Cumulative trace separation is equivalent to cumulative pair product-span. -/
theorem pairCumulativeWordTupleSpanTop_iff_pairTraceSeparatingUpTo {D₁ D₂ : ℕ}
    (A : MPSTensor d D₁) (B : MPSTensor d D₂) {S : ℕ} :
    PairCumulativeWordTupleSpanTop A B S ↔ PairTraceSeparatingUpTo A B S :=
  ⟨pairTraceSeparatingUpTo_of_pairCumulativeWordTupleSpanTop A B,
    pairCumulativeWordTupleSpanTop_of_pairTraceSeparatingUpTo A B⟩

/-- Homogeneous pair product-span implies cumulative pair product-span at the same cutoff. -/
theorem pairCumulativeWordTupleSpanTop_of_pairWordTupleSpanTop {D₁ D₂ : ℕ}
    (A : MPSTensor d D₁) (B : MPSTensor d D₂) {S : ℕ}
    (hSpan : PairWordTupleSpanTop A B S) :
    PairCumulativeWordTupleSpanTop A B S := by
  classical
  unfold PairCumulativeWordTupleSpanTop
  apply eq_top_iff.mpr
  intro M _
  have hM : M ∈ Submodule.span ℂ (Set.range (pairWordTuple A B S)) := by
    rw [hSpan]
    exact Submodule.mem_top
  have hle : Submodule.span ℂ (Set.range (pairWordTuple A B S)) ≤
      pairCumulativeSpan A B S := by
    apply Submodule.span_le.mpr
    rintro N ⟨w, rfl⟩
    simpa [pairWordTuple, pairEvalWordTuple] using
      (pairEvalWordTuple_mem_pairCumulativeSpan A B (w := List.ofFn w) (S := S) (by simp))
  exact hle hM

/-- Homogeneous trace separation implies cumulative pair product-span at the same cutoff. -/
theorem pairCumulativeWordTupleSpanTop_of_pairTraceSeparatingAt {D₁ D₂ : ℕ}
    (A : MPSTensor d D₁) (B : MPSTensor d D₂) {S : ℕ}
    (hSep : PairTraceSeparatingAt A B S) :
    PairCumulativeWordTupleSpanTop A B S :=
  pairCumulativeWordTupleSpanTop_of_pairTraceSeparatingUpTo A B
    (pairTraceSeparatingUpTo_of_pairTraceSeparatingAt A B hSep)

/-- Trace separation by all finite pair words is dual to the span of all pair word tuples. -/
theorem pairAllWordsSpanTop_of_pairTraceSeparatingAll {D₁ D₂ : ℕ}
    (A : MPSTensor d D₁) (B : MPSTensor d D₂)
    (hSep : PairTraceSeparatingAll A B) :
    PairAllWordsSpanTop A B := by
  classical
  unfold PairAllWordsSpanTop
  by_contra hnot
  let W : Submodule ℂ
      (Matrix (Fin D₁) (Fin D₁) ℂ × Matrix (Fin D₂) (Fin D₂) ℂ) :=
    pairAllWordsSpan A B
  have hlt : W < ⊤ := lt_of_le_of_ne le_top (by simpa [W] using hnot)
  obtain ⟨f, hfne, hfker⟩ := Submodule.exists_le_ker_of_lt_top W hlt
  obtain ⟨ΔA, ΔB, hf_repr⟩ := exists_pair_trace_repr f
  have hΔ : ΔA = 0 ∧ ΔB = 0 := by
    refine hSep ΔA ΔB ?_
    intro w
    have hwmem : pairEvalWordTuple A B w ∈ W :=
      Submodule.subset_span ⟨w, rfl⟩
    have hf0 : f (pairEvalWordTuple A B w) = 0 := hfker hwmem
    simpa [pairEvalWordTuple, hf_repr] using hf0
  have hfzero : f = 0 := by
    apply LinearMap.ext
    intro M
    have hM := hf_repr M
    rw [hΔ.1, hΔ.2] at hM
    simpa using hM
  exact hfne hfzero

/-- The span of all finite pair words gives trace separation by all finite pair words. -/
theorem pairTraceSeparatingAll_of_pairAllWordsSpanTop {D₁ D₂ : ℕ}
    (A : MPSTensor d D₁) (B : MPSTensor d D₂)
    (hSpan : PairAllWordsSpanTop A B) :
    PairTraceSeparatingAll A B := by
  classical
  intro ΔA ΔB hΔ
  have hZeroOnSpan :
      ∀ M : Matrix (Fin D₁) (Fin D₁) ℂ × Matrix (Fin D₂) (Fin D₂) ℂ,
        M ∈ pairAllWordsSpan A B →
          Matrix.trace (ΔA * M.1) + Matrix.trace (ΔB * M.2) = 0 := by
    intro M hM
    exact pair_trace_zero_on_span ΔA ΔB
      (Ω := Set.range (pairEvalWordTuple A B))
      (by
        rintro M ⟨w, rfl⟩
        exact hΔ w)
      M (by simpa [pairAllWordsSpan] using hM)
  constructor
  · apply trace_mul_right_eq_zero
    intro M
    have hpair := hZeroOnSpan (M, 0) (by rw [hSpan]; exact Submodule.mem_top)
    simpa using hpair
  · apply trace_mul_right_eq_zero
    intro N
    have hpair := hZeroOnSpan (0, N) (by rw [hSpan]; exact Submodule.mem_top)
    simpa using hpair

/-- All-length trace separation is equivalent to all-word pair product-span. -/
theorem pairAllWordsSpanTop_iff_pairTraceSeparatingAll {D₁ D₂ : ℕ}
    (A : MPSTensor d D₁) (B : MPSTensor d D₂) :
    PairAllWordsSpanTop A B ↔ PairTraceSeparatingAll A B :=
  ⟨pairTraceSeparatingAll_of_pairAllWordsSpanTop A B,
    pairAllWordsSpanTop_of_pairTraceSeparatingAll A B⟩

/-- If all pair words span the product algebra, then words up to some finite cutoff already span. -/
theorem exists_pairCumulativeWordTupleSpanTop_of_pairAllWordsSpanTop {D₁ D₂ : ℕ}
    (A : MPSTensor d D₁) (B : MPSTensor d D₂)
    (hSpan : PairAllWordsSpanTop A B) :
    ∃ S : ℕ, PairCumulativeWordTupleSpanTop A B S := by
  classical
  let V := Matrix (Fin D₁) (Fin D₁) ℂ × Matrix (Fin D₂) (Fin D₂) ℂ
  have hx : ∀ x : V, ∃ S : ℕ, x ∈ pairCumulativeSpan A B S := by
    intro x
    have hxAll : x ∈ pairAllWordsSpan A B := by
      rw [hSpan]
      exact Submodule.mem_top
    induction hxAll using Submodule.span_induction with
    | mem y hy =>
        rcases hy with ⟨w, rfl⟩
        exact ⟨w.length, pairEvalWordTuple_mem_pairCumulativeSpan A B le_rfl⟩
    | zero => exact ⟨0, Submodule.zero_mem _⟩
    | add x y _ _ hx hy =>
        rcases hx with ⟨Sx, hSx⟩
        rcases hy with ⟨Sy, hSy⟩
        refine ⟨max Sx Sy, Submodule.add_mem _ ?_ ?_⟩
        · exact (pairCumulativeSpan_mono A B (le_max_left Sx Sy)) hSx
        · exact (pairCumulativeSpan_mono A B (le_max_right Sx Sy)) hSy
    | smul a x _ hx =>
        rcases hx with ⟨Sx, hSx⟩
        exact ⟨Sx, Submodule.smul_mem _ a hSx⟩
  haveI : IsNoetherian ℂ V := isNoetherian_of_isNoetherianRing_of_finite ℂ V
  let f : ℕ →o Submodule ℂ V :=
    ⟨fun S => pairCumulativeSpan A B S, fun _ _ hST => pairCumulativeSpan_mono A B hST⟩
  obtain ⟨S₀, hstab⟩ := (monotone_stabilizes_iff_noetherian.mpr ‹IsNoetherian ℂ V›) f
  refine ⟨S₀, eq_top_iff.mpr ?_⟩
  intro x _
  rcases hx x with ⟨S, hS⟩
  rcases le_total S S₀ with hSS₀ | hS₀S
  · exact (pairCumulativeSpan_mono A B hSS₀) hS
  · have heq : pairCumulativeSpan A B S = pairCumulativeSpan A B S₀ :=
      (hstab S hS₀S).symm
    simpa [heq] using hS

/-- If no nonzero trace functional vanishes on all pair words, then a finite cumulative
cutoff already trace-separates the pair. -/
theorem exists_pairTraceSeparatingUpTo_of_pairTraceSeparatingAll {D₁ D₂ : ℕ}
    (A : MPSTensor d D₁) (B : MPSTensor d D₂)
    (hSep : PairTraceSeparatingAll A B) :
    ∃ S : ℕ, PairTraceSeparatingUpTo A B S := by
  obtain ⟨S, hS⟩ := exists_pairCumulativeWordTupleSpanTop_of_pairAllWordsSpanTop A B
    (pairAllWordsSpanTop_of_pairTraceSeparatingAll A B hSep)
  exact ⟨S, pairTraceSeparatingUpTo_of_pairCumulativeWordTupleSpanTop A B hS⟩

/-- A finite cumulative cutoff exists exactly when no nonzero trace functional
vanishes on all finite pair words. -/
theorem exists_pairTraceSeparatingUpTo_iff_pairTraceSeparatingAll {D₁ D₂ : ℕ}
    (A : MPSTensor d D₁) (B : MPSTensor d D₂) :
    (∃ S : ℕ, PairTraceSeparatingUpTo A B S) ↔ PairTraceSeparatingAll A B := by
  constructor
  · rintro ⟨S, hS⟩ ΔA ΔB hΔ
    exact hS ΔA ΔB (fun w _hw => hΔ w)
  · exact exists_pairTraceSeparatingUpTo_of_pairTraceSeparatingAll A B

/-- A finite family of all-length pair trace-separation hypotheses admits one common
cumulative cutoff. -/
theorem exists_forall_pairTraceSeparatingUpTo_of_forall_pairTraceSeparatingAll
    (A : (k : Fin r) → MPSTensor d (dim k))
    (hSep : ∀ k j : Fin r, j ≠ k → PairTraceSeparatingAll (A k) (A j)) :
    ∃ S : ℕ, ∀ k j : Fin r, j ≠ k → PairTraceSeparatingUpTo (A k) (A j) S := by
  classical
  let Sij : Fin r × Fin r → ℕ := fun p =>
    if h : p.2 ≠ p.1 then
      Classical.choose (exists_pairTraceSeparatingUpTo_of_pairTraceSeparatingAll
        (A p.1) (A p.2) (hSep p.1 p.2 h))
    else 0
  let S : ℕ := Finset.univ.sup Sij
  refine ⟨S, ?_⟩
  intro k j hjk
  have hbase : PairTraceSeparatingUpTo (A k) (A j) (Sij (k, j)) := by
    simpa [Sij, hjk] using
      (Classical.choose_spec (exists_pairTraceSeparatingUpTo_of_pairTraceSeparatingAll
        (A k) (A j) (hSep k j hjk)))
  have hle : Sij (k, j) ≤ S := by
    exact Finset.le_sup (s := Finset.univ) (f := Sij) (Finset.mem_univ (k, j))
  exact hbase.mono hle

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

**Route A (spectral, completed upstream):**
`¬ GaugePhaseEquiv` → `spectralRadius(mixedTransfer) < 1` → `mpvOverlap → 0`.
This is proved in `TNLean/Spectral/SpectralGap.lean`.

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

The proof uses the Burnside/Jacobson density theorem on the pair product
algebra `A := alg{(Aᵢ, Bᵢ) | i}` inside `M_{D}(ℂ) × M_{D}(ℂ)`.  Because
`A` and `B` are individually injective, the left and right projections of `A`
are the full matrix algebra.  The non-gauge-equivalence hypothesis rules out
a nontrivial common invariant subspace of the pair action on `ℂ^D ⊕ ℂ^D`.
Burnside then forces `A = M_D × M_D`, which is exactly the statement that the
pair word tuples over all word lengths span the full product algebra.
By duality this is `PairTraceSeparatingAll`.

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
    -- By Burnside/Jacobson on the product algebra, this happens iff the pair action
    -- on ℂ^D ⊕ ℂ^D has no nontrivial invariant subspace, which follows from
    -- the injectivity of A, B and ¬ GaugeEquiv A B.
    --
    -- Formal proof: use `burnside_matrix` on the pair of tensors after verifying
    -- irreducibility of the joint action.  This requires the lemma:
    --   `isIrreducibleAction_pair_of_injective_not_gaugeEquiv`
    -- whose statement and proof mirror `isIrreducibleAction_of_isIrreducibleTensor`
    -- but for the block-diagonal pair tensor `i ↦ (A_i, B_i)`.
    sorry
  -- Step 1: duality ⇒ all-length trace separation
  exact pairTraceSeparatingAll_of_pairAllWordsSpanTop A B hPairSpanTop

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
  -- We need a length L such that `(1, 1)` is in the homogeneous pair span
  -- at all lengths ≥ L.  Once L is available, choose T = L + S and the
  -- identity-padding lemma gives the result.
  --
  -- **Remaining blocker:**  Prove `∃ L,` the pair identity `(1, 1)` belongs
  -- to `Submodule.span ℂ (Set.range (pairWordTuple A B L))` for all
  -- sufficiently large homogeneous lengths (or at least at an arithmetic
  -- progression that covers all padding offsets needed by the lemma below).
  -- This is the Burnside–Jacobson density statement for the pair algebra:
  -- once the pair algebra equals M_D × M_D, the identity `(1, 1)` is a
  -- polynomial in the generators, and padding with enough copies of a
  -- simultaneously-invertible word lifts it to a single homogeneous length.
  sorry

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

/-- Pair product-span at length `S` gives a length-`S` selector for the first
block of the pair. -/
theorem hasBlockSelectorOn_of_pairWordTupleSpanTop
    (A : (k : Fin r) → MPSTensor d (dim k)) {S : ℕ}
    {k j : Fin r} (hSpan : PairWordTupleSpanTop (A k) (A j) S) :
    HasBlockSelectorOn A k S {j} := by
  classical
  have htarget : ((1 : Matrix (Fin (dim k)) (Fin (dim k)) ℂ),
      (0 : Matrix (Fin (dim j)) (Fin (dim j)) ℂ)) ∈
      Submodule.span ℂ (Set.range (pairWordTuple (A k) (A j) S)) := by
    rw [hSpan]
    exact Submodule.mem_top
  rcases (Submodule.mem_span_range_iff_exists_fun ℂ).mp htarget with ⟨c, hc⟩
  let M : (l : Fin r) → Matrix (Fin (dim l)) (Fin (dim l)) ℂ :=
    fun l => ∑ w : Fin S → Fin d, c w • evalWord (A l) (List.ofFn w)
  refine ⟨M, ?_, ?_, ?_⟩
  · refine (Submodule.mem_span_range_iff_exists_fun ℂ).mpr ⟨c, ?_⟩
    ext l
    simp [M, wordTuple]
  · have hk := congrArg
      (LinearMap.fst ℂ (Matrix (Fin (dim k)) (Fin (dim k)) ℂ)
        (Matrix (Fin (dim j)) (Fin (dim j)) ℂ)) hc
    simpa [M, pairWordTuple, Fintype.linearCombination_apply] using hk
  · intro l hl
    have hlj : l = j := by simpa using hl
    subst l
    have hj := congrArg
      (LinearMap.snd ℂ (Matrix (Fin (dim k)) (Fin (dim k)) ℂ)
        (Matrix (Fin (dim j)) (Fin (dim j)) ℂ)) hc
    simpa [M, pairWordTuple, Fintype.linearCombination_apply] using hj

/-- Pair trace-separation at length `S` gives a length-`S` selector for the
first block of the pair. -/
theorem hasBlockSelectorOn_of_pairTraceSeparatingAt
    (A : (k : Fin r) → MPSTensor d (dim k)) {S : ℕ}
    {k j : Fin r} (hSep : PairTraceSeparatingAt (A k) (A j) S) :
    HasBlockSelectorOn A k S {j} :=
  hasBlockSelectorOn_of_pairWordTupleSpanTop A
    (pairWordTupleSpanTop_of_pairTraceSeparatingAt (A k) (A j) hSep)

/-- A common pair product-span length for all ordered distinct pairs gives
pairwise block separators. -/
theorem hasPairBlockSeparatingWords_of_forall_pairWordTupleSpanTop
    (A : (k : Fin r) → MPSTensor d (dim k)) {S : ℕ}
    (hSpan : ∀ k j : Fin r, j ≠ k → PairWordTupleSpanTop (A k) (A j) S) :
    HasPairBlockSeparatingWords A S := by
  intro k j hjk
  exact hasBlockSelectorOn_of_pairWordTupleSpanTop A (hSpan k j hjk)

/-- A common pair trace-separation length for all ordered distinct pairs gives
pairwise block separators. -/
theorem hasPairBlockSeparatingWords_of_forall_pairTraceSeparatingAt
    (A : (k : Fin r) → MPSTensor d (dim k)) {S : ℕ}
    (hSep : ∀ k j : Fin r, j ≠ k → PairTraceSeparatingAt (A k) (A j) S) :
    HasPairBlockSeparatingWords A S := by
  intro k j hjk
  exact hasBlockSelectorOn_of_pairTraceSeparatingAt A (hSep k j hjk)

/-- Existential form of the pair trace-separation criterion for pairwise block
separators. -/
theorem exists_hasPairBlockSeparatingWords_of_exists_forall_pairTraceSeparatingAt
    (A : (k : Fin r) → MPSTensor d (dim k))
    (hSep : ∃ S : ℕ,
      ∀ k j : Fin r, j ≠ k → PairTraceSeparatingAt (A k) (A j) S) :
    ∃ S : ℕ, HasPairBlockSeparatingWords A S := by
  rcases hSep with ⟨S, hS⟩
  exact ⟨S, hasPairBlockSeparatingWords_of_forall_pairTraceSeparatingAt A hS⟩

/-- The tuple-valued span of word evaluations is closed under pointwise matrix
multiplication, at the cost of adding word lengths. -/
theorem pointwise_mul_mem_span_wordTuple_add
    (A : (k : Fin r) → MPSTensor d (dim k))
    {L S : ℕ}
    {M N : (k : Fin r) → Matrix (Fin (dim k)) (Fin (dim k)) ℂ}
    (hM : M ∈ Submodule.span ℂ (Set.range (wordTuple A L)))
    (hN : N ∈ Submodule.span ℂ (Set.range (wordTuple A S))) :
    (fun k : Fin r => M k * N k) ∈
      Submodule.span ℂ (Set.range (wordTuple A (L + S))) := by
  classical
  let spanLS : Submodule ℂ ((k : Fin r) → Matrix (Fin (dim k)) (Fin (dim k)) ℂ) :=
    Submodule.span ℂ (Set.range (wordTuple A (L + S)))
  have hleft_gen : ∀ u : Fin L → Fin d,
      (fun k : Fin r => wordTuple A L u k * N k) ∈ spanLS := by
    intro u
    induction hN using Submodule.span_induction with
    | mem N hNmem =>
        rcases hNmem with ⟨v, rfl⟩
        have hEq : (fun k : Fin r => wordTuple A L u k * wordTuple A S v k) =
            wordTuple A (L + S) (Fin.append u v) := by
          funext k
          simp [wordTuple, List.ofFn_fin_append, evalWord_append]
        rw [hEq]
        exact Submodule.subset_span ⟨Fin.append u v, rfl⟩
    | zero =>
        have hzero : (fun k : Fin r =>
            wordTuple A L u k *
              (0 : (k : Fin r) → Matrix (Fin (dim k)) (Fin (dim k)) ℂ) k) = 0 := by
          funext k
          simp
        rw [hzero]
        exact Submodule.zero_mem _
    | add N₁ N₂ _ _ hN₁ hN₂ =>
        have hEq : (fun k : Fin r => wordTuple A L u k * (N₁ + N₂) k) =
            (fun k : Fin r => wordTuple A L u k * N₁ k) +
              (fun k : Fin r => wordTuple A L u k * N₂ k) := by
          funext k
          simp [Matrix.mul_add]
        rw [hEq]
        exact Submodule.add_mem _ hN₁ hN₂
    | smul a N _ hN =>
        have hEq : (fun k : Fin r => wordTuple A L u k * (a • N) k) =
            a • (fun k : Fin r => wordTuple A L u k * N k) := by
          funext k
          simp
        rw [hEq]
        exact Submodule.smul_mem _ a hN
  induction hM using Submodule.span_induction with
  | mem M hMmem =>
      rcases hMmem with ⟨u, rfl⟩
      exact hleft_gen u
  | zero =>
      have hzero : (fun k : Fin r =>
          (0 : (k : Fin r) → Matrix (Fin (dim k)) (Fin (dim k)) ℂ) k * N k) = 0 := by
        funext k
        simp
      rw [hzero]
      exact Submodule.zero_mem _
  | add M₁ M₂ _ _ hM₁ hM₂ =>
      have hEq : (fun k : Fin r => (M₁ + M₂) k * N k) =
          (fun k : Fin r => M₁ k * N k) +
            (fun k : Fin r => M₂ k * N k) := by
        funext k
        simp [Matrix.add_mul]
      rw [hEq]
      exact Submodule.add_mem _ hM₁ hM₂
  | smul a M _ hM =>
      have hEq : (fun k : Fin r => (a • M) k * N k) =
          a • (fun k : Fin r => M k * N k) := by
        funext k
        simp
      rw [hEq]
      exact Submodule.smul_mem _ a hM

/-- The empty word is the identity on every block, so it selects a block on the
empty target set. -/
theorem hasBlockSelectorOn_empty
    (A : (k : Fin r) → MPSTensor d (dim k)) (k : Fin r) :
    HasBlockSelectorOn A k 0 ∅ := by
  classical
  refine ⟨wordTuple A 0 (fun i => Fin.elim0 i), ?_, ?_, ?_⟩
  · exact Submodule.subset_span ⟨fun i => Fin.elim0 i, rfl⟩
  · simp [wordTuple]
  · intro j hj
    simp at hj

/-- Multiplying two partial selectors for the same block produces a selector
that vanishes on the union of their target sets. -/
theorem HasBlockSelectorOn.mul
    {A : (k : Fin r) → MPSTensor d (dim k)} {k : Fin r}
    {L S : ℕ} {targets₁ targets₂ : Finset (Fin r)}
    (h₁ : HasBlockSelectorOn A k L targets₁)
    (h₂ : HasBlockSelectorOn A k S targets₂) :
    HasBlockSelectorOn A k (L + S) (targets₁ ∪ targets₂) := by
  classical
  rcases h₁ with ⟨M, hM, hMk, hMzero⟩
  rcases h₂ with ⟨N, hN, hNk, hNzero⟩
  refine ⟨fun j => M j * N j, ?_, ?_, ?_⟩
  · exact pointwise_mul_mem_span_wordTuple_add A hM hN
  · simp [hMk, hNk]
  · intro j hj
    rcases Finset.mem_union.mp hj with hj | hj
    · simp [hMzero j hj]
    · simp [hNzero j hj]

/-- Pairwise block-separating word polynomials multiply to a selector on any
finite target set. -/
theorem hasBlockSelectorOn_finset_of_pairBlockSeparatingWords
    (A : (k : Fin r) → MPSTensor d (dim k)) {S : ℕ}
    (hPair : HasPairBlockSeparatingWords A S)
    (k : Fin r) (targets : Finset (Fin r))
    (htargets : ∀ j : Fin r, j ∈ targets → j ≠ k) :
    HasBlockSelectorOn A k (targets.card * S) targets := by
  classical
  revert htargets
  refine Finset.induction_on targets ?base ?step
  · intro _
    simpa using hasBlockSelectorOn_empty A k
  · intro j targets hj_not_mem ih htargets_insert
    have htargets_tail : ∀ l : Fin r, l ∈ targets → l ≠ k := by
      intro l hl
      exact htargets_insert l (Finset.mem_insert_of_mem hl)
    have htail := ih htargets_tail
    have hjk : j ≠ k := htargets_insert j (Finset.mem_insert_self j targets)
    have hsingle : HasBlockSelectorOn A k S {j} := hPair k j hjk
    have hmul : HasBlockSelectorOn A k (targets.card * S + S) (targets ∪ {j}) :=
      htail.mul hsingle
    have hsets : targets ∪ {j} = insert j targets := by
      ext l
      simp
    have hlen : (insert j targets).card * S = targets.card * S + S := by
      rw [Finset.card_insert_of_notMem hj_not_mem]
      exact Nat.succ_mul targets.card S
    simpa [hsets, hlen] using hmul

/-- Tuple-span selectors on `Finset.univ.erase k` recover coefficient-based
block-selector words. -/
theorem hasBlockSelectorWords_of_forall_hasBlockSelectorOn_univ_erase
    (A : (k : Fin r) → MPSTensor d (dim k)) {S : ℕ}
    (h : ∀ k : Fin r, HasBlockSelectorOn A k S (Finset.univ.erase k)) :
    HasBlockSelectorWords A S := by
  classical
  intro k
  rcases h k with ⟨M, hM, hMk, hMzero⟩
  rcases (Submodule.mem_span_range_iff_exists_fun ℂ).mp hM with ⟨c, hc⟩
  refine ⟨c, ?_, ?_⟩
  · have hk := congrArg (fun N => N k) hc
    simpa [wordTuple, hMk] using hk
  · intro j hjk
    have hjmem : j ∈ Finset.univ.erase k := by
      simp [hjk]
    have hj := congrArg (fun N => N j) hc
    simpa [wordTuple, hMzero j hjmem] using hj

/-- Pairwise block-separating word polynomials assemble into full block-selector
words by multiplying the pairwise selectors for the chosen block against all
other blocks. -/
theorem hasBlockSelectorWords_of_pairBlockSeparatingWords
    (A : (k : Fin r) → MPSTensor d (dim k)) {S : ℕ}
    (hPair : HasPairBlockSeparatingWords A S) :
    HasBlockSelectorWords A ((r - 1) * S) := by
  classical
  refine hasBlockSelectorWords_of_forall_hasBlockSelectorOn_univ_erase A ?_
  intro k
  have htargets : ∀ j : Fin r, j ∈ Finset.univ.erase k → j ≠ k := by
    intro j hj
    exact (Finset.mem_erase.mp hj).1
  have hsel := hasBlockSelectorOn_finset_of_pairBlockSeparatingWords A hPair k
    (Finset.univ.erase k) htargets
  have hcard : (Finset.univ.erase k).card = r - 1 := by
    simp [Fintype.card_fin]
  simpa [hcard] using hsel

/-- Any finite-length product-algebra spanning witness already contains block
selectors as a special case. -/
theorem hasBlockSelectorWords_of_wordTupleSpanTop
    (A : (k : Fin r) → MPSTensor d (dim k))
    {S : ℕ} (hSpan : WordTupleSpanTop A S) :
    HasBlockSelectorWords A S := by
  classical
  intro k
  let target : (j : Fin r) → Matrix (Fin (dim j)) (Fin (dim j)) ℂ :=
    fun j => if j = k then 1 else 0
  have htarget : target ∈ Submodule.span ℂ (Set.range (wordTuple A S)) := by
    rw [hSpan]
    exact Submodule.mem_top
  rcases (Submodule.mem_span_range_iff_exists_fun ℂ).mp htarget with ⟨c, hc⟩
  refine ⟨c, ?_, ?_⟩
  · simpa [target] using congrArg (fun M => M k) hc
  · intro j hj
    simpa [target, hj] using congrArg (fun M => M j) hc

private theorem exists_dualCoeffs_of_wordEntryFamily_linearIndependent
    (A : (k : Fin r) → MPSTensor d (dim k))
    {L : ℕ} (hLI : LinearIndependent ℂ (wordEntryFamily A L)) :
    ∃ coeff : BlockEntryIndex dim → (Fin L → Fin d) → ℂ,
      ∀ x y : BlockEntryIndex dim,
        ∑ w : Fin L → Fin d, coeff x w * wordEntryFamily A L y w =
          if x = y then 1 else 0 := by
  classical
  let lc := Fintype.linearCombination ℂ (wordEntryFamily A L)
  have hlcKer : lc.ker = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro c hc
    exact funext (Fintype.linearIndependent_iff.mp hLI c (by simpa [lc] using hc))
  obtain ⟨Ψ, hΨ⟩ := lc.exists_leftInverse_of_injective hlcKer
  let coeff : BlockEntryIndex dim → (Fin L → Fin d) → ℂ :=
    fun x w => Ψ ((Pi.single w (1 : ℂ) : (Fin L → Fin d) → ℂ)) x
  have hΨ_apply :
      ∀ (f : (Fin L → Fin d) → ℂ) (x : BlockEntryIndex dim),
        Ψ f x = ∑ w : Fin L → Fin d, f w * coeff x w := by
    intro f x
    calc
      Ψ f x = Ψ (∑ w : Fin L → Fin d, (Pi.single w (f w) : (Fin L → Fin d) → ℂ)) x := by
        simpa using
          congrArg (fun g : ((Fin L → Fin d) → ℂ) => Ψ g x) (Finset.univ_sum_single f).symm
      _ = ∑ w : Fin L → Fin d, Ψ ((Pi.single w (f w) : (Fin L → Fin d) → ℂ)) x := by
        rw [map_sum]
        simp
      _ = ∑ w : Fin L → Fin d, f w * coeff x w := by
        refine Finset.sum_congr rfl ?_
        intro w _
        have hsingle_smul :
            ((Pi.single w (f w) : (Fin L → Fin d) → ℂ)) =
              f w • ((Pi.single w (1 : ℂ) : (Fin L → Fin d) → ℂ)) := by
          ext z
          by_cases hzw : z = w
          · subst hzw
            simp
          · simp [Pi.single_eq_of_ne hzw]
        rw [hsingle_smul]
        simp [coeff]
  refine ⟨coeff, ?_⟩
  intro x y
  have hsingle :
      lc ((Pi.single y (1 : ℂ) : BlockEntryIndex dim → ℂ)) = wordEntryFamily A L y := by
    ext w
    rw [Fintype.linearCombination_apply, Finset.sum_eq_single y]
    · simp
    · intro z _ hzy
      simp [Pi.single_eq_of_ne hzy]
    · intro hy
      exact False.elim (hy (Finset.mem_univ y))
  have hy : Ψ (wordEntryFamily A L y) x = if x = y then 1 else 0 := by
    have hleft :
        Ψ (lc ((Pi.single y (1 : ℂ) : BlockEntryIndex dim → ℂ))) =
          ((Pi.single y (1 : ℂ) : BlockEntryIndex dim → ℂ)) := by
      simpa using congrArg (fun f => f ((Pi.single y (1 : ℂ) : BlockEntryIndex dim → ℂ))) hΨ
    simpa [hsingle, Pi.single_apply] using congrFun hleft x
  simpa [hΨ_apply (wordEntryFamily A L y) x, mul_comm] using hy

/-- Linear independence of the scalar word-entry family forces the tuple-valued
length-`L` word evaluations to span the full product algebra. -/
theorem wordTupleSpanTop_of_wordEntryFamily_linearIndependent
    (A : (k : Fin r) → MPSTensor d (dim k))
    {L : ℕ} (hLI : LinearIndependent ℂ (wordEntryFamily A L)) :
    WordTupleSpanTop A L := by
  classical
  rcases exists_dualCoeffs_of_wordEntryFamily_linearIndependent A hLI with
    ⟨coeff, hcoeff⟩
  rw [WordTupleSpanTop, span_range_eq_top_iff_surjective_fintypeLinearCombination]
  intro M
  let c : (Fin L → Fin d) → ℂ :=
    fun w => ∑ x : BlockEntryIndex dim, blockEntryValue M x * coeff x w
  refine ⟨c, ?_⟩
  ext j a b
  calc
    (Fintype.linearCombination ℂ (wordTuple A L) c) j a b
        = (∑ w : Fin L → Fin d, c w • evalWord (A j) (List.ofFn w)) a b := by
            simp [Fintype.linearCombination_apply, wordTuple, Pi.smul_apply]
    _ = ∑ w : Fin L → Fin d, c w * wordEntryFamily A L ⟨j, (a, b)⟩ w := by
          simp_rw [Matrix.sum_apply, Matrix.smul_apply]
          simp [wordEntryFamily, blockEntryValue, wordTuple]
    _ = ∑ w : Fin L → Fin d,
          ∑ x : BlockEntryIndex dim,
            blockEntryValue M x * (coeff x w * wordEntryFamily A L ⟨j, (a, b)⟩ w) := by
          unfold c
          refine Finset.sum_congr rfl ?_
          intro w _
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl ?_
          intro x _
          ring
    _ = ∑ x : BlockEntryIndex dim,
          blockEntryValue M x *
            (∑ w : Fin L → Fin d, coeff x w * wordEntryFamily A L ⟨j, (a, b)⟩ w) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl ?_
          intro x _
          rw [← Finset.mul_sum]
    _ = ∑ x : BlockEntryIndex dim,
          blockEntryValue M x * (if x = ⟨j, (a, b)⟩ then 1 else 0) := by
          refine Finset.sum_congr rfl ?_
          intro x _
          rw [hcoeff x ⟨j, (a, b)⟩]
    _ = blockEntryValue M ⟨j, (a, b)⟩ := by
          rw [Finset.sum_eq_single ⟨j, (a, b)⟩]
          · simp
          · intro x _ hx
            simp [hx]
          · intro hmem
            exact False.elim (hmem (Finset.mem_univ _))
    _ = M j a b := rfl

/-- The linear-independence criterion above gives the abstract Proposition-IV.3
selector data as a corollary. -/
theorem hasBlockSelectorWords_of_wordEntryFamily_linearIndependent
    (A : (k : Fin r) → MPSTensor d (dim k))
    {L : ℕ} (hLI : LinearIndependent ℂ (wordEntryFamily A L)) :
    HasBlockSelectorWords A L :=
  hasBlockSelectorWords_of_wordTupleSpanTop A
    (wordTupleSpanTop_of_wordEntryFamily_linearIndependent A hLI)

/-- The linear-independence criterion above also yields the `HasBiCF` witness
used by `HorizontalCFData`. -/
theorem hasBiCF_of_wordEntryFamily_linearIndependent
    (A : (k : Fin r) → MPSTensor d (dim k))
    {L : ℕ} (hLI : LinearIndependent ℂ (wordEntryFamily A L)) :
    HasBiCF A :=
  hasBiCF_of_wordTupleSpanTop A
    (wordTupleSpanTop_of_wordEntryFamily_linearIndependent A hLI)

/-- Abstract finite-length data isolating the content of Proposition IV.3
(`propblockinj`) from arXiv:1606.00608.

A family is `PropBlockInjective` if there is a common blocking length making
all blocks injective, together with a second finite family of words selecting
individual blocks. Concatenating an injective prefix with a selector suffix then
spans the full product algebra. -/
def PropBlockInjective
    (A : (k : Fin r) → MPSTensor d (dim k)) : Prop :=
  ∃ L S : ℕ, (∀ k, IsNBlkInjective (A k) L) ∧ HasBlockSelectorWords A S

/-- Common block injectivity plus pairwise block-separating word polynomials
produce the abstract Proposition-IV.3 selector data. -/
theorem propBlockInjective_of_common_blockInjective_of_pairBlockSeparatingWords
    (A : (k : Fin r) → MPSTensor d (dim k))
    {L S : ℕ}
    (hInj : ∀ k, IsNBlkInjective (A k) L)
    (hPair : HasPairBlockSeparatingWords A S) :
    PropBlockInjective A :=
  ⟨L, (r - 1) * S, hInj, hasBlockSelectorWords_of_pairBlockSeparatingWords A hPair⟩

/-- Common block injectivity plus finite-length block selectors yield the full
word-tuple span condition. -/
theorem wordTupleSpanTop_of_common_blockInjective_of_blockSelectorWords
    (A : (k : Fin r) → MPSTensor d (dim k))
    {L S : ℕ}
    (hInj : ∀ k, IsNBlkInjective (A k) L)
    (hSel : HasBlockSelectorWords A S) :
    WordTupleSpanTop A (L + S) := by
  classical
  unfold WordTupleSpanTop
  apply top_unique
  intro M _
  have hMk_mem :
      ∀ k : Fin r,
        M k ∈ Submodule.span ℂ
          (Set.range fun u : Fin L → Fin d => evalWord (A k) (List.ofFn u)) := by
    intro k
    rw [hInj k]
    exact Submodule.mem_top
  choose prefixCoeffs hprefix using
    fun k =>
      (Submodule.mem_span_range_iff_exists_fun ℂ).mp (hMk_mem k)
  choose selectorCoeffs hselector_self hselector_off using hSel
  let assembled : (k : Fin r) → Matrix (Fin (dim k)) (Fin (dim k)) ℂ :=
    ∑ k : Fin r, ∑ u : Fin L → Fin d, ∑ v : Fin S → Fin d,
      (prefixCoeffs k u * selectorCoeffs k v) •
        wordTuple A (L + S) (Fin.append u v)
  have hassembled_mem :
      assembled ∈ Submodule.span ℂ (Set.range (wordTuple A (L + S))) := by
    unfold assembled
    refine Submodule.sum_mem _ ?_
    intro k _
    refine Submodule.sum_mem _ ?_
    intro u _
    refine Submodule.sum_mem _ ?_
    intro v _
    refine Submodule.smul_mem _ _ ?_
    exact Submodule.subset_span ⟨Fin.append u v, rfl⟩
  have hassembled : assembled = M := by
    funext j
    unfold assembled
    calc
      (∑ k : Fin r, ∑ u : Fin L → Fin d, ∑ v : Fin S → Fin d,
            (prefixCoeffs k u * selectorCoeffs k v) •
              wordTuple A (L + S) (Fin.append u v)) j
          = ∑ k : Fin r, ∑ u : Fin L → Fin d, ∑ v : Fin S → Fin d,
              (prefixCoeffs k u * selectorCoeffs k v) •
                (evalWord (A j) (List.ofFn u) *
                  evalWord (A j) (List.ofFn v)) := by
              simp [wordTuple, List.ofFn_fin_append, evalWord_append]
      _ = ∑ k : Fin r, ∑ u : Fin L → Fin d,
            prefixCoeffs k u •
              (evalWord (A j) (List.ofFn u) *
                ∑ v : Fin S → Fin d,
                  selectorCoeffs k v • evalWord (A j) (List.ofFn v)) := by
            refine Finset.sum_congr rfl ?_
            intro k _
            refine Finset.sum_congr rfl ?_
            intro u _
            calc
              ∑ v : Fin S → Fin d,
                  (prefixCoeffs k u * selectorCoeffs k v) •
                    (evalWord (A j) (List.ofFn u) *
                      evalWord (A j) (List.ofFn v))
                = ∑ v : Fin S → Fin d,
                    prefixCoeffs k u •
                      (evalWord (A j) (List.ofFn u) *
                        (selectorCoeffs k v • evalWord (A j) (List.ofFn v))) := by
                    refine Finset.sum_congr rfl ?_
                    intro v _
                    rw [Matrix.mul_smul]
                    simp [smul_smul]
              _ = prefixCoeffs k u •
                    (evalWord (A j) (List.ofFn u) *
                      ∑ v : Fin S → Fin d,
                        selectorCoeffs k v • evalWord (A j) (List.ofFn v)) := by
                    rw [Matrix.mul_sum, Finset.smul_sum]
      _ = ∑ k : Fin r, ∑ u : Fin L → Fin d,
            if h : k = j then
              prefixCoeffs k u • evalWord (A j) (List.ofFn u)
            else 0 := by
            refine Finset.sum_congr rfl ?_
            intro k _
            refine Finset.sum_congr rfl ?_
            intro u _
            by_cases hkj : k = j
            · subst hkj
              simp [hselector_self]
            · have hjk : j ≠ k := by
                intro hjk
                exact hkj hjk.symm
              have hzero :
                  ∑ v : Fin S → Fin d,
                    selectorCoeffs k v • evalWord (A j) (List.ofFn v) = 0 :=
                hselector_off k j hjk
              simp [hkj, hzero]
      _ = ∑ u : Fin L → Fin d,
            prefixCoeffs j u • evalWord (A j) (List.ofFn u) := by
            simp
      _ = M j := hprefix j
  rw [← hassembled]
  exact hassembled_mem

/-- Common block injectivity plus pairwise block-separating word polynomials
yield the full word-tuple span condition. -/
theorem wordTupleSpanTop_of_common_blockInjective_of_pairBlockSeparatingWords
    (A : (k : Fin r) → MPSTensor d (dim k))
    {L S : ℕ}
    (hInj : ∀ k, IsNBlkInjective (A k) L)
    (hPair : HasPairBlockSeparatingWords A S) :
    WordTupleSpanTop A (L + (r - 1) * S) :=
  wordTupleSpanTop_of_common_blockInjective_of_blockSelectorWords A hInj
    (hasBlockSelectorWords_of_pairBlockSeparatingWords A hPair)

/-- Common block injectivity plus pairwise block-separating word polynomials
imply `HasBiCF`. -/
theorem hasBiCF_of_common_blockInjective_of_pairBlockSeparatingWords
    (A : (k : Fin r) → MPSTensor d (dim k))
    {L S : ℕ}
    (hInj : ∀ k, IsNBlkInjective (A k) L)
    (hPair : HasPairBlockSeparatingWords A S) :
    HasBiCF A :=
  hasBiCF_of_wordTupleSpanTop A
    (wordTupleSpanTop_of_common_blockInjective_of_pairBlockSeparatingWords A hInj hPair)

/-- The abstract Proposition-IV.3 selector data imply the finite-length
word-tuple span condition. -/
theorem wordTupleSpanTop_of_propBlockInjective
    (A : (k : Fin r) → MPSTensor d (dim k))
    (hProp : PropBlockInjective A) :
    ∃ N : ℕ, WordTupleSpanTop A N := by
  rcases hProp with ⟨L, S, hInj, hSel⟩
  exact ⟨L + S,
    wordTupleSpanTop_of_common_blockInjective_of_blockSelectorWords A hInj hSel⟩

/-- The abstract Proposition-IV.3 selector data imply `HasBiCF`. -/
theorem hasBiCF_of_propBlockInjective
    (A : (k : Fin r) → MPSTensor d (dim k))
    (hProp : PropBlockInjective A) :
    HasBiCF A := by
  rcases wordTupleSpanTop_of_propBlockInjective A hProp with ⟨N, hN⟩
  exact hasBiCF_of_wordTupleSpanTop A hN

section DuplicateScalarBlocks

/-- Nonzero weights for the duplicate-block counterexample. -/
def duplicateScalarWeights : Fin 2 → ℂ
  | 0 => 1
  | 1 => 2

/-- Common block dimension for the duplicate-block counterexample. -/
abbrev duplicateScalarDim : Fin 2 → ℕ := fun _ => 1

/-- Two identical `1 × 1` blocks. This family is blockwise injective and
left-canonical, but it cannot admit any finite-length `wordEntryFamily`
linear-independence witness. -/
def duplicateScalarBlocks :
    (k : Fin 2) → MPSTensor 1 (duplicateScalarDim k)
  | _ => fun _ => (1 : Matrix (Fin 1) (Fin 1) ℂ)

private theorem span_singleton_one_finOne_eq_top :
    (ℂ ∙ (1 : Matrix (Fin 1) (Fin 1) ℂ)) = ⊤ := by
  refine (Submodule.span_singleton_eq_top_iff ℂ
    (1 : Matrix (Fin 1) (Fin 1) ℂ)).2 ?_
  intro M
  refine ⟨M 0 0, ?_⟩
  ext i j
  have hi : i = 0 := Fin.eq_zero i
  have hj : j = 0 := Fin.eq_zero j
  subst hi
  subst hj
  simp

/-- Each duplicate scalar block is injective. -/
theorem duplicateScalarBlocks_isInjective :
    ∀ k, IsInjective (duplicateScalarBlocks k) := by
  intro k
  simpa [duplicateScalarBlocks, duplicateScalarDim, IsInjective, Set.range_const] using
    span_singleton_one_finOne_eq_top

/-- The duplicate scalar blocks are left-canonical. -/
theorem duplicateScalarBlocks_leftCanonical :
    ∀ k, ∑ i : Fin 1, (duplicateScalarBlocks k i)ᴴ * duplicateScalarBlocks k i = 1 := by
  intro k
  simp [duplicateScalarBlocks]

/-- The counterexample weights are nonzero. -/
theorem duplicateScalarWeights_ne_zero :
    ∀ k, duplicateScalarWeights k ≠ 0 := by
  intro k
  fin_cases k <;> norm_num [duplicateScalarWeights]

/-- Duplicate blocks force repeated scalar word-entry functionals, so no blocking
length can make `wordEntryFamily` linearly independent. -/
theorem duplicateScalarBlocks_not_linearIndependent_wordEntryFamily (L : ℕ) :
    ¬ LinearIndependent ℂ (wordEntryFamily duplicateScalarBlocks L) := by
  intro hLI
  let x0 : BlockEntryIndex duplicateScalarDim := ⟨0, (0, 0)⟩
  let x1 : BlockEntryIndex duplicateScalarDim := ⟨1, (0, 0)⟩
  have hEq : wordEntryFamily duplicateScalarBlocks L x0 =
      wordEntryFamily duplicateScalarBlocks L x1 := by
    funext w
    simp [x0, x1, wordEntryFamily, blockEntryValue, wordTuple, duplicateScalarBlocks]
  have hx : x0 = x1 := hLI.injective hEq
  have h01 : (0 : Fin 2) = 1 := by
    simpa [x0, x1] using congrArg Sigma.fst hx
  exact Fin.zero_ne_one h01

/-- Concrete obstruction to the Issue-#822 target on the current hypotheses:
blockwise injectivity, left-canonicality, and nonzero weights do not by
themselves imply a finite-length `wordEntryFamily` witness. -/
theorem duplicateScalarBlocks_not_exists_linearIndependent_wordEntryFamily :
    ¬ ∃ L, LinearIndependent ℂ (wordEntryFamily duplicateScalarBlocks L) := by
  rintro ⟨L, hL⟩
  exact duplicateScalarBlocks_not_linearIndependent_wordEntryFamily L hL

/-- The duplicate scalar blocks do not satisfy the biCF trace-separation property. -/
theorem duplicateScalarBlocks_not_hasBiCF :
    ¬ HasBiCF duplicateScalarBlocks := by
  rintro ⟨L, hL⟩
  let Δ : (k : Fin 2) → Matrix (Fin (duplicateScalarDim k)) (Fin (duplicateScalarDim k)) ℂ :=
    fun k => if k = 0 then 1 else -1
  have hTrace :
      ∀ w : Fin L → Fin 1,
        (∑ k : Fin 2,
          Matrix.trace (Δ k * evalWord (duplicateScalarBlocks k) (List.ofFn w))) = 0 := by
    intro w
    simp [Δ, duplicateScalarBlocks, duplicateScalarDim, Matrix.trace_fin_one]
  have hzero := hL Δ hTrace 0
  have hentry := congrFun (congrFun hzero 0) 0
  simp [Δ] at hentry

/-- Counterexample to deriving finite-length block separation from the
other `HorizontalCFData` fields alone. -/
theorem duplicateScalarBlocks_counterexample :
    (∀ k, IsInjective (duplicateScalarBlocks k)) ∧
      (∀ k, ∑ i : Fin 1,
        (duplicateScalarBlocks k i)ᴴ * duplicateScalarBlocks k i = 1) ∧
      (∀ k, duplicateScalarWeights k ≠ 0) ∧
      ¬ HasBiCF duplicateScalarBlocks ∧
      ¬ ∃ L, LinearIndependent ℂ (wordEntryFamily duplicateScalarBlocks L) := by
  refine ⟨duplicateScalarBlocks_isInjective, duplicateScalarBlocks_leftCanonical,
    duplicateScalarWeights_ne_zero, duplicateScalarBlocks_not_hasBiCF,
    duplicateScalarBlocks_not_exists_linearIndependent_wordEntryFamily⟩

end DuplicateScalarBlocks

end MPSTensor

namespace MPOTensor

variable {d : ℕ} {r : ℕ} {dim : Fin r → ℕ} {μ : Fin r → ℂ}

/-- Forgetting the structure fields of `HorizontalCFData` leaves the bare `HasBiCF`
property on the block family. -/
theorem HorizontalCFData.toHasBiCF
    {A : (k : Fin r) → MPSTensor d (dim k)}
    (hCF : HorizontalCFData (d := d) μ A) :
    MPSTensor.HasBiCF A :=
  hCF.biCF

/-- A finite-length block-separation hypothesis yields `HorizontalCFData`. -/
theorem horizontalCFData_of_wordTupleSpanTop
    (A : (k : Fin r) → MPSTensor d (dim k))
    (hInj : ∀ k, MPSTensor.IsInjective (A k))
    (hLeft : ∀ k, ∑ i : Fin d, (A k i)ᴴ * A k i = 1)
    (hμne : ∀ k, μ k ≠ 0)
    (hSpan : ∃ L : ℕ, MPSTensor.WordTupleSpanTop A L) :
    HorizontalCFData (d := d) μ A := by
  rcases hSpan with ⟨L, hL⟩
  refine {
    block_injective := hInj
    left_canonical := hLeft
    weight_ne_zero := hμne
    biCF := ?_
  }
  exact MPSTensor.hasBiCF_of_wordTupleSpanTop A hL

/-- Linear independence of the scalar word-entry family is another concrete
route into `HorizontalCFData`: it already implies the finite-length product
algebra span condition. -/
theorem horizontalCFData_of_wordEntryFamily_linearIndependent
    (A : (k : Fin r) → MPSTensor d (dim k))
    (hInj : ∀ k, MPSTensor.IsInjective (A k))
    (hLeft : ∀ k, ∑ i : Fin d, (A k i)ᴴ * A k i = 1)
    (hμne : ∀ k, μ k ≠ 0)
    {L : ℕ}
    (hLI : LinearIndependent ℂ (MPSTensor.wordEntryFamily A L)) :
    HorizontalCFData (d := d) μ A :=
  horizontalCFData_of_wordTupleSpanTop A hInj hLeft hμne
    ⟨L, MPSTensor.wordTupleSpanTop_of_wordEntryFamily_linearIndependent A hLI⟩

/-- Proposition-IV.3-style selector data yield `HorizontalCFData` through the
finite-length span criterion. -/
theorem horizontalCFData_of_propBlockInjective
    (A : (k : Fin r) → MPSTensor d (dim k))
    (hInj : ∀ k, MPSTensor.IsInjective (A k))
    (hLeft : ∀ k, ∑ i : Fin d, (A k i)ᴴ * A k i = 1)
    (hμne : ∀ k, μ k ≠ 0)
    (hProp : MPSTensor.PropBlockInjective A) :
    HorizontalCFData (d := d) μ A := by
  refine {
    block_injective := hInj
    left_canonical := hLeft
    weight_ne_zero := hμne
    biCF := MPSTensor.hasBiCF_of_propBlockInjective A hProp
  }


/-!
## Why the remaining `HorizontalCFData` fields are still insufficient

The strengthened hypotheses used above are strictly extra data. A simple
obstruction shows that one cannot derive `biCF` from blockwise injectivity,
left-canonicality, and nonzero (even pairwise distinct) weights alone.

Take `r = 2`, `d = 1`, `dim k = 1`, and let both blocks be the same scalar tensor
`A_k(0) = 1`, while the weights are `μ 0 = 1` and `μ 1 = 2`. Then each block is
injective and left-canonical, and the weights are distinct and nonzero. However for
any blocking length `L` there is only one word `w : Fin L → Fin 1`, and
`evalWord (A k) (List.ofFn w) = 1` for both blocks. Choosing `Δ 0 = 1` and
`Δ 1 = -1` makes

`∑ k, Matrix.trace (Δ k * MPSTensor.evalWord (A k) (List.ofFn w)) = 0`

for that unique word, while `Δ ≠ 0`. Therefore `HasBiCF A` fails.

The new predicate `PropBlockInjective` expresses one abstract finite-length route,
while `wordEntryFamily` gives a second, equivalent linear-algebra criterion.
What remains open is to derive either of those finite-length witnesses from the
repository's current BNT / canonical-form hypotheses, i.e. to formalize the full
content of Proposition IV.3 of arXiv:1606.00608.
-/

end MPOTensor
