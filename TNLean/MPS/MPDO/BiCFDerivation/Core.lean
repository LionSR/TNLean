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
# Finite-length sufficient conditions for MPDO biCF

The `HorizontalCFData` structure in `VerticalCF.lean` states the block-injective
canonical-form property `biCF` as a hypothesis. This file states finite-length
sufficient conditions for deriving that field.

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
   [Cirac--Perez-Garcia--Schuch--Verstraete 2017], Proposition IV.3.

4. A **pairwise-to-global selector reduction**: if every ordered pair of
   distinct blocks admits a finite word polynomial that is the identity on the
   first block and zero on the second, then multiplying these pairwise
   separators gives full block-selector words.

5. A finite-dimensional **cumulative pair trace criterion**: if no nonzero pair
   trace functional vanishes on all finite pair words, then a finite cumulative
   word-length bound already detects every nonzero test pair.

This isolates the missing ingredient more precisely: one still needs a proved
finite-length block-separation theorem producing either the pairwise separators
of item (4), the selector data of item (3), or equivalently the word-entry
linear independence of item (2), from canonical-form/BNT data.

The duplicate scalar-block obstruction showing that the remaining
`HorizontalCFData` fields do not imply `biCF` is in
`TNLean.MPS.MPDO.BiCFDerivation.Counterexample`.
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

end MPSTensor
