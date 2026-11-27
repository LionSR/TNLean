/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Kraus.Injectivity
import QICLean.Kraus.Wielandt.SpanGrowth.CumulativeSpan
import QICLean.Kraus.Word
import TNLean.MPS.Tensor
import QICLean.Kraus.Wielandt.SpanGrowth.EigenvectorSpreading
import QICLean.Kraus.Wielandt.SpanGrowth.VectorToMatrixSpan
import TNLean.MPS.Tensor.Physical.Blocking
import QICLean.Kraus.Wielandt.SpanGrowth.CumulativeToWordSpan
import QICLean.Kraus.Wielandt.SpanGrowth.AlgebraSpan
import QICLean.Kraus.Wielandt.SpanGrowth.NonzeroTraceProduct

/-!
# Cumulative word spans and TN injectivity

For an MPS tensor $A$, the exact word span $S_n(A)$ contains products of
length $n$, while the cumulative span $T_n(A)$ contains products of length at
most $n$. This file also relates these spaces to block injectivity and
normality.

## Eigenvector spreading for MPS tensors

This file preserves the established MPS tensor interface to the transfer-free
vector-spreading results in `Kraus` and proves the normal-tensor specialization.

## Vector-to-matrix span results for MPS tensors

This file preserves the established `MPSTensor` interface to the channel-generic
vector-to-matrix span results in `Kraus`. The blocking results remain here because
they use the tensor-network blocking operation.

## From cumulative span to word span for MPS tensors

This file gives the MPS-facing consequences of the generic Kraus-family span
results. The transfer-free statements are MPS restatements of the corresponding
Kraus-family results. The MPS-specific results connect exact
word-span fullness to block injectivity and normality.

### Main results

* `isNBlkInjective_of_ge_of_unital` propagates block injectivity under the
  equation $\sum_a A_a A_a^\dagger=I$.
* `isNormal_of_cumulativeSpan_eq_top_of_aperiodic` derives normality from full
  cumulative span and identity membership in the one-letter span.
* `isNormal_of_algSpan_eq_top_of_aperiodic` combines this with algebra-span
  fullness.
* `Kraus.exists_eigenvector_of_cumulativeSpan_eq_top` extracts a nonzero-eigenvalue
  eigenvector from a word with nonzero trace.

### References

* arXiv:0909.5347, Proposition 3
* arXiv:1606.00608, Section 2.3

## Nonzero Trace Words at Bounded Length (Lemma 1)

This file gives tensor consequences of **Lemma 1** of arXiv:0909.5347
(Sanz, Pérez-García, Wolf, Cirac). If `A` is normal, then some nonempty word product of
length at most `D² − dim(S₁(A)) + 1` has nonzero trace. For a minimal Kraus family,
`dim(S₁(A)) = d`, which recovers the paper's bound. The full span-growth argument is
proved for finite matrix families in
`TNLean.Kraus.Wielandt.SpanGrowth.NonzeroTraceProduct`; the results below state its
coarse and sharp consequences for normal matrix product tensors.
-/

section

open scoped Matrix

namespace MPSTensor

variable {d D : ℕ}

/-! ### Injectivity and normality -/

/-- Block injectivity at a positive length propagates to the next length. -/
theorem isNBlkInjective_succ_of_isNBlkInjective
    (A : MPSTensor d D) {L : ℕ} (hLpos : 0 < L)
    (hL : Kraus.IsNBlkInjective A L) :
    Kraus.IsNBlkInjective A (L + 1) := by
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
    (hLpos : 0 < L) (hL : Kraus.IsNBlkInjective A L) (hLm : L ≤ m) :
    Kraus.IsNBlkInjective A m := by
  induction m, hLm using Nat.le_induction with
  | base => exact hL
  | succ m hLm ih =>
      exact isNBlkInjective_succ_of_isNBlkInjective A
        (lt_of_lt_of_le hLpos hLm) ih

/-- Normality implies fullness of a cumulative word span. -/
theorem cumulativeSpan_eq_top_of_isNormal (A : MPSTensor d D)
    (hN : Kraus.IsNormal A) : ∃ N, Kraus.cumulativeSpan A N = ⊤ := by
  obtain ⟨N, _hNpos, hN⟩ := hN
  exact ⟨N, eq_top_iff.mpr (le_trans
    (eq_top_iff.mp (show Kraus.wordSpan A N = ⊤ from hN))
    (Kraus.wordSpan_le_cumulativeSpan A le_rfl))⟩

/-- Zero-block injectivity forces one-dimensional bond space. -/
theorem bondDim_eq_one_of_isNBlkInjective_zero [NeZero D]
    (A : MPSTensor d D) (hA : Kraus.IsNBlkInjective A 0) :
    D = 1 := by
  by_contra hD_ne
  have hD_pos : 0 < D := NeZero.pos D
  have hD_ge : 2 ≤ D := by omega
  have htop : Kraus.wordSpan A 0 =
      (⊤ : Submodule ℂ (Matrix (Fin D) (Fin D) ℂ)) := hA
  exact Kraus.wordSpan_zero_ne_top_of_two_le A hD_ge htop

end MPSTensor

end

section

open scoped Matrix

namespace MPSTensor

variable {d D : ℕ}

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
    (hNormal : Kraus.IsNormal A) :
    Kraus.cumulativeVectorSpan A φ (D - 1) = ⊤ := by
  obtain ⟨N, hN⟩ := cumulativeSpan_eq_top_of_isNormal A hNormal
  exact Kraus.eigenvector_spreading_of_cumulativeSpan_eq_top A φ hφ hN

end MPSTensor

end

section

open scoped Matrix
open Kraus (blockTensor flattenBlockedWord evalWord_blockTensor length_flattenBlockedWord)

namespace MPSTensor

variable {d D : ℕ}

/-! ## Blocking transfer: word spans for blocked tensors -/

/-- A blocked word product of length `n` is an ordinary word product of length `n*L`. -/
theorem wordSpan_blockTensor_le (A : MPSTensor d D) (L n : ℕ) :
    Kraus.wordSpan (blockTensor (d := d) (n := Fin D) A L) n ≤ Kraus.wordSpan A (n * L) := by
  classical
  apply Submodule.span_le.mpr
  rintro M ⟨σ, rfl⟩
  have hblock :
      Kraus.evalWord (blockTensor (d := d) (n := Fin D) A L) (List.ofFn σ) =
        Kraus.evalWord A (flattenBlockedWord d L (List.ofFn σ)) :=
    evalWord_blockTensor (A := A) (L := L) (List.ofFn σ)
  have hlen : (flattenBlockedWord d L (List.ofFn σ)).length = n * L := by
    simpa [List.length_ofFn] using
      (length_flattenBlockedWord (d := d) (L := L) (List.ofFn σ))
  simpa [hblock, hlen] using (Kraus.evalWord_mem_wordSpan A (flattenBlockedWord d L (List.ofFn σ)))

/-- If the blocked tensor has full word span at level `n`, then the original tensor
has full word span at level `n*L`. -/
theorem wordSpan_eq_top_of_blockTensor_wordSpan_eq_top
    (A : MPSTensor d D) (L n : ℕ)
    (h : Kraus.wordSpan (blockTensor (d := d) (n := Fin D) A L) n = ⊤) :
    Kraus.wordSpan A (n * L) = ⊤ := by
  refine eq_top_iff.mpr ?_
  simpa [h] using (wordSpan_blockTensor_le (A := A) (L := L) (n := n))

end MPSTensor

end

section

open scoped Matrix
open MPSTensor

namespace MPSTensor

variable {d D : ℕ}

/-! ## MPS-specific consequences -/

/-- PGVWC07 injectivity propagation: for a right-normalized tensor, block
injectivity at length `L` implies block injectivity at every length `m ≥ L`. -/
theorem isNBlkInjective_of_ge_of_unital
    (A : MPSTensor d D)
    (hUnital : ∑ a : Fin d, A a * (A a)ᴴ = 1)
    {L m : ℕ} (hL : Kraus.IsNBlkInjective A L) (hm : L ≤ m) :
    Kraus.IsNBlkInjective A m := by
  exact Kraus.wordSpan_eq_top_of_ge_of_unital A hUnital hL hm

/-- If `Kraus.cumulativeSpan A N = ⊤` and the identity belongs to the one-letter span,
then `A` is normal. -/
theorem isNormal_of_cumulativeSpan_eq_top_of_aperiodic
    (A : MPSTensor d D) {N : ℕ}
    (hcs : Kraus.cumulativeSpan A N = ⊤)
    (hone : (1 : Matrix (Fin D) (Fin D) ℂ) ∈ Kraus.wordSpan A 1) :
    Kraus.IsNormal A := by
  refine ⟨N + 1, Nat.zero_lt_succ N, ?_⟩
  change Kraus.wordSpan A (N + 1) = ⊤
  rw [← Kraus.cumulativeSpan_eq_wordSpan_of_one_mem_wordSpan_one A hone]
  exact eq_top_iff.mpr (hcs.ge.trans (Kraus.cumulativeSpan_mono A N))

/-- If the generated matrix algebra is full and the identity belongs to the
one-letter span, then `A` is normal. -/
theorem isNormal_of_algSpan_eq_top_of_aperiodic
    (A : MPSTensor d D)
    (halg : Matrix.algSpan A = ⊤)
    (hone : (1 : Matrix (Fin D) (Fin D) ℂ) ∈ Kraus.wordSpan A 1) :
    Kraus.IsNormal A := by
  obtain ⟨N, hN⟩ := Kraus.exists_cumulativeSpan_eq_top_of_algSpan_eq_top A halg
  exact isNormal_of_cumulativeSpan_eq_top_of_aperiodic A hN hone

end MPSTensor

end

section

open scoped Matrix

namespace MPSTensor

variable {d D : ℕ}

/-- If `A` is normal, its cumulative word span equals the full matrix algebra by step `D²`.

Paper: arXiv:0909.5347, Lemma 1, proof paragraphs 1–3. -/
theorem cumulativeSpan_eq_top_of_isNormal_bound [NeZero D]
    (A : MPSTensor d D) (hN : Kraus.IsNormal A) :
    Kraus.cumulativeSpan A (D ^ 2) = ⊤ := by
  obtain ⟨N, _, hN⟩ := hN
  exact Kraus.cumulativeSpan_eq_top_of_wordSpan_eq_top_bound A hN

/-- **Lemma 1, sharp span form** (arXiv:0909.5347): if `A` is normal, its cumulative
word span is full by step `D² − dim(S₁(A)) + 1`. -/
theorem cumulativeSpan_eq_top_of_isNormal_sharp [NeZero D]
    (A : MPSTensor d D) (hN : Kraus.IsNormal A) :
    Kraus.cumulativeSpan A (D ^ 2 - Module.finrank ℂ (Kraus.wordSpan A 1) + 1) = ⊤ := by
  obtain ⟨N, _, hN⟩ := hN
  exact Kraus.cumulativeSpan_eq_top_of_wordSpan_eq_top_sharp A hN

end MPSTensor

end
