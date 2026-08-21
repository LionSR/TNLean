/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Kraus.Wielandt.SpanGrowth.NonzeroTraceProduct
import TNLean.Wielandt.SpanGrowth.CumulativeSpan

/-!
# Nonzero Trace Words at Bounded Length (Lemma 1)

This file gives tensor consequences of **Lemma 1** of arXiv:0909.5347
(Sanz, Pérez-García, Wolf, Cirac). If `A` is normal, then some nonempty word product of
length at most `D² − dim(S₁(A)) + 1` has nonzero trace. For a minimal Kraus family,
`dim(S₁(A)) = d`, which recovers the paper's bound. The full span-growth argument is
proved for finite matrix families in
`TNLean.Kraus.Wielandt.SpanGrowth.NonzeroTraceProduct`; the results below state its
coarse and sharp consequences for normal matrix product tensors.
-/

open scoped Matrix

namespace MPSTensor

variable {d D : ℕ}

/-- If `A` is normal, its cumulative word span equals the full matrix algebra by step `D²`.

Paper: arXiv:0909.5347, Lemma 1, proof paragraphs 1–3. -/
theorem cumulativeSpan_eq_top_of_isNormal_bound [NeZero D]
    (A : MPSTensor d D) (hN : IsNormal A) :
    Kraus.cumulativeSpan A (D ^ 2) = ⊤ := by
  obtain ⟨N, _, hN⟩ := hN
  exact Kraus.cumulativeSpan_eq_top_of_wordSpan_eq_top_bound A hN

/-- **Lemma 1, sharp span form** (arXiv:0909.5347): if `A` is normal, its cumulative
word span is full by step `D² − dim(S₁(A)) + 1`. -/
theorem cumulativeSpan_eq_top_of_isNormal_sharp [NeZero D]
    (A : MPSTensor d D) (hN : IsNormal A) :
    Kraus.cumulativeSpan A (D ^ 2 - Module.finrank ℂ (Kraus.wordSpan A 1) + 1) = ⊤ := by
  obtain ⟨N, _, hN⟩ := hN
  exact Kraus.cumulativeSpan_eq_top_of_wordSpan_eq_top_sharp A hN

end MPSTensor
