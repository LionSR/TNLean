/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import TNLean.MPS.Core.ScaledNormality
import TNLean.MPS.FundamentalTheorem.Reduction.MultiBlock

/-!
# Weighted multi-block compression from a periodic-vector hypothesis

This file states the weighted form of the multi-block asymmetric compression theorem
(`Notes/OpenProblemsTN/problems/p5_asymmetric_fundamental_theorem.tex`, §7.6, Theorem 7.8,
`cor:p5-weighted-compression`): the blocks of the target carry nonzero weights `μ s`, the
hypothesis is the equality of periodic vectors at every positive length,
`V_N(B) = ∑_{s ∈ S} μ_s^N V_N(A_{(s)})`, and the compression of a word of `B` onto the slot `s`
returns `μ_s^{|w|}` times the corresponding word of `A_{(s)}`.

The weighted blocks `μ s • A s` are normal because a nonzero rescaling preserves normality
(`MPSTensor.isNormal_smul_iff`), and the periodic-vector hypothesis gives the word-trace
hypothesis of `MPSTensor.exists_multiBlockCompression_of_isNormal` because every nonempty word
is `List.ofFn` of its own index function.

## Main results

* `MPSTensor.MultiBlockCompression.left_mul_evalWord_mul_right_smul`: the weighted word
  compression `W_s B^w V_s = μ_s^{|w|} A_{(s)}^w`, the note's `eq:p5-weighted-word-compression`.
* `MPSTensor.exists_weightedMultiBlockCompression_of_isNormal`: Theorem 7.8 itself, with the
  hypothesis in the periodic-vector form.
-/

open scoped Matrix

namespace MPSTensor

variable {d DB : ℕ} {ι : Type*} [DecidableEq ι] {D : ι → ℕ}

/-- **The weighted word compression** (P5 note, Theorem 7.8,
`eq:p5-weighted-word-compression`). Compressing a word of `B` onto the slot `s` of a
multi-block compression whose blocks are the weighted tensors `μ s • A s` returns the
corresponding word of `A s` scaled by `μ s` to the length of the word. -/
theorem MultiBlockCompression.left_mul_evalWord_mul_right_smul {B : MPSTensor d DB}
    {S : Finset ι} {μ : ι → ℂ} {A : ∀ s, MPSTensor d (D s)}
    (P : MultiBlockCompression B S fun s => μ s • A s) (s : {s // s ∈ S})
    (w : List (Fin d)) :
    P.left s * Kraus.evalWord B w * P.right s = μ s.1 ^ w.length • Kraus.evalWord (A s.1) w := by
  rw [P.left_mul_evalWord_mul_right s]
  exact Kraus.evalWord_smul (μ s.1) (A s.1) w

/-- **Weighted canonical-form compression** (P5 note, Theorem 7.8,
`cor:p5-weighted-compression`). Let `A s`, `s ∈ S`, be normal tensors of positive bond
dimension, let `μ s` be nonzero weights, and let `B` be an arbitrary tensor whose periodic
vectors satisfy `V_N(B) = ∑_{s ∈ S} μ_s^N V_N(A_{(s)})` at every positive length `N`. Then `B`
admits a multi-block compression onto the weighted blocks `μ s • A s`.

All the conclusions of the note are read off this datum: `MultiBlockCompression.isReduction`
gives `W_s V_s = 1` together with the intertwining of every word,
`MultiBlockCompression.left_mul_evalWord_mul_right_smul` gives
`W_s B^w V_s = μ_s^{|w|} A_{(s)}^w`, `MultiBlockCompression.left_mul_right_of_ne` gives the
mutual biorthogonality of distinct slots, `MultiBlockCompression.evalWord_remainder_eq_zero`
gives the nilpotency of the remainder, and `MultiBlockCompression.dim_eq` gives the dimension
count. -/
theorem exists_weightedMultiBlockCompression_of_isNormal (S : Finset ι) (μ : ι → ℂ)
    (A : ∀ s, MPSTensor d (D s)) (hμ : ∀ s ∈ S, μ s ≠ 0)
    (hA : ∀ s ∈ S, Kraus.IsNormal (A s)) (hD : ∀ s ∈ S, 0 < D s) (B : MPSTensor d DB)
    (hmpv : ∀ N : ℕ, 0 < N → ∀ σ : Fin N → Fin d,
      mpv B σ = ∑ s ∈ S, μ s ^ N * mpv (A s) σ) :
    Nonempty (MultiBlockCompression B S fun s => μ s • A s) := by
  refine exists_multiBlockCompression_of_isNormal S (fun s => μ s • A s)
    (fun s hs => (isNormal_smul_iff (hμ s hs) (A s)).2 (hA s hs)) hD B ?_
  intro w hw
  have h := hmpv w.length (List.length_pos_of_ne_nil hw) w.get
  simp only [mpv, coeff, List.ofFn_get] at h
  rw [h]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [show Kraus.evalWord (μ s • A s) w = μ s ^ w.length • Kraus.evalWord (A s) w from
    Kraus.evalWord_smul (μ s) (A s) w, Matrix.trace_smul, smul_eq_mul]

end MPSTensor
