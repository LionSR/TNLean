/-
Copyright (c) 2025 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.PiAlgebra.FundamentalTheoremComplete

/-!
# Block separation: from `SameMPV₂` to per-block `SameMPV`

The current checked reduction from global `SameMPV₂` on block-diagonal tensors
to per-block `SameMPV` uses the mixed-transfer peeling argument in
`CanonicalFormSep.lean`.  This file only provides the elementary word identities
needed there, for example
`evalWord(A, w^L) = (evalWord(A,w))^L`.

## Main results

* `evalWord_replicate` — evalWord on replicated single letters gives matrix powers
* `evalWord_flatten_replicate` — evalWord on flattened replicated words gives matrix powers
* `mpv_const_eq_trace_pow` — mpv of constant configurations as traces of powers
* `sameMPV₂_repeated_word` — the repeated-word trace identity extracted from `SameMPV₂`

## References

* [PerezGarcia2007String] Pérez-García, Verstraete, Wolf, Cirac (quant-ph/0608197), Appendix E
* [Cirac2017MPS] De las Cuevas, Schuch, Pérez-García, Cirac (arXiv:2011.12127), Section IV
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.longLine false

open scoped Matrix BigOperators

namespace MPSTensor

variable {d : ℕ}

section BlockSeparation

variable {r : ℕ} {dim : Fin r → ℕ} [∀ k, NeZero (dim k)]

/-! #### Evaluation on replicated lists -/

/-- `evalWord A` on a replicated single letter gives a matrix power. -/
lemma evalWord_replicate (A : MPSTensor d D) (i : Fin d) (L : ℕ) :
    evalWord A (List.replicate L i) = (A i) ^ L := by
  induction L with
  | zero => simp
  | succ n ih => rw [List.replicate_succ, evalWord, ih, pow_succ']

/-- `evalWord A` on a flattened replicated word gives a matrix power. -/
lemma evalWord_flatten_replicate (A : MPSTensor d D) (w : List (Fin d)) (L : ℕ) :
    evalWord A ((List.replicate L w).flatten) = (evalWord A w) ^ L := by
  induction L with
  | zero => simp [List.replicate]
  | succ n ih =>
      simp only [List.replicate_succ, List.flatten_cons]
      rw [evalWord_append, ih, pow_succ']

/-- The mpv of a constant configuration equals a trace of a matrix power. -/
lemma mpv_const_eq_trace_pow (A : MPSTensor d D) (i : Fin d) (L : ℕ) :
    mpv A (fun _ : Fin L => i) = Matrix.trace ((A i) ^ L) := by
  simp only [mpv, coeff, List.ofFn_const, evalWord_replicate]

private lemma length_flatten_replicate {α : Type*} (w : List α) (L : ℕ) :
    ((List.replicate L w).flatten).length = w.length * L := by
  rw [List.length_flatten, List.map_replicate, List.sum_replicate, smul_eq_mul,
    Nat.mul_comm]

/-- `SameMPV₂` on block-diagonal tensors implies the repeated-word trace identity. -/
theorem sameMPV₂_repeated_word
    (μ : Fin r → ℂ)
    (A B : (k : Fin r) → MPSTensor d (dim k))
    (hSame : SameMPV₂ (toTensorFromBlocks μ A) (toTensorFromBlocks μ B))
    (w : List (Fin d)) (L : ℕ) :
    ∑ k, (μ k) ^ (w.length * L) *
      (Matrix.trace ((evalWord (A k) w) ^ L) -
       Matrix.trace ((evalWord (B k) w) ^ L)) = 0 := by
  set flat := (List.replicate L w).flatten with flat_def
  have hlen : flat.length = w.length * L := length_flatten_replicate w L
  set σ : Fin (w.length * L) → Fin d :=
    fun i => flat.get (Fin.cast hlen.symm i) with σ_def
  have hofFn : List.ofFn σ = flat := by
    rw [σ_def]
    conv_rhs => rw [← List.ofFn_getElem (xs := flat)]
    apply List.ofFn_congr (by omega)
  have hsummed := sameMPV₂_summed_blocks μ A B hSame (w.length * L) σ
  simp only [mpv, coeff, hofFn, flat_def, evalWord_flatten_replicate] at hsummed
  simp only [smul_eq_mul] at hsummed
  rw [show (∑ k, (μ k) ^ (w.length * L) *
      (Matrix.trace ((evalWord (A k) w) ^ L) -
       Matrix.trace ((evalWord (B k) w) ^ L))) =
      ∑ k, (μ k) ^ (w.length * L) * Matrix.trace ((evalWord (A k) w) ^ L) -
        ∑ k, (μ k) ^ (w.length * L) * Matrix.trace ((evalWord (B k) w) ^ L) by
      rw [← Finset.sum_sub_distrib]
      congr 1
      ext k
      ring]
  rw [hsummed, sub_self]

/-! #### Repeated words

The lemmas in this section are used by the mixed-transfer peeling proof in
`CanonicalFormSep.lean`.  They only identify evaluations on repeated words; they
do not assert per-block separation by themselves.
-/

/-!
### Status

The per-block separation statement one might hope for,

`(∀ N σ,
    ∑ k, (μ k) ^ N • (mpv (A k) σ - mpv (B k) σ) = 0) →
  ∀ k, SameMPV (A k) (B k)`,

is **false** without additional hypotheses (e.g. canonical-form normalization
preventing rescalings between the block tensors and the phases `μ k`).

Accordingly, this file currently only provides the trustworthy lemmas
`evalWord_replicate`, `evalWord_flatten_replicate`, `mpv_const_eq_trace_pow`,
and `sameMPV₂_repeated_word`.

A checked counterexample to the naive full separation statement is retained in
`TNLean.Archive.BlockSepCounterexample`.

For end-to-end results from `SameMPV₂`, use
`fundamentalTheorem_multiBlock_fromSameMPV₂` (in
`PiAlgebra/FundamentalTheoremComplete.lean`), which takes per-block separation
as an explicit hypothesis.
-/

end BlockSeparation

end MPSTensor
