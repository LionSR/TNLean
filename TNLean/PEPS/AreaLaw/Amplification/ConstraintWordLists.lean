/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Analysis.ContractionWordDecay
import QICLean.Probability.PoissonWordPartition

/-!
# One clock realization for the full, retained and truncated products

The local-products lemma compares three chronological products on the same clock
realization: the full product `D` of the roots `(I - k_i)^{1/2}`, the retained product
`D_ret` over the events anchored near `S`, and its radius truncation. The truncation
estimate is stated for the product over the retained letters of a full Poisson word,
and the omission estimate for the product over a list of letters filtered by the same
predicate. This module identifies the two descriptions: a chronological product is the
product of its roots in reverse list order, and the retained product of a full word is
the product over the filtered list of its letters.

It also records that every chronological product of roots of positive contractions
annihilating `Ω`, and its adjoint, fix `Ω` and the projection onto `Ω`.

## Main statements

* `Matrix.contractionWord_eq_prod_reverse`: a chronological product as a list product.
* `Matrix.contractionWord_partitionWords_fst`: the retained product of a full word is the
  product over its filtered letters.
* `Matrix.contractionWord_mul_vecMulVec_self` and
  `Matrix.conjTranspose_contractionWord_mulVec_self`: the products fix the ground
  projection and their adjoints fix the ground vector.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*, September 24, 2026,
  Lemma 10.1 (`lem:amplification-local-products`), `09-amplification.tex`, lines 50–56
  and 70 (one clock realization for the three products), and lines 501–504 (every exact
  factor fixes the ground vector in both directions).
  Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

Independently formalized from the manuscript; no upstream Lean proof text is reused.
-/

open scoped MatrixOrder ComplexOrder

namespace Matrix

variable {n ι : Type*} [Fintype n] [DecidableEq n]

/-- A chronological product of roots is the product of the roots of its letters in reverse
order, so that later letters act on the left.
Source: `09-amplification.tex`, lines 52–54. -/
theorem contractionWord_eq_prod_reverse (k : ι → Matrix n n ℂ) :
    ∀ (m : ℕ) (w : Fin m → ι),
      contractionWord k m w = ((List.ofFn w).reverse.map fun i => CFC.sqrt (1 - k i)).prod
  | 0, w => by simp
  | m + 1, w => by
    rw [contractionWord, contractionWord_eq_prod_reverse k m, List.ofFn_succ',
      List.concat_eq_append, List.reverse_append]
    simp

/-- **The retained product on the full realization.** The chronological product over the
letters of a full word that satisfy `P` equals the product over the `P`-filtered list of
its letters, with later letters on the left.
Source: `09-amplification.tex`, lines 52–56 and 70. -/
theorem contractionWord_partitionWords_fst (P : ι → Prop) [DecidablePred P]
    (k : ι → Matrix n n ℂ) (w : PoissonWord.Word ι) :
    contractionWord (fun i : {i // P i} => k i) (PoissonWord.partitionWords P w).1.1
        (PoissonWord.partitionWords P w).1.2 =
      (((List.ofFn w.2).filter fun i => decide (P i)).reverse.map
        fun i => CFC.sqrt (1 - k i)).prod := by
  rw [contractionWord_eq_prod_reverse, ← PoissonWord.ofFn_partitionWords_fst,
    List.map_reverse, List.map_reverse, List.map_map]
  rfl

/-- A chronological product of roots of contractions annihilating `Ω` fixes the
projection `|Ω⟩⟨Ω|` from the left.
Source: `09-amplification.tex`, lines 501–503. -/
theorem contractionWord_mul_vecMulVec_self (k : ι → Matrix n n ℂ) (hk : ∀ i, k i ≤ 1)
    {Ω : n → ℂ} (hΩ : ∀ i, k i *ᵥ Ω = 0) (m : ℕ) (w : Fin m → ι) :
    contractionWord k m w * vecMulVec Ω (star Ω) = vecMulVec Ω (star Ω) := by
  have h0 : ∀ i, toEuclideanLin (k i) (WithLp.toLp 2 Ω) = 0 := fun i => by
    ext j; simp [hΩ i]
  have h := contractionWord_fix k hk h0 m w
  have h' : contractionWord k m w *ᵥ Ω = Ω := by
    simpa using congrArg WithLp.ofLp h
  rw [mul_vecMulVec, h']

/-- The adjoint of a chronological product of roots of positive contractions annihilating
`Ω` fixes `Ω`. Each root is Hermitian and fixes `Ω`.
Source: `09-amplification.tex`, lines 501–504. -/
theorem conjTranspose_contractionWord_mulVec_self (k : ι → Matrix n n ℂ)
    (hk : ∀ i, k i ≤ 1) {Ω : n → ℂ} (hΩ : ∀ i, k i *ᵥ Ω = 0) :
    ∀ (m : ℕ) (w : Fin m → ι), (contractionWord k m w)ᴴ *ᵥ Ω = Ω
  | 0, w => by simp
  | m + 1, w => by
    have hG : (CFC.sqrt (1 - k (w (Fin.last m))))ᴴ = CFC.sqrt (1 - k (w (Fin.last m))) :=
      (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg _)).star_eq
    rw [contractionWord, conjTranspose_mul, hG, ← mulVec_mulVec,
      sqrt_one_sub_mulVec_eq_self (hk _) (hΩ _),
      conjTranspose_contractionWord_mulVec_self k hk hΩ m]

end Matrix
