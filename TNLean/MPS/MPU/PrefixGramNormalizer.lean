/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Algebra.FrameOperator
import QICLean.Algebra.MatrixUnitaryBetween
import Mathlib.LinearAlgebra.Matrix.Vec
import Mathlib.Analysis.Matrix.PosDef
import TNLean.MPS.MPU.AffineGramHull
import TNLean.Algebra.FinSumPermutation

/-!
# Global normalization of MPU prefix Grams

A finite matrix-product factorization at one cut determines a prefix Gram
and a suffix Gram. Their trace pairing is the expectation of the full
physical input Gram. Global isometry therefore gives a trace normalizer,
and minimal row and column spanning makes the maximally mixed cap Grams
positive definite.

These are the boundary identities used by the determinant normalization
in Section 5 of `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. The
normalization theorem supplies a positive-definite metric from the actual
operator factorization; it does not assume such a metric. The physical
prefix Gram is explicitly connected to `MPUCircuit.prefixInputGram`.

The affine determinant argument and circuit-complexity theorem are separate
results and are not asserted in this module.
-/

open scoped Matrix Kronecker ComplexOrder

namespace Matrix

variable {B E : Type*} [Fintype B] [Fintype E]

private theorem trace_rowGram_kronecker (V : Matrix B E ℂ)
    (ρ : Matrix B B ℂ) (τ : Matrix E E ℂ) :
    (vecMulVec (star Vᵀ.vec) Vᵀ.vec * (ρ ⊗ₖ τ)).trace =
      (Vᴴ * ρᵀ * V * τ).trace := by
  rw [vecMulVec_mul, trace_vecMulVec, vec_vecMul_kronecker,
    star_vec_dotProduct_vec]
  rw [← trace_transpose (Vᵀᴴ * (τᵀ * Vᵀ * ρ))]
  simp only [transpose_mul, conjTranspose_transpose_eq_transpose_conjTranspose,
    transpose_transpose]
  simpa only [Matrix.mul_assoc] using trace_mul_comm (ρᵀ * (V * τ)) Vᴴ

end Matrix

namespace MPUPrefixGram

open Matrix

variable {A B C E R : Type*}
  [Fintype A] [Fintype B] [Fintype C] [Fintype E] [Fintype R]

/-- The finite operator obtained by contracting one virtual bond between
a prefix and suffix. Its physical row index is the pair of output indices,
and its physical column index is the pair of input indices.

Source: `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, Section 5,
"A minimal open-boundary representation". -/
def factorizedOperator (F : A → Matrix B R ℂ) (G : C → Matrix R E ℂ) :
    Matrix (A × C) (B × E) ℂ :=
  fun ac be ↦ (F ac.1 * G ac.2) be.1 be.2

/-- The density-weighted prefix Gram in rectangular matrix coordinates.
The transpose follows from the physical coefficient `ρ b′ b`.
The theorem `prefixGram_eq_prefixInputGram` identifies it with the existing
row-matrix definition of a prefix Gram.

Source: `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, Section 5,
"A minimal open-boundary representation". -/
def prefixGram (F : A → Matrix B R ℂ) (ρ : Matrix B B ℂ) : Matrix R R ℂ :=
  ∑ a, (F a)ᴴ * ρᵀ * F a

/-- The density-weighted suffix Gram in rectangular matrix coordinates.
Taking the normalized identity as input gives the maximally mixed suffix Gram.

Source: `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, Section 5,
"A minimal open-boundary representation". -/
def suffixGram (G : C → Matrix R E ℂ) (τ : Matrix E E ℂ) : Matrix R R ℂ :=
  ∑ c, G c * τ * (G c)ᴴ

omit [Fintype B] [Fintype E] in
private theorem factorizedOperator_gram
    (F : A → Matrix B R ℂ) (G : C → Matrix R E ℂ) :
    (factorizedOperator F G)ᴴ * factorizedOperator F G =
      ∑ a, ∑ c, vecMulVec (star (F a * G c)ᵀ.vec) (F a * G c)ᵀ.vec := by
  ext x y
  simp only [mul_apply, conjTranspose_apply, Fintype.sum_prod_type,
    Matrix.sum_apply, vecMulVec_apply, Pi.star_apply, vec, transpose_apply,
    factorizedOperator]

/-- The prefix and suffix trace pairing is the expectation of the full
physical input Gram in the product input `ρ ⊗ τ`. The identity holds for
arbitrary complex matrices, before imposing positivity or normalization.

Source: `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, Section 5,
"A minimal open-boundary representation". -/
theorem trace_prefixGram_mul_suffixGram
    (F : A → Matrix B R ℂ) (G : C → Matrix R E ℂ)
    (ρ : Matrix B B ℂ) (τ : Matrix E E ℂ) :
    (prefixGram F ρ * suffixGram G τ).trace =
      ((factorizedOperator F G)ᴴ * factorizedOperator F G * (ρ ⊗ₖ τ)).trace := by
  rw [factorizedOperator_gram]
  simp only [prefixGram, suffixGram, Matrix.sum_mul, Matrix.mul_sum, trace_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr₂
  intro a _ c _
  rw [Matrix.trace_rowGram_kronecker, trace_mul_cycle']
  simp only [conjTranspose_mul, Matrix.mul_assoc]

omit [Fintype R] in
/-- A positive-semidefinite physical input gives a positive-semidefinite
prefix Gram. Transposition preserves positivity.

Source: `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, Section 5,
"A minimal open-boundary representation". -/
theorem prefixGram_posSemidef [Finite R]
    (F : A → Matrix B R ℂ) {ρ : Matrix B B ℂ} (hρ : ρ.PosSemidef) :
    (prefixGram F ρ).PosSemidef := by
  exact posSemidef_sum Finset.univ fun a _ ↦ hρ.transpose.conjTranspose_mul_mul_same (F a)

omit [Fintype R] in
/-- A positive-semidefinite physical input gives a positive-semidefinite
suffix Gram.

Source: `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, Section 5,
"A minimal open-boundary representation". -/
theorem suffixGram_posSemidef [Finite R]
    (G : C → Matrix R E ℂ) {τ : Matrix E E ℂ} (hτ : τ.PosSemidef) :
    (suffixGram G τ).PosSemidef := by
  exact posSemidef_sum Finset.univ fun c _ ↦ hτ.mul_mul_conjTranspose_same (G c)

/-- A globally isometric factorization normalizes the prefix-suffix trace
pairing by the product of the two input traces. A unitary factorization
is a special case.

Source: `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, Section 5,
"A minimal open-boundary representation". -/
theorem trace_prefixGram_mul_suffixGram_of_isIsometry
    [DecidableEq B] [DecidableEq E]
    (F : A → Matrix B R ℂ) (G : C → Matrix R E ℂ)
    (ρ : Matrix B B ℂ) (τ : Matrix E E ℂ)
    (hU : (factorizedOperator F G).IsIsometry) :
    (prefixGram F ρ * suffixGram G τ).trace = ρ.trace * τ.trace := by
  rw [trace_prefixGram_mul_suffixGram]
  change (factorizedOperator F G)ᴴ * factorizedOperator F G = 1 at hU
  rw [hU, Matrix.one_mul, trace_kronecker]

/-- For a globally isometric factorization, the maximally mixed suffix Gram
normalizes every prefix input of trace one. No condition on operator
Schmidt values or unitarity at other lengths is used.

Source: `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, Section 5,
"A minimal open-boundary representation". -/
theorem trace_prefixGram_mul_suffixGram_normalizedIdentity
    [DecidableEq B] [DecidableEq E] [Nonempty E]
    (F : A → Matrix B R ℂ) (G : C → Matrix R E ℂ)
    (ρ : Matrix B B ℂ) (hU : (factorizedOperator F G).IsIsometry) :
    (prefixGram F ρ * suffixGram G ((Fintype.card E : ℂ)⁻¹ • 1)).trace = ρ.trace := by
  rw [trace_prefixGram_mul_suffixGram_of_isIsometry F G ρ _ hU, trace_smul, trace_one]
  simp [smul_eq_mul, (Nat.cast_ne_zero.mpr Fintype.card_ne_zero :
    (Fintype.card E : ℂ) ≠ 0)]

omit [Fintype R] in
/-- The rectangular prefix Gram agrees with the existing prefix Gram
formed from one-row matrices. This uses the sandwich identity already
proved in `MPUCircuit.prefixInputGram_eq_sum_sandwich`.

Source: `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, Section 5,
"A minimal open-boundary representation". -/
theorem prefixGram_eq_prefixInputGram
    (F : A → Matrix B R ℂ) (ρ : Matrix B B ℂ) :
    prefixGram F ρ = MPUCircuit.prefixInputGram
      (fun a b (_ : Unit) r ↦ F a b r) ρ := by
  exact (MPUCircuit.prefixInputGram_eq_sum_sandwich
    (fun a b (_ : Unit) r ↦ F a b r) ρ).symm

omit [Fintype R] in
/-- A maximally mixed prefix Gram is positive definite when the prefix rows
span the virtual coordinate space. Its unnormalized form is the transpose
of the finite frame operator of those rows.

Source: `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, Section 5,
"A minimal open-boundary representation". -/
theorem prefixGram_normalizedIdentity_posDef_of_span_eq_top [Finite R]
    [DecidableEq B] [Nonempty B]
    (F : A → Matrix B R ℂ)
    (hspan : Submodule.span ℂ (Set.range (fun ab : A × B ↦ fun r ↦ F ab.1 ab.2 r)) = ⊤) :
    (prefixGram F ((Fintype.card B : ℂ)⁻¹ • 1)).PosDef := by
  have hframe := (posDef_sum_vecMulVec_iff_span_eq_top
    (fun ab : A × B ↦ fun r ↦ F ab.1 ab.2 r)).2 hspan
  have hgram : prefixGram F (1 : Matrix B B ℂ) =
      (∑ ab : A × B, vecMulVec (fun r ↦ F ab.1 ab.2 r)
        (star (fun r ↦ F ab.1 ab.2 r)))ᵀ := by
    ext v w
    simp only [prefixGram, transpose_one, Matrix.mul_one, Matrix.sum_apply,
      mul_apply, conjTranspose_apply, transpose_apply, Fintype.sum_prod_type,
      vecMulVec_apply, Pi.star_apply, mul_comm]
  have hscaled : prefixGram F ((Fintype.card B : ℂ)⁻¹ • 1) =
      (Fintype.card B : ℂ)⁻¹ • prefixGram F (1 : Matrix B B ℂ) := by
    simp only [prefixGram, transpose_smul, Matrix.mul_smul, Matrix.smul_mul,
      Finset.smul_sum]
  rw [hscaled, hgram]
  apply hframe.transpose.smul
  rw [inv_pos]
  exact_mod_cast Fintype.card_pos

omit [Fintype R] in
/-- A maximally mixed suffix Gram is positive definite when the suffix
columns span the virtual coordinate space. Its unnormalized form is their
finite frame operator.

Source: `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, Section 5,
"A minimal open-boundary representation". -/
theorem suffixGram_normalizedIdentity_posDef_of_span_eq_top [Finite R]
    [DecidableEq E] [Nonempty E]
    (G : C → Matrix R E ℂ)
    (hspan : Submodule.span ℂ (Set.range (fun ce : C × E ↦ fun r ↦ G ce.1 r ce.2)) = ⊤) :
    (suffixGram G ((Fintype.card E : ℂ)⁻¹ • 1)).PosDef := by
  have hframe := (posDef_sum_vecMulVec_iff_span_eq_top
    (fun ce : C × E ↦ fun r ↦ G ce.1 r ce.2)).2 hspan
  have hgram : suffixGram G (1 : Matrix E E ℂ) =
      ∑ ce : C × E, vecMulVec (fun r ↦ G ce.1 r ce.2)
        (star (fun r ↦ G ce.1 r ce.2)) := by
    ext v w
    simp only [suffixGram, Matrix.mul_one, Matrix.sum_apply, mul_apply,
      conjTranspose_apply, Fintype.sum_prod_type, vecMulVec_apply, Pi.star_apply]
  have hscaled : suffixGram G ((Fintype.card E : ℂ)⁻¹ • 1) =
      (Fintype.card E : ℂ)⁻¹ • suffixGram G (1 : Matrix E E ℂ) := by
    simp only [suffixGram, Matrix.mul_smul, Matrix.smul_mul, Finset.smul_sum]
  rw [hscaled, hgram]
  apply hframe.smul
  rw [inv_pos]
  exact_mod_cast Fintype.card_pos

omit [Fintype E] in
/-- Global isometry and spanning suffix columns supply a positive-definite
trace normalizer for every trace-one prefix input. The normalizer is the
maximally mixed suffix Gram, rather than an additional assumed boundary
metric.

Source: `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, Section 5,
"A minimal open-boundary representation". -/
theorem exists_posDef_prefixInputGram_normalizer_of_isIsometry [Finite E]
    [DecidableEq B] [DecidableEq E] [Nonempty E]
    (F : A → Matrix B R ℂ) (G : C → Matrix R E ℂ)
    (hU : (factorizedOperator F G).IsIsometry)
    (hspan : Submodule.span ℂ (Set.range (fun ce : C × E ↦ fun r ↦ G ce.1 r ce.2)) = ⊤) :
    ∃ Q : Matrix R R ℂ, Q.PosDef ∧
      ∀ ρ : Matrix B B ℂ, ρ.trace = 1 →
        (MPUCircuit.prefixInputGram (fun a b (_ : Unit) r ↦ F a b r) ρ * Q).trace = 1 := by
  let := Fintype.ofFinite E
  refine ⟨suffixGram G ((Fintype.card E : ℂ)⁻¹ • 1),
    suffixGram_normalizedIdentity_posDef_of_span_eq_top G hspan, ?_⟩
  intro ρ hρ
  rw [← prefixGram_eq_prefixInputGram,
    trace_prefixGram_mul_suffixGram_normalizedIdentity F G ρ hU, hρ]

omit [Fintype R] in
/-- Spanning prefix rows supply a positive-definite physical prefix Gram.
The witnessing density matrix is the maximally mixed physical input.

Source: `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, Section 5,
"A minimal open-boundary representation". -/
theorem exists_posDef_mem_densityPrefixGrams_of_span_eq_top [Finite R]
    [Nonempty B]
    (F : A → Matrix B R ℂ)
    (hspan : Submodule.span ℂ (Set.range (fun ab : A × B ↦ fun r ↦ F ab.1 ab.2 r)) = ⊤) :
    ∃ P ∈ MPUCircuit.densityPrefixGrams (fun a b (_ : Unit) r ↦ F a b r), P.PosDef := by
  classical
  let ρ : Matrix B B ℂ := (Fintype.card B : ℂ)⁻¹ • 1
  have hcard : 0 < (Fintype.card B : ℂ) := by exact_mod_cast Fintype.card_pos
  have hρpsd : ρ.PosSemidef := PosSemidef.one.smul (inv_nonneg.mpr hcard.le)
  have hρtrace : ρ.trace = 1 := by
    simp [ρ, trace_smul, trace_one, smul_eq_mul, hcard.ne']
  refine ⟨prefixGram F ρ, ⟨ρ, hρpsd, hρtrace, ?_⟩,
    prefixGram_normalizedIdentity_posDef_of_span_eq_top F hspan⟩
  exact (prefixGram_eq_prefixInputGram F ρ).symm

omit [Fintype R] in
/-- The real affine hull of physical prefix Grams contains a positive-definite
point whenever the prefix rows span the virtual coordinate space. The
point is already realized by the maximally mixed physical input.

Source: `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, Section 5,
"A minimal open-boundary representation". -/
theorem exists_posDef_mem_prefixGramAffineHull_of_span_eq_top [Finite R]
    [Nonempty B]
    (F : A → Matrix B R ℂ)
    (hspan : Submodule.span ℂ (Set.range (fun ab : A × B ↦ fun r ↦ F ab.1 ab.2 r)) = ⊤) :
    ∃ P ∈ MPUCircuit.prefixGramAffineHull (fun a b (_ : Unit) r ↦ F a b r), P.PosDef := by
  obtain ⟨P, hP, hPD⟩ := exists_posDef_mem_densityPrefixGrams_of_span_eq_top F hspan
  exact ⟨P, subset_affineSpan ℝ _ hP, hPD⟩

end MPUPrefixGram
