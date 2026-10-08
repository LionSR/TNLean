/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Core.Blocking
import TNLean.MPS.SharedInfra.WordTupleGauge
import TNLean.MPS.ParentHamiltonian.CyclicWordSpan

/-!
# Word spanning through an isometric sector decomposition

A simultaneous word span of compressed sectors gives the ambient word span
of their embedded diagonal matrix algebra. Matrices commuting with the support
projections are reconstructed from their compressed corners. For cyclic
sectors this supplies the initial degree-zero word span at a multiple of the
period; propagation to other lengths is a separate step.

No positivity of the sector dimensions or normalization is needed in this
finite algebraic implication. The isometric resolution and letter
intertwiners are stated explicitly.

Source: arXiv:1708.00029, Lemma bdcf; Nachtergaele,
arXiv:cond-mat/9410110, equations (3.10)--(3.11) and Section 6.
-/

open scoped Matrix BigOperators
namespace MPSTensor
variable {d D r : ℕ} {dim : Fin r → ℕ}

/-- Embed a tuple of sector matrices into the ambient virtual matrix algebra.
Source: arXiv:1708.00029, Lemma bdcf. -/
noncomputable def sectorMatrixEmbedding
    (V : (j : Fin r) → Matrix (Fin D) (Fin (dim j)) ℂ) :
    ((j : Fin r) → Matrix (Fin (dim j)) (Fin (dim j)) ℂ) →ₗ[ℂ]
      Matrix (Fin D) (Fin D) ℂ where
  toFun M := ∑ j, V j * M j * (V j)ᴴ
  map_add' M N := by
    simp [Matrix.mul_add, Matrix.add_mul, Finset.sum_add_distrib]
  map_smul' c M := by
    simp [Matrix.mul_smul, Matrix.smul_mul, Finset.smul_sum]

/-- An isometric resolution and letter intertwiners map each simultaneous word
to the corresponding ambient word. Source: arXiv:1708.00029, Lemma bdcf. -/
theorem sectorMatrixEmbedding_wordTuple
    (C : MPSTensor d D) (B : (j : Fin r) → MPSTensor d (dim j))
    (V : (j : Fin r) → Matrix (Fin D) (Fin (dim j)) ℂ)
    (hSum : ∑ j, V j * (V j)ᴴ = 1)
    (hInt : ∀ j i, C i * V j = V j * B j i)
    (q : ℕ) (σ : Fin q → Fin d) :
    sectorMatrixEmbedding V (wordTuple B q σ) = Kraus.evalWord C (List.ofFn σ) := by
  change (∑ j, V j * Kraus.evalWord (B j) (List.ofFn σ) * (V j)ᴴ) = _
  have hW (j : Fin r) := Kraus.evalWord_intertwine C (B j) (V j) (hInt j) (List.ofFn σ)
  simp only [← hW, Matrix.mul_assoc, ← Finset.mul_sum, hSum, Matrix.mul_one]
/-- Full simultaneous sector spanning contains the entire embedded matrix algebra
in the ambient word span. Source: arXiv:1708.00029, Lemma bdcf. -/
theorem sectorMatrixEmbedding_range_le_wordSpan
    (C : MPSTensor d D) (B : (j : Fin r) → MPSTensor d (dim j))
    (V : (j : Fin r) → Matrix (Fin D) (Fin (dim j)) ℂ)
    (hSum : ∑ j, V j * (V j)ᴴ = 1)
    (hInt : ∀ j i, C i * V j = V j * B j i)
    {q : ℕ} (hSpan : WordTupleSpanTop B q) :
    (sectorMatrixEmbedding V).range ≤ Kraus.wordSpan C q := by
  rw [LinearMap.range_eq_map, ← hSpan, Submodule.map_span_le]
  rintro _ ⟨σ, rfl⟩
  rw [sectorMatrixEmbedding_wordTuple C B V hSum hInt]
  exact Submodule.subset_span ⟨σ, rfl⟩

/-- A matrix commuting with the sector support projections is reconstructed from
its compressed diagonal corners. Source: arXiv:1708.00029, Lemma bdcf. -/
theorem sectorMatrixEmbedding_compress_eq
    (V : (j : Fin r) → Matrix (Fin D) (Fin (dim j)) ℂ)
    (hV : ∀ j, (V j)ᴴ * V j = 1)
    (hSum : ∑ j, V j * (V j)ᴴ = 1)
    (X : Matrix (Fin D) (Fin D) ℂ)
    (hComm : ∀ j, (V j * (V j)ᴴ) * X = X * (V j * (V j)ᴴ)) :
    sectorMatrixEmbedding V (fun j => (V j)ᴴ * X * V j) = X := by
  have hProj (j : Fin r) :
      (V j * (V j)ᴴ) * (V j * (V j)ᴴ) = V j * (V j)ᴴ := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (V j)ᴴ, hV, Matrix.one_mul]
  have hTerm (j : Fin r) : V j * ((V j)ᴴ * X * V j) * (V j)ᴴ =
      X * (V j * (V j)ᴴ) := by
    calc
      _ = (V j * (V j)ᴴ) * X * (V j * (V j)ᴴ) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hComm, Matrix.mul_assoc, hProj]
  change (∑ j, V j * ((V j)ᴴ * X * V j) * (V j)ᴴ) = X
  simp only [hTerm, ← Finset.mul_sum, hSum, Matrix.mul_one]

/-- Every matrix commuting with the sector support projections belongs to the
ambient word span under simultaneous sector spanning.
Source: arXiv:1708.00029, Lemma bdcf; Nachtergaele,
arXiv:cond-mat/9410110, equations (3.10)--(3.11). -/
theorem mem_wordSpan_of_sector_wordTupleSpanTop
    (C : MPSTensor d D) (B : (j : Fin r) → MPSTensor d (dim j))
    (V : (j : Fin r) → Matrix (Fin D) (Fin (dim j)) ℂ)
    (hV : ∀ j, (V j)ᴴ * V j = 1)
    (hSum : ∑ j, V j * (V j)ᴴ = 1)
    (hInt : ∀ j i, C i * V j = V j * B j i)
    {q : ℕ} (hSpan : WordTupleSpanTop B q)
    {X : Matrix (Fin D) (Fin D) ℂ}
    (hComm : ∀ j, (V j * (V j)ᴴ) * X = X * (V j * (V j)ᴴ)) :
    X ∈ Kraus.wordSpan C q :=
  sectorMatrixEmbedding_range_le_wordSpan C B V hSum hInt hSpan
    ⟨_, sectorMatrixEmbedding_compress_eq V hV hSum X hComm⟩

/-- Simultaneous spanning of the cyclic blocked sectors gives exact original
word spanning of the degree-zero cyclic corners at a multiple of the period.
The supports may be assigned arbitrary cyclic labels.
Source: arXiv:1708.00029, Lemma bdcf; Nachtergaele,
arXiv:cond-mat/9410110, Section 6. -/
theorem wordSpan_eq_cyclicMatrixSubspace_of_blocked_sector_span [NeZero r]
    (A : MPSTensor d D) (P : ZMod r → Matrix (Fin D) (Fin D) ℂ)
    (B : (j : Fin r) → MPSTensor (blockPhysDim d r) (dim j))
    (V : (j : Fin r) → Matrix (Fin D) (Fin (dim j)) ℂ)
    (hV : ∀ j, (V j)ᴴ * V j = 1)
    (hSum : ∑ j, V j * (V j)ᴴ = 1)
    (hInt : ∀ j i, blockTensor A r i * V j = V j * B j i)
    (hVP : ∀ j, ∃ u : ZMod r, V j * (V j)ᴴ = P u)
    (hCycle : ∀ u i, P u * A i = A i * P (u + 1))
    {q : ℕ} (hSpan : WordTupleSpanTop B q) :
    Kraus.wordSpan A (q * r) = cyclicMatrixSubspace P (q * r) := by
  apply le_antisymm (wordSpan_le_cyclicMatrixSubspace A P hCycle (q * r))
  intro X hX
  rw [← Kraus.wordSpan_blockTensor A r q]
  apply mem_wordSpan_of_sector_wordTupleSpanTop (blockTensor A r) B V hV hSum hInt hSpan
  intro j
  obtain ⟨u, hu⟩ := hVP j
  simpa only [hu, Nat.cast_mul, ZMod.natCast_self, mul_zero, add_zero] using hX u

end MPSTensor

