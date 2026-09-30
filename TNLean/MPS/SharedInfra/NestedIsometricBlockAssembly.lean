/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.SharedInfra.IsometricBlockAssembly
import TNLean.MPS.Core.NestedBlockMPVFlatten

/-!
# Unitary assembly of nested isometric blocks

Composing the coordinate inclusion of an outer block with the isometries
of its inner blocks gives an isometric decomposition of the full bond
space. One unitary then identifies the flattened inner direct sum with
the original outer direct sum, for all matrices on the inner blocks.

Source: arXiv:1708.00029, Lemma `lem:blocking-arbitrary` and Theorem 4.1,
lines 765--806.
-/

open scoped Matrix BigOperators

namespace MPSTensor

/-- Nested isometric decompositions assemble into one unitary, independently
of the matrices or scalar weights subsequently placed in the inner blocks.
Source: arXiv:1708.00029, Lemma `lem:blocking-arbitrary` and Theorem 4.1,
lines 765--806. -/
theorem exists_unitary_of_nested_isometric_block_decomposition
    {r : ℕ} {dim : Fin r → ℕ} (count : Fin r → ℕ)
    (innerDim : (j : Fin r) → Fin (count j) → ℕ)
    (V : (j : Fin r) → (a : Fin (count j)) → Matrix (Fin (dim j)) (Fin (innerDim j a)) ℂ)
    (hV : ∀ j a, (V j a)ᴴ * V j a = 1)
    (hsum : ∀ j, ∑ a, V j a * (V j a)ᴴ = 1) :
    ∃ Y : Matrix (Fin (∑ j, dim j)) (Fin (∑ s, nestedBlockFlatDim count innerDim s)) ℂ,
      Y * Yᴴ = 1 ∧ Yᴴ * Y = 1 ∧
      ∀ B : (j : Fin r) → (a : Fin (count j)) →
          Matrix (Fin (innerDim j a)) (Fin (innerDim j a)) ℂ,
        Y * Matrix.reindex
            (finSigmaFinEquiv (n := nestedBlockFlatDim count innerDim))
            (finSigmaFinEquiv (n := nestedBlockFlatDim count innerDim))
            (Matrix.blockDiagonal' fun s : Fin (∑ j, count j) =>
              (B (finSigmaFinEquiv.symm s).1 (finSigmaFinEquiv.symm s).2 :
                Matrix (Fin (nestedBlockFlatDim count innerDim s))
                  (Fin (nestedBlockFlatDim count innerDim s)) ℂ)) * Yᴴ =
          Matrix.reindex finSigmaFinEquiv finSigmaFinEquiv
            (Matrix.blockDiagonal' fun j => ∑ a, V j a * B j a * (V j a)ᴴ) := by
  classical
  let F : (s : Fin (∑ j, count j)) →
      Matrix (Fin (∑ j, dim j)) (Fin (nestedBlockFlatDim count innerDim s)) ℂ :=
    fun s => blockInclusion dim (finSigmaFinEquiv.symm s).1 *
      V (finSigmaFinEquiv.symm s).1 (finSigmaFinEquiv.symm s).2
  have hflat (f : ((j : Fin r) × Fin (count j)) →
      Matrix (Fin (∑ j, dim j)) (Fin (∑ j, dim j)) ℂ) :
      (∑ s : Fin (∑ j, count j), f (finSigmaFinEquiv.symm s)) = ∑ j, ∑ a, f ⟨j, a⟩ := by
    simpa only [Fintype.sum_sigma] using Equiv.sum_comp finSigmaFinEquiv.symm f
  have hF : ∀ s, (F s)ᴴ * F s = 1 := by
    intro s
    let j := (finSigmaFinEquiv.symm s).1
    let a := (finSigmaFinEquiv.symm s).2
    change (blockInclusion dim j * V j a)ᴴ * (blockInclusion dim j * V j a) = 1
    rw [Matrix.conjTranspose_mul, Matrix.mul_assoc,
      ← Matrix.mul_assoc (blockInclusion dim j)ᴴ,
      blockInclusion_conjTranspose_mul_self, Matrix.one_mul, hV]
  have hFsum : ∑ s, F s * (F s)ᴴ = 1 := by
    change (∑ s : Fin (∑ j, count j),
      (fun x : (j : Fin r) × Fin (count j) =>
        (blockInclusion dim x.1 * V x.1 x.2) *
          (blockInclusion dim x.1 * V x.1 x.2)ᴴ) (finSigmaFinEquiv.symm s)) = 1
    rw [hflat (fun x => (blockInclusion dim x.1 * V x.1 x.2) *
      (blockInclusion dim x.1 * V x.1 x.2)ᴴ)]
    calc (∑ j, ∑ a, (blockInclusion dim j * V j a) *
            (blockInclusion dim j * V j a)ᴴ) =
          ∑ j, blockInclusion dim j * (∑ a, V j a * (V j a)ᴴ) *
            (blockInclusion dim j)ᴴ := by
              simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.conjTranspose_mul,
                Matrix.mul_assoc]
      _ = 1 := by simp only [hsum, Matrix.mul_one, sum_blockInclusion_mul_conjTranspose]
  obtain ⟨Y, hY, hY', hdiag⟩ := exists_unitary_of_isometric_block_decomposition F hF hFsum
  refine ⟨Y, hY, hY', ?_⟩
  intro B
  refine (hdiag (fun s => B (finSigmaFinEquiv.symm s).1
    (finSigmaFinEquiv.symm s).2)).trans ?_
  change (∑ s : Fin (∑ j, count j),
    (fun x : (j : Fin r) × Fin (count j) =>
      (blockInclusion dim x.1 * V x.1 x.2) * B x.1 x.2 *
        (blockInclusion dim x.1 * V x.1 x.2)ᴴ) (finSigmaFinEquiv.symm s)) = _
  rw [hflat (fun x => (blockInclusion dim x.1 * V x.1 x.2) * B x.1 x.2 *
    (blockInclusion dim x.1 * V x.1 x.2)ᴴ), reindex_blockDiagonal_eq_sum_blockInclusion]
  simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.conjTranspose_mul, Matrix.mul_assoc]

end MPSTensor
