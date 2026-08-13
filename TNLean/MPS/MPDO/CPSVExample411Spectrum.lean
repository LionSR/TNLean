/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Analysis.EntropyDecomposition
import TNLean.MPS.MPDO.CPSVExample411Ambient

/-!
# Exact finite-ring spectra for CPSV16 Example 4.11

This module specializes the effective binary finite-ring block formula to a ring of length four.
The resulting reduced states are diagonal, and direct enumeration of the internal transition count
gives their characteristic-polynomial roots with exact multiplicities. The ambient two-qubit-site
roots are obtained by isometric transport, with the additional zero roots stated separately.

These are project-derived finite-periodic consequences of the neighboring operators printed in
CPSV16 Example 4.11. They do not assert an entropy identity, an area law, or zero correlation
length. See `docs/paper-gaps/cpsv16_examples_4_10_4_11_entropy.tex`.

## Main results

* `effective_reducedBlockState_four_eq_diagonal`: the effective reduced state is diagonal.
* `effective_charpoly_roots_one` through `effective_charpoly_roots_four`: the four effective root
  multisets.
* `ambient_charpoly_roots_eq_zero_add_effective`: generic isometric zero-padding at ring length
  four.
* `ambient_charpoly_roots_one` through `ambient_charpoly_roots_four`: the four full ambient root
  multisets.
-/

open scoped Matrix

noncomputable section

namespace MPOTensor.CPSVExample411Spectrum

open Polynomial

/-- The length-four block probability determined by a block length and an internal transition
count. -/
private def fourBlockProbabilityOfCount (L t : ℕ) : ℝ :=
  (2 : ℝ) ^ L * ((3 : ℝ) ^ (5 - L) + (-1 : ℝ) ^ t) /
    ((2 : ℝ) ^ (t + 2) * 82)

/-- The real diagonal probability of a binary word retained from the length-four ring. -/
private def fourBlockProbability {L : ℕ} (x : Fin L → Fin 2) : ℝ :=
  fourBlockProbabilityOfCount L (CPSVExample411BinarySupport.internalTransitionCount x)

/-- At every nonempty block length at most four, the effective reduced state is the diagonal
matrix of the exact length-four finite-ring probabilities. -/
theorem effective_reducedBlockState_four_eq_diagonal {L : ℕ} (hL : 1 ≤ L) (hL4 : L ≤ 4) :
    reducedBlockState CPSVExample411BinarySupport.M 4 L hL4 =
      Matrix.diagonal (fun x ↦ (fourBlockProbability x : ℂ)) := by
  ext x y
  rw [CPSVExample411BinarySupport.reducedBlockState_apply hL hL4,
    Matrix.diagonal_apply]
  split_ifs with hxy
  · subst y
    simp only [fourBlockProbability, fourBlockProbabilityOfCount]
    rw [show 4 - L + 1 = 5 - L by omega]
    norm_num
  · rfl

/-- Binary words of length one have no internal transitions. -/
theorem transition_counts_one :
    Finset.univ.val.map (CPSVExample411BinarySupport.internalTransitionCount :
      (Fin 1 → Fin 2) → ℕ) = {0, 0} := by
  decide

/-- Binary words of length two have transition-count multiset $\{0,0,1,1\}$. -/
theorem transition_counts_two :
    Finset.univ.val.map (CPSVExample411BinarySupport.internalTransitionCount :
      (Fin 2 → Fin 2) → ℕ) = {0, 0, 1, 1} := by
  decide

/-- Binary words of length three have transition-count multiset
$\{0,0,1,1,1,1,2,2\}$. -/
theorem transition_counts_three :
    Finset.univ.val.map (CPSVExample411BinarySupport.internalTransitionCount :
      (Fin 3 → Fin 2) → ℕ) = {0, 0, 1, 1, 1, 1, 2, 2} := by
  decide

/-- Binary words of length four have two words with zero transitions, six with one, six with two,
and two with three. -/
theorem transition_counts_four :
    Finset.univ.val.map (CPSVExample411BinarySupport.internalTransitionCount :
      (Fin 4 → Fin 2) → ℕ) =
      {0, 0, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 3, 3} := by
  decide

private theorem effective_roots {L : ℕ} (hL : 1 ≤ L) (hL4 : L ≤ 4) :
    (reducedBlockState CPSVExample411BinarySupport.M 4 L hL4).charpoly.roots =
      (Finset.univ.val.map (fourBlockProbability : (Fin L → Fin 2) → ℝ)).map
        (fun r : ℝ ↦ (r : ℂ)) := by
  rw [effective_reducedBlockState_four_eq_diagonal hL hL4,
    Matrix.charpoly_roots_diagonal_ofReal]

/-- The effective one-site reduced state has root $1/2$ with multiplicity two. -/
theorem effective_charpoly_roots_one :
    (reducedBlockState CPSVExample411BinarySupport.M 4 1 (by omega)).charpoly.roots =
      2 • {(1 / 2 : ℂ)} := by
  rw [effective_roots (by omega) (by omega),
    show fourBlockProbability = fourBlockProbabilityOfCount 1 ∘
      CPSVExample411BinarySupport.internalTransitionCount from rfl,
    ← Multiset.map_map, transition_counts_one]
  norm_num [fourBlockProbabilityOfCount]
  rfl

/-- The effective two-site reduced state has roots $14/41$ and $13/82$, each with multiplicity
 two. -/
theorem effective_charpoly_roots_two :
    (reducedBlockState CPSVExample411BinarySupport.M 4 2 (by omega)).charpoly.roots =
      2 • {(14 / 41 : ℂ)} + 2 • {(13 / 82 : ℂ)} := by
  rw [effective_roots (by omega) (by omega),
    show fourBlockProbability = fourBlockProbabilityOfCount 2 ∘
      CPSVExample411BinarySupport.internalTransitionCount from rfl,
    ← Multiset.map_map, transition_counts_two]
  norm_num [fourBlockProbabilityOfCount]
  rfl

/-- The effective three-site reduced state has roots $10/41$, $4/41$, and $5/82$ with
multiplicities two, four, and two, respectively. -/
theorem effective_charpoly_roots_three :
    (reducedBlockState CPSVExample411BinarySupport.M 4 3 (by omega)).charpoly.roots =
      2 • {(10 / 41 : ℂ)} + 4 • {(4 / 41 : ℂ)} + 2 • {(5 / 82 : ℂ)} := by
  rw [effective_roots (by omega) (by omega),
    show fourBlockProbability = fourBlockProbabilityOfCount 3 ∘
      CPSVExample411BinarySupport.internalTransitionCount from rfl,
    ← Multiset.map_map, transition_counts_three]
  norm_num [fourBlockProbabilityOfCount]
  rfl

/-- The effective four-site state has roots $8/41$, $2/41$, and $1/82$ with multiplicities two,
twelve, and two, respectively. -/
theorem effective_charpoly_roots_four :
    (reducedBlockState CPSVExample411BinarySupport.M 4 4 (by omega)).charpoly.roots =
      2 • {(8 / 41 : ℂ)} + 12 • {(2 / 41 : ℂ)} + 2 • {(1 / 82 : ℂ)} := by
  rw [effective_roots (by omega) (by omega),
    show fourBlockProbability = fourBlockProbabilityOfCount 4 ∘
      CPSVExample411BinarySupport.internalTransitionCount from rfl,
    ← Multiset.map_map, transition_counts_four]
  norm_num [fourBlockProbabilityOfCount]
  rfl

/-- Isometric inclusion into the ambient two-qubit site space pads the effective characteristic
polynomial by $4^L-2^L$ zero roots. -/
theorem ambient_charpoly_eq_X_pow_mul_effective {L : ℕ} (hL4 : L ≤ 4) :
    (reducedBlockState CPSVExample411Ambient.ambientM 4 L hL4).charpoly =
      X ^ (4 ^ L - 2 ^ L) *
        (reducedBlockState CPSVExample411BinarySupport.M 4 L hL4).charpoly := by
  rw [CPSVExample411Ambient.ambientM,
    reducedBlockState_changePhysicalBasis_of_isometry CPSVExample411Ambient.inclusion
      CPSVExample411Ambient.inclusion_isometry,
    singleKrausMap_apply, Matrix.mul_assoc]
  rw [Matrix.charpoly_mul_comm_of_le
    (sitewisePhysicalMatrix CPSVExample411Ambient.inclusion L)
    (reducedBlockState CPSVExample411BinarySupport.M 4 L hL4 *
      (sitewisePhysicalMatrix CPSVExample411Ambient.inclusion L)ᴴ)]
  · simp only [Fintype.card_fun, Fintype.card_fin]
    rw [Matrix.mul_assoc,
      sitewisePhysicalMatrix_isometry CPSVExample411Ambient.inclusion
        CPSVExample411Ambient.inclusion_isometry,
      Matrix.mul_one]
  · simp only [Fintype.card_fun, Fintype.card_fin]
    exact Nat.pow_le_pow_left (by omega) L

/-- The full ambient root multiset consists of $4^L-2^L$ zeros followed by the effective roots. -/
theorem ambient_charpoly_roots_eq_zero_add_effective {L : ℕ} (hL4 : L ≤ 4) :
    (reducedBlockState CPSVExample411Ambient.ambientM 4 L hL4).charpoly.roots =
      (4 ^ L - 2 ^ L) • {(0 : ℂ)} +
        (reducedBlockState CPSVExample411BinarySupport.M 4 L hL4).charpoly.roots := by
  rw [ambient_charpoly_eq_X_pow_mul_effective hL4, Polynomial.roots_mul,
    Polynomial.roots_X_pow]
  exact mul_ne_zero (pow_ne_zero _ Polynomial.X_ne_zero)
    (Matrix.charpoly_monic _).ne_zero

/-- The ambient one-site state has two zero roots and two roots equal to $1/2$. -/
theorem ambient_charpoly_roots_one :
    (reducedBlockState CPSVExample411Ambient.ambientM 4 1 (by omega)).charpoly.roots =
      2 • {(0 : ℂ)} + 2 • {(1 / 2 : ℂ)} := by
  rw [ambient_charpoly_roots_eq_zero_add_effective, effective_charpoly_roots_one]
  norm_num

/-- The ambient two-site state has twelve zero roots; its four nonzero roots are the effective
ones. -/
theorem ambient_charpoly_roots_two :
    (reducedBlockState CPSVExample411Ambient.ambientM 4 2 (by omega)).charpoly.roots =
      12 • {(0 : ℂ)} + 2 • {(14 / 41 : ℂ)} + 2 • {(13 / 82 : ℂ)} := by
  rw [ambient_charpoly_roots_eq_zero_add_effective, effective_charpoly_roots_two]
  norm_num
  rfl

/-- The ambient three-site state has fifty-six zero roots; its eight nonzero roots are the
effective ones. -/
theorem ambient_charpoly_roots_three :
    (reducedBlockState CPSVExample411Ambient.ambientM 4 3 (by omega)).charpoly.roots =
      56 • {(0 : ℂ)} + 2 • {(10 / 41 : ℂ)} + 4 • {(4 / 41 : ℂ)} +
        2 • {(5 / 82 : ℂ)} := by
  rw [ambient_charpoly_roots_eq_zero_add_effective, effective_charpoly_roots_three]
  norm_num
  rfl

/-- The ambient four-site state has 240 zero roots; its sixteen nonzero roots are the effective
ones. -/
theorem ambient_charpoly_roots_four :
    (reducedBlockState CPSVExample411Ambient.ambientM 4 4 (by omega)).charpoly.roots =
      240 • {(0 : ℂ)} + 2 • {(8 / 41 : ℂ)} + 12 • {(2 / 41 : ℂ)} +
        2 • {(1 / 82 : ℂ)} := by
  rw [ambient_charpoly_roots_eq_zero_add_effective, effective_charpoly_roots_four]
  norm_num
  simp only [Multiset.add_assoc]

end MPOTensor.CPSVExample411Spectrum
