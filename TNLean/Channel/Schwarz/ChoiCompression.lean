/-
Copyright (c) 2026 Sirui Lu and TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import TNLean.Channel.Schwarz.TwoPositive

/-!
# Choi compression for the rank-one test

This file records the matrix identity connecting the pure-state ampliation test
for `k`-positivity with the Choi-matrix compression appearing in Wolf Chapter 3,
Proposition 3.1, equation (3.4).

The Choi matrix is normalized using `Matrix.omegaVec`, so the vector attached to
a matrix $X\in M_{D\times k}(\mathbb{C})$ has component $D^{-1/2}X_{i,p}$ at
the pair $(i,p)$.

## Main definitions

* `ChoiJamiolkowski.rightCompression`: the right-factor Choi compression,
  written in the index convention of the blockwise ampliation.

## Main results

* `ChoiJamiolkowski.nPositiveAmpliation_rankOne_eq_rightCompression`: the
  ampliation of the associated rank-one matrix is exactly that compression.

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Chapter 3,
  Proposition 3.1, equation (3.4)][Wolf2012QChannels]
-/

open scoped Matrix BigOperators
open Matrix Finset

namespace ChoiJamiolkowski

variable {D k : ℕ}

/-- The right-factor Choi compression, written in the index convention of the
blockwise ampliation.  Here `X : Matrix (Fin D) (Fin k) ℂ` carries the original
Choi auxiliary index and the `k`-dimensional ampliation index.  The
$(i,p),(j,q)$ entry is
$\sum_{a,b} X_{a,p}\,\tau_{(i,a),(j,b)}\,\overline{X_{b,q}}$, where $\tau$ is
the Choi matrix of `T`. -/
noncomputable def rightCompression
    (T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (X : Matrix (Fin D) (Fin k) ℂ) :
    Matrix (Fin D × Fin k) (Fin D × Fin k) ℂ :=
  Matrix.of fun ip jq =>
    ∑ a : Fin D, ∑ b : Fin D,
      X a ip.2 * choiMatrix T (ip.1, a) (jq.1, b) * star (X b jq.2)

/-- The entry formula for the right-factor compression of the Choi matrix.  The
$(i,p),(j,q)$ entry is
$\sum_{a,b} X_{a,p}\,\tau_{(i,a),(j,b)}\,\overline{X_{b,q}}$, where $\tau$ is
the Choi matrix of `T`. -/
theorem rightCompression_apply
    (T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (X : Matrix (Fin D) (Fin k) ℂ) (i j : Fin D) (p q : Fin k) :
    rightCompression T X (i, p) (j, q) =
      ∑ a : Fin D, ∑ b : Fin D,
        X a p * choiMatrix T (i, a) (j, b) * star (X b q) :=
  rfl

/-- The coefficient vector obtained from the normalized maximally entangled
vector by applying `X` on the right tensor factor. -/
noncomputable def compressedOmegaVector (X : Matrix (Fin D) (Fin k) ℂ) :
    Fin D × Fin k → ℂ :=
  fun ip => ((1 : ℂ) / ((D : ℝ).sqrt : ℂ)) * X ip.1 ip.2

/-- The rank-one matrix used by the ampliation test agrees with the right-factor
compression of the Choi matrix. -/
theorem nPositiveAmpliation_rankOne_eq_rightCompression
    (T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (X : Matrix (Fin D) (Fin k) ℂ) :
    nPositiveAmpliation k T
        (Matrix.vecMulVec (compressedOmegaVector X) (star (compressedOmegaVector X))) =
      rightCompression T X := by
  classical
  ext ⟨i, p⟩ ⟨j, q⟩
  let c : ℂ := (1 : ℂ) / ((D : ℝ).sqrt : ℂ)
  have hblock :
      (Matrix.of fun a b =>
          Matrix.vecMulVec (compressedOmegaVector X) (star (compressedOmegaVector X))
            (a, p) (b, q)) =
        ∑ a : Fin D, ∑ b : Fin D,
          (X a p * star (X b q)) • Matrix.bipartiteSlice (Matrix.omegaProj D) a b := by
    calc
      (Matrix.of fun a b =>
          Matrix.vecMulVec (compressedOmegaVector X) (star (compressedOmegaVector X))
            (a, p) (b, q))
          = Matrix.of fun a b => (X a p * star (X b q)) * (c * star c) := by
            ext a b
            simp [compressedOmegaVector, c, Matrix.vecMulVec_apply]
            ring
      _ = ∑ a : Fin D, ∑ b : Fin D,
          (X a p * star (X b q)) • Matrix.bipartiteSlice (Matrix.omegaProj D) a b := by
            rw [Matrix.matrix_eq_sum_single
              (Matrix.of fun a b => (X a p * star (X b q)) * (c * star c))]
            simp [ChoiJamiolkowski.omegaSlice_eq_single, c, Matrix.smul_single,
              smul_eq_mul, mul_assoc, mul_left_comm, mul_comm]
  calc
    nPositiveAmpliation k T
        (Matrix.vecMulVec (compressedOmegaVector X) (star (compressedOmegaVector X)))
        (i, p) (j, q)
        = T (Matrix.of fun a b =>
            Matrix.vecMulVec (compressedOmegaVector X) (star (compressedOmegaVector X))
              (a, p) (b, q)) i j := rfl
    _ = T (∑ a : Fin D, ∑ b : Fin D,
          (X a p * star (X b q)) • Matrix.bipartiteSlice (Matrix.omegaProj D) a b) i j := by
        rw [hblock]
    _ = (∑ a : Fin D, ∑ b : Fin D,
          (X a p * star (X b q)) • T (Matrix.bipartiteSlice (Matrix.omegaProj D) a b)) i j := by
        simp [map_sum]
    _ = rightCompression T X (i, p) (j, q) := by
        rw [rightCompression_apply]
        simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, choiMatrix_apply]
        apply Finset.sum_congr rfl
        intro a _
        apply Finset.sum_congr rfl
        intro b _
        ring_nf

end ChoiJamiolkowski
