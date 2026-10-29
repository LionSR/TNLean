/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Basic.Complex.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.LinearAlgebra.Matrix.Bilinear
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Span.Basic

/-!
# Rectangular overlap reconstruction for varying-bond open chains

The local reconstruction in PGVWC07's open-boundary uniqueness proof is
rectangular. Equality of two adjacent two-site trace representations,
together with C1 on their middle site, identifies their boundary matrix
products. The canonical row-isometry identity then constructs the common
three-site boundary by an explicit sum involving adjoints. No one-sided
inverse or translation-invariant square padding is used.

This module supplies that finite reconstruction step and preservation of
the row-isometry identity under blocking. It does not define a new chain
predicate or assert the full varying-bond parent-Hamiltonian kernel theorem.

Source: PGVWC07, arXiv:quant-ph/0608197, Theorem 9 proof,
`Papers/quant-ph_0608197/MPSarchive.tex`, lines 1212–1237,
especially the middle-site C1 argument and the displayed Y construction,
lines 1222–1234.
-/

open scoped Matrix BigOperators

namespace Matrix

variable {a b c e I J K : Type*}
  [Fintype a] [Fintype b] [Fintype c] [Fintype e]
  [Fintype I] [Fintype J] [Fintype K] [DecidableEq a]

private theorem eq_of_trace_mul_spanning_rectangular
    (B : J → Matrix b c ℂ) (hB : Submodule.span ℂ (Set.range B) = ⊤)
    (M N : Matrix c b ℂ)
    (h : ∀ j, Matrix.trace (M * B j) = Matrix.trace (N * B j)) : M = N := by
  have hlin :
      (Matrix.traceLinearMap c ℂ ℂ).comp (Matrix.mulLeftLinearMap c ℂ M) =
        (Matrix.traceLinearMap c ℂ ℂ).comp (Matrix.mulLeftLinearMap c ℂ N) := by
    apply LinearMap.ext_on_range hB
    intro j
    exact h j
  apply Matrix.ext_iff_trace_mul_right.mpr
  intro T
  exact DFunLike.congr_fun hlin T

/-- The middle-site C1 condition identifies the two actual rectangular
boundary products in overlapping two-site trace representations.
Source: PGVWC07, Theorem 9 proof, lines 1220–1224. -/
theorem obc_overlap_boundary_mul_eq
    (A : I → Matrix a b ℂ) (B : J → Matrix b c ℂ) (C : K → Matrix c e ℂ)
    (hB : Submodule.span ℂ (Set.range B) = ⊤)
    (X : K → Matrix c a ℂ) (Y : I → Matrix e b ℂ)
    (hOverlap : ∀ i j k,
      Matrix.trace (X k * A i * B j) = Matrix.trace (Y i * B j * C k))
    (i : I) (k : K) : X k * A i = C k * Y i := by
  apply eq_of_trace_mul_spanning_rectangular B hB
  intro j
  exact (hOverlap i j k).trans (Matrix.trace_mul_cycle (Y i) (B j) (C k))

/-- The source's canonical isometry construction produces one actual
three-site boundary. Its explicit value is the sum of the right
boundary times the adjoint first-site tensor.
Source: PGVWC07, Theorem 9 proof, lines 1224–1234. -/
theorem obc_threeSite_boundary_reconstruction
    (A : I → Matrix a b ℂ) (B : J → Matrix b c ℂ) (C : K → Matrix c e ℂ)
    (hA : ∑ i, A i * (A i)ᴴ = (1 : Matrix a a ℂ))
    (hB : Submodule.span ℂ (Set.range B) = ⊤)
    (X : K → Matrix c a ℂ) (Y : I → Matrix e b ℂ)
    (hOverlap : ∀ i j k,
      Matrix.trace (X k * A i * B j) = Matrix.trace (Y i * B j * C k))
    (k : K) : X k = C k * (∑ i, Y i * (A i)ᴴ) := by
  have hmatch := obc_overlap_boundary_mul_eq A B C hB X Y hOverlap
  calc
    X k = X k * (1 : Matrix a a ℂ) := (Matrix.mul_one _).symm
    _ = X k * (∑ i, A i * (A i)ᴴ) := by rw [hA]
    _ = ∑ i, (X k * A i) * (A i)ᴴ := by
      rw [Matrix.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      exact (Matrix.mul_assoc (X k) (A i) (A i)ᴴ).symm
    _ = ∑ i, (C k * Y i) * (A i)ᴴ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [hmatch i k]
    _ = C k * (∑ i, Y i * (A i)ᴴ) := by
      rw [Matrix.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      exact Matrix.mul_assoc (C k) (Y i) (A i)ᴴ

/-- The common boundary gives the actual three-site trace coefficients,
with all four virtual leg spaces allowed to differ.
Source: PGVWC07, Theorem 9 proof, lines 1224–1234. -/
theorem obc_threeSite_trace_reconstruction
    (A : I → Matrix a b ℂ) (B : J → Matrix b c ℂ) (C : K → Matrix c e ℂ)
    (hA : ∑ i, A i * (A i)ᴴ = (1 : Matrix a a ℂ))
    (hB : Submodule.span ℂ (Set.range B) = ⊤)
    (X : K → Matrix c a ℂ) (Y : I → Matrix e b ℂ)
    (hOverlap : ∀ i j k,
      Matrix.trace (X k * A i * B j) = Matrix.trace (Y i * B j * C k))
    (i : I) (j : J) (k : K) :
    Matrix.trace (X k * A i * B j) =
      Matrix.trace ((∑ t, Y t * (A t)ᴴ) * A i * B j * C k) := by
  rw [obc_threeSite_boundary_reconstruction A B C hA hB X Y hOverlap k]
  simpa only [Matrix.mul_assoc] using
    Matrix.trace_mul_comm (C k) ((∑ t, Y t * (A t)ᴴ) * A i * B j)

/-- Two adjacent local trace representations of an actual three-site
coefficient family combine into one three-site representation. The
boundary families are obtained from the local conditions rather than
supplied as global reconstruction data.
Source: PGVWC07, Theorem 9 proof, equation unique-OBC and the displayed
Y construction, lines 1212–1234. -/
theorem obc_threeSite_reconstruction_of_pair_sections
    (A : I → Matrix a b ℂ) (B : J → Matrix b c ℂ) (C : K → Matrix c e ℂ)
    (hA : ∑ i, A i * (A i)ᴴ = (1 : Matrix a a ℂ))
    (hB : Submodule.span ℂ (Set.range B) = ⊤)
    (φ : I → J → K → ℂ)
    (hLeft : ∀ k, ∃ X : Matrix c a ℂ,
      ∀ i j, φ i j k = Matrix.trace (X * A i * B j))
    (hRight : ∀ i, ∃ Y : Matrix e b ℂ,
      ∀ j k, φ i j k = Matrix.trace (Y * B j * C k)) :
    ∃ Z : Matrix e a ℂ,
      ∀ i j k, φ i j k = Matrix.trace (Z * A i * B j * C k) := by
  classical
  let X : K → Matrix c a ℂ := fun k => Classical.choose (hLeft k)
  let Y : I → Matrix e b ℂ := fun i => Classical.choose (hRight i)
  have hX (i : I) (j : J) (k : K) : φ i j k = Matrix.trace (X k * A i * B j) :=
    Classical.choose_spec (hLeft k) i j
  have hY (i : I) (j : J) (k : K) : φ i j k = Matrix.trace (Y i * B j * C k) :=
    Classical.choose_spec (hRight i) j k
  have hOverlap (i : I) (j : J) (k : K) :
      Matrix.trace (X k * A i * B j) = Matrix.trace (Y i * B j * C k) :=
    (hX i j k).symm.trans (hY i j k)
  refine ⟨∑ t, Y t * (A t)ᴴ, ?_⟩
  intro i j k
  exact (hX i j k).trans (obc_threeSite_trace_reconstruction A B C hA hB X Y hOverlap i j k)

/-- Blocking two consecutive rectangular canonical site families
preserves the row-isometry identity. This supplies the isometry step
when the open-boundary reconstruction is iterated over longer blocks.
Source: PGVWC07, Theorem 9 proof, lines 1224–1237. -/
theorem obc_block_rowIsometry [DecidableEq b]
    (A : I → Matrix a b ℂ) (B : J → Matrix b c ℂ)
    (hA : ∑ i, A i * (A i)ᴴ = (1 : Matrix a a ℂ))
    (hB : ∑ j, B j * (B j)ᴴ = (1 : Matrix b b ℂ)) :
    ∑ p : I × J, (A p.1 * B p.2) * (A p.1 * B p.2)ᴴ = (1 : Matrix a a ℂ) := by
  have hinner (i : I) : ∑ j, (A i * B j) * (A i * B j)ᴴ =
      A i * (∑ j, B j * (B j)ᴴ) * (A i)ᴴ := by
    rw [Matrix.mul_sum, Matrix.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [Fintype.sum_prod_type]
  simp only [hinner, hB, Matrix.mul_one]
  exact hA

end Matrix
