import MPSLean.MPS.CPPrimitive
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Instances.Matrix

open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.Frobenius
open Matrix Finset

variable {D : ℕ}

-- With Frobenius norm, the ‖·‖ is the Frobenius norm.
-- The Frobenius norm is the PiLp 2 norm, so:
-- ‖X‖_F = √(Σᵢ ‖rowᵢ‖²) = √(Σᵢⱼ ‖X i j‖²)

-- For bounding ‖X‖_F, I need a bound in terms of entries.
-- One approach: use the PiLp norm inequality
-- ‖x‖_2 ≤ √n * ‖x‖_∞ for x ∈ ℝⁿ

-- But the Frobenius norm on matrices is PiLp 2 of PiLp 2,
-- so ‖X‖_F ≤ √m * max_i ‖row_i‖_2 ≤ √m * √n * max |X i j|
-- For square D×D: ‖X‖_F ≤ D * max |X i j|

-- Can I use PiLp.norm_le or similar?

-- Actually, let me try a completely different approach.
-- Use trace(X*X) as a direct bound.
-- For Hermitian X: trace(X² ) = Σ λᵢ²
-- For PSD X: λᵢ ≥ 0, so Σ λᵢ² ≤ (Σ λᵢ)² = (trace X)²

-- But the Frobenius norm ‖X‖² = trace(X^H * X) = trace(X²) for Hermitian X
-- So ‖X‖_F ≤ |trace X| for PSD X

-- Actually, can I compute: ‖X‖² = trace(X^H * X)?
-- For Frobenius norm, this should hold.

-- Let me check:
#check @EuclideanDomain.instNorm -- no this is for domains

-- For Frobenius norm:
-- The norm is defined via PiLp 2, which gives
-- ‖X‖² = Σᵢ ‖X i‖² = Σᵢ Σⱼ ‖X i j‖²
-- = Σᵢⱼ ‖X i j‖²

-- For Hermitian X with eigenvalues λ₁,...,λ_D:
-- Σᵢⱼ |X i j|² = trace(X^H X) = trace(X²) = Σ λᵢ²

-- So ‖X‖_F² = Σ λᵢ²
-- For PSD: 0 ≤ λᵢ ≤ Σ λⱼ, so Σ λᵢ² ≤ (Σ λⱼ)²
-- ‖X‖_F ≤ Σ λᵢ = trace X (real nonneg for PSD)

-- I need to formalize this. Let me look for the Frobenius norm characterization:
-- ‖X‖² = trace(X^H * X)

-- Actually, I don't think this identity exists as a Mathlib lemma for the Frobenius norm.
-- The Frobenius norm is defined as PiLp 2 norm, not via trace.

-- Let me try yet another approach. Instead of bounding the Frobenius norm directly,
-- use that all norms are equivalent in finite dim.
-- Actually, the bornology (bounded sets) is the same for all norms giving the same topology.
-- In finite dim, all norms give the same topology.

-- But the key issue: the Bornology instance comes from the NormedAddCommGroup instance.
-- With Frobenius norm, the Bornology is the one from Frobenius metric.
-- With L∞ norm, it's the one from L∞ metric.
-- But finite-dim topological equivalence means the bornologies are the same.

-- Hmm, actually, Bornology.IsBounded for a NormedAddCommGroup is defined via
-- the metric bornology, which depends on the metric. For equivalent metrics,
-- the bornologies should be the same.

-- Actually, for a seminormed group, IsBounded is:
-- ∃ C, ∀ x ∈ s, ∀ y ∈ s, dist x y ≤ C
-- which is equivalent to ∃ C, ∀ x ∈ s, ‖x‖ ≤ C
-- for the specific norm.

-- So I need to prove ‖X‖_F ≤ C for the Frobenius norm.

-- Let me try to use the eigenvalue characterization.
-- For PSD X, the Frobenius norm squared is Σ λᵢ².
-- And Σ λᵢ² ≤ (Σ λᵢ)² = ‖trace X‖² for PSD.

-- In Lean, the spectral theorem gives X = U diag(λ) U*.
-- The Frobenius norm is unitarily invariant: ‖UXU*‖ = ‖X‖.
-- And ‖diag(λ)‖_F = √(Σ λᵢ²).

-- This is still complex. Let me try a direct computation with Finset.sum bounds.

-- Alternative SIMPLER approach: bound Frobenius norm by D × max entry.
-- ‖X‖_F² = Σᵢⱼ ‖X i j‖² ≤ D² × max ‖X i j‖²
-- ‖X‖_F ≤ D × max ‖X i j‖

-- And for PSD: max ‖X i j‖ ≤ ‖trace X‖

-- The bound ‖X‖_F ≤ D × ‖trace X‖ ≤ D × c gives boundedness.

-- To prove this, I need: ‖X‖_F² ≤ D² × (max ‖X i j‖)²
-- and max ‖X i j‖ ≤ ‖trace X‖ (from entry bound, currently sorry)

-- And for Frobenius norm: ‖X‖_F² = Σᵢⱼ ‖X i j‖²
-- ≤ Σᵢⱼ (max ‖X i j‖)² = D² × (max ‖X i j‖)²

-- For PiLp 2, the norm satisfies ‖x‖₂ ≤ √n × sup ‖xᵢ‖
-- This should be available in Mathlib.

-- Let me search for a norm bound for PiLp:
-- EuclideanSpace.norm_le: ‖x‖ ≤ ...
-- Or PiLp norm bounds

-- Actually, forget the Frobenius approach. Let me just change the approach:
-- Instead of using norm_le_iff (which is for L∞), let me compute the Frobenius norm bound
-- directly using the definition.

-- Key: I'll use that for the Frobenius norm on D×D matrices,
-- ‖X‖_F ≤ D * max_{i,j} ‖X i j‖

-- This follows from: ‖X‖_F² = Σ ‖Xij‖² ≤ D² * (max ‖Xij‖)²

-- And for PSD X: max ‖Xij‖ ≤ ‖trace X‖

-- The first inequality is a standard l2/l∞ comparison.
-- Let me look for it:

-- Actually, let me just prove IsBounded directly using isBounded_range_of_tendsto
-- or Metric.isBounded_range
-- Or: show the set is contained in Metric.closedBall 0 r for some r

-- isBounded_closedBall: Metric.closedBall is bounded
-- IsBounded.subset: subset of bounded is bounded

-- So: show {X | PSD ∧ ‖tr X‖ ≤ c} ⊆ Metric.closedBall 0 r
-- i.e., ‖X‖_F ≤ r for some r

-- I need: ‖X‖_F ≤ D * c for PSD X with ‖tr X‖ ≤ c

-- For PiLp 2 norm: ‖f‖₂ = √(Σ ‖fᵢ‖²)

-- Matrix with Frobenius = PiLp 2 (Fin D) (PiLp 2 (Fin D) ℂ)
-- So ‖X‖_F = √(Σᵢ ‖row_i‖₂²)
-- where ‖row_i‖₂ = √(Σⱼ ‖X i j‖²)

-- To bound this: use ‖X i j‖ ≤ ‖tr X‖ ≤ c (entry bound)
-- Then ‖row_i‖₂ ≤ √(D * c²) = √D * c
-- And ‖X‖_F ≤ √(D * D * c²) = D * c

-- For the Frobenius norm: we can use Metric.closedBall
-- Metric.isBounded_closedBall gives that closed balls are bounded

-- So: X ∈ set → ‖X‖_F ≤ D * c → X ∈ closedBall 0 (D * c) → bounded

-- Let me try this approach:

-- Sorry for now - focusing on getting the structure right
