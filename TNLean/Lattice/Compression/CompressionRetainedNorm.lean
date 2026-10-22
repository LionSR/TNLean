/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.Compression.DistributedConstruction

/-!
# Absolute compression error and retained norm

Remark 5.3 of the polynomial-PEPS manuscript records how the compression theorem is used.
The compression approximates the actual physical density `ρ` of a distributed construction,
which is subnormalized, and does not normalize it. Its output `σ` need be neither positive
nor Hermitian. The later application separately proves that `ρ` is close in trace norm to a
normalized pure state `|Ω⟩⟨Ω|`; then the retained norm `Tr ρ` is close to one, and the
absolute compression error adds to that approximation error:

* `‖σ - ρ‖₁ ≤ κ` and `‖ρ - |Ω⟩⟨Ω|‖₁ ≤ η` give `‖σ - |Ω⟩⟨Ω|‖₁ ≤ κ + η`;
* `|Tr ρ - 1| ≤ η`, so the retained norm is close to one.

No bound on the private dimensions or on Schmidt ranks enters either estimate.

The compression theorem itself (Theorem 5.2) is not proved here: its error conclusion
`‖σ - ρ‖₁ ≤ κ` is a hypothesis, exactly as the remark takes it from that theorem.

## Main results

* `TNLean.Lattice.Compression.rectangularTraceNorm_sub_pure_le_of_retained_density`: the
  remark for arbitrary square matrices.
* `PartyCircuit.DistributedConstruction.rectangularTraceNorm_compression_sub_pure_le`:
  the remark for the physical density of a distributed construction, together with
  `1 - η ≤ Re Tr ρ ≤ 1`.

## References

* Polynomial-PEPS manuscript (Sept 24 2026), Remark 5.3 (`rem:compression-retained-norm`),
  `04-compression.tex:602–611`.
-/

/-!
Source: September 24, 2026, polynomial-PEPS manuscript, 04-compression.tex,
rem:compression-retained-norm; Remark 5.3.
Manuscript revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Independently formalized; no upstream Lean proof text reused.
-/

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace TNLean.Lattice.Compression

variable {a : Type*} [Fintype a] [DecidableEq a]

/-- The trace of a square matrix is bounded by its trace norm. -/
theorem norm_trace_le_rectangularTraceNorm (A : Matrix a a ℂ) :
    ‖A.trace‖ ≤ Matrix.rectangularTraceNorm A := by
  have hone : ‖(1 : Matrix a a ℂ)‖ ≤ 1 := by
    rcases isEmpty_or_nonempty a with ha | ha
    · rw [Subsingleton.elim (1 : Matrix a a ℂ) 0, norm_zero]
      exact zero_le_one
    · exact (CStarRing.norm_one (E := Matrix a a ℂ)).le
  have h := Matrix.norm_trace_conjTranspose_mul_le_rectangularTraceNorm A 1 hone
  rwa [Matrix.mul_one, Matrix.trace_conjTranspose, norm_star] at h

/-- **Absolute compression error and retained norm.** Let `ρ` be a possibly subnormalized
density and `Ω` a unit vector. If an operator `σ` approximates `ρ` with absolute trace-norm
error `κ`, and `ρ` lies within `η` of `|Ω⟩⟨Ω|`, then `‖σ - |Ω⟩⟨Ω|‖₁ ≤ κ + η` and
`|Tr ρ - 1| ≤ η`. Neither `ρ` nor `σ` is renormalized, and `σ` need be neither positive nor
Hermitian.

Source: Polynomial-PEPS manuscript (Sept 24 2026), Remark 5.3
(`rem:compression-retained-norm`), `04-compression.tex:602–611`. -/
theorem rectangularTraceNorm_sub_pure_le_of_retained_density
    (σ ρ : Matrix a a ℂ) (Ω : EuclideanSpace ℂ a) (hΩ : ‖Ω‖ = 1) {κ η : ℝ}
    (hcompression : Matrix.rectangularTraceNorm (σ - ρ) ≤ κ)
    (hpure : Matrix.rectangularTraceNorm (ρ - Matrix.euclideanOuterProduct Ω Ω) ≤ η) :
    Matrix.rectangularTraceNorm (σ - Matrix.euclideanOuterProduct Ω Ω) ≤ κ + η ∧
      ‖ρ.trace - 1‖ ≤ η := by
  refine ⟨?_, ?_⟩
  · calc
      _ = Matrix.rectangularTraceNorm
          ((σ - ρ) + (ρ - Matrix.euclideanOuterProduct Ω Ω)) := by rw [sub_add_sub_cancel]
      _ ≤ _ := (Matrix.rectangularTraceNorm_add_le _ _).trans (add_le_add hcompression hpure)
  · have htrace : (Matrix.euclideanOuterProduct Ω Ω).trace = 1 := by
      rw [Matrix.trace_euclideanOuterProduct_self, hΩ]
      norm_num
    calc
      ‖ρ.trace - 1‖ = ‖(ρ - Matrix.euclideanOuterProduct Ω Ω).trace‖ := by
        rw [Matrix.trace_sub, htrace]
      _ ≤ _ := (norm_trace_le_rectangularTraceNorm _).trans hpure

end TNLean.Lattice.Compression

namespace TNLean.Lattice.PartyCircuit.DistributedConstruction

variable {P : Type} [Fintype P] [DecidableEq P]

/-- **Remark 5.3 for a distributed construction.** Let `ρ` be the actual physical density of
a distributed construction, which is not normalized, and let `σ` be any operator with
`‖σ - ρ‖₁ ≤ κ`, as produced by the compression theorem. If `ρ` lies within `η` of the pure
state of a unit vector `Ω`, then `‖σ - |Ω⟩⟨Ω|‖₁ ≤ κ + η`, and the retained norm satisfies
`1 - η ≤ Re Tr ρ ≤ 1`. No positivity or Hermiticity of `σ` and no bound on private
dimensions or Schmidt ranks is assumed. The compression theorem enters only through its
error conclusion `‖σ - ρ‖₁ ≤ κ`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), Remark 5.3
(`rem:compression-retained-norm`), `04-compression.tex:602–611`. -/
theorem rectangularTraceNorm_compression_sub_pure_le (C : DistributedConstruction P)
    (σ : Matrix ((p : P) → Fin (C.physicalDimension p))
      ((p : P) → Fin (C.physicalDimension p)) ℂ)
    (Ω : EuclideanSpace ℂ ((p : P) → Fin (C.physicalDimension p))) (hΩ : ‖Ω‖ = 1)
    {κ η : ℝ} (hcompression : Matrix.rectangularTraceNorm (σ - C.physicalDensity) ≤ κ)
    (hpure : Matrix.rectangularTraceNorm
      (C.physicalDensity - Matrix.euclideanOuterProduct Ω Ω) ≤ η) :
    Matrix.rectangularTraceNorm (σ - Matrix.euclideanOuterProduct Ω Ω) ≤ κ + η ∧
      1 - η ≤ C.physicalDensity.trace.re ∧ C.physicalDensity.trace.re ≤ 1 := by
  obtain ⟨hσ, htrace⟩ := Compression.rectangularTraceNorm_sub_pure_le_of_retained_density
    σ C.physicalDensity Ω hΩ hcompression hpure
  refine ⟨hσ, ?_, ?_⟩
  · have hre := (Complex.abs_re_le_norm (C.physicalDensity.trace - 1)).trans htrace
    rw [Complex.sub_re, Complex.one_re] at hre
    linarith [neg_abs_le (C.physicalDensity.trace.re - 1)]
  · have h := (Complex.le_def.mp C.trace_physicalDensity_le_one).1
    rw [Complex.one_re] at h
    convert h using 3

end TNLean.Lattice.PartyCircuit.DistributedConstruction
