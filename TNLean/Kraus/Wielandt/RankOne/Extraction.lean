/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Analysis.MatrixNonzeroTraceEigenvalue
import TNLean.Kraus.WordSpan

/-!
# Eigenvectors from a full exact word span

A full exact word span contains a word with nonzero trace. The corresponding word matrix has a
nonzero eigenvalue and a nonzero eigenvector.
-/

open scoped Matrix

namespace Kraus

variable {d D : ℕ}

/-- If `wordSpan K N = ⊤` and `[NeZero D]`, some word of length `N` has nonzero trace.

Paper: arXiv:0909.5347, Theorem 1 proof, first paragraph. -/
theorem exists_nonzero_trace_word_of_wordSpan_eq_top [NeZero D]
    (K : Fin d → Matrix (Fin D) (Fin D) ℂ) {N : ℕ} (htop : wordSpan K N = ⊤) :
    ∃ σ : Fin N → Fin d, (MPSTensor.evalWord K (List.ofFn σ)).trace ≠ 0 := by
  by_contra hall
  push Not at hall
  have hI : (1 : Matrix (Fin D) (Fin D) ℂ) ∈ wordSpan K N :=
    htop ▸ Submodule.mem_top
  let trMap : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] ℂ :=
    Matrix.traceLinearMap (Fin D) ℂ ℂ
  have hker : wordSpan K N ≤ LinearMap.ker trMap := by
    apply Submodule.span_le.mpr
    rintro M ⟨σ, rfl⟩
    exact LinearMap.mem_ker.mpr (hall σ)
  have htrI : (1 : Matrix (Fin D) (Fin D) ℂ).trace ≠ 0 := by
    simp only [Matrix.trace_one, Fintype.card_fin, ne_eq, Nat.cast_eq_zero]
    exact_mod_cast NeZero.ne D
  exact htrI (LinearMap.mem_ker.mp (hker hI))

/-- If `wordSpan K N = ⊤` and `[NeZero D]`, some word of length `N` has a nonzero eigenvalue
and a corresponding nonzero eigenvector.

Paper: arXiv:0909.5347, Theorem 1 proof, first paragraph. -/
theorem exists_eigenvector_of_wordSpan_eq_top [NeZero D]
    (K : Fin d → Matrix (Fin D) (Fin D) ℂ) {N : ℕ} (htop : wordSpan K N = ⊤) :
    ∃ (σ : Fin N → Fin d) (μ : ℂ) (φ : Fin D → ℂ),
      μ ≠ 0 ∧ φ ≠ 0 ∧
      MPSTensor.evalWord K (List.ofFn σ) *ᵥ φ = μ • φ := by
  obtain ⟨σ, hσ⟩ := exists_nonzero_trace_word_of_wordSpan_eq_top K htop
  obtain ⟨μ, φ, hμ, hφ, heig⟩ := exists_eigenvector_of_trace_ne_zero _ hσ
  exact ⟨σ, μ, φ, hμ, hφ, heig⟩

end Kraus
