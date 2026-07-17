/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.MatrixAux
import TNLean.MPS.MPDO.CommonWeightAbsorption
import TNLean.MPS.MPDO.SourceBNTBlocking

/-!
# Nonzero closing data for a basis of normal tensors

Eventual linear independence of a basis of normal tensors supplies one common
positive word length at which every representative has a nonzero matrix
entry.  When the canonical-form weights are independent of the copy index,
the coefficient of every representative is nonzero at the corresponding
total chain length.  Their product is the nonzero scalar selected before the
principal BNT--Markov identity in arXiv:1606.00608, Appendix C.2.

This file proves the selection of the nonzero scalar.  It does not yet identify
that scalar with an entry of the closing matrix in a three-site family closure.

## References

* Cirac--Perez-Garcia--Schuch--Verstraete, arXiv:1606.00608,
  BNT definition at lines 271--274 and Appendix C.2, lines 1714--1718.
-/

open scoped Matrix BigOperators

namespace MPSTensor

variable {d D g : ℕ} {dim : Fin g → ℕ}

/-- A basis of normal tensors has one common positive word length at which
every representative has a nonzero matrix entry.

Source: arXiv:1606.00608, BNT definition at lines 271--274 and Appendix C.2,
lines 1714--1718. -/
theorem IsCPSVBasisOfNormalTensors.exists_common_nonzero_word_entry
    {A : MPSTensor d D} {B : (j : Fin g) → MPSTensor d (dim j)}
    (hBNT : IsCPSVBasisOfNormalTensors A (fun j ↦ ⟨dim j, B j⟩)) :
    ∃ L : ℕ, 0 < L ∧ ∀ j : Fin g,
      ∃ (σ : Fin L → Fin d) (α β : Fin (dim j)),
        evalWord (B j) (List.ofFn σ) α β ≠ 0 := by
  obtain ⟨L₀, hLI⟩ := hBNT.eventually_li
  refine ⟨L₀ + 1, by omega, ?_⟩
  intro j
  have hState : mpvState (d := d) (B j) (L₀ + 1) ≠ 0 :=
    (hLI (L₀ + 1) (by omega)).ne_zero j
  have hCoeff : ∃ σ : Fin (L₀ + 1) → Fin d, mpv (B j) σ ≠ 0 := by
    by_contra hzero
    push Not at hzero
    apply hState
    ext σ
    rw [mpvState_apply]
    exact hzero σ
  obtain ⟨σ, hσ⟩ := hCoeff
  have hWord : evalWord (B j) (List.ofFn σ) ≠ 0 := by
    intro hzero
    apply hσ
    change Matrix.trace (evalWord (B j) (List.ofFn σ)) = 0
    rw [hzero]
    simp
  obtain ⟨α, β, hαβ⟩ := Matrix.exists_entry_ne_zero_of_ne_zero _ hWord
  exact ⟨σ, α, β, hαβ⟩

namespace SectorDecomposition

/-- At one common positive tail length `L`, every representative has a
nonzero weighted tail entry at total chain length `L + 3`:
\[
  q_j\bigl[A_j^{\sigma_1}\cdots A_j^{\sigma_L}\bigr]_{\alpha,\beta}
  \ne 0,
  \qquad q_j=\sum_q\mu_{j,q}^{L+3}.
\]

This is the nonzero scalar denoted by
\(m_j=q_j\widetilde m_j\) in the source.  Identifying it with an entry of a
three-site family-closing matrix is a separate statement.

Source: arXiv:1606.00608, Appendix C.2, lines 1714--1718. -/
theorem exists_common_nonzero_weighted_tail_entry
    (S : SectorDecomposition d)
    (hWeight : ∀ (j : Fin S.basisCount) (q q' : Fin (S.copies j)),
      S.weight j q = S.weight j q')
    {A : MPSTensor d D}
    (hBNT : IsCPSVBasisOfNormalTensors A
      (fun j ↦ ⟨S.basisDim j, S.basis j⟩)) :
    ∃ L : ℕ, 0 < L ∧ ∀ j : Fin S.basisCount,
      ∃ (σ : Fin L → Fin d) (α β : Fin (S.basisDim j)),
        S.coeff (L + 3) j *
          evalWord (S.basis j) (List.ofFn σ) α β ≠ 0 := by
  obtain ⟨L, hL, hWord⟩ := hBNT.exists_common_nonzero_word_entry
  refine ⟨L, hL, ?_⟩
  intro j
  obtain ⟨σ, α, β, hEntry⟩ := hWord j
  exact ⟨σ, α, β,
    mul_ne_zero
      (S.coeff_ne_zero_of_weight_copy_independent hWeight (L + 3) j)
      hEntry⟩

end SectorDecomposition

end MPSTensor
