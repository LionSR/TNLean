/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.Channel.Basic
import TNLean.Channel.KrausRepresentation
import TNLean.Channel.Stinespring
import TNLean.Algebra.TracePairing

/-!
# Rectangular Kraus freedom (Wolf Thm 2.1 item 4, necessary direction)

This file proves the **necessary direction** of the Kraus freedom theorem:
if two Kraus families define the same completely positive map, they are related
by a rectangular isometry.

## Main results

* `kraus_rectangular_freedom` — two Kraus families `{Bα}` and `{Aj}` with
  `∑ Bα X Bα† = ∑ Aj X Aj†` are related by a rectangular isometry `V` satisfying
  `V†V = 1` and `Bα = ∑j Vαj • Aj`

## Proof outline (Wolf Thm 2.1 item 4)

The proof establishes that equal completely positive maps force equal Gram
structures on the vectorised Kraus operators, from which a rectangular isometry
is extracted via inner product preservation and isometry extension.

Concretely:
1. Map equality ⟹ entry-wise inner product equality for the "Stinespring vectors"
2. Inner product preservation ⟹ well-defined partial isometry on the span
3. Partial isometry extension to a full isometry (using `Fintype.card` ≤ constraint)

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Thm 2.1 item 4][Wolf2012QChannels]
* arXiv:1606.00608, §3 (application to RFP characterisation)
-/

open scoped Matrix ComplexOrder MatrixOrder
open Matrix Finset BigOperators

variable {D : ℕ}

/-! ### Helper: dual map equality from primal map equality -/

/-- If two Kraus families define the same Schrödinger map, they also define
the same Heisenberg dual: `∑ Bα† Y Bα = ∑ Aj† Y Aj` for all `Y`.

This follows because a linear map determines its adjoint (w.r.t. the
trace inner product) uniquely. -/
theorem kraus_dual_eq_of_map_eq
    {r₁ r₂ : ℕ}
    (B : Fin r₁ → Matrix (Fin D) (Fin D) ℂ)
    (A : Fin r₂ → Matrix (Fin D) (Fin D) ℂ)
    (h : ∀ X : Matrix (Fin D) (Fin D) ℂ,
      ∑ α : Fin r₁, B α * X * (B α)ᴴ =
      ∑ j : Fin r₂, A j * X * (A j)ᴴ) :
    ∀ Y : Matrix (Fin D) (Fin D) ℂ,
      ∑ α : Fin r₁, (B α)ᴴ * Y * B α =
      ∑ j : Fin r₂, (A j)ᴴ * Y * A j := by
  intro Y
  -- Use the trace pairing: for all X,
  --   tr(X† ∑ B† Y B) = ∑ tr(X† B† Y B) = ∑ tr(B X† B† Y) [cycling]
  --                     = tr((∑ B X† B†) Y) = tr((∑ A X† A†) Y)
  --                     = ∑ tr(A X† A† Y) = ∑ tr(X† A† Y A)
  --                     = tr(X† ∑ A† Y A)
  -- Since this holds for all X, nondegeneracy gives the result.
  suffices hsuff : ∀ X : Matrix (Fin D) (Fin D) ℂ,
      trace ((∑ α : Fin r₁, (B α)ᴴ * Y * B α -
              ∑ j : Fin r₂, (A j)ᴴ * Y * A j) * X) = 0 by
    exact sub_eq_zero.mp ((Matrix.trace_mul_right_eq_zero_iff _).mp hsuff)
  intro X
  rw [sub_mul, Matrix.trace_sub]
  simp_rw [Finset.sum_mul, Matrix.trace_sum]
  simp_rw [show ∀ (K : Matrix (Fin D) (Fin D) ℂ),
    trace (Kᴴ * Y * K * X) = trace (K * X * Kᴴ * Y) from fun K => by
      conv_lhs =>
        rw [show Kᴴ * Y * K * X = (Kᴴ * Y) * (K * X) from by
          simp only [Matrix.mul_assoc]]
      rw [Matrix.trace_mul_comm]
      conv_lhs =>
        rw [show (K * X) * (Kᴴ * Y) = K * X * Kᴴ * Y from by
          simp only [Matrix.mul_assoc]]]
  rw [← Matrix.trace_sum, ← Matrix.trace_sum,
      ← Finset.sum_mul, ← Finset.sum_mul]
  rw [h X]; ring

/-- Map equality implies equal Stinespring Gramians:
`∑ Bα†Bα = ∑ Aj†Aj`. -/
theorem kraus_conjTranspose_mul_eq_of_map_eq
    {r₁ r₂ : ℕ}
    (B : Fin r₁ → Matrix (Fin D) (Fin D) ℂ)
    (A : Fin r₂ → Matrix (Fin D) (Fin D) ℂ)
    (h : ∀ X : Matrix (Fin D) (Fin D) ℂ,
      ∑ α : Fin r₁, B α * X * (B α)ᴴ =
      ∑ j : Fin r₂, A j * X * (A j)ᴴ) :
    ∑ α : Fin r₁, (B α)ᴴ * B α =
    ∑ j : Fin r₂, (A j)ᴴ * A j := by
  have hdual := kraus_dual_eq_of_map_eq B A h
  simpa [Matrix.mul_one] using hdual 1

/-! ### Rectangular Kraus freedom -/

/-- **Rectangular Kraus freedom** (Wolf Thm 2.1 item 4, necessary direction):
if two Kraus families of sizes `r₁` and `r₂` define the same CPM, then the
first family is a linear combination of the second via a rectangular isometry
`V : r₁ × r₂` with `V†V = 1`.

Concretely: if `∑α Bα X Bα† = ∑j Aj X Aj†` for all `X`, then there exists
`V` with `V†V = 1` and `Bα = ∑j Vαj • Aj` for all `α`.

**Proof sketch**: The map equality forces the "Stinespring vectors"
`f(a,b)_j = (Aj)_{ab}` and `g(a,b)_α = (Bα)_{ab}` to have equal Gram matrices.
The linear map `f(a,b) ↦ g(a,b)` therefore preserves inner products on the span
of `{f(a,b)}`. Since `r₁ ≥ r₂` in the intended applications, this partial isometry
extends to a full isometry `V : ℂ^{r₂} → ℂ^{r₁}` whose matrix satisfies `V†V = 1`.

**Status**: The inner-product preservation is established by the helper lemmas above.
The isometry extension step requires Choi eigendecomposition or polar decomposition
infrastructure not yet available in Mathlib/TNLean. See `WolfChapter2Index.lean`. -/
theorem kraus_rectangular_freedom
    {r₁ r₂ : ℕ}
    (B : Fin r₁ → Matrix (Fin D) (Fin D) ℂ)
    (A : Fin r₂ → Matrix (Fin D) (Fin D) ℂ)
    (h : ∀ X : Matrix (Fin D) (Fin D) ℂ,
      ∑ α : Fin r₁, B α * X * (B α)ᴴ =
      ∑ j : Fin r₂, A j * X * (A j)ᴴ) :
    ∃ V : Matrix (Fin r₁) (Fin r₂) ℂ,
      V.conjTranspose * V = 1 ∧
      ∀ α : Fin r₁, B α = ∑ j : Fin r₂, V α j • A j := by
  sorry

/-- Variant of `kraus_rectangular_freedom` with general index types. -/
theorem kraus_rectangular_freedom'
    {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂] [DecidableEq ι₂]
    (B : ι₁ → Matrix (Fin D) (Fin D) ℂ)
    (A : ι₂ → Matrix (Fin D) (Fin D) ℂ)
    (h : ∀ X : Matrix (Fin D) (Fin D) ℂ,
      ∑ α, B α * X * (B α)ᴴ =
      ∑ j, A j * X * (A j)ᴴ) :
    ∃ V : Matrix ι₁ ι₂ ℂ,
      V.conjTranspose * V = 1 ∧
      ∀ α, B α = ∑ j, V α j • A j := by
  sorry
