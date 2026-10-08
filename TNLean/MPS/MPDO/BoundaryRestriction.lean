/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.BoundaryBiorthogonal
import Mathlib.LinearAlgebra.Matrix.Bilinear

/-!
# Restricting arbitrary-boundary transport to an invariant bond block

An invariant bond-space inclusion with a left inverse transports a boundary
of the smaller tensor to a boundary of the ambient tensor. Composing with a
length-independent target boundary map then gives exact biorthogonal tensors
for the smaller source tensor. The inclusion need not be an isometry.

This is the block-restriction step in GLM23 Appendix A preceding `decompopen`.
-/

open scoped Matrix BigOperators

namespace MPSTensor

variable {d D E r : ℕ} {dim : Fin r → ℕ}

/-- An invariant bond-space inclusion transports arbitrary boundary
coefficients by the same rectangular sandwich at every length. Source:
GLM23, Appendix A, the block-projector argument preceding `decompopen`. -/
theorem mpvWithBoundary_sandwich_of_intertwiner
    (B : MPSTensor d D) (C : MPSTensor d E)
    (V : Matrix (Fin E) (Fin D) ℂ) (W : Matrix (Fin D) (Fin E) ℂ)
    (hVW : V * W = 1) (hW : ∀ i, B i * W = W * C i)
    (X : Matrix (Fin E) (Fin E) ℂ) {L : ℕ} (w : Fin L → Fin d) :
    mpvWithBoundary B (W * X * V) w = mpvWithBoundary C X w := by
  have hw := Kraus.evalWord_intertwine B C W hW (List.ofFn w)
  change Matrix.trace ((W * X * V) * Kraus.evalWord B (List.ofFn w)) =
    Matrix.trace (X * Kraus.evalWord C (List.ofFn w))
  calc
    Matrix.trace ((W * X * V) * Kraus.evalWord B (List.ofFn w)) =
        Matrix.trace ((X * V * Kraus.evalWord B (List.ofFn w)) * W) := by
      rw [Matrix.mul_assoc W X V, Matrix.mul_assoc W (X * V),
        Matrix.trace_mul_comm]
    _ = Matrix.trace (X * Kraus.evalWord C (List.ofFn w)) := by
      rw [Matrix.mul_assoc (X * V), hw, ← Matrix.mul_assoc (X * V),
        Matrix.mul_assoc X V W, hVW, Matrix.mul_one]

/-- Exact biorthogonal target blocks exist for every invariant retract of
a tensor with length-independent arbitrary-boundary transport. Source:
GLM23, Appendix A, restriction to fixed incoming block labels. -/
theorem exists_biorthogonalDecomposition_of_boundaryTransport_restrict
    (B : MPSTensor d D) (C : MPSTensor d E)
    (A : (c : Fin r) → MPSTensor d (dim c))
    (b : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ]
      ((c : Fin r) → Matrix (Fin (dim c)) (Fin (dim c)) ℂ))
    (hb : ∀ (n : ℕ), 0 < n → ∀ X : Matrix (Fin D) (Fin D) ℂ,
      ∀ w : Fin n → Fin d,
        mpvWithBoundary B X w = ∑ c : Fin r, mpvWithBoundary (A c) (b X c) w)
    (V₀ : Matrix (Fin E) (Fin D) ℂ) (W₀ : Matrix (Fin D) (Fin E) ℂ)
    (hVW : V₀ * W₀ = 1) (hW : ∀ i, B i * W₀ = W₀ * C i)
    {L : ℕ} (hL : 0 < L) (hSpan : WordTupleSpanTop A L) :
    ∃ (m : Fin r → ℕ)
      (V : ∀ c, Fin (m c) → Matrix (Fin (dim c)) (Fin E) ℂ)
      (W : ∀ c, Fin (m c) → Matrix (Fin E) (Fin (dim c)) ℂ),
      IsBiorthogonalDecomposition C (fun q : (c : Fin r) × Fin (m c) ↦ A q.1)
        (fun q ↦ V q.1 q.2) (fun q ↦ W q.1 q.2) := by
  let inclusion := (mulRightLinearMap (Fin D) ℂ V₀).comp
    (mulLeftLinearMap (Fin E) ℂ W₀)
  apply exists_biorthogonalDecomposition_of_boundaryTransport C A (b.comp inclusion)
    ?_ hL hSpan
  intro n hn X w
  change mpvWithBoundary C X w =
    ∑ c : Fin r, mpvWithBoundary (A c) (b (W₀ * X * V₀) c) w
  rw [← mpvWithBoundary_sandwich_of_intertwiner B C V₀ W₀ hVW hW X w]
  exact hb n hn (W₀ * X * V₀) w

end MPSTensor
