/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Algebra.MatrixAlgebra.MatrixUnitFactorization
import TNLean.MPS.Operator.Boundary.BoundaryRepresentationClosedness
import Mathlib.LinearAlgebra.Matrix.Bilinear

/-!
# Exact biorthogonal decompositions from arbitrary-boundary transport

Length-independent arbitrary-boundary transport, together with simultaneous
word spanning of the target blocks at one positive length, gives an exact
local decomposition into mutually biorthogonal copies of those blocks.
The image of the identity of the target block algebra is only a support
idempotent on the ambient bond space. No adjoint, star closure, ambient
completeness, or nilpotent-remainder hypothesis is used.

## References

* Garre-Rubio--Lootens--Molnár, arXiv:2203.12563v3, `fusiontensors`,
  `eq:orthoW`, `fusiontensors2`, `eq:orthoV`, and Appendix A.

## Restricting arbitrary-boundary transport to an invariant bond block

An invariant bond-space inclusion with a left inverse transports a boundary
of the smaller tensor to a boundary of the ambient tensor. Composing with a
length-independent target boundary map then gives exact biorthogonal tensors
for the smaller source tensor. The inclusion need not be an isometry.

This is the block-restriction step in GLM23 Appendix A preceding `decompopen`.
-/

section

open scoped Matrix BigOperators

noncomputable section

namespace MPSTensor

variable {d D r : ℕ} {dim : Fin r → ℕ}

/-- A representation of the target block algebra splits into an exact local
biorthogonal decomposition. This gives a matrix-unit proof of the
reconstruction in GLM23 Appendix A, `decompopen` and `eq:ortho`. -/
theorem exists_biorthogonalDecomposition_of_nonUnitalAlgHom
    (B : MPSTensor d D) (A : (c : Fin r) → MPSTensor d (dim c))
    (ρ : ((c : Fin r) → Matrix (Fin (dim c)) (Fin (dim c)) ℂ) →ₙₐ[ℂ]
      Matrix (Fin D) (Fin D) ℂ)
    (hρ : ∀ i : Fin d, ρ (fun c ↦ A c i) = B i) :
    ∃ (m : Fin r → ℕ)
      (V : ∀ c, Fin (m c) → Matrix (Fin (dim c)) (Fin D) ℂ)
      (W : ∀ c, Fin (m c) → Matrix (Fin D) (Fin (dim c)) ℂ),
      IsBiorthogonalDecomposition B (fun q : (c : Fin r) × Fin (m c) ↦ A q.1)
        (fun q ↦ V q.1 q.2) (fun q ↦ W q.1 q.2) := by
  let f : ((c : Fin r) → Matrix (Fin (dim c)) (Fin (dim c)) ℂ) →ₗ[ℂ]
      Matrix (Fin D) (Fin D) ℂ :=
    { toFun := ρ
      map_add' := map_add ρ
      map_smul' := map_smul ρ }
  have hf : ∀ M N, f (M * N) = f M * f N := map_mul ρ
  obtain ⟨m, W, V, hsame, hcross, hsum, _⟩ :=
    Matrix.exists_piMatrix_blocks dim f hf
  change ∀ M, ρ M = ∑ c, ∑ μ, W c μ * M c * V c μ at hsum
  refine ⟨m, V, W, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨c, μ⟩
    simpa using hsame c μ μ
  · rintro ⟨c, μ⟩ ⟨e, ν⟩ hne
    by_cases hce : c = e
    · subst e
      have hμν : μ ≠ ν := by
        intro heq
        subst ν
        exact hne rfl
      simpa [hμν] using hsame c μ ν
    · exact hcross c e hce μ ν
  · intro i
    rw [← hρ i, hsum]
    exact (Fintype.sum_sigma' (fun c μ ↦ W c μ * A c i * V c μ)).symm

/-- Arbitrary-boundary transport gives exact biorthogonal local tensors once
the target blocks span simultaneously at one positive length. It is enough
to compare that length and twice that length, while length one recovers the
unblocked local letters. Source: GLM23, Appendix A. -/
theorem exists_biorthogonalDecomposition_of_boundaryTransport
    (B : MPSTensor d D) (A : (c : Fin r) → MPSTensor d (dim c))
    (b : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ]
      ((c : Fin r) → Matrix (Fin (dim c)) (Fin (dim c)) ℂ))
    (hb : ∀ (n : ℕ), 0 < n → ∀ X : Matrix (Fin D) (Fin D) ℂ,
      ∀ w : Fin n → Fin d,
        mpvWithBoundary B X w = ∑ c : Fin r, mpvWithBoundary (A c) (b X c) w)
    {L : ℕ} (hL : 0 < L) (hSpan : WordTupleSpanTop A L) :
    ∃ (m : Fin r → ℕ)
      (V : ∀ c, Fin (m c) → Matrix (Fin (dim c)) (Fin D) ℂ)
      (W : ∀ c, Fin (m c) → Matrix (Fin D) (Fin (dim c)) ℂ),
      IsBiorthogonalDecomposition B (fun q : (c : Fin r) × Fin (m c) ↦ A q.1)
        (fun q ↦ V q.1 q.2) (fun q ↦ W q.1 q.2) :=
  exists_biorthogonalDecomposition_of_nonUnitalAlgHom B A
    (boundaryRepresentation B A b hb hL hSpan)
    (boundaryRepresentation_letter B A b hb hL hSpan)

end MPSTensor

namespace MPOTensor

variable {d D r : ℕ} {dim : Fin r → ℕ}

/-- Arbitrary-boundary closedness gives an exact local fusion decomposition
of the stacked tensor into target block copies, with biorthogonal left
inverses. Source: GLM23, `fusiontensors`, `eq:orthoW`, and Appendix A.
The target blocks need only span simultaneously at one positive length. -/
theorem IsBoundaryClosed.exists_biorthogonalDecomposition
    {T : MPOTensor d (∑ c : Fin r, dim c)} (hT : IsBoundaryClosed T)
    (A : (c : Fin r) → MPSTensor (d * d) (dim c))
    (hBlocks : T.toMPSTensor = MPSTensor.toTensorFromBlocks (fun _ ↦ 1) A)
    {L : ℕ} (hL : 0 < L) (hSpan : MPSTensor.WordTupleSpanTop A L) :
    ∃ (m : Fin r → ℕ)
      (V : ∀ c, Fin (m c) → Matrix (Fin (dim c))
        (Fin ((∑ c : Fin r, dim c) * (∑ c : Fin r, dim c))) ℂ)
      (W : ∀ c, Fin (m c) → Matrix
        (Fin ((∑ c : Fin r, dim c) * (∑ c : Fin r, dim c))) (Fin (dim c)) ℂ),
      MPSTensor.IsBiorthogonalDecomposition (mulTensor T T).toMPSTensor
        (fun q : (c : Fin r) × Fin (m c) ↦ A q.1)
        (fun q ↦ V q.1 q.2) (fun q ↦ W q.1 q.2) := by
  obtain ⟨ρ, hρ⟩ := hT.exists_boundaryRepresentation A hBlocks hL hSpan
  exact MPSTensor.exists_biorthogonalDecomposition_of_nonUnitalAlgHom
    (mulTensor T T).toMPSTensor A ρ hρ

/-- Arbitrary-boundary compatibility gives exact action tensors and their
biorthogonal left inverses. Source: GLM23, `fusiontensors2`, `eq:orthoV`,
and Appendix A, final paragraph. The target blocks need only span
simultaneously at one positive length. -/
theorem IsBoundaryCompatible.exists_biorthogonalDecomposition
    {T : MPOTensor d D} {A : MPSTensor d (∑ c : Fin r, dim c)}
    (h : IsBoundaryCompatible T A)
    (B : (c : Fin r) → MPSTensor d (dim c))
    (hBlocks : A = MPSTensor.toTensorFromBlocks (fun _ ↦ 1) B)
    {L : ℕ} (hL : 0 < L) (hSpan : MPSTensor.WordTupleSpanTop B L) :
    ∃ (m : Fin r → ℕ)
      (V : ∀ c, Fin (m c) → Matrix (Fin (dim c)) (Fin (D * ∑ c, dim c)) ℂ)
      (W : ∀ c, Fin (m c) → Matrix (Fin (D * ∑ c, dim c)) (Fin (dim c)) ℂ),
      MPSTensor.IsBiorthogonalDecomposition (actTensor T A)
        (fun q : (c : Fin r) × Fin (m c) ↦ B q.1)
        (fun q ↦ V q.1 q.2) (fun q ↦ W q.1 q.2) := by
  obtain ⟨ρ, hρ⟩ := h.exists_boundaryRepresentation B hBlocks hL hSpan
  exact MPSTensor.exists_biorthogonalDecomposition_of_nonUnitalAlgHom
    (actTensor T A) B ρ hρ

end MPOTensor
end

end

section

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

end
