/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.CanonicalForm.Reduction

/-!
# Invariant-projector closure

This file isolates the normalization-free algebraic step in the sufficient
condition for canonical form from Cirac, Pérez-García, Schuch, and Verstraete,
arXiv:1606.00608, lines 253--254.

The source assumes that every orthogonal projection satisfying
\(P A^i = P A^i P\) also satisfies \(A^i P = P A^i P\).  The recursive
decomposition in `MPSTensor.exists_irreducible_blockDecomp` uses the opposite
orientation, \((1-P)A^iP=0\).  Applying the source hypothesis to \(1-P\)
shows that such a projection commutes with every tensor matrix.  This argument
does not require a left-canonical or unital normalization.

The subsequent passage from these reducing projections to primitive,
spectral-radius-one blocks is not proved here.  Its missing spectral statement
is recorded in
`docs/paper-gaps/cpsv16_projector_closure_canonical_form.tex`.
-/

open scoped Matrix

namespace MPSTensor

variable {d D : ℕ}

/-- The invariant-projector closure condition of arXiv:1606.00608, lines
253--254: every left-invariant orthogonal projection is also right-invariant. -/
def HasInvariantProjectorClosure (A : MPSTensor d D) : Prop :=
  ∀ P : Matrix (Fin D) (Fin D) ℂ,
    IsOrthogonalProjection P →
    (∀ i : Fin d, P * A i = P * A i * P) →
    ∀ i : Fin d, A i * P = P * A i * P

/-- Under invariant-projector closure, every invariant orthogonal projection
reduces all tensor matrices.

This is the projection step in the sufficient condition for canonical form in
arXiv:1606.00608, lines 253--254.  It is independent of any left-canonical or
unital normalization. -/
theorem commutes_of_hasInvariantProjectorClosure_of_lowerZero
    (A : MPSTensor d D) (P : Matrix (Fin D) (Fin D) ℂ)
    (hClosure : HasInvariantProjectorClosure A)
    (hP : IsOrthogonalProjection P)
    (hLower : ∀ i : Fin d, (1 - P) * A i * P = 0) :
    ∀ i : Fin d, P * A i = A i * P := by
  intro i
  have hLeftComplement : ∀ j : Fin d,
      (1 - P) * A j = (1 - P) * A j * (1 - P) := by
    intro j
    have h := hLower j
    calc
      (1 - P) * A j = (1 - P) * A j * P + (1 - P) * A j * (1 - P) := by
        noncomm_ring
      _ = (1 - P) * A j * (1 - P) := by rw [h, zero_add]
  have hRightComplement := hClosure (1 - P) hP.one_sub hLeftComplement i
  have hAP : A i * P = P * A i * P := by
    have h := hLower i
    apply eq_of_sub_eq_zero
    calc
      A i * P - P * A i * P = (1 - P) * A i * P := by noncomm_ring
      _ = 0 := h
  have hPcomp : P * (1 - P) = 0 := by
    rw [mul_sub, mul_one, hP.2, sub_self]
  have hUpper : P * A i * (1 - P) = 0 := by
    calc
      P * A i * (1 - P) = P * (A i * (1 - P)) := by noncomm_ring
      _ = P * ((1 - P) * A i * (1 - P)) := by rw [hRightComplement]
      _ = (P * (1 - P)) * A i * (1 - P) := by noncomm_ring
      _ = 0 := by rw [hPcomp, zero_mul, zero_mul]
  calc
    P * A i = P * A i * P + P * A i * (1 - P) := by noncomm_ring
    _ = P * A i * P := by rw [hUpper, add_zero]
    _ = A i * P := hAP.symm

/-- If a tensor with invariant-projector closure has a nontrivial invariant
orthogonal projection, then it has a nontrivial reducing projection. -/
theorem exists_reducing_projection_of_hasInvariantProj
    (A : MPSTensor d D) (hClosure : HasInvariantProjectorClosure A)
    (hInv : HasInvariantProj A) :
    ∃ P : Matrix (Fin D) (Fin D) ℂ,
      IsOrthogonalProjection P ∧ P ≠ 0 ∧ P ≠ 1 ∧
        (∀ i : Fin d, P * A i = A i * P) := by
  obtain ⟨P, hP, hP0, hP1, hLower⟩ := hInv
  exact ⟨P, hP, hP0, hP1,
    commutes_of_hasInvariantProjectorClosure_of_lowerZero A P hClosure hP hLower⟩

end MPSTensor
