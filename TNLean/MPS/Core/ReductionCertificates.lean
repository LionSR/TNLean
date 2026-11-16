/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.ComplexOfRing
import TNLean.MPS.Core.Reduction

/-!
# Local reduction identities over a coefficient ring

Finite fusion and action matrices can be calculated over a commutative coefficient ring.
Mapping the cap, single-letter and projection-insertion identities into the complex numbers
gives a reduction on every word, by the existing local compression theorem.
-/

namespace MPSTensor

open scoped Kronecker

variable {R : Type*} [CommRing R] {d D E : ℕ}

/-- Entrywise ring maps preserve the Kronecker products in fusion and action reductions. -/
theorem complexOfRing_kronecker (f : R →+* ℂ) {m n p q : Type*}
    (X : Matrix m n R) (Y : Matrix p q R) :
    complexOfRing f (X ⊗ₖ Y) = complexOfRing f X ⊗ₖ complexOfRing f Y := by
  ext i j
  exact map_mul f _ _

/-- Local reduction identities remain valid after applying a ring homomorphism to every
entry. The conclusion includes all words, including the empty word. -/
theorem isReduction_complexOfRing_of_local_compression (f : R →+* ℂ)
    (B : Fin d → Matrix (Fin E) (Fin E) R)
    (A : Fin d → Matrix (Fin D) (Fin D) R)
    (V : Matrix (Fin D) (Fin E) R) (W : Matrix (Fin E) (Fin D) R)
    (hVW : V * W = 1) (hletter : ∀ i, V * B i * W = A i)
    (hinsert : ∀ i j, B i * W * V * B j = B i * B j) :
    IsReduction (fun i ↦ complexOfRing f (B i)) (fun i ↦ complexOfRing f (A i))
      (complexOfRing f V) (complexOfRing f W) := by
  apply IsReduction.of_local_compression
  · rw [← complexOfRing_mul, hVW, complexOfRing_one]
  · intro i
    simp only [← complexOfRing_mul, hletter]
  · intro i j
    simp only [← complexOfRing_mul, hinsert]

end MPSTensor
