/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.HoleEncoder

/-!
# Degenerate cases and raw-coordinate semantics of hole encoders

The zero innovation family has no tag, while the empty-outer convention has one.
The coefficient tests exercise a reset site and a preserved complementary site.
-/

open scoped BigOperators Matrix Matrix.Norms.L2Operator
open TNLean.PEPS

namespace TNLeanTest.HoleEncoder

noncomputable section

example (v : Fin 2 → ℂ) (b : Fin 2) :
    coordinateResetMatrix (0 : Fin 2) v 0 b = star (v b) := by
  simp [coordinateResetMatrix]

example (v : Fin 2 → ℂ) (b : Fin 2) :
    coordinateResetMatrix (0 : Fin 2) v 1 b = 0 := by
  simp [coordinateResetMatrix]

example : Fintype.card PUnit = 1 := by simp

example (x : Fin 2 → ℂ) : (identityHoleEncoder *ᵥ x) (PUnit.unit, 1) = x 1 := by
  simp

example (x : Fin 0 → ℂ) :
    ‖WithLp.toLp 2 (identityHoleEncoder *ᵥ x)‖ = ‖WithLp.toLp 2 x‖ :=
  identityHoleEncoder_norm x

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Out : V → Type*} [∀ v, Fintype (Out v)]

example (R : Fin 0 → Finset V) (hR : Monotone R)
    (S : (j : Fin 0) → Submodule ℂ (((w : {w : V // w ∈ R j}) → Out w.1) → ℂ)) :
    Fintype.card (HoleEncoderTag R hR S) = 0 := by
  rw [card_holeEncoderTag]
  simp

example (R : Fin 0 → Finset V) (hR : Monotone R)
    (S : (j : Fin 0) → Submodule ℂ (((w : {w : V // w ∈ R j}) → Out w.1) → ℂ))
    (zero : (v : V) → Out v) : holeEncoder R hR S zero = 0 :=
  holeEncoder_empty R hR S zero

example {n : ℕ} (R : Fin n → Finset V) (hR : Monotone R)
    (zero : (v : V) → Out v) : holeEncoder R hR (fun _ => ⊥) zero = 0 :=
  holeEncoder_zero_spaces R hR zero

/-- No tag can be produced from a zero-dimensional inside family. -/
example {n : ℕ} (R : Fin n → Finset V) (hR : Monotone R) :
    Fintype.card (HoleEncoderTag (Out := Out) R hR (fun _ => ⊥)) = 0 := by
  apply Nat.eq_zero_of_le_zero
  simpa using card_holeEncoderTag_le (Out := Out) R hR (fun _ => ⊥)

/-- A scalar region may reset no sites and still contribute a tag. -/
example : Module.finrank ℂ
    (⊤ : Submodule ℂ (((w : {w : Fin 1 // w ∈ (∅ : Finset (Fin 1))}) → Fin 2) → ℂ)) = 1 := by
  simp

/-- A changing radius retains the same full raw output alphabet. -/
example {n : ℕ} (R : Fin n → Finset V) (hR : Monotone R)
    (S : (j : Fin n) → Submodule ℂ (((w : {w : V // w ∈ R j}) → Out w.1) → ℂ))
    (zero : (v : V) → Out v) :
    Matrix (HoleEncoderTag R hR S × ((w : {w : V // w ∈ Finset.univ}) → Out w.1))
      ((w : {w : V // w ∈ Finset.univ}) → Out w.1) ℂ :=
  holeEncoder R hR S zero

/-- Every site in the selected radius is reset, including sites outside smaller radii. -/
example {n : ℕ} (R : Fin n → Finset V) (hR : Monotone R)
    (S : (j : Fin n) → Submodule ℂ (((w : {w : V // w ∈ R j}) → Out w.1) → ℂ))
    (zero : (v : V) → Out v) (t : HoleEncoderTag R hR S)
    (α β : (w : {w : V // w ∈ Finset.univ}) → Out w.1)
    (v : V) (hv : v ∈ R t.1) (hα : α ⟨v, Finset.mem_univ v⟩ ≠ zero v) :
    holeEncoder R hR S zero (t, α) β = 0 :=
  holeEncoder_eq_zero_of_not_reset R hR S zero t α β v hv hα

/-- A complementary input coordinate cannot be silently renamed or discarded. -/
example {n : ℕ} (R : Fin n → Finset V) (hR : Monotone R)
    (S : (j : Fin n) → Submodule ℂ (((w : {w : V // w ∈ R j}) → Out w.1) → ℂ))
    (zero : (v : V) → Out v) (t : HoleEncoderTag R hR S)
    (α β : (w : {w : V // w ∈ Finset.univ}) → Out w.1)
    (v : V) (hv : v ∉ R t.1)
    (hαβ : α ⟨v, Finset.mem_univ v⟩ ≠ β ⟨v, Finset.mem_univ v⟩) :
    holeEncoder R hR S zero (t, α) β = 0 :=
  holeEncoder_eq_zero_of_complement_ne R hR S zero t α β v hv hαβ

end

end TNLeanTest.HoleEncoder
