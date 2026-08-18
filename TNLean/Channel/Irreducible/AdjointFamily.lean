/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Channel.Irreducible.Basic
import TNLean.Channel.FixedPoint.SupportInvariance

/-!
# Irreducibility of the conjugate-transposed Kraus family

Irreducibility of a finite Kraus map passes to the conjugate-transposed family:
if `X ↦ ∑ᵢ Kᵢ X Kᵢ†` is irreducible, so is `X ↦ ∑ᵢ Kᵢ† X Kᵢ`.

An invariant projection `P` for the conjugate-transposed family gives
`(1-P) Kᵢ† P = 0`; taking adjoints yields `P Kᵢ (1-P) = 0`, so `1 - P` is an
invariant projection for the original family, which forces `P ∈ {0, 1}`.

## Main declarations

* `Kraus.isIrreducibleMap_mapLM_conjTranspose`: irreducibility passes to the
  conjugate-transposed Kraus family.
* `Kraus.isIrreducibleMap_mapLM_conjTranspose_iff`: the two irreducibilities are
  equivalent.

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Section 6.2][Wolf2012QChannels]
-/

open scoped Matrix ComplexOrder BigOperators
open Matrix

namespace Kraus

variable {d D : ℕ}

local notation "Mat" => Matrix (Fin D) (Fin D) ℂ

/-- Irreducibility of a Kraus map passes to the conjugate-transposed family. -/
theorem isIrreducibleMap_mapLM_conjTranspose
    (K : Fin d → Mat) (hIrr : IsIrreducibleMap (mapLM K)) :
    IsIrreducibleMap (mapLM fun i => (K i)ᴴ) := by
  intro P hProj hInv
  -- Lower-zero condition for the conjugate-transposed family.
  have hLowerAdj : ∀ i : Fin d, (1 - P) * (K i)ᴴ * P = 0 :=
    invariance_implies_lowerZero (fun i => (K i)ᴴ) P hProj
      (by simpa only [mapLM_apply] using hInv)
  have hPH : Pᴴ = P := hProj.1.eq
  have h1PH : (1 - P)ᴴ = 1 - P := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hPH]
  -- Taking adjoints gives the complementary condition for the original family.
  have hUpper : ∀ i : Fin d, P * K i * (1 - P) = 0 := by
    intro i
    have h := congrArg Matrix.conjTranspose (hLowerAdj i)
    simpa [Matrix.conjTranspose_mul, hPH, h1PH, Matrix.mul_assoc] using h
  -- `1 - P` is an invariant projection for the original family.
  have hQProj : IsOrthogonalProjection (1 - P) := hProj.one_sub
  have hLowerQ : ∀ i : Fin d, (1 - (1 - P)) * K i * (1 - P) = 0 := by
    intro i
    simpa using hUpper i
  have hInvQ : ∀ X, (1 - P) * mapLM K ((1 - P) * X * (1 - P)) * (1 - P) =
      mapLM K ((1 - P) * X * (1 - P)) := by
    intro X
    simpa only [mapLM_apply] using lowerZero_implies_invariance K (1 - P) hQProj hLowerQ X
  rcases hIrr (1 - P) hQProj hInvQ with hQ | hQ
  · exact Or.inr (sub_eq_zero.mp hQ).symm
  · exact Or.inl (sub_eq_self.mp hQ)

/-- Irreducibility of a Kraus map and of its conjugate-transposed family are
equivalent. -/
theorem isIrreducibleMap_mapLM_conjTranspose_iff (K : Fin d → Mat) :
    IsIrreducibleMap (mapLM fun i => (K i)ᴴ) ↔ IsIrreducibleMap (mapLM K) := by
  constructor
  · intro h
    simpa only [Matrix.conjTranspose_conjTranspose] using
      isIrreducibleMap_mapLM_conjTranspose (fun i => (K i)ᴴ) h
  · exact isIrreducibleMap_mapLM_conjTranspose K

end Kraus
