/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.LinearAlgebra.UnitaryGroup
import TNLean.Channel.KrausFreedom

/-!
# Unitary freedom of Kraus representations

This file restates the directional Kraus-freedom lemmas already proved in
`TNLean.Channel.KrausRepresentation` and `TNLean.Channel.KrausFreedom` as
iff statements matching Wolf Theorem 2.18.

## Main results

* `kraus_isometry_freedom_iff` — two finite Kraus families define the same
  completely positive map if and only if, after padding the smaller family with
  zeros, they are related by an isometric mixing matrix.
* `kraus_unitary_freedom_iff` — same-size Kraus families define the same map if
  and only if they are related by a unitary mixing matrix.

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Theorem 2.18][Wolf2012QChannels]
-/

open scoped Matrix
open Matrix Finset BigOperators

variable {D : ℕ}

/-- **Wolf Theorem 2.18 (isometric form)**: two finite Kraus families define the
same completely positive map if and only if, after padding the smaller family
with zeros, they are related by an isometric mixing matrix. -/
theorem kraus_isometry_freedom_iff
    {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂] [DecidableEq ι₂]
    (B : ι₁ → Matrix (Fin D) (Fin D) ℂ)
    (A : ι₂ → Matrix (Fin D) (Fin D) ℂ)
    (hCard : Fintype.card ι₂ ≤ Fintype.card ι₁) :
    (∀ X : Matrix (Fin D) (Fin D) ℂ,
      ∑ α, B α * X * (B α)ᴴ = ∑ j, A j * X * (A j)ᴴ) ↔
      ∃ V : Matrix ι₁ ι₂ ℂ,
        Vᴴ * V = 1 ∧
        ∀ α, B α = ∑ j, V α j • A j := by
  refine ⟨fun h => kraus_rectangular_freedom' B A h hCard, ?_⟩
  rintro ⟨V, hV, hBA⟩
  exact kraus_same_map_of_isometry_combination (K := B) (K' := A) (W := V) hV hBA

/-- **Wolf Theorem 2.18 (unitary form)**: if two Kraus families have the same
finite index type, then they define the same completely positive map if and only
if they are related by a unitary mixing matrix. -/
theorem kraus_unitary_freedom_iff
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B A : ι → Matrix (Fin D) (Fin D) ℂ) :
    (∀ X : Matrix (Fin D) (Fin D) ℂ,
      ∑ α, B α * X * (B α)ᴴ = ∑ j, A j * X * (A j)ᴴ) ↔
      ∃ U : Matrix.unitaryGroup ι ℂ,
        ∀ α, B α = ∑ j, (U : Matrix ι ι ℂ) α j • A j := by
  -- Both directions share the translation between `Uᴴ * U = 1` and the bundled
  -- `Matrix.unitaryGroup` predicate via `Matrix.mem_unitaryGroup_iff'`.
  rw [kraus_isometry_freedom_iff B A le_rfl]
  refine ⟨fun ⟨V, hV, hBA⟩ => ⟨⟨V, Matrix.mem_unitaryGroup_iff'.2 hV⟩, hBA⟩,
          fun ⟨U, hBA⟩ => ⟨(U : Matrix ι ι ℂ), Matrix.mem_unitaryGroup_iff'.mp U.prop, hBA⟩⟩
