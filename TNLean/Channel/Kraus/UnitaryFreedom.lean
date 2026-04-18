/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.LinearAlgebra.UnitaryGroup
import TNLean.Channel.KrausFreedom

/-!
# Unitary freedom of Kraus representations

This file packages the directional Kraus-freedom lemmas already proved in
`TNLean.Channel.KrausRepresentation` and `TNLean.Channel.KrausFreedom` into
iff statements matching Wolf Theorem 2.18.

## Main results

* `kraus_isometry_freedom_iff` — two finite Kraus families define the same
  completely positive map if and only if, after padding the smaller family with
  zeros, they are related by an isometric mixing matrix.
* `kraus_unitary_freedom_iff` — same-size Kraus families define the same map if
  and only if they are related by a unitary mixing matrix.

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Thm 2.18][Wolf2012QChannels]
-/

open scoped Matrix ComplexOrder MatrixOrder
open Matrix Finset BigOperators

variable {D : ℕ}

private theorem kraus_same_map_of_isometry_combination_aux
    {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂] [DecidableEq ι₂]
    (B : ι₁ → Matrix (Fin D) (Fin D) ℂ)
    (A : ι₂ → Matrix (Fin D) (Fin D) ℂ)
    (V : Matrix ι₁ ι₂ ℂ)
    (hV : Vᴴ * V = 1)
    (hBA : ∀ α, B α = ∑ j, V α j • A j) :
    ∀ X : Matrix (Fin D) (Fin D) ℂ,
      ∑ α, B α * X * (B α)ᴴ = ∑ j, A j * X * (A j)ᴴ := by
  intro X
  have hV_entry : ∀ j k : ι₂,
      ∑ α : ι₁, (starRingEnd ℂ) (V α j) * V α k = if j = k then 1 else 0 := by
    intro j k
    have h := congrArg (fun M : Matrix ι₂ ι₂ ℂ => M j k) hV
    simpa [Matrix.mul_apply, Matrix.one_apply] using h
  calc
    ∑ α, B α * X * (B α)ᴴ
        = ∑ α,
            (∑ j, V α j • A j) * X * ((∑ j, V α j • A j)ᴴ) := by
          simp [hBA]
    _ = ∑ α, ∑ j, ∑ k,
          (((starRingEnd ℂ) (V α k)) * V α j) • (A j * X * (A k)ᴴ) := by
          simp_rw [Matrix.sum_mul, Matrix.conjTranspose_sum, Matrix.conjTranspose_smul,
            Matrix.mul_sum, smul_mul_assoc, mul_smul_comm, Matrix.mul_assoc, smul_smul]
          simp [mul_comm]
    _ = ∑ j, ∑ k,
          (∑ α, ((starRingEnd ℂ) (V α k)) * V α j) • (A j * X * (A k)ᴴ) := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro j _
          rw [Finset.sum_comm]
          simp_rw [← Finset.sum_smul]
    _ = ∑ j, ∑ k,
          (if k = j then 1 else 0) • (A j * X * (A k)ᴴ) := by
          simp_rw [hV_entry]
          simp
    _ = ∑ j, A j * X * (A j)ᴴ := by
          simp

/-- **Wolf Thm. 2.18 (isometric form)**: two finite Kraus families define the
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
  constructor
  · intro h
    exact kraus_rectangular_freedom' B A h hCard
  · rintro ⟨V, hV, hBA⟩
    exact kraus_same_map_of_isometry_combination_aux B A V hV hBA

/-- **Wolf Thm. 2.18 (unitary form)**: if two Kraus families have the same
finite index type, then they define the same completely positive map if and only
if they are related by a unitary mixing matrix. -/
theorem kraus_unitary_freedom_iff
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B A : ι → Matrix (Fin D) (Fin D) ℂ) :
    (∀ X : Matrix (Fin D) (Fin D) ℂ,
      ∑ α, B α * X * (B α)ᴴ = ∑ j, A j * X * (A j)ᴴ) ↔
      ∃ U : Matrix.unitaryGroup ι ℂ,
        ∀ α, B α = ∑ j, (U : Matrix ι ι ℂ) α j • A j := by
  constructor
  · intro h
    obtain ⟨V, hV, hBA⟩ := (kraus_isometry_freedom_iff B A le_rfl).mp h
    refine ⟨⟨V, Matrix.mem_unitaryGroup_iff'.2 ?_⟩, hBA⟩
    simpa using hV
  · rintro ⟨U, hBA⟩
    refine (kraus_isometry_freedom_iff B A le_rfl).mpr ?_
    refine ⟨(U : Matrix ι ι ℂ), ?_, hBA⟩
    have hU : ((U : Matrix ι ι ℂ)ᴴ * (U : Matrix ι ι ℂ)) = 1 := by
      exact Matrix.mem_unitaryGroup_iff'.mp U.prop
    simpa using hU
