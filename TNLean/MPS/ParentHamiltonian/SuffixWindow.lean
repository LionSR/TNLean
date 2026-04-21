/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.IntersectionProperty
import TNLean.MPS.Chain.BlockedChainFT
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Suffix-window restrictions for parent-Hamiltonian ground spaces

This file introduces restriction maps obtained by fixing a prefix and reading the
last `L` sites of a state on `K + L` sites. It records the resulting matrix
identities needed for the open-chain range-reduction argument in
[CPGSV21, §IV.C].

## Main results

- `MPSTensor.tailRestrictₗ` — fix a prefix and restrict to the suffix window
- `Fin.snoc_append` — compatibility of `Fin.snoc` with `Fin.append`
- `MPSTensor.tailRestrictₗ_groundSpaceMap` — suffix restriction preserves the
  ground-space form
- `MPSTensor.groundSpace_inTailGround` — a ground-space state restricts to
  ground-space states on every suffix slice
- `MPSTensor.exists_left_tail_compatibility` — extract matrices satisfying
  `Z j * evalWord A (List.ofFn u) = A j * Y u`

## References

* [CPGSV21] arXiv:2011.12127, lines 2049–2078
-/

open scoped Matrix

namespace Fin

variable {d K L : ℕ}

/-- Appending a prefix commutes with adding a final site by `Fin.snoc`. -/
theorem snoc_append (u : Fin K → Fin d) (σ : Fin L → Fin d) (j : Fin d) :
    (Fin.snoc (Fin.append u σ) j : Fin (K + L + 1) → Fin d) =
      Fin.append u (Fin.snoc σ j) := by
  simpa using (Fin.append_snoc u σ j).symm

end Fin

namespace MPSTensor

variable {d D : ℕ}

/-- Suffix restriction: fixing a prefix `u : Fin K → Fin d` and keeping the last
`L` sites of a state on `K + L` sites. -/
def tailRestrictₗ {d K L : ℕ} (u : Fin K → Fin d) :
    NSiteSpace d (K + L) →ₗ[ℂ] NSiteSpace d L where
  toFun ψ := fun σ => ψ (Fin.append u σ)
  map_add' ψ₁ ψ₂ := by
    ext σ
    simp
  map_smul' c ψ := by
    ext σ
    simp

@[simp] theorem tailRestrictₗ_apply {d K L : ℕ} (u : Fin K → Fin d)
    (ψ : NSiteSpace d (K + L)) (σ : Fin L → Fin d) :
    tailRestrictₗ u ψ σ = ψ (Fin.append u σ) :=
  rfl

/-- Restricting the last site after fixing a prefix is the same as first
restricting the last site and then fixing the prefix. -/
@[simp] theorem tailRestrictₗ_restrictLast {d K L : ℕ} (u : Fin K → Fin d)
    (ψ : NSiteSpace d (K + L + 1)) (j : Fin d) :
    restrictLast (tailRestrictₗ u ψ) j = tailRestrictₗ u (restrictLast ψ j) := by
  ext σ
  simp [Fin.snoc_append]

/-- Restricting a ground-space vector of length `L + 1` by fixing the last site
produces the expected boundary matrix `A j * X`. -/
@[simp] theorem restrictLast_groundSpaceMap (A : MPSTensor d D) {L : ℕ}
    (j : Fin d) (X : Matrix (Fin D) (Fin D) ℂ) :
    restrictLast (groundSpaceMap A (L + 1) X) j = groundSpaceMap A L (A j * X) := by
  ext σ
  simp only [restrictLast_apply, groundSpaceMap_apply]
  rw [evalWord_ofFn_snoc]
  simp [Matrix.mul_assoc]

/-- If the length-`L` word span is all of `M_D`, then `groundSpaceMap A L` is
injective. -/
theorem groundSpaceMap_injective_of_wordSpan_eq_top {A : MPSTensor d D} {L : ℕ}
    (hwordL : wordSpan A L = ⊤) :
    Function.Injective (groundSpaceMap A L) := by
  have hBlkInj : IsInjective (blockTensor A L) := by
    exact (isNBlkInjective_iff_blockTensor_isInjective A L).mp
      ((wordSpan_eq_top_iff_isNBlkInjective A L).mp hwordL)
  intro X Y hXY
  apply groundSpaceMap_injective hBlkInj (show 0 < 1 by omega)
  ext σ
  have hXY' := congrArg (fun ψ => ψ (decodeBlock d L (σ 0))) hXY
  simpa [groundSpaceMap_apply, blockTensor, wordOfBlock, decodeBlock] using hXY'

/-- Block injectivity at length `L` implies injectivity of `groundSpaceMap A L`. -/
theorem groundSpaceMap_injective_of_isNBlkInjective {A : MPSTensor d D} {L : ℕ}
    (hInj : IsNBlkInjective A L) :
    Function.Injective (groundSpaceMap A L) :=
  groundSpaceMap_injective_of_wordSpan_eq_top
    ((wordSpan_eq_top_iff_isNBlkInjective A L).mpr hInj)

/-- Restricting a ground-space vector to a suffix slice preserves the ground-space
form, with the prefix word moved to the right boundary matrix by trace cyclicity. -/
@[simp] theorem tailRestrictₗ_groundSpaceMap (A : MPSTensor d D) {K L : ℕ}
    (u : Fin K → Fin d) (X : Matrix (Fin D) (Fin D) ℂ) :
    tailRestrictₗ u (groundSpaceMap A (K + L) X) =
      groundSpaceMap A L (X * evalWord A (List.ofFn u)) := by
  ext σ
  calc
    tailRestrictₗ u (groundSpaceMap A (K + L) X) σ
        = Matrix.trace (evalWord A (List.ofFn (Fin.append u σ)) * X) := by
            simp [groundSpaceMap_apply]
    _ = Matrix.trace (evalWord A (List.ofFn σ) * (X * evalWord A (List.ofFn u))) := by
          rw [List.ofFn_fin_append, evalWord_append]
          symm
          simpa [Matrix.mul_assoc] using
            (Matrix.trace_mul_cycle'
              (evalWord A (List.ofFn σ))
              X
              (evalWord A (List.ofFn u)))
    _ = groundSpaceMap A L (X * evalWord A (List.ofFn u)) σ := by
          simp [groundSpaceMap_apply]

/-- A state on `K + L` sites lies in the tail ground condition if every fixed
prefix gives an `L`-site ground-space vector. -/
def InTailGround (A : MPSTensor d D) (K L : ℕ) (ψ : NSiteSpace d (K + L)) : Prop :=
  ∀ u : Fin K → Fin d, tailRestrictₗ u ψ ∈ groundSpace A L

/-- A ground-space vector restricts to a ground-space vector on every suffix
slice. -/
theorem groundSpace_inTailGround (A : MPSTensor d D) (K L : ℕ)
    {ψ : NSiteSpace d (K + L)} (hψ : ψ ∈ groundSpace A (K + L)) :
    InTailGround A K L ψ := by
  intro u
  rw [groundSpace, LinearMap.mem_range] at hψ ⊢
  obtain ⟨X, rfl⟩ := hψ
  refine ⟨X * evalWord A (List.ofFn u), ?_⟩
  exact (tailRestrictₗ_groundSpaceMap (A := A) u X).symm

/-- From the long left-window condition and the suffix-window condition, extract
boundary matrices satisfying the common overlap identity
`Z j * evalWord A (List.ofFn u) = A j * Y u`. -/
theorem exists_left_tail_compatibility {A : MPSTensor d D} {K L₀ : ℕ}
    (hInj : IsNBlkInjective A L₀) {ψ : NSiteSpace d (K + L₀ + 1)}
    (hLeft : InLeftGround A (K + L₀) ψ)
    (hTail : InTailGround A K (L₀ + 1) ψ) :
    ∃ Z : Fin d → Matrix (Fin D) (Fin D) ℂ,
      ∃ Y : (Fin K → Fin d) → Matrix (Fin D) (Fin D) ℂ,
        (∀ j : Fin d, restrictLast ψ j = groundSpaceMap A (K + L₀) (Z j)) ∧
        (∀ u : Fin K → Fin d, tailRestrictₗ u ψ = groundSpaceMap A (L₀ + 1) (Y u)) ∧
        (∀ (j : Fin d) (u : Fin K → Fin d),
          Z j * evalWord A (List.ofFn u) = A j * Y u) := by
  have hLeft' :
      ∀ j : Fin d, ∃ Z : Matrix (Fin D) (Fin D) ℂ,
        restrictLast ψ j = groundSpaceMap A (K + L₀) Z := by
    intro j
    have hj := hLeft j
    rw [groundSpace, LinearMap.mem_range] at hj
    rcases hj with ⟨Z, hZ⟩
    exact ⟨Z, hZ.symm⟩
  choose Z hZ using hLeft'
  have hTail' :
      ∀ u : Fin K → Fin d, ∃ Y : Matrix (Fin D) (Fin D) ℂ,
        tailRestrictₗ u ψ = groundSpaceMap A (L₀ + 1) Y := by
    intro u
    have hu := hTail u
    rw [groundSpace, LinearMap.mem_range] at hu
    rcases hu with ⟨Y, hY⟩
    exact ⟨Y, hY.symm⟩
  choose Y hY using hTail'
  have hCompat : ∀ (j : Fin d) (u : Fin K → Fin d),
      Z j * evalWord A (List.ofFn u) = A j * Y u := by
    intro j u
    apply groundSpaceMap_injective_of_isNBlkInjective hInj
    have hLeftSlice :
        tailRestrictₗ u (restrictLast ψ j) =
          groundSpaceMap A L₀ (Z j * evalWord A (List.ofFn u)) := by
      rw [hZ j]
      exact tailRestrictₗ_groundSpaceMap (A := A) u (Z j)
    have hTailSlice :
        tailRestrictₗ u (restrictLast ψ j) = groundSpaceMap A L₀ (A j * Y u) := by
      calc
        tailRestrictₗ u (restrictLast ψ j)
            = restrictLast (tailRestrictₗ u ψ) j := by
                exact (tailRestrictₗ_restrictLast (u := u) (ψ := ψ) (j := j)).symm
        _ = restrictLast (groundSpaceMap A (L₀ + 1) (Y u)) j := by
              rw [hY u]
        _ = groundSpaceMap A L₀ (A j * Y u) := by
              exact restrictLast_groundSpaceMap (A := A) (j := j) (X := Y u)
    exact hLeftSlice.symm.trans hTailSlice
  exact ⟨Z, Y, hZ, hY, hCompat⟩

end MPSTensor
