/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Tensor.GroundSpace.IntersectionProperty
import Mathlib.Data.Fin.Tuple.Basic
import TNLean.MPS.Tensor.Words.Basic

/-!
# Suffix-window restrictions for parent-Hamiltonian ground spaces

This file introduces restriction maps obtained by fixing a prefix and reading the
last \(L\) sites of a state on \(K + L\) sites. It states the resulting matrix
identities needed for the open-chain range-reduction argument in
[Cirac--Perez-Garcia--Schuch--Verstraete 2021, arXiv:2011.12127,
Section IV.C, lines 2049--2094].

## Main results

- `MPSTensor.tailRestrictₗ` — fix a prefix and restrict to the suffix window
- `MPSTensor.tailRestrictₗ_groundSpaceMap` — suffix restriction preserves the
  ground-space form
- `MPSTensor.groundSpace_inTailGround` — a ground-space state restricts to
  ground-space states on every suffix slice
- `MPSTensor.exists_left_tail_compatibility` — extract matrices satisfying
  \(Z_j A^u = A_j Y_u\)
* `MPSTensor.exists_right_factor_of_evalWord_compatibility`,
  `MPSTensor.groundSpace_extend_right_of_isNBlkInjective`: growing back for block-injective
  parent-Hamiltonian ground spaces.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2021] arXiv:2011.12127,
  Section IV.C, lines 2049--2078
-/

open scoped Matrix

section SuffixWindow

namespace MPSTensor

variable {d D : ℕ}

/-- Suffix restriction: fixing a prefix \(u\) and keeping the last
\(L\) sites of a state on \(K + L\) sites. -/
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
  simp only [restrictLast_apply, tailRestrictₗ_apply]
  rw [Fin.append_snoc]

/-- Restricting a ground-space vector of length \(L + 1\) by fixing the last site
produces the expected boundary matrix \(A_j X\). -/
@[simp] theorem restrictLast_groundSpaceMap (A : MPSTensor d D) {L : ℕ}
    (j : Fin d) (X : Matrix (Fin D) (Fin D) ℂ) :
    restrictLast (groundSpaceMap A (L + 1) X) j = groundSpaceMap A L (A j * X) := by
  ext σ
  simp only [restrictLast_apply, groundSpaceMap_apply]
  rw [evalWord_ofFn_snoc]
  simp [Matrix.mul_assoc]

/-- Restricting a ground-space vector of length \(L + 1\) by fixing the first site
produces the expected boundary matrix \(X A_i\). -/
@[simp] theorem restrictFirst_groundSpaceMap (A : MPSTensor d D) {L : ℕ}
    (i : Fin d) (X : Matrix (Fin D) (Fin D) ℂ) :
    restrictFirst (groundSpaceMap A (L + 1) X) i = groundSpaceMap A L (X * A i) := by
  ext σ
  simp only [restrictFirst_apply, groundSpaceMap_apply, evalWord_ofFn_cons]
  calc
    Matrix.trace ((A i * Kraus.evalWord A (List.ofFn σ)) * X)
        = Matrix.trace (X * (A i * Kraus.evalWord A (List.ofFn σ))) := by
            rw [Matrix.trace_mul_comm]
    _ = Matrix.trace ((X * A i) * Kraus.evalWord A (List.ofFn σ)) := by
          rw [Matrix.mul_assoc]
    _ = Matrix.trace (Kraus.evalWord A (List.ofFn σ) * (X * A i)) := by
          rw [Matrix.trace_mul_comm]

/-- Restricting a ground-space vector to a suffix slice preserves the ground-space
form, with the prefix word moved to the right boundary matrix by trace cyclicity. -/
@[simp] theorem tailRestrictₗ_groundSpaceMap (A : MPSTensor d D) {K L : ℕ}
    (u : Fin K → Fin d) (X : Matrix (Fin D) (Fin D) ℂ) :
    tailRestrictₗ u (groundSpaceMap A (K + L) X) =
      groundSpaceMap A L (X * Kraus.evalWord A (List.ofFn u)) := by
  ext σ
  calc
    tailRestrictₗ u (groundSpaceMap A (K + L) X) σ
        = Matrix.trace (Kraus.evalWord A (List.ofFn (Fin.append u σ)) * X) := by
            simp [groundSpaceMap_apply]
    _ = Matrix.trace (Kraus.evalWord A (List.ofFn σ) * (X * Kraus.evalWord A (List.ofFn u))) := by
          rw [List.ofFn_fin_append, Kraus.evalWord_append]
          symm
          simpa [Matrix.mul_assoc] using
            (Matrix.trace_mul_cycle'
              (Kraus.evalWord A (List.ofFn σ))
              X
              (Kraus.evalWord A (List.ofFn u)))
    _ = groundSpaceMap A L (X * Kraus.evalWord A (List.ofFn u)) σ := by
          simp [groundSpaceMap_apply]

/-- A state on \(K + L\) sites lies in the tail ground condition if every fixed
prefix gives an \(L\)-site ground-space vector. -/
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
  refine ⟨X * Kraus.evalWord A (List.ofFn u), ?_⟩
  exact (tailRestrictₗ_groundSpaceMap (A := A) u X).symm

/-- From the long left-window condition and the suffix-window condition, extract
boundary matrices satisfying the common overlap identity
\(Z_j A^u = A_j Y_u\). -/
theorem exists_left_tail_compatibility {A : MPSTensor d D} {K L₀ : ℕ}
    (hInj : Kraus.IsNBlkInjective A L₀) {ψ : NSiteSpace d (K + L₀ + 1)}
    (hLeft : InLeftGround A (K + L₀) ψ)
    (hTail : InTailGround A K (L₀ + 1) ψ) :
    ∃ Z : Fin d → Matrix (Fin D) (Fin D) ℂ,
      ∃ Y : (Fin K → Fin d) → Matrix (Fin D) (Fin D) ℂ,
        (∀ j : Fin d, restrictLast ψ j = groundSpaceMap A (K + L₀) (Z j)) ∧
        (∀ u : Fin K → Fin d, tailRestrictₗ u ψ = groundSpaceMap A (L₀ + 1) (Y u)) ∧
        (∀ (j : Fin d) (u : Fin K → Fin d),
          Z j * Kraus.evalWord A (List.ofFn u) = A j * Y u) := by
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
      Z j * Kraus.evalWord A (List.ofFn u) = A j * Y u := by
    intro j u
    apply groundSpaceMap_injective_of_isNBlkInjective hInj
    have hLeftSlice :
        tailRestrictₗ u (restrictLast ψ j) =
          groundSpaceMap A L₀ (Z j * Kraus.evalWord A (List.ofFn u)) := by
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

end SuffixWindow

section ExtendRight

/-!
## Growing back for block-injective parent-Hamiltonian ground spaces

This file proves the open-chain grow-back step from
[Cirac--Perez-Garcia--Schuch--Verstraete 2021, arXiv:2011.12127,
Section IV.C, lines 2049--2094].
Starting from the compatibility family extracted by
`MPSTensor.exists_left_tail_compatibility`, we show that block injectivity forces
all boundary matrices `Z j` to share a common right factor. This yields the
open-chain extension theorem `groundSpace_extend_right_of_isNBlkInjective`.

### Main results

- `MPSTensor.exists_right_factor_of_evalWord_compatibility` — common right-factor
  extraction from universal word compatibility
- `MPSTensor.groundSpace_extend_right_of_isNBlkInjective` — if the long left
  window and the suffix window both lie in the ground space, then the whole
  state lies in the ground space

### References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2021] arXiv:2011.12127,
  Section IV.C, lines 2049--2078
-/

open Kraus (blockPhysDim wordOfBlock length_wordOfBlock blockTensor
  isNBlkInjective_iff_blockTensor_isInjective)

namespace MPSTensor

variable {d D : ℕ}

/-- If the compatibility identity is available for every single physical letter,
then block injectivity yields a common right factor. -/
private theorem exists_right_factor_of_letter_compatibility [NeZero D]
    {A : MPSTensor d D} {L₀ : ℕ}
    (hInj : Kraus.IsNBlkInjective A L₀) (hL₀ : 0 < L₀)
    {Z : Fin d → Matrix (Fin D) (Fin D) ℂ}
    (hCompat : ∀ i : Fin d, ∃ Y : Matrix (Fin D) (Fin D) ℂ,
      ∀ j : Fin d, Z j * A i = A j * Y) :
    ∃ X : Matrix (Fin D) (Fin D) ℂ, ∀ j : Fin d, Z j = A j * X := by
  have hBlkInj : Kraus.IsInjective (blockTensor A L₀) :=
    (isNBlkInjective_iff_blockTensor_isInjective A L₀).mp hInj
  obtain ⟨c, hc⟩ := hBlkInj.exists_decomposition (1 : Matrix (Fin D) (Fin D) ℂ)
  have hBlockCompat : ∀ i : Fin (blockPhysDim d L₀),
      ∃ Y : Matrix (Fin D) (Fin D) ℂ,
        ∀ j : Fin d, Z j * blockTensor A L₀ i = A j * Y := by
    intro i
    have hword : wordOfBlock d L₀ i ≠ [] := by
      intro hnil
      have hlen : 0 = L₀ := by
        simpa [hnil] using (length_wordOfBlock d L₀ i)
      omega
    obtain ⟨Y, hY⟩ :=
      exists_evalWord_factor_of_letter_compatibility (A := A) hCompat (wordOfBlock d L₀ i) hword
    refine ⟨Y, ?_⟩
    intro j
    exact hY j
  choose Y hY using hBlockCompat
  let X : Matrix (Fin D) (Fin D) ℂ := ∑ i, c i • Y i
  refine ⟨X, ?_⟩
  intro j
  calc
    Z j = Z j * (1 : Matrix (Fin D) (Fin D) ℂ) := by simp
    _ = Z j * ∑ i, c i • blockTensor A L₀ i := by rw [hc]
    _ = ∑ i, c i • (Z j * blockTensor A L₀ i) := by
          simp [Finset.mul_sum]
    _ = ∑ i, c i • (A j * Y i) := by
          refine Finset.sum_congr rfl ?_
          intro i _
          rw [hY i j]
    _ = A j * ∑ i, c i • Y i := by
          simp [Finset.mul_sum]
    _ = A j * X := by rfl

/-- The positive-length case of the grow-back theorem.  Compatibility for words
of length \(K + 1\) reduces to the single-letter case by stripping the first
letter and applying the induction hypothesis to the matrices \(Z_j A_i\). -/
private theorem exists_right_factor_of_evalWord_compatibility_succ [NeZero D]
    {A : MPSTensor d D} {L₀ : ℕ}
    (hInj : Kraus.IsNBlkInjective A L₀) (hL₀ : 0 < L₀) :
    ∀ K : ℕ, ∀ {Z : Fin d → Matrix (Fin D) (Fin D) ℂ},
      (∀ σ : Fin (K + 1) → Fin d, ∃ Yσ : Matrix (Fin D) (Fin D) ℂ,
        ∀ j : Fin d, Z j * Kraus.evalWord A (List.ofFn σ) = A j * Yσ) →
      ∃ X : Matrix (Fin D) (Fin D) ℂ, ∀ j : Fin d, Z j = A j * X
  | 0, Z, hCompat =>
      have hCompat1 : ∀ i : Fin d, ∃ Y : Matrix (Fin D) (Fin D) ℂ,
          ∀ j : Fin d, Z j * A i = A j * Y := by
        intro i
        let σ : Fin 1 → Fin d := fun _ => i
        obtain ⟨Y, hY⟩ := hCompat σ
        refine ⟨Y, ?_⟩
        intro j
        simpa [σ, Kraus.evalWord] using hY j
      exists_right_factor_of_letter_compatibility hInj hL₀ hCompat1
  | K + 1, Z, hCompat =>
      have hCompat1 : ∀ i : Fin d, ∃ X : Matrix (Fin D) (Fin D) ℂ,
          ∀ j : Fin d, Z j * A i = A j * X := by
        intro i
        let Zi : Fin d → Matrix (Fin D) (Fin D) ℂ := fun j => Z j * A i
        have hCompatZi : ∀ σ : Fin (K + 1) → Fin d,
            ∃ Yσ : Matrix (Fin D) (Fin D) ℂ,
              ∀ j : Fin d, Zi j * Kraus.evalWord A (List.ofFn σ) = A j * Yσ := by
          intro σ
          obtain ⟨Yσ, hYσ⟩ := hCompat (Fin.cons i σ)
          refine ⟨Yσ, ?_⟩
          intro j
          simpa [Zi, evalWord_ofFn_cons, Matrix.mul_assoc] using hYσ j
        obtain ⟨X, hX⟩ :=
          exists_right_factor_of_evalWord_compatibility_succ hInj hL₀ K hCompatZi
        exact ⟨X, hX⟩
      exists_right_factor_of_letter_compatibility hInj hL₀ hCompat1

/-- Inverting step: if a family of boundary matrices satisfies the compatibility
identity \(Z_j A^σ = A_j Y_σ\) for every length-\(K\) word \(σ\), then all \(Z_j\)
share a common right factor. -/
theorem exists_right_factor_of_evalWord_compatibility [NeZero D]
    {A : MPSTensor d D} {K L₀ : ℕ}
    (hInj : Kraus.IsNBlkInjective A L₀) (hL₀ : 0 < L₀)
    {Z : Fin d → Matrix (Fin D) (Fin D) ℂ}
    (hCompat : ∀ σ : Fin K → Fin d, ∃ Yσ : Matrix (Fin D) (Fin D) ℂ,
      ∀ j : Fin d, Z j * Kraus.evalWord A (List.ofFn σ) = A j * Yσ) :
    ∃ X : Matrix (Fin D) (Fin D) ℂ, ∀ j : Fin d, Z j = A j * X := by
  cases K with
  | zero =>
      let σ : Fin 0 → Fin d := Fin.elim0
      obtain ⟨Y, hY⟩ := hCompat σ
      refine ⟨Y, ?_⟩
      intro j
      simpa [σ, Kraus.evalWord] using hY j
  | succ K =>
      exact exists_right_factor_of_evalWord_compatibility_succ hInj hL₀ K hCompat

/-- If two adjacent open-chain windows satisfy the ground-space condition at the
injectivity length \(L₀ + 1\), then the full \((K + L₀ + 1)\)-site state is itself
in the open-chain ground space. -/
theorem groundSpace_extend_right_of_isNBlkInjective
    [NeZero D] {A : MPSTensor d D} {K L₀ : ℕ} (hInj : Kraus.IsNBlkInjective A L₀)
    (hL₀ : 0 < L₀) {ψ : NSiteSpace d (K + L₀ + 1)}
    (hLeft : InLeftGround A (K + L₀) ψ)
    (hTail : InTailGround A K (L₀ + 1) ψ) :
    ψ ∈ groundSpace A (K + L₀ + 1) := by
  obtain ⟨Z, Y, hZ, _hY, hCompat⟩ :=
    exists_left_tail_compatibility (A := A) hInj hLeft hTail
  obtain ⟨X, hX⟩ :=
    exists_right_factor_of_evalWord_compatibility (A := A) hInj hL₀
      (Z := Z) (fun σ => ⟨Y σ, fun j => hCompat j σ⟩)
  have hSlices : ∀ j : Fin d,
      restrictLast ψ j = restrictLast (groundSpaceMap A (K + L₀ + 1) X) j := by
    intro j
    rw [hZ j, hX j]
    exact (restrictLast_groundSpaceMap (A := A) (L := K + L₀) (j := j) (X := X)).symm
  have hψ : ψ = groundSpaceMap A (K + L₀ + 1) X := by
    ext τ
    have hτ := congrArg (fun ξ => ξ (Fin.init τ)) (hSlices (τ (Fin.last _)))
    simpa [restrictLast_apply, Fin.snoc_init_self] using hτ
  rw [groundSpace, LinearMap.mem_range]
  exact ⟨X, hψ.symm⟩

end MPSTensor

end ExtendRight
