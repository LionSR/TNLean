/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.SuffixWindow

/-!
# Right-extension for block-injective parent-Hamiltonian ground spaces

This file proves the open-chain grow-back step from [CPGSV21, §IV.C].
Starting from the compatibility family extracted by
`MPSTensor.exists_left_tail_compatibility`, we show that block injectivity forces
all boundary matrices `Z j` to share a common right factor. This yields the
open-chain extension theorem `groundSpace_extend_right_of_isNBlkInjective`.

## Main results

- `MPSTensor.exists_right_factor_of_evalWord_compatibility` — common right-factor
  extraction from universal word compatibility
- `MPSTensor.groundSpace_extend_right_of_isNBlkInjective` — if the long left
  window and the suffix window both lie in the ground space, then the whole
  state lies in the ground space

## References

* [CPGSV21] arXiv:2011.12127, lines 2049–2078
-/

open scoped Matrix

namespace MPSTensor

variable {d D : ℕ}

/-- Letter compatibility extends to every nonempty word by multiplying the
corresponding boundary matrix on the right by the remaining suffix product. -/
private theorem exists_evalWord_factor_of_letter_compatibility {A : MPSTensor d D}
    {Z : Fin d → Matrix (Fin D) (Fin D) ℂ}
    (hCompat : ∀ i : Fin d, ∃ Y : Matrix (Fin D) (Fin D) ℂ,
      ∀ j : Fin d, Z j * A i = A j * Y)
    (w : List (Fin d)) (hw : w ≠ []) :
    ∃ Y : Matrix (Fin D) (Fin D) ℂ,
      ∀ j : Fin d, Z j * evalWord A w = A j * Y := by
  cases w with
  | nil => cases hw rfl
  | cons i w =>
      obtain ⟨Y, hY⟩ := hCompat i
      refine ⟨Y * evalWord A w, ?_⟩
      intro j
      calc
        Z j * evalWord A (i :: w)
            = Z j * (A i * evalWord A w) := by simp [evalWord]
        _ = (Z j * A i) * evalWord A w := by rw [Matrix.mul_assoc]
        _ = (A j * Y) * evalWord A w := by rw [hY j]
        _ = A j * (Y * evalWord A w) := by rw [Matrix.mul_assoc]

/-- If the compatibility identity is available for every single physical letter,
then block injectivity yields a common right factor. -/
private theorem exists_right_factor_of_letter_compatibility [NeZero D]
    {A : MPSTensor d D} {L₀ : ℕ}
    (hInj : IsNBlkInjective A L₀) (hL₀ : 0 < L₀)
    {Z : Fin d → Matrix (Fin D) (Fin D) ℂ}
    (hCompat : ∀ i : Fin d, ∃ Y : Matrix (Fin D) (Fin D) ℂ,
      ∀ j : Fin d, Z j * A i = A j * Y) :
    ∃ X : Matrix (Fin D) (Fin D) ℂ, ∀ j : Fin d, Z j = A j * X := by
  have hBlkInj : IsInjective (blockTensor A L₀) :=
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
    simpa [blockTensor] using hY j
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
of length `K + 1` reduces to the single-letter case by stripping the first
letter and applying the induction hypothesis to the matrices `Z j * A i`. -/
private theorem exists_right_factor_of_evalWord_compatibility_succ [NeZero D]
    {A : MPSTensor d D} {L₀ : ℕ}
    (hInj : IsNBlkInjective A L₀) (hL₀ : 0 < L₀) :
    ∀ K : ℕ, ∀ {Z : Fin d → Matrix (Fin D) (Fin D) ℂ},
      (∀ σ : Fin (K + 1) → Fin d, ∃ Yσ : Matrix (Fin D) (Fin D) ℂ,
        ∀ j : Fin d, Z j * evalWord A (List.ofFn σ) = A j * Yσ) →
      ∃ X : Matrix (Fin D) (Fin D) ℂ, ∀ j : Fin d, Z j = A j * X
  | 0, Z, hCompat =>
      have hCompat1 : ∀ i : Fin d, ∃ Y : Matrix (Fin D) (Fin D) ℂ,
          ∀ j : Fin d, Z j * A i = A j * Y := by
        intro i
        let σ : Fin 1 → Fin d := fun _ => i
        obtain ⟨Y, hY⟩ := hCompat σ
        refine ⟨Y, ?_⟩
        intro j
        simpa [σ, evalWord] using hY j
      exists_right_factor_of_letter_compatibility hInj hL₀ hCompat1
  | K + 1, Z, hCompat =>
      have hCompat1 : ∀ i : Fin d, ∃ X : Matrix (Fin D) (Fin D) ℂ,
          ∀ j : Fin d, Z j * A i = A j * X := by
        intro i
        let Zi : Fin d → Matrix (Fin D) (Fin D) ℂ := fun j => Z j * A i
        have hCompatZi : ∀ σ : Fin (K + 1) → Fin d,
            ∃ Yσ : Matrix (Fin D) (Fin D) ℂ,
              ∀ j : Fin d, Zi j * evalWord A (List.ofFn σ) = A j * Yσ := by
          intro σ
          obtain ⟨Yσ, hYσ⟩ := hCompat (Fin.cons i σ)
          refine ⟨Yσ, ?_⟩
          intro j
          simpa [Zi, evalWord_ofFn_cons, Matrix.mul_assoc] using hYσ j
        obtain ⟨X, hX⟩ :=
          exists_right_factor_of_evalWord_compatibility_succ hInj hL₀ K hCompatZi
        exact ⟨X, hX⟩
      exists_right_factor_of_letter_compatibility hInj hL₀ hCompat1

/-- If a family of boundary matrices satisfies the compatibility identity
`Z j * A^σ = A j * Y_σ` for every length-`K` word `σ`, then all `Z j` share a
common right factor. -/
theorem exists_right_factor_of_evalWord_compatibility [NeZero D]
    {A : MPSTensor d D} {K L₀ : ℕ}
    (hInj : IsNBlkInjective A L₀) (hL₀ : 0 < L₀)
    {Z : Fin d → Matrix (Fin D) (Fin D) ℂ}
    (hCompat : ∀ σ : Fin K → Fin d, ∃ Yσ : Matrix (Fin D) (Fin D) ℂ,
      ∀ j : Fin d, Z j * evalWord A (List.ofFn σ) = A j * Yσ) :
    ∃ X : Matrix (Fin D) (Fin D) ℂ, ∀ j : Fin d, Z j = A j * X := by
  cases K with
  | zero =>
      let σ : Fin 0 → Fin d := Fin.elim0
      obtain ⟨Y, hY⟩ := hCompat σ
      refine ⟨Y, ?_⟩
      intro j
      simpa [σ, evalWord] using hY j
  | succ K =>
      exact exists_right_factor_of_evalWord_compatibility_succ hInj hL₀ K hCompat

/-- If two adjacent open-chain windows satisfy the ground-space condition at the
injectivity length `L₀ + 1`, then the full `(K + L₀ + 1)`-site state is itself
in the open-chain ground space. -/
theorem groundSpace_extend_right_of_isNBlkInjective
    [NeZero D] {A : MPSTensor d D} {K L₀ : ℕ} (hInj : IsNBlkInjective A L₀)
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
