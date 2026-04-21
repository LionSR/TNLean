/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.SuffixWindow

/-!
# Open-chain range reduction from suffix windows

This file proves the open-chain grow-back theorem used in the normal-MPS range
reduction argument for parent Hamiltonians. Starting from the suffix-window API
in `SuffixWindow.lean`, we first extract a common right factor from a family of
matrix compatibility relations, then use that factor to regrow an element of the
full ground space.

## Main statements

- `MPSTensor.groundSpace_extend_right_of_isNBlkInjective` — if the first
  `K + L₀` sites lie in `groundSpace A (K + L₀)` after fixing the last letter,
  and every suffix slice of length `L₀ + 1` lies in `groundSpace A (L₀ + 1)`,
  then the whole state lies in `groundSpace A (K + L₀ + 1)`.

## Implementation notes

The algebraic core is a recursive grow-back lemma. Its base step uses an
`L₀`-blocked decomposition of the identity, obtained from block injectivity of
`A`, while the recursive step strips the first letter of a word and re-applies
that base result.

## References

* [CPGSV21] arXiv:2011.12127, lines 2049–2078
-/

open scoped Matrix BigOperators

namespace MPSTensor

variable {d D : ℕ}

/-- Block injectivity at length `L₀ > 0` yields matrices `R i` with
`∑ i, A i * R i = 1`. -/
private theorem exists_left_decomposition_of_isNBlkInjective {A : MPSTensor d D}
    [NeZero D] {L₀ : ℕ} (hInj : IsNBlkInjective A L₀) (hL₀ : 0 < L₀) :
    ∃ R : Fin d → Matrix (Fin D) (Fin D) ℂ, ∑ i, A i * R i = 1 := by
  obtain ⟨K, hK⟩ := Nat.exists_eq_add_of_lt hL₀
  rw [zero_add] at hK
  subst hK
  let hBlk : IsInjective (blockTensor A (K + 1)) :=
    (isNBlkInjective_iff_blockTensor_isInjective A (K + 1)).mp hInj
  let c : Fin (blockPhysDim d (K + 1)) → ℂ := decompositionMap hBlk 1
  let cWord : (Fin (K + 1) → Fin d) → ℂ :=
    fun σ => c (Fintype.equivFin (Fin (K + 1) → Fin d) σ)
  have hdecompWords :
      ∑ σ : Fin (K + 1) → Fin d, cWord σ • evalWord A (List.ofFn σ) = 1 := by
    have hdecomp :
        ∑ i : Fin (blockPhysDim d (K + 1)), c i • blockTensor A (K + 1) i = 1 := by
      unfold c
      exact decompositionMap_sum hBlk (1 : Matrix (Fin D) (Fin D) ℂ)
    have hsum :
        ∑ σ : Fin (K + 1) → Fin d, cWord σ • evalWord A (List.ofFn σ) =
          ∑ i : Fin (blockPhysDim d (K + 1)), c i • blockTensor A (K + 1) i := by
      symm
      simpa [cWord, blockTensor, wordOfBlock, decodeBlock] using
        (Fintype.sum_equiv (Fintype.equivFin (Fin (K + 1) → Fin d)).symm
          (f := fun i : Fin (blockPhysDim d (K + 1)) => c i • blockTensor A (K + 1) i)
          (g := fun σ : Fin (K + 1) → Fin d => cWord σ • evalWord A (List.ofFn σ))
          (by
            intro i
            simp [cWord, blockTensor, wordOfBlock, decodeBlock]))
    exact hsum.trans hdecomp
  let R : Fin d → Matrix (Fin D) (Fin D) ℂ :=
    fun i => ∑ τ : Fin K → Fin d, cWord (Fin.cons i τ) • evalWord A (List.ofFn τ)
  refine ⟨R, ?_⟩
  calc
    ∑ i, A i * R i
        = ∑ i, ∑ τ : Fin K → Fin d,
            A i * (cWord (Fin.cons i τ) • evalWord A (List.ofFn τ)) := by
              simp [R, Finset.mul_sum]
    _ = ∑ i, ∑ τ : Fin K → Fin d,
            cWord (Fin.cons i τ) • (A i * evalWord A (List.ofFn τ)) := by
              refine Finset.sum_congr rfl ?_
              intro i _
              refine Finset.sum_congr rfl ?_
              intro τ _
              rw [Matrix.mul_smul]
    _ = ∑ i, ∑ τ : Fin K → Fin d,
            cWord (Fin.cons i τ) • evalWord A (List.ofFn (Fin.cons i τ)) := by
              refine Finset.sum_congr rfl ?_
              intro i _
              refine Finset.sum_congr rfl ?_
              intro τ _
              rw [evalWord_ofFn_cons]
    _ = ∑ p : Fin d × (Fin K → Fin d),
            cWord (Fin.cons p.1 p.2) • evalWord A (List.ofFn (Fin.cons p.1 p.2)) := by
          simpa using
            (Fintype.sum_prod_type
              (f := fun p : Fin d × (Fin K → Fin d) =>
                cWord (Fin.cons p.1 p.2) • evalWord A (List.ofFn (Fin.cons p.1 p.2)))).symm
    _ = ∑ σ : Fin (K + 1) → Fin d, cWord σ • evalWord A (List.ofFn σ) := by
          simpa using
            (Fintype.sum_equiv (Fin.consEquiv (fun _ => Fin d))
              (f := fun p : Fin d × (Fin K → Fin d) =>
                cWord (Fin.cons p.1 p.2) • evalWord A (List.ofFn (Fin.cons p.1 p.2)))
              (g := fun σ : Fin (K + 1) → Fin d => cWord σ • evalWord A (List.ofFn σ))
              (by
                intro p
                rcases p with ⟨i, τ⟩
                rfl))
    _ = 1 := hdecompWords

/-- If a family `Z j` satisfies the one-letter compatibility
`Z j * A i = A j * Y i`, then it has a common right factor. -/
private theorem exists_common_right_factor_of_letter_compatibility
    {A : MPSTensor d D} [NeZero D] {L₀ : ℕ} (hInj : IsNBlkInjective A L₀)
    (hL₀ : 0 < L₀) {Z : Fin d → Matrix (Fin D) (Fin D) ℂ}
    (hCompat : ∀ i : Fin d, ∃ Y : Matrix (Fin D) (Fin D) ℂ,
      ∀ j : Fin d, Z j * A i = A j * Y) :
    ∃ X : Matrix (Fin D) (Fin D) ℂ, ∀ j : Fin d, Z j = A j * X := by
  obtain ⟨R, hR⟩ := exists_left_decomposition_of_isNBlkInjective hInj hL₀
  choose Y hY using hCompat
  refine ⟨∑ i, Y i * R i, ?_⟩
  intro j
  calc
    Z j = Z j * 1 := by simp
    _ = Z j * (∑ i, A i * R i) := by rw [hR]
    _ = ∑ i, (Z j * A i) * R i := by
          simp [Matrix.mul_assoc, Matrix.mul_sum]
    _ = ∑ i, (A j * Y i) * R i := by
          refine Finset.sum_congr rfl ?_
          intro i _
          rw [hY i j]
    _ = A j * ∑ i, Y i * R i := by
          simp [Matrix.mul_assoc, Matrix.mul_sum]

/-- Word-indexed compatibility relations admit a common right factor. -/
private theorem exists_common_right_factor_of_word_compatibility
    {A : MPSTensor d D} [NeZero D] {L₀ K : ℕ} (hInj : IsNBlkInjective A L₀)
    (hL₀ : 0 < L₀) (hK : 0 < K) {Z : Fin d → Matrix (Fin D) (Fin D) ℂ}
    (hCompat : ∀ σ : Fin K → Fin d, ∃ Y : Matrix (Fin D) (Fin D) ℂ,
      ∀ j : Fin d, Z j * evalWord A (List.ofFn σ) = A j * Y) :
    ∃ X : Matrix (Fin D) (Fin D) ℂ, ∀ j : Fin d, Z j = A j * X := by
  obtain ⟨n, hn⟩ := Nat.exists_eq_add_of_lt hK
  rw [zero_add] at hn
  subst hn
  induction n generalizing Z with
  | zero =>
      apply exists_common_right_factor_of_letter_compatibility hInj hL₀
      intro i
      rcases hCompat (fun _ => i) with ⟨Y, hY⟩
      refine ⟨Y, ?_⟩
      intro j
      simpa [evalWord] using hY j
  | succ n ih =>
      have hPos : 0 < n + 1 := by omega
      have hLetters : ∀ i : Fin d, ∃ Y : Matrix (Fin D) (Fin D) ℂ,
          ∀ j : Fin d, Z j * A i = A j * Y := by
        intro i
        have hCompatTail :
            ∀ σ : Fin (n + 1) → Fin d, ∃ Y : Matrix (Fin D) (Fin D) ℂ,
              ∀ j : Fin d, (Z j * A i) * evalWord A (List.ofFn σ) = A j * Y := by
          intro σ
          rcases hCompat (Fin.cons i σ) with ⟨Y, hY⟩
          refine ⟨Y, ?_⟩
          intro j
          simpa [evalWord_ofFn_cons, Matrix.mul_assoc] using hY j
        obtain ⟨X, hX⟩ := ih hPos hCompatTail
        exact ⟨X, hX⟩
      exact exists_common_right_factor_of_letter_compatibility hInj hL₀ hLetters

/-- If the left `K + L₀` sites and every suffix slice of length `L₀ + 1`
satisfy the corresponding ground-space conditions, then the whole `(K + L₀ + 1)`-
site state lies in `groundSpace A (K + L₀ + 1)`. -/
theorem groundSpace_extend_right_of_isNBlkInjective
    {A : MPSTensor d D} [NeZero D] {K L₀ : ℕ} (hInj : IsNBlkInjective A L₀)
    (hL₀ : 0 < L₀) (hK : 0 < K) {ψ : NSiteSpace d (K + L₀ + 1)}
    (hLeft : InLeftGround A (K + L₀) ψ)
    (hTail : InTailGround A K (L₀ + 1) ψ) :
    ψ ∈ groundSpace A (K + L₀ + 1) := by
  obtain ⟨Z, Y, hZ, _hY, hCompat⟩ :=
    exists_left_tail_compatibility (A := A) (K := K) (L₀ := L₀) hInj hLeft hTail
  have hCompat' :
      ∀ σ : Fin K → Fin d, ∃ Y' : Matrix (Fin D) (Fin D) ℂ,
        ∀ j : Fin d, Z j * evalWord A (List.ofFn σ) = A j * Y' := by
    intro σ
    exact ⟨Y σ, fun j => hCompat j σ⟩
  obtain ⟨X, hX⟩ :=
    exists_common_right_factor_of_word_compatibility
      (A := A) (L₀ := L₀) (K := K) hInj hL₀ hK hCompat'
  rw [groundSpace, LinearMap.mem_range]
  refine ⟨X, ?_⟩
  ext τ
  calc
    groundSpaceMap A (K + L₀ + 1) X τ
        = groundSpaceMap A (K + L₀ + 1) X
            (Fin.snoc (Fin.init τ) (τ (Fin.last (K + L₀)))) := by
              rw [Fin.snoc_init_self]
    _ = Matrix.trace (evalWord A (List.ofFn (Fin.init τ)) * (A (τ (Fin.last (K + L₀))) * X)) := by
          simp only [groundSpaceMap_apply, evalWord_ofFn_snoc, Matrix.mul_assoc]
    _ = Matrix.trace (evalWord A (List.ofFn (Fin.init τ)) * Z (τ (Fin.last (K + L₀)))) := by
          rw [(hX (τ (Fin.last (K + L₀)))).symm]
    _ = restrictLast ψ (τ (Fin.last (K + L₀))) (Fin.init τ) := by
          rw [hZ (τ (Fin.last (K + L₀)))]
          simp [groundSpaceMap_apply]
    _ = ψ (Fin.snoc (Fin.init τ) (τ (Fin.last (K + L₀)))) := by
          simp [restrictLast_apply]
    _ = ψ τ := by
          rw [Fin.snoc_init_self]

end MPSTensor
