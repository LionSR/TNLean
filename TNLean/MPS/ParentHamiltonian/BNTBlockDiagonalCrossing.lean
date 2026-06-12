/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.ParentHamiltonian.BNTBlockDiagonalChain

/-!
# Crossing-window boundary equations for block-diagonal parent spaces

This file isolates the cyclic-window step for a block component when the window
crosses the chosen cut.  The input is the blockwise matrix identity appearing in
the boundary-closing part of arXiv:quant-ph/0608197, Theorem 2blocks.2.
-/

open scoped Matrix BigOperators

namespace MPSTensor

variable {d : ℕ}

/-- A crossing cyclic window is local when the boundary matrix satisfies the
crossing identity for the wrapped head and the complementary interval.

Let the cyclic window beginning at \(i\) cross the cut, so \(N<i+L\). Write
\(a=i+L-N\). The sites \(0,\ldots,a-1\) carry the wrapped head of the window,
the sites \(a,\ldots,i-1\) carry the outside configuration, and the sites
\(i,\ldots,N-1\) carry the tail of the window. If, for every head word
\(\beta\), there is a matrix \(E\) such that
\[
  \mu_j^N X_j A^j_\beta
    A^j_{\tau_a}\cdots A^j_{\tau_{i-1}}
    =
  A^j_\beta E,
\]
then the restriction is the local vector \(\Gamma_L^{A_j}(E)\).

This is the matrix form of the boundary-closing comparison in
arXiv:quant-ph/0608197, Theorem 2blocks.2, proof lines 1436--1456. -/
theorem blockDiagonal_boundary_cyclicRestrict_component_mem_groundSpace_of_crossing_matrix
    {r : ℕ} {dim : Fin r → ℕ}
    (μ : Fin r → ℂ) (A : (j : Fin r) → MPSTensor d (dim j))
    {L N : ℕ} (hN : 0 < N) (hLN : L ≤ N)
    (X : (j : Fin r) → Matrix (Fin (dim j)) (Fin (dim j)) ℂ)
    (j : Fin r) (i : Fin N) (τ : Fin N → Fin d)
    (hi : N < i.val + L)
    (hIdentity : ∃ E : Matrix (Fin (dim j)) (Fin (dim j)) ℂ,
      ∀ β : Fin (i.val + L - N) → Fin d,
        (((μ j) ^ N • X j) * evalWord (A j) (List.ofFn β)) *
            evalWord (A j) (List.ofFn fun k : Fin (N - L) =>
              τ ⟨i.val + L - N + k.val, by omega⟩) =
          evalWord (A j) (List.ofFn β) * E) :
    cyclicRestrictₗ hN L i τ
        (groundSpaceMap (A j) N ((μ j) ^ N • X j)) ∈
      groundSpace (A j) L := by
  classical
  rcases hIdentity with ⟨E, hE⟩
  rw [groundSpace, LinearMap.mem_range]
  refine ⟨E, ?_⟩
  ext σ
  let headWord : List (Fin d) := List.ofFn fun k : Fin (i.val + L - N) =>
    σ ⟨N - i.val + k.val, by omega⟩
  let middleWord : List (Fin d) := List.ofFn fun k : Fin (N - L) =>
    τ ⟨i.val + L - N + k.val, by omega⟩
  let tailWord : List (Fin d) := List.ofFn fun k : Fin (N - i.val) =>
    σ ⟨k.val, by omega⟩
  let Xj : Matrix (Fin (dim j)) (Fin (dim j)) ℂ := (μ j) ^ N • X j
  have hσ : List.ofFn σ = tailWord ++ headWord := by
    apply List.ext_getElem
    · simp [tailWord, headWord, List.length_ofFn]
      omega
    · intro k hk₁ hk₂
      have hkL : k < L := by
        simpa only [List.length_ofFn] using hk₁
      simp only [List.getElem_ofFn]
      by_cases hkTail : k < N - i.val
      · rw [List.getElem_append_left]
        · have htail :
              tailWord[k]'(by simpa [tailWord, List.length_ofFn] using hkTail) =
                σ ⟨k, hkL⟩ := by
            simp only [tailWord, List.getElem_ofFn]
          rw [htail]
        · simpa [tailWord, List.length_ofFn] using hkTail
      · rw [List.getElem_append_right]
        · have hidx : k - tailWord.length < headWord.length := by
            simp [tailWord, headWord, List.length_ofFn]
            omega
          have hhead :
              headWord[k - tailWord.length]'hidx = σ ⟨k, hkL⟩ := by
            simp only [headWord, List.getElem_ofFn]
            congr 1
            ext
            simp [tailWord, List.length_ofFn]
            omega
          rw [hhead]
        · simpa [tailWord, List.length_ofFn] using
            (show tailWord.length ≤ k by simp [tailWord, List.length_ofFn]; omega)
  have hcfg :
      List.ofFn (cyclicCfg hN L i σ τ) = headWord ++ (middleWord ++ tailWord) := by
    apply List.ext_getElem
    · simp [headWord, middleWord, tailWord, List.length_ofFn]
      omega
    · intro k hk₁ hk₂
      have hkN : k < N := by
        simpa only [List.length_ofFn] using hk₁
      simp only [List.getElem_ofFn]
      by_cases hkHead : k < i.val + L - N
      · have hoff : (k + N - i.val) % N = N - i.val + k := by
          have hsum : k + N - i.val = N - i.val + k := by omega
          rw [hsum]
          exact Nat.mod_eq_of_lt (by omega)
        have hoffLt : (k + N - i.val) % N < L := by
          rw [hoff]
          omega
        rw [cyclicCfg, dif_pos hoffLt]
        rw [List.getElem_append_left]
        · have hhead :
              headWord[k]'(by simpa [headWord, List.length_ofFn] using hkHead) =
                σ ⟨N - i.val + k, by omega⟩ := by
            simp only [headWord, List.getElem_ofFn]
          rw [hhead]
          exact congrArg σ (Fin.ext hoff)
        · simpa [headWord, List.length_ofFn] using hkHead
      · by_cases hkMiddle : k < i.val
        · have hoff : (k + N - i.val) % N = k + N - i.val := by
            exact Nat.mod_eq_of_lt (by omega)
          have hoffNot : ¬(k + N - i.val) % N < L := by
            rw [hoff]
            omega
          rw [cyclicCfg, dif_neg hoffNot]
          rw [List.getElem_append_right]
          · rw [List.getElem_append_left]
            · have hidx :
                  k - headWord.length < middleWord.length := by
                simp [headWord, middleWord, List.length_ofFn]
                omega
              have hmiddle :
                  middleWord[k - headWord.length]'hidx = τ ⟨k, hkN⟩ := by
                simp only [middleWord, List.getElem_ofFn]
                congr 1
                ext
                simp [headWord, List.length_ofFn]
                omega
              rw [hmiddle]
            · simp [headWord, middleWord, List.length_ofFn]
              omega
          · simp [headWord, List.length_ofFn]
            omega
        · have hi_le_k : i.val ≤ k := by omega
          have hoff : (k + N - i.val) % N = k - i.val := by
            have hsum : k + N - i.val = k - i.val + N := by omega
            rw [hsum, Nat.add_mod_right]
            exact Nat.mod_eq_of_lt (by omega)
          have hoffLt : (k + N - i.val) % N < L := by
            rw [hoff]
            omega
          rw [cyclicCfg, dif_pos hoffLt]
          rw [List.getElem_append_right]
          · rw [List.getElem_append_right]
            · have hidx :
                  k - headWord.length - middleWord.length < tailWord.length := by
                simp [headWord, middleWord, tailWord, List.length_ofFn]
                omega
              have htail :
                  tailWord[k - headWord.length - middleWord.length]'hidx =
                    σ ⟨k - i.val, by omega⟩ := by
                simp only [tailWord, List.getElem_ofFn]
                congr 1
                ext
                simp [headWord, middleWord, List.length_ofFn]
                omega
              rw [htail]
              exact congrArg σ (Fin.ext hoff)
            · simp [headWord, middleWord, List.length_ofFn]
              omega
          · simp [headWord, List.length_ofFn]
            omega
  have hIdentityσ :
      (Xj * evalWord (A j) headWord) * evalWord (A j) middleWord =
        evalWord (A j) headWord * E := by
    simpa [Xj, headWord, middleWord] using
      hE (fun k : Fin (i.val + L - N) => σ ⟨N - i.val + k.val, by omega⟩)
  simp only [groundSpaceMap_apply, cyclicRestrictₗ_apply]
  rw [hσ, hcfg, evalWord_append, evalWord_append, evalWord_append]
  set H := evalWord (A j) headWord
  set M := evalWord (A j) middleWord
  set T := evalWord (A j) tailWord
  calc
    Matrix.trace ((T * H) * E) = Matrix.trace (T * (H * E)) := by
      rw [Matrix.mul_assoc]
    _ = Matrix.trace (T * ((Xj * H) * M)) := by
      rw [hIdentityσ]
    _ = Matrix.trace ((T * Xj) * (H * M)) := by
      rw [← Matrix.mul_assoc T (Xj * H) M]
      rw [← Matrix.mul_assoc T Xj H]
      rw [Matrix.mul_assoc (T * Xj) H M]
    _ = Matrix.trace ((H * M) * (T * Xj)) := Matrix.trace_mul_comm _ _
    _ = Matrix.trace (((H * M) * T) * Xj) := by
      rw [← Matrix.mul_assoc (H * M) T Xj]
    _ = Matrix.trace ((H * (M * T)) * Xj) := by
      rw [Matrix.mul_assoc H M T]
    _ = Matrix.trace ((H * (M * T)) * ((μ j) ^ N • X j)) := by
      rfl

end MPSTensor
