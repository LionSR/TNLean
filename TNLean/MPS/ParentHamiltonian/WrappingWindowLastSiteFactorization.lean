/-
Copyright (c) 2025 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.Basic
import TNLean.MPS.ParentHamiltonian.BlockStrip
import TNLean.MPS.ParentHamiltonian.CyclicWindow
import TNLean.MPS.FundamentalTheorem.FiniteLength
import TNLean.Wielandt.SpanGrowth.VectorToMatrixSpan

/-!
# Last-site factorization of a wrapping cyclic window

Coordinate and word-product factorizations for the cyclic window beginning at
the last site of a periodic chain.
-/

open scoped Matrix BigOperators

namespace MPSTensor

variable {d D : ℕ}

/-! ### Cyclic config decomposition at the last-site boundary-crossing position

These lemmas analyze the structure of `cyclicCfg` at position \(N-1\),
where the window wraps from the last site back to the first sites. -/

/-- At the last-site boundary-crossing position \(N-1\), the cyclic config's last site is
\(\sigma_w(0)\). -/
private theorem cyclicCfg_last_eq {N L : ℕ} (hN : 2 ≤ N) (hLN : L ≤ N) (hL : 1 < L)
    (σ_w : Fin L → Fin d) (τ : Fin N → Fin d) :
    cyclicCfg (by omega : 0 < N) L ⟨N - 1, by omega⟩ σ_w τ ⟨N - 1, by omega⟩ =
      σ_w ⟨0, by omega⟩ := by
  simp only [cyclicCfg]
  have hval : (N - 1 : ℕ) + N - (N - 1 : ℕ) = N := by omega
  have hoffset : ((N - 1) + N - (N - 1)) % N = 0 := by
    rw [hval]; exact Nat.mod_self N
  rw [dite_eq_left (show ((N - 1) + N - (N - 1)) % N < L by rw [hoffset]; omega)]
  congr 1; ext; simp

/-- At the wrapping position \(N-1\), sites \(0,\ldots,L-2\) get
\(\sigma_w(1),\ldots,\sigma_w(L-1)\). -/
private theorem cyclicCfg_window_site {N L : ℕ} (hN : 2 ≤ N) (_hLN : L ≤ N) (hL : 1 < L)
    (σ_w : Fin L → Fin d) (τ : Fin N → Fin d)
    {k : ℕ} (hk : k < L - 1) :
    cyclicCfg (by omega : 0 < N) L ⟨N - 1, by omega⟩ σ_w τ ⟨k, by omega⟩ =
      σ_w ⟨k + 1, by omega⟩ := by
  simp only [cyclicCfg]
  have hoffset : (k + N - (N - 1)) % N = k + 1 := by
    have : k + N - (N - 1) = k + 1 := by omega
    rw [this, Nat.mod_eq_of_lt (by omega)]
  rw [dite_eq_left (show (k + N - (N - 1)) % N < L by rw [hoffset]; omega)]
  congr 1; ext; simp [hoffset]

/-- At the wrapping position \(N-1\), complement sites get \(\tau\) values. -/
private theorem cyclicCfg_complement_site {N L : ℕ} (hN : 2 ≤ N) (_hLN : L ≤ N) (hL : 1 < L)
    (σ_w : Fin L → Fin d) (τ : Fin N → Fin d)
    {k : ℕ} (hk1 : L - 1 ≤ k) (hk2 : k < N - 1) :
    cyclicCfg (by omega : 0 < N) L ⟨N - 1, by omega⟩ σ_w τ ⟨k, by omega⟩ =
      τ ⟨k, by omega⟩ := by
  simp only [cyclicCfg]
  have hoffset : (k + N - (N - 1)) % N = k + 1 := by
    have : k + N - (N - 1) = k + 1 := by omega
    rw [this, Nat.mod_eq_of_lt (by omega)]
  rw [dite_eq_right (show ¬((k + N - (N - 1)) % N < L) by rw [hoffset]; omega)]

/-! ### Snoc factorization

Factor the full cyclic configuration product as \(A^{\mathrm{init}} A_{\sigma_w(0)}\),
then split \(\mathrm{init}\) into window-tail and complement parts. -/

/-- The word product along the cyclic configuration at position \(M\) on \(M+1\) sites
decomposes as \(A^{\mathrm{init}} A_{\sigma_w(0)}\), where \(\mathrm{init}\) covers
sites \(0,\ldots,M-1\). -/
theorem evalWord_cyclicCfg_snoc {A : MPSTensor d D}
    {M L : ℕ} (hM : 1 ≤ M) (hLN : L ≤ M + 1) (hL : 1 < L)
    (σ_w : Fin L → Fin d) (τ : Fin (M + 1) → Fin d) :
    Kraus.evalWord A (List.ofFn (cyclicCfg (by omega : 0 < M + 1) L ⟨M, by omega⟩ σ_w τ)) =
    Kraus.evalWord A (List.ofFn (fun k : Fin M =>
      cyclicCfg (by omega : 0 < M + 1) L ⟨M, by omega⟩ σ_w τ
        (Fin.castSucc k))) *
    A (σ_w ⟨0, by omega⟩) := by
  set cfg := cyclicCfg (by omega : 0 < M + 1) L ⟨M, by omega⟩ σ_w τ
  -- cfg = Fin.snoc init (σ_w 0)
  have hsnoc : cfg = Fin.snoc (fun k : Fin M => cfg (Fin.castSucc k))
      (σ_w ⟨0, by omega⟩) := by
    funext ⟨k, hk⟩
    by_cases hkM : k < M
    · have : (⟨k, hk⟩ : Fin (M + 1)) = Fin.castSucc ⟨k, hkM⟩ := by
        ext; simp [Fin.castSucc]
      rw [this, Fin.snoc_castSucc]
    · have : (⟨k, hk⟩ : Fin (M + 1)) = Fin.last M := by
        ext; simp [Fin.last]; omega
      rw [this, Fin.snoc_last]
      exact cyclicCfg_last_eq (by omega) hLN hL σ_w τ
  rw [show List.ofFn cfg = List.ofFn (Fin.snoc (fun k : Fin M => cfg (Fin.castSucc k))
      (σ_w ⟨0, by omega⟩)) from by rw [← hsnoc]]
  rw [evalWord_ofFn_snoc]

/-- The init part of the cyclic config at position M decomposes into
tail (window sites 1..L-1) and complement (sites L-1..M-1). -/
theorem init_evalWord_split {A : MPSTensor d D}
    {M L : ℕ} (hM : 1 ≤ M) (hLN : L ≤ M + 1) (hL : 1 < L)
    (σ_w : Fin L → Fin d) (τ : Fin (M + 1) → Fin d) :
    Kraus.evalWord A (List.ofFn (fun k : Fin M =>
      cyclicCfg (by omega : 0 < M + 1) L ⟨M, by omega⟩ σ_w τ (Fin.castSucc k))) =
    Kraus.evalWord A (List.ofFn (fun k : Fin (L - 1) => σ_w ⟨k.val + 1, by omega⟩)) *
    Kraus.evalWord A (List.ofFn (fun k : Fin (M + 1 - L) =>
      τ ⟨k.val + L - 1, by omega⟩)) := by
  rw [← Kraus.evalWord_append]
  congr 1
  apply List.ext_getElem
  · simp only [List.length_ofFn, List.length_append]; omega
  · intro k hk1 hk2
    simp only [List.length_ofFn] at hk1
    simp only [List.getElem_ofFn]
    by_cases hkL : k < L - 1
    · -- Window site: init(k) = σ_w(k+1)
      rw [List.getElem_append_left (by simp only [List.length_ofFn]; exact hkL),
          List.getElem_ofFn]
      exact cyclicCfg_window_site (by omega) (by omega) hL σ_w τ hkL
    · -- Complement site: init(k) = τ(k)
      rw [List.getElem_append_right (by simp only [List.length_ofFn]; omega),
          List.getElem_ofFn]
      simp only [List.length_ofFn]
      have hcomp := cyclicCfg_complement_site (by omega : 2 ≤ M + 1) hLN hL σ_w τ
        (show L - 1 ≤ k from by omega) (show k < M from by omega)
      -- hcomp is about cyclicCfg at the original index; use Fin.castSucc ⟨k, _⟩.
      have : (Fin.castSucc (⟨k, by omega⟩ : Fin M) : Fin (M + 1)) =
          ⟨k, by omega⟩ := by ext; simp [Fin.castSucc]
      rw [this] at *
      -- The complement site: cyclicCfg returns τ(k)
      -- After unfolding, offset = k+1 ≥ L, so returns τ
      unfold cyclicCfg
      simp only []
      have hoffset : (k + (M + 1) - M) % (M + 1) = k + 1 := by
        have : k + (M + 1) - M = k + 1 := by omega
        rw [this, Nat.mod_eq_of_lt (by omega)]
      rw [dite_eq_right (by rw [hoffset]; omega)]
      congr 1; ext; simp; omega

end MPSTensor
