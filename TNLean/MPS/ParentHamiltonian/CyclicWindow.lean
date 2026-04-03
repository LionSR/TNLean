/-
Copyright (c) 2025 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.ParentHamiltonian.IntersectionProperty

/-!
# Cyclic window infrastructure for periodic MPS chains

This file provides the infrastructure for restricting N-site quantum states to
cyclic windows of L consecutive sites on a periodic chain.

## Main results

* `MPSTensor.contiguous_mem_groundSpace` — iterated intersection:
  non-wrapping window conditions imply membership in the open-chain ground space
-/

open scoped Matrix BigOperators

namespace MPSTensor

variable {d D : ℕ}

/-! ### Contiguous (non-wrapping) window extraction -/

/-- Assemble an N-site configuration by placing window values `σ` at
contiguous sites `[s, s+1, ..., s+M-1]` and using `τ` for the remaining sites. -/
def contiguousCfg {N : ℕ} (s M : ℕ)
    (σ : Fin M → Fin d) (τ : Fin N → Fin d) : Fin N → Fin d :=
  fun k => if h : s ≤ k.val ∧ k.val < s + M
           then σ ⟨k.val - s, by omega⟩
           else τ k

/-- Linear restriction to a contiguous block `[s, s+1, ..., s+M-1]`. -/
def contiguousRestrictₗ {N : ℕ} (s M : ℕ) (_hsM : s + M ≤ N)
    (τ : Fin N → Fin d) : NSiteSpace d N →ₗ[ℂ] NSiteSpace d M where
  toFun ψ σ := ψ (contiguousCfg s M σ τ)
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

@[simp]
theorem contiguousRestrictₗ_apply {N : ℕ} (s M : ℕ) (hsM : s + M ≤ N)
    (τ : Fin N → Fin d) (ψ : NSiteSpace d N) (σ : Fin M → Fin d) :
    contiguousRestrictₗ s M hsM τ ψ σ = ψ (contiguousCfg s M σ τ) := rfl

/-- The contiguous config at position 0 with M = N covers all sites. -/
theorem contiguousCfg_zero_full {N : ℕ} (σ : Fin N → Fin d) (τ : Fin N → Fin d) :
    contiguousCfg (N := N) 0 N σ τ = σ := by
  ext ⟨k, hk⟩
  simp only [contiguousCfg, Nat.zero_le, true_and]
  simp [hk]

/-- Restricting the last site of a contiguous `(M+1)`-block peels off
the rightmost site and extends the outside config. -/
theorem contiguousRestrictₗ_restrictLast {N : ℕ} (s M : ℕ) (hsM1 : s + (M + 1) ≤ N)
    (τ : Fin N → Fin d) (ψ : NSiteSpace d N) (j : Fin d) :
    restrictLast (contiguousRestrictₗ s (M + 1) hsM1 τ ψ) j =
    contiguousRestrictₗ s M (by omega) (Function.update τ ⟨s + M, by omega⟩ j) ψ := by
  ext σ
  simp only [restrictLast_apply, contiguousRestrictₗ_apply]
  congr 1; ext ⟨k, hk⟩
  simp only [contiguousCfg]
  by_cases hwin : s ≤ k ∧ k < s + M
  · -- k is in the smaller window [s, s+M)
    rw [dif_pos (show s ≤ k ∧ k < s + (M + 1) from by omega), dif_pos hwin]
    have hcast : (⟨k - s, by omega⟩ : Fin (M + 1)) =
        Fin.castSucc (⟨k - s, by omega⟩ : Fin M) := by
      ext; simp [Fin.castSucc]
    rw [hcast, Fin.snoc_castSucc]
  · by_cases hbdy : k = s + M
    · -- k is at position s+M (the site being peeled off)
      rw [dif_pos (show s ≤ k ∧ k < s + (M + 1) from by omega), dif_neg hwin]
      have hlast : (⟨k - s, by omega⟩ : Fin (M + 1)) = Fin.last M := by
        ext; simp [Fin.last]; omega
      rw [hlast, Fin.snoc_last]
      simp [Function.update, hbdy]
    · -- k is outside both windows
      rw [dif_neg (show ¬(s ≤ k ∧ k < s + (M + 1)) from by omega), dif_neg hwin]
      simp [Function.update, show ¬(k = s + M) from hbdy]

/-- Restricting the first site of a contiguous `(M+1)`-block peels off
the leftmost site and shifts the window start. -/
theorem contiguousRestrictₗ_restrictFirst {N : ℕ} (s M : ℕ) (hsM1 : s + (M + 1) ≤ N)
    (τ : Fin N → Fin d) (ψ : NSiteSpace d N) (i : Fin d) :
    restrictFirst (contiguousRestrictₗ s (M + 1) hsM1 τ ψ) i =
    contiguousRestrictₗ (s + 1) M (by omega) (Function.update τ ⟨s, by omega⟩ i) ψ := by
  ext σ
  simp only [restrictFirst_apply, contiguousRestrictₗ_apply]
  congr 1; ext ⟨k, hk⟩
  simp only [contiguousCfg]
  by_cases hwin : s + 1 ≤ k ∧ k < s + 1 + M
  · -- k is in the shifted window [s+1, s+1+M)
    rw [dif_pos (show s ≤ k ∧ k < s + (M + 1) from by omega), dif_pos hwin]
    have hsucc : (⟨k - s, by omega⟩ : Fin (M + 1)) =
        Fin.succ (⟨k - (s + 1), by omega⟩ : Fin M) := by
      ext; simp; omega
    rw [hsucc, Fin.cons_succ]
  · by_cases hbdy : k = s
    · -- k is at position s (the site being peeled off)
      rw [dif_pos (show s ≤ k ∧ k < s + (M + 1) from by omega), dif_neg hwin]
      have hzero : (⟨k - s, by omega⟩ : Fin (M + 1)) = 0 := by
        ext; simp; omega
      rw [hzero, Fin.cons_zero]
      simp [Function.update, hbdy]
    · -- k is outside both windows
      rw [dif_neg (show ¬(s ≤ k ∧ k < s + (M + 1)) from by omega), dif_neg hwin]
      simp [Function.update, show ¬(k = s) from hbdy]

/-! ### Iterated intersection: non-wrapping windows → open-chain membership -/

/-- If an N-site state `ψ` satisfies the L-site ground condition at all
non-wrapping contiguous positions `s` (meaning `s + L ≤ N`), then
`ψ ∈ groundSpace A N` (the open-chain ground space).

The proof works by induction on `k` from 0 to `N - L`: at each step, two
adjacent windows of size `L + k` at positions `s` and `s + 1` are combined
via the intersection property to form a window of size `L + k + 1`.

**Hypotheses:** `L ≥ 2` (from the intersection property) and `L ≤ N`. -/
theorem contiguous_mem_groundSpace {A : MPSTensor d D} (hA : IsInjective A)
    {L N : ℕ} (hL : 1 < L) (hLN : L ≤ N) [NeZero d]
    {ψ : NSiteSpace d N}
    (hwindow : ∀ (s : ℕ) (hs : s + L ≤ N)
      (τ : Fin N → Fin d),
        contiguousRestrictₗ s L hs τ ψ ∈ groundSpace A L) :
    ψ ∈ groundSpace A N := by
  -- Prove the stronger claim parametrized by M: for L ≤ M ≤ N, every
  -- contiguous restriction of size M lies in groundSpace A M.
  suffices claim : ∀ (M : ℕ) (hLM : L ≤ M) (hMN : M ≤ N)
      (s : ℕ) (hs : s + M ≤ N) (τ : Fin N → Fin d),
        contiguousRestrictₗ s M hs τ ψ ∈ groundSpace A M by
    -- Apply at M = N, s = 0 to get ψ ∈ G_N
    have h0 := claim N hLN le_rfl 0 (by omega) (fun _ => ⟨0, Fin.pos'⟩)
    rwa [show (contiguousRestrictₗ 0 N (by omega) (fun _ => ⟨0, Fin.pos'⟩) ψ) = ψ from by
      ext σ; simp [contiguousRestrictₗ_apply, contiguousCfg_zero_full]] at h0
  -- By strong induction on M
  intro M
  induction M with
  | zero => intro hLM; omega
  | succ M ih =>
    intro hLM hMN s hs τ
    by_cases hbase : M + 1 ≤ L
    · -- M + 1 = L (base case)
      have : M + 1 = L := by omega
      subst this
      exact hwindow s hs τ
    · -- M ≥ L, so intersection property applies
      push_neg at hbase
      apply groundSpace_intersection hA (show 1 < M from by omega)
      · -- InLeftGround: restrict the last site
        intro j
        rw [contiguousRestrictₗ_restrictLast]
        exact ih (by omega) (by omega) s (by omega) _
      · -- InRightGround: restrict the first site
        intro i
        rw [contiguousRestrictₗ_restrictFirst]
        exact ih (by omega) (by omega) (s + 1) (by omega) _

/-! ### Cyclic window extraction -/

/-- Assemble an N-site configuration from a cyclic window at position `i`
(covering sites `i, i+1, ..., i+L-1 mod N`) and outside values `τ`.
Site `k` gets the window value `σ(offset)` where `offset = (k - i + N) % N`
if `offset < L`, otherwise it gets `τ(k)`. -/
def cyclicCfg {N : ℕ} (_hN : 0 < N) (L : ℕ)
    (i : Fin N) (σ : Fin L → Fin d) (τ : Fin N → Fin d) : Fin N → Fin d :=
  fun k =>
    if h : (k.val + N - i.val) % N < L
    then σ ⟨(k.val + N - i.val) % N, h⟩
    else τ k

/-- Linear restriction to a cyclic window at position `i`. -/
def cyclicRestrictₗ {N : ℕ} (hN : 0 < N) (L : ℕ)
    (i : Fin N) (τ : Fin N → Fin d) : NSiteSpace d N →ₗ[ℂ] NSiteSpace d L where
  toFun ψ σ := ψ (cyclicCfg hN L i σ τ)
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

@[simp]
theorem cyclicRestrictₗ_apply {N : ℕ} (hN : 0 < N) (L : ℕ)
    (i : Fin N) (τ : Fin N → Fin d) (ψ : NSiteSpace d N) (σ : Fin L → Fin d) :
    cyclicRestrictₗ hN L i τ ψ σ = ψ (cyclicCfg hN L i σ τ) := rfl

/-- For a non-wrapping window (`i + L ≤ N`), the cyclic config agrees with
the contiguous config. -/
theorem cyclicCfg_eq_contiguousCfg {N : ℕ} (hN : 0 < N) {L : ℕ} (hLN : L ≤ N)
    {i : Fin N} (hi : i.val + L ≤ N)
    (σ : Fin L → Fin d) (τ : Fin N → Fin d) :
    cyclicCfg hN L i σ τ = contiguousCfg i.val L σ τ := by
  ext ⟨k, hk⟩
  simp only [cyclicCfg, contiguousCfg]
  -- Compute the offset
  by_cases h : i.val ≤ k ∧ k < i.val + L
  · -- k is in the non-wrapping window
    have hoff : (k + N - i.val) % N = k - i.val := by
      have : k + N - i.val = k - i.val + N := by omega
      rw [this, Nat.add_mod_right]
      exact Nat.mod_eq_of_lt (by omega)
    have hlt : (k + N - i.val) % N < L := by omega
    rw [dif_pos hlt, dif_pos h]
    congr 1; ext; simp [hoff]
  · -- k is outside
    have hh : ¬(i.val ≤ k ∧ k < i.val + L) := h
    have hoff_ge : ¬((k + N - i.val) % N < L) := by
      intro habs
      apply hh
      constructor
      · by_contra hlt
        push_neg at hlt
        -- k < i, so (k + N - i) % N = k + N - i ≥ N - i ≥ L
        have : k + N - i.val < N := by omega
        rw [Nat.mod_eq_of_lt this] at habs
        omega
      · by_contra hge
        push_neg at hge
        -- i ≤ k (since ¬(k < i) would be handled above)
        -- and k ≥ i + L
        have hile : i.val ≤ k := by
          by_contra hlt
          push_neg at hlt
          have : k + N - i.val < N := by omega
          rw [Nat.mod_eq_of_lt this] at habs
          omega
        have : (k + N - i.val) % N = k - i.val := by
          have : k + N - i.val = k - i.val + N := by omega
          rw [this, Nat.add_mod_right]
          exact Nat.mod_eq_of_lt (by omega)
        omega
    rw [dif_neg hoff_ge, dif_neg hh]

/-- The non-wrapping window condition from the cyclic definition implies
the contiguous window condition. -/
theorem cyclicRestrictₗ_eq_contiguousRestrictₗ {N : ℕ} (hN : 0 < N)
    {L : ℕ} (hLN : L ≤ N) {i : Fin N} (hi : i.val + L ≤ N)
    (τ : Fin N → Fin d) (ψ : NSiteSpace d N) :
    cyclicRestrictₗ hN L i τ ψ = contiguousRestrictₗ i.val L (by omega) τ ψ := by
  ext σ
  simp [cyclicCfg_eq_contiguousCfg hN hLN hi]

/-! ### One-step rotation -/

/-- Rotate an `N`-site configuration one step to the left:
`(σ₀, σ₁, ..., σ_{N-1}) ↦ (σ₁, ..., σ_{N-1}, σ₀)`. -/
def rotateLeftCfg {N : ℕ} (hN : 0 < N) (σ : Fin N → Fin d) : Fin N → Fin d :=
  fun k => σ ⟨(k.val + 1) % N, Nat.mod_lt _ hN⟩

/-- Rotate an `N`-site state one step to the left by precomposing with
`rotateLeftCfg`. -/
def rotateLeftState {N : ℕ} (hN : 0 < N) : NSiteSpace d N →ₗ[ℂ] NSiteSpace d N where
  toFun ψ := fun σ => ψ (rotateLeftCfg hN σ)
  map_add' _ _ := by ext; simp [rotateLeftCfg]
  map_smul' _ _ := by ext; simp [rotateLeftCfg]

@[simp] theorem rotateLeftState_apply {N : ℕ} (hN : 0 < N)
    (ψ : NSiteSpace d N) (σ : Fin N → Fin d) :
    rotateLeftState hN ψ σ = ψ (rotateLeftCfg hN σ) := rfl

/-- Rotating a `Fin.cons` configuration left gives the corresponding `Fin.snoc`. -/
theorem rotateLeftCfg_cons {N : ℕ} (i : Fin d) (σ : Fin N → Fin d) :
    rotateLeftCfg (N := N + 1) (Nat.succ_pos _) (Fin.cons i σ) = Fin.snoc σ i := by
  ext k
  rcases Fin.eq_last_or_eq_castSucc k with rfl | ⟨k, rfl⟩
  · simp [rotateLeftCfg]
  · simp [rotateLeftCfg]

/-- Contiguous windows of the left-rotated state are exactly the cyclic windows
of the original state, with shifted start index. -/
theorem contiguousRestrictₗ_rotateLeftState_eq_cyclicRestrictₗ {N : ℕ} (hN : 0 < N)
    {L : ℕ} (hL : 0 < L) (s : ℕ) (hs : s + L ≤ N)
    (τ : Fin N → Fin d) (ψ : NSiteSpace d N) :
    contiguousRestrictₗ s L hs τ (rotateLeftState hN ψ) =
      cyclicRestrictₗ hN L ⟨s + 1, by omega⟩ (rotateLeftCfg hN τ) ψ := by
  ext σ
  simp only [contiguousRestrictₗ_apply, cyclicRestrictₗ_apply, rotateLeftState_apply]
  congr 1
  ext ⟨k, hk⟩
  simp only [rotateLeftCfg, contiguousCfg, cyclicCfg]
  by_cases hwrap : k + 1 = N
  · have hk_last : k = N - 1 := by omega
    subst hk_last
    have hs_ne : s + L ≠ N + 1 := by omega
    by_cases hwin : s ≤ N - 1 ∧ N - 1 < s + L
    · have hs_eq : s + L = N := by omega
      have hoff : (N - 1 + N - (s + 1)) % N = L - 1 := by
        rw [show N - 1 + N - (s + 1) = N + (L - 1) from by omega, Nat.add_mod_right]
        exact Nat.mod_eq_of_lt (by omega)
      rw [dif_pos hwin, dif_pos (show (N - 1 + N - (s + 1)) % N < L by
        rw [hoff]; omega)]
      congr 1
      ext
      simp [hoff]
    · have hnot : ¬((N - 1 + N - (s + 1)) % N < L) := by
        rw [show N - 1 + N - (s + 1) = 2 * N - s - 2 by omega]
        have hs_lt : s + L < N := by
          omega
        have hoff' : (2 * N - s - 2) % N = N - s - 2 := by
          have hlt : N - s - 2 < N := by omega
          exact Nat.mod_eq_of_lt hlt
        rw [hoff']
        omega
      rw [dif_neg hwin, dif_neg hnot]
      simp [rotateLeftCfg, hwrap]
  · have hk_lt : k + 1 < N := by omega
    have hmod : (k + 1) % N = k + 1 := Nat.mod_eq_of_lt hk_lt
    by_cases hwin : s ≤ k + 1 ∧ k + 1 < s + L
    · have hoff : (k + N - (s + 1)) % N = k + 1 - (s + 1) := by
        have hlt : k + N - (s + 1) < N := by
          omega
        rw [Nat.mod_eq_of_lt hlt]
        omega
      rw [dif_pos (by simpa [hmod] using hwin), dif_pos (by
        rw [hoff]
        omega)]
      congr 1
      ext
      simp [hmod, hoff]
    · have hnot : ¬((k + N - (s + 1)) % N < L) := by
        intro hkL
        apply hwin
        constructor
        · by_contra hs'
          have hlt : k + N - (s + 1) < N := by omega
          rw [Nat.mod_eq_of_lt hlt] at hkL
          omega
        · have hle : s + 1 ≤ k + 1 := by omega
          have hoff : (k + N - (s + 1)) % N = k + 1 - (s + 1) := by
            have hlt : k + N - (s + 1) < N := by omega
            rw [Nat.mod_eq_of_lt hlt]
            omega
          rw [hoff] at hkL
          omega
      rw [dif_neg hwin, dif_neg hnot]
      simp [rotateLeftCfg, hmod]

end MPSTensor
