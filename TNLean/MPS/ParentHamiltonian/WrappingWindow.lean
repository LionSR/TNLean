/-
Copyright (c) 2025 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.ParentHamiltonian.Basic
import TNLean.MPS.ParentHamiltonian.BlockStrip
import TNLean.MPS.ParentHamiltonian.CyclicWindow
import TNLean.MPS.FundamentalTheorem.FiniteLength

/-!
# Wrapping window argument for periodic MPS chains

This file proves that the boundary matrix `X` arising from the open-chain
intersection property must commute with all generators `A_j` of an injective
MPS tensor on a periodic chain.

## Proof strategy

On a periodic chain of `N` sites with window size `L`, the last cyclic window
wraps around from position `N-1` back to the first `L-1` sites. The proof
proceeds as follows:

1. **Cyclic config decomposition** (`cyclicCfg_last_eq`, `cyclicCfg_window_site`,
   `cyclicCfg_complement_site`): At the wrapping position `N-1`, the cyclic
   configuration decomposes into window sites `σ_w(0), σ_w(1), …, σ_w(L-1)`
   (wrapping around) and complement sites from `τ`.

2. **Snoc factorization** (`evalWord_cyclicCfg_snoc`, `init_evalWord_split`):
   The product `evalWord A (cyclicCfg ...)` factors as
   `evalWord(tail) * evalWord(complement) * A(σ_w(0))`, enabling trace rotation.

3. **Trace rotation** (`wrapping_window_matEq`): Using `tr(P * Q) = tr(Q * P)`,
   we rotate the wrapping boundary to obtain a matrix equation
   `X * evalWord(σ_tail) * evalWord(complement) = evalWord(σ_tail) * Y_τ`
   for all window tails `σ_tail` and background configs `τ`.

4. **Spanning extension** (`boundary_matrix_commutes`): Since
   `wordSpan A (L-1) = ⊤` for injective `A`, the equation extends from
   `evalWord(σ_tail)` to all matrices `M₁`, yielding `[X, M₁] * complement = 0`.
   A second spanning argument (over complement words) gives `X * M₁ = M₁ * X`
   for all `M₁`, hence `X * A_j = A_j * X`.

## Main results

* `MPSTensor.boundary_matrix_commutes_of_isNBlkInjective_of_long_word_commutes`
  — block injectivity turns long-word commutation into generator commutation
* `MPSTensor.boundary_matrix_commutes` — if `groundSpaceMap A N X` lies in
  every cyclic window's ground space, then `X` commutes with all `A_j`.

## References

* [CPGSV21] arXiv:2011.12127, lines 2013–2094
* [FNW92] Sections 3–4
-/

open scoped Matrix BigOperators

namespace MPSTensor

variable {d D : ℕ}

/-! ### Cyclic config decomposition at the wrapping position

These lemmas analyze the structure of `cyclicCfg` at position `N-1`,
where the window wraps from the last site back to the first sites. -/

/-- At the wrapping position `N-1`, the cyclic config's last site is `σ_w 0`. -/
private theorem cyclicCfg_last_eq {N L : ℕ} (hN : 2 ≤ N) (hLN : L ≤ N) (hL : 1 < L)
    (σ_w : Fin L → Fin d) (τ : Fin N → Fin d) :
    cyclicCfg (by omega : 0 < N) L ⟨N - 1, by omega⟩ σ_w τ ⟨N - 1, by omega⟩ =
      σ_w ⟨0, by omega⟩ := by
  simp only [cyclicCfg]
  have hval : (N - 1 : ℕ) + N - (N - 1 : ℕ) = N := by omega
  have hoffset : ((N - 1) + N - (N - 1)) % N = 0 := by
    rw [hval]; exact Nat.mod_self N
  rw [dif_pos (show ((N - 1) + N - (N - 1)) % N < L by rw [hoffset]; omega)]
  congr 1; ext; simp

/-- At the wrapping position `N-1`, sites `0..L-2` get `σ_w(1)..σ_w(L-1)`. -/
private theorem cyclicCfg_window_site {N L : ℕ} (hN : 2 ≤ N) (_hLN : L ≤ N) (hL : 1 < L)
    (σ_w : Fin L → Fin d) (τ : Fin N → Fin d)
    {k : ℕ} (hk : k < L - 1) :
    cyclicCfg (by omega : 0 < N) L ⟨N - 1, by omega⟩ σ_w τ ⟨k, by omega⟩ =
      σ_w ⟨k + 1, by omega⟩ := by
  simp only [cyclicCfg]
  have hoffset : (k + N - (N - 1)) % N = k + 1 := by
    have : k + N - (N - 1) = k + 1 := by omega
    rw [this, Nat.mod_eq_of_lt (by omega)]
  rw [dif_pos (show (k + N - (N - 1)) % N < L by rw [hoffset]; omega)]
  congr 1; ext; simp [hoffset]

/-- At the wrapping position `N-1`, complement sites get τ values. -/
private theorem cyclicCfg_complement_site {N L : ℕ} (hN : 2 ≤ N) (_hLN : L ≤ N) (hL : 1 < L)
    (σ_w : Fin L → Fin d) (τ : Fin N → Fin d)
    {k : ℕ} (hk1 : L - 1 ≤ k) (hk2 : k < N - 1) :
    cyclicCfg (by omega : 0 < N) L ⟨N - 1, by omega⟩ σ_w τ ⟨k, by omega⟩ =
      τ ⟨k, by omega⟩ := by
  simp only [cyclicCfg]
  have hoffset : (k + N - (N - 1)) % N = k + 1 := by
    have : k + N - (N - 1) = k + 1 := by omega
    rw [this, Nat.mod_eq_of_lt (by omega)]
  rw [dif_neg (show ¬((k + N - (N - 1)) % N < L) by rw [hoffset]; omega)]

/-! ### Snoc factorization

Factor the full cyclic config product as `evalWord(init) * A(σ_w(0))`,
then split `init` into window-tail and complement parts. -/

/-- The evalWord of the cyclic config at position `M` (= `N-1`) on `M+1` sites
decomposes as `evalWord(init) * A(σ_w(0))` where `init` covers sites `0..M-1`. -/
private theorem evalWord_cyclicCfg_snoc {A : MPSTensor d D}
    {M L : ℕ} (hM : 1 ≤ M) (hLN : L ≤ M + 1) (hL : 1 < L)
    (σ_w : Fin L → Fin d) (τ : Fin (M + 1) → Fin d) :
    evalWord A (List.ofFn (cyclicCfg (by omega : 0 < M + 1) L ⟨M, by omega⟩ σ_w τ)) =
    evalWord A (List.ofFn (fun k : Fin M =>
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
private theorem init_evalWord_split {A : MPSTensor d D}
    {M L : ℕ} (hM : 1 ≤ M) (hLN : L ≤ M + 1) (hL : 1 < L)
    (σ_w : Fin L → Fin d) (τ : Fin (M + 1) → Fin d) :
    evalWord A (List.ofFn (fun k : Fin M =>
      cyclicCfg (by omega : 0 < M + 1) L ⟨M, by omega⟩ σ_w τ (Fin.castSucc k))) =
    evalWord A (List.ofFn (fun k : Fin (L - 1) => σ_w ⟨k.val + 1, by omega⟩)) *
    evalWord A (List.ofFn (fun k : Fin (M + 1 - L) =>
      τ ⟨k.val + L - 1, by omega⟩)) := by
  rw [← evalWord_append]
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
      -- hcomp is about cyclicCfg ... ⟨k, _⟩, we need it about Fin.castSucc ⟨k, _⟩
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
      rw [dif_neg (by rw [hoffset]; omega)]
      congr 1; ext; simp; omega

/-! ### Mirror factorization at the opposite wrapped position

At the wrapped position `N - L + 1`, the cyclic word starts with the last window
site, then runs through the complement, then finishes with the remaining
`L - 1` window sites.  This yields the factorization needed for the mirror
block-injective extraction. -/

/-- At the opposite wrapped position `N - L + 1`, site `0` carries the final
window entry `σ_w(L-1)`. -/
private theorem cyclicCfg_mirror_zero_eq {N L : ℕ} (hN : 2 ≤ N) (hLN : L ≤ N) (hL : 1 < L)
    (σ_w : Fin L → Fin d) (τ : Fin N → Fin d) :
    cyclicCfg (by omega : 0 < N) L ⟨N - L + 1, by omega⟩ σ_w τ ⟨0, by omega⟩ =
      σ_w ⟨L - 1, by omega⟩ := by
  simp only [cyclicCfg]
  have hoffset : (0 + N - (N - L + 1)) % N = L - 1 := by
    have : 0 + N - (N - L + 1) = L - 1 := by omega
    rw [this, Nat.mod_eq_of_lt (by omega)]
  have hoffset_lt : (0 + N - (N - L + 1)) % N < L := by
    rw [hoffset]
    omega
  rw [dif_pos hoffset_lt]
  apply congrArg σ_w
  ext
  exact hoffset

/-- At the opposite wrapped position `N - L + 1`, the complement sites
`1, ..., N - L` keep their `τ` values. -/
private theorem cyclicCfg_mirror_complement_site {N L : ℕ}
    (hN : 2 ≤ N) (_hLN : L ≤ N) (hL : 1 < L)
    (σ_w : Fin L → Fin d) (τ : Fin N → Fin d)
    {k : ℕ} (hk1 : 1 ≤ k) (hk2 : k < N - L + 1) :
    cyclicCfg (by omega : 0 < N) L ⟨N - L + 1, by omega⟩ σ_w τ ⟨k, by omega⟩ =
      τ ⟨k, by omega⟩ := by
  simp only [cyclicCfg]
  have hoffset : (k + N - (N - L + 1)) % N = k + L - 1 := by
    have : k + N - (N - L + 1) = k + L - 1 := by omega
    rw [this, Nat.mod_eq_of_lt (by omega)]
  rw [dif_neg (show ¬((k + N - (N - L + 1)) % N < L) by rw [hoffset]; omega)]

/-- At the opposite wrapped position `N - L + 1`, the final `L - 1` physical
sites carry the first `L - 1` entries of the window. -/
private theorem cyclicCfg_mirror_window_site {N L : ℕ}
    (hN : 2 ≤ N) (_hLN : L ≤ N) (hL : 1 < L)
    (σ_w : Fin L → Fin d) (τ : Fin N → Fin d)
    {k : ℕ} (hk : k < L - 1) :
    cyclicCfg (by omega : 0 < N) L ⟨N - L + 1, by omega⟩ σ_w τ
        ⟨N - L + 1 + k, by omega⟩ =
      σ_w ⟨k, by omega⟩ := by
  simp only [cyclicCfg]
  have hoffset : (N - L + 1 + k + N - (N - L + 1)) % N = k := by
    have : N - L + 1 + k + N - (N - L + 1) = N + k := by omega
    rw [this, Nat.add_mod_left]
    exact Nat.mod_eq_of_lt (by omega)
  rw [dif_pos (show (N - L + 1 + k + N - (N - L + 1)) % N < L by rw [hoffset]; omega)]
  congr 1; ext; simp [hoffset]

/-- At the opposite wrapped position `N - L + 1`, the cyclic word factors as
the final window letter, then the complement word, then the remaining
`L - 1`-site window head. -/
private theorem evalWord_cyclicCfg_cons {A : MPSTensor d D}
    {M L : ℕ} (hM : 1 ≤ M) (hLN : L ≤ M + 1) (hL : 1 < L)
    (σ_w : Fin L → Fin d) (τ : Fin (M + 1) → Fin d) :
    evalWord A (List.ofFn (cyclicCfg (by omega : 0 < M + 1) L
      ⟨M + 1 - L + 1, by omega⟩ σ_w τ)) =
    A (σ_w ⟨L - 1, by omega⟩) *
      evalWord A (List.ofFn (fun k : Fin (M + 1 - L) => τ ⟨k.val + 1, by omega⟩)) *
      evalWord A (List.ofFn (fun k : Fin (L - 1) =>
        σ_w ⟨k.val, Nat.lt_trans k.isLt (by omega)⟩)) := by
  let cfg : Fin (M + 1) → Fin d :=
    cyclicCfg (by omega : 0 < M + 1) L ⟨M + 1 - L + 1, by omega⟩ σ_w τ
  let comp : Fin (M + 1 - L) → Fin d := fun k => τ ⟨k.val + 1, by omega⟩
  let head : Fin (L - 1) → Fin d := fun k => σ_w ⟨k.val, Nat.lt_trans k.isLt (by omega)⟩
  let tail : Fin M → Fin d := fun k =>
    if h : k.val < M + 1 - L
    then comp ⟨k.val, h⟩
    else head ⟨k.val - (M + 1 - L), by omega⟩
  have hcons : cfg = Fin.cons (σ_w ⟨L - 1, by omega⟩) tail := by
    funext x
    refine Fin.cases ?_ ?_ x
    · simpa [cfg] using cyclicCfg_mirror_zero_eq (by omega : 2 ≤ M + 1) hLN hL σ_w τ
    · intro k
      rw [Fin.cons_succ]
      by_cases hkC : k.val < M + 1 - L
      · have hcomp := cyclicCfg_mirror_complement_site (by omega : 2 ≤ M + 1) hLN hL σ_w τ
          (show 1 ≤ k.val + 1 from by omega) (show k.val + 1 < M + 1 - L + 1 from by omega)
        have hsucc : (Fin.succ k : Fin (M + 1)) = ⟨k.val + 1, by omega⟩ := by
          ext
          simp [Fin.succ]
        simpa [cfg, tail, comp, hkC, hsucc] using hcomp
      · have hwin := cyclicCfg_mirror_window_site (by omega : 2 ≤ M + 1) hLN hL σ_w τ
          (k := k.val - (M + 1 - L)) (show k.val - (M + 1 - L) < L - 1 from by omega)
        have hsucc : (Fin.succ k : Fin (M + 1)) =
            ⟨M + 1 - L + 1 + (k.val - (M + 1 - L)), by omega⟩ := by
          ext
          simp [Fin.succ]
          omega
        simpa [cfg, tail, head, comp, hkC, hsucc] using hwin
  have htail : List.ofFn tail = List.ofFn comp ++ List.ofFn head := by
    apply List.ext_getElem
    · simp only [List.length_ofFn, List.length_append]
      omega
    · intro k hk1 hk2
      simp only [List.length_ofFn] at hk1
      simp only [List.getElem_ofFn]
      by_cases hkC : k < M + 1 - L
      · rw [List.getElem_append_left (by simpa using hkC)]
        rw [List.getElem_ofFn]
        simp [tail, comp, head, hkC]
      · rw [List.getElem_append_right (by simpa [List.length_ofFn] using hkC)]
        rw [List.getElem_ofFn]
        simp only [List.length_ofFn]
        simp [tail, comp, head, hkC]
  rw [show List.ofFn cfg = List.ofFn (Fin.cons (σ_w ⟨L - 1, by omega⟩) tail) by rw [hcons]]
  rw [evalWord_ofFn_cons, htail, evalWord_append]
  simp [comp, head, Matrix.mul_assoc]

/-! ### Trace rotation and matrix equation extraction

Use `tr(P * Q) = tr(Q * P)` to rotate the wrapping boundary,
then extract a matrix equation via `groundSpaceMap_injective`. -/

set_option maxHeartbeats 800000 in
-- Expanding `cyclicCfg` and rotating the trace through the wrapping window produces
-- large normalization goals, so this proof needs a larger heartbeat budget.
private theorem wrapping_window_matEq {A : MPSTensor d D} [NeZero D]
    (hA : IsInjective A) {L : ℕ} (hL : 1 < L) {M : ℕ} (hM : 1 ≤ M) (hLN : L ≤ M + 1)
    {X : Matrix (Fin D) (Fin D) ℂ}
    (Y : (Fin (M + 1) → Fin d) → Matrix (Fin D) (Fin D) ℂ)
    (hY : ∀ τ σ_w, Matrix.trace (evalWord A (List.ofFn
          (cyclicCfg (by omega : 0 < M + 1) L ⟨M, by omega⟩ σ_w τ)) * X) =
        Matrix.trace (evalWord A (List.ofFn σ_w) * Y τ)) :
    ∀ (σ_tail : Fin (L - 1) → Fin d) (τ : Fin (M + 1) → Fin d),
      X * evalWord A (List.ofFn σ_tail) *
        evalWord A (List.ofFn (fun k : Fin (M + 1 - L) =>
          τ ⟨k.val + L - 1, by omega⟩)) =
      evalWord A (List.ofFn σ_tail) * Y τ := by
  -- Trace rotation FIRST (before mkσ to avoid whnf blowup)
  have hTraceRot : ∀ (σ_w : Fin L → Fin d) (τ : Fin (M + 1) → Fin d),
      Matrix.trace (A (σ_w ⟨0, by omega⟩) * X *
        evalWord A (List.ofFn (fun k : Fin M =>
          cyclicCfg (by omega : 0 < M + 1) L ⟨M, by omega⟩ σ_w τ (Fin.castSucc k)))) =
      Matrix.trace (evalWord A (List.ofFn σ_w) * Y τ) := by
    intro σ_w τ
    set P := evalWord A (List.ofFn (fun k : Fin M =>
      cyclicCfg (by omega : 0 < M + 1) L ⟨M, by omega⟩ σ_w τ (Fin.castSucc k)))
    set Aj := A (σ_w ⟨0, by omega⟩)
    calc Matrix.trace (Aj * X * P)
        = Matrix.trace (P * (Aj * X)) := Matrix.trace_mul_comm (Aj * X) P
      _ = Matrix.trace (P * Aj * X) := by rw [← Matrix.mul_assoc]
      _ = Matrix.trace (evalWord A (List.ofFn
            (cyclicCfg (by omega : 0 < M + 1) L ⟨M, by omega⟩ σ_w τ)) * X) := by
          rw [← evalWord_cyclicCfg_snoc hM (by omega) hL σ_w τ]
      _ = Matrix.trace (evalWord A (List.ofFn σ_w) * Y τ) := hY τ σ_w
  -- Build σ_w from j and σ_tail
  let mkσ (j : Fin d) (σ_tail : Fin (L - 1) → Fin d) : Fin L → Fin d :=
    fun k => if h : k.val = 0 then j else σ_tail ⟨k.val - 1, by omega⟩
  -- Properties of mkσ
  have mkσ_zero : ∀ j σ_tail, mkσ j σ_tail ⟨0, by omega⟩ = j := by
    intro j σ_tail; simp [mkσ]
  have mkσ_tail_eq : ∀ j σ_tail,
      (fun k : Fin (L - 1) => (mkσ j σ_tail) ⟨k.val + 1, by omega⟩) = σ_tail := by
    intro j σ_tail; ext ⟨k, hk⟩
    simp [mkσ]
  have mkσ_evalWord : ∀ j σ_tail,
      evalWord A (List.ofFn (mkσ j σ_tail)) =
      A j * evalWord A (List.ofFn σ_tail) := by
    intro j σ_tail
    have hlist : List.ofFn (mkσ j σ_tail) = [j] ++ List.ofFn σ_tail := by
      apply List.ext_getElem
      · simp [List.length_ofFn]; omega
      · intro k hk1 hk2
        simp only [List.length_ofFn] at hk1
        simp only [List.getElem_ofFn]
        by_cases hk0 : k = 0
        · subst hk0; simp [mkσ]
        · rw [List.getElem_append_right (by simp; omega)]
          simp only [List.length_cons, List.length_nil]
          rw [List.getElem_ofFn]
          simp [mkσ, show k ≠ 0 from hk0]
    rw [hlist, evalWord_append]; simp [evalWord_cons, evalWord_nil]
  -- Matrix equation via groundSpaceMap_injective on 1 site
  intro σ_tail τ
  apply groundSpaceMap_injective hA (show 0 < 1 from by omega)
  ext σ₁
  simp only [groundSpaceMap_apply]
  rw [show List.ofFn σ₁ = [σ₁ 0] from by
    apply List.ext_getElem <;> simp]
  simp only [evalWord_cons, evalWord_nil, mul_one]
  have key := hTraceRot (mkσ (σ₁ 0) σ_tail) τ
  rw [mkσ_zero] at key
  rw [init_evalWord_split hM (by omega) hL (mkσ (σ₁ 0) σ_tail) τ] at key
  rw [mkσ_tail_eq] at key
  rw [mkσ_evalWord] at key
  rw [Matrix.mul_assoc (A (σ₁ 0)) X, ← Matrix.mul_assoc X,
      Matrix.mul_assoc (A (σ₁ 0))] at key
  exact key

/-- Block injectivity strips the wrapped tail block and yields the one-sided
compatibility `C_τ * A j * X = Y_τ * A j`.  This is the valid local
replacement identified by the #730 audit; issue #761 asks for the missing mirror
comparison on top of this step. -/
theorem wrapping_window_compatibility_of_isNBlkInjective
    {A : MPSTensor d D} [NeZero D] {L₀ M : ℕ}
    (hInj : IsNBlkInjective A L₀) (hL₀ : 0 < L₀) (hM : L₀ ≤ M)
    {X : Matrix (Fin D) (Fin D) ℂ}
    (Y : (Fin (M + 1) → Fin d) → Matrix (Fin D) (Fin D) ℂ)
    (hY : ∀ τ σ_w, Matrix.trace (evalWord A (List.ofFn
          (cyclicCfg (by omega : 0 < M + 1) (L₀ + 1) ⟨M, by omega⟩ σ_w τ)) * X) =
        Matrix.trace (evalWord A (List.ofFn σ_w) * Y τ)) :
    ∀ (j : Fin d) (τ : Fin (M + 1) → Fin d),
      evalWord A (List.ofFn (fun k : Fin (M + 1 - (L₀ + 1)) =>
        τ ⟨k.val + L₀, by omega⟩)) * A j * X =
      Y τ * A j := by
  have hM1 : 1 ≤ M := by omega
  have hL : 1 < L₀ + 1 := by omega
  intro j τ
  apply groundSpaceMap_injective_of_isNBlkInjective hInj
  ext σ_tail
  have key := hY τ (Fin.cons j σ_tail)
  rw [evalWord_cyclicCfg_snoc hM1 (by omega) hL (Fin.cons j σ_tail) τ] at key
  rw [init_evalWord_split hM1 (by omega) hL (Fin.cons j σ_tail) τ] at key
  rw [evalWord_ofFn_cons] at key
  have key' :
      Matrix.trace
          (evalWord A (List.ofFn σ_tail) *
            (evalWord A (List.ofFn (fun k : Fin (M + 1 - (L₀ + 1)) =>
              τ ⟨k.val + L₀, by omega⟩)) *
              A j * X)) =
        Matrix.trace (A j * evalWord A (List.ofFn σ_tail) * Y τ) := by
    simpa [Matrix.mul_assoc] using key
  simp only [groundSpaceMap_apply] at *
  calc
    Matrix.trace
        (evalWord A (List.ofFn σ_tail) *
          (evalWord A (List.ofFn (fun k : Fin (M + 1 - (L₀ + 1)) =>
            τ ⟨k.val + L₀, by omega⟩)) *
            A j * X))
      = Matrix.trace (A j * evalWord A (List.ofFn σ_tail) * Y τ) := key'
    _ = Matrix.trace ((evalWord A (List.ofFn σ_tail) * Y τ) * A j) := by
          simpa [Matrix.mul_assoc] using
            (Matrix.trace_mul_comm (A j) (evalWord A (List.ofFn σ_tail) * Y τ))
    _ = Matrix.trace
        (evalWord A (List.ofFn σ_tail) * (Y τ * A j)) := by
          simp [Matrix.mul_assoc]

/-- The opposite wrapped position `N - L₀` exposes the mirror compatibility
`X * A j * C_τ = A j * Y_τ` after block-injective stripping of the trailing
`L₀`-site block.  This is the missing second wrapped-window extraction needed
for the block-injective periodic argument. -/
theorem wrapping_window_mirror_compatibility_of_isNBlkInjective
    {A : MPSTensor d D} [NeZero D] {L₀ M : ℕ}
    (hInj : IsNBlkInjective A L₀) (hL₀ : 0 < L₀) (hM : L₀ ≤ M)
    {X : Matrix (Fin D) (Fin D) ℂ}
    (Y : (Fin (M + 1) → Fin d) → Matrix (Fin D) (Fin D) ℂ)
    (hY : ∀ τ σ_w, Matrix.trace (evalWord A (List.ofFn
          (cyclicCfg (by omega : 0 < M + 1) (L₀ + 1) ⟨M + 1 - L₀, by omega⟩ σ_w τ)) * X) =
        Matrix.trace (evalWord A (List.ofFn σ_w) * Y τ)) :
    ∀ (j : Fin d) (τ : Fin (M + 1) → Fin d),
      X * A j * evalWord A (List.ofFn (fun k : Fin (M + 1 - (L₀ + 1)) =>
        τ ⟨k.val + 1, by omega⟩)) =
      A j * Y τ := by
  intro j τ
  apply groundSpaceMap_injective_of_isNBlkInjective hInj
  ext σ_head
  simp only [groundSpaceMap_apply]
  have key := hY τ (Fin.snoc σ_head j)
  have hfactor := evalWord_cyclicCfg_cons (A := A) (show 1 ≤ M by omega) (by omega) (by omega)
    (Fin.snoc σ_head j) τ
  have hfactor' :
      evalWord A (List.ofFn (cyclicCfg (by omega : 0 < M + 1) (L₀ + 1)
          ⟨M + 1 - L₀, by omega⟩ (Fin.snoc σ_head j) τ)) =
        A j *
          evalWord A (List.ofFn (fun k : Fin (M + 1 - (L₀ + 1)) =>
            τ ⟨k.val + 1, by omega⟩)) *
          evalWord A (List.ofFn σ_head) := by
    convert hfactor using 2
    · have hstart : (⟨M + 1 - L₀, by omega⟩ : Fin (M + 1)) =
          ⟨M - L₀ + 1, by omega⟩ := by
            ext
            simp
            omega
      simpa using congrArg List.ofFn
        (congrArg
          (fun s => cyclicCfg (by omega : 0 < M + 1) (L₀ + 1) s (Fin.snoc σ_head j) τ)
          hstart)
    · congr 1
      change A j = A ((@Fin.snoc L₀ (fun _ => Fin d) σ_head j) (Fin.last L₀))
      rw [Fin.snoc_last]
    · congr 1
      apply List.ext_getElem
      · simp [List.length_ofFn]
      · intro k hk1 hk2
        simp only [List.length_ofFn] at hk1
        simp only [List.getElem_ofFn]
        have hcast : (⟨k, Nat.lt_trans hk1 (Nat.lt_succ_self L₀)⟩ : Fin (L₀ + 1)) =
            Fin.castSucc ⟨k, hk1⟩ := by
              ext
              simp [Fin.castSucc]
        rw [hcast, Fin.snoc_castSucc]
  rw [hfactor'] at key
  rw [evalWord_ofFn_snoc] at key
  have key' :
      Matrix.trace
          ((A j *
              evalWord A (List.ofFn (fun k : Fin (M + 1 - (L₀ + 1)) =>
                τ ⟨k.val + 1, by omega⟩)) *
              evalWord A (List.ofFn σ_head)) * X) =
        Matrix.trace (evalWord A (List.ofFn σ_head) * (A j * Y τ)) := by
    simpa [Fin.init, Fin.init_snoc, Matrix.mul_assoc] using key
  calc
    Matrix.trace
        (evalWord A (List.ofFn σ_head) *
          (X * A j * evalWord A (List.ofFn (fun k : Fin (M + 1 - (L₀ + 1)) =>
            τ ⟨k.val + 1, by omega⟩))))
      = Matrix.trace
          ((A j *
              evalWord A (List.ofFn (fun k : Fin (M + 1 - (L₀ + 1)) =>
                τ ⟨k.val + 1, by omega⟩)) *
              evalWord A (List.ofFn σ_head)) * X) := by
            simpa [Matrix.mul_assoc] using
              (Matrix.trace_mul_cycle'
                (evalWord A (List.ofFn σ_head))
                X
                (A j * evalWord A (List.ofFn (fun k : Fin (M + 1 - (L₀ + 1)) =>
                  τ ⟨k.val + 1, by omega⟩))))
    _ = Matrix.trace (evalWord A (List.ofFn σ_head) * (A j * Y τ)) := by
          simpa [Matrix.mul_assoc] using key'

/-! ### Main commutation result

Extend from the wrapping window equation to full commutation via spanning. -/

/-- If a boundary matrix commutes with all words of some length `m ≥ L₀`, then
block injectivity forces it to commute with every generator. -/
theorem boundary_matrix_commutes_of_isNBlkInjective_of_long_word_commutes
    {A : MPSTensor d D} {L₀ m : ℕ} (hInj : IsNBlkInjective A L₀) (hL₀ : 0 < L₀)
    (hm : L₀ ≤ m) {X : Matrix (Fin D) (Fin D) ℂ}
    (hComm : ∀ ω : Fin m → Fin d,
      X * evalWord A (List.ofFn ω) = evalWord A (List.ofFn ω) * X) :
    ∀ j : Fin d, X * A j = A j * X := by
  intro j
  exact commutes_all_of_commutes_long_words_of_isNBlkInjective
    (A := A) hInj hL₀ hm hComm (A j)

set_option maxHeartbeats 800000 in
-- The double spanning argument over window tails and complements creates large
-- `LinearMap.ext_on_range` goals, so we raise the heartbeat budget here as well.
/-- If `groundSpaceMap A N X` lies in every cyclic window's ground space,
then `X` commutes with all generators `A_j`.

This is the key step in the periodic-chain uniqueness argument:
the wrapping window constraint forces the boundary matrix into the center
of the algebra generated by `{A_j}`. -/
theorem boundary_matrix_commutes {A : MPSTensor d D} [NeZero D]
    (hA : IsInjective A) {L N : ℕ} (hN : 2 ≤ N) (hL : 1 < L) (hLN : L ≤ N)
    {X : Matrix (Fin D) (Fin D) ℂ}
    (hψ : ∀ (i : Fin N) (τ : Fin N → Fin d),
      cyclicRestrictₗ (by omega : 0 < N) L i τ (groundSpaceMap A N X) ∈
        groundSpace A L) :
    ∀ j : Fin d, X * A j = A j * X := by
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  have hM : 1 ≤ M := by omega
  have hN0 : 0 < M + 1 := by omega
  -- Extract Y_τ from wrapping window ground space membership
  have hGS : ∀ τ : Fin (M + 1) → Fin d, ∃ Y : Matrix (Fin D) (Fin D) ℂ,
      ∀ σ_w : Fin L → Fin d,
        Matrix.trace (evalWord A (List.ofFn
          (cyclicCfg hN0 L ⟨M, by omega⟩ σ_w τ)) * X) =
        Matrix.trace (evalWord A (List.ofFn σ_w) * Y) := by
    intro τ
    have hmem := hψ ⟨M, by omega⟩ τ
    rw [groundSpace, LinearMap.mem_range] at hmem
    obtain ⟨Y, hY⟩ := hmem
    refine ⟨Y, fun σ_w => ?_⟩
    have : cyclicRestrictₗ hN0 L ⟨M, by omega⟩ τ (groundSpaceMap A (M + 1) X) σ_w =
        groundSpaceMap A L Y σ_w := by rw [← hY]
    simp only [cyclicRestrictₗ_apply, groundSpaceMap_apply] at this
    exact this
  choose Y hY using hGS
  -- Matrix equation from wrapping_window_matEq
  have hMatEq := wrapping_window_matEq hA hL hM (by omega) Y (fun τ σ_w => hY τ σ_w)
  -- Extend to all M₁ via spanning in σ_tail (wordSpan(L-1) = ⊤)
  have hMatEq2 : ∀ (M₁ : Matrix (Fin D) (Fin D) ℂ) (τ : Fin (M + 1) → Fin d),
      X * M₁ * evalWord A (List.ofFn (fun k : Fin (M + 1 - L) =>
        τ ⟨k.val + L - 1, by omega⟩)) = M₁ * Y τ := by
    intro M₁ τ
    have hfg : (LinearMap.mulLeft ℂ X).comp
        (LinearMap.mulRight ℂ (evalWord A (List.ofFn (fun k : Fin (M + 1 - L) =>
          τ ⟨k.val + L - 1, by omega⟩)))) =
        LinearMap.mulRight ℂ (Y τ) := by
      apply LinearMap.ext_on_range
        (v := fun σ : Fin (L - 1) → Fin d => evalWord A (List.ofFn σ))
      · simpa [wordSpan] using wordSpan_eq_top_of_isInjective hA (by omega : 0 < L - 1)
      · intro σ_tail
        simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply,
                    LinearMap.mulRight_apply]
        rw [← Matrix.mul_assoc]; exact hMatEq σ_tail τ
    have := congrArg (· M₁) hfg
    simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply,
               LinearMap.mulRight_apply] at this
    rw [← Matrix.mul_assoc] at this; exact this
  -- Y τ = X * compProd(τ) (take M₁ = 1)
  have hYeq : ∀ τ : Fin (M + 1) → Fin d,
      Y τ = X * evalWord A (List.ofFn (fun k : Fin (M + 1 - L) =>
        τ ⟨k.val + L - 1, by omega⟩)) := by
    intro τ; have := hMatEq2 1 τ; rw [mul_one, one_mul] at this; exact this.symm
  -- (X * M₁ - M₁ * X) * compProd(τ) = 0 for all M₁, τ
  have hCommComp : ∀ (M₁ : Matrix (Fin D) (Fin D) ℂ) (τ : Fin (M + 1) → Fin d),
      (X * M₁ - M₁ * X) * evalWord A (List.ofFn (fun k : Fin (M + 1 - L) =>
        τ ⟨k.val + L - 1, by omega⟩)) = 0 := by
    intro M₁ τ
    have h1 := hMatEq2 M₁ τ
    rw [hYeq τ, ← Matrix.mul_assoc] at h1
    rw [sub_mul, sub_eq_zero]; exact h1
  -- Conclude: X * M₁ = M₁ * X
  haveI : NeZero d := neZero_d_of_isInjective hA
  have hd : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  have hComm : ∀ M₁ : Matrix (Fin D) (Fin D) ℂ, X * M₁ = M₁ * X := by
    intro M₁
    by_cases hML : M + 1 = L
    · have h0 : M + 1 - L = 0 := by omega
      have := hCommComp M₁ (fun _ => ⟨0, hd⟩)
      simp only [h0, List.ofFn_zero, evalWord_nil, mul_one] at this
      exact sub_eq_zero.mp this
    · have hML' : 0 < M + 1 - L := by omega
      have hφ : LinearMap.mulLeft ℂ (X * M₁ - M₁ * X) = 0 := by
        apply LinearMap.ext_on_range
          (v := fun f : Fin (M + 1 - L) → Fin d => evalWord A (List.ofFn f))
        · simpa [wordSpan] using wordSpan_eq_top_of_isInjective hA hML'
        · intro f
          simp only [LinearMap.mulLeft_apply, LinearMap.zero_apply]
          let τ₀ : Fin (M + 1) → Fin d := fun k =>
            if h : L - 1 ≤ k.val ∧ k.val < M
            then f ⟨k.val - (L - 1), by omega⟩
            else ⟨0, hd⟩
          have hτ₀ : (fun k : Fin (M + 1 - L) => τ₀ ⟨k.val + L - 1, by omega⟩) = f := by
            ext ⟨k, hk⟩; simp only [τ₀]
            rw [dif_pos ⟨by omega, by omega⟩]
            congr 2; ext1; dsimp only; omega
          rw [← hτ₀]; exact hCommComp M₁ τ₀
      have := congrArg (· 1) hφ
      simp only [LinearMap.mulLeft_apply, mul_one, LinearMap.zero_apply] at this
      exact sub_eq_zero.mp this
  intro j; exact hComm (A j)

end MPSTensor
