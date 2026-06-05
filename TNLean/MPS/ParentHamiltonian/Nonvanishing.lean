/-
Copyright (c) 2025 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.ParentHamiltonian.Basic
import TNLean.Algebra.TracePairing
import TNLean.Wielandt.SpanGrowth.CumulativeSpan

/-!
# Nonvanishing of block-injective MPS vectors

This file records the descent argument showing that a block-injective tensor has
a nonzero periodic MPS vector on chains longer than the injectivity length.
-/

open scoped Matrix BigOperators

namespace MPSTensor

variable {d D : ℕ}

/-- If all products of some positive length \(k\) are zero and \(A\) is
\(L_0\)-block-injective with \(L_0>0\), we reach a contradiction.

**Descent argument:** if \(k\le L_0\), factor every length-\(L_0\) word through
a zero length-\(k\) prefix. If \(k>L_0\), use the span equality
\[
  \operatorname{span}\{A^w : |w|=L_0\}=M_D(\mathbb C)
\]
with the identity matrix to show that every product of length \(k-L_0\) is zero,
then recurse. -/
private theorem allZero_contradiction [NeZero D]
    {A : MPSTensor d D} {L₀ : ℕ} (hInj : IsNBlkInjective A L₀) (hL₀ : 0 < L₀)
    {k : ℕ} (hk : 0 < k)
    (hzero : ∀ w : List (Fin d), w.length = k → evalWord A w = 0) : False := by
  have hws : wordSpan A L₀ = ⊤ := (wordSpan_eq_top_iff_isNBlkInjective A L₀).mpr hInj
  -- Strong induction on k.
  suffices ∀ k, 0 < k → (∀ w : List (Fin d), w.length = k → evalWord A w = 0) → False from
    this k hk hzero
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro hk_pos hk_zero
    by_cases hkL : k ≤ L₀
    · -- Case k ≤ L₀: factor every length-L₀ word as (take k) ++ (drop k).
      have hws_bot : wordSpan A L₀ = ⊥ := by
        rw [eq_bot_iff, wordSpan]
        apply Submodule.span_le.mpr
        rintro _ ⟨σ, rfl⟩
        rw [SetLike.mem_coe, Submodule.mem_bot]
        have hsplit := List.take_append_drop k (List.ofFn σ)
        have htake_len : (List.take k (List.ofFn σ)).length = k := by
          rw [List.length_take]; simp; omega
        calc evalWord A (List.ofFn σ)
            = evalWord A (List.take k (List.ofFn σ) ++
                List.drop k (List.ofFn σ)) := by rw [hsplit]
          _ = evalWord A (List.take k (List.ofFn σ)) *
                evalWord A (List.drop k (List.ofFn σ)) := evalWord_append ..
          _ = 0 * evalWord A (List.drop k (List.ofFn σ)) := by
                rw [hk_zero _ htake_len]
          _ = 0 := zero_mul _
      exact absurd (hws ▸ hws_bot) top_ne_bot
    · -- Case k > L₀: use span = M_D and M = 1 to descend to k - L₀.
      push Not at hkL
      have hkL₀_pos : 0 < k - L₀ := by omega
      apply ih (k - L₀) (by omega) hkL₀_pos
      intro w₂ hw₂
      -- For each σ₁ of length L₀: evalWord A (ofFn σ₁) * evalWord A w₂ = 0.
      have hmul_zero : ∀ σ₁ : Fin L₀ → Fin d,
          evalWord A (List.ofFn σ₁) * evalWord A w₂ = 0 := by
        intro σ₁
        have hlen : (List.ofFn σ₁ ++ w₂).length = k := by simp [hw₂]; omega
        have := hk_zero _ hlen
        rwa [evalWord_append] at this
      -- The map M ↦ M * evalWord A w₂ vanishes on wordSpan A L₀ = ⊤.
      have hright : LinearMap.mulRight ℂ (evalWord A w₂) = 0 := by
        apply LinearMap.ext_on_range
          (v := fun σ : Fin L₀ → Fin d => evalWord A (List.ofFn σ))
          (hv := by rwa [← wordSpan])
        intro σ₁
        simp [LinearMap.mulRight_apply, hmul_zero σ₁]
      -- Taking M = 1: evalWord A w₂ = 0.
      have h1 : (1 : Matrix (Fin D) (Fin D) ℂ) * evalWord A w₂ = 0 :=
        show LinearMap.mulRight ℂ (evalWord A w₂) 1 = 0 by rw [hright]; simp
      simpa using h1

/-- For a tensor that is injective after blocking, the MPS vector is nonzero on
chains of sufficient length.

If the length-\(N\) MPS vector vanished, then
\(\operatorname{tr}(A^w)=0\) for every word \(w\) of length \(N\). The
block-injectivity span identity
\[
  \operatorname{span}\{A^u : |u|=L_0\}=M_D(\mathbb C)
\]
forces every suffix product of length \(N-L_0\) to vanish. Strong induction on
the word length then gives a contradiction. -/
theorem mpv_ne_zero_of_isNBlkInjective {A : MPSTensor d D} [NeZero D]
    {L₀ : ℕ} (hInj : IsNBlkInjective A L₀) (hL₀ : 0 < L₀)
    {N : ℕ} (hN : L₀ + 1 ≤ N) :
    (mpv A : NSiteSpace d N) ≠ 0 := by
  have hws : wordSpan A L₀ = ⊤ := (wordSpan_eq_top_iff_isNBlkInjective A L₀).mpr hInj
  intro hzero
  -- mpv = 0 means tr(evalWord A (List.ofFn σ)) = 0 for all σ : Fin N → Fin d.
  have htr_zero : ∀ σ : Fin N → Fin d,
      Matrix.trace (evalWord A (List.ofFn σ)) = 0 := by
    intro σ; simpa [mpv, coeff] using congrFun hzero σ
  -- All products of length (N - L₀) are zero by trace nondegeneracy.
  have hprod_zero : ∀ w₂ : List (Fin d), w₂.length = N - L₀ →
      evalWord A w₂ = 0 := by
    intro w₂ hw₂
    -- Show ∀ M, tr(evalWord A w₂ * M) = 0 to get evalWord A w₂ = 0.
    apply trace_mul_right_eq_zero
    intro M
    -- The functional P ↦ tr(P * evalWord A w₂) vanishes on wordSpan A L₀ = ⊤.
    have hφ : (Matrix.traceLinearMap (Fin D) ℂ ℂ).comp
        (LinearMap.mulRight ℂ (evalWord A w₂)) = 0 := by
      apply LinearMap.ext_on_range
        (v := fun σ : Fin L₀ → Fin d => evalWord A (List.ofFn σ))
        (hv := by rwa [← wordSpan])
      intro σ₁
      simp only [LinearMap.comp_apply, LinearMap.mulRight_apply,
        Matrix.traceLinearMap_apply]
      -- tr(evalWord A (List.ofFn σ₁) * evalWord A w₂) = tr(evalWord A (σ₁ ++ w₂))
      rw [← evalWord_append]
      -- This is a trace of a length-N word product, hence 0.
      have hlen : (List.ofFn σ₁ ++ w₂).length = N := by simp [hw₂]; omega
      let σ' : Fin N → Fin d :=
        fun i => (List.ofFn σ₁ ++ w₂).get ⟨i.val, hlen.symm ▸ i.isLt⟩
      have hw_eq : List.ofFn σ' = List.ofFn σ₁ ++ w₂ := by
        apply List.ext_get
        · simp [hw₂]; omega
        · intro i h1 h2; simp [σ']
      rw [← hw_eq]
      exact htr_zero σ'
    -- From hφ: ∀ P, tr(P * evalWord A w₂) = 0. By trace commutativity:
    calc Matrix.trace (evalWord A w₂ * M)
        = Matrix.trace (M * evalWord A w₂) := Matrix.trace_mul_comm ..
      _ = 0 := by
          simpa [Matrix.traceLinearMap_apply] using congrArg (· M) hφ
  exact allZero_contradiction hInj hL₀ (by omega : 0 < N - L₀) hprod_zero

end MPSTensor
