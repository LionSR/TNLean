/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.IntersectionProperty
import TNLean.MPS.FundamentalTheorem.FiniteLength
import TNLean.Algebra.TracePairing
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.List.OfFn

/-!
# Block-word stripping for block-injective parent-Hamiltonian arguments

This file provides the algebraic stripping lemmas needed in the periodic
parent-Hamiltonian closure argument for block-injective tensors.

## Main results

- `MPSTensor.groundSpaceMap_injective_of_wordSpan_eq_top`
- `MPSTensor.groundSpaceMap_injective_of_isNBlkInjective`
- `MPSTensor.exists_right_factor_of_block_word_compatibility`
- `MPSTensor.commutes_block_words_of_commutes_long_words_of_isNBlkInjective`

## Mathematical content

If words of a fixed length `L` span the full matrix algebra, then the trace map
`groundSpaceMap A L` is injective. We use this to formulate a block-word
compatibility argument: if a family indexed by length-`L₀` words satisfies a
common right-factor relation after multiplying by every length-`K` suffix, then
block injectivity at length `L₀` strips the suffix and produces a common right
factor already at block length `L₀`.

The final theorem applies this stripping mechanism to commutation relations:
commutation with all words of length `m ≥ L₀` forces commutation with all block
words of length `L₀`.

## References

* [CPGSV21] arXiv:2011.12127, §IV.C
-/

open scoped Matrix BigOperators

namespace MPSTensor

variable {d D : ℕ}

/-- If words of length `L` span the full matrix algebra, then `groundSpaceMap A L`
has trivial kernel. -/
theorem groundSpaceMap_injective_of_wordSpan_eq_top {A : MPSTensor d D}
    {L : ℕ} (hWord : wordSpan A L = ⊤) :
    Function.Injective (groundSpaceMap A L) := by
  have hker : (groundSpaceMap A L).ker = ⊥ := by
    apply (LinearMap.ker_eq_bot').2
    intro X hX
    have hφ :
        (Matrix.traceLinearMap (Fin D) ℂ ℂ).comp (LinearMap.mulRight ℂ X) = 0 := by
      apply LinearMap.ext_on_range
        (v := fun σ : Fin L → Fin d => evalWord A (List.ofFn σ))
      · simpa [wordSpan] using hWord
      · intro σ
        simpa [groundSpaceMap_apply, Matrix.traceLinearMap_apply] using
          congrArg (fun ψ => ψ σ) hX
    exact trace_mul_right_eq_zero fun N => by
      have hNX : Matrix.trace (N * X) = 0 := by
        simpa [Matrix.traceLinearMap_apply] using congrArg (fun f => f N) hφ
      calc
        Matrix.trace (X * N) = Matrix.trace (N * X) := Matrix.trace_mul_comm X N
        _ = 0 := hNX
  exact LinearMap.ker_eq_bot.mp hker

/-- Block injectivity at length `L₀` makes `groundSpaceMap A L₀` injective. -/
theorem groundSpaceMap_injective_of_isNBlkInjective {A : MPSTensor d D}
    {L₀ : ℕ} (hInj : IsNBlkInjective A L₀) :
    Function.Injective (groundSpaceMap A L₀) := by
  apply groundSpaceMap_injective_of_wordSpan_eq_top
  exact (wordSpan_eq_top_iff_isNBlkInjective A L₀).mpr hInj

/-- Letter compatibility extends to every nonempty word.  The left family `Z` and
right family `F` can be indexed by any finite type; only the physical word lies
in the MPS alphabet. -/
private theorem exists_evalWord_factor_of_letter_compatibility
    {A : MPSTensor d D} {α : Type*} {F Z : α → Matrix (Fin D) (Fin D) ℂ}
    (hCompat : ∀ i : Fin d, ∃ Y : Matrix (Fin D) (Fin D) ℂ,
      ∀ a : α, Z a * A i = F a * Y)
    (w : List (Fin d)) (hw : w ≠ []) :
    ∃ Y : Matrix (Fin D) (Fin D) ℂ,
      ∀ a : α, Z a * evalWord A w = F a * Y := by
  cases w with
  | nil => cases hw rfl
  | cons i w =>
      obtain ⟨Y, hY⟩ := hCompat i
      refine ⟨Y * evalWord A w, ?_⟩
      intro a
      calc
        Z a * evalWord A (i :: w)
            = Z a * (A i * evalWord A w) := by simp [evalWord]
        _ = (Z a * A i) * evalWord A w := by rw [Matrix.mul_assoc]
        _ = (F a * Y) * evalWord A w := by rw [hY a]
        _ = F a * (Y * evalWord A w) := by rw [Matrix.mul_assoc]

/-- If a family indexed by length-`L₀` words is compatible with multiplication by
single physical letters, then block injectivity strips the letter and produces a
common right factor already at block length `L₀`. -/
private theorem exists_right_factor_of_block_letter_compatibility
    {A : MPSTensor d D} {L₀ : ℕ} (hInj : IsNBlkInjective A L₀) (hL₀ : 0 < L₀)
    {Z : (Fin L₀ → Fin d) → Matrix (Fin D) (Fin D) ℂ}
    (hCompat : ∀ i : Fin d, ∃ Y : Matrix (Fin D) (Fin D) ℂ,
      ∀ σ : Fin L₀ → Fin d,
        Z σ * A i = evalWord A (List.ofFn σ) * Y) :
    ∃ X : Matrix (Fin D) (Fin D) ℂ,
      ∀ σ : Fin L₀ → Fin d, Z σ = evalWord A (List.ofFn σ) * X := by
  have hCompatBlock : ∀ τ : Fin L₀ → Fin d,
      ∃ Yτ : Matrix (Fin D) (Fin D) ℂ,
        ∀ σ : Fin L₀ → Fin d,
          Z σ * evalWord A (List.ofFn τ) = evalWord A (List.ofFn σ) * Yτ := by
    intro τ
    have hw : List.ofFn τ ≠ [] := by
      intro hnil
      have hlen : L₀ = 0 := by
        simpa [List.length_ofFn] using congrArg List.length hnil
      omega
    exact exists_evalWord_factor_of_letter_compatibility
      (A := A) (F := fun σ : Fin L₀ → Fin d => evalWord A (List.ofFn σ))
      (Z := Z) hCompat (List.ofFn τ) hw
  choose Y hY using hCompatBlock
  let gen : (Fin L₀ → Fin d) → Matrix (Fin D) (Fin D) ℂ :=
    fun σ => evalWord A (List.ofFn σ)
  have hSurj : Function.Surjective (Fintype.linearCombination ℂ gen) := by
    apply (span_range_eq_top_iff_surjective_fintypeLinearCombination ℂ gen).mp
    simpa [gen, wordSpan] using (wordSpan_eq_top_iff_isNBlkInjective A L₀).mpr hInj
  obtain ⟨c, hc⟩ := hSurj (1 : Matrix (Fin D) (Fin D) ℂ)
  have hc' : ∑ τ, c τ • gen τ = (1 : Matrix (Fin D) (Fin D) ℂ) := by
    simpa [Fintype.linearCombination_apply] using hc
  let X : Matrix (Fin D) (Fin D) ℂ := ∑ τ, c τ • Y τ
  refine ⟨X, ?_⟩
  intro σ
  calc
    Z σ = Z σ * (1 : Matrix (Fin D) (Fin D) ℂ) := by simp
    _ = Z σ * ∑ τ, c τ • gen τ := by rw [hc']
    _ = ∑ τ, c τ • (Z σ * gen τ) := by simp [Finset.mul_sum]
    _ = ∑ τ, c τ • (gen σ * Y τ) := by
          refine Finset.sum_congr rfl ?_
          intro τ _
          rw [hY τ σ]
    _ = gen σ * ∑ τ, c τ • Y τ := by simp [Finset.mul_sum]
    _ = evalWord A (List.ofFn σ) * X := by rfl

/-- Block-word stripping theorem: compatibility with every suffix word of a fixed
length `K` implies a common right factor already at block length `L₀`. -/
theorem exists_right_factor_of_block_word_compatibility
    {A : MPSTensor d D} {K L₀ : ℕ} (hInj : IsNBlkInjective A L₀) (hL₀ : 0 < L₀)
    {Z : (Fin L₀ → Fin d) → Matrix (Fin D) (Fin D) ℂ}
    (hCompat : ∀ τ : Fin K → Fin d, ∃ Yτ : Matrix (Fin D) (Fin D) ℂ,
      ∀ σ : Fin L₀ → Fin d,
        Z σ * evalWord A (List.ofFn τ) = evalWord A (List.ofFn σ) * Yτ) :
    ∃ X : Matrix (Fin D) (Fin D) ℂ,
      ∀ σ : Fin L₀ → Fin d, Z σ = evalWord A (List.ofFn σ) * X := by
  induction K generalizing Z with
  | zero =>
      let τ0 : Fin 0 → Fin d := Fin.elim0
      obtain ⟨Y, hY⟩ := hCompat τ0
      refine ⟨Y, ?_⟩
      intro σ
      simpa [τ0, evalWord] using hY σ
  | succ K ih =>
      have hCompat1 : ∀ i : Fin d, ∃ Xi : Matrix (Fin D) (Fin D) ℂ,
          ∀ σ : Fin L₀ → Fin d,
            Z σ * A i = evalWord A (List.ofFn σ) * Xi := by
        intro i
        let Zi : (Fin L₀ → Fin d) → Matrix (Fin D) (Fin D) ℂ :=
          fun σ => Z σ * A i
        have hCompatZi : ∀ τ : Fin K → Fin d, ∃ Yτ : Matrix (Fin D) (Fin D) ℂ,
            ∀ σ : Fin L₀ → Fin d,
              Zi σ * evalWord A (List.ofFn τ) = evalWord A (List.ofFn σ) * Yτ := by
          intro τ
          obtain ⟨Yτ, hYτ⟩ := hCompat (Fin.cons i τ)
          refine ⟨Yτ, ?_⟩
          intro σ
          simpa [Zi, evalWord_ofFn_cons, Matrix.mul_assoc] using hYτ σ
        obtain ⟨Xi, hXi⟩ := ih hCompatZi
        exact ⟨Xi, hXi⟩
      exact exists_right_factor_of_block_letter_compatibility hInj hL₀ hCompat1

/-- If a matrix commutes with all words of some length `m ≥ L₀`, then it already
commutes with every block word of length `L₀`. -/
theorem commutes_block_words_of_commutes_long_words_of_isNBlkInjective
    {A : MPSTensor d D} {L₀ m : ℕ} (hInj : IsNBlkInjective A L₀) (hL₀ : 0 < L₀)
    (hm : L₀ ≤ m) {X : Matrix (Fin D) (Fin D) ℂ}
    (hComm : ∀ ω : Fin m → Fin d,
      X * evalWord A (List.ofFn ω) = evalWord A (List.ofFn ω) * X) :
    ∀ σ : Fin L₀ → Fin d,
      X * evalWord A (List.ofFn σ) = evalWord A (List.ofFn σ) * X := by
  let Z : (Fin L₀ → Fin d) → Matrix (Fin D) (Fin D) ℂ :=
    fun σ => X * evalWord A (List.ofFn σ)
  have hmEq : L₀ + (m - L₀) = m := by omega
  have hComm' : ∀ ω : Fin (L₀ + (m - L₀)) → Fin d,
      X * evalWord A (List.ofFn ω) = evalWord A (List.ofFn ω) * X := by
    intro ω
    let ω' : Fin m → Fin d := fun i => ω (Fin.cast hmEq.symm i)
    have hω' := hComm ω'
    have hlist : List.ofFn ω' = List.ofFn ω := by
      apply List.ext_getElem
      · simp [ω', hmEq]
      · intro i h1 h2
        simp [ω', Fin.cast]
    simpa [ω', hlist] using hω'
  have hCompat : ∀ τ : Fin (m - L₀) → Fin d,
      ∃ Yτ : Matrix (Fin D) (Fin D) ℂ,
        ∀ σ : Fin L₀ → Fin d,
          Z σ * evalWord A (List.ofFn τ) = evalWord A (List.ofFn σ) * Yτ := by
    intro τ
    refine ⟨evalWord A (List.ofFn τ) * X, ?_⟩
    intro σ
    have hστ := hComm' (Fin.append σ τ)
    rw [List.ofFn_fin_append, evalWord_append, ← Matrix.mul_assoc, Matrix.mul_assoc,
      Matrix.mul_assoc] at hστ
    simpa [Z, Matrix.mul_assoc] using hστ
  obtain ⟨R, hR⟩ :=
    exists_right_factor_of_block_word_compatibility (A := A) hInj hL₀ (Z := Z) hCompat
  let gen : (Fin L₀ → Fin d) → Matrix (Fin D) (Fin D) ℂ :=
    fun σ => evalWord A (List.ofFn σ)
  have hSurj : Function.Surjective (Fintype.linearCombination ℂ gen) := by
    apply (span_range_eq_top_iff_surjective_fintypeLinearCombination ℂ gen).mp
    simpa [gen, wordSpan] using (wordSpan_eq_top_iff_isNBlkInjective A L₀).mpr hInj
  obtain ⟨c, hc⟩ := hSurj (1 : Matrix (Fin D) (Fin D) ℂ)
  have hc' : ∑ σ, c σ • gen σ = (1 : Matrix (Fin D) (Fin D) ℂ) := by
    simpa [Fintype.linearCombination_apply] using hc
  have hXR : X = R := by
    calc
      X = X * (1 : Matrix (Fin D) (Fin D) ℂ) := by simp
      _ = X * ∑ σ, c σ • gen σ := by rw [hc']
      _ = ∑ σ, c σ • (X * gen σ) := by simp [Finset.mul_sum]
      _ = ∑ σ, c σ • (gen σ * R) := by
            refine Finset.sum_congr rfl ?_
            intro σ _
            exact congrArg (fun M => c σ • M) (hR σ)
      _ = (∑ σ, c σ • gen σ) * R := by simp [Finset.sum_mul]
      _ = R := by rw [hc', one_mul]
  intro σ
  simpa [Z, hXR] using hR σ

/-- If a matrix commutes with all words of some length `m ≥ L₀`, then block
injectivity forces it to commute with every matrix in the ambient algebra. -/
theorem commutes_all_of_commutes_long_words_of_isNBlkInjective
    {A : MPSTensor d D} {L₀ m : ℕ} (hInj : IsNBlkInjective A L₀) (hL₀ : 0 < L₀)
    (hm : L₀ ≤ m) {X : Matrix (Fin D) (Fin D) ℂ}
    (hComm : ∀ ω : Fin m → Fin d,
      X * evalWord A (List.ofFn ω) = evalWord A (List.ofFn ω) * X) :
    ∀ M : Matrix (Fin D) (Fin D) ℂ, X * M = M * X := by
  have hBlock :=
    commutes_block_words_of_commutes_long_words_of_isNBlkInjective
      (A := A) hInj hL₀ hm hComm
  have hφ : LinearMap.mulLeft ℂ X = LinearMap.mulRight ℂ X := by
    apply LinearMap.ext_on_range
      (v := fun σ : Fin L₀ → Fin d => evalWord A (List.ofFn σ))
    · simpa [wordSpan] using (wordSpan_eq_top_iff_isNBlkInjective A L₀).mpr hInj
    · intro σ
      simpa [LinearMap.mulLeft_apply, LinearMap.mulRight_apply] using hBlock σ
  intro M
  simpa [LinearMap.mulLeft_apply, LinearMap.mulRight_apply] using congrArg (fun f => f M) hφ

end MPSTensor
