/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.FundamentalTheorem.Basic
import TNLean.Wielandt.WielandtBound
import TNLean.Algebra.TracePairing

/-!
# Fundamental Theorem with finite-length MPV agreement

This file strengthens the single-block Fundamental Theorem of MPS by weakening
the hypothesis from `SameMPV` (agreement for **all** system sizes) to
`SameMPVFrom N₀` (agreement for system sizes `N ≥ N₀`).

## Main results

* `SameMPVFrom` — definition of finite-length MPV agreement
* `sameMPV_of_sameMPVFrom_of_injective` — finite-length agreement implies
  full agreement for injective tensors
* `fundamentalTheorem_singleBlock_finiteLength` — the strengthened FT

## Mathematical content

The key mathematical challenge is converting trace agreement on long words into
`evalWord` agreement on all words. The naive approach of pairing
`tr(evalWord A w * A i) = tr(evalWord B w * A i)` fails because the extensions
`w ++ [i]` produce `evalWord B w * B i`, not `evalWord B w * A i`.

The correct proof strategy uses the **linear extension** approach from the
existing FT proof (`LinearExtension.lean`): if `SameMPV A B` holds, there is
a unique linear map `T` with `T(A i) = B i` that is multiplicative. For the
finite-length case, one shows that `SameMPVFrom N₀` still determines `T`
uniquely, because word products of length `≥ 1` span `M_D(ℂ)` (by injectivity)
and the trace agreements of length `≥ N₀` pin down the action of `T`.

This requires a non-trivial inductive argument that interleaves the linear
extension construction with the trace pairing.

## Strengthening relative to the literature

The standard formulation of the FT (Pérez-García et al. 2007, Cirac et al. 2021)
requires either all-length agreement or works in the thermodynamic limit.
This formalization shows that a finite threshold suffices, making the theorem
applicable to fixed-size quantum systems.

## References

* [Pérez-García, Verstraete, Wolf, Cirac, *Matrix Product State Representations*,
  arXiv:quant-ph/0608197]
-/

open scoped Matrix BigOperators

namespace MPSTensor

variable {d D : ℕ}

/-! ## Definition: finite-length MPV agreement -/

/-- Two tensors generate the same MPV family **from system size `N₀` onwards**. -/
def SameMPVFrom (N₀ : ℕ) (A B : MPSTensor d D) : Prop :=
  ∀ (N : ℕ), N₀ ≤ N → ∀ (σ : Fin N → Fin d), mpv A σ = mpv B σ

/-- `SameMPV` implies `SameMPVFrom N₀` for any `N₀`. -/
theorem SameMPV.sameMPVFrom {A B : MPSTensor d D} (h : SameMPV A B) (N₀ : ℕ) :
    SameMPVFrom N₀ A B :=
  fun N _ σ => h N σ

/-- `SameMPVFrom 0` is equivalent to `SameMPV`. -/
theorem sameMPVFrom_zero_iff {A B : MPSTensor d D} :
    SameMPVFrom 0 A B ↔ SameMPV A B :=
  ⟨fun h N σ => h N (Nat.zero_le N) σ, fun h => h.sameMPVFrom 0⟩

/-- Monotonicity: `SameMPVFrom N₀` implies `SameMPVFrom N₁` for `N₀ ≤ N₁`. -/
theorem SameMPVFrom.mono {A B : MPSTensor d D} {N₀ N₁ : ℕ}
    (h : SameMPVFrom N₀ A B) (hle : N₀ ≤ N₁) :
    SameMPVFrom N₁ A B :=
  fun N hN σ => h N (le_trans hle hN) σ

/-! ## Trace agreement on word extensions -/

/-- If `SameMPVFrom N₀ A B`, then traces of word evaluations agree for words
of length `≥ N₀`. -/
lemma SameMPVFrom.trace_evalWord_of_length_ge
    {A B : MPSTensor d D} {N₀ : ℕ}
    (h : SameMPVFrom N₀ A B) {w : List (Fin d)} (hw : N₀ ≤ w.length) :
    Matrix.trace (evalWord A w) = Matrix.trace (evalWord B w) := by
  have := h w.length hw w.get
  simp only [mpv, coeff, List.ofFn_get] at this
  exact this

/-! ## Helper: word span for injective tensors -/

/-- For an injective tensor, `wordSpan A n = ⊤` for all `n ≥ 1`.

Base: `wordSpan A 1 = span(range A) = ⊤`. Step: right-multiply each generator
by the A-decomposition of `1` to embed `wordSpan A n` into `wordSpan A (n+1)`. -/
private theorem wordSpan_eq_top_of_isInjective
    {A : MPSTensor d D} (hA : IsInjective A)
    {n : ℕ} (hn : 1 ≤ n) : wordSpan A n = ⊤ := by
  classical
  obtain ⟨c, hc⟩ := hA.exists_decomposition 1
  induction n with
  | zero => omega
  | succ n ih =>
    rcases n.eq_zero_or_pos with rfl | hn'
    · -- Base case: wordSpan A 1 = span(range A) = ⊤
      rw [eq_top_iff, ← hA.span_eq_top]
      apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      have : A i = evalWord A [i] := by simp
      rw [this]; exact evalWord_mem_wordSpan A [i]
    · -- Inductive step: wordSpan A n ≤ wordSpan A (n+1)
      rw [eq_top_iff, ← ih hn']
      apply Submodule.span_le.mpr
      rintro _ ⟨σ, rfl⟩
      have key : evalWord A (List.ofFn σ) =
          ∑ i, c i • evalWord A (List.ofFn σ ++ [i]) := by
        conv_lhs => rw [show evalWord A (List.ofFn σ) = evalWord A (List.ofFn σ) * 1
          from (mul_one _).symm, hc, Finset.mul_sum]
        simp only [Algebra.mul_smul_comm, evalWord_append, evalWord_cons,
          evalWord_nil, mul_one]
      dsimp only
      rw [key]
      exact Submodule.sum_mem _ fun i _ =>
        Submodule.smul_mem _ _ (by
          have := evalWord_mem_wordSpan A (List.ofFn σ ++ [i])
          rwa [show (List.ofFn σ ++ [i]).length = n + 1 from by simp] at this)

/-! ## Main results -/

/-- **Finite-length agreement implies full agreement** for injective tensors.

**Proof**: For `N₀ ≥ 1`, let `1 = Σ cᵢ Aⁱ` (by injectivity) and `S = Σ cᵢ Bⁱ`.

1. Show `wordSpan B N₀ = ⊤` via the composition identity
   `traceMulRightPi A ∘ lcA = traceMulRightPi B ∘ lcB` (at word level `N₀`),
   using trace agreement at length `N₀ + 1` and the finrank transfer
   `ker_bot_of_range_le`.
2. Show `S = 1` by trace nondegeneracy on `wordSpan B N₀ = ⊤`:
   for `|v| = N₀`, the identity `tr(v_B · S) = tr(v_A) = tr(v_B)` gives
   `tr(M(S−1)) = 0` for all `M`.
3. Step down: for `|w| < N₀`, use `tr(w_A) = Σ cᵢ tr((w++[i])_A)` and
   `tr(w_B) = Σ cᵢ tr((w++[i])_B)` (the latter by `S = 1`), plus the
   inductive hypothesis at length `|w|+1`. -/
theorem sameMPV_of_sameMPVFrom_of_injective [NeZero D]
    {A B : MPSTensor d D}
    (hA : IsInjective A)
    {N₀ : ℕ} (hFrom : SameMPVFrom N₀ A B) :
    SameMPV A B := by
  -- Handle N₀ = 0 trivially.
  rcases N₀.eq_zero_or_pos with rfl | hN₀
  · exact sameMPVFrom_zero_iff.mp hFrom
  -- N₀ ≥ 1. Set up decomposition.
  classical
  obtain ⟨c, hc⟩ := hA.exists_decomposition 1
  -- ── Step 1: wordSpan B N₀ = ⊤ (composition identity) ──
  have hWB : wordSpan B N₀ = ⊤ := by
    let genA := fun σ : Fin N₀ → Fin d => evalWord A (List.ofFn σ)
    let genB := fun σ : Fin N₀ → Fin d => evalWord B (List.ofFn σ)
    let lcA := Fintype.linearCombination ℂ genA
    let lcB := Fintype.linearCombination ℂ genB
    let ΦA := traceMulRightPi (d := d) (D := D) A
    let ΦB := traceMulRightPi (d := d) (D := D) B
    have hSurjA : Function.Surjective lcA :=
      (span_range_eq_top_iff_surjective_fintypeLinearCombination ℂ genA).mp
        (wordSpan_eq_top_of_isInjective hA hN₀)
    -- Composition identity: Φ_A ∘ lc_A = Φ_B ∘ lc_B
    have hComp : (ΦA ∘ₗ lcA) = (ΦB ∘ₗ lcB) := by
      apply LinearMap.ext; intro α; apply funext; intro j
      change Matrix.trace (lcA α * A j) = Matrix.trace (lcB α * B j)
      simp only [lcA, lcB, Fintype.linearCombination_apply, Finset.sum_mul,
        smul_mul_assoc, Matrix.trace_sum, Matrix.trace_smul, smul_eq_mul]
      apply Finset.sum_congr rfl; intro σ _
      conv_lhs => rw [show evalWord A (List.ofFn σ) * A j =
          evalWord A (List.ofFn σ ++ [j]) from by
        rw [show A j = evalWord A [j] from by simp, ← evalWord_append]]
      conv_rhs => rw [show evalWord B (List.ofFn σ) * B j =
          evalWord B (List.ofFn σ ++ [j]) from by
        rw [show B j = evalWord B [j] from by simp, ← evalWord_append]]
      have key := hFrom.trace_evalWord_of_length_ge
        (show N₀ ≤ (List.ofFn σ ++ [j]).length by simp)
      rw [key]
    -- Range inclusion → ker Φ_B = ⊥
    have hRange : ΦA.range ≤ ΦB.range := by
      rw [show ΦA.range = (ΦA ∘ₗ lcA).range from by
        simp [LinearMap.range_comp, LinearMap.range_eq_top.2 hSurjA], hComp]
      exact LinearMap.range_comp_le_range lcB ΦB
    have hKerΦB : ΦB.ker = ⊥ :=
      ker_bot_of_range_le ΦA ΦB (traceMulRightPi_ker_eq_bot hA) hRange
    -- Equal kernels → equal range dimensions → lc_B surjective
    have hKerEq : lcA.ker = lcB.ker := by
      ext α; constructor
      · intro hα
        have h1 : (ΦA ∘ₗ lcA) α = (ΦB ∘ₗ lcB) α := congrFun (congrArg DFunLike.coe hComp) α
        simp only [LinearMap.comp_apply, LinearMap.mem_ker.mp hα, map_zero] at h1
        exact LinearMap.mem_ker.mpr (LinearMap.ker_eq_bot'.mp hKerΦB _ h1.symm)
      · intro hα
        have h1 : (ΦA ∘ₗ lcA) α = (ΦB ∘ₗ lcB) α := congrFun (congrArg DFunLike.coe hComp) α
        simp only [LinearMap.comp_apply, LinearMap.mem_ker.mp hα, map_zero] at h1
        exact LinearMap.mem_ker.mpr
          (LinearMap.ker_eq_bot'.mp (traceMulRightPi_ker_eq_bot hA) _ h1)
    have hSurjB : Function.Surjective lcB := by
      rw [← LinearMap.range_eq_top]
      have hRkA := LinearMap.finrank_range_add_finrank_ker lcA
      have hRkB := LinearMap.finrank_range_add_finrank_ker lcB
      rw [LinearMap.range_eq_top.mpr hSurjA, hKerEq] at hRkA
      apply Submodule.eq_top_of_finrank_eq
      have := finrank_top (R := ℂ) (M := Matrix (Fin D) (Fin D) ℂ)
      omega
    exact (span_range_eq_top_iff_surjective_fintypeLinearCombination ℂ genB).mpr hSurjB
  -- ── Step 2: S = 1 (trace nondegeneracy) ──
  set S := ∑ i, c i • B i
  have hS : S = 1 := by
    suffices h : S - 1 = 0 from sub_eq_zero.mp h
    apply trace_mul_right_eq_zero; intro N
    -- The linear functional tr((S−1) · _) vanishes on wordSpan B N₀ = ⊤
    have hf : (Matrix.traceLinearMap (Fin D) ℂ ℂ).comp
        (LinearMap.mulLeft ℂ (S - 1)) = 0 := by
      apply LinearMap.ext_on_range
        (v := fun σ : Fin N₀ → Fin d => evalWord B (List.ofFn σ))
        (hv := hWB)
      intro σ
      simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply,
        Matrix.traceLinearMap_apply, LinearMap.zero_apply, sub_mul, map_sub,
        one_mul]
      -- Goal: tr(S · evalWord B (List.ofFn σ)) - tr(evalWord B (List.ofFn σ)) = 0
      -- Both sides equal tr(evalWord A (List.ofFn σ))
      have h_SN : Matrix.trace (S * evalWord B (List.ofFn σ)) =
          Matrix.trace (evalWord A (List.ofFn σ)) := by
        show Matrix.trace ((∑ i, c i • B i) * evalWord B (List.ofFn σ)) = _
        rw [Finset.sum_mul]
        simp only [smul_mul_assoc, Matrix.trace_sum, Matrix.trace_smul,
          smul_eq_mul, ← evalWord_cons]
        have : Matrix.trace (evalWord A (List.ofFn σ)) =
            ∑ i, c i * Matrix.trace (evalWord A (i :: List.ofFn σ)) := by
          conv_lhs => rw [show evalWord A (List.ofFn σ) = 1 * evalWord A (List.ofFn σ)
            from (one_mul _).symm, hc, Finset.sum_mul]
          simp only [smul_mul_assoc, Matrix.trace_sum, Matrix.trace_smul,
            smul_eq_mul, ← evalWord_cons]
        rw [this]; apply Finset.sum_congr rfl; intro i _; congr 1
        exact (hFrom.trace_evalWord_of_length_ge (w := i :: List.ofFn σ) (by simp)).symm
      rw [h_SN, (hFrom.trace_evalWord_of_length_ge (show N₀ ≤ (List.ofFn σ).length by simp)).symm,
        sub_self]
    simpa [Matrix.traceLinearMap_apply, LinearMap.mulLeft_apply]
      using congrFun (congrArg DFunLike.coe hf) N
  -- ── Step 3: SameMPV by downward induction ──
  suffices h_all : ∀ w : List (Fin d),
      Matrix.trace (evalWord A w) = Matrix.trace (evalWord B w) by
    intro N σ; simpa [mpv, coeff] using h_all (List.ofFn σ)
  -- Induction on k = N₀ − |w|
  suffices h_k : ∀ k, ∀ w : List (Fin d), w.length + k = N₀ →
      Matrix.trace (evalWord A w) = Matrix.trace (evalWord B w) by
    intro w
    by_cases hle : N₀ ≤ w.length
    · exact hFrom.trace_evalWord_of_length_ge hle
    · exact h_k (N₀ - w.length) w (by omega)
  intro k; induction k with
  | zero => exact fun w hw => hFrom.trace_evalWord_of_length_ge (by omega)
  | succ k ih =>
    intro w hw
    -- Decompose using A: tr(w_A) = Σ cᵢ tr((w++[i])_A)
    have hA_sum : Matrix.trace (evalWord A w) =
        ∑ i : Fin d, c i * Matrix.trace (evalWord A (w ++ [i])) := by
      conv_lhs => rw [show evalWord A w = evalWord A w * 1 from (mul_one _).symm, hc,
        Finset.mul_sum]
      simp only [Algebra.mul_smul_comm, Matrix.trace_sum, Matrix.trace_smul, smul_eq_mul]
      apply Finset.sum_congr rfl; intro i _; congr 1
      rw [show A i = evalWord A [i] from by simp, ← evalWord_append]
    -- Decompose using B (S = 1): tr(w_B) = Σ cᵢ tr((w++[i])_B)
    have hB_sum : Matrix.trace (evalWord B w) =
        ∑ i : Fin d, c i * Matrix.trace (evalWord B (w ++ [i])) := by
      conv_lhs => rw [show evalWord B w = evalWord B w * 1 from (mul_one _).symm,
        show (1 : Matrix (Fin D) (Fin D) ℂ) = S from hS.symm, Finset.mul_sum]
      simp only [Algebra.mul_smul_comm, Matrix.trace_sum, Matrix.trace_smul, smul_eq_mul]
      apply Finset.sum_congr rfl; intro i _; congr 1
      rw [show B i = evalWord B [i] from by simp, ← evalWord_append]
    rw [hA_sum, hB_sum]
    apply Finset.sum_congr rfl; intro i _; congr 1
    exact ih (w ++ [i]) (by simp; omega)

/-- **Strengthened single-block Fundamental Theorem (finite-length version).**

If `A` is injective and `A`, `B` agree on all MPV coefficients for system sizes
`N ≥ N₀` (for **any** threshold `N₀`), then they are gauge equivalent. -/
theorem fundamentalTheorem_singleBlock_finiteLength [NeZero D]
    {A B : MPSTensor d D}
    (hA : IsInjective A)
    {N₀ : ℕ} (hFrom : SameMPVFrom N₀ A B) :
    GaugeEquiv A B :=
  fundamentalTheorem_singleBlock hA (sameMPV_of_sameMPVFrom_of_injective hA hFrom)

/-- For injective tensors, finite-length MPV agreement (from any threshold) is
equivalent to gauge equivalence. -/
theorem sameMPVFrom_iff_gaugeEquiv_of_injective [NeZero D]
    {A B : MPSTensor d D} (hA : IsInjective A) {N₀ : ℕ} :
    SameMPVFrom N₀ A B ↔ GaugeEquiv A B := by
  constructor
  · exact fundamentalTheorem_singleBlock_finiteLength hA
  · intro hGE
    exact (GaugeEquiv.sameMPV hGE).sameMPVFrom _

end MPSTensor
