/-
Copyright (c) 2025 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.FundamentalTheorem.Full
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Coefficient convergence for canonical-form BNT decompositions

This module proves that the normalized decomposition coefficients `(μ k / μ 0)^N` converge
automatically from the separated weight hypothesis `HasStrictOrderedNonzeroWeights μ`
(with legacy wrappers through `IsCanonicalForm`), and provides a self-contained version of the
Fundamental Theorem (Thm 4.4) that derives the decomposition data from canonical form structure.

## Main results

### `HasStrictOrderedNonzeroWeights.norm_div_mu_lt_one`
For `k ≠ 0`, the norm ratio `‖μ k / μ 0‖ < 1` from the separated weight data.
The legacy wrapper `IsCanonicalForm.norm_div_mu_lt_one` remains available.

### `HasStrictOrderedNonzeroWeights.coeff_ratio_tendsto`
The normalized coefficient `(μ k / μ ⟨0, hr⟩) ^ N` converges: to `1` for the dominant
block `k = 0`, and to `0` for all other blocks. The legacy wrapper
`IsCanonicalForm.coeff_ratio_tendsto` remains available.

### `mpv_toTensorFromBlocks_eq_mu0_pow_mul_normalized`
The original block-diagonal MPV factors as `μ₀^N` times the normalized block-diagonal MPV.

### `proportional_normalized_of_proportional`
Proportionality of original block-diagonal MPVs transfers to normalized versions with
an adjusted proportionality constant; equivalently, the dominant factors `μ₀^N` are absorbed
into `c`.

### `fundamentalTheorem_proportionalMPV_CFBNT_auto`
Self-contained Fundamental Theorem (Thm 4.4) that derives the BNT decomposition
data automatically from `IsCanonicalFormBNT`. The user supplies:
- Two CF-BNT families
- A proportionality constant `c : ℕ → ℂ` with
  `mpv(toTensorFromBlocks μA A) σ = c N * mpv(toTensorFromBlocks μB B) σ`
- Convergent nonzero coefficients `aLim`, `bLim` for re-weighted decompositions
  (typically built from `(μ j / μ 0)^N` after dominant-weight normalization)

## References

- Pérez-García, Verstraete, Wolf, Cirac, *Matrix Product State Representations*,
  Quantum Inf. Comput. 7 (2007), arXiv:quant-ph/0608197.
- Cirac, Pérez-García, Schuch, Verstraete, *Matrix product states and projected entangled pair
  states: Concepts, symmetries, theorems*, Rev. Mod. Phys. 93 (2021), arXiv:2011.12127.
-/

open scoped Matrix BigOperators
open Filter

namespace MPSTensor

variable {d : ℕ}

/-! ## Coefficient convergence from strict antitonicity of norms -/

private lemma fin0_lt_of_ne {r : ℕ} (hr : 0 < r) (k : Fin r) (hk : k ≠ ⟨0, hr⟩) :
    ⟨0, hr⟩ < k := by
  simp only [Fin.lt_def]
  have : k.val ≠ 0 := by
    intro heq
    exact hk (Fin.ext heq)
  omega

namespace HasStrictOrderedNonzeroWeights

variable {r : ℕ}
variable {μ : Fin r → ℂ}

/-- The norm of `μ k / μ 0` is strictly less than 1 for `k ≠ 0`, because
`mu_strict_anti` gives `‖μ k‖ < ‖μ 0‖` for `0 < k`. -/
theorem norm_div_mu_lt_one (hμ : HasStrictOrderedNonzeroWeights μ) (hr : 0 < r)
    (k : Fin r) (hk : k ≠ ⟨0, hr⟩) :
    ‖μ k / μ ⟨0, hr⟩‖ < 1 := by
  rw [norm_div]
  have hμ0_pos : (0 : ℝ) < ‖μ ⟨0, hr⟩‖ := by
    rw [norm_pos_iff]
    exact hμ.mu_ne_zero ⟨0, hr⟩
  rw [div_lt_one hμ0_pos]
  exact hμ.mu_strict_anti (fin0_lt_of_ne hr k hk)

/-- **Coefficient convergence from strict antitonicity.**

For separated strict nonzero weight data, the normalized coefficient
`(μ k / μ ⟨0, hr⟩) ^ N` converges:
- to `1` when `k = ⟨0, hr⟩` (dominant block), since `μ₀ / μ₀ = 1`;
- to `0` when `k ≠ ⟨0, hr⟩`, since `‖μ_k / μ₀‖ < 1`. -/
theorem coeff_ratio_tendsto (hμ : HasStrictOrderedNonzeroWeights μ) (hr : 0 < r) :
    ∀ k : Fin r,
      Tendsto (fun N => (μ k / μ ⟨0, hr⟩) ^ N) atTop
        (nhds (if k = ⟨0, hr⟩ then 1 else 0)) := by
  intro k
  by_cases hk : k = ⟨0, hr⟩
  · simp only [hk, div_self (hμ.mu_ne_zero ⟨0, hr⟩), one_pow]
    exact tendsto_const_nhds
  · simp only [if_neg hk]
    exact tendsto_pow_atTop_nhds_zero_of_norm_lt_one
      (hμ.norm_div_mu_lt_one hr k hk)

/-- The norm of `μ k` is strictly less than `‖μ 0‖` for non-dominant blocks. -/
theorem norm_mu_lt_dominant (hμ : HasStrictOrderedNonzeroWeights μ) (hr : 0 < r)
    (k : Fin r) (hk : k ≠ ⟨0, hr⟩) :
    ‖μ k‖ < ‖μ ⟨0, hr⟩‖ :=
  hμ.mu_strict_anti (fin0_lt_of_ne hr k hk)

end HasStrictOrderedNonzeroWeights

namespace IsCanonicalForm

variable {r : ℕ} {dim : Fin r → ℕ}
variable {μ : Fin r → ℂ} {A : (k : Fin r) → MPSTensor d (dim k)}

/-- Backwards-compatible wrapper for
`HasStrictOrderedNonzeroWeights.norm_div_mu_lt_one`. -/
theorem norm_div_mu_lt_one (hCF : IsCanonicalForm μ A) (hr : 0 < r)
    (k : Fin r) (hk : k ≠ ⟨0, hr⟩) :
    ‖μ k / μ ⟨0, hr⟩‖ < 1 :=
  hCF.toHasStrictOrderedNonzeroWeights.norm_div_mu_lt_one hr k hk

/-- Backwards-compatible wrapper for
`HasStrictOrderedNonzeroWeights.coeff_ratio_tendsto`. -/
theorem coeff_ratio_tendsto (hCF : IsCanonicalForm μ A) (hr : 0 < r) :
    ∀ k : Fin r,
      Tendsto (fun N => (μ k / μ ⟨0, hr⟩) ^ N) atTop
        (nhds (if k = ⟨0, hr⟩ then 1 else 0)) :=
  hCF.toHasStrictOrderedNonzeroWeights.coeff_ratio_tendsto hr

/-- Backwards-compatible wrapper for
`HasStrictOrderedNonzeroWeights.norm_mu_lt_dominant`. -/
theorem norm_mu_lt_dominant (hCF : IsCanonicalForm μ A) (hr : 0 < r)
    (k : Fin r) (hk : k ≠ ⟨0, hr⟩) :
    ‖μ k‖ < ‖μ ⟨0, hr⟩‖ :=
  hCF.toHasStrictOrderedNonzeroWeights.norm_mu_lt_dominant hr k hk

end IsCanonicalForm

/-! ## Normalized block-diagonal tensor -/

/-- Construct the block-diagonal tensor with eigenvalues normalized by the dominant one.
This is `toTensorFromBlocks (fun k => μ k / μ ⟨0, hr⟩) A`. -/
noncomputable def toTensorFromBlocksNormalized {r : ℕ} {dim : Fin r → ℕ}
    (μ : Fin r → ℂ) (hr : 0 < r) (A : (k : Fin r) → MPSTensor d (dim k)) :
    MPSTensor d (∑ k : Fin r, dim k) :=
  toTensorFromBlocks (fun k => μ k / μ ⟨0, hr⟩) A

/-- Expand the normalized block-diagonal MPV as the sum of normalized coefficients times the
individual block MPVs. -/
theorem mpv_toTensorFromBlocksNormalized_eq_sum
    {r : ℕ} {dim : Fin r → ℕ}
    (μ : Fin r → ℂ) (hr : 0 < r) (A : (k : Fin r) → MPSTensor d (dim k))
    {N : ℕ} (σ : Fin N → Fin d) :
    mpv (toTensorFromBlocksNormalized μ hr A) σ =
      ∑ k : Fin r, (μ k / μ ⟨0, hr⟩) ^ N • mpv (A k) σ :=
  mpv_toTensorFromBlocks_eq_sum (fun k => μ k / μ ⟨0, hr⟩) A σ

/-- The original block-diagonal MPV factors as `μ₀^N` times the normalized block-diagonal MPV.

This identity is the key algebraic step for normalizing the BNT decomposition:
`mpv(toTensorFromBlocks μ A) σ = μ₀^N * mpv(toTensorFromBlocksNormalized μ A) σ`. -/
theorem mpv_toTensorFromBlocks_eq_mu0_pow_mul_normalized
    {r : ℕ} {dim : Fin r → ℕ}
    (μ : Fin r → ℂ) (hr : 0 < r) (A : (k : Fin r) → MPSTensor d (dim k))
    (hμ0 : μ ⟨0, hr⟩ ≠ 0)
    {N : ℕ} (σ : Fin N → Fin d) :
    mpv (toTensorFromBlocks μ A) σ =
      (μ ⟨0, hr⟩) ^ N * mpv (toTensorFromBlocksNormalized μ hr A) σ := by
  rw [mpv_toTensorFromBlocks_eq_sum, mpv_toTensorFromBlocksNormalized_eq_sum]
  simp only [smul_eq_mul, Finset.mul_sum]
  congr 1
  ext k
  rw [div_pow, ← mul_assoc, mul_div_cancel₀ _ (pow_ne_zero N hμ0)]

/-! ## Proportionality transfer to normalized tensors -/

/-- If the original block-diagonal MPVs are proportional, the normalized versions are too
with an adjusted proportionality constant `c N * (μB₀ / μA₀)^N`.

This is the formal counterpart of normalizing by the dominant weight: the factors `μA₀^N` and
`μB₀^N` are moved out of the decomposition, and the leftover ratio is absorbed into the new
proportionality constant. Concretely, from `mpv(A_total) σ = c N * mpv(B_total) σ` and the
factorization `mpv(A_total) σ = μA₀^N * mpv(A_norm) σ`, we get
`mpv(A_norm) σ = c N * (μB₀/μA₀)^N * mpv(B_norm) σ`. -/
theorem proportional_normalized_of_proportional
    {rA rB : ℕ} {dimA : Fin rA → ℕ} {dimB : Fin rB → ℕ}
    {μA : Fin rA → ℂ} {μB : Fin rB → ℂ}
    (A : (j : Fin rA) → MPSTensor d (dimA j))
    (B : (k : Fin rB) → MPSTensor d (dimB k))
    (hrA : 0 < rA) (hrB : 0 < rB)
    (hμA0 : μA ⟨0, hrA⟩ ≠ 0) (hμB0 : μB ⟨0, hrB⟩ ≠ 0)
    (c : ℕ → ℂ)
    (hProp : ∀ N (σ : Fin N → Fin d),
      mpv (toTensorFromBlocks μA A) σ = c N * mpv (toTensorFromBlocks μB B) σ)
    {N : ℕ} (σ : Fin N → Fin d) :
    mpv (toTensorFromBlocksNormalized μA hrA A) σ =
      (c N * (μB ⟨0, hrB⟩ / μA ⟨0, hrA⟩) ^ N) *
        mpv (toTensorFromBlocksNormalized μB hrB B) σ := by
  have hμA0N : (μA ⟨0, hrA⟩) ^ N ≠ 0 := pow_ne_zero N hμA0
  have h := hProp N σ
  rw [mpv_toTensorFromBlocks_eq_mu0_pow_mul_normalized μA hrA A hμA0 σ] at h
  rw [mpv_toTensorFromBlocks_eq_mu0_pow_mul_normalized μB hrB B hμB0 σ] at h
  -- h : μA₀^N * mpv(A_norm) = c_N * (μB₀^N * mpv(B_norm))
  -- Goal: mpv(A_norm) = c_N * (μB₀/μA₀)^N * mpv(B_norm)
  -- Divide h by μA₀^N:
  have h2 : mpv (toTensorFromBlocksNormalized μA hrA A) σ =
      (μA ⟨0, hrA⟩ ^ N)⁻¹ * (c N * (μB ⟨0, hrB⟩ ^ N *
        mpv (toTensorFromBlocksNormalized μB hrB B) σ)) := by
    rw [← h, ← mul_assoc, inv_mul_cancel₀ hμA0N, one_mul]
  rw [h2]
  rw [div_pow, ← inv_pow]
  ring

/-! ## Self-contained Fundamental Theorem (Thm 4.4)

The auto version derives the BNT decomposition data from the canonical form structure.
The user only needs to supply:
1. Two CF-BNT families with proportional block-diagonal MPVs
2. Coefficients and their limits for the re-weighted decomposition
3. The convergence of the (adjusted) proportionality constant

The coefficient data `aLim`/`bLim` is needed because the raw decomposition coefficients
`(μ k)^N` do not satisfy the convergence hypotheses directly. In the strict-dominance regime one
first normalizes by the dominant weight, so the relevant arrays are `(μ k / μ 0)^N`; these
converge to `0` for non-dominant blocks, while the overall factor `μ 0^N` is absorbed into the
proportionality constant. In grouped equal-modulus sectors even the normalized sums can still
oscillate. The paper resolves this via induction on block count, matching dominant blocks first
and stripping them off. Our formalization takes the needed convergent coefficient data as
explicit hypotheses.

**What is derived automatically from `IsCanonicalFormBNT`:**
- The overlap properties (self → 1, cross → 0)
- The decomposition identity `mpv(toTensorFromBlocks μ A) σ = Σ_k (μ_k)^N * mpv(A_k) σ`
- Injectivity and left-canonical normalization

**What the user must supply:**
- The proportionality `mpv(A_total) = c_N * mpv(B_total)`
- Convergent decomposition coefficients `aCoeff`, `bCoeff` with nonzero limits
- The convergence of the proportionality constant `c` -/
/-- Self-contained CF-BNT proportional FT wrapper using the assembled theorem from
`FundamentalTheoremFull`. -/
theorem fundamentalTheorem_proportionalMPV_CFBNT_auto
    {d rA rB : ℕ}
    {dimA : Fin rA → ℕ} {dimB : Fin rB → ℕ}
    [∀ k, NeZero (dimA k)] [∀ k, NeZero (dimB k)]
    {μA : Fin rA → ℂ} {μB : Fin rB → ℂ}
    (A : (j : Fin rA) → MPSTensor d (dimA j))
    (B : (k : Fin rB) → MPSTensor d (dimB k))
    (hA : IsCanonicalFormBNT μA A)
    (hB : IsCanonicalFormBNT μB B)
    -- Decomposition coefficients (supplied by the caller; see design note above)
    (aCoeff : ℕ → Fin rA → ℂ) (bCoeff : ℕ → Fin rB → ℂ)
    (aLim : Fin rA → ℂ) (bLim : Fin rB → ℂ)
    (haCoeff : ∀ j, Tendsto (fun N => aCoeff N j) atTop (nhds (aLim j)))
    (hbCoeff : ∀ k, Tendsto (fun N => bCoeff N k) atTop (nhds (bLim k)))
    (haLim_ne : ∀ j, aLim j ≠ 0)
    (hbLim_ne : ∀ k, bLim k ≠ 0)
    -- Decomposition identities (with the supplied coefficients)
    (hA_decomp : ∀ N (σ : Fin N → Fin d),
      mpv (toTensorFromBlocks μA A) σ =
        ∑ j : Fin rA, (aCoeff N j) * mpv (A j) σ)
    (hB_decomp : ∀ N (σ : Fin N → Fin d),
      mpv (toTensorFromBlocks μB B) σ =
        ∑ k : Fin rB, (bCoeff N k) * mpv (B k) σ)
    -- Proportionality
    (c : ℕ → ℂ) (cLim : ℂ)
    (hProp : ∀ N (σ : Fin N → Fin d),
      mpv (toTensorFromBlocks μA A) σ = c N * mpv (toTensorFromBlocks μB B) σ)
    (hc : Tendsto c atTop (nhds cLim))
    (hcLim_ne : cLim ≠ 0) :
    ProportionalMPVPermutationConclusion (d := d) (dimA := dimA) (dimB := dimB) A B :=
  fundamentalTheorem_proportionalMPV_CFBNT A B hA hB
    (toTensorFromBlocks μA A) (toTensorFromBlocks μB B)
    aCoeff bCoeff aLim bLim c cLim
    hA_decomp hB_decomp haCoeff hbCoeff haLim_ne hbLim_ne hProp hc hcLim_ne

end MPSTensor
