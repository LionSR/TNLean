/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.Hastings.AreaLaw
import TNLean.MPS.AreaLaw.Hastings.MPSFromEntropy
import TNLean.MPS.AreaLaw.MPSApproximation

/-!
# Matrix product state approximation of the gapped ground state from Lemma 1

Let `Ω` be a gapped ground vector of a finite-range Hamiltonian on the chain of `L` sites with
local dimension `q > 1`, and suppose Lemma 1 holds around `Ω` with constants `ξ' > 0` and
`C₁ ≥ 1`. The area law bounds the entropy of every initial segment by `S_max`. With
`k₀ = ⌈exp(2 S_max)/2⌉`, truncating every cut onto the `k'` leading eigenvectors of its left
marginal, for `k' ≥ k₀`, gives an open-boundary matrix product state `Φ` of bond dimension at
most `k'` with `‖Φ - Ω‖² ≤ (L - 1) 4 C₁² e^{2/ξ'} (k'/k₀)^{-1/(ξ' log q)}`.

Source: Hastings, *An area law for one-dimensional quantum systems*, arXiv:0705.2024v4,
section "Matrix Product States", lines 505–557, with `S_max` from eq. `entbd` (lines 130–137).
This discharges the per-cut entropy hypothesis of
`isOpenMPS_norm_sub_sq_le_of_factorization_of_entropy`, recorded in
`docs/paper-gaps/hastings07_mps_entropy_stage.tex`.

**Stage theorem.** Lemma 1 enters as a hypothesis, as in
`regionEntropy_prefix_le_of_factorization`. The theorem becomes the source's matrix product
state approximation, with only the hypotheses of Hastings' theorem, once Lemma 1 is supplied
for the gapped ground state with a constant `C₁` uniform in the chain.

**Scope restriction (quantitative bounds of Lemma 1):** when `ξ'` and `C₁` are supplied by
the formalized Lemma 1, they carry its quantitative restrictions. Its length is
`ξ = 8 max(2v₀/ΔE, 1)`, with `v₀` the velocity of the chain localization estimate, which is
not shown to be the source's `max(2v/ΔE, ξ_C)` (arXiv:0705.2024v4, lines 96–112, 139–142); the
printed `ξ' = 6ξ` is not reached; and `C₁` is not shown to be bounded by a polynomial in `ξ`
(lines 258–262). The bond dimension `k₀ = ⌈exp(2 S_max)/2⌉` inherits these through the
area-law bound `S_max`. Documented in `docs/paper-gaps/hastings07_lemma1_decay_length.tex`
and `docs/paper-gaps/hastings07_gaussian_average_exponent.tex`.

The error is the squared norm, documented in
`docs/paper-gaps/hastings07_mps_error_measure.tex`. The value of `S_max` carries the local fix
of `TNLean.MPS.AreaLaw.Hastings.areaLawBound`.

**Local fix (constant):** the constant `e^{2/ξ'}` replaces the printed `e^{1/ξ'}`, because the
constraint is available only at even exponents. Documented in
`docs/paper-gaps/hastings07_schmidt_tail_constant.tex`.
-/

open Matrix Real
open TNLean.Lattice

namespace TNLean.MPS.AreaLaw.Hastings

variable {L q R : ℕ} {J : ℝ}

/-- **Matrix product state approximation of the gapped ground state, from Lemma 1 (stage
theorem).** Let `Ω` be a gapped ground vector of a finite-range Hamiltonian `h` on the chain
of `L` sites with local dimension `q > 1`, around which Lemma 1 holds with constants `ξ' > 0`
and `C₁ ≥ 1`. With `k₀ = ⌈exp(2 S_max)/2⌉` for the area-law bound
`S_max = areaLawBound ξ' C₁ q`, for every `k' ≥ k₀` the truncation `Φ` onto the `k'` leading
eigenvectors at every cut is an open-boundary matrix product state of bond dimension at most
`k'` with
`‖Φ - Ω‖² ≤ (L - 1) 4 C₁² e^{2/ξ'} (k'/k₀)^{-1/(ξ' log q)}`.
Hastings, arXiv:0705.2024v4, lines 505–557, with the constants of the module docstring. -/
theorem isOpenMPS_norm_sub_sq_le_of_gappedGroundState (h : ChainHamiltonian L q R J)
    {E₀ Δ : ℝ} {Ω : EuclideanSpace ℂ (Fin L → Fin q)}
    (hgs : Matrix.IsGappedGroundState h.operator E₀ Ω Δ) (hq : 1 < q)
    {ξ' C₁ : ℝ} (hξ' : 0 < ξ') (hC₁ : 1 ≤ C₁)
    (hfact : ∀ c l : ℕ, c + l ≤ L → ∃ OB OL OR : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ,
      IsFactorizationAt Ω c l (C₁ * Real.exp (-(l / ξ'))) OB OL OR)
    {k' : ℕ} (hk' : ⌈Real.exp (2 * areaLawBound ξ' C₁ q) / 2⌉₊ ≤ k') :
    let k₀ := ⌈Real.exp (2 * areaLawBound ξ' C₁ q) / 2⌉₊
    let P : ∀ k : ℕ, LeftBlockMatrix L q k := fun k ↦
      (Entropy.regionState_isHermitian (n := fun _ : Fin L ↦ q) (leftBlock L k)
        Ω).leadingEigenprojection k'
    let Φ := sequentialTruncation P (L - 1) Ω
    IsOpenMPS L q k' (fun x ↦ Φ x) ∧
      ‖Φ - Ω‖ ^ 2 ≤ ((L - 1 : ℕ) : ℝ) *
        (4 * C₁ ^ 2 * exp (2 / ξ') * ((k' : ℝ) / k₀) ^ (-1 / (ξ' * log q))) := by
  intro k₀ P Φ
  refine isOpenMPS_norm_sub_sq_le_of_isFactorizationAt_of_entropy hq hgs.1 hξ'
    (fun j _ m hm ↦ hfact j m hm) (fun j _ ↦ ?_) hk'
  -- The area law bounds the entropy of every initial segment by `S_max`.
  have hS := regionEntropy_prefix_le_of_factorization h hgs hξ' hC₁ hfact j
  rw [← leftBlock_eq_interval] at hS
  calc Real.exp (2 * Entropy.regionEntropy (n := fun _ : Fin L ↦ q) (leftBlock L j) Ω) / 2
      ≤ Real.exp (2 * areaLawBound ξ' C₁ q) / 2 := by gcongr
    _ ≤ k₀ := Nat.le_ceil _

end TNLean.MPS.AreaLaw.Hastings
