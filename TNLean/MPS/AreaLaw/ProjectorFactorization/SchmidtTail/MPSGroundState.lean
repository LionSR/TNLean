/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ProjectorFactorization.AreaLaw
import TNLean.MPS.AreaLaw.ProjectorFactorization.LiebRobinson
import TNLean.MPS.AreaLaw.Approximation.MPSApproximation
import QICLean.ManyBody.Hamiltonian.GroundSpace
import TNLean.MPS.AreaLaw.ProjectorFactorization.PositiveFactorization
import TNLean.MPS.AreaLaw.ProjectorFactorization.SchmidtTail.SchmidtTailConstraint
import TNLean.MPS.AreaLaw.ProjectorFactorization.SchmidtTail.SchmidtTailMPS

/-!
# Matrix product state approximation of a gapped ground state

Let `Ω` be a gapped ground vector on a chain of `L` sites. Approximate
factorization with constants `ξ' > 0` and `C₁ ≥ 1`, together with an
entropy bound `Smax` at every cut, gives a matrix product state `Φ` of
bond dimension at most `k'` for every `k' ≥ k₀ = ceil(exp(2 Smax)/2)`.
The squared error is at most
`(L-1) * 4 C₁² exp(2/ξ') * (k'/k₀)^(-1/(ξ' log q))`.
Hastings, arXiv:0705.2024v4, lines 505–557, uses the entropy bound from
lines 130–144 to choose the common threshold.

This module supplies both hypotheses from the Hamiltonian assumptions,
using `Smax = areaLawBound ξ' C₁ q`. For `q = 1`, truncation is exact.

**Scope restriction (auxiliary parameters):** the endpoints below use
`lemmaOneLength R (J/ΔE) 1` or `ζ = lemmaOneEndpointLength R J ΔE`.
The corresponding physical Lieb–Robinson velocities include a term
proportional to the gap, rather than being expressed as a fixed multiple of `J`. Moreover,
the auxiliary entropy bound at these lengths has the corrected doubled
exponent. The common order-`J` source-parameter conclusion, with the
printed entropy maximum in `k₀`, is proved in
`Hastings/SourceConsequences.lean`. The auxiliary bounds remain valid.
See `docs/paper-gaps/hastings07_lemma1_decay_length.tex`,
`docs/paper-gaps/hastings07_doubling_constants.tex`, and
`docs/paper-gaps/hastings07_mps_entropy_stage.tex`.

**Local fix (error and constant):** the error is the squared norm of an
unnormalized truncation, and `exp(2/ξ')` replaces the printed `exp(1/ξ')`
because the constraint is available only at even exponents. See
`docs/paper-gaps/hastings07_mps_error_measure.tex` and
`docs/paper-gaps/hastings07_schmidt_tail_constant.tex`.

It also contains the following results.

* `TNLean.MPS.AreaLaw.Hastings.isOpenMPS_norm_sub_sq_le_of_factorization_of_entropy`,
  `TNLean.MPS.AreaLaw.Hastings.isOpenMPS_norm_sub_sq_le_of_isFactorizationAt_of_entropy`: matrix
  product state approximation from the entropy of the cuts.
-/

section MPSFromEntropy

/-!
## Matrix product state approximation from the entropy of the cuts

Suppose that the unit vector `Ω` on a chain of `L` sites with local dimension `q ≥ 1` satisfies
the approximate factorization of Hastings' Lemma 1 at every internal cut, and that a natural
number `k₀` satisfies `k₀ ≥ exp(2 S_j)/2` for the entropy `S_j` of the first `j` sites at every
internal cut `j`. Truncating every cut onto the `k'` leading eigenvectors of its left marginal,
for `k' ≥ k₀`, gives an open-boundary matrix product state `Φ` of bond dimension at most `k'`
with `‖Φ - Ω‖² ≤ (L - 1) 4 C₁² e^{2/ξ'} (k'/k₀)^{-1/(ξ' log q)}` when `L ≥ 2`.
For `L < 2`, there is no internal cut and `Φ = Ω`. For `q = 1` every left marginal is a `1 × 1`
matrix of trace one, so the truncation is exact and again `Φ = Ω`; there `log q = 0`, and the
bound holds because its left side vanishes. The source assumes `q ≥ 2`. The vector `Φ` is not
required to be normalized; the error is the squared Hilbert-space norm. Entropies use natural
logarithms.

Source: Hastings, *An area law for one-dimensional quantum systems*, arXiv:0705.2024v4,
section "Matrix Product States", lines 505–557. The constraint at each cut is eq. `constraint`
with `P = 1/2` and `k₀ = exp(2S)/2` (eq. `k0Ent`); the tail bound and the error of the matrix
product state follow from it as in the source.

**Scope restriction (conditional construction):** Hastings explicitly assumes a uniform entropy
bound in the conditional construction (lines 516–518). This theorem takes the factorization
and a common entropy threshold as hypotheses. The application under only the Hamiltonian
assumptions, which derives both bounds with constants independent of chain length, is
`exists_isOpenMPS_norm_sub_sq_le_of_isGapped` in
`TNLean/MPS/AreaLaw/Hastings/MPSGroundState.lean`. Documented in
`docs/paper-gaps/hastings07_mps_entropy_stage.tex`.

The source's `k₀ = exp(2S)/2` is a real number. Here `k₀` is any natural number at least
`exp(2 S_j)/2` at every cut, such as the ceiling of the largest of these; the constraint at a
cut is applied with this common `k₀`, which only weakens it. The error is the squared norm,
documented in `docs/paper-gaps/hastings07_mps_error_measure.tex`.

**Local fix (constant):** the constant `e^{2/ξ'}` replaces the printed `e^{1/ξ'}`, because the
constraint is available only at even exponents. Documented in
`docs/paper-gaps/hastings07_schmidt_tail_constant.tex`.
-/

open Matrix Real
open scoped Matrix.Norms.L2Operator ComplexOrder

namespace TNLean.MPS.AreaLaw.Hastings

variable {L q : ℕ}

/-- **Matrix product state from the entropy of the cuts (stage theorem).** Under the
approximate factorization of Lemma 1 at every internal cut, if the natural number `k₀`
satisfies `k₀ ≥ exp(2 S_j)/2` for the entropy `S_j` of the first `j` sites at every internal
cut `j`, then for every `k' ≥ k₀` the
truncation `Φ` onto the `k'` leading eigenvectors at every cut is an open-boundary matrix product
state of bond dimension at most `k'`. For `L ≥ 2`,
`‖Φ - Ω‖² ≤ (L - 1) 4 C₁² e^{2/ξ'} (k'/k₀)^{-1/(ξ' log q)}`.
For `L < 2` or `q = 1`, `Φ = Ω`. The approximant need not be normalized, and the error is the
squared Hilbert-space norm, not a trace norm.
Hastings, arXiv:0705.2024v4, lines 505–557, with the constant described in the module
docstring. -/
theorem isOpenMPS_norm_sub_sq_le_of_factorization_of_entropy [NeZero q]
    {Ω : EuclideanSpace ℂ (Fin L → Fin q)} (hΩ : ‖Ω‖ = 1) {ξ' C₁ : ℝ} (hξ' : 0 < ξ')
    (hfact : ∀ j ∈ Finset.Ico 1 L, ∀ m : ℕ, j + m ≤ L →
      ∃ (OB OL OR : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) (SB SL SR : Finset (Fin L)),
      ManyBody.IsSupportedOn (X := fun _ ↦ Fin q) OB SB ∧ SB ⊆ leftBlock L (j + m) ∧
      ManyBody.IsSupportedOn (X := fun _ ↦ Fin q) OL SL ∧ SL ⊆ leftBlock L j ∧
      ManyBody.IsSupportedOn (X := fun _ ↦ Fin q) OR SR ∧ Disjoint SR (leftBlock L j) ∧
      ‖OB * OL * OR - vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω))‖ ≤
        C₁ * Real.exp (-(m / ξ')))
    {k₀ : ℕ}
    (hk₀ : ∀ j ∈ Finset.Ico 1 L,
      Real.exp (2 * ManyBody.regionEntropy (X := fun _ ↦ Fin q) Ω (leftBlock L j)) / 2 ≤
        k₀)
    {k' : ℕ} (hk' : k₀ ≤ k') :
    let P : ∀ k : ℕ, LeftBlockMatrix L q k := fun k ↦
      (ManyBody.regionState_isHermitian (X := fun _ ↦ Fin q) (leftBlock L k)
        Ω).leadingEigenprojection k'
    let Φ := sequentialTruncation P (L - 1) Ω
    IsOpenMPS L q k' (fun x ↦ Φ x) ∧
      ‖Φ - Ω‖ ^ 2 ≤ ((L - 1 : ℕ) : ℝ) *
        (4 * C₁ ^ 2 * exp (2 / ξ') * ((k' : ℝ) / k₀) ^ (-1 / (ξ' * log q))) := by
  intro P Φ
  rcases Nat.lt_or_ge L 2 with hL | hL
  · -- Without an internal cut there is nothing to truncate.
    refine ⟨(isOpenMPS_sequentialTruncation_leadingEigenprojection Ω hΩ k').1, ?_⟩
    have h := norm_sequentialTruncation_leadingEigenprojection_sub_sq_le Ω hΩ k'
    rw [Finset.Ico_eq_empty (by omega), Finset.sum_empty] at h
    rw [show L - 1 = 0 by omega, Nat.cast_zero, zero_mul]
    exact h
  · have hk₀pos : (0 : ℝ) < k₀ :=
      lt_of_lt_of_le (by positivity) (hk₀ 1 (Finset.mem_Ico.mpr ⟨le_rfl, by omega⟩))
    rcases (NeZero.one_le (n := q)).lt_or_eq with hq | hq
    · refine isOpenMPS_norm_sub_sq_le_of_schmidtTail_geometric Ω hΩ
        (by exact_mod_cast hq) hξ' (by positivity) hk₀pos ?_ (by exact_mod_cast hk')
      intro j hj m n hn
      exact one_sub_kyFanNorm_le_of_factorization_of_entropy hq.le hΩ j (hfact j hj)
        (hk₀ j hj) m n (by exact_mod_cast hn)
    · -- For `q = 1` every left marginal is a `1 × 1` matrix of trace one, so the truncation onto
      -- `k' ≥ 1` leading eigenvectors is exact and `Φ = Ω`.
      subst hq
      obtain ⟨hmps, hnorm⟩ := isOpenMPS_sequentialTruncation_leadingEigenprojection Ω hΩ k'
      refine ⟨hmps, ?_⟩
      have hk'1 : 1 ≤ k' := le_trans (by exact_mod_cast hk₀pos) hk'
      have hzero : ∀ j ∈ Finset.Ico 1 L, Real.sqrt (1 -
          (ManyBody.regionState_isHermitian (X := fun _ ↦ Fin 1) (leftBlock L j)
            Ω).kyFanNorm k') = 0 := by
        intro j _
        refine Real.sqrt_eq_zero'.2 ?_
        have hpsd := ManyBody.regionState_posSemidef (X := fun _ ↦ Fin 1) (leftBlock L j) Ω
        have hcard := hpsd.isHermitian.kyFanNorm_card_eq_trace_re
        rw [ManyBody.trace_regionState, hΩ] at hcard
        have hc1 : Fintype.card (ManyBody.RegionConfig (fun _ ↦ Fin 1) (leftBlock L j)) ≤ k' :=
          (Fintype.card_le_one_iff_subsingleton.2 inferInstance).trans hk'1
        have := hpsd.kyFanNorm_mono hc1
        simp only [one_pow, Complex.ofReal_one, Complex.one_re] at hcard
        linarith
      rw [Finset.sum_congr rfl hzero, Finset.sum_const_zero] at hnorm
      rw [le_antisymm hnorm (norm_nonneg _)]
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
      positivity

/-- **Matrix product state from the entropy of the cuts, from Lemma 1 (stage theorem).** The
same bound as `isOpenMPS_norm_sub_sq_le_of_factorization_of_entropy`, with the approximate
factorization at every internal cut `j` and every length `m` in the form of the conclusion of
Lemma 1, `IsFactorizationAt Ω j m (C₁ e^{-m/ξ'})`. Hastings, arXiv:0705.2024v4, lines 246–267
and 505–557. -/
theorem isOpenMPS_norm_sub_sq_le_of_isFactorizationAt_of_entropy [NeZero q]
    {Ω : EuclideanSpace ℂ (Fin L → Fin q)} (hΩ : ‖Ω‖ = 1) {ξ' C₁ : ℝ} (hξ' : 0 < ξ')
    (hfact : ∀ j ∈ Finset.Ico 1 L, ∀ m : ℕ, j + m ≤ L →
      ∃ OB OL OR : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ,
        IsFactorizationAt Ω j m (C₁ * Real.exp (-(m / ξ'))) OB OL OR)
    {k₀ : ℕ}
    (hk₀ : ∀ j ∈ Finset.Ico 1 L,
      Real.exp (2 * ManyBody.regionEntropy (X := fun _ ↦ Fin q) Ω (leftBlock L j)) / 2 ≤
        k₀)
    {k' : ℕ} (hk' : k₀ ≤ k') :
    let P : ∀ k : ℕ, LeftBlockMatrix L q k := fun k ↦
      (ManyBody.regionState_isHermitian (X := fun _ ↦ Fin q) (leftBlock L k)
        Ω).leadingEigenprojection k'
    let Φ := sequentialTruncation P (L - 1) Ω
    IsOpenMPS L q k' (fun x ↦ Φ x) ∧
      ‖Φ - Ω‖ ^ 2 ≤ ((L - 1 : ℕ) : ℝ) *
        (4 * C₁ ^ 2 * exp (2 / ξ') * ((k' : ℝ) / k₀) ^ (-1 / (ξ' * log q))) :=
  isOpenMPS_norm_sub_sq_le_of_factorization_of_entropy hΩ hξ'
    (fun j hj m hm ↦ by
      obtain ⟨OB, OL, OR, hF⟩ := hfact j hj m hm
      exact ⟨OB, OL, OR, exists_factorization_of_isFactorizationAt hF⟩)
    hk₀ hk'

end TNLean.MPS.AreaLaw.Hastings

end MPSFromEntropy

section MPSGroundState

open scoped Matrix.Norms.L2Operator

open Matrix Real

open ManyBody (IsGapped groundSpace ChainInteraction)

namespace TNLean.MPS.AreaLaw.Hastings

variable {L q R : ℕ} {J : ℝ}

/-- **Matrix product state approximation of the gapped ground state, from Lemma 1 (stage
theorem).** Let `Ω` be a gapped ground vector of a finite-range Hamiltonian `h` on the chain
of `L` sites with local dimension `q ≥ 1`, around which Lemma 1 holds with constants `ξ' > 0`
and `C₁ ≥ 1`. With `k₀ = ⌈exp(2 S_max)/2⌉` for the area-law bound
`S_max = areaLawBound ξ' C₁ q`, for every `k' ≥ k₀` the truncation `Φ` onto the `k'` leading
eigenvectors at every cut is an open-boundary matrix product state of bond dimension at most
`k'` with
`‖Φ - Ω‖² ≤ (L - 1) 4 C₁² e^{2/ξ'} (k'/k₀)^{-1/(ξ' log q)}`.
Hastings, arXiv:0705.2024v4, lines 505–557, with the constants of the module docstring. -/
theorem isOpenMPS_norm_sub_sq_le_of_gappedGroundState [NeZero q] (h : ChainInteraction L q R)
    {E₀ Δ : ℝ} {Ω : EuclideanSpace ℂ (Fin L → Fin q)}
    (hΩ : ‖Ω‖ = 1) (hgap : IsGapped h.hamiltonian E₀ Δ)
    (hspan : groundSpace h.hamiltonian E₀ = Submodule.span ℂ {Ω})
    {ξ' C₁ : ℝ} (hξ' : 0 < ξ') (hC₁ : 1 ≤ C₁)
    (hfact : ∀ c l : ℕ, c + l ≤ L → ∃ OB OL OR : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ,
      IsFactorizationAt Ω c l (C₁ * Real.exp (-(l / ξ'))) OB OL OR)
    {k' : ℕ} (hk' : ⌈Real.exp (2 * areaLawBound ξ' C₁ q) / 2⌉₊ ≤ k') :
    let k₀ := ⌈Real.exp (2 * areaLawBound ξ' C₁ q) / 2⌉₊
    let P : ∀ k : ℕ, LeftBlockMatrix L q k := fun k ↦
      (ManyBody.regionState_isHermitian (X := fun _ ↦ Fin q) (leftBlock L k)
        Ω).leadingEigenprojection k'
    let Φ := sequentialTruncation P (L - 1) Ω
    IsOpenMPS L q k' (fun x ↦ Φ x) ∧
      ‖Φ - Ω‖ ^ 2 ≤ ((L - 1 : ℕ) : ℝ) *
        (4 * C₁ ^ 2 * exp (2 / ξ') * ((k' : ℝ) / k₀) ^ (-1 / (ξ' * log q))) := by
  intro k₀ P Φ
  refine isOpenMPS_norm_sub_sq_le_of_isFactorizationAt_of_entropy hΩ hξ'
    (fun j _ m hm ↦ hfact j m hm) (fun j _ ↦ ?_) hk'
  -- The area law bounds the entropy of every initial segment by `S_max`.
  have hS := regionEntropy_prefix_le_of_factorization h hΩ hgap hspan hξ' hC₁ hfact j
  rw [← leftBlock_eq_interval] at hS
  calc Real.exp (2 * ManyBody.regionEntropy (X := fun _ ↦ Fin q) Ω (leftBlock L j)) / 2
      ≤ Real.exp (2 * areaLawBound ξ' C₁ q) / 2 := by gcongr
    _ ≤ k₀ := Nat.le_ceil _

/-- **Hastings' matrix product state approximation of the gapped ground state.** Let `R` be a
range and `κ > 6`. There is a constant `K ≥ 0`, depending only on `R` and `κ`, with the
following property. Let `J ≥ 0` bound the interaction terms, let `ΔE > 0` be a gap, and put
`ξ̂ = lemmaOneLength R (J/ΔE) 1`, `ξ' = κ ξ̂` and `C₁ = max (K ξ̂³) 1`. For every chain of `L`
sites with local dimension `q ≥ 1` and every gapped ground vector `Ω` of a chain Hamiltonian
of range `R` and term norm `J` with gap `ΔE`, with `k₀ = ⌈exp(2 S_max)/2⌉` for
`S_max = areaLawBound ξ' C₁ q`, the truncation `Φ` onto the `k'` leading eigenvectors at every
cut, for every `k' ≥ k₀`, is an open-boundary matrix product state of bond dimension at most
`k'` with `‖Φ - Ω‖² ≤ (L - 1) 4 C₁² e^{2/ξ'} (k'/k₀)^{-1/(ξ' log q)}`. The constants depend
only on `R`, `κ`, `J/ΔE` and `q`, not on `L`. Hastings, arXiv:0705.2024v4, lines 505–557, with
`C₁` polynomial in `ξ̂` as at lines 258–262 and the restrictions of the module docstring. -/
theorem exists_isOpenMPS_norm_sub_sq_le_of_isGapped (R : ℕ) {κ : ℝ} (hκ : 6 < κ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {J ΔE : ℝ}, 0 ≤ J → 0 < ΔE →
      ∀ {L q : ℕ} [NeZero q] (h : ChainInteraction L q R) (_ : ∀ X, (h.term X).IsHermitian)
          (_ : ∀ X, ‖h.term X‖ ≤ J) {E₀ : ℝ}
      {Ω : EuclideanSpace ℂ (Fin L → Fin q)}, ‖Ω‖ = 1 → IsGapped h.hamiltonian E₀ ΔE →
      groundSpace h.hamiltonian E₀ = Submodule.span ℂ {Ω} →
      ∀ {k' : ℕ}, ⌈Real.exp (2 * areaLawBound (κ * lemmaOneLength R (J / ΔE) 1)
          (max (K * lemmaOneLength R (J / ΔE) 1 ^ 3) 1) q) / 2⌉₊ ≤ k' →
        let k₀ := ⌈Real.exp (2 * areaLawBound (κ * lemmaOneLength R (J / ΔE) 1)
          (max (K * lemmaOneLength R (J / ΔE) 1 ^ 3) 1) q) / 2⌉₊
        let P : ∀ k : ℕ, LeftBlockMatrix L q k := fun k ↦
          (ManyBody.regionState_isHermitian (X := fun _ ↦ Fin q) (leftBlock L k)
            Ω).leadingEigenprojection k'
        let Φ := sequentialTruncation P (L - 1) Ω
        IsOpenMPS L q k' (fun x ↦ Φ x) ∧
          ‖Φ - Ω‖ ^ 2 ≤ ((L - 1 : ℕ) : ℝ) *
            (4 * (max (K * lemmaOneLength R (J / ΔE) 1 ^ 3) 1) ^ 2 *
              exp (2 / (κ * lemmaOneLength R (J / ΔE) 1)) *
              ((k' : ℝ) / k₀) ^ (-1 / ((κ * lemmaOneLength R (J / ΔE) 1) * log q))) := by
  obtain ⟨K, hK0, hF⟩ := exists_projectorFactorization_pow R hκ
  refine ⟨K, hK0, fun {J ΔE} hJ hΔ {L q} _ h hh hhJ {E₀} {Ω} hΩ hgap hspan {k'} hk' ↦ ?_⟩
  have hξ'0 : 0 < κ * lemmaOneLength R (J / ΔE) 1 :=
    mul_pos (by linarith) (lemmaOneLength_pos R _ 1)
  refine isOpenMPS_norm_sub_sq_le_of_gappedGroundState h hΩ hgap hspan hξ'0
      (le_max_right _ _)
    (fun c l _ ↦ ?_) hk'
  obtain ⟨OB, OL, OR, hf⟩ := hF hJ hΔ h hh hhJ hΩ hgap hspan c l
  exact ⟨OB, OL, OR, hf.mono
    (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)⟩

/-- **Hastings' matrix product state approximation at the printed rate `ξ' = 6ξ`.** There is a
constant `K ≥ 0`, depending only on `R`, with the following property. Let `J ≥ 0` bound the
interaction terms, let `ΔE > 0` be a gap, and put `ζ = lemmaOneEndpointLength R J ΔE =
(5/4) ξ̂`, `ξ' = 6ζ` and `C₁ = max (K ζ³) 1`. Then the conclusion of
`exists_isOpenMPS_norm_sub_sq_le_of_isGapped` holds with these `ξ'` and `C₁`.
Hastings, arXiv:0705.2024v4, lines 505–557, with `ξ' = 6ξ` (lines 141–142) for `ξ = ζ`, `C₁`
polynomial in `ζ` (lines 258–262), and the restriction on `ζ` of the module docstring. -/
theorem exists_isOpenMPS_norm_sub_sq_le_of_isGapped_endpoint (R : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {J ΔE : ℝ}, 0 ≤ J → 0 < ΔE →
      ∀ {L q : ℕ} [NeZero q] (h : ChainInteraction L q R) (_ : ∀ X, (h.term X).IsHermitian)
          (_ : ∀ X, ‖h.term X‖ ≤ J) {E₀ : ℝ}
      {Ω : EuclideanSpace ℂ (Fin L → Fin q)}, ‖Ω‖ = 1 → IsGapped h.hamiltonian E₀ ΔE →
      groundSpace h.hamiltonian E₀ = Submodule.span ℂ {Ω} →
      ∀ {k' : ℕ}, ⌈Real.exp (2 * areaLawBound (6 * lemmaOneEndpointLength R J ΔE)
          (max (K * lemmaOneEndpointLength R J ΔE ^ 3) 1) q) / 2⌉₊ ≤ k' →
        let k₀ := ⌈Real.exp (2 * areaLawBound (6 * lemmaOneEndpointLength R J ΔE)
          (max (K * lemmaOneEndpointLength R J ΔE ^ 3) 1) q) / 2⌉₊
        let P : ∀ k : ℕ, LeftBlockMatrix L q k := fun k ↦
          (ManyBody.regionState_isHermitian (X := fun _ ↦ Fin q) (leftBlock L k)
            Ω).leadingEigenprojection k'
        let Φ := sequentialTruncation P (L - 1) Ω
        IsOpenMPS L q k' (fun x ↦ Φ x) ∧
          ‖Φ - Ω‖ ^ 2 ≤ ((L - 1 : ℕ) : ℝ) *
            (4 * (max (K * lemmaOneEndpointLength R J ΔE ^ 3) 1) ^ 2 *
              exp (2 / (6 * lemmaOneEndpointLength R J ΔE)) *
              ((k' : ℝ) / k₀) ^ (-1 / ((6 * lemmaOneEndpointLength R J ΔE) * log q))) := by
  obtain ⟨K, hK0, hF⟩ := exists_projectorFactorization_endpoint R
  refine ⟨K, hK0, fun {J ΔE} hJ hΔ {L q} _ h hh hhJ {E₀} {Ω} hΩ hgap hspan {k'} hk' ↦ ?_⟩
  have hζ0 : 0 < 6 * lemmaOneEndpointLength R J ΔE := by
    rw [lemmaOneEndpointLength_eq]; linarith [lemmaOneLength_pos R (J / ΔE) 1]
  refine isOpenMPS_norm_sub_sq_le_of_gappedGroundState h hΩ hgap hspan hζ0 (le_max_right _ _)
    (fun c l _ ↦ ?_) hk'
  obtain ⟨OB, OL, OR, hf⟩ := hF hJ hΔ h hh hhJ hΩ hgap hspan c l
  exact ⟨OB, OL, OR, hf.mono
    (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)⟩

end TNLean.MPS.AreaLaw.Hastings

end MPSGroundState
