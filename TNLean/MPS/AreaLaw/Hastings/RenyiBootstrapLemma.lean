/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.Hastings.BootstrapLemma
import TNLean.MPS.AreaLaw.Hastings.SchmidtRankRenyiBootstrap

/-!
# The Rényi form of Hastings' bootstrap lemma

At the end of the proof of Lemma 2, Hastings, *An area law for one-dimensional quantum systems*
(arXiv:0705.2024v4, `References/0705.2024/law16.tex`, lines 392–410), notes that the argument
extends to the Rényi entropies `S_α(ρ⁰_{1,j}) = (1 − α)⁻¹ ln tr (ρ⁰_{1,j})^α` whenever
`exp(−2α/ξ') (D²)^{1−α} < 1`. The bound then differs from the von Neumann bound only in the
function replacing `F(ξ', D)`.

This file proves that statement on Hastings' own hypotheses. The Schmidt-tail constraints come
from Lemma 1 exactly as for the von Neumann entropy (`ChainBootstrap.lean`), and the Rényi
entropy under them is bounded by `renyiEntropy_le_of_schmidtRank_mixtures`. Lemma 1 is supplied
at the printed rate by `exists_projectorFactorization_endpoint`, with the length
`ζ = lemmaOneEndpointLength R J ΔE`, the rate `ξ' = 6ζ` and the constant `C₁ = K ζ³`, as in
`exists_entropy_le_of_overlap_schmidtRank_mixture`.

The function replacing `F(ξ', D)` is
`4 ln D − ln(1 − (D²)^{1−α} e^{−2α/ξ'}) / (1 − α)`.

**Scope restriction (quantitative bounds):** `exists_renyiEntropy_le_of_overlap_schmidtRank_mixture`
inherits the quantitative restriction of the formalized Lemma 1. Its length
`ζ = (5/4) lemmaOneLength R (J/ΔE) 1` comes from the chain Lieb–Robinson estimate with the
velocity raised by `5/4`, whose prefactor grows with `J` and whose second operator acts on one
site, so `ζ` is not shown to be the source's `max(2v/ΔE, ξ_C)` for a Lieb–Robinson pair in the
source's sense (lines 96–112). Documented in `docs/paper-gaps/hastings07_lemma1_decay_length.tex`
and `docs/paper-gaps/hastings07_gaussian_average_exponent.tex`.

**Scope restriction (orders):** the Rényi bound is proved for orders `0 < α < 1`. Order `1` is
the von Neumann entropy, bounded by `exists_entropy_le_of_overlap_schmidtRank_mixture`. Orders
`α > 1`, for which the convergence condition always holds, are not covered here. Documented in
`docs/paper-gaps/hastings07_renyi_bootstrap_orders.tex`.

## Main results

* `TNLean.MPS.AreaLaw.Hastings.renyiEntropy_le_of_overlap_schmidtRank_mixture_of_isFactorizationAt`:
  the Rényi bound from Lemma 1 at one cut.
* `TNLean.MPS.AreaLaw.exists_renyiEntropy_le_of_overlap_schmidtRank_mixture`: the Rényi form of
  Lemma 2 for a gapped chain.
-/

namespace TNLean.MPS.AreaLaw.Hastings

open TNLean.MPS.AreaLaw Matrix
open scoped InnerProductSpace Matrix.Norms.L2Operator ComplexOrder

variable {L q : ℕ}

/-- **The Rényi bootstrap bound from Lemma 1 at one cut.** Let `Ω` be a unit vector on the chain
of `L` sites with local dimension `q ≥ 2`, and suppose that at the cut `j` and every length `m`
there is a factorization `IsFactorizationAt Ω j m (C₁ e^{-m/ξ'})`, with `ξ' > 0` and `C₁ ≥ 1`.
Let `ρ = ∑ wᵢ |ψᵢ⟩⟨ψᵢ|` be a mixture of unit trace of vectors of cut rank at most `k` with overlap
`P > 0` with `Ω`. For `0 < α < 1` with `(q²)^{1−α} e^{−2α/ξ'} < 1`, the Rényi entropy of order
`α` of the first `j` sites is at most
`ln k + ξ' ln(2 C₁²/P) ln q + 4 ln q − ln(1 − (q²)^{1−α} e^{−2α/ξ'}) / (1 − α)`.
Hastings, arXiv:0705.2024v4, Lemma 2 (`ble`), the Rényi extension at lines 392–410. -/
theorem renyiEntropy_le_of_overlap_schmidtRank_mixture_of_isFactorizationAt (hq : 2 ≤ q)
    {Ω : EuclideanSpace ℂ (Fin L → Fin q)} (hΩ : ‖Ω‖ = 1) (j : ℕ) {ξ' C₁ α : ℝ} (hξ : 0 < ξ')
    (hC₁ : 1 ≤ C₁) (hα0 : 0 < α) (hα1 : α < 1)
    (hconv : ((q : ℝ) ^ 2) ^ (1 - α) * Real.exp (-(2 * α / ξ')) < 1)
    (hfact : ∀ m : ℕ, ∃ OB OL OR : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ,
      IsFactorizationAt Ω j m (C₁ * Real.exp (-(m / ξ'))) OB OL OR)
    {k r : ℕ} (hk : 1 ≤ k) (w : Fin r → ℝ) (ψ : Fin r → EuclideanSpace ℂ (Fin L → Fin q))
    (hw : ∀ i, 0 ≤ w i) (hrank : ∀ i, (cutMatrix (ψ i) j).rank ≤ k)
    (hnorm : ∑ i, w i * ‖ψ i‖ ^ 2 = 1) {P : ℝ} (hP : 0 < P)
    (hPdef : ∑ i, w i * ‖⟪ψ i, Ω⟫_ℂ‖ ^ 2 = P) :
    renyiEntropy (cutMatrix Ω j * (cutMatrix Ω j)ᴴ)
        (posSemidef_self_mul_conjTranspose (cutMatrix Ω j)).isHermitian α ≤
      Real.log k + ξ' * Real.log (2 * C₁ ^ 2 / P) * Real.log q + 4 * Real.log q -
        Real.log (1 - ((q : ℝ) ^ 2) ^ (1 - α) * Real.exp (-(2 * α / ξ'))) / (1 - α) := by
  classical
  have hq1 : 1 ≤ q := by omega
  have hfact' : ∀ m : ℕ, j + m ≤ L → ∃ (OB OL OR : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
      (SB SL SR : Finset (Fin L)),
      Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) OB SB ∧ SB ⊆ leftBlock L (j + m) ∧
      Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) OL SL ∧ SL ⊆ leftBlock L j ∧
      Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) OR SR ∧ Disjoint SR (leftBlock L j) ∧
      ‖OB * OL * OR - vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω))‖ ≤
        C₁ * Real.exp (-(m / ξ')) := fun m _ ↦ by
    obtain ⟨OB, OL, OR, hF⟩ := hfact m
    obtain ⟨SB, SL, SR, h⟩ := exists_factorization_of_isFactorizationAt hF
    exact ⟨OB, OL, OR, SB, SL, SR, h⟩
  set cv : EuclideanSpace ℂ (Fin L → Fin q) → _ := fun x ↦
    WithLp.ofLp (Entropy.cutVector (n := fun _ : Fin L ↦ q) (leftBlock L j) x) with hcv
  have hdot : ∀ x y, star (cv x) ⬝ᵥ cv y = ⟪x, y⟫_ℂ := fun x y ↦ star_cutVector_dotProduct j x y
  have hnormsq : ∀ x : EuclideanSpace ℂ (Fin L → Fin q), (star (cv x) ⬝ᵥ cv x).re = ‖x‖ ^ 2 := by
    intro x
    rw [hdot, inner_self_eq_norm_sq_to_K]
    norm_cast
  set Ψ := cv Ω with hΨdef
  have hΨ : star Ψ ⬝ᵥ Ψ = 1 := by
    rw [hdot, inner_self_eq_norm_sq_to_K, hΩ]; norm_num
  have hP1 : P ≤ 1 := by
    rw [← hPdef, ← hnorm]
    refine Finset.sum_le_sum fun i _ ↦ mul_le_mul_of_nonneg_left ?_ (hw i)
    calc ‖⟪ψ i, Ω⟫_ℂ‖ ^ 2 ≤ (‖ψ i‖ * ‖Ω‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (norm_inner_le_norm _ _) 2
      _ = ‖ψ i‖ ^ 2 := by rw [hΩ, mul_one]
  have hc : 1 ≤ 2 * C₁ ^ 2 / P := by
    rw [le_div_iff₀ hP]; nlinarith
  exact renyiEntropy_le_of_schmidtRank_mixtures Ψ hΨ hk hq hξ hc hα0 hα1 hconv (fun s hs ↦ by
    obtain ⟨r', w', ψ', hw', hrank', hpos', hov'⟩ :=
      exists_mixture_rank_cutMatrix_le_overlap_of_factorization hq1 hΩ j hfact' hk w ψ hw
        hrank hnorm hP hPdef hs
    refine ⟨r', w', fun i ↦ cv (ψ' i), hw', hrank', ?_, ?_⟩
    · simp only [hnormsq]; exact hpos'
    · simp only [hnormsq]; simp only [hΨdef, hdot]; exact hov')

/-- For local dimension `q = 1` the Rényi entropy of order `0 < α < 1` of the first `j` sites of a
unit vector is at most zero: the reduced density matrix acts on a space of dimension one. -/
theorem renyiEntropy_cutMatrix_nonpos_of_one {Ω : EuclideanSpace ℂ (Fin L → Fin 1)} (hΩ : ‖Ω‖ = 1)
    (j : ℕ) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    renyiEntropy (cutMatrix Ω j * (cutMatrix Ω j)ᴴ)
        (posSemidef_self_mul_conjTranspose (cutMatrix Ω j)).isHermitian α ≤ 0 := by
  set Ψ := WithLp.ofLp (Entropy.cutVector (n := fun _ : Fin L ↦ 1) (leftBlock L j) Ω)
  have hΨ : star Ψ ⬝ᵥ Ψ = 1 := by
    rw [star_cutVector_dotProduct, inner_self_eq_norm_sq_to_K, hΩ]; norm_num
  obtain ⟨hp0, hpsum⟩ := eigenvalues₀_nonneg_and_sum_eq_one Ψ hΨ
  change renyiEntropy (schmidtCoeffMatrix Ψ * (schmidtCoeffMatrix Ψ)ᴴ)
    (posSemidef_self_mul_conjTranspose (schmidtCoeffMatrix Ψ)).isHermitian α ≤ 0
  rw [renyiEntropy_eq_log_sum_eigenvalues₀_rpow _ hα0.ne' hα1.ne]
  have hsum := sum_rpow_le_card_rpow_mul_sum_rpow Finset.univ _ (fun a _ ↦ hp0 a) hα0.le hα1.le
  rw [hpsum, Real.one_rpow, mul_one, Finset.card_univ, Fintype.card_fin] at hsum
  have hc : ((Fintype.card ((leftBlock L j) → Fin 1) : ℕ) : ℝ) ^ (1 - α) = 1 := by simp
  have hsum' := hsum.trans hc.le
  have hlog : Real.log (∑ a, (posSemidef_self_mul_conjTranspose
      (schmidtCoeffMatrix Ψ)).isHermitian.eigenvalues₀ a ^ α) ≤ 0 :=
    Real.log_nonpos (Finset.sum_nonneg fun a _ ↦ Real.rpow_nonneg (hp0 a) _) hsum'
  exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr (by linarith)) hlog

end TNLean.MPS.AreaLaw.Hastings

namespace TNLean.MPS.AreaLaw

open Hastings Matrix TNLean.Lattice
open scoped InnerProductSpace ComplexOrder

/-- **Hastings' bootstrap lemma for Rényi entropies (Lemma 2, lines 392–410).** There is a constant
`K ≥ 1`, depending only on the range `R`, with the following property. Let `H` be a chain
Hamiltonian of range `R` and term norm at most `J ≥ 0` with a unique ground state `Ω` and gap
`ΔE > 0`, on `L` sites with local dimension `q`, and let `ζ = lemmaOneEndpointLength R J ΔE`,
`ξ' = 6ζ` and `C₁ = K ζ³`. Let `0 < α < 1` with `(q²)^{1−α} e^{−2α/ξ'} < 1`. For every cut `j`
and every mixture `ρ = ∑ wᵢ |ψᵢ⟩⟨ψᵢ|` of unit trace of vectors of Schmidt rank at most `k ≥ 1`
across the cut with `⟨Ω, ρ Ω⟩ = P > 0`, the Rényi entropy of order `α` of the first `j` sites
is at most `ln k + ξ' ln(2 C₁²/P) ln q + 4 ln q − ln(1 − (q²)^{1−α} e^{−2α/ξ'}) / (1 − α)`.
Hastings, arXiv:0705.2024v4, Lemma 2 (`ble`), lines 280–311 and 392–410, at the printed rate
`ξ' = 6ξ` (lines 139–142) for `ξ = ζ`, with `C₁` polynomial in the length (lines 258–262) and
the restrictions of the module docstring. -/
theorem exists_renyiEntropy_le_of_overlap_schmidtRank_mixture (R : ℕ) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ {J ΔE : ℝ}, 0 ≤ J → 0 < ΔE →
      ∀ {L q : ℕ} [NeZero q] (h : ChainHamiltonian L q R J) {E₀ : ℝ}
      {Ω : EuclideanSpace ℂ (Fin L → Fin q)}, IsGappedGroundState h.operator E₀ Ω ΔE →
      ∀ {α : ℝ}, 0 < α → α < 1 →
      ((q : ℝ) ^ 2) ^ (1 - α) * Real.exp (-(2 * α / (6 * lemmaOneEndpointLength R J ΔE))) < 1 →
      ∀ (j : ℕ) {k r : ℕ}, 1 ≤ k → ∀ (w : Fin r → ℝ)
        (ψ : Fin r → EuclideanSpace ℂ (Fin L → Fin q)), (∀ i, 0 ≤ w i) →
        (∀ i, (cutMatrix (ψ i) j).rank ≤ k) → ∑ i, w i * ‖ψ i‖ ^ 2 = 1 →
        ∀ {P : ℝ}, 0 < P → ∑ i, w i * ‖⟪ψ i, Ω⟫_ℂ‖ ^ 2 = P →
        renyiEntropy (cutMatrix Ω j * (cutMatrix Ω j)ᴴ)
            (posSemidef_self_mul_conjTranspose (cutMatrix Ω j)).isHermitian α ≤
          Real.log k + 6 * lemmaOneEndpointLength R J ΔE *
            Real.log (2 * (K * lemmaOneEndpointLength R J ΔE ^ 3) ^ 2 / P) * Real.log q +
            4 * Real.log q -
            Real.log (1 - ((q : ℝ) ^ 2) ^ (1 - α) *
              Real.exp (-(2 * α / (6 * lemmaOneEndpointLength R J ΔE)))) / (1 - α) := by
  obtain ⟨K, -, hF⟩ := exists_projectorFactorization_endpoint R
  refine ⟨max K 1, le_max_right _ _, ?_⟩
  intro J ΔE hJ hΔ L q _ h E₀ Ω hgs α hα0 hα1 hconv j k r hk w ψ hw hrank hnorm P hP hPdef
  have hΩ : ‖Ω‖ = 1 := hgs.1
  have h16 := (sixteen_le_lemmaOneLength_and_le R (div_nonneg hJ hΔ.le)).1
  have hζ : 20 ≤ lemmaOneEndpointLength R J ΔE := by
    rw [lemmaOneEndpointLength_eq]; linarith
  have hξ : 0 < 6 * lemmaOneEndpointLength R J ΔE := by linarith
  have hC₁ : 1 ≤ max K 1 * lemmaOneEndpointLength R J ΔE ^ 3 :=
    one_le_mul_of_one_le_of_one_le (le_max_right _ _) (one_le_pow₀ (by linarith))
  rcases lt_or_ge q 2 with hq | hq
  · -- For `q = 1` the Rényi entropy is at most zero and the right side is nonnegative.
    have hq1 : q = 1 := by have := NeZero.one_le (n := q); omega
    subst hq1
    refine (renyiEntropy_cutMatrix_nonpos_of_one hΩ j hα0 hα1).trans ?_
    have hk0 : 0 ≤ Real.log k := Real.log_nonneg (by exact_mod_cast hk)
    simp only [Nat.cast_one, one_pow, Real.one_rpow, one_mul, Real.log_one, mul_zero,
      add_zero] at hconv ⊢
    have hx0 := Real.exp_pos (-(2 * α / (6 * lemmaOneEndpointLength R J ΔE)))
    have hlog : Real.log (1 - Real.exp (-(2 * α / (6 * lemmaOneEndpointLength R J ΔE)))) ≤ 0 :=
      Real.log_nonpos (by linarith) (by linarith)
    have h2 : Real.log (1 - Real.exp (-(2 * α / (6 * lemmaOneEndpointLength R J ΔE)))) /
        (1 - α) ≤ 0 := div_nonpos_of_nonpos_of_nonneg hlog (by linarith)
    linarith
  · exact renyiEntropy_le_of_overlap_schmidtRank_mixture_of_isFactorizationAt hq hΩ j hξ hC₁
      hα0 hα1 hconv (fun m ↦ by
        obtain ⟨OB, OL, OR, hFm⟩ := hF hJ hΔ h hgs j m
        exact ⟨OB, OL, OR, hFm.mono (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_pos (by linarith) 3).le)
          (Real.exp_pos _).le)⟩) hk w ψ hw hrank hnorm hP hPdef

end TNLean.MPS.AreaLaw
