/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.Hastings.ChainBootstrap
import TNLean.MPS.AreaLaw.SequentialTruncation

/-!
# Hastings' Schmidt-tail constraint on the chain

Let `Ω` be a unit vector on the chain of `L` sites and `ρ` its marginal on the first `j` sites.
If the `k` largest eigenvalues of `ρ` carry weight at least `1/2`, then under the approximate
factorization of Lemma 1 the eigenvalues of `ρ` beyond the `k q^{2m}` largest add up to at most
`4 C₁² e^{-2m/ξ'}` (eq. `constraint` with `P = 1/2`).

The mixture of the bootstrap is the single state `E Ω`, where `E` projects the first `j` sites
onto the `k` leading eigenvectors of `ρ`. Its overlap with `Ω` is the weight of those
eigenvalues.

**Stage:** the theorem takes the weight bound of the `k` leading eigenvalues as a hypothesis.
For `k ≥ exp(2 S(ρ))/2` it is Hastings' bound of lines 526–535 (eq. `k0Ent`).

## Main results

* `TNLean.MPS.AreaLaw.Hastings.one_sub_kyFanNorm_le_of_factorization`: eq. `constraint`.

## References

Hastings, arXiv:0705.2024v4, section "Matrix Product States", lines 536–544 of
`References/0705.2024/law16.tex`.
-/

open Matrix
open scoped InnerProductSpace Matrix.Norms.L2Operator ComplexOrder

namespace TNLean.MPS.AreaLaw.Hastings

open TNLean.MPS.AreaLaw

variable {L q : ℕ}

/-- **Hastings' Schmidt-tail constraint on the chain.** Let `Ω` be a unit vector on the chain of
`L` sites, `j` a cut and `ρ` the marginal of `Ω` on the first `j` sites. Assume the approximate
factorization of Lemma 1 with constant `C₁` and length `ξ'`, and that the `k` largest
eigenvalues of `ρ` add up to at least `1/2`. Then for every scale `m` and every `n ≥ k q^{2m}`
the eigenvalues of `ρ` beyond the `n` largest add up to at most `4 C₁² e^{-2m/ξ'}`.

Hastings, arXiv:0705.2024v4, lines 536–544, eq. `constraint` with `P = 1/2`.

**Stage:** the weight bound `hlead` on the `k` leading eigenvalues is a hypothesis. For
`k ≥ exp(2 S(ρ))/2` it is Hastings' bound of lines 526–535 (eq. `k0Ent`). -/
theorem one_sub_kyFanNorm_le_of_factorization (hq : 1 ≤ q)
    {Ω : EuclideanSpace ℂ (Fin L → Fin q)} (hΩ : ‖Ω‖ = 1) (j : ℕ) {ξ' C₁ : ℝ}
    (hfact : ∀ m : ℕ, j + m ≤ L → ∃ (OB OL OR : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
      (SB SL SR : Finset (Fin L)),
      Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) OB SB ∧ SB ⊆ leftBlock L (j + m) ∧
      Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) OL SL ∧ SL ⊆ leftBlock L j ∧
      Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) OR SR ∧ Disjoint SR (leftBlock L j) ∧
      ‖OB * OL * OR - vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω))‖ ≤
        C₁ * Real.exp (-(m / ξ')))
    {k : ℕ} (hk : 1 ≤ k)
    (hlead : 1 / 2 ≤ (Entropy.regionState_isHermitian (n := fun _ : Fin L ↦ q) (leftBlock L j)
      Ω).kyFanNorm k)
    (m n : ℕ) (hn : k * q ^ (2 * m) ≤ n) :
    1 - (Entropy.regionState_isHermitian (n := fun _ : Fin L ↦ q) (leftBlock L j) Ω).kyFanNorm n
      ≤ 4 * C₁ ^ 2 * Real.exp (-(2 * m) / ξ') := by
  classical
  set hρ := Entropy.regionState_isHermitian (n := fun _ : Fin L ↦ q) (leftBlock L j) Ω
    with hρdef
  have hρpsd := Entropy.regionState_posSemidef (n := fun _ : Fin L ↦ q) (leftBlock L j) Ω
  set e := Real.exp (-(2 * m) / ξ') with he
  have he' : Real.exp (-(2 * (m : ℝ) / ξ')) = e := by rw [he, neg_div]
  have hmono : hρ.kyFanNorm (k * q ^ (2 * m)) ≤ hρ.kyFanNorm n := hρpsd.kyFanNorm_mono hn
  -- The single state `E Ω`, with `E` the projection onto the `k` leading eigenvectors.
  set E := hρ.leadingEigenprojection k with hEdef
  have hspec := hρ.leadingEigenprojection_spec k
  have hE : IsStarProjection E :=
    ⟨hspec.2.1, Matrix.isHermitian_iff_isSelfAdjoint.mp hspec.1⟩
  set ψ0 := toEuclideanLin (Entropy.localLift (leftBlock L j) E) Ω with hψ0
  set P := ‖ψ0‖ ^ 2 with hPdef0
  have hPk : P = hρ.kyFanNorm k := by
    rw [hPdef0, hψ0, Entropy.norm_sq_toEuclideanLin_localLift_eq_trace hE]
    exact hspec.2.2.2.2.1
  have hP2 : 1 / 2 ≤ P := hPk ▸ hlead
  have hP : 0 < P := by linarith
  have hPP : Eᴴ * E = E := by
    have h := hE.isSelfAdjoint.star_eq
    rw [star_eq_conjTranspose] at h
    rw [h, hE.isIdempotentElem.eq]
  have hinner : ⟪ψ0, ψ0⟫_ℂ = ⟪Ω, ψ0⟫_ℂ := by
    rw [hψ0, ← LinearMap.adjoint_inner_right, ← toEuclideanLin_conjTranspose_eq_adjoint,
      ← Matrix.toEuclideanLin_mul_apply, ← Entropy.localLift_conjTranspose,
      ← Entropy.localLift_mul, hPP]
  have hov0 : ‖⟪ψ0, Ω⟫_ℂ‖ = P := by
    rw [norm_inner_symm, ← hinner, inner_self_eq_norm_sq_to_K, norm_pow]
    simp [hPdef0]
  -- The trivial case: the bound is at least one.
  by_cases hs : 2 * C₁ ^ 2 / P * Real.exp (-(2 * m / ξ')) < 1
  swap
  · push Not at hs
    have hc : 2 * C₁ ^ 2 / P ≤ 4 * C₁ ^ 2 := by
      rw [div_le_iff₀ hP]; nlinarith [sq_nonneg C₁]
    have hK0 : 0 ≤ hρ.kyFanNorm n := hρpsd.kyFanNorm_nonneg n
    rw [he'] at hs
    nlinarith [Real.exp_pos (-(2 * m) / ξ')]
  obtain ⟨r', w', ψ', hw', hrank', hpos', hov'⟩ :=
    exists_mixture_rank_cutMatrix_le_overlap_of_factorization hq hΩ j hfact hk
      (fun _ : Fin 1 ↦ 1 / P) (fun _ ↦ ψ0) (fun _ ↦ by positivity)
      (fun _ ↦ (rank_cutMatrix_localLift_le j E Ω).trans
        (hspec.2.2.2.1.trans_le (min_le_left _ _)))
      (by simp only [Finset.univ_unique, Finset.sum_singleton]; field_simp; exact hPdef0.symm) hP
      (by simp only [Finset.univ_unique, Finset.sum_singleton, hov0]; field_simp) hs
  -- Pass to the coefficient vector across the cut.
  set cv : EuclideanSpace ℂ (Fin L → Fin q) → _ := fun x ↦
    WithLp.ofLp (Entropy.cutVector (n := fun _ : Fin L ↦ q) (leftBlock L j) x) with hcv
  have hdot : ∀ x y, star (cv x) ⬝ᵥ cv y = ⟪x, y⟫_ℂ := fun x y ↦ star_cutVector_dotProduct j x y
  have hnormsq : ∀ x : EuclideanSpace ℂ (Fin L → Fin q), (star (cv x) ⬝ᵥ cv x).re = ‖x‖ ^ 2 := by
    intro x
    rw [hdot, inner_self_eq_norm_sq_to_K]
    norm_cast
  have hΨ : star (cv Ω) ⬝ᵥ cv Ω = 1 := by
    rw [hdot, inner_self_eq_norm_sq_to_K, hΩ]; norm_num
  have htail := one_sub_kyFanNorm_le_of_schmidtRank_mixture (cv Ω) hΨ
    (η := 2 * C₁ ^ 2 / P * Real.exp (-(2 * m / ξ'))) (by positivity) w'
    (fun i ↦ cv (ψ' i)) hw' hrank' (by simp only [hnormsq]; exact hpos')
    (by simp only [hnormsq]; simp only [hdot]; exact hov')
  -- The marginal is `C Cᴴ` for the cut matrix `C`.
  have hρeq : Entropy.regionState (n := fun _ : Fin L ↦ q) (leftBlock L j) Ω =
      cutMatrix Ω j * (cutMatrix Ω j)ᴴ := by
    unfold Entropy.regionState
    exact partialTraceRight_vecMulVec_eq _
  have hkf : ∀ {A B : Matrix (Entropy.RegionConfig (fun _ : Fin L ↦ q) (leftBlock L j))
      (Entropy.RegionConfig (fun _ : Fin L ↦ q) (leftBlock L j)) ℂ} (_ : A = B)
      (hA : A.IsHermitian) (hB : B.IsHermitian), hA.kyFanNorm (k * q ^ (2 * m)) =
        hB.kyFanNorm (k * q ^ (2 * m)) := by
    rintro A B rfl hA hB; rfl
  have hkey : hρ.kyFanNorm (k * q ^ (2 * m)) = (posSemidef_self_mul_conjTranspose
      (schmidtCoeffMatrix (cv Ω))).isHermitian.kyFanNorm (k * q ^ (2 * m)) :=
    hkf hρeq _ _
  have hc : 2 * C₁ ^ 2 / P ≤ 4 * C₁ ^ 2 := by
    rw [div_le_iff₀ hP]; nlinarith [sq_nonneg C₁]
  rw [he'] at htail
  nlinarith [Real.exp_pos (-(2 * m) / ξ')]

end TNLean.MPS.AreaLaw.Hastings
