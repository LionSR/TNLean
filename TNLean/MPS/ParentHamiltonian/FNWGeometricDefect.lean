/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.FNWProjectorDefect

/-!
# Geometric form of the FNW projector estimate

Nachtergaele, arXiv:cond-mat/9410110, imports from Fannes--Nachtergaele--Werner the
bound

\[
  \lVert G_{\Lambda_n}G_{\Lambda_{n+1}\setminus\Lambda_{n-l}}-G_{\Lambda_{n+1}}\rVert
    \le c\lambda^l\,\frac{1+c\lambda^l}{1-c\lambda^l},
\]

stated at lines 1180--1194 and again for the best overlap constant \(A^\alpha_m\) at
lines 2401--2412, display `boundAm`. The prescription there is that \(\lambda\) may be
any number with \(\lambda_i<\lambda<1\) for every eigenvalue \(\lambda_i\ne 1\) of the
transfer operator.

This module composes the three already-proved ingredients into that display. Fannes--
Nachtergaele--Werner, *Communications in Mathematical Physics* 144 (1992), Lemma 6.2
gives the coefficient \(a(m)(1+a(m))/a_-(m)\); equation (5.9) gives \(1-a(m)\le
a_-(m)\); and Lemma 5.2 with equations (5.9)--(5.10) gives \(a(m)\le c\lambda^m\) for
every prescribed rate above the rho-weighted spectral radius of the transfer remainder.

**Scope restriction (FNW rate and prefactor):** two clauses of the source display are
narrower here than in print, and both are recorded in
`docs/paper-gaps/cpgsv21_martingale_overlap.tex`.

The rate: the source prescribes that \(\lambda\) may be any number with
\(\lambda_i<\lambda<1\) for every eigenvalue \(\lambda_i\ne 1\) of the transfer operator.
What is proved below holds instead for any rate strictly above the rho-weighted spectral
radius of the transfer remainder. The two conditions are known to describe the same rates
only once that radius is identified with the largest modulus among the nonunit transfer
eigenvalues, and that identification is not formalized: the available eigenvalue result
bounds each eigenvalue of the remainder below one without characterizing its spectrum.

The prefactor: the source states that \(c\) may be taken equal to \(k^2\), the dimension
of the auxiliary space. The prefactor produced here is the existential rate-dependent one
supplied by Lemma 5.2; no dimension-only value is asserted.

## Main results

* `MPSTensor.wholeIncrement_groundProjection_defect_le_fnw_geometric`
* `MPSTensor.IsPrimitiveMPS.exists_wholeIncrement_groundProjection_defect_le_fnw_geometric`
* `MPSTensor.IsPrimitiveMPS.exists_openChain_groundProjection_defect_le_fnw_geometric`
-/

open scoped BigOperators ComplexOrder ENNReal Matrix NNReal

namespace MPSTensor

noncomputable section

variable {d D : ℕ}

local notation "Mat" => Matrix (Fin D) (Fin D) ℂ

attribute [local instance] groundSpaceES_hasOrthogonalProjection

/-- Display (6.1) of Nachtergaele, arXiv:cond-mat/9410110, lines 2401--2412, at a fixed
interaction length. Given the geometric bound \(a(m)\le c\lambda^m<1\) on the source
mixing quantity, the FNW Lemma 6.2 coefficient \(a(m)(1+a(m))/a_-(m)\) is at most
\(c\lambda^m(1+c\lambda^m)/(1-c\lambda^m)\). -/
theorem wholeIncrement_groundProjection_defect_le_fnw_geometric [NeZero D]
    (ρ : Mat) (hρ : ρ.PosDef) (htr : Matrix.trace ρ = 1)
    (A : MPSTensor d D) (hA : IsLeftCanonical A)
    (hρfix : Kraus.transferMap A ρ = ρ) {L m : ℕ}
    (hInj : Kraus.IsNBlkInjective A L) (hL : 0 < L) (hLm : L ≤ m)
    {c lam : ℝ}
    (hmix : fnwMixingQuantity ρ hρ A htr m ≤ c * lam ^ m)
    (hsmall : c * lam ^ m < 1)
    (r ℓ : ℕ) (hℓ : 0 < ℓ) :
    ‖(reassocTailBoundaryMapES A r m ℓ).range.starProjection ∘L
          (leftBoundaryMapES A (r + m) ℓ).range.starProjection -
        (groundSpaceES A (r + m + ℓ)).starProjection‖ ≤
      c * lam ^ m * (1 + c * lam ^ m) / (1 - c * lam ^ m) := by
  have ha0 : 0 ≤ fnwMixingQuantity ρ hρ A htr m :=
    fnwMixingQuantity_nonneg ρ hρ A htr m
  have ha1 : fnwMixingQuantity ρ hρ A htr m < 1 := lt_of_le_of_lt hmix hsmall
  have h59 : 1 - fnwMixingQuantity ρ hρ A htr m ≤ fnwLowerBoundaryConstant ρ hρ A m :=
    one_sub_fnwMixingQuantity_le_fnwLowerBoundaryConstant ρ hρ htr A m
  have hdenpos : 0 < 1 - c * lam ^ m := sub_pos.mpr hsmall
  have hden : 1 - c * lam ^ m ≤ fnwLowerBoundaryConstant ρ hρ A m := by linarith
  have ht0 : 0 ≤ c * lam ^ m := ha0.trans hmix
  have hnum : fnwMixingQuantity ρ hρ A htr m * (1 + fnwMixingQuantity ρ hρ A htr m) ≤
      c * lam ^ m * (1 + c * lam ^ m) := by nlinarith
  have hnum0 : 0 ≤ c * lam ^ m * (1 + c * lam ^ m) := by nlinarith
  calc
    ‖(reassocTailBoundaryMapES A r m ℓ).range.starProjection ∘L
          (leftBoundaryMapES A (r + m) ℓ).range.starProjection -
        (groundSpaceES A (r + m + ℓ)).starProjection‖ ≤
        fnwMixingQuantity ρ hρ A htr m * (1 + fnwMixingQuantity ρ hρ A htr m) /
          fnwLowerBoundaryConstant ρ hρ A m :=
      wholeIncrement_groundProjection_defect_le_fnw_factored
        ρ hρ htr A hA hρfix hInj hL hLm r ℓ hℓ
    _ ≤ c * lam ^ m * (1 + c * lam ^ m) / (1 - c * lam ^ m) := by gcongr

/-- A primitive matrix-product state satisfies display (6.1) of Nachtergaele,
arXiv:cond-mat/9410110, lines 2401--2412, with a rate strictly below one and a positive
prefactor: there is a positive interaction length beyond which the whole-increment ground
projector defect is at most \(c\lambda^m(1+c\lambda^m)/(1-c\lambda^m)\), uniformly in the
prefix and suffix lengths. The rate is chosen inside the proof, as some number strictly
between the rho-weighted spectral radius of the transfer remainder and one; the conclusion
exports only that the chosen rate is positive and below one. A caller that needs a
particular admissible rate uses the rate-parameterized mixing estimate together with the
fixed-length geometric bound instead. -/
theorem IsPrimitiveMPS.exists_wholeIncrement_groundProjection_defect_le_fnw_geometric
    [NeZero D] {A : MPSTensor d D} {ρ : Mat} (hP : IsPrimitiveMPS A ρ)
    (hρ : ρ.PosDef) :
    ∃ c lam : ℝ, ∃ L : ℕ,
      0 < c ∧ 0 < lam ∧ lam < 1 ∧ 0 < L ∧ Kraus.IsNBlkInjective A L ∧
        ∀ m : ℕ, L ≤ m → c * lam ^ m < 1 → ∀ r ℓ : ℕ, 0 < ℓ →
          ‖(reassocTailBoundaryMapES A r m ℓ).range.starProjection ∘L
                (leftBoundaryMapES A (r + m) ℓ).range.starProjection -
              (groundSpaceES A (r + m + ℓ)).starProjection‖ ≤
            c * lam ^ m * (1 + c * lam ^ m) / (1 - c * lam ^ m) := by
  set σ : Mat := (Matrix.trace ρ)⁻¹ • ρ with hσ_def
  have hσ : σ.PosDef := hρ.inv_trace_smul
  have hPσ : IsPrimitiveMPS A σ := IsPrimitiveMPS.smul_inv_trace hP hρ
  have htr : Matrix.trace σ = 1 := by
    rw [hσ_def]
    exact Matrix.trace_inv_trace_smul (ne_of_gt hρ.trace_pos)
  obtain ⟨rate, hrate, hrate_one⟩ :=
    ENNReal.lt_iff_exists_nnreal_btwn.mp (hPσ.fnwWeightedRemainder_spectralRadius_lt_one hσ)
  obtain ⟨c, hc, hbound⟩ :=
    hPσ.exists_fnwMixingQuantity_le_geometric hσ htr rate hrate
  have hrate_pos : 0 < (rate : ℝ) := by
    rcases eq_or_ne rate 0 with rfl | hne
    · exact absurd hrate (by simp)
    · exact NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hne)
  have hrate_lt : (rate : ℝ) < 1 := by exact_mod_cast ENNReal.coe_lt_one_iff.mp hrate_one
  obtain ⟨L, hL, hInj⟩ := isNormal_of_isPrimitiveMPS_with_posDef hP hρ
  refine ⟨c, (rate : ℝ), L, hc, hrate_pos, hrate_lt, hL, hInj,
    fun m hLm hsmall r ℓ hℓ ↦ ?_⟩
  exact wholeIncrement_groundProjection_defect_le_fnw_geometric σ hσ htr A hP.norm
    hPσ.fixedPoint_is_fixed hInj hL hLm (hbound m (le_trans hL hLm)) hsmall r ℓ hℓ

/-- The open-chain projector defect at overlap length \(l\) is the whole-increment defect
with a one-site suffix. -/
theorem openChain_groundProjection_defect_eq_wholeIncrement
    (A : MPSTensor d D) (K l : ℕ) :
    openChainTailGroundProjectionES A K (l + 1) ∘L
          openChainLeftGroundProjectionES A (K + l) -
        (groundSpaceES A (K + l + 1)).starProjection =
      (reassocTailBoundaryMapES A K l 1).range.starProjection ∘L
          (leftBoundaryMapES A (K + l) 1).range.starProjection -
        (groundSpaceES A (K + l + 1)).starProjection := by
  simp only [openChainTailGroundProjectionES, openChainLeftGroundProjectionES,
    reassocTailBoundaryMapES_one, range_tailBoundaryMapES, range_leftBoundaryMapES_one]

/-- The open-chain form of display (6.1) of Nachtergaele, arXiv:cond-mat/9410110,
lines 1180--1194: any prefix length and an overlap length beyond the interaction
length give the projector defect
\(\lVert G_{\Lambda_n}G_{\Lambda_{n+1}\setminus\Lambda_{n-l}}-G_{\Lambda_{n+1}}\rVert\)
at most \(c\lambda^l(1+c\lambda^l)/(1-c\lambda^l)\). The one-site suffix supplies
the source's positive spectator length, so no restriction on the prefix remains. -/
theorem IsPrimitiveMPS.exists_openChain_groundProjection_defect_le_fnw_geometric
    [NeZero D] {A : MPSTensor d D} {ρ : Mat} (hP : IsPrimitiveMPS A ρ)
    (hρ : ρ.PosDef) :
    ∃ c lam : ℝ, ∃ L : ℕ,
      0 < c ∧ 0 < lam ∧ lam < 1 ∧ 0 < L ∧ Kraus.IsNBlkInjective A L ∧
        ∀ l : ℕ, L ≤ l → c * lam ^ l < 1 → ∀ K : ℕ,
          ‖openChainTailGroundProjectionES A K (l + 1) ∘L
                openChainLeftGroundProjectionES A (K + l) -
              (groundSpaceES A (K + l + 1)).starProjection‖ ≤
            c * lam ^ l * (1 + c * lam ^ l) / (1 - c * lam ^ l) := by
  obtain ⟨c, lam, L, hc, hlam, hlam_one, hL, hInj, hDefect⟩ :=
    hP.exists_wholeIncrement_groundProjection_defect_le_fnw_geometric hρ
  refine ⟨c, lam, L, hc, hlam, hlam_one, hL, hInj, fun l hLl hsmall K ↦ ?_⟩
  rw [openChain_groundProjection_defect_eq_wholeIncrement]
  exact hDefect l hLl hsmall K 1 one_pos

end

end MPSTensor
