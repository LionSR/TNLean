/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.FNWGeometricDefect
import TNLean.MPS.ParentHamiltonian.Martingale.OpenChain
import TNLean.Wielandt.Primitivity.StronglyIrreducibleToFullRank

/-!
# The open-chain C3 threshold

This file chooses an overlap length, measured in sites of the input tensor, at which the
projector-defect estimate imported by Nachtergaele from Fannes--Nachtergaele--Werner
satisfies Nachtergaele's condition C3. The coefficient is the rational function
\(c\lambda^l(1+c\lambda^l)/(1-c\lambda^l)\) of arXiv:cond-mat/9410110, lines
1180--1194 and display (6.1) at lines 2401--2412; it tends to zero as the overlap length
grows, so some overlap length puts it below the C3 threshold \(1/\sqrt{l+1}\). If the
input tensor is already a blocked representative, one such site is one blocked-chain
filtration step.

The prefix length is unrestricted, as it was before the coefficient was replaced.
The projector estimate holds at the zero prefix, so the source's positivity there
is not needed. Only the literal martingale-difference statement keeps a positive
prefix, because Nachtergaele's difference \(E_n=G_{\Lambda_n}-G_{\Lambda_{n+1}}\)
is itself indexed by volumes strictly larger than the interaction range.

## Main results

* `MPSTensor.IsPrimitiveMPS.exists_uniform_wholeIncrement_defect_le_seven_sixteenths`
  chooses one original-site scale uniformly for every prefix length.
* `MPSTensor.IsPrimitiveMPS.exists_threeBlock_wholeIncrement_defect_le_seven_sixteenths`
  specializes the uniform estimate to three equal original-site blocks.
* `MPSTensor.IsPrimitiveMPS.exists_openChain_groundProjection_defect_lt_c3_threshold`
  chooses a block-injective overlap length and one uniform C3 defect coefficient.
* `MPSTensor.IsPrimitiveMPS.exists_openChain_martingaleDifference_norm_lt_c3_threshold`
  states the same bound as Nachtergaele's literal C3 operator norm.
* `MPSTensor.IsPrimitiveMPS.exists_re_inner_openChain_anticommutator_ge_c3_threshold`
  gives the corresponding open-chain excitation-projection anticommutator estimate.

## References

* B. Nachtergaele, arXiv:cond-mat/9410110, eqs. (2.4)--(2.5), Theorem 3,
  and Section 6.
* M. Fannes, B. Nachtergaele and R. F. Werner, *Communications in Mathematical
  Physics* 144 (1992), Lemma 5.2, eq. (5.9), and Lemma 6.2.
-/

open Filter
open scoped ComplexOrder InnerProductSpace Topology

namespace MPSTensor

variable {d D : ℕ}

attribute [local instance] groundSpaceES_hasOrthogonalProjection

private theorem tendsto_sqrt_succ_mul_pow_of_lt_one {r : ℝ}
    (hr : 0 ≤ r) (hr_lt_one : r < 1) :
    Tendsto (fun n : ℕ => Real.sqrt ((n + 1 : ℕ) : ℝ) * r ^ n) atTop (𝓝 0) := by
  apply squeeze_zero
  · intro n
    positivity
  · intro n
    have hsqrt : Real.sqrt ((n + 1 : ℕ) : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
      rw [Real.sqrt_le_self_iff]
      exact Or.inr (by norm_num [Nat.cast_add])
    exact mul_le_mul_of_nonneg_right hsqrt (pow_nonneg hr n)
  · simpa only [Nat.cast_add, Nat.cast_one, add_mul, one_mul, zero_add] using
      (tendsto_self_mul_const_pow_of_lt_one hr hr_lt_one).add
        (tendsto_pow_atTop_nhds_zero_of_lt_one hr hr_lt_one)

private theorem tendsto_fnw_coefficient_mul_sqrt
    {c lam : ℝ} (hlam : 0 ≤ lam) (hlam_lt_one : lam < 1) :
    Tendsto
      (fun n : ℕ =>
        c * lam ^ n * (1 + c * lam ^ n) / (1 - c * lam ^ n) *
          Real.sqrt ((n + 1 : ℕ) : ℝ))
      atTop (𝓝 0) := by
  have hpow : Tendsto (fun n : ℕ => lam ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hlam hlam_lt_one
  have hsqrt := tendsto_sqrt_succ_mul_pow_of_lt_one hlam hlam_lt_one
  have hden : Tendsto (fun n : ℕ => 1 - c * lam ^ n) atTop (𝓝 1) := by
    have h : Tendsto (fun n : ℕ => 1 - c * lam ^ n) atTop (𝓝 (1 - c * 0)) :=
      tendsto_const_nhds.sub (tendsto_const_nhds.mul hpow)
    simpa using h
  have hnum : Tendsto (fun n : ℕ => c * (1 + c * lam ^ n)) atTop (𝓝 c) := by
    have h : Tendsto (fun n : ℕ => c * (1 + c * lam ^ n)) atTop (𝓝 (c * (1 + c * 0))) :=
      tendsto_const_nhds.mul (tendsto_const_nhds.add (tendsto_const_nhds.mul hpow))
    simpa using h
  have hquot :
      Tendsto (fun n : ℕ => c * (1 + c * lam ^ n) / (1 - c * lam ^ n)) atTop (𝓝 c) := by
    have h := hnum.div hden one_ne_zero
    rw [div_one] at h
    exact h
  have hprod := hsqrt.mul hquot
  rw [zero_mul] at hprod
  exact hprod.congr fun n ↦ by ring

private theorem tendsto_fnw_coefficient
    {c lam : ℝ} (hlam : 0 ≤ lam) (hlam_lt_one : lam < 1) :
    Tendsto (fun n : ℕ => c * lam ^ n * (1 + c * lam ^ n) / (1 - c * lam ^ n))
      atTop (𝓝 0) := by
  have hpow : Tendsto (fun n : ℕ => lam ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hlam hlam_lt_one
  have hden : Tendsto (fun n : ℕ => 1 - c * lam ^ n) atTop (𝓝 1) := by
    have h : Tendsto (fun n : ℕ => 1 - c * lam ^ n) atTop (𝓝 (1 - c * 0)) :=
      tendsto_const_nhds.sub (tendsto_const_nhds.mul hpow)
    simpa using h
  have hnum :
      Tendsto (fun n : ℕ => c * lam ^ n * (1 + c * lam ^ n)) atTop (𝓝 0) := by
    have h : Tendsto (fun n : ℕ => c * lam ^ n * (1 + c * lam ^ n)) atTop
        (𝓝 (c * 0 * (1 + c * 0))) :=
      (tendsto_const_nhds.mul hpow).mul
        (tendsto_const_nhds.add (tendsto_const_nhds.mul hpow))
    simpa using h
  have h := hnum.div hden one_ne_zero
  rw [zero_div] at h
  exact h

/-- There is a positive block-injective length \(p\), measured in sites of the
input tensor, such that the whole-increment projector defect with overlap and
suffix lengths \(L=Q=p\) is at most \(7/16\) for every positive prefix length
\(K\).

The coefficient decays because it is the rational function
\(c\lambda^p(1+c\lambda^p)/(1-c\lambda^p)\) of Nachtergaele,
arXiv:cond-mat/9410110, display (6.1) at lines 2401--2412. -/
theorem IsPrimitiveMPS.exists_uniform_wholeIncrement_defect_le_seven_sixteenths
    [NeZero D] {A : MPSTensor d D} {ρ : Matrix (Fin D) (Fin D) ℂ}
    (hP : IsPrimitiveMPS A ρ) (hρ : ρ.PosDef) :
    ∃ p : ℕ,
      0 < p ∧ Kraus.IsNBlkInjective A p ∧
        ∀ K : ℕ,
          ‖(reassocTailBoundaryMapES A K p p).range.starProjection ∘L
                (leftBoundaryMapES A (K + p) p).range.starProjection -
              (groundSpaceES A (K + p + p)).starProjection‖ ≤ 7 / 16 := by
  obtain ⟨c, lam, L, hc, hlam, hlam_lt_one, hLpos, hLinj, hDefect⟩ :=
    hP.exists_wholeIncrement_groundProjection_defect_le_fnw_geometric hρ
  have hlam_pow : Tendsto (fun n : ℕ => lam ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hlam.le hlam_lt_one
  have hsmall_lim : Tendsto (fun n : ℕ => c * lam ^ n) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul hlam_pow
  have hcoefficient_lim := tendsto_fnw_coefficient (c := c) hlam.le hlam_lt_one
  have hsmall : ∀ᶠ n : ℕ in atTop, c * lam ^ n < 1 :=
    (tendsto_order.1 hsmall_lim).2 1 zero_lt_one
  have hcoefficient : ∀ᶠ n : ℕ in atTop,
      c * lam ^ n * (1 + c * lam ^ n) / (1 - c * lam ^ n) < 7 / 16 :=
    (tendsto_order.1 hcoefficient_lim).2 (7 / 16) (by norm_num)
  have hlarge : ∀ᶠ n : ℕ in atTop, max 1 L ≤ n := eventually_ge_atTop _
  obtain ⟨p, hp_large, hp_small, hp_coefficient⟩ :=
    (hlarge.and (hsmall.and hcoefficient)).exists
  have hp : 0 < p := lt_of_lt_of_le (by omega) hp_large
  have hLle : L ≤ p := le_trans (le_max_right 1 L) hp_large
  have hInj : Kraus.IsNBlkInjective A p := isNBlkInjective_of_le hLpos hLinj hLle
  refine ⟨p, hp, hInj, fun K ↦ ?_⟩
  exact (hDefect p hLle hp_small K p hp).trans hp_coefficient.le

/-- At the length \(p\) chosen uniformly above, taking the prefix length
\(K=p\) gives three consecutive blocks of \(p\) original sites and projector
defect at most \(7/16\). -/
theorem IsPrimitiveMPS.exists_threeBlock_wholeIncrement_defect_le_seven_sixteenths
    [NeZero D] {A : MPSTensor d D} {ρ : Matrix (Fin D) (Fin D) ℂ}
    (hP : IsPrimitiveMPS A ρ) (hρ : ρ.PosDef) :
    ∃ p : ℕ,
      0 < p ∧ Kraus.IsNBlkInjective A p ∧
        ‖(reassocTailBoundaryMapES A p p p).range.starProjection ∘L
              (leftBoundaryMapES A (p + p) p).range.starProjection -
            (groundSpaceES A (p + p + p)).starProjection‖ ≤ 7 / 16 := by
  obtain ⟨p, hp, hInj, hDefect⟩ :=
    hP.exists_uniform_wholeIncrement_defect_le_seven_sixteenths hρ
  exact ⟨p, hp, hInj, hDefect p⟩

/-- A primitive MPS with faithful fixed point has a block-injective overlap length
at which the uniform open-chain ground-projector defect satisfies Nachtergaele's
condition C3, arXiv:cond-mat/9410110, eq. (2.4).

The coefficient is the imported Fannes--Nachtergaele--Werner coefficient
\(c\lambda^l(1+c\lambda^l)/(1-c\lambda^l)\) of arXiv:cond-mat/9410110, lines
1180--1194 and display (6.1) at lines 2401--2412, evaluated at the chosen overlap
length. -/
theorem IsPrimitiveMPS.exists_openChain_groundProjection_defect_lt_c3_threshold
    [NeZero D] {A : MPSTensor d D} {ρ : Matrix (Fin D) (Fin D) ℂ}
    (hP : IsPrimitiveMPS A ρ) (hρ : ρ.PosDef) :
    ∃ l : ℕ, ∃ ε : ℝ,
      1 < l ∧ Kraus.IsNBlkInjective A l ∧ 0 ≤ ε ∧
      ε < 1 / Real.sqrt ((l + 1 : ℕ) : ℝ) ∧
      ∀ K : ℕ,
        ‖openChainTailGroundProjectionES A K (l + 1) ∘L
              openChainLeftGroundProjectionES A (K + l) -
            (groundSpaceES A (K + l + 1)).starProjection‖ ≤ ε := by
  obtain ⟨c, lam, L, hc, hlam, hlam_lt_one, hLpos, hLinj, hDefect⟩ :=
    hP.exists_openChain_groundProjection_defect_le_fnw_geometric hρ
  have hlam_pow : Tendsto (fun n : ℕ => lam ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hlam.le hlam_lt_one
  have hsmall_lim : Tendsto (fun n : ℕ => c * lam ^ n) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul hlam_pow
  have hcoefficient_lim :=
    tendsto_fnw_coefficient_mul_sqrt (c := c) hlam.le hlam_lt_one
  have hsmall : ∀ᶠ n : ℕ in atTop, c * lam ^ n < 1 :=
    (tendsto_order.1 hsmall_lim).2 1 zero_lt_one
  have hcoefficient : ∀ᶠ n : ℕ in atTop,
      c * lam ^ n * (1 + c * lam ^ n) / (1 - c * lam ^ n) *
          Real.sqrt ((n + 1 : ℕ) : ℝ) < 1 :=
    (tendsto_order.1 hcoefficient_lim).2 1 zero_lt_one
  have hlarge : ∀ᶠ n : ℕ in atTop, max 2 L ≤ n := eventually_ge_atTop _
  obtain ⟨l, hl_large, hl_small, hl_coefficient⟩ :=
    (hlarge.and (hsmall.and hcoefficient)).exists
  let ε := c * lam ^ l * (1 + c * lam ^ l) / (1 - c * lam ^ l)
  have hl : 1 < l := lt_of_lt_of_le (by omega) hl_large
  have hLle : L ≤ l := le_trans (le_max_right 2 L) hl_large
  have hInj : Kraus.IsNBlkInjective A l := isNBlkInjective_of_le hLpos hLinj hLle
  have hden : 0 < 1 - c * lam ^ l := sub_pos.mpr hl_small
  have hε : 0 ≤ ε := by
    have hnum : 0 ≤ c * lam ^ l * (1 + c * lam ^ l) := by positivity
    exact div_nonneg hnum hden.le
  have hsqrt : 0 < Real.sqrt ((l + 1 : ℕ) : ℝ) := Real.sqrt_pos.2 (by positivity)
  have hε_lt : ε < 1 / Real.sqrt ((l + 1 : ℕ) : ℝ) := by
    rw [lt_div_iff₀ hsqrt]
    simpa only [ε, one_mul] using hl_coefficient
  refine ⟨l, ε, hl, hInj, hε, hε_lt, ?_⟩
  intro K
  exact hDefect l hLle hl_small K

/-- A primitive MPS with faithful fixed point satisfies Nachtergaele's condition C3
in its literal martingale-difference form
\[
  \lVert G_{\Lambda_{n+1}\setminus\Lambda_{n-l}}E_n\rVert
    \leq \varepsilon_l < \frac{1}{\sqrt{l+1}}.
\]
The indices are \(n=K+l\) and \(n_l=l+1\), so \(0<K\), and the same \(l\)
and \(\varepsilon_l\) are supplied by
`exists_openChain_groundProjection_defect_lt_c3_threshold`. This is only the
exact projector identification following condition C3 in Nachtergaele,
arXiv:cond-mat/9410110, equation (2.4); no new decay estimate enters. -/
theorem IsPrimitiveMPS.exists_openChain_martingaleDifference_norm_lt_c3_threshold
    [NeZero D] {A : MPSTensor d D} {ρ : Matrix (Fin D) (Fin D) ℂ}
    (hP : IsPrimitiveMPS A ρ) (hρ : ρ.PosDef) :
    ∃ l : ℕ, ∃ ε : ℝ, ∃ hl : 1 < l, ∃ hInj : Kraus.IsNBlkInjective A l,
      0 ≤ ε ∧ ε < 1 / Real.sqrt ((l + 1 : ℕ) : ℝ) ∧
      ∀ (K : ℕ) (hK : 0 < K),
        ‖openChainTailGroundProjectionES A K (l + 1) ∘L
            openChainMartingaleDifferenceES A K l hInj hl.le hK‖ ≤ ε := by
  obtain ⟨l, ε, hl, hInj, hε, hε_lt, hDefect⟩ :=
    hP.exists_openChain_groundProjection_defect_lt_c3_threshold hρ
  refine ⟨l, ε, hl, hInj, hε, hε_lt, fun K hK ↦ ?_⟩
  rw [openChainTailGroundProjection_comp_martingaleDifference hInj hl.le hK]
  exact hDefect K

/-- The C3 threshold yields the uniform open-chain anticommutator estimate for
the complementary excitation projections. Nachtergaele's identity following condition
C3 identifies the projector defect, arXiv:cond-mat/9410110, eq. (2.4); the
anticommutator estimate is the two-projection consequence proved in this development. -/
theorem IsPrimitiveMPS.exists_re_inner_openChain_anticommutator_ge_c3_threshold
    [NeZero D] {A : MPSTensor d D} {ρ : Matrix (Fin D) (Fin D) ℂ}
    (hP : IsPrimitiveMPS A ρ) (hρ : ρ.PosDef) :
    ∃ l : ℕ, ∃ ε : ℝ,
      1 < l ∧ 0 ≤ ε ∧ ε < 1 / Real.sqrt ((l + 1 : ℕ) : ℝ) ∧
      ∀ (K : ℕ) (v : EuclideanSpace ℂ (Cfg d (K + l + 1))),
        -ε *
            (RCLike.re
                (⟪(openChainTailGroundSpaceES A K (l + 1))ᗮ.starProjection v, v⟫_ℂ) +
              RCLike.re
                (⟪(openChainLeftGroundSpaceES A (K + l))ᗮ.starProjection v, v⟫_ℂ)) ≤
          RCLike.re
              (⟪(openChainTailGroundSpaceES A K (l + 1))ᗮ.starProjection v,
                (openChainLeftGroundSpaceES A (K + l))ᗮ.starProjection v⟫_ℂ) +
            RCLike.re
              (⟪(openChainLeftGroundSpaceES A (K + l))ᗮ.starProjection v,
                (openChainTailGroundSpaceES A K (l + 1))ᗮ.starProjection v⟫_ℂ) := by
  obtain ⟨l, ε, hl, hInj, hε, hε_lt, hDefect⟩ :=
    hP.exists_openChain_groundProjection_defect_lt_c3_threshold hρ
  refine ⟨l, ε, hl, hε, hε_lt, ?_⟩
  intro K v
  exact re_inner_openChain_anticommutator_ge_neg_of_groundProjection_defect
    hInj hl.le (hDefect K) v

end MPSTensor
