/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.CorrelatorFiniteSize
import TNLean.MPS.Preparation.TransferSpectrumFromCorrelations

/-!
# Passing actual finite-ring correlations to limiting contractions

Block injectivity and trace preservation give pointwise primitivity. Thus
the complementary transfer powers tend to zero, and the existing exact
finite-ring contraction formula tends to the actual limiting connected
correlator. No common transfer rate is used for this passage.

An eventual finite-ring correlation bound therefore bounds the limiting
contraction. The existing eigenvalue observables then transfer any common
finite-ring rate to the nonunit transfer spectrum, with no convergence or
limiting-correlation estimate supplied as a premise.

Source: arXiv:2307.01696, Supplemental Material, proof of Lemma 2;
SPC11, arXiv:1010.3732, Section II.F, lines 929–953.
-/

noncomputable section

open Filter
open scoped Matrix BigOperators InnerProductSpace ComplexOrder MatrixOrder Matrix.Norms.Operator

namespace MPSTensor

variable {d D L : ℕ}

/-- The actual finite periodic connected correlator converges to its
fixed-point contraction as the unobserved return interval grows. Only
pointwise block injectivity is used: no uniform transfer gap or assumed
convergence is required. Source: arXiv:2307.01696, Supplemental Material,
proof of Lemma 2, expansion of the final transfer power. -/
theorem tendsto_mpvConnectedCorrelator_limitCorrelator [NeZero D]
    {A : MPSTensor d D} (hL0 : 0 < L) (hL : Kraus.IsNBlkInjective A L)
    (hA : ∑ i, (A i)ᴴ * A i = 1)
    {ρ : Matrix (Fin D) (Fin D) ℂ} (hρ : ρ.PosDef)
    (hρfix : Kraus.transferMap A ρ = ρ) (hρtr : Matrix.trace ρ = 1)
    (X Y : Matrix (Cfg d L) (Cfg d L) ℂ) {t : ℕ} (ht : 1 ≤ t) :
    Tendsto (fun n : ℕ ↦ mpvConnectedCorrelator A (L + t + L + n) 0 (L + t) X Y)
      atTop (nhds (limitCorrelator A ρ (by rw [hρtr]; exact one_ne_zero) L X Y t)) := by
  classical
  have htr : Matrix.trace ρ ≠ 0 := by rw [hρtr]; exact one_ne_zero
  let E := Kraus.transferMap A
  let T := E - fixedPointProj ρ htr
  let V := Matrix (Fin D) (Fin D) ℂ
  let Φ : Module.End ℂ V ≃ₐ[ℂ] (V →L[ℂ] V) := Module.End.toContinuousLinearMap V
  have hNormal : Kraus.IsNormal A := ⟨L, hL0, hL⟩
  have hPP : IsPrimitivePaper A := isPrimitivePaper_of_hasEventuallyFullKrausRank A
    ((hasEventuallyFullKrausRank_iff_isNormal A).2 hNormal)
  obtain ⟨_, _, _, hPer, hIrr⟩ := (primitivePaper_iff_stronglyIrreducible A hA).1 hPP
  have hChannel : IsChannel E := Kraus.isChannel_mapLM A hA
  obtain ⟨_, hgap⟩ := spectralRadius_compl_lt_one_of_primitive_fixedPoint_of_irreducible_channel
    E hChannel hIrr hPer ρ hρ.posSemidef
      (fun h ↦ htr (by rw [h, Matrix.trace_zero])) hρfix
  have hpow : Tendsto (fun n : ℕ ↦ (Φ T) ^ n) atTop (nhds 0) :=
    pow_tendsto_zero_of_spectralRadius_lt_one _ hgap
  let tr : (V →L[ℂ] V) →L[ℂ] ℂ := LinearMap.toContinuousLinearMap
    ((LinearMap.trace ℂ V).comp Φ.symm.toLinearMap)
  have hTraceEq (F : Module.End ℂ V) (n : ℕ) :
      tr (Φ F * (Φ T) ^ n) = LinearMap.trace ℂ V (F * T ^ n) := by
    change LinearMap.trace ℂ V (Φ.symm (Φ F * (Φ T) ^ n)) = _
    rw [← map_pow, ← map_mul, Φ.symm_apply_apply]
  have hTrace (F : Module.End ℂ V) :
      Tendsto (fun n : ℕ ↦ LinearMap.trace ℂ V (F * T ^ n)) atTop (nhds 0) := by
    have hprod := (tendsto_const_nhds (x := Φ F)).mul hpow
    have h := (tr.continuous.tendsto (Φ F * 0)).comp hprod
    simpa only [Function.comp_def, hTraceEq, mul_zero, map_zero] using h
  have hTraceAdd (F : Module.End ℂ V) (k : ℕ) :
      Tendsto (fun n : ℕ ↦ LinearMap.trace ℂ V (F * T ^ (k + n))) atTop (nhds 0) := by
    simpa only [pow_add, mul_assoc] using hTrace (F * T ^ k)
  let EX := physicalObservableTransfer A L X
  let EY := physicalObservableTransfer A L Y
  let α := Matrix.trace (EX ρ)
  let β := Matrix.trace (EY ρ)
  let g := limitCorrelator A ρ htr L X Y t
  have hZerr : Tendsto (fun n : ℕ ↦ LinearMap.trace ℂ V (T ^ (L + t + L + n)))
      atTop (nhds 0) := by
    simpa only [one_mul] using hTraceAdd 1 (L + t + L)
  have hXYerr := hTrace (EX * E ^ t * EY)
  have hXerr : Tendsto
      (fun n : ℕ ↦ LinearMap.trace ℂ V (EX * T ^ (t + (L + n)))) atTop (nhds 0) := by
    simpa only [Nat.add_assoc] using hTraceAdd EX (t + L)
  have hYerr : Tendsto
      (fun n : ℕ ↦ LinearMap.trace ℂ V (EY * T ^ (n + (L + t)))) atTop (nhds 0) := by
    simpa only [Nat.add_comm] using hTraceAdd EY (L + t)
  have hZlim : Tendsto (fun n : ℕ ↦ 1 + LinearMap.trace ℂ V (T ^ (L + t + L + n)))
      atTop (nhds (1 : ℂ)) := by
    simpa only [add_zero] using (tendsto_const_nhds (x := (1 : ℂ))).add hZerr
  have hXYlim : Tendsto
      (fun n : ℕ ↦ α * β + g + LinearMap.trace ℂ V ((EX * E ^ t * EY) * T ^ n))
      atTop (nhds (α * β + g)) := by
    simpa only [add_zero] using (tendsto_const_nhds (x := α * β + g)).add hXYerr
  have hXlim : Tendsto
      (fun n : ℕ ↦ α + LinearMap.trace ℂ V (EX * T ^ (t + (L + n))))
      atTop (nhds α) := by
    simpa only [add_zero] using (tendsto_const_nhds (x := α)).add hXerr
  have hYlim : Tendsto
      (fun n : ℕ ↦ β + LinearMap.trace ℂ V (EY * T ^ (n + (L + t))))
      atTop (nhds β) := by
    simpa only [add_zero] using (tendsto_const_nhds (x := β)).add hYerr
  have hlim := (hXYlim.div hZlim one_ne_zero).sub
    ((hXlim.div hZlim one_ne_zero).mul (hYlim.div hZlim one_ne_zero))
  have hlim' : Tendsto (fun n : ℕ ↦
      (α * β + g + LinearMap.trace ℂ V ((EX * E ^ t * EY) * T ^ n)) /
          (1 + LinearMap.trace ℂ V (T ^ (L + t + L + n))) -
        (α + LinearMap.trace ℂ V (EX * T ^ (t + (L + n)))) /
          (1 + LinearMap.trace ℂ V (T ^ (L + t + L + n))) *
        ((β + LinearMap.trace ℂ V (EY * T ^ (n + (L + t)))) /
          (1 + LinearMap.trace ℂ V (T ^ (L + t + L + n))))) atTop (nhds g) := by
    simpa only [Pi.div_apply, div_one, add_sub_cancel_left] using hlim
  apply hlim'.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact (mpvConnectedCorrelator_eq_of_compl hL0 hA hρfix hρtr htr X Y ht hn).symm

/-- An eventual bound on the actual finite-ring correlators survives the
thermodynamic limit. The convergence is derived from block injectivity,
not supplied. Source: arXiv:2307.01696, Supplemental Material, proof of
Lemma 2, finite-size correction to the fixed-point contraction. -/
theorem norm_limitCorrelator_le_of_eventually_mpvConnectedCorrelator_le [NeZero D]
    {A : MPSTensor d D} (hL0 : 0 < L) (hL : Kraus.IsNBlkInjective A L)
    (hA : ∑ i, (A i)ᴴ * A i = 1)
    {ρ : Matrix (Fin D) (Fin D) ℂ} (hρ : ρ.PosDef)
    (hρfix : Kraus.transferMap A ρ = ρ) (hρtr : Matrix.trace ρ = 1)
    (X Y : Matrix (Cfg d L) (Cfg d L) ℂ) {t : ℕ} (ht : 1 ≤ t) {B : ℝ}
    (hFinite : ∀ᶠ n : ℕ in atTop,
      ‖mpvConnectedCorrelator A (L + t + L + n) 0 (L + t) X Y‖ ≤ B) :
    ‖limitCorrelator A ρ (by rw [hρtr]; exact one_ne_zero) L X Y t‖ ≤ B :=
  le_of_tendsto (tendsto_mpvConnectedCorrelator_limitCorrelator
    hL0 hL hA hρ hρfix hρtr X Y ht).norm hFinite

/-- A common eventual finite-ring correlation rate bounds the actual
nonunit transfer spectrum. Pointwise convergence is proved above and the
eigenvalue observables are reused; no limiting-correlation or uniform
transfer-gap premise is introduced. The finite-ring bound is explicit,
so this is a bridge for the physical clustering theorem, rather than the
physical-gap implication itself. Source: SPC11, arXiv:1010.3732,
Section II.F, lines 929–953; arXiv:2307.01696, proof of Lemma 2. -/
theorem norm_transfer_spectrum_le_of_finite_mpvConnectedCorrelator_bound [NeZero D]
    {A : MPSTensor d D} (hL0 : 0 < L) (hL : Kraus.IsNBlkInjective A L)
    (hA : ∑ i, (A i)ᴴ * A i = 1)
    {ρ : Matrix (Fin D) (Fin D) ℂ} (hρ : ρ.PosDef)
    (hρfix : Kraus.transferMap A ρ = ρ) (hρtr : Matrix.trace ρ = 1)
    {r : ℝ} (hr : 0 < r)
    (hFinite : ∀ X Y : Matrix (Cfg d L) (Cfg d L) ℂ,
      ∃ C : ℝ, ∃ t₀ : ℕ, ∀ t : ℕ, t₀ ≤ t →
        ∀ᶠ n : ℕ in atTop,
          ‖mpvConnectedCorrelator A (L + t + L + n) 0 (L + t) X Y‖ ≤ C * r ^ t)
    {lam : ℂ} (hlam : lam ∈ spectrum ℂ (Kraus.transferMap A)) (hlamOne : lam ≠ 1) :
    ‖lam‖ ≤ r := by
  apply norm_transfer_spectrum_le_of_limitCorrelator_bound hL hA hρtr hr ?_ hlam hlamOne
  intro X Y
  obtain ⟨C, t₀, hC⟩ := hFinite X Y
  refine ⟨C, max t₀ 1, fun t ht ↦ ?_⟩
  exact norm_limitCorrelator_le_of_eventually_mpvConnectedCorrelator_le
    hL0 hL hA hρ hρfix hρtr X Y (le_trans (le_max_right _ _) ht)
      (hC t (le_trans (le_max_left _ _) ht))

end MPSTensor
