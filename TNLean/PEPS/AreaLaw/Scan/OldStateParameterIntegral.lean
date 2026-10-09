/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.OldStateIntegral
import QICLean.Representation.ReplicaTransport.IntegratedEntropy

/-!
# Parameter integrability of the actual old-state coherent integral

The accepted transport-state expectation theorem gives AE strong measurability
in the interpolation parameter. Pairing with the Hermitian part of the coherent
average preserves the real trace, and the transported-state bound gives
integrability on the whole unit interval. The zero supplied vector contributes
exactly zero. No symmetry or positive replica-count premise is needed.

The finite weighted-sum bridge applies to either fill or charge data, with a
fixed good-history predicate and the original supplied vector. It does not
assert continuity in the interpolation parameter or construct leaf measures.
-/

open scoped BigOperators Matrix ComplexOrder Matrix.Norms.L2Operator
open Matrix MeasureTheory Set
open Entropy (SiteConfig)

noncomputable section

namespace TensorPower.ReplicaTransport.TransportData

variable {V : Type*} [Fintype V] [DecidableEq V] {K : ℕ}
variable {H : Type*} [DecidableEq H] {C : H → Type*} [∀ h, DecidableEq (C h)]
variable (D : TransportData V K H C) (n : V → ℕ) [∀ v, NeZero (n v)]

/-- The actual old-state integral of the zero supplied vector is zero, at
all interpolation parameters and every replica count. -/
@[simp] theorem oldFourierCoherentIntegral_zero_pre (t : ℝ) (k : ℕ) (p : ℝ) (h : H)
    (F : (SiteConfig n → ℂ) → ℝ) :
    D.oldFourierCoherentIntegral n t k 0 p h F = 0 := by
  have hv : Matrix.Transport.filteredVector (D.rootPath n t k p) 0 = 0 := by
    simp [Matrix.Transport.filteredVector, Matrix.Transport.filteredRaw]
  have hrank : vecMulVec (0 : Config k (fun v => Fin (n v)) → ℂ)
      (star (0 : Config k (fun v => Fin (n v)) → ℂ)) = 0 := by
    ext a b
    simp [Matrix.vecMulVec]
  have hstate (u : ℝ) : D.state n t k 0 p ⟨h, none⟩ u = 0 := by
    simp only [state, Matrix.Transport.transportState, hv, Matrix.mulVec_zero,
      hrank, map_zero]
  simp [oldFourierCoherentIntegral, hstate, realCoherentIntegral]

/-- The Hermitian test matrix has exactly the original real coherent
expectation in the actual old state, including the endpoints. -/
theorem oldFourierCoherentIntegral_eq_integral_hermPart (hD : D.IsAdmissible)
    {t : ℝ} (ht : 0 ≤ t) {k : ℕ} (hcomm : D.CrossBandCommute n t k)
    (pre : Config k (fun v => Fin (n v)) → ℂ) (p : ℝ) (h : H)
    {F : (SiteConfig n → ℂ) → ℝ} (hF : Continuous F) :
    D.oldFourierCoherentIntegral n t k pre p h F =
      ∫ u, Matrix.Transport.fourierWeight u *
        (D.state n t k pre p ⟨h, none⟩ u *
          hermPart (coherentAverage k (base n) F)).trace.re := by
  unfold oldFourierCoherentIntegral
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun u => by
    rw [re_trace_mul_hermPart (D.posSemidef_state hD ht hcomm pre p _ u).isHermitian,
      trace_mul_coherentAverage k (base n) hF]

/-- AE strong measurability in the interpolation parameter for the exact
old-state Fourier/coherent integral. The supplied vector may be zero. -/
theorem aestronglyMeasurable_oldFourierCoherentIntegral (hD : D.IsAdmissible)
    {t : ℝ} (ht : 0 ≤ t) {k : ℕ} (hcomm : D.CrossBandCommute n t k)
    (pre : Config k (fun v => Fin (n v)) → ℂ) (h : H)
    {F : (SiteConfig n → ℂ) → ℝ} (hF : Continuous F) :
    AEStronglyMeasurable (fun p => D.oldFourierCoherentIntegral n t k pre p h F)
      (volume.restrict (Ioo 0 1)) := by
  by_cases hpre : pre = 0
  · subst pre
    simpa only [oldFourierCoherentIntegral_zero_pre] using
      (aestronglyMeasurable_const : AEStronglyMeasurable (fun _ : ℝ => (0 : ℝ))
        (volume.restrict (Ioo 0 1)))
  · refine (D.aestronglyMeasurable_integral_state hD ht hcomm hpre h
      (isHermitian_hermPart (coherentAverage k (base n) F))).congr ?_
    exact Filter.Eventually.of_forall fun p =>
      (D.oldFourierCoherentIntegral_eq_integral_hermPart n hD ht hcomm pre p h hF).symm

/-- A uniform interior bound for a fixed continuous symbol and replica count.
The zero-vector case uses its actual zero state. -/
theorem abs_oldFourierCoherentIntegral_le (hD : D.IsAdmissible)
    {t : ℝ} (ht : 0 ≤ t) {k : ℕ} (hcomm : D.CrossBandCommute n t k)
    (pre : Config k (fun v => Fin (n v)) → ℂ) {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1)
    (h : H) {F : (SiteConfig n → ℂ) → ℝ} (hF : Continuous F) :
    |D.oldFourierCoherentIntegral n t k pre p h F| ≤
      ‖hermPart (coherentAverage k (base n) F)‖ / 2 := by
  by_cases hpre : pre = 0
  · subst pre
    rw [oldFourierCoherentIntegral_zero_pre, abs_zero]
    positivity
  · rw [D.oldFourierCoherentIntegral_eq_integral_hermPart n hD ht hcomm pre p h hF]
    exact D.abs_integral_state_le hD ht hcomm hpre hp ⟨h, none⟩
      (isHermitian_hermPart _)

/-- The exact old-state scalar integral is integrable on the open unit interval. -/
theorem integrableOn_Ioo_oldFourierCoherentIntegral (hD : D.IsAdmissible)
    {t : ℝ} (ht : 0 ≤ t) {k : ℕ} (hcomm : D.CrossBandCommute n t k)
    (pre : Config k (fun v => Fin (n v)) → ℂ) (h : H)
    {F : (SiteConfig n → ℂ) → ℝ} (hF : Continuous F) :
    IntegrableOn (fun p => D.oldFourierCoherentIntegral n t k pre p h F) (Ioo 0 1) := by
  refine ⟨D.aestronglyMeasurable_oldFourierCoherentIntegral n hD ht hcomm pre h hF,
    HasFiniteIntegral.restrict_of_bounded
      (C := ‖hermPart (coherentAverage k (base n) F)‖ / 2) (by simp) ?_⟩
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with p hp
  rw [Real.norm_eq_abs]
  exact D.abs_oldFourierCoherentIntegral_le n hD ht hcomm pre hp h hF

/-- Null endpoints extend the derived integrability to the closed unit interval. -/
theorem intervalIntegrable_oldFourierCoherentIntegral (hD : D.IsAdmissible)
    {t : ℝ} (ht : 0 ≤ t) {k : ℕ} (hcomm : D.CrossBandCommute n t k)
    (pre : Config k (fun v => Fin (n v)) → ℂ) (h : H)
    {F : (SiteConfig n → ℂ) → ℝ} (hF : Continuous F) :
    IntervalIntegrable (fun p => D.oldFourierCoherentIntegral n t k pre p h F) volume 0 1 :=
  (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mpr
    (D.integrableOn_Ioo_oldFourierCoherentIntegral n hD ht hcomm pre h hF)

/-- Closed-interval integrability concerns the original endpoint values. -/
theorem integrableOn_Icc_oldFourierCoherentIntegral (hD : D.IsAdmissible)
    {t : ℝ} (ht : 0 ≤ t) {k : ℕ} (hcomm : D.CrossBandCommute n t k)
    (pre : Config k (fun v => Fin (n v)) → ℂ) (h : H)
    {F : (SiteConfig n → ℂ) → ℝ} (hF : Continuous F) :
    IntegrableOn (fun p => D.oldFourierCoherentIntegral n t k pre p h F) (Icc 0 1) :=
  (intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).mp
    (D.intervalIntegrable_oldFourierCoherentIntegral n hD ht hcomm pre h hF)

/-- AE strong measurability also holds on the closed unit interval. -/
theorem aestronglyMeasurable_Icc_oldFourierCoherentIntegral (hD : D.IsAdmissible)
    {t : ℝ} (ht : 0 ≤ t) {k : ℕ} (hcomm : D.CrossBandCommute n t k)
    (pre : Config k (fun v => Fin (n v)) → ℂ) (h : H)
    {F : (SiteConfig n → ℂ) → ℝ} (hF : Continuous F) :
    AEStronglyMeasurable (fun p => D.oldFourierCoherentIntegral n t k pre p h F)
      (volume.restrict (Icc 0 1)) :=
  (D.integrableOn_Icc_oldFourierCoherentIntegral n hD ht hcomm pre h hF).aestronglyMeasurable

variable [Fintype H]

/-- Fixed good-history selection and history weights preserve AE strong
measurability. This bridge is independent of the kind of transport round. -/
theorem aestronglyMeasurable_sum_oldFourierCoherentIntegral (hD : D.IsAdmissible)
    {t : ℝ} (ht : 0 ≤ t) {k : ℕ} (hcomm : D.CrossBandCommute n t k)
    (pre : Config k (fun v => Fin (n v)) → ℂ)
    (good : H → Prop) [DecidablePred good] (w : H → ℝ)
    (F : H → (SiteConfig n → ℂ) → ℝ) (hF : ∀ h, Continuous (F h)) :
    AEStronglyMeasurable (fun p => ∑ h, if good h then
      w h * D.oldFourierCoherentIntegral n t k pre p h (F h) else 0)
      (volume.restrict (Ioo 0 1)) := by
  apply Finset.aestronglyMeasurable_fun_sum
  intro h _
  by_cases hg : good h
  · simp only [hg, ↓reduceIte]
    exact aestronglyMeasurable_const.mul
      (D.aestronglyMeasurable_oldFourierCoherentIntegral n hD ht hcomm pre h (hF h))
  · simp only [hg, ↓reduceIte]
    exact aestronglyMeasurable_const

/-- Finite history sums are genuinely interval integrable, with the same
supplied vector, predicate and weights in every term. -/
theorem intervalIntegrable_sum_oldFourierCoherentIntegral (hD : D.IsAdmissible)
    {t : ℝ} (ht : 0 ≤ t) {k : ℕ} (hcomm : D.CrossBandCommute n t k)
    (pre : Config k (fun v => Fin (n v)) → ℂ)
    (good : H → Prop) [DecidablePred good] (w : H → ℝ)
    (F : H → (SiteConfig n → ℂ) → ℝ) (hF : ∀ h, Continuous (F h)) :
    IntervalIntegrable (fun p => ∑ h, if good h then
      w h * D.oldFourierCoherentIntegral n t k pre p h (F h) else 0) volume 0 1 := by
  have hint (h : H) : IntervalIntegrable (fun p => if good h then
      w h * D.oldFourierCoherentIntegral n t k pre p h (F h) else 0) volume 0 1 := by
    by_cases hg : good h
    · simp only [hg, ↓reduceIte]
      exact (D.intervalIntegrable_oldFourierCoherentIntegral n hD ht hcomm pre h (hF h)).const_mul _
    · simp only [hg, ↓reduceIte]
      exact intervalIntegrable_const
  simpa only [Finset.sum_apply] using
    (IntervalIntegrable.sum Finset.univ (fun h _ => hint h))

end TensorPower.ReplicaTransport.TransportData
