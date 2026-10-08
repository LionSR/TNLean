/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.ContinuousPhysicalCovariance
import TNLean.MPS.Symmetry.ContinuousStringEndpoints

/-!
# Continuous effective symmetries give physical string order

A nonscalar Hermitian virtual generator gives physical string order with
identity endpoints for every sufficiently small nonzero parameter.

Source: arXiv:0802.0447, lines 291–296 and 331–359. The effective convention
excludes the scalar virtual line. The supported lift fixes unused physical
support; this is not a classification of all ambient physical stabilizers.
-/

open scoped Matrix BigOperators ComplexOrder MatrixOrder TNOperatorSpace
open scoped Matrix.Norms.L2Operator Topology
open Filter
namespace MPSTensor
variable {d D : ℕ}
local notation "Mat" => Matrix (Fin D) (Fin D) ℂ

/-- A nonscalar Hermitian virtual generator satisfying the infinitesimal
transfer criterion produces a single Hermitian physical generator. At every
sufficiently small nonzero parameter, its physical twist is nonscalar and the
actual complex string correlator with identity endpoints tends to the strictly
positive real number `|tr (Λ exp(i t H))|²`.

Source: arXiv:0802.0447, lines 291–296 and 352–359, with the effective
nontriviality convention excluding scalar virtual generators. This proves the
forward implication from an effective generator, not a full classification. -/
theorem pureCanonical_continuous_generator_identity_endpoints
    [NeZero D] (A : MPSTensor d D)
    (Λ : Mat) (hΛpos : Λ.PosDef) (hΛtr : Matrix.trace Λ = 1)
    (hΛfix : Kraus.transferMap (fun i => (A i)ᴴ) Λ = Λ)
    (hNorm : Kraus.transferMap A 1 = 1)
    (hPure : ∀ (ev : ℂ) (X : Mat), X ≠ 0 → ‖ev‖ = 1 →
      Kraus.transferMap A X = ev • X → ev = 1 ∧ ∃ c : ℂ, X = c • 1)
    (H : Mat) (hH : H.IsHermitian) (hHnon : ∀ c : ℂ, H ≠ c • 1)
    (hComm : Commute (rowAdjointGenerator H) (rowTransferMatrix A)) :
    ∃ K : Matrix (Fin d) (Fin d) ℂ,
      K.IsHermitian ∧ (∀ c : ℂ, K ≠ c • 1) ∧
      (∀ t : ℝ, CondC1 A (Matrix.hermitianUnitaryPath K t)
        (Matrix.hermitianUnitaryPath H t)) ∧
      (∀ t : ℝ, Matrix.hermitianUnitaryPath K t *
        (Matrix.hermitianUnitaryPath K t)ᴴ = 1) ∧
      ∀ᶠ t in 𝓝[≠] (0 : ℝ),
        (∀ c : ℂ, Matrix.hermitianUnitaryPath K t ≠ c • 1) ∧
        0 < ‖Matrix.trace (Λ * Matrix.hermitianUnitaryPath H t)‖ ^ 2 ∧
        Tendsto
          (fun N : ℕ => physicalStringOrderParam A Λ 1 1
            (Matrix.hermitianUnitaryPath K t) N) atTop
          (nhds ((‖Matrix.trace (Λ * Matrix.hermitianUnitaryPath H t)‖ ^ 2 : ℝ) : ℂ)) ∧
        HasPhysicalStringOrderWith A Λ 1 1 (Matrix.hermitianUnitaryPath K t) := by
  obtain ⟨K, hK, hInf, hCov⟩ := exists_hermitian_physical_generator A H hH hComm
  have hFix : ∀ X : Mat, Kraus.transferMap A X = X → ∃ c : ℂ, X = c • 1 := by
    intro X hX
    rcases eq_or_ne X 0 with rfl | hXne
    · exact ⟨0, by simp⟩
    · exact (hPure 1 X hXne (by simp) (by simpa using hX)).2
  have hKnon : ∀ c : ℂ, K ≠ c • 1 := by
    intro c hc
    have hScalar : ∀ i, H * A i - A i * H = c • A i := by
      intro i
      rw [← hInf i, hc]
      simp [Matrix.one_apply]
    obtain ⟨_, z, hz⟩ :=
      eq_scalar_of_scalar_commutator_action A Λ H hΛtr hΛfix hNorm hFix c hScalar
    exact hHnon z hz
  obtain ⟨hIrr, hPrim⟩ :=
    pureCanonical_isIrreducibleMap_and_isPrimitive A Λ hΛpos hΛfix hNorm hPure
  have htrace : ∀ᶠ t in 𝓝[≠] (0 : ℝ),
      Matrix.trace (Λ * Matrix.hermitianUnitaryPath H t) ≠ 0 :=
    (eventually_trace_virtualPath_ne_zero Λ hΛtr (Matrix.hermitianUnitaryPath H)
      (Matrix.continuous_hermitianUnitaryPath H).continuousAt
      (Matrix.hermitianUnitaryPath_zero H)).filter_mono nhdsWithin_le_nhds
  refine ⟨K, hK, hKnon, hCov, Matrix.hermitianUnitaryPath_mul_conjTranspose K hK, ?_⟩
  filter_upwards [Matrix.eventually_hermitianUnitaryPath_nonscalar K hKnon, htrace]
    with t ht htr
  have hpos : 0 < ‖Matrix.trace (Λ * Matrix.hermitianUnitaryPath H t)‖ ^ 2 :=
    pow_pos (norm_pos_iff.mpr htr) 2
  have hlim : Tendsto
      (fun N : ℕ => physicalStringOrderParam A Λ 1 1
        (Matrix.hermitianUnitaryPath K t) N) atTop
      (nhds ((‖Matrix.trace (Λ * Matrix.hermitianUnitaryPath H t)‖ ^ 2 : ℝ) : ℂ)) := by
    simpa only [Complex.conj_mul', Complex.ofReal_pow] using
      physicalStringOrderParam_identity_tendsto A hIrr hPrim Λ hΛpos hΛtr hΛfix hNorm
        (Matrix.hermitianUnitaryPath K t) (Matrix.hermitianUnitaryPath H t)
        (Matrix.hermitianUnitaryPath_mul_conjTranspose H hH t) (hCov t)
  refine ⟨ht, hpos, hlim, _, hpos, ?_⟩
  simpa using hlim.norm

/-- Effective continuous virtual symmetry gives physical string order with
Hermitian identity endpoints. Source: arXiv:0802.0447, lines 291–296 and
352–359, under the explicitly stated scalar-exclusion convention. -/
theorem hasPhysicalStringOrder_of_continuous_generator
    [NeZero D] (A : MPSTensor d D)
    (Λ : Mat) (hΛpos : Λ.PosDef) (hΛtr : Matrix.trace Λ = 1)
    (hΛfix : Kraus.transferMap (fun i => (A i)ᴴ) Λ = Λ)
    (hNorm : Kraus.transferMap A 1 = 1)
    (hPure : ∀ (ev : ℂ) (X : Mat), X ≠ 0 → ‖ev‖ = 1 →
      Kraus.transferMap A X = ev • X → ev = 1 ∧ ∃ c : ℂ, X = c • 1)
    (H : Mat) (hH : H.IsHermitian) (hHnon : ∀ c : ℂ, H ≠ c • 1)
    (hComm : Commute (rowAdjointGenerator H) (rowTransferMatrix A)) :
    HasPhysicalStringOrder A Λ := by
  obtain ⟨K, _, _, _, hUnitary, hNear⟩ :=
    pureCanonical_continuous_generator_identity_endpoints
      A Λ hΛpos hΛtr hΛfix hNorm hPure H hH hHnon hComm
  obtain ⟨t, ht, _, _, hSO⟩ := hNear.exists
  exact ⟨Matrix.hermitianUnitaryPath K t, 1, 1, hUnitary t, ht, hSO⟩

end MPSTensor
