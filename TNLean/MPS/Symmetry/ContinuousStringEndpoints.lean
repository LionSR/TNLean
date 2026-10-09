/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.PhysicalStringAsymptotics
import QICLean.Channel.Irreducible.AdjointFamily

/-!
# Identity endpoints for continuous physical symmetries

Source: arXiv:0802.0447, lines 291–296 and 331–359.
The fixed-twist result has no extra invariance assumption on the density.
-/

open scoped Matrix BigOperators ComplexOrder MatrixOrder TNOperatorSpace
open Filter

namespace MPSTensor

variable {d D : ℕ}
local notation "Mat" => Matrix (Fin D) (Fin D) ℂ

/-- Stationarity preserves the trace functional. Supporting identity for
arXiv:0802.0447, lines 291–296. This specialization reuses the generic
QIC trace-adjoint pairing and Kraus-adjoint identification. -/
private theorem trace_stationary_transfer (A : MPSTensor d D) (Λ : Mat)
    (hΛfix : Kraus.transferMap (fun i => (A i)ᴴ) Λ = Λ) (X : Mat) :
    Matrix.trace (Λ * Kraus.transferMap A X) = Matrix.trace (Λ * X) := by
  calc
    Matrix.trace (Λ * Kraus.transferMap A X) =
        Matrix.trace (Matrix.traceAdjointMap (Kraus.transferMap A) Λ * X) :=
      (Matrix.trace_traceAdjointMap_mul (Kraus.transferMap A) Λ X).symm
    _ = Matrix.trace (Kraus.transferMap (fun i => (A i)ᴴ) Λ * X) := by
      rw [Kraus.traceAdjointMap_mapLM_eq_mapLM_conjTranspose]
    _ = Matrix.trace (Λ * X) := by rw [hΛfix]

/-- Scalar infinitesimal physical action is impossible for a nonscalar virtual
matrix in canonical pure form. Source: arXiv:0802.0447, lines 147–160 and
352–359, with scalar virtual generators explicitly excluded. -/
theorem eq_scalar_of_scalar_commutator_action
    (A : MPSTensor d D) (Λ H : Mat)
    (hΛtr : Matrix.trace Λ = 1)
    (hΛfix : Kraus.transferMap (fun i => (A i)ᴴ) Λ = Λ)
    (hNorm : Kraus.transferMap A 1 = 1)
    (hFix : ∀ X : Mat, Kraus.transferMap A X = X → ∃ z : ℂ, X = z • 1)
    (c : ℂ) (hComm : ∀ i, H * A i - A i * H = c • A i) :
    c = 0 ∧ ∃ z : ℂ, H = z • 1 := by
  have hAA : ∑ i, A i * (A i)ᴴ = 1 := by
    simpa only [Kraus.transferMap_apply, Matrix.mul_one] using hNorm
  have hdiff : H - Kraus.transferMap A H = c • 1 := by
    calc
      H - Kraus.transferMap A H =
          ∑ i, (H * A i - A i * H) * (A i)ᴴ := by
        simp only [Matrix.sub_mul, Finset.sum_sub_distrib, Matrix.mul_assoc,
          ← Matrix.mul_sum, hAA, Matrix.mul_one, Kraus.transferMap_apply]
      _ = ∑ i, (c • A i) * (A i)ᴴ := by simp_rw [hComm]
      _ = c • 1 := by simp only [smul_mul_assoc, ← Finset.smul_sum, hAA]
  have hc : c = 0 := by
    have ht := congrArg (fun X : Mat => Matrix.trace (Λ * X)) hdiff
    simpa only [Matrix.mul_sub, Matrix.trace_sub,
      trace_stationary_transfer A Λ hΛfix, sub_self, Matrix.mul_smul,
      Matrix.mul_one, Matrix.trace_smul, hΛtr, smul_eq_mul, mul_one] using ht.symm
  refine ⟨hc, hFix H ?_⟩
  rw [hc, zero_smul, sub_eq_zero] at hdiff
  exact hdiff.symm

/-- The complex identity-endpoint correlator converges without demodulation
for an unphased virtual intertwiner. Its limit is the nonnegative quantity
`conj (tr (Λ V)) * tr (Λ V)`, hence `|tr (Λ V)|²`.
Source: arXiv:0802.0447, lines 291–296. -/
theorem physicalStringOrderParam_identity_tendsto
    [NeZero D] (A : MPSTensor d D)
    (hIrr : IsIrreducibleMap (Kraus.transferMap A))
    (hPrim : IsPrimitive (Kraus.transferMap A))
    (Λ : Mat) (hΛpos : Λ.PosDef) (hΛtr : Matrix.trace Λ = 1)
    (hΛfix : Kraus.transferMap (fun i => (A i)ᴴ) Λ = Λ)
    (hNorm : Kraus.transferMap A 1 = 1)
    (u : Matrix (Fin d) (Fin d) ℂ) (V : Mat)
    (hV : V * Vᴴ = 1)
    (hInter : ∀ i, ∑ j, u i j • A j = V * A i * Vᴴ) :
    Tendsto (fun N : ℕ => physicalStringOrderParam A Λ 1 1 u N) atTop
      (nhds (starRingEnd ℂ (Matrix.trace (Λ * V)) * Matrix.trace (Λ * V))) := by
  have hlim := physicalStringOrderParam_phase_adjusted_tendsto
    A hIrr hPrim Λ hΛpos hΛtr hΛfix hNorm 1 1 u V 1 hV (by simp)
    (by simpa only [one_smul] using hInter)
  have hconj : Matrix.trace (Λ * Vᴴ) =
      starRingEnd ℂ (Matrix.trace (Λ * V)) := by
    calc
      Matrix.trace (Λ * Vᴴ) = Matrix.trace ((Λ * V)ᴴ) := by
        rw [Matrix.conjTranspose_mul, hΛpos.isHermitian.eq, Matrix.trace_mul_comm]
      _ = _ := Matrix.trace_conjTranspose _
  simpa only [one_pow, inv_one, one_mul, twistedTransferMap_one, hNorm,
    Matrix.mul_one, trace_stationary_transfer A Λ hΛfix, hconj] using hlim

/-- Along a continuous virtual path starting at identity, the source endpoint
trace is nonzero near zero. No group law or covariance is required for this
continuity step. Source: arXiv:0802.0447, lines 291–296. -/
theorem eventually_trace_virtualPath_ne_zero
    (Λ : Mat) (hΛtr : Matrix.trace Λ = 1)
    (V : ℝ → Mat) (hV : ContinuousAt V 0) (hV0 : V 0 = 1) :
    ∀ᶠ t in nhds (0 : ℝ), Matrix.trace (Λ * V t) ≠ 0 := by
  have htrace : ContinuousAt (fun t => Matrix.trace (Λ * V t)) 0 := by
    fun_prop
  have hzero : Matrix.trace (Λ * V 0) ≠ 0 := by simp [hV0, hΛtr]
  exact htrace (isClosed_singleton.isOpen_compl.mem_nhds hzero)

end MPSTensor
