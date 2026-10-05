/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.TorusArcWindowGaugeExistence
import TNLean.PEPS.TorusWindowGaugeUniqueness

/-!
# The Fundamental Theorem from normal torus windows

The existence and uniqueness statements are assembled here: equality of the torus states
determines the two directional gauges up to scalar, with one common site scalar whose
torus-volume power is one.
-/

namespace TNLean.PEPS

open scoped Matrix

variable {width height d L K : ℕ} [NeZero width] [NeZero height]
variable [Fact (1 < width)] [Fact (1 < height)]

/-- The normal translation-invariant PEPS Fundamental Theorem at the minimal torus sizes:
the tensors differ by a covariant bond gauge and a volume-one scalar, and any other
local gauge relation has proportional matrices on every edge.

Source: arXiv:1804.04964, the normal TI PEPS corollary at lines 2297--2318 and
its proof at lines 2320--2444 of `Papers/1804.04964/paper_normal.tex`. -/
theorem fundamentalTheorem_normalTorusArcWindowPEPS
    (A B : Tensor (torusGraph width height) d)
    (hA : NormalTorusArcWindowInjectivityHypotheses L K (regionInjectivityDataOf A))
    (hB : NormalTorusArcWindowInjectivityHypotheses L K (regionInjectivityDataOf B))
    (hATI : IsTorusTranslationInvariant A) (hBTI : IsTorusTranslationInvariant B)
    (hAB : SameState A B)
    (hposA : ∀ e : Edge (torusGraph width height), 0 < A.bondDim e)
    (hposB : ∀ e : Edge (torusGraph width height), 0 < B.bondDim e)
    (hL : 0 < L) (hK : 0 < K)
    (hxw : 2 * L + 1 ≤ width) (hyh : 2 * K + 1 ≤ height) :
    ∃ (hbond : A.bondDim = B.bondDim)
      (X : (e : Edge (torusGraph width height)) → GL (Fin (B.bondDim e)) ℂ)
      (lam : ℂ),
      IsTranslationCovariantGaugeFamily B X ∧
      (∀ (v : TorusVertex width height)
        (η : (ie : IncidentEdge (torusGraph width height) v) → Fin (A.bondDim ie.1))
        (σ : Fin d),
        A.component v η σ =
          lam * gaugeVertex B X v (fun ie => Fin.cast (congr_fun hbond ie.1) (η ie)) σ) ∧
      lam ^ (width * height) = 1 ∧
      ∀ (X' : (e : Edge (torusGraph width height)) → GL (Fin (B.bondDim e)) ℂ)
        (lam' : ℂ),
        (∀ (v : TorusVertex width height)
          (η : (ie : IncidentEdge (torusGraph width height) v) → Fin (A.bondDim ie.1))
          (σ : Fin d),
          A.component v η σ =
            lam' * gaugeVertex B X' v (fun ie => Fin.cast (congr_fun hbond ie.1) (η ie)) σ) →
        ∀ e : Edge (torusGraph width height), ∃ c : ℂˣ,
          (X' e : Matrix (Fin (B.bondDim e)) (Fin (B.bondDim e)) ℂ) =
            (c : ℂ) • (X e : Matrix (Fin (B.bondDim e)) (Fin (B.bondDim e)) ℂ) := by
  obtain ⟨hbond, X, lam, hXcov, hPV, hPow⟩ :=
    exists_translationCovariantGauge_of_normalArcWindows_sameState A B hA hB hATI hBTI
      hAB hposA hposB hL hK hxw hyh
  refine ⟨hbond, X, lam, hXcov, hPV, hPow, ?_⟩
  intro X' lam' hPV' e
  have hU := regionInjectivityUnionClosure_of_overlap A hposA
  have hR := hA.windowCornerRegion_injective hU (by omega) (by omega) hxw hyh
  have hCR := hA.compl_windowCornerRegion_injective hU (by omega) (by omega) hxw hyh
  have hPow' := lambda_pow_card_torus_eq_one A B (windowCornerRegion L K)
    hR hCR hposA hAB X' hbond lam' hPV'
  exact torusGauge_unique_scalar_of_normalArcWindows hB hBTI hposB (by omega) (by omega)
    hxw hyh hbond X X' hPV hPow hPV' hPow' e

end TNLean.PEPS
