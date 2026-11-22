/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.FundamentalTheorem.Torus.Window.CrossTensorTransfer
import TNLean.PEPS.FundamentalTheorem.Torus.TorusReferenceAbsorbedFamily
import TNLean.PEPS.FundamentalTheorem.Torus.Window.CornerRegion
import TNLean.PEPS.FundamentalTheorem.Torus.Window.GaugeUniqueness

/-!
# Translation-covariant gauges from normal arc windows

Two translation-invariant PEPS tensors defining the same state have equal bond dimensions
and differ by a translation-covariant bond gauge and one scalar. The scalar raised to the
number of torus vertices is one. The horizontal and vertical reference gauges are obtained
from the staircase insertion correspondence, and the local relation follows by comparing
two injective regions that differ by one vertex.

All positive window lengths are allowed, including a unit side. These are the existence
and normalization parts of the normal translation-invariant PEPS corollary in
arXiv:1804.04964. The complete derivation is recorded in
`docs/paper-gaps/peps_normal_ft_2d_overlap.tex`.

**Local fix (nonzero virtual spaces):** the source treats the virtual bond spaces as nonzero
(arXiv:1804.04964, lines 582 and 1037 of `Papers/1804.04964/paper_normal.tex`) without listing
this among the corollary's hypotheses. The theorem here takes the tensor hypothesis
`IsNormalTorusArcWindowPEPS`, whose field `bondDim_pos` carries it, and states no separate
positivity hypothesis. Documented in `docs/paper-gaps/peps_injective_ft_section3_route.tex`.

## The Fundamental Theorem from normal torus windows

The existence and uniqueness statements are assembled here: equality of the torus states
determines the two directional gauges up to scalar, with one common site scalar whose
torus-volume power is one.

**Local fix (nonzero virtual spaces):** the source treats the virtual bond spaces as nonzero
(arXiv:1804.04964, lines 582 and 1037 of `Papers/1804.04964/paper_normal.tex`) without listing
this among the hypotheses of the corollary. Both tensors are taken through
`IsNormalTorusArcWindowPEPS`, which carries the convention as the field `bondDim_pos`, so the
theorem states no separate positivity hypothesis. Documented in
`docs/paper-gaps/peps_injective_ft_section3_route.tex`.
-/

section

open ManyBody (Edge)

namespace TNLean.PEPS

open scoped Matrix

variable {width height d L K : ℕ} [NeZero width] [NeZero height]
variable [Fact (1 < width)] [Fact (1 < height)]

/-- Equal-state normal translation-invariant tensors have a translation-covariant bond
gauge and a scalar whose power at the torus volume is one, at the minimal size bounds.
The bond dimensions, reference gauges and local proportionality are all derived.

Source: arXiv:1804.04964, normal TI PEPS corollary, lines 2368--2444 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem exists_translationCovariantGauge_of_normalArcWindows_sameState
    (A B : Tensor (torusGraph width height) d)
    (hA : IsNormalTorusArcWindowPEPS L K A) (hB : IsNormalTorusArcWindowPEPS L K B)
    (hATI : IsTorusTranslationInvariant A) (hBTI : IsTorusTranslationInvariant B)
    (hAB : SameState A B) (hL : 0 < L) (hK : 0 < K)
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
      lam ^ (width * height) = 1 := by
  have hbond := bondDim_eq_of_normalArcWindows_sameState A B hA hB hATI hBTI hAB
    hL hK hxw hyh
  obtain ⟨hA, hposA⟩ := hA
  obtain ⟨hB, hposB⟩ := hB
  obtain ⟨hEh, Zh, wh, _, hmemh⟩ := exists_staircaseWindowEdgeCoeffIdentityWitness
    (a := 1) (b := 0) A B hA hB hATI hBTI hAB hposA hposB hL hK
    (by omega) (by omega) (by omega) hxw hyh
  let eh := horizontalStaircaseReferenceEdge
    (((1 : ℕ) : ZMod width), ((0 : ℕ) : ZMod height)) L K
  have heh : IsHorizontalTorusEdge eh :=
    isHorizontalTorusEdge_torusRightEdge _
  obtain ⟨ev, hev, hEv, Zv, wv, hmemv⟩ :=
    exists_verticalEdgeCoeffIdentityWitness_of_normalArcWindows A B hA hB hATI hBTI hAB
      hposA hposB hL hK hxw hyh
  obtain ⟨X, hXcov, hedge⟩ :=
    exists_torusCovariantAbsorbedGaugeFamily_of_edgeReferenceWitnesses hATI hBTI
      (by omega) (by omega) hbond hposA eh ev heh hev Zh Zh Zv Zv wh wv hmemh hmemv
  obtain ⟨lam, hComp, hPow⟩ := exists_scalar_of_normalArcWindows_absorbedGauge
    A B hA hB hATI hBTI hAB hposA hposB (by omega) (by omega) hxw hyh
      hbond X hXcov hedge
  exact ⟨hbond, X, lam, hXcov, hComp, hPow⟩

end TNLean.PEPS

end

section

open ManyBody (Edge)

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
    (hA : IsNormalTorusArcWindowPEPS L K A) (hB : IsNormalTorusArcWindowPEPS L K B)
    (hATI : IsTorusTranslationInvariant A) (hBTI : IsTorusTranslationInvariant B)
    (hAB : SameState A B) (hL : 0 < L) (hK : 0 < K)
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
      hAB hL hK hxw hyh
  refine ⟨hbond, X, lam, hXcov, hPV, hPow, ?_⟩
  intro X' lam' hPV' e
  have hposA := hA.bondDim_pos
  have hU := regionInjectivityUnionClosure_of_overlap A hposA
  have hR := hA.windowCornerRegion_injective hU (by omega) (by omega) hxw hyh
  have hCR := hA.compl_windowCornerRegion_injective hU (by omega) (by omega) hxw hyh
  have hPow' := lambda_pow_card_torus_eq_one A B (windowCornerRegion L K)
    hR hCR hposA hAB X' hbond lam' hPV'
  exact torusGauge_unique_scalar_of_normalArcWindows hB hBTI (by omega) (by omega) hxw hyh
    hbond X X' hPV hPow hPV' hPow' e

end TNLean.PEPS

end
