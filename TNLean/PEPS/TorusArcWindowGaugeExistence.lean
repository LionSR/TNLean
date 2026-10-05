/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.TorusWindowVerticalWitness
import TNLean.PEPS.TorusReferenceAbsorbedFamily
import TNLean.PEPS.TorusWindowScalarComparison

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
-/

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
      lam ^ (width * height) = 1 := by
  have hbond := bondDim_eq_of_normalArcWindows_sameState A B hA hB hATI hBTI hAB
    hposA hposB hL hK hxw hyh
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
