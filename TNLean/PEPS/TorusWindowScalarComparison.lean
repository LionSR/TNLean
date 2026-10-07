/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.TorusWindowCornerRegion
import TNLean.PEPS.TorusTranslatedScalarComparison
import TNLean.PEPS.NormalSquareInjectivity
import TNLean.PEPS.RegionBlock.ProportionalityFromAbsorbed

/-!
# Scalar comparison from injective windows and absorbed edge gauges

The corner comparison regions give the final scalar and its normalization for
translation-invariant normal PEPS on a torus of width at least 2L + 1 and height
at least 2K + 1. The edge gauge family and equality of bond dimensions are supplied
as established mathematical data. This module proves their scalar consequence;
it does not assume these data as part of the normal-tensor hypotheses.

The argument is the final comparison in arXiv:1804.04964, proof of Theorem 3,
lines 1544–1571, and applies to all positive window lengths.
-/

namespace TNLean.PEPS
open scoped Matrix
variable {width height d L K : ℕ} [NeZero width] [NeZero height]
variable [Fact (1 < width)] [Fact (1 < height)]

/-- Positive-length injective arc windows and an actual covariant absorbed edge gauge imply
a common site scalar whose torus-volume power is one. This is the final comparison in
arXiv:1804.04964, proof of Theorem 3, lines 1544–1571, at the minimal window size bounds. -/
theorem exists_scalar_of_normalArcWindows_absorbedGauge
    (A B : Tensor (torusGraph width height) d)
    (hA : NormalTorusArcWindowInjectivityHypotheses L K (regionInjectivityDataOf A))
    (hB : NormalTorusArcWindowInjectivityHypotheses L K (regionInjectivityDataOf B))
    (hATI : IsTorusTranslationInvariant A) (hBTI : IsTorusTranslationInvariant B)
    (hAB : SameState A B)
    (hposA : ∀ e : Edge (torusGraph width height), 0 < A.bondDim e)
    (hposB : ∀ e : Edge (torusGraph width height), 0 < B.bondDim e)
    (hL : 0 < L) (hK : 0 < K)
    (hxw : 2 * L + 1 ≤ width) (hyh : 2 * K + 1 ≤ height)
    (hbond : A.bondDim = B.bondDim)
    (X : (e : Edge (torusGraph width height)) → GL (Fin (B.bondDim e)) ℂ)
    (hXcov : IsTranslationCovariantGaugeFamily B X)
    (hedge : ∀ (e : Edge (torusGraph width height)) (σ : TorusVertex width height → Fin d)
        (N : Matrix (Fin (A.bondDim e)) (Fin (A.bondDim e)) ℂ),
      edgeInsertedCoeff A e σ N = edgeInsertedCoeff (applyGauge B X) e σ
        (Matrix.reindexAlgEquiv ℂ ℂ (finCongr (congr_fun hbond e)) N)) :
    ∃ lam : ℂ,
      (∀ (v : TorusVertex width height)
        (η : (ie : IncidentEdge (torusGraph width height) v) → Fin (A.bondDim ie.1))
        (σ : Fin d),
        A.component v η σ =
          lam * gaugeVertex B X v (fun ie => Fin.cast (congr_fun hbond ie.1) (η ie)) σ) ∧
      lam ^ (width * height) = 1 := by
  let R : Finset (TorusVertex width height) := windowCornerRegion L K
  let S : Finset (TorusVertex width height) := windowCornerRectangle L K
  let v₀ : TorusVertex width height := windowCornerVertex L K
  have hinsert : insert v₀ R = S := insert_windowCornerVertex_windowCornerRegion hxw hyh
  have inj (T : Tensor (torusGraph width height) d)
      (hT : NormalTorusArcWindowInjectivityHypotheses L K (regionInjectivityDataOf T))
      (hposT : ∀ e : Edge (torusGraph width height), 0 < T.bondDim e) :
      RegionBlockedTensorInjective T R ∧ RegionBlockedTensorInjective T S ∧
      RegionBlockedTensorInjective T (Finset.univ \ R) ∧
      RegionBlockedTensorInjective T (Finset.univ \ S) := by
    have hU := regionInjectivityUnionClosure_of_overlap T hposT
    exact ⟨hT.windowCornerRegion_injective hU hL hK hxw hyh,
      hT.windowCornerRectangle_injective hU hL hK hxw hyh,
      hT.compl_windowCornerRegion_injective hU hL hK hxw hyh,
      hT.compl_windowCornerRectangle_injective hU hL hK hxw hyh⟩
  obtain ⟨hRA, hSA, hCRA, hCSA⟩ := inj A hA hposA
  obtain ⟨hRB, hSB, hCRB, hCSB⟩ := inj B hB hposB
  have liftC (Q : Finset (TorusVertex width height))
      (hQ : RegionBlockedTensorInjective B Q) :
      RegionBlockedTensorInjective (reindexTensor (applyGauge B X) hbond) Q :=
    regionBlockedTensorInjective_reindexTensor (applyGauge B X) hbond Q
      (regionBlockedTensorInjective_applyGauge B X Q hQ)
  let _ : Nonempty {e : Edge (torusGraph width height) // IsRegionBoundaryEdge R e} :=
    ⟨⟨torusUpEdge v₀, isRegionBoundaryEdge_windowCornerRegion hK hxw hyh⟩⟩
  let _ : Nonempty {e : Edge (torusGraph width height) // IsRegionBoundaryEdge S e} :=
    ⟨⟨torusUpEdge ((L : ZMod width), ((K - 1 : ℕ) : ZMod height)),
      isRegionBoundaryEdge_windowCornerRectangle hK hxw hyh⟩⟩
  obtain ⟨cR, hcR0, hRp⟩ := twoBlockProportional_of_edgeAbsorbed A B hbond X R
    hRA hCRA (liftC R hRB) (liftC _ hCRB) hedge
  obtain ⟨cS, _, hSp⟩ := twoBlockProportional_of_edgeAbsorbed A B hbond X S
    hSA hCSA (liftC S hSB) (liftC _ hCSB) hedge
  rw [← hinsert] at hSp
  have hPV := component_eq_gaugeVertex_of_translatedProportional hATI hBTI hXcov
    hbond hposA R v₀ (windowCornerVertex_notMem hxw hyh) hcR0 hRB hRp hSp
  exact ⟨cS / cR, hPV,
    lambda_pow_card_torus_eq_one A B R hRA hCRA hposA hAB X hbond (cS / cR) hPV⟩

end TNLean.PEPS
