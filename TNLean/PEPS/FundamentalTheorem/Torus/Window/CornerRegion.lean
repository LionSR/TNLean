/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.FundamentalTheorem.Torus.Window.WindowComplement
import TNLean.PEPS.FundamentalTheorem.Torus.TorusEdgeBlockingCrossing
import TNLean.PEPS.FundamentalTheorem.Torus.TorusGaugedWeightCovariance
import TNLean.PEPS.Injectivity.Normal.NormalSquareInjectivity
import TNLean.PEPS.FundamentalTheorem.Normal.RegionInsertion.ProportionalityFromAbsorbed

/-!
# Corner comparison regions at the minimal torus sizes

For positive rectangular window lengths L and K, let S be the rectangle of size
(L + 1) × (K + 1) starting at (L, K), and let R be S with its lower-left vertex removed.
If every L × K arc window is injective, then R, S and both complements are injective
when the torus has width at least 2L + 1 and height at least 2K + 1. The proof writes
R as the union of two rectangles and its complement as the union of the complement
of S and one L × K rectangle.

These are the one-site comparison regions used in arXiv:1804.04964, proof of
Theorem 3, lines 1544–1571 and the normal TI PEPS corollary. They allow the scalar
comparison without a separate lower bound of seven on either torus dimension.

## Scalar comparison from injective windows and absorbed edge gauges

The corner comparison regions give the final scalar and its normalization for
translation-invariant normal PEPS on a torus of width at least 2L + 1 and height
at least 2K + 1. The edge gauge family and equality of bond dimensions are supplied
as established mathematical data. This module proves their scalar consequence;
it does not assume these data as part of the normal-tensor hypotheses.

The argument is the final comparison in arXiv:1804.04964, proof of Theorem 3,
lines 1544–1571, and applies to all positive window lengths.
-/

section

namespace TNLean.PEPS

variable {width height : ℕ} [NeZero width] [NeZero height]
variable {L K : ℕ}

/-- The (L + 1) × (K + 1) rectangle starting at (L, K). -/
def windowCornerRectangle (L K : ℕ) : Finset (TorusVertex width height) :=
  torusContiguousRectangle L K (L + 1) (K + 1)

/-- The comparison rectangle with its lower-left vertex omitted, expressed as two rectangles. -/
def windowCornerRegion (L K : ℕ) : Finset (TorusVertex width height) :=
  torusContiguousRectangle (L + 1) K L (K + 1) ∪
    torusContiguousRectangle L (K + 1) (L + 1) K

/-- The vertex (L, K) omitted from the comparison region. -/
def windowCornerVertex (L K : ℕ) : TorusVertex width height :=
  ((L : ZMod width), (K : ZMod height))

/-- Membership in the punctured comparison rectangle, expressed in coordinate values. -/
theorem mem_windowCornerRegion (v : TorusVertex width height) :
    v ∈ windowCornerRegion L K ↔
      (L + 1 ≤ v.1.val ∧ v.1.val < 2 * L + 1 ∧ K ≤ v.2.val ∧
        v.2.val < 2 * K + 1) ∨
      (L ≤ v.1.val ∧ v.1.val < 2 * L + 1 ∧ K + 1 ≤ v.2.val ∧
        v.2.val < 2 * K + 1) := by
  simp only [windowCornerRegion, Finset.mem_union, mem_torusContiguousRectangle]
  omega

/-- At the minimal size bounds, the corner vertex has precisely the coordinate values (L, K). -/
theorem eq_windowCornerVertex_iff (hw : 2 * L + 1 ≤ width)
    (hh : 2 * K + 1 ≤ height) (v : TorusVertex width height) :
    v = windowCornerVertex L K ↔ v.1.val = L ∧ v.2.val = K := by
  constructor
  · rintro rfl
    exact ⟨ZMod.val_cast_of_lt (by omega), ZMod.val_cast_of_lt (by omega)⟩
  · rintro ⟨h1, h2⟩
    refine Prod.ext (ZMod.val_injective width ?_) (ZMod.val_injective height ?_)
    · rw [h1]
      exact (ZMod.val_cast_of_lt (by omega : L < width)).symm
    · rw [h2]
      exact (ZMod.val_cast_of_lt (by omega : K < height)).symm

/-- The omitted corner vertex is outside the comparison region. -/
theorem windowCornerVertex_notMem (hw : 2 * L + 1 ≤ width)
    (hh : 2 * K + 1 ≤ height) :
    (windowCornerVertex L K : TorusVertex width height) ∉
      windowCornerRegion L K := by
  rw [mem_windowCornerRegion]
  have h1 : (windowCornerVertex L K : TorusVertex width height).1.val = L :=
    ZMod.val_cast_of_lt (by omega)
  have h2 : (windowCornerVertex L K : TorusVertex width height).2.val = K :=
    ZMod.val_cast_of_lt (by omega)
  omega

/-- Restoring the omitted vertex completes the comparison rectangle. -/
theorem insert_windowCornerVertex_windowCornerRegion (hw : 2 * L + 1 ≤ width)
    (hh : 2 * K + 1 ≤ height) :
    insert (windowCornerVertex L K : TorusVertex width height)
      (windowCornerRegion L K) = windowCornerRectangle L K := by
  ext v
  rw [Finset.mem_insert, mem_windowCornerRegion, eq_windowCornerVertex_iff hw hh,
    windowCornerRectangle, mem_torusContiguousRectangle]
  omega

/-- The complement is covered by the completed rectangle's complement and one window. -/
theorem compl_windowCornerRegion_eq_union (hL : 0 < L) (hK : 0 < K) :
    (Finset.univ \ windowCornerRegion L K : Finset (TorusVertex width height)) =
      (Finset.univ \ windowCornerRectangle L K) ∪
        torusContiguousRectangle 1 1 L K := by
  ext v
  simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_union,
    mem_windowCornerRegion, windowCornerRectangle,
    mem_torusContiguousRectangle]
  omega

namespace NormalTorusArcWindowInjectivityHypotheses
variable {κ : RegionInjectivityData (TorusVertex width height)}

/-- A non-wrapping rectangle containing a full injective window is injective. -/
private theorem contiguousRectangle_injective
    (h : NormalTorusArcWindowInjectivityHypotheses L K κ)
    (hUnion : RegionInjectivityUnionClosure κ) (hL : 0 < L) (hK : 0 < K)
    {xStart yStart xLen yLen : ℕ} (hx : L ≤ xLen) (hy : K ≤ yLen)
    (hxw : xStart + xLen ≤ width) (hyh : yStart + yLen ≤ height) :
    κ.IsInjective (torusContiguousRectangle xStart yStart xLen yLen) := by
  rw [← torusArcRectangle_eq_torusContiguousRectangle xStart yStart xLen yLen
    (by omega) (by omega) hxw hyh]
  exact h.arcRectangle_injective hUnion hL hK hx hy (by omega) (by omega)

/-- The punctured comparison rectangle is injective by the union of its two rectangles. -/
theorem windowCornerRegion_injective
    (h : NormalTorusArcWindowInjectivityHypotheses L K κ)
    (hUnion : RegionInjectivityUnionClosure κ) (hL : 0 < L) (hK : 0 < K)
    (hw : 2 * L + 1 ≤ width) (hh : 2 * K + 1 ≤ height) :
    κ.IsInjective (windowCornerRegion L K : Finset (TorusVertex width height)) := by
  unfold windowCornerRegion
  exact hUnion.union_injective
    (h.contiguousRectangle_injective hUnion hL hK (by omega) (by omega)
      (by omega) (by omega))
    (h.contiguousRectangle_injective hUnion hL hK (by omega) (by omega)
      (by omega) (by omega))

/-- The completed comparison rectangle is injective. -/
theorem windowCornerRectangle_injective
    (h : NormalTorusArcWindowInjectivityHypotheses L K κ)
    (hUnion : RegionInjectivityUnionClosure κ) (hL : 0 < L) (hK : 0 < K)
    (hw : 2 * L + 1 ≤ width) (hh : 2 * K + 1 ≤ height) :
    κ.IsInjective (windowCornerRectangle L K : Finset (TorusVertex width height)) := by
  exact h.contiguousRectangle_injective hUnion hL hK (by omega) (by omega)
    (by omega) (by omega)

/-- The complement of the completed comparison rectangle is injective by two arc bands. -/
theorem compl_windowCornerRectangle_injective
    (h : NormalTorusArcWindowInjectivityHypotheses L K κ)
    (hUnion : RegionInjectivityUnionClosure κ) (hL : 0 < L) (hK : 0 < K)
    (hw : 2 * L + 1 ≤ width) (hh : 2 * K + 1 ≤ height) :
    κ.IsInjective (Finset.univ \ (windowCornerRectangle L K :
      Finset (TorusVertex width height))) := by
  rw [windowCornerRectangle,
    ← torusArcRectangle_eq_torusContiguousRectangle L K (L + 1) (K + 1)
      (by omega) (by omega) (by omega) (by omega),
    compl_torusArcRectangle _ _ _ (by omega) (by omega)]
  exact hUnion.union_injective
    (h.arcRectangle_injective hUnion hL hK (by omega) (by omega) (by omega) (by omega))
    (h.arcRectangle_injective hUnion hL hK (by omega) (by omega) (by omega) (by omega))

/-- The complement of the punctured comparison rectangle is injective by adding one window. -/
theorem compl_windowCornerRegion_injective
    (h : NormalTorusArcWindowInjectivityHypotheses L K κ)
    (hUnion : RegionInjectivityUnionClosure κ) (hL : 0 < L) (hK : 0 < K)
    (hw : 2 * L + 1 ≤ width) (hh : 2 * K + 1 ≤ height) :
    κ.IsInjective (Finset.univ \ (windowCornerRegion L K :
      Finset (TorusVertex width height))) := by
  rw [compl_windowCornerRegion_eq_union hL hK]
  exact hUnion.union_injective
    (h.compl_windowCornerRectangle_injective hUnion hL hK hw hh)
    (h.contiguousRectangle_injective hUnion hL hK (by omega) (by omega)
      (by omega) (by omega))

end NormalTorusArcWindowInjectivityHypotheses

section BoundaryEdges
variable [Fact (1 < width)] [Fact (1 < height)]

/-- The upward edge from the omitted vertex crosses the punctured comparison region. -/
theorem isRegionBoundaryEdge_windowCornerRegion (hK : 0 < K)
    (hw : 2 * L + 1 ≤ width) (hh : 2 * K + 1 ≤ height) :
    IsRegionBoundaryEdge (G := torusGraph width height) (windowCornerRegion L K)
      (torusUpEdge (windowCornerVertex L K : TorusVertex width height)) := by
  have h1 : (windowCornerVertex L K : TorusVertex width height).1.val = L :=
    ZMod.val_cast_of_lt (by omega)
  have h2 : (windowCornerVertex L K : TorusVertex width height).2.val = K :=
    ZMod.val_cast_of_lt (by omega)
  obtain ⟨hf, hs⟩ := torusUpEdge_endpoints_of_lt
    (p := windowCornerVertex L K) (by rw [h2]; omega)
  rw [IsRegionBoundaryEdge, hf, hs]
  refine Or.inr ⟨windowCornerVertex_notMem hw hh, ?_⟩
  rw [mem_windowCornerRegion]
  have h3 : ((windowCornerVertex L K : TorusVertex width height).2 + 1).val =
      K + 1 := by
    rw [show (windowCornerVertex L K : TorusVertex width height).2 + 1 =
        ((K + 1 : ℕ) : ZMod height) by simp [windowCornerVertex]]
    exact ZMod.val_cast_of_lt (by omega)
  dsimp only
  omega

/-- The upward edge just below the corner crosses the completed comparison rectangle. -/
theorem isRegionBoundaryEdge_windowCornerRectangle (hK : 0 < K)
    (hw : 2 * L + 1 ≤ width) (hh : 2 * K + 1 ≤ height) :
    IsRegionBoundaryEdge (G := torusGraph width height) (windowCornerRectangle L K)
      (torusUpEdge ((L : ZMod width), ((K - 1 : ℕ) : ZMod height))) := by
  have hx : (L : ZMod width).val = L := ZMod.val_cast_of_lt (by omega)
  have hy : ((K - 1 : ℕ) : ZMod height).val = K - 1 := ZMod.val_cast_of_lt (by omega)
  have heq : ((K - 1 : ℕ) : ZMod height) + 1 = (K : ZMod height) := by
    have hnat : K - 1 + 1 = K := by omega
    simpa only [Nat.cast_add, Nat.cast_one] using
      congrArg (fun n : ℕ ↦ (n : ZMod height)) hnat
  obtain ⟨hf, hs⟩ := torusUpEdge_endpoints_of_lt
    (p := ((L : ZMod width), ((K - 1 : ℕ) : ZMod height))) (by dsimp; rw [hy]; omega)
  rw [IsRegionBoundaryEdge, hf, hs]
  refine Or.inr ⟨?_, ?_⟩
  · rw [windowCornerRectangle, mem_torusContiguousRectangle]
    dsimp only
    omega
  · rw [windowCornerRectangle, mem_torusContiguousRectangle]
    dsimp only
    rw [heq, hx, ZMod.val_cast_of_lt (by omega : K < height)]
    omega

end BoundaryEdges

end TNLean.PEPS

end

section

open ManyBody (Edge)

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

end
