/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.CZXRectangleBoundary
import TNLean.PEPS.Examples.CZXOpenRegion
import TNLean.PEPS.Examples.CZXBoundaryChain

/-!
# Effective qubit support of an actual CZX rectangle

Nonzero coefficients of the actual open-region contraction force adjacent
clockwise boundary legs to agree on their common plaquette qubit. Thus every
supported native boundary configuration lies in the cyclic adjacent-pair
embedding. Bottom and left native pairs are reversed before applying this
clockwise convention.

**Scope restriction (rectangular region):** both torus periods are at least
three and the region is a positive proper bounded coordinate rectangle.
Normalized reduced-density and nonrectangular-region assertions remain open;
see `docs/paper-gaps/rmp_peps_czx_boundary_chain.tex`.

## References

- [arXiv:1106.4752](https://arxiv.org/abs/1106.4752), CZX model boundary, lines 330–345.
-/

open scoped BigOperators

namespace TNLean.PEPS

variable {width height : ℕ} [NeZero width] [NeZero height]
variable [Fact (2 < width)] [Fact (2 < height)]
local instance : Fact (1 < width) := ⟨by have := Fact.out (p := 2 < width); omega⟩
local instance : Fact (1 < height) := ⟨by have := Fact.out (p := 2 < height); omega⟩

/-- Read the actual rectangle crossing labels in clockwise order, reversing
bottom and left pairs to obtain the cyclic adjacent-plaquette convention. -/
noncomputable def czxRectangleBoundaryLabels (xStart yStart w h : ℕ)
    (hw : 0 < w) (hh : 0 < h) (hx : xStart + w ≤ width) (hy : yStart + h ≤ height)
    (hwp : w < width) (hhp : h < height)
    (μ : RegionBoundaryConfig (czxPEPS width height)
      (torusContiguousRectangle xStart yStart w h)) : Fin (2 * w + 2 * h) → Fin 4 :=
  fun i => if w + h ≤ i.val then
      czxBondSwap (μ (torusRectanglePerimeterEquiv xStart yStart w h hw hh hx hy hwp hhp i))
    else μ (torusRectanglePerimeterEquiv xStart yStart w h hw hh hx hy hwp hhp i)

private theorem czx_component_constraints
    (ζ : Edge (torusGraph width height) → Fin 4) (v : TorusVertex width height) (s : Fin 16)
    (hn : (czxPEPS width height).component v (fun e => ζ e.1) s ≠ 0) :
    ζ (torusUpEdge v) = czxBond (czxTopLeft s, czxTopRight s) ∧
      ζ (torusRightEdge v) = czxBond (czxTopRight s, czxBottomRight s) ∧
      ζ (torusDownEdge v) = czxBond (czxBottomLeft s, czxBottomRight s) ∧
      ζ (torusLeftEdge v) = czxBond (czxTopLeft s, czxBottomLeft s) := by
  change czxSiteTensor (ζ (torusUpEdge v)) (ζ (torusRightEdge v))
    (czxBondSwap (ζ (torusDownEdge v))) (czxBondSwap (ζ (torusLeftEdge v))) s ≠ 0 at hn
  simp only [czxSiteTensor, ne_eq, ite_eq_right_iff, one_ne_zero, imp_false, not_not] at hn
  refine ⟨hn.1, hn.2.1, ?_, ?_⟩
  · apply czxBondSwap.injective
    simpa only [czxBondSwap_czxBond] using hn.2.2.1
  · apply czxBondSwap.injective
    simpa only [czxBondSwap_czxBond] using hn.2.2.2

private theorem czx_horizontal_qubits
    (ζ : Edge (torusGraph width height) → Fin 4)
    (v : TorusVertex width height) (s t : Fin 16)
    (hs : (czxPEPS width height).component v (fun e => ζ e.1) s ≠ 0)
    (ht : (czxPEPS width height).component (v.1 + 1, v.2) (fun e => ζ e.1) t ≠ 0) :
    czxTopRight s = czxTopLeft t ∧ czxBottomRight s = czxBottomLeft t := by
  have hr := (czx_component_constraints ζ v s hs).2.1
  have hl := (czx_component_constraints ζ (v.1 + 1, v.2) t ht).2.2.2
  rw [torusLeftEdge_add_one] at hl
  exact Prod.mk.inj (czxBond.injective (hr.symm.trans hl))

private theorem czx_vertical_qubits
    (ζ : Edge (torusGraph width height) → Fin 4)
    (v : TorusVertex width height) (s t : Fin 16)
    (hs : (czxPEPS width height).component v (fun e => ζ e.1) s ≠ 0)
    (ht : (czxPEPS width height).component (v.1, v.2 + 1) (fun e => ζ e.1) t ≠ 0) :
    czxTopLeft s = czxBottomLeft t ∧ czxTopRight s = czxBottomRight t := by
  have hu := (czx_component_constraints ζ v s hs).1
  have hd := (czx_component_constraints ζ (v.1, v.2 + 1) t ht).2.2.1
  rw [torusDownEdge_add_one] at hd
  exact Prod.mk.inj (czxBond.injective (hu.symm.trans hd))

private def czxRectangleFirstQubit (xStart yStart w h : ℕ)
    (σ : TorusVertex width height → Fin 16) (i : Fin (2 * w + 2 * h)) : Fin 2 :=
  let s := σ (torusRectanglePerimeterSite (width := width) (height := height) xStart yStart w h i)
  if i.val < w then czxTopLeft s
  else if i.val < w + h then czxTopRight s
  else if i.val < 2 * w + h then czxBottomRight s
  else czxBottomLeft s

private def czxRectangleSecondQubit (xStart yStart w h : ℕ)
    (σ : TorusVertex width height → Fin 16) (i : Fin (2 * w + 2 * h)) : Fin 2 :=
  let s := σ (torusRectanglePerimeterSite (width := width) (height := height) xStart yStart w h i)
  if i.val < w then czxTopRight s
  else if i.val < w + h then czxBottomRight s
  else if i.val < 2 * w + h then czxBottomLeft s
  else czxTopLeft s

private theorem czxRectangle_qubits_adjacent (xStart yStart w h : ℕ)
    (hw : 0 < w) (hh : 0 < h) (hx : xStart + w ≤ width) (hy : yStart + h ≤ height)
    [NeZero (2 * w + 2 * h)]
    (ζ : Edge (torusGraph width height) → Fin 4) (σ : TorusVertex width height → Fin 16)
    (hn : ∀ v ∈ torusContiguousRectangle xStart yStart w h,
      (czxPEPS width height).component v (fun e => ζ e.1) (σ v) ≠ 0)
    (i : Fin (2 * w + 2 * h)) :
    czxRectangleSecondQubit xStart yStart w h σ i =
      czxRectangleFirstQubit xStart yStart w h σ (i + 1) := by
  have hi := hn _ (torusRectanglePerimeterSite_mem xStart yStart w h hw hh hx hy i)
  have hj := hn _ (torusRectanglePerimeterSite_mem xStart yStart w h hw hh hx hy (i + 1))
  have hv : (i + 1).val = (i.val + 1) % (2 * w + 2 * h) := by
    rw [Fin.val_add]
    change (i.val + 1 % (2 * w + 2 * h)) % (2 * w + 2 * h) = _
    rw [Nat.mod_eq_of_lt (show 1 < 2 * w + 2 * h by omega)]
  by_cases ht : i.val < w
  · rw [Nat.mod_eq_of_lt (show i.val + 1 < 2 * w + 2 * h by omega)] at hv
    by_cases hnext : i.val + 1 < w
    · have hjt : (i + 1).val < w := by omega
      have hs : torusRectanglePerimeterSite (width := width) (height := height)
          xStart yStart w h (i + 1) =
          ((torusRectanglePerimeterSite (width := width) (height := height)
              xStart yStart w h i).1 + 1,
            (torusRectanglePerimeterSite (width := width) (height := height)
                xStart yStart w h i).2) := by
        simp only [torusRectanglePerimeterSite, ht, hjt, ite_true]
        rw [hv]
        push_cast
        exact Prod.ext (add_assoc _ _ _).symm rfl
      have hadj := czx_horizontal_qubits ζ _ _
        (σ (torusRectanglePerimeterSite xStart yStart w h (i + 1))) hi (by
          rw [← hs]
          exact hj)
      simpa only [czxRectangleFirstQubit, czxRectangleSecondQubit, ht, hjt, ite_true] using hadj.1
    · have hiw : i.val + 1 = w := by omega
      have hjt : ¬(i + 1).val < w := by omega
      have hjr : (i + 1).val < w + h := by omega
      have hs : torusRectanglePerimeterSite (width := width) (height := height)
          xStart yStart w h i = torusRectanglePerimeterSite (width := width) (height := height)
              xStart yStart w h (i + 1) := by
        simp only [torusRectanglePerimeterSite, ht, hjt, hjr, ite_true, ite_false]
        rw [hv]
        congr 1 <;> congr 1 <;> omega
      simp only [czxRectangleFirstQubit, czxRectangleSecondQubit, ht, hjt, hjr,
        ite_true, ite_false, hs]
  · by_cases hr : i.val < w + h
    · rw [Nat.mod_eq_of_lt (show i.val + 1 < 2 * w + 2 * h by omega)] at hv
      have hjt : ¬(i + 1).val < w := by omega
      by_cases hnext : i.val + 1 < w + h
      · have hjr : (i + 1).val < w + h := by omega
        have hs : torusRectanglePerimeterSite (width := width) (height := height)
            xStart yStart w h i =
            ((torusRectanglePerimeterSite (width := width) (height := height)
                xStart yStart w h (i + 1)).1,
              (torusRectanglePerimeterSite (width := width) (height := height)
                  xStart yStart w h (i + 1)).2 + 1) := by
          simp only [torusRectanglePerimeterSite, ht, hr, hjt, hjr, ite_true, ite_false]
          rw [hv]
          refine Prod.ext rfl ?_
          dsimp only
          have he : yStart + (w + h - 1 - i.val) =
              yStart + (w + h - 1 - (i.val + 1)) + 1 := by omega
          simpa only [Nat.cast_add, Nat.cast_one] using
            congrArg (fun k : ℕ => (k : ZMod height)) he
        have hadj := czx_vertical_qubits ζ _ _
          (σ (torusRectanglePerimeterSite xStart yStart w h i)) hj (by
            rw [← hs]
            exact hi)
        simpa only [czxRectangleFirstQubit, czxRectangleSecondQubit, ht, hr, hjt, hjr,
          ite_true, ite_false] using hadj.2.symm
      · have hjr : ¬(i + 1).val < w + h := by omega
        have hjb : (i + 1).val < 2 * w + h := by omega
        have hs : torusRectanglePerimeterSite (width := width) (height := height)
            xStart yStart w h i = torusRectanglePerimeterSite (width := width) (height := height)
                xStart yStart w h (i + 1) := by
          simp only [torusRectanglePerimeterSite, ht, hr, hjt, hjr, hjb,
            ite_true, ite_false]
          rw [hv]
          congr 1 <;> congr 1 <;> omega
        simp only [czxRectangleFirstQubit, czxRectangleSecondQubit, ht, hr, hjt, hjr, hjb,
          ite_true, ite_false, hs]
    · by_cases hb : i.val < 2 * w + h
      · rw [Nat.mod_eq_of_lt (show i.val + 1 < 2 * w + 2 * h by omega)] at hv
        have hjt : ¬(i + 1).val < w := by omega
        have hjr : ¬(i + 1).val < w + h := by omega
        by_cases hnext : i.val + 1 < 2 * w + h
        · have hjb : (i + 1).val < 2 * w + h := by omega
          have hs : torusRectanglePerimeterSite (width := width) (height := height)
              xStart yStart w h i =
              ((torusRectanglePerimeterSite (width := width) (height := height)
                  xStart yStart w h (i + 1)).1 + 1,
                (torusRectanglePerimeterSite (width := width) (height := height)
                    xStart yStart w h (i + 1)).2) := by
            simp only [torusRectanglePerimeterSite, ht, hr, hb, hjt, hjr, hjb,
              ite_true, ite_false]
            rw [hv]
            refine Prod.ext ?_ rfl
            dsimp only
            have he : xStart + (2 * w + h - 1 - i.val) =
                xStart + (2 * w + h - 1 - (i.val + 1)) + 1 := by omega
            simpa only [Nat.cast_add, Nat.cast_one] using
              congrArg (fun k : ℕ => (k : ZMod width)) he
          have hadj := czx_horizontal_qubits ζ _ _
            (σ (torusRectanglePerimeterSite xStart yStart w h i)) hj (by
              rw [← hs]
              exact hi)
          simpa only [czxRectangleFirstQubit, czxRectangleSecondQubit, ht, hr, hb, hjt, hjr, hjb,
            ite_true, ite_false] using hadj.2.symm
        · have hjb : ¬(i + 1).val < 2 * w + h := by omega
          have hs : torusRectanglePerimeterSite (width := width) (height := height)
              xStart yStart w h i = torusRectanglePerimeterSite (width := width) (height := height)
                  xStart yStart w h (i + 1) := by
            simp only [torusRectanglePerimeterSite, ht, hr, hb, hjt, hjr, hjb,
              ite_true, ite_false]
            rw [hv]
            congr 1 <;> congr 1 <;> omega
          simp only [czxRectangleFirstQubit, czxRectangleSecondQubit, ht, hr, hb, hjt, hjr, hjb,
            ite_true, ite_false, hs]
      · by_cases hnext : i.val + 1 < 2 * w + 2 * h
        · rw [Nat.mod_eq_of_lt hnext] at hv
          have hjt : ¬(i + 1).val < w := by omega
          have hjr : ¬(i + 1).val < w + h := by omega
          have hjb : ¬(i + 1).val < 2 * w + h := by omega
          have hs : torusRectanglePerimeterSite (width := width) (height := height)
              xStart yStart w h (i + 1) =
              ((torusRectanglePerimeterSite (width := width) (height := height)
                  xStart yStart w h i).1,
                (torusRectanglePerimeterSite (width := width) (height := height)
                    xStart yStart w h i).2 + 1) := by
            simp only [torusRectanglePerimeterSite, ht, hr, hb, hjt, hjr, hjb, ite_false]
            rw [hv]
            refine Prod.ext rfl ?_
            dsimp only
            have he : yStart + (i.val + 1 - (2 * w + h)) =
                yStart + (i.val - (2 * w + h)) + 1 := by omega
            simpa only [Nat.cast_add, Nat.cast_one] using
              congrArg (fun k : ℕ => (k : ZMod height)) he
          have hadj := czx_vertical_qubits ζ _ _
            (σ (torusRectanglePerimeterSite xStart yStart w h (i + 1))) hi (by
              rw [← hs]
              exact hj)
          simpa only [czxRectangleFirstQubit, czxRectangleSecondQubit, ht, hr, hb, hjt, hjr, hjb,
            ite_true, ite_false] using hadj.1
        · have hv0 : (i + 1).val = 0 := by
            rw [hv, show i.val + 1 = 2 * w + 2 * h by omega, Nat.mod_self]
          have hjt : (i + 1).val < w := by omega
          have hs : torusRectanglePerimeterSite (width := width) (height := height)
              xStart yStart w h i = torusRectanglePerimeterSite (width := width) (height := height)
                  xStart yStart w h (i + 1) := by
            simp only [torusRectanglePerimeterSite, ht, hr, hb, hjt,
              ite_true, ite_false]
            simp only [hv0, Nat.add_zero]
            congr 1
            congr 1
            omega
          simp only [czxRectangleFirstQubit, czxRectangleSecondQubit, ht, hr, hb, hjt,
            ite_true, ite_false, hs]

private theorem czxRectangle_labels_pair (xStart yStart w h : ℕ)
    (hw : 0 < w) (hh : 0 < h) (hx : xStart + w ≤ width) (hy : yStart + h ≤ height)
    (ζ : Edge (torusGraph width height) → Fin 4) (σ : TorusVertex width height → Fin 16)
    (hn : ∀ v ∈ torusContiguousRectangle xStart yStart w h,
      (czxPEPS width height).component v (fun e => ζ e.1) (σ v) ≠ 0)
    (i : Fin (2 * w + 2 * h)) :
    (if w + h ≤ i.val then czxBondSwap (ζ (torusRectanglePerimeterEdge xStart yStart w h i))
      else ζ (torusRectanglePerimeterEdge xStart yStart w h i)) =
      czxBond (czxRectangleFirstQubit xStart yStart w h σ i,
        czxRectangleSecondQubit xStart yStart w h σ i) := by
  have hc := czx_component_constraints ζ _ _
    (hn _ (torusRectanglePerimeterSite_mem xStart yStart w h hw hh hx hy i))
  have he (z : TorusVertex width height ⊕ TorusVertex width height) :
      torusEdgeEquiv z = Sum.elim torusRightEdge torusUpEdge z := rfl
  by_cases ht : i.val < w
  · have hrev : ¬w + h ≤ i.val := by omega
    simpa only [torusRectanglePerimeterEdge, torusRectanglePerimeterCode, he,
      Sum.elim_inl, Sum.elim_inr,
      czxRectangleFirstQubit, czxRectangleSecondQubit, torusRectanglePerimeterSite,
      ht, hrev, ite_true, ite_false] using hc.1
  · by_cases hr : i.val < w + h
    · have hrev : ¬w + h ≤ i.val := by omega
      simpa only [torusRectanglePerimeterEdge, torusRectanglePerimeterCode, he,
      Sum.elim_inl, Sum.elim_inr,
        czxRectangleFirstQubit, czxRectangleSecondQubit, torusRectanglePerimeterSite,
        ht, hr, hrev, ite_true, ite_false] using hc.2.1
    · have hrev : w + h ≤ i.val := by omega
      by_cases hb : i.val < 2 * w + h
      · simpa only [torusRectanglePerimeterEdge, torusRectanglePerimeterCode, he,
      Sum.elim_inl, Sum.elim_inr,
          czxRectangleFirstQubit, czxRectangleSecondQubit, torusRectanglePerimeterSite,
          ht, hr, hb, hrev, ite_true, ite_false, czxBondSwap_czxBond, torusDownEdge] using
          congrArg czxBondSwap hc.2.2.1
      · simpa only [torusRectanglePerimeterEdge, torusRectanglePerimeterCode, he,
      Sum.elim_inl, Sum.elim_inr,
          czxRectangleFirstQubit, czxRectangleSecondQubit, torusRectanglePerimeterSite,
          ht, hr, hb, hrev, ite_true, ite_false, czxBondSwap_czxBond, torusLeftEdge] using
          congrArg czxBondSwap hc.2.2.2

/-- Every nonzero coefficient of the actual rectangle contraction has
clockwise boundary labels in the cyclic adjacent-plaquette embedding.
The conclusion is derived from the local CZX tensor and the native internal
bond identifications; it is not an assumed boundary-support condition. -/
theorem czxRectangleBoundaryLabels_mem_range_of_openRegionWeight_ne_zero
    (xStart yStart w h : ℕ)
    (hw : 0 < w) (hh : 0 < h) (hx : xStart + w ≤ width) (hy : yStart + h ≤ height)
    (hwp : w < width) (hhp : h < height) [NeZero (2 * w + 2 * h)]
    (μ : RegionBoundaryConfig (czxPEPS width height)
      (torusContiguousRectangle xStart yStart w h))
    (σ : RegionPhysicalConfig (d := 16) (torusContiguousRectangle xStart yStart w h))
    (hσ : openRegionWeight (czxPEPS width height)
      (torusContiguousRectangle xStart yStart w h) μ σ ≠ 0) :
    ∃ c : Fin (2 * w + 2 * h) → Fin 2,
      czxRectangleBoundaryLabels xStart yStart w h hw hh hx hy hwp hhp μ =
        czxBoundaryLegs (2 * w + 2 * h) c := by
  classical
  let R : Finset (TorusVertex width height) := torusContiguousRectangle xStart yStart w h
  rw [openRegionWeight_czxPEPS] at hσ
  simp only [ne_eq, ite_eq_right_iff, one_ne_zero, imp_false, not_not] at hσ
  obtain ⟨η, hημ, hη⟩ := hσ
  change ({e : Edge (torusGraph width height) // IsRegionIncidentEdge R e} → Fin 4) at η
  let ζ : Edge (torusGraph width height) → Fin 4 :=
    fun e => if he : IsRegionIncidentEdge R e then η ⟨e, he⟩ else 0
  let τ : TorusVertex width height → Fin 16 :=
    fun v => if hv : v ∈ R then σ ⟨v, hv⟩ else 0
  have hn (v : TorusVertex width height) (hv : v ∈ R) :
      (czxPEPS width height).component v (fun e => ζ e.1) (τ v) ≠ 0 := by
    have hlocal := (Finset.prod_ne_zero_iff.mp hη) ⟨v, hv⟩ (Finset.mem_univ _)
    have heq : (fun e : IncidentEdge (torusGraph width height) v => ζ e.1) =
        (fun e => η ⟨e.1, isRegionIncidentEdge_of_regionVertex R ⟨v, hv⟩ e⟩) := by
      funext e
      exact dite_eq_left (isRegionIncidentEdge_of_regionVertex R ⟨v, hv⟩ e)
    rw [heq]
    simpa only [τ, dite_eq_left hv] using hlocal
  have hboundary (i : Fin (2 * w + 2 * h)) :
      μ (torusRectanglePerimeterEquiv xStart yStart w h hw hh hx hy hwp hhp i) =
        ζ (torusRectanglePerimeterEdge xStart yStart w h i) := by
    have he := congrFun hημ
      (torusRectanglePerimeterEquiv xStart yStart w h hw hh hx hy hwp hhp i)
    have hi := isRegionBoundaryEdge_touches R
      (torusRectanglePerimeterEdge_boundary xStart yStart w h hw hh hx hy hwp hhp i)
    dsimp only [ζ]
    rw [dite_eq_left hi]
    exact he.symm
  refine ⟨czxRectangleFirstQubit xStart yStart w h τ, ?_⟩
  funext i
  unfold czxRectangleBoundaryLabels
  rw [hboundary]
  rw [czxRectangle_labels_pair xStart yStart w h hw hh hx hy ζ τ hn i,
    czxRectangle_qubits_adjacent xStart yStart w h hw hh hx hy ζ τ hn i]
  rfl

end TNLean.PEPS
