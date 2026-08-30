/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.TorusWindowPeeling.EndOperation
import TNLean.PEPS.TwoInjectiveComparison.EndOperationComposition

/-!
# Physical end operations and the staircase virtual operation

This file states the staircase end-pair comparison in the physical-operation notation of Lemma 5.
The insert on each highlighted window is obtained by applying its physical operation to the
genuine open blocked tensor.  Equality of the two open end-pair extensions then gives the unique
matrix `X` on the reference edge.  For every fixed external boundary configuration, the left
operation satisfies the paper's `O₁` factor relation and the right operation satisfies its
`O₃ᵀ`-oriented factor relation.

The theorem is a direct specialization of
`existsUnique_virtualOperation_of_horizontalStaircaseEndPair`.  In particular, its only
injectivity hypotheses are those of the two genuine end windows; it assumes no injectivity of a
modified insert, a vertex, the end pair, or its complement.

## References

* [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected entangled pair states
  generating the same state*, arXiv:1804.04964, Lemma 5 at lines 2213--2252 and the
  two-dimensional end-window comparison at lines 2415--2444 of
  `Papers/1804.04964/paper_normal.tex`](https://arxiv.org/abs/1804.04964).
-/

open scoped BigOperators Matrix

namespace TNLean
namespace PEPS

section Torus

variable {width height : ℕ} [NeZero width] [NeZero height]
variable [Fact (1 < width)] [Fact (1 < height)]
variable {d : ℕ}

/-- **The unique staircase virtual operation obtained from `O₁` and `O₃ᵀ`.**

Apply `O₁` and `O₃` to the genuine blocked tensors of the two highlighted end windows.  If the
resulting inserts have equal open extensions to their end pair, there is a unique matrix `X` on
the reference edge.  Holding the external boundary labels fixed, `O₁` realizes `X` in the
left-factor orientation and `O₃` realizes `X` in the source's transposed right-factor orientation.

This is the physical-operation form of the two-dimensional ``compare the two ends'' step.  The
composition laws for these two relations are
`IsO1VirtualOperation.mul` and `IsO3TransposeVirtualOperation.mul`.

Source: arXiv:1804.04964, Lemma 5, lines 2213--2252, and the two-dimensional end-window
comparison at lines 2415--2444 of `Papers/1804.04964/paper_normal.tex`. -/
theorem existsUnique_virtualOperation_of_horizontalStaircaseEndPhysicalOperations
    (A : Tensor (torusGraph width height) d) {L K a b : ℕ}
    (hTI : IsTorusTranslationInvariant A)
    (hL : 0 < L) (hK : 0 < K) (ha0 : 1 ≤ a)
    (haw : a + 2 * L ≤ width) (hbh : b + 2 * K - 1 ≤ height)
    (hpos : ∀ eg : Edge (torusGraph width height), 0 < A.bondDim eg)
    (hleftInjective : RegionBlockedTensorInjective (G := torusGraph width height) A
      (horizontalStaircaseLeftWindow ((a : ZMod width), (b : ZMod height)) L K))
    (hrightInjective : RegionBlockedTensorInjective (G := torusGraph width height) A
      (horizontalStaircaseRightWindow ((a : ZMod width), (b : ZMod height)) L K))
    (O₁ : Module.End ℂ
      (RegionPhysicalConfig (V := TorusVertex width height) (d := d)
        (horizontalStaircaseLeftWindow
          ((a : ZMod width), (b : ZMod height)) L K) → ℂ))
    (O₃ : Module.End ℂ
      (RegionPhysicalConfig (V := TorusVertex width height) (d := d)
        (horizontalStaircaseRightWindow
          ((a : ZMod width), (b : ZMod height)) L K) → ℂ))
    (heq :
      extendInsert (G := torusGraph width height)
          (horizontalStaircaseLeftWindow_subset_endPair
            ((a : ZMod width), (b : ZMod height)))
          (fun μ ↦ O₁ (regionBlockedWeight (G := torusGraph width height) A
            (horizontalStaircaseLeftWindow
              ((a : ZMod width), (b : ZMod height)) L K) μ)) =
        extendInsert (G := torusGraph width height)
          (horizontalStaircaseRightWindow_subset_endPair
            ((a : ZMod width), (b : ZMod height)))
          (fun μ ↦ O₃ (regionBlockedWeight (G := torusGraph width height) A
            (horizontalStaircaseRightWindow
              ((a : ZMod width), (b : ZMod height)) L K) μ))) :
    let s : TorusVertex width height := ((a : ZMod width), (b : ZMod height))
    let Wleft := horizontalStaircaseLeftWindow s L K
    let Wright := horizontalStaircaseRightWindow s L K
    let Eleft := horizontalStaircaseLeftWindowBoundaryConfigEquiv A hL hK ha0 haw hbh
    let Eright := horizontalStaircaseRightWindowBoundaryConfigEquiv A hL hK ha0 haw hbh
    ∃! X : Matrix
        (Fin (A.bondDim (horizontalStaircaseReferenceEdge s L K)))
        (Fin (A.bondDim (horizontalStaircaseReferenceEdge s L K))) ℂ,
      (∀ etaLeft : HorizontalStaircaseLeftExternalBoundaryConfig A (L := L) (K := K) s,
        IsO1VirtualOperation
          (fun k : Fin (A.bondDim (horizontalStaircaseReferenceEdge s L K)) ↦
            regionBlockedWeight (G := torusGraph width height) A Wleft
              (Eleft.symm (k, etaLeft))) O₁ X) ∧
      ∀ etaRight : HorizontalStaircaseRightExternalBoundaryConfig A (L := L) (K := K) s,
        IsO3TransposeVirtualOperation
          (fun k : Fin (A.bondDim (horizontalStaircaseReferenceEdge s L K)) ↦
            regionBlockedWeight (G := torusGraph width height) A Wright
              (Eright.symm (k, etaRight))) O₃ X := by
  classical
  dsimp only
  let s : TorusVertex width height := ((a : ZMod width), (b : ZMod height))
  let Wleft := horizontalStaircaseLeftWindow s L K
  let Wright := horizontalStaircaseRightWindow s L K
  let hleft : Wleft ⊆ horizontalStaircaseEndPair s L K :=
    horizontalStaircaseLeftWindow_subset_endPair s
  let hright : Wright ⊆ horizontalStaircaseEndPair s L K :=
    horizontalStaircaseRightWindow_subset_endPair s
  let Eleft := horizontalStaircaseLeftWindowBoundaryConfigEquiv A hL hK ha0 haw hbh
  let Eright := horizontalStaircaseRightWindowBoundaryConfigEquiv A hL hK ha0 haw hbh
  let Cleft : RegionInsert (G := torusGraph width height) (d := d) A Wleft :=
    fun μ ↦ O₁ (regionBlockedWeight (G := torusGraph width height) A Wleft μ)
  let Cright : RegionInsert (G := torusGraph width height) (d := d) A Wright :=
    fun μ ↦ O₃ (regionBlockedWeight (G := torusGraph width height) A Wright μ)
  have heq' : extendInsert (G := torusGraph width height) hleft Cleft =
      extendInsert (G := torusGraph width height) hright Cright := by
    simpa only [s, Wleft, Wright, hleft, hright, Cleft, Cright] using heq
  obtain ⟨X, hX, hXunique⟩ :=
    existsUnique_virtualOperation_of_horizontalStaircaseEndPair
      A hTI hL hK ha0 haw hbh hpos hleftInjective hrightInjective Cleft Cright heq'
  refine ⟨X, ⟨?_, ?_⟩, ?_⟩
  · intro etaLeft k
    funext sigmaLeft
    simpa only [Cleft, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_comm] using
      hX.1 k etaLeft sigmaLeft
  · intro etaRight k
    funext sigmaRight
    simpa only [Cright, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using
      hX.2 k etaRight sigmaRight
  · intro Y hY
    apply hXunique
    constructor
    · intro k etaLeft sigmaLeft
      have h := congrFun (hY.1 etaLeft k) sigmaLeft
      simpa only [Cleft, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_comm] using h
    · intro k etaRight sigmaRight
      have h := congrFun (hY.2 etaRight k) sigmaRight
      simpa only [Cright, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using h

end Torus

end PEPS
end TNLean
