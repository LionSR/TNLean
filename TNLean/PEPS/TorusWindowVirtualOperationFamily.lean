/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.RegionBlock.InteriorBondInsertion
import TNLean.PEPS.TorusWindowBondUniform
import TNLean.PEPS.TorusWindowFamilyCrossing
import TNLean.PEPS.TorusWindowPeeling.SingleBond

/-!
# One virtual operation on the staircase window family

Fix the horizontal reference edge `e` and a virtual operation `X` on it.  The staircase
windows are divided exactly as in the proof of the two-dimensional corollary of
arXiv:1804.04964:

* `W₀` contains only the ordered right endpoint of `e`; it carries the boundary insert of
  `Xᵀ`, whose boundary orientation is `X`;
* `W₁, …, W_{L-1}` contain both endpoints of `e`; they carry the interior-bond insert of
  `X`;
* `W_L, …, W_{L+K-1}` contain only the ordered left endpoint of `e`; they carry the boundary
  insert of `X`.

Every assembled deformed state is the non-boundary bond product of its window times the same
closed-network coefficient `E_B(e, ω, X)`.  Translation invariance makes those products equal,
so the entire family has one common deformed state.  Applying the existing single-bond peeling
then equates the first-window coefficient with `Xᵀ` and the last-window coefficient with `X`.
This transpose agrees with the ordered-endpoint convention of Lemma 5, where the right-end
physical operation occurs in the map from `O₃ᵀ` to `X`.

The construction follows the paper's actual operation: it keeps the distinguished bond `e`
fixed and adjoins genuine tensors to a window.  No auxiliary matrix-span or different-bond
transport is introduced.

## References

* [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected entangled pair
  states generating the same state*, arXiv:1804.04964, Lemma 5 at lines 2045--2252 and the
  two-dimensional corollary and proof sketch at lines 2297--2444 of
  `Papers/1804.04964/paper_normal.tex`](https://arxiv.org/abs/1804.04964).
-/

open scoped BigOperators Matrix

namespace TNLean
namespace PEPS

section Torus

variable {width height : ℕ} [NeZero width] [NeZero height]
variable [Fact (1 < width)] [Fact (1 < height)]
variable {d : ℕ} {L K : ℕ} {B : Tensor (torusGraph width height) d}

/-- The insert family realizing one virtual operation `X` on the horizontal reference edge.

The first window, which contains only the ordered right endpoint, carries `Xᵀ`.  Windows
strictly between `0` and `L` contain both endpoints and use the interior-bond insert.  Windows
from `L` onward contain the ordered left endpoint and carry `X`.  The intended indices are
`0 ≤ j < L + K`.

Source: arXiv:1804.04964, proof sketch at lines 2320--2444 of
`Papers/1804.04964/paper_normal.tex`. -/
noncomputable def staircaseVirtualOperationInsert {a b : ℕ}
    (hL : 0 < L) (hK : 0 < K) (haw : a + 2 * L ≤ width) (hyh : 2 * K ≤ height)
    (X : Matrix
      (Fin (B.bondDim (horizontalStaircaseReferenceEdge
        ((a : ZMod width), (b : ZMod height)) L K)))
      (Fin (B.bondDim (horizontalStaircaseReferenceEdge
        ((a : ZMod width), (b : ZMod height)) L K))) ℂ)
    (j : ℕ) : RegionInsert (G := torusGraph width height) (d := d) B
      (staircaseWindow ((a : ZMod width), (b : ZMod height)) L K j) :=
  if hj0 : j = 0 then
    bondInsertedRegionInsert (G := torusGraph width height) B
      (staircaseWindow ((a : ZMod width), (b : ZMod height)) L K j)
      ⟨_, isRegionBoundaryEdge_staircaseWindow_referenceEdge hL hK haw hyh (Or.inl hj0)⟩ Xᵀ
  else if hjL : L ≤ j then
    bondInsertedRegionInsert (G := torusGraph width height) B
      (staircaseWindow ((a : ZMod width), (b : ZMod height)) L K j)
      ⟨_, isRegionBoundaryEdge_staircaseWindow_referenceEdge hL hK haw hyh (Or.inr hjL)⟩ X
  else
    interiorBondInsertedRegionInsert (G := torusGraph width height) B
      (staircaseWindow ((a : ZMod width), (b : ZMod height)) L K j)
      (horizontalStaircaseReferenceEdge ((a : ZMod width), (b : ZMod height)) L K)
      (referenceEdge_endpoints_mem_staircaseWindow_of_interior hL hK haw hyh
        (Nat.one_le_iff_ne_zero.mpr hj0) (lt_of_not_ge hjL)) X

/-- On the first staircase window the virtual-operation family is the boundary insert of
`Xᵀ`.  Its boundary orientation transposes once more, so the closed-network operation is `X`.

Source: arXiv:1804.04964, Lemma 5 at lines 2045--2252 and the proof sketch at lines
2320--2444 of `Papers/1804.04964/paper_normal.tex`. -/
theorem staircaseVirtualOperationInsert_zero {a b : ℕ}
    (hL : 0 < L) (hK : 0 < K) (haw : a + 2 * L ≤ width) (hyh : 2 * K ≤ height)
    (X : Matrix
      (Fin (B.bondDim (horizontalStaircaseReferenceEdge
        ((a : ZMod width), (b : ZMod height)) L K)))
      (Fin (B.bondDim (horizontalStaircaseReferenceEdge
        ((a : ZMod width), (b : ZMod height)) L K))) ℂ) :
    staircaseVirtualOperationInsert (B := B) hL hK haw hyh X 0 =
      bondInsertedRegionInsert (G := torusGraph width height) B
        (staircaseWindow ((a : ZMod width), (b : ZMod height)) L K 0)
        ⟨_, isRegionBoundaryEdge_staircaseWindow_referenceEdge hL hK haw hyh
          (Or.inl rfl)⟩ Xᵀ := by
  simp [staircaseVirtualOperationInsert]

/-- On the last staircase window the virtual-operation family is the boundary insert of `X`.
The window contains the ordered left endpoint, so its boundary orientation is the identity.

Source: arXiv:1804.04964, Lemma 5 at lines 2045--2252 and the proof sketch at lines
2320--2444 of `Papers/1804.04964/paper_normal.tex`. -/
theorem staircaseVirtualOperationInsert_last {a b : ℕ}
    (hL : 0 < L) (hK : 0 < K) (haw : a + 2 * L ≤ width) (hyh : 2 * K ≤ height)
    (X : Matrix
      (Fin (B.bondDim (horizontalStaircaseReferenceEdge
        ((a : ZMod width), (b : ZMod height)) L K)))
      (Fin (B.bondDim (horizontalStaircaseReferenceEdge
        ((a : ZMod width), (b : ZMod height)) L K))) ℂ) :
    staircaseVirtualOperationInsert (B := B) hL hK haw hyh X (L + K - 1) =
      bondInsertedRegionInsert (G := torusGraph width height) B
        (staircaseWindow ((a : ZMod width), (b : ZMod height)) L K (L + K - 1))
        ⟨_, isRegionBoundaryEdge_staircaseWindow_referenceEdge hL hK haw hyh
          (Or.inr (by omega))⟩ X := by
  simp [staircaseVirtualOperationInsert, show L + K - 1 ≠ 0 by omega,
    show L ≤ L + K - 1 by omega]

/-- Every insert in the staircase family realizes the same closed-network virtual operation.

For `0 ≤ j < L + K`, its assembled deformed state is
\[
  p_B(W_0) E_B(e,\omega,X).
\]
The three index ranges use, respectively, the right-end boundary insert of `Xᵀ`, the
interior-bond insert of `X`, and the left-end boundary insert of `X`.  Translation invariance
identifies the non-boundary bond products of all the translated `L × K` windows.

Source: arXiv:1804.04964, the two-dimensional corollary and proof sketch at lines
2297--2444 of `Papers/1804.04964/paper_normal.tex`. -/
theorem deformedRegionStateAssembled_staircaseVirtualOperationInsert {a b j : ℕ}
    (hTI : IsTorusTranslationInvariant B)
    (hpos : ∀ e : Edge (torusGraph width height), 0 < B.bondDim e)
    (hL : 0 < L) (hK : 0 < K) (haw : a + 2 * L ≤ width) (hyh : 2 * K ≤ height)
    (_hj : j < L + K)
    (X : Matrix
      (Fin (B.bondDim (horizontalStaircaseReferenceEdge
        ((a : ZMod width), (b : ZMod height)) L K)))
      (Fin (B.bondDim (horizontalStaircaseReferenceEdge
        ((a : ZMod width), (b : ZMod height)) L K))) ℂ)
    (cfg : TorusVertex width height → Fin d) :
    deformedRegionStateAssembled (G := torusGraph width height) B
        (staircaseWindow ((a : ZMod width), (b : ZMod height)) L K j)
        (staircaseVirtualOperationInsert (B := B) hL hK haw hyh X j) cfg =
      regionInteriorBondProd (G := torusGraph width height) B
          (staircaseWindow ((a : ZMod width), (b : ZMod height)) L K 0) •
        edgeInsertedCoeff (G := torusGraph width height) B
          (horizontalStaircaseReferenceEdge ((a : ZMod width), (b : ZMod height)) L K) cfg X := by
  classical
  by_cases hj0 : j = 0
  · subst j
    rw [staircaseVirtualOperationInsert_zero]
    rw [deformedRegionStateAssembled_bondInserted_eq_smul_edgeInsertedCoeff]
    have hleft :
        (horizontalStaircaseReferenceEdge
          ((a : ZMod width), (b : ZMod height)) L K).1.1 ∉
          staircaseWindow ((a : ZMod width), (b : ZMod height)) L K 0 := by
      rw [referenceEdge_leftEndpoint_mem_staircaseWindow hL hK haw hyh]
      omega
    simp [regionEdgeOrient, hleft]
  · by_cases hjL : L ≤ j
    · simp only [staircaseVirtualOperationInsert, hj0, ↓reduceDIte, hjL]
      rw [deformedRegionStateAssembled_bondInserted_eq_smul_edgeInsertedCoeff]
      have hleft :
          (horizontalStaircaseReferenceEdge
            ((a : ZMod width), (b : ZMod height)) L K).1.1 ∈
            staircaseWindow ((a : ZMod width), (b : ZMod height)) L K j := by
        rw [referenceEdge_leftEndpoint_mem_staircaseWindow hL hK haw hyh]
        omega
      simp only [regionEdgeOrient, hleft, ite_true]
      rw [regionInteriorBondProd_staircaseWindow_eq hTI _ L K j 0]
    · simp only [staircaseVirtualOperationInsert, hj0, hjL, ↓reduceDIte]
      rw [deformedRegionStateAssembled_interiorBondInserted_eq_smul_edgeInsertedCoeff
        (hpos := hpos)]
      rw [regionInteriorBondProd_staircaseWindow_eq hTI _ L K j 0]

/-- The virtual-operation family supplies the common-state hypothesis of the single-bond
peeling.  Consequently, the coefficient on the first window with `Xᵀ` inserted equals the
coefficient on the last window with `X` inserted.

The hypotheses here are exactly those of the existing end-window peeling theorem together with
translation invariance, which identifies the normalizing bond products.  This is a
single-tensor end-window identity, not yet the cross-tensor gauge conjugation.

Source: arXiv:1804.04964, Lemma 5 at lines 2045--2252 and the two-dimensional proof sketch at
lines 2320--2444 of `Papers/1804.04964/paper_normal.tex`. -/
theorem regionInsertedCoeff_endWindows_eq_staircaseVirtualOperation {a b : ℕ}
    (h : NormalTorusArcWindowInjectivityHypotheses L K
      (regionInjectivityDataOf (G := torusGraph width height) B))
    (hUB : RegionInjectivityUnionClosure
      (regionInjectivityDataOf (G := torusGraph width height) B))
    (hTI : IsTorusTranslationInvariant B)
    (hpos : ∀ e : Edge (torusGraph width height), 0 < B.bondDim e)
    (hL : 2 ≤ L) (hK : 2 ≤ K) (ha0 : 1 ≤ a)
    (haw : a + 2 * L ≤ width) (hbh : b + 2 * K - 1 ≤ height)
    (hxw : 2 * L + 1 ≤ width) (hyh : 2 * K + 1 ≤ height)
    (X : Matrix
      (Fin (B.bondDim (horizontalStaircaseReferenceEdge
        ((a : ZMod width), (b : ZMod height)) L K)))
      (Fin (B.bondDim (horizontalStaircaseReferenceEdge
        ((a : ZMod width), (b : ZMod height)) L K))) ℂ)
    (cfg : TorusVertex width height → Fin d) :
    regionInsertedCoeff (G := torusGraph width height) B
        (staircaseWindow ((a : ZMod width), (b : ZMod height)) L K 0)
        ⟨_, isRegionBoundaryEdge_staircaseWindow_zero_referenceEdge B
          (by omega) (by omega) ha0 haw hbh⟩ Xᵀ
        (restrictRegionσ (V := TorusVertex width height) (d := d) _ cfg)
        (restrictRegionσ (V := TorusVertex width height) (d := d) _ cfg) =
      regionInsertedCoeff (G := torusGraph width height) B
        (staircaseWindow ((a : ZMod width), (b : ZMod height)) L K (L + K - 1))
        ⟨_, isRegionBoundaryEdge_staircaseWindow_last_referenceEdge B
          (by omega) (by omega) ha0 haw hbh⟩ X
        (restrictRegionσ (V := TorusVertex width height) (d := d) _ cfg)
        (restrictRegionσ (V := TorusVertex width height) (d := d) _ cfg) := by
  apply regionInsertedCoeff_endWindows_eq_of_staircase h hUB hpos hL hK ha0 haw hbh hxw hyh
    Xᵀ X (staircaseVirtualOperationInsert (B := B) (by omega) (by omega) haw (by omega) X)
    (fun cfg ↦
      regionInteriorBondProd (G := torusGraph width height) B
          (staircaseWindow ((a : ZMod width), (b : ZMod height)) L K 0) •
        edgeInsertedCoeff (G := torusGraph width height) B
          (horizontalStaircaseReferenceEdge ((a : ZMod width), (b : ZMod height)) L K) cfg X)
  · intro j hj
    funext cfg
    exact deformedRegionStateAssembled_staircaseVirtualOperationInsert hTI hpos
      (by omega) (by omega) haw (by omega) hj X cfg
  · exact staircaseVirtualOperationInsert_zero (by omega) (by omega) haw (by omega) X
  · exact staircaseVirtualOperationInsert_last (by omega) (by omega) haw (by omega) X

end Torus

end PEPS
end TNLean
