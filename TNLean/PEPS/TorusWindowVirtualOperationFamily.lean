/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.RegionBlock.InteriorBondInsertion
import TNLean.PEPS.RegionBlock.PhysicalOperation
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
so the entire family has one common deformed state.  Independently, window injectivity gives an
explicit physical operator `Oⱼ(X)` whose action on every open-boundary genuine block is the insert
`Cⱼ(X)`.  The direct region-to-edge identities equate the first-window coefficient with `Xᵀ`
and the last-window coefficient with `X`.  This transpose agrees with the ordered-endpoint
convention of Lemma 5, where the right-end physical operation occurs in the map from `O₃ᵀ` to `X`.

If a second tensor has the same closed state, the same physical operators `Oⱼ(X)` may be applied
to its genuine window blocks even though its virtual boundary spaces need not agree with those of
the first tensor.  The partial-state identity transfers the common-state property across the two
tensors after the honest interior-bond factors are accounted for.  Thus the physical operations
give the common family required by the converse before any multiplication law is considered.

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

/-- The physical operator `Oⱼ(X)` on the `j`-th injective staircase window that realizes the
insert `Cⱼ(X)`.

The arc-window hypotheses make `Wⱼ` injective.  The chosen left inverse of its blocked-tensor map
therefore turns the open-boundary insert family `Cⱼ(X)` into one linear operator on the physical
space of the window.

Source: arXiv:1804.04964, the virtual/physical operation correspondence at lines 2320--2321 and
the displayed staircase windows at lines 2323--2366 of
`Papers/1804.04964/paper_normal.tex`. -/
noncomputable def staircaseVirtualOperationPhysicalOp {a b : ℕ}
    (h : NormalTorusArcWindowInjectivityHypotheses L K
      (regionInjectivityDataOf (G := torusGraph width height) B))
    (hL : 0 < L) (hK : 0 < K) (haw : a + 2 * L ≤ width) (hyh : 2 * K ≤ height)
    (X : Matrix
      (Fin (B.bondDim (horizontalStaircaseReferenceEdge
        ((a : ZMod width), (b : ZMod height)) L K)))
      (Fin (B.bondDim (horizontalStaircaseReferenceEdge
        ((a : ZMod width), (b : ZMod height)) L K))) ℂ)
    (j : ℕ) :
    (RegionPhysicalConfig (V := TorusVertex width height) (d := d)
        (staircaseWindow ((a : ZMod width), (b : ZMod height)) L K j) → ℂ) →ₗ[ℂ]
      (RegionPhysicalConfig (V := TorusVertex width height) (d := d)
        (staircaseWindow ((a : ZMod width), (b : ZMod height)) L K j) → ℂ) :=
  physicalOpOfRegionInsert (G := torusGraph width height) B
    (staircaseWindow ((a : ZMod width), (b : ZMod height)) L K j)
    (by
      have hi := h.staircaseWindow_injective ((a : ZMod width), (b : ZMod height)) j
      rwa [regionInjectivityDataOf_isInjective] at hi)
    (staircaseVirtualOperationInsert (B := B) hL hK haw hyh X j)

/-- The operator `Oⱼ(X)` realizes `Cⱼ(X)` as an open-boundary identity.  For every virtual
boundary configuration `μ`,
\[
  O_j(X)\bigl(T_{B,W_j}(\mu)\bigr)=C_j(X)(\mu).
\]

In particular, the common-state theorem below is not being used to infer a local physical
realization after closing the complement: the physical operator is exhibited first, on the
window's full physical space.

Source: arXiv:1804.04964, the virtual/physical operation correspondence at lines 2320--2321 and
the displayed staircase windows at lines 2323--2366 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem staircaseVirtualOperationPhysicalOp_realizes {a b : ℕ}
    (h : NormalTorusArcWindowInjectivityHypotheses L K
      (regionInjectivityDataOf (G := torusGraph width height) B))
    (hL : 0 < L) (hK : 0 < K) (haw : a + 2 * L ≤ width) (hyh : 2 * K ≤ height)
    (X : Matrix
      (Fin (B.bondDim (horizontalStaircaseReferenceEdge
        ((a : ZMod width), (b : ZMod height)) L K)))
      (Fin (B.bondDim (horizontalStaircaseReferenceEdge
        ((a : ZMod width), (b : ZMod height)) L K))) ℂ)
    (j : ℕ)
    (μ : RegionBoundaryConfig (G := torusGraph width height) B
      (staircaseWindow ((a : ZMod width), (b : ZMod height)) L K j)) :
    staircaseVirtualOperationPhysicalOp (B := B) h hL hK haw hyh X j
        (regionBlockedWeight (G := torusGraph width height) B
          (staircaseWindow ((a : ZMod width), (b : ZMod height)) L K j) μ) =
      staircaseVirtualOperationInsert (B := B) hL hK haw hyh X j μ := by
  unfold staircaseVirtualOperationPhysicalOp
  apply physicalOpOfRegionInsert_realizes

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

/-- The physical operations `Oⱼ(X)` constructed from one tensor `A`, when applied to the
corresponding genuine staircase-window blocks of a tensor `B` with the same closed state, all
produce one common deformed state of `B`.

For each window, `deformedRegionState_regionInsertOfPhysicalOp_sameState` transfers the closed
action of `Oⱼ(X)` from `A` to `B`, without identifying their virtual boundary spaces.  On `A`, the
operation realizes the insert family `Cⱼ(X)`, whose deformed states agree.  Translation invariance
identifies the interior-bond products for the windows of each tensor, and positivity of the bond
dimensions of `A` cancels its one common nonzero factor.

This is exactly the common-state premise for comparing consecutive physical operations in the
two-dimensional converse.  It assumes neither a multiplication law for the operations nor an
auxiliary single-vertex or coarse-block injectivity condition.

The source family has indices `0 ≤ k < L + K`.  The truncated offsets in `staircaseWindow`
stabilize at the last window for `L + K - 1 ≤ k`, so the statement below holds for arbitrary
natural indices; this is stabilization, not a cyclic convention.  No equality between the
edge-dependent bond dimensions of `A` and `B` is assumed.

Source: arXiv:1804.04964, the virtual-to-physical staircase construction at lines 2320--2368 and
the common-state comparison of the four physical operations at lines 2368--2415 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem deformedRegionStateAssembled_staircasePhysicalOp_sameState
    {A B : Tensor (torusGraph width height) d} {a b j j' : ℕ}
    (hA : NormalTorusArcWindowInjectivityHypotheses L K
      (regionInjectivityDataOf (G := torusGraph width height) A))
    (hATI : IsTorusTranslationInvariant A) (hBTI : IsTorusTranslationInvariant B)
    (hAB : SameState A B)
    (hposA : ∀ e : Edge (torusGraph width height), 0 < A.bondDim e)
    (hL : 0 < L) (hK : 0 < K) (haw : a + 2 * L ≤ width) (hyh : 2 * K ≤ height)
    (X : Matrix
      (Fin (A.bondDim (horizontalStaircaseReferenceEdge
        ((a : ZMod width), (b : ZMod height)) L K)))
      (Fin (A.bondDim (horizontalStaircaseReferenceEdge
        ((a : ZMod width), (b : ZMod height)) L K))) ℂ) :
    deformedRegionStateAssembled (G := torusGraph width height) B
        (staircaseWindow ((a : ZMod width), (b : ZMod height)) L K j)
        (regionInsertOfPhysicalOp (G := torusGraph width height) B
          (staircaseWindow ((a : ZMod width), (b : ZMod height)) L K j)
          (staircaseVirtualOperationPhysicalOp (B := A) hA hL hK haw hyh X j)) =
      deformedRegionStateAssembled (G := torusGraph width height) B
        (staircaseWindow ((a : ZMod width), (b : ZMod height)) L K j')
        (regionInsertOfPhysicalOp (G := torusGraph width height) B
          (staircaseWindow ((a : ZMod width), (b : ZMod height)) L K j')
          (staircaseVirtualOperationPhysicalOp (B := A) hA hL hK haw hyh X j')) := by
  classical
  funext cfg
  have hrealizes (k : ℕ) :
      regionInsertOfPhysicalOp (G := torusGraph width height) A
          (staircaseWindow ((a : ZMod width), (b : ZMod height)) L K k)
          (staircaseVirtualOperationPhysicalOp (B := A) hA hL hK haw hyh X k) =
        staircaseVirtualOperationInsert (B := A) hL hK haw hyh X k := by
    funext μ
    exact staircaseVirtualOperationPhysicalOp_realizes hA hL hK haw hyh X k μ
  have hcross (k : ℕ) :
      (regionInteriorBondProd (G := torusGraph width height) B
        (staircaseWindow ((a : ZMod width), (b : ZMod height)) L K k) : ℂ) •
        deformedRegionStateAssembled (G := torusGraph width height) A
          (staircaseWindow ((a : ZMod width), (b : ZMod height)) L K k)
          (regionInsertOfPhysicalOp (G := torusGraph width height) A
            (staircaseWindow ((a : ZMod width), (b : ZMod height)) L K k)
            (staircaseVirtualOperationPhysicalOp (B := A) hA hL hK haw hyh X k)) cfg =
      (regionInteriorBondProd (G := torusGraph width height) A
        (staircaseWindow ((a : ZMod width), (b : ZMod height)) L K k) : ℂ) •
        deformedRegionStateAssembled (G := torusGraph width height) B
          (staircaseWindow ((a : ZMod width), (b : ZMod height)) L K k)
          (regionInsertOfPhysicalOp (G := torusGraph width height) B
            (staircaseWindow ((a : ZMod width), (b : ZMod height)) L K k)
            (staircaseVirtualOperationPhysicalOp (B := A) hA hL hK haw hyh X k)) cfg := by
    exact deformedRegionState_regionInsertOfPhysicalOp_sameState
      (G := torusGraph width height) A B hAB
      (staircaseWindow ((a : ZMod width), (b : ZMod height)) L K k)
      (staircaseVirtualOperationPhysicalOp (B := A) hA hL hK haw hyh X k)
      (restrictRegionσ (V := TorusVertex width height) (d := d) _ cfg)
      (restrictRegionσ (V := TorusVertex width height) (d := d) _ cfg)
  have hcross_j := hcross j
  have hcross_j' := hcross j'
  rw [hrealizes j,
    deformedRegionStateAssembled_staircaseVirtualOperationInsert hATI hposA hL hK haw hyh X cfg,
    regionInteriorBondProd_staircaseWindow_eq (A := B) hBTI _ L K j 0,
    regionInteriorBondProd_staircaseWindow_eq (A := A) hATI _ L K j 0] at hcross_j
  rw [hrealizes j',
    deformedRegionStateAssembled_staircaseVirtualOperationInsert hATI hposA hL hK haw hyh X cfg,
    regionInteriorBondProd_staircaseWindow_eq (A := B) hBTI _ L K j' 0,
    regionInteriorBondProd_staircaseWindow_eq (A := A) hATI _ L K j' 0] at hcross_j'
  simp only [nsmul_eq_mul, smul_eq_mul] at hcross_j hcross_j'
  have hpA :
      (regionInteriorBondProd (G := torusGraph width height) A
        (staircaseWindow ((a : ZMod width), (b : ZMod height)) L K 0) : ℂ) ≠ 0 := by
    have hpos : 0 < regionInteriorBondProd (G := torusGraph width height) A
        (staircaseWindow ((a : ZMod width), (b : ZMod height)) L K 0) :=
      Finset.prod_pos (fun e _ => hposA e)
    exact_mod_cast hpos.ne'
  exact mul_left_cancel₀ hpA (hcross_j.symm.trans hcross_j')

/-- The coefficient on the first window with `Xᵀ` inserted equals the coefficient on the last
window with `X` inserted.

This is the direct coefficient-level shadow of the virtual-operation family.  The region-to-edge
identity sends both sides to the coefficient with `X` on the same reference edge, and translation
invariance identifies their non-boundary bond products.  No injectivity or complement hypothesis
is needed for this equality.  The open-boundary physical realization is the separate theorem
`staircaseVirtualOperationPhysicalOp_realizes`.

Source: arXiv:1804.04964, Lemma 5 at lines 2045--2252 and the two-dimensional proof sketch at
lines 2320--2444 of `Papers/1804.04964/paper_normal.tex`. -/
theorem regionInsertedCoeff_endWindows_eq_staircaseVirtualOperation {a b : ℕ}
    (hTI : IsTorusTranslationInvariant B)
    (hL : 2 ≤ L) (hK : 2 ≤ K) (ha0 : 1 ≤ a)
    (haw : a + 2 * L ≤ width) (hbh : b + 2 * K - 1 ≤ height)
    (hyh : 2 * K + 1 ≤ height)
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
  rw [regionInsertedCoeff_eq_smul_edgeInsertedCoeff,
    regionInsertedCoeff_eq_smul_edgeInsertedCoeff]
  have hcfg0 :
      assembleRegionσ (V := TorusVertex width height) (d := d)
          (staircaseWindow ((a : ZMod width), (b : ZMod height)) L K 0)
          (restrictRegionσ (V := TorusVertex width height) (d := d) _ cfg)
          (restrictRegionσ (V := TorusVertex width height) (d := d) _ cfg) = cfg :=
    assembleRegionσ_restrict _ cfg
  have hcfgLast :
      assembleRegionσ (V := TorusVertex width height) (d := d)
          (staircaseWindow ((a : ZMod width), (b : ZMod height)) L K (L + K - 1))
          (restrictRegionσ (V := TorusVertex width height) (d := d) _ cfg)
          (restrictRegionσ (V := TorusVertex width height) (d := d) _ cfg) = cfg :=
    assembleRegionσ_restrict _ cfg
  rw [hcfg0, hcfgLast]
  have hleft0 :
      (horizontalStaircaseReferenceEdge
        ((a : ZMod width), (b : ZMod height)) L K).1.1 ∉
        staircaseWindow ((a : ZMod width), (b : ZMod height)) L K 0 := by
    rw [referenceEdge_leftEndpoint_mem_staircaseWindow (by omega) (by omega) haw (by omega)]
    omega
  have hleftLast :
      (horizontalStaircaseReferenceEdge
        ((a : ZMod width), (b : ZMod height)) L K).1.1 ∈
        staircaseWindow ((a : ZMod width), (b : ZMod height)) L K (L + K - 1) := by
    rw [referenceEdge_leftEndpoint_mem_staircaseWindow (by omega) (by omega) haw (by omega)]
    omega
  simp only [regionEdgeOrient, hleft0, hleftLast, ite_false, ite_true,
    Matrix.transpose_transpose]
  rw [regionInteriorBondProd_staircaseWindow_eq hTI _ L K 0 (L + K - 1)]

end Torus

end PEPS
end TNLean
