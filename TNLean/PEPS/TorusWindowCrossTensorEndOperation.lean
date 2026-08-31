/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.NormalSquareInjectivity
import TNLean.PEPS.TorusWindowChain6
import TNLean.PEPS.TorusWindowPeeling.EndPhysicalOperation
import TNLean.PEPS.TorusWindowVirtualOperationFamily

/-!
# The cross-tensor end operation on a staircase edge

Fix a virtual matrix `X` for a tensor `A`, and realize it by the physical operations on the
staircase windows.  If a tensor `B` generates the same closed state, those same physical
operations give one common family on the genuine `B` window tensors.  The paper next compares the
two end windows with open boundaries and uses their injectivity to extract one unique virtual
matrix on the highlighted bond of `B`.

This file formalizes that extraction and the paper's ensuing composition argument.  The canonical
left end operations satisfy `O₁ᴬ(XY) = O₁ᴬ(X) O₁ᴬ(Y)`.  The canonical right end
operations satisfy `O₃ᴬ(XY) = O₃ᴬ(Y) O₃ᴬ(X)` in the underlying orientation, equivalently
ordinary multiplication after passing to `O₃ᵀ`.  Choosing the globally unique matrix on the
`B`-bond therefore gives a multiplicative cross-tensor assignment.  No external boundary
configuration is selected in this argument, and no bond-dimension identification or gauge is
constructed.

**Scope restriction (displayed horizontal staircase, `L, K ≥ 2`):** The result is stated for the
non-wrapping horizontal staircase coordinates supported by the present boundary-geometry API.
It assumes `L, K ≥ 2`, so the displayed windows straddle the highlighted edge; the paper treats
`L = K = 2` in its sketch and leaves the cases `L = 1` or `K = 1` unaddressed.  This clarification
and the rotation/translation assembly needed for the full two-dimensional corollary are recorded
in `docs/paper-gaps/peps_normal_ft_2d_overlap.tex`.

## References

* [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected entangled pair states
  generating the same state*, arXiv:1804.04964, Lemma 5 at lines 2045--2252 and the
  two-dimensional open-boundary and end-window comparison at lines 2368--2444 of
  `Papers/1804.04964/paper_normal.tex`](https://arxiv.org/abs/1804.04964).
-/

namespace TNLean
namespace PEPS

section RegionPhysicalOperation

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ}

private noncomputable def regionBoundaryConfigSplitAt
    (A : Tensor G d) (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f}) :
    RegionBoundaryConfig (G := G) A R ≃
      Fin (A.bondDim f.1) ×
        ((g : {g : {g : Edge G // IsRegionBoundaryEdge (G := G) R g} // g ≠ f}) →
          Fin (A.bondDim g.1.1)) :=
  Equiv.piSplitAt f (fun g ↦ Fin (A.bondDim g.1))

omit [Fintype V] in
private theorem sameAwayFromBond_iff_splitAt_snd_eq
    (A : Tensor G d) (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (mu nu : RegionBoundaryConfig (G := G) A R) :
    SameAwayFromBond f mu nu ↔
      (regionBoundaryConfigSplitAt (G := G) A R f mu).2 =
        (regionBoundaryConfigSplitAt (G := G) A R f nu).2 := by
  constructor
  · intro h
    funext g
    exact h g.1 g.2
  · intro h g hg
    exact congrFun h ⟨g, hg⟩

private theorem bondInsertedRegionInsert_splitAt
    (A : Tensor G d) (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (M : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ)
    (j : Fin (A.bondDim f.1))
    (eta : (g : {g : {g : Edge G // IsRegionBoundaryEdge (G := G) R g} // g ≠ f}) →
      Fin (A.bondDim g.1.1)) :
    let E := regionBoundaryConfigSplitAt (G := G) A R f
    bondInsertedRegionInsert (G := G) A R f M (E.symm (j, eta)) =
      ∑ i : Fin (A.bondDim f.1), M i j •
        regionBlockedWeight (G := G) A R (E.symm (i, eta)) := by
  classical
  dsimp only
  let E := regionBoundaryConfigSplitAt (G := G) A R f
  funext sigma
  rw [bondInsertedRegionInsert]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [← Equiv.sum_comp E.symm, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun i _ ↦ ?_)
  rw [Finset.sum_eq_single eta]
  · have hsame : SameAwayFromBond f (E.symm (i, eta)) (E.symm (j, eta)) := by
      rw [sameAwayFromBond_iff_splitAt_snd_eq A R f]
      simp only [E, Equiv.apply_symm_apply]
    have hif : (E.symm (i, eta)) f = i := by
      simp [E, regionBoundaryConfigSplitAt, Equiv.piSplitAt_symm_apply]
    have hjf : (E.symm (j, eta)) f = j := by
      simp [E, regionBoundaryConfigSplitAt, Equiv.piSplitAt_symm_apply]
    rw [ite_eq_left hsame, hif, hjf]
  · intro eta' _ heta'
    have hnot : ¬ SameAwayFromBond f (E.symm (i, eta')) (E.symm (j, eta)) := by
      intro hsame
      apply heta'
      rw [sameAwayFromBond_iff_splitAt_snd_eq A R f] at hsame
      simpa only [E, Equiv.apply_symm_apply] using hsame
    rw [ite_eq_right hnot, zero_mul]
  · intro heta
    exact absurd (Finset.mem_univ eta) heta

private theorem physicalOpOfRegionInsert_mul_of_apply
    (A : Tensor G d) (R : Finset V)
    (hR : RegionBlockedTensorInjective (G := G) A R)
    (C D E : RegionInsert (G := G) (d := d) A R)
    (h : ∀ mu, physicalOpOfRegionInsert (G := G) A R hR C (D mu) = E mu) :
    physicalOpOfRegionInsert (G := G) A R hR C *
        physicalOpOfRegionInsert (G := G) A R hR D =
      physicalOpOfRegionInsert (G := G) A R hR E := by
  classical
  apply LinearMap.ext
  intro v
  rw [Module.End.mul_apply]
  change physicalOpOfRegionInsert (G := G) A R hR C
      ((Fintype.linearCombination ℂ D)
        (regionBlockedLeftInverse (G := G) A R hR v)) =
    (Fintype.linearCombination ℂ E)
      (regionBlockedLeftInverse (G := G) A R hR v)
  simp only [Fintype.linearCombination_apply, map_sum, map_smul]
  refine Finset.sum_congr rfl (fun mu _ ↦ ?_)
  rw [h mu]

private theorem physicalOpOfBondInsertedRegionInsert_isO1
    (A : Tensor G d) (R : Finset V)
    (hR : RegionBlockedTensorInjective (G := G) A R)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (M : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ)
    (eta : (g : {g : {g : Edge G // IsRegionBoundaryEdge (G := G) R g} // g ≠ f}) →
      Fin (A.bondDim g.1.1)) :
    let E := regionBoundaryConfigSplitAt (G := G) A R f
    IsO1VirtualOperation
      (fun i : Fin (A.bondDim f.1) ↦
        regionBlockedWeight (G := G) A R (E.symm (i, eta)))
      (physicalOpOfRegionInsert (G := G) A R hR
        (bondInsertedRegionInsert (G := G) A R f M)) M := by
  dsimp only
  intro j
  rw [physicalOpOfRegionInsert_realizes, bondInsertedRegionInsert_splitAt]

private theorem physicalOpOfBondInsertedRegionInsert_mul
    (A : Tensor G d) (R : Finset V)
    (hR : RegionBlockedTensorInjective (G := G) A R)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (M N : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ) :
    physicalOpOfRegionInsert (G := G) A R hR
        (bondInsertedRegionInsert (G := G) A R f (M * N)) =
      physicalOpOfRegionInsert (G := G) A R hR
          (bondInsertedRegionInsert (G := G) A R f M) *
        physicalOpOfRegionInsert (G := G) A R hR
          (bondInsertedRegionInsert (G := G) A R f N) := by
  classical
  symm
  apply physicalOpOfRegionInsert_mul_of_apply A R hR
  intro nu
  rw [← physicalOpOfRegionInsert_realizes A R hR
      (bondInsertedRegionInsert (G := G) A R f N) nu,
    ← physicalOpOfRegionInsert_realizes A R hR
      (bondInsertedRegionInsert (G := G) A R f (M * N)) nu]
  let E := regionBoundaryConfigSplitAt (G := G) A R f
  rw [← E.symm_apply_apply nu, ← Module.End.mul_apply]
  rw [(physicalOpOfBondInsertedRegionInsert_isO1 A R hR f M (E nu).2).mul
      (physicalOpOfBondInsertedRegionInsert_isO1 A R hR f N (E nu).2) (E nu).1,
    physicalOpOfBondInsertedRegionInsert_isO1 A R hR f (M * N) (E nu).2 (E nu).1]

end RegionPhysicalOperation

section Torus

variable {width height : ℕ} [NeZero width] [NeZero height]
variable [Fact (1 < width)] [Fact (1 < height)]
variable {d L K : ℕ}

private noncomputable def regionPhysicalOperationCongr
    {R S : Finset (TorusVertex width height)} (h : R = S)
    (O : Module.End ℂ
      (RegionPhysicalConfig (V := TorusVertex width height) (d := d) R → ℂ)) :
    Module.End ℂ
      (RegionPhysicalConfig (V := TorusVertex width height) (d := d) S → ℂ) := by
  subst S
  exact O

omit [NeZero width] [NeZero height] [Fact (1 < width)] [Fact (1 < height)] in
private theorem regionPhysicalOperationCongr_mul
    {R S : Finset (TorusVertex width height)} (h : R = S)
    (O P : Module.End ℂ
      (RegionPhysicalConfig (V := TorusVertex width height) (d := d) R → ℂ)) :
    regionPhysicalOperationCongr h (O * P) =
      regionPhysicalOperationCongr h O * regionPhysicalOperationCongr h P := by
  subst S
  rfl

private noncomputable def regionInsertCongr
    (B : Tensor (torusGraph width height) d)
    {R S : Finset (TorusVertex width height)} (h : R = S)
    (C : RegionInsert (G := torusGraph width height) (d := d) B R) :
    RegionInsert (G := torusGraph width height) (d := d) B S := by
  subst S
  exact C

private theorem regionInsertOfPhysicalOp_congr
    (B : Tensor (torusGraph width height) d)
    {R S : Finset (TorusVertex width height)} (h : R = S)
    (O : Module.End ℂ
      (RegionPhysicalConfig (V := TorusVertex width height) (d := d) R → ℂ)) :
    regionInsertCongr B h (regionInsertOfPhysicalOp (G := torusGraph width height) B R O) =
      regionInsertOfPhysicalOp (G := torusGraph width height) B S
        (regionPhysicalOperationCongr h O) := by
  subst S
  rfl

private theorem extendInsert_congr_region
    (B : Tensor (torusGraph width height) d)
    {R S P : Finset (TorusVertex width height)} (h : R = S)
    (hRP : R ⊆ P) (hSP : S ⊆ P)
    (C : RegionInsert (G := torusGraph width height) (d := d) B R) :
    extendInsert (G := torusGraph width height) hRP C =
      extendInsert (G := torusGraph width height) hSP (regionInsertCongr B h C) := by
  subst S
  rfl

/-- The paper's left end operation `O₁` for the staircase family of `A`.

The last staircase window is the left end window, whose right boundary contains the highlighted
edge.  The canonical physical realization of `X` on that window is therefore the operation named
`O₁` in Lemma 5.

Source: arXiv:1804.04964, Lemma 5 at lines 2045--2129 and the staircase windows at lines
2320--2415 of `Papers/1804.04964/paper_normal.tex`. -/
noncomputable def staircaseO1PhysicalOp (A : Tensor (torusGraph width height) d) {a b : ℕ}
    (hA : NormalTorusArcWindowInjectivityHypotheses L K
      (regionInjectivityDataOf (G := torusGraph width height) A))
    (hL : 0 < L) (hK : 0 < K) (haw : a + 2 * L ≤ width) (hyh : 2 * K ≤ height)
    (X : Matrix
      (Fin (A.bondDim (horizontalStaircaseReferenceEdge
        ((a : ZMod width), (b : ZMod height)) L K)))
      (Fin (A.bondDim (horizontalStaircaseReferenceEdge
        ((a : ZMod width), (b : ZMod height)) L K))) ℂ) :
    Module.End ℂ
      (RegionPhysicalConfig (V := TorusVertex width height) (d := d)
        (horizontalStaircaseLeftWindow
          ((a : ZMod width), (b : ZMod height)) L K) → ℂ) :=
  regionPhysicalOperationCongr
    (staircaseWindow_last ((a : ZMod width), (b : ZMod height)) hL hK)
    (staircaseVirtualOperationPhysicalOp (B := A) hA hL hK haw hyh X (L + K - 1))

/-- The paper's right end operation `O₃` for the staircase family of `A`.

The first staircase window is the right end window, whose left boundary contains the highlighted
edge.  Its canonical physical realization is the underlying operation `O₃`; the extracted
relation is read in the paper's `O₃ᵀ` orientation.

Source: arXiv:1804.04964, Lemma 5 at lines 2045--2129 and the staircase windows at lines
2320--2415 of `Papers/1804.04964/paper_normal.tex`. -/
noncomputable def staircaseO3PhysicalOp (A : Tensor (torusGraph width height) d) {a b : ℕ}
    (hA : NormalTorusArcWindowInjectivityHypotheses L K
      (regionInjectivityDataOf (G := torusGraph width height) A))
    (hL : 0 < L) (hK : 0 < K) (haw : a + 2 * L ≤ width) (hyh : 2 * K ≤ height)
    (X : Matrix
      (Fin (A.bondDim (horizontalStaircaseReferenceEdge
        ((a : ZMod width), (b : ZMod height)) L K)))
      (Fin (A.bondDim (horizontalStaircaseReferenceEdge
        ((a : ZMod width), (b : ZMod height)) L K))) ℂ) :
    Module.End ℂ
      (RegionPhysicalConfig (V := TorusVertex width height) (d := d)
        (horizontalStaircaseRightWindow
          ((a : ZMod width), (b : ZMod height)) L K) → ℂ) :=
  regionPhysicalOperationCongr
    (staircaseWindow_zero ((a : ZMod width), (b : ZMod height)) L K)
    (staircaseVirtualOperationPhysicalOp (B := A) hA hL hK haw hyh X 0)

/-- The canonical left staircase operations preserve multiplication in the paper's ordinary
`O₁` order:
\[
  O₁ᴬ(XY)=O₁ᴬ(X)O₁ᴬ(Y).
\]

The proof uses the chosen left inverse only through its defining identity on the genuine blocked
window.  It therefore requires no spanning of the ambient physical space and no auxiliary
injectivity hypothesis.

Source: arXiv:1804.04964, the statement `X \mapsto O_1` at line 2044 and the phrase "by
composition" in Lemma 5 at line 2252 of `Papers/1804.04964/paper_normal.tex`. -/
theorem staircaseO1PhysicalOp_mul (A : Tensor (torusGraph width height) d) {a b : ℕ}
    (hA : NormalTorusArcWindowInjectivityHypotheses L K
      (regionInjectivityDataOf (G := torusGraph width height) A))
    (hL : 0 < L) (hK : 0 < K) (haw : a + 2 * L ≤ width) (hyh : 2 * K ≤ height)
    (X Y : Matrix
      (Fin (A.bondDim (horizontalStaircaseReferenceEdge
        ((a : ZMod width), (b : ZMod height)) L K)))
      (Fin (A.bondDim (horizontalStaircaseReferenceEdge
        ((a : ZMod width), (b : ZMod height)) L K))) ℂ) :
    staircaseO1PhysicalOp A hA hL hK haw hyh (X * Y) =
      staircaseO1PhysicalOp A hA hL hK haw hyh X *
        staircaseO1PhysicalOp A hA hL hK haw hyh Y := by
  unfold staircaseO1PhysicalOp
  rw [← regionPhysicalOperationCongr_mul]
  apply congrArg (regionPhysicalOperationCongr
    (staircaseWindow_last ((a : ZMod width), (b : ZMod height)) hL hK))
  unfold staircaseVirtualOperationPhysicalOp
  rw [staircaseVirtualOperationInsert_last, staircaseVirtualOperationInsert_last,
    staircaseVirtualOperationInsert_last]
  apply physicalOpOfBondInsertedRegionInsert_mul

/-- The underlying canonical right staircase operations preserve multiplication in the reversed
`O₃` order:
\[
  O₃ᴬ(XY)=O₃ᴬ(Y)O₃ᴬ(X).
\]
Equivalently, after reading the relation in the paper's transposed orientation,
`X \mapsto (O₃ᴬ(X))ᵀ` preserves multiplication in the ordinary order.  The reversal comes
exactly from `(XY)ᵀ=YᵀXᵀ`; no transpose is chosen on the abstract physical endomorphism
space.

Source: arXiv:1804.04964, the statement `X \mapsto O_3^T` at line 2044, the assignments
`O_3^T \mapsto X` and `O_3 \mapsto X^T` at lines 2129 and 2252, and the phrase "by composition"
at line 2252 of `Papers/1804.04964/paper_normal.tex`. -/
theorem staircaseO3PhysicalOp_mul (A : Tensor (torusGraph width height) d) {a b : ℕ}
    (hA : NormalTorusArcWindowInjectivityHypotheses L K
      (regionInjectivityDataOf (G := torusGraph width height) A))
    (hL : 0 < L) (hK : 0 < K) (haw : a + 2 * L ≤ width) (hyh : 2 * K ≤ height)
    (X Y : Matrix
      (Fin (A.bondDim (horizontalStaircaseReferenceEdge
        ((a : ZMod width), (b : ZMod height)) L K)))
      (Fin (A.bondDim (horizontalStaircaseReferenceEdge
        ((a : ZMod width), (b : ZMod height)) L K))) ℂ) :
    staircaseO3PhysicalOp A hA hL hK haw hyh (X * Y) =
      staircaseO3PhysicalOp A hA hL hK haw hyh Y *
        staircaseO3PhysicalOp A hA hL hK haw hyh X := by
  unfold staircaseO3PhysicalOp
  rw [← regionPhysicalOperationCongr_mul]
  apply congrArg (regionPhysicalOperationCongr
    (staircaseWindow_zero ((a : ZMod width), (b : ZMod height)) L K))
  unfold staircaseVirtualOperationPhysicalOp
  rw [staircaseVirtualOperationInsert_zero, staircaseVirtualOperationInsert_zero,
    staircaseVirtualOperationInsert_zero, Matrix.transpose_mul]
  apply physicalOpOfBondInsertedRegionInsert_mul

/-- **The virtual operation on `B` extracted from the staircase operations of `A`.**

Let `A` and `B` be translation-invariant tensors with the same closed state and with every cyclic
`L × K` window injective.  Apply the canonical physical operations `Oⱼᴬ(X)` to the genuine
window tensors of `B`.  Their common transformed state gives, by the paper's consecutive-window
and corner-completion argument, an equality of the two open end-window inserts.  Injectivity of
those two genuine `B` windows then extracts a unique matrix `Y` on the highlighted bond of
`B` such that the left operation `O₁ᴬ(X)` realizes `Y`, while the right operation `O₃ᴬ(X)`
realizes `Y` in the paper's transposed `O₃ᵀ` orientation.

No equality between the bond dimensions of `A` and `B` is assumed or concluded.  This theorem
does not compare `X` and `Y`, nor does it assert that the assignment `X ↦ Y` is multiplicative.

Source: arXiv:1804.04964, the common open-boundary family at lines 2368--2415, the end-window
comparison at lines 2415--2444, and the two-end extraction of Lemma 5 at lines 2213--2252 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem existsUnique_crossTensorVirtualOperation_of_staircasePhysicalOp_sameState
    (A B : Tensor (torusGraph width height) d) {a b : ℕ}
    (hA : NormalTorusArcWindowInjectivityHypotheses L K
      (regionInjectivityDataOf (G := torusGraph width height) A))
    (hB : NormalTorusArcWindowInjectivityHypotheses L K
      (regionInjectivityDataOf (G := torusGraph width height) B))
    (hATI : IsTorusTranslationInvariant A) (hBTI : IsTorusTranslationInvariant B)
    (hAB : SameState A B)
    (hposA : ∀ e : Edge (torusGraph width height), 0 < A.bondDim e)
    (hposB : ∀ e : Edge (torusGraph width height), 0 < B.bondDim e)
    (hL : 2 ≤ L) (hK : 2 ≤ K) (ha0 : 1 ≤ a)
    (haw : a + 2 * L ≤ width) (hbh : b + 2 * K - 1 ≤ height)
    (hxw : 2 * L + 1 ≤ width) (hyh : 2 * K + 1 ≤ height)
    (X : Matrix
      (Fin (A.bondDim (horizontalStaircaseReferenceEdge
        ((a : ZMod width), (b : ZMod height)) L K)))
      (Fin (A.bondDim (horizontalStaircaseReferenceEdge
        ((a : ZMod width), (b : ZMod height)) L K))) ℂ) :
    let s : TorusVertex width height := ((a : ZMod width), (b : ZMod height))
    let Wleft := horizontalStaircaseLeftWindow s L K
    let Wright := horizontalStaircaseRightWindow s L K
    let Eleft := horizontalStaircaseLeftWindowBoundaryConfigEquiv B
      (by omega) (by omega) ha0 haw hbh
    let Eright := horizontalStaircaseRightWindowBoundaryConfigEquiv B
      (by omega) (by omega) ha0 haw hbh
    ∃! Y : Matrix
        (Fin (B.bondDim (horizontalStaircaseReferenceEdge s L K)))
        (Fin (B.bondDim (horizontalStaircaseReferenceEdge s L K))) ℂ,
      (∀ etaLeft : HorizontalStaircaseLeftExternalBoundaryConfig B (L := L) (K := K) s,
        IsO1VirtualOperation
          (fun k : Fin (B.bondDim (horizontalStaircaseReferenceEdge s L K)) ↦
            regionBlockedWeight (G := torusGraph width height) B Wleft
              (Eleft.symm (k, etaLeft)))
          (staircaseO1PhysicalOp A hA (by omega) (by omega) haw (by omega) X) Y) ∧
      ∀ etaRight : HorizontalStaircaseRightExternalBoundaryConfig B (L := L) (K := K) s,
        IsO3TransposeVirtualOperation
          (fun k : Fin (B.bondDim (horizontalStaircaseReferenceEdge s L K)) ↦
            regionBlockedWeight (G := torusGraph width height) B Wright
              (Eright.symm (k, etaRight)))
          (staircaseO3PhysicalOp A hA (by omega) (by omega) haw (by omega) X) Y := by
  classical
  dsimp only
  let s : TorusVertex width height := ((a : ZMod width), (b : ZMod height))
  let O₁ := staircaseO1PhysicalOp A hA (by omega) (by omega) haw (by omega) X
  let O₃ := staircaseO3PhysicalOp A hA (by omega) (by omega) haw (by omega) X
  let C : ∀ j, RegionInsert (G := torusGraph width height) (d := d) B
      (staircaseWindow s L K j) :=
    fun j ↦ regionInsertOfPhysicalOp (G := torusGraph width height) B
      (staircaseWindow s L K j)
      (staircaseVirtualOperationPhysicalOp (B := A) hA
        (by omega) (by omega) haw (by omega) X j)
  let common := deformedRegionStateAssembled (G := torusGraph width height) B
    (staircaseWindow s L K 0) (C 0)
  have hagree : ∀ j, j < L + K →
      deformedRegionStateAssembled (G := torusGraph width height) B
        (staircaseWindow s L K j) (C j) = common := by
    intro j _
    exact deformedRegionStateAssembled_staircasePhysicalOp_sameState
      (L := L) (K := K) (a := a) (b := b) (j := j) (j' := 0)
      hA hATI hBTI hAB hposA (by omega) (by omega) haw (by omega) X
  have hUB : RegionInjectivityUnionClosure
      (regionInjectivityDataOf (G := torusGraph width height) B) :=
    regionInjectivityUnionClosure_of_overlap B hposB
  have hend := staircasePair_insert_eq_open hB hUB hposB hL hK hxw hyh s C common hagree
  have hleftInjective : RegionBlockedTensorInjective (G := torusGraph width height) B
      (horizontalStaircaseLeftWindow s L K) := by
    have hi := hB.horizontalStaircaseLeftWindow_injective s
    rwa [regionInjectivityDataOf_isInjective] at hi
  have hrightInjective : RegionBlockedTensorInjective (G := torusGraph width height) B
      (horizontalStaircaseRightWindow s L K) := by
    have hi := hB.horizontalStaircaseRightWindow_injective s
    rwa [regionInjectivityDataOf_isInjective] at hi
  have hLpos : 0 < L := by omega
  have hKpos : 0 < K := by omega
  have hlast := staircaseWindow_last s hLpos hKpos
  have hzero := staircaseWindow_zero s L K
  have hCleft :
      regionInsertCongr B hlast (C (L + K - 1)) =
        regionInsertOfPhysicalOp (G := torusGraph width height) B
          (horizontalStaircaseLeftWindow s L K) O₁ := by
    simpa only [C, O₁, s, staircaseO1PhysicalOp] using
      regionInsertOfPhysicalOp_congr B hlast
        (staircaseVirtualOperationPhysicalOp (B := A) hA hLpos hKpos haw (by omega) X
          (L + K - 1))
  have hCright :
      regionInsertCongr B hzero (C 0) =
        regionInsertOfPhysicalOp (G := torusGraph width height) B
          (horizontalStaircaseRightWindow s L K) O₃ := by
    simpa only [C, O₃, s, staircaseO3PhysicalOp] using
      regionInsertOfPhysicalOp_congr B hzero
        (staircaseVirtualOperationPhysicalOp (B := A) hA hLpos hKpos haw (by omega) X 0)
  have heq :
      extendInsert (G := torusGraph width height)
          (horizontalStaircaseLeftWindow_subset_endPair s)
          (fun μ ↦ O₁ (regionBlockedWeight (G := torusGraph width height) B
            (horizontalStaircaseLeftWindow s L K) μ)) =
        extendInsert (G := torusGraph width height)
          (horizontalStaircaseRightWindow_subset_endPair s)
          (fun μ ↦ O₃ (regionBlockedWeight (G := torusGraph width height) B
            (horizontalStaircaseRightWindow s L K) μ)) := by
    calc
      _ = extendInsert (G := torusGraph width height)
          (horizontalStaircaseLeftWindow_subset_endPair s)
          (regionInsertCongr B hlast (C (L + K - 1))) := by
            exact congrArg
              (extendInsert (G := torusGraph width height)
                (horizontalStaircaseLeftWindow_subset_endPair s)) hCleft.symm
      _ = extendInsert (G := torusGraph width height)
          (staircaseWindow_last_subset_endPair hLpos hKpos s) (C (L + K - 1)) :=
            (extendInsert_congr_region B hlast
              (staircaseWindow_last_subset_endPair hLpos hKpos s)
              (horizontalStaircaseLeftWindow_subset_endPair s) (C (L + K - 1))).symm
      _ = extendInsert (G := torusGraph width height)
          (staircaseWindow_zero_subset_endPair s L K) (C 0) := hend.symm
      _ = extendInsert (G := torusGraph width height)
          (horizontalStaircaseRightWindow_subset_endPair s)
          (regionInsertCongr B hzero (C 0)) :=
            extendInsert_congr_region B hzero
              (staircaseWindow_zero_subset_endPair s L K)
              (horizontalStaircaseRightWindow_subset_endPair s) (C 0)
      _ = _ := by
        exact congrArg
          (extendInsert (G := torusGraph width height)
            (horizontalStaircaseRightWindow_subset_endPair s)) hCright
  simpa only [s, O₁, O₃] using
    existsUnique_virtualOperation_of_horizontalStaircaseEndPhysicalOperations
      B hBTI (by omega) (by omega) ha0 haw hbh hposB hleftInjective hrightInjective O₁ O₃ heq

/-- The canonical cross-tensor matrix assignment on the highlighted staircase edge.

For `X` on the `A`-bond, this is the unique matrix on the `B`-bond simultaneously determined by
the `O₁ᴬ(X)` relation at every left external boundary configuration and the `O₃ᴬ(X)` relation,
read in the paper's `O₃ᵀ` orientation, at every right external boundary configuration.  The
definition chooses the witness of the globally quantified uniqueness theorem; it does not choose
an external boundary configuration.

Source: arXiv:1804.04964, the cross-tensor assignment `X \mapsto Y` at lines 563--582,
the uniquely defined assignments `O_1 \mapsto X` and `O_3^T \mapsto X` in Lemma 5 at lines
2129 and 2252, and the two-dimensional staircase comparison at lines 2320--2444 of
`Papers/1804.04964/paper_normal.tex`. -/
noncomputable def staircaseCrossTensorVirtualOperation
    (A B : Tensor (torusGraph width height) d) {a b : ℕ}
    (hA : NormalTorusArcWindowInjectivityHypotheses L K
      (regionInjectivityDataOf (G := torusGraph width height) A))
    (hB : NormalTorusArcWindowInjectivityHypotheses L K
      (regionInjectivityDataOf (G := torusGraph width height) B))
    (hATI : IsTorusTranslationInvariant A) (hBTI : IsTorusTranslationInvariant B)
    (hAB : SameState A B)
    (hposA : ∀ e : Edge (torusGraph width height), 0 < A.bondDim e)
    (hposB : ∀ e : Edge (torusGraph width height), 0 < B.bondDim e)
    (hL : 2 ≤ L) (hK : 2 ≤ K) (ha0 : 1 ≤ a)
    (haw : a + 2 * L ≤ width) (hbh : b + 2 * K - 1 ≤ height)
    (hxw : 2 * L + 1 ≤ width) (hyh : 2 * K + 1 ≤ height)
    (X : Matrix
      (Fin (A.bondDim (horizontalStaircaseReferenceEdge
        ((a : ZMod width), (b : ZMod height)) L K)))
      (Fin (A.bondDim (horizontalStaircaseReferenceEdge
        ((a : ZMod width), (b : ZMod height)) L K))) ℂ) :
    Matrix
      (Fin (B.bondDim (horizontalStaircaseReferenceEdge
        ((a : ZMod width), (b : ZMod height)) L K)))
      (Fin (B.bondDim (horizontalStaircaseReferenceEdge
        ((a : ZMod width), (b : ZMod height)) L K))) ℂ :=
  Classical.choose
    (existsUnique_crossTensorVirtualOperation_of_staircasePhysicalOp_sameState
      A B hA hB hATI hBTI hAB hposA hposB hL hK ha0 haw hbh hxw hyh X).exists

/-- The canonical cross-tensor matrix satisfies both end relations for every external boundary
configuration.

The left relation is the source assignment `O₁ ↦ X`; the right relation is the source
assignment `O₃ᵀ ↦ X`, equivalently `O₃ ↦ Xᵀ`.

Source: arXiv:1804.04964, Lemma 5 at lines 2213--2252 and the two-dimensional end-window
comparison at lines 2415--2444 of `Papers/1804.04964/paper_normal.tex`. -/
theorem staircaseCrossTensorVirtualOperation_spec
    (A B : Tensor (torusGraph width height) d) {a b : ℕ}
    (hA : NormalTorusArcWindowInjectivityHypotheses L K
      (regionInjectivityDataOf (G := torusGraph width height) A))
    (hB : NormalTorusArcWindowInjectivityHypotheses L K
      (regionInjectivityDataOf (G := torusGraph width height) B))
    (hATI : IsTorusTranslationInvariant A) (hBTI : IsTorusTranslationInvariant B)
    (hAB : SameState A B)
    (hposA : ∀ e : Edge (torusGraph width height), 0 < A.bondDim e)
    (hposB : ∀ e : Edge (torusGraph width height), 0 < B.bondDim e)
    (hL : 2 ≤ L) (hK : 2 ≤ K) (ha0 : 1 ≤ a)
    (haw : a + 2 * L ≤ width) (hbh : b + 2 * K - 1 ≤ height)
    (hxw : 2 * L + 1 ≤ width) (hyh : 2 * K + 1 ≤ height)
    (X : Matrix
      (Fin (A.bondDim (horizontalStaircaseReferenceEdge
        ((a : ZMod width), (b : ZMod height)) L K)))
      (Fin (A.bondDim (horizontalStaircaseReferenceEdge
        ((a : ZMod width), (b : ZMod height)) L K))) ℂ) :
    let s : TorusVertex width height := ((a : ZMod width), (b : ZMod height))
    let Wleft := horizontalStaircaseLeftWindow s L K
    let Wright := horizontalStaircaseRightWindow s L K
    let Eleft := horizontalStaircaseLeftWindowBoundaryConfigEquiv B
      (by omega) (by omega) ha0 haw hbh
    let Eright := horizontalStaircaseRightWindowBoundaryConfigEquiv B
      (by omega) (by omega) ha0 haw hbh
    (∀ etaLeft : HorizontalStaircaseLeftExternalBoundaryConfig B (L := L) (K := K) s,
        IsO1VirtualOperation
          (fun k : Fin (B.bondDim (horizontalStaircaseReferenceEdge s L K)) ↦
            regionBlockedWeight (G := torusGraph width height) B Wleft
              (Eleft.symm (k, etaLeft)))
          (staircaseO1PhysicalOp A hA (by omega) (by omega) haw (by omega) X)
          (staircaseCrossTensorVirtualOperation A B hA hB hATI hBTI hAB hposA hposB
            hL hK ha0 haw hbh hxw hyh X)) ∧
      ∀ etaRight : HorizontalStaircaseRightExternalBoundaryConfig B (L := L) (K := K) s,
        IsO3TransposeVirtualOperation
          (fun k : Fin (B.bondDim (horizontalStaircaseReferenceEdge s L K)) ↦
            regionBlockedWeight (G := torusGraph width height) B Wright
              (Eright.symm (k, etaRight)))
          (staircaseO3PhysicalOp A hA (by omega) (by omega) haw (by omega) X)
          (staircaseCrossTensorVirtualOperation A B hA hB hATI hBTI hAB hposA hposB
            hL hK ha0 haw hbh hxw hyh X) := by
  simpa only [staircaseCrossTensorVirtualOperation] using
    Classical.choose_spec
      (existsUnique_crossTensorVirtualOperation_of_staircasePhysicalOp_sameState
        A B hA hB hATI hBTI hAB hposA hposB hL hK ha0 haw hbh hxw hyh X).exists

/-- The canonical cross-tensor matrix assignment preserves multiplication:
\[
  Y_{A\to B}(X_1X_2)=Y_{A\to B}(X_1)Y_{A\to B}(X_2).
\]

Here `Y_{A\to B}(X)` only disambiguates the paper's input matrix `X` and uniquely recovered
output matrix `Y`; the source calls the assignment `X \mapsto Y`.

Both end relations remain globally quantified throughout the proof.  On the left,
`O₁ᴬ(XY)=O₁ᴬ(X)O₁ᴬ(Y)` and `IsO1VirtualOperation.mul` give the product in ordinary
order.  On the right, the underlying operations satisfy
`O₃ᴬ(XY)=O₃ᴬ(Y)O₃ᴬ(X)`; `IsO3TransposeVirtualOperation.mul` reads this as ordinary
multiplication in the `O₃ᵀ` orientation.  The globally unique `B`-bond matrix then gives the
displayed equality.

This theorem records the multiplicative part of the source's algebra-homomorphism assertion.
Additivity, scalar compatibility, and the unit law are not packaged here.

Source: arXiv:1804.04964, the cross-tensor algebra-homomorphism statement `X \mapsto Y` at
line 582, the end-operation statements in Lemma 5 at lines 2129 and 2252, and the
two-dimensional reduction to Lemma 5 at lines 2320--2444 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem staircaseCrossTensorVirtualOperation_mul
    (A B : Tensor (torusGraph width height) d) {a b : ℕ}
    (hA : NormalTorusArcWindowInjectivityHypotheses L K
      (regionInjectivityDataOf (G := torusGraph width height) A))
    (hB : NormalTorusArcWindowInjectivityHypotheses L K
      (regionInjectivityDataOf (G := torusGraph width height) B))
    (hATI : IsTorusTranslationInvariant A) (hBTI : IsTorusTranslationInvariant B)
    (hAB : SameState A B)
    (hposA : ∀ e : Edge (torusGraph width height), 0 < A.bondDim e)
    (hposB : ∀ e : Edge (torusGraph width height), 0 < B.bondDim e)
    (hL : 2 ≤ L) (hK : 2 ≤ K) (ha0 : 1 ≤ a)
    (haw : a + 2 * L ≤ width) (hbh : b + 2 * K - 1 ≤ height)
    (hxw : 2 * L + 1 ≤ width) (hyh : 2 * K + 1 ≤ height)
    (X Y : Matrix
      (Fin (A.bondDim (horizontalStaircaseReferenceEdge
        ((a : ZMod width), (b : ZMod height)) L K)))
      (Fin (A.bondDim (horizontalStaircaseReferenceEdge
        ((a : ZMod width), (b : ZMod height)) L K))) ℂ) :
    staircaseCrossTensorVirtualOperation A B hA hB hATI hBTI hAB hposA hposB
        hL hK ha0 haw hbh hxw hyh (X * Y) =
      staircaseCrossTensorVirtualOperation A B hA hB hATI hBTI hAB hposA hposB
          hL hK ha0 haw hbh hxw hyh X *
        staircaseCrossTensorVirtualOperation A B hA hB hATI hBTI hAB hposA hposB
          hL hK ha0 haw hbh hxw hyh Y := by
  have hspecXY := staircaseCrossTensorVirtualOperation_spec A B hA hB hATI hBTI hAB
    hposA hposB hL hK ha0 haw hbh hxw hyh (X * Y)
  have hspecX := staircaseCrossTensorVirtualOperation_spec A B hA hB hATI hBTI hAB
    hposA hposB hL hK ha0 haw hbh hxw hyh X
  have hspecY := staircaseCrossTensorVirtualOperation_spec A B hA hB hATI hBTI hAB
    hposA hposB hL hK ha0 haw hbh hxw hyh Y
  have hex := existsUnique_crossTensorVirtualOperation_of_staircasePhysicalOp_sameState
    A B hA hB hATI hBTI hAB hposA hposB hL hK ha0 haw hbh hxw hyh (X * Y)
  dsimp only at hspecXY hspecX hspecY hex
  apply hex.unique hspecXY
  constructor
  · intro etaLeft
    simpa only [staircaseO1PhysicalOp_mul] using
      (hspecX.1 etaLeft).mul (hspecY.1 etaLeft)
  · intro etaRight
    simpa only [staircaseO3PhysicalOp_mul] using
      (hspecX.2 etaRight).mul (hspecY.2 etaRight)

end Torus

end PEPS
end TNLean
