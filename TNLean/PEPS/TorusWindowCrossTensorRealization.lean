/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.TorusWindowCrossTensorEndOperation
import TNLean.PEPS.RegionBlock.Algebra

/-!
# Physical realization of staircase bond insertions

The left staircase operation realizes a bond insertion for every boundary configuration.
The globally quantified cross-tensor end relation gives the same realization on the second
tensor. Addition and complex scalar multiplication commute with these physical operations.

**Scope restriction (displayed horizontal staircase):** The staircase declarations use the
non-wrapping horizontal coordinates of `TorusWindowCrossTensorEndOperation`. The cross-tensor
assignment assumes `L, K ≥ 2`; the smaller windows and the rotation/translation assembly for the
full two-dimensional theorem remain recorded in
`docs/paper-gaps/peps_normal_ft_2d_overlap.tex`. The generic region statements have no such
restriction.

Source: arXiv:1804.04964, the algebra assignment at lines 563--582 and the two-dimensional
end-window comparison at lines 2368--2444 of `Papers/1804.04964/paper_normal.tex`.
-/

namespace TNLean.PEPS
open scoped BigOperators Matrix

section Region
variable {V : Type*} [Fintype V] [LinearOrder V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ}

/-- Physical operations agreeing on every blocked tensor of one state representation agree on
every blocked tensor of a second representation, when both complementary regions are injective.

Source: arXiv:1804.04964, the equal-image argument at lines 400--457. -/
theorem physicalOps_eq_on_blocks_of_sameState
    (A B : Tensor G d) (R : Finset V) (hAB : SameState A B)
    (hCA : RegionBlockedTensorInjective (G := G) A (Finset.univ \ R))
    (hCB : RegionBlockedTensorInjective (G := G) B (Finset.univ \ R))
    (hposA : ∀ e : Edge G, 0 < A.bondDim e)
    (hposB : ∀ e : Edge G, 0 < B.bondDim e)
    (O P : Module.End ℂ (RegionPhysicalConfig (V := V) (d := d) R → ℂ))
    (h : ∀ μ, O (regionBlockedWeight (G := G) A R μ) =
      P (regionBlockedWeight (G := G) A R μ))
    (μ : RegionBoundaryConfig (G := G) B R) :
    O (regionBlockedWeight (G := G) B R μ) =
      P (regionBlockedWeight (G := G) B R μ) := by
  apply LinearMap.eqOn_span (s := Set.range (regionBlockedWeight (G := G) A R))
  · exact fun _ ⟨ν, hν⟩ ↦ hν ▸ h ν
  · rw [← range_regionBlockedTensorMap_eq_span,
      range_regionBlockedTensorMap_eq_of_sameState A B R hAB hCA hCB hposA hposB,
      range_regionBlockedTensorMap_eq_span]
    exact Submodule.subset_span ⟨μ, rfl⟩

end Region

section IdentityInsert
variable {V : Type*} [Fintype V] [LinearOrder V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ}

/-- Inserting the identity on a boundary bond leaves each blocked tensor unchanged. -/
theorem bondInsertedRegionInsert_one (A : Tensor G d) (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (μ : RegionBoundaryConfig (G := G) A R) :
    bondInsertedRegionInsert (G := G) A R f 1 μ =
      regionBlockedWeight (G := G) A R μ := by
  classical
  simpa [Matrix.one_apply] using
    bondInsertedRegionInsert_splitAt A R f 1
      (regionBoundaryConfigSplitAt (G := G) A R f μ).1
      (regionBoundaryConfigSplitAt (G := G) A R f μ).2

/-- The family of all boundary insertions determines its bond matrix, when the region and its
complement are injective.

Source: arXiv:1804.04964, Lemma `inj_isomorph`, lines 377--457. -/
theorem bondInsertedRegionInsert_injective (A : Tensor G d) (R : Finset V)
    (hR : RegionBlockedTensorInjective (G := G) A R)
    (hC : RegionBlockedTensorInjective (G := G) A (Finset.univ \ R))
    (hpos : ∀ e : Edge G, 0 < A.bondDim e)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f}) :
    Function.Injective (bondInsertedRegionInsert (G := G) A R f) := by
  intro X Y h
  apply regionInsertedCoeff_injective A R hR hC hpos f X Y
  intro σ τ
  rw [← deformedRegionState_bondInsertedRegionInsert,
    ← deformedRegionState_bondInsertedRegionInsert, h]

end IdentityInsert

section InsertLinearity
variable {V : Type*} [Fintype V] [LinearOrder V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ}

private theorem physicalOpOfRegionInsert_add (A : Tensor G d) (R : Finset V)
    (hR : RegionBlockedTensorInjective (G := G) A R)
    (C D : RegionInsert (G := G) (d := d) A R) :
    physicalOpOfRegionInsert (G := G) A R hR (C + D) =
      physicalOpOfRegionInsert (G := G) A R hR C +
        physicalOpOfRegionInsert (G := G) A R hR D := by
  ext v σ
  simp [physicalOpOfRegionInsert, Fintype.linearCombination_apply, smul_add,
    Finset.sum_add_distrib]

private theorem physicalOpOfRegionInsert_smul (A : Tensor G d) (R : Finset V)
    (hR : RegionBlockedTensorInjective (G := G) A R)
    (c : ℂ) (C : RegionInsert (G := G) (d := d) A R) :
    physicalOpOfRegionInsert (G := G) A R hR (c • C) =
      c • physicalOpOfRegionInsert (G := G) A R hR C := by
  ext v σ
  simp [physicalOpOfRegionInsert, Fintype.linearCombination_apply,
    smul_smul, Finset.mul_sum, mul_comm, mul_left_comm]

/-- Boundary bond insertion preserves addition of bond matrices. -/
theorem bondInsertedRegionInsert_add (A : Tensor G d) (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (X Y : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ) :
    bondInsertedRegionInsert (G := G) A R f (X + Y) =
      bondInsertedRegionInsert (G := G) A R f X +
        bondInsertedRegionInsert (G := G) A R f Y := by
  ext μ σ
  simp [bondInsertedRegionInsert, add_mul, ← Finset.sum_add_distrib, ite_add_ite]

/-- Boundary bond insertion preserves complex scalar multiplication. -/
theorem bondInsertedRegionInsert_smul (A : Tensor G d) (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (c : ℂ) (X : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ) :
    bondInsertedRegionInsert (G := G) A R f (c • X) =
      c • bondInsertedRegionInsert (G := G) A R f X := by
  ext μ σ
  simp [bondInsertedRegionInsert, smul_eq_mul, Finset.mul_sum, mul_ite, mul_assoc]

end InsertLinearity

section CastIdentity
variable {width height d : ℕ} [NeZero width] [NeZero height]
variable [Fact (1 < width)] [Fact (1 < height)]

omit [NeZero width] [NeZero height] [Fact (1 < width)] [Fact (1 < height)] in
private theorem regionPhysicalOperationCongr_add
    {R S : Finset (TorusVertex width height)} (h : R = S)
    (O P : Module.End ℂ (RegionPhysicalConfig (V := TorusVertex width height) (d := d) R → ℂ)) :
    regionPhysicalOperationCongr h (O + P) =
      regionPhysicalOperationCongr h O + regionPhysicalOperationCongr h P := by
  cases h
  rfl

omit [NeZero width] [NeZero height] [Fact (1 < width)] [Fact (1 < height)] in
private theorem regionPhysicalOperationCongr_smul
    {R S : Finset (TorusVertex width height)} (h : R = S) (c : ℂ)
    (O : Module.End ℂ (RegionPhysicalConfig (V := TorusVertex width height) (d := d) R → ℂ)) :
    regionPhysicalOperationCongr h (c • O) = c • regionPhysicalOperationCongr h O := by
  cases h
  rfl

end CastIdentity

section StaircaseAlgebra
variable {width height : ℕ} [NeZero width] [NeZero height]
variable [Fact (1 < width)] [Fact (1 < height)]
variable {d L K a b : ℕ}
variable (A B : Tensor (torusGraph width height) d)
variable (hA : NormalTorusArcWindowInjectivityHypotheses L K
  (regionInjectivityDataOf (G := torusGraph width height) A))
variable (hB : NormalTorusArcWindowInjectivityHypotheses L K
  (regionInjectivityDataOf (G := torusGraph width height) B))
variable (hATI : IsTorusTranslationInvariant A) (hBTI : IsTorusTranslationInvariant B)
variable (hAB : SameState A B)
variable (hposA : ∀ e : Edge (torusGraph width height), 0 < A.bondDim e)
variable (hposB : ∀ e : Edge (torusGraph width height), 0 < B.bondDim e)
variable (hL : 2 ≤ L) (hK : 2 ≤ K) (ha0 : 1 ≤ a)
variable (haw : a + 2 * L ≤ width) (hbh : b + 2 * K - 1 ≤ height)
variable (hxw : 2 * L + 1 ≤ width) (hyh : 2 * K + 1 ≤ height)

private theorem regionInsertCongr_bondInserted
    (A : Tensor (torusGraph width height) d)
    {R S : Finset (TorusVertex width height)} (h : R = S)
    (e : Edge (torusGraph width height))
    (hR : IsRegionBoundaryEdge (G := torusGraph width height) R e)
    (hS : IsRegionBoundaryEdge (G := torusGraph width height) S e)
    (X : Matrix (Fin (A.bondDim e)) (Fin (A.bondDim e)) ℂ) :
    regionInsertCongr A h (bondInsertedRegionInsert (G := torusGraph width height) A R ⟨e, hR⟩ X) =
      bondInsertedRegionInsert (G := torusGraph width height) A S ⟨e, hS⟩ X := by
  subst S
  rfl

/-- The canonical left physical operation realizes the prescribed bond insertion at every
boundary configuration.

Source: arXiv:1804.04964, the physical realization at lines 563--582 and 2368--2444. -/
theorem staircaseO1PhysicalOp_realizes_insert
    (A : Tensor (torusGraph width height) d)
    (hA : NormalTorusArcWindowInjectivityHypotheses L K
      (regionInjectivityDataOf (G := torusGraph width height) A))
    (hL : 0 < L) (hK : 0 < K) (ha0 : 1 ≤ a)
    (haw : a + 2 * L ≤ width) (hbh : b + 2 * K - 1 ≤ height) (hyh : 2 * K ≤ height)
    (X : Matrix (Fin (A.bondDim (horizontalStaircaseReferenceEdge
        ((a : ZMod width), (b : ZMod height)) L K)))
      (Fin (A.bondDim (horizontalStaircaseReferenceEdge
        ((a : ZMod width), (b : ZMod height)) L K))) ℂ) :
    regionInsertOfPhysicalOp (G := torusGraph width height) A
      (horizontalStaircaseLeftWindow ((a : ZMod width), (b : ZMod height)) L K)
      (staircaseO1PhysicalOp A hA hL hK haw hyh X) =
    bondInsertedRegionInsert (G := torusGraph width height) A
      (horizontalStaircaseLeftWindow ((a : ZMod width), (b : ZMod height)) L K)
      ⟨_, isRegionBoundaryEdge_horizontalStaircaseLeftWindow_referenceEdge
        A hL hK ha0 haw hbh⟩ X := by
  have hreal : regionInsertOfPhysicalOp (G := torusGraph width height) A
      (staircaseWindow ((a : ZMod width), (b : ZMod height)) L K (L + K - 1))
      (staircaseVirtualOperationPhysicalOp (B := A) hA hL hK haw hyh X (L + K - 1)) =
      staircaseVirtualOperationInsert (B := A) hL hK haw hyh X (L + K - 1) := by
    funext μ
    exact staircaseVirtualOperationPhysicalOp_realizes hA hL hK haw hyh X (L + K - 1) μ
  have h := congrArg (regionInsertCongr A
    (staircaseWindow_last ((a : ZMod width), (b : ZMod height)) hL hK)) hreal
  rw [regionInsertOfPhysicalOp_congr, staircaseVirtualOperationInsert_last] at h
  rw [regionInsertCongr_bondInserted A
    (staircaseWindow_last ((a : ZMod width), (b : ZMod height)) hL hK) _ _
    (isRegionBoundaryEdge_horizontalStaircaseLeftWindow_referenceEdge A hL hK ha0 haw hbh)] at h
  exact h

/-- A left virtual relation holding for every exterior configuration is exactly a bond
insertion on the full boundary-indexed blocked tensor.

Source: arXiv:1804.04964, the end-window comparison at lines 2368--2444. -/
theorem leftEnd_regionInsertOfPhysicalOp_eq_bondInserted
    (A : Tensor (torusGraph width height) d)
    (hL : 0 < L) (hK : 0 < K) (ha0 : 1 ≤ a)
    (haw : a + 2 * L ≤ width) (hbh : b + 2 * K - 1 ≤ height)
    (O : Module.End ℂ
      (RegionPhysicalConfig (V := TorusVertex width height) (d := d)
        (horizontalStaircaseLeftWindow ((a : ZMod width), (b : ZMod height)) L K) → ℂ))
    (M : Matrix (Fin (A.bondDim (horizontalStaircaseReferenceEdge
        ((a : ZMod width), (b : ZMod height)) L K)))
      (Fin (A.bondDim (horizontalStaircaseReferenceEdge
        ((a : ZMod width), (b : ZMod height)) L K))) ℂ)
    (hO : ∀ eta : HorizontalStaircaseLeftExternalBoundaryConfig A
        (L := L) (K := K) ((a : ZMod width), (b : ZMod height)),
      IsO1VirtualOperation
        (fun k => regionBlockedWeight (G := torusGraph width height) A
          (horizontalStaircaseLeftWindow ((a : ZMod width), (b : ZMod height)) L K)
          ((horizontalStaircaseLeftWindowBoundaryConfigEquiv A hL hK ha0 haw hbh).symm
            (k, eta))) O M) :
    regionInsertOfPhysicalOp (G := torusGraph width height) A
      (horizontalStaircaseLeftWindow ((a : ZMod width), (b : ZMod height)) L K) O =
    bondInsertedRegionInsert (G := torusGraph width height) A
      (horizontalStaircaseLeftWindow ((a : ZMod width), (b : ZMod height)) L K)
      ⟨_, isRegionBoundaryEdge_horizontalStaircaseLeftWindow_referenceEdge
        A hL hK ha0 haw hbh⟩ M := by
  funext ν
  let E := horizontalStaircaseLeftWindowBoundaryConfigEquiv A hL hK ha0 haw hbh
  let F := regionBoundaryConfigSplitAt (G := torusGraph width height) A
    (horizontalStaircaseLeftWindow ((a : ZMod width), (b : ZMod height)) L K)
    ⟨_, isRegionBoundaryEdge_horizontalStaircaseLeftWindow_referenceEdge A hL hK ha0 haw hbh⟩
  have h := (hO (E ν).2) (E ν).1
  have hconfig (i) : E.symm (i, (E ν).2) = F.symm (i, (F ν).2) := by
    simp only [E, F, horizontalStaircaseLeftWindowBoundaryConfigEquiv,
      regionBoundaryConfigSplitAt, Equiv.symm_trans_apply, Equiv.trans_apply,
      Equiv.prodCongr_symm, Equiv.prodCongr_apply, Equiv.refl_symm,
      Equiv.refl_apply, Prod.map_apply, Prod.map_snd, Equiv.symm_apply_apply]
  simp only [E, Prod.mk.eta, Equiv.symm_apply_apply] at h
  dsimp only [E] at hconfig
  simp_rw [hconfig] at h
  change O (regionBlockedWeight (G := torusGraph width height) A
    (horizontalStaircaseLeftWindow ((a : ZMod width), (b : ZMod height)) L K) ν) =
    ∑ i, M i (F ν).1 • regionBlockedWeight (G := torusGraph width height) A
      (horizontalStaircaseLeftWindow ((a : ZMod width), (b : ZMod height)) L K)
      (F.symm (i, (F ν).2)) at h
  rw [← bondInsertedRegionInsert_splitAt A
    (horizontalStaircaseLeftWindow ((a : ZMod width), (b : ZMod height)) L K)
    ⟨_, isRegionBoundaryEdge_horizontalStaircaseLeftWindow_referenceEdge A hL hK ha0 haw hbh⟩
    M (F ν).1 (F ν).2] at h
  simpa only [F, Prod.mk.eta, Equiv.symm_apply_apply, regionInsertOfPhysicalOp] using h

/-- The canonical left staircase physical operation preserves addition of virtual matrices.

Source: arXiv:1804.04964, the algebra assignment at lines 563--582. -/
theorem staircaseO1PhysicalOp_add (A : Tensor (torusGraph width height) d) {a b : ℕ}
    (hA : NormalTorusArcWindowInjectivityHypotheses L K
      (regionInjectivityDataOf (G := torusGraph width height) A))
    (hL : 0 < L) (hK : 0 < K) (haw : a + 2 * L ≤ width) (hyh : 2 * K ≤ height)
    (X Y : Matrix
      (Fin (A.bondDim (horizontalStaircaseReferenceEdge
        ((a : ZMod width), (b : ZMod height)) L K)))
      (Fin (A.bondDim (horizontalStaircaseReferenceEdge
        ((a : ZMod width), (b : ZMod height)) L K))) ℂ) :
    staircaseO1PhysicalOp A hA hL hK haw hyh (X + Y) =
      staircaseO1PhysicalOp A hA hL hK haw hyh X +
        staircaseO1PhysicalOp A hA hL hK haw hyh Y := by
  unfold staircaseO1PhysicalOp
  rw [← regionPhysicalOperationCongr_add]
  apply congrArg (regionPhysicalOperationCongr
    (staircaseWindow_last ((a : ZMod width), (b : ZMod height)) hL hK))
  simp only [staircaseVirtualOperationPhysicalOp, staircaseVirtualOperationInsert_last]
  rw [bondInsertedRegionInsert_add, physicalOpOfRegionInsert_add]

/-- The canonical left staircase physical operation preserves complex scalar multiplication.

Source: arXiv:1804.04964, the algebra assignment at lines 563--582. -/
theorem staircaseO1PhysicalOp_smul (A : Tensor (torusGraph width height) d) {a b : ℕ}
    (hA : NormalTorusArcWindowInjectivityHypotheses L K
      (regionInjectivityDataOf (G := torusGraph width height) A))
    (hL : 0 < L) (hK : 0 < K) (haw : a + 2 * L ≤ width) (hyh : 2 * K ≤ height)
    (c : ℂ) (X : Matrix
      (Fin (A.bondDim (horizontalStaircaseReferenceEdge
        ((a : ZMod width), (b : ZMod height)) L K)))
      (Fin (A.bondDim (horizontalStaircaseReferenceEdge
        ((a : ZMod width), (b : ZMod height)) L K))) ℂ) :
    staircaseO1PhysicalOp A hA hL hK haw hyh (c • X) =
      c • staircaseO1PhysicalOp A hA hL hK haw hyh X := by
  unfold staircaseO1PhysicalOp
  rw [← regionPhysicalOperationCongr_smul]
  apply congrArg (regionPhysicalOperationCongr
    (staircaseWindow_last ((a : ZMod width), (b : ZMod height)) hL hK))
  rw [staircaseVirtualOperationPhysicalOp, staircaseVirtualOperationPhysicalOp,
    staircaseVirtualOperationInsert_last, staircaseVirtualOperationInsert_last,
    bondInsertedRegionInsert_smul, physicalOpOfRegionInsert_smul]

/-- The canonical cross-tensor virtual assignment is realized on the second tensor by the
first tensor's canonical left physical operation, for every boundary configuration.

Source: arXiv:1804.04964, the assignment at lines 563--582 and 2368--2444. -/
theorem staircaseCrossTensorVirtualOperation_realizes (X) :
    regionInsertOfPhysicalOp B
      (horizontalStaircaseLeftWindow ((a : ZMod width), (b : ZMod height)) L K)
      (staircaseO1PhysicalOp A hA (by omega) (by omega) haw (by omega) X) =
      bondInsertedRegionInsert B
      (horizontalStaircaseLeftWindow ((a : ZMod width), (b : ZMod height)) L K)
      ⟨_, isRegionBoundaryEdge_horizontalStaircaseLeftWindow_referenceEdge
        B (by omega) (by omega) ha0 haw hbh⟩
      (staircaseCrossTensorVirtualOperation A B hA hB hATI hBTI hAB
        hposA hposB hL hK ha0 haw hbh hxw hyh X) := by
  exact leftEnd_regionInsertOfPhysicalOp_eq_bondInserted B
    (by omega) (by omega) ha0 haw hbh _ _
    (staircaseCrossTensorVirtualOperation_spec A B hA hB hATI hBTI hAB
      hposA hposB hL hK ha0 haw hbh hxw hyh X).1

include hA hB hATI hBTI hAB hposA hposB hL hK ha0 haw hbh hxw hyh in
/-- Physical realization transports inserted coefficients with their non-boundary-bond
multiplicities. Equality of these multiplicities is not assumed.

Source: arXiv:1804.04964, the equal-state insertion argument at lines 563--582. -/
theorem staircaseCrossTensorVirtualOperation_normalized_coeff
    (X : Matrix
      (Fin (A.bondDim (horizontalStaircaseReferenceEdge
        ((a : ZMod width), (b : ZMod height)) L K)))
      (Fin (A.bondDim (horizontalStaircaseReferenceEdge
        ((a : ZMod width), (b : ZMod height)) L K))) ℂ)
    (σ : RegionPhysicalConfig (V := TorusVertex width height) (d := d)
      (horizontalStaircaseLeftWindow ((a : ZMod width), (b : ZMod height)) L K))
    (τ : RegionPhysicalConfig (V := TorusVertex width height) (d := d)
      (Finset.univ \ horizontalStaircaseLeftWindow ((a : ZMod width), (b : ZMod height)) L K)) :
    let W := horizontalStaircaseLeftWindow ((a : ZMod width), (b : ZMod height)) L K
    let f : {f : Edge (torusGraph width height) // IsRegionBoundaryEdge W f} :=
      ⟨_, isRegionBoundaryEdge_horizontalStaircaseLeftWindow_referenceEdge A
        (by omega) (by omega) ha0 haw hbh⟩
    (regionInteriorBondProd B W : ℂ) * regionInsertedCoeff A W f X σ τ =
      (regionInteriorBondProd A W : ℂ) * regionInsertedCoeff B W f
        (staircaseCrossTensorVirtualOperation A B hA hB hATI hBTI hAB hposA hposB
          hL hK ha0 haw hbh hxw hyh X) σ τ := by
  have hrealA := staircaseO1PhysicalOp_realizes_insert A hA (by omega) (by omega)
    ha0 haw hbh (by omega) X
  have hrealB := leftEnd_regionInsertOfPhysicalOp_eq_bondInserted B (by omega) (by omega)
    ha0 haw hbh _ _
    (staircaseCrossTensorVirtualOperation_spec A B hA hB hATI hBTI hAB hposA hposB
      hL hK ha0 haw hbh hxw hyh X).1
  have h := deformedRegionState_regionInsertOfPhysicalOp_sameState A B hAB
    (horizontalStaircaseLeftWindow ((a : ZMod width), (b : ZMod height)) L K)
    (staircaseO1PhysicalOp A hA (by omega) (by omega) haw (by omega) X) σ τ
  simpa only [hrealA, hrealB, deformedRegionState_bondInsertedRegionInsert, smul_eq_mul] using h

end StaircaseAlgebra
end TNLean.PEPS
