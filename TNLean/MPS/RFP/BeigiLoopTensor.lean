/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Core.CyclicTrace
import TNLean.MPS.Periodic.Applications
import TNLean.MPS.RFP.BeigiEventuallyConstantSectorGraph

/-!
# Matrix product tensors associated with Beigi loops

For a positive loop in Beigi's sector graph, choose a nonzero vector in the
corresponding edge ground space.  Its components couple the right factor at
one site to the left factor at the next site.  This cyclic product is a
translation-invariant matrix product vector: the virtual index is the left
factor of the loop sector, and the local matrix has entries
\[
  A^{(r,l)}_{a,b}=\delta_{a,l}\,\varphi(r,b).
\]
The one-site unitary in the spatial decomposition then transports this tensor
back to the original physical coordinates.

This is the product-of-pairs state in Beigi's construction.  It is distinct
from a product over disjoint pairs of physical sites.

## References

* S. Beigi, *Classification of the phases of 1D spin chains with commuting
  Hamiltonians*, J. Phys. A 45 (2012) 025306, Section IV.
-/

open scoped BigOperators Kronecker Matrix

namespace MPSTensor.BeigiSectorGraphData

open FiniteWeightedDigraph

variable {d D : ℕ} {A : MPSTensor d D}

/-- A nonzero vector in the edge ground space carried by a positive loop.

Source: Beigi, J. Phys. A 45 (2012) 025306, Section IV. -/
noncomputable def loopBondVector (F : BeigiSectorGraphData A)
    (l : Loop F.edgeWeight) :
    Matrix.EtaEdgeIndex F.leftDim F.rightDim l.1 l.1 → ℂ :=
  Classical.choose <| Submodule.exists_mem_ne_zero_of_ne_bot <|
    (F.isEdge_iff_edgeWeight_ne_zero l.1 l.1).2 l.2

/-- The chosen loop vector belongs to its edge ground space. -/
theorem loopBondVector_mem (F : BeigiSectorGraphData A)
    (l : Loop F.edgeWeight) :
    F.loopBondVector l ∈ F.edgeGroundSpace l.1 l.1 :=
  (Classical.choose_spec <| Submodule.exists_mem_ne_zero_of_ne_bot <|
    (F.isEdge_iff_edgeWeight_ne_zero l.1 l.1).2 l.2).1

/-- The chosen loop vector is nonzero. -/
theorem loopBondVector_ne_zero (F : BeigiSectorGraphData A)
    (l : Loop F.edgeWeight) :
    F.loopBondVector l ≠ 0 :=
  (Classical.choose_spec <| Submodule.exists_mem_ne_zero_of_ne_bot <|
    (F.isEdge_iff_edgeWeight_ne_zero l.1 l.1).2 l.2).2

/-- The sector-coordinate tensor associated with a positive loop.

For a physical coordinate in the loop sector, the row index records the local
left factor and the column index is contracted with the next site's left
factor.  The matrix entry is the corresponding component of the loop bond
vector.  Coordinates in every other sector give the zero matrix.

Source: Beigi, J. Phys. A 45 (2012) 025306, Section IV. -/
noncomputable def loopCoordinateTensor (F : BeigiSectorGraphData A)
    (l : Loop F.edgeWeight) : MPSTensor d (F.leftDim l.1) :=
  fun i a b ↦
    if hq : (F.sectorEquiv.symm i).1 = l.1 then
      if a = Fin.cast (congrArg F.leftDim hq) (F.sectorEquiv.symm i).2.2 then
        F.loopBondVector l
          (Fin.cast (congrArg F.rightDim hq) (F.sectorEquiv.symm i).2.1, b)
      else 0
    else 0

/-- The physical loop tensor obtained by applying the spatial-decomposition
unitary to the sector-coordinate tensor.

Source: Beigi, J. Phys. A 45 (2012) 025306, Section IV. -/
noncomputable def loopTensor (F : BeigiSectorGraphData A)
    (l : Loop F.edgeWeight) : MPSTensor d (F.leftDim l.1) :=
  rotatePhysical F.unitary (F.loopCoordinateTensor l)

/-- The left sector factor at site `n`, transported to the loop sector using
the hypothesis that the physical index at that site belongs to the loop. -/
private def loopLeftIndex (F : BeigiSectorGraphData A)
    (l : Loop F.edgeWeight) {N : ℕ} (s : Fin N → Fin d)
    (hsector : ∀ n, (F.sectorEquiv.symm (s n)).1 = l.1) (n : Fin N) :
    Fin (F.leftDim l.1) :=
  Fin.cast (congrArg F.leftDim (hsector n))
    (F.sectorEquiv.symm (s n)).2.2

/-- The right sector factor at site `n`, transported to the loop sector using
the hypothesis that the physical index at that site belongs to the loop. -/
private def loopRightIndex (F : BeigiSectorGraphData A)
    (l : Loop F.edgeWeight) {N : ℕ} (s : Fin N → Fin d)
    (hsector : ∀ n, (F.sectorEquiv.symm (s n)).1 = l.1) (n : Fin N) :
    Fin (F.rightDim l.1) :=
  Fin.cast (congrArg F.rightDim (hsector n))
    (F.sectorEquiv.symm (s n)).2.1

/-- The cyclic product of copies of the loop bond vector in sector coordinates.

The right factor at site `n` is paired with the left factor at site `n + 1`.
The value is zero unless every site belongs to the chosen loop sector.

Source: Beigi, J. Phys. A 45 (2012) 025306, Section IV. -/
noncomputable def loopCyclicProduct (F : BeigiSectorGraphData A)
    (l : Loop F.edgeWeight) {N : ℕ} [NeZero N]
    (s : Fin N → Fin d) : ℂ :=
  if hsector : ∀ n, (F.sectorEquiv.symm (s n)).1 = l.1 then
    ∏ n : Fin N, F.loopBondVector l
      (F.loopRightIndex l s hsector n, F.loopLeftIndex l s hsector (n + 1))
  else 0

/-- The physical product-of-pairs state associated with a positive loop.

It is the sitewise unitary image of the cyclic product whose bonds join the
right factor at site `n` to the left factor at site `n + 1`.

Source: Beigi, J. Phys. A 45 (2012) 025306, Section IV. -/
noncomputable def loopProductState (F : BeigiSectorGraphData A)
    (l : Loop F.edgeWeight) {N : ℕ} [NeZero N] : NSiteSpace d N :=
  fun s ↦ ∑ t : Fin N → Fin d,
    (∏ n : Fin N, F.unitary (s n) (t n)) * F.loopCyclicProduct l t

/-- The Euclidean-space realization of a positive-loop product state.

Source: Beigi, J. Phys. A 45 (2012) 025306, Section IV. -/
noncomputable def loopProductStateES (F : BeigiSectorGraphData A)
    (l : Loop F.edgeWeight) {N : ℕ} [NeZero N] :
    EuclideanSpace ℂ (Fin N → Fin d) :=
  (WithLp.linearEquiv 2 ℂ (NSiteSpace d N)).symm (F.loopProductState l)

private theorem edgeProjector_mulVec_loopBondVector
    (F : BeigiSectorGraphData A) (l : Loop F.edgeWeight) :
    (F.edgeProjector l.1 l.1).mulVec (F.loopBondVector l) =
      F.loopBondVector l := by
  exact (F.edgeProjector_isProj l.1 l.1).mem_iff_map_id.mp
    (F.loopBondVector_mem l)

private theorem loopCyclicProduct_etaCyclicEdgeEquiv_symm_constant
    (F : BeigiSectorGraphData A) (l : Loop F.edgeWeight)
    {N : ℕ} [NeZero N]
    (x : (n : Fin N) → Matrix.EtaEdgeIndex F.leftDim F.rightDim l.1 l.1) :
    F.loopCyclicProduct l
        ((Matrix.etaCyclicEdgeEquiv F.leftDim F.rightDim F.sectorEquiv).symm
          ⟨fun _ ↦ l.1, x⟩) =
      ∏ n : Fin N, F.loopBondVector l (x n) := by
  classical
  unfold loopCyclicProduct
  have hsector : ∀ n : Fin N,
      (F.sectorEquiv.symm
        ((Matrix.etaCyclicEdgeEquiv F.leftDim F.rightDim F.sectorEquiv).symm
          ⟨fun _ ↦ l.1, x⟩ n)).1 = l.1 := by
    intro n
    rw [Matrix.etaCyclicEdgeEquiv_symm_apply]
    simp
  rw [dif_pos hsector]
  have hsite (m : Fin N) :
      F.sectorEquiv.symm
          ((Matrix.etaCyclicEdgeEquiv F.leftDim F.rightDim F.sectorEquiv).symm
            ⟨fun _ ↦ l.1, x⟩ m) =
        ⟨l.1,
          (Matrix.etaFixedSectorCyclicEdgeEquiv F.leftDim F.rightDim
            (fun _ : Fin N ↦ l.1)).symm x m⟩ := by
    rw [Matrix.etaCyclicEdgeEquiv_symm_apply]
    exact Equiv.symm_apply_apply F.sectorEquiv _
  apply Finset.prod_congr rfl
  intro n _
  congr 1
  apply Prod.ext
  · apply Fin.ext
    simp only [loopRightIndex, Fin.val_cast]
    have h := congrArg (fun z ↦ z.2.1.val) (hsite n)
    exact h
  · apply Fin.ext
    simp only [loopLeftIndex, Fin.val_cast]
    have h := congrArg (fun z ↦ z.2.2.val) (hsite (n + 1))
    have hedge := Matrix.etaFixedSectorCyclicEdgeEquiv_symm_edge
      F.leftDim F.rightDim (fun _ : Fin N ↦ l.1) x n
    exact h.trans (congrArg (fun z ↦ z.2.val) hedge)

private theorem loopCyclicProduct_etaCyclicEdgeEquiv_symm_of_ne
    (F : BeigiSectorGraphData A) (l : Loop F.edgeWeight)
    {N : ℕ} [NeZero N] (k : Fin N → Fin F.sectorCount)
    (hk : k ≠ fun _ ↦ l.1)
    (x : (n : Fin N) →
      Matrix.EtaEdgeIndex F.leftDim F.rightDim (k n) (k (n + 1))) :
    F.loopCyclicProduct l
        ((Matrix.etaCyclicEdgeEquiv F.leftDim F.rightDim F.sectorEquiv).symm
          ⟨k, x⟩) = 0 := by
  unfold loopCyclicProduct
  rw [dif_neg]
  intro hsector
  apply hk
  funext n
  have hsite :
      F.sectorEquiv.symm
          ((Matrix.etaCyclicEdgeEquiv F.leftDim F.rightDim F.sectorEquiv).symm
            ⟨k, x⟩ n) =
        ⟨k n,
          (Matrix.etaFixedSectorCyclicEdgeEquiv F.leftDim F.rightDim k).symm x n⟩ := by
    rw [Matrix.etaCyclicEdgeEquiv_symm_apply]
    exact Equiv.symm_apply_apply F.sectorEquiv _
  exact (congrArg Sigma.fst hsite).symm.trans (hsector n)

/-- The cyclic product belonging to a positive loop is nonzero at every
positive chain length.

Source: Beigi, J. Phys. A 45 (2012) 025306, Section IV. -/
theorem loopCyclicProduct_ne_zero (F : BeigiSectorGraphData A)
    (l : Loop F.edgeWeight) {N : ℕ} [NeZero N] :
    F.loopCyclicProduct l ≠ (0 : NSiteSpace d N) := by
  classical
  have hexists : ∃ q, F.loopBondVector l q ≠ 0 := by
    by_contra h
    push Not at h
    apply F.loopBondVector_ne_zero l
    funext q
    exact h q
  obtain ⟨q, hq⟩ := hexists
  let x : (n : Fin N) →
      Matrix.EtaEdgeIndex F.leftDim F.rightDim l.1 l.1 := fun _ ↦ q
  intro hzero
  have hvalue := congrFun hzero
    ((Matrix.etaCyclicEdgeEquiv F.leftDim F.rightDim F.sectorEquiv).symm
      ⟨fun _ ↦ l.1, x⟩)
  rw [F.loopCyclicProduct_etaCyclicEdgeEquiv_symm_constant l x] at hvalue
  have hprod : ∏ n : Fin N, F.loopBondVector l (x n) ≠ 0 := by
    exact Finset.prod_ne_zero_iff.mpr fun n _ ↦ by simpa only [x] using hq
  exact hprod hvalue

/-- Cyclic products belonging to distinct positive loops have disjoint sector
support and hence zero inner product.

Source: Beigi, J. Phys. A 45 (2012) 025306, Section IV. -/
theorem loopCyclicProduct_inner_eq_zero_of_ne
    (F : BeigiSectorGraphData A) {l m : Loop F.edgeWeight}
    {N : ℕ} [NeZero N] (hlm : l ≠ m) :
    inner ℂ (WithLp.toLp 2 (F.loopCyclicProduct (N := N) l))
      (WithLp.toLp 2 (F.loopCyclicProduct (N := N) m)) = 0 := by
  classical
  rw [EuclideanSpace.inner_toLp_toLp, dotProduct]
  apply Finset.sum_eq_zero
  intro s _
  by_cases hl : ∀ n, (F.sectorEquiv.symm (s n)).1 = l.1
  · have hm : ¬ ∀ n, (F.sectorEquiv.symm (s n)).1 = m.1 := by
      intro hm
      apply hlm
      apply Subtype.ext
      exact (hl 0).symm.trans (hm 0)
    have hmzero : F.loopCyclicProduct m s = 0 := by
      unfold loopCyclicProduct
      rw [dif_neg hm]
    rw [hmzero, zero_mul]
  · have hlzero : F.loopCyclicProduct l s = 0 := by
      unfold loopCyclicProduct
      rw [dif_neg hl]
    rw [Pi.star_apply, hlzero, star_zero, mul_zero]

private theorem blockGroundProduct_mulVec_loopCyclicProduct
    (F : BeigiSectorGraphData A) (l : Loop F.edgeWeight)
    {N : ℕ} [NeZero N] :
    (Matrix.blockDiagonal' fun k : Fin N → Fin F.sectorCount ↦
        fun (x y : (n : Fin N) → Matrix.EtaEdgeIndex F.leftDim F.rightDim
          (k n) (k (n + 1))) ↦ ∏ n : Fin N,
          F.edgeProjector (k n) (k (n + 1)) (x n) (y n)).mulVec
        (fun z ↦ F.loopCyclicProduct l
          ((Matrix.etaCyclicEdgeEquiv F.leftDim F.rightDim F.sectorEquiv).symm z)) =
      fun z ↦ F.loopCyclicProduct l
        ((Matrix.etaCyclicEdgeEquiv F.leftDim F.rightDim F.sectorEquiv).symm z) := by
  classical
  let B : (k : Fin N → Fin F.sectorCount) →
      Matrix ((n : Fin N) → Matrix.EtaEdgeIndex F.leftDim F.rightDim
        (k n) (k (n + 1)))
        ((n : Fin N) → Matrix.EtaEdgeIndex F.leftDim F.rightDim
          (k n) (k (n + 1))) ℂ :=
    fun k x y ↦ ∏ n : Fin N,
      F.edgeProjector (k n) (k (n + 1)) (x n) (y n)
  change (Matrix.blockDiagonal' B).mulVec
      (fun z ↦ F.loopCyclicProduct l
        ((Matrix.etaCyclicEdgeEquiv F.leftDim F.rightDim F.sectorEquiv).symm z)) = _
  funext z
  obtain ⟨k, x⟩ := z
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_sigma]
  rw [Finset.sum_eq_single k]
  · have hdiag (y : (n : Fin N) → Matrix.EtaEdgeIndex F.leftDim F.rightDim
        (k n) (k (n + 1))) :
        Matrix.blockDiagonal' B ⟨k, x⟩ ⟨k, y⟩ = B k x y := by
      exact Matrix.blockDiagonal'_apply_eq B k x y
    simp_rw [hdiag]
    simp only [B]
    by_cases hk : k = fun _ ↦ l.1
    · subst k
      simp_rw [F.loopCyclicProduct_etaCyclicEdgeEquiv_symm_constant l]
      exact Matrix.piProduct_mulVec_pureTensor_of_mulVec_eq_self
        (fun _ : Fin N ↦ F.edgeProjector l.1 l.1)
        (fun _ : Fin N ↦ F.loopBondVector l)
        (fun _ ↦ F.edgeProjector_mulVec_loopBondVector l) x
    · simp_rw [F.loopCyclicProduct_etaCyclicEdgeEquiv_symm_of_ne l k hk]
      simp
  · intro h _ hne
    apply Finset.sum_eq_zero
    intro y _
    have hoff : Matrix.blockDiagonal' B ⟨k, x⟩ ⟨h, y⟩ = 0 := by
      exact Matrix.blockDiagonal'_apply_ne B x y (Ne.symm hne)
    rw [hoff, zero_mul]
  · exact fun h ↦ absurd (Finset.mem_univ k) h

private theorem transformedGroundBondProduct_mulVec_loopCyclicProduct
    (F : BeigiSectorGraphData A) (l : Loop F.edgeWeight)
    {N : ℕ} [NeZero N] (hN : 2 ≤ N) :
    ((List.ofFn fun i : Fin N ↦
      MPOTensor.embedLocalOperator (d := d) 2 N hN i
        (Matrix.reindex (finTwoArrowEquiv (Fin d)).symm
          (finTwoArrowEquiv (Fin d)).symm
          (star (F.unitary ⊗ₖ F.unitary) *
            twoSiteParentGroundProjectorMatrix A *
              (F.unitary ⊗ₖ F.unitary)))).prod).mulVec
        (F.loopCyclicProduct l) = F.loopCyclicProduct l := by
  classical
  let e := Matrix.etaCyclicEdgeEquiv (N := N)
    F.leftDim F.rightDim F.sectorEquiv
  let T := (List.ofFn fun i : Fin N ↦
    MPOTensor.embedLocalOperator (d := d) 2 N hN i
      (Matrix.reindex (finTwoArrowEquiv (Fin d)).symm
        (finTwoArrowEquiv (Fin d)).symm
        (star (F.unitary ⊗ₖ F.unitary) *
          twoSiteParentGroundProjectorMatrix A *
            (F.unitary ⊗ₖ F.unitary)))).prod
  have hblocks : Matrix.reindex e e T =
      Matrix.blockDiagonal' fun k : Fin N → Fin F.sectorCount ↦
        fun (x y : (n : Fin N) → Matrix.EtaEdgeIndex F.leftDim F.rightDim
          (k n) (k (n + 1))) ↦ ∏ n : Fin N,
            F.edgeProjector (k n) (k (n + 1)) (x n) (y n) := by
    exact MPOTensor.reindex_product_embedLocalOperator_of_etaPair_decomposition
      hN F.leftDim F.rightDim F.sectorEquiv F.edgeProjector
      (star (F.unitary ⊗ₖ F.unitary) *
        twoSiteParentGroundProjectorMatrix A * (F.unitary ⊗ₖ F.unitary))
      F.groundProjector_block
  have hfix : (Matrix.reindex e e T).mulVec
      (F.loopCyclicProduct l ∘ e.symm) = F.loopCyclicProduct l ∘ e.symm := by
    rw [hblocks]
    exact F.blockGroundProduct_mulVec_loopCyclicProduct l
  rw [Matrix.reindex_mulVec] at hfix
  funext s
  have hs := congrFun hfix (e s)
  simpa only [Function.comp_apply, Equiv.symm_apply_apply] using hs

private theorem loopProductState_eq_sitewisePhysicalMatrix_mulVec
    (F : BeigiSectorGraphData A) (l : Loop F.edgeWeight)
    {N : ℕ} [NeZero N] :
    F.loopProductState l =
      (MPOTensor.sitewisePhysicalMatrix F.unitary N).mulVec
        (F.loopCyclicProduct l) := by
  rfl

/-- A positive-loop product state is nonzero at every positive chain length.

Source: Beigi, J. Phys. A 45 (2012) 025306, Section IV. -/
theorem loopProductState_ne_zero (F : BeigiSectorGraphData A)
    (l : Loop F.edgeWeight) {N : ℕ} [NeZero N] :
    F.loopProductState (N := N) l ≠ 0 := by
  classical
  let W := MPOTensor.sitewisePhysicalMatrix F.unitary N
  have hWstarW : Wᴴ * W = 1 := by
    apply MPOTensor.sitewisePhysicalMatrix_isometry
    simpa only [Matrix.star_eq_conjTranspose] using
      Unitary.star_mul_self_of_mem F.unitary_mem
  rw [F.loopProductState_eq_sitewisePhysicalMatrix_mulVec l]
  intro hzero
  apply F.loopCyclicProduct_ne_zero (N := N) l
  have hzero' := congrArg (fun v ↦ Wᴴ *ᵥ v) hzero
  simp only [Matrix.mulVec_zero] at hzero'
  change Wᴴ *ᵥ W *ᵥ F.loopCyclicProduct (N := N) l = 0 at hzero'
  rw [Matrix.mulVec_mulVec, hWstarW, Matrix.one_mulVec] at hzero'
  exact hzero'

/-- The Euclidean realization of a positive-loop product state is nonzero at
every positive chain length.

Source: Beigi, J. Phys. A 45 (2012) 025306, Section IV. -/
theorem loopProductStateES_ne_zero (F : BeigiSectorGraphData A)
    (l : Loop F.edgeWeight) {N : ℕ} [NeZero N] :
    F.loopProductStateES (N := N) l ≠ 0 := by
  exact (WithLp.linearEquiv 2 ℂ (NSiteSpace d N)).symm.injective.ne
    (F.loopProductState_ne_zero l)

/-- Euclidean positive-loop product states belonging to distinct loops are
orthogonal at every positive chain length.

Source: Beigi, J. Phys. A 45 (2012) 025306, Section IV. -/
theorem loopProductStateES_inner_eq_zero_of_ne
    (F : BeigiSectorGraphData A) {l m : Loop F.edgeWeight}
    {N : ℕ} [NeZero N] (hlm : l ≠ m) :
    inner ℂ (F.loopProductStateES (N := N) l)
      (F.loopProductStateES (N := N) m) = 0 := by
  classical
  let W := MPOTensor.sitewisePhysicalMatrix F.unitary N
  have hWstarW : Wᴴ * W = 1 := by
    apply MPOTensor.sitewisePhysicalMatrix_isometry
    simpa only [Matrix.star_eq_conjTranspose] using
      Unitary.star_mul_self_of_mem F.unitary_mem
  rw [loopProductStateES, loopProductStateES]
  change inner ℂ (WithLp.toLp 2 (F.loopProductState l))
    (WithLp.toLp 2 (F.loopProductState m)) = 0
  rw [F.loopProductState_eq_sitewisePhysicalMatrix_mulVec l,
    F.loopProductState_eq_sitewisePhysicalMatrix_mulVec m]
  change inner ℂ (WithLp.toLp 2 (W *ᵥ F.loopCyclicProduct l))
    (WithLp.toLp 2 (W *ᵥ F.loopCyclicProduct m)) = 0
  rw [EuclideanSpace.inner_toLp_toLp, dotProduct_comm, Matrix.star_mulVec,
    ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, hWstarW,
    Matrix.one_mulVec, dotProduct_comm]
  exact F.loopCyclicProduct_inner_eq_zero_of_ne hlm

/-- The Euclidean positive-loop product states are linearly independent at
every positive chain length.

Source: Beigi, J. Phys. A 45 (2012) 025306, Section IV. -/
theorem loopProductStateES_linearIndependent
    (F : BeigiSectorGraphData A) {N : ℕ} [NeZero N] :
    LinearIndependent ℂ
      (fun l : Loop F.edgeWeight ↦ F.loopProductStateES (N := N) l) := by
  apply linearIndependent_of_ne_zero_of_inner_eq_zero
  · intro l
    exact F.loopProductStateES_ne_zero l
  · intro l m hlm
    exact F.loopProductStateES_inner_eq_zero_of_ne hlm

private theorem groundBondProduct_mulVec_loopProductState
    (F : BeigiSectorGraphData A) (l : Loop F.edgeWeight)
    {N : ℕ} [NeZero N] (hN : 2 ≤ N) :
    ((List.ofFn fun i : Fin N ↦
      MPOTensor.embedLocalOperator (d := d) 2 N hN i
        (Matrix.reindex (finTwoArrowEquiv (Fin d)).symm
          (finTwoArrowEquiv (Fin d)).symm
          (twoSiteParentGroundProjectorMatrix A))).prod).mulVec
        (F.loopProductState l) = F.loopProductState l := by
  classical
  let W := MPOTensor.sitewisePhysicalMatrix F.unitary N
  let Q := (List.ofFn fun i : Fin N ↦
    MPOTensor.embedLocalOperator (d := d) 2 N hN i
      (Matrix.reindex (finTwoArrowEquiv (Fin d)).symm
        (finTwoArrowEquiv (Fin d)).symm
        (twoSiteParentGroundProjectorMatrix A))).prod
  let T := (List.ofFn fun i : Fin N ↦
    MPOTensor.embedLocalOperator (d := d) 2 N hN i
      (Matrix.reindex (finTwoArrowEquiv (Fin d)).symm
        (finTwoArrowEquiv (Fin d)).symm
        (star (F.unitary ⊗ₖ F.unitary) *
          twoSiteParentGroundProjectorMatrix A *
            (F.unitary ⊗ₖ F.unitary)))).prod
  have hUUstar := F.unitary_mul_conjTranspose
  have hWWstar : W * Wᴴ = 1 := by
    simp only [W]
    rw [MPOTensor.sitewisePhysicalMatrix_mul_conjTranspose, hUUstar,
      MPOTensor.sitewisePhysicalMatrix_one]
  have hconj : singleKrausMap (MPOTensor.sitewisePhysicalMatrix F.unitaryᴴ N) Q = T := by
    simpa only [Q, T] using F.singleKrausMap_groundBondProduct hN
  have hmatrix : Q * W = W * T := by
    have hconj' : Wᴴ * Q * W = T := by
      simpa only [singleKrausMap_apply,
        MPOTensor.sitewisePhysicalMatrix_conjTranspose,
        Matrix.conjTranspose_conjTranspose, W] using hconj
    calc
      Q * W = 1 * (Q * W) := by rw [Matrix.one_mul]
      _ = (W * Wᴴ) * (Q * W) := by rw [hWWstar]
      _ = W * (Wᴴ * Q * W) := by simp only [Matrix.mul_assoc]
      _ = W * T := by rw [hconj']
  rw [F.loopProductState_eq_sitewisePhysicalMatrix_mulVec l]
  change Q.mulVec (W.mulVec (F.loopCyclicProduct l)) =
    W.mulVec (F.loopCyclicProduct l)
  rw [Matrix.mulVec_mulVec, hmatrix, ← Matrix.mulVec_mulVec,
    F.transformedGroundBondProduct_mulVec_loopCyclicProduct l hN]

/-- The product-of-pairs state associated with a positive Beigi loop has zero
energy for the finite two-site parent Hamiltonian.

This is the membership part of Beigi's ground-space description: it does not
assert that the loop states span the ground space.

**Scope restriction (chain length):** The theorem treats `N ≥ 2`, the
nondegenerate range of the two-site periodic parent Hamiltonian used here.
The length-one convention is recorded in
`docs/paper-gaps/cpsv16_nncph_ground_state_scope.tex`.

Source: Beigi, J. Phys. A 45 (2012) 025306, Sections III--IV. -/
theorem loopProductState_mem_ker_parentHamiltonian
    (F : BeigiSectorGraphData A) (l : Loop F.edgeWeight)
    {N : ℕ} (hN : 2 ≤ N) :
    letI : NeZero N := ⟨by omega⟩
    F.loopProductState l ∈ LinearMap.ker (parentHamiltonian A 2 N) := by
  letI : NeZero N := ⟨by omega⟩
  exact F.mem_ker_parentHamiltonian_of_groundBondProduct_mulVec_eq_self hN
    (F.loopProductState l) (F.groundBondProduct_mulVec_loopProductState l hN)

/-- In the Euclidean-space realization, every positive-loop product state
belongs to the finite parent-Hamiltonian ground space.

This theorem proves membership only; the assertion that these states span the
ground space is a separate part of Beigi's argument.

**Scope restriction (chain length):** The theorem treats `N ≥ 2`, the
nondegenerate range of the two-site periodic parent Hamiltonian used here.
The length-one convention is recorded in
`docs/paper-gaps/cpsv16_nncph_ground_state_scope.tex`.

Source: Beigi, J. Phys. A 45 (2012) 025306, Sections III--IV. -/
theorem loopProductState_mem_parentHamiltonianGroundSpaceES
    (F : BeigiSectorGraphData A) (l : Loop F.edgeWeight)
    {N : ℕ} (hN : 2 ≤ N) :
    letI : NeZero N := ⟨by omega⟩
    F.loopProductStateES l ∈ parentHamiltonianGroundSpaceES A 2 N := by
  letI : NeZero N := ⟨by omega⟩
  rw [loopProductStateES, parentHamiltonianGroundSpaceES, Submodule.mem_map]
  exact ⟨F.loopProductState l, F.loopProductState_mem_ker_parentHamiltonian l hN, rfl⟩

private theorem span_loopProductStateES_eq_parentHamiltonianGroundSpaceES_of_finrank_eq
    (F : BeigiSectorGraphData A) {N : ℕ} (hN : 2 < N)
    (hfinrank : Module.finrank ℂ (parentHamiltonianGroundSpaceES A 2 N) =
      Fintype.card (Loop F.edgeWeight)) :
    letI : NeZero N := ⟨by omega⟩
    Submodule.span ℂ
      (Set.range (fun l : Loop F.edgeWeight ↦ F.loopProductStateES l)) =
      parentHamiltonianGroundSpaceES A 2 N := by
  letI : NeZero N := ⟨by omega⟩
  apply Submodule.eq_of_le_of_finrank_eq
  · rw [Submodule.span_le]
    rintro _ ⟨l, rfl⟩
    change F.loopProductStateES l ∈ parentHamiltonianGroundSpaceES A 2 N
    exact F.loopProductState_mem_parentHamiltonianGroundSpaceES l (by omega)
  · calc
      Module.finrank ℂ (Submodule.span ℂ
          (Set.range (fun l : Loop F.edgeWeight ↦ F.loopProductStateES l))) =
          Fintype.card (Loop F.edgeWeight) :=
        finrank_span_eq_card F.loopProductStateES_linearIndependent
      _ = Module.finrank ℂ (parentHamiltonianGroundSpaceES A 2 N) := hfinrank.symm

/-- If the parent-ground-space dimension is eventually constant, then at every
length greater than two the positive-loop product states span the whole parent
ground space.

**Scope restriction (chain length):** The theorem treats $N > 2$, the range
covered by the ordered-cycle ground-space dimension formula used here.  The
short-chain conventions are recorded in
`docs/paper-gaps/cpsv16_nncph_ground_state_scope.tex`.

Source: Beigi, J. Phys. A 45 (2012) 025306, Sections III--IV. -/
theorem span_loopProductStateES_eq_parentHamiltonianGroundSpaceES
    (F : BeigiSectorGraphData A)
    (hparent : ∃ c N₀ : ℕ, ∀ M : ℕ, N₀ < M →
      Module.finrank ℂ (parentHamiltonianGroundSpaceES A 2 M) = c)
    {N : ℕ} (hN : 2 < N) :
    letI : NeZero N := ⟨by omega⟩
    Submodule.span ℂ
      (Set.range (fun l : Loop F.edgeWeight ↦ F.loopProductStateES l)) =
      parentHamiltonianGroundSpaceES A 2 N := by
  exact F.span_loopProductStateES_eq_parentHamiltonianGroundSpaceES_of_finrank_eq hN
    (F.parentHamiltonianGroundSpaceES_finrank_eq_card_loop hparent hN)

/-- In the BNT nearest-neighbor setting, positive-loop product states span the
whole parent ground space at every length greater than two.

**Scope restriction (chain length):** The theorem treats $N > 2$, the range
covered by the ordered-cycle ground-space dimension formula used here.  The
short-chain conventions are recorded in
`docs/paper-gaps/cpsv16_nncph_ground_state_scope.tex`.

Source: CPSV16, Definition 3.9 and Theorem 3.10, source lines 517--540;
Beigi, J. Phys. A 45 (2012) 025306, Sections III--IV. -/
theorem span_loopProductStateES_eq_parentHamiltonianGroundSpaceES_of_hasBNTSectorData
    {P : SectorDecomposition d} (F : BeigiSectorGraphData P.toTensor)
    (hBNT : HasBNTSectorData P)
    (hNNCPH : HasNNCPHGroundSpaces P.toTensor P.basis)
    {N : ℕ} (hN : 2 < N) :
    letI : NeZero N := ⟨by omega⟩
    Submodule.span ℂ
      (Set.range (fun l : Loop F.edgeWeight ↦ F.loopProductStateES l)) =
      parentHamiltonianGroundSpaceES P.toTensor 2 N := by
  exact F.span_loopProductStateES_eq_parentHamiltonianGroundSpaceES_of_finrank_eq hN
    (F.parentHamiltonianGroundSpaceES_finrank_eq_card_loop_of_hasBNTSectorData
      hBNT hNNCPH hN)

/-- The sector-coordinate loop tensor closes to the cyclic product of loop
bond vectors at every positive length.

Source: Beigi, J. Phys. A 45 (2012) 025306, Section IV. -/
theorem mpv_loopCoordinateTensor (F : BeigiSectorGraphData A)
    (l : Loop F.edgeWeight) {N : ℕ} [NeZero N] (s : Fin N → Fin d) :
    mpv (F.loopCoordinateTensor l) s = F.loopCyclicProduct l s := by
  classical
  rw [mpv, coeff, trace_evalWord_eq_sum_cyclic]
  unfold loopCyclicProduct
  by_cases hsector : ∀ n, (F.sectorEquiv.symm (s n)).1 = l.1
  · rw [dif_pos hsector]
    let g : Fin N → Fin (F.leftDim l.1) := F.loopLeftIndex l s hsector
    rw [Finset.sum_eq_single g]
    · apply Finset.prod_congr rfl
      intro n _
      simp only [loopCoordinateTensor, hsector n, ↓reduceDIte, g]
      rw [if_pos (by rfl)]
      simp only [loopRightIndex]
    · intro b _ hb
      have hdiff : ∃ n, b n ≠ g n := by
        by_contra h
        apply hb
        funext n
        exact not_ne_iff.mp (not_exists.mp h n)
      obtain ⟨n, hn⟩ := hdiff
      rw [Finset.prod_eq_zero (Finset.mem_univ n)]
      simp only [loopCoordinateTensor, hsector n, ↓reduceDIte]
      rw [if_neg (by simpa only [g, loopLeftIndex] using hn)]
    · simp
  · rw [dif_neg hsector]
    apply Finset.sum_eq_zero
    intro g _
    simp only [not_forall] at hsector
    obtain ⟨n, hn⟩ := hsector
    rw [Finset.prod_eq_zero (Finset.mem_univ n)]
    simp only [loopCoordinateTensor, hn, ↓reduceDIte]

/-- The periodic matrix product vector of `loopTensor` is exactly Beigi's
physical product-of-pairs state at every positive chain length.

Source: Beigi, J. Phys. A 45 (2012) 025306, Section IV. -/
theorem mpv_loopTensor (F : BeigiSectorGraphData A)
    (l : Loop F.edgeWeight) {N : ℕ} [NeZero N] (s : Fin N → Fin d) :
    mpv (F.loopTensor l) s = F.loopProductState l s := by
  rw [loopTensor, MPSTensor.mpv_rotatePhysical]
  simp only [loopProductState]
  apply Finset.sum_congr rfl
  intro t _
  congr 1
  exact F.mpv_loopCoordinateTensor l t

end MPSTensor.BeigiSectorGraphData
