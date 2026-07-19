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
  Hamiltonians*, arXiv:1105.1019v2, Section IV, source lines 602--606.
-/

open scoped BigOperators Kronecker Matrix

namespace MPSTensor.BeigiSectorGraphData

open FiniteWeightedDigraph

variable {d D : ℕ} {A : MPSTensor d D}

/-- A nonzero vector in the edge ground space carried by a positive loop.

Source: Beigi, arXiv:1105.1019v2, Section IV, source lines 602--606. -/
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

Source: Beigi, arXiv:1105.1019v2, Section IV, source lines 602--606. -/
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

Source: Beigi, arXiv:1105.1019v2, Section IV, source lines 602--606. -/
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

Source: Beigi, arXiv:1105.1019v2, Section IV, source lines 602--606. -/
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

Source: Beigi, arXiv:1105.1019v2, Section IV, source lines 602--606. -/
noncomputable def loopProductState (F : BeigiSectorGraphData A)
    (l : Loop F.edgeWeight) {N : ℕ} [NeZero N] : NSiteSpace d N :=
  fun s ↦ ∑ t : Fin N → Fin d,
    (∏ n : Fin N, F.unitary (s n) (t n)) * F.loopCyclicProduct l t

private theorem edgeProjector_mulVec_loopBondVector
    (F : BeigiSectorGraphData A) (l : Loop F.edgeWeight) :
    (F.edgeProjector l.1 l.1).mulVec (F.loopBondVector l) =
      F.loopBondVector l := by
  have hproj : LinearMap.IsProj (F.edgeGroundSpace l.1 l.1)
      (Matrix.toLin' (F.edgeProjector l.1 l.1)) := by
    rw [edgeGroundSpace, LinearMap.isProj_range_iff_isIdempotentElem]
    change Matrix.toLin' (F.edgeProjector l.1 l.1) *
      Matrix.toLin' (F.edgeProjector l.1 l.1) =
        Matrix.toLin' (F.edgeProjector l.1 l.1)
    rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul,
      (F.edgeProjector_isOrthogonal l.1 l.1).2.eq]
  exact hproj.mem_iff_map_id.mp (F.loopBondVector_mem l)

private theorem piProduct_mulVec_pureTensor
    {N : ℕ} {α : Fin N → Type*} [∀ n, Fintype (α n)]
    (P : (n : Fin N) → Matrix (α n) (α n) ℂ)
    (v : (n : Fin N) → α n → ℂ)
    (hv : ∀ n, (P n).mulVec (v n) = v n)
    (x : (n : Fin N) → α n) :
    Matrix.mulVec
        (fun (x y : (n : Fin N) → α n) ↦ ∏ n, P n (x n) (y n))
        (fun y : (n : Fin N) → α n ↦ ∏ n, v n (y n)) x =
      ∏ n, v n (x n) := by
  classical
  simp only [Matrix.mulVec, dotProduct]
  rw [← Fintype.piFinset_univ]
  simp_rw [← Finset.prod_mul_distrib]
  rw [← Finset.prod_univ_sum
    (fun n : Fin N ↦ (Finset.univ : Finset (α n)))
    (fun n y ↦ P n (x n) y * v n y)]
  apply Finset.prod_congr rfl
  intro n _
  simpa only [Matrix.mulVec, dotProduct] using congrFun (hv n) (x n)

private theorem reindex_mulVec {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) (M : Matrix α α ℂ) (v : α → ℂ) :
    (Matrix.reindex e e M).mulVec (v ∘ e.symm) =
      (M.mulVec v) ∘ e.symm := by
  funext x
  simp only [Matrix.mulVec, dotProduct, Matrix.reindex_apply,
    Function.comp_apply]
  exact Equiv.sum_comp e.symm
    (fun y : α ↦ M (e.symm x) y * v y)

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
      exact piProduct_mulVec_pureTensor
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
  rw [reindex_mulVec] at hfix
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
  have hUstarU : F.unitaryᴴ * F.unitary = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using
      Unitary.star_mul_self_of_mem F.unitary_mem
  have hUUstar : F.unitary * F.unitaryᴴ = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using
      Unitary.mul_star_self_of_mem F.unitary_mem
  have hWWstar : W * Wᴴ = 1 := by
    simp only [W]
    rw [MPOTensor.sitewisePhysicalMatrix_mul_conjTranspose, hUUstar,
      MPOTensor.sitewisePhysicalMatrix_one]
  have hconj : singleKrausMap (MPOTensor.sitewisePhysicalMatrix F.unitaryᴴ N) Q = T := by
    have hprod := MPOTensor.singleKrausMap_bondProduct_of_unitary F.unitaryᴴ
      (by simpa using hUUstar) (by simpa using hUstarU) hN
      (Matrix.reindex (finTwoArrowEquiv (Fin d)).symm
        (finTwoArrowEquiv (Fin d)).symm (twoSiteParentGroundProjectorMatrix A))
    simp_rw [MPOTensor.singleKrausMap_sitewise_conjTranspose_two_eq] at hprod
    have hpair : MPOTensor.pairBondMatrix
        (Matrix.reindex (finTwoArrowEquiv (Fin d)).symm
          (finTwoArrowEquiv (Fin d)).symm
          (twoSiteParentGroundProjectorMatrix A)) =
        twoSiteParentGroundProjectorMatrix A := by
      ext x y
      simp [MPOTensor.pairBondMatrix, Matrix.reindex_apply]
    rw [hpair] at hprod
    simpa only [Q, T] using hprod
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

Source: Beigi, arXiv:1105.1019v2, Section III, source lines 487--500, and
Section IV, source lines 602--606. -/
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

Source: Beigi, arXiv:1105.1019v2, Section III, source lines 487--500, and
Section IV, source lines 602--606. -/
theorem loopProductState_mem_parentHamiltonianGroundSpaceES
    (F : BeigiSectorGraphData A) (l : Loop F.edgeWeight)
    {N : ℕ} (hN : 2 ≤ N) :
    letI : NeZero N := ⟨by omega⟩
    (WithLp.linearEquiv 2 ℂ (NSiteSpace d N)).symm (F.loopProductState l) ∈
      parentHamiltonianGroundSpaceES A 2 N := by
  letI : NeZero N := ⟨by omega⟩
  rw [parentHamiltonianGroundSpaceES, Submodule.mem_map]
  exact ⟨F.loopProductState l, F.loopProductState_mem_ker_parentHamiltonian l hN, rfl⟩

/-- The sector-coordinate loop tensor closes to the cyclic product of loop
bond vectors at every positive length.

Source: Beigi, arXiv:1105.1019v2, Section IV, source lines 602--606. -/
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

Source: Beigi, arXiv:1105.1019v2, Section IV, source lines 602--606. -/
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
