/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.CommutingBondEtaCyclicTransport
import TNLean.MPS.ParentHamiltonian.KernelChainGroundSpace
import TNLean.MPS.RFP.BeigiSpatialDecomposition
import TNLean.Algebra.CommutingProjectionProduct

/-!
# The finite sector graph of a commuting parent Hamiltonian

Beigi's spatial decomposition writes the one-site space as a finite direct sum
of left--right tensor factors.  In these coordinates, the complementary
two-site parent interaction is a direct sum of operators
`1 ⊗ P_{a,b} ⊗ 1`, where `P_{a,b}` is the orthogonal projector onto the
ground space carried by the directed edge from `a` to `b`.

The product of all translated complementary interactions is therefore block
diagonal over ordered cyclic sector sequences.  Its trace is the sum, over
those sequences, of the products of the edge-ground-space dimensions.  Since
this product is the ground-space projector of the commuting parent
Hamiltonian, its trace gives Beigi's ordered-cycle formula.

## Main declarations

* `BeigiSectorGraphData`: the finite local sector data and its two-site
  coordinate identity;
* `BeigiSectorGraphData.OrderedCycle`: ordered cyclic sector sequences whose
  adjacent edge ground spaces are nonzero;
* `BeigiSectorGraphData.singleKrausMap_groundBondProduct`: spatial conjugation
  of the complete complementary-interaction product;
* `BeigiSectorGraphData.mem_ker_parentHamiltonian_of_groundBondProduct_mulVec_eq_self`:
  its fixed vectors have zero parent-Hamiltonian energy;
* `BeigiSectorGraphData.parentHamiltonianGroundSpaceES_finrank_eq`: Beigi's
  finite-chain dimension formula.

## References

* S. Beigi, *Classification of the phases of 1D spin chains with commuting
  Hamiltonians*, arXiv:1105.1019v2, Section III, equations (2)--(4), pages
  3--4.
-/

open scoped BigOperators ComplexOrder Kronecker Matrix

namespace MPSTensor

variable {d D : ℕ}

/-- The two-site projector onto the canonical parent ground space, in ordered
pair coordinates.  It is the complement of the canonical parent interaction.

Source: Beigi, arXiv:1105.1019v2, Section III, equation (2), page 3. -/
noncomputable def twoSiteParentGroundProjectorMatrix (A : MPSTensor d D) :
    Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  1 - twoSiteParentInteractionMatrix A

/-- The finite sector graph associated with a spatial decomposition of the
canonical two-site parent interaction.

The edge projector `edgeProjector a b` has range `ker Q_{a,b}` in Beigi's
notation.  The only compatibility field is the local coordinate identity for
the complementary bond `1 - h`; no finite-chain ground-space statement or
scale-invariance hypothesis is part of the data.

Source: Beigi, arXiv:1105.1019v2, Section III, equations (2)--(3), pages 3--4. -/
structure BeigiSectorGraphData (A : MPSTensor d D) where
  /-- The number of sectors in the one-site spatial decomposition.

  Source: Beigi, arXiv:1105.1019v2, Section III, equation (2), page 3. -/
  sectorCount : ℕ
  /-- The dimension of the left factor in each sector.

  Source: Beigi, arXiv:1105.1019v2, Section III, equation (2), page 3. -/
  leftDim : Fin sectorCount → ℕ
  /-- The dimension of the right factor in each sector.

  Source: Beigi, arXiv:1105.1019v2, Section III, equation (2), page 3. -/
  rightDim : Fin sectorCount → ℕ
  /-- Identification of one physical site with its finite sum of right--left
  sector factors.

  Source: Beigi, arXiv:1105.1019v2, Section III, equation (2), page 3. -/
  sectorEquiv : Matrix.EtaSiteIndex sectorCount leftDim rightDim ≃ Fin d
  /-- The one-site unitary implementing the spatial coordinates.

  Source: Beigi, arXiv:1105.1019v2, Section III, equation (2), page 3. -/
  unitary : Matrix (Fin d) (Fin d) ℂ
  /-- The spatial coordinate change is unitary.

  Source: Beigi, arXiv:1105.1019v2, Section III, equation (2), page 3. -/
  unitary_mem : unitary ∈ Matrix.unitaryGroup (Fin d) ℂ
  /-- The projector onto the ground space carried by the directed edge
  `a ⟶ b`.

  Source: Beigi, arXiv:1105.1019v2, Section III, equations (2)--(3), pages 3--4. -/
  edgeProjector : (a b : Fin sectorCount) →
    Matrix (Matrix.EtaEdgeIndex leftDim rightDim a b)
      (Matrix.EtaEdgeIndex leftDim rightDim a b) ℂ
  /-- Every edge ground-space operator is an orthogonal projector.

  Source: Beigi, arXiv:1105.1019v2, Section III, equations (2)--(3), pages 3--4. -/
  edgeProjector_isOrthogonal : ∀ a b,
    (edgeProjector a b).IsHermitian ∧ IsIdempotentElem (edgeProjector a b)
  /-- In spatial coordinates, the complementary parent interaction is the
  direct sum of the edge ground-space projectors, with identities on the two
  boundary factors.

  Source: Beigi, arXiv:1105.1019v2, Section III, equation (2), page 3. -/
  groundProjector_block :
    Matrix.reindex (Matrix.etaPairSpatialBlockEquiv sectorEquiv).symm
        (Matrix.etaPairSpatialBlockEquiv sectorEquiv).symm
        (star (unitary ⊗ₖ unitary) * twoSiteParentGroundProjectorMatrix A *
          (unitary ⊗ₖ unitary)) =
      Matrix.blockDiagonal' fun ab : Fin sectorCount × Fin sectorCount ↦
        ((1 : Matrix (Fin (leftDim ab.1)) (Fin (leftDim ab.1)) ℂ) ⊗ₖ
          edgeProjector ab.1 ab.2) ⊗ₖ
            (1 : Matrix (Fin (rightDim ab.2)) (Fin (rightDim ab.2)) ℂ)

namespace BeigiSectorGraphData

variable {A : MPSTensor d D}

/-- The edge ground space from sector `a` to sector `b`.

This is `ker Q_{a,b}` in Beigi's notation, represented as the range of its
orthogonal projector `P_{a,b}`.

Source: Beigi, arXiv:1105.1019v2, Section III, equation (3), page 4. -/
noncomputable def edgeGroundSpace (F : BeigiSectorGraphData A)
    (a b : Fin F.sectorCount) :
    Submodule ℂ (Matrix.EtaEdgeIndex F.leftDim F.rightDim a b → ℂ) :=
  LinearMap.range (Matrix.toLin' (F.edgeProjector a b))

/-- The edge projector is a projection onto its edge ground space.

Source: Beigi, arXiv:1105.1019v2, Section III, equations (2)--(3), pages 3--4. -/
theorem edgeProjector_isProj (F : BeigiSectorGraphData A)
    (a b : Fin F.sectorCount) :
    LinearMap.IsProj (F.edgeGroundSpace a b)
      (Matrix.toLin' (F.edgeProjector a b)) := by
  rw [edgeGroundSpace, LinearMap.isProj_range_iff_isIdempotentElem]
  change Matrix.toLin' (F.edgeProjector a b) *
    Matrix.toLin' (F.edgeProjector a b) = Matrix.toLin' (F.edgeProjector a b)
  rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul,
    (F.edgeProjector_isOrthogonal a b).2.eq]

/-- The spatial coordinate matrix is right-unitary.

Source: Beigi, arXiv:1105.1019v2, Section III, equation (2), page 3. -/
theorem unitary_mul_conjTranspose (F : BeigiSectorGraphData A) :
    F.unitary * F.unitaryᴴ = 1 := by
  simpa only [Matrix.star_eq_conjTranspose] using
    Unitary.mul_star_self_of_mem F.unitary_mem

/-- A directed edge is present exactly when its edge ground space is nonzero.

Source: Beigi, arXiv:1105.1019v2, Section III, graph definition immediately
after equation (2), page 3. -/
def IsEdge (F : BeigiSectorGraphData A) (a b : Fin F.sectorCount) : Prop :=
  F.edgeGroundSpace a b ≠ ⊥

/-- An ordered cyclic sector sequence all of whose adjacent edge ground spaces
are nonzero.  Cyclic rotation is not quotiented out: the source sum is over
ordered cycles.

Source: Beigi, arXiv:1105.1019v2, Section III, equations (3)--(4), page 4. -/
def OrderedCycle (F : BeigiSectorGraphData A) (N : ℕ) [NeZero N] :=
  {k : Fin N → Fin F.sectorCount // ∀ n : Fin N, F.IsEdge (k n) (k (n + 1))}

noncomputable instance (F : BeigiSectorGraphData A) (N : ℕ) [NeZero N] :
    Fintype (F.OrderedCycle N) := by
  classical
  unfold OrderedCycle
  infer_instance

noncomputable instance (F : BeigiSectorGraphData A) (N : ℕ) [NeZero N] :
    DecidableEq (F.OrderedCycle N) :=
  Classical.decEq _

/-- The complementary two-site bond in configuration coordinates. -/
private noncomputable def groundBond (A : MPSTensor d D) :
    Matrix (Fin 2 → Fin d) (Fin 2 → Fin d) ℂ :=
  Matrix.reindex (finTwoArrowEquiv (Fin d)).symm
    (finTwoArrowEquiv (Fin d)).symm (twoSiteParentGroundProjectorMatrix A)

/-- The coordinate-transformed complementary two-site bond. -/
private noncomputable def transformedGroundBond (F : BeigiSectorGraphData A) :
    Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  star (F.unitary ⊗ₖ F.unitary) * twoSiteParentGroundProjectorMatrix A *
    (F.unitary ⊗ₖ F.unitary)

private theorem transformedGroundBond_block (F : BeigiSectorGraphData A) :
    Matrix.reindex (Matrix.etaPairSpatialBlockEquiv F.sectorEquiv).symm
        (Matrix.etaPairSpatialBlockEquiv F.sectorEquiv).symm
        F.transformedGroundBond =
      Matrix.blockDiagonal' fun ab : Fin F.sectorCount × Fin F.sectorCount ↦
        ((1 : Matrix (Fin (F.leftDim ab.1)) (Fin (F.leftDim ab.1)) ℂ) ⊗ₖ
          F.edgeProjector ab.1 ab.2) ⊗ₖ
            (1 : Matrix (Fin (F.rightDim ab.2)) (Fin (F.rightDim ab.2)) ℂ) :=
  F.groundProjector_block

private theorem localTerm_eq_toLin'_embedLocalOperator {N : ℕ} (hN : 2 ≤ N)
    (i : Fin N) :
    localTerm A 2 N i = Matrix.toLin'
      (MPOTensor.embedLocalOperator (d := d) 2 N hN i
        (LinearMap.toMatrix' (parentInteraction A 2))) := by
  classical
  apply LinearMap.ext
  intro v
  funext σ
  rw [localTerm_apply_of_le A 2 N hN i, Matrix.toLin'_apply,
    MPOTensor.embedLocalOperator_mulVec_apply]
  symm
  exact congrFun (LinearMap.congr_fun
    (Matrix.toLin'_toMatrix' (parentInteraction A 2))
    (fun τ ↦ v (replaceWindow 2 hN i σ τ))) (extractWindow 2 i σ)

private theorem groundBond_eq_one_sub_toMatrix' :
    groundBond A = 1 - LinearMap.toMatrix' (parentInteraction A 2) := by
  classical
  ext x y
  simp only [groundBond, twoSiteParentGroundProjectorMatrix,
    twoSiteParentInteractionMatrix, Matrix.reindex_apply,
    finTwoArrowEquiv_symm_apply, Equiv.symm_symm, finTwoArrowEquiv_apply,
    Equiv.toFun_as_coe, piFinTwoEquiv_apply, Fin.isValue, Matrix.submatrix_apply,
    Matrix.sub_apply, Matrix.one_apply, Prod.mk.injEq, LinearMap.toMatrix'_apply]
  · have hx : ![x 0, x 1] = x := by
      funext j
      fin_cases j <;> rfl
    have hy : ![y 0, y 1] = y := by
      funext j
      fin_cases j <;> rfl
    rw [hx, hy]
    have hxy : (x 0 = y 0 ∧ x 1 = y 1) ↔ x = y := by
      constructor
      · rintro ⟨h0, h1⟩
        funext j
        fin_cases j
        · exact h0
        · exact h1
      · rintro rfl
        exact ⟨rfl, rfl⟩
    simp only [hxy]

private theorem embedLocalOperator_groundBond_eq_one_sub {N : ℕ} (hN : 2 ≤ N)
    (i : Fin N) :
    MPOTensor.embedLocalOperator (d := d) 2 N hN i (groundBond A) =
      1 - MPOTensor.embedLocalOperator (d := d) 2 N hN i
        (LinearMap.toMatrix' (parentInteraction A 2)) := by
  classical
  rw [groundBond_eq_one_sub_toMatrix']
  ext σ τ
  by_cases hστ : MPOTensor.AgreesOutsideWindow (d := d) 2 hN i σ τ
  · simp only [MPOTensor.embedLocalOperator_apply, hστ, if_true,
      Matrix.sub_apply, Matrix.one_apply]
    by_cases hEq : σ = τ
    · subst τ
      simp
    · have hExtract : extractWindow 2 i σ ≠ extractWindow 2 i τ := by
        intro h
        apply hEq
        rw [← replaceWindow_extractWindow 2 hN i τ]
        rw [← h, hστ]
      simp [hEq, hExtract]
  · have hne : σ ≠ τ := by
      intro hEq
      subst τ
      exact hστ (by simp [MPOTensor.AgreesOutsideWindow])
    simp [MPOTensor.embedLocalOperator_apply, hστ, hne]

private theorem singleKrausMap_groundBond_eq_transformedGroundBond
    (F : BeigiSectorGraphData A) :
    singleKrausMap (MPOTensor.sitewisePhysicalMatrix F.unitaryᴴ 2) (groundBond A) =
      Matrix.reindex (finTwoArrowEquiv (Fin d)).symm
        (finTwoArrowEquiv (Fin d)).symm F.transformedGroundBond := by
  rw [MPOTensor.singleKrausMap_sitewise_conjTranspose_two_eq]
  congr 1

/-- Conjugating the product of complementary two-site parent interactions by
the sitewise spatial unitary gives the corresponding product in sector
coordinates.

Source: Beigi, arXiv:1105.1019v2, Section III, equation (2), page 3. -/
theorem singleKrausMap_groundBondProduct (F : BeigiSectorGraphData A)
    {N : ℕ} [NeZero N] (hN : 2 ≤ N) :
    singleKrausMap (MPOTensor.sitewisePhysicalMatrix F.unitaryᴴ N)
        ((List.ofFn fun i : Fin N ↦
          MPOTensor.embedLocalOperator (d := d) 2 N hN i
            (Matrix.reindex (finTwoArrowEquiv (Fin d)).symm
              (finTwoArrowEquiv (Fin d)).symm
              (twoSiteParentGroundProjectorMatrix A))).prod) =
      (List.ofFn fun i : Fin N ↦
        MPOTensor.embedLocalOperator (d := d) 2 N hN i
          (Matrix.reindex (finTwoArrowEquiv (Fin d)).symm
            (finTwoArrowEquiv (Fin d)).symm
            (star (F.unitary ⊗ₖ F.unitary) *
              twoSiteParentGroundProjectorMatrix A *
                (F.unitary ⊗ₖ F.unitary)))).prod := by
  have hUstarU : F.unitaryᴴ * F.unitary = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using
      Unitary.star_mul_self_of_mem F.unitary_mem
  have hUUstar := F.unitary_mul_conjTranspose
  have hprod := MPOTensor.singleKrausMap_bondProduct_of_unitary F.unitaryᴴ
    (by simpa using hUUstar) (by simpa using hUstarU) hN (groundBond A)
  simp_rw [singleKrausMap_groundBond_eq_transformedGroundBond] at hprod
  simpa only [groundBond, transformedGroundBond] using hprod

private theorem groundBondEmbeddings_commute (F : BeigiSectorGraphData A)
    {N : ℕ} [NeZero N] (hN : 2 ≤ N) (i j : Fin N) :
    Commute
      (MPOTensor.embedLocalOperator (d := d) 2 N hN i (groundBond A))
      (MPOTensor.embedLocalOperator (d := d) 2 N hN j (groundBond A)) := by
  classical
  let W := MPOTensor.sitewisePhysicalMatrix F.unitaryᴴ N
  let G : Fin N → Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ := fun n ↦
    MPOTensor.embedLocalOperator (d := d) 2 N hN n (groundBond A)
  let T : Fin N → Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ := fun n ↦
    MPOTensor.embedLocalOperator (d := d) 2 N hN n
      (Matrix.reindex (finTwoArrowEquiv (Fin d)).symm
        (finTwoArrowEquiv (Fin d)).symm F.transformedGroundBond)
  have hUstarU : star F.unitary * F.unitary = 1 :=
    Unitary.star_mul_self_of_mem F.unitary_mem
  have hUstarU' : F.unitaryᴴ * F.unitary = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using hUstarU
  have hUUstar' := F.unitary_mul_conjTranspose
  have hWstarW : Wᴴ * W = 1 := by
    simp only [W, MPOTensor.sitewisePhysicalMatrix_conjTranspose,
      Matrix.conjTranspose_conjTranspose]
    rw [← MPOTensor.sitewisePhysicalMatrix_conjTranspose,
      MPOTensor.sitewisePhysicalMatrix_mul_conjTranspose, hUUstar',
      MPOTensor.sitewisePhysicalMatrix_one]
  have hWWstar : W * Wᴴ = 1 := by
    simp only [W]
    rw [MPOTensor.sitewisePhysicalMatrix_mul_conjTranspose]
    simp only [Matrix.conjTranspose_conjTranspose]
    rw [hUstarU', MPOTensor.sitewisePhysicalMatrix_one]
  have hWone : singleKrausMap W 1 = 1 := by
    simp only [singleKrausMap_apply, Matrix.mul_one]
    exact hWWstar
  have hconj (n : Fin N) : singleKrausMap W (G n) = T n := by
    simp only [G, T]
    rw [MPOTensor.singleKrausMap_embedLocalOperator_eq_range_mul_lift
      F.unitaryᴴ (by simpa using hUUstar') hN n,
      singleKrausMap_groundBond_eq_transformedGroundBond]
    rw [show singleKrausMap
      (MPOTensor.sitewisePhysicalMatrix F.unitaryᴴ N) 1 = 1 by exact hWone]
    exact Matrix.one_mul _
  have hT : Commute (T i) (T j) := by
    exact MPOTensor.embedLocalOperator_commute_of_etaPair_decomposition hN
      F.leftDim F.rightDim F.sectorEquiv F.edgeProjector F.transformedGroundBond
      F.transformedGroundBond_block i j
  rw [← hconj i, ← hconj j] at hT
  have hback := congrArg (singleKrausMap Wᴴ) hT.eq
  simp only [singleKrausMap_apply, Matrix.conjTranspose_conjTranspose] at hback
  simp only [← Matrix.mul_assoc, hWstarW, Matrix.one_mul] at hback
  simp only [Matrix.mul_assoc, hWstarW, Matrix.mul_one] at hback
  simp only [G] at hback
  exact hback

private theorem localTerm_commute (F : BeigiSectorGraphData A)
    {N : ℕ} [NeZero N] (hN : 2 ≤ N) (i j : Fin N) :
    Commute (localTerm A 2 N i) (localTerm A 2 N j) := by
  classical
  let G : Fin N → Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ := fun n ↦
    MPOTensor.embedLocalOperator (d := d) 2 N hN n (groundBond A)
  have hG : Commute (G i) (G j) := F.groundBondEmbeddings_commute hN i j
  have htoLin (n : Fin N) :
      Matrix.toLin' (G n) = 1 - localTerm A 2 N n := by
    simp only [G]
    rw [embedLocalOperator_groundBond_eq_one_sub]
    change (Matrix.toLinAlgEquiv' :
      Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ ≃ₐ[ℂ]
        Module.End ℂ (NSiteSpace d N))
        (1 - MPOTensor.embedLocalOperator (d := d) 2 N hN n
          (LinearMap.toMatrix' (parentInteraction A 2))) = _
    rw [map_sub, map_one]
    change 1 - Matrix.toLin'
      (MPOTensor.embedLocalOperator (d := d) 2 N hN n
        (LinearMap.toMatrix' (parentInteraction A 2))) = _
    rw [localTerm_eq_toLin'_embedLocalOperator (A := A) hN n]
  have hcomp : Commute
      (1 - localTerm A 2 N i) (1 - localTerm A 2 N j) := by
    rw [← htoLin i, ← htoLin j]
    exact hG.map Matrix.toLinAlgEquiv'
  change localTerm A 2 N i * localTerm A 2 N j =
    localTerm A 2 N j * localTerm A 2 N i
  change (1 - localTerm A 2 N i) * (1 - localTerm A 2 N j) =
    (1 - localTerm A 2 N j) * (1 - localTerm A 2 N i) at hcomp
  simp only [sub_mul, mul_sub, one_mul, mul_one] at hcomp
  abel_nf at hcomp
  exact add_left_cancel (add_left_cancel (add_left_cancel hcomp))

private theorem localTermES_commute (F : BeigiSectorGraphData A)
    {N : ℕ} [NeZero N] (hN : 2 ≤ N) (i j : Fin N) :
    Commute (localTermES A 2 i) (localTermES A 2 j) := by
  let e := WithLp.linearEquiv 2 ℂ (NSiteSpace d N)
  have hraw := F.localTerm_commute hN i j
  have hmap := hraw.map (LinearEquiv.conjAlgEquiv ℂ e.symm)
  simpa only [localTermES, e, LinearEquiv.conjAlgEquiv_apply,
    LinearEquiv.symm_symm] using hmap

private theorem edgeProjector_trace (F : BeigiSectorGraphData A)
    (a b : Fin F.sectorCount) :
    Matrix.trace (F.edgeProjector a b) =
      (Module.finrank ℂ (F.edgeGroundSpace a b) : ℂ) := by
  classical
  rw [← Matrix.trace_toLin'_eq]
  exact (F.edgeProjector_isProj a b).trace

private theorem transformedGroundBondProduct_trace (F : BeigiSectorGraphData A)
    {N : ℕ} [NeZero N] (hN : 2 ≤ N) :
    Matrix.trace
        (List.ofFn fun i : Fin N ↦
          MPOTensor.embedLocalOperator (d := d) 2 N hN i
            (Matrix.reindex (finTwoArrowEquiv (Fin d)).symm
              (finTwoArrowEquiv (Fin d)).symm F.transformedGroundBond)).prod =
      ∑ k : Fin N → Fin F.sectorCount,
        (↑(∏ n : Fin N,
          Module.finrank ℂ (F.edgeGroundSpace (k n) (k (n + 1)))) : ℂ) := by
  classical
  let e := Matrix.etaCyclicEdgeEquiv (N := N) F.leftDim F.rightDim F.sectorEquiv
  let edgeBlock (k : Fin N → Fin F.sectorCount) :
      Matrix ((n : Fin N) → Matrix.EtaEdgeIndex F.leftDim F.rightDim (k n) (k (n + 1)))
        ((n : Fin N) → Matrix.EtaEdgeIndex F.leftDim F.rightDim (k n) (k (n + 1))) ℂ :=
    fun x y ↦ ∏ n : Fin N,
      F.edgeProjector (k n) (k (n + 1)) (x n) (y n)
  have hblocks : Matrix.reindex e e
      (List.ofFn fun i : Fin N ↦
        MPOTensor.embedLocalOperator (d := d) 2 N hN i
          (Matrix.reindex (finTwoArrowEquiv (Fin d)).symm
            (finTwoArrowEquiv (Fin d)).symm F.transformedGroundBond)).prod =
      Matrix.blockDiagonal' edgeBlock :=
    MPOTensor.reindex_product_embedLocalOperator_of_etaPair_decomposition
      hN F.leftDim F.rightDim F.sectorEquiv F.edgeProjector F.transformedGroundBond
      F.transformedGroundBond_block
  calc
    Matrix.trace
        (List.ofFn fun i : Fin N ↦
          MPOTensor.embedLocalOperator (d := d) 2 N hN i
            (Matrix.reindex (finTwoArrowEquiv (Fin d)).symm
              (finTwoArrowEquiv (Fin d)).symm F.transformedGroundBond)).prod =
        Matrix.trace (Matrix.reindex e e
          (List.ofFn fun i : Fin N ↦
            MPOTensor.embedLocalOperator (d := d) 2 N hN i
              (Matrix.reindex (finTwoArrowEquiv (Fin d)).symm
                (finTwoArrowEquiv (Fin d)).symm F.transformedGroundBond)).prod) := by
          exact (Matrix.trace_reindex e _).symm
    _ = Matrix.trace (Matrix.blockDiagonal' edgeBlock) := by
          rw [hblocks]
    _ = _ := by
      rw [Matrix.trace_blockDiagonal']
      apply Finset.sum_congr rfl
      intro k _
      simp only [edgeBlock]
      rw [Matrix.trace_piProduct]
      simp_rw [F.edgeProjector_trace]
      norm_cast

private theorem groundBondProduct_trace (F : BeigiSectorGraphData A)
    {N : ℕ} [NeZero N] (hN : 2 ≤ N) :
    Matrix.trace
        (List.ofFn fun i : Fin N ↦
          MPOTensor.embedLocalOperator (d := d) 2 N hN i (groundBond A)).prod =
      ∑ k : Fin N → Fin F.sectorCount,
        (↑(∏ n : Fin N,
          Module.finrank ℂ (F.edgeGroundSpace (k n) (k (n + 1)))) : ℂ) := by
  classical
  let W := MPOTensor.sitewisePhysicalMatrix F.unitaryᴴ N
  let Q := (List.ofFn fun i : Fin N ↦
    MPOTensor.embedLocalOperator (d := d) 2 N hN i (groundBond A)).prod
  have hUUstar := F.unitary_mul_conjTranspose
  have hWstarW : Wᴴ * W = 1 := by
    simp only [W, MPOTensor.sitewisePhysicalMatrix_conjTranspose,
      Matrix.conjTranspose_conjTranspose]
    rw [← MPOTensor.sitewisePhysicalMatrix_conjTranspose,
      MPOTensor.sitewisePhysicalMatrix_mul_conjTranspose, hUUstar,
      MPOTensor.sitewisePhysicalMatrix_one]
  have hprod := F.singleKrausMap_groundBondProduct hN
  have htrace := F.transformedGroundBondProduct_trace hN
  have hconj : singleKrausMap W Q =
      (List.ofFn fun i : Fin N ↦
        MPOTensor.embedLocalOperator (d := d) 2 N hN i
          (Matrix.reindex (finTwoArrowEquiv (Fin d)).symm
            (finTwoArrowEquiv (Fin d)).symm F.transformedGroundBond)).prod := by
    simpa only [W, Q, groundBond, transformedGroundBond] using hprod
  calc
    Matrix.trace Q = Matrix.trace (singleKrausMap W Q) := by
      simp only [singleKrausMap_apply]
      symm
      rw [Matrix.trace_mul_comm (W * Q) Wᴴ, ← Matrix.mul_assoc, hWstarW,
        Matrix.one_mul]
    _ = _ := by rw [hconj]; exact htrace

private theorem toLin'_groundBondProduct {N : ℕ} [NeZero N] (hN : 2 ≤ N) :
    Matrix.toLin' ((List.ofFn fun i : Fin N ↦
      MPOTensor.embedLocalOperator (d := d) 2 N hN i (groundBond A)).prod) =
      (List.ofFn fun i : Fin N ↦ 1 - localTerm A 2 N i).prod := by
  classical
  have hfactor (i : Fin N) : Matrix.toLin'
      (MPOTensor.embedLocalOperator (d := d) 2 N hN i (groundBond A)) =
      1 - localTerm A 2 N i := by
    rw [embedLocalOperator_groundBond_eq_one_sub]
    change (Matrix.toLinAlgEquiv' :
      Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ ≃ₐ[ℂ]
        Module.End ℂ (NSiteSpace d N))
        (1 - MPOTensor.embedLocalOperator (d := d) 2 N hN i
          (LinearMap.toMatrix' (parentInteraction A 2))) = _
    rw [map_sub, map_one]
    change 1 - Matrix.toLin'
      (MPOTensor.embedLocalOperator (d := d) 2 N hN i
        (LinearMap.toMatrix' (parentInteraction A 2))) = _
    rw [localTerm_eq_toLin'_embedLocalOperator (A := A) hN i]
  change (Matrix.toLinAlgEquiv' :
    Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ ≃ₐ[ℂ]
      Module.End ℂ (NSiteSpace d N)) _ = _
  rw [map_list_prod, List.map_ofFn]
  apply congrArg List.prod
  apply congrArg List.ofFn
  funext i
  exact hfactor i

private theorem conj_localComplementProduct {N : ℕ} :
    (LinearEquiv.conjAlgEquiv ℂ
      (WithLp.linearEquiv 2 ℂ (NSiteSpace d N)).symm)
        (List.ofFn fun i : Fin N ↦ 1 - localTerm A 2 N i).prod =
      (List.ofFn fun i : Fin N ↦ 1 - localTermES A 2 i).prod := by
  rw [map_list_prod, List.map_ofFn]
  apply congrArg List.prod
  apply congrArg List.ofFn
  funext i
  simp only [Function.comp_apply, map_sub, map_one, localTermES,
    LinearEquiv.conjAlgEquiv_apply, LinearEquiv.symm_symm]

/-- The three realizations of the complete complementary-interaction product,
together with the canonical identifications between them. -/
private structure ComplementProductTransport (A : MPSTensor d D)
    (N : ℕ) [NeZero N] (hN : 2 ≤ N) where
  qMatrix : Matrix (Cfg d N) (Cfg d N) ℂ
  qRaw : Module.End ℂ (NSiteSpace d N)
  qES : Module.End ℂ (EuclideanSpace ℂ (Cfg d N))
  e : EuclideanSpace ℂ (Cfg d N) ≃ₗ[ℂ] NSiteSpace d N
  hMatrix : Matrix.toLin' qMatrix = qRaw
  hES : (LinearEquiv.conjAlgEquiv ℂ e.symm) qRaw = qES

/-- The canonical matrix, raw-linear, and Euclidean transport witness for the
complete complementary-interaction product. -/
private noncomputable def complementProductTransport (A : MPSTensor d D)
    {N : ℕ} [NeZero N] (hN : 2 ≤ N) :
    ComplementProductTransport A N hN where
  qMatrix := (List.ofFn fun i : Fin N ↦
    MPOTensor.embedLocalOperator (d := d) 2 N hN i (groundBond A)).prod
  qRaw := (List.ofFn fun i : Fin N ↦ 1 - localTerm A 2 N i).prod
  qES := (List.ofFn fun i : Fin N ↦ 1 - localTermES A 2 i).prod
  e := WithLp.linearEquiv 2 ℂ (NSiteSpace d N)
  hMatrix := toLin'_groundBondProduct (A := A) hN
  hES := conj_localComplementProduct (A := A) (N := N)

private theorem localComplementProductES_trace (F : BeigiSectorGraphData A)
    {N : ℕ} [NeZero N] (hN : 2 ≤ N) :
    LinearMap.trace ℂ (EuclideanSpace ℂ (Cfg d N))
        (List.ofFn fun i : Fin N ↦ 1 - localTermES A 2 i).prod =
      ∑ k : Fin N → Fin F.sectorCount,
        (↑(∏ n : Fin N,
          Module.finrank ℂ (F.edgeGroundSpace (k n) (k (n + 1)))) : ℂ) := by
  classical
  let transport := complementProductTransport A hN
  change LinearMap.trace ℂ (EuclideanSpace ℂ (Cfg d N)) transport.qES = _
  calc
    LinearMap.trace ℂ (EuclideanSpace ℂ (Cfg d N)) transport.qES =
        LinearMap.trace ℂ (NSiteSpace d N) transport.qRaw := by
          rw [← transport.hES]
          exact LinearMap.trace_conj' transport.qRaw transport.e.symm
    _ = Matrix.trace transport.qMatrix := by
      rw [← transport.hMatrix, Matrix.trace_toLin'_eq]
    _ = _ := by
      simpa only [transport, complementProductTransport] using
        F.groundBondProduct_trace hN

private theorem parentHamiltonianGroundSpaceES_finrank_eq_all_sequences
    (F : BeigiSectorGraphData A) {N : ℕ} [NeZero N] (hN : 2 ≤ N) :
    Module.finrank ℂ (parentHamiltonianGroundSpaceES A 2 N) =
      ∑ k : Fin N → Fin F.sectorCount,
        ∏ n : Fin N, Module.finrank ℂ (F.edgeGroundSpace (k n) (k (n + 1))) := by
  classical
  have hproj := LinearMap.isProj_ker_sum_listProd_one_sub
    (fun i : Fin N ↦ localTermES A 2 i)
    (fun i ↦ localTermES_isSymmetricProjection A 2 i)
    (fun i j ↦ F.localTermES_commute hN i j)
  rw [← parentHamiltonianES_eq_sum_localTermES] at hproj
  have htrace := hproj.trace
  rw [F.localComplementProductES_trace hN] at htrace
  norm_cast at htrace
  rw [parentHamiltonianGroundSpaceES_eq_ker_parentHamiltonianES]
  exact htrace.symm

/-- A vector fixed by the complete product of complementary two-site parent
interactions belongs to the kernel of the finite parent Hamiltonian.

For sector data of Beigi type, the translated parent interactions commute, so
the product of their complements is the projector onto the common kernel.

**Scope restriction (sector data):** This criterion is stated under
`BeigiSectorGraphData A`, which supplies the commutativity of the translated
parent interactions.  This restricted auxiliary form, and its possible
generalization to an explicit commutativity hypothesis, are recorded in
`docs/paper-gaps/cpsv16_nncph_ground_state_scope.tex`.

Source: Beigi, arXiv:1105.1019v2, Section III, source lines 487--500. -/
theorem mem_ker_parentHamiltonian_of_groundBondProduct_mulVec_eq_self
    (F : BeigiSectorGraphData A) {N : ℕ} [NeZero N] (hN : 2 ≤ N)
    (v : NSiteSpace d N)
    (hv : ((List.ofFn fun i : Fin N ↦
      MPOTensor.embedLocalOperator (d := d) 2 N hN i
        (Matrix.reindex (finTwoArrowEquiv (Fin d)).symm
          (finTwoArrowEquiv (Fin d)).symm
          (twoSiteParentGroundProjectorMatrix A))).prod).mulVec v = v) :
    v ∈ LinearMap.ker (parentHamiltonian A 2 N) := by
  classical
  let transport := complementProductTransport A hN
  have hraw : transport.qRaw v = v := by
    rw [← transport.hMatrix, Matrix.toLin'_apply]
    exact hv
  have hfixES : transport.qES (transport.e.symm v) = transport.e.symm v := by
    rw [← transport.hES]
    simp only [LinearEquiv.conjAlgEquiv_apply]
    change transport.e.symm
      (transport.qRaw (transport.e (transport.e.symm v))) = transport.e.symm v
    rw [transport.e.apply_symm_apply, hraw]
  have hproj := LinearMap.isProj_ker_sum_listProd_one_sub
    (fun i : Fin N ↦ localTermES A 2 i)
    (fun i ↦ localTermES_isSymmetricProjection A 2 i)
    (fun i j ↦ F.localTermES_commute hN i j)
  rw [← parentHamiltonianES_eq_sum_localTermES] at hproj
  have hkerES : transport.e.symm v ∈
      LinearMap.ker (parentHamiltonianES A 2 N) :=
    hproj.mem_iff_map_id.mpr hfixES
  rw [LinearMap.mem_ker] at hkerES ⊢
  have h := congrArg transport.e hkerES
  simpa [parentHamiltonianES, transport, complementProductTransport] using h

/-- Beigi's finite-chain ground-space dimension formula: for a periodic chain
of length at least two, the dimension is the sum over ordered cyclic
sector sequences of the products of the adjacent edge-ground-space
dimensions.

**Scope restriction (chain length):** Beigi's equations (3)--(4) apply to all
periodic lengths, whereas this theorem treats `2 ≤ N`; the one-site periodic
interaction convention remains open. Documented in
`docs/paper-gaps/cpsv16_nncph_ground_state_scope.tex`.

Source: Beigi, arXiv:1105.1019v2, Section III, equations (2)--(4), source
lines 451--512. -/
theorem parentHamiltonianGroundSpaceES_finrank_eq
    (F : BeigiSectorGraphData A) {N : ℕ} (hN : 2 ≤ N) :
    letI : NeZero N := ⟨by omega⟩
    Module.finrank ℂ (parentHamiltonianGroundSpaceES A 2 N) =
      ∑ c : F.OrderedCycle N,
        ∏ n : Fin N,
          Module.finrank ℂ (F.edgeGroundSpace (c.1 n) (c.1 (n + 1))) := by
  classical
  letI : NeZero N := ⟨by omega⟩
  let weight : (Fin N → Fin F.sectorCount) → ℕ := fun k ↦
    ∏ n : Fin N, Module.finrank ℂ (F.edgeGroundSpace (k n) (k (n + 1)))
  let cycle : (Fin N → Fin F.sectorCount) → Prop := fun k ↦
    ∀ n : Fin N, F.IsEdge (k n) (k (n + 1))
  rw [F.parentHamiltonianGroundSpaceES_finrank_eq_all_sequences (by omega)]
  change ∑ k : Fin N → Fin F.sectorCount, weight k =
    ∑ c : {k // cycle k}, weight c.1
  calc
    ∑ k : Fin N → Fin F.sectorCount, weight k =
        ∑ k ∈ Finset.univ.filter cycle, weight k := by
      symm
      apply Finset.sum_subset (Finset.filter_subset cycle Finset.univ)
      intro k _ hk
      have hncycle : ¬cycle k := by simpa using hk
      simp only [cycle, not_forall] at hncycle
      obtain ⟨n, hn⟩ := hncycle
      have hbot : F.edgeGroundSpace (k n) (k (n + 1)) = ⊥ :=
        not_ne_iff.mp hn
      change (∏ m : Fin N,
        Module.finrank ℂ (F.edgeGroundSpace (k m) (k (m + 1)))) = 0
      rw [Finset.prod_eq_zero (Finset.mem_univ n)]
      exact Submodule.finrank_eq_zero.mpr hbot
    _ = ∑ c : {k // cycle k}, weight c.1 := by
      exact Finset.sum_subtype (Finset.univ.filter cycle) (by simp) weight

/-- Beigi's ordered-cycle ground-space dimension formula at period two.  The
two cyclic windows traverse the same pair of sites in opposite orders, so
`(a, b)` and `(b, a)` remain distinct ordered cycles when `a ≠ b`.

Source: Beigi, arXiv:1105.1019v2, Section III, equations (2)--(4), source
lines 451--512; the period-two ordered-cycle convention is explicit at source
lines 509--512. -/
theorem parentHamiltonianGroundSpaceES_finrank_eq_two
    (F : BeigiSectorGraphData A) :
    Module.finrank ℂ (parentHamiltonianGroundSpaceES A 2 2) =
      ∑ c : F.OrderedCycle 2,
        ∏ n : Fin 2,
          Module.finrank ℂ (F.edgeGroundSpace (c.1 n) (c.1 (n + 1))) := by
  apply F.parentHamiltonianGroundSpaceES_finrank_eq (N := 2)
  omega

end BeigiSectorGraphData

end MPSTensor
