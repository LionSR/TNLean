import TNLean.PEPS.RegionBlock.Realization
import TNLean.PEPS.RegionBlock.Recovery
import TNLean.PEPS.RegionBlock.Algebra
import TNLean.PEPS.InsertionAlgebra

/-!
# Region physical-to-virtual recovery and the region insertion transfer

For a boundary edge `f` of an arbitrary finite region `R`, with single in-region
endpoint vertex `v`, this file recovers a matrix insertion on `f` of the second
tensor from a matrix insertion of the first, transferred across `SameState`. This
supplies the data of a `RegionInsertionTransfer` on `f` and closes the last
gating ingredient of the per-edge gauge for the normal PEPS Fundamental Theorem.

The development is the region analogue of the edge-level transfer of
`TNLean.PEPS.InsertionAlgebra` (built on the physical-to-virtual recovery
`physical_to_virtual_insertion`). The single in-region endpoint vertex `v` plays
the role of the edge's right endpoint, and the blocked-region weight of the rest
of `R` plays the role of the open middle weight:

* `regionInsertedCoeff_eq_regionRealizationSum` is the region analogue of
  `edgeInsertedCoeff_eq_sum_right_physicalRealization`: the region-inserted
  coefficient is a realization sum over the boundary configurations of `R`, with
  the inserted matrix carried by the physical operator `regionInsertionOp` at
  `v`. This is the realization-on-`A` general-matrix step.
* `regionRealizationSum_eq_smul_stateRealizationSum` collapses the
  tensor-dependent realization sum to the bond-dimension product
  `regionInteriorBondProd` times a `SameState`-invariant closed-state realization
  sum, via the identity-insertion bridge of `TNLean.PEPS.RegionBlock.Recovery`.
* `regionStateRealizationSum_sameState` transfers the closed-state realization
  sum across `SameState`.
* `regionTransferMatrix` reads off the recovered matrix on the second tensor's
  bond, and `regionTransferMatrix_regionInsertedCoeff` is the matched coefficient.
* `RegionInsertionTransfer.of_sameState` assembles the
  `RegionInsertionTransfer` datum, after which
  `exists_regionEdgeGauge_of_transfer` produces the per-edge gauge.

## References

- [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected entangled
  pair states generating the same state*, arXiv:1804.04964, Section 3, Lemma
  `inj_isomorph`, lines 254--582 of
  `Papers/1804.04964/paper_normal.tex`](https://arxiv.org/abs/1804.04964)
-/

open scoped BigOperators Matrix

namespace TNLean
namespace PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ}

/-! ### The unique in-region endpoint of a boundary edge

A boundary edge `f` of `R` has exactly one endpoint in `R`, the in-region
endpoint vertex `v = regionBoundaryEdgeInVertex R f`. This uniqueness is what lets
the rest of `R` ignore the virtual leg of the boundary edge `f`. -/

omit [Fintype V] [DecidableRel G.Adj] in
/-- The unique in-region endpoint of a boundary edge `f` of `R`: any endpoint of
`f` lying in `R` equals `regionBoundaryEdgeInVertex R f`. -/
theorem regionBoundaryEdge_endpoint_in_R_eq (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    {w : V} (hw : f.1.1.1 = w ∨ f.1.1.2 = w) (hwR : w ∈ R) :
    w = regionBoundaryEdgeInVertex (G := G) R f := by
  rcases f.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rcases hw with hw | hw
    · rw [regionBoundaryEdgeInVertex, if_pos h1]; exact hw.symm
    · exact absurd (hw ▸ hwR) h2
  · rcases hw with hw | hw
    · exact absurd (hw ▸ hwR) h1
    · rw [regionBoundaryEdgeInVertex, if_neg h1]; exact hw.symm

omit [Fintype V] in
/-- The rest-of-region product reads a global virtual configuration only away from
the boundary edge `f`: changing the configuration on `f` does not affect it. The
in-region endpoint of `f` is `v`, which is excluded, and the other endpoint lies
outside `R`. -/
theorem regionRestProd_congr_off_f (A : Tensor G d) (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (σ : RegionPhysicalConfig (V := V) (d := d) R)
    (ζ ζ' : VirtualConfig A)
    (hagree : ∀ e : Edge G, e ≠ f.1 → ζ e = ζ' e) :
    regionRestProd (G := G) A R f σ ζ = regionRestProd (G := G) A R f σ ζ' := by
  classical
  rw [regionRestProd, regionRestProd]
  refine Finset.prod_congr rfl (fun w hw => ?_)
  rw [Finset.mem_compl, Finset.mem_singleton] at hw
  congr 1; funext ie
  by_cases hf : ie.1 = f.1
  · exfalso; apply hw
    have hwendp : f.1.1.1 = w.1 ∨ f.1.1.2 = w.1 := by
      have := ie.2; rw [hf] at this; exact this
    exact Subtype.ext (regionBoundaryEdge_endpoint_in_R_eq (G := G) R f hwendp w.2)
  · exact hagree ie.1 hf

/-! ### The vertex-opened coefficient at the in-region endpoint

The region-inserted coefficient is realized at `v` through `regionOpenCoeff`, the
coefficient function on local virtual configurations at `v` through which the
blocked-region weight factors. The two lemmas below pin down its support on the
boundary edge `f` and its reindexing when the boundary value on `f` is changed. -/

open scoped Classical in
/-- The vertex-opened coefficient vanishes unless the local configuration at `v`
agrees with the boundary configuration `ν` on the boundary edge `f`. The boundary
configuration fixes the virtual index on `f`, and so does the local configuration
at `v` through its `f`-incident leg. -/
theorem regionOpenCoeff_eq_zero_of_ne (A : Tensor G d) (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (ν : RegionBoundaryConfig (G := G) A R)
    (σ : RegionPhysicalConfig (V := V) (d := d) R)
    (η : LocalVirtualConfig A (regionBoundaryEdgeInVertex (G := G) R f))
    (hne : η (regionBoundaryEdgeInIncident (G := G) R f) ≠ ν f) :
    regionOpenCoeff (G := G) A R f ν σ η = 0 := by
  classical
  rw [regionOpenCoeff]; apply Finset.sum_eq_zero; intro ζ hζ; exfalso
  rw [Finset.mem_filter] at hζ; obtain ⟨_, hbl, hvl⟩ := hζ; apply hne
  rw [← hvl, regionVertexLocalConfig_apply]
  have hbf := congrFun hbl f; rw [regionBoundaryLabel_apply] at hbf
  simp only [regionBoundaryEdgeInIncident_edge]; exact hbf

open scoped Classical in
/-- Reindexing the vertex-opened coefficient on the boundary edge `f`: setting the
`f`-leg of the local configuration to `ν f` and reading the rest from `η` equals
reading the boundary configuration with its `f`-value updated to the `f`-leg of
`η`. Both filtered global sums describe the same configurations, since the
rest-of-region product ignores the value on `f`. -/
theorem regionOpenCoeff_update_eq (A : Tensor G d) (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (ν : RegionBoundaryConfig (G := G) A R)
    (σ : RegionPhysicalConfig (V := V) (d := d) R)
    (η : LocalVirtualConfig A (regionBoundaryEdgeInVertex (G := G) R f)) :
    regionOpenCoeff (G := G) A R f ν σ
        ((localVirtualConfigSplitAt (G := G) A (regionBoundaryEdgeInIncident (G := G) R f)).symm
          (ν f, (localVirtualConfigSplitAt (G := G) A
            (regionBoundaryEdgeInIncident (G := G) R f) η).2)) =
      regionOpenCoeff (G := G) A R f
        (Function.update ν f (η (regionBoundaryEdgeInIncident (G := G) R f))) σ η := by
  classical
  set inc := regionBoundaryEdgeInIncident (G := G) R f with hinc
  set ηx := (localVirtualConfigSplitAt (G := G) A inc).symm
      (ν f, (localVirtualConfigSplitAt (G := G) A inc η).2) with hηx
  have hηxinc : ηx inc = ν f := by rw [hηx, localVirtualConfigSplitAt_symm_apply_fst]
  have hηxother : ∀ je : IncidentEdge G (regionBoundaryEdgeInVertex (G := G) R f), je ≠ inc →
      ηx je = η je := by
    intro je hje
    rw [hηx, localVirtualConfigSplitAt_symm_apply_snd A inc _ ⟨je, hje⟩,
      localVirtualConfigSplitAt_apply_snd]
  rw [regionOpenCoeff, regionOpenCoeff]
  refine Finset.sum_nbij'
    (fun ζ => Function.update ζ f.1 (η inc))
    (fun ζ => Function.update ζ f.1 (ν f)) ?_ ?_ ?_ ?_ ?_
  · intro ζ hζ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hζ ⊢
    obtain ⟨hbl, hvl⟩ := hζ
    refine ⟨?_, ?_⟩
    · funext g; rw [regionBoundaryLabel_apply]
      by_cases hg : g = f
      · subst hg; rw [Function.update_self, Function.update_self]
      · have hne : g.1 ≠ f.1 := fun h => hg (Subtype.ext h)
        rw [Function.update_of_ne hne (η inc) ζ, Function.update_of_ne hg (η inc) ν]
        have := congrFun hbl g; rw [regionBoundaryLabel_apply] at this; exact this
    · funext ie; rw [regionVertexLocalConfig_apply]
      by_cases hie : ie = inc
      · subst hie; exact Function.update_self _ _ _
      · have hne : ie.1 ≠ f.1 := fun h => hie (Subtype.ext h)
        rw [Function.update_of_ne hne (η inc) ζ]
        have := congrFun hvl ie; rw [regionVertexLocalConfig_apply] at this
        rw [this, hηxother ie hie]
  · intro ζ hζ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hζ ⊢
    obtain ⟨hbl, hvl⟩ := hζ
    refine ⟨?_, ?_⟩
    · funext g; rw [regionBoundaryLabel_apply]
      by_cases hg : g = f
      · subst hg; rw [Function.update_self]
      · have hne : g.1 ≠ f.1 := fun h => hg (Subtype.ext h)
        rw [Function.update_of_ne hne (ν f) ζ]
        have := congrFun hbl g
        rw [regionBoundaryLabel_apply, Function.update_of_ne hg _ ν] at this
        exact this
    · funext ie; rw [regionVertexLocalConfig_apply]
      by_cases hie : ie = inc
      · subst hie; rw [hηxinc]; exact Function.update_self _ _ _
      · have hne : ie.1 ≠ f.1 := fun h => hie (Subtype.ext h)
        rw [Function.update_of_ne hne (ν f) ζ]
        have := congrFun hvl ie; rw [regionVertexLocalConfig_apply] at this
        rw [this, hηxother ie hie]
  · intro ζ hζ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hζ
    obtain ⟨hbl, _⟩ := hζ
    funext e
    simp only []
    by_cases he : e = f.1
    · subst he; rw [Function.update_self]
      have := congrFun hbl f; rw [regionBoundaryLabel_apply] at this; exact this.symm
    · simp only [Function.update_of_ne he]
  · intro ζ hζ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hζ
    obtain ⟨hbl, _⟩ := hζ
    funext e
    simp only []
    by_cases he : e = f.1
    · subst he; rw [Function.update_self]
      have := congrFun hbl f
      rw [regionBoundaryLabel_apply, Function.update_self] at this; exact this.symm
    · simp only [Function.update_of_ne he]
  · intro ζ _
    exact (regionRestProd_congr_off_f (G := G) A R f σ ζ (Function.update ζ f.1 (η inc))
      (fun e he => (Function.update_of_ne he (η inc) ζ).symm))

/-! ### The region realization sum

The realization-on-`A` step expresses the region-inserted coefficient as a sum
over boundary configurations, with the inserted matrix carried by the physical
operator `regionInsertionOp` acting on the blocked-region weight at `v`. The two
coefficient lemmas below match the open region weight against the operator
applied. -/

open scoped Classical in
/-- The inner boundary-configuration sum of the region-inserted coefficient,
evaluated against the open region coefficient, collapses to the matrix entry on
the boundary edge `f` times the open region coefficient at the updated boundary
configuration. -/
theorem region_lhs_coeff (A : Tensor G d) (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (M : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ)
    (ν : RegionBoundaryConfig (G := G) A R)
    (σ : RegionPhysicalConfig (V := V) (d := d) R)
    (η : LocalVirtualConfig A (regionBoundaryEdgeInVertex (G := G) R f)) :
    (∑ μ : RegionBoundaryConfig (G := G) A R,
        (if SameAwayFromBond f μ ν then M (μ f) (ν f) else 0) *
          regionOpenCoeff (G := G) A R f μ σ η) =
      M (η (regionBoundaryEdgeInIncident (G := G) R f)) (ν f) *
        regionOpenCoeff (G := G) A R f
          (Function.update ν f (η (regionBoundaryEdgeInIncident (G := G) R f))) σ η := by
  classical
  set inc := regionBoundaryEdgeInIncident (G := G) R f with hinc
  rw [Finset.sum_eq_single (Function.update ν f (η inc))]
  · have hsame : SameAwayFromBond f (Function.update ν f (η inc)) ν := by
      intro c hc; rw [Function.update_of_ne hc]
    have hμf : (Function.update ν f (η inc)) f = η inc := Function.update_self _ _ _
    rw [if_pos hsame, hμf]
  · intro μ _ hμne
    by_cases hsame : SameAwayFromBond f μ ν
    · rw [if_pos hsame]
      have hμf_ne : μ f ≠ η inc := by
        intro hμf
        apply hμne
        funext c
        by_cases hc : c = f
        · subst hc; rw [Function.update_self, hμf]
        · rw [Function.update_of_ne hc]; exact hsame c hc
      rw [regionOpenCoeff_eq_zero_of_ne A R f μ σ η (fun h => hμf_ne h.symm), mul_zero]
    · rw [if_neg hsame, zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

open scoped Classical in
/-- The physical operator at `v` from `M.transpose`, applied to the open region
coefficient, reads off the matrix entry on the boundary edge `f` times the open
region coefficient at the updated boundary configuration. -/
theorem region_rhs_coeff (A : Tensor G d) (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (M : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ)
    (ν : RegionBoundaryConfig (G := G) A R)
    (σ : RegionPhysicalConfig (V := V) (d := d) R)
    (η : LocalVirtualConfig A (regionBoundaryEdgeInVertex (G := G) R f)) :
    (localIncidentMatrixOp A (regionBoundaryEdgeInIncident (G := G) R f) M.transpose
        (regionOpenCoeff (G := G) A R f ν σ)) η =
      M (η (regionBoundaryEdgeInIncident (G := G) R f)) (ν f) *
        regionOpenCoeff (G := G) A R f
          (Function.update ν f (η (regionBoundaryEdgeInIncident (G := G) R f))) σ η := by
  classical
  rw [localIncidentMatrixOp_apply]
  refine (Fintype.sum_eq_single (ν f) ?_).trans ?_
  · intro x hxne
    have hcfg : ((localVirtualConfigSplitAt (G := G) A
        (regionBoundaryEdgeInIncident (G := G) R f)).symm
          (x, ((localVirtualConfigSplitAt (G := G) A
            (regionBoundaryEdgeInIncident (G := G) R f)) η).2))
          (regionBoundaryEdgeInIncident (G := G) R f) = x := by
      rw [localVirtualConfigSplitAt_symm_apply_fst]
    rw [regionOpenCoeff_eq_zero_of_ne A R f ν σ _ (by rw [hcfg]; exact hxne), mul_zero]
  · rw [Matrix.transpose_apply, regionOpenCoeff_update_eq A R f ν σ η]

/-- The blocked-region weight as a function of the physical leg at the in-region
endpoint `v`, used as the realization vector that the physical operator acts on. -/
noncomputable def regionWeightVec (A : Tensor G d) (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (ν : RegionBoundaryConfig (G := G) A R)
    (σ : RegionPhysicalConfig (V := V) (d := d) R) : Fin d → ℂ :=
  localTensorMap A (regionBoundaryEdgeInVertex (G := G) R f) (regionOpenCoeff (G := G) A R f ν σ)

open scoped Classical in
/-- **Inner-sum realization at the in-region endpoint.** The inner
boundary-configuration sum of the region-inserted coefficient against the
blocked-region weight equals the physical operator `regionInsertionOp` from
`M.transpose`, applied to the region weight vector and evaluated at the physical
leg `σ v`. -/
theorem region_innerSum_eq_realized (A : Tensor G d) (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (hvA : LinearIndependent ℂ (A.component (regionBoundaryEdgeInVertex (G := G) R f)))
    (M : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ)
    (ν : RegionBoundaryConfig (G := G) A R)
    (σ : RegionPhysicalConfig (V := V) (d := d) R) :
    (∑ μ : RegionBoundaryConfig (G := G) A R,
        (if SameAwayFromBond f μ ν then M (μ f) (ν f) else 0) *
          regionBlockedWeight (G := G) A R μ σ) =
      regionInsertionOp (G := G) A R f hvA M.transpose
          (regionWeightVec (G := G) A R f ν σ)
        (σ ⟨regionBoundaryEdgeInVertex (G := G) R f,
          regionBoundaryEdgeInVertex_mem (G := G) R f⟩) := by
  classical
  set v := regionBoundaryEdgeInVertex (G := G) R f with hv
  set vmem : {w : V // w ∈ R} := ⟨v, regionBoundaryEdgeInVertex_mem (G := G) R f⟩ with hvmem
  rw [regionWeightVec,
    regionInsertionOp_realizes A R f hvA M.transpose (regionOpenCoeff (G := G) A R f ν σ),
    localTensorMap, Fintype.linearCombination_apply, Finset.sum_apply]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [show (∑ η : LocalVirtualConfig A v,
        (localIncidentMatrixOp A (regionBoundaryEdgeInIncident (G := G) R f) M.transpose
          (regionOpenCoeff (G := G) A R f ν σ)) η * A.component v η (σ vmem)) =
      ∑ η : LocalVirtualConfig A v,
        (M (η (regionBoundaryEdgeInIncident (G := G) R f)) (ν f) *
          regionOpenCoeff (G := G) A R f
            (Function.update ν f (η (regionBoundaryEdgeInIncident (G := G) R f))) σ η) *
          A.component v η (σ vmem) from
      Finset.sum_congr rfl (fun η _ => by rw [region_rhs_coeff A R f M ν σ η])]
  rw [show (∑ μ : RegionBoundaryConfig (G := G) A R,
        (if SameAwayFromBond f μ ν then M (μ f) (ν f) else 0) *
          regionBlockedWeight (G := G) A R μ σ) =
      ∑ μ : RegionBoundaryConfig (G := G) A R,
        ∑ η : LocalVirtualConfig A v,
          ((if SameAwayFromBond f μ ν then M (μ f) (ν f) else 0) *
            regionOpenCoeff (G := G) A R f μ σ η) * A.component v η (σ vmem) from ?_]
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun η _ => ?_)
    rw [← Finset.sum_mul]
    congr 1
    exact region_lhs_coeff A R f M ν σ η
  · refine Finset.sum_congr rfl (fun μ _ => ?_)
    rw [regionBlockedWeight_eq_localTensorMap A R f μ σ,
      localTensorMap, Fintype.linearCombination_apply, Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun η _ => ?_)
    ring

/-- The region realization sum: the realization-on-`A` form of the
region-inserted coefficient, with the inserted matrix carried by the physical
operator `O` at the in-region endpoint `v`, contracted against the complement
block of `R`.

This is the region analogue of the right realization sum of
`edgeInsertedCoeff_eq_sum_right_physicalRealization`. -/
noncomputable def regionRealizationSum (A : Tensor G d) (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (O : (Fin d → ℂ) →ₗ[ℂ] (Fin d → ℂ))
    (σ : RegionPhysicalConfig (V := V) (d := d) R)
    (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R)) : ℂ := by
  classical
  exact
    ∑ ν : RegionBoundaryConfig (G := G) A R,
      O (regionWeightVec (G := G) A R f ν σ)
          (σ ⟨regionBoundaryEdgeInVertex (G := G) R f,
            regionBoundaryEdgeInVertex_mem (G := G) R f⟩) *
        regionBlockedWeight (G := G) A (Finset.univ \ R)
          (regionComplementBoundaryConfig (G := G) A R ν) τ

open scoped Classical in
/-- **Realization-on-`A` of the region-inserted coefficient.** The region-inserted
coefficient of `M` is the region realization sum carrying `M.transpose` through
the physical operator `regionInsertionOp` at the in-region endpoint `v`.

This is the region analogue of `edgeInsertedCoeff_eq_sum_right_physicalRealization`,
with the single in-region endpoint vertex `v` playing the role of the edge's right
endpoint.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, lines 254--582 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem regionInsertedCoeff_eq_regionRealizationSum (A : Tensor G d) (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (hvA : LinearIndependent ℂ (A.component (regionBoundaryEdgeInVertex (G := G) R f)))
    (M : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ)
    (σ : RegionPhysicalConfig (V := V) (d := d) R)
    (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R)) :
    regionInsertedCoeff (G := G) A R f M σ τ =
      regionRealizationSum (G := G) A R f
        (regionInsertionOp (G := G) A R f hvA M.transpose) σ τ := by
  classical
  rw [regionInsertedCoeff_eq, regionRealizationSum, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun ν _ => ?_)
  rw [← Finset.sum_mul, region_innerSum_eq_realized A R f hvA M ν σ]

/-! ### Collapse to the closed-state realization sum

The region realization sum is tensor-dependent (through the blocked-region
weights of `R` and its complement). It collapses to the bond-dimension product
`regionInteriorBondProd` times a `SameState`-invariant closed-state realization
sum, by the identity-insertion bridge: with the inserted matrix expanded over the
standard basis at `v`, each basis sum is an identity insertion, which reads the
closed state coefficient by `regionInsertedCoeff_one_eq_stateCoeff`. -/

open scoped Classical in
/-- The open region coefficient is unchanged when the physical configuration is
updated at the in-region endpoint `v`, since the rest-of-region product reads the
physical legs only away from `v`. -/
theorem regionOpenCoeff_update_vmem (A : Tensor G d) (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (ν : RegionBoundaryConfig (G := G) A R)
    (σ : RegionPhysicalConfig (V := V) (d := d) R) (a : Fin d) :
    regionOpenCoeff (G := G) A R f ν
        (Function.update σ ⟨regionBoundaryEdgeInVertex (G := G) R f,
          regionBoundaryEdgeInVertex_mem (G := G) R f⟩ a) =
      regionOpenCoeff (G := G) A R f ν σ := by
  classical
  set vmem : {w : V // w ∈ R} :=
    ⟨regionBoundaryEdgeInVertex (G := G) R f, regionBoundaryEdgeInVertex_mem (G := G) R f⟩
    with hvmem
  funext η
  rw [regionOpenCoeff, regionOpenCoeff]
  refine Finset.sum_congr rfl (fun ζ _ => ?_)
  rw [regionRestProd, regionRestProd]
  refine Finset.prod_congr rfl (fun w hw => ?_)
  rw [Finset.mem_compl, Finset.mem_singleton] at hw
  rw [Function.update_of_ne hw]

open scoped Classical in
/-- The region weight vector at the physical leg `a` equals the blocked-region
weight with the physical configuration updated to `a` at the in-region endpoint
`v`. -/
theorem regionWeightVec_apply_eq (A : Tensor G d) (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (ν : RegionBoundaryConfig (G := G) A R)
    (σ : RegionPhysicalConfig (V := V) (d := d) R) (a : Fin d) :
    regionWeightVec (G := G) A R f ν σ a =
      regionBlockedWeight (G := G) A R ν
        (Function.update σ ⟨regionBoundaryEdgeInVertex (G := G) R f,
          regionBoundaryEdgeInVertex_mem (G := G) R f⟩ a) := by
  classical
  set vmem : {w : V // w ∈ R} :=
    ⟨regionBoundaryEdgeInVertex (G := G) R f, regionBoundaryEdgeInVertex_mem (G := G) R f⟩
    with hvmem
  rw [regionBlockedWeight_eq_localTensorMap A R f ν (Function.update σ vmem a),
    show (Function.update σ vmem a) vmem = a from Function.update_self _ _ _,
    regionOpenCoeff_update_vmem A R f ν σ a, regionWeightVec]

/-- The closed-state realization sum: the physical operator `O` acting on the
standard basis at the in-region endpoint `v`, weighted by the closed state
coefficient with the physical leg at `v` ranging over the basis.

This is the `SameState`-invariant form: it reads the two tensors only through the
closed state coefficient, which `SameState` equates. -/
noncomputable def regionStateRealizationSum (A : Tensor G d) (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (O : (Fin d → ℂ) →ₗ[ℂ] (Fin d → ℂ))
    (σ : RegionPhysicalConfig (V := V) (d := d) R)
    (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R)) : ℂ :=
  ∑ a : Fin d,
    O (Pi.single a (1 : ℂ))
        (σ ⟨regionBoundaryEdgeInVertex (G := G) R f,
          regionBoundaryEdgeInVertex_mem (G := G) R f⟩) *
      stateCoeff A (assembleRegionσ (V := V) (d := d) R
        (Function.update σ ⟨regionBoundaryEdgeInVertex (G := G) R f,
          regionBoundaryEdgeInVertex_mem (G := G) R f⟩ a) τ)

open scoped Classical in
/-- **Collapse to the closed-state realization sum.** The region realization sum
equals the bond-dimension product over the non-boundary edges times the
closed-state realization sum. Expanding the physical operator over the standard
basis at `v`, each basis sum is an identity insertion, and
`regionInsertedCoeff_one_eq_stateCoeff` reads off the closed state coefficient
with the overcounting multiplicity `regionInteriorBondProd`.

Source: arXiv:1804.04964, Section 3, lines 1205--1210 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem regionRealizationSum_eq_smul_stateRealizationSum (A : Tensor G d) (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (O : (Fin d → ℂ) →ₗ[ℂ] (Fin d → ℂ))
    (σ : RegionPhysicalConfig (V := V) (d := d) R)
    (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R)) :
    regionRealizationSum (G := G) A R f O σ τ =
      regionInteriorBondProd (G := G) A R • regionStateRealizationSum (G := G) A R f O σ τ := by
  classical
  set vmem : {w : V // w ∈ R} :=
    ⟨regionBoundaryEdgeInVertex (G := G) R f, regionBoundaryEdgeInVertex_mem (G := G) R f⟩
    with hvmem
  rw [regionRealizationSum]
  have hexpand : ∀ ν : RegionBoundaryConfig (G := G) A R,
      O (regionWeightVec (G := G) A R f ν σ) (σ vmem) =
        ∑ a : Fin d, (regionWeightVec (G := G) A R f ν σ a) * O (Pi.single a (1 : ℂ)) (σ vmem) := by
    intro ν
    have hsingle : ∀ a : Fin d, (fun j => if a = j then (1 : ℂ) else 0) = Pi.single a (1 : ℂ) := by
      intro a; funext j; simp [Pi.single_apply, eq_comm]
    rw [LinearMap.pi_apply_eq_sum_univ O (regionWeightVec (G := G) A R f ν σ), Finset.sum_apply]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Pi.smul_apply, smul_eq_mul, hsingle a]
  rw [Finset.sum_congr rfl (fun ν (_ : ν ∈ Finset.univ) => by rw [hexpand ν])]
  rw [show (∑ ν : RegionBoundaryConfig (G := G) A R,
        (∑ a : Fin d, (regionWeightVec (G := G) A R f ν σ a) * O (Pi.single a (1 : ℂ)) (σ vmem)) *
          regionBlockedWeight (G := G) A (Finset.univ \ R)
            (regionComplementBoundaryConfig (G := G) A R ν) τ) =
      ∑ a : Fin d, ∑ ν : RegionBoundaryConfig (G := G) A R,
        O (Pi.single a (1 : ℂ)) (σ vmem) *
          (regionBlockedWeight (G := G) A R ν (Function.update σ vmem a) *
            regionBlockedWeight (G := G) A (Finset.univ \ R)
              (regionComplementBoundaryConfig (G := G) A R ν) τ) from ?_]
  · rw [regionStateRealizationSum, Finset.smul_sum]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [← Finset.mul_sum]
    rw [show (∑ ν : RegionBoundaryConfig (G := G) A R,
          regionBlockedWeight (G := G) A R ν (Function.update σ vmem a) *
            regionBlockedWeight (G := G) A (Finset.univ \ R)
              (regionComplementBoundaryConfig (G := G) A R ν) τ) =
        regionInsertedCoeff (G := G) A R f
          (1 : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ)
          (Function.update σ vmem a) τ from
        (regionInsertedCoeff_identity A R f (Function.update σ vmem a) τ).symm]
    rw [regionInsertedCoeff_one_eq_stateCoeff A R f (Function.update σ vmem a) τ,
      nsmul_eq_mul, nsmul_eq_mul]
    ring
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun ν _ => ?_)
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [regionWeightVec_apply_eq A R f ν σ a]
    ring

/-- The closed-state realization sum is `SameState`-invariant: it reads the tensor
only through the closed state coefficient, which `SameState` equates. This is what
carries the region realization from one tensor to the other. -/
theorem regionStateRealizationSum_sameState {A B : Tensor G d} (hAB : SameState A B)
    (R : Finset V) (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (O : (Fin d → ℂ) →ₗ[ℂ] (Fin d → ℂ))
    (σ : RegionPhysicalConfig (V := V) (d := d) R)
    (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R)) :
    regionStateRealizationSum (G := G) A R f O σ τ =
      regionStateRealizationSum (G := G) B R f O σ τ := by
  rw [regionStateRealizationSum, regionStateRealizationSum]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [hAB _]

/-! ### The operator on the closed state vector

The closed-state realization sum equals a single physical operator acting on the
closed state vector at the in-region endpoint `v`. Since the closed state vector
is `SameState`-invariant (`regionStateVec_sameState`), this is the form that
carries the region-inserted coefficient from one tensor to the other: applying the
in-region endpoint operator of the first tensor to the (shared) closed state
vector reads the region-inserted coefficient through whichever tensor's blocked
weight is used to factor the state vector. -/

open scoped Classical in
/-- The closed-state realization sum equals the physical operator `O` applied to
the closed state vector at the in-region endpoint `v`, evaluated at the physical
leg `σ v`. Both expand `O` over the standard basis at `v`; the closed state vector
is the standard-basis combination weighted by the closed state coefficient. -/
theorem regionStateRealizationSum_eq_op_regionStateVec (A : Tensor G d) (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (O : (Fin d → ℂ) →ₗ[ℂ] (Fin d → ℂ))
    (σ : RegionPhysicalConfig (V := V) (d := d) R)
    (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R)) :
    regionStateRealizationSum (G := G) A R f O σ τ =
      O (regionStateVec (G := G) A R f σ τ)
        (σ ⟨regionBoundaryEdgeInVertex (G := G) R f,
          regionBoundaryEdgeInVertex_mem (G := G) R f⟩) := by
  classical
  set vmem : {w : V // w ∈ R} :=
    ⟨regionBoundaryEdgeInVertex (G := G) R f, regionBoundaryEdgeInVertex_mem (G := G) R f⟩
    with hvmem
  rw [regionStateRealizationSum]
  have hsingle : ∀ a : Fin d, (fun j => if a = j then (1 : ℂ) else 0) = Pi.single a (1 : ℂ) := by
    intro a; funext j; simp [Pi.single_apply, eq_comm]
  rw [LinearMap.pi_apply_eq_sum_univ O (regionStateVec (G := G) A R f σ τ), Finset.sum_apply]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Pi.smul_apply, smul_eq_mul, hsingle a, regionStateVec]
  ring

open scoped Classical in
/-- **Region-inserted coefficient through the in-region endpoint operator.** The
region-inserted coefficient of `M` is the bond-dimension product over the
non-boundary edges times the in-region endpoint operator from `M.transpose`,
applied to the closed state vector at `v`.

Combining `regionInsertedCoeff_eq_regionRealizationSum`, the collapse to the
closed-state realization sum, and the identification of that sum with the operator
on the closed state vector, this is the form on which the `SameState` transfer
acts: the closed state vector is `SameState`-invariant, and the only remaining
tensor dependence is the bond-dimension product and the in-region endpoint
operator.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, lines 254--582 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem regionInsertedCoeff_eq_smul_op_regionStateVec (A : Tensor G d) (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (hvA : LinearIndependent ℂ (A.component (regionBoundaryEdgeInVertex (G := G) R f)))
    (M : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ)
    (σ : RegionPhysicalConfig (V := V) (d := d) R)
    (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R)) :
    regionInsertedCoeff (G := G) A R f M σ τ =
      regionInteriorBondProd (G := G) A R •
        (regionInsertionOp (G := G) A R f hvA M.transpose
            (regionStateVec (G := G) A R f σ τ))
          (σ ⟨regionBoundaryEdgeInVertex (G := G) R f,
            regionBoundaryEdgeInVertex_mem (G := G) R f⟩) := by
  rw [regionInsertedCoeff_eq_regionRealizationSum A R f hvA M σ τ,
    regionRealizationSum_eq_smul_stateRealizationSum,
    regionStateRealizationSum_eq_op_regionStateVec]

/-! ### Matched region-inserted coefficients from a realized matrix transfer

The region-inserted coefficients of the two tensors are matched as soon as the
in-region endpoint operator of the first tensor is realized, on the images of the
second tensor's local tensor map at `v`, by a matrix insertion on the boundary
edge `f`. This is the region analogue of
`edgeRightInsertionOp_realizes_edgeTransferMatrix`: the physical operator
transferred across `SameState` becomes a virtual matrix insertion on the second
tensor's bond.

The two ingredients left open are the realization itself — the region analogue of
the physical-to-virtual recovery `physical_to_virtual_insertion` — and the
equality of the bond-dimension products over the non-boundary edges, which is the
multiplicity bookkeeping of the region/complement contraction. -/

open scoped Classical in
/-- **Matched region-inserted coefficients from a realized matrix transfer.** If
the in-region endpoint operator of the first tensor from `M.transpose` is realized
on the second tensor's local tensor images by inserting `N.transpose` on the
boundary edge `f`, and the two bond-dimension products over the non-boundary edges
agree, then the region-inserted coefficient of `M` in the first tensor equals the
region-inserted coefficient of `N` in the second.

The proof moves the region-inserted coefficient onto the in-region endpoint
operator acting on the closed state vector
(`regionInsertedCoeff_eq_smul_op_regionStateVec`), uses `SameState` to equate the
closed state vectors (`regionStateVec_sameState`), rewrites the second tensor's
state vector as a local tensor image (`regionStateVec_eq_localTensorMap`), and
applies the realization hypothesis.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, lines 254--582 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem regionInsertedCoeff_transfer_of_realizes (A B : Tensor G d) (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (hvA : LinearIndependent ℂ (A.component (regionBoundaryEdgeInVertex (G := G) R f)))
    (hvB : LinearIndependent ℂ (B.component (regionBoundaryEdgeInVertex (G := G) R f)))
    (hAB : SameState A B)
    (hbond : regionInteriorBondProd (G := G) A R = regionInteriorBondProd (G := G) B R)
    (M : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ)
    (N : Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ)
    (hreal : ∀ c : LocalVirtualConfig B (regionBoundaryEdgeInVertex (G := G) R f) → ℂ,
      regionInsertionOp (G := G) A R f hvA M.transpose
          (localTensorMap B (regionBoundaryEdgeInVertex (G := G) R f) c) =
        localTensorMap B (regionBoundaryEdgeInVertex (G := G) R f)
          (localIncidentMatrixOp B (regionBoundaryEdgeInIncident (G := G) R f) N.transpose c))
    (σ : RegionPhysicalConfig (V := V) (d := d) R)
    (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R)) :
    regionInsertedCoeff (G := G) A R f M σ τ =
      regionInsertedCoeff (G := G) B R f N σ τ := by
  classical
  rw [regionInsertedCoeff_eq_smul_op_regionStateVec A R f hvA M σ τ,
    regionStateVec_sameState hAB R f σ τ,
    regionInsertedCoeff_eq_smul_op_regionStateVec B R f hvB N σ τ, ← hbond]
  congr 1
  rw [regionStateVec_eq_localTensorMap B R f σ τ, hreal,
    ← regionInsertionOp_realizes B R f hvB N.transpose]

end PEPS
end TNLean
