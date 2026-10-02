/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.ParentHamiltonian.TorusSectorLocalGroundSpace
import TNLean.PEPS.ParentHamiltonian.RegularTorusRectangleEntropyBound
import TNLean.PEPS.TorusIncidentGInjectivity
import TNLean.PEPS.RegularGInjectiveSimplyConnectedEntropy
import TNLean.PEPS.TorusRectangleRealization

/-!
# Coherent torus sectors recover interior regional ground spaces

For a regular G-injective native tensor, every nonzero coherent sum of
commuting torus closures has full regional physical support on a positive
strict interior coordinate rectangle. Local closure membership gives the
support inclusion, while the simply connected regular Schmidt-rank theorem
gives equality of dimensions. Thus its physical coefficient matrix has range
exactly the original regional ground space.

**Scope restriction (interior regular sectors):** Both periods are at least
three, the virtual representation is regular, each closure pair commutes,
the coherent sum is nonzero, and the rectangle is positive and strictly
interior. This is a local support statement, not a classification of the
full parent-Hamiltonian ground space; see
`docs/paper-gaps/rmp_peps_quantum_double_g_isometry.tex`.

Source: Schuch, Cirac, and Pérez-García, arXiv:1001.3807, Theorem 5.5
and Corollary 6.10, local source lines 1440–1545 and 2074–2090.
-/

open scoped BigOperators Matrix ComplexOrder

namespace TNLean.PEPS

variable {width height : ℕ} [NeZero width] [NeZero height]
variable [Fact (2 < width)] [Fact (2 < height)]

local instance : Fact (1 < width) := ⟨by have := Fact.out (p := 2 < width); omega⟩
local instance : Fact (1 < height) := ⟨by have := Fact.out (p := 2 < height); omega⟩

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G] {d : ℕ}
local notation "X" => TorusVertex width height

/-- Every coherent closure cut has physical range contained in the original
interior regional ground space. Source: SCP10, local closure span in
Theorem 5.5, lines 1440–1545. No injectivity or commutativity is needed. -/
theorem range_torusClosureSuperpositionCut_le_regionGroundSpace_interior_rectangle
    {I : Type*} [Fintype I]
    (a : G → G → G → G → Fin d → ℂ) (pairs : I → G × G) (μ : I → ℂ)
    (xStart yStart xLen yLen : ℕ) (hxStart : 0 < xStart) (hyStart : 0 < yStart)
    (hxEnd : xStart + xLen < width) (hyEnd : yStart + yLen < height) :
    let R : Finset X := torusContiguousRectangle xStart yStart xLen yLen
    let M : Matrix (RegionPhysicalConfig (d := d) R)
        (RegionPhysicalConfig (d := d) (Finset.univ \ R)) ℂ :=
      fun σ τ => torusClosureSuperpositionCut a pairs μ R (σ, τ)
    (Matrix.mulVecLin M).range ≤ regionGroundSpace (groupBondTensor (torusIncidentSite a)) R := by
  intro R M
  rw [Matrix.range_mulVecLin, Submodule.span_le]
  rintro ψ ⟨τ, rfl⟩
  exact torusGClosure_sum_slice_mem_regionGroundSpace_interior_rectangle
    a pairs μ xStart yStart xLen yLen hxStart hyStart hxEnd hyEnd τ

/-- Every nonzero coherent sum of commuting regular G-injective torus
closures has the entire original regional ground space as physical support
on a positive strict interior rectangle. Source: SCP10, Corollary 6.10,
lines 2074–2090, together with the local closure span in Theorem 5.5. -/
theorem IsGInjective.range_torusClosureSuperpositionCut_eq_regionGroundSpace_interior_rectangle
    {I : Type*} [Fintype I] {a : G → G → G → G → Fin d → ℂ}
    (ha : IsGInjective (torusLegRep (leftRegularMatrix G)) (siteMap a))
    (pairs : I → G × G) (hcomm : ∀ i, Commute (pairs i).1 (pairs i).2) (μ : I → ℂ)
    (hne : (∑ i, μ i • torusGClosure (width := width) (height := height)
      (leftRegularMatrix G) a (pairs i).1 (pairs i).2) ≠ 0)
    (xStart yStart xLen yLen : ℕ) (hxStart : 0 < xStart) (hyStart : 0 < yStart)
    (hxPos : 0 < xLen) (hyPos : 0 < yLen)
    (hxEnd : xStart + xLen < width) (hyEnd : yStart + yLen < height) :
    let R : Finset X := torusContiguousRectangle xStart yStart xLen yLen
    let M : Matrix (RegionPhysicalConfig (d := d) R)
        (RegionPhysicalConfig (d := d) (Finset.univ \ R)) ℂ :=
      fun σ τ => torusClosureSuperpositionCut a pairs μ R (σ, τ)
    (Matrix.mulVecLin M).range = regionGroundSpace (groupBondTensor (torusIncidentSite a)) R := by
  classical
  intro R M
  have hxLen : xLen < width := by omega
  have hyLen : yLen < height := by omega
  have hR := torusGraph_rectangle_connected xStart yStart xLen yLen
    hxPos hyPos hxEnd.le hyEnd.le
  have hSC := isSimplyConnected_torusRegionRealization_rectangle
    xStart yStart xLen yLen hxPos hyPos hxLen hyLen hxEnd.le hyEnd.le
  obtain ⟨hpos, -, -, hrank, -, -⟩ :=
    ha.torusPhysicalCut_rank_zeroEntropy_of_isSimplyConnected R hR hSC pairs hcomm μ hne
  let Ψ := ∑ i, μ i • torusGClosure (width := width) (height := height)
    (leftRegularMatrix G) a (pairs i).1 (pairs i).2
  let K := physicalCutMatrix (fun v => v ∈ R) Ψ
  have ht : (K * K.conjTranspose).trace ≠ 0 := ne_of_gt hpos
  have hKrank : K.rank = Fintype.card G ^
      (Fintype.card {f : Edge (torusGraph width height) // IsRegionBoundaryEdge R f} - 1) := by
    rw [Matrix.rank_smul_of_mem_nonZeroDivisors _
      (mem_nonZeroDivisors_of_ne_zero (inv_ne_zero ht)),
      Matrix.rank_self_mul_conjTranspose] at hrank
    exact hrank
  let eD : {v : X // v ∈ Finset.univ \ R} ≃ {v : X // ¬v ∈ R} :=
    Equiv.subtypeEquivRight (fun v => by simp)
  let eS := eD.arrowCongr (Equiv.refl (Fin d))
  have hM : M = K.submatrix (Equiv.refl _) eS := by
    ext σ τ
    rfl
  have hMrank : M.rank = Fintype.card G ^ (2 * xLen + 2 * yLen - 1) := by
    rw [hM, Matrix.rank_submatrix, hKrank,
      card_regionBoundaryEdge_torusRectangle
        xStart yStart xLen yLen hxPos hyPos hxEnd.le hyEnd.le hxLen hyLen]
  apply Submodule.eq_of_le_of_finrank_eq
  · exact range_torusClosureSuperpositionCut_le_regionGroundSpace_interior_rectangle
      a pairs μ xStart yStart xLen yLen hxStart hyStart hxEnd hyEnd
  · change M.rank = Module.finrank ℂ (regionGroundSpace (groupBondTensor (torusIncidentSite a)) R)
    rw [hMrank]
    exact (finrank_regionGroundSpace_of_regular_connected (torusIncidentSite a)
      (fun v => ha.isGInjective_torusIncidentSite v) R hR _
      (torusRectangleBoundaryEquiv
        xStart yStart xLen yLen hxPos hyPos hxEnd.le hyEnd.le hxLen hyLen)).symm

/-- The actual regional reduced density of a nonzero coherent sum of
commuting regular G-injective closures has support equal to the original
regional ground space on a positive strict interior rectangle. Source:
SCP10, Corollary 6.10 and the local closure span in Theorem 5.5. -/
theorem IsGInjective.range_torusClosureReducedDensity_eq_regionGroundSpace_interior_rectangle
    {I : Type*} [Fintype I] {a : G → G → G → G → Fin d → ℂ}
    (ha : IsGInjective (torusLegRep (leftRegularMatrix G)) (siteMap a))
    (pairs : I → G × G) (hcomm : ∀ i, Commute (pairs i).1 (pairs i).2) (μ : I → ℂ)
    (hne : (∑ i, μ i • torusGClosure (width := width) (height := height)
      (leftRegularMatrix G) a (pairs i).1 (pairs i).2) ≠ 0)
    (xStart yStart xLen yLen : ℕ) (hxStart : 0 < xStart) (hyStart : 0 < yStart)
    (hxPos : 0 < xLen) (hyPos : 0 < yLen)
    (hxEnd : xStart + xLen < width) (hyEnd : yStart + yLen < height) :
    let R : Finset X := torusContiguousRectangle xStart yStart xLen yLen
    let ψ := torusClosureSuperpositionCut a pairs μ R
    (Matrix.mulVecLin
      (Matrix.partialTraceRight (Matrix.vecMulVec ψ (star ψ)))).range =
        regionGroundSpace (groupBondTensor (torusIncidentSite a)) R := by
  classical
  intro R ψ
  rw [Matrix.partialTraceRight_vecMulVec_eq]
  let M : Matrix (RegionPhysicalConfig (d := d) R)
      (RegionPhysicalConfig (d := d) (Finset.univ \ R)) ℂ := fun σ τ => ψ (σ, τ)
  have hM := ha.range_torusClosureSuperpositionCut_eq_regionGroundSpace_interior_rectangle
    pairs hcomm μ hne xStart yStart xLen yLen hxStart hyStart hxPos hyPos hxEnd hyEnd
  apply Submodule.eq_of_le_of_finrank_eq
  · change (Matrix.mulVecLin (M * Mᴴ)).range ≤ _
    rw [Matrix.mulVecLin_mul]
    exact (LinearMap.range_comp_le_range _ _).trans hM.le
  · change (M * Mᴴ).rank = Module.finrank ℂ
      (regionGroundSpace (groupBondTensor (torusIncidentSite a)) R)
    rw [Matrix.rank_self_mul_conjTranspose]
    change Module.finrank ℂ (Matrix.mulVecLin M).range = _
    rw [hM]

end TNLean.PEPS
