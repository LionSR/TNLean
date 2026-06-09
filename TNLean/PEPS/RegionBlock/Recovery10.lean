import TNLean.PEPS.RegionBlock.Recovery9

/-!
# Region physical-to-virtual recovery: the coefficient transfer

This file closes the single remaining gap of the normal PEPS Fundamental Theorem
(arXiv:1804.04964, Section 3): the **coefficient transfer**. For every inserted
matrix `M` on the first tensor's boundary bond there is a matrix `N` on the second
tensor's bond whose region-inserted coefficient equals the first tensor's at every
physical configuration. Feeding it to `regionResonateReconcile_of_coeff_transfer`
(`TNLean.PEPS.RegionBlock.Recovery9`) yields the region resonate reconcile
`RegionResonateReconcile`, the last open obligation of
`docs/paper-gaps/peps_normal_ft_section3_route.tex`.

## Strategy

The v-side factorization `regionInsertedCoeff_eq_complement_blockedMap_B`
(`Recovery9`) writes the first tensor's region-inserted coefficient, as a function
of the complement physical configuration `τ`, as the second tensor's complement
blocked tensor map applied to a row function `cRow σ`. The B-analogue
`regionInsertedCoeff_eq_complement_blockedMap` (`Recovery7`) writes the *second*
tensor's region-inserted coefficient of `N` in the same complement form, with row
function `regionComplementRow B R f N σ`. Since the second tensor's complement
blocked tensor map is injective (`hCB`), the coefficient transfer is equivalent to
producing a matrix `N` whose complement row matches `cRow σ` at every `σ`.

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

/-! ### The v-side row and the reduction of the coefficient transfer

The v-side row `vSideRow A B R f hvA hAB hDim M σ` is the row function reading the
first tensor's in-region endpoint operator against the second tensor's region
weight vectors at the endpoint leg. By the v-side factorization
`regionInsertedCoeff_eq_complement_blockedMap_B`, the first tensor's region-inserted
coefficient, as a function of the complement physical configuration, is the second
tensor's complement blocked tensor map applied to this row. -/

/-- The v-side row of the first tensor's region-inserted coefficient through the
second tensor's complement block: for a complement boundary configuration `ν` of
`univ \ R`, the first tensor's in-region endpoint operator from `M.transpose`,
applied to the second tensor's region weight vector at the reindexed boundary
configuration, evaluated at the endpoint physical leg `σ v`.

This is the row read off by `regionBlockedLeftInverse_complement_regionInsertedCoeff_B`
(`Recovery9`): the second tensor's complement blocked left inverse applied to the
first tensor's region-inserted coefficient viewed as a function of the complement
physical configuration recovers `vSideRow`.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, lines 254--582 of
`Papers/1804.04964/paper_normal.tex`. -/
noncomputable def vSideRow (A B : Tensor G d) (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (hvA : LinearIndependent ℂ (A.component (regionBoundaryEdgeInVertex (G := G) R f)))
    (M : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ)
    (σ : RegionPhysicalConfig (V := V) (d := d) R) :
    RegionBoundaryConfig (G := G) B (Finset.univ \ R) → ℂ :=
  fun ν =>
    (regionInsertionOp (G := G) A R f hvA M.transpose
        (regionWeightVec (G := G) B R f
          ((regionComplementBoundaryConfigEquiv (G := G) B R).symm ν) σ))
      (σ ⟨regionBoundaryEdgeInVertex (G := G) R f,
        regionBoundaryEdgeInVertex_mem (G := G) R f⟩)

/-- The first tensor's region-inserted coefficient of `M`, as a function of the
complement physical configuration `τ`, is the second tensor's complement blocked
tensor map applied to the v-side row. This restates
`regionInsertedCoeff_eq_complement_blockedMap_B` (`Recovery9`) with the row named. -/
theorem regionInsertedCoeff_eq_complement_blockedMap_vSideRow (A B : Tensor G d)
    (R : Finset V) (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (hvA : LinearIndependent ℂ (A.component (regionBoundaryEdgeInVertex (G := G) R f)))
    (hAB : SameState A B) (hDim : A.bondDim = B.bondDim)
    (M : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ)
    (σ : RegionPhysicalConfig (V := V) (d := d) R) :
    (fun τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R) =>
        regionInsertedCoeff (G := G) A R f M σ τ) =
      regionBlockedTensorMap (G := G) B (Finset.univ \ R)
        (vSideRow (G := G) A B R f hvA M σ) :=
  regionInsertedCoeff_eq_complement_blockedMap_B A B R f hvA hAB hDim M σ

/-- **Reduction of the coefficient transfer to the row equality.** If there is a
matrix `N` on the second tensor's bond whose complement row matches the v-side row
at every region physical configuration, then the region-inserted coefficient of `M`
in the first tensor equals that of `N` in the second at every physical configuration.

The second tensor's complement blocked tensor map sends the matched rows to the two
region-inserted coefficients (v-side `regionInsertedCoeff_eq_complement_blockedMap_B`
for the first tensor and `regionInsertedCoeff_eq_complement_blockedMap` for the
second), so equal rows give equal coefficients.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, lines 254--582 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem regionInsertedCoeff_eq_of_complementRow_eq (A B : Tensor G d) (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (hvA : LinearIndependent ℂ (A.component (regionBoundaryEdgeInVertex (G := G) R f)))
    (hAB : SameState A B) (hDim : A.bondDim = B.bondDim)
    (M : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ)
    (N : Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ)
    (hrow : ∀ σ : RegionPhysicalConfig (V := V) (d := d) R,
      vSideRow (G := G) A B R f hvA M σ = regionComplementRow (G := G) B R f N σ)
    (σ : RegionPhysicalConfig (V := V) (d := d) R)
    (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R)) :
    regionInsertedCoeff (G := G) A R f M σ τ =
      regionInsertedCoeff (G := G) B R f N σ τ := by
  have hA := congrFun
    (regionInsertedCoeff_eq_complement_blockedMap_vSideRow A B R f hvA hAB hDim M σ) τ
  rw [hA, hrow σ, ← regionInsertedCoeff_eq_complement_blockedMap B R f N σ τ]

end PEPS
end TNLean
