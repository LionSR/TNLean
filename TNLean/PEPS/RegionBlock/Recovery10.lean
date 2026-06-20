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

/-! ### The double-complement transport of the blocked tensor map

The blocked tensor map of `univ \ (univ \ R)`, applied to a row function and
evaluated at the double-complement transport of a region physical configuration,
equals the blocked tensor map of `R` applied to the row precomposed with the
double-complement boundary-configuration transport. This isolates the dependent
reindexing `univ \ (univ \ R) = R` into a single tensor-map identity, built from
the double-complement weight invariance `regionBlockedWeight_doubleCompl`
(`Recovery6`). -/

/-- The double-complement boundary-configuration transport as an equivalence: a
boundary configuration on `R` corresponds to one on `univ \ (univ \ R)` by reading
each crossing edge under the double-complement boundary-edge equivalence. -/
def regionDoubleComplBoundaryConfigEquiv (A : Tensor G d) (R : Finset V) :
    RegionBoundaryConfig (G := G) A R ≃
      RegionBoundaryConfig (G := G) A (Finset.univ \ (Finset.univ \ R)) :=
  Equiv.piCongrLeft' (fun e => Fin (A.bondDim e.1))
    (regionBoundaryEdgeDoubleComplEquiv (G := G) R).symm

/-- **The double-complement transport of the blocked tensor map.** The blocked
tensor map of `univ \ (univ \ R)` applied to a row `c`, evaluated at the
double-complement transport of `σ`, equals the blocked tensor map of `R` applied to
`c` precomposed with the double-complement boundary-configuration transport,
evaluated at `σ`.

Expanding both sides as boundary-configuration sums (`regionBlockedTensorMap_apply`)
and reindexing the left sum by the double-complement boundary-configuration
equivalence, each summand matches by the double-complement weight invariance
`regionBlockedWeight_doubleCompl`. -/
theorem regionBlockedTensorMap_doubleCompl (A : Tensor G d) (R : Finset V)
    (c : RegionBoundaryConfig (G := G) A (Finset.univ \ (Finset.univ \ R)) → ℂ)
    (σ : RegionPhysicalConfig (V := V) (d := d) R) :
    regionBlockedTensorMap (G := G) A (Finset.univ \ (Finset.univ \ R)) c
        (regionDoubleComplPhysicalConfig (V := V) (d := d) R σ) =
      regionBlockedTensorMap (G := G) A R
        (fun bdry => c (regionDoubleComplBoundaryConfig (G := G) A R bdry)) σ := by
  classical
  rw [regionBlockedTensorMap_apply, regionBlockedTensorMap_apply]
  rw [← Equiv.sum_comp (regionDoubleComplBoundaryConfigEquiv (G := G) A R)
    (fun w : RegionBoundaryConfig (G := G) A (Finset.univ \ (Finset.univ \ R)) =>
      c w • regionBlockedWeight (G := G) A (Finset.univ \ (Finset.univ \ R)) w
        (regionDoubleComplPhysicalConfig (V := V) (d := d) R σ))]
  refine Finset.sum_congr rfl (fun bdry _ => ?_)
  refine congrArg (c (regionDoubleComplBoundaryConfig (G := G) A R bdry) • ·) ?_
  exact regionBlockedWeight_doubleCompl A R bdry σ

/-! ### The σ-side region factorization of the first tensor's coefficient

The symmetric counterpart of the v-side factorization
`regionInsertedCoeff_eq_complement_blockedMap_B`. The first tensor's
region-inserted coefficient, as a function of the *region* physical configuration
`σ`, is the second tensor's *region* blocked tensor map applied to a row function.
The proof rereads the coefficient on the set complement `univ \ R` through the cast
identity `regionInsertedCoeff_eq_compl` (`Recovery6`), applies the v-side
factorization there (its complement is `univ \ (univ \ R)`), and transports the
`univ \ (univ \ R)` block back to `R` by `regionBlockedTensorMap_doubleCompl`. This
is the membership the σ-side read-off rests on: the σ-dependence runs through the
second tensor's region block. -/

/-- The σ-side row of the first tensor's region-inserted coefficient through the
second tensor's region block: the out-of-region endpoint operator of the first
tensor from `M.transpose`, applied to the second tensor's complement weight vector
at the reindexed boundary configuration, evaluated at the out-of-region endpoint
physical leg, with the boundary configuration transported across the double
complement.

This is the symmetric analogue of `vSideRow`, read off the cast identity
`regionInsertedCoeff_eq_compl` and the v-side factorization applied to the set
complement `univ \ R`.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, lines 254--582 of
`Papers/1804.04964/paper_normal.tex`. -/
noncomputable def complSideRow (A B : Tensor G d) (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (hvAout : LinearIndependent ℂ
      (A.component (regionBoundaryEdgeInVertex (G := G) (Finset.univ \ R)
        (regionBoundaryEdgeToCompl (G := G) R f))))
    (M : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ)
    (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R)) :
    RegionBoundaryConfig (G := G) B R → ℂ :=
  fun bdry =>
    (regionInsertionOp (G := G) A (Finset.univ \ R)
        (regionBoundaryEdgeToCompl (G := G) R f) hvAout M.transpose.transpose
        (regionWeightVec (G := G) B (Finset.univ \ R)
          (regionBoundaryEdgeToCompl (G := G) R f)
          ((regionComplementBoundaryConfigEquiv (G := G) B (Finset.univ \ R)).symm
            (regionDoubleComplBoundaryConfig (G := G) B R bdry)) τ))
      (τ ⟨regionBoundaryEdgeInVertex (G := G) (Finset.univ \ R)
          (regionBoundaryEdgeToCompl (G := G) R f),
        regionBoundaryEdgeInVertex_mem (G := G) (Finset.univ \ R)
          (regionBoundaryEdgeToCompl (G := G) R f)⟩)

/-- **The σ-side region factorization.** The first tensor's region-inserted
coefficient of `M`, as a function of the region physical configuration `σ`, is the
second tensor's region blocked tensor map applied to the σ-side row.

The cast identity `regionInsertedCoeff_eq_compl` rereads the coefficient on the set
complement `univ \ R`; the v-side factorization
`regionInsertedCoeff_eq_complement_blockedMap_B` applied there writes it as the
second tensor's `univ \ (univ \ R)` blocked tensor map of a row, evaluated at the
double-complement transport of `σ`; and `regionBlockedTensorMap_doubleCompl`
transports the `univ \ (univ \ R)` block back to `R`.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, lines 254--582 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem regionInsertedCoeff_eq_region_blockedMap_B (A B : Tensor G d) (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (hvAout : LinearIndependent ℂ
      (A.component (regionBoundaryEdgeInVertex (G := G) (Finset.univ \ R)
        (regionBoundaryEdgeToCompl (G := G) R f))))
    (hAB : SameState A B) (hDim : A.bondDim = B.bondDim)
    (M : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ)
    (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R)) :
    (fun σ : RegionPhysicalConfig (V := V) (d := d) R =>
        regionInsertedCoeff (G := G) A R f M σ τ) =
      regionBlockedTensorMap (G := G) B R (complSideRow (G := G) A B R f hvAout M τ) := by
  funext σ
  -- Reread the coefficient on the set complement `univ \ R`.
  rw [regionInsertedCoeff_eq_compl A R f M σ τ]
  -- The v-side factorization on `univ \ R`, evaluated at the double-complement of `σ`.
  have hv := congrFun
    (regionInsertedCoeff_eq_complement_blockedMap_B A B (Finset.univ \ R)
      (regionBoundaryEdgeToCompl (G := G) R f) hvAout hAB hDim M.transpose τ)
    (regionDoubleComplPhysicalConfig (V := V) (d := d) R σ)
  rw [hv]
  -- Transport the `univ \ (univ \ R)` block back to `R`.
  rw [regionBlockedTensorMap_doubleCompl B R]
  rfl

/-! ### The double factorization of the first tensor's coefficient

Combining the v-side and σ-side factorizations, the first tensor's region-inserted
coefficient factors through both blocked endpoints of the second tensor at once:
there is a doubly-indexed coefficient `K` with

```
coeff_A M σ τ = ∑_μ ∑_ν' K μ ν' · WB_R(μ, σ) · WB_Rc(ν', τ).
```

The region row `complSideRow τ` reads the coefficient off the region block
(σ-side); as a function of `τ`, each region-row coordinate lies in the image of the
second tensor's complement block (a finite linear combination of the v-side
complement-image coefficients), so the complement left inverse reads off `K`. This
is the membership the read-off rests on. -/

/-- The region row read off the σ-side factorization through the second tensor's
region block: `regionRowB A B R f hvAout M τ = regionBlockedLeftInverse B R hRB`
applied to the first tensor's coefficient viewed as a function of `σ`. By the
σ-side factorization it equals `complSideRow A B R f hvAout M τ`. -/
noncomputable def regionRowB (A B : Tensor G d) (R : Finset V)
    (hRB : RegionBlockedTensorInjective (G := G) B R)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (M : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ)
    (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R)) :
    RegionBoundaryConfig (G := G) B R → ℂ :=
  regionBlockedLeftInverse (G := G) B R hRB (fun σ => regionInsertedCoeff (G := G) A R f M σ τ)

/-- The region row equals the σ-side row. This is the σ-side read-off: the second
tensor's region blocked left inverse applied to the first tensor's coefficient
recovers the σ-side row `complSideRow`. -/
theorem regionRowB_eq_complSideRow (A B : Tensor G d) (R : Finset V)
    (hRB : RegionBlockedTensorInjective (G := G) B R)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (hvAout : LinearIndependent ℂ
      (A.component (regionBoundaryEdgeInVertex (G := G) (Finset.univ \ R)
        (regionBoundaryEdgeToCompl (G := G) R f))))
    (hAB : SameState A B) (hDim : A.bondDim = B.bondDim)
    (M : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ)
    (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R)) :
    regionRowB (G := G) A B R hRB f M τ = complSideRow (G := G) A B R f hvAout M τ := by
  rw [regionRowB, regionInsertedCoeff_eq_region_blockedMap_B A B R f hvAout hAB hDim M τ,
    regionBlockedLeftInverse_apply_regionBlockedTensorMap]

/-- **Membership of the region row in the complement block image.** For each region
boundary configuration `μ` of the second tensor, the region-row coordinate
`regionRowB … τ μ`, as a function of the complement physical configuration `τ`,
lies in the image of the second tensor's complement blocked tensor map.

Writing the first tensor's coefficient, as a function of `σ`, over the standard
basis, the region left inverse is linear, so the region-row coordinate is a finite
linear combination of the coefficients `fun τ => coeff_A M σ' τ`; each of these lies
in the complement block image by the v-side factorization
`regionInsertedCoeff_eq_complement_blockedMap_vSideRow`, and the image is a
submodule. -/
theorem regionRowB_mem_range (A B : Tensor G d) (R : Finset V)
    (hRB : RegionBlockedTensorInjective (G := G) B R)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (hvA : LinearIndependent ℂ (A.component (regionBoundaryEdgeInVertex (G := G) R f)))
    (hAB : SameState A B) (hDim : A.bondDim = B.bondDim)
    (M : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ)
    (μ : RegionBoundaryConfig (G := G) B R) :
    (fun τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R) =>
        regionRowB (G := G) A B R hRB f M τ μ) ∈
      LinearMap.range (regionBlockedTensorMap (G := G) B (Finset.univ \ R)) := by
  classical
  -- Each coefficient `fun τ => coeff_A M σ' τ` lies in the complement block image.
  have hmem : ∀ σ' : RegionPhysicalConfig (V := V) (d := d) R,
      (fun τ => regionInsertedCoeff (G := G) A R f M σ' τ) ∈
        LinearMap.range (regionBlockedTensorMap (G := G) B (Finset.univ \ R)) := by
    intro σ'
    rw [regionInsertedCoeff_eq_complement_blockedMap_vSideRow A B R f hvA hAB hDim M σ']
    exact LinearMap.mem_range_self _ _
  -- The region-row coordinate is the linear combination of these over the basis of `σ`.
  have hexpand : (fun τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R) =>
        regionRowB (G := G) A B R hRB f M τ μ) =
      ∑ σ' : RegionPhysicalConfig (V := V) (d := d) R,
        (regionBlockedLeftInverse (G := G) B R hRB
            (fun σ => if σ = σ' then (1 : ℂ) else 0) μ) •
          (fun τ => regionInsertedCoeff (G := G) A R f M σ' τ) := by
    funext τ
    rw [regionRowB]
    rw [show (fun σ => regionInsertedCoeff (G := G) A R f M σ τ) =
        ∑ σ' : RegionPhysicalConfig (V := V) (d := d) R,
          regionInsertedCoeff (G := G) A R f M σ' τ •
            (fun σ => if σ = σ' then (1 : ℂ) else 0) from ?_]
    · rw [map_sum]
      simp only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_comm]
    · funext σ
      rw [Finset.sum_apply]
      rw [Finset.sum_eq_single σ]
      · rw [Pi.smul_apply, if_pos rfl, smul_eq_mul, mul_one]
      · intro σ'' _ hne
        rw [Pi.smul_apply, if_neg (Ne.symm hne), smul_zero]
      · intro hσ; exact absurd (Finset.mem_univ σ) hσ
  rw [hexpand]
  refine Submodule.sum_mem _ (fun σ' _ => ?_)
  exact Submodule.smul_mem _ _ (hmem σ')

/-- The doubly-indexed transfer coefficient: the second tensor's complement blocked
left inverse applied to the region-row coordinate viewed as a function of the
complement physical configuration. By the membership
`regionRowB_mem_range`, it reproduces the region-row coordinate against the
complement block. -/
noncomputable def transferCoeff (A B : Tensor G d) (R : Finset V)
    (hRB : RegionBlockedTensorInjective (G := G) B R)
    (hCB : RegionBlockedTensorInjective (G := G) B (Finset.univ \ R))
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (M : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ)
    (μ : RegionBoundaryConfig (G := G) B R) :
    RegionBoundaryConfig (G := G) B (Finset.univ \ R) → ℂ :=
  regionBlockedLeftInverse (G := G) B (Finset.univ \ R) hCB
    (fun τ => regionRowB (G := G) A B R hRB f M τ μ)

/-- The region-row coordinate, as a function of the complement physical
configuration, is the second tensor's complement blocked tensor map applied to the
transfer coefficient. This is the complement read-off from the membership
`regionRowB_mem_range`. -/
theorem regionRowB_eq_complement_blockedMap (A B : Tensor G d) (R : Finset V)
    (hRB : RegionBlockedTensorInjective (G := G) B R)
    (hCB : RegionBlockedTensorInjective (G := G) B (Finset.univ \ R))
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (hvA : LinearIndependent ℂ (A.component (regionBoundaryEdgeInVertex (G := G) R f)))
    (hAB : SameState A B) (hDim : A.bondDim = B.bondDim)
    (M : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ)
    (μ : RegionBoundaryConfig (G := G) B R) :
    (fun τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R) =>
        regionRowB (G := G) A B R hRB f M τ μ) =
      regionBlockedTensorMap (G := G) B (Finset.univ \ R)
        (transferCoeff (G := G) A B R hRB hCB f M μ) := by
  obtain ⟨c, hc⟩ := regionRowB_mem_range A B R hRB f hvA hAB hDim M μ
  rw [transferCoeff, ← hc, regionBlockedLeftInverse_apply_regionBlockedTensorMap]

/-- **The double factorization.** The first tensor's region-inserted coefficient of
`M` is the doubly-blocked contraction of the second tensor: a boundary-configuration
double sum of the transfer coefficient against the second tensor's region and
complement blocked weights.

The σ-side factorization writes the coefficient as the second tensor's region
blocked tensor map of the region row; the region row, as a function of the
complement physical configuration, is the second tensor's complement blocked tensor
map of the transfer coefficient (`regionRowB_eq_complement_blockedMap`). Expanding
both blocked tensor maps gives the double sum.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, lines 254--582 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem regionInsertedCoeff_eq_doubleSum_transferCoeff (A B : Tensor G d) (R : Finset V)
    (hRB : RegionBlockedTensorInjective (G := G) B R)
    (hCB : RegionBlockedTensorInjective (G := G) B (Finset.univ \ R))
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (hvA : LinearIndependent ℂ (A.component (regionBoundaryEdgeInVertex (G := G) R f)))
    (hvAout : LinearIndependent ℂ
      (A.component (regionBoundaryEdgeInVertex (G := G) (Finset.univ \ R)
        (regionBoundaryEdgeToCompl (G := G) R f))))
    (hAB : SameState A B) (hDim : A.bondDim = B.bondDim)
    (M : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ)
    (σ : RegionPhysicalConfig (V := V) (d := d) R)
    (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R)) :
    regionInsertedCoeff (G := G) A R f M σ τ =
      ∑ μ : RegionBoundaryConfig (G := G) B R,
        ∑ ν' : RegionBoundaryConfig (G := G) B (Finset.univ \ R),
          transferCoeff (G := G) A B R hRB hCB f M μ ν' *
            regionBlockedWeight (G := G) B (Finset.univ \ R) ν' τ *
            regionBlockedWeight (G := G) B R μ σ := by
  -- The σ-side factorization.
  have hσ := congrFun
    (regionInsertedCoeff_eq_region_blockedMap_B A B R f hvAout hAB hDim M τ) σ
  rw [hσ, regionBlockedTensorMap_apply]
  refine Finset.sum_congr rfl (fun μ _ => ?_)
  -- `complSideRow τ μ` is the region row, which is the complement blocked map of `K`.
  rw [← regionRowB_eq_complSideRow A B R hRB f hvAout hAB hDim M τ]
  have hrow := congrFun
    (regionRowB_eq_complement_blockedMap A B R hRB hCB f hvA hAB hDim M μ) τ
  rw [hrow, regionBlockedTensorMap_apply, smul_eq_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun ν' _ => ?_)
  rw [smul_eq_mul]

/-! ### The coefficient transfer from the incident-matrix form of the transfer
coefficient

If the transfer coefficient `transferCoeff` has the incident-matrix coupling form
of a single matrix `N` on the boundary bond `f` — coupling only the `f`-legs of the
two boundary configurations and contracting the residual legs by the identity
(`SameAwayFromBond`) — then the first tensor's region-inserted coefficient of `M`
equals the second tensor's of `N`. This is the bridge from the reconcile structure
to the coefficient transfer. -/

open scoped Classical in
/-- **The coefficient transfer from the incident-matrix form.** If there is a matrix
`N` on the second tensor's bond whose incident-matrix coupling form reproduces the
transfer coefficient, then the first tensor's region-inserted coefficient of `M`
equals the second tensor's of `N` at every physical configuration.

The double factorization `regionInsertedCoeff_eq_doubleSum_transferCoeff` writes the
first tensor's coefficient as the double sum of the transfer coefficient against the
second tensor's region and complement blocked weights; substituting the
incident-matrix form and reindexing the complement boundary-configuration sum by the
complement boundary-configuration equivalence yields the explicit double-sum form of
the second tensor's region-inserted coefficient (`regionInsertedCoeff_eq`).

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, lines 254--582 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem regionInsertedCoeff_eq_of_transferCoeff_form (A B : Tensor G d) (R : Finset V)
    (hRB : RegionBlockedTensorInjective (G := G) B R)
    (hCB : RegionBlockedTensorInjective (G := G) B (Finset.univ \ R))
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (hvA : LinearIndependent ℂ (A.component (regionBoundaryEdgeInVertex (G := G) R f)))
    (hvAout : LinearIndependent ℂ
      (A.component (regionBoundaryEdgeInVertex (G := G) (Finset.univ \ R)
        (regionBoundaryEdgeToCompl (G := G) R f))))
    (hAB : SameState A B) (hDim : A.bondDim = B.bondDim)
    (M : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ)
    (N : Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ)
    (hform : ∀ (μ : RegionBoundaryConfig (G := G) B R)
        (ν' : RegionBoundaryConfig (G := G) B (Finset.univ \ R)),
      transferCoeff (G := G) A B R hRB hCB f M μ ν' =
        (if SameAwayFromBond f μ
              ((regionComplementBoundaryConfigEquiv (G := G) B R).symm ν') then
            N (μ f) (((regionComplementBoundaryConfigEquiv (G := G) B R).symm ν') f) else 0))
    (σ : RegionPhysicalConfig (V := V) (d := d) R)
    (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R)) :
    regionInsertedCoeff (G := G) A R f M σ τ =
      regionInsertedCoeff (G := G) B R f N σ τ := by
  classical
  rw [regionInsertedCoeff_eq_doubleSum_transferCoeff A B R hRB hCB f hvA hvAout hAB hDim M σ τ,
    regionInsertedCoeff_eq]
  -- Reindex the second tensor's inner `ν`-sum by the complement boundary-config equivalence.
  set E := regionComplementBoundaryConfigEquiv (G := G) B R with hE
  rw [show (∑ μ : RegionBoundaryConfig (G := G) B R,
        ∑ ν : RegionBoundaryConfig (G := G) B R,
          (if SameAwayFromBond f μ ν then N (μ f) (ν f) else 0) *
            regionBlockedWeight (G := G) B R μ σ *
            regionBlockedWeight (G := G) B (Finset.univ \ R)
              (regionComplementBoundaryConfig (G := G) B R ν) τ) =
      ∑ μ : RegionBoundaryConfig (G := G) B R,
        ∑ ν' : RegionBoundaryConfig (G := G) B (Finset.univ \ R),
          (if SameAwayFromBond f μ (E.symm ν') then N (μ f) ((E.symm ν') f) else 0) *
            regionBlockedWeight (G := G) B R μ σ *
            regionBlockedWeight (G := G) B (Finset.univ \ R) ν' τ from ?_]
  · refine Finset.sum_congr rfl (fun μ _ => Finset.sum_congr rfl (fun ν' _ => ?_))
    rw [hform μ ν']
    ring
  · refine Finset.sum_congr rfl (fun μ _ => ?_)
    rw [← Equiv.sum_comp E
      (fun ν' : RegionBoundaryConfig (G := G) B (Finset.univ \ R) =>
        (if SameAwayFromBond f μ (E.symm ν') then N (μ f) ((E.symm ν') f) else 0) *
          regionBlockedWeight (G := G) B R μ σ *
          regionBlockedWeight (G := G) B (Finset.univ \ R) ν' τ)]
    refine Finset.sum_congr rfl (fun ν _ => ?_)
    rw [hE, Equiv.symm_apply_apply, regionComplementBoundaryConfigEquiv_apply]

/-! ### The v-side row through the transfer coefficient

The v-side row, as a function of the region physical configuration, is the second
tensor's region blocked tensor map applied to the transfer coefficient at the fixed
complement boundary configuration. This relates the two read-offs: the v-side
complement read-off and the σ-side region read-off agree on the transfer
coefficient. -/

/-- **The v-side row is the region blocked map of the transfer coefficient.** The
v-side row at the complement boundary configuration `ν'`, as a function of the region
physical configuration, is the second tensor's region blocked tensor map applied to
the transfer-coefficient column `fun μ => transferCoeff … μ ν'`.

Both the v-side factorization and the double factorization write the first tensor's
coefficient against the second tensor's complement block; linear independence of the
complement blocked weights (`hCB`) forces the two complement coefficients to agree.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, lines 254--582 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem vSideRow_eq_region_blockedMap_transferCoeff (A B : Tensor G d) (R : Finset V)
    (hRB : RegionBlockedTensorInjective (G := G) B R)
    (hCB : RegionBlockedTensorInjective (G := G) B (Finset.univ \ R))
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (hvA : LinearIndependent ℂ (A.component (regionBoundaryEdgeInVertex (G := G) R f)))
    (hvAout : LinearIndependent ℂ
      (A.component (regionBoundaryEdgeInVertex (G := G) (Finset.univ \ R)
        (regionBoundaryEdgeToCompl (G := G) R f))))
    (hAB : SameState A B) (hDim : A.bondDim = B.bondDim)
    (M : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ)
    (ν' : RegionBoundaryConfig (G := G) B (Finset.univ \ R)) :
    (fun σ : RegionPhysicalConfig (V := V) (d := d) R =>
        vSideRow (G := G) A B R f hvA M σ ν') =
      regionBlockedTensorMap (G := G) B R
        (fun μ => transferCoeff (G := G) A B R hRB hCB f M μ ν') := by
  classical
  funext σ
  -- The v-side row is the complement read-off of `coeff_A` at `σ`.
  have hvrow : vSideRow (G := G) A B R f hvA M σ =
      regionBlockedLeftInverse (G := G) B (Finset.univ \ R) hCB
        (fun τ => regionInsertedCoeff (G := G) A R f M σ τ) := by
    rw [regionInsertedCoeff_eq_complement_blockedMap_vSideRow A B R f hvA hAB hDim M σ,
      regionBlockedLeftInverse_apply_regionBlockedTensorMap]
  -- The double factorization writes `coeff_A` at `σ` through the complement block too.
  have hdouble : (fun τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R) =>
        regionInsertedCoeff (G := G) A R f M σ τ) =
      regionBlockedTensorMap (G := G) B (Finset.univ \ R)
        (fun ν'' => regionBlockedTensorMap (G := G) B R
          (fun μ => transferCoeff (G := G) A B R hRB hCB f M μ ν'') σ) := by
    funext τ
    rw [regionInsertedCoeff_eq_doubleSum_transferCoeff A B R hRB hCB f hvA hvAout hAB hDim M σ τ,
      regionBlockedTensorMap_apply, Finset.sum_comm]
    refine Finset.sum_congr rfl (fun ν'' _ => ?_)
    rw [regionBlockedTensorMap_apply, smul_eq_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun μ _ => ?_)
    rw [smul_eq_mul]
    ring
  -- The complement read-off of `coeff_A` at `σ` is the inner region blocked map.
  have hread : regionBlockedLeftInverse (G := G) B (Finset.univ \ R) hCB
        (fun τ => regionInsertedCoeff (G := G) A R f M σ τ) =
      (fun ν'' => regionBlockedTensorMap (G := G) B R
        (fun μ => transferCoeff (G := G) A B R hRB hCB f M μ ν'') σ) := by
    rw [hdouble, regionBlockedLeftInverse_apply_regionBlockedTensorMap]
  rw [hvrow, hread]

end PEPS
end TNLean
