import TNLean.PEPS.RegionBlock.Recovery8

/-!
# Region physical-to-virtual recovery: the region resonate reconcile

This file proves the region resonate reconcile `RegionResonateReconcile`
(`TNLean.PEPS.RegionBlock.Recovery8`), the single remaining mathematical content of
remaining obligation 4 of `docs/paper-gaps/peps_normal_ft_section3_route.tex`: for
every inserted matrix `M`, the virtual pullback
`W := localVirtualOpOfPhysicalOpAt B hvB (regionInsertionOp A R f hvA M.transpose)`
of the transferred in-region endpoint operator is of incident-matrix form on the
boundary leg `f`.

## Strategy

The region port of `physical_to_virtual_insertion`
(`TNLean.PEPS.InsertionRealization`). The two "endpoints" are the blocked regions
`R` and `univ \ R`, joined by the single boundary edge `f`; there is no middle
block (the region/complement split has empty interior). The inversion tool is the
blocked-region left inverse `regionBlockedLeftInverse` (`Recovery5`) applied to
each block, not the per-vertex split of the edge proof.

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

/-! ### The leg-wise pin of the in-region endpoint operator

The non-circular endpoint pin `regionInsertionOp_regionStateVec_pin` evaluates the
in-region endpoint operator of the first tensor, applied to the second tensor's
closed state vector, only at the endpoint physical leg `σ v`. Updating the
in-region physical configuration at the endpoint vertex `v` to an arbitrary value
`a` leaves the closed state vector unchanged (`regionStateVec_update_vmem`) while
moving the evaluation leg to `a`, so the pin extends to every leg. This reads the
*whole output vector* of the in-region endpoint operator on the second tensor's
state vector as the region-inserted coefficient of the first tensor, scanned over
the endpoint physical configuration. -/

/-- **The leg-wise pin of the in-region endpoint operator.** The in-region endpoint
operator of the first tensor from `M.transpose`, applied to the second tensor's
closed state vector and evaluated at an arbitrary physical leg `a`, recovers the
first tensor's region-inserted coefficient of `M` at the endpoint physical
configuration updated to `a`, up to the interior bond product.

This is the non-circular endpoint pin `regionInsertionOp_regionStateVec_pin`
applied to `σ` updated at the endpoint vertex `v` to the value `a`: the state
vector is unchanged by that update (`regionStateVec_update_vmem`), and the updated
endpoint leg reads `a`.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, lines 254--582 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem regionInsertionOp_regionStateVec_pin_leg (A B : Tensor G d) (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (hvA : LinearIndependent ℂ (A.component (regionBoundaryEdgeInVertex (G := G) R f)))
    (hAB : SameState A B)
    (M : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ)
    (σ : RegionPhysicalConfig (V := V) (d := d) R)
    (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R)) (a : Fin d) :
    regionInteriorBondProd (G := G) A R •
        (regionInsertionOp (G := G) A R f hvA M.transpose
          (regionStateVec (G := G) B R f σ τ)) a =
      regionInsertedCoeff (G := G) A R f M
        (Function.update σ ⟨regionBoundaryEdgeInVertex (G := G) R f,
          regionBoundaryEdgeInVertex_mem (G := G) R f⟩ a) τ := by
  have hpin := regionInsertionOp_regionStateVec_pin A B R f hvA hAB M
    (Function.update σ ⟨regionBoundaryEdgeInVertex (G := G) R f,
      regionBoundaryEdgeInVertex_mem (G := G) R f⟩ a) τ
  rw [regionStateVec_update_vmem B R f σ τ a] at hpin
  rw [← hpin]
  congr 2
  rw [Function.update_self]

end PEPS
end TNLean
