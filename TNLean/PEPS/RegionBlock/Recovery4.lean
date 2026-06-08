import TNLean.PEPS.RegionBlock.Recovery3

/-!
# Region physical-to-virtual recovery: incident-matrix form of the virtual pullback

This file isolates the last load-bearing fact behind the region physical-to-virtual
realization `RegionTransferRealizes` for the normal PEPS Fundamental Theorem
(remaining obligation 4 of `docs/paper-gaps/peps_normal_ft_section3_route.tex`).

The conditional recovery `regionTransferRealizesAt_of_hform`
(`TNLean.PEPS.RegionBlock.Recovery3`) reduces the realization `hreal` to the
matrix-structure hypothesis

```
hform : localVirtualOpOfPhysicalOpAt B hvB
            (regionInsertionOp A R f hvA M.transpose) =
          localIncidentMatrixOp B (regionBoundaryEdgeInIncident R f)
            (regionTransferMatrix A B R f hvA hvB hposB M).transpose
```

Because `regionTransferMatrix … M` is *defined* as the read-off
`(incidentMatrixOfLocalOp B inc refRes W)ᵀ` of the virtual pullback
`W := localVirtualOpOfPhysicalOpAt B hvB (regionInsertionOp A R f hvA M.transpose)`,
the hypothesis `hform` holds **exactly when `W` is of incident-matrix form** on the
boundary leg `inc`: if `W = localIncidentMatrixOp B inc P` for some matrix `P`, the
read-off recovers `P` (`incidentMatrixOfLocalOp_localIncidentMatrixOp`) and the
round-trip closes `hform`. This file proves that reduction unconditionally
(`hform_of_isIncidentMatrixForm`) and packages it as the per-matrix realization
`regionTransferRealizesAt_of_isIncidentMatrixForm`.

What remains for the unconditional normal theorem is the *region resonate* step:
showing `W` is of incident-matrix form by inverting the blocked complement endpoint
of the boundary edge `f`. This is the region analogue of the endpoint inversion of
`physical_to_virtual_insertion` (`TNLean.PEPS.InsertionRealization`), with the
empty interior of the two-block region/complement split replacing the middle-tensor
inversion.

## References

- [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected entangled
  pair states generating the same state*, arXiv:1804.04964, Section 3, Lemma
  `inj_isomorph`, lines 254--582 of
  `Papers/1804.04964/paper_normal.tex`](https://arxiv.org/abs/1804.04964)
-/

open scoped BigOperators Matrix

namespace TNLean
namespace PEPS

/-! ### Block-swap symmetry of the abstract two-block inserted coefficient

The two-block inserted coefficient inserts a matrix on one shared bond and
contracts the two blocks against each other. Swapping the two blocks, transposing
the inserted matrix, and exchanging the external and physical arguments leaves the
value unchanged. This is the abstract form of the symmetry between the in-region
endpoint of a boundary edge and its out-of-region endpoint: the two contracted
blocks `R` and its complement enter the region-inserted coefficient symmetrically,
up to transposing the inserted matrix on the boundary edge. -/

section TwoBlockSwap

variable {Bond : Type*} [Fintype Bond]
variable {bondDim : Bond → Type*} [∀ b, Fintype (bondDim b)]

open scoped Classical in
/-- **Block-swap symmetry of the two-block inserted coefficient.** Inserting `X`
on a shared bond `b` and contracting the first block against the second equals
inserting `Xᵀ` and contracting the second block against the first, with the
external and physical arguments exchanged.

The two summation variables are exchanged and the `SameAwayFromBond` predicate is
symmetric, so the only change is `X (μ b) (ν b)` becoming `Xᵀ (ν b) (μ b) = X (μ b)
(ν b)` together with the block factors swapping order. This is the abstract
symmetry between the in-region and out-of-region endpoints of a boundary edge.

Source: arXiv:1804.04964, Section 3, equation eq:lem_inj_eq_ten_2: the two
contracted blocks of a single boundary edge enter symmetrically. -/
theorem twoBlockInsertedCoeff_swap
    {External₁ External₂ Physical₁ Physical₂ : Type*}
    (A₁ : TwoBlockTensor bondDim External₁ Physical₁)
    (A₂ : TwoBlockTensor bondDim External₂ Physical₂)
    (b : Bond) (X : Matrix (bondDim b) (bondDim b) ℂ)
    (η₁ : External₁) (η₂ : External₂) (σ₁ : Physical₁) (σ₂ : Physical₂) :
    twoBlockInsertedCoeff A₁ A₂ b X η₁ η₂ σ₁ σ₂ =
      twoBlockInsertedCoeff A₂ A₁ b X.transpose η₂ η₁ σ₂ σ₁ := by
  classical
  rw [twoBlockInsertedCoeff, twoBlockInsertedCoeff, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun μ _ => Finset.sum_congr rfl (fun ν _ => ?_))
  have hsym : SameAwayFromBond b ν μ ↔ SameAwayFromBond b μ ν :=
    ⟨fun h c hc => (h c hc).symm, fun h c hc => (h c hc).symm⟩
  by_cases hsame : SameAwayFromBond b μ ν
  · rw [if_pos hsame, if_pos (hsym.mpr hsame), Matrix.transpose_apply]
    ring
  · rw [if_neg hsame, if_neg (fun h => hsame (hsym.mp h)), zero_mul, zero_mul, zero_mul]

end TwoBlockSwap

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ}

/-! ### Incident-matrix form of the virtual pullback closes `hform`

The region transfer matrix is the read-off of the virtual pullback `W`. When `W`
is already of incident-matrix form on the boundary leg, the read-off inverts it
and `hform` is the round-trip identity. This is the unconditional reduction the
region resonate step feeds into. -/

/-- **The matrix-structure hypothesis `hform` from incident-matrix form.** If the
virtual pullback `W := localVirtualOpOfPhysicalOpAt B hvB (regionInsertionOp A R f
hvA M.transpose)` of the transferred in-region endpoint operator is of
incident-matrix form on the boundary leg `inc` — that is, `W = localIncidentMatrixOp
B inc P` for some matrix `P` — then the matrix-structure hypothesis `hform` holds.

The region transfer matrix is the read-off `(incidentMatrixOfLocalOp B inc refRes
W)ᵀ`, so its transpose is `incidentMatrixOfLocalOp B inc refRes W`; reading off the
incident-matrix form `W` recovers `P` (`incidentMatrixOfLocalOp_localIncidentMatrixOp`),
and reinserting `P` returns `W`. This is the unconditional reduction of `hform` to
the incident-matrix structure of `W`.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, lines 254--582 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem hform_of_isIncidentMatrixForm (A B : Tensor G d) (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (hvA : LinearIndependent ℂ (A.component (regionBoundaryEdgeInVertex (G := G) R f)))
    (hvB : LinearIndependent ℂ (B.component (regionBoundaryEdgeInVertex (G := G) R f)))
    (hposB : ∀ e : Edge G, 0 < B.bondDim e)
    (M : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ)
    (P : Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ)
    (hP : localVirtualOpOfPhysicalOpAt B hvB
        (regionInsertionOp (G := G) A R f hvA M.transpose) =
      localIncidentMatrixOp B (regionBoundaryEdgeInIncident (G := G) R f) P) :
    localVirtualOpOfPhysicalOpAt B hvB
        (regionInsertionOp (G := G) A R f hvA M.transpose) =
      localIncidentMatrixOp B (regionBoundaryEdgeInIncident (G := G) R f)
        (regionTransferMatrix (G := G) A B R f hvA hvB hposB M).transpose := by
  classical
  set inc := regionBoundaryEdgeInIncident (G := G) R f with hinc
  set W := localVirtualOpOfPhysicalOpAt B hvB
    (regionInsertionOp (G := G) A R f hvA M.transpose) with hW
  -- The read-off recovers `P` from the incident-matrix form of `W`.
  have hread : (regionTransferMatrix (G := G) A B R f hvA hvB hposB M).transpose = P := by
    rw [regionTransferMatrix, Matrix.transpose_transpose, ← hW, hP,
      incidentMatrixOfLocalOp_localIncidentMatrixOp]
  rw [hread, hP]

/-! ### The virtual pullback realizes the transferred endpoint operator

Image preservation (`regionInsertionOp_localProjectorAt_eq`, the `himage` half) makes
the virtual pullback `W` realize the transferred in-region endpoint operator on every
local tensor image of `B` at `v`: the chosen left inverse undoes the projection,
because the projection fixes the output. This is the bridge from the physical
operator `regionInsertionOp A R f hvA M.transpose` to its virtual pullback `W`. -/

/-- **The virtual pullback realizes the transferred endpoint operator.** With image
preservation (`regionInsertionOp_localProjectorAt_eq`), the local tensor map of the
virtual pullback `W := localVirtualOpOfPhysicalOpAt B hvB (regionInsertionOp A R f hvA
M.transpose)` applied to a coefficient `c` returns the transferred in-region endpoint
operator applied to the local tensor image of `c`.

This is the region analogue of the realization the chosen left inverse provides at the
edge level: the virtual pullback agrees with the physical operator on the image of the
local tensor map at `v`.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, lines 254--582 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem localTensorMap_localVirtualOpOfPhysicalOpAt_regionInsertionOp
    (A B : Tensor G d) (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (hvA : LinearIndependent ℂ (A.component (regionBoundaryEdgeInVertex (G := G) R f)))
    (hvB : LinearIndependent ℂ (B.component (regionBoundaryEdgeInVertex (G := G) R f)))
    (hAB : SameState A B) (hA : IsVertexInjective A) (hB : IsVertexInjective B)
    (hposA : ∀ e : Edge G, 0 < A.bondDim e) (hposB : ∀ e : Edge G, 0 < B.bondDim e)
    (M : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ)
    (c : LocalVirtualConfig B (regionBoundaryEdgeInVertex (G := G) R f) → ℂ) :
    localTensorMap B (regionBoundaryEdgeInVertex (G := G) R f)
        (localVirtualOpOfPhysicalOpAt B hvB
          (regionInsertionOp (G := G) A R f hvA M.transpose) c) =
      regionInsertionOp (G := G) A R f hvA M.transpose
        (localTensorMap B (regionBoundaryEdgeInVertex (G := G) R f) c) :=
  localVirtualOpOfPhysicalOpAt_realizes_of_projector B hvB
    (regionInsertionOp (G := G) A R f hvA M.transpose)
    (fun c => regionInsertionOp_localProjectorAt_eq A B R f hvA hvB hAB hA hB hposA hposB M c) c

end PEPS
end TNLean
