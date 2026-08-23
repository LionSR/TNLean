/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.TorusWindowPeeling.WindowIndependence

/-!
# Insertion of a virtual operation on an interior bond

Let `e` be a bond whose two endpoints lie in a region `R`.  A virtual operation `X` on `e`
can be represented by an insert on `R` as follows.  First regard `e` as a boundary edge of
the singleton containing its ordered left endpoint and apply the boundary-bond insert there.
Then adjoin the genuine tensors at the remaining vertices of `R` by `extendInsert`.  The
extension identity preserves the resulting closed state.  Finally, the ratio of the two
non-boundary bond products changes its normalization from that of the singleton to that of
`R`.

Thus the assembled deformed state is
\[
  p_A(R)\,E_A(e,\omega,X),
\]
where `p_A(R)` is the non-boundary bond product and `E_A` is the coefficient obtained by
inserting `X` on `e` in the closed network.  The singleton contains the ordered left endpoint,
so no transpose is introduced.  This supplies the insert used for the interior-bond case of the
paper's staircase.  For an injective window, `physicalOpOfRegionInsert_realizes` separately turns
this insert into an actual physical operator on the window.  The closed-state extension identity
below supplies the common-state calculation; it is not being used by itself as a local physical
realization.  The extension uses the same contraction operation of adjoining genuine tensors that
occurs later in the sketch's end-region comparison.

## References

* [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected entangled pair
  states generating the same state*, arXiv:1804.04964, the virtual-operation realization
  at lines 2320--2321 and the later tensor-adjoining comparison at lines 2415--2444 of
  `Papers/1804.04964/paper_normal.tex`](https://arxiv.org/abs/1804.04964).
-/

open scoped BigOperators Matrix

namespace TNLean
namespace PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ}

omit [Fintype V] [DecidableRel G.Adj] in
private theorem edgeLeftVertices_subset_of_mem (e : Edge G) {R : Finset V}
    (hleft : e.1.1 ∈ R) : edgeLeftVertices e ⊆ R := by
  intro v hv
  rw [mem_edgeLeftVertices] at hv
  simpa [hv] using hleft

omit [Fintype V] [DecidableRel G.Adj] in
private theorem isRegionBoundaryEdge_edgeLeftVertices (e : Edge G) :
    IsRegionBoundaryEdge (G := G) (edgeLeftVertices e) e := by
  rw [IsRegionBoundaryEdge]
  left
  constructor
  · simp [edgeLeftVertices]
  · simpa [edgeLeftVertices] using (edgeLeft_ne_edgeRight e).symm

/-- The insert on a region `R` representing a virtual operation `X` on an interior bond `e`.

The operation is first inserted on the singleton containing the ordered left endpoint of `e`.
The remaining genuine tensors of `R` are then adjoined by `extendInsert`, and the result is
rescaled from the singleton's non-boundary bond product to that of `R`.

Source: arXiv:1804.04964, the virtual-operation realization at lines 2320--2321 of
`Papers/1804.04964/paper_normal.tex`; compare the tensor adjoining at lines 2415--2444. -/
noncomputable def interiorBondInsertedRegionInsert (A : Tensor G d) (R : Finset V)
    (e : Edge G) (hends : e.1.1 ∈ R ∧ e.1.2 ∈ R)
    (X : Matrix (Fin (A.bondDim e)) (Fin (A.bondDim e)) ℂ) :
    RegionInsert (G := G) (d := d) A R :=
  let hsub : edgeLeftVertices e ⊆ R := edgeLeftVertices_subset_of_mem e hends.1
  let hbd : IsRegionBoundaryEdge (G := G) (edgeLeftVertices e) e :=
    isRegionBoundaryEdge_edgeLeftVertices e
  fun ν σ ↦
    (regionInteriorBondProd (G := G) A R : ℂ) *
      (regionInteriorBondProd (G := G) A (edgeLeftVertices e) : ℂ)⁻¹ *
        extendInsert (G := G) hsub
          (bondInsertedRegionInsert (G := G) A (edgeLeftVertices e) ⟨e, hbd⟩ X) ν σ

/-- The assembled state of an interior-bond insert is the non-boundary bond product of the
region times the closed-network coefficient with the same virtual operation on that bond:
\[
  \Psi^{\mathrm{as}}_{A,R,I^{\mathrm{int}}_{R,e,X}}(\omega)
  = p_A(R) E_A(e,\omega,X).
\]

The extension identity adjoins the genuine tensors without changing the closed state.  The
normalizing ratio cancels the singleton's non-boundary bond product.  Since the singleton
contains the ordered left endpoint of `e`, the boundary orientation is the identity.

This is a closed-state identity.  The open-boundary physical realization on an injective region is
`physicalOpOfRegionInsert_realizes` in `TNLean/PEPS/RegionBlock/PhysicalOperation.lean`.

Source: arXiv:1804.04964, the virtual-operation realization at lines 2320--2321 of
`Papers/1804.04964/paper_normal.tex`; compare the tensor adjoining at lines 2415--2444. -/
theorem deformedRegionStateAssembled_interiorBondInserted_eq_smul_edgeInsertedCoeff
    (A : Tensor G d) (R : Finset V) (e : Edge G)
    (hends : e.1.1 ∈ R ∧ e.1.2 ∈ R)
    (hpos : ∀ f : Edge G, 0 < A.bondDim f)
    (X : Matrix (Fin (A.bondDim e)) (Fin (A.bondDim e)) ℂ) (cfg : V → Fin d) :
    deformedRegionStateAssembled (G := G) A R
        (interiorBondInsertedRegionInsert (G := G) A R e hends X) cfg =
      regionInteriorBondProd (G := G) A R •
        edgeInsertedCoeff (G := G) A e cfg X := by
  classical
  rw [interiorBondInsertedRegionInsert]
  rw [deformedRegionStateAssembled_const_smul]
  rw [← deformedRegionState_extend (edgeLeftVertices_subset_of_mem e hends.1) hpos]
  rw [deformedRegionStateAssembled_bondInserted_eq_smul_edgeInsertedCoeff]
  simp only [regionEdgeOrient, edgeLeftVertices, Finset.mem_singleton, ite_true]
  rw [nsmul_eq_mul, nsmul_eq_mul]
  have hne : (regionInteriorBondProd (G := G) A (edgeLeftVertices e) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (regionInteriorBondProd_pos (G := G) A (edgeLeftVertices e) hpos).ne'
  rw [edgeLeftVertices] at hne
  field_simp [hne]

end PEPS
end TNLean
