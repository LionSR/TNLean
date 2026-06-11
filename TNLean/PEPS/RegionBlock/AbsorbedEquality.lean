import TNLean.PEPS.RegionBlock.GaugeBridge

/-!
# The region-level absorbed plain equality from the per-edge conjugation identity

This file performs the first step of the normal PEPS Fundamental Theorem's final comparison
on a single comparison region: it turns the per-edge gauge's *conjugation*-form region-inserted
coefficient identity into the *absorbed plain* equality the region comparison
`regionComplement_comparison` consumes (arXiv:1804.04964, Section 3, proof of Theorem 3, lines
1519--1571 of `Papers/1804.04964/paper_normal.tex`).

The per-edge gauge engine delivers, at a region `R` with single boundary edge `f`, the
conjugation form

> `regionInsertedCoeff A R f M = regionInsertedCoeff B R f (Z · M · Z⁻¹)`

(`exists_regionEdgeGauge_torus_coeff`, the witness field `EdgeCoeffIdentityWitness.hidZ`).  The
region comparison wants instead the *absorbed* form

> `regionInsertedCoeff A R f M = regionInsertedCoeff (applyGauge B X) R f M`

with the *same* inserted matrix `M` on both sides and `X` the absorbed orientation gauge.  The
bridge between the two is the region gauge-absorption identity
`regionInsertedCoeff_applyGauge`: inserting `M` on the gauged tensor cancels every interior
gauge of the region and of its complement and conjugates `M` by the gauge transpose on the single
boundary edge `f`, oriented by `regionEdgeOrient`.

The matrix reconciliation matches the engine's `Z · · · Z⁻¹` conjugation with the bridge's
`Xᵀ · orient(·) · (X⁻¹)ᵀ` conjugation by choosing the absorbed boundary gauge `X` to be the
orientation-adapted transpose of the engine gauge: when `f`'s left endpoint lies in `R`,
`X = (Zᵀ)`, so the two transposes cancel; otherwise `X = Z⁻¹`, so the bridge's outer transpose
flips the conjugation onto the same form.  This is the region analogue of the edge-level absorbed
equality `post_absorption_edge_insertion_equality`, whose absorbed gauge is likewise the
transposed engine gauge.

The single absorbing matrix is region/orientation-dependent at `f`; assembling these into one
orientation-uniform absorbing family on the torus is the open obligation 5 of
`docs/paper-gaps/peps_normal_ft_section3_route.tex`.  This file supplies the per-region step.

## References

* [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected entangled pair states
  generating the same state*, arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1519--1571 of
  `Papers/1804.04964/paper_normal.tex`](https://arxiv.org/abs/1804.04964)
-/

open scoped BigOperators Matrix

namespace TNLean
namespace PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ}

/-- The orientation-adapted absorbing gauge at a boundary edge.  The bridge
`regionInsertedCoeff_applyGauge` conjugates the inserted matrix by `Xᵀ · orient(·) · (X⁻¹)ᵀ`
with `orient = regionEdgeOrient B R f`.  To turn it into the engine's `Z · · · Z⁻¹` conjugation,
the absorbing matrix `X` is the transpose of `Z` when `f`'s left endpoint lies in `R` (so the two
transposes cancel) and the inverse of `Z` otherwise (so the bridge's outer transpose flips the
conjugation back). -/
noncomputable def absorbedBoundaryGauge (B : Tensor G d) (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (Z : GL (Fin (B.bondDim f.1)) ℂ) : GL (Fin (B.bondDim f.1)) ℂ :=
  if f.1.1.1 ∈ R then glTranspose Z else Z⁻¹

omit [Fintype V] in
/-- The matrix reconciliation behind the absorbed equality.  Conjugating `N` by the bridge's
`Xᵀ · orient(·) · (X⁻¹)ᵀ` with `X` the orientation-adapted absorbing gauge of `Z` reproduces the
engine's `Z · N · Z⁻¹` conjugation. -/
theorem regionEdgeOrient_absorbedBoundaryGauge (B : Tensor G d) (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (Z : GL (Fin (B.bondDim f.1)) ℂ)
    (N : Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ) :
    regionEdgeOrient (G := G) B R f
        ((absorbedBoundaryGauge (G := G) B R f Z :
            Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ)ᵀ *
          regionEdgeOrient (G := G) B R f N *
          ((absorbedBoundaryGauge (G := G) B R f Z :
            Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ)⁻¹)ᵀ) =
      (Z : Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ) * N *
        (↑Z⁻¹ : Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ) := by
  have hdetZ : IsUnit (Z : Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp Z.isUnit
  unfold absorbedBoundaryGauge regionEdgeOrient
  by_cases h : f.1.1.1 ∈ R
  · -- Orientation is the identity; `X = glTranspose Z` so `Xᵀ = Z` and `(X⁻¹)ᵀ = Z⁻¹`.
    simp only [if_pos h, glTranspose_coe, Matrix.GeneralLinearGroup.coe_inv,
      Matrix.transpose_transpose, Matrix.transpose_nonsing_inv]
  · -- Orientation is the transpose; `X = Z⁻¹` so `Xᵀ = (Z⁻¹)ᵀ` and `(X⁻¹)ᵀ = Zᵀ`.
    simp only [if_neg h, Matrix.GeneralLinearGroup.coe_inv, Matrix.transpose_mul,
      Matrix.transpose_transpose, Matrix.transpose_nonsing_inv,
      Matrix.nonsing_inv_nonsing_inv _ hdetZ]
    rw [mul_assoc]

/-- **The region-level absorbed plain equality from the per-edge conjugation identity.**

If the per-edge gauge `Z` realizes the engine's conjugation-form region-inserted coefficient
identity at a region `R` with single boundary edge `f` --- `A` inserting `M` matches `B` inserting
`Z · (reindex M) · Z⁻¹` --- then `A` inserting `M` matches the absorbed tensor
`applyGauge B X` inserting the *same* `(reindex M)`, where `X` is the orientation-adapted
absorbing gauge `absorbedBoundaryGauge` at `f` (and an arbitrary invertible matrix on every other
edge, since only the gauge on `f` enters `regionInsertedCoeff … f`).

This is the region analogue of `post_absorption_edge_insertion_equality`: the conjugation-form
coefficient identity becomes the absorbed plain equality.  The matrix reconciliation is
`regionEdgeOrient_absorbedBoundaryGauge`; the bond cancellation is the bridge
`regionInsertedCoeff_applyGauge`.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1519--1544 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem regionInsertedCoeff_eq_applyGauge_of_conjIdentity (A B : Tensor G d) (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (hbd : A.bondDim = B.bondDim)
    (Z : GL (Fin (B.bondDim f.1)) ℂ)
    (X : (e : Edge G) → GL (Fin (B.bondDim e)) ℂ)
    (hXf : X f.1 = absorbedBoundaryGauge (G := G) B R f Z)
    (hid : ∀ (M : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ)
      (σ : RegionPhysicalConfig (V := V) (d := d) R)
      (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R)),
      regionInsertedCoeff (G := G) A R f M σ τ =
        regionInsertedCoeff (G := G) B R f
          ((Z : Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ) *
              Matrix.reindexAlgEquiv ℂ ℂ (finCongr (congr_fun hbd f.1)) M *
            (↑Z⁻¹ : Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ)) σ τ)
    (M : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ)
    (σ : RegionPhysicalConfig (V := V) (d := d) R)
    (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R)) :
    regionInsertedCoeff (G := G) A R f M σ τ =
      regionInsertedCoeff (G := G) (applyGauge B X) R f
        (Matrix.reindexAlgEquiv ℂ ℂ (finCongr (congr_fun hbd f.1)) M) σ τ := by
  -- The bridge on the right, with the gauge on `f` chosen as the orientation-adapted absorber.
  rw [regionInsertedCoeff_applyGauge B R X f
    (Matrix.reindexAlgEquiv ℂ ℂ (finCongr (congr_fun hbd f.1)) M) σ τ]
  -- The engine identity on the left.
  rw [hid M σ τ]
  -- Reconcile the two conjugation forms.
  rw [hXf, regionEdgeOrient_absorbedBoundaryGauge B R f Z
    (Matrix.reindexAlgEquiv ℂ ℂ (finCongr (congr_fun hbd f.1)) M)]

end PEPS
end TNLean
