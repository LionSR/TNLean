import TNLean.PEPS.RegionBlock.GaugeBridge
import TNLean.PEPS.RegionBlock.Recovery9

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

with the *same* inserted matrix `M` on both sides and `X` the absorbed
orientation gauge.  The bridge between the two is the region gauge-absorption
identity `regionInsertedCoeff_applyGauge`: inserting `M` on the gauged tensor
cancels every interior gauge of the region and of its complement and conjugates
`M` by the gauge transpose on the single boundary edge `f`, oriented by
`regionEdgeOrient`.

The matrix reconciliation matches the engine's `Z · · · Z⁻¹` conjugation with
the bridge's `Xᵀ · orient(·) · (X⁻¹)ᵀ` conjugation by choosing the absorbed
boundary gauge `X` to be the orientation-adapted transpose of the engine gauge:
when `f`'s left endpoint lies in `R`, `X = (Zᵀ)`, so the two transposes cancel;
otherwise `X = Z⁻¹`, so the bridge's outer transpose flips the conjugation onto
the same form.  This is the region analogue of the edge-level absorbed equality
`post_absorption_edge_insertion_equality`, whose absorbed gauge is likewise the
transposed engine gauge.

The single absorbing matrix is region/orientation-dependent at `f`; assembling
these into one orientation-uniform absorbing family on the torus is the open
obligation 5 of `docs/paper-gaps/peps_normal_ft_section3_route.tex`.  This file
supplies the per-region step.

## References

* [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected
  entangled pair states generating the same state*, arXiv:1804.04964, Section
  3, proof of Theorem 3, lines 1519--1571 of
  `Papers/1804.04964/paper_normal.tex`](https://arxiv.org/abs/1804.04964)
-/

open scoped BigOperators Matrix

namespace TNLean
namespace PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ}

/-- The orientation-adapted absorbing gauge at a boundary edge.  The bridge
`regionInsertedCoeff_applyGauge` conjugates the inserted matrix by
`Xᵀ · orient(·) · (X⁻¹)ᵀ` with `orient = regionEdgeOrient B R f`.  To turn it
into the engine's `Z · · · Z⁻¹` conjugation, the absorbing matrix `X` is the
transpose of `Z` when `f`'s left endpoint lies in `R` (so the two transposes
cancel) and the inverse of `Z` otherwise (so the bridge's outer transpose flips
the conjugation back). -/
noncomputable def absorbedBoundaryGauge (B : Tensor G d) (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (Z : GL (Fin (B.bondDim f.1)) ℂ) : GL (Fin (B.bondDim f.1)) ℂ :=
  if f.1.1.1 ∈ R then glTranspose Z else Z⁻¹

omit [Fintype V] in
/-- The matrix reconciliation behind the absorbed equality.  Conjugating `N`
by the bridge's `Xᵀ · orient(·) · (X⁻¹)ᵀ` with `X` the orientation-adapted
absorbing gauge of `Z` reproduces the engine's `Z · N · Z⁻¹` conjugation. -/
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

/-! ### From the region absorbed equality to the edge-level absorbed equality

The region-inserted coefficient of any region `R` at a boundary edge `f`, with `M` inserted, is
the bond-dimension product over the non-boundary edges times the edge-inserted coefficient at `f`
of the assembled physical configuration, with `M` oriented to the edge convention
(`regionInsertedCoeff_eq_smul_edgeInsertedCoeff`).  Because the interior multiplicity is the same
for `A` and for `applyGauge B X` (gauge preserves bond dimensions and `A.bondDim = B.bondDim`)
and is a positive integer, the region absorbed equality cancels to the *edge-level* absorbed
equality.  The edge-level identity is over the single edge `f` and no longer mentions the region,
so it transports to every region with `f` on its boundary. -/

/-- Restricting a global physical configuration to a region and its complement and gluing back
recovers the global configuration. -/
theorem assembleRegionσ_restrict (R : Finset V) (σ : V → Fin d) :
    assembleRegionσ (V := V) (d := d) R (fun w => σ w.1) (fun w => σ w.1) = σ := by
  funext w
  by_cases h : w ∈ R
  · rw [assembleRegionσ, dif_pos h]
  · rw [assembleRegionσ, dif_neg h]

/-- **The edge-level absorbed plain equality from the region absorbed equality.**

If, at a region `R` with boundary edge `f`, inserting `M` on `A` matches inserting the reindexed
`M` on `applyGauge B X` for every region and complement physical configuration, and every bond
dimension of `A` is positive, then the *edge-level* absorbed equality holds at `f`: inserting `N`
on `A`'s edge `f.1` matches inserting the reindexed `N` on `applyGauge B X`'s edge `f.1`, for
every global physical configuration and every matrix.

The region-to-edge identity `regionInsertedCoeff_eq_smul_edgeInsertedCoeff` reads both region
coefficients as the (shared, positive) interior multiplicity times the edge-inserted coefficient
of the assembled configuration with the orientation-corrected matrix; cancelling the multiplicity
and running over the assembled configurations and the orientation involution gives the edge-level
identity over the bare edge `f.1`.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1519--1544 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem edgeInsertedCoeff_eq_applyGauge_of_region (A B : Tensor G d) (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (hbd : A.bondDim = B.bondDim)
    (X : (e : Edge G) → GL (Fin (B.bondDim e)) ℂ)
    (hposA : ∀ e : Edge G, 0 < A.bondDim e)
    (hregion : ∀ (M : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ)
      (σ : RegionPhysicalConfig (V := V) (d := d) R)
      (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R)),
      regionInsertedCoeff (G := G) A R f M σ τ =
        regionInsertedCoeff (G := G) (applyGauge B X) R f
          (Matrix.reindexAlgEquiv ℂ ℂ (finCongr (congr_fun hbd f.1)) M) σ τ)
    (σ : V → Fin d) (N : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ) :
    edgeInsertedCoeff (G := G) A f.1 σ N =
      edgeInsertedCoeff (G := G) (applyGauge B X) f.1 σ
        (Matrix.reindexAlgEquiv ℂ ℂ (finCongr (congr_fun hbd f.1)) N) := by
  classical
  -- The interior multiplicity is shared and positive.
  have hbd' : A.bondDim = (applyGauge B X).bondDim := hbd
  have hmult : regionInteriorBondProd (G := G) A R =
      regionInteriorBondProd (G := G) (applyGauge B X) R :=
    regionInteriorBondProd_congr A (applyGauge B X) R hbd'
  have hposBt : ∀ e : Edge G, 0 < (applyGauge B X).bondDim e := fun e => by
    rw [← congr_fun hbd' e]; exact hposA e
  have hne : (regionInteriorBondProd (G := G) (applyGauge B X) R : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (regionInteriorBondProd_pos (G := G) (applyGauge B X) R hposBt).ne'
  -- Evaluate the region absorbed equality at the orientation-corrected matrix and the assembled
  -- configuration, and read both sides through the region-to-edge identity.
  have hkey := hregion (regionEdgeOrient (G := G) A R f N)
    (fun w => σ w.1) (fun w => σ w.1)
  rw [regionInsertedCoeff_eq_smul_edgeInsertedCoeff A R f
      (regionEdgeOrient (G := G) A R f N),
    regionInsertedCoeff_eq_smul_edgeInsertedCoeff (applyGauge B X) R f] at hkey
  -- The orientation is an involution, so the corrected matrices unwind on both sides.
  rw [regionEdgeOrient_regionEdgeOrient A R f] at hkey
  -- The bond dimension of `applyGauge B X` at `f.1` is that of `B`, so the two orientations agree.
  have horient : regionEdgeOrient (G := G) (applyGauge B X) R f
      (Matrix.reindexAlgEquiv ℂ ℂ (finCongr (congr_fun hbd f.1))
        (regionEdgeOrient (G := G) A R f N)) =
        Matrix.reindexAlgEquiv ℂ ℂ (finCongr (congr_fun hbd f.1)) N := by
    rw [regionEdgeOrient, regionEdgeOrient]
    by_cases h : f.1.1.1 ∈ R
    · simp only [if_pos h]
    · simp only [if_neg h]
      change ((Matrix.reindex (finCongr (congr_fun hbd f.1))
          (finCongr (congr_fun hbd f.1))) Nᵀ)ᵀ =
        (Matrix.reindex (finCongr (congr_fun hbd f.1))
          (finCongr (congr_fun hbd f.1))) N
      rw [Matrix.transpose_reindex, Matrix.transpose_transpose]
  rw [horient] at hkey
  -- Cancel the shared positive interior multiplicity and rewrite the assembled configuration.
  rw [assembleRegionσ_restrict R σ, hmult] at hkey
  -- The natural-number smul is the cast smul; cancel the positive scalar.
  rw [← Nat.cast_smul_eq_nsmul ℂ, ← Nat.cast_smul_eq_nsmul ℂ] at hkey
  exact smul_right_injective ℂ hne hkey
/-- **The region absorbed equality at any region from the edge-level absorbed equality.**

If the edge-level absorbed equality holds at an edge `e` --- inserting `N` on `A`'s edge `e`
matches inserting the reindexed `N` on `applyGauge B X`'s edge `e` for every global physical
configuration --- then the region absorbed equality holds at *every* region `R` having `e` as a
boundary edge: inserting `M` on `A` over `R` at `e` matches inserting the reindexed `M` on
`applyGauge B X` over `R` at `e`.

This is the converse of `edgeInsertedCoeff_eq_applyGauge_of_region`: the region-to-edge identity
multiplies the edge-level identity back up by the (shared) interior multiplicity at `R`.  Together
the two directions express the region-independence the route note records: the absorbed plain
equality over any region follows from the single edge-level identity at the boundary edge.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1519--1544 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem regionInsertedCoeff_eq_applyGauge_of_edge (A B : Tensor G d)
    (hbd : A.bondDim = B.bondDim)
    (X : (e : Edge G) → GL (Fin (B.bondDim e)) ℂ)
    (e : Edge G)
    (hedge : ∀ (σ : V → Fin d) (N : Matrix (Fin (A.bondDim e)) (Fin (A.bondDim e)) ℂ),
      edgeInsertedCoeff (G := G) A e σ N =
        edgeInsertedCoeff (G := G) (applyGauge B X) e σ
          (Matrix.reindexAlgEquiv ℂ ℂ (finCongr (congr_fun hbd e)) N))
    (R : Finset V) (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f}) (hfe : f.1 = e)
    (M : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ)
    (σ : RegionPhysicalConfig (V := V) (d := d) R)
    (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R)) :
    regionInsertedCoeff (G := G) A R f M σ τ =
      regionInsertedCoeff (G := G) (applyGauge B X) R f
        (Matrix.reindexAlgEquiv ℂ ℂ (finCongr (congr_fun hbd f.1)) M) σ τ := by
  subst hfe
  -- Read both region coefficients through the region-to-edge identity.
  rw [regionInsertedCoeff_eq_smul_edgeInsertedCoeff A R f M σ τ,
    regionInsertedCoeff_eq_smul_edgeInsertedCoeff (applyGauge B X) R f
      (Matrix.reindexAlgEquiv ℂ ℂ (finCongr (congr_fun hbd f.1)) M) σ τ]
  -- The interior multiplicities agree (gauge preserves bond dimensions, `A.bondDim = B.bondDim`).
  rw [regionInteriorBondProd_congr A (applyGauge B X) R hbd]
  congr 1
  -- The orientation of the reindexed `M` matches the reindex of the oriented `M`.
  have horient : regionEdgeOrient (G := G) (applyGauge B X) R f
      (Matrix.reindexAlgEquiv ℂ ℂ (finCongr (congr_fun hbd f.1)) M) =
        Matrix.reindexAlgEquiv ℂ ℂ (finCongr (congr_fun hbd f.1))
          (regionEdgeOrient (G := G) A R f M) := by
    rw [regionEdgeOrient, regionEdgeOrient]
    by_cases h : f.1.1.1 ∈ R
    · simp only [if_pos h]
    · simp only [if_neg h]
      change ((Matrix.reindex (finCongr (congr_fun hbd f.1))
          (finCongr (congr_fun hbd f.1))) M)ᵀ =
        (Matrix.reindex (finCongr (congr_fun hbd f.1))
          (finCongr (congr_fun hbd f.1))) Mᵀ
      exact Matrix.transpose_reindex _ _ _
  rw [horient]
  exact hedge (assembleRegionσ (V := V) (d := d) R σ τ) (regionEdgeOrient (G := G) A R f M)

end PEPS
end TNLean
