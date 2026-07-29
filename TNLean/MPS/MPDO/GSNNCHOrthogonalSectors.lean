/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.BNTProjectorSelection
import TNLean.MPS.MPDO.GSNNCHSectorSum

/-!
# Orthogonal sector construction of the GSNNCH form

The GSNNCH form of Definition 4.8 is obtained by combining positive commuting
bond products supported on pairwise orthogonal one-site subspaces.  The natural
multiplicity of each sector remains outside its bond product.

## Main declarations

* `MPOTensor.OrthogonalCommutingSectorFamily`: orthogonally supported commuting
  bond products for a finite family of MPO tensors.
* `MPOTensor.OrthogonalCommutingSectorFamily.toGSNNCHData`: the corresponding
  finite-chain GSNNCH sector decomposition.
* `MPOTensor.hasGSNNCHForm_of_orthogonalCommutingSectorFamily`: the outer-sector
  sum has the source GSNNCH form at every chain length at least two.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Definition 4.8 and Appendix C.2, Proposition `prop3to4`, lines 1783--1792
-/

open scoped ComplexOrder

namespace MPOTensor

variable {d g : ℕ} {dim : Fin g → ℕ}

/-- A finite family of positive commuting bond products supported on pairwise
orthogonal one-site subspaces.

The equality in `realizes_mpo` has scalar one.  Hence the natural
multiplicities in an outer direct sum are not absorbed into chain-length
dependent rescalings of the bonds.

This is sufficient data for the outer-sector assembly in arXiv:1606.00608,
Definition 4.8, lines 829--850.

**Scope restriction (supplied orthogonal sectors):** Proposition `prop3to4`
starts from five blockwise identities; it does not assume this assembled family
of orthogonal projections and supported bonds.  See
`docs/paper-gaps/cpsv16_gsnnch_sector_decomposition.tex`. -/
structure OrthogonalCommutingSectorFamily
    (K : (s : Fin g) → MPOTensor d (dim s)) where
  /-- The one-site projection of each outer sector.
  Source: arXiv:1606.00608, lines 838--842 and 1783--1792. -/
  projection : Fin g → Matrix (Fin d) (Fin d) ℂ
  /-- Every outer-sector projection is orthogonal.
  Source: arXiv:1606.00608, lines 838--842. -/
  projection_isOrthogonal : ∀ s, IsOrthogonalProjection (projection s)
  /-- Distinct outer sectors have orthogonal one-site spaces.
  Source: arXiv:1606.00608, lines 838--842. -/
  projection_orthogonal : ∀ {s t}, s ≠ t → projection s * projection t = 0
  /-- The positive translation-invariant bond of each sector.
  Source: arXiv:1606.00608, lines 843--850 and 1783--1792. -/
  bondData : Fin g → TranslationInvariantBondData d
  /-- Each bond acts on the tensor square of its one-site sector.
  Source: arXiv:1606.00608, lines 838--850. -/
  bond_supported : ∀ s,
    twoSiteSectorProjection (projection s) * (bondData s).bond *
      twoSiteSectorProjection (projection s) = (bondData s).bond
  /-- Every sector MPO is exactly the periodic product of its translated bond.

  **Scope restriction (supplied exact sector products):** This field records the
  product identity needed for the later outer-sector assembly; it is not derived
  here from the five hypotheses of CPSV16 Proposition `prop3to4`.  See
  `docs/paper-gaps/cpsv16_gsnnch_sector_decomposition.tex`. -/
  realizes_mpo : ∀ s N (hN : 2 ≤ N),
    mpo (K s) N = ((bondData s).toCommutingFormData hN).product

namespace OrthogonalCommutingSectorFamily

variable {K : (s : Fin g) → MPOTensor d (dim s)}

/-- The finite-chain GSNNCH decomposition determined by orthogonally supported
commuting sector bonds and their natural multiplicities.

This packages supplied sector data into the form of arXiv:1606.00608,
Definition 4.8, lines 829--850.

**Scope restriction (assembly from supplied data):** This definition does not
derive the orthogonal sectors from the five hypotheses of Proposition
`prop3to4`.  See
`docs/paper-gaps/cpsv16_gsnnch_sector_decomposition.tex`. -/
noncomputable def toGSNNCHData (F : OrthogonalCommutingSectorFamily K)
    (multiplicity : Fin g → ℕ) (N : ℕ) (hN : 2 ≤ N) : GSNNCHData d N where
  hN := hN
  sectorCount := g
  multiplicity := multiplicity
  sectorProjection := F.projection
  sectorProjection_isOrthogonal := F.projection_isOrthogonal
  sectorProjection_orthogonal := fun hst ↦ F.projection_orthogonal hst
  bond := fun s ↦ (F.bondData s).bond
  bond_pos := fun s ↦ (F.bondData s).bond_pos
  bond_supported := F.bond_supported
  neighboring_comm := fun s ↦
    (F.bondData s).bond_comm hN ⟨0, by omega⟩ ⟨1, by omega⟩

/-- The sector product in the induced GSNNCH decomposition is the prescribed
commuting bond product.

Source: arXiv:1606.00608, equation `rhoNCommv2`, lines 843--850. -/
@[simp] theorem toGSNNCHData_sectorProduct
    (F : OrthogonalCommutingSectorFamily K) (multiplicity : Fin g → ℕ)
    (N : ℕ) (hN : 2 ≤ N) (s : Fin g) :
    (F.toGSNNCHData multiplicity N hN).sectorProduct s =
      ((F.bondData s).toCommutingFormData hN).product := by
  rfl

/-- The unnormalized state of the induced GSNNCH decomposition is the
multiplicity-weighted sum of the sector MPOs.

**Scope restriction (identity for supplied sector data):** This is an algebraic
consequence of `OrthogonalCommutingSectorFamily`; it is not the implication from
the five printed hypotheses of Proposition `prop3to4`.  See
`docs/paper-gaps/cpsv16_gsnnch_sector_decomposition.tex`. -/
theorem toGSNNCHData_unnormalizedState
    (F : OrthogonalCommutingSectorFamily K) (multiplicity : Fin g → ℕ)
    (N : ℕ) (hN : 2 ≤ N) :
    (F.toGSNNCHData multiplicity N hN).unnormalizedState =
      ∑ s : Fin g, (multiplicity s : ℂ) • mpo (K s) N := by
  change (∑ s : Fin g, (multiplicity s : ℂ) •
      ((F.bondData s).toCommutingFormData hN).product) =
    ∑ s : Fin g, (multiplicity s : ℂ) • mpo (K s) N
  apply Finset.sum_congr rfl
  intro s _
  rw [F.realizes_mpo s N hN]

end OrthogonalCommutingSectorFamily

/-- A multiplicity-weighted sum of orthogonally supported commuting sector
products has the GSNNCH form of arXiv:1606.00608, Definition 4.8, at every
chain length at least two.

This is a sufficient-condition theorem once the orthogonal sectors, supported
positive bonds, and exact sector-product identities have been supplied.

**Scope restriction (later outer-sector assembly):** Proposition `prop3to4`
starts from five blockwise identities and does not assume these assembled data.
See `docs/paper-gaps/cpsv16_gsnnch_sector_decomposition.tex`. -/
theorem hasGSNNCHForm_of_orthogonalCommutingSectorFamily
    {D : ℕ} (M : MPOTensor d D) (K : (s : Fin g) → MPOTensor d (dim s))
    (multiplicity : Fin g → ℕ) (F : OrthogonalCommutingSectorFamily K)
    (hM : ∀ N : ℕ, 2 ≤ N →
      mpo M N = ∑ s : Fin g, (multiplicity s : ℂ) • mpo (K s) N) :
    HasGSNNCHForm M := by
  intro N hN
  refine ⟨F.toGSNNCHData multiplicity N hN, 1, by norm_num, ?_⟩
  rw [show ((1 : ℝ) : ℂ) = 1 by norm_num, one_smul]
  rw [F.toGSNNCHData_unnormalizedState, hM N hN]

/-- Once the absorbed BNT representatives have orthogonally supported
commuting bond products, the original tensor has the GSNNCH form with the BNT
copy numbers as its natural multiplicities.

This is a sufficient-condition theorem using a supplied
`OrthogonalCommutingSectorFamily` and the positive-length BNT sum.

**Scope restriction (assembled BNT sector family):** The hypotheses are stronger
than the five blockwise identities printed in Proposition `prop3to4`.  See
`docs/paper-gaps/cpsv16_gsnnch_sector_decomposition.tex`. -/
theorem hasGSNNCHForm_of_commonWeightAbsorbedBasisMPOTensor
    {D : ℕ} (M : MPOTensor d D)
    (S : MPSTensor.SectorDecomposition (d * d))
    (hM : MPSTensor.SameMPV₂Pos M.toMPSTensor S.toTensor)
    (hWeight : ∀ (s : Fin S.basisCount) (q q' : Fin (S.copies s)),
      S.weight s q = S.weight s q')
    (F : OrthogonalCommutingSectorFamily
      (fun s ↦ commonWeightAbsorbedBasisMPOTensor S hWeight s)) :
    HasGSNNCHForm M := by
  apply hasGSNNCHForm_of_orthogonalCommutingSectorFamily M _ S.copies F
  intro N hN
  exact mpo_eq_sum_copies_smul_commonWeightAbsorbedBasisMPOTensor
    M S hM hWeight (by omega)

end MPOTensor
