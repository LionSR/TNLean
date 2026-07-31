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
* `MPOTensor.ProportionalOrthogonalCommutingSectorFamily`: the corresponding
  family when each sector operator is a positive scalar multiple of its bond
  product.
* `MPOTensor.ProportionalOrthogonalCommutingSectorFamily.mpo_posSemidef_of_two_le`:
  every sector operator of length at least two is positive semidefinite.
* `MPOTensor.ProportionalOrthogonalCommutingSectorFamily.isMPDO_of_mpo_one_pos`:
  one-site positivity completes the sector MPDO property.
* `MPOTensor.OrthogonalCommutingSectorFamily.toGSNNCHData`: the corresponding
  finite-chain GSNNCH sector decomposition.
* `MPOTensor.hasGSNNCHForm_of_orthogonalCommutingSectorFamily`: the outer-sector
  sum has the source GSNNCH form at every chain length at least two.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Definition 4.8 and Appendix C.2, Proposition `prop3to4`, lines 1786--1796
-/

open scoped ComplexOrder

namespace MPOTensor

variable {d g : ℕ} {dim : Fin g → ℕ}

/-- A finite family of positive commuting bond products supported on pairwise
orthogonal one-site subspaces.

The equality in `realizes_mpo` has scalar one.  Hence the natural
multiplicities in an outer direct sum are not absorbed into chain-length
dependent rescalings of the bonds.

These hypotheses suffice for the outer-sector direct sum in arXiv:1606.00608,
Definition 4.8, lines 829--850.

**Scope restriction (supplied orthogonal sectors):** CPSV16 Appendix C.2,
Proposition `prop3to4`, lines 1786--1796, starts from five blockwise
identities; it does not assume this family of orthogonal projections and supported bonds.  See
`docs/paper-gaps/cpsv16_gsnnch_sector_decomposition.tex`. -/
structure OrthogonalCommutingSectorFamily
    (K : (s : Fin g) → MPOTensor d (dim s)) where
  /-- The one-site projection of each outer sector.
  Source: arXiv:1606.00608, lines 838--842 and 1786--1796. -/
  projection : Fin g → Matrix (Fin d) (Fin d) ℂ
  /-- Every outer-sector projection is orthogonal.
  Source: arXiv:1606.00608, lines 838--842. -/
  projection_isOrthogonal : ∀ s, IsOrthogonalProjection (projection s)
  /-- Distinct outer sectors have orthogonal one-site spaces.
  Source: arXiv:1606.00608, lines 838--842. -/
  projection_orthogonal : ∀ {s t}, s ≠ t → projection s * projection t = 0
  /-- The positive translation-invariant bond of each sector.
  Source: arXiv:1606.00608, lines 843--850 and 1786--1796. -/
  bondData : Fin g → TranslationInvariantBondData d
  /-- Each bond acts on the tensor square of its one-site sector.
  Source: arXiv:1606.00608, lines 838--850. -/
  bond_supported : ∀ s,
    twoSiteSectorProjection (projection s) * (bondData s).bond *
      twoSiteSectorProjection (projection s) = (bondData s).bond
  /-- Every sector MPO is exactly the periodic product of its translated bond.

  **Scope restriction (supplied exact sector products):** This field records the
  product identity needed for the later outer-sector direct sum; it is not derived
  here from the five hypotheses of CPSV16 Proposition `prop3to4`.  See
  `docs/paper-gaps/cpsv16_gsnnch_sector_decomposition.tex`. -/
  realizes_mpo : ∀ s N (hN : 2 ≤ N),
    mpo (K s) N = ((bondData s).toCommutingFormData hN).product

/-- A finite family of positive commuting bond products supported on pairwise
orthogonal one-site subspaces, with positive proportional realization of each
sector operator.

This is the proportional sector form in arXiv:1606.00608, equation
`ApprhoNComm`, lines 1641--1665. The sector scalar may depend on the sector and
the chain length.

**Scope restriction (supplied orthogonal sectors):** CPSV16 Appendix C.2,
Proposition `prop3to4`, lines 1786--1796, starts from five blockwise identities;
it does not assume this family of orthogonal projections and supported bonds.
See `docs/paper-gaps/cpsv16_gsnnch_sector_decomposition.tex`. -/
structure ProportionalOrthogonalCommutingSectorFamily
    (K : (s : Fin g) → MPOTensor d (dim s)) where
  /-- The one-site projection of each outer sector.
  Source: arXiv:1606.00608, lines 838--842 and 1641--1665. -/
  projection : Fin g → Matrix (Fin d) (Fin d) ℂ
  /-- Every outer-sector projection is orthogonal.
  Source: arXiv:1606.00608, lines 838--842. -/
  projection_isOrthogonal : ∀ s, IsOrthogonalProjection (projection s)
  /-- Distinct outer sectors have orthogonal one-site spaces.
  Source: arXiv:1606.00608, lines 838--842. -/
  projection_orthogonal : ∀ {s t}, s ≠ t → projection s * projection t = 0
  /-- The positive translation-invariant bond of each sector.
  Source: arXiv:1606.00608, lines 843--850 and 1641--1665. -/
  bondData : Fin g → TranslationInvariantBondData d
  /-- Each bond acts on the tensor square of its one-site sector.
  Source: arXiv:1606.00608, lines 838--850. -/
  bond_supported : ∀ s,
    twoSiteSectorProjection (projection s) * (bondData s).bond *
      twoSiteSectorProjection (projection s) = (bondData s).bond
  /-- Every sector MPO is a positive scalar multiple of the periodic product
  of its translated bond.
  Source: arXiv:1606.00608, equation `ApprhoNComm`, lines 1641--1665. -/
  realizes_mpo : ∀ s N (hN : 2 ≤ N),
    ((bondData s).toCommutingFormData hN).Realizes (mpo (K s) N)

namespace ProportionalOrthogonalCommutingSectorFamily

variable {K : (s : Fin g) → MPOTensor d (dim s)}

/-- Every chain of length at least two in a proportional orthogonal commuting
sector family is positive semidefinite. The positive commuting bond gives a
positive product, and the realization rescales it by a positive real number.

Source: arXiv:1606.00608, equation `ApprhoNComm`, lines 1641--1665. -/
theorem mpo_posSemidef_of_two_le
    (F : ProportionalOrthogonalCommutingSectorFamily K)
    (s : Fin g) (N : ℕ) (hN : 2 ≤ N) :
    (mpo (K s) N).PosSemidef := by
  let form := (F.bondData s).toCommutingFormData hN
  have hproduct : form.product.PosSemidef := by
    rw [← GSNNCHData.ofCommutingFormData_unnormalizedState]
    exact (GSNNCHData.ofCommutingFormData form).unnormalizedState_posSemidef
  obtain ⟨c, hc, hreal⟩ := F.realizes_mpo s N hN
  rw [hreal]
  exact hproduct.smul (by exact_mod_cast hc.le)

/-- One-site positivity completes the positive commuting-product realization
to MPDO positivity at every nonempty chain length.

The commuting bond controls exactly the source-defined lengths $N \ge 2$; the
one-site case is therefore retained as the sharp additional boundary.

Source: arXiv:1606.00608, equation `ApprhoNComm`, lines 1641--1665. -/
theorem isMPDO_of_mpo_one_pos
    (F : ProportionalOrthogonalCommutingSectorFamily K)
    (hOne : ∀ s, (mpo (K s) 1).PosSemidef) :
    ∀ s, IsMPDO (K s) := by
  intro s N hN
  by_cases hN1 : N = 1
  · subst N
    exact hOne s
  · exact F.mpo_posSemidef_of_two_le s N (by omega)

end ProportionalOrthogonalCommutingSectorFamily

namespace OrthogonalCommutingSectorFamily

variable {K : (s : Fin g) → MPOTensor d (dim s)}

/-- An exact orthogonal commuting sector family is a proportional family with
normalization scalar one.

Source: arXiv:1606.00608, equation `ApprhoNComm`, lines 1641--1665. -/
noncomputable def toProportional (F : OrthogonalCommutingSectorFamily K) :
    ProportionalOrthogonalCommutingSectorFamily K where
  projection := F.projection
  projection_isOrthogonal := F.projection_isOrthogonal
  projection_orthogonal := fun hst ↦ F.projection_orthogonal hst
  bondData := F.bondData
  bond_supported := F.bond_supported
  realizes_mpo := by
    intro s N hN
    refine ⟨1, zero_lt_one, ?_⟩
    simpa using F.realizes_mpo s N hN

/-- The finite-chain GSNNCH decomposition determined by orthogonally supported
commuting sector bonds and their natural multiplicities.

This constructs the finite-chain decomposition from the supplied sector bonds in
arXiv:1606.00608,
Definition 4.8, lines 829--850.

**Scope restriction (supplied orthogonal sectors):** This definition does not
derive the orthogonal sectors from the five hypotheses of CPSV16 Appendix C.2,
Proposition `prop3to4`, lines 1786--1796.  See
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
the five printed hypotheses of CPSV16 Appendix C.2, Proposition `prop3to4`,
lines 1786--1796.  See
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

**Scope restriction (supplied outer sectors):** CPSV16 Appendix C.2,
Proposition `prop3to4`, lines 1786--1796, starts from five blockwise
identities and does not assume these projections and bonds.  See
`docs/paper-gaps/cpsv16_gsnnch_sector_decomposition.tex`. -/
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

**Scope restriction (supplied BNT sector family):** The hypotheses are stronger
than the five blockwise identities printed in CPSV16 Appendix C.2,
Proposition `prop3to4`, lines 1786--1796.  See
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
