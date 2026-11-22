/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Analysis.Isometry.CoisometricCompression
import TNLean.MPS.Operator.Interaction.PhysicalGibbsEmbedding
import TNLean.MPS.MPDO.TopologicalForm.TopologicalGibbsHamiltonian
import TNLean.MPS.MPDO.Fusion.BNTFusionTensorClauseFromRFP

/-!
# Physical-space topological Gibbs Hamiltonian

This file extends the retained-coordinate Gibbs decomposition to the ambient
physical chain. The retained-row coisometry supplies a finite energy on the
physical support and zero energy on its orthogonal complement.

**Scope restriction (positive chains of length at least two):** Definition 4.8
of the source fixes no length-one two-site convention, so the physical Gibbs
decompositions in this file cover exactly the source-defined chains of length
at least two.  See `docs/paper-gaps/cpsv16_topological_gibbs_length_one.tex`.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  lines 999--1016

## Literal CPSV RFP tensors have a physical commuting Gibbs decomposition

This file selects the BNT fusion tensor clause furnished by the literal CPSV
canonical-form theorem and applies the physical-coordinate Gibbs construction.

**Scope restriction (positive chains of length at least two):** Definition 4.8
of the source fixes no length-one two-site convention, so the main result covers
exactly the source-defined chains of length at least two.  See
`docs/paper-gaps/cpsv16_topological_gibbs_length_one.tex`.

### Main definitions

* `MPOTensor.cpsvRFPBNTFusionTensorClause`

### Main result

* `MPOTensor.physicalTopologicalGibbsDecomposition_of_isRFPViaTS_of_cpsvCanonicalForm`

### References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Theorems 4.14 and 4.15 and Appendix C.4
-/

section

open scoped Matrix BigOperators ComplexOrder

noncomputable section

namespace MPOTensor.BNTFusionTensorClause

variable {d D : ℕ} {M : MPOTensor d D}

/-- The one-site multiplicity energy compressed back to the ambient physical
coordinates.

The retained energy is the logarithmic factor from CPSV16, lines 999–1002.
Its compression to the ambient physical space is the construction recorded
in `docs/paper-gaps/cpsv16_topological_gibbs_physical_complement.tex`; the
complement extension itself is not stated in CPSV16. -/
def physicalMultiplicityEnergy (H : BNTFusionTensorClause M) :
    Matrix (Fin d) (Fin d) ℂ :=
  H.verticalCoisometryᴴ * H.retainedMultiplicityEnergy *
    H.verticalCoisometry

/-- The ambient physical one-site energy is Hermitian.

This supplies the Hermiticity required by CPSV16, Definition 4.8,
lines 831–847, for the physical-complement construction documented in
`docs/paper-gaps/cpsv16_topological_gibbs_physical_complement.tex`. -/
theorem physicalMultiplicityEnergy_isHermitian
    (H : BNTFusionTensorClause M) :
    H.physicalMultiplicityEnergy.IsHermitian := by
  exact Matrix.isHermitian_conjTranspose_mul_mul H.verticalCoisometry
    H.retainedMultiplicityEnergy_isHermitian

/-- The retained multiplicity weight transported to physical coordinates
and extended by the identity on the orthogonal complement.

The retained factor occurs in CPSV16, lines 999–1002. The identity extension
on the physical complement is not stated there; it is recorded in
`docs/paper-gaps/cpsv16_topological_gibbs_physical_complement.tex`. -/
def physicalMultiplicityWeight (H : BNTFusionTensorClause M) :
    Matrix (Fin d) (Fin d) ℂ :=
  H.verticalCoisometryᴴ * H.retainedMultiplicityOperator *
      H.verticalCoisometry +
    (1 - H.verticalCoisometryᴴ * H.verticalCoisometry)

/-- Exponentiating the negative ambient one-site energy gives the retained
weight transported to physical coordinates, with the identity on the
orthogonal complement.

The retained exponential identity is CPSV16, lines 999–1002. The complement
extension is a general coisometric-compression identity, not a statement of
CPSV16; see
`docs/paper-gaps/cpsv16_topological_gibbs_physical_complement.tex`. -/
theorem exp_neg_physicalMultiplicityEnergy
    (H : BNTFusionTensorClause M) :
    NormedSpace.exp (-H.physicalMultiplicityEnergy) =
      H.physicalMultiplicityWeight := by
  rw [physicalMultiplicityEnergy, physicalMultiplicityWeight,
    Matrix.exp_neg_conjTranspose_mul_mul_of_mul_conjTranspose_eq_one
      H.verticalCoisometry H.retainedMultiplicityEnergy H.coisometry,
    H.exp_neg_retainedMultiplicityEnergy]

/-- The retained-row coisometry intertwines the ambient physical Gibbs
weight with the retained multiplicity operator.

This is the one-site support identity used to lift the retained factor from
CPSV16, lines 999–1002, to the physical complement. The complement extension
is documented in
`docs/paper-gaps/cpsv16_topological_gibbs_physical_complement.tex`. -/
theorem verticalCoisometry_mul_physicalMultiplicityWeight
    (H : BNTFusionTensorClause M) :
    H.verticalCoisometry * H.physicalMultiplicityWeight =
      H.retainedMultiplicityOperator * H.verticalCoisometry := by
  unfold physicalMultiplicityWeight
  simp only [Matrix.mul_add, Matrix.mul_sub, Matrix.mul_one]
  rw [← Matrix.mul_assoc H.verticalCoisometry H.verticalCoisometryᴴ,
    H.coisometry, Matrix.one_mul]
  rw [sub_self, add_zero]
  simp only [← Matrix.mul_assoc, H.coisometry, Matrix.one_mul]

/-- The adjoint retained-row map intertwines the retained multiplicity
operator with the ambient physical Gibbs weight.

This is the adjoint one-site support identity used to lift the retained
factor from CPSV16, lines 999–1002. The complement extension is documented
in `docs/paper-gaps/cpsv16_topological_gibbs_physical_complement.tex`. -/
theorem physicalMultiplicityWeight_mul_conjTranspose_verticalCoisometry
    (H : BNTFusionTensorClause M) :
    H.physicalMultiplicityWeight * H.verticalCoisometryᴴ =
      H.verticalCoisometryᴴ * H.retainedMultiplicityOperator := by
  unfold physicalMultiplicityWeight
  simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.one_mul]
  rw [Matrix.mul_assoc H.verticalCoisometryᴴ H.verticalCoisometry,
    H.coisometry, Matrix.mul_one]
  rw [sub_self, add_zero]
  simp only [Matrix.mul_assoc, H.coisometry, Matrix.mul_one]

/-- On every chain, the sitewise retained-row coisometry intertwines the
ambient physical Gibbs factor with the retained multiplicity factor.

This is the chain version of the support transport used in the physical
formula of CPSV16, lines 1013–1016. Its complement construction is recorded
in `docs/paper-gaps/cpsv16_topological_gibbs_physical_complement.tex`. -/
theorem sitewiseVerticalCoisometry_mul_physicalMultiplicityWeight
    (H : BNTFusionTensorClause M) (L : ℕ) :
    (Matrix.piKronecker fun _ : Fin L ↦ H.verticalCoisometry) *
        (Matrix.piKronecker fun _ : Fin L ↦ H.physicalMultiplicityWeight) =
      (Matrix.piKronecker fun _ : Fin L ↦ H.retainedMultiplicityOperator) *
        (Matrix.piKronecker fun _ : Fin L ↦ H.verticalCoisometry) := by
  rw [Matrix.piKronecker_mul,
    H.verticalCoisometry_mul_physicalMultiplicityWeight,
    Matrix.piKronecker_mul]

/-- On every chain, the sitewise adjoint retained-row map intertwines the
retained multiplicity factor with the ambient physical Gibbs factor.

This is the adjoint chain support transport used in the physical formula of
CPSV16, lines 1013–1016. Its complement construction is recorded in
`docs/paper-gaps/cpsv16_topological_gibbs_physical_complement.tex`. -/
theorem sitewisePhysicalMultiplicityWeight_mul_conjTranspose_verticalCoisometry
    (H : BNTFusionTensorClause M) (L : ℕ) :
    (Matrix.piKronecker fun _ : Fin L ↦ H.physicalMultiplicityWeight) *
        (Matrix.piKronecker fun _ : Fin L ↦ H.verticalCoisometryᴴ) =
      (Matrix.piKronecker fun _ : Fin L ↦ H.verticalCoisometryᴴ) *
        (Matrix.piKronecker fun _ : Fin L ↦ H.retainedMultiplicityOperator) := by
  rw [Matrix.piKronecker_mul,
    H.physicalMultiplicityWeight_mul_conjTranspose_verticalCoisometry,
    Matrix.piKronecker_mul]

/-- The sitewise tensor power of the retained-row coisometry remains a
coisometry.

This is the chain-level coordinate property used in the physical
reconstruction at CPSV16, lines 999 and 1013–1016. The rectangular
orientation is documented in
`docs/paper-gaps/cpsv16_topological_gibbs_physical_complement.tex`. -/
theorem sitewiseVerticalCoisometry_mul_conjTranspose
    (H : BNTFusionTensorClause M) (L : ℕ) :
    (Matrix.piKronecker fun _ : Fin L ↦ H.verticalCoisometry) *
        (Matrix.piKronecker fun _ : Fin L ↦ H.verticalCoisometry)ᴴ =
      1 := by
  rw [MPOTensor.tensorPower_mul_conjTranspose,
    H.coisometry, Matrix.piKronecker_one]

/-- The fixed physical two-site Gibbs term: the ambient one-site energy on
the first site and the identity on the second.

This has the two-site form of CPSV16, Definition 4.8, lines 831–847, and is
used for the Hamiltonian at lines 1013–1016. Its physical-complement
construction is documented in
`docs/paper-gaps/cpsv16_topological_gibbs_physical_complement.tex`. -/
def physicalTopologicalGibbsLocalTerm (H : BNTFusionTensorClause M) :
    Matrix (Fin 2 → Fin d) (Fin 2 → Fin d) ℂ :=
  MPOTensor.twoSiteFirstOperator H.physicalMultiplicityEnergy

/-- The fixed physical two-site Gibbs term is Hermitian.

This verifies the local Hermiticity condition in CPSV16, Definition 4.8,
lines 831–847, for the physical-complement construction documented in
`docs/paper-gaps/cpsv16_topological_gibbs_physical_complement.tex`. -/
theorem physicalTopologicalGibbsLocalTerm_isHermitian
    (H : BNTFusionTensorClause M) :
    H.physicalTopologicalGibbsLocalTerm.IsHermitian :=
  MPOTensor.twoSiteFirstOperator_isHermitian
    H.physicalMultiplicityEnergy_isHermitian

/-- The periodic translation-invariant physical Gibbs Hamiltonian on a chain
of length `N + 2`.

This is the physical-space `H_N = ∑ᵢ h_{i,i+1}` of CPSV16,
lines 1013–1016, with the two-site convention of Definition 4.8,
lines 831–847. The complement choice is documented in
`docs/paper-gaps/cpsv16_topological_gibbs_physical_complement.tex`. The
length-at-least-two scope is documented in
`docs/paper-gaps/cpsv16_topological_gibbs_length_one.tex`. -/
def physicalTopologicalGibbsHamiltonianSuccSucc
    (H : BNTFusionTensorClause M) (N : ℕ) :
    Matrix (Fin (N + 2) → Fin d) (Fin (N + 2) → Fin d) ℂ :=
  ∑ i : Fin (N + 2),
    ManyBody.placeAlong (X := fun _ ↦ Fin d) (ManyBody.ringWindow (by omega : 2 ≤ N + 2) i)
      H.physicalTopologicalGibbsLocalTerm

/-- Periodic translates of the physical two-site Gibbs term commute
pairwise.

This is `[h_{i-1,i}, h_{i,i+1}] = 0` from CPSV16, lines 1013–1016, for
the physical-complement construction documented in
`docs/paper-gaps/cpsv16_topological_gibbs_physical_complement.tex`. The
length-at-least-two scope is documented in
`docs/paper-gaps/cpsv16_topological_gibbs_length_one.tex`. -/
theorem physicalTopologicalGibbsBondSuccSucc_commute
    (H : BNTFusionTensorClause M) (N : ℕ)
    (i j : Fin (N + 2)) :
    Commute
      (ManyBody.placeAlong (X := fun _ ↦ Fin d) (ManyBody.ringWindow (by omega : 2 ≤ N + 2) i)
        H.physicalTopologicalGibbsLocalTerm)
      (ManyBody.placeAlong (X := fun _ ↦ Fin d) (ManyBody.ringWindow (by omega : 2 ≤ N + 2) j)
        H.physicalTopologicalGibbsLocalTerm) := by
  rw [physicalTopologicalGibbsLocalTerm,
    MPOTensor.placeAlong_ringWindow_twoSiteFirstOperator,
    MPOTensor.placeAlong_ringWindow_twoSiteFirstOperator]
  exact MPOTensor.commute_placeAlong_ringWindow_oneSiteOperator (by omega)
    H.physicalMultiplicityEnergy i j

/-- The physical Gibbs factor is the tensor power of the retained
multiplicity weight transported to physical coordinates and extended by the
identity on the orthogonal complement.

This is the physical-space exponential factor `e^{-H_N}` in CPSV16,
lines 1013–1016. The complement extension is not stated in CPSV16; see
`docs/paper-gaps/cpsv16_topological_gibbs_physical_complement.tex`. The
length-at-least-two scope is documented in
`docs/paper-gaps/cpsv16_topological_gibbs_length_one.tex`. -/
theorem exp_neg_physicalTopologicalGibbsHamiltonianSuccSucc
    (H : BNTFusionTensorClause M) (N : ℕ) :
    NormedSpace.exp (-H.physicalTopologicalGibbsHamiltonianSuccSucc N) =
      (Matrix.piKronecker fun _ : Fin (N + 2) ↦ H.physicalMultiplicityWeight) := by
  have hneg (i : Fin (N + 2)) :
      -ManyBody.placeAlong (X := fun _ ↦ Fin d) (ManyBody.ringWindow (by omega : 1 ≤ N + 2) i)
          (MPOTensor.oneSiteOperator H.physicalMultiplicityEnergy) =
        ManyBody.placeAlong (X := fun _ ↦ Fin d) (ManyBody.ringWindow (by omega : 1 ≤ N + 2) i)
          (MPOTensor.oneSiteOperator (-H.physicalMultiplicityEnergy)) := by
    rw [← ManyBody.placeAlong_neg]
    congr 1
  unfold physicalTopologicalGibbsHamiltonianSuccSucc
  rw [← Finset.sum_neg_distrib]
  simp_rw [physicalTopologicalGibbsLocalTerm,
    MPOTensor.placeAlong_ringWindow_twoSiteFirstOperator, hneg]
  rw [MPOTensor.exp_sum_placeAlong_ringWindow_oneSiteOperator,
    H.exp_neg_physicalMultiplicityEnergy]

/-- The `Fin d`-indexed terminal projector transported from retained
coordinates to the ambient physical chain of length `N + 2`.

This is the physical projector `P_i^(N)` in CPSV16, lines 1013–1016. Its
transport through the rectangular retained-row coisometry is the construction
recorded in
`docs/paper-gaps/cpsv16_topological_gibbs_physical_complement.tex`. The
length-at-least-two scope is recorded in
`docs/paper-gaps/cpsv16_topological_gibbs_length_one.tex`. -/
def physicalIndexedAmbientTopologicalSpectralProjectorSuccSucc
    (H : BNTFusionTensorClause M) (hM : IsMPDO M)
    (N : ℕ) (i : Fin d) :
    Matrix (Fin (N + 2) → Fin d) (Fin (N + 2) → Fin d) ℂ :=
  let W := (Matrix.piKronecker fun _ : Fin (N + 2) ↦ H.verticalCoisometry)
  Wᴴ *
      H.physicalIndexedTopologicalSpectralProjectorSucc hM (N + 1) i *
    W

/-- Every transported `Fin d`-indexed ambient physical operator is an
orthogonal projection.

This proves the projection property required for `P_i^(N)` in CPSV16,
lines 1013–1016. The physical-complement transport is recorded in
`docs/paper-gaps/cpsv16_topological_gibbs_physical_complement.tex`, and the
length-at-least-two scope in
`docs/paper-gaps/cpsv16_topological_gibbs_length_one.tex`. -/
theorem physicalIndexedAmbientTopologicalSpectralProjectorSuccSucc_isOrthogonalProjection
    (H : BNTFusionTensorClause M) (hM : IsMPDO M)
    (hLI : (BNTLabelCoefficientFamily.ofChi H.chi).LengthIndependent)
    (N : ℕ) (i : Fin d) :
    (H.physicalIndexedAmbientTopologicalSpectralProjectorSuccSucc
        hM N i).IsHermitian ∧
      H.physicalIndexedAmbientTopologicalSpectralProjectorSuccSucc
          hM N i *
        H.physicalIndexedAmbientTopologicalSpectralProjectorSuccSucc
          hM N i =
        H.physicalIndexedAmbientTopologicalSpectralProjectorSuccSucc
          hM N i := by
  let W := (Matrix.piKronecker fun _ : Fin (N + 2) ↦ H.verticalCoisometry)
  let P :=
    H.physicalIndexedTopologicalSpectralProjectorSucc hM (N + 1) i
  have hP :
      P.IsHermitian ∧ P * P = P :=
    H.physicalIndexedTopologicalSpectralProjectorSucc_isOrthogonalProjection
      hM hLI (N + 1) i
  have hPstar : IsStarProjection P := by
    rw [isStarProjection_iff']
    exact ⟨hP.2, by
      simpa [Matrix.star_eq_conjTranspose] using hP.1.eq⟩
  have hW : W * Wᴴ = 1 :=
    H.sitewiseVerticalCoisometry_mul_conjTranspose (N + 2)
  have hLift :=
    IsStarProjection.conjTranspose_mul_mul_of_mul_conjTranspose_eq_one
      hPstar W hW
  rw [isStarProjection_iff'] at hLift
  exact ⟨by
    change (Wᴴ * P * W)ᴴ = Wᴴ * P * W
    simpa [Matrix.star_eq_conjTranspose] using hLift.2, hLift.1⟩

/-- Distinct zero-padded retained terminal projectors multiply to zero.

This is the retained-coordinate orthogonality underlying the physical
projectors in CPSV16, lines 1013–1016. The zero-padding and coordinate scope
are documented in
`docs/paper-gaps/cpsv16_topological_gibbs_physical_complement.tex`. -/
theorem physicalIndexedTopologicalSpectralProjectorSucc_mul_eq_zero
    (H : BNTFusionTensorClause M) (hM : IsMPDO M)
    (hLI : (BNTLabelCoefficientFamily.ofChi H.chi).LengthIndependent)
    (N : ℕ) {i j : Fin d} (hij : i ≠ j) :
    H.physicalIndexedTopologicalSpectralProjectorSucc hM N i *
        H.physicalIndexedTopologicalSpectralProjectorSucc hM N j =
      0 := by
  classical
  by_cases hi : ∃ s, H.terminalSpectralEmbedding s = i
  · obtain ⟨s, rfl⟩ := hi
    rw [physicalIndexedTopologicalSpectralProjectorSucc,
      H.terminalSpectralEmbedding.injective.extend_apply]
    by_cases hj : ∃ t, H.terminalSpectralEmbedding t = j
    · obtain ⟨t, rfl⟩ := hj
      have hst : s ≠ t := by
        intro hst
        subst t
        exact hij rfl
      rw [physicalIndexedTopologicalSpectralProjectorSucc,
        H.terminalSpectralEmbedding.injective.extend_apply]
      exact
        H.topologicalSpectralProjectorSucc_mul_eq_zero hM hLI N hst
    · rw [physicalIndexedTopologicalSpectralProjectorSucc,
        Function.extend_apply' _ _ _ hj, Matrix.mul_zero]
  · rw [physicalIndexedTopologicalSpectralProjectorSucc,
      Function.extend_apply' _ _ _ hi, Matrix.zero_mul]

/-- Distinct transported `Fin d`-indexed ambient physical projectors multiply
to zero.

This is the pairwise orthogonality of the physical projectors in CPSV16,
lines 1013–1016. Their transport and complement support are recorded in
`docs/paper-gaps/cpsv16_topological_gibbs_physical_complement.tex`, and the
length-at-least-two scope in
`docs/paper-gaps/cpsv16_topological_gibbs_length_one.tex`. -/
theorem physicalIndexedAmbientTopologicalSpectralProjectorSuccSucc_mul_eq_zero
    (H : BNTFusionTensorClause M) (hM : IsMPDO M)
    (hLI : (BNTLabelCoefficientFamily.ofChi H.chi).LengthIndependent)
    (N : ℕ) {i j : Fin d} (hij : i ≠ j) :
    H.physicalIndexedAmbientTopologicalSpectralProjectorSuccSucc hM N i *
        H.physicalIndexedAmbientTopologicalSpectralProjectorSuccSucc hM N j =
      0 := by
  let W := (Matrix.piKronecker fun _ : Fin (N + 2) ↦ H.verticalCoisometry)
  let P :=
    H.physicalIndexedTopologicalSpectralProjectorSucc hM (N + 1) i
  let Q :=
    H.physicalIndexedTopologicalSpectralProjectorSucc hM (N + 1) j
  have hW : W * Wᴴ = 1 :=
    H.sitewiseVerticalCoisometry_mul_conjTranspose (N + 2)
  have hPQ : P * Q = 0 :=
    H.physicalIndexedTopologicalSpectralProjectorSucc_mul_eq_zero
      hM hLI (N + 1) hij
  change (Wᴴ * P * W) * (Wᴴ * Q * W) = 0
  calc
    (Wᴴ * P * W) * (Wᴴ * Q * W) =
        Wᴴ * (P * ((W * Wᴴ) * (Q * W))) := by
      simp only [Matrix.mul_assoc]
    _ = Wᴴ * (P * (Q * W)) := by rw [hW, Matrix.one_mul]
    _ = Wᴴ * ((P * Q) * W) := by rw [Matrix.mul_assoc]
    _ = 0 := by rw [hPQ, Matrix.zero_mul, Matrix.mul_zero]

/-- The retained sitewise multiplicity operator is the retained
multiplicity-weight factor at chain length `N + 2`.

This is the retained factor in CPSV16, lines 999–1002 and 1013–1016. The
physical-coordinate use of this identity is documented in
`docs/paper-gaps/cpsv16_topological_gibbs_physical_complement.tex`, with the
length-at-least-two scope in
`docs/paper-gaps/cpsv16_topological_gibbs_length_one.tex`. -/
theorem sitewiseRetainedMultiplicityOperator_eq_topologicalMultiplicityWeightFactorSucc
    (H : BNTFusionTensorClause M) (N : ℕ) :
    (Matrix.piKronecker fun _ : Fin (N + 2) ↦ H.retainedMultiplicityOperator) =
      H.topologicalMultiplicityWeightFactorSucc (N + 1) := by
  rw [H.topologicalMultiplicityWeightFactorSucc_eq_diagonal]
  ext x y
  simp only [Matrix.piKronecker_apply, retainedMultiplicityOperator,
    Matrix.diagonal_apply]
  by_cases hxy : x = y
  · subst y
    simp
  · rw [ite_eq_right hxy]
    have hcoord : ∃ n, x n ≠ y n := by
      simpa only [not_forall, not_not] using
        (not_congr funext_iff).mp hxy
    obtain ⟨n, hn⟩ := hcoord
    apply Finset.prod_eq_zero (Finset.mem_univ n)
    rw [ite_eq_right hn]

/-- Every transported `Fin d`-indexed ambient physical projector commutes
with the ambient physical Gibbs factor.

This is `[P_i^(N), e^{-H_N}] = 0` from CPSV16, lines 1013–1016. The
physical-complement transport and mixed-sector cancellation are recorded in
`docs/paper-gaps/cpsv16_topological_gibbs_physical_complement.tex`, and the
length-at-least-two scope in
`docs/paper-gaps/cpsv16_topological_gibbs_length_one.tex`. -/
theorem physicalIndexedAmbientTopologicalSpectralProjectorSuccSucc_commutes_gibbsFactor
    (H : BNTFusionTensorClause M) (hM : IsMPDO M)
    (N : ℕ) (i : Fin d) :
    H.physicalIndexedAmbientTopologicalSpectralProjectorSuccSucc hM N i *
        NormedSpace.exp
          (-H.physicalTopologicalGibbsHamiltonianSuccSucc N) =
      NormedSpace.exp
          (-H.physicalTopologicalGibbsHamiltonianSuccSucc N) *
        H.physicalIndexedAmbientTopologicalSpectralProjectorSuccSucc
          hM N i := by
  let W := (Matrix.piKronecker fun _ : Fin (N + 2) ↦ H.verticalCoisometry)
  let P :=
    H.physicalIndexedTopologicalSpectralProjectorSucc hM (N + 1) i
  let Gp :=
    (Matrix.piKronecker fun _ : Fin (N + 2) ↦ H.physicalMultiplicityWeight)
  let Gr :=
    (Matrix.piKronecker fun _ : Fin (N + 2) ↦ H.retainedMultiplicityOperator)
  have hleft : W * Gp = Gr * W :=
    H.sitewiseVerticalCoisometry_mul_physicalMultiplicityWeight (N + 2)
  have hright : Gp * Wᴴ = Wᴴ * Gr := by
    dsimp only [W]
    rw [Matrix.conjTranspose_piKronecker]
    exact
      H.sitewisePhysicalMultiplicityWeight_mul_conjTranspose_verticalCoisometry
        (N + 2)
  have hcomm : P * Gr = Gr * P := by
    have h :=
      H.physicalIndexedTopologicalSpectralProjectorSucc_commutes_gibbsFactor
        hM N i
    rw [H.exp_neg_topologicalGibbsHamiltonianSuccSucc,
      ← H.sitewiseRetainedMultiplicityOperator_eq_topologicalMultiplicityWeightFactorSucc]
      at h
    exact h
  rw [H.exp_neg_physicalTopologicalGibbsHamiltonianSuccSucc]
  change (Wᴴ * P * W) * Gp = Gp * (Wᴴ * P * W)
  calc
    (Wᴴ * P * W) * Gp = Wᴴ * (P * (W * Gp)) := by
      simp only [Matrix.mul_assoc]
    _ = Wᴴ * (P * (Gr * W)) := by rw [hleft]
    _ = Wᴴ * ((P * Gr) * W) := by rw [Matrix.mul_assoc]
    _ = Wᴴ * ((Gr * P) * W) := by rw [hcomm]
    _ = (Wᴴ * Gr) * (P * W) := by simp only [Matrix.mul_assoc]
    _ = (Gp * Wᴴ) * (P * W) := by rw [hright]
    _ = Gp * (Wᴴ * P * W) := by simp only [Matrix.mul_assoc]

/-- Multiplying one transported physical projector by the ambient Gibbs
factor is exactly the adjoint sitewise transport of the corresponding
retained projector/Gibbs product.

This is the per-sector transport behind the physical density formula in
CPSV16, lines 1013–1016. The complement support argument is recorded in
`docs/paper-gaps/cpsv16_topological_gibbs_physical_complement.tex`, and the
length-at-least-two scope in
`docs/paper-gaps/cpsv16_topological_gibbs_length_one.tex`. -/
theorem physicalIndexedAmbientProjector_mul_gibbsFactor_eq_transport
    (H : BNTFusionTensorClause M) (hM : IsMPDO M)
    (N : ℕ) (i : Fin d) :
    H.physicalIndexedAmbientTopologicalSpectralProjectorSuccSucc hM N i *
        NormedSpace.exp
          (-H.physicalTopologicalGibbsHamiltonianSuccSucc N) =
      (Matrix.piKronecker fun _ : Fin (N + 2) ↦ H.verticalCoisometry)ᴴ *
          (H.physicalIndexedTopologicalSpectralProjectorSucc
              hM (N + 1) i *
            NormedSpace.exp
              (-H.topologicalGibbsHamiltonianSuccSucc N)) *
        (Matrix.piKronecker fun _ : Fin (N + 2) ↦ H.verticalCoisometry) := by
  let W := (Matrix.piKronecker fun _ : Fin (N + 2) ↦ H.verticalCoisometry)
  let P :=
    H.physicalIndexedTopologicalSpectralProjectorSucc hM (N + 1) i
  let Gp :=
    (Matrix.piKronecker fun _ : Fin (N + 2) ↦ H.physicalMultiplicityWeight)
  let Gr :=
    (Matrix.piKronecker fun _ : Fin (N + 2) ↦ H.retainedMultiplicityOperator)
  have hleft : W * Gp = Gr * W :=
    H.sitewiseVerticalCoisometry_mul_physicalMultiplicityWeight (N + 2)
  rw [H.exp_neg_physicalTopologicalGibbsHamiltonianSuccSucc,
    H.exp_neg_topologicalGibbsHamiltonianSuccSucc,
    ← H.sitewiseRetainedMultiplicityOperator_eq_topologicalMultiplicityWeightFactorSucc]
  change (Wᴴ * P * W) * Gp = Wᴴ * (P * Gr) * W
  calc
    (Wᴴ * P * W) * Gp = Wᴴ * (P * (W * Gp)) := by
      simp only [Matrix.mul_assoc]
    _ = Wᴴ * (P * (Gr * W)) := by rw [hleft]
    _ = Wᴴ * (P * Gr) * W := by simp only [Matrix.mul_assoc]

/-- The physical MPDO on a chain of length `N + 2` is the `d`-term sum of
transported physical projectors times the ambient commuting Gibbs factor.

This is the literal physical-coordinate density formula in CPSV16,
lines 1013–1016. The finite complement extension and projector transport are
recorded in
`docs/paper-gaps/cpsv16_topological_gibbs_physical_complement.tex`; the
length-at-least-two scope is recorded in
`docs/paper-gaps/cpsv16_topological_gibbs_length_one.tex`. -/
theorem mpo_eq_sum_physicalIndexedAmbientProjector_mul_gibbsFactor
    (H : BNTFusionTensorClause M) (hM : IsMPDO M) (N : ℕ) :
    mpo M (N + 2) =
      ∑ i : Fin d,
        (H.physicalIndexedTerminalEigenvalue hM i : ℂ) •
          (H.physicalIndexedAmbientTopologicalSpectralProjectorSuccSucc
              hM N i *
            NormedSpace.exp
              (-H.physicalTopologicalGibbsHamiltonianSuccSucc N)) := by
  let W := (Matrix.piKronecker fun _ : Fin (N + 2) ↦ H.verticalCoisometry)
  have hreconstruct :=
    H.singleKrausMap_physicalIndexedGibbsDecomposition_eq_mpo hM N
  rw [← Matrix.conjTranspose_piKronecker] at hreconstruct
  rw [← hreconstruct]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul]
  congr 1
  rw [singleKrausMap_apply]
  rw [Matrix.conjTranspose_conjTranspose]
  change Wᴴ *
        (H.physicalIndexedTopologicalSpectralProjectorSucc
            hM (N + 1) i *
          NormedSpace.exp
            (-H.topologicalGibbsHamiltonianSuccSucc N)) *
      W =
    H.physicalIndexedAmbientTopologicalSpectralProjectorSuccSucc hM N i *
      NormedSpace.exp
        (-H.physicalTopologicalGibbsHamiltonianSuccSucc N)
  exact
    (H.physicalIndexedAmbientProjector_mul_gibbsFactor_eq_transport
      hM N i).symm

/-- The physical-coordinate commuting Gibbs decomposition above one site.

One fixed Hermitian two-site term is translated on every chain of length
`N + 2`; its translates commute. The `Fin d`-indexed nonnegative
eigenweights and ambient physical projectors give pairwise orthogonal
projections which commute with the physical Gibbs factor and reconstruct the
physical MPDO exactly.

Source: CPSV16, lines 1013–1016, with the local two-site convention of
Definition 4.8, lines 831–847.

**Local fix (physical complement):** The retained-row derivation is extended
by zero energy on the orthogonal physical complement, and the retained
projectors are transported through the adjoint sitewise coisometry. This
finite extension is documented in
`docs/paper-gaps/cpsv16_topological_gibbs_physical_complement.tex`. -/
def HasPhysicalTopologicalGibbsDecomposition
    (H : BNTFusionTensorClause M) (hM : IsMPDO M) : Prop :=
  H.physicalTopologicalGibbsLocalTerm.IsHermitian ∧
    ∀ N : ℕ,
      (∀ i j : Fin (N + 2),
        Commute
          (ManyBody.placeAlong (X := fun _ ↦ Fin d)
            (ManyBody.ringWindow (by omega : 2 ≤ N + 2) i) H.physicalTopologicalGibbsLocalTerm)
          (ManyBody.placeAlong (X := fun _ ↦ Fin d)
            (ManyBody.ringWindow (by omega : 2 ≤ N + 2) j)
            H.physicalTopologicalGibbsLocalTerm)) ∧
      (∀ i : Fin d,
        0 ≤ H.physicalIndexedTerminalEigenvalue hM i ∧
          ((H.physicalIndexedAmbientTopologicalSpectralProjectorSuccSucc
              hM N i).IsHermitian ∧
            H.physicalIndexedAmbientTopologicalSpectralProjectorSuccSucc
                hM N i *
              H.physicalIndexedAmbientTopologicalSpectralProjectorSuccSucc
                hM N i =
              H.physicalIndexedAmbientTopologicalSpectralProjectorSuccSucc
                hM N i)) ∧
      (∀ i j : Fin d, i ≠ j →
        H.physicalIndexedAmbientTopologicalSpectralProjectorSuccSucc
              hM N i *
            H.physicalIndexedAmbientTopologicalSpectralProjectorSuccSucc
              hM N j =
          0) ∧
      (∀ i : Fin d,
        H.physicalIndexedAmbientTopologicalSpectralProjectorSuccSucc
              hM N i *
            NormedSpace.exp
              (-H.physicalTopologicalGibbsHamiltonianSuccSucc N) =
          NormedSpace.exp
              (-H.physicalTopologicalGibbsHamiltonianSuccSucc N) *
            H.physicalIndexedAmbientTopologicalSpectralProjectorSuccSucc
              hM N i) ∧
      mpo M (N + 2) =
        ∑ i : Fin d,
          (H.physicalIndexedTerminalEigenvalue hM i : ℂ) •
            (H.physicalIndexedAmbientTopologicalSpectralProjectorSuccSucc
                hM N i *
              NormedSpace.exp
                (-H.physicalTopologicalGibbsHamiltonianSuccSucc N))

/-- A chosen BNT fusion clause has the physical-coordinate commuting Gibbs
decomposition on every chain of length at least two.

Source: CPSV16, lines 1013–1016, with the local two-site convention of
Definition 4.8, lines 831–847.

**Local fix (physical complement):** The retained-row derivation is extended
by zero energy on the orthogonal physical complement, as documented in
`docs/paper-gaps/cpsv16_topological_gibbs_physical_complement.tex`. -/
theorem hasPhysicalTopologicalGibbsDecomposition
    (H : BNTFusionTensorClause M) (hM : IsMPDO M)
    (hLI : (BNTLabelCoefficientFamily.ofChi H.chi).LengthIndependent) :
    H.HasPhysicalTopologicalGibbsDecomposition hM := by
  refine ⟨H.physicalTopologicalGibbsLocalTerm_isHermitian, fun N ↦ ?_⟩
  exact ⟨H.physicalTopologicalGibbsBondSuccSucc_commute N,
    fun i ↦ ⟨H.physicalIndexedTerminalEigenvalue_nonneg hM i,
      H.physicalIndexedAmbientTopologicalSpectralProjectorSuccSucc_isOrthogonalProjection
        hM hLI N i⟩,
    fun _ _ hij ↦
      H.physicalIndexedAmbientTopologicalSpectralProjectorSuccSucc_mul_eq_zero
        hM hLI N hij,
    H.physicalIndexedAmbientTopologicalSpectralProjectorSuccSucc_commutes_gibbsFactor
      hM N,
    H.mpo_eq_sum_physicalIndexedAmbientProjector_mul_gibbsFactor hM N⟩

end MPOTensor.BNTFusionTensorClause

namespace MPOTensor

variable {d D : ℕ}

/-- **Physical-coordinate commuting Gibbs decomposition for a
length-independent RFP MPDO above one site.**

The BNT fusion clause, physical two-site Hamiltonian, nonnegative
eigenweights, and ambient physical projector family are selected or
constructed internally. For every chain of length `N + 2`, the local
translates commute, the projectors are pairwise orthogonal and commute with
the Gibbs factor, and their weighted Gibbs sum is the physical MPDO.

Source: CPSV16, lines 1013–1016, with the local two-site convention of
Definition 4.8, lines 831–847.

**Local fix (physical complement):** The retained-row derivation is extended
by zero energy on the orthogonal physical complement, and the retained
projectors are transported through the adjoint sitewise coisometry. This
finite extension is documented in
`docs/paper-gaps/cpsv16_topological_gibbs_physical_complement.tex`. -/
theorem physicalTopologicalGibbsDecomposition_of_isRFPViaTS
    (M : MPOTensor d D) (hHorizontal : IsHorizontalCF M)
    (hM : IsMPDO M) (hRFP : IsRFPViaTS M)
    (hLI : (BNTLabelCoefficientFamily.ofChi
      (rfpBNTFusionTensorClause M hHorizontal hM hRFP).chi).LengthIndependent) :
    let H := rfpBNTFusionTensorClause M hHorizontal hM hRFP
    H.HasPhysicalTopologicalGibbsDecomposition hM := by
  dsimp only
  exact
    BNTFusionTensorClause.hasPhysicalTopologicalGibbsDecomposition
      (rfpBNTFusionTensorClause M hHorizontal hM hRFP) hM hLI

end MPOTensor
end

end

section

open scoped Matrix BigOperators ComplexOrder Kronecker

noncomputable section

namespace MPOTensor

variable {d D : ℕ}

/-- A BNT fusion tensor clause selected from the literal CPSV canonical-form
and renormalization fixed-point hypotheses.

Source: CPSV16, Theorem 4.14(i),(iii), lines 972--993, and Appendix C.4,
lines 1929--2046 of `Papers/1606.00608/MPDO-22-12-17-2.tex`.

**Local fix (Figure-11 fixed-pair support):** For a fixed input pair, the active
output family may be empty. See
`docs/paper-gaps/cpsv16_figure11_per_pair_support.tex`.

**Local fix (Figure-11 fusion coisometry):** The retained-row fusion map is a
coisometry onto the active output sectors and satisfies exact adjoint
reconstruction; no full-space isometry is asserted. See
`docs/paper-gaps/cpsv16_figure11_fusion_coisometry.tex`. -/
noncomputable def cpsvRFPBNTFusionTensorClause (M : MPOTensor d D)
    (hCanonical : MPSTensor.IsCPSVCanonicalForm M.toMPSTensor)
    (hM : IsMPDO M) (hRFP : IsRFPViaTS M) :
    BNTFusionTensorClause M :=
  Classical.choice
    (HasBNTFusionTensorClause.of_isRFPViaTS M hCanonical hM hRFP)

/-- **Physical-coordinate commuting Gibbs decomposition for a literal CPSV
RFP MPDO above one site.**

For a tensor in literal CPSV canonical form which generates MPDOs and satisfies
the renormalization fixed-point condition, select its BNT fusion tensor clause.
If the associated coefficient family is independent of the chain length, then
the selected clause gives the physical-coordinate commuting Gibbs
decomposition on every chain of length `N + 2`.

Source: CPSV16, Theorem 4.14(i),(iii), lines 972--993, Theorem 4.15,
lines 1013--1016, and Appendix C.4, lines 1929--2046 of
`Papers/1606.00608/MPDO-22-12-17-2.tex`.

**Local fix (Figure-11 fixed-pair support):** For a fixed input pair, the active
output family may be empty. See
`docs/paper-gaps/cpsv16_figure11_per_pair_support.tex`.

**Local fix (Figure-11 fusion coisometry):** The retained-row fusion map is a
coisometry onto the active output sectors and satisfies exact adjoint
reconstruction; no full-space isometry is asserted. See
`docs/paper-gaps/cpsv16_figure11_fusion_coisometry.tex`.

**Local fix (physical complement):** The retained energy is extended by zero
on the orthogonal physical complement, and the retained projectors are
transported through the adjoint sitewise coisometry. See
`docs/paper-gaps/cpsv16_topological_gibbs_physical_complement.tex`. -/
theorem physicalTopologicalGibbsDecomposition_of_isRFPViaTS_of_cpsvCanonicalForm
    (M : MPOTensor d D)
    (hCanonical : MPSTensor.IsCPSVCanonicalForm M.toMPSTensor)
    (hM : IsMPDO M) (hRFP : IsRFPViaTS M)
    (hLI : (BNTLabelCoefficientFamily.ofChi
      (cpsvRFPBNTFusionTensorClause M hCanonical hM hRFP).chi).LengthIndependent) :
    let H := cpsvRFPBNTFusionTensorClause M hCanonical hM hRFP
    H.HasPhysicalTopologicalGibbsDecomposition hM := by
  dsimp only
  exact
    BNTFusionTensorClause.hasPhysicalTopologicalGibbsDecomposition
      (cpsvRFPBNTFusionTensorClause M hCanonical hM hRFP) hM hLI

end MPOTensor
end

end
