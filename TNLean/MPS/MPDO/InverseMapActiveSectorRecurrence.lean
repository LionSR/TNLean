/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.MatrixAux
import TNLean.MPS.MPDO.PhysicalSectorPruning
import TNLean.MPS.MPDO.PhysicalSectorVirtualSpanning
import TNLean.MPS.MPDO.SectorEtaOperator
import TNLean.MPS.MPDO.SectorRecurrence
import TNLean.MPS.MPDO.RecurrentSectorRephasing

/-!
# Recurrence after reparameterizing zero-weight sectors

For the inverse-map physical-sector factorization, every positive-weight
Hayashi sector contains a nonzero virtual matrix. Otherwise the corresponding
middle-site block of the three-site closure would vanish, contrary to its
expression as a nonzero weight times two trace-one density matrices.

After zero-weight sectors are reparameterized, every endpoint of a nonzero
neighboring operator has positive weight. Injectivity supplies spanning by the
sector virtual matrices, so the triangle-closing argument proves recurrence of
the neighboring support. The recurrent-support rephasing theorem then gives a
physical-sector factorization with positive semidefinite neighboring
operators, without an additional recurrence hypothesis.

## References

- [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Appendix C.2, Lemma C.4 (`propSN`), lines 1406--1450
- `docs/paper-gaps/cpgsv17_mpdo_sal_zcl_eta_local_structure.tex`
-/

open scoped Matrix ComplexOrder BigOperators

namespace MPOTensor

variable {d D : ℕ}

/-- Conjugating the middle physical index of a three-site closure is the same
as replacing the middle MPO matrix by its conjugated physical matrix.

Source: arXiv:1606.00608, Appendix C.2, lines 1421--1438. -/
theorem conjugated_middle_threeSiteClosure
    {rho : Matrix (Fin d × Fin d × Fin d) (Fin d × Fin d × Fin d) ℂ}
    (K : MPOTensor d D) (R : Matrix (Fin D) (Fin D) ℂ)
    (hρ : IsThreeSiteClosure K R rho)
    (U : Matrix (Fin d) (Fin d) ℂ)
    (i₁ j₁ i₃ j₃ b b' : Fin d) :
    (∑ i₂ : Fin d, ∑ j₂ : Fin d,
      U b i₂ * rho (i₁, i₂, i₃) (j₁, j₂, j₃) * star (U b' j₂)) =
      Matrix.trace
        (K i₁ j₁ * conjugatePhysical K U b b' * K i₃ j₃ * R) := by
  have hmiddle : conjugatePhysical K U b b' =
      ∑ i₂ : Fin d, ∑ j₂ : Fin d,
        (U b i₂ * star (U b' j₂)) • K i₂ j₂ := by
    have h := PhysicalSectorFactorization.changePhysicalBasis_apply_eq_sum U K b b'
    rw [Fintype.sum_prod_type] at h
    exact h
  rw [hmiddle]
  simp only [Matrix.mul_sum, Matrix.mul_smul, Matrix.sum_mul,
    Matrix.smul_mul, Matrix.trace_sum, Matrix.trace_smul, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i₂ _
  apply Finset.sum_congr rfl
  intro j₂ _
  rw [hρ i₁ i₂ i₃ j₁ j₂ j₃]
  ring

/-- Both endpoints of a nonzero neighboring operator in the zero-weight
reparameterized inverse-map factorization have positive Hayashi weight.

The source weight is nonzero because its right tensor was set to zero when
inactive. The target weight is nonzero because a zero target weight already
makes the original neighboring operator vanish.

**Local fix (inactive sectors):** see
`docs/paper-gaps/cpgsv17_mpdo_sal_zcl_eta_local_structure.tex`.

Source: arXiv:1606.00608, Appendix C.2, equation `etarl`, lines 1441--1445. -/
theorem probability_ne_zero_of_reparameterized_neighboringOperator_ne_zero
    {rho : Matrix (Fin d × Fin d × Fin d) (Fin d × Fin d × Fin d) ℂ}
    (K : MPOTensor d D) (hK : K.IsInjective)
    (R : Matrix (Fin D) (Fin D) ℂ) (hρ : IsThreeSiteClosure K R rho)
    (hη : EtaStructure rho) (alpha beta : Fin D) (hm : R beta alpha ≠ 0)
    {k h : Fin hη.m}
    (hkh : (zeroWeightReparameterizedInverseMapPhysicalSectorFactorization
      K hK R hρ hη alpha beta hm).neighboringOperator k h ≠ 0) :
    hη.p k ≠ 0 ∧ hη.p h ≠ 0 := by
  constructor
  · intro hk
    rw [zeroWeightReparameterizedInverseMapPhysicalSectorFactorization_neighboringOperator,
      if_neg (fun hne ↦ hne hk)] at hkh
    exact hkh rfl
  · intro hh
    rw [zeroWeightReparameterizedInverseMapPhysicalSectorFactorization_neighboringOperator,
      sectorEta_eq_zero_of_target_weight_eq_zero K hK hη R alpha beta k h hh] at hkh
    split at hkh <;> exact hkh rfl

/-- Every positive-weight Hayashi sector contains a nonzero virtual matrix in
the deactivated inverse-map factorization.

The two trace-one sector density matrices have nonzero diagonal entries. If
all virtual matrices in the sector vanished, the corresponding conjugated
middle-site MPO matrix would be zero. The closure identity would then make the
associated diagonal entry of the three-site state vanish, contradicting the
Hayashi block decomposition and the nonzero sector weight.

**Local fix (inactive sectors):** the ambient physical decomposition is
unchanged; only right tensors in zero-weight sectors are set to zero. This
correction is recorded in
`docs/paper-gaps/cpgsv17_mpdo_sal_zcl_eta_local_structure.tex`.

Source: arXiv:1606.00608, Appendix C.2, equations `formK` and `etarl`, lines
1434--1445. -/
theorem exists_active_sectorVirtualMatrix_ne_zero
    {rho : Matrix (Fin d × Fin d × Fin d) (Fin d × Fin d × Fin d) ℂ}
    (K : MPOTensor d D) (hK : K.IsInjective)
    (R : Matrix (Fin D) (Fin D) ℂ) (hρ : IsThreeSiteClosure K R rho)
    (hη : EtaStructure rho) (alpha beta : Fin D) (hm : R beta alpha ≠ 0)
    (k : Fin hη.m) (hk : hη.p k ≠ 0) :
    ∃ x y :
        (zeroWeightReparameterizedInverseMapPhysicalSectorFactorization
          K hK R hρ hη alpha beta hm).SectorIndex k,
      (zeroWeightReparameterizedInverseMapPhysicalSectorFactorization
        K hK R hρ hη alpha beta hm).sectorVirtualMatrix k x y ≠ 0 := by
  classical
  let F := zeroWeightReparameterizedInverseMapPhysicalSectorFactorization
    K hK R hρ hη alpha beta hm
  by_contra hall
  push Not at hall
  obtain ⟨⟨i₁, l⟩, hleft⟩ :=
    Matrix.exists_diagonal_ne_zero_of_trace_eq_one
      (hη.ρ_left k) (hη.hρ_left_dm k).2
  obtain ⟨⟨r, i₃⟩, hright⟩ :=
    Matrix.exists_diagonal_ne_zero_of_trace_eq_one
      (hη.ρ_right k) (hη.hρ_right_dm k).2
  let x : F.SectorIndex k := (l, r)
  let b : Fin d := hη.decompB.symm ⟨k, (l, r)⟩
  have hmid : conjugatePhysical K hη.U_B b b = 0 := by
    ext gamma delta
    have hslice := F.transformedPhysicalSlice_apply_same gamma delta k x x
    have hzero := congrFun (congrFun (hall x x) gamma) delta
    change
      Matrix.reindex hη.decompB hη.decompB
        ((hη.U_B : Matrix (Fin d) (Fin d) ℂ) *
          physicalSlice K gamma delta *
            (hη.U_B : Matrix (Fin d) (Fin d) ℂ)ᴴ)
          ⟨k, (l, r)⟩ ⟨k, (l, r)⟩ = _ at hslice
    rw [Matrix.reindex_apply, Matrix.submatrix_apply] at hslice
    change (((hη.U_B : Matrix (Fin d) (Fin d) ℂ) *
      physicalSlice K gamma delta *
        (hη.U_B : Matrix (Fin d) (Fin d) ℂ)ᴴ) b b) = _ at hslice
    change conjugatePhysical K hη.U_B b b gamma delta = 0
    exact hslice.trans hzero
  have hs := congrFun (congrFun hη.h_state
    (i₁, (⟨k, (l, r)⟩, i₃))) (i₁, (⟨k, (l, r)⟩, i₃))
  rw [Matrix.reindex_apply, Matrix.submatrix_apply] at hs
  have hindex : (HayashiMarkov.abcEquiv hη.decompB).symm
      (i₁, (⟨k, (l, r)⟩, i₃)) = (i₁, b, i₃) := by
    simp [HayashiMarkov.abcEquiv, b]
  rw [hindex, HayashiMarkov.liftB_conj_apply,
    HayashiMarkov.blockState_apply] at hs
  have hs' :
      (∑ i₂ : Fin d, ∑ j₂ : Fin d,
        (hη.U_B : Matrix (Fin d) (Fin d) ℂ) b i₂ *
          rho (i₁, i₂, i₃) (i₁, j₂, i₃) *
            star ((hη.U_B : Matrix (Fin d) (Fin d) ℂ) b j₂)) =
        (hη.p k : ℂ) * hη.ρ_left k (i₁, l) (i₁, l) *
          hη.ρ_right k (r, i₃) (r, i₃) := by
    simpa using hs
  have hclosure := conjugated_middle_threeSiteClosure
    K R hρ hη.U_B i₁ i₁ i₃ i₃ b b
  rw [hclosure, hmid] at hs'
  simp only [Matrix.mul_zero, Matrix.zero_mul, Matrix.trace_zero] at hs'
  exact mul_ne_zero (mul_ne_zero (Complex.ofReal_ne_zero.mpr hk) hleft) hright hs'.symm

/-- The nonzero neighboring support of the deactivated inverse-map
factorization is recurrent.

Indeed, every nonzero edge has positive-weight endpoints, hence each endpoint
contains a nonzero virtual matrix. Injectivity gives spanning by all sector
virtual matrices, and every edge therefore closes through a third sector.

**Local fix (inactive sectors):** see
`docs/paper-gaps/cpgsv17_mpdo_sal_zcl_eta_local_structure.tex`.

Source: arXiv:1606.00608, Appendix C.2, Lemma C.4 (`propSN`), lines
1406--1450. -/
theorem zeroWeightReparameterizedInverseMapPhysicalSectorFactorization_isRecurrentSupport
    {rho : Matrix (Fin d × Fin d × Fin d) (Fin d × Fin d × Fin d) ℂ}
    (K : MPOTensor d D) (hK : K.IsInjective)
    (R : Matrix (Fin D) (Fin D) ℂ) (hρ : IsThreeSiteClosure K R rho)
    (hη : EtaStructure rho) (alpha beta : Fin D) (hm : R beta alpha ≠ 0) :
    IsRecurrentSupport (fun k h ↦
      (zeroWeightReparameterizedInverseMapPhysicalSectorFactorization
        K hK R hρ hη alpha beta hm).neighboringOperator k h) := by
  let F := zeroWeightReparameterizedInverseMapPhysicalSectorFactorization
    K hK R hρ hη alpha beta hm
  intro k h hkh
  apply F.neighboringOperator_reaches_of_ne_zero
    (F.sectorVirtualMatrixFamily_span_eq_top hK) _ hkh
  intro a b hab
  obtain ⟨ha, hb⟩ :=
    probability_ne_zero_of_reparameterized_neighboringOperator_ne_zero
      K hK R hρ hη alpha beta hm hab
  exact ⟨exists_active_sectorVirtualMatrix_ne_zero
    K hK R hρ hη alpha beta hm a ha,
    exists_active_sectorVirtualMatrix_ne_zero
      K hK R hρ hη alpha beta hm b hb⟩

/-- The zero-weight reparameterized inverse-map factorization admits a
reciprocal sector rephasing with positive semidefinite neighboring operators.

This exposes the coherent rephasing witness used both for the positive
factorization and for the active trace-matrix primitivity theorem.

**Local fix (inactive sectors):** see
`docs/paper-gaps/cpgsv17_mpdo_sal_zcl_eta_local_structure.tex`.

Source: arXiv:1606.00608, Appendix C.2, Lemma C.4 (`propSN`), lines
1406--1450. -/
theorem exists_rephase_zeroWeightInverseMap_posSemidef
    {rho : Matrix (Fin d × Fin d × Fin d) (Fin d × Fin d × Fin d) ℂ}
    (K : MPOTensor d D) (hK : K.IsInjective)
    (R : Matrix (Fin D) (Fin D) ℂ) (hρ : IsThreeSiteClosure K R rho)
    (hη : EtaStructure rho) (alpha beta : Fin D) (hm : R beta alpha ≠ 0)
    (hM : IsMPDO K) :
    let F := zeroWeightReparameterizedInverseMapPhysicalSectorFactorization
      K hK R hρ hη alpha beta hm
    ∃ z : Fin F.sectorCount → Circle,
      ∀ k h, ((F.rephase z).neighboringOperator k h).PosSemidef := by
  let F := zeroWeightReparameterizedInverseMapPhysicalSectorFactorization
    K hK R hρ hη alpha beta hm
  let eta : etaOperators hη := fun k h ↦ F.neighboringOperator k h
  have hcyc : ∀ {N : ℕ} [NeZero N] (q : Fin N → Fin hη.m),
      (cyclicEtaTensorProduct hη eta q).PosSemidef := by
    intro N _ q
    exact cyclicEtaTensorProduct_posSemidef K hη F.leftTensor F.rightTensor
      F.factorization (hM N) q
  have hrec : IsRecurrentSupport eta :=
    zeroWeightReparameterizedInverseMapPhysicalSectorFactorization_isRecurrentSupport
      K hK R hρ hη alpha beta hm
  obtain ⟨z, hz⟩ :=
    exists_vertexPhase_smul_posSemidef hη eta hcyc hrec
  refine ⟨z, fun k h ↦ ?_⟩
  rw [F.rephase_neighboringOperator]
  exact hz k h

/-- The inverse-map construction admits a physical-sector factorization whose
neighboring operators are all positive semidefinite, with no recurrence
hypothesis.

Zero-weight sectors are first deactivated without changing the physical
factorization. Their support is recurrent by the preceding theorem. Positivity
of all cyclic sector products then yields a coherent vertex rephasing.

**Local fix (inactive sectors):** see
`docs/paper-gaps/cpgsv17_mpdo_sal_zcl_eta_local_structure.tex`.

Source: arXiv:1606.00608, Appendix C.2, Lemma C.4 (`propSN`), lines
1406--1450. -/
theorem exists_positive_inverseMapPhysicalSectorFactorization
    {rho : Matrix (Fin d × Fin d × Fin d) (Fin d × Fin d × Fin d) ℂ}
    (K : MPOTensor d D) (hK : K.IsInjective)
    (R : Matrix (Fin D) (Fin D) ℂ) (hρ : IsThreeSiteClosure K R rho)
    (hη : EtaStructure rho) (alpha beta : Fin D) (hm : R beta alpha ≠ 0)
    (hM : IsMPDO K) :
    ∃ F : PhysicalSectorFactorization K,
      ∀ k h, (F.neighboringOperator k h).PosSemidef := by
  let F := zeroWeightReparameterizedInverseMapPhysicalSectorFactorization
    K hK R hρ hη alpha beta hm
  obtain ⟨z, hpos⟩ := exists_rephase_zeroWeightInverseMap_posSemidef
    K hK R hρ hη alpha beta hm hM
  exact ⟨F.rephase z, hpos⟩

/-- Every injective MPO tensor satisfying the strong area law admits a
physical-sector factorization with positive semidefinite neighboring
operators.

This is the positive local structure asserted in Lemma C.4. Zero-weight
Hayashi sectors remain present in the physical decomposition, but their unused
right tensors are set to zero before the coherent rephasing.

**Local fix (inactive sectors):** see
`docs/paper-gaps/cpgsv17_mpdo_sal_zcl_eta_local_structure.tex`.

Source: arXiv:1606.00608, Appendix C.2, Lemma C.4 (`propSN`), lines
1406--1450. -/
theorem exists_positive_physicalSectorFactorization_of_isSAL
    (K : MPOTensor d D) (hK : K.IsInjective) (hSAL : IsSAL K) :
    ∃ F : PhysicalSectorFactorization K,
      ∀ k h, (F.neighboringOperator k h).PosSemidef := by
  obtain ⟨hη⟩ := exists_etaStructure_reducedBlockState_of_isSAL K hSAL
  obtain ⟨beta, alpha, hm⟩ :=
    exists_normalizedFourSiteTail_entry_ne_zero
      K ((Classical.choose_spec hSAL).1 4 (by omega))
  exact exists_positive_inverseMapPhysicalSectorFactorization K hK
    (normalizedFourSiteTail K) (isThreeSiteClosure_reducedBlockState K)
    hη alpha beta hm (Classical.choose hSAL)

/-- Every injective MPO tensor satisfying the strong area law has the
positive commuting nearest-neighbor product structure of Proposition C.8.

Source: arXiv:1606.00608, Appendix C.2, Proposition C.8 (`3to4`), lines
1571--1593. -/
theorem nonempty_etaLocalStructureData_of_isSAL
    (K : MPOTensor d D) (hK : K.IsInjective) (hSAL : IsSAL K) :
    Nonempty (EtaLocalStructureData K) := by
  obtain ⟨F, hF⟩ := exists_positive_physicalSectorFactorization_of_isSAL K hK hSAL
  exact ⟨F.etaLocalStructureData hF⟩

end MPOTensor
