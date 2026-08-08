/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.InverseMapActiveSectorRecurrence
import TNLean.MPS.MPDO.PhysicalSectorRephasing
import TNLean.MPS.MPDO.PhysicalSectorTraceMatrix

/-!
# Primitivity of the active inverse-map sector trace matrix

The coherently rephased inverse-map physical-sector factorization has a
primitive trace matrix on the positive-weight Hayashi sectors. Zero-weight
sectors remain in the physical direct sum; they are omitted only from the
auxiliary trace matrix because the source-faithful reparameterization makes
all incident neighboring operators vanish.

Source: arXiv:1606.00608, Appendix C.2, Lemma C.4 (`propSN`), lines
1406--1471.
-/

open scoped Matrix ComplexOrder BigOperators

namespace MPOTensor

variable {d D : ℕ}
  {rho : Matrix (Fin d × Fin d × Fin d) (Fin d × Fin d × Fin d) ℂ}

/-- A zero-weight sector has zero virtual matrices in the source-faithful
zero-weight reparameterization.

**Local fix (inactive sectors):** see
`docs/paper-gaps/cpgsv17_mpdo_sal_zcl_eta_local_structure.tex`.

Source: arXiv:1606.00608, Appendix C.2, equations `formK` and `etarl`, lines
1434--1445. -/
theorem zeroWeightReparameterized_sectorVirtualMatrix_eq_zero
    (K : MPOTensor d D) (hK : K.IsInjective)
    (R : Matrix (Fin D) (Fin D) ℂ) (hρ : IsThreeSiteClosure K R rho)
    (hη : EtaStructure rho) (alpha beta : Fin D) (hm : R beta alpha ≠ 0)
    (k : Fin hη.m) (hk : hη.p k = 0)
    (x y : (zeroWeightReparameterizedInverseMapPhysicalSectorFactorization
      K hK R hρ hη alpha beta hm).SectorIndex k) :
    (zeroWeightReparameterizedInverseMapPhysicalSectorFactorization
      K hK R hρ hη alpha beta hm).sectorVirtualMatrix k x y = 0 := by
  ext gamma delta
  rw [PhysicalSectorFactorization.sectorVirtualMatrix]
  have hleft :
      (zeroWeightReparameterizedInverseMapPhysicalSectorFactorization
        K hK R hρ hη alpha beta hm).leftTensor k gamma = 0 := by
    change sectorTensorL K hK hη R alpha beta k gamma = 0
    exact sectorTensorL_eq_zero_of_weight_eq_zero
      K hK hη R alpha beta k gamma hk
  rw [hleft, Matrix.zero_apply, zero_mul, Matrix.zero_apply]

/-- Every neighboring operator incident to a zero-weight sector vanishes after
zero-weight reparameterization and coherent rephasing.

The reparameterization sets the right tensor of an inactive source sector to
zero, while its left tensor was already zero. Thus both outgoing and incoming
neighboring operators vanish.

**Local fix (inactive sectors):** see
`docs/paper-gaps/cpgsv17_mpdo_sal_zcl_eta_local_structure.tex`.

Source: arXiv:1606.00608, Appendix C.2, equations `formK` and `etarl`, lines
1434--1445. -/
theorem rephase_zeroWeightReparameterized_neighboringOperator_eq_zero_of_incident
    (K : MPOTensor d D) (hK : K.IsInjective)
    (R : Matrix (Fin D) (Fin D) ℂ) (hρ : IsThreeSiteClosure K R rho)
    (hη : EtaStructure rho) (alpha beta : Fin D) (hm : R beta alpha ≠ 0)
    (z : Fin hη.m → Circle) (k h : Fin hη.m)
    (hzero : hη.p k = 0 ∨ hη.p h = 0) :
    let F := zeroWeightReparameterizedInverseMapPhysicalSectorFactorization
      K hK R hρ hη alpha beta hm
    ((F.rephase z).neighboringOperator k h) = 0 := by
  let F := zeroWeightReparameterizedInverseMapPhysicalSectorFactorization
    K hK R hρ hη alpha beta hm
  change (F.rephase z).neighboringOperator k h = 0
  rw [F.rephase_neighboringOperator]
  suffices F.neighboringOperator k h = 0 by simp [this]
  rcases hzero with hk | hh
  · rw [zeroWeightReparameterizedInverseMapPhysicalSectorFactorization_neighboringOperator,
      if_neg (not_ne_iff.mpr hk)]
  · rw [zeroWeightReparameterizedInverseMapPhysicalSectorFactorization_neighboringOperator]
    split
    · exact sectorEta_eq_zero_of_target_weight_eq_zero
        K hK hη R alpha beta k h hh
    · rfl

/-- The source inverse-map factorization admits a coherent rephasing retaining the
active-sector witnesses used to prove primitivity and the Case-I coefficient equations.

**Local fix (inactive sectors):** the physical factorization retains every
zero-weight sector. The active matrix and its spanning family use only the
nonzero-weight Hayashi sectors. See
`docs/paper-gaps/cpgsv17_mpdo_sal_zcl_eta_local_structure.tex`.

**Local fix (periodicity):** the returned triangle witness gives closed walks of
lengths two and three in place of the source's blocking of periodic components.
See the same paper-gap note.

Source: arXiv:1606.00608, Appendix C.2, Lemma C.4 (`propSN`), lines
1406--1471. -/
theorem exists_rephased_inverseMap_activeSectorTraceMatrix_primitivity_witnesses
    (K : MPOTensor d D) (hK : K.IsInjective)
    (R : Matrix (Fin D) (Fin D) ℂ) (hρ : IsThreeSiteClosure K R rho)
    (hη : EtaStructure rho) (alpha beta : Fin D) (hm : R beta alpha ≠ 0)
    (hM : IsMPDO K) :
    let F := zeroWeightReparameterizedInverseMapPhysicalSectorFactorization
      K hK R hρ hη alpha beta hm
    ∃ z : Fin F.sectorCount → Circle,
      (∀ k h, ((F.rephase z).neighboringOperator k h).PosSemidef) ∧
        Submodule.span ℂ
          (Set.range ((F.rephase z).activeSectorOneSiteMatrixFamily hη.p)) = ⊤ ∧
        (∀ k : (F.rephase z).ActiveSector hη.p,
          ∃ x y : (F.rephase z).SectorIndex k,
            (F.rephase z).sectorVirtualMatrix k x y ≠ 0) ∧
        (∀ {k h : (F.rephase z).ActiveSector hη.p},
          (F.rephase z).neighboringOperator k h ≠ 0 →
            ∃ j : (F.rephase z).ActiveSector hη.p,
              (F.rephase z).neighboringOperator h j ≠ 0 ∧
                (F.rephase z).neighboringOperator j k ≠ 0) ∧
        (∀ k, hη.p k = 0 → ∀ gamma, (F.rephase z).leftTensor k gamma = 0) ∧
        Nonempty ((F.rephase z).ActiveSector hη.p) := by
  let F := zeroWeightReparameterizedInverseMapPhysicalSectorFactorization
    K hK R hρ hη alpha beta hm
  change ∃ z : Fin F.sectorCount → Circle,
    (∀ k h, ((F.rephase z).neighboringOperator k h).PosSemidef) ∧
      Submodule.span ℂ
        (Set.range ((F.rephase z).activeSectorOneSiteMatrixFamily hη.p)) = ⊤ ∧
      (∀ k : (F.rephase z).ActiveSector hη.p,
        ∃ x y : (F.rephase z).SectorIndex k,
          (F.rephase z).sectorVirtualMatrix k x y ≠ 0) ∧
      (∀ {k h : (F.rephase z).ActiveSector hη.p},
        (F.rephase z).neighboringOperator k h ≠ 0 →
          ∃ j : (F.rephase z).ActiveSector hη.p,
            (F.rephase z).neighboringOperator h j ≠ 0 ∧
              (F.rephase z).neighboringOperator j k ≠ 0) ∧
      (∀ k, hη.p k = 0 → ∀ gamma, (F.rephase z).leftTensor k gamma = 0) ∧
      Nonempty ((F.rephase z).ActiveSector hη.p)
  obtain ⟨z, hpos⟩ := exists_rephase_zeroWeightInverseMap_posSemidef
    K hK R hρ hη alpha beta hm hM
  have hspanAll :
      Submodule.span ℂ (Set.range F.sectorVirtualMatrixFamily) = ⊤ :=
    F.sectorVirtualMatrixFamily_span_eq_top hK
  have hinactiveVirtual : ∀ k, hη.p k = 0 →
      ∀ x y : F.SectorIndex k, F.sectorVirtualMatrix k x y = 0 := by
    intro k hk x y
    exact zeroWeightReparameterized_sectorVirtualMatrix_eq_zero
      K hK R hρ hη alpha beta hm k hk x y
  have hspanF : Submodule.span ℂ
      (Set.range (F.activeSectorOneSiteMatrixFamily hη.p)) = ⊤ :=
    F.activeSectorOneSiteMatrixFamily_span_eq_top hη.p hspanAll hinactiveVirtual
  have hfamily :
      (F.rephase z).activeSectorOneSiteMatrixFamily hη.p =
        F.activeSectorOneSiteMatrixFamily hη.p := by
    funext q
    simp [PhysicalSectorFactorization.activeSectorOneSiteMatrixFamily]
  have hspan : Submodule.span ℂ
      (Set.range ((F.rephase z).activeSectorOneSiteMatrixFamily hη.p)) = ⊤ := by
    rw [hfamily]
    exact hspanF
  have hnonzero : ∀ k : (F.rephase z).ActiveSector hη.p,
      ∃ x y : (F.rephase z).SectorIndex k,
        (F.rephase z).sectorVirtualMatrix k x y ≠ 0 := by
    intro k
    obtain ⟨x, y, hxy⟩ := exists_active_sectorVirtualMatrix_ne_zero
      K hK R hρ hη alpha beta hm k.1 k.property
    exact ⟨x, y, by simpa using hxy⟩
  have hedgeNonzero : ∀ {k h}, F.neighboringOperator k h ≠ 0 →
      (∃ x y : F.SectorIndex k, F.sectorVirtualMatrix k x y ≠ 0) ∧
        ∃ x y : F.SectorIndex h, F.sectorVirtualMatrix h x y ≠ 0 := by
    intro k h hkh
    obtain ⟨hk, hh⟩ :=
      probability_ne_zero_of_reparameterized_neighboringOperator_ne_zero
        K hK R hρ hη alpha beta hm hkh
    exact ⟨exists_active_sectorVirtualMatrix_ne_zero
      K hK R hρ hη alpha beta hm k hk,
      exists_active_sectorVirtualMatrix_ne_zero
        K hK R hρ hη alpha beta hm h hh⟩
  have htriangle : ∀ {k h : (F.rephase z).ActiveSector hη.p},
      (F.rephase z).neighboringOperator k h ≠ 0 →
        ∃ j : (F.rephase z).ActiveSector hη.p,
          (F.rephase z).neighboringOperator h j ≠ 0 ∧
            (F.rephase z).neighboringOperator j k ≠ 0 := by
    intro k h hkh
    have hkhF : F.neighboringOperator k.1 h.1 ≠ 0 :=
      (F.rephase_neighboringOperator_ne_zero_iff z k.1 h.1).1 hkh
    obtain ⟨j, hhj, hjk⟩ :=
      F.exists_two_edge_return_of_neighboringOperator_ne_zero
        hspanAll hedgeNonzero hkhF
    have hj : hη.p j ≠ 0 :=
      (probability_ne_zero_of_reparameterized_neighboringOperator_ne_zero
        K hK R hρ hη alpha beta hm hhj).2
    exact ⟨⟨j, hj⟩,
      (F.rephase_neighboringOperator_ne_zero_iff z h.1 j).2 hhj,
      (F.rephase_neighboringOperator_ne_zero_iff z j k.1).2 hjk⟩
  have hinactive : ∀ k, hη.p k = 0 →
      ∀ gamma, (F.rephase z).leftTensor k gamma = 0 := by
    intro k hk gamma
    change (z k : ℂ) • sectorTensorL K hK hη R alpha beta k gamma = 0
    rw [sectorTensorL_eq_zero_of_weight_eq_zero K hK hη R alpha beta k gamma hk,
      smul_zero]
  have hactive : ∃ k, hη.p k ≠ 0 := by
    by_contra h
    simp only [not_exists, not_ne_iff] at h
    have hzero_one : (0 : ℝ) = 1 := by
      simpa [h] using hη.hp_sum
    exact zero_ne_one hzero_one
  have hne : Nonempty ((F.rephase z).ActiveSector hη.p) := by
    obtain ⟨k, hk⟩ := hactive
    exact ⟨⟨k, hk⟩⟩
  exact ⟨z, hpos, hspan, hnonzero, htriangle, hinactive, hne⟩

/-- The source inverse-map factorization admits a coherent rephasing whose
active trace matrix is primitive.

**Local fix (inactive sectors):** the physical factorization retains every
zero-weight sector. Primitivity concerns only the subtype on which the Hayashi
weight is nonzero. See
`docs/paper-gaps/cpgsv17_mpdo_sal_zcl_eta_local_structure.tex`.

**Local fix (periodicity):** the proof uses closed walks of lengths two and
three in place of the source's blocking of periodic components. See the same
paper-gap note.

Source: arXiv:1606.00608, Appendix C.2, Lemma C.4 (`propSN`), lines
1406--1471. -/
theorem exists_rephased_inverseMap_activeSectorTraceMatrix_isPrimitive
    (K : MPOTensor d D) (hK : K.IsInjective)
    (R : Matrix (Fin D) (Fin D) ℂ) (hρ : IsThreeSiteClosure K R rho)
    (hη : EtaStructure rho) (alpha beta : Fin D) (hm : R beta alpha ≠ 0)
    (hM : IsMPDO K) :
    let F := zeroWeightReparameterizedInverseMapPhysicalSectorFactorization
      K hK R hρ hη alpha beta hm
    ∃ z : Fin F.sectorCount → Circle,
      (∀ k h, ((F.rephase z).neighboringOperator k h).PosSemidef) ∧
        Matrix.IsPrimitive ((F.rephase z).activeSectorTraceMatrix hη.p) := by
  let F := zeroWeightReparameterizedInverseMapPhysicalSectorFactorization
    K hK R hρ hη alpha beta hm
  obtain ⟨z, hpos, hspan, hnonzero, htriangle, _, _⟩ :=
    exists_rephased_inverseMap_activeSectorTraceMatrix_primitivity_witnesses
      K hK R hρ hη alpha beta hm hM
  exact ⟨z, hpos, (F.rephase z).activeSectorTraceMatrix_isPrimitive
    hη.p hpos hspan hnonzero htriangle⟩

/-- Every injective MPO tensor satisfying the strong area law admits a
positive physical-sector factorization whose active trace matrix is primitive.

The accompanying weights are nonnegative and sum to one. Zero-weight sectors
remain in the physical factorization and are omitted only from the auxiliary
trace matrix.

**Local fix (inactive sectors):** see
`docs/paper-gaps/cpgsv17_mpdo_sal_zcl_eta_local_structure.tex`.

**Local fix (periodicity):** the proof uses closed walks of lengths two and
three in place of the source's blocking of periodic components. See the same
paper-gap note.

Source: arXiv:1606.00608, Appendix C.2, Lemma C.4 (`propSN`), lines
1406--1471. -/
theorem exists_positive_physicalSectorFactorization_activeSectorTraceMatrix_isPrimitive_of_isSAL
    (K : MPOTensor d D) (hK : K.IsInjective) (hSAL : IsSAL K) :
    ∃ (F : PhysicalSectorFactorization K) (p : Fin F.sectorCount → ℝ),
      (∀ k, 0 ≤ p k) ∧
        (∑ k, p k) = 1 ∧
          (∀ k h, (F.neighboringOperator k h).PosSemidef) ∧
            Matrix.IsPrimitive (F.activeSectorTraceMatrix p) := by
  obtain ⟨hη⟩ := exists_etaStructure_reducedBlockState_of_isSAL K hSAL
  obtain ⟨beta, alpha, hm⟩ :=
    exists_normalizedFourSiteTail_entry_ne_zero
      K ((Classical.choose_spec hSAL).1 4 (by omega))
  let F₀ := zeroWeightReparameterizedInverseMapPhysicalSectorFactorization
    K hK (normalizedFourSiteTail K)
      (isThreeSiteClosure_reducedBlockState K) hη alpha beta hm
  obtain ⟨z, hpos, hprim⟩ :=
    exists_rephased_inverseMap_activeSectorTraceMatrix_isPrimitive
      K hK (normalizedFourSiteTail K)
        (isThreeSiteClosure_reducedBlockState K) hη alpha beta hm
          (Classical.choose hSAL)
  exact ⟨F₀.rephase z, hη.p, hη.hp_nonneg, hη.hp_sum, hpos, hprim⟩

end MPOTensor
