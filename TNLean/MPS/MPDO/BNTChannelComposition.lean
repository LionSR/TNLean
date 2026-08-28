/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Algebra.MatrixKroneckerEmbed
import QICLean.Algebra.PositiveSemidefiniteNormalization
import QICLean.Channel.SupportCompletion
import QICLean.Channel.ProjectiveResolution
import TNLean.MPS.MPDO.BNTBoundaryDecomposition
import TNLean.MPS.MPDO.CommonWeightAbsorbedBNTSupport
import TNLean.MPS.MPDO.FirstSite
import TNLean.MPS.MPDO.PhysicalBlocking
import TNLean.MPS.MPDO.RFPViaTS

/-!
# Composition of blocked renormalization channels across BNT sectors

This file proves the conditional channel-composition theorem in the viable
zero-correlation-length route to the all-BNT part of the fundamental theorem
for matrix product density operators. The construction measures the outer BNT
sector on the first original physical site and then applies that sector's
renormalization channel.

## References

* Cirac--Perez-Garcia--Schuch--Verstraete, arXiv:1606.00608,
  Appendix C.2, lines 1646--1665 and 1810--1825.
-/

open scoped Matrix BigOperators ComplexOrder Kronecker

noncomputable section

namespace MPOTensor

variable {d D : ℕ}

/-! ### Blocking coordinates -/

/-- Identify a two-site chain configuration with one blocked physical index.

Source: arXiv:1606.00608, Theorem 4.9, lines 851--856. -/
def blockedOneChainEquiv (d : ℕ) : (Fin 2 → Fin d) ≃ Fin (d * d) :=
  (finTwoArrowEquiv (Fin d)).trans (blockedIndexEquiv d).symm

/-- Identify a four-site chain configuration with two blocked physical
indices.

Source: arXiv:1606.00608, Appendix C.2, lines 1810--1825. -/
def blockedTwoChainEquiv (d : ℕ) :
    (Fin 4 → Fin d) ≃ Fin (d * d) × Fin (d * d) :=
  (_root_.finFourArrowEquiv (Fin d)).trans (blockedPairEquiv d).symm

/-- The one-site closure of a two-site blocking is the two-site chain closure
in blocked physical coordinates.

Source: arXiv:1606.00608, Theorem 4.9, lines 851--856. -/
theorem equivReindexMap_physCloseN_two_eq_physClose1_blockTwo
    (K : MPOTensor d D) (X : Matrix (Fin D) (Fin D) ℂ) :
    Matrix.equivReindexMap (blockedOneChainEquiv d) (physCloseN K 2 X) =
      physClose1 (blockTwo K) X := by
  ext i j
  simp [Matrix.equivReindexMap, Matrix.coe_reindexLinearEquiv,
    blockedOneChainEquiv, blockedIndexEquiv, blockTwo, physCloseN,
    List.ofFn_succ, evalWord_cons, Matrix.mul_assoc]

/-- The two-site closure of a two-site blocking is the four-site chain closure
in blocked physical coordinates.

Source: arXiv:1606.00608, Appendix C.2, lines 1810--1825. -/
theorem equivReindexMap_physCloseN_four_eq_physClose2_blockTwo
    (K : MPOTensor d D) (X : Matrix (Fin D) (Fin D) ℂ) :
    Matrix.equivReindexMap (blockedTwoChainEquiv d) (physCloseN K 4 X) =
      physClose2 (blockTwo K) X := by
  ext i j
  simp [Matrix.equivReindexMap, Matrix.coe_reindexLinearEquiv,
    blockedTwoChainEquiv, blockedPairEquiv, blockedIndexEquiv, blockTwo,
    physCloseN, List.ofFn_succ, evalWord_cons, Matrix.mul_assoc]

/-- The outer-sector measurement on one blocked site: the original one-site
projection acts on the first constituent site and the identity acts on the
second.

Source: arXiv:1606.00608, Appendix C.2, lines 1810--1817. -/
def blockedFirstSiteProjection (P : Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin (d * d)) (Fin (d * d)) ℂ :=
  Matrix.equivReindexMap (blockedOneChainEquiv d) (firstSiteMatrix P 1)

/-- In product coordinates the one-block measurement is exactly
`P ⊗ₖ 1`.

Source: arXiv:1606.00608, Appendix C.2, lines 1810--1817. -/
theorem blockedFirstSiteProjection_eq_reindex_kronecker_one
    (P : Matrix (Fin d) (Fin d) ℂ) :
    blockedFirstSiteProjection P =
      Matrix.reindex (blockedIndexEquiv d).symm (blockedIndexEquiv d).symm
        (P ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ)) := by
  ext i j
  have htail :
      (![i.divNat, i.modNat] ∘ Fin.succ : Fin 1 → Fin d) =
          ![j.divNat, j.modNat] ∘ Fin.succ ↔ i.modNat = j.modNat := by
    constructor
    · intro h
      simpa using congrFun h 0
    · intro h
      funext k
      fin_cases k
      simpa using h
  have hscalar :
      (if (![i.divNat, i.modNat] ∘ Fin.succ : Fin 1 → Fin d) =
          ![j.divNat, j.modNat] ∘ Fin.succ then P i.divNat j.divNat else 0) =
        if i.modNat = j.modNat then P i.divNat j.divNat else 0 := by
    by_cases h : i.modNat = j.modNat
    · rw [ite_eq_left h, ite_eq_left]
      funext k
      fin_cases k
      simpa using h
    · rw [ite_eq_right h, ite_eq_right]
      exact fun hEq ↦ h (htail.mp hEq)
  simpa [blockedFirstSiteProjection, Matrix.equivReindexMap,
    Matrix.coe_reindexLinearEquiv, blockedOneChainEquiv, blockedIndexEquiv,
    firstSiteMatrix, Matrix.kroneckerMap_apply, Matrix.one_apply] using hscalar

/-! ### First-site support of arbitrary-boundary closures -/

/-- Left support of every physical slice implies left support of every
arbitrary-boundary physical closure on the first site.

Source: arXiv:1606.00608, Appendix C.2, equations `PjKiPj` and `AppTSK`,
lines 1680--1691 and 1810--1825. -/
theorem firstSiteMatrix_mul_physCloseN_of_mul_physicalSlice
    (K : MPOTensor d D) (P : Matrix (Fin d) (Fin d) ℂ)
    (hP : ∀ β α, P * physicalSlice K β α = physicalSlice K β α)
    (N : ℕ) (X : Matrix (Fin D) (Fin D) ℂ) :
    firstSiteMatrix P N * physCloseN K (N + 1) X = physCloseN K (N + 1) X := by
  ext σ τ
  rw [firstSiteMatrix_mul_apply]
  simp only [physCloseN_apply, List.ofFn_succ, Fin.cons_zero, Fin.cons_succ,
    evalWord_cons, Matrix.mul_assoc]
  rw [sum_mul_trace_eq_trace_sum_smul]
  have hTensor :
      (∑ i : Fin d, P (σ 0) i • K i (τ 0)) = K (σ 0) (τ 0) := by
    ext β α
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
    simpa [physicalSlice, Matrix.mul_apply] using
      congrFun (congrFun (hP β α) (σ 0)) (τ 0)
  rw [hTensor]
  rfl

/-- If a one-site matrix annihilates every physical slice on the left, then it
annihilates every arbitrary-boundary closure on the first site.

Source: arXiv:1606.00608, Appendix C.2, equations `AppKxKy=0`, `PjKiPj`, and
`AppTSK`, lines 1634--1639, 1680--1691, and 1810--1825. -/
theorem firstSiteMatrix_mul_physCloseN_eq_zero_of_mul_physicalSlice_eq_zero
    (K : MPOTensor d D) (P : Matrix (Fin d) (Fin d) ℂ)
    (hP : ∀ β α, P * physicalSlice K β α = 0)
    (N : ℕ) (X : Matrix (Fin D) (Fin D) ℂ) :
    firstSiteMatrix P N * physCloseN K (N + 1) X = 0 := by
  ext σ τ
  rw [firstSiteMatrix_mul_apply]
  simp only [physCloseN_apply, List.ofFn_succ, Fin.cons_zero, Fin.cons_succ,
    evalWord_cons, Matrix.mul_assoc, Matrix.zero_apply]
  rw [sum_mul_trace_eq_trace_sum_smul]
  have hTensor : (∑ i : Fin d, P (σ 0) i • K i (τ 0)) = 0 := by
    ext β α
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply]
    simpa [physicalSlice, Matrix.mul_apply] using
      congrFun (congrFun (hP β α) (σ 0)) (τ 0)
  simp [hTensor]

/-- Right support of every physical slice implies right support of every
arbitrary-boundary physical closure on the first site.

Source: arXiv:1606.00608, Appendix C.2, equations `PjKiPj` and `AppTSK`,
lines 1680--1691 and 1810--1825. -/
theorem physCloseN_mul_firstSiteMatrix_of_physicalSlice_mul
    (K : MPOTensor d D) (P : Matrix (Fin d) (Fin d) ℂ)
    (hP : ∀ β α, physicalSlice K β α * P = physicalSlice K β α)
    (N : ℕ) (X : Matrix (Fin D) (Fin D) ℂ) :
    physCloseN K (N + 1) X * firstSiteMatrix P N = physCloseN K (N + 1) X := by
  ext σ τ
  rw [mul_firstSiteMatrix_apply]
  simp only [physCloseN_apply, List.ofFn_succ, Fin.cons_zero, Fin.cons_succ,
    evalWord_cons, Matrix.mul_assoc]
  have hTensor :
      (∑ j : Fin d, P j (τ 0) • K (σ 0) j) = K (σ 0) (τ 0) := by
    ext β α
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
    simpa [physicalSlice, Matrix.mul_apply, mul_comm] using
      congrFun (congrFun (hP β α) (σ 0)) (τ 0)
  calc
    ∑ j : Fin d,
        Matrix.trace
            (K (σ 0) j *
              (evalWord K (List.ofFn fun i ↦ σ i.succ)
                (List.ofFn fun i ↦ τ i.succ) * X)) * P j (τ 0) =
        ∑ j : Fin d, P j (τ 0) *
          Matrix.trace
            (K (σ 0) j *
              (evalWord K (List.ofFn fun i ↦ σ i.succ)
                (List.ofFn fun i ↦ τ i.succ) * X)) := by
      apply Finset.sum_congr rfl
      intro j _
      exact mul_comm _ _
    _ = Matrix.trace
        ((∑ j : Fin d, P j (τ 0) • K (σ 0) j) *
          (evalWord K (List.ofFn fun i ↦ σ i.succ)
            (List.ofFn fun i ↦ τ i.succ) * X)) :=
      sum_mul_trace_eq_trace_sum_smul _ _ _
    _ = _ := by rw [hTensor]

/-- Two-sided physical-slice support gives the corresponding first-site
single-Kraus selection of every arbitrary-boundary closure.

Source: arXiv:1606.00608, Appendix C.2, equations `PjKiPj` and `AppTSK`,
lines 1680--1691 and 1810--1825. -/
theorem singleKrausMap_firstSiteMatrix_physCloseN_of_twoSidedSupport
    (K : MPOTensor d D) (P : Matrix (Fin d) (Fin d) ℂ)
    (hHerm : P.IsHermitian)
    (hP : ∀ β α, P * physicalSlice K β α = physicalSlice K β α ∧
      physicalSlice K β α * P = physicalSlice K β α)
    (N : ℕ) (X : Matrix (Fin D) (Fin D) ℂ) :
    singleKrausMap (firstSiteMatrix P N) (physCloseN K (N + 1) X) =
      physCloseN K (N + 1) X := by
  rw [singleKrausMap_apply, (firstSiteMatrix_isHermitian hHerm N).eq,
    firstSiteMatrix_mul_physCloseN_of_mul_physicalSlice K P (fun β α ↦ (hP β α).1),
    physCloseN_mul_firstSiteMatrix_of_physicalSlice_mul K P (fun β α ↦ (hP β α).2)]

/-- The first-site lift of an orthogonal projection is a star projection.

This is the projection lift used in arXiv:1606.00608, Appendix C.2,
lines 1810--1817. -/
theorem firstSiteMatrix_isStarProjection
    {P : Matrix (Fin d) (Fin d) ℂ} (hP : IsOrthogonalProjection P) (N : ℕ) :
    IsStarProjection (firstSiteMatrix P N) := by
  rw [isStarProjection_iff']
  exact ⟨firstSiteMatrix_mul_firstSiteMatrix P P N ▸ congrArg
      (fun Q ↦ firstSiteMatrix Q N) hP.2,
    by simpa [Matrix.star_eq_conjTranspose] using
      (firstSiteMatrix_isHermitian hP.1 N).eq⟩

/-- A finite sum of first-site lifts is the first-site lift of the sum. -/
theorem sum_firstSiteMatrix
    {ι : Type*} [Fintype ι] (P : ι → Matrix (Fin d) (Fin d) ℂ) (N : ℕ) :
    ∑ s, firstSiteMatrix (P s) N = firstSiteMatrix (∑ s, P s) N := by
  ext σ τ
  simp only [Matrix.sum_apply, firstSiteMatrix, Finset.sum_mul]

/-- A resolution of the one-site identity remains a resolution after acting
on the first site of a longer chain.

This is the completed outer-sector resolution used in arXiv:1606.00608,
Appendix C.2, lines 1810--1817. -/
theorem sum_firstSiteMatrix_eq_one
    {ι : Type*} [Fintype ι] (P : ι → Matrix (Fin d) (Fin d) ℂ)
    (hPsum : ∑ s, P s = 1) (N : ℕ) :
    ∑ s, firstSiteMatrix (P s) N = 1 := by
  rw [sum_firstSiteMatrix, hPsum, firstSiteMatrix_one]

/-- The sum of pairwise orthogonal sector projections supports every physical
slice belonging to one of the sectors on both sides. -/
theorem sum_projection_twoSidedSupport_physicalSlice
    {ι : Type*} [Fintype ι]
    {bondDim : ι → ℕ} (K : (s : ι) → MPOTensor d (bondDim s))
    (P : ι → Matrix (Fin d) (Fin d) ℂ)
    (hOrth : ∀ {s t}, s ≠ t → P s * P t = 0)
    (hSupport : ∀ s β α,
      P s * physicalSlice (K s) β α = physicalSlice (K s) β α ∧
        physicalSlice (K s) β α * P s = physicalSlice (K s) β α)
    (s : ι) (β α : Fin (bondDim s)) :
    (∑ t, P t) * physicalSlice (K s) β α = physicalSlice (K s) β α ∧
      physicalSlice (K s) β α * (∑ t, P t) = physicalSlice (K s) β α := by
  classical
  constructor
  · rw [Matrix.sum_mul, Finset.sum_eq_single s]
    · exact (hSupport s β α).1
    · intro t _ hts
      calc
        P t * physicalSlice (K s) β α =
            (P t * P s) * physicalSlice (K s) β α := by
          rw [Matrix.mul_assoc, (hSupport s β α).1]
        _ = 0 := by rw [hOrth hts, Matrix.zero_mul]
    · simp
  · rw [Matrix.mul_sum, Finset.sum_eq_single s]
    · exact (hSupport s β α).2
    · intro t _ hts
      calc
        physicalSlice (K s) β α * P t =
            (physicalSlice (K s) β α * P s) * P t := by
          rw [(hSupport s β α).2]
        _ = 0 := by rw [Matrix.mul_assoc, hOrth (Ne.symm hts), Matrix.mul_zero]
    · simp

/-- Pairwise orthogonal two-sided supports select precisely the matching
sector in every arbitrary-boundary physical closure.

Source: arXiv:1606.00608, Appendix C.2, equations `AppKxKy=0`, `PjKiPj`, and
`AppTSK`, lines 1634--1639, 1680--1691, and 1810--1825. -/
theorem singleKrausMap_firstSiteMatrix_physCloseN_eq_ite
    {ι : Type*} [DecidableEq ι]
    {bondDim : ι → ℕ} (K : (s : ι) → MPOTensor d (bondDim s))
    (P : ι → Matrix (Fin d) (Fin d) ℂ)
    (hProj : ∀ s, IsOrthogonalProjection (P s))
    (hOrth : ∀ {s t}, s ≠ t → P s * P t = 0)
    (hSupport : ∀ s β α,
      P s * physicalSlice (K s) β α = physicalSlice (K s) β α ∧
        physicalSlice (K s) β α * P s = physicalSlice (K s) β α)
    (s t : ι) (N : ℕ)
    (X : Matrix (Fin (bondDim t)) (Fin (bondDim t)) ℂ) :
    singleKrausMap (firstSiteMatrix (P s) N) (physCloseN (K t) (N + 1) X) =
      if s = t then physCloseN (K t) (N + 1) X else 0 := by
  classical
  by_cases hst : s = t
  · subst t
    split
    · exact singleKrausMap_firstSiteMatrix_physCloseN_of_twoSidedSupport
        (K s) (P s) (hProj s).1 (hSupport s) N X
    · contradiction
  · rw [ite_eq_right hst, singleKrausMap_apply,
      (firstSiteMatrix_isHermitian (hProj s).1 N).eq]
    have hzero : ∀ β α, P s * physicalSlice (K t) β α = 0 := by
      intro β α
      calc
        P s * physicalSlice (K t) β α =
            (P s * P t) * physicalSlice (K t) β α := by
          rw [Matrix.mul_assoc, (hSupport t β α).1]
        _ = 0 := by rw [hOrth hst, Matrix.zero_mul]
    rw [firstSiteMatrix_mul_physCloseN_eq_zero_of_mul_physicalSlice_eq_zero
      (K t) (P s) hzero N X, Matrix.zero_mul]

/-! ### Sector channels in ordinary chain coordinates -/

/-- Transport a blocked coarse-graining channel from blocked indices to the
ordinary four-site and two-site chain coordinates.

Source: arXiv:1606.00608, Appendix C.2, lines 1810--1825. -/
def coarseningMapInChainCoordinates
    (S : Matrix (Fin (d * d) × Fin (d * d))
        (Fin (d * d) × Fin (d * d)) ℂ →ₗ[ℂ]
      Matrix (Fin (d * d)) (Fin (d * d)) ℂ) :
    Matrix (Fin 4 → Fin d) (Fin 4 → Fin d) ℂ →ₗ[ℂ]
      Matrix (Fin 2 → Fin d) (Fin 2 → Fin d) ℂ :=
  Matrix.equivReindexMap (blockedOneChainEquiv d).symm ∘ₗ S ∘ₗ
    Matrix.equivReindexMap (blockedTwoChainEquiv d)

/-- Transport a blocked refinement channel from blocked indices to the
ordinary two-site and four-site chain coordinates.

Source: arXiv:1606.00608, Appendix C.2, lines 1810--1825. -/
def refinementMapInChainCoordinates
    (T : Matrix (Fin (d * d)) (Fin (d * d)) ℂ →ₗ[ℂ]
      Matrix (Fin (d * d) × Fin (d * d))
        (Fin (d * d) × Fin (d * d)) ℂ) :
    Matrix (Fin 2 → Fin d) (Fin 2 → Fin d) ℂ →ₗ[ℂ]
      Matrix (Fin 4 → Fin d) (Fin 4 → Fin d) ℂ :=
  Matrix.equivReindexMap (blockedTwoChainEquiv d).symm ∘ₗ T ∘ₗ
    Matrix.equivReindexMap (blockedOneChainEquiv d)

/-- Coordinate transport preserves the channel property of the blocked
coarse-graining map.

Source: arXiv:1606.00608, Appendix C.2, lines 1810--1825. -/
theorem coarseningMapInChainCoordinates_isKrausCPTP
    {S : Matrix (Fin (d * d) × Fin (d * d))
        (Fin (d * d) × Fin (d * d)) ℂ →ₗ[ℂ]
      Matrix (Fin (d * d)) (Fin (d * d)) ℂ}
    (hS : IsKrausCPTP S) : IsKrausCPTP (coarseningMapInChainCoordinates S) := by
  exact isKrausCPTP_comp
    (isKrausCPTP_comp
      (Matrix.equivReindexMap_isKrausCPTP (blockedTwoChainEquiv d)) hS)
    (Matrix.equivReindexMap_isKrausCPTP (blockedOneChainEquiv d).symm)

/-- Coordinate transport preserves the channel property of the blocked
refinement map.

Source: arXiv:1606.00608, Appendix C.2, lines 1810--1825. -/
theorem refinementMapInChainCoordinates_isKrausCPTP
    {T : Matrix (Fin (d * d)) (Fin (d * d)) ℂ →ₗ[ℂ]
      Matrix (Fin (d * d) × Fin (d * d))
        (Fin (d * d) × Fin (d * d)) ℂ}
    (hT : IsKrausCPTP T) : IsKrausCPTP (refinementMapInChainCoordinates T) := by
  exact isKrausCPTP_comp
    (isKrausCPTP_comp
      (Matrix.equivReindexMap_isKrausCPTP (blockedOneChainEquiv d)) hT)
    (Matrix.equivReindexMap_isKrausCPTP (blockedTwoChainEquiv d).symm)

/-- In chain coordinates, a blocked coarse-graining equation is the
length-four to length-two closure equation.

Source: arXiv:1606.00608, Appendix C.2, lines 1810--1825. -/
theorem coarseningMapInChainCoordinates_physCloseN
    (K : MPOTensor d D)
    (S : Matrix (Fin (d * d) × Fin (d * d))
        (Fin (d * d) × Fin (d * d)) ℂ →ₗ[ℂ]
      Matrix (Fin (d * d)) (Fin (d * d)) ℂ)
    (hS : ∀ X, S (physClose2 (blockTwo K) X) = physClose1 (blockTwo K) X)
    (X : Matrix (Fin D) (Fin D) ℂ) :
    coarseningMapInChainCoordinates S (physCloseN K 4 X) = physCloseN K 2 X := by
  simp only [coarseningMapInChainCoordinates, LinearMap.comp_apply]
  rw [equivReindexMap_physCloseN_four_eq_physClose2_blockTwo K X, hS,
    ← equivReindexMap_physCloseN_two_eq_physClose1_blockTwo K X]
  exact (Matrix.reindexLinearEquiv ℂ ℂ (blockedOneChainEquiv d)
    (blockedOneChainEquiv d)).symm_apply_apply (physCloseN K 2 X)

/-- In chain coordinates, a blocked refinement equation is the length-two to
length-four closure equation.

Source: arXiv:1606.00608, Appendix C.2, lines 1810--1825. -/
theorem refinementMapInChainCoordinates_physCloseN
    (K : MPOTensor d D)
    (T : Matrix (Fin (d * d)) (Fin (d * d)) ℂ →ₗ[ℂ]
      Matrix (Fin (d * d) × Fin (d * d))
        (Fin (d * d) × Fin (d * d)) ℂ)
    (hT : ∀ X, T (physClose1 (blockTwo K) X) = physClose2 (blockTwo K) X)
    (X : Matrix (Fin D) (Fin D) ℂ) :
    refinementMapInChainCoordinates T (physCloseN K 2 X) = physCloseN K 4 X := by
  simp only [refinementMapInChainCoordinates, LinearMap.comp_apply]
  rw [equivReindexMap_physCloseN_two_eq_physClose1_blockTwo K X, hT,
    ← equivReindexMap_physCloseN_four_eq_physClose2_blockTwo K X]
  exact (Matrix.reindexLinearEquiv ℂ ℂ (blockedTwoChainEquiv d)
    (blockedTwoChainEquiv d)).symm_apply_apply (physCloseN K 4 X)

/-! ### Projector-controlled channel composition -/

/-- One direction of the projector-controlled channel assembly, for sectorwise
channels from length-`n + 1` to length-`m + 1` chains. The assembled sum of
projector-compressed sector channels is completely positive, preserves the
trace selected by the completed outer projection, and maps the length-`n + 1`
closures to the length-`m + 1` closures, which are supported on the completed
outer projection.

This is the common core of the coarse-graining and refinement directions of
the projective-measurement step in arXiv:1606.00608, Appendix C.2,
lines 1810--1825. -/
private theorem sum_comp_singleKrausMap_firstSiteMatrix_properties
    {ι : Type*} [Fintype ι]
    {bondDim : ι → ℕ}
    (M : MPOTensor d D) (K : (s : ι) → MPOTensor d (bondDim s))
    (P : ι → Matrix (Fin d) (Fin d) ℂ)
    (hProj : ∀ s, IsOrthogonalProjection (P s))
    (hOrth : ∀ {s t}, s ≠ t → P s * P t = 0)
    (hSupport : ∀ s β α,
      P s * physicalSlice (K s) β α = physicalSlice (K s) β α ∧
        physicalSlice (K s) β α * P s = physicalSlice (K s) β α)
    (boundary : Matrix (Fin D) (Fin D) ℂ →
      (s : ι) → Matrix (Fin (bondDim s)) (Fin (bondDim s)) ℂ)
    (n m : ℕ)
    (hDecompIn : ∀ X, physCloseN M (n + 1) X =
      ∑ s, physCloseN (K s) (n + 1) (boundary X s))
    (hDecompOut : ∀ X, physCloseN M (m + 1) X =
      ∑ s, physCloseN (K s) (m + 1) (boundary X s))
    (F : ι → Matrix (Fin (n + 1) → Fin d) (Fin (n + 1) → Fin d) ℂ →ₗ[ℂ]
      Matrix (Fin (m + 1) → Fin d) (Fin (m + 1) → Fin d) ℂ)
    (hF : ∀ s, IsKrausCPTP (F s))
    (hFclose : ∀ s Y, F s (physCloseN (K s) (n + 1) Y) =
      physCloseN (K s) (m + 1) Y) :
    IsKrausCP (∑ s, F s ∘ₗ singleKrausMap (firstSiteMatrix (P s) n)) ∧
      (∀ X, Matrix.trace
          ((∑ s, F s ∘ₗ singleKrausMap (firstSiteMatrix (P s) n)) X) =
        Matrix.trace (firstSiteMatrix (∑ s, P s) n * X)) ∧
      (∀ X, firstSiteMatrix (∑ s, P s) n * physCloseN M (n + 1) X *
          firstSiteMatrix (∑ s, P s) n = physCloseN M (n + 1) X) ∧
      (∀ X, (∑ s, F s ∘ₗ singleKrausMap (firstSiteMatrix (P s) n))
          (physCloseN M (n + 1) X) = physCloseN M (m + 1) X) := by
  classical
  have hQSupport : ∀ s β α,
      (∑ t, P t) * physicalSlice (K s) β α = physicalSlice (K s) β α ∧
        physicalSlice (K s) β α * (∑ t, P t) = physicalSlice (K s) β α :=
    sum_projection_twoSidedSupport_physicalSlice K P hOrth hSupport
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact isKrausCP_sum_comp_singleKrausMap
      (fun s ↦ firstSiteMatrix (P s) n) F (fun s ↦ (hF s).isKrausCP)
  · intro X
    rw [trace_sum_comp_singleKrausMap_of_starProjections
      (fun s ↦ firstSiteMatrix (P s) n) F
      (fun s ↦ firstSiteMatrix_isStarProjection (hProj s) n) hF,
      sum_firstSiteMatrix]
  · intro X
    rw [hDecompIn X, Matrix.mul_sum, Matrix.sum_mul]
    apply Finset.sum_congr rfl
    intro s _
    rw [firstSiteMatrix_mul_physCloseN_of_mul_physicalSlice
      (K s) (∑ t, P t) (fun β α ↦ (hQSupport s β α).1) n]
    rw [physCloseN_mul_firstSiteMatrix_of_physicalSlice_mul
      (K s) (∑ t, P t) (fun β α ↦ (hQSupport s β α).2) n]
  · intro X
    rw [hDecompIn X]
    simp only [LinearMap.sum_apply, LinearMap.comp_apply, map_sum]
    apply Eq.trans ?_ (hDecompOut X).symm
    apply Finset.sum_congr rfl
    intro s _
    calc
      ∑ x, F x (singleKrausMap (firstSiteMatrix (P x) n)
          (physCloseN (K s) (n + 1) (boundary X s))) =
          F s (physCloseN (K s) (n + 1) (boundary X s)) := by
        simp_rw [singleKrausMap_firstSiteMatrix_physCloseN_eq_ite
          K P hProj hOrth hSupport]
        rw [Finset.sum_eq_single s]
        · simp
        · intro x _ hxs
          rw [ite_eq_right hxs, map_zero]
        · simp
      _ = physCloseN (K s) (m + 1) (boundary X s) := hFclose s (boundary X s)

/-- Assemble sectorwise blocked renormalization channels in ordinary chain
coordinates. The same sector boundary is used at lengths two and four.

This is the projective-measurement step of arXiv:1606.00608, Appendix C.2,
lines 1810--1825. -/
theorem exists_chainCoordinateRFP_of_projectiveSectorDecomposition
    {ι : Type*} [Fintype ι]
    {bondDim : ι → ℕ}
    (M : MPOTensor d D) (K : (s : ι) → MPOTensor d (bondDim s))
    (P : ι → Matrix (Fin d) (Fin d) ℂ)
    (hProj : ∀ s, IsOrthogonalProjection (P s))
    (hPsum : ∑ s, P s = 1)
    (hOrth : ∀ {s t}, s ≠ t → P s * P t = 0)
    (hSupport : ∀ s β α,
      P s * physicalSlice (K s) β α = physicalSlice (K s) β α ∧
        physicalSlice (K s) β α * P s = physicalSlice (K s) β α)
    (boundary : Matrix (Fin D) (Fin D) ℂ →
      (s : ι) → Matrix (Fin (bondDim s)) (Fin (bondDim s)) ℂ)
    (hDecompTwo : ∀ X, physCloseN M 2 X =
      ∑ s, physCloseN (K s) 2 (boundary X s))
    (hDecompFour : ∀ X, physCloseN M 4 X =
      ∑ s, physCloseN (K s) 4 (boundary X s))
    (hRFP : ∀ s, IsRFPViaTS (blockTwo (K s))) :
    ∃ (S : Matrix (Fin 4 → Fin d) (Fin 4 → Fin d) ℂ →ₗ[ℂ]
        Matrix (Fin 2 → Fin d) (Fin 2 → Fin d) ℂ)
      (T : Matrix (Fin 2 → Fin d) (Fin 2 → Fin d) ℂ →ₗ[ℂ]
        Matrix (Fin 4 → Fin d) (Fin 4 → Fin d) ℂ),
      IsKrausCPTP S ∧ IsKrausCPTP T ∧
      (∀ X, S (physCloseN M 4 X) = physCloseN M 2 X) ∧
      (∀ X, T (physCloseN M 2 X) = physCloseN M 4 X) := by
  classical
  choose S₀ T₀ hS₀ hT₀ hS₀close hT₀close using hRFP
  let S : ι → Matrix (Fin 4 → Fin d) (Fin 4 → Fin d) ℂ →ₗ[ℂ]
      Matrix (Fin 2 → Fin d) (Fin 2 → Fin d) ℂ :=
    fun s ↦ coarseningMapInChainCoordinates (S₀ s)
  let T : ι → Matrix (Fin 2 → Fin d) (Fin 2 → Fin d) ℂ →ₗ[ℂ]
      Matrix (Fin 4 → Fin d) (Fin 4 → Fin d) ℂ :=
    fun s ↦ refinementMapInChainCoordinates (T₀ s)
  let Sglobal := ∑ s, S s ∘ₗ singleKrausMap (firstSiteMatrix (P s) 3)
  let Tglobal := ∑ s, T s ∘ₗ singleKrausMap (firstSiteMatrix (P s) 1)
  refine ⟨Sglobal, Tglobal, ?_, ?_, ?_, ?_⟩
  · exact isKrausCPTP_sum_comp_singleKrausMap_of_starProjectionResolution
      (fun s ↦ firstSiteMatrix (P s) 3) S
      (fun s ↦ firstSiteMatrix_isStarProjection (hProj s) 3)
      (sum_firstSiteMatrix_eq_one P hPsum 3)
      (fun s ↦ coarseningMapInChainCoordinates_isKrausCPTP (hS₀ s))
  · exact isKrausCPTP_sum_comp_singleKrausMap_of_starProjectionResolution
      (fun s ↦ firstSiteMatrix (P s) 1) T
      (fun s ↦ firstSiteMatrix_isStarProjection (hProj s) 1)
      (sum_firstSiteMatrix_eq_one P hPsum 1)
      (fun s ↦ refinementMapInChainCoordinates_isKrausCPTP (hT₀ s))
  · exact (sum_comp_singleKrausMap_firstSiteMatrix_properties M K P hProj
      hOrth hSupport boundary 3 1 hDecompFour hDecompTwo S
      (fun s ↦ coarseningMapInChainCoordinates_isKrausCPTP (hS₀ s))
      (fun s Y ↦ coarseningMapInChainCoordinates_physCloseN
        (K s) (S₀ s) (hS₀close s) Y)).2.2.2
  · exact (sum_comp_singleKrausMap_firstSiteMatrix_properties M K P hProj
      hOrth hSupport boundary 1 3 hDecompTwo hDecompFour T
      (fun s ↦ refinementMapInChainCoordinates_isKrausCPTP (hT₀ s))
      (fun s Y ↦ refinementMapInChainCoordinates_physCloseN
        (K s) (T₀ s) (hT₀close s) Y)).2.2.2

/-- Assemble sectorwise blocked renormalization channels when the orthogonal
sector projections need not resolve the identity. The active sums are
completed trace-preservingly on the orthogonal input complements and agree
with the uncompleted sums on the physical closures.

This is the physical-complement completion of the projection-first argument
in arXiv:1606.00608, Appendix C.2, lines 1810--1817. -/
theorem exists_chainCoordinateRFP_of_orthogonalSectorDecomposition
    {ι : Type*} [Fintype ι]
    {bondDim : ι → ℕ}
    (M : MPOTensor d D) (K : (s : ι) → MPOTensor d (bondDim s))
    (P : ι → Matrix (Fin d) (Fin d) ℂ)
    (hProj : ∀ s, IsOrthogonalProjection (P s))
    (hOrth : ∀ {s t}, s ≠ t → P s * P t = 0)
    (hSupport : ∀ s β α,
      P s * physicalSlice (K s) β α = physicalSlice (K s) β α ∧
        physicalSlice (K s) β α * P s = physicalSlice (K s) β α)
    (boundary : Matrix (Fin D) (Fin D) ℂ →
      (s : ι) → Matrix (Fin (bondDim s)) (Fin (bondDim s)) ℂ)
    (hDecompTwo : ∀ X, physCloseN M 2 X =
      ∑ s, physCloseN (K s) 2 (boundary X s))
    (hDecompFour : ∀ X, physCloseN M 4 X =
      ∑ s, physCloseN (K s) 4 (boundary X s))
    (hRFP : ∀ s, IsRFPViaTS (blockTwo (K s)))
    (ρTwo : Matrix (Fin 2 → Fin d) (Fin 2 → Fin d) ℂ)
    (hρTwo : ρTwo.PosSemidef) (hρTwoTrace : Matrix.trace ρTwo = 1)
    (ρFour : Matrix (Fin 4 → Fin d) (Fin 4 → Fin d) ℂ)
    (hρFour : ρFour.PosSemidef) (hρFourTrace : Matrix.trace ρFour = 1) :
    ∃ (S : Matrix (Fin 4 → Fin d) (Fin 4 → Fin d) ℂ →ₗ[ℂ]
        Matrix (Fin 2 → Fin d) (Fin 2 → Fin d) ℂ)
      (T : Matrix (Fin 2 → Fin d) (Fin 2 → Fin d) ℂ →ₗ[ℂ]
        Matrix (Fin 4 → Fin d) (Fin 4 → Fin d) ℂ),
      IsKrausCPTP S ∧ IsKrausCPTP T ∧
      (∀ X, S (physCloseN M 4 X) = physCloseN M 2 X) ∧
      (∀ X, T (physCloseN M 2 X) = physCloseN M 4 X) := by
  classical
  choose S₀ T₀ hS₀ hT₀ hS₀close hT₀close using hRFP
  let S : ι → Matrix (Fin 4 → Fin d) (Fin 4 → Fin d) ℂ →ₗ[ℂ]
      Matrix (Fin 2 → Fin d) (Fin 2 → Fin d) ℂ :=
    fun s ↦ coarseningMapInChainCoordinates (S₀ s)
  let T : ι → Matrix (Fin 2 → Fin d) (Fin 2 → Fin d) ℂ →ₗ[ℂ]
      Matrix (Fin 4 → Fin d) (Fin 4 → Fin d) ℂ :=
    fun s ↦ refinementMapInChainCoordinates (T₀ s)
  let Q : Matrix (Fin d) (Fin d) ℂ := ∑ s, P s
  let QFour : Matrix (Fin 4 → Fin d) (Fin 4 → Fin d) ℂ := firstSiteMatrix Q 3
  let QTwo : Matrix (Fin 2 → Fin d) (Fin 2 → Fin d) ℂ := firstSiteMatrix Q 1
  let Sactive := ∑ s, S s ∘ₗ singleKrausMap (firstSiteMatrix (P s) 3)
  let Tactive := ∑ s, T s ∘ₗ singleKrausMap (firstSiteMatrix (P s) 1)
  let Sglobal := Matrix.supportCompletion Sactive QFour ρTwo
  let Tglobal := Matrix.supportCompletion Tactive QTwo ρFour
  have hQ : IsOrthogonalProjection Q :=
    isOrthogonalProjection_sum_of_pairwise_mul_eq_zero P hProj hOrth
  have hQFourHerm : QFour.IsHermitian := firstSiteMatrix_isHermitian hQ.1 3
  have hQFourIdem : QFour * QFour = QFour := by
    exact (firstSiteMatrix_isStarProjection hQ 3).isIdempotentElem.eq
  have hQTwoHerm : QTwo.IsHermitian := firstSiteMatrix_isHermitian hQ.1 1
  have hQTwoIdem : QTwo * QTwo = QTwo := by
    exact (firstSiteMatrix_isStarProjection hQ 1).isIdempotentElem.eq
  obtain ⟨hSactiveCP, hSactiveTrace, hFourSupported, hSactiveClose⟩ :=
    sum_comp_singleKrausMap_firstSiteMatrix_properties M K P hProj hOrth
      hSupport boundary 3 1 hDecompFour hDecompTwo S
      (fun s ↦ coarseningMapInChainCoordinates_isKrausCPTP (hS₀ s))
      (fun s Y ↦ coarseningMapInChainCoordinates_physCloseN
        (K s) (S₀ s) (hS₀close s) Y)
  obtain ⟨hTactiveCP, hTactiveTrace, hTwoSupported, hTactiveClose⟩ :=
    sum_comp_singleKrausMap_firstSiteMatrix_properties M K P hProj hOrth
      hSupport boundary 1 3 hDecompTwo hDecompFour T
      (fun s ↦ refinementMapInChainCoordinates_isKrausCPTP (hT₀ s))
      (fun s Y ↦ refinementMapInChainCoordinates_physCloseN
        (K s) (T₀ s) (hT₀close s) Y)
  refine ⟨Sglobal, Tglobal, ?_, ?_, ?_, ?_⟩
  · exact Matrix.supportCompletion_isKrausCPTP
      Sactive QFour ρTwo hSactiveCP hQFourHerm hQFourIdem
      hSactiveTrace hρTwo hρTwoTrace
  · exact Matrix.supportCompletion_isKrausCPTP
      Tactive QTwo ρFour hTactiveCP hQTwoHerm hQTwoIdem
      hTactiveTrace hρFour hρFourTrace
  · intro X
    rw [show Sglobal (physCloseN M 4 X) = Sactive (physCloseN M 4 X) by
      exact Matrix.supportCompletion_apply_of_supported
        Sactive QFour ρTwo _ hQFourHerm hQFourIdem (hFourSupported X)]
    exact hSactiveClose X
  · intro X
    rw [show Tglobal (physCloseN M 2 X) = Tactive (physCloseN M 2 X) by
      exact Matrix.supportCompletion_apply_of_supported
        Tactive QTwo ρFour _ hQTwoHerm hQTwoIdem (hTwoSupported X)]
    exact hTactiveClose X

/-- Transport a pair of renormalization channels in ordinary length-two and
length-four chain coordinates to the physical coordinates of a two-site
blocking.

Source: arXiv:1606.00608, Appendix C.2, lines 1810--1825. -/
theorem blockTwo_isRFPViaTS_of_chainCoordinateRFP
    (M : MPOTensor d D)
    (S : Matrix (Fin 4 → Fin d) (Fin 4 → Fin d) ℂ →ₗ[ℂ]
      Matrix (Fin 2 → Fin d) (Fin 2 → Fin d) ℂ)
    (T : Matrix (Fin 2 → Fin d) (Fin 2 → Fin d) ℂ →ₗ[ℂ]
      Matrix (Fin 4 → Fin d) (Fin 4 → Fin d) ℂ)
    (hS : IsKrausCPTP S) (hT : IsKrausCPTP T)
    (hSclose : ∀ X, S (physCloseN M 4 X) = physCloseN M 2 X)
    (hTclose : ∀ X, T (physCloseN M 2 X) = physCloseN M 4 X) :
    IsRFPViaTS (blockTwo M) := by
  let Sblocked := Matrix.equivReindexMap (blockedOneChainEquiv d) ∘ₗ S ∘ₗ
    Matrix.equivReindexMap (blockedTwoChainEquiv d).symm
  let Tblocked := Matrix.equivReindexMap (blockedTwoChainEquiv d) ∘ₗ T ∘ₗ
    Matrix.equivReindexMap (blockedOneChainEquiv d).symm
  refine ⟨Sblocked, Tblocked, ?_, ?_, ?_, ?_⟩
  · exact isKrausCPTP_comp
      (isKrausCPTP_comp
        (Matrix.equivReindexMap_isKrausCPTP (blockedTwoChainEquiv d).symm) hS)
      (Matrix.equivReindexMap_isKrausCPTP (blockedOneChainEquiv d))
  · exact isKrausCPTP_comp
      (isKrausCPTP_comp
        (Matrix.equivReindexMap_isKrausCPTP (blockedOneChainEquiv d).symm) hT)
      (Matrix.equivReindexMap_isKrausCPTP (blockedTwoChainEquiv d))
  · intro X
    simp only [Sblocked, LinearMap.comp_apply]
    rw [← equivReindexMap_physCloseN_four_eq_physClose2_blockTwo M X]
    rw [equivReindexMap_symm_apply_self, hSclose,
      equivReindexMap_physCloseN_two_eq_physClose1_blockTwo]
  · intro X
    simp only [Tblocked, LinearMap.comp_apply]
    rw [← equivReindexMap_physCloseN_two_eq_physClose1_blockTwo M X]
    rw [equivReindexMap_symm_apply_self, hTclose,
      equivReindexMap_physCloseN_four_eq_physClose2_blockTwo]

/-! ### Conditional all-BNT theorem -/

/-- An exact canonical BNT reconstruction with copy-independent absorbed
weights has a blocked renormalization channel pair whenever its completed
outer physical supports resolve the identity and every absorbed
representative has such a pair.

The assembled channels first measure the outer BNT sector on the first
original site of the blocked input and then apply the corresponding sector
channel. Thus no inner channel label is combined with the outer BNT label.
For an arbitrary virtual boundary `X`, the sector boundary is the sum of the
diagonal copy blocks of `G⁻¹ * X * G`; the same boundary occurs in the
length-two and length-four closure identities.

This is a project-derived conditional form of the channel assembly in
arXiv:1606.00608, Appendix C.2, lines 1646--1665 and 1810--1825. It is not the
printed implication (iv) to (v) of Theorem 4.9.

**Scope restriction (conditional channel composition):** In addition to the
source hypotheses, this theorem assumes that the outer support projections
resolve the physical identity (`hPsum`) and that every absorbed representative
already has a blocked renormalization channel pair (`hRFP`). These two
obligations and their elimination plans are recorded in
<https://sirui-lu.com/QICLean/paper-gaps/cpgsv17_pf_rank_one.pdf>: prove projector completeness from
the source hypotheses and construct the representative channel pairs. -/
theorem blockTwo_isRFPViaTS_of_commonWeightAbsorbedBNTChannels
    (S : MPSTensor.SectorDecomposition (d * d))
    (hWeight : ∀ (j : Fin S.basisCount) (q q' : Fin (S.copies j)),
      S.weight j q = S.weight j q')
    (M : MPOTensor d S.totalDim)
    (G : GL (Fin S.totalDim) ℂ)
    (hG : ∀ i, M.toMPSTensor i =
      (G : Matrix (Fin S.totalDim) (Fin S.totalDim) ℂ) * S.toTensor i *
        (↑(G⁻¹) : Matrix (Fin S.totalDim) (Fin S.totalDim) ℂ))
    (P : Fin S.basisCount → Matrix (Fin d) (Fin d) ℂ)
    (hProj : ∀ s, IsOrthogonalProjection (P s))
    (hPsum : ∑ s, P s = 1)
    (hOrth : ∀ {s t}, s ≠ t → P s * P t = 0)
    (hSupport : ∀ s (β α : Fin (S.basisDim s)),
      P s * physicalSlice (commonWeightAbsorbedBasisMPOTensor S hWeight s) β α =
          physicalSlice (commonWeightAbsorbedBasisMPOTensor S hWeight s) β α ∧
        physicalSlice (commonWeightAbsorbedBasisMPOTensor S hWeight s) β α * P s =
          physicalSlice (commonWeightAbsorbedBasisMPOTensor S hWeight s) β α)
    (hRFP : ∀ s, IsRFPViaTS
      (blockTwo (commonWeightAbsorbedBasisMPOTensor S hWeight s))) :
    IsRFPViaTS (blockTwo M) := by
  let K : (s : Fin S.basisCount) → MPOTensor d (S.basisDim s) :=
    fun s ↦ commonWeightAbsorbedBasisMPOTensor S hWeight s
  let boundary : Matrix (Fin S.totalDim) (Fin S.totalDim) ℂ →
      (s : Fin S.basisCount) →
        Matrix (Fin (S.basisDim s)) (Fin (S.basisDim s)) ℂ :=
    fun X s ↦ representativeBoundary S
      ((↑(G⁻¹) : Matrix (Fin S.totalDim) (Fin S.totalDim) ℂ) * X *
        (G : Matrix (Fin S.totalDim) (Fin S.totalDim) ℂ)) s
  obtain ⟨Schain, Tchain, hSchain, hTchain, hSclose, hTclose⟩ :=
    exists_chainCoordinateRFP_of_projectiveSectorDecomposition
      M K P hProj hPsum hOrth hSupport boundary
      (fun X ↦ physCloseN_eq_sum_commonWeightAbsorbedBasis_of_gauge_toTensor
        S hWeight M G hG 2 X)
      (fun X ↦ physCloseN_eq_sum_commonWeightAbsorbedBasis_of_gauge_toTensor
        S hWeight M G hG 4 X)
      hRFP
  exact blockTwo_isRFPViaTS_of_chainCoordinateRFP
    M Schain Tchain hSchain hTchain hSclose hTclose

/-- An exact canonical BNT reconstruction with copy-independent absorbed
weights has a blocked renormalization channel pair whenever its outer physical
supports are pairwise orthogonal and every absorbed representative has such a
pair. The supports need not resolve the ambient physical identity.

The active projector-controlled sums are completed on their orthogonal input
complements by trace-and-prepare channels. Since every relevant closure is
supported on the sum of the outer projections, the complementary terms vanish
on the two channel equations.

This is a project-derived completion of the projection-first construction in
arXiv:1606.00608, Appendix C.2, lines 1646--1665 and 1810--1825. -/
theorem blockTwo_isRFPViaTS_of_commonWeightAbsorbedBNTChannels_of_orthogonalSupports
    (S : MPSTensor.SectorDecomposition (d * d))
    (hWeight : ∀ (j : Fin S.basisCount) (q q' : Fin (S.copies j)),
      S.weight j q = S.weight j q')
    (M : MPOTensor d S.totalDim)
    (G : GL (Fin S.totalDim) ℂ)
    (hG : ∀ i, M.toMPSTensor i =
      (G : Matrix (Fin S.totalDim) (Fin S.totalDim) ℂ) * S.toTensor i *
        (↑(G⁻¹) : Matrix (Fin S.totalDim) (Fin S.totalDim) ℂ))
    (P : Fin S.basisCount → Matrix (Fin d) (Fin d) ℂ)
    (hProj : ∀ s, IsOrthogonalProjection (P s))
    (hOrth : ∀ {s t}, s ≠ t → P s * P t = 0)
    (hSupport : ∀ s (β α : Fin (S.basisDim s)),
      P s * physicalSlice (commonWeightAbsorbedBasisMPOTensor S hWeight s) β α =
          physicalSlice (commonWeightAbsorbedBasisMPOTensor S hWeight s) β α ∧
        physicalSlice (commonWeightAbsorbedBasisMPOTensor S hWeight s) β α * P s =
          physicalSlice (commonWeightAbsorbedBasisMPOTensor S hWeight s) β α)
    (hRFP : ∀ s, IsRFPViaTS
      (blockTwo (commonWeightAbsorbedBasisMPOTensor S hWeight s))) :
    IsRFPViaTS (blockTwo M) := by
  classical
  by_cases hd : d = 0
  · subst d
    apply blockTwo_isRFPViaTS_of_commonWeightAbsorbedBNTChannels
      S hWeight M G hG P hProj
    · exact Subsingleton.elim _ _
    · exact hOrth
    · exact hSupport
    · exact hRFP
  · let i₀ : Fin d := ⟨0, Nat.pos_of_ne_zero hd⟩
    let xTwo : Fin 2 → Fin d := fun _ ↦ i₀
    let xFour : Fin 4 → Fin d := fun _ ↦ i₀
    let ρTwo : Matrix (Fin 2 → Fin d) (Fin 2 → Fin d) ℂ :=
      Matrix.normalizePosSemidef xTwo 1
    let ρFour : Matrix (Fin 4 → Fin d) (Fin 4 → Fin d) ℂ :=
      Matrix.normalizePosSemidef xFour 1
    let K : (s : Fin S.basisCount) → MPOTensor d (S.basisDim s) :=
      fun s ↦ commonWeightAbsorbedBasisMPOTensor S hWeight s
    let boundary : Matrix (Fin S.totalDim) (Fin S.totalDim) ℂ →
        (s : Fin S.basisCount) →
          Matrix (Fin (S.basisDim s)) (Fin (S.basisDim s)) ℂ :=
      fun X s ↦ representativeBoundary S
        ((↑(G⁻¹) : Matrix (Fin S.totalDim) (Fin S.totalDim) ℂ) * X *
          (G : Matrix (Fin S.totalDim) (Fin S.totalDim) ℂ)) s
    obtain ⟨Schain, Tchain, hSchain, hTchain, hSclose, hTclose⟩ :=
      exists_chainCoordinateRFP_of_orthogonalSectorDecomposition
        M K P hProj hOrth hSupport boundary
        (fun X ↦ physCloseN_eq_sum_commonWeightAbsorbedBasis_of_gauge_toTensor
          S hWeight M G hG 2 X)
        (fun X ↦ physCloseN_eq_sum_commonWeightAbsorbedBasis_of_gauge_toTensor
          S hWeight M G hG 4 X)
        hRFP ρTwo
        (Matrix.normalizePosSemidef_posSemidef xTwo Matrix.PosSemidef.one)
        (Matrix.normalizePosSemidef_trace xTwo Matrix.PosSemidef.one)
        ρFour
        (Matrix.normalizePosSemidef_posSemidef xFour Matrix.PosSemidef.one)
        (Matrix.normalizePosSemidef_trace xFour Matrix.PosSemidef.one)
    exact blockTwo_isRFPViaTS_of_chainCoordinateRFP
      M Schain Tchain hSchain hTchain hSclose hTclose

end MPOTensor
