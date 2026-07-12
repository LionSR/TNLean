/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.PhysicalSectorFactorization
import TNLean.MPS.MPDO.KrausCPTP
import TNLean.Algebra.MatrixAux

/-!
# Preparations of neighboring physical sectors

This file records the positivity and rank-one trace factorization of the
neighboring operators associated with a physical-sector factorization.  These
are precisely the additional hypotheses in Proposition C.7 of
arXiv:1606.00608.

For every active pair of sectors, the neighboring operator is normalized to a
density matrix.  On zero-weight pairs it is completed by a uniform density
matrix, provided the corresponding factor space is nonempty.  The resulting
family defines the orthogonally controlled preparation occurring in
$\mathcal S_1$.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Appendix C.2, lines 1389--1403 and 1548--1555
-/

open scoped Matrix BigOperators ComplexOrder

namespace MPOTensor.PhysicalSectorFactorization

variable {d D : ℕ} {K : MPOTensor d D}

/-- Positivity and rank-one trace factorization of the neighboring operators
of a physical-sector factorization:
\[
  \eta_{k,h}\geq 0,\qquad
  \operatorname{tr}(\eta_{k,h})=a_kb_h,\qquad
  \sum_k a_kb_k=1.
\]

Together with `PhysicalSectorFactorization`, these are exactly the hypotheses
used in Proposition C.7.

Source: arXiv:1606.00608, Appendix C.2, lines 1389--1403. -/
structure NeighboringTraceFactorization (F : PhysicalSectorFactorization K) where
  /-- Every neighboring operator $\eta_{k,h}$ is positive semidefinite. -/
  neighboringOperator_pos : ∀ k h, (F.neighboringOperator k h).PosSemidef
  /-- The left factors in the rank-one trace matrix. -/
  a : Fin F.sectorCount → ℝ
  /-- The right factors in the rank-one trace matrix. -/
  b : Fin F.sectorCount → ℝ
  /-- The trace matrix has entries $\operatorname{tr}(\eta_{k,h})=a_kb_h$. -/
  trace_neighboringOperator : ∀ k h,
    (F.neighboringOperator k h).trace = ((a k * b h : ℝ) : ℂ)
  /-- The diagonal products satisfy $\sum_k a_kb_k=1$. -/
  sum_mul : ∑ k, a k * b k = 1

namespace NeighboringTraceFactorization

variable {F : PhysicalSectorFactorization K}

/-- Every sector-pair weight $a_kb_h$ is nonnegative. -/
theorem weight_nonneg (H : NeighboringTraceFactorization F)
    (k h : Fin F.sectorCount) :
    0 ≤ H.a k * H.b h := by
  have htrace := (H.neighboringOperator_pos k h).trace_nonneg
  rw [H.trace_neighboringOperator] at htrace
  exact_mod_cast htrace

/-- A zero-weight neighboring operator vanishes. -/
theorem neighboringOperator_eq_zero_of_mul_eq_zero
    (H : NeighboringTraceFactorization F) (k h : Fin F.sectorCount)
    (hzero : H.a k * H.b h = 0) :
    F.neighboringOperator k h = 0 := by
  apply (Matrix.PosSemidef.trace_eq_zero_iff
    (H.neighboringOperator_pos k h)).mp
  rw [H.trace_neighboringOperator, hzero]
  norm_num

/-- An active neighboring operator acts on a nonempty factor space. -/
theorem neighborIndex_nonempty_of_mul_ne_zero
    (H : NeighboringTraceFactorization F) (k h : Fin F.sectorCount)
    (hactive : H.a k * H.b h ≠ 0) :
    Nonempty (NeighborIndex F k h) := by
  by_contra hempty
  haveI : IsEmpty (NeighborIndex F k h) := not_nonempty_iff.mp hempty
  have htrace : (F.neighboringOperator k h).trace = 0 := by
    simp [Matrix.trace]
  rw [H.trace_neighboringOperator] at htrace
  apply hactive
  exact_mod_cast htrace

/-- The normalized neighboring density on a sector pair.  On a zero-weight
pair this expression is the zero matrix; its trace is one on active pairs.

Source: arXiv:1606.00608, Appendix C.2, lines 1551--1555. -/
noncomputable def normalizedNeighboringDensity
    (H : NeighboringTraceFactorization F) (k h : Fin F.sectorCount) :
    Matrix (NeighborIndex F k h) (NeighborIndex F k h) ℂ :=
  (((H.a k * H.b h)⁻¹ : ℝ) : ℂ) • F.neighboringOperator k h

/-- The normalized neighboring density is positive semidefinite. -/
theorem normalizedNeighboringDensity_pos
    (H : NeighboringTraceFactorization F) (k h : Fin F.sectorCount) :
    (H.normalizedNeighboringDensity k h).PosSemidef := by
  apply (H.neighboringOperator_pos k h).smul
  exact_mod_cast inv_nonneg.mpr (H.weight_nonneg k h)

/-- On an active sector pair, the normalized neighboring density has trace
one. -/
theorem trace_normalizedNeighboringDensity
    (H : NeighboringTraceFactorization F) (k h : Fin F.sectorCount)
    (hactive : H.a k * H.b h ≠ 0) :
    (H.normalizedNeighboringDensity k h).trace = 1 := by
  simp only [normalizedNeighboringDensity, Matrix.trace_smul,
    H.trace_neighboringOperator, smul_eq_mul]
  norm_cast
  exact inv_mul_cancel₀ hactive

/-- On an active sector pair, adjoining the normalized neighboring density is
trace-preserving and completely positive.  This is the individual
$\mathcal S_{k,h}$ preparation from arXiv:1606.00608, Appendix C.2,
lines 1551--1555. -/
theorem normalizedNeighboringPreparationMap_isKrausCPTP
    {α : Type*} [Fintype α] [DecidableEq α]
    (H : NeighboringTraceFactorization F) (k h : Fin F.sectorCount)
    (hactive : H.a k * H.b h ≠ 0) :
    IsKrausCPTP (Matrix.preparationMap (α := α)
      (H.normalizedNeighboringDensity k h)) :=
  Matrix.preparationMap_isKrausCPTP _
    (H.normalizedNeighboringDensity_pos k h)
    (H.trace_normalizedNeighboringDensity k h hactive)

/-- A uniform density matrix used to complete a zero-weight neighboring
sector. -/
noncomputable def inactiveNeighboringDensity
    (k h : Fin F.sectorCount) [Nonempty (NeighborIndex F k h)] :
    Matrix (NeighborIndex F k h) (NeighborIndex F k h) ℂ :=
  Matrix.faithfulDensity _

/-- The inactive neighboring density is positive definite. -/
theorem inactiveNeighboringDensity_posDef
    (k h : Fin F.sectorCount) [Nonempty (NeighborIndex F k h)] :
    (inactiveNeighboringDensity (F := F) k h).PosDef :=
  Matrix.faithfulDensity_posDef _

/-- The inactive neighboring density has trace one. -/
theorem inactiveNeighboringDensity_trace
    (k h : Fin F.sectorCount) [Nonempty (NeighborIndex F k h)] :
    (inactiveNeighboringDensity (F := F) k h).trace = 1 :=
  Matrix.faithfulDensity_trace _

/-- The neighboring density equals the normalized source operator on an
active pair and a uniform density on a zero-weight pair.

On active pairs this is the state adjoined by $\mathcal S_{k,h}$ in
arXiv:1606.00608, Appendix C.2, lines 1551--1555.  The inactive branch is a
trace-preserving extension where the source quotient is undefined. -/
noncomputable def completedNeighboringDensity
    (H : NeighboringTraceFactorization F)
    (hindex : ∀ k h, Nonempty (NeighborIndex F k h))
    (k h : Fin F.sectorCount) :
    Matrix (NeighborIndex F k h) (NeighborIndex F k h) ℂ :=
  if H.a k * H.b h ≠ 0 then H.normalizedNeighboringDensity k h
  else
    letI := hindex k h
    inactiveNeighboringDensity k h

/-- Every completed neighboring density is positive semidefinite. -/
theorem completedNeighboringDensity_pos
    (H : NeighboringTraceFactorization F)
    (hindex : ∀ k h, Nonempty (NeighborIndex F k h))
    (k h : Fin F.sectorCount) :
    (H.completedNeighboringDensity hindex k h).PosSemidef := by
  rw [completedNeighboringDensity]
  split_ifs
  · exact H.normalizedNeighboringDensity_pos k h
  · letI := hindex k h
    exact (inactiveNeighboringDensity_posDef (F := F) k h).posSemidef

/-- Every completed neighboring density has trace one. -/
theorem trace_completedNeighboringDensity
    (H : NeighboringTraceFactorization F)
    (hindex : ∀ k h, Nonempty (NeighborIndex F k h))
    (k h : Fin F.sectorCount) :
    (H.completedNeighboringDensity hindex k h).trace = 1 := by
  rw [completedNeighboringDensity]
  split_ifs with hactive
  · exact H.trace_normalizedNeighboringDensity k h hactive
  · letI := hindex k h
    exact inactiveNeighboringDensity_trace (F := F) k h

/-- On an active pair, the completed density is the normalized neighboring
operator from Proposition C.7. -/
theorem completedNeighboringDensity_eq_normalized
    (H : NeighboringTraceFactorization F)
    (hindex : ∀ k h, Nonempty (NeighborIndex F k h))
    (k h : Fin F.sectorCount) (hactive : H.a k * H.b h ≠ 0) :
    H.completedNeighboringDensity hindex k h =
      H.normalizedNeighboringDensity k h := by
  simp [completedNeighboringDensity, hactive]

/-- The sectorwise map which adjoins the completed neighboring density. -/
noncomputable def completedNeighboringPreparationMap
    {α : Type*} [Fintype α] [DecidableEq α]
    (H : NeighboringTraceFactorization F)
    (hindex : ∀ k h, Nonempty (NeighborIndex F k h))
    (k h : Fin F.sectorCount) :
    Matrix α α ℂ →ₗ[ℂ]
      Matrix (α × NeighborIndex F k h) (α × NeighborIndex F k h) ℂ :=
  Matrix.preparationMap (H.completedNeighboringDensity hindex k h)

/-- Adjoining a completed neighboring density is trace-preserving and
completely positive.  On active pairs this is $\mathcal S_{k,h}$ from
arXiv:1606.00608, Appendix C.2, lines 1551--1555. -/
theorem completedNeighboringPreparationMap_isKrausCPTP
    {α : Type*} [Fintype α] [DecidableEq α]
    (H : NeighboringTraceFactorization F)
    (hindex : ∀ k h, Nonempty (NeighborIndex F k h))
    (k h : Fin F.sectorCount) :
    IsKrausCPTP (H.completedNeighboringPreparationMap hindex (α := α) k h) := by
  simpa [completedNeighboringPreparationMap] using
    Matrix.preparationMap_isKrausCPTP _
      (H.completedNeighboringDensity_pos hindex k h)
      (H.trace_completedNeighboringDensity hindex k h)

/-- On an active pair, the completed preparation is the source preparation. -/
theorem completedNeighboringPreparationMap_eq_normalized
    {α : Type*} [Fintype α] [DecidableEq α]
    (H : NeighboringTraceFactorization F)
    (hindex : ∀ k h, Nonempty (NeighborIndex F k h))
    (k h : Fin F.sectorCount) (hactive : H.a k * H.b h ≠ 0) :
    H.completedNeighboringPreparationMap hindex (α := α) k h =
      Matrix.preparationMap (H.normalizedNeighboringDensity k h) := by
  rw [completedNeighboringPreparationMap,
    H.completedNeighboringDensity_eq_normalized hindex k h hactive]

/-! ## Orthogonally controlled neighboring preparations -/

section ControlledPreparation

variable {α : Fin F.sectorCount × Fin F.sectorCount → Type*}
variable [∀ p, Fintype (α p)] [∀ p, DecidableEq (α p)]

/-- The orthogonally controlled neighboring-state preparation.  It discards
coherences between sector pairs and adjoins the completed neighboring density
inside each diagonal sector.

On active pairs its sector maps are the $\mathcal S_{k,h}$ preparations in
arXiv:1606.00608, Appendix C.2, lines 1548--1555. -/
noncomputable def completedNeighboringControlledMap
    (H : NeighboringTraceFactorization F)
    (hindex : ∀ k h, Nonempty (NeighborIndex F k h)) :
    Matrix (Σ p, α p) (Σ p, α p) ℂ →ₗ[ℂ]
      Matrix (Σ p, α p × NeighborIndex F p.1 p.2)
        (Σ p, α p × NeighborIndex F p.1 p.2) ℂ :=
  Matrix.controlledKrausMap
    (fun p => Fintype.card (NeighborIndex F p.1 p.2))
    (fun p j => Matrix.preparationKraus
      (H.completedNeighboringDensity hindex p.1 p.2)
      (H.completedNeighboringDensity_pos hindex p.1 p.2)
      ((Fintype.equivFin (NeighborIndex F p.1 p.2)).symm j))

/-- On a diagonal sector pair, the controlled map is preparation of the
completed neighboring density.

Source: arXiv:1606.00608, Appendix C.2, lines 1548--1555. -/
theorem completedNeighboringControlledMap_sameBlock_apply
    (H : NeighboringTraceFactorization F)
    (hindex : ∀ k h, Nonempty (NeighborIndex F k h))
    (X : Matrix (Σ p, α p) (Σ p, α p) ℂ)
    (p : Fin F.sectorCount × Fin F.sectorCount) (a b : α p)
    (u v : NeighborIndex F p.1 p.2) :
    H.completedNeighboringControlledMap hindex X ⟨p, (a, u)⟩ ⟨p, (b, v)⟩ =
      H.completedNeighboringPreparationMap hindex p.1 p.2
        (X.submatrix (Sigma.mk p) (Sigma.mk p)) (a, u) (b, v) := by
  classical
  rw [completedNeighboringControlledMap, Matrix.controlledKrausMap_sameBlock_apply,
    Matrix.rectangularKrausMap_equiv
      (Fintype.equivFin (NeighborIndex F p.1 p.2)),
    Matrix.rectangularKrausMap_preparationKraus_eq]
  rfl

/-- The orthogonally controlled neighboring-state preparation is
trace-preserving and completely positive.

This is the sector-control part of $\mathcal S_1$ in arXiv:1606.00608,
Appendix C.2, lines 1548--1555. -/
theorem completedNeighboringControlledMap_isKrausCPTP
    (H : NeighboringTraceFactorization F)
    (hindex : ∀ k h, Nonempty (NeighborIndex F k h)) :
    IsKrausCPTP (H.completedNeighboringControlledMap hindex (α := α)) := by
  apply Matrix.controlledKrausMap_isKrausCPTP
  intro p
  exact Matrix.preparationKraus_resolution
    (H.completedNeighboringDensity hindex p.1 p.2)
    (H.completedNeighboringDensity_pos hindex p.1 p.2)
    (H.trace_completedNeighboringDensity hindex p.1 p.2)

end ControlledPreparation

end NeighboringTraceFactorization

end MPOTensor.PhysicalSectorFactorization
