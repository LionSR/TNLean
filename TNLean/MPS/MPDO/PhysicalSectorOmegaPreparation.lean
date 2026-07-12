/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.PhysicalSectorSubspinMaps
import TNLean.MPS.MPDO.PhysicalSectorTraceActions

/-!
# Preparations of the three-site neighboring operator

For a physical-sector factorization, the four middle subspins between outer
sectors (k) and (h) carry

\[
  \Omega_{k,h}=\bigoplus_l(\eta_{k,l}\otimes\eta_{l,h}).
\]

This file proves positivity and the trace identity
\(\operatorname{tr}(\Omega_{k,h})=a_kb_h\). On an active sector pair,
\(\Omega_{k,h}\) is normalized by \((a_kb_h)^{-1}\). On a zero-weight pair,
the source quotient is undefined; a density matrix is chosen on the same
subspin space to extend the preparation to a trace-preserving completely
positive map. These preparations are combined according to the orthogonal
outer-sector decomposition in the definition of \(\mathcal T_1\).

**Local fix (zero-weight quotient):** the density chosen on an inactive pair
makes the source map total without adding a nonzero-weight hypothesis. This is
documented in
`docs/paper-gaps/cpgsv17_mpdo_zero_weight_preparation_completion.tex`.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Appendix C.2, lines 1510--1516 and 1523--1535
-/

open scoped Matrix BigOperators ComplexOrder Kronecker

namespace MPOTensor.PhysicalSectorFactorization

variable {d D : ℕ} {K : MPOTensor d D} {F : PhysicalSectorFactorization K}

/-! ### The direct-sum neighboring operator -/

/-- The operator on the four middle subspins between outer sectors (k) and
(h):
\[
  \Omega_{k,h}=\bigoplus_l(\eta_{k,l}\otimes\eta_{l,h}).
\]

Source: arXiv:1606.00608, Appendix C.2, lines 1510--1516 and 1527--1535. -/
noncomputable def threeSiteNeighboringOperator
    (F : PhysicalSectorFactorization K) (k h : Fin F.sectorCount) :
    Matrix (ThreeSiteMiddleIndex F k h) (ThreeSiteMiddleIndex F k h) ℂ :=
  Matrix.blockDiagonal' fun l ↦
    F.neighboringOperator k l ⊗ₖ F.neighboringOperator l h

/-- The trace of \(\Omega_{k,h}\) is the sum of the products of the two
neighboring-operator traces.

Source: arXiv:1606.00608, Appendix C.2, lines 1510--1516 and 1527--1535. -/
theorem trace_threeSiteNeighboringOperator
    (F : PhysicalSectorFactorization K) (k h : Fin F.sectorCount) :
    (F.threeSiteNeighboringOperator k h).trace =
      ∑ l, (F.neighboringOperator k l).trace *
        (F.neighboringOperator l h).trace := by
  rw [threeSiteNeighboringOperator, Matrix.trace_blockDiagonal']
  simp only [Matrix.trace_kronecker]

/-- The operator \(\Omega_{k,h}\) is positive semidefinite.

Source: arXiv:1606.00608, Appendix C.2, lines 1510--1516 and 1527--1535. -/
theorem NeighboringTraceFactorization.threeSiteNeighboringOperator_pos
    (H : NeighboringTraceFactorization F) (k h : Fin F.sectorCount) :
    (F.threeSiteNeighboringOperator k h).PosSemidef := by
  apply Matrix.PosSemidef.blockDiagonal'
  intro l
  exact (H.neighboringOperator_pos k l).kronecker
    (H.neighboringOperator_pos l h)

/-- Under the rank-one trace factorization,
\(\operatorname{tr}(\Omega_{k,h})=a_kb_h\).

Source: arXiv:1606.00608, Appendix C.2, lines 1527--1535. -/
theorem NeighboringTraceFactorization.trace_threeSiteNeighboringOperator
    (H : NeighboringTraceFactorization F) (k h : Fin F.sectorCount) :
    (F.threeSiteNeighboringOperator k h).trace =
      ((H.a k * H.b h : ℝ) : ℂ) := by
  rw [F.trace_threeSiteNeighboringOperator]
  exact H.sum_threeSite_trace_coefficients k h

/-- The sector set is nonempty because \(\sum_l a_lb_l=1\).

Source: arXiv:1606.00608, Appendix C.2, lines 1395--1402. -/
theorem NeighboringTraceFactorization.sector_nonempty
    (H : NeighboringTraceFactorization F) : Nonempty (Fin F.sectorCount) := by
  by_contra hempty
  haveI : IsEmpty (Fin F.sectorCount) := not_nonempty_iff.mp hempty
  have hzero : ∑ l : Fin F.sectorCount, H.a l * H.b l = 0 := by simp
  have hsum := H.sum_mul
  rw [hzero] at hsum
  norm_num at hsum

/-- The subspin space carrying \(\Omega_{k,h}\) is nonempty.

Source: arXiv:1606.00608, Appendix C.2, lines 1381--1388 and 1527--1535. -/
theorem NeighboringTraceFactorization.threeSiteMiddleIndex_nonempty
    (H : NeighboringTraceFactorization F) (k h : Fin F.sectorCount) :
    Nonempty (ThreeSiteMiddleIndex F k h) := by
  rcases H.sector_nonempty with ⟨l⟩
  rcases F.neighborIndex_nonempty k l with ⟨u⟩
  rcases F.neighborIndex_nonempty l h with ⟨v⟩
  exact ⟨⟨l, (u, v)⟩⟩

/-- If \(a_kb_h=0\), then \(\Omega_{k,h}=0\).

Source: arXiv:1606.00608, Appendix C.2, lines 1527--1535. -/
theorem NeighboringTraceFactorization.threeSiteNeighboringOperator_eq_zero_of_mul_eq_zero
    (H : NeighboringTraceFactorization F) (k h : Fin F.sectorCount)
    (hzero : H.a k * H.b h = 0) :
    F.threeSiteNeighboringOperator k h = 0 := by
  apply (Matrix.PosSemidef.trace_eq_zero_iff
    (H.threeSiteNeighboringOperator_pos k h)).mp
  rw [H.trace_threeSiteNeighboringOperator, hzero]
  norm_num

/-! ### Normalization and completion -/

/-- The normalized operator \((a_kb_h)^{-1}\Omega_{k,h}\). Its trace is one
when \(a_kb_h\ne0\), which is the domain of the quotient in the source.

Source: arXiv:1606.00608, Appendix C.2, lines 1527--1535. -/
noncomputable def NeighboringTraceFactorization.normalizedThreeSiteNeighboringDensity
    (H : NeighboringTraceFactorization F) (k h : Fin F.sectorCount) :
    Matrix (ThreeSiteMiddleIndex F k h) (ThreeSiteMiddleIndex F k h) ℂ :=
  (((H.a k * H.b h)⁻¹ : ℝ) : ℂ) • F.threeSiteNeighboringOperator k h

/-- The normalized three-site neighboring operator is positive semidefinite.

Source: arXiv:1606.00608, Appendix C.2, lines 1527--1535. -/
theorem NeighboringTraceFactorization.normalizedThreeSiteNeighboringDensity_pos
    (H : NeighboringTraceFactorization F) (k h : Fin F.sectorCount) :
    (H.normalizedThreeSiteNeighboringDensity k h).PosSemidef := by
  apply (H.threeSiteNeighboringOperator_pos k h).smul
  exact_mod_cast inv_nonneg.mpr (H.weight_nonneg k h)

/-- On an active pair, the normalized three-site neighboring operator has
trace one.

Source: arXiv:1606.00608, Appendix C.2, lines 1527--1535. -/
theorem NeighboringTraceFactorization.trace_normalizedThreeSiteNeighboringDensity
    (H : NeighboringTraceFactorization F) (k h : Fin F.sectorCount)
    (hactive : H.a k * H.b h ≠ 0) :
    (H.normalizedThreeSiteNeighboringDensity k h).trace = 1 := by
  simp only [NeighboringTraceFactorization.normalizedThreeSiteNeighboringDensity,
    Matrix.trace_smul, H.trace_threeSiteNeighboringOperator, smul_eq_mul]
  norm_cast
  exact inv_mul_cancel₀ hactive

/-- A density matrix used to extend the preparation on a zero-weight outer
sector pair, where the quotient in the source formula is undefined.

**Local fix (zero-weight quotient):** this completion makes the source map
total without adding a nonzero-weight hypothesis. Documented in
`docs/paper-gaps/cpgsv17_mpdo_zero_weight_preparation_completion.tex`.

Source formula: arXiv:1606.00608, Appendix C.2, lines 1527--1535. -/
noncomputable def NeighboringTraceFactorization.inactiveThreeSiteNeighboringDensity
    (H : NeighboringTraceFactorization F) (k h : Fin F.sectorCount) :
    Matrix (ThreeSiteMiddleIndex F k h) (ThreeSiteMiddleIndex F k h) ℂ :=
  letI := H.threeSiteMiddleIndex_nonempty k h
  Matrix.faithfulDensity _

/-- The density chosen on a zero-weight pair is positive definite.

This is the zero-weight completion of the source formula at arXiv:1606.00608,
Appendix C.2, lines 1527--1535. -/
theorem NeighboringTraceFactorization.inactiveThreeSiteNeighboringDensity_posDef
    (H : NeighboringTraceFactorization F) (k h : Fin F.sectorCount) :
    (H.inactiveThreeSiteNeighboringDensity k h).PosDef :=
  letI := H.threeSiteMiddleIndex_nonempty k h
  Matrix.faithfulDensity_posDef _

/-- The density chosen on a zero-weight pair has trace one.

This is the zero-weight completion of the source formula at arXiv:1606.00608,
Appendix C.2, lines 1527--1535. -/
theorem NeighboringTraceFactorization.inactiveThreeSiteNeighboringDensity_trace
    (H : NeighboringTraceFactorization F) (k h : Fin F.sectorCount) :
    (H.inactiveThreeSiteNeighboringDensity k h).trace = 1 :=
  letI := H.threeSiteMiddleIndex_nonempty k h
  Matrix.faithfulDensity_trace _

/-- The completed three-site neighboring density is the normalized source
operator on an active pair and a density matrix on a zero-weight pair.

The second branch extends the source formula to a trace-preserving map where
the quotient \((a_kb_h)^{-1}\) is undefined.

**Local fix (zero-weight quotient):** documented in
`docs/paper-gaps/cpgsv17_mpdo_zero_weight_preparation_completion.tex`.

Source: arXiv:1606.00608, Appendix C.2, lines 1527--1535. -/
noncomputable def NeighboringTraceFactorization.completedThreeSiteNeighboringDensity
    (H : NeighboringTraceFactorization F) (k h : Fin F.sectorCount) :
    Matrix (ThreeSiteMiddleIndex F k h) (ThreeSiteMiddleIndex F k h) ℂ :=
  if H.a k * H.b h ≠ 0 then H.normalizedThreeSiteNeighboringDensity k h
  else H.inactiveThreeSiteNeighboringDensity k h

/-- Every completed three-site neighboring density is positive semidefinite.

Source formula: arXiv:1606.00608, Appendix C.2, lines 1527--1535. -/
theorem NeighboringTraceFactorization.completedThreeSiteNeighboringDensity_pos
    (H : NeighboringTraceFactorization F) (k h : Fin F.sectorCount) :
    (H.completedThreeSiteNeighboringDensity k h).PosSemidef := by
  rw [NeighboringTraceFactorization.completedThreeSiteNeighboringDensity]
  split_ifs
  · exact H.normalizedThreeSiteNeighboringDensity_pos k h
  · exact (H.inactiveThreeSiteNeighboringDensity_posDef k h).posSemidef

/-- Every completed three-site neighboring density has trace one.

Source formula: arXiv:1606.00608, Appendix C.2, lines 1527--1535. -/
theorem NeighboringTraceFactorization.trace_completedThreeSiteNeighboringDensity
    (H : NeighboringTraceFactorization F) (k h : Fin F.sectorCount) :
    (H.completedThreeSiteNeighboringDensity k h).trace = 1 := by
  rw [NeighboringTraceFactorization.completedThreeSiteNeighboringDensity]
  split_ifs with hactive
  · exact H.trace_normalizedThreeSiteNeighboringDensity k h hactive
  · exact H.inactiveThreeSiteNeighboringDensity_trace k h

/-- On an active pair, the completed density is
\((a_kb_h)^{-1}\Omega_{k,h}\). -/
theorem NeighboringTraceFactorization.completedThreeSiteNeighboringDensity_eq_normalized
    (H : NeighboringTraceFactorization F) (k h : Fin F.sectorCount)
    (hactive : H.a k * H.b h ≠ 0) :
    H.completedThreeSiteNeighboringDensity k h =
      H.normalizedThreeSiteNeighboringDensity k h := by
  simp [NeighboringTraceFactorization.completedThreeSiteNeighboringDensity, hactive]

/-! ### The controlled preparation -/

/-- The sectorwise map which adjoins the completed three-site neighboring
density.

Source: arXiv:1606.00608, Appendix C.2, lines 1527--1535. -/
noncomputable def NeighboringTraceFactorization.completedThreeSitePreparationMap
    {α : Type*} [Fintype α] [DecidableEq α]
    (H : NeighboringTraceFactorization F) (k h : Fin F.sectorCount) :
    Matrix α α ℂ →ₗ[ℂ]
      Matrix (α × ThreeSiteMiddleIndex F k h)
        (α × ThreeSiteMiddleIndex F k h) ℂ :=
  Matrix.preparationMap (H.completedThreeSiteNeighboringDensity k h)

/-- Adjoining the completed three-site neighboring density is
trace-preserving and completely positive.

Source: arXiv:1606.00608, Appendix C.2, lines 1527--1535. -/
theorem NeighboringTraceFactorization.completedThreeSitePreparationMap_isKrausCPTP
    {α : Type*} [Fintype α] [DecidableEq α]
    (H : NeighboringTraceFactorization F) (k h : Fin F.sectorCount) :
    IsKrausCPTP (H.completedThreeSitePreparationMap (α := α) k h) := by
  simpa [NeighboringTraceFactorization.completedThreeSitePreparationMap] using
    Matrix.preparationMap_isKrausCPTP _
      (H.completedThreeSiteNeighboringDensity_pos k h)
      (H.trace_completedThreeSiteNeighboringDensity k h)

/-- On an active pair, the completed preparation adjoins the normalized
operator \((a_kb_h)^{-1}\Omega_{k,h}\). -/
theorem NeighboringTraceFactorization.completedThreeSitePreparationMap_eq_normalized
    {α : Type*} [Fintype α] [DecidableEq α]
    (H : NeighboringTraceFactorization F) (k h : Fin F.sectorCount)
    (hactive : H.a k * H.b h ≠ 0) :
    H.completedThreeSitePreparationMap (α := α) k h =
      Matrix.preparationMap (H.normalizedThreeSiteNeighboringDensity k h) := by
  rw [NeighboringTraceFactorization.completedThreeSitePreparationMap,
    H.completedThreeSiteNeighboringDensity_eq_normalized k h hactive]

section ControlledPreparation

variable {α : Fin F.sectorCount × Fin F.sectorCount → Type*}
variable [∀ p, Fintype (α p)] [∀ p, DecidableEq (α p)]

/-- The orthogonally controlled preparation of \(\Omega_{k,h}\). It discards
coherences between distinct pairs of outer sectors and adjoins the completed
three-site neighboring density in every diagonal pair.

On active pairs this is \(\mathcal T_{k,h}\) from the source; the zero-weight
branch is its trace-preserving extension.

**Local fix (zero-weight quotient):** the inactive branch makes the source map
total without adding a nonzero-weight hypothesis. Documented in
`docs/paper-gaps/cpgsv17_mpdo_zero_weight_preparation_completion.tex`.

Source: arXiv:1606.00608, Appendix C.2, lines 1523--1535. -/
noncomputable def NeighboringTraceFactorization.completedThreeSiteControlledMap
    (H : NeighboringTraceFactorization F) :
    Matrix (Σ p, α p) (Σ p, α p) ℂ →ₗ[ℂ]
      Matrix (Σ p, α p × ThreeSiteMiddleIndex F p.1 p.2)
        (Σ p, α p × ThreeSiteMiddleIndex F p.1 p.2) ℂ :=
  Matrix.controlledKrausMap
    (fun p ↦ Fintype.card (ThreeSiteMiddleIndex F p.1 p.2))
    (fun p j ↦ Matrix.preparationKraus
      (H.completedThreeSiteNeighboringDensity p.1 p.2)
      (H.completedThreeSiteNeighboringDensity_pos p.1 p.2)
      ((Fintype.equivFin (ThreeSiteMiddleIndex F p.1 p.2)).symm j))

/-- On a diagonal outer-sector pair, the controlled map is preparation of
the completed three-site neighboring density.

Source: arXiv:1606.00608, Appendix C.2, lines 1523--1535. -/
theorem NeighboringTraceFactorization.completedThreeSiteControlledMap_sameBlock_apply
    (H : NeighboringTraceFactorization F)
    (X : Matrix (Σ p, α p) (Σ p, α p) ℂ)
    (p : Fin F.sectorCount × Fin F.sectorCount) (a b : α p)
    (u v : ThreeSiteMiddleIndex F p.1 p.2) :
    H.completedThreeSiteControlledMap X ⟨p, (a, u)⟩ ⟨p, (b, v)⟩ =
      H.completedThreeSitePreparationMap p.1 p.2
        (X.submatrix (Sigma.mk p) (Sigma.mk p)) (a, u) (b, v) := by
  classical
  rw [NeighboringTraceFactorization.completedThreeSiteControlledMap,
    Matrix.controlledKrausMap_sameBlock_apply,
    Matrix.rectangularKrausMap_equiv
      (Fintype.equivFin (ThreeSiteMiddleIndex F p.1 p.2)),
    Matrix.rectangularKrausMap_preparationKraus_eq]
  rfl

/-- The orthogonally controlled three-site neighboring preparation is
trace-preserving and completely positive.

Source: arXiv:1606.00608, Appendix C.2, lines 1523--1535. -/
theorem NeighboringTraceFactorization.completedThreeSiteControlledMap_isKrausCPTP
    (H : NeighboringTraceFactorization F) :
    IsKrausCPTP (H.completedThreeSiteControlledMap (α := α)) := by
  apply Matrix.controlledKrausMap_isKrausCPTP
  intro p
  exact Matrix.preparationKraus_resolution
    (H.completedThreeSiteNeighboringDensity p.1 p.2)
    (H.completedThreeSiteNeighboringDensity_pos p.1 p.2)
    (H.trace_completedThreeSiteNeighboringDensity p.1 p.2)

end ControlledPreparation

end MPOTensor.PhysicalSectorFactorization
