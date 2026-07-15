/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.Channel.KrausCPTP
import TNLean.MPS.MPDO.SimpleLocalStructure
import TNLean.Algebra.MatrixAux

/-!
# Normalized neighboring-operator preparations

This file defines the direct-sum operator

$$
\Omega_{k,h}=\bigoplus_l(\eta_{k,l}\otimes\eta_{l,h})
$$

from arXiv:1606.00608, Appendix C.2, lines 1527--1535. It proves positivity,
computes its trace from the rank-one trace factorization
$\operatorname{tr}(\eta_{k,h})=a_kb_h$, and treats the pairs with
$a_kb_h=0$ without assuming that all sector weights are nonzero.

The results construct the individual normalized preparations on active sector
pairs, complete the zero-weight pairs with faithful density matrices, and
assemble the completed families into global orthogonally controlled maps.
-/

open scoped Matrix BigOperators ComplexOrder

namespace MPOTensor.ExplicitEtaOperators

variable {dA dB dC : ℕ}
variable {rhoABC : Matrix (Fin dA × Fin dB × Fin dC)
  (Fin dA × Fin dB × Fin dC) ℂ}
variable {hη : EtaStructure rhoABC}

/-- The rank-one trace factorization of the neighboring operators:
$\operatorname{tr}(\eta_{k,h})=a_kb_h$ and $\sum_l a_lb_l=1$.

Source: arXiv:1606.00608, Appendix C.2, lines 1395--1402. -/
structure RankOneTraceFactorization (data : ExplicitEtaOperators hη) where
  a : Fin hη.m → ℝ
  b : Fin hη.m → ℝ
  trace_eta : ∀ k h, (data.eta k h).trace = ((a k * b h : ℝ) : ℂ)
  sum_mul : ∑ l, a l * b l = 1

/-- The index space of the neighboring operator $\eta_{k,h}$. -/
abbrev EtaIndex (k h : Fin hη.m) := Fin (hη.dR k) × Fin (hη.dL h)

/-- The index space of
$\Omega_{k,h}=\bigoplus_l(\eta_{k,l}\otimes\eta_{l,h})$.
The outer sigma coordinate records the intermediate sector $l$. -/
abbrev OmegaIndex (k h : Fin hη.m) :=
  Σ l : Fin hη.m,
    (Fin (hη.dR k) × Fin (hη.dL l)) ×
      (Fin (hη.dR l) × Fin (hη.dL h))

/-- Every right Hayashi factor is nonempty. This follows from the trace-one
right density matrix, without a separate dimension hypothesis. -/
lemma dR_nonempty (hη : EtaStructure rhoABC) (k : Fin hη.m) :
    Nonempty (Fin (hη.dR k)) := by
  have hp : Nonempty (Fin (hη.dR k) × Fin dC) :=
    Matrix.nonempty_of_trace_eq_one (hη.ρ_right k) (hη.hρ_right_dm k).2
  exact hp.map Prod.fst

/-- Every left Hayashi factor is nonempty. This follows from the trace-one
left density matrix, without a separate dimension hypothesis. -/
lemma dL_nonempty (hη : EtaStructure rhoABC) (k : Fin hη.m) :
    Nonempty (Fin (hη.dL k)) := by
  have hp : Nonempty (Fin dA × Fin (hη.dL k)) :=
    Matrix.nonempty_of_trace_eq_one (hη.ρ_left k) (hη.hρ_left_dm k).2
  exact hp.map Prod.snd

/-- The Hayashi sector set is nonempty because its probabilities sum to one. -/
lemma sector_nonempty (hη : EtaStructure rhoABC) : Nonempty (Fin hη.m) := by
  classical
  by_contra h
  haveI : IsEmpty (Fin hη.m) := not_nonempty_iff.mp h
  have hzero : ∑ k : Fin hη.m, hη.p k = 0 := by simp
  have hsum := hη.hp_sum
  rw [hzero] at hsum
  norm_num at hsum

/-- The neighboring-operator space is nonempty for every sector pair. -/
lemma etaIndex_nonempty (hη : EtaStructure rhoABC) (k h : Fin hη.m) :
    Nonempty (EtaIndex (hη := hη) k h) := by
  letI := dR_nonempty hη k
  letI := dL_nonempty hη h
  infer_instance

/-- The direct-sum neighboring-operator space is nonempty for every sector
pair. -/
lemma omegaIndex_nonempty (hη : EtaStructure rhoABC) (k h : Fin hη.m) :
    Nonempty (OmegaIndex (hη := hη) k h) := by
  rcases sector_nonempty hη with ⟨l⟩
  letI := dR_nonempty hη k
  letI := dL_nonempty hη l
  letI := dR_nonempty hη l
  letI := dL_nonempty hη h
  exact (inferInstance : Nonempty
    ((Fin (hη.dR k) × Fin (hη.dL l)) ×
      (Fin (hη.dR l) × Fin (hη.dL h)))).map (Sigma.mk l)

/-- The direct sum
$\Omega_{k,h}=\bigoplus_l(\eta_{k,l}\otimes\eta_{l,h})$, adjoined by the
preparation map $\mathcal T_{k,h}$ in arXiv:1606.00608, Appendix C.2,
lines 1527--1535. -/
noncomputable def omega (data : ExplicitEtaOperators hη) (k h : Fin hη.m) :
    Matrix (OmegaIndex k h) (OmegaIndex k h) ℂ :=
  Matrix.blockDiagonal' fun l ↦
    Matrix.kroneckerMap (· * ·) (data.eta k l) (data.eta l h)

/-- Each $\Omega_{k,h}$ is positive semidefinite.

Source: arXiv:1606.00608, Appendix C.2, lines 1527--1535. -/
theorem omega_pos (data : ExplicitEtaOperators hη) (k h : Fin hη.m) :
    (data.omega k h).PosSemidef := by
  apply Matrix.PosSemidef.blockDiagonal'
  intro l
  exact (data.eta_pos k l).kronecker (data.eta_pos l h)

/-- The trace of $\Omega_{k,h}$ is the sum of the products of the two
neighboring-operator traces:

$$
\operatorname{tr}(\Omega_{k,h})
=\sum_l\operatorname{tr}(\eta_{k,l})\operatorname{tr}(\eta_{l,h}).
$$

Source: arXiv:1606.00608, Appendix C.2, lines 1527--1535. -/
theorem trace_omega (data : ExplicitEtaOperators hη) (k h : Fin hη.m) :
    (data.omega k h).trace =
      ∑ l, (data.eta k l).trace * (data.eta l h).trace := by
  rw [omega, Matrix.trace_blockDiagonal']
  simp only [Matrix.trace_kronecker]

/-- Under the source rank-one trace factorization,
$\operatorname{tr}(\Omega_{k,h})=a_kb_h$.

Source: arXiv:1606.00608, Appendix C.2, lines 1395--1402 and 1531--1535. -/
theorem trace_omega_eq_mul (data : ExplicitEtaOperators hη)
    (factor : RankOneTraceFactorization data) (k h : Fin hη.m) :
    (data.omega k h).trace = ((factor.a k * factor.b h : ℝ) : ℂ) := by
  rw [data.trace_omega]
  simp_rw [factor.trace_eta]
  norm_cast
  calc
    ∑ l, factor.a k * factor.b l * (factor.a l * factor.b h) =
        factor.a k * (∑ l, factor.a l * factor.b l) * factor.b h := by
      rw [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro l _
      ring
    _ = factor.a k * factor.b h := by rw [factor.sum_mul]; ring

/-- Every sector weight $a_kb_h$ is nonnegative, as it is the trace of the
positive semidefinite operator $\eta_{k,h}$. -/
theorem weight_nonneg (data : ExplicitEtaOperators hη)
    (factor : RankOneTraceFactorization data) (k h : Fin hη.m) :
    0 ≤ factor.a k * factor.b h := by
  have htrace := (data.eta_pos k h).trace_nonneg
  rw [factor.trace_eta] at htrace
  exact_mod_cast htrace

/-- If $a_kb_h=0$, then the corresponding positive operator
$\eta_{k,h}$ vanishes. -/
theorem eta_eq_zero_of_mul_eq_zero (data : ExplicitEtaOperators hη)
    (factor : RankOneTraceFactorization data) (k h : Fin hη.m)
    (hzero : factor.a k * factor.b h = 0) :
    data.eta k h = 0 := by
  apply (Matrix.PosSemidef.trace_eq_zero_iff (data.eta_pos k h)).mp
  rw [factor.trace_eta, hzero]
  norm_num

/-- If $a_kb_h=0$, then the corresponding positive direct-sum operator
$\Omega_{k,h}$ vanishes. -/
theorem omega_eq_zero_of_mul_eq_zero (data : ExplicitEtaOperators hη)
    (factor : RankOneTraceFactorization data) (k h : Fin hη.m)
    (hzero : factor.a k * factor.b h = 0) :
    data.omega k h = 0 := by
  apply (Matrix.PosSemidef.trace_eq_zero_iff (data.omega_pos k h)).mp
  rw [data.trace_omega_eq_mul factor k h, hzero]
  norm_num

/-- The normalized neighboring operator on an active pair $a_kb_h\ne0$.
The definition is also meaningful on a zero pair, but it is used only with an
active-pair hypothesis. -/
noncomputable def normalizedEta (data : ExplicitEtaOperators hη)
    (factor : RankOneTraceFactorization data) (k h : Fin hη.m) :=
  (((factor.a k * factor.b h)⁻¹ : ℝ) : ℂ) • data.eta k h

/-- The normalized direct-sum operator on an active pair $a_kb_h\ne0$.
The definition is also meaningful on a zero pair, but it is used only with an
active-pair hypothesis. -/
noncomputable def normalizedOmega (data : ExplicitEtaOperators hη)
    (factor : RankOneTraceFactorization data) (k h : Fin hη.m) :=
  (((factor.a k * factor.b h)⁻¹ : ℝ) : ℂ) • data.omega k h

/-- The normalized neighboring operator is positive semidefinite. On a zero
pair it is the zero operator; the trace-one statement below is restricted to
active pairs.

Source: arXiv:1606.00608, Appendix C.2, lines 1551--1555. -/
theorem normalizedEta_pos (data : ExplicitEtaOperators hη)
    (factor : RankOneTraceFactorization data) (k h : Fin hη.m) :
    (data.normalizedEta factor k h).PosSemidef := by
  apply (data.eta_pos k h).smul
  exact_mod_cast inv_nonneg.mpr (data.weight_nonneg factor k h)

/-- On an active pair, the normalized neighboring operator has trace one.

Source: arXiv:1606.00608, Appendix C.2, lines 1551--1555. -/
theorem trace_normalizedEta (data : ExplicitEtaOperators hη)
    (factor : RankOneTraceFactorization data) (k h : Fin hη.m)
    (hactive : factor.a k * factor.b h ≠ 0) :
    (data.normalizedEta factor k h).trace = 1 := by
  simp only [normalizedEta, Matrix.trace_smul, factor.trace_eta, smul_eq_mul]
  norm_cast
  exact inv_mul_cancel₀ hactive

/-- The normalized direct-sum operator is positive semidefinite. On a zero
pair it is the zero operator; the trace-one statement below is restricted to
active pairs.

Source: arXiv:1606.00608, Appendix C.2, lines 1527--1535. -/
theorem normalizedOmega_pos (data : ExplicitEtaOperators hη)
    (factor : RankOneTraceFactorization data) (k h : Fin hη.m) :
    (data.normalizedOmega factor k h).PosSemidef := by
  apply (data.omega_pos k h).smul
  exact_mod_cast inv_nonneg.mpr (data.weight_nonneg factor k h)

/-- On an active pair, the normalized direct-sum operator has trace one.

Source: arXiv:1606.00608, Appendix C.2, lines 1527--1535. -/
theorem trace_normalizedOmega (data : ExplicitEtaOperators hη)
    (factor : RankOneTraceFactorization data) (k h : Fin hη.m)
    (hactive : factor.a k * factor.b h ≠ 0) :
    (data.normalizedOmega factor k h).trace = 1 := by
  simp only [normalizedOmega, Matrix.trace_smul,
    data.trace_omega_eq_mul factor k h, smul_eq_mul]
  norm_cast
  exact inv_mul_cancel₀ hactive

/-- On an active pair, adjoining the normalized neighboring operator is a
trace-preserving completely positive map. This is the individual
$\mathcal S_{k,h}$ preparation from arXiv:1606.00608, Appendix C.2,
lines 1551--1555. -/
theorem normalizedEta_preparationMap_isKrausCPTP
    {α : Type*} [Fintype α] [DecidableEq α]
    (data : ExplicitEtaOperators hη) (factor : RankOneTraceFactorization data)
    (k h : Fin hη.m) (hactive : factor.a k * factor.b h ≠ 0) :
    IsKrausCPTP (Matrix.preparationMap (α := α)
      (data.normalizedEta factor k h)) :=
  Matrix.preparationMap_isKrausCPTP _
    (data.normalizedEta_pos factor k h) (data.trace_normalizedEta factor k h hactive)

/-- On an active pair, adjoining the normalized direct-sum operator is a
trace-preserving completely positive map. This is the individual
$\mathcal T_{k,h}$ preparation from arXiv:1606.00608, Appendix C.2,
lines 1527--1535. -/
theorem normalizedOmega_preparationMap_isKrausCPTP
    {α : Type*} [Fintype α] [DecidableEq α]
    (data : ExplicitEtaOperators hη) (factor : RankOneTraceFactorization data)
    (k h : Fin hη.m) (hactive : factor.a k * factor.b h ≠ 0) :
    IsKrausCPTP (Matrix.preparationMap (α := α)
      (data.normalizedOmega factor k h)) :=
  Matrix.preparationMap_isKrausCPTP _
    (data.normalizedOmega_pos factor k h) (data.trace_normalizedOmega factor k h hactive)

/-! ## Completion on inactive sector pairs -/

/-- The faithful uniform density matrix used to complete a zero-weight
neighboring sector. The nonemptiness of its space follows from the trace-one
Hayashi density matrices. -/
noncomputable def inactiveEtaDensity (hη : EtaStructure rhoABC) (k h : Fin hη.m) :
    Matrix (EtaIndex (hη := hη) k h) (EtaIndex (hη := hη) k h) ℂ :=
  letI := etaIndex_nonempty hη k h
  Matrix.faithfulDensity _

/-- The inactive neighboring-sector density is positive definite. -/
theorem inactiveEtaDensity_posDef (hη : EtaStructure rhoABC) (k h : Fin hη.m) :
    (inactiveEtaDensity hη k h).PosDef :=
  letI := etaIndex_nonempty hη k h
  Matrix.faithfulDensity_posDef _

/-- The inactive neighboring-sector density has trace one. -/
theorem inactiveEtaDensity_trace (hη : EtaStructure rhoABC) (k h : Fin hη.m) :
    (inactiveEtaDensity hη k h).trace = 1 :=
  letI := etaIndex_nonempty hη k h
  Matrix.faithfulDensity_trace _

/-- The faithful uniform density matrix used to complete a zero-weight
direct-sum neighboring sector. The nonemptiness of its space follows from the
trace-one Hayashi density matrices and probabilities. -/
noncomputable def inactiveOmegaDensity (hη : EtaStructure rhoABC) (k h : Fin hη.m) :
    Matrix (OmegaIndex (hη := hη) k h) (OmegaIndex (hη := hη) k h) ℂ :=
  letI := omegaIndex_nonempty hη k h
  Matrix.faithfulDensity _

/-- The inactive direct-sum neighboring-sector density is positive definite. -/
theorem inactiveOmegaDensity_posDef (hη : EtaStructure rhoABC) (k h : Fin hη.m) :
    (inactiveOmegaDensity hη k h).PosDef :=
  letI := omegaIndex_nonempty hη k h
  Matrix.faithfulDensity_posDef _

/-- The inactive direct-sum neighboring-sector density has trace one. -/
theorem inactiveOmegaDensity_trace (hη : EtaStructure rhoABC) (k h : Fin hη.m) :
    (inactiveOmegaDensity hη k h).trace = 1 :=
  letI := omegaIndex_nonempty hη k h
  Matrix.faithfulDensity_trace _

/-- The completed neighboring density equals the normalized source operator
on an active pair and the faithful uniform density on a zero-weight pair.

On active pairs this is the state adjoined by $\mathcal S_{k,h}$ in
arXiv:1606.00608, Appendix C.2, lines 1551--1555. The inactive branch is a
trace-preserving extension where the source quotient is undefined. -/
noncomputable def completedEta (data : ExplicitEtaOperators hη)
    (factor : RankOneTraceFactorization data) (k h : Fin hη.m) :
    Matrix (EtaIndex (hη := hη) k h) (EtaIndex (hη := hη) k h) ℂ :=
  if factor.a k * factor.b h ≠ 0 then data.normalizedEta factor k h
  else inactiveEtaDensity hη k h

/-- The completed direct-sum density equals the normalized source operator on
an active pair and the faithful uniform density on a zero-weight pair.

On active pairs this is the state adjoined by $\mathcal T_{k,h}$ in
arXiv:1606.00608, Appendix C.2, lines 1527--1535. The inactive branch is a
trace-preserving extension where the source quotient is undefined. -/
noncomputable def completedOmega (data : ExplicitEtaOperators hη)
    (factor : RankOneTraceFactorization data) (k h : Fin hη.m) :
    Matrix (OmegaIndex (hη := hη) k h) (OmegaIndex (hη := hη) k h) ℂ :=
  if factor.a k * factor.b h ≠ 0 then data.normalizedOmega factor k h
  else inactiveOmegaDensity hη k h

/-- The completed neighboring density is positive semidefinite on every
sector pair. -/
theorem completedEta_pos (data : ExplicitEtaOperators hη)
    (factor : RankOneTraceFactorization data) (k h : Fin hη.m) :
    (data.completedEta factor k h).PosSemidef := by
  rw [completedEta]
  split_ifs
  · exact data.normalizedEta_pos factor k h
  · exact (inactiveEtaDensity_posDef hη k h).posSemidef

/-- The completed neighboring density has trace one on every sector pair. -/
theorem trace_completedEta (data : ExplicitEtaOperators hη)
    (factor : RankOneTraceFactorization data) (k h : Fin hη.m) :
    (data.completedEta factor k h).trace = 1 := by
  rw [completedEta]
  split_ifs with hactive
  · exact data.trace_normalizedEta factor k h hactive
  · exact inactiveEtaDensity_trace hη k h

/-- The completed direct-sum density is positive semidefinite on every sector
pair. -/
theorem completedOmega_pos (data : ExplicitEtaOperators hη)
    (factor : RankOneTraceFactorization data) (k h : Fin hη.m) :
    (data.completedOmega factor k h).PosSemidef := by
  rw [completedOmega]
  split_ifs
  · exact data.normalizedOmega_pos factor k h
  · exact (inactiveOmegaDensity_posDef hη k h).posSemidef

/-- The completed direct-sum density has trace one on every sector pair. -/
theorem trace_completedOmega (data : ExplicitEtaOperators hη)
    (factor : RankOneTraceFactorization data) (k h : Fin hη.m) :
    (data.completedOmega factor k h).trace = 1 := by
  rw [completedOmega]
  split_ifs with hactive
  · exact data.trace_normalizedOmega factor k h hactive
  · exact inactiveOmegaDensity_trace hη k h

/-- On an active pair, the completed neighboring density is the normalized
neighboring operator from the source formula. -/
theorem completedEta_eq_normalizedEta (data : ExplicitEtaOperators hη)
    (factor : RankOneTraceFactorization data) (k h : Fin hη.m)
    (hactive : factor.a k * factor.b h ≠ 0) :
    data.completedEta factor k h = data.normalizedEta factor k h := by
  simp [completedEta, hactive]

/-- On an active pair, the completed direct-sum density is the normalized
direct-sum operator from the source formula. -/
theorem completedOmega_eq_normalizedOmega (data : ExplicitEtaOperators hη)
    (factor : RankOneTraceFactorization data) (k h : Fin hη.m)
    (hactive : factor.a k * factor.b h ≠ 0) :
    data.completedOmega factor k h = data.normalizedOmega factor k h := by
  simp [completedOmega, hactive]

/-- The sectorwise preparation which adjoins the completed neighboring
density. -/
noncomputable def completedEtaPreparationMap
    {α : Type*} [Fintype α] [DecidableEq α]
    (data : ExplicitEtaOperators hη) (factor : RankOneTraceFactorization data)
    (k h : Fin hη.m) :
    Matrix α α ℂ →ₗ[ℂ]
      Matrix (α × EtaIndex (hη := hη) k h) (α × EtaIndex (hη := hη) k h) ℂ :=
  Matrix.preparationMap (data.completedEta factor k h)

/-- The sectorwise preparation which adjoins the completed direct-sum
density. -/
noncomputable def completedOmegaPreparationMap
    {α : Type*} [Fintype α] [DecidableEq α]
    (data : ExplicitEtaOperators hη) (factor : RankOneTraceFactorization data)
    (k h : Fin hη.m) :
    Matrix α α ℂ →ₗ[ℂ]
      Matrix (α × OmegaIndex (hη := hη) k h) (α × OmegaIndex (hη := hη) k h) ℂ :=
  Matrix.preparationMap (data.completedOmega factor k h)

/-- Adjoining the completed neighboring density is trace-preserving and
completely positive on every sector pair. It agrees with $\mathcal S_{k,h}$
of arXiv:1606.00608, Appendix C.2, lines 1551--1555, on active pairs. -/
theorem completedEta_preparationMap_isKrausCPTP
    {α : Type*} [Fintype α] [DecidableEq α]
    (data : ExplicitEtaOperators hη) (factor : RankOneTraceFactorization data)
    (k h : Fin hη.m) :
    IsKrausCPTP (data.completedEtaPreparationMap factor (α := α) k h) := by
  simpa [completedEtaPreparationMap] using Matrix.preparationMap_isKrausCPTP _
    (data.completedEta_pos factor k h) (data.trace_completedEta factor k h)

/-- Adjoining the completed direct-sum density is trace-preserving and
completely positive on every sector pair. It agrees with $\mathcal T_{k,h}$
of arXiv:1606.00608, Appendix C.2, lines 1527--1535, on active pairs. -/
theorem completedOmega_preparationMap_isKrausCPTP
    {α : Type*} [Fintype α] [DecidableEq α]
    (data : ExplicitEtaOperators hη) (factor : RankOneTraceFactorization data)
    (k h : Fin hη.m) :
    IsKrausCPTP (data.completedOmegaPreparationMap factor (α := α) k h) := by
  simpa [completedOmegaPreparationMap] using Matrix.preparationMap_isKrausCPTP _
    (data.completedOmega_pos factor k h) (data.trace_completedOmega factor k h)

/-- On an active pair, the completed neighboring preparation is the source
preparation. -/
theorem completedEtaPreparationMap_eq_normalized
    {α : Type*} [Fintype α] [DecidableEq α]
    (data : ExplicitEtaOperators hη) (factor : RankOneTraceFactorization data)
    (k h : Fin hη.m) (hactive : factor.a k * factor.b h ≠ 0) :
    data.completedEtaPreparationMap factor (α := α) k h =
      Matrix.preparationMap (data.normalizedEta factor k h) := by
  rw [completedEtaPreparationMap, data.completedEta_eq_normalizedEta factor k h hactive]

/-- On an active pair, the completed direct-sum preparation is the source
preparation. -/
theorem completedOmegaPreparationMap_eq_normalized
    {α : Type*} [Fintype α] [DecidableEq α]
    (data : ExplicitEtaOperators hη) (factor : RankOneTraceFactorization data)
    (k h : Fin hη.m) (hactive : factor.a k * factor.b h ≠ 0) :
    data.completedOmegaPreparationMap factor (α := α) k h =
      Matrix.preparationMap (data.normalizedOmega factor k h) := by
  rw [completedOmegaPreparationMap, data.completedOmega_eq_normalizedOmega factor k h hactive]

/-! ## Global orthogonally controlled preparations -/

section GlobalCompletion

variable {α : Fin hη.m × Fin hη.m → Type*}
variable [∀ p, Fintype (α p)] [∀ p, DecidableEq (α p)]

/-- The global orthogonally controlled neighboring-state preparation. It
discards coherences between sector pairs and adjoins the completed neighboring
density inside each diagonal sector.

On active pairs its sector maps are the $\mathcal S_{k,h}$ preparations in
arXiv:1606.00608, Appendix C.2, lines 1548--1555. The inactive sectors give a
trace-preserving extension and are not identified with the undefined source
quotient. -/
noncomputable def completedEtaControlledMap
    (data : ExplicitEtaOperators hη) (factor : RankOneTraceFactorization data) :
    Matrix (Σ p, α p) (Σ p, α p) ℂ →ₗ[ℂ]
      Matrix (Σ p, α p × EtaIndex (hη := hη) p.1 p.2)
        (Σ p, α p × EtaIndex (hη := hη) p.1 p.2) ℂ :=
  Matrix.controlledKrausMap
    (fun p => Fintype.card (EtaIndex (hη := hη) p.1 p.2))
    (fun p j => Matrix.preparationKraus (data.completedEta factor p.1 p.2)
      (data.completedEta_pos factor p.1 p.2)
      ((Fintype.equivFin (EtaIndex (hη := hη) p.1 p.2)).symm j))

/-- On each diagonal sector pair, the completed neighboring-state control is
the preparation map for the completed neighboring density.

Source: arXiv:1606.00608, Appendix C.2, lines 1548--1555. -/
theorem completedEtaControlledMap_sameBlock_apply
    (data : ExplicitEtaOperators hη) (factor : RankOneTraceFactorization data)
    (X : Matrix (Σ p, α p) (Σ p, α p) ℂ) (p : Fin hη.m × Fin hη.m)
    (a b : α p) (u v : EtaIndex (hη := hη) p.1 p.2) :
    data.completedEtaControlledMap factor X ⟨p, (a, u)⟩ ⟨p, (b, v)⟩ =
      data.completedEtaPreparationMap factor p.1 p.2
        (X.submatrix (Sigma.mk p) (Sigma.mk p)) (a, u) (b, v) := by
  classical
  rw [completedEtaControlledMap, Matrix.controlledKrausMap_sameBlock_apply,
    Matrix.rectangularKrausMap_equiv
      (Fintype.equivFin (EtaIndex (hη := hη) p.1 p.2)),
    Matrix.rectangularKrausMap_preparationKraus_eq]
  rfl

/-- The global orthogonally controlled neighboring-state preparation is
trace-preserving and completely positive.

This is the completed sector-control part of $\mathcal S_1$ in
arXiv:1606.00608, Appendix C.2, lines 1548--1555. It does not include the
regrouping and shift maps surrounding $\mathcal S_1$ in the full construction. -/
theorem completedEtaControlledMap_isKrausCPTP
    (data : ExplicitEtaOperators hη) (factor : RankOneTraceFactorization data) :
    IsKrausCPTP (data.completedEtaControlledMap factor (α := α)) := by
  apply Matrix.controlledKrausMap_isKrausCPTP
  intro p
  exact Matrix.preparationKraus_resolution (data.completedEta factor p.1 p.2)
    (data.completedEta_pos factor p.1 p.2) (data.trace_completedEta factor p.1 p.2)

/-- The global orthogonally controlled direct-sum preparation. It discards
coherences between sector pairs and adjoins the completed direct-sum density
inside each diagonal sector.

On active pairs its sector maps are the $\mathcal T_{k,h}$ preparations in
arXiv:1606.00608, Appendix C.2, lines 1523--1535. The inactive sectors give a
trace-preserving extension and are not identified with the undefined source
quotient. -/
noncomputable def completedOmegaControlledMap
    (data : ExplicitEtaOperators hη) (factor : RankOneTraceFactorization data) :
    Matrix (Σ p, α p) (Σ p, α p) ℂ →ₗ[ℂ]
      Matrix (Σ p, α p × OmegaIndex (hη := hη) p.1 p.2)
        (Σ p, α p × OmegaIndex (hη := hη) p.1 p.2) ℂ :=
  Matrix.controlledKrausMap
    (fun p => Fintype.card (OmegaIndex (hη := hη) p.1 p.2))
    (fun p j => Matrix.preparationKraus (data.completedOmega factor p.1 p.2)
      (data.completedOmega_pos factor p.1 p.2)
      ((Fintype.equivFin (OmegaIndex (hη := hη) p.1 p.2)).symm j))

/-- On each diagonal sector pair, the completed direct-sum control is the
preparation map for the completed direct-sum density.

Source: arXiv:1606.00608, Appendix C.2, lines 1523--1535. -/
theorem completedOmegaControlledMap_sameBlock_apply
    (data : ExplicitEtaOperators hη) (factor : RankOneTraceFactorization data)
    (X : Matrix (Σ p, α p) (Σ p, α p) ℂ) (p : Fin hη.m × Fin hη.m)
    (a b : α p) (u v : OmegaIndex (hη := hη) p.1 p.2) :
    data.completedOmegaControlledMap factor X ⟨p, (a, u)⟩ ⟨p, (b, v)⟩ =
      data.completedOmegaPreparationMap factor p.1 p.2
        (X.submatrix (Sigma.mk p) (Sigma.mk p)) (a, u) (b, v) := by
  classical
  rw [completedOmegaControlledMap, Matrix.controlledKrausMap_sameBlock_apply,
    Matrix.rectangularKrausMap_equiv
      (Fintype.equivFin (OmegaIndex (hη := hη) p.1 p.2)),
    Matrix.rectangularKrausMap_preparationKraus_eq]
  rfl

/-- The global orthogonally controlled direct-sum preparation is
trace-preserving and completely positive.

This is the completed sector-control part of $\mathcal T_1$ in
arXiv:1606.00608, Appendix C.2, lines 1523--1535. It does not include the
regrouping and shift maps surrounding $\mathcal T_1$ in the full construction. -/
theorem completedOmegaControlledMap_isKrausCPTP
    (data : ExplicitEtaOperators hη) (factor : RankOneTraceFactorization data) :
    IsKrausCPTP (data.completedOmegaControlledMap factor (α := α)) := by
  apply Matrix.controlledKrausMap_isKrausCPTP
  intro p
  exact Matrix.preparationKraus_resolution (data.completedOmega factor p.1 p.2)
    (data.completedOmega_pos factor p.1 p.2) (data.trace_completedOmega factor p.1 p.2)

end GlobalCompletion

end MPOTensor.ExplicitEtaOperators
