/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.MPDO.KrausCPTP
import TNLean.MPS.MPDO.SimpleLocalStructure

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
pairs. The orthogonal direct sum of these maps, including a trace-preserving
completion on unused zero-weight input summands, is a separate construction.
-/

open scoped Matrix BigOperators ComplexOrder

namespace MPOTensor.ExplicitEtaOperators

variable {dA dB dC : ℕ}
variable {rhoABC : Matrix (Fin dA × Fin dB × Fin dC)
  (Fin dA × Fin dB × Fin dC) ℂ}
variable {hη : EtaStructure rhoABC}

/-- The rank-one trace factorization of the neighboring operators:
$\operatorname{tr}(\eta_{k,h})=a_kb_h$ and $\sum_l a_lb_l=1$.

These are equations Apptralktrrk and AppPsiPhi in arXiv:1606.00608,
Appendix C.2, lines 1395--1402. -/
structure RankOneTraceFactorization (data : ExplicitEtaOperators hη) where
  a : Fin hη.m → ℝ
  b : Fin hη.m → ℝ
  trace_eta : ∀ k h, (data.eta k h).trace = ((a k * b h : ℝ) : ℂ)
  sum_mul : ∑ l, a l * b l = 1

/-- The index space of
$\Omega_{k,h}=\bigoplus_l(\eta_{k,l}\otimes\eta_{l,h})$.
The outer sigma coordinate records the intermediate sector $l$. -/
abbrev OmegaIndex (k h : Fin hη.m) :=
  Σ l : Fin hη.m,
    (Fin (hη.dR k) × Fin (hη.dL l)) ×
      (Fin (hη.dR l) × Fin (hη.dL h))

/-- The direct sum
$\Omega_{k,h}=\bigoplus_l(\eta_{k,l}\otimes\eta_{l,h})$ used by
$\mathcal T_1$ in arXiv:1606.00608, Appendix C.2, lines 1527--1535. -/
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

Source: arXiv:1606.00608, Appendix C.2, equations Apptralktrrk and
AppPsiPhi at lines 1395--1402, and lines 1531--1535. -/
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
theorem mul_nonneg (data : ExplicitEtaOperators hη)
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
  exact_mod_cast inv_nonneg.mpr (data.mul_nonneg factor k h)

/-- On an active pair, the normalized neighboring operator has trace one.

Source: arXiv:1606.00608, Appendix C.2, lines 1551--1555. -/
theorem trace_normalizedEta (data : ExplicitEtaOperators hη)
    (factor : RankOneTraceFactorization data) (k h : Fin hη.m)
    (hactive : factor.a k * factor.b h ≠ 0) :
    (data.normalizedEta factor k h).trace = 1 := by
  rcases mul_ne_zero_iff.mp hactive with ⟨ha, hb⟩
  have haC : (factor.a k : ℂ) ≠ 0 := by exact_mod_cast ha
  have hbC : (factor.b h : ℂ) ≠ 0 := by exact_mod_cast hb
  simp only [normalizedEta, Matrix.trace_smul, factor.trace_eta, smul_eq_mul]
  norm_cast
  field_simp

/-- The normalized direct-sum operator is positive semidefinite. On a zero
pair it is the zero operator; the trace-one statement below is restricted to
active pairs.

Source: arXiv:1606.00608, Appendix C.2, lines 1527--1535. -/
theorem normalizedOmega_pos (data : ExplicitEtaOperators hη)
    (factor : RankOneTraceFactorization data) (k h : Fin hη.m) :
    (data.normalizedOmega factor k h).PosSemidef := by
  apply (data.omega_pos k h).smul
  exact_mod_cast inv_nonneg.mpr (data.mul_nonneg factor k h)

/-- On an active pair, the normalized direct-sum operator has trace one.

Source: arXiv:1606.00608, Appendix C.2, lines 1527--1535. -/
theorem trace_normalizedOmega (data : ExplicitEtaOperators hη)
    (factor : RankOneTraceFactorization data) (k h : Fin hη.m)
    (hactive : factor.a k * factor.b h ≠ 0) :
    (data.normalizedOmega factor k h).trace = 1 := by
  rcases mul_ne_zero_iff.mp hactive with ⟨ha, hb⟩
  have haC : (factor.a k : ℂ) ≠ 0 := by exact_mod_cast ha
  have hbC : (factor.b h : ℂ) ≠ 0 := by exact_mod_cast hb
  simp only [normalizedOmega, Matrix.trace_smul,
    data.trace_omega_eq_mul factor k h, smul_eq_mul]
  norm_cast
  field_simp

/-- On an active pair, adjoining the normalized neighboring operator is a
trace-preserving completely positive map. This is the individual
$\mathcal S_{k,h}$ preparation from arXiv:1606.00608, Appendix C.2,
lines 1551--1555. -/
theorem normalizedEta_preparationMap_isKrausCPTP
    {α : Type*} [Fintype α] [DecidableEq α]
    (data : ExplicitEtaOperators hη) (factor : RankOneTraceFactorization data)
    (k h : Fin hη.m) (hactive : factor.a k * factor.b h ≠ 0) :
    IsKrausCPTP (Matrix.preparationMap (α := α)
      (data.normalizedEta factor k h)) := by
  exact Matrix.preparationMap_isKrausCPTP _
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
      (data.normalizedOmega factor k h)) := by
  exact Matrix.preparationMap_isKrausCPTP _
    (data.normalizedOmega_pos factor k h) (data.trace_normalizedOmega factor k h hactive)

end MPOTensor.ExplicitEtaOperators
