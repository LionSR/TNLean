/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Analysis.EntropyDecomposition
import TNLean.MPS.MPDO.CPSVExample412Literal

/-!
# The four-site entropy obstruction in CPSV16 Example 4.12

For the literal tensor of CPSV16 Example 4.12, the normalized four-site state is
the uniform distribution on the eight even-parity binary configurations.  We
regard the four sites as the tripartite system
\[
  A=\{0\},\qquad B=\{1,3\},\qquad C=\{2\}.
\]
The three proper marginals entering strong subadditivity are maximally mixed,
whereas the full state has only eight nonzero eigenvalues.  Consequently
\[
  S(ABC)=3\log 2,\quad S(B)=2\log 2,\quad
  S(AB)=S(BC)=3\log 2,
\]
and equality in strong subadditivity fails.

This finite entropy calculation supplies the state-specific obstruction needed
for the source claim that Example 4.12 is not of the simple commuting form.  The
separate implication from a four-cycle GSNNCH representation to the relevant
Markov equality is not asserted here.

## Reference

* Cirac--Perez-Garcia--Schuch--Verstraete, arXiv:1606.00608, Example 4.12,
  lines 932--938.
-/

open scoped Matrix BigOperators ComplexOrder

namespace MPOTensor.CPSVExample412Literal

/-- Decode the two-site subsystem $B=\{1,3\}$ from one four-dimensional
basis label.

Source state: CPSV16, arXiv:1606.00608, Example 4.12, lines 932--937. -/
def fourCycleMiddleBits (b : Fin 4) : Fin 2 × Fin 2 :=
  (finProdFinEquiv (m := 2) (n := 2)).symm b

/-- The real eigenvalue of $\sigma_z$ at a binary basis label.

Source: CPSV16, arXiv:1606.00608, Example 4.12, lines 935--937. -/
def siteSignReal (i : Fin 2) : ℝ :=
  if i = 0 then 1 else -1

@[simp] private lemma siteSignReal_zero : siteSignReal 0 = 1 := by
  simp [siteSignReal]

@[simp] private lemma siteSignReal_one : siteSignReal 1 = -1 := by
  simp [siteSignReal]

/-- The four-site basis regrouping for
$A=\{0\}$, $B=\{1,3\}$, and $C=\{2\}$.  The two binary labels in $B$ are
encoded as one element of `Fin 4`.

Source state: CPSV16, arXiv:1606.00608, Example 4.12, lines 932--937. -/
def fourCycleTripartiteEquiv :
    (Fin 2 × Fin 4 × Fin 2) ≃ (Fin 4 → Fin 2) where
  toFun x := ![x.1,
    (fourCycleMiddleBits x.2.1).1,
    x.2.2,
    (fourCycleMiddleBits x.2.1).2]
  invFun σ := (σ 0, finProdFinEquiv (m := 2) (n := 2) (σ 1, σ 3), σ 2)
  left_inv x := by
    obtain ⟨a, b, c⟩ := x
    ext <;> simp [fourCycleMiddleBits]
  right_inv σ := by
    funext i
    fin_cases i <;> simp [fourCycleMiddleBits]

/-- The normalized four-site Example 4.12 state in the tripartite basis
$A=\{0\}$, $B=\{1,3\}$, $C=\{2\}$.

Source state: CPSV16, arXiv:1606.00608, Example 4.12, equations at
lines 933--937. -/
noncomputable def fourCycleTripartiteState :
    Matrix (Fin 2 × Fin 4 × Fin 2) (Fin 2 × Fin 4 × Fin 2) ℂ :=
  (normalizedMPO M 4).submatrix fourCycleTripartiteEquiv fourCycleTripartiteEquiv

/-- The diagonal probability of a tripartite basis vector in the normalized
four-site state: $1/8$ for even parity and zero for odd parity.

Source formula: CPSV16, arXiv:1606.00608, Example 4.12, lines 933--937. -/
noncomputable def fourCycleWeight (x : Fin 2 × Fin 4 × Fin 2) : ℝ :=
  (1 + siteSignReal x.1 * siteSignReal (fourCycleMiddleBits x.2.1).1 *
    siteSignReal x.2.2 * siteSignReal (fourCycleMiddleBits x.2.1).2) / 16

private lemma siteSign_eq_siteSignReal (i : Fin 2) :
    MPOTensor.siteSign i = (siteSignReal i : ℂ) := by
  fin_cases i <;> simp [MPOTensor.siteSign, SpinCover.pauli]

private lemma configurationSign_fourCycle (x : Fin 2 × Fin 4 × Fin 2) :
    MPOTensor.configurationSign (fourCycleTripartiteEquiv x) =
      (siteSignReal x.1 * siteSignReal (fourCycleMiddleBits x.2.1).1 *
        siteSignReal x.2.2 * siteSignReal (fourCycleMiddleBits x.2.1).2 : ℝ) := by
  rw [MPOTensor.configurationSign, Fin.prod_univ_four]
  change MPOTensor.siteSign x.1 * MPOTensor.siteSign (fourCycleMiddleBits x.2.1).1 *
      MPOTensor.siteSign x.2.2 * MPOTensor.siteSign (fourCycleMiddleBits x.2.1).2 = _
  simp only [siteSign_eq_siteSignReal]
  push_cast
  ring

/-- The regrouped normalized four-site state is diagonal, with uniform weight
$1/8$ on the eight even-parity configurations.

Source formula: CPSV16, arXiv:1606.00608, Example 4.12, lines 933--937. -/
theorem fourCycleTripartiteState_eq_diagonal :
    fourCycleTripartiteState =
      Matrix.diagonal fun x => (fourCycleWeight x : ℂ) := by
  rw [fourCycleTripartiteState, normalizedMPO, trace_rho 4 (by omega), rho_eq_diagonal]
  ext x y
  by_cases hxy : x = y
  · subst y
    simp only [Matrix.submatrix_apply, Matrix.smul_apply, Matrix.diagonal_apply_eq,
      smul_eq_mul]
    rw [configurationSign_fourCycle]
    simp only [fourCycleWeight]
    push_cast
    norm_num
    ring
  · simp [Matrix.submatrix_apply, Matrix.diagonal_apply_ne _ hxy,
      Matrix.diagonal_apply_ne _ (fourCycleTripartiteEquiv.injective.ne hxy)]

/-- The regrouped four-site state is Hermitian.

Source state: CPSV16, arXiv:1606.00608, Example 4.12, lines 933--937. -/
theorem fourCycleTripartiteState_isHermitian :
    fourCycleTripartiteState.IsHermitian := by
  exact (normalizedMPO_isHermitian M 4 (M_isMPDO 4 (by omega))).submatrix
    fourCycleTripartiteEquiv

private lemma sum_fourCycleWeight_C (a : Fin 2) (b : Fin 4) :
    ∑ c : Fin 2, fourCycleWeight (a, b, c) = 1 / 8 := by
  rw [Fin.sum_univ_two]
  simp only [fourCycleWeight, siteSignReal_zero, siteSignReal_one]
  ring

private lemma sum_fourCycleWeight_A (b : Fin 4) (c : Fin 2) :
    ∑ a : Fin 2, fourCycleWeight (a, b, c) = 1 / 8 := by
  rw [Fin.sum_univ_two]
  simp only [fourCycleWeight, siteSignReal_zero, siteSignReal_one]
  ring

private lemma sum_fourCycleWeight_AC (b : Fin 4) :
    ∑ a : Fin 2, ∑ c : Fin 2, fourCycleWeight (a, b, c) = 1 / 4 := by
  simp_rw [sum_fourCycleWeight_C]
  rw [Fin.sum_univ_two]
  norm_num

/-- The $AB$ marginal of the four-site state is maximally mixed on eight
dimensions.

Derived from the state formula in CPSV16, arXiv:1606.00608,
Example 4.12, lines 933--937. -/
theorem traceC_fourCycleTripartiteState :
    Matrix.traceC_ABC fourCycleTripartiteState =
      (8 : ℂ)⁻¹ • (1 : Matrix (Fin 2 × Fin 4) (Fin 2 × Fin 4) ℂ) := by
  rw [fourCycleTripartiteState_eq_diagonal]
  ext x y
  by_cases hxy : x = y
  · subst y
    simp only [Matrix.traceC_ABC, Matrix.diagonal_apply_eq, Matrix.smul_apply,
      Matrix.one_apply_eq, smul_eq_mul, mul_one]
    obtain ⟨a, b⟩ := x
    norm_cast
    simpa using congrArg (fun r : ℝ => (r : ℂ)) (sum_fourCycleWeight_C a b)
  · have hneq : ∀ c : Fin 2, (x.1, x.2, c) ≠ (y.1, y.2, c) := by
      intro c h
      apply hxy
      exact congrArg (fun z : Fin 2 × Fin 4 × Fin 2 => (z.1, z.2.1)) h
    simp [Matrix.traceC_ABC, hxy, hneq]

/-- The $BC$ marginal of the four-site state is maximally mixed on eight
dimensions.

Derived from the state formula in CPSV16, arXiv:1606.00608,
Example 4.12, lines 933--937. -/
theorem traceA_fourCycleTripartiteState :
    Matrix.traceA_ABC fourCycleTripartiteState =
      (8 : ℂ)⁻¹ • (1 : Matrix (Fin 4 × Fin 2) (Fin 4 × Fin 2) ℂ) := by
  rw [fourCycleTripartiteState_eq_diagonal]
  ext x y
  by_cases hxy : x = y
  · subst y
    simp only [Matrix.traceA_ABC, Matrix.diagonal_apply_eq, Matrix.smul_apply,
      Matrix.one_apply_eq, smul_eq_mul, mul_one]
    obtain ⟨b, c⟩ := x
    norm_cast
    simpa using congrArg (fun r : ℝ => (r : ℂ)) (sum_fourCycleWeight_A b c)
  · have hneq : ∀ a : Fin 2, (a, x.1, x.2) ≠ (a, y.1, y.2) := by
      intro a h
      apply hxy
      exact congrArg (fun z : Fin 2 × Fin 4 × Fin 2 => z.2) h
    simp [Matrix.traceA_ABC, hxy, hneq]

/-- The $B$ marginal of the four-site state is maximally mixed on four
dimensions.

Derived from the state formula in CPSV16, arXiv:1606.00608,
Example 4.12, lines 933--937. -/
theorem traceAC_fourCycleTripartiteState :
    Matrix.traceAC_ABC fourCycleTripartiteState =
      (4 : ℂ)⁻¹ • (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
  rw [fourCycleTripartiteState_eq_diagonal]
  ext x y
  by_cases hxy : x = y
  · subst y
    simp only [Matrix.traceAC_ABC, Matrix.diagonal_apply_eq, Matrix.smul_apply,
      Matrix.one_apply_eq, smul_eq_mul, mul_one]
    norm_cast
    simpa using congrArg (fun r : ℝ => (r : ℂ)) (sum_fourCycleWeight_AC x)
  · have hneq : ∀ a c : Fin 2, (a, x, c) ≠ (a, y, c) := by
      intro a c h
      apply hxy
      exact congrArg (fun z : Fin 2 × Fin 4 × Fin 2 => z.2.1) h
    simp [Matrix.traceAC_ABC, hxy, hneq]

/-- A maximally mixed state on a finite basis of cardinality $d$ has entropy
$\log d$.

Source: Wolf, *Quantum Channels & Operations*, Section 8.2. -/
private theorem vonNeumannEntropy_inv_card_smul_one
    {n : Type*} [Fintype n] [DecidableEq n] (d : ℕ)
    (hcard : Fintype.card n = d) (hd : 0 < d)
    (hρ : (((d : ℂ)⁻¹) • (1 : Matrix n n ℂ)).IsHermitian) :
    vonNeumannEntropy (((d : ℂ)⁻¹) • (1 : Matrix n n ℂ)) hρ =
      Real.log d := by
  have heq : ((d : ℂ)⁻¹) • (1 : Matrix n n ℂ) =
      Matrix.diagonal (fun _ : n => (((d : ℝ)⁻¹ : ℝ) : ℂ)) := by
    rw [Matrix.smul_one_eq_diagonal]
    ext i j
    simp
  let hdiag : (Matrix.diagonal fun _ : n => (((d : ℝ)⁻¹ : ℝ) : ℂ)).IsHermitian :=
    Matrix.isHermitian_diagonal_of_self_adjoint _ (by
      rw [isSelfAdjoint_iff]
      ext i
      simp)
  rw [vonNeumannEntropy_congr heq hρ hdiag, Matrix.vonNeumannEntropy_diagonal]
  rw [Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul]
  simp [Real.negMulLog, hd.ne', Real.log_inv]

/-- The entropy of the normalized four-site Example 4.12 state is
$3\log 2$.

Derived from the state formula in CPSV16, arXiv:1606.00608,
Example 4.12, lines 933--937. -/
theorem fourCycleTripartiteState_entropy :
    vonNeumannEntropy fourCycleTripartiteState
      fourCycleTripartiteState_isHermitian = 3 * Real.log 2 := by
  let hd : (Matrix.diagonal fun x : Fin 2 × Fin 4 × Fin 2 =>
      (fourCycleWeight x : ℂ)).IsHermitian :=
    Matrix.isHermitian_diagonal_of_self_adjoint _ (by
      rw [isSelfAdjoint_iff]
      ext x
      simp [Complex.conj_ofReal])
  rw [vonNeumannEntropy_congr fourCycleTripartiteState_eq_diagonal
    fourCycleTripartiteState_isHermitian hd, Matrix.vonNeumannEntropy_diagonal]
  rw [Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type]
  simp_rw [← Equiv.sum_comp (finProdFinEquiv : Fin 2 × Fin 2 ≃ Fin 4)]
  simp_rw [Fintype.sum_prod_type]
  rw [Fin.sum_univ_two]
  simp_rw [Fin.sum_univ_two]
  norm_num [fourCycleWeight, fourCycleMiddleBits, siteSignReal,
    Real.negMulLog_zero]
  rw [Real.negMulLog]
  rw [show (1 / 8 : ℝ) = (8 : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
  norm_num
  ring

/-- The entropy of the $AB$ marginal is $3\log 2$.

Derived from the state formula in CPSV16, arXiv:1606.00608,
Example 4.12, lines 933--937. -/
theorem traceC_fourCycleTripartiteState_entropy :
    vonNeumannEntropy (Matrix.traceC_ABC fourCycleTripartiteState)
      (Matrix.traceC_ABC_isHermitian fourCycleTripartiteState_isHermitian) =
        3 * Real.log 2 := by
  let hscaled : (((8 : ℂ)⁻¹) •
      (1 : Matrix (Fin 2 × Fin 4) (Fin 2 × Fin 4) ℂ)).IsHermitian :=
    (Matrix.isHermitian_one (n := Fin 2 × Fin 4) (α := ℂ)).smul (by
      simp [IsSelfAdjoint])
  calc
    _ = vonNeumannEntropy
        (((8 : ℂ)⁻¹) • (1 : Matrix (Fin 2 × Fin 4) (Fin 2 × Fin 4) ℂ))
        hscaled := vonNeumannEntropy_congr traceC_fourCycleTripartiteState _ _
    _ = Real.log 8 := vonNeumannEntropy_inv_card_smul_one 8 (by simp) (by omega) hscaled
    _ = 3 * Real.log 2 := by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
      norm_num

/-- The entropy of the $BC$ marginal is $3\log 2$.

Derived from the state formula in CPSV16, arXiv:1606.00608,
Example 4.12, lines 933--937. -/
theorem traceA_fourCycleTripartiteState_entropy :
    vonNeumannEntropy (Matrix.traceA_ABC fourCycleTripartiteState)
      (Matrix.traceA_ABC_isHermitian fourCycleTripartiteState_isHermitian) =
        3 * Real.log 2 := by
  let hscaled : (((8 : ℂ)⁻¹) •
      (1 : Matrix (Fin 4 × Fin 2) (Fin 4 × Fin 2) ℂ)).IsHermitian :=
    (Matrix.isHermitian_one (n := Fin 4 × Fin 2) (α := ℂ)).smul (by
      simp [IsSelfAdjoint])
  calc
    _ = vonNeumannEntropy
        (((8 : ℂ)⁻¹) • (1 : Matrix (Fin 4 × Fin 2) (Fin 4 × Fin 2) ℂ))
        hscaled := vonNeumannEntropy_congr traceA_fourCycleTripartiteState _ _
    _ = Real.log 8 := vonNeumannEntropy_inv_card_smul_one 8 (by simp) (by omega) hscaled
    _ = 3 * Real.log 2 := by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
      norm_num

/-- The entropy of the $B$ marginal is $2\log 2$.

Derived from the state formula in CPSV16, arXiv:1606.00608,
Example 4.12, lines 933--937. -/
theorem traceAC_fourCycleTripartiteState_entropy :
    vonNeumannEntropy (Matrix.traceAC_ABC fourCycleTripartiteState)
      (Matrix.traceAC_ABC_isHermitian fourCycleTripartiteState_isHermitian) =
        2 * Real.log 2 := by
  let hscaled : (((4 : ℂ)⁻¹) • (1 : Matrix (Fin 4) (Fin 4) ℂ)).IsHermitian :=
    (Matrix.isHermitian_one (n := Fin 4) (α := ℂ)).smul (by
      simp [IsSelfAdjoint])
  calc
    _ = vonNeumannEntropy (((4 : ℂ)⁻¹) • (1 : Matrix (Fin 4) (Fin 4) ℂ))
        hscaled := vonNeumannEntropy_congr traceAC_fourCycleTripartiteState _ _
    _ = Real.log 4 := vonNeumannEntropy_inv_card_smul_one 4 (by simp) (by omega) hscaled
    _ = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      norm_num

/-- The four-site Example 4.12 state fails equality in strong subadditivity
for $A=\{0\}$, $B=\{1,3\}$, and $C=\{2\}$.

This is the finite entropy obstruction behind the source statement that the
state is not of the simple commuting form.  The GSNNCH-to-Markov implication is
a separate assertion.

Derived from the state formula in CPSV16, arXiv:1606.00608,
Example 4.12, lines 933--937. -/
theorem fourCycleTripartiteState_not_isSSAEquality :
    ¬ IsSSAEquality fourCycleTripartiteState
      fourCycleTripartiteState_isHermitian := by
  rw [IsSSAEquality, fourCycleTripartiteState_entropy,
    traceAC_fourCycleTripartiteState_entropy,
    traceC_fourCycleTripartiteState_entropy,
    traceA_fourCycleTripartiteState_entropy]
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  linarith

end MPOTensor.CPSVExample412Literal
