/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.TwistedDimerUnitaryFactorization
import TNLean.MPS.MPDO.CPSVExample412NormalizedRFP

/-!
# The density factors of the twisted dimer

The flag factor of the explicit bond–flag factorization is exactly the
normalized tensor of CPSV16 Example 4.12, at every length, including zero.
The mixed Bell bond state has trace one. Hence the decorated state and the
closed twisted-dimer operator both have trace one at every positive length.
The explicit operator factorization and its scope are recorded in
`docs/audits/2026-09-05_twisted_dimer_unitary_factorization.md`.

**Local fix (normalization):** CPSV16, arXiv:1606.00608, Example 4.12,
lines 932--939, prints a tensor without the factor one half. The flag factor
here is the corrected density-normalized representative, not the printed
unnormalized tensor; see
<https://sirui-lu.com/QICLean/paper-gaps/cpsv16_example_4_12_normalization.pdf>.
Its existing channel fixed-point theorem is used without changing that scale.
No strict on-site tensor or virtual-gauge equivalence is asserted. Nor is the
flag tensor claimed to have literally length-independent coefficients in a
spectrally normalized vertical basis; see
<https://sirui-lu.com/QICLean/paper-gaps/cpsv16_unit_weight_rfp_scale_tension.pdf>.
-/

open scoped BigOperators Matrix Kronecker ComplexOrder

noncomputable section

namespace MPOTensor.TwistedDimer

/-- The zero-label flag matrix is the identity. -/
lemma flagMatrix_zero : flagMatrix 0 = 1 := by
  ext f g
  simp [flagMatrix, tau_zero, Matrix.diagonal_apply, Matrix.one_apply]

/-- The one-label flag matrix is the Pauli Z matrix used in CPSV16 Example 4.12. -/
lemma flagMatrix_one : flagMatrix 1 = CPSVExample412Literal.sigmaZ := by
  ext f g
  fin_cases f <;> fin_cases g <;>
    norm_num [flagMatrix, tau, CPSVExample412Literal.sigmaZ, SpinCover.pauli,
      Matrix.diagonal_apply]

/-- The flag factor agrees with the density-normalized tensor of CPSV16
Example 4.12 at every length. At length zero both operators have the single
entry two, so this identity does not require a positivity-of-length hypothesis. -/
theorem evenFlagState_eq_mpo_Mhat (N : ℕ) :
    evenFlagState N = mpo CPSVExample412NormalizedRFP.Mhat N := by
  rw [CPSVExample412NormalizedRFP.mpo_Mhat]
  cases N with
  | zero =>
      rw [CPSVExample412Literal.rho_eq_diagonal]
      ext s t
      have h : s = t := Subsingleton.elim _ _
      subst t
      simp [evenFlagState, powN, configurationSign]
  | succ N =>
      rw [CPSVExample412Literal.rho_eq_finKronecker (N + 1) (by omega)]
      ext s t
      norm_num [evenFlagState, flagMatrix_zero, flagMatrix_one, powN, Matrix.finKronecker]

/-- The flag family has a density-operator tensor satisfying both channel
fixed-point equations, namely the already normalized CPSV16 Example 4.12 tensor. -/
theorem evenFlagState_has_rfpRepresentation :
    ∃ A : MPOTensor 2 2, IsMPDO A ∧ IsRFPViaTS A ∧
      ∀ N, evenFlagState N = mpo A N :=
  ⟨CPSVExample412NormalizedRFP.Mhat,
    CPSVExample412NormalizedRFP.Mhat_isMPDO,
    CPSVExample412NormalizedRFP.Mhat_isRFPViaTS, evenFlagState_eq_mpo_Mhat⟩

/-- At positive length the flag factor is positive semidefinite. -/
theorem evenFlagState_posSemidef {N : ℕ} (hN : 0 < N) :
    (evenFlagState N).PosSemidef := by
  rw [evenFlagState_eq_mpo_Mhat]
  exact CPSVExample412NormalizedRFP.Mhat_isMPDO N hN

/-- At positive length the flag factor is normalized. -/
theorem trace_evenFlagState {N : ℕ} (hN : 0 < N) : (evenFlagState N).trace = 1 := by
  rw [evenFlagState_eq_mpo_Mhat]
  exact CPSVExample412NormalizedRFP.trace_mpo_Mhat N hN

/-- Each rational Bell projector is positive semidefinite. -/
lemma bellProjector_posSemidef (ε : Fin 2) : (bellProjector ε).PosSemidef := by
  let v : Bond → ℂ := fun a => if a.1 = a.2 then (tau ε a.2 : ℂ) else 0
  have h : bellProjector ε = (1 / 2 : ℂ) • Matrix.vecMulVec v (star v) := by
    ext a b
    by_cases ha : a.1 = a.2 <;> by_cases hb : b.1 = b.2 <;>
      simp [bellProjector, v, Matrix.vecMulVec, ha, hb, mul_assoc]
  rw [h]
  exact (Matrix.posSemidef_vecMulVec_self_star v).smul (by positivity)

/-- The bond factor is a positive mixture of the two normalized Bell projectors. -/
theorem sigma_posSemidef : sigma.PosSemidef := by
  unfold sigma bondState
  exact ((bellProjector_posSemidef 0).smul (by dsimp [x]; positivity)).add
    ((bellProjector_posSemidef 1).smul (by simp only [tau_zero]; dsimp [y]; positivity))

/-- The Bell mixture has trace one. -/
theorem trace_sigma : sigma.trace = 1 := by
  norm_num [Matrix.trace, sigma, bondState_apply, Fintype.sum_prod_type,
    Fin.sum_univ_two, Cmat, cDiag_eq, cOff_eq]

/-- Every finite product of the normalized bond state has trace one. -/
lemma trace_powN_sigma (N : ℕ) : (powN sigma N).trace = 1 := by
  calc
    (powN sigma N).trace = ∏ _ : Fin N, sigma.trace :=
      (Fintype.prod_sum fun _ : Fin N => fun a : Bond => sigma a a).symm
    _ = 1 := by simp [trace_sigma]

/-- The independent bond states and the even-parity flag state give a
positive semidefinite operator in the original site coordinates. -/
theorem decoratedState_posSemidef {N : ℕ} (hN : 0 < N) :
    (decoratedState N).PosSemidef := by
  exact ((Matrix.finKronecker_posSemidef (fun _ : Fin N => sigma)
    (fun _ => sigma_posSemidef)).kronecker (evenFlagState_posSemidef hN)).submatrix
      ((incomingCellEquiv N).trans (bondFlagEquiv N))

/-- Regrouping the independent normalized factors preserves trace one. -/
theorem trace_decoratedState {N : ℕ} (hN : 0 < N) :
    (decoratedState N).trace = 1 := by
  calc
    (decoratedState N).trace = (powN sigma N ⊗ₖ evenFlagState N).trace :=
      ((incomingCellEquiv N).trans (bondFlagEquiv N)).sum_comp
        (fun a => (powN sigma N ⊗ₖ evenFlagState N) a a)
    _ = 1 := by rw [Matrix.trace_kronecker, trace_powN_sigma, trace_evenFlagState hN, mul_one]

/-- The periodic twisted-dimer operator is normalized at every positive
length, by its explicit unitary conjugation of the normalized factor states. -/
theorem trace_mpo_T {N : ℕ} (hN : 0 < N) : (mpo T N).trace = 1 := by
  rw [mpo_eq_unitary_factorization hN, Matrix.trace_mul_cycle,
    chainUnitary_conjTranspose_mul, one_mul, trace_decoratedState hN]

end MPOTensor.TwistedDimer
