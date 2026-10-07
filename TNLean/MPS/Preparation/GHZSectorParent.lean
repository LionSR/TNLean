/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Circuit.WeightedGHZ
import TNLean.MPS.Preparation.GHZSectorObstruction
import TNLean.MPS.Examples.GHZ
import TNLean.MPS.ParentHamiltonian.ChainGroundSpace
import TNLean.MPS.ParentHamiltonian.Defs
import TNLean.MPS.Preparation.RepeatedBlockCounterexample

/-!
# Different periodic sector weights with identical parent constraints

The repeated-block tensor `A⁰ = diag(1, 1, 0)`, `A¹ = diag(0, 0, 1)` generates
`2|0ᴺ⟩ + |1ᴺ⟩`, whereas the GHZ tensor `B⁰ = diag(1, 0)`, `B¹ = diag(0, 1)`
generates `|0ᴺ⟩ + |1ᴺ⟩`. Their normalized positive-length states are therefore the
weighted GHZ vectors with coefficients `(2, 1)/√5` and `(1, 1)/√2`.

The coefficient two is the trace multiplicity of two identical virtual blocks,
whose scalar weights are all one. It is independent of chain length. Scaling a
single virtual block by a fixed scalar `μ` would instead contribute `μ^N`.
The source-family membership of the repeated-block example is proved by
`isBNTCanonicalForm_repeatedBlockSector` and `reindex_toTensor_repeatedBlockSector`.

Despite the distinct periodic weights, the two tensors have identical local
MPS spaces at every length: the diagonal boundary entries on the repeated
sector are added. Consequently their canonical parent interactions and periodic
chain constraints agree. This is equality of parent spaces and Hamiltonians,
not equality of periodic vectors.

## References

* Malz--Styliaris--Wei--Cirac, arXiv:2307.01696, Supplemental Material,
  eqs. (S2)--(S4), for multiplicities and periodic sector coefficients.
* Cirac--Pérez-García--Schuch--Verstraete, arXiv:2011.12127,
  Appendix A, for the GHZ tensor; Section IV.C, for parent spaces.
-/

open Matrix QuantumCircuit
open scoped BigOperators InnerProductSpace

namespace MPSTensor

private lemma repeatedBlockDiag_eq_single (i : Fin 2) (j : Fin 3) :
    repeatedBlockDiag i j = (Pi.single (if j = 2 then 1 else 0) 1 : Fin 2 → ℂ) i := by
  fin_cases i <;> fin_cases j <;> simp [repeatedBlockDiag]

/-- A boundary matrix on the repeated tensor contributes the sum of the two
boundary entries of the repeated sector and the entry of the other sector. -/
theorem groundSpaceMap_repeatedBlockTensor_eq_ghzState (N : ℕ)
    (X : Matrix (Fin 3) (Fin 3) ℂ) :
    groundSpaceMap repeatedBlockTensor N X =
      ghzState (M := N) ![X 0 0 + X 1 1, X 2 2] := by
  ext σ
  rw [groundSpaceMap_apply, evalWord_diagonal]
  simp only [Matrix.trace, List.map_ofFn, List.prod_ofFn,
    Fin.sum_univ_three, Function.comp_def, repeatedBlockDiag_eq_single,
    ghzState, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  norm_num
  ring

/-- The ordinary GHZ tensor retains the two diagonal boundary entries as its
physical sector coefficients. -/
theorem groundSpaceMap_ghzTensor_eq_ghzState (N : ℕ)
    (X : Matrix (Fin 2) (Fin 2) ℂ) :
    groundSpaceMap ghzTensor N X = ghzState (M := N) ![X 0 0, X 1 1] := by
  ext σ
  rw [groundSpaceMap_apply]
  change Matrix.trace (Kraus.evalWord (fun i => Matrix.diagonal (Pi.single i 1))
    (List.ofFn σ) * X) = _
  rw [evalWord_diagonal]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.diagonal_mul, List.map_ofFn, List.prod_ofFn,
    Fin.sum_univ_two, Function.comp_def, ghzState, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one]
  simp only [Pi.single_apply]
  simp only [eq_comm (a := (0 : Fin 2)), eq_comm (a := (1 : Fin 2))]
  ring

/-- Periodic trace multiplicity gives constant sector amplitudes `(2, 1)` at
every length; the empty word has amplitude three. -/
theorem mpv_repeatedBlockTensor_eq_ghzState (N : ℕ) :
    (mpv repeatedBlockTensor : NSiteSpace 2 N) = ghzState (M := N) ![2, 1] := by
  rw [mpv_eq_groundSpaceMap_one, groundSpaceMap_repeatedBlockTensor_eq_ghzState]
  norm_num

/-- The periodic GHZ tensor gives the equal-weight GHZ vector; the empty word
has amplitude two. -/
theorem mpv_ghzTensor_eq_ghzState (N : ℕ) :
    (mpv ghzTensor : NSiteSpace 2 N) = ghzState (M := N) ![1, 1] := by
  rw [mpv_eq_groundSpaceMap_one, groundSpaceMap_ghzTensor_eq_ghzState]
  norm_num

/-- The norm of the multiplicity-weighted periodic vector is `√5` on nonempty chains. -/
theorem norm_mpvState_repeatedBlockTensor {N : ℕ} [NeZero N] :
    ‖mpvState repeatedBlockTensor N‖ = Real.sqrt 5 := by
  have h : ‖mpvState repeatedBlockTensor N‖ ^ 2 = 5 := by
    change ‖(WithLp.toLp 2 (mpv repeatedBlockTensor) : MPVSpace 2 N)‖ ^ 2 = _
    rw [mpv_repeatedBlockTensor_eq_ghzState, norm_ghzState_two_sq]
    norm_num
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num),
    Real.sqrt_nonneg 5, norm_nonneg (mpvState repeatedBlockTensor N)]

/-- The norm of the balanced periodic vector is `√2` on nonempty chains. -/
theorem norm_mpvState_ghzTensor {N : ℕ} [NeZero N] :
    ‖mpvState ghzTensor N‖ = Real.sqrt 2 := by
  have h : ‖mpvState ghzTensor N‖ ^ 2 = 2 := by
    change ‖(WithLp.toLp 2 (mpv ghzTensor) : MPVSpace 2 N)‖ ^ 2 = _
    rw [mpv_ghzTensor_eq_ghzState, norm_ghzState_two_sq]
    norm_num
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num),
    Real.sqrt_nonneg 2, norm_nonneg (mpvState ghzTensor N)]

/-- The actual normalized periodic state of the repeated-block source is
`(2|0ᴺ⟩ + |1ᴺ⟩)/√5`, with no length-dependent reweighting. -/
theorem normalizedMPVState_repeatedBlockTensor {N : ℕ} [NeZero N] :
    normalizedMPVState repeatedBlockTensor N =
      WithLp.toLp 2 (ghzState (M := N)
        ![2 / (Real.sqrt 5 : ℂ), 1 / (Real.sqrt 5 : ℂ)]) := by
  rw [normalizedMPVState, norm_mpvState_repeatedBlockTensor]
  apply PiLp.ext
  intro σ
  change ((Real.sqrt 5 : ℂ)⁻¹ • (mpv repeatedBlockTensor : NSiteSpace 2 N)) σ = _
  rw [mpv_repeatedBlockTensor_eq_ghzState, ghzState_smul_two]
  simp [div_eq_mul_inv, mul_comm]

/-- The normalized periodic GHZ state is `( |0ᴺ⟩ + |1ᴺ⟩ )/√2`. -/
theorem normalizedMPVState_ghzTensor {N : ℕ} [NeZero N] :
    normalizedMPVState ghzTensor N =
      WithLp.toLp 2 (ghzState (M := N)
        ![1 / (Real.sqrt 2 : ℂ), 1 / (Real.sqrt 2 : ℂ)]) := by
  rw [normalizedMPVState, norm_mpvState_ghzTensor]
  apply PiLp.ext
  intro σ
  change ((Real.sqrt 2 : ℂ)⁻¹ • (mpv ghzTensor : NSiteSpace 2 N)) σ = _
  rw [mpv_ghzTensor_eq_ghzState, ghzState_smul_two]
  simp [div_eq_mul_inv]

/-- Repeating a virtual GHZ sector changes its periodic trace coefficient but
leaves the entire local boundary-generated space unchanged. -/
theorem groundSpace_repeatedBlockTensor_eq_ghzTensor (L : ℕ) :
    groundSpace repeatedBlockTensor L = groundSpace ghzTensor L := by
  apply le_antisymm
  · rintro ψ ⟨X, rfl⟩
    refine ⟨Matrix.diagonal ![X 0 0 + X 1 1, X 2 2], ?_⟩
    rw [groundSpaceMap_ghzTensor_eq_ghzState, groundSpaceMap_repeatedBlockTensor_eq_ghzState]
    simp
  · rintro ψ ⟨X, rfl⟩
    refine ⟨Matrix.diagonal ![X 0 0, 0, X 1 1], ?_⟩
    rw [groundSpaceMap_repeatedBlockTensor_eq_ghzState, groundSpaceMap_ghzTensor_eq_ghzState]
    simp

/-- The canonical local parent projector is insensitive to the two sector
multiplicities. In particular the two-site parent interactions coincide. -/
theorem parentInteraction_repeatedBlockTensor_eq_ghzTensor (L : ℕ) :
    parentInteraction repeatedBlockTensor L = parentInteraction ghzTensor L := by
  simp [parentInteraction, groundSpaceES, groundSpace_repeatedBlockTensor_eq_ghzTensor]

/-- The periodic chains impose identical parent constraints at every interaction
range and system size, including the common degenerate-size conventions. -/
theorem chainGroundSpace_repeatedBlockTensor_eq_ghzTensor (L N : ℕ) :
    chainGroundSpace repeatedBlockTensor L N = chainGroundSpace ghzTensor L N :=
  chainGroundSpace_eq_of_groundSpace_eq (groundSpace_repeatedBlockTensor_eq_ghzTensor L)

/-- The finite-chain canonical parent Hamiltonians coincide although their
periodic MPS vectors carry different sector probabilities. -/
theorem parentHamiltonian_repeatedBlockTensor_eq_ghzTensor (L N : ℕ) :
    parentHamiltonian repeatedBlockTensor L N = parentHamiltonian ghzTensor L N := by
  simp [parentHamiltonian, localTerm, parentInteraction_repeatedBlockTensor_eq_ghzTensor]

/-- The actual normalized periodic vectors of two tensors with identical parent
Hamiltonians require a linear circuit depth for sufficiently accurate conversion. -/
theorem repeatedBlockTensor_infidelity_lower_bound {N T : ℕ} [NeZero N]
    {U : Matrix (Fin N → Fin 2) (Fin N → Fin 2) ℂ}
    (hU : IsLocalCircuitOfDepth U T) (hN : 4 * T + 4 < N) :
    (9 : ℝ) / 5000 ≤ 1 - ‖⟪Matrix.toEuclideanLin U
      (normalizedMPVState repeatedBlockTensor N), normalizedMPVState ghzTensor N⟫_ℂ‖ := by
  rw [normalizedMPVState_repeatedBlockTensor, normalizedMPVState_ghzTensor]
  simpa only [Matrix.toLpLin_apply, Complex.invSqrtTwo, one_div] using
    MPSPreparation.ghz_sector_weight_infidelity_lower_bound hU hN

/-- Overlap error below `9/5000` between the multiplicity-weighted and balanced
periodic states forces the ring length to be at most `4T+4`. -/
theorem length_le_of_repeatedBlockTensor_infidelity_lt {N T : ℕ} [NeZero N]
    {U : Matrix (Fin N → Fin 2) (Fin N → Fin 2) ℂ}
    (hU : IsLocalCircuitOfDepth U T)
    (herr : 1 - ‖⟪Matrix.toEuclideanLin U (normalizedMPVState repeatedBlockTensor N),
      normalizedMPVState ghzTensor N⟫_ℂ‖ < (9 : ℝ) / 5000) : N ≤ 4 * T + 4 := by
  by_contra hN
  exact (not_lt_of_ge (repeatedBlockTensor_infidelity_lower_bound hU (by omega))) herr

end MPSTensor
