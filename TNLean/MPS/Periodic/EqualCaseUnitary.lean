/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Periodic.UnitaryBlockMatching
import TNLean.MPS.FundamentalTheorem.UnitaryGauge
import TNLean.MPS.FundamentalTheorem.SectorBNT.UnblockedPowerSumCoefficients

/-!
# Unitary gauges preserving the periodic matching phase

Canonical periodic blocks admit unitary matching gauges. The scalar phase
is kept unchanged, so the same phase remains available in the equal-case
copy-weight identity. This is required in arXiv:1708.00029, Theorem 4.1,
lines 752--765, and follows from CPSV16, Corollary A.6.
-/

open scoped Matrix

namespace MPSTensor

/-- A scalar gauge between trace-preserving periodic blocks can be made
unitary without changing its scalar. Source: arXiv:1708.00029, Theorem 4.1,
lines 752--765; arXiv:1606.00608, Corollary A.6. -/
theorem ScalarGaugeEquiv.exists_unitary_of_isPeriodic
    {d D₁ D₂ m n : ℕ} {A : MPSTensor d D₁} {B : MPSTensor d D₂}
    {ζ : ℂ} (h : ScalarGaugeEquiv ζ A B) (hζ : ζ ≠ 0)
    (hA : IsPeriodic m A) (hB : IsPeriodic n B) :
    ∃ (hd : D₁ = D₂) (U : Matrix.unitaryGroup (Fin D₂) ℂ),
      ‖ζ‖ = 1 ∧ ∀ i,
        (cast (congrArg (MPSTensor d) hd) A) i =
          ζ • ((U : Matrix (Fin D₂) (Fin D₂) ℂ) * B i *
            (U : Matrix (Fin D₂) (Fin D₂) ℂ)ᴴ) := by
  obtain ⟨hd, X, hX⟩ := h
  subst D₁
  let : NeZero D₂ := ⟨hB.bondDim_ne_zero⟩
  obtain ⟨U, hnorm, hU⟩ :=
    exists_unitaryConj_of_gaugePhase_data_of_leftCanonical_irreducible
      X ζ hζ hX hB.leftCanonical hA.leftCanonical hB.irreducible hA.irreducible
  exact ⟨rfl, U, hnorm, hU⟩

/-- Periodic blocks in one MPV phase class admit a unitary gauge and a
unit-modulus scalar. The scalar here is chosen with the gauge; it is not
asserted to equal a specified witness of MPV phase equivalence.
Source: arXiv:1708.00029, Proposition `equal-or-orthogonal-generalized`
and Theorem 4.1, lines 752--765. -/
theorem MPVBlockPhaseEquiv.exists_unitary_of_isPeriodic
    {d D₁ D₂ m n : ℕ} {A : MPSTensor d D₁} {B : MPSTensor d D₂}
    (h : MPVBlockPhaseEquiv A B) (hA : IsPeriodic m A) (hB : IsPeriodic n B) :
    ∃ (hd : D₁ = D₂) (ζ : ℂ) (U : Matrix.unitaryGroup (Fin D₂) ℂ),
      ‖ζ‖ = 1 ∧ ∀ i,
        (cast (congrArg (MPSTensor d) hd) A) i =
          ζ • ((U : Matrix (Fin D₂) (Fin D₂) ℂ) * B i *
            (U : Matrix (Fin D₂) (Fin D₂) ℂ)ᴴ) := by
  obtain ⟨hd, ζ, X, hζ, hX⟩ :=
    hetRepeatedBlocks_of_mpvBlockPhaseEquiv_of_isPeriodic hA hB h
  have hGauge : ScalarGaugeEquiv ζ A B := ⟨hd, X, hX⟩
  obtain ⟨hd', U, hnorm, hU⟩ := hGauge.exists_unitary_of_isPeriodic
    (Complex.ne_zero_of_norm_eq_one hζ) hA hB
  exact ⟨hd', ζ, U, hnorm, hU⟩

/-- Periodic equal-case matching admits unitary basis gauges while retaining
exactly the phases in the multiplicity identity. Source: arXiv:1708.00029,
Theorem 3.8 and Theorem 4.1, lines 643--690 and 752--765. -/
theorem fundamentalTheorem_periodic_equalCase_unitary_matching
    {d : ℕ} (P Q : SectorDecomposition d)
    (periodP : Fin P.basisCount → ℕ) (periodQ : Fin Q.basisCount → ℕ)
    (hPerP : ∀ j, IsPeriodic (periodP j) (P.basis j))
    (hPerQ : ∀ k, IsPeriodic (periodQ k) (Q.basis k))
    (hNonRepP : ∀ i j, i ≠ j → ¬ HetRepeatedBlocks (P.basis i) (P.basis j))
    (hNonRepQ : ∀ i j, i ≠ j → ¬ HetRepeatedBlocks (Q.basis i) (Q.basis j))
    (hSame : SameMPV₂Pos P.toTensor Q.toTensor) :
    ∃ (perm : Fin P.basisCount ≃ Fin Q.basisCount)
      (hd : ∀ j, P.basisDim j = Q.basisDim (perm j))
      (ξ : Fin P.basisCount → ℂ)
      (U : (j : Fin P.basisCount) → Matrix.unitaryGroup (Fin (Q.basisDim (perm j))) ℂ)
      (z : (j : Fin P.basisCount) → Fin (P.copies j) → ℂ),
      (∀ j, ‖ξ j‖ = 1) ∧
      (∀ j, periodP j = periodQ (perm j)) ∧
      (∀ j i, (cast (congrArg (MPSTensor d) (hd j)) (P.basis j)) i =
        ξ j • ((U j : Matrix (Fin (Q.basisDim (perm j))) (Fin (Q.basisDim (perm j))) ℂ) *
          Q.basis (perm j) i *
          (U j : Matrix (Fin (Q.basisDim (perm j))) (Fin (Q.basisDim (perm j))) ℂ)ᴴ)) ∧
      (∀ j, Matrix.diagonal (z j) ^ periodP j = 1) ∧
      (∀ j, ∃ (_hCopies : P.copies j = Q.copies (perm j))
          (τ : Fin (P.copies j) ≃ Fin (Q.copies (perm j))),
        Matrix.diagonal (z j) * Matrix.diagonal (fun q => ξ j * P.weight j q) =
          Matrix.diagonal (fun q => Q.weight (perm j) (τ q))) := by
  classical
  obtain ⟨perm, ξ, z, hξ, hperiod, hGauge, _, hz, hWeights, _⟩ :=
    fundamentalTheorem_periodic_equalCase_sectorDecomposition
      P Q periodP periodQ hPerP hPerQ hNonRepP hNonRepQ hSame
  have hUnitary := fun j => (hGauge j).exists_unitary_of_isPeriodic
    (Complex.ne_zero_of_norm_eq_one (hξ j)) (hPerP j) (hPerQ (perm j))
  choose hd U _ hU using hUnitary
  exact ⟨perm, hd, ξ, U, z, hξ, hperiod, hU, hz, hWeights⟩

/-- Equal periodic families with trace-preserving canonical basis tensors are
related by a global unitary after the finite-order multiplicity phase gauge.
The phase on each copy has order dividing that copy's period. Source:
arXiv:1708.00029, Theorem 3.8 and Theorem 4.1, lines 643--690 and 752--765. -/
theorem fundamentalTheorem_periodic_equalCase_unitary_global
    {d : ℕ} (P Q : SectorDecomposition d)
    (periodP : Fin P.basisCount → ℕ) (periodQ : Fin Q.basisCount → ℕ)
    (hPerP : ∀ j, IsPeriodic (periodP j) (P.basis j))
    (hPerQ : ∀ k, IsPeriodic (periodQ k) (Q.basis k))
    (hNonRepP : ∀ i j, i ≠ j → ¬ HetRepeatedBlocks (P.basis i) (P.basis j))
    (hNonRepQ : ∀ i j, i ≠ j → ¬ HetRepeatedBlocks (Q.basis i) (Q.basis j))
    (hSame : SameMPV₂Pos P.toTensor Q.toTensor)
    (L : ℕ) (hLdvd : ∀ j, periodP j ∣ L) :
    ∃ (z : (j : Fin P.basisCount) → Fin (P.copies j) → ℂ)
      (Y : Matrix (Fin P.totalDim) (Fin Q.totalDim) ℂ),
      (∀ j q, z j q ^ periodP j = 1) ∧
      Y * Yᴴ = 1 ∧ Yᴴ * Y = 1 ∧
      blockScalarMatrix P.flatDim (P.flatCopyScalar z) ^ L = 1 ∧
      (∀ i, blockScalarMatrix P.flatDim (P.flatCopyScalar z) * P.toTensor i =
        P.toTensor i * blockScalarMatrix P.flatDim (P.flatCopyScalar z)) ∧
      (∀ i, blockScalarMatrix P.flatDim (P.flatCopyScalar z) * P.toTensor i =
        Y * Q.toTensor i * Yᴴ) ∧
      SameMPV₂Pos P.toTensor
        (fun i => blockScalarMatrix P.flatDim (P.flatCopyScalar z) * P.toTensor i) := by
  classical
  obtain ⟨perm, hd, ξ, U, z, _, _, hU, hz, hWeights⟩ :=
    fundamentalTheorem_periodic_equalCase_unitary_matching P Q periodP periodQ
      hPerP hPerQ hNonRepP hNonRepQ hSame
  let V := Equiv.piCongrLeft (fun k => Matrix.unitaryGroup (Fin (Q.basisDim k)) ℂ) perm U
  have hV : ∀ j i, (cast (congrArg (MPSTensor d) (hd j)) (P.basis j)) i =
      ξ j • ((V (perm j) : Matrix (Fin (Q.basisDim (perm j)))
          (Fin (Q.basisDim (perm j))) ℂ) * Q.basis (perm j) i *
        (V (perm j) : Matrix (Fin (Q.basisDim (perm j)))
          (Fin (Q.basisDim (perm j))) ℂ)ᴴ) := by
    intro j i
    simpa only [V, Equiv.piCongrLeft_apply_apply] using hU j i
  choose hCopies τ hτ using hWeights
  have hweight : ∀ j q, z j q * (ξ j * P.weight j q) = Q.weight (perm j) (τ j q) := by
    intro j q
    simpa only [Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply_eq] using
      congrArg (fun M => M q q) (hτ j)
  have hzpow : ∀ j q, z j q ^ periodP j = 1 := by
    intro j q
    simpa only [Matrix.diagonal_pow, Pi.pow_apply, Matrix.diagonal_apply_eq,
      Matrix.one_apply_eq] using congrArg (fun M => M q q) (hz j)
  obtain ⟨Y, hY⟩ := equalCase_global_unitary_zgauge_of_blockwise
    perm hd τ ξ V hV z hweight periodP hPerP hzpow L hLdvd
  exact ⟨z, Y, hzpow, hY⟩

end MPSTensor
