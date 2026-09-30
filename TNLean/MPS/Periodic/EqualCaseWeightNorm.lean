/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Periodic.EqualCaseGlobal
import TNLean.MPS.Periodic.UnitBlockTracePreserving

/-!
# Unit multiplicities in the periodic equal case

The equal-case theorem matches copy weights after multiplication by two
unit-modulus factors: a phase relating the periodic basis tensors and a
root of unity on each copy. Consequently unit-modulus weights on one side
force unit-modulus weights on the other. This is the normalization step
in arXiv:1708.00029, Theorem 4.1, lines 752--765.
-/

namespace MPSTensor

/-- Equality of periodic families preserves unit modulus of all copy
weights. This derives the normalization from the equal-case theorem,
rather than assuming it for the refinement root. Source:
arXiv:1708.00029, Theorem 4.1, lines 752--765. -/
theorem SectorDecomposition.weight_norm_eq_one_of_periodic_sameMPV₂Pos
    {d : ℕ} (P Q : SectorDecomposition d)
    (periodP : Fin P.basisCount → ℕ) (periodQ : Fin Q.basisCount → ℕ)
    (hPerP : ∀ j, IsPeriodic (periodP j) (P.basis j))
    (hPerQ : ∀ k, IsPeriodic (periodQ k) (Q.basis k))
    (hNonRepP : ∀ i j, i ≠ j → ¬ HetRepeatedBlocks (P.basis i) (P.basis j))
    (hNonRepQ : ∀ i j, i ≠ j → ¬ HetRepeatedBlocks (Q.basis i) (Q.basis j))
    (hSame : SameMPV₂Pos P.toTensor Q.toTensor)
    (hQ : ∀ j q, ‖Q.weight j q‖ = 1) :
    ∀ j q, ‖P.weight j q‖ = 1 := by
  classical
  obtain ⟨perm, ξ, z, hξ, _, _, _, hz, hWeights, _⟩ :=
    fundamentalTheorem_periodic_equalCase_sectorDecomposition
      P Q periodP periodQ hPerP hPerQ hNonRepP hNonRepQ hSame
  intro j q
  have hzpow : z j q ^ periodP j = 1 := by
    have h := congrArg (fun M => M q q) (hz j)
    simpa only [Matrix.diagonal_pow, Pi.pow_apply, Matrix.diagonal_apply_eq,
      Matrix.one_apply_eq] using h
  have hznorm : ‖z j q‖ = 1 :=
    Complex.norm_eq_one_of_pow_eq_one hzpow (Nat.ne_of_gt (hPerP j).period_pos)
  obtain ⟨_, τ, hτ⟩ := hWeights j
  have heq : z j q * (ξ j * P.weight j q) = Q.weight (perm j) (τ q) := by
    have h := congrArg (fun M => M q q) hτ
    simpa only [Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply_eq] using h
  have hnorm := congrArg norm heq
  simpa only [norm_mul, hznorm, hξ j, one_mul, hQ] using hnorm

/-- The literal periodic representative on the other side of an equal-case
comparison is trace preserving whenever all target copy weights have unit
modulus. Source: arXiv:1708.00029, Theorem 4.1, lines 752--765. -/
theorem SectorDecomposition.leftCanonical_of_periodic_sameMPV₂Pos
    {d : ℕ} (P Q : SectorDecomposition d)
    (periodP : Fin P.basisCount → ℕ) (periodQ : Fin Q.basisCount → ℕ)
    (hPerP : ∀ j, IsPeriodic (periodP j) (P.basis j))
    (hPerQ : ∀ k, IsPeriodic (periodQ k) (Q.basis k))
    (hNonRepP : ∀ i j, i ≠ j → ¬ HetRepeatedBlocks (P.basis i) (P.basis j))
    (hNonRepQ : ∀ i j, i ≠ j → ¬ HetRepeatedBlocks (Q.basis i) (Q.basis j))
    (hSame : SameMPV₂Pos P.toTensor Q.toTensor)
    (hQ : ∀ j q, ‖Q.weight j q‖ = 1) : IsLeftCanonical P.toTensor := by
  have hNorm := P.weight_norm_eq_one_of_periodic_sameMPV₂Pos Q
    periodP periodQ hPerP hPerQ hNonRepP hNonRepQ hSame hQ
  exact leftCanonical_toTensorFromBlocks_of_weight_norm_one P.flatBasis P.flatWeight
    (fun s => (hPerP (P.flatIndexEquiv.symm s).1).leftCanonical)
    (fun s => hNorm (P.flatIndexEquiv.symm s).1 (P.flatIndexEquiv.symm s).2)

end MPSTensor
