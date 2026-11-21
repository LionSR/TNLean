/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Algebra.MatrixInvolutionConjugation
import TNLean.MPS.MPU.Equivalence
import TNLean.MPS.MPU.Examples.ShiftTilde
import TNLean.MPS.MPU.SymmetryPathTransport

/-!
# Symmetry transport by the physical swap

Multiplication by the local swap converts swap-combined adjunction and
transposition into ordinary adjunction and transposition. It preserves
entrywise conjugation. The same multiplication transports continuous paths.

The strict comparisons
`strictlyEquivalentUnderSymmetry_shiftSwapDagger_iff`,
`strictlyEquivalentUnderSymmetry_shiftSwapTranspose_iff` and
`strictlyEquivalentUnderSymmetry_conjugation_ketLeftMul_swap_iff` formalize
Lemma `lemma:sym-trafo-swap`, where "same phase" means strict equivalence:
arXiv:1703.09188 omits the qualifier when it is clear from the context
(lines 725--730), the printed proof transports continuous symmetric paths at
fixed chain length (lines 2071--2078), and the section names ancillas
explicitly where it allows them (line 2208).

**Local fix:** equation `threeMPU2` uses one-sided multiplication
\(\widetilde U_N=S_NU_N\). The conjugation paragraph in the printed proof
of `lemma:sym-trafo-swap` instead displays two-sided multiplication. We use
the transformation in the defining equation. See
`docs/paper-gaps/mpu_swap_symmetry_one_sided.tex`.

Source: arXiv:1703.09188, equations `threeMPU2` and Lemma
`lemma:sym-trafo-swap`, lines 2053--2085.
-/

open scoped Matrix

namespace MPOTensor

variable {d D Da Db : ℕ}

/-- Adjunction combined with exchange of the two physical species.
Source: arXiv:1703.09188, equation `SSymmetries-dagger`, with \(Q=S\). -/
noncomputable def shiftSwapDaggerSymmetry (d : ℕ) :
    FiniteChainOperatorSymmetry (d * d) where
  applicable := {N | 0 < N}
  action := fun {N} X ↦
    Matrix.tensorPower N (shiftPhysicalSwap d) * Xᴴ *
      Matrix.tensorPower N (shiftPhysicalSwap d)

/-- Transposition combined with exchange of the two physical species.
Source: arXiv:1703.09188, equation `SSymmetries-transpose`, with \(Q=S\). -/
noncomputable def shiftSwapTransposeSymmetry (d : ℕ) :
    FiniteChainOperatorSymmetry (d * d) where
  applicable := {N | 0 < N}
  action := fun {N} X ↦
    Matrix.tensorPower N (shiftPhysicalSwap d) * Xᵀ *
      Matrix.tensorPower N (shiftPhysicalSwap d)

private theorem shiftPhysicalSwap_conjTranspose (d : ℕ) :
    (shiftPhysicalSwap d)ᴴ = shiftPhysicalSwap d := by
  simp only [shiftPhysicalSwap, Matrix.conjTranspose_permMatrix,
    Equiv.Perm.inv_def, bondPairSwapEquiv_symm]

private theorem shiftPhysicalSwap_transpose (d : ℕ) :
    (shiftPhysicalSwap d)ᵀ = shiftPhysicalSwap d := by
  simp only [shiftPhysicalSwap, Matrix.transpose_permMatrix,
    Equiv.Perm.inv_def, bondPairSwapEquiv_symm]

/-- The local physical swap is involutive.
Source: arXiv:1703.09188, Section `othersymmetries`, lines 1315--1322. -/
theorem shiftPhysicalSwap_mul_self (d : ℕ) :
    shiftPhysicalSwap d * shiftPhysicalSwap d = 1 := by
  have h := shiftPhysicalSwap_mem_unitaryGroup d
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose,
    shiftPhysicalSwap_conjTranspose] at h
  exact h

private theorem chainSwap_mul_self (d N : ℕ) :
    Matrix.tensorPower N (shiftPhysicalSwap d) *
      Matrix.tensorPower N (shiftPhysicalSwap d) = 1 := by
  rw [Matrix.tensorPower_mul, shiftPhysicalSwap_mul_self,
    Matrix.tensorPower_one]

private theorem chainSwap_transpose (d N : ℕ) :
    (Matrix.tensorPower N (shiftPhysicalSwap d))ᵀ =
      Matrix.tensorPower N (shiftPhysicalSwap d) := by
  have h := shiftPhysicalSwap_transpose d
  ext σ τ
  simp only [Matrix.transpose_apply, Matrix.tensorPower_apply]
  apply Finset.prod_congr rfl
  intro n _
  exact congrFun (congrFun h (σ n)) (τ n)

private theorem chainSwap_map_star (d N : ℕ) :
    (Matrix.tensorPower N (shiftPhysicalSwap d)).map (starRingEnd ℂ) =
      Matrix.tensorPower N (shiftPhysicalSwap d) := by
  ext σ τ
  simp [Matrix.tensorPower_apply, shiftPhysicalSwap, Equiv.Perm.permMatrix,
    PEquiv.toMatrix_apply]

/-- The physical swap converts swap-combined adjunction into adjunction.
Source: arXiv:1703.09188, Lemma `lemma:sym-trafo-swap`, lines 2065--2085. -/
theorem isInvariantUnderSymmetry_shiftSwapDagger_iff {E : ℕ} (U : MPOTensor (d * d) E) :
    IsInvariantUnderSymmetry (shiftSwapDaggerSymmetry d) U ↔
      IsInvariantUnderSymmetry (daggerSymmetry (d * d))
        (U.ketLeftMul (shiftPhysicalSwap d)) := by
  apply isInvariantUnderSymmetry_iff_of_pointwise
    (shiftSwapDaggerSymmetry d) (daggerSymmetry (d * d)) _ _ rfl
  intro N
  change _ ↔ (mpo (U.ketLeftMul (shiftPhysicalSwap d)) N)ᴴ = _
  rw [mpo_ketLeftMul]
  apply Matrix.swapCombined_fixed_iff_leftMul _ _ (chainSwap_mul_self d N)
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_tensorPower,
    shiftPhysicalSwap_conjTranspose]

/-- The physical swap converts swap-combined transposition into transposition.
Source: arXiv:1703.09188, Lemma `lemma:sym-trafo-swap`, lines 2065--2085. -/
theorem isInvariantUnderSymmetry_shiftSwapTranspose_iff {E : ℕ} (U : MPOTensor (d * d) E) :
    IsInvariantUnderSymmetry (shiftSwapTransposeSymmetry d) U ↔
      IsInvariantUnderSymmetry (transposeSymmetry (d * d))
        (U.ketLeftMul (shiftPhysicalSwap d)) := by
  apply isInvariantUnderSymmetry_iff_of_pointwise
    (shiftSwapTransposeSymmetry d) (transposeSymmetry (d * d)) _ _ rfl
  intro N
  change _ ↔ (mpo (U.ketLeftMul (shiftPhysicalSwap d)) N)ᵀ = _
  rw [mpo_ketLeftMul]
  apply Matrix.swapCombined_fixed_iff_leftMul _ _ (chainSwap_mul_self d N)
  rw [Matrix.transpose_mul, chainSwap_transpose]

/-- The physical swap preserves entrywise conjugation invariance.
Source: arXiv:1703.09188, Lemma `lemma:sym-trafo-swap`, lines 2065--2085. -/
theorem isInvariantUnderSymmetry_conjugation_ketLeftMul_swap_iff
    {E : ℕ} (U : MPOTensor (d * d) E) :
    IsInvariantUnderSymmetry (conjugationSymmetry (d * d)) U ↔
      IsInvariantUnderSymmetry (conjugationSymmetry (d * d))
        (U.ketLeftMul (shiftPhysicalSwap d)) := by
  apply isInvariantUnderSymmetry_iff_of_pointwise _ _ _ _ rfl
  intro N
  change (mpo U N).map (starRingEnd ℂ) = _ ↔
    (mpo (U.ketLeftMul (shiftPhysicalSwap d)) N).map (starRingEnd ℂ) = _
  rw [mpo_ketLeftMul, Matrix.map_mul, chainSwap_map_star]
  constructor
  · exact congrArg (fun X ↦ Matrix.tensorPower N (shiftPhysicalSwap d) * X)
  · intro h
    simpa only [← Matrix.mul_assoc, chainSwap_mul_self, Matrix.one_mul] using
      congrArg (fun X ↦ Matrix.tensorPower N (shiftPhysicalSwap d) * X) h

/-- Swap multiplication identifies strict equivalence under swap-combined
adjunction with strict equivalence under adjunction.
Source: arXiv:1703.09188, Lemma `lemma:sym-trafo-swap`, lines 2065--2085. -/
theorem strictlyEquivalentUnderSymmetry_shiftSwapDagger_iff
    (U : MPOTensor (d * d) Da) (V : MPOTensor (d * d) Db) :
    StrictlyEquivalentUnderSymmetry (shiftSwapDaggerSymmetry d) U V rfl ↔
      StrictlyEquivalentUnderSymmetry (daggerSymmetry (d * d))
        (U.ketLeftMul (shiftPhysicalSwap d)) (V.ketLeftMul (shiftPhysicalSwap d)) rfl :=
  strictlyEquivalentUnderSymmetry_iff_ketLeftMul _ _ _
    (shiftPhysicalSwap_mem_unitaryGroup d) (shiftPhysicalSwap_mul_self d)
    isInvariantUnderSymmetry_shiftSwapDagger_iff U V

/-- Swap multiplication identifies strict equivalence under swap-combined
transposition with strict equivalence under transposition.
Source: arXiv:1703.09188, Lemma `lemma:sym-trafo-swap`, lines 2065--2085. -/
theorem strictlyEquivalentUnderSymmetry_shiftSwapTranspose_iff
    (U : MPOTensor (d * d) Da) (V : MPOTensor (d * d) Db) :
    StrictlyEquivalentUnderSymmetry (shiftSwapTransposeSymmetry d) U V rfl ↔
      StrictlyEquivalentUnderSymmetry (transposeSymmetry (d * d))
        (U.ketLeftMul (shiftPhysicalSwap d)) (V.ketLeftMul (shiftPhysicalSwap d)) rfl :=
  strictlyEquivalentUnderSymmetry_iff_ketLeftMul _ _ _
    (shiftPhysicalSwap_mem_unitaryGroup d) (shiftPhysicalSwap_mul_self d)
    isInvariantUnderSymmetry_shiftSwapTranspose_iff U V

/-- Swap multiplication preserves strict equivalence under entrywise
conjugation.
Source: arXiv:1703.09188, Lemma `lemma:sym-trafo-swap`, lines 2065--2085. -/
theorem strictlyEquivalentUnderSymmetry_conjugation_ketLeftMul_swap_iff
    (U : MPOTensor (d * d) Da) (V : MPOTensor (d * d) Db) :
    StrictlyEquivalentUnderSymmetry (conjugationSymmetry (d * d)) U V rfl ↔
      StrictlyEquivalentUnderSymmetry (conjugationSymmetry (d * d))
        (U.ketLeftMul (shiftPhysicalSwap d)) (V.ketLeftMul (shiftPhysicalSwap d)) rfl :=
  strictlyEquivalentUnderSymmetry_iff_ketLeftMul _ _ _
    (shiftPhysicalSwap_mem_unitaryGroup d) (shiftPhysicalSwap_mul_self d)
    isInvariantUnderSymmetry_conjugation_ketLeftMul_swap_iff U V

end MPOTensor
