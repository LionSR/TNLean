/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.Equivalence
import TNLean.MPS.MPU.Examples.ShiftTilde
import TNLean.MPS.MPU.SymmetryPathTransport

/-!
# Symmetry transport by the physical swap

Multiplication by the local swap converts swap-combined adjunction and
transposition into ordinary adjunction and transposition. It preserves
entrywise conjugation. The same multiplication transports continuous paths.

**Scope restriction:** path comparisons in this module use one fixed ambient
bond dimension. The comparison of all three source examples, whose canonical
bond dimensions differ, still requires a relation permitting common ambient
representatives. See `docs/paper-gaps/mpu_equivalence_fixed_bond.tex`.

**Scope restriction (no identity ancillas):** The strict comparisons
`strictlyEquivalentUnderSymmetry_shiftSwapDagger_iff`,
`strictlyEquivalentUnderSymmetry_shiftSwapTranspose_iff` and
`strictlyEquivalentUnderSymmetry_conjugation_ketLeftMul_swap_iff` compare
strict equivalence without adjoining identity ancillas. The source definition
of equivalence under a symmetry also permits identity ancillas
(arXiv:1703.09188, Definition `def:equivalent-symmetry`, lines 1356--1366),
and transporting the symmetry action to the enlarged physical dimension is not
determined by the source. See
`docs/paper-gaps/mpu_symmetry_ancilla_transport.tex`.

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

variable {d D : ℕ}

/-- Pointwise equivalent invariance equations at the same applicable chain
lengths give equivalent symmetry-invariance predicates.
This is the pointwise step in arXiv:1703.09188, Lemma `lemma:sym-trafo-swap`. -/
theorem isInvariantUnderSymmetry_iff_of_pointwise
    (S T : FiniteChainOperatorSymmetry d) (U V : MPOTensor d D)
    (happlicable : S.applicable = T.applicable)
    (hST : ∀ N : ℕ, S.action (mpo U N) = mpo U N ↔ T.action (mpo V N) = mpo V N) :
    IsInvariantUnderSymmetry S U ↔ IsInvariantUnderSymmetry T V := by
  unfold IsInvariantUnderSymmetry
  simp_rw [happlicable, hST]

/-- Adjunction on every positive-length periodic operator.
Source: arXiv:1703.09188, time reversal, lines 965--973. -/
def daggerSymmetry (d : ℕ) : FiniteChainOperatorSymmetry d where
  applicable := {N | 0 < N}
  action := fun X ↦ Xᴴ

/-- Transposition on every positive-length periodic operator.
Source: arXiv:1703.09188, transposition, lines 1258--1264. -/
def transposeSymmetry (d : ℕ) : FiniteChainOperatorSymmetry d where
  applicable := {N | 0 < N}
  action := fun X ↦ Xᵀ

/-- Entrywise conjugation on every positive-length periodic operator.
Source: arXiv:1703.09188, conjugation, lines 1005--1010. -/
def conjugationSymmetry (d : ℕ) : FiniteChainOperatorSymmetry d where
  applicable := {N | 0 < N}
  action := fun X ↦ X.map (starRingEnd ℂ)

/-- Adjunction combined with exchange of the two physical species.
Source: arXiv:1703.09188, equation `SSymmetries-dagger`, with \(Q=S\). -/
noncomputable def shiftSwapDaggerSymmetry (d : ℕ) :
    FiniteChainOperatorSymmetry (d * d) where
  applicable := {N | 0 < N}
  action := fun {N} X ↦
    sitewisePhysicalMatrix (shiftPhysicalSwap d) N * Xᴴ *
      sitewisePhysicalMatrix (shiftPhysicalSwap d) N

/-- Transposition combined with exchange of the two physical species.
Source: arXiv:1703.09188, equation `SSymmetries-transpose`, with \(Q=S\). -/
noncomputable def shiftSwapTransposeSymmetry (d : ℕ) :
    FiniteChainOperatorSymmetry (d * d) where
  applicable := {N | 0 < N}
  action := fun {N} X ↦
    sitewisePhysicalMatrix (shiftPhysicalSwap d) N * Xᵀ *
      sitewisePhysicalMatrix (shiftPhysicalSwap d) N

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
    sitewisePhysicalMatrix (shiftPhysicalSwap d) N *
      sitewisePhysicalMatrix (shiftPhysicalSwap d) N = 1 := by
  rw [sitewisePhysicalMatrix_mul, shiftPhysicalSwap_mul_self,
    sitewisePhysicalMatrix_one]

private theorem chainSwap_transpose (d N : ℕ) :
    (sitewisePhysicalMatrix (shiftPhysicalSwap d) N)ᵀ =
      sitewisePhysicalMatrix (shiftPhysicalSwap d) N := by
  have h := shiftPhysicalSwap_transpose d
  ext σ τ
  simp only [Matrix.transpose_apply, sitewisePhysicalMatrix]
  apply Finset.prod_congr rfl
  intro n _
  exact congrFun (congrFun h (σ n)) (τ n)

private theorem chainSwap_map_star (d N : ℕ) :
    (sitewisePhysicalMatrix (shiftPhysicalSwap d) N).map (starRingEnd ℂ) =
      sitewisePhysicalMatrix (shiftPhysicalSwap d) N := by
  ext σ τ
  simp [sitewisePhysicalMatrix, shiftPhysicalSwap, Equiv.Perm.permMatrix,
    PEquiv.toMatrix_apply]

/-- For an involution \(Q\), an operation satisfying
\(\mathrm{op}(QX)=\mathrm{op}(X)Q\) converts the equation
\(Q\mathrm{op}(X)Q=X\) into \(\mathrm{op}(QX)=QX\).
This is the matrix argument in arXiv:1703.09188, Section `othersymmetries`,
lines 1295--1322, and Lemma `lemma:sym-trafo-swap`. -/
theorem swapCombined_fixed_iff_leftMul {n : Type*} [Fintype n] [DecidableEq n]
    (Q X : Matrix n n ℂ) (hQ : Q * Q = 1)
    (op : Matrix n n ℂ → Matrix n n ℂ) (hop : op (Q * X) = op X * Q) :
    Q * op X * Q = X ↔ op (Q * X) = Q * X := by
  rw [hop]
  constructor
  · intro h
    simpa only [← Matrix.mul_assoc, hQ, Matrix.one_mul] using
      congrArg (fun Y ↦ Q * Y) h
  · intro h
    calc
      Q * op X * Q = Q * (op X * Q) := Matrix.mul_assoc ..
      _ = Q * (Q * X) := congrArg (fun Y ↦ Q * Y) h
      _ = X := by rw [← Matrix.mul_assoc, hQ, Matrix.one_mul]

/-- The physical swap converts swap-combined adjunction into adjunction.
Source: arXiv:1703.09188, Lemma `lemma:sym-trafo-swap`, lines 2065--2085. -/
theorem isInvariantUnderSymmetry_shiftSwapDagger_iff (U : MPOTensor (d * d) D) :
    IsInvariantUnderSymmetry (shiftSwapDaggerSymmetry d) U ↔
      IsInvariantUnderSymmetry (daggerSymmetry (d * d))
        (U.ketLeftMul (shiftPhysicalSwap d)) := by
  apply isInvariantUnderSymmetry_iff_of_pointwise
    (shiftSwapDaggerSymmetry d) (daggerSymmetry (d * d)) _ _ rfl
  intro N
  change _ ↔ (mpo (U.ketLeftMul (shiftPhysicalSwap d)) N)ᴴ = _
  rw [mpo_ketLeftMul]
  apply swapCombined_fixed_iff_leftMul _ _ (chainSwap_mul_self d N)
  rw [Matrix.conjTranspose_mul, sitewisePhysicalMatrix_conjTranspose,
    shiftPhysicalSwap_conjTranspose]

/-- The physical swap converts swap-combined transposition into transposition.
Source: arXiv:1703.09188, Lemma `lemma:sym-trafo-swap`, lines 2065--2085. -/
theorem isInvariantUnderSymmetry_shiftSwapTranspose_iff (U : MPOTensor (d * d) D) :
    IsInvariantUnderSymmetry (shiftSwapTransposeSymmetry d) U ↔
      IsInvariantUnderSymmetry (transposeSymmetry (d * d))
        (U.ketLeftMul (shiftPhysicalSwap d)) := by
  apply isInvariantUnderSymmetry_iff_of_pointwise
    (shiftSwapTransposeSymmetry d) (transposeSymmetry (d * d)) _ _ rfl
  intro N
  change _ ↔ (mpo (U.ketLeftMul (shiftPhysicalSwap d)) N)ᵀ = _
  rw [mpo_ketLeftMul]
  apply swapCombined_fixed_iff_leftMul _ _ (chainSwap_mul_self d N)
  rw [Matrix.transpose_mul, chainSwap_transpose]

/-- The physical swap preserves entrywise conjugation invariance.
Source: arXiv:1703.09188, Lemma `lemma:sym-trafo-swap`, lines 2065--2085. -/
theorem isInvariantUnderSymmetry_conjugation_ketLeftMul_swap_iff
    (U : MPOTensor (d * d) D) :
    IsInvariantUnderSymmetry (conjugationSymmetry (d * d)) U ↔
      IsInvariantUnderSymmetry (conjugationSymmetry (d * d))
        (U.ketLeftMul (shiftPhysicalSwap d)) := by
  apply isInvariantUnderSymmetry_iff_of_pointwise _ _ _ _ rfl
  intro N
  change (mpo U N).map (starRingEnd ℂ) = _ ↔
    (mpo (U.ketLeftMul (shiftPhysicalSwap d)) N).map (starRingEnd ℂ) = _
  rw [mpo_ketLeftMul, Matrix.map_mul, chainSwap_map_star]
  constructor
  · exact congrArg (fun X ↦ sitewisePhysicalMatrix (shiftPhysicalSwap d) N * X)
  · intro h
    simpa only [← Matrix.mul_assoc, chainSwap_mul_self, Matrix.one_mul] using
      congrArg (fun X ↦ sitewisePhysicalMatrix (shiftPhysicalSwap d) N * X) h

/-- Swap multiplication identifies strict equivalence under swap-combined
adjunction with strict equivalence under adjunction, at fixed bond dimension.
Source: arXiv:1703.09188, Lemma `lemma:sym-trafo-swap`, lines 2065--2085. -/
theorem strictlyEquivalentUnderSymmetry_shiftSwapDagger_iff
    (U V : MPOTensor (d * d) D) :
    StrictlyEquivalentUnderSymmetry (shiftSwapDaggerSymmetry d) U V rfl ↔
      StrictlyEquivalentUnderSymmetry (daggerSymmetry (d * d))
        (U.ketLeftMul (shiftPhysicalSwap d)) (V.ketLeftMul (shiftPhysicalSwap d)) rfl :=
  strictlyEquivalentUnderSymmetry_iff_ketLeftMul _ _ _
    (shiftPhysicalSwap_mem_unitaryGroup d) (shiftPhysicalSwap_mul_self d)
    isInvariantUnderSymmetry_shiftSwapDagger_iff U V

/-- Swap multiplication identifies strict equivalence under swap-combined
transposition with strict equivalence under transposition, at fixed bond dimension.
Source: arXiv:1703.09188, Lemma `lemma:sym-trafo-swap`, lines 2065--2085. -/
theorem strictlyEquivalentUnderSymmetry_shiftSwapTranspose_iff
    (U V : MPOTensor (d * d) D) :
    StrictlyEquivalentUnderSymmetry (shiftSwapTransposeSymmetry d) U V rfl ↔
      StrictlyEquivalentUnderSymmetry (transposeSymmetry (d * d))
        (U.ketLeftMul (shiftPhysicalSwap d)) (V.ketLeftMul (shiftPhysicalSwap d)) rfl :=
  strictlyEquivalentUnderSymmetry_iff_ketLeftMul _ _ _
    (shiftPhysicalSwap_mem_unitaryGroup d) (shiftPhysicalSwap_mul_self d)
    isInvariantUnderSymmetry_shiftSwapTranspose_iff U V

/-- Swap multiplication preserves strict equivalence under entrywise
conjugation, at fixed bond dimension.
Source: arXiv:1703.09188, Lemma `lemma:sym-trafo-swap`, lines 2065--2085. -/
theorem strictlyEquivalentUnderSymmetry_conjugation_ketLeftMul_swap_iff
    (U V : MPOTensor (d * d) D) :
    StrictlyEquivalentUnderSymmetry (conjugationSymmetry (d * d)) U V rfl ↔
      StrictlyEquivalentUnderSymmetry (conjugationSymmetry (d * d))
        (U.ketLeftMul (shiftPhysicalSwap d)) (V.ketLeftMul (shiftPhysicalSwap d)) rfl :=
  strictlyEquivalentUnderSymmetry_iff_ketLeftMul _ _ _
    (shiftPhysicalSwap_mem_unitaryGroup d) (shiftPhysicalSwap_mul_self d)
    isInvariantUnderSymmetry_conjugation_ketLeftMul_swap_iff U V

end MPOTensor
