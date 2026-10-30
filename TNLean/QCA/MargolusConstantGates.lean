/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.QCA.MargolusCoherentCoordinates
import TNLean.QCA.ConsecutivePairCoordinates

/-!
# One fixed pair of actual Margolus gates

The transported even coordinates give one shifted output rule which is
used on the left after translation by minus two, and on the right
without translation. The full matrix-unit expression therefore uses the
same output gate on both neighbouring pairs. Original QCA covariance
then translates this fixed two-layer expression to every block.

Source: Schumacher–Werner, quant-ph/0405174, bruleU/bruleV,
lines 980–1001, translation compatibility and basis freedom,
lines 1033–1041, and defBBq, lines 1199–1226.

**Scope restriction (homogeneous chain):** The physical size is one fixed
positive integer; see
`docs/paper-gaps/gnvw12_site_dependent_adjacent_generation_scope.tex`.
-/

open scoped Matrix Kronecker BigOperators

namespace SpinChain.PropagatesWithin

variable {d : ℕ} [NeZero d]
  {ω : QuasiLocalAlgebra d ≃⋆ₐ[ℂ] QuasiLocalAlgebra d}
  (hω : PropagatesWithin ω (Finset.Icc (-1) 1)) (hcov : TranslationCovariant ω)

/-- Translation back by two recovers the even input factor from the
one common shifted output rule. Source: Schumacher–Werner defBBq,
lines 1199–1226. -/
theorem coherentMargolusOutputRule_left
    (A : Matrix (Fin (supportAlgebraMatrixSize hω 0))
      (Fin (supportAlgebraMatrixSize hω 0)) ℂ) :
    quasiLocalTranslation d (-2)
      (matrixToQuasiLocalObservable d (rightPair 0)
        (coherentMargolusOutputRule hω hcov (1 ⊗ₖ A))) =
      matrixToQuasiLocalObservable d (leftPair 0)
        ((evenSupportMatrixEquiv hω 0).symm A) := by
  have h := coherentMargolusOutputRule_kronecker hω hcov 1 A
  simp only [map_one, one_mul] at h
  rw [h, ← quasiLocalTranslation_symm d 2, StarAlgEquiv.symm_apply_apply]

/-- The same shifted output rule recovers the odd input factor directly.
Source: Schumacher–Werner defBBq and bruleV, lines 980–1001 and 1199–1226. -/
theorem coherentMargolusOutputRule_right
    (B : Matrix (Fin (supportAlgebraMatrixSize hω 1))
      (Fin (supportAlgebraMatrixSize hω 1)) ℂ) :
    matrixToQuasiLocalObservable d (rightPair 0)
      (coherentMargolusOutputRule hω hcov (B ⊗ₖ 1)) =
      matrixToQuasiLocalObservable d (rightPair 0)
        ((oddSupportMatrixEquiv hω 0).symm B) := by
  have h := coherentMargolusOutputRule_kronecker hω hcov B 1
  simpa only [map_one, mul_one] using h

/-- The actual product input rule uses the same shifted output rule at
both neighbouring pairs. Source: Schumacher–Werner locMarg, bruleU,
bruleV and defBBq, lines 980–1008 and 1199–1226. -/
theorem coherentMargolus_alternating_kronecker
    (A : Matrix (Fin (supportAlgebraMatrixSize hω 0))
      (Fin (supportAlgebraMatrixSize hω 0)) ℂ)
    (B : Matrix (Fin (supportAlgebraMatrixSize hω 1))
      (Fin (supportAlgebraMatrixSize hω 1)) ℂ) :
    ω (matrixToQuasiLocalObservable d (evenPair 0)
      ((margolusInputRule hω 0).symm (A ⊗ₖ B))) =
      quasiLocalTranslation d (-2)
          (matrixToQuasiLocalObservable d (rightPair 0)
            (coherentMargolusOutputRule hω hcov (1 ⊗ₖ A))) *
        matrixToQuasiLocalObservable d (rightPair 0)
          (coherentMargolusOutputRule hω hcov (B ⊗ₖ 1)) := by
  rw [coherentMargolusOutputRule_left, coherentMargolusOutputRule_right]
  simpa only [StarAlgEquiv.apply_symm_apply] using
    margolusInputRule_symm_kronecker hω 0
      ((evenSupportMatrixEquiv hω 0).symm A) ((oddSupportMatrixEquiv hω 0).symm B)

/-- The literal two-layer expression in one fixed shifted output gate.
The first factor acts on the preceding pair and the second on the
following pair, with input order odd then even for this gate.
Source: Schumacher–Werner bruleU/bruleV and locMarg, lines 980–1008. -/
noncomputable def constantMargolusGateRule
    (V : Matrix (Fin d × Fin d)
      (Fin (supportAlgebraMatrixSize hω 1) × Fin (supportAlgebraMatrixSize hω 0)) ℂ)
    (K : Matrix (Fin (supportAlgebraMatrixSize hω 0) × Fin (supportAlgebraMatrixSize hω 1))
      (Fin (supportAlgebraMatrixSize hω 0) × Fin (supportAlgebraMatrixSize hω 1)) ℂ) :
    QuasiLocalAlgebra d :=
  ∑ i, ∑ j, K i j •
    (quasiLocalTranslation d (-2)
        (matrixToQuasiLocalObservable d (rightPair 0)
          (Matrix.reindex (consecutivePairConfigEquiv d 1) (consecutivePairConfigEquiv d 1)
            (V * (1 ⊗ₖ Matrix.single i.1 j.1 (1 : ℂ)) * Vᴴ))) *
      matrixToQuasiLocalObservable d (rightPair 0)
        (Matrix.reindex (consecutivePairConfigEquiv d 1) (consecutivePairConfigEquiv d 1)
          (V * (Matrix.single i.2 j.2 (1 : ℂ) ⊗ₖ 1) * Vᴴ)))

private theorem single_prod_eq_smul_kronecker
    {p q : Type*} [DecidableEq p] [DecidableEq q]
    (i j : p × q) (z : ℂ) :
    Matrix.single i j z = z •
      (Matrix.single i.1 j.1 (1 : ℂ) ⊗ₖ Matrix.single i.2 j.2 (1 : ℂ)) := by
  rw [Matrix.single_kronecker_single, one_mul, Matrix.smul_single, smul_eq_mul, mul_one]

private theorem constantMargolusGateRule_eq
    (V : Matrix (Fin d × Fin d)
      (Fin (supportAlgebraMatrixSize hω 1) × Fin (supportAlgebraMatrixSize hω 0)) ℂ)
    (hV : ∀ B, coherentMargolusOutputRule hω hcov B =
      Matrix.reindex (consecutivePairConfigEquiv d 1) (consecutivePairConfigEquiv d 1)
        (V * B * Vᴴ))
    (K : Matrix (Fin (supportAlgebraMatrixSize hω 0) × Fin (supportAlgebraMatrixSize hω 1))
      (Fin (supportAlgebraMatrixSize hω 0) × Fin (supportAlgebraMatrixSize hω 1)) ℂ) :
    ω (matrixToQuasiLocalObservable d (evenPair 0)
      ((margolusInputRule hω 0).symm K)) = constantMargolusGateRule hω V K := by
  classical
  unfold constantMargolusGateRule
  conv_lhs => rw [Matrix.matrix_eq_sum_single K]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [single_prod_eq_smul_kronecker, map_smul, map_smul, map_smul,
    coherentMargolus_alternating_kronecker hω hcov, hV, hV]

/-- There is one fixed input unitary and one fixed shifted output
unitary whose literal alternating rule gives the actual QCA image on
all translated pair matrices. Both gates and their common intermediate
coordinates are derived. No equality between independently chosen
factor presentations, circuit identity or output-action premise is used.
Source: Schumacher–Werner bruleU/bruleV, lines 980–1001, translation
compatibility, lines 1033–1041, and defBBq, lines 1199–1226. -/
theorem exists_fixed_margolus_unitary_gates :
    ∃ (U : Matrix (Fin (supportAlgebraMatrixSize hω 0) ×
          Fin (supportAlgebraMatrixSize hω 1)) (Fin d × Fin d) ℂ)
      (V : Matrix (Fin d × Fin d)
          (Fin (supportAlgebraMatrixSize hω 1) × Fin (supportAlgebraMatrixSize hω 0)) ℂ),
      U.IsUnitaryBetween ∧ V.IsUnitaryBetween ∧
      (∀ A, margolusInputRule hω 0
        (Matrix.reindex (consecutivePairConfigEquiv d 0) (consecutivePairConfigEquiv d 0) A) =
          U * A * Uᴴ) ∧
      (∀ B, coherentMargolusOutputRule hω hcov B =
        Matrix.reindex (consecutivePairConfigEquiv d 1) (consecutivePairConfigEquiv d 1)
          (V * B * Vᴴ)) ∧
      ∀ (t : ℤ) (A : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ),
        ω (quasiLocalTranslation d t (matrixToQuasiLocalObservable d (evenPair 0)
          (Matrix.reindex (consecutivePairConfigEquiv d 0) (consecutivePairConfigEquiv d 0) A))) =
          quasiLocalTranslation d t (constantMargolusGateRule hω V (U * A * Uᴴ)) := by
  let E := Matrix.matrixReindexStarAlgEquiv (consecutivePairConfigEquiv d 1)
  let F := (Matrix.matrixReindexStarAlgEquiv (consecutivePairConfigEquiv d 0)).trans
    (margolusInputRule hω 0)
  let G := (coherentMargolusOutputRule hω hcov).trans E.symm
  obtain ⟨U, hU, hInput⟩ :=
    Matrix.exists_unitary_conj_of_starAlgEquiv_matrix_between F
  obtain ⟨V, hV, hOutput⟩ :=
    Matrix.exists_unitary_conj_of_starAlgEquiv_matrix_between G
  have hInput' (A : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
      margolusInputRule hω 0
        (Matrix.reindex (consecutivePairConfigEquiv d 0) (consecutivePairConfigEquiv d 0) A) =
          U * A * Uᴴ := hInput A
  have hOutput' (B) : coherentMargolusOutputRule hω hcov B =
      Matrix.reindex (consecutivePairConfigEquiv d 1) (consecutivePairConfigEquiv d 1)
        (V * B * Vᴴ) := by
    have h := congrArg E (hOutput B)
    change E (E.symm (coherentMargolusOutputRule hω hcov B)) = E (V * B * Vᴴ) at h
    rw [StarAlgEquiv.apply_symm_apply] at h
    exact h
  refine ⟨U, V, hU, hV, hInput', hOutput', ?_⟩
  intro t A
  rw [(translationCovariant_iff ω).mp hcov t]
  congr 1
  have h := constantMargolusGateRule_eq hω hcov V hOutput'
    (margolusInputRule hω 0
      (Matrix.reindex (consecutivePairConfigEquiv d 0) (consecutivePairConfigEquiv d 0) A))
  simpa only [StarAlgEquiv.symm_apply_apply, hInput'] using h

end SpinChain.PropagatesWithin
