/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.QCA.MargolusUnitaryGates
import TNLean.QCA.TranslationCovariance
import Mathlib.Data.Matrix.Basis

/-!
# The actual alternating rule on every even-pair observable

The first rule splits an even physical pair into its two prescribed
support factors. Those factors are inserted in the two neighbouring
shifted output rules. A matrix-unit expansion gives the resulting actual
quasi-local observable for every input matrix, not only product inputs.

Source: Schumacher–Werner, quant-ph/0405174, locMarg, bruleU and bruleV,
lines 980–1008; GNVW, arXiv:0910.3675v2, AARReven and AARRodd,
lines 1276–1318.

**Scope restriction (homogeneous chain):** The physical size is one fixed
positive integer. See
`docs/paper-gaps/gnvw12_site_dependent_adjacent_generation_scope.tex`.
The finite local identities here use position-dependent prescribed
factor coordinates and no translation-covariance premise.
-/

open scoped Matrix Kronecker BigOperators

namespace SpinChain.PropagatesWithin

variable {d : ℕ} [NeZero d]
  {ω : QuasiLocalAlgebra d ≃⋆ₐ[ℂ] QuasiLocalAlgebra d}

/-- The even and odd factors of one input pair are recovered from the
two neighbouring shifted output gates. This is the actual alternating
local product rule, Schumacher–Werner locMarg, lines 980–1008. -/
theorem margolus_alternating_kronecker
    (hω : PropagatesWithin ω (Finset.Icc (-1) 1)) (x : ℤ)
    (A : Matrix (Fin (supportAlgebraMatrixSize hω (2 * (x + 1))))
      (Fin (supportAlgebraMatrixSize hω (2 * (x + 1)))) ℂ)
    (B : Matrix (Fin (supportAlgebraMatrixSize hω (2 * (x + 1) + 1)))
      (Fin (supportAlgebraMatrixSize hω (2 * (x + 1) + 1))) ℂ) :
    ω (matrixToQuasiLocalObservable d (evenPair (x + 1))
      ((margolusInputRule hω (x + 1)).symm (A ⊗ₖ B))) =
      matrixToQuasiLocalObservable d (rightPair x)
          (margolusOutputRule hω x (1 ⊗ₖ A)) *
        matrixToQuasiLocalObservable d (rightPair (x + 1))
          (margolusOutputRule hω (x + 1) (B ⊗ₖ 1)) := by
  let a := (evenSupportMatrixEquiv hω (x + 1)).symm A
  let b := (oddSupportMatrixEquiv hω (x + 1)).symm B
  have hInput := margolusInputRule_symm_kronecker hω (x + 1) a b
  have hLeft := margolusOutputRule_kronecker hω x 1 a
  have hRight := margolusOutputRule_kronecker hω (x + 1) b 1
  simp only [map_one, StarAlgEquiv.apply_symm_apply, one_mul] at hLeft
  simp only [map_one, StarAlgEquiv.apply_symm_apply, mul_one] at hRight
  rw [hLeft, hRight]
  simpa only [StarAlgEquiv.apply_symm_apply] using hInput

/-- The finite matrix-unit expression for the alternating output on an
even pair. The two factors are placed on the actual neighbouring shifted
physical pairs. Source: Schumacher–Werner locMarg, lines 980–1008. -/
noncomputable def margolusAlternatingPairRule
    (hω : PropagatesWithin ω (Finset.Icc (-1) 1)) (x : ℤ)
    (K : Matrix (Fin (supportAlgebraMatrixSize hω (2 * (x + 1))) ×
        Fin (supportAlgebraMatrixSize hω (2 * (x + 1) + 1)))
      (Fin (supportAlgebraMatrixSize hω (2 * (x + 1))) ×
        Fin (supportAlgebraMatrixSize hω (2 * (x + 1) + 1))) ℂ) :
    QuasiLocalAlgebra d :=
  ∑ i, ∑ j, K i j •
    (matrixToQuasiLocalObservable d (rightPair x)
        (margolusOutputRule hω x (1 ⊗ₖ Matrix.single i.1 j.1 (1 : ℂ))) *
      matrixToQuasiLocalObservable d (rightPair (x + 1))
        (margolusOutputRule hω (x + 1) (Matrix.single i.2 j.2 (1 : ℂ) ⊗ₖ 1)))

private theorem single_prod_eq_smul_kronecker
    {p q : Type*} [DecidableEq p] [DecidableEq q]
    (i j : p × q) (z : ℂ) :
    Matrix.single i j z = z •
      (Matrix.single i.1 j.1 (1 : ℂ) ⊗ₖ Matrix.single i.2 j.2 (1 : ℂ)) := by
  rw [Matrix.single_kronecker_single, one_mul, Matrix.smul_single, smul_eq_mul, mul_one]

/-- The explicit alternating rule equals the actual QCA image for every
matrix in the intermediate input-pair coordinates. No local action or
factorization equality is a premise. Source: Schumacher–Werner locMarg,
lines 980–1008. -/
theorem margolusAlternatingPairRule_eq
    (hω : PropagatesWithin ω (Finset.Icc (-1) 1)) (x : ℤ)
    (K : Matrix (Fin (supportAlgebraMatrixSize hω (2 * (x + 1))) ×
        Fin (supportAlgebraMatrixSize hω (2 * (x + 1) + 1)))
      (Fin (supportAlgebraMatrixSize hω (2 * (x + 1))) ×
        Fin (supportAlgebraMatrixSize hω (2 * (x + 1) + 1))) ℂ) :
    ω (matrixToQuasiLocalObservable d (evenPair (x + 1))
      ((margolusInputRule hω (x + 1)).symm K)) =
      margolusAlternatingPairRule hω x K := by
  classical
  unfold margolusAlternatingPairRule
  conv_lhs => rw [Matrix.matrix_eq_sum_single K]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [single_prod_eq_smul_kronecker, map_smul, map_smul, map_smul,
    margolus_alternating_kronecker]

/-- Every actual physical even-pair matrix has the explicit alternating
output formula. Source: Schumacher–Werner locMarg, bruleU and bruleV,
lines 980–1008. -/
theorem margolusAlternatingPairRule_input
    (hω : PropagatesWithin ω (Finset.Icc (-1) 1)) (x : ℤ)
    (A : Matrix (Config d (evenPair (x + 1))) (Config d (evenPair (x + 1))) ℂ) :
    ω (matrixToQuasiLocalObservable d (evenPair (x + 1)) A) =
      margolusAlternatingPairRule hω x (margolusInputRule hω (x + 1) A) := by
  simpa only [StarAlgEquiv.symm_apply_apply] using
    margolusAlternatingPairRule_eq hω x (margolusInputRule hω (x + 1) A)

/-- The explicit alternating pair rules have one and only one continuous
star-algebra action on the whole quasi-local algebra. It is the actual
original QCA action. Existence has no assumed action or compatibility
premise: the full pair formula was derived first; even-pair generation
and completion density give uniqueness.
Source: Schumacher–Werner locMarg and Lemma localrule, lines 341–365
and 980–1008. -/
theorem existsUnique_margolus_local_extension
    (hω : PropagatesWithin ω (Finset.Icc (-1) 1)) :
    ∃! F : QuasiLocalAlgebra d →⋆ₐ[ℂ] QuasiLocalAlgebra d,
      Continuous F ∧ ∀ (x : ℤ)
        (A : Matrix (Config d (evenPair (x + 1))) (Config d (evenPair (x + 1))) ℂ),
        F (matrixToQuasiLocalObservable d (evenPair (x + 1)) A) =
          margolusAlternatingPairRule hω x (margolusInputRule hω (x + 1) A) := by
  refine ⟨ω.toStarAlgHom, ⟨ω.isometry.continuous, ?_⟩, ?_⟩
  · exact margolusAlternatingPairRule_input hω
  · intro F hF
    apply quasiLocalStarAlgHom_ext_evenPair F ω.toStarAlgHom hF.1 ω.isometry.continuous
    intro x A
    have hpair (y : ℤ)
        (B : Matrix (Config d (evenPair (y + 1))) (Config d (evenPair (y + 1))) ℂ) :
        F (matrixToQuasiLocalObservable d (evenPair (y + 1)) B) =
          ω (matrixToQuasiLocalObservable d (evenPair (y + 1)) B) :=
      (hF.2 y B).trans (margolusAlternatingPairRule_input hω y B).symm
    have hx : ∀ B : Matrix (Config d (evenPair x)) (Config d (evenPair x)) ℂ,
        F (matrixToQuasiLocalObservable d (evenPair x) B) =
          ω (matrixToQuasiLocalObservable d (evenPair x) B) := by
      simpa only [sub_add_cancel] using hpair (x - 1)
    simpa only [matrixToQuasiLocalObservable, StarAlgHom.comp_apply,
      StarAlgEquiv.apply_symm_apply] using hx (CStarMatrix.ofMatrixStarAlgEquiv.symm A)

/-- Translation compatibility is agreement with the original QCA at
all translated blocks, derived from its actual covariance. No constraint
on an arbitrary pair of gates is substituted for that requirement.
Source: Schumacher–Werner, lines 1033–1041. -/
theorem margolusAlternatingPairRule_translation
    (hω : PropagatesWithin ω (Finset.Icc (-1) 1))
    (hcov : TranslationCovariant ω) (t x : ℤ)
    (A : Matrix (Config d (evenPair (x + 1))) (Config d (evenPair (x + 1))) ℂ) :
    ω (quasiLocalTranslation d t
      (matrixToQuasiLocalObservable d (evenPair (x + 1)) A)) =
      quasiLocalTranslation d t
        (margolusAlternatingPairRule hω x (margolusInputRule hω (x + 1) A)) := by
  rw [(translationCovariant_iff ω).mp hcov t,
    margolusAlternatingPairRule_input]

end SpinChain.PropagatesWithin
