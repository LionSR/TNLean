/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.QCA.AlgebraicTranslation
import TNLean.QCA.QuasiLocal

/-!
# Translations of quasi-local observables

Operator-norm isometries of the algebraic local algebra extend continuously to its completion.
Thus lattice translations induce an additive action on the quasi-local observable algebra by
star-algebra equivalences. The extension agrees with algebraic-local and finite-region translation
on the dense local subalgebra and preserves the operator norm.

This file concerns translations of quasi-local observables only. It does not define finite support
in the completion, finite propagation, translation covariance, or quantum cellular automata.

## Main definitions

* `SpinChain.quasiLocalTranslation` — quasi-local translation as a star-algebra equivalence.

## Main results

* `SpinChain.quasiLocalTranslation_algebraicToQuasiLocal` — evaluation on the dense algebraic
  subalgebra.
* `SpinChain.quasiLocalTranslation_quasiLocalObservable` — evaluation on a finite-region
  representative.
* `SpinChain.quasiLocalTranslation_zero`, `SpinChain.quasiLocalTranslation_add`, and
  `SpinChain.quasiLocalTranslation_symm` — the additive action in composition form.
* `SpinChain.quasiLocalTranslation_one`, `SpinChain.quasiLocalTranslation_mul`, and
  `SpinChain.quasiLocalTranslation_inv` — the same action in automorphism-group form.
* `SpinChain.norm_quasiLocalTranslation` and `SpinChain.quasiLocalTranslation_isometry` — norm
  and distance preservation.

## References

* Cirac--Perez-Garcia--Schuch--Verstraete, arXiv:1703.09188, Appendix, lines 2292--2306.
* Schumacher--Werner, quant-ph/0405174, Definition 1.
-/

open scoped ComplexOrder

namespace SpinChain

attribute [local instance] CStarMatrix.instNorm CStarMatrix.instNormedAddCommGroup
  CStarMatrix.instNormedRing CStarMatrix.instCStarRing

/-- Translation by a lattice displacement extends from algebraic-local observables to a
star-algebra equivalence of the quasi-local algebra.

Source context: arXiv:1703.09188, Appendix, lines 2292--2296 construct the quasi-local
completion, while line 2298 invokes its translation operator in the definition of a QCA and line
2306 invokes translation covariance. The extension below supplies that background operator; it is
not stated separately in the appendix. -/
noncomputable def quasiLocalTranslation (d : ℕ) [NeZero d] (a : ℤ) :
    QuasiLocalAlgebra d ≃⋆ₐ[ℂ] QuasiLocalAlgebra d :=
  UniformSpace.Completion.mapStarAlgEquiv
    (algebraicLocalTranslation d a)
    (algebraicLocalTranslation_isometry d a).continuous
    (by
      rw [algebraicLocalTranslation_symm]
      exact (algebraicLocalTranslation_isometry d (-a)).continuous)

/-- Quasi-local translation acts by the completion map of algebraic-local translation. -/
lemma quasiLocalTranslation_apply (d : ℕ) [NeZero d] (a : ℤ)
    (A : QuasiLocalAlgebra d) :
    quasiLocalTranslation d a A =
      UniformSpace.Completion.map (algebraicLocalTranslation d a) A :=
  rfl

/-- Quasi-local translation agrees with algebraic-local translation on the dense algebraic
subalgebra.

Source context: this is the dense-subalgebra formula underlying the translation operator invoked in
arXiv:1703.09188, Appendix, line 2298; the formula is not displayed separately there. -/
@[simp]
lemma quasiLocalTranslation_algebraicToQuasiLocal (d : ℕ) [NeZero d] (a : ℤ)
    (A : AlgebraicLocalAlgebra d) :
    quasiLocalTranslation d a (algebraicToQuasiLocal d A) =
      algebraicToQuasiLocal d (algebraicLocalTranslation d a A) :=
  UniformSpace.Completion.mapStarAlgEquiv_coe _ _ _ A

/-- Quasi-local translation sends a finite-region representative to its translated
representative.

Source context: this is the finite-region formula underlying the translation operator invoked in
arXiv:1703.09188, Appendix, line 2298; the formula is not displayed separately there. -/
lemma quasiLocalTranslation_quasiLocalObservable (d : ℕ) [NeZero d] (a : ℤ)
    (Λ : Finset ℤ) (A : LocalAlgebra d Λ) :
    quasiLocalTranslation d a (quasiLocalObservable d Λ A) =
      quasiLocalObservable d (translateRegion a Λ) (localTranslation d a Λ A) := by
  rw [quasiLocalObservable, quasiLocalObservable, StarAlgHom.comp_apply,
    StarAlgHom.comp_apply, quasiLocalTranslation_algebraicToQuasiLocal,
    algebraicLocalTranslation_localObservable]

/-- Translation by zero is the identity on the quasi-local algebra.

Source context: the group-action laws are implicit in the translation operator invoked in
arXiv:1703.09188, Appendix, line 2298; they are not stated separately there. -/
@[simp]
lemma quasiLocalTranslation_zero (d : ℕ) [NeZero d] :
    quasiLocalTranslation d 0 = StarAlgEquiv.refl ℂ (QuasiLocalAlgebra d) := by
  apply StarAlgEquiv.ext
  intro A
  induction A using UniformSpace.Completion.induction_on with
  | hp =>
      change IsClosed {A : QuasiLocalAlgebra d |
        UniformSpace.Completion.map (algebraicLocalTranslation d 0) A = A}
      exact isClosed_eq UniformSpace.Completion.continuous_map continuous_id
  | ih A =>
      change quasiLocalTranslation d 0 (algebraicToQuasiLocal d A) =
        algebraicToQuasiLocal d A
      simp

/-- Successive quasi-local translations compose by adding their displacements.

Source context: the group-action laws are implicit in the translation operator invoked in
arXiv:1703.09188, Appendix, line 2298; they are not stated separately there. -/
lemma quasiLocalTranslation_add (d : ℕ) [NeZero d] (a b : ℤ) :
    (quasiLocalTranslation d a).trans (quasiLocalTranslation d b) =
      quasiLocalTranslation d (a + b) := by
  apply StarAlgEquiv.ext
  intro A
  induction A using UniformSpace.Completion.induction_on with
  | hp =>
      change IsClosed {A : QuasiLocalAlgebra d |
        UniformSpace.Completion.map (algebraicLocalTranslation d b)
            (UniformSpace.Completion.map (algebraicLocalTranslation d a) A) =
          UniformSpace.Completion.map (algebraicLocalTranslation d (a + b)) A}
      exact isClosed_eq
        (UniformSpace.Completion.continuous_map.comp
          UniformSpace.Completion.continuous_map)
        UniformSpace.Completion.continuous_map
  | ih A =>
      change quasiLocalTranslation d b
          (quasiLocalTranslation d a (algebraicToQuasiLocal d A)) =
        quasiLocalTranslation d (a + b) (algebraicToQuasiLocal d A)
      simp only [quasiLocalTranslation_algebraicToQuasiLocal]
      rw [← StarAlgEquiv.trans_apply, algebraicLocalTranslation_add]

/-- The inverse of quasi-local translation by `a` is translation by `-a`.

Source context: the group-action laws are implicit in the translation operator invoked in
arXiv:1703.09188, Appendix, line 2298; they are not stated separately there. -/
@[simp]
lemma quasiLocalTranslation_symm (d : ℕ) [NeZero d] (a : ℤ) :
    (quasiLocalTranslation d a).symm = quasiLocalTranslation d (-a) := by
  apply StarAlgEquiv.ext
  intro A
  apply (quasiLocalTranslation d a).symm_apply_eq.mpr
  change A = quasiLocalTranslation d a (quasiLocalTranslation d (-a) A)
  rw [← StarAlgEquiv.trans_apply, quasiLocalTranslation_add, neg_add_cancel,
    quasiLocalTranslation_zero]
  rfl

/-- The product of quasi-local translations is translation by the displacements in reversed
order.

The reversal comes from automorphism multiplication: `ω * η` first applies `η` and then `ω`.
Source context: the group-action laws are implicit in the translation operator invoked in
arXiv:1703.09188, Appendix, line 2298; they are not stated separately there. -/
@[simp]
lemma quasiLocalTranslation_mul (d : ℕ) [NeZero d] (a b : ℤ) :
    quasiLocalTranslation d a * quasiLocalTranslation d b =
      quasiLocalTranslation d (b + a) := by
  simpa only [StarAlgEquiv.aut_mul] using quasiLocalTranslation_add d b a

/-- The group inverse of quasi-local translation by `a` is translation by `-a`.

Source context: the group-action laws are implicit in the translation operator invoked in
arXiv:1703.09188, Appendix, line 2298; they are not stated separately there. -/
@[simp]
lemma quasiLocalTranslation_inv (d : ℕ) [NeZero d] (a : ℤ) :
    (quasiLocalTranslation d a)⁻¹ = quasiLocalTranslation d (-a) := by
  rw [StarAlgEquiv.aut_inv, quasiLocalTranslation_symm]

/-- Quasi-local translation by zero is the identity automorphism.

Source context: the group-action laws are implicit in the translation operator invoked in
arXiv:1703.09188, Appendix, line 2298; they are not stated separately there. -/
@[simp]
lemma quasiLocalTranslation_one (d : ℕ) [NeZero d] :
    quasiLocalTranslation d 0 =
      (1 : QuasiLocalAlgebra d ≃⋆ₐ[ℂ] QuasiLocalAlgebra d) := by
  simpa only [StarAlgEquiv.aut_one] using quasiLocalTranslation_zero d

/-- Quasi-local translation preserves the operator norm.

Source context: the appendix invokes translation as an automorphism of the quasi-local algebra at
line 2298; norm preservation is a standard C-star algebra consequence, not a separate claim
there. -/
@[simp]
lemma norm_quasiLocalTranslation (d : ℕ) [NeZero d] (a : ℤ)
    (A : QuasiLocalAlgebra d) :
    ‖quasiLocalTranslation d a A‖ = ‖A‖ :=
  StarAlgEquiv.norm_map (quasiLocalTranslation d a) A

/-- Quasi-local translation is an operator-norm isometry.

Source context: the appendix invokes translation as an automorphism of the quasi-local algebra at
line 2298; isometry is a standard C-star algebra consequence, not a separate claim there. -/
lemma quasiLocalTranslation_isometry (d : ℕ) [NeZero d] (a : ℤ) :
    Isometry (quasiLocalTranslation d a) :=
  StarAlgEquiv.isometry (quasiLocalTranslation d a)

end SpinChain
