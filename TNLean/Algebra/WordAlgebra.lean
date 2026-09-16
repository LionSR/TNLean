/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.FreeMonoid.Basic
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.LinearAlgebra.Trace
import Mathlib.RingTheory.SimpleModule.Rank

/-!
# The word algebra of a finite alphabet

This file introduces the free unital associative algebra `F = ℂ⟨x_1, …, x_d⟩` used in the
positive-word character theory of the asymmetric fundamental theorem
(`Notes/OpenProblemsTN/problems/p5_asymmetric_fundamental_theorem.tex`, §7.4,
eq:p5-free-algebra and eq:p5-positive-ideal), realized as the monoid algebra of the free monoid
on `Fin d`, so that the nonempty words are a basis.

## Main definitions

* `WordAlgebra d`: the monoid algebra `MonoidAlgebra ℂ (FreeMonoid (Fin d))`.
* `WordAlgebra.ofWord w`: the basis element of the word `w : List (Fin d)`.
* `WordAlgebra.aug`: the augmentation, the algebra map sending every generator to `0`; its kernel
  is the two-sided ideal `F₊` of polynomials without constant term.
* `WordAlgebra.actAlgHom M`: the action of the word algebra on a module `M` by `ℂ`-linear
  endomorphisms, and the trace character `WordAlgebra.traceChar M` together with the word
  traces `WordAlgebra.traceWord M w`.

## Main results

* `WordAlgebra.linearMap_eq_on_ker_aug`: two linear functionals agreeing on every nonempty
  word agree on the kernel of the augmentation.
* `WordAlgebra.smul_eq_aug_smul`: when every generator acts as zero, the word algebra acts
  through the augmentation.
* `WordAlgebra.finrank_eq_one_of_isSimpleModule_of_forall_smul_eq_zero`: a simple module on
  which every generator acts as zero is one-dimensional (the one-dimensional zero module
  of the source).
-/

/-- The word algebra on the alphabet `Fin d`: the monoid algebra of the free monoid, i.e. the
free unital associative `ℂ`-algebra on `d` generators with the words as a basis. -/
abbrev WordAlgebra (d : ℕ) := MonoidAlgebra ℂ (FreeMonoid (Fin d))

namespace WordAlgebra

variable {d : ℕ}

/-- The basis element of the word `w`. -/
noncomputable def ofWord (w : List (Fin d)) : WordAlgebra d :=
  MonoidAlgebra.of ℂ (FreeMonoid (Fin d)) (FreeMonoid.ofList w)

@[simp] lemma ofWord_nil : ofWord ([] : List (Fin d)) = 1 :=
  map_one (MonoidAlgebra.of ℂ (FreeMonoid (Fin d)))

lemma ofWord_append (u v : List (Fin d)) : ofWord (u ++ v) = ofWord u * ofWord v := by
  simp [ofWord, FreeMonoid.ofList_append]

lemma ofWord_cons (i : Fin d) (w : List (Fin d)) : ofWord (i :: w) = ofWord [i] * ofWord w := by
  rw [← ofWord_append]; rfl

lemma ofWord_eq_single (w : List (Fin d)) :
    ofWord w = MonoidAlgebra.single (FreeMonoid.ofList w) (1 : ℂ) := rfl

/-- The augmentation: the algebra map sending every generator to zero. Its kernel is the ideal
of polynomials with zero constant term (eq:p5-positive-ideal). -/
noncomputable def aug : WordAlgebra d →ₐ[ℂ] ℂ :=
  MonoidAlgebra.lift ℂ ℂ (FreeMonoid (Fin d)) (FreeMonoid.lift fun _ => (0 : ℂ))

lemma aug_ofWord (w : List (Fin d)) : aug (ofWord w) = if w = [] then 1 else 0 := by
  unfold aug ofWord
  rw [MonoidAlgebra.lift_of, FreeMonoid.lift_apply, FreeMonoid.toList_ofList]
  cases w with
  | nil => simp
  | cons i w => simp

@[simp] lemma aug_ofWord_nil : aug (ofWord ([] : List (Fin d))) = 1 := by simp

lemma aug_ofWord_of_ne_nil {w : List (Fin d)} (hw : w ≠ []) : aug (ofWord w) = 0 := by
  simp [aug_ofWord, hw]

lemma aug_mul_left {p : WordAlgebra d} (hp : aug p = 0) (q : WordAlgebra d) :
    aug (q * p) = 0 := by
  rw [map_mul, hp, mul_zero]

lemma aug_mul_right {p : WordAlgebra d} (hp : aug p = 0) (q : WordAlgebra d) :
    aug (p * q) = 0 := by
  rw [map_mul, hp, zero_mul]

lemma aug_pow {p : WordAlgebra d} (hp : aug p = 0) {n : ℕ} (hn : 0 < n) : aug (p ^ n) = 0 := by
  rw [map_pow, hp, zero_pow hn.ne']

/-- A linear functional is determined on the kernel of the augmentation by its values on the
nonempty words: the difference of two functionals agreeing there is a multiple of the
augmentation. -/
lemma sub_eq_aug_mul {χ₁ χ₂ : WordAlgebra d →ₗ[ℂ] ℂ}
    (h : ∀ w : List (Fin d), w ≠ [] → χ₁ (ofWord w) = χ₂ (ofWord w)) (p : WordAlgebra d) :
    χ₁ p - χ₂ p = (χ₁ 1 - χ₂ 1) * aug p := by
  induction p using MonoidAlgebra.induction_on with
  | of g =>
    change χ₁ (ofWord (FreeMonoid.toList g)) - χ₂ (ofWord (FreeMonoid.toList g)) =
      (χ₁ 1 - χ₂ 1) * aug (ofWord (FreeMonoid.toList g))
    rw [aug_ofWord]
    split_ifs with hw
    · rw [hw]; simp
    · rw [h _ hw]; simp
  | add f g hf hg => rw [map_add, map_add, map_add, mul_add, ← hf, ← hg]; ring
  | smul r f hf =>
    rw [map_smul, map_smul, map_smul, smul_eq_mul, smul_eq_mul, smul_eq_mul, ← mul_assoc,
      mul_comm _ r, mul_assoc, ← hf]
    ring

/-- Two linear functionals agreeing on every nonempty word agree on the kernel of the
augmentation (eq:p5-main-positive-character). -/
lemma linearMap_eq_on_ker_aug {χ₁ χ₂ : WordAlgebra d →ₗ[ℂ] ℂ}
    (h : ∀ w : List (Fin d), w ≠ [] → χ₁ (ofWord w) = χ₂ (ofWord w)) {p : WordAlgebra d}
    (hp : aug p = 0) : χ₁ p = χ₂ p := by
  have := sub_eq_aug_mul h p
  rw [hp, mul_zero, sub_eq_zero] at this
  exact this

section Module

variable (M : Type*) [AddCommGroup M] [Module ℂ M] [Module (WordAlgebra d) M]
  [IsScalarTower ℂ (WordAlgebra d) M]

/-- The action of the word algebra on `M` by `ℂ`-linear endomorphisms. -/
noncomputable def actAlgHom : WordAlgebra d →ₐ[ℂ] Module.End ℂ M := Algebra.lsmul ℂ ℂ M

@[simp] lemma actAlgHom_apply (p : WordAlgebra d) (m : M) : actAlgHom M p m = p • m := rfl

/-- The trace character `p ↦ tr (ρ_M p)` of the module `M`. -/
noncomputable def traceChar : WordAlgebra d →ₗ[ℂ] ℂ :=
  (LinearMap.trace ℂ M).comp (actAlgHom M).toLinearMap

lemma traceChar_apply (p : WordAlgebra d) :
    traceChar M p = LinearMap.trace ℂ M (actAlgHom M p) := rfl

/-- The trace of the action of the word `w`. -/
noncomputable def traceWord (w : List (Fin d)) : ℂ := traceChar M (ofWord w)

lemma traceWord_def (w : List (Fin d)) :
    traceWord M w = LinearMap.trace ℂ M (actAlgHom M (ofWord w)) := rfl

variable {M}

/-- Trace characters agreeing on all nonempty words agree on the kernel of the augmentation.
This is the linear extension step eq:p5-main-positive-character of the main proof, stated for an
arbitrary second functional so that finite sums of characters are covered. -/
lemma traceChar_eq_of_traceWord_eq {χ : WordAlgebra d →ₗ[ℂ] ℂ}
    (h : ∀ w : List (Fin d), w ≠ [] → traceWord M w = χ (ofWord w)) {p : WordAlgebra d}
    (hp : aug p = 0) : traceChar M p = χ p :=
  linearMap_eq_on_ker_aug h hp

/-- If every generator acts as zero on `M`, the word algebra acts through the augmentation. -/
lemma smul_eq_aug_smul (h0 : ∀ (i : Fin d) (m : M), (ofWord [i] : WordAlgebra d) • m = 0)
    (p : WordAlgebra d) (m : M) : p • m = aug p • m := by
  have key : actAlgHom (d := d) M = (Algebra.ofId ℂ (Module.End ℂ M)).comp aug := by
    refine MonoidAlgebra.algHom_ext ?_ (Subsingleton.elim _ _)
    intro g
    change actAlgHom M (ofWord (FreeMonoid.toList g)) =
      (Algebra.ofId ℂ (Module.End ℂ M)) (aug (ofWord (FreeMonoid.toList g)))
    rw [aug_ofWord]
    generalize FreeMonoid.toList g = w
    cases w with
    | nil => simp
    | cons i w =>
      simp only [reduceCtorEq, ite_false, map_zero]
      ext m
      rw [ofWord_cons, map_mul, Module.End.mul_apply, actAlgHom_apply, actAlgHom_apply, h0]
      simp
  have := congrArg (fun f : WordAlgebra d →ₐ[ℂ] Module.End ℂ M => f p m) key
  simpa [Algebra.ofId_apply] using this

/-- A simple module on which every generator acts as zero is one-dimensional over `ℂ`: it is
the one-dimensional zero module of the source (Lemma 7.5 of the P5 note, final
paragraph). -/
lemma finrank_eq_one_of_isSimpleModule_of_forall_smul_eq_zero
    [IsSimpleModule (WordAlgebra d) M]
    (h0 : ∀ (i : Fin d) (m : M), (ofWord [i] : WordAlgebra d) • m = 0) :
    Module.finrank ℂ M = 1 := by
  rw [← isSimpleModule_iff_finrank_eq_one, isSimpleModule_iff]
  let e : Submodule (WordAlgebra d) M ≃o Submodule ℂ M :=
    { toFun := Submodule.restrictScalars ℂ
      invFun := fun N =>
        { carrier := N
          add_mem' := fun ha hb => N.add_mem ha hb
          zero_mem' := N.zero_mem
          smul_mem' := fun p m hm => by
            change p • m ∈ N
            rw [smul_eq_aug_smul h0]
            exact N.smul_mem _ hm }
      left_inv := fun K => by ext; rfl
      right_inv := fun N => by ext; rfl
      map_rel_iff' := fun {K₁ K₂} => Submodule.restrictScalars_le ℂ }
  have : Nontrivial (Submodule ℂ M) := e.symm.toEquiv.nontrivial
  refine ⟨fun N => ?_⟩
  rcases IsSimpleOrder.eq_bot_or_eq_top (e.symm N) with hN | hN
  · left
    simpa using congrArg e hN
  · right
    simpa using congrArg e hN

end Module

end WordAlgebra
