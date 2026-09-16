/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import TNLean.Algebra.IsNilpotentOfTracePow
import TNLean.MPS.FundamentalTheorem.Reduction.SimpleSeparation

/-!
# Identifying a simple quotient with a target block

The inductive proof of the multi-block asymmetric compression theorem
(`Notes/OpenProblemsTN/problems/p5_asymmetric_fundamental_theorem.tex`, §7.5) peels a simple
quotient `M ⧸ K` off a module `M` whose word traces are the sum of the word traces of a family
of normal blocks. This file proves that such a quotient, when some generator acts on it
nontrivially, is isomorphic to one of the blocks: otherwise a positive element separating the
quotient from the blocks would act on `M` with vanishing trace powers, hence nilpotently, while
acting as the identity on the quotient.

## Main results

* `WordAlgebra.traceChar_eq_sum_of_traceWord_eq`: the trace character of `M` on the positive
  ideal is the sum of the characters of the blocks.
* `MPSTensor.exists_linearEquiv_wordModule_of_isSimpleModule_quotient`: the identification.
-/

namespace WordAlgebra

variable {d : ℕ} {ι : Type*}

/-- On the positive ideal, the trace character of `M` is the sum of the trace characters of a
family of tensor modules whose word traces sum to those of `M`. -/
lemma traceChar_eq_sum_of_traceWord_eq (M : Type*) [AddCommGroup M] [Module ℂ M]
    [Module (WordAlgebra d) M] [IsScalarTower ℂ (WordAlgebra d) M]
    (S : Finset ι) {D : ι → ℕ} (C : ∀ s, MPSTensor d (D s))
    (htr : ∀ w : List (Fin d), w ≠ [] →
      traceWord M w = ∑ s ∈ S, Matrix.trace (Kraus.evalWord (C s) w))
    {p : WordAlgebra d} (hp : aug p = 0) :
    traceChar M p = ∑ s ∈ S, traceChar (C s).WordModule p := by
  have h : ∀ w : List (Fin d), w ≠ [] →
      traceWord M w = (∑ s ∈ S, traceChar (C s).WordModule) (ofWord w) := by
    intro w hw
    rw [htr w hw, LinearMap.sum_apply]
    exact Finset.sum_congr rfl fun s _ => (MPSTensor.traceChar_wordModule_ofWord (C s) w).symm
  rw [traceChar_eq_of_traceWord_eq h hp, LinearMap.sum_apply]

end WordAlgebra

namespace MPSTensor

open WordAlgebra

variable {d : ℕ} {ι : Type*}

/-- Identification of a simple quotient. Let `M` be a finite-dimensional module whose word
traces are the sums of the word traces of the tensor modules of a finite family of blocks `C s`
each of which is simple, and let `K` be a submodule with simple quotient on which some
generator acts nontrivially. Then the quotient is isomorphic to one of the blocks. -/
theorem exists_linearEquiv_wordModule_of_isSimpleModule_quotient
    (M : Type*) [AddCommGroup M] [Module ℂ M] [Module (WordAlgebra d) M]
    [IsScalarTower ℂ (WordAlgebra d) M] [FiniteDimensional ℂ M]
    (K : Submodule (WordAlgebra d) M) [IsSimpleModule (WordAlgebra d) (M ⧸ K)]
    (hQ : ∃ (i : Fin d) (q : M ⧸ K), (ofWord [i] : WordAlgebra d) • q ≠ 0)
    (S : Finset ι) {D : ι → ℕ} (C : ∀ s, MPSTensor d (D s))
    (hC : ∀ s ∈ S, IsSimpleModule (WordAlgebra d) (C s).WordModule)
    (htr : ∀ w : List (Fin d), w ≠ [] →
      traceWord M w = ∑ s ∈ S, Matrix.trace (Kraus.evalWord (C s) w)) :
    ∃ s ∈ S, Nonempty ((M ⧸ K) ≃ₗ[WordAlgebra d] (C s).WordModule) := by
  by_contra hcon
  have hne : ∀ s ∈ S, IsEmpty ((M ⧸ K) ≃ₗ[WordAlgebra d] (C s).WordModule) := by
    intro s hs
    refine ⟨fun e => hcon ⟨s, hs, ⟨e⟩⟩⟩
  obtain ⟨p, hp, hpQ, hpS⟩ :=
    exists_aug_eq_zero_of_forall_isEmpty_linearEquiv (M ⧸ K) hQ S C hC hne
  -- `p` acts as zero on every block, so all its trace powers on `M` vanish.
  have hzero : ∀ k : ℕ, 0 < k → LinearMap.trace ℂ M ((actAlgHom M p) ^ k) = 0 := by
    intro k hk
    rw [← map_pow, ← traceChar_apply, traceChar_eq_sum_of_traceWord_eq M S C htr (aug_pow hp hk)]
    refine Finset.sum_eq_zero fun s hs => ?_
    have h0 : actAlgHom (C s).WordModule p = 0 := by
      ext v
      simp [hpS s hs v]
    rw [traceChar_apply, map_pow, h0, zero_pow hk.ne', map_zero]
  obtain ⟨n, hn⟩ := LinearMap.isNilpotent_of_forall_trace_pow_eq_zero (actAlgHom M p) hzero
  -- `p ^ n` acts as zero on `M`, hence on the quotient, where `p` acts as the identity.
  have hpow : ∀ m : M, (p ^ n) • m = 0 := by
    intro m
    have := LinearMap.congr_fun hn m
    simpa [← map_pow] using this
  have hpowQ : ∀ (k : ℕ) (q : M ⧸ K), (p ^ k) • q = q := by
    intro k q
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, mul_smul, hpQ, ih]
  have : Subsingleton (M ⧸ K) := by
    refine ⟨fun q q' => ?_⟩
    obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective K q
    obtain ⟨m', rfl⟩ := Submodule.Quotient.mk_surjective K q'
    rw [← hpowQ n (Submodule.Quotient.mk m), ← hpowQ n (Submodule.Quotient.mk m'),
      ← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul, hpow, hpow]
  exact not_subsingleton_iff_nontrivial.2
    (IsSimpleModule.nontrivial (WordAlgebra d) (M ⧸ K)) this

end MPSTensor
