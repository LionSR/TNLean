/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Basic.Complex.Basic
import TNLean.Algebra.MonomialMatrix
import TNLean.Algebra.MatrixSingleSpan
import Mathlib.Algebra.Group.Int.Units
import Mathlib.Algebra.GroupWithZero.Units.Fintype

/-!
# Finite signed permutation representations spanning matrix algebras

Signed permutation matrices form a finite subgroup of the unitary group. Every
matrix unit is a half-difference of two such matrices, so their complex span is
the full matrix algebra. This supplies finite groups of prescribed irreducible
matrix size for the construction in SCP10, Theorem 4.1
(arXiv:1001.3807, local source lines 852–885).
-/

open scoped Matrix
open Matrix
noncomputable section
namespace TNLean

variable (ι : Type*) [Fintype ι] [DecidableEq ι]

private theorem intUnit_phase (u : ℤˣ) :
    star ((u : ℤ) : ℂ) * ((u : ℤ) : ℂ) = 1 := by
  simp only [star_intCast]
  norm_cast
  exact Int.isUnit_mul_self u.isUnit

/-- The finite subgroup of signed permutation matrices.
Source: SCP10, Theorem 4.1, finite-group construction in lines 868–882. -/
def signedPermutationSubgroup : Subgroup (Matrix.unitaryGroup ι ℂ) where
  carrier := {U | ∃ (σ : Equiv.Perm ι) (φ : ι → ℤˣ),
    (U : Matrix ι ι ℂ) = Matrix.monomial σ (fun i => ((φ i : ℤ) : ℂ))}
  one_mem' := by
    refine ⟨1, fun _ => 1, ?_⟩
    simpa using (Matrix.monomial_one (ι := ι) (R := ℂ)).symm
  mul_mem' := by
    rintro U V ⟨σ, φ, hU⟩ ⟨τ, ψ, hV⟩
    refine ⟨σ * τ, fun i => φ (τ i) * ψ i, ?_⟩
    change (U : Matrix ι ι ℂ) * (V : Matrix ι ι ℂ) = _
    rw [hU, hV, Matrix.monomial_mul_monomial]
    simp only [Units.val_mul, Int.cast_mul]
  inv_mem' := by
    rintro U ⟨σ, φ, hU⟩
    refine ⟨σ.symm, fun i => φ (σ.symm i), ?_⟩
    change star (U : Matrix ι ι ℂ) = _
    rw [hU, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_monomial]
    simp only [star_intCast]

instance instFiniteSignedPermutationSubgroup : Finite (signedPermutationSubgroup ι) := by
  let f : Equiv.Perm ι × (ι → ℤˣ) → Matrix ι ι ℂ :=
    fun p => Matrix.monomial p.1 (fun i => ((p.2 i : ℤ) : ℂ))
  let : Finite (Set.range f) := (Set.finite_range f).to_subtype
  apply Finite.of_injective (fun g : signedPermutationSubgroup ι =>
    (⟨(g.1 : Matrix ι ι ℂ), by
      obtain ⟨σ, φ, h⟩ := g.2
      exact ⟨(σ, φ), h.symm⟩⟩ : Set.range f))
  intro g h he
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun z : Set.range f => z.1) he

/-- The defining representation of signed permutation matrices.
Source: SCP10, Theorem 4.1, finite-group construction in lines 868–882. -/
def signedPermutationRepresentation : signedPermutationSubgroup ι →* Matrix ι ι ℂ :=
  (Matrix.unitaryGroup ι ℂ).subtype.comp (signedPermutationSubgroup ι).subtype

/-- Every signed permutation matrix is unitary.
Source: SCP10, Theorem 4.1, finite-group construction in lines 868–882. -/
theorem signedPermutationRepresentation_mem_unitaryGroup (g : signedPermutationSubgroup ι) :
    signedPermutationRepresentation ι g ∈ Matrix.unitaryGroup ι ℂ := g.1.2

/-- Signed monomial matrices are exactly the range of the defining representation.
Source: SCP10, Theorem 4.1, finite-group construction in lines 868–882. -/
theorem signedPermutationRepresentation_range (M : Matrix ι ι ℂ) :
    M ∈ Set.range (signedPermutationRepresentation ι) ↔
      ∃ (σ : Equiv.Perm ι) (φ : ι → ℤˣ),
        M = Matrix.monomial σ (fun i => ((φ i : ℤ) : ℂ)) := by
  constructor
  · rintro ⟨g, rfl⟩
    exact g.2
  · rintro ⟨σ, φ, rfl⟩
    exact ⟨⟨⟨_, Matrix.monomial_mem_unitaryGroup σ _ (fun i => intUnit_phase (φ i))⟩,
      σ, φ, rfl⟩, rfl⟩

/-- Every matrix unit is a half-difference of two signed permutation matrices.
Source: SCP10, Theorem 4.1, finite-group construction in lines 868–882. -/
theorem exists_signedPermutationRepresentation_sub_eq_single (i j : ι) :
    ∃ g h : signedPermutationSubgroup ι,
      (1 / 2 : ℂ) • (signedPermutationRepresentation ι g -
        signedPermutationRepresentation ι h) = Matrix.single i j 1 := by
  let σ := Equiv.swap i j
  let φ : ι → ℤˣ := fun k => if k = j then -1 else 1
  let P : Matrix ι ι ℂ := Matrix.monomial σ (fun _ => 1)
  let Q : Matrix ι ι ℂ := Matrix.monomial σ (fun k => ((φ k : ℤ) : ℂ))
  obtain ⟨g, hg⟩ := (signedPermutationRepresentation_range ι P).mpr
    ⟨σ, fun _ => 1, by simp [P]⟩
  obtain ⟨h, hh⟩ := (signedPermutationRepresentation_range ι Q).mpr ⟨σ, φ, rfl⟩
  have hunit : (1 / 2 : ℂ) • (P - Q) = Matrix.single i j 1 := by
    ext k l
    by_cases hl : l = j
    · subst l
      by_cases hk : k = i
      · subst k
        norm_num [P, Q, σ, φ, Matrix.monomial_apply, Matrix.single_apply]
      · simp [P, Q, σ, φ, Matrix.monomial_apply, hk, Ne.symm hk]
    · simp [P, Q, φ, Matrix.monomial_apply, hl, Ne.symm hl]
  exact ⟨g, h, by rw [hg, hh]; exact hunit⟩

/-- The signed permutation representation spans the full complex matrix algebra.
Source: SCP10, Theorem 4.1, finite-group construction in lines 868–882. -/
theorem span_signedPermutationRepresentation :
    Submodule.span ℂ (Set.range (signedPermutationRepresentation ι)) = ⊤ := by
  apply Submodule.eq_top_of_forall_single_mem
  intro i j
  obtain ⟨g, h, he⟩ := exists_signedPermutationRepresentation_sub_eq_single ι i j
  rw [← he]
  exact (Submodule.span ℂ (Set.range (signedPermutationRepresentation ι))).smul_mem _
    (Submodule.sub_mem _ (Submodule.subset_span ⟨g, rfl⟩)
      (Submodule.subset_span ⟨h, rfl⟩))

end TNLean
