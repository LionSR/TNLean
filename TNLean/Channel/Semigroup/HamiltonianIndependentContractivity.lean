/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Channel.Semigroup.RelaxationConditions
import TNLean.Channel.Semigroup.LindbladForm.GKSLTheorem
import TNLean.Channel.Semigroup.ReducibleQDS.Equivalence

/-!
# Algebraic companion to the Hamiltonian-independent contractivity conjecture

This file kernel-checks algebraic and finite-dimensional pieces surrounding the
conjecture posed by Wolff--Malz--Trivedi, arXiv:2602.16067v1, Section "Outlook
and open questions", lines 853--855 of the source.  It does **not** formalize or
claim the full analytic Hamiltonian-independent contractivity conjecture.

The invariant-subspace statements below formalize the Outlook observation on
source line 855: full adjoint-free jump algebra generation makes every frozen
driven Lindbladian irreducible.  The explicit four-dimensional computation is
relevant to the trace-norm right-derivative formula of Proposition 19 (source
lines 615--635): full generation does not by itself make every instantaneous
witness strictly decreasing.
-/

open scoped Matrix ComplexOrder BigOperators NNReal MatrixOrder TNOperatorSpace
open Matrix Finset Module

noncomputable section

variable {D : ℕ}

local notation "Mat" => Matrix (Fin D) (Fin D) ℂ

/-- Full adjoint-free jump generation leaves no nontrivial orthogonal
projection invariant under every jump.  This is the algebraic mechanism behind
the frozen-Hamiltonian observation in arXiv:2602.16067v1, Outlook, lines
853--855. -/
theorem full_jump_algebra_projection_eq_zero_or_one
    (F : LindbladForm D)
    (hGen : Algebra.adjoin ℂ (Set.range F.L) = ⊤)
    (P : Mat) (hP : IsOrthogonalProjection P)
    (hInv : ∀ j : Fin F.r, (1 - P) * F.L j * P = 0) :
    P = 0 ∨ P = 1 := by
  have hAdjoin : ∀ A : Mat, A ∈ Algebra.adjoin ℂ (Set.range F.L) →
      (1 - P) * A * P = 0 := by
    apply lower_left_block_vanishes_on_adjoin hP
    rintro A ⟨j, rfl⟩
    exact hInv j
  apply proj_zero_or_one_of_sandwich P
  intro A
  exact hAdjoin A (hGen ▸ Algebra.mem_top)

/-- Equivalently, every nontrivial orthogonal projection leaks through at least
one jump operator. -/
theorem exists_jump_leakage_of_full_algebra_generation
    (F : LindbladForm D)
    (hGen : Algebra.adjoin ℂ (Set.range F.L) = ⊤)
    (P : Mat) (hP : IsNontrivialProjection P) :
    ∃ j : Fin F.r, (1 - P) * F.L j * P ≠ 0 := by
  by_contra h
  push Not at h
  rcases full_jump_algebra_projection_eq_zero_or_one F hGen P hP.1 h with hP0 | hP1
  · exact hP.2.1 hP0
  · exact hP.2.2 hP1

/-- Full generation by the jumps alone excludes a block-upper-triangular
Lindblad decomposition for every choice of the frozen Hamiltonian encoded in
`F`.  Compare arXiv:2602.16067v1, Outlook, line 855. -/
theorem full_jump_algebra_implies_no_blockUpperTriangular
    (F : LindbladForm D)
    (hGen : Algebra.adjoin ℂ (Set.range F.L) = ⊤) :
    ¬ HasBlockUpperTriangularLindblad F.toLinearMap := by
  apply full_algebra_generation_implies_no_blockUpperTriangular F
  apply top_unique
  rw [← hGen]
  exact Algebra.adjoin_mono Set.subset_union_left

/-- The corresponding frozen Lindblad generator is non-reducible.  Since `F`
is arbitrary, this applies to every frozen Hamiltonian with the same
full-algebra-generating jump family. -/
theorem full_jump_algebra_implies_not_isReducibleQDS
    (F : LindbladForm D)
    (hGen : Algebra.adjoin ℂ (Set.range F.L) = ⊤) :
    ¬ IsReducibleQDS F.toLinearMap := by
  have hGKSL : IsGKSLGenerator F.toLinearMap :=
    (gksl_iff_ccp_and_traceAnnihilating F.toLinearMap).2
      ⟨F.isCCP, F.isTraceAnnihilating⟩
  apply not_isReducibleQDS_of_no_blockUpperTriangular_lindblad hGKSL
  exact full_jump_algebra_implies_no_blockUpperTriangular F hGen

namespace HICFourDimensionalExample

abbrev Mat4 := Matrix (Fin 4) (Fin 4) ℂ

/-- The standard matrix unit $E_{ij}$, with zero-based Lean indices. -/
def e (i j : Fin 4) : Mat4 := Matrix.single i j 1

/-- $A=E_{21}+E_{32}+E_{14}$ in one-based mathematical notation. -/
def A : Mat4 := e 1 0 + e 2 1 + e 0 3

/-- $B=E_{43}$ in one-based mathematical notation. -/
def B : Mat4 := e 3 2

private lemma A_cube : A ^ 3 = e 2 3 := by
  simp [A, e, pow_succ, Matrix.mul_add, Matrix.add_mul]

/-- The two matrices generate all sixteen standard matrix units and hence the
full unital algebra $M_4(ℂ)$. -/
theorem adjoin_A_B_eq_top : Algebra.adjoin ℂ ({A, B} : Set Mat4) = ⊤ := by
  let S : Subalgebra ℂ Mat4 := Algebra.adjoin ℂ ({A, B} : Set Mat4)
  have hA : A ∈ S := Algebra.subset_adjoin (by simp)
  have hB : B ∈ S := Algebra.subset_adjoin (by simp)
  have h23 : e 2 3 ∈ S := by
    rw [← A_cube]
    exact S.pow_mem hA 3
  have h22 : e 2 2 ∈ S := by
    simpa [e, B] using S.mul_mem h23 hB
  have h33 : e 3 3 ∈ S := by
    simpa [e, B] using S.mul_mem hB h23
  have h21 : e 2 1 ∈ S := by
    simpa [e, A, Matrix.mul_add] using S.mul_mem h22 hA
  have h03 : e 0 3 ∈ S := by
    simpa [e, A, Matrix.add_mul] using S.mul_mem hA h33
  have h10 : e 1 0 ∈ S := by
    have := S.sub_mem (S.sub_mem hA h21) h03
    simpa [A, sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using this
  have hunit_mul (i j k : Fin 4) (hij : e i j ∈ S) (hjk : e j k ∈ S) :
      e i k ∈ S := by
    simpa [e, Matrix.single_mul_single_same] using S.mul_mem hij hjk
  have hsingle : ∀ i j : Fin 4, e i j ∈ S := by
    intro i j
    fin_cases i <;> fin_cases j
    · exact hunit_mul 0 3 0 h03 (hunit_mul 3 2 0 hB (hunit_mul 2 1 0 h21 h10))
    · exact hunit_mul 0 3 1 h03 (hunit_mul 3 2 1 hB h21)
    · exact hunit_mul 0 3 2 h03 hB
    · exact h03
    · exact h10
    · exact hunit_mul 1 0 1 h10 (hunit_mul 0 3 1 h03 (hunit_mul 3 2 1 hB h21))
    · exact hunit_mul 1 0 2 h10 (hunit_mul 0 3 2 h03 hB)
    · exact hunit_mul 1 0 3 h10 h03
    · exact hunit_mul 2 1 0 h21 h10
    · exact h21
    · exact h22
    · exact hunit_mul 2 1 3 h21 (hunit_mul 1 0 3 h10 h03)
    · exact hunit_mul 3 2 0 hB (hunit_mul 2 1 0 h21 h10)
    · exact hunit_mul 3 2 1 hB h21
    · exact hB
    · exact h33
  have hSub : S.toSubmodule = ⊤ :=
    (Submodule.eq_top_iff_forall_basis_mem (Matrix.stdBasis ℂ (Fin 4) (Fin 4))).2
      (fun ij => by
        rw [Matrix.stdBasis_eq_single]
        exact hsingle ij.1 ij.2)
  change S = ⊤
  apply top_unique
  intro M _
  change M ∈ S.toSubmodule
  rw [hSub]
  exact Submodule.mem_top

/-- The traceless Hermitian witness $x=E_{11}-E_{33}$. -/
def x : Mat4 := e 0 0 - e 2 2

/-- Exact dissipator calculation for the four-dimensional family.  Its two
middle positive diagonal entries and two outer negative entries show directly
that full jump generation does not automatically provide a pointwise strict
trace-norm derivative argument of the kind computed in Proposition 19 of
arXiv:2602.16067v1 (source lines 615--635). -/
theorem dissipator_sum_x :
    dissipator A x + dissipator B x =
      -e 0 0 + e 1 1 + e 2 2 - e 3 3 := by
  simp only [dissipator, A, e, Fin.isValue, x, Matrix.mul_sub, Matrix.add_mul,
    Matrix.single_mul_single_same, mul_one, ne_eq, one_ne_zero, not_false_eq_true,
    Matrix.single_mul_single_of_ne, add_zero, Fin.reduceEq, sub_zero,
    Matrix.conjTranspose_add, Matrix.conjTranspose_single, star_one, Matrix.mul_add,
    zero_ne_one, one_div, zero_add, Matrix.smul_single, smul_eq_mul, Matrix.sub_mul,
    sub_self, B, zero_sub, neg_mul, smul_neg, sub_neg_eq_add]
  have hhalf (i : Fin 4) :
      Matrix.single i i (2 : ℂ)⁻¹ = (2 : ℂ)⁻¹ • e i i := by
    simp [e]
  rw [hhalf 0, hhalf 2]
  norm_num
  change e 1 1 - (1 / 2 : ℂ) • e 0 0 - (1 / 2 : ℂ) • e 0 0 +
      (-e 3 3 + (1 / 2 : ℂ) • e 2 2 + (1 / 2 : ℂ) • e 2 2) =
    -e 0 0 + e 1 1 + e 2 2 - e 3 3
  module

end HICFourDimensionalExample

end
