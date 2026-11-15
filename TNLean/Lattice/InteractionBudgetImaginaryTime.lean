/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.ExpConjugation
import TNLean.Circuit.LocalCircuit
import TNLean.Lattice.GraphDegreeGrowth
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Imaginary-time conjugation from per-site interaction budgets

For a finite family of operators on at most `k` sites, a per-site norm budget `g`
gives factorial growth of the actual commutator iterates, with rate `2 * g * k`.
Each first commutator is expanded separately before induction on its support union.
The resulting conjugation bound allows empty supports, zero local dimension,
zero budgets and arbitrary complex scalar energy shifts.

This is a conservative auxiliary to Arad, Kuwahara and Landau, arXiv:1406.3898,
Section 2.1, equations (1)–(4), and Section 3, Lemma 3.1. No positivity or
Hermiticity is assumed; the sharper positive-term source estimate is not asserted.
-/

open scoped BigOperators Matrix.Norms.L2Operator

namespace TNLean.Lattice

open QuantumCircuit

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] {q : ℕ}

/-- An observable on at most `k * r` sites has rising-factorial commutator growth.
The first local commutators have individual supports of size at most `k * (r + 1)`.
This is the support-union argument of AKL14, Section 3, with the general
commutator inequality in place of the positive-term improvement. -/
theorem norm_iterated_commutator_le_ascFactorial
    (X : κ → Finset ι) (h : κ → Matrix (ι → Fin q) (ι → Fin q) ℂ)
    (k : ℕ) (g : ℝ) (hg : 0 ≤ g)
    (hSupport : ∀ i, h i ∈ supportedOperators q (X i : Set ι))
    (hSize : ∀ i, (X i).card ≤ k)
    (hBudget : ∀ x, ∑ i ∈ Finset.univ.filter (fun i ↦ x ∈ X i), ‖h i‖ ≤ g)
    (m r : ℕ) (O : Matrix (ι → Fin q) (ι → Fin q) ℂ) (S : Finset ι)
    (hO : O ∈ supportedOperators q (S : Set ι)) (hS : S.card ≤ k * r) :
    ‖((fun A ↦ (∑ i, h i) * A - A * (∑ i, h i))^[m] O)‖ ≤
      (2 * g * k) ^ m * (r.ascFactorial m : ℝ) * ‖O‖ := by
  classical
  let ad : Matrix (ι → Fin q) (ι → Fin q) ℂ →L[ℂ]
      Matrix (ι → Fin q) (ι → Fin q) ℂ :=
    ContinuousLinearMap.mul ℂ _ (∑ i, h i) -
      (ContinuousLinearMap.mul ℂ _).flip (∑ i, h i)
  change ‖((ad : _ → _)^[m] O)‖ ≤ _
  induction m generalizing r O S with
  | zero => simp
  | succ m ih =>
    let active := Finset.univ.filter fun i ↦ ¬Disjoint (X i) S
    have hfirst : ad O = ∑ i ∈ active, (h i * O - O * h i) := by
      change (∑ i, h i) * O - O * (∑ i, h i) = _
      rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro i _ hi
      have hd : Disjoint (X i) S := by
        by_contra hd
        exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hd⟩)
      exact sub_eq_zero.mpr
        (commute_of_mem_supportedOperators (Finset.disjoint_coe.mpr hd) (hSupport i) hO).eq
    have hexpand : (ad : _ → _)^[m + 1] O =
        ∑ i ∈ active, (ad : _ → _)^[m] (h i * O - O * h i) := by
      rw [Function.iterate_succ_apply, hfirst]
      simpa only [ContinuousLinearMap.pow_apply_eq_iterate] using
        map_sum (ad ^ m) (fun i ↦ h i * O - O * h i) active
    have hlocal (i : κ) : h i * O - O * h i ∈
        supportedOperators q ((X i ∪ S : Finset ι) : Set ι) := by
      have hh := supportedOperators_mono
        (Finset.coe_subset.mpr (Finset.subset_union_left : X i ⊆ X i ∪ S)) (hSupport i)
      have ho := supportedOperators_mono
        (Finset.coe_subset.mpr (Finset.subset_union_right : S ⊆ X i ∪ S)) hO
      exact Submodule.sub_mem _ (mul_mem_supportedOperators hh ho)
        (mul_mem_supportedOperators ho hh)
    have hcard (i : κ) : (X i ∪ S).card ≤ k * (r + 1) := by
      calc
        (X i ∪ S).card ≤ (X i).card + S.card := Finset.card_union_le _ _
        _ ≤ k + k * r := Nat.add_le_add (hSize i) hS
        _ = k * (r + 1) := by ring
    have hweight : (∑ i ∈ active, ‖h i‖) ≤ (k : ℝ) * r * g := by
      calc
        (∑ i ∈ active, ‖h i‖) ≤ (S.card : ℝ) * g :=
          sum_weight_meeting_le_card_mul_budget X (fun i ↦ ‖h i‖)
            (fun i ↦ norm_nonneg _) g hBudget S active
            (fun i hi ↦ (Finset.mem_filter.mp hi).2)
        _ ≤ (k : ℝ) * r * g :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hS) hg
    have hcomm (i : κ) : ‖h i * O - O * h i‖ ≤ 2 * ‖h i‖ * ‖O‖ := by
      calc
        ‖h i * O - O * h i‖ ≤ ‖h i * O‖ + ‖O * h i‖ := norm_sub_le _ _
        _ ≤ ‖h i‖ * ‖O‖ + ‖O‖ * ‖h i‖ :=
          add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
        _ = 2 * ‖h i‖ * ‖O‖ := by ring
    calc
      ‖((ad : _ → _)^[m + 1] O)‖ =
          ‖∑ i ∈ active, (ad : _ → _)^[m] (h i * O - O * h i)‖ := by rw [hexpand]
      _ ≤ ∑ i ∈ active, ‖((ad : _ → _)^[m] (h i * O - O * h i))‖ := norm_sum_le _ _
      _ ≤ ∑ i ∈ active,
          (2 * g * k) ^ m * ((r + 1).ascFactorial m : ℝ) *
            (2 * ‖h i‖ * ‖O‖) := by
        apply Finset.sum_le_sum
        intro i _
        exact (ih (r + 1) (h i * O - O * h i) (X i ∪ S) (hlocal i) (hcard i)).trans
          (mul_le_mul_of_nonneg_left (hcomm i) (by positivity))
      _ = (2 * g * k) ^ m * ((r + 1).ascFactorial m : ℝ) *
          (2 * (∑ i ∈ active, ‖h i‖) * ‖O‖) := by
        simp only [Finset.mul_sum, Finset.sum_mul]
      _ ≤ (2 * g * k) ^ m * ((r + 1).ascFactorial m : ℝ) *
          (2 * ((k : ℝ) * r * g) * ‖O‖) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hweight (by norm_num)) (norm_nonneg O)
      _ = (2 * g * k) ^ (m + 1) * (r.ascFactorial (m + 1) : ℝ) * ‖O‖ := by
        have hr : (r.ascFactorial (m + 1) : ℝ) =
            r * ((r + 1).ascFactorial m : ℝ) := by
          exact_mod_cast (Nat.ascFactorial_succ (n := r) (k := m)).trans
            (Nat.succ_ascFactorial r m).symm
        rw [hr, pow_succ]
        ring

/-- A `k`-site observable has factorial growth at rate `2 * g * k` under the
actual finite interaction sum. AKL14, Section 3, conservative factor-two estimate. -/
theorem norm_iterated_commutator_le_factorial
    (X : κ → Finset ι) (h : κ → Matrix (ι → Fin q) (ι → Fin q) ℂ)
    (k : ℕ) (g : ℝ) (hg : 0 ≤ g)
    (hSupport : ∀ i, h i ∈ supportedOperators q (X i : Set ι))
    (hSize : ∀ i, (X i).card ≤ k)
    (hBudget : ∀ x, ∑ i ∈ Finset.univ.filter (fun i ↦ x ∈ X i), ‖h i‖ ≤ g)
    (O : Matrix (ι → Fin q) (ι → Fin q) ℂ) (S : Finset ι)
    (hO : O ∈ supportedOperators q (S : Set ι)) (hS : S.card ≤ k) (m : ℕ) :
    ‖((fun A ↦ (∑ i, h i) * A - A * (∑ i, h i))^[m] O)‖ ≤
      (2 * g * k) ^ m * (m.factorial : ℝ) * ‖O‖ := by
  simpa only [Nat.one_ascFactorial, mul_one] using
    norm_iterated_commutator_le_ascFactorial X h k g hg hSupport hSize hBudget
      m 1 O S hO (by simpa using hS)

/-- Short imaginary-time conjugation by a finite interaction sum, including any
complex scalar energy shift. AKL14, Section 3, conservative auxiliary to Lemma 3.1. -/
theorem norm_exp_conjugation_interactionBudget_shift_le_two
    (X : κ → Finset ι) (h : κ → Matrix (ι → Fin q) (ι → Fin q) ℂ)
    (k : ℕ) (g : ℝ) (hg : 0 ≤ g)
    (hSupport : ∀ i, h i ∈ supportedOperators q (X i : Set ι))
    (hSize : ∀ i, (X i).card ≤ k)
    (hBudget : ∀ x, ∑ i ∈ Finset.univ.filter (fun i ↦ x ∈ X i), ‖h i‖ ≤ g)
    (O : Matrix (ι → Fin q) (ι → Fin q) ℂ) (S : Finset ι)
    (hO : O ∈ supportedOperators q (S : Set ι)) (hS : S.card ≤ k)
    (z : ℂ) (t : ℝ) (ht : 0 ≤ t) (hsmall : (2 * g * k) * t ≤ 1 / 2) :
    let H := ∑ i, h i
    ‖NormedSpace.exp ((t : ℂ) • (H - z • 1)) * O *
      NormedSpace.exp (-((t : ℂ) • (H - z • 1)))‖ ≤ 2 * ‖O‖ := by
  intro H
  apply Matrix.norm_exp_conjugation_le_two_of_growth (H - z • 1) O
    (2 * g * k) t (by positivity) ht hsmall
  have had : (fun A ↦ (H - z • 1) * A - A * (H - z • 1)) =
      (fun A ↦ H * A - A * H) := by
    funext A
    simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
    abel
  intro m
  rw [had]
  exact norm_iterated_commutator_le_factorial X h k g hg hSupport hSize hBudget O S hO hS m

end TNLean.Lattice
