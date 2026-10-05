/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Circuit.ExpectationBounds
import TNLean.Circuit.GHZState
import TNLean.Circuit.SupportedMatrixElements

/-!
# Weighted GHZ vectors and separated correlations

In a weighted binary GHZ vector `a|0ᴺ⟩ + b|1ᴺ⟩`, observables with disjoint supports
and one unobserved site have connected correlation of modulus at most
`4 |a|² |b|²`. The unobserved site removes the off-diagonal branch matrix elements;
within either product branch the two expectations factor.
-/

open Matrix
open scoped BigOperators InnerProductSpace

namespace QuantumCircuit

variable {N : ℕ}

/-- A diagonal observable depending on one site's label is supported on that site. -/
theorem diagonal_comp_eval_mem_supportedOperators {d : ℕ} (i : Fin N) (f : Fin d → ℂ) :
    diagonal (fun σ : Fin N → Fin d => f (σ i)) ∈ supportedOperators d {i} := by
  let m : Fin N → Matrix (Fin d) (Fin d) ℂ :=
    fun j => diagonal (fun x => if j = i then f x else 1)
  have hm : ∀ j ∉ ({i} : Set (Fin N)), m j = 1 := by
    intro j hj
    have hji : j ≠ i := by simpa using hj
    simp [m, hji]
  have heq : rectKronecker m = diagonal (fun σ : Fin N → Fin d => f (σ i)) := by
    ext σ τ
    rw [rectKronecker_apply]
    by_cases h : σ = τ
    · subst τ
      simp [m]
    · obtain ⟨j, hj⟩ := Function.ne_iff.mp h
      rw [diagonal_apply_ne _ h]
      exact Finset.prod_eq_zero (Finset.mem_univ j) (diagonal_apply_ne _ hj)
  rw [← heq]
  exact rectKronecker_mem_supportedOperators hm

/-- A binary GHZ vector is the sum of its two constant computational-basis branches. -/
theorem ghzState_two_eq (a b : ℂ) :
    ghzState (M := N) ![a, b] =
      a • Pi.single (fun _ : Fin N => (0 : Fin 2)) 1 +
        b • Pi.single (fun _ : Fin N => (1 : Fin 2)) 1 := by
  change (fun s => ∑ j, (![a, b] : Fin 2 → ℂ) j *
    productVector (fun _ : Fin N => Pi.single j 1) s) = _
  simp only [Fin.sum_univ_two, productVector_single]
  rfl

/-- The two constant binary configurations differ on every nonempty chain. -/
theorem zero_config_ne_one [NeZero N] :
    (fun _ : Fin N => (0 : Fin 2)) ≠ (fun _ : Fin N => (1 : Fin 2)) := by
  intro h
  have := congrFun h 0
  norm_num at this

/-- The squared norm of a nonempty binary GHZ vector is the sum of its sector weights. -/
theorem norm_ghzState_two_sq {N : ℕ} [NeZero N] (a b : ℂ) :
    ‖(WithLp.toLp 2 (ghzState (M := N) ![a, b]) : EuclideanSpace ℂ (Fin N → Fin 2))‖ ^ 2 =
      ‖a‖ ^ 2 + ‖b‖ ^ 2 := by
  rw [ghzState_two_eq]
  change ‖a • (PiLp.single 2 (fun _ : Fin N => (0 : Fin 2)) (1 : ℂ) :
      EuclideanSpace ℂ (Fin N → Fin 2)) +
    b • (PiLp.single 2 (fun _ : Fin N => (1 : Fin 2)) (1 : ℂ) :
      EuclideanSpace ℂ (Fin N → Fin 2))‖ ^ 2 = _
  rw [norm_add_sq (𝕜 := ℂ)]
  simp [norm_smul, inner_smul_left, inner_smul_right, EuclideanSpace.inner_single_left,
    zero_config_ne_one]

/-- Scaling a binary GHZ vector scales both of its sector amplitudes. -/
theorem ghzState_smul_two {N : ℕ} (c a b : ℂ) :
    c • ghzState (M := N) ![a, b] = ghzState (M := N) ![c * a, c * b] := by
  simp only [ghzState_two_eq, smul_add, smul_smul]

/-- A GHZ vector is normalized when its two orthogonal branch weights sum to one. -/
theorem norm_ghzState_two [NeZero N] {a b : ℂ} (hab : star a * a + star b * b = 1) :
    ‖(WithLp.toLp 2 (ghzState (M := N) ![a, b]) :
      EuclideanSpace ℂ (Fin N → Fin 2))‖ = 1 := by
  have hnorm : expect (ghzState (M := N) ![a, b]) 1 = 1 := by
    rw [ghzState_two_eq, expect_smul_single_add_of_offDiag_zero a b
      (by simp [zero_config_ne_one]) (by simp [Ne.symm zero_config_ne_one])]
    simpa using hab
  rw [expect_eq_inner] at hnorm
  simp only [one_mulVec, inner_self_eq_norm_sq_to_K] at hnorm
  have hs : ‖(WithLp.toLp 2 (ghzState (M := N) ![a, b]) :
      EuclideanSpace ℂ (Fin N → Fin 2))‖ ^ 2 = 1 := by
    apply Complex.ofReal_injective
    simpa using hnorm
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 hs

/-- A diagonal observable reads the two constant configurations of the GHZ vector. -/
theorem expect_ghzState_two_diagonal [NeZero N] (a b : ℂ)
    (f : (Fin N → Fin 2) → ℂ) :
    expect (ghzState (M := N) ![a, b]) (diagonal f) =
      star a * a * f (fun _ => 0) + star b * b * f (fun _ => 1) := by
  rw [ghzState_two_eq, expect_smul_single_add_of_offDiag_zero a b
    (diagonal_apply_ne _ zero_config_ne_one) (diagonal_apply_ne _ zero_config_ne_one.symm)]
  simp

/-- A supported observable has a classical two-branch expectation if any site is unobserved. -/
theorem expect_ghzState_two {S : Set (Fin N)} (a b : ℂ)
    {A : Matrix (Fin N → Fin 2) (Fin N → Fin 2) ℂ}
    (hA : A ∈ supportedOperators 2 S) (hS : ∃ i, i ∉ S) :
    expect (ghzState (M := N) ![a, b]) A =
      star a * a * A (fun _ => 0) (fun _ => 0) +
        star b * b * A (fun _ => 1) (fun _ => 1) := by
  obtain ⟨i, hi⟩ := hS
  rw [ghzState_two_eq]
  exact expect_smul_single_add_of_offDiag_zero a b
    (apply_eq_zero_of_mem_supportedOperators hA ⟨i, hi, by decide⟩)
    (apply_eq_zero_of_mem_supportedOperators hA ⟨i, hi, by decide⟩)

/-- The exact connected correlation of two separated observables in a binary GHZ vector. -/
theorem covariance_ghzState_two {S S' : Set (Fin N)} (hSS' : Disjoint S S')
    (hcover : ∃ i, i ∉ S ∪ S') {a b : ℂ} (hab : star a * a + star b * b = 1)
    {A B : Matrix (Fin N → Fin 2) (Fin N → Fin 2) ℂ}
    (hA : A ∈ supportedOperators 2 S) (hB : B ∈ supportedOperators 2 S') :
    expect (ghzState (M := N) ![a, b]) (A * B) -
        expect (ghzState (M := N) ![a, b]) A * expect (ghzState (M := N) ![a, b]) B =
      (star a * a) * (star b * b) *
        (A (fun _ => 0) (fun _ => 0) - A (fun _ => 1) (fun _ => 1)) *
        (B (fun _ => 0) (fun _ => 0) - B (fun _ => 1) (fun _ => 1)) := by
  have hAu : A ∈ supportedOperators 2 (S ∪ S') :=
    supportedOperators_mono Set.subset_union_left hA
  have hBu : B ∈ supportedOperators 2 (S ∪ S') :=
    supportedOperators_mono Set.subset_union_right hB
  rw [expect_ghzState_two a b (mul_mem_supportedOperators hAu hBu) hcover,
    expect_ghzState_two a b hAu hcover, expect_ghzState_two a b hBu hcover,
    mul_apply_eq_mul_of_mem_supportedOperators hSS' hA hB,
    mul_apply_eq_mul_of_mem_supportedOperators hSS' hA hB]
  linear_combination
    -(star a * a * A (fun _ => 0) (fun _ => 0) * B (fun _ => 0) (fun _ => 0) +
      star b * b * A (fun _ => 1) (fun _ => 1) * B (fun _ => 1) (fun _ => 1)) * hab

/-- Separated unitary observables in a normalized GHZ vector have correlation at most
four times the product of the sector probabilities. -/
theorem norm_covariance_ghzState_two_le {S S' : Set (Fin N)} (hSS' : Disjoint S S')
    (hcover : ∃ i, i ∉ S ∪ S') {a b : ℂ} (hab : star a * a + star b * b = 1)
    {A B : Matrix (Fin N → Fin 2) (Fin N → Fin 2) ℂ}
    (hA : A ∈ supportedOperators 2 S) (hB : B ∈ supportedOperators 2 S')
    (hAu : A ∈ unitary _) (hBu : B ∈ unitary _) :
    ‖expect (ghzState (M := N) ![a, b]) (A * B) -
        expect (ghzState (M := N) ![a, b]) A * expect (ghzState (M := N) ![a, b]) B‖ ≤
      4 * ‖a‖ ^ 2 * ‖b‖ ^ 2 := by
  have hentry (C : Matrix (Fin N → Fin 2) (Fin N → Fin 2) ℂ) (hC : C ∈ unitary _)
      (σ : Fin N → Fin 2) : ‖C σ σ‖ ≤ 1 := by
    have hn : ‖(WithLp.toLp 2 (Pi.single σ (1 : ℂ)) :
        EuclideanSpace ℂ (Fin N → Fin 2))‖ = 1 := by
      change ‖(PiLp.single (β := fun _ : Fin N → Fin 2 => ℂ) 2 σ (1 : ℂ))‖ = 1
      simp
    simpa only [expect_single] using norm_expect_le_one hn hC
  have hdiff (C : Matrix (Fin N → Fin 2) (Fin N → Fin 2) ℂ) (hC : C ∈ unitary _) :
      ‖C (fun _ => 0) (fun _ => 0) - C (fun _ => 1) (fun _ => 1)‖ ≤ 2 := by
    exact (norm_sub_le _ _).trans (by
      linarith [hentry C hC (fun _ => 0), hentry C hC (fun _ => 1)])
  rw [covariance_ghzState_two hSS' hcover hab hA hB]
  simp only [norm_mul, norm_star]
  calc
    _ ≤ ‖a‖ * ‖a‖ * (‖b‖ * ‖b‖) * 2 * 2 := by gcongr <;> apply hdiff <;> assumption
    _ = 4 * ‖a‖ ^ 2 * ‖b‖ ^ 2 := by ring

section Ring

variable [NeZero N]

/-- A shallow circuit preserves the upper bound on distant GHZ-sector correlations. -/
theorem norm_covariance_mulVec_ghzState_two_le {T : ℕ}
    {U A B : Matrix (Fin N → Fin 2) (Fin N → Fin 2) ℂ}
    (hU : IsLocalCircuitOfDepth U T) {X Y : Set (Fin N)}
    (hXY : IsSeparatedBy X Y (2 * T))
    (hcover : ∃ k, k ∉ neighbourhood X T ∪ neighbourhood Y T)
    (hA : A ∈ supportedOperators 2 X) (hB : B ∈ supportedOperators 2 Y)
    (hAu : A ∈ unitary _) (hBu : B ∈ unitary _)
    {a b : ℂ} (hab : star a * a + star b * b = 1) :
    ‖expect (U *ᵥ ghzState (M := N) ![a, b]) (A * B) -
        expect (U *ᵥ ghzState (M := N) ![a, b]) A *
          expect (U *ᵥ ghzState (M := N) ![a, b]) B‖ ≤ 4 * ‖a‖ ^ 2 * ‖b‖ ^ 2 := by
  have hunit : U * star U = 1 := Unitary.mul_star_self_of_mem hU.mem_unitary
  have hprod : star U * (A * B) * U = (star U * A * U) * (star U * B * U) := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc U (star U), hunit, Matrix.one_mul]
  simp only [expect_mulVec]
  rw [hprod]
  exact norm_covariance_ghzState_two_le (disjoint_neighbourhood_of_isSeparatedBy hXY)
    hcover hab (conj_circuitOp_mem_supportedOperators hU hA)
    (conj_circuitOp_mem_supportedOperators hU hB)
    (Submonoid.mul_mem _ (Submonoid.mul_mem _ (Unitary.star_mem hU.mem_unitary) hAu)
      hU.mem_unitary)
    (Submonoid.mul_mem _ (Submonoid.mul_mem _ (Unitary.star_mem hU.mem_unitary) hBu)
      hU.mem_unitary)

end Ring

end QuantumCircuit
