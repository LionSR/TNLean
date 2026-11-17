/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Fintype.Sigma
import TNLean.Algebra.ExpConjugation
import TNLean.Circuit.SiteEmbedding
import TNLean.Circuit.SupportedMatrixElements
import QICLean.Entropy.RegionUnion

/-!
# Imaginary-time conjugation for interactions of bounded support and degree

Let positive contractions `h i` act on finite sets `D i` of an arbitrary finite
site set, with `|D i| ≤ k` and every site in at most `g` of the sets. An
observable supported on at most `k` sites then satisfies
`‖ad_H^m O‖ ≤ (g k)^m m! ‖O‖`, and
`‖exp(sH) O exp(-sH)‖ ≤ 2 ‖O‖` for `0 ≤ s ≤ 1 / (2 g k)`, also after any scalar
shift of `H`.

The commutator iterate is written as a sum of pieces, each a nested commutator
along one sequence of interaction terms. A piece after `j` commutators is
supported on at most `|S| + j k` sites, so at most `g (|S| + j k)` terms fail to
commute with it, and each such commutator costs at most the norm of the piece.

The route uses positivity of the terms through `‖[h, X]‖ ≤ ‖X‖`. The
interaction-budget estimate of the same lemma, with norm budgets in place of
positivity, is the positivity-free variant with an extra factor two.

Source: Arad, Kuwahara and Landau, arXiv:1406.3898, Lemma `lem:Hadamard-bound`,
`low70.tex`, lines 795–880, for `k`-local interactions in which every site meets
at most `g` terms. The constant `g k` comes from this counting and need not
match the printed one; the conclusion is used only through the displayed bound.
-/

open scoped BigOperators Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace QuantumCircuit

open scoped BigOperators Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator

variable {ι I : Type*} [Fintype ι] [DecidableEq ι] {q : ℕ}

/-- Only terms meeting the observable's support contribute to a commutator.
For positive contractions, each such term costs at most the observable norm.
This is a finite-sum step supporting AKL14, arXiv:1406.3898, low70.tex,
lines 817–837; it is not an iterated-commutator or imaginary-time theorem.
The site type is arbitrary. -/
theorem norm_commutator_sum_le_active_card (s : Finset I)
    (h : I → Matrix (ι → Fin q) (ι → Fin q) ℂ) (D : I → Finset ι)
    (O : Matrix (ι → Fin q) (ι → Fin q) ℂ) (S : Finset ι)
    (hsupport : ∀ i ∈ s, Entropy.IsSupportedOn (n := fun _ ↦ q) (h i) (D i))
    (hO : Entropy.IsSupportedOn (n := fun _ ↦ q) O S)
    (h0 : ∀ i ∈ s, 0 ≤ h i) (h1 : ∀ i ∈ s, h i ≤ 1) :
    ‖(∑ i ∈ s, h i) * O - O * (∑ i ∈ s, h i)‖ ≤
      ((s.filter fun i ↦ ¬Disjoint (D i) S).card : ℝ) * ‖O‖ := by
  classical
  let active := s.filter fun i ↦ ¬Disjoint (D i) S
  have hsum : (∑ i ∈ s, (h i * O - O * h i)) =
      ∑ i ∈ active, (h i * O - O * h i) := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro i hi hia
    by_cases hd : Disjoint (D i) S
    · have hc : Commute (h i) O := ManyBody.commute_of_mem_supportedOperators_of_disjoint ((hsupport i hi)) (hO) hd
      exact sub_eq_zero.mpr hc.eq
    · exact False.elim (hia (Finset.mem_filter.mpr ⟨hi, hd⟩))
  calc
    ‖(∑ i ∈ s, h i) * O - O * (∑ i ∈ s, h i)‖ =
        ‖∑ i ∈ s, (h i * O - O * h i)‖ := by
      rw [Finset.sum_mul, Finset.mul_sum, Finset.sum_sub_distrib]
    _ = ‖∑ i ∈ active, (h i * O - O * h i)‖ := congrArg (‖·‖) hsum
    _ ≤ ∑ i ∈ active, ‖h i * O - O * h i‖ := norm_sum_le _ _
    _ ≤ ∑ _i ∈ active, ‖O‖ := by
      apply Finset.sum_le_sum
      intro i hi
      have his : i ∈ s := (Finset.mem_filter.mp hi).1
      exact Matrix.norm_commutator_le_of_nonneg_le_one (h i) O (h0 i his) (h1 i his)
    _ = (active.card : ℝ) * ‖O‖ := by simp only [Finset.sum_const, nsmul_eq_mul]

end QuantumCircuit

namespace TNLean.Lattice

open QuantumCircuit

variable {ι I : Type*} [Fintype ι] [DecidableEq ι] {q : ℕ}

omit [Fintype ι] in
/-- At most `g |S|` terms meet a set `S` when every site lies in at most `g`
supports. Supporting AKL14, arXiv:1406.3898, low70.tex, lines 817–837. -/
theorem card_filter_not_disjoint_le {s : Finset I} (D : I → Finset ι) {g : ℕ}
    (hg : ∀ x : ι, (s.filter fun i ↦ x ∈ D i).card ≤ g) (S : Finset ι) :
    (s.filter fun i ↦ ¬Disjoint (D i) S).card ≤ g * S.card := by
  classical
  calc
    (s.filter fun i ↦ ¬Disjoint (D i) S).card ≤
        (S.biUnion fun x ↦ s.filter fun i ↦ x ∈ D i).card := by
      apply Finset.card_le_card
      intro i hi
      obtain ⟨his, hd⟩ := Finset.mem_filter.mp hi
      obtain ⟨x, hxD, hxS⟩ := Finset.not_disjoint_iff.mp hd
      exact Finset.mem_biUnion.mpr ⟨x, hxS, Finset.mem_filter.mpr ⟨his, hxD⟩⟩
    _ ≤ ∑ x ∈ S, (s.filter fun i ↦ x ∈ D i).card := Finset.card_biUnion_le
    _ ≤ ∑ _x ∈ S, g := Finset.sum_le_sum fun x _ ↦ hg x
    _ = g * S.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]

/-- The commutator iterates of a bounded-support, bounded-degree sum of positive
contractions split into at most `∏_{j<m} g (|S| + j k)` pieces, each of norm at
most `‖O‖` and supported on at most `|S| + m k` sites. Supporting AKL14,
arXiv:1406.3898, low70.tex, lines 804–877. -/
theorem exists_commutator_iterate_decomposition {s : Finset I}
    (h : I → Matrix (ι → Fin q) (ι → Fin q) ℂ) (D : I → Finset ι) {k g : ℕ}
    (hs : ∀ i ∈ s, Entropy.IsSupportedOn (n := fun _ ↦ q) (h i) (D i))
    (h0 : ∀ i ∈ s, 0 ≤ h i) (h1 : ∀ i ∈ s, h i ≤ 1)
    (hk : ∀ i ∈ s, (D i).card ≤ k)
    (hg : ∀ x : ι, (s.filter fun i ↦ x ∈ D i).card ≤ g)
    (O : Matrix (ι → Fin q) (ι → Fin q) ℂ) (S₀ : Finset ι)
    (hO : Entropy.IsSupportedOn (n := fun _ ↦ q) O S₀) (m : ℕ) :
    let H : Matrix (ι → Fin q) (ι → Fin q) ℂ := ∑ i ∈ s, h i
    ∃ (N : ℕ) (X : Fin N → Matrix (ι → Fin q) (ι → Fin q) ℂ) (S : Fin N → Finset ι),
      (fun Y ↦ H * Y - Y * H)^[m] O = ∑ a, X a ∧
      (∀ a, Entropy.IsSupportedOn (n := fun _ ↦ q) (X a) (S a)) ∧
      (∀ a, ‖X a‖ ≤ ‖O‖) ∧ (∀ a, (S a).card ≤ S₀.card + m * k) ∧
      N ≤ ∏ j ∈ Finset.range m, g * (S₀.card + j * k) := by
  intro H
  classical
  induction m with
  | zero =>
    refine ⟨1, fun _ ↦ O, fun _ ↦ S₀, by simp, fun _ ↦ hO, fun _ ↦ le_rfl,
      fun _ ↦ by simp, by simp⟩
  | succ m ih =>
    obtain ⟨N, X, S, hsum, hsupp, hnorm, hcard, hN⟩ := ih
    let T : Fin N → Finset I := fun a ↦ s.filter fun i ↦ ¬Disjoint (D i) (S a)
    let σ := Σ a : Fin N, ↥(T a)
    let e := Fintype.equivFin σ
    let f : σ → Matrix (ι → Fin q) (ι → Fin q) ℂ := fun p ↦
      h p.2.1 * X p.1 - X p.1 * h p.2.1
    let R : σ → Finset ι := fun p ↦ S p.1 ∪ D p.2.1
    have hTs (p : σ) : p.2.1 ∈ s := (Finset.mem_filter.mp p.2.2).1
    refine ⟨Fintype.card σ, fun j ↦ f (e.symm j), fun j ↦ R (e.symm j), ?_, ?_, ?_, ?_, ?_⟩
    · have hterm (a : Fin N) : H * X a - X a * H = ∑ i ∈ T a, (h i * X a - X a * h i) := by
        rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
        symm
        apply Finset.sum_subset (Finset.filter_subset _ _)
        intro i hi hiT
        by_cases hd : Disjoint (D i) (S a)
        · have hc : Commute (h i) (X a) := ManyBody.commute_of_mem_supportedOperators_of_disjoint ((hs i hi)) ((hsupp a)) hd
          exact sub_eq_zero.mpr hc.eq
        · exact False.elim (hiT (Finset.mem_filter.mpr ⟨hi, hd⟩))
      rw [Function.iterate_succ_apply', hsum, Finset.mul_sum, Finset.sum_mul,
        ← Finset.sum_sub_distrib]
      calc
        ∑ a, (H * X a - X a * H) = ∑ a, ∑ i : ↥(T a), (h i.1 * X a - X a * h i.1) := by
          refine Finset.sum_congr rfl fun a _ ↦ ?_
          rw [hterm a, ← Finset.sum_coe_sort (T a)]
        _ = ∑ p : σ, f p := (Fintype.sum_sigma f).symm
        _ = ∑ j, f (e.symm j) := (Equiv.sum_comp e.symm f).symm
    · intro j
      let p := e.symm j
      have hhR : h p.2.1 ∈ ManyBody.supportedOperators (fun _ ↦ Fin q) (R p : Finset ι) :=
        ManyBody.supportedOperators_mono (by simp [R])
          ((hs _ (hTs p)))
      have hXR : X p.1 ∈ ManyBody.supportedOperators (fun _ ↦ Fin q) (R p : Finset ι) :=
        ManyBody.supportedOperators_mono (by simp [R])
          ((hsupp p.1))
      exact (Submodule.sub_mem _ (mul_mem hhR hXR)
          (mul_mem hXR hhR))
    · intro j
      exact (Matrix.norm_commutator_le_of_nonneg_le_one _ _ (h0 _ (hTs _))
        (h1 _ (hTs _))).trans (hnorm _)
    · intro j
      let p := e.symm j
      calc
        (R p).card ≤ (S p.1).card + (D p.2.1).card := Finset.card_union_le _ _
        _ ≤ (S₀.card + m * k) + k := add_le_add (hcard _) (hk _ (hTs p))
        _ = S₀.card + (m + 1) * k := by ring
    · calc
        Fintype.card σ = ∑ a, (T a).card := by
          simp only [σ, Fintype.card_sigma, Fintype.card_coe]
        _ ≤ ∑ _a : Fin N, g * (S₀.card + m * k) := by
          refine Finset.sum_le_sum fun a _ ↦ ?_
          exact (card_filter_not_disjoint_le D hg (S a)).trans
            (Nat.mul_le_mul_left _ (hcard a))
        _ = N * (g * (S₀.card + m * k)) := by simp
        _ ≤ (∏ j ∈ Finset.range m, g * (S₀.card + j * k)) * (g * (S₀.card + m * k)) :=
          Nat.mul_le_mul_right _ hN
        _ = ∏ j ∈ Finset.range (m + 1), g * (S₀.card + j * k) :=
          (Finset.prod_range_succ _ _).symm

/-- The commutator iterates of a bounded-support, bounded-degree sum of positive
contractions on an observable of at most `k` sites grow at most like
`(g k)^m m!`. This is the factorial estimate of AKL14, arXiv:1406.3898,
`lem:Hadamard-bound`, low70.tex, lines 804–877. -/
theorem norm_commutator_iterate_le {s : Finset I}
    (h : I → Matrix (ι → Fin q) (ι → Fin q) ℂ) (D : I → Finset ι) {k g : ℕ}
    (hs : ∀ i ∈ s, Entropy.IsSupportedOn (n := fun _ ↦ q) (h i) (D i))
    (h0 : ∀ i ∈ s, 0 ≤ h i) (h1 : ∀ i ∈ s, h i ≤ 1)
    (hk : ∀ i ∈ s, (D i).card ≤ k)
    (hg : ∀ x : ι, (s.filter fun i ↦ x ∈ D i).card ≤ g)
    (O : Matrix (ι → Fin q) (ι → Fin q) ℂ) (S₀ : Finset ι)
    (hO : Entropy.IsSupportedOn (n := fun _ ↦ q) O S₀) (hS₀ : S₀.card ≤ k) (m : ℕ) :
    let H : Matrix (ι → Fin q) (ι → Fin q) ℂ := ∑ i ∈ s, h i
    ‖(fun Y ↦ H * Y - Y * H)^[m] O‖ ≤ ((g * k : ℕ) : ℝ) ^ m * (m.factorial : ℝ) * ‖O‖ := by
  intro H
  obtain ⟨N, X, S, hsum, -, hnorm, -, hN⟩ :=
    exists_commutator_iterate_decomposition h D hs h0 h1 hk hg O S₀ hO m
  have hprod : ∏ j ∈ Finset.range m, g * (S₀.card + j * k) ≤ (g * k) ^ m * m.factorial := by
    calc
      ∏ j ∈ Finset.range m, g * (S₀.card + j * k) ≤
          ∏ j ∈ Finset.range m, (g * k) * (j + 1) := by
        refine Finset.prod_le_prod fun j _ ↦ ?_
        calc
          g * (S₀.card + j * k) ≤ g * (k + j * k) := Nat.mul_le_mul_left _ (by omega)
          _ = (g * k) * (j + 1) := by ring
      _ = (g * k) ^ m * m.factorial := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range,
          Finset.prod_range_add_one_eq_factorial]
  have hNreal : (N : ℝ) ≤ ((g * k : ℕ) : ℝ) ^ m * (m.factorial : ℝ) := by
    exact_mod_cast hN.trans hprod
  calc
    ‖(fun Y ↦ H * Y - Y * H)^[m] O‖ = ‖∑ a, X a‖ := by rw [hsum]
    _ ≤ ∑ a, ‖X a‖ := norm_sum_le _ _
    _ ≤ ∑ _a : Fin N, ‖O‖ := Finset.sum_le_sum fun a _ ↦ hnorm a
    _ = (N : ℝ) * ‖O‖ := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hNreal (norm_nonneg O)

/-- Imaginary-time conjugation by a bounded-support, bounded-degree sum of
positive contractions is bounded by `2 ‖O‖` for `0 ≤ s ≤ 1 / (2 g k)`, after any
scalar shift. This is AKL14, arXiv:1406.3898, `lem:Hadamard-bound`,
low70.tex, lines 795–880, for an observable on at most `k` sites. -/
theorem norm_exp_conjugation_shift_le_two {s : Finset I}
    (h : I → Matrix (ι → Fin q) (ι → Fin q) ℂ) (D : I → Finset ι) {k g : ℕ}
    (hk0 : 0 < k) (hg0 : 0 < g)
    (hs : ∀ i ∈ s, Entropy.IsSupportedOn (n := fun _ ↦ q) (h i) (D i))
    (h0 : ∀ i ∈ s, 0 ≤ h i) (h1 : ∀ i ∈ s, h i ≤ 1)
    (hk : ∀ i ∈ s, (D i).card ≤ k)
    (hg : ∀ x : ι, (s.filter fun i ↦ x ∈ D i).card ≤ g)
    (O : Matrix (ι → Fin q) (ι → Fin q) ℂ) (S₀ : Finset ι)
    (hO : Entropy.IsSupportedOn (n := fun _ ↦ q) O S₀) (hS₀ : S₀.card ≤ k)
    (z : ℂ) (t : ℝ) (ht0 : 0 ≤ t) (ht : 2 * ((g * k : ℕ) : ℝ) * t ≤ 1) :
    let H : Matrix (ι → Fin q) (ι → Fin q) ℂ := ∑ i ∈ s, h i
    ‖NormedSpace.exp ((t : ℂ) • (H - z • 1)) * O *
      NormedSpace.exp (-((t : ℂ) • (H - z • 1)))‖ ≤ 2 * ‖O‖ := by
  intro H
  have hκ : (0 : ℝ) < ((g * k : ℕ) : ℝ) := by exact_mod_cast Nat.mul_pos hg0 hk0
  apply Matrix.norm_exp_conjugation_le_two_of_growth (H - z • 1) O _ t hκ.le ht0 (by linarith)
  intro m
  have had :
      (fun X : Matrix (ι → Fin q) (ι → Fin q) ℂ ↦ (H - z • 1) * X - X * (H - z • 1)) =
      (fun X : Matrix (ι → Fin q) (ι → Fin q) ℂ ↦ H * X - X * H) := by
    funext X
    simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
    abel
  rw [had]
  exact norm_commutator_iterate_le h D hs h0 h1 hk hg O S₀ hO hS₀ m

/-- Conjugating a sum of boundary positive contractions, each on at most `k`
sites, costs at most twice their number. Supporting AKL14, arXiv:1406.3898,
low70.tex, lines 817–877. -/
theorem norm_exp_conjugation_shift_sum_le [DecidableEq I] {s J : Finset I}
    (h : I → Matrix (ι → Fin q) (ι → Fin q) ℂ) (D : I → Finset ι) {k g : ℕ}
    (hk0 : 0 < k) (hg0 : 0 < g)
    (hs : ∀ i ∈ s ∪ J, Entropy.IsSupportedOn (n := fun _ ↦ q) (h i) (D i))
    (h0 : ∀ i ∈ s ∪ J, 0 ≤ h i) (h1 : ∀ i ∈ s ∪ J, h i ≤ 1)
    (hk : ∀ i ∈ s ∪ J, (D i).card ≤ k)
    (hg : ∀ x : ι, (s.filter fun i ↦ x ∈ D i).card ≤ g)
    (z : ℂ) (t : ℝ) (ht0 : 0 ≤ t) (ht : 2 * ((g * k : ℕ) : ℝ) * t ≤ 1) :
    let H : Matrix (ι → Fin q) (ι → Fin q) ℂ := ∑ i ∈ s, h i
    ‖NormedSpace.exp ((t : ℂ) • (H - z • 1)) * (∑ j ∈ J, h j) *
      NormedSpace.exp (-((t : ℂ) • (H - z • 1)))‖ ≤ 2 * (J.card : ℝ) := by
  intro H
  have hnorm1 : ‖(1 : Matrix (ι → Fin q) (ι → Fin q) ℂ)‖ ≤ 1 :=
    IsStarProjection.norm_le _ (IsStarProjection.one _)
  have hterm (j : I) (hj : j ∈ J) :
      ‖NormedSpace.exp ((t : ℂ) • (H - z • 1)) * h j *
        NormedSpace.exp (-((t : ℂ) • (H - z • 1)))‖ ≤ 2 := by
    have hjJ : j ∈ s ∪ J := Finset.mem_union_right s hj
    have hjnorm : ‖h j‖ ≤ 1 :=
      (CStarAlgebra.norm_le_norm_of_le_of_nonneg (h1 j hjJ) (h0 j hjJ)).trans hnorm1
    calc
      _ ≤ 2 * ‖h j‖ := norm_exp_conjugation_shift_le_two h D hk0 hg0
          (fun i hi ↦ hs i (Finset.mem_union_left J hi))
          (fun i hi ↦ h0 i (Finset.mem_union_left J hi))
          (fun i hi ↦ h1 i (Finset.mem_union_left J hi))
          (fun i hi ↦ hk i (Finset.mem_union_left J hi)) hg
          (h j) (D j) (hs j hjJ) (hk j hjJ) z t ht0 ht
      _ ≤ 2 := by linarith
  calc
    _ = ‖∑ j ∈ J, NormedSpace.exp ((t : ℂ) • (H - z • 1)) * h j *
          NormedSpace.exp (-((t : ℂ) • (H - z • 1)))‖ := by
      rw [Finset.mul_sum, Finset.sum_mul]
    _ ≤ ∑ j ∈ J, ‖NormedSpace.exp ((t : ℂ) • (H - z • 1)) * h j *
        NormedSpace.exp (-((t : ℂ) • (H - z • 1)))‖ := norm_sum_le _ _
    _ ≤ ∑ _j ∈ J, (2 : ℝ) := Finset.sum_le_sum hterm
    _ = 2 * (J.card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_comm]

end TNLean.Lattice
