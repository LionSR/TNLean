/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.ExpConjugation
import TNLean.MPS.AreaLaw.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Disjoint
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic.Positivity
import TNLean.Circuit.EntropySupport
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Topology.Algebra.InfiniteSum.Module
import Mathlib.Data.FunLike.IsApply
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith

/-!
# Imaginary-time conjugation for nearest-neighbour Hamiltonians

For a sum of positive unit contractions supported on nearest-neighbour bonds,
a two-site observable satisfies `‖exp(tH) * O * exp(-tH)‖ ≤ 2 * ‖O‖` for
`0 ≤ t ≤ 1 / 8`. The estimate is unchanged by a scalar shift of `H`.

The proof follows the commutator argument of Arad, Kuwahara and Landau,
arXiv:1406.3898, Lemma `lem:Hadamard-bound`, `low70.tex`, lines 795–880.
After `m` commutators the support has grown by at most `m` sites on each
side, so at most `2*m + 3` bonds contribute. This gives the factorial
bound `4^m * m! * ‖O‖`; the exponential series is then bounded by a
geometric series. The Hamiltonian is the original bond sum throughout.
-/

open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A positive contraction has commutator norm at most the norm of the other
factor. Auxiliary to AKL14, arXiv:1406.3898, low70.tex, lines 831–837.
The other factor need not be Hermitian, and the index type may be empty. -/
private theorem norm_commutator_le_of_nonneg_le_one (h O : Matrix n n ℂ)
    (h0 : 0 ≤ h) (h1 : h ≤ 1) : ‖h * O - O * h‖ ≤ ‖O‖ := by
  let c : Matrix n n ℂ := (1 / 2 : ℝ) • 1
  have hsplit : (1 : Matrix n n ℂ) = c + c := by
    dsimp [c]
    rw [← add_smul]
    norm_num
  have hlo : -c ≤ h - c := by
    simpa only [zero_sub] using sub_le_sub_right h0 c
  have hhi : h - c ≤ c := by
    apply (sub_le_iff_le_add).2
    rw [← hsplit]
    exact h1
  have hcself : IsSelfAdjoint c :=
    IsSelfAdjoint.smul (IsSelfAdjoint.all (1 / 2 : ℝ)) (IsSelfAdjoint.one (Matrix n n ℂ))
  have hcenterself : IsSelfAdjoint (h - c) := (IsSelfAdjoint.of_nonneg h0).sub hcself
  have hnorm1 : ‖(1 : Matrix n n ℂ)‖ ≤ 1 :=
    IsStarProjection.norm_le _ (IsStarProjection.one (Matrix n n ℂ))
  have hcnorm : ‖c‖ ≤ (1 / 2 : ℝ) := by
    calc
      ‖c‖ = (1 / 2 : ℝ) * ‖(1 : Matrix n n ℂ)‖ := by
        dsimp [c]
        rw [norm_smul]
        norm_num
      _ ≤ (1 / 2 : ℝ) * 1 := mul_le_mul_of_nonneg_left hnorm1 (by norm_num)
      _ = 1 / 2 := by ring
  have hcenternorm0 : ‖h - c‖ ≤ ‖c‖ := by
    simpa only [norm_neg, max_self] using
      (IsSelfAdjoint.norm_le_max_of_le_of_le hlo hhi hcenterself)
  have hcenternorm : ‖h - c‖ ≤ (1 / 2 : ℝ) := hcenternorm0.trans hcnorm
  have hcomm : h * O - O * h = (h - c) * O - O * (h - c) := by
    dsimp [c]
    simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
    abel
  calc
    ‖h * O - O * h‖ = ‖(h - c) * O - O * (h - c)‖ := congrArg (‖·‖) hcomm
    _ ≤ ‖(h - c) * O‖ + ‖O * (h - c)‖ := norm_sub_le _ _
    _ ≤ ‖h - c‖ * ‖O‖ + ‖O‖ * ‖h - c‖ :=
      add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ ≤ (1 / 2 : ℝ) * ‖O‖ + ‖O‖ * (1 / 2 : ℝ) :=
      add_le_add (mul_le_mul_of_nonneg_right hcenternorm (norm_nonneg O))
        (mul_le_mul_of_nonneg_left hcenternorm (norm_nonneg O))
    _ = ‖O‖ := by ring

end Matrix

namespace QuantumCircuit

open scoped BigOperators Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator

variable {ι I : Type*} [Fintype ι] [DecidableEq ι] {q : ℕ}

/-- Only terms meeting the observable's support contribute to a commutator.
For positive contractions, each such term costs at most the observable norm.
This is a finite-sum step supporting AKL14, arXiv:1406.3898, low70.tex,
lines 817–837; it is not an iterated-commutator or imaginary-time theorem. -/
private theorem norm_commutator_sum_le_active_card (s : Finset I)
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
    · have hc : Commute (h i) O := commute_of_mem_supportedOperators
        (Finset.disjoint_coe.mpr hd)
        (mem_supportedOperators_of_isSupportedOn (hsupport i hi))
        (mem_supportedOperators_of_isSupportedOn hO)
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

namespace TNLean.MPS.AreaLaw

/-- At most 2m+3 nearest-neighbor bonds meet the m-fold enlargement of a
possibly clipped two-site interval. No condition on the chain length or
centre is needed. Supporting AKL14, arXiv:1406.3898, lines 795–880. -/
private theorem card_bonds_meeting_enlarged_interval_le (L c m : ℕ) :
    (Finset.univ.filter fun i : Fin (L - 1) ↦
      ¬Disjoint (interval L i.val (i.val + 2))
        (interval L (c - m) (c + 2 + m))).card ≤ 2 * m + 3 := by
  classical
  let I := Finset.univ.filter fun i : Fin (L - 1) ↦
    ¬Disjoint (interval L i.val (i.val + 2))
      (interval L (c - m) (c + 2 + m))
  have hbounds (i : I) : c ≤ i.val.val + m + 1 ∧ i.val.val < c + m + 2 := by
    have hi := (Finset.mem_filter.mp i.property).2
    obtain ⟨v, hv, hvc⟩ := Finset.not_disjoint_iff.mp hi
    rw [mem_interval] at hv hvc
    omega
  let f : I → Fin (2 * m + 3) := fun i ↦
    ⟨i.val.val + m + 1 - c, by have hi := hbounds i; omega⟩
  have hf : Function.Injective f := by
    intro i j hij
    have heq := congrArg Fin.val hij
    have hi := hbounds i
    have hj := hbounds j
    have hval : i.val.val = j.val.val := by
      dsimp only [f] at heq
      omega
    apply Subtype.ext
    exact Fin.ext hval
  simpa only [Fintype.card_coe, Fintype.card_fin] using
    (Fintype.card_le_of_injective f hf)

end TNLean.MPS.AreaLaw

namespace TNLean.MPS.AreaLaw

/-- A nearest-neighbor bond meeting an enlarged two-site interval is
contained in its next enlargement. This is the support step for AKL14,
arXiv:1406.3898, low70.tex, lines 817–877. The chain may be empty and the
intervals are clipped at its endpoints. -/
private theorem bond_subset_enlarged_interval_succ {L c m i : ℕ}
    (hmeet : ¬Disjoint (interval L i (i + 2))
      (interval L (c - m) (c + 2 + m))) :
    interval L i (i + 2) ⊆
      interval L (c - (m + 1)) (c + 2 + (m + 1)) := by
  obtain ⟨v, hvi, hvc⟩ := Finset.not_disjoint_iff.mp hmeet
  intro w hw
  simp only [mem_interval] at hvi hvc hw ⊢
  omega

/-- Enlargement by one preserves the old interval. Supporting the same
nearest-neighbor support argument of AKL14, arXiv:1406.3898, lines 817–877. -/
private theorem enlarged_interval_subset_succ (L c m : ℕ) :
    interval L (c - m) (c + 2 + m) ⊆
      interval L (c - (m + 1)) (c + 2 + (m + 1)) := by
  intro w hw
  simp only [mem_interval] at hw ⊢
  omega

end TNLean.MPS.AreaLaw

namespace TNLean.MPS.AreaLaw

open QuantumCircuit
open scoped BigOperators Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator

/-- One commutator with an original nearest-neighbour regional sum enlarges
a two-site interval by one and costs at most four times the next order.
Supporting AKL14, arXiv:1406.3898, low70.tex, lines 817–877. -/
private theorem nearest_neighbour_commutator_step {L q c m : ℕ}
    (s : Finset (Fin (L - 1)))
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hs : ∀ i ∈ s, Entropy.IsSupportedOn (n := fun _ ↦ q) (h i)
      (interval L i.val (i.val + 2)))
    (h0 : ∀ i ∈ s, 0 ≤ h i) (h1 : ∀ i ∈ s, h i ≤ 1)
    (X : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hX : Entropy.IsSupportedOn (n := fun _ ↦ q) X
      (interval L (c - m) (c + 2 + m))) :
    Entropy.IsSupportedOn (n := fun _ ↦ q)
      ((∑ i ∈ s, h i) * X - X * (∑ i ∈ s, h i))
      (interval L (c - (m + 1)) (c + 2 + (m + 1))) ∧
    ‖(∑ i ∈ s, h i) * X - X * (∑ i ∈ s, h i)‖ ≤
      (4 : ℝ) * ((m : ℝ) + 1) * ‖X‖ := by
  classical
  let J := interval L (c - (m + 1)) (c + 2 + (m + 1))
  have hXJ : X ∈ supportedOperators q (J : Set (Fin L)) :=
    supportedOperators_mono
      (by simpa only [Finset.coe_subset] using enlarged_interval_subset_succ L c m)
      (mem_supportedOperators_of_isSupportedOn hX)
  have hterm (i : Fin (L - 1)) (hi : i ∈ s) :
      h i * X - X * h i ∈ supportedOperators q (J : Set (Fin L)) := by
    by_cases hd : Disjoint (interval L i.val (i.val + 2))
        (interval L (c - m) (c + 2 + m))
    · have hc : Commute (h i) X := commute_of_mem_supportedOperators
        (Finset.disjoint_coe.mpr hd)
        (mem_supportedOperators_of_isSupportedOn (hs i hi))
        (mem_supportedOperators_of_isSupportedOn hX)
      rw [sub_eq_zero.mpr hc.eq]
      exact Submodule.zero_mem _
    · have hhJ : h i ∈ supportedOperators q (J : Set (Fin L)) :=
        supportedOperators_mono
          (by simpa only [Finset.coe_subset] using bond_subset_enlarged_interval_succ hd)
          (mem_supportedOperators_of_isSupportedOn (hs i hi))
      exact Submodule.sub_mem _ (mul_mem_supportedOperators hhJ hXJ)
        (mul_mem_supportedOperators hXJ hhJ)
  have hsupport : Entropy.IsSupportedOn (n := fun _ ↦ q)
      ((∑ i ∈ s, h i) * X - X * (∑ i ∈ s, h i)) J := by
    apply isSupportedOn_of_mem_supportedOperators
    have hsum := (supportedOperators q (J : Set (Fin L))).sum_mem hterm
    simpa only [Finset.sum_sub_distrib, Finset.sum_mul, Finset.mul_sum] using hsum
  refine ⟨hsupport, ?_⟩
  let active := s.filter fun i ↦ ¬Disjoint (interval L i.val (i.val + 2))
    (interval L (c - m) (c + 2 + m))
  have hcard : active.card ≤ 4 * (m + 1) := by
    calc
      active.card ≤ (Finset.univ.filter fun i : Fin (L - 1) ↦
          ¬Disjoint (interval L i.val (i.val + 2))
            (interval L (c - m) (c + 2 + m))).card := by
        apply Finset.card_le_card
        intro i hi
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, (Finset.mem_filter.mp hi).2⟩
      _ ≤ 2 * m + 3 := card_bonds_meeting_enlarged_interval_le L c m
      _ ≤ 4 * (m + 1) := by omega
  have hcardReal : (active.card : ℝ) ≤ (4 : ℝ) * ((m : ℝ) + 1) := by
    exact_mod_cast hcard
  exact (norm_commutator_sum_le_active_card s h
    (fun i ↦ interval L i.val (i.val + 2)) X
    (interval L (c - m) (c + 2 + m)) hs hX h0 h1).trans
      (mul_le_mul_of_nonneg_right hcardReal (norm_nonneg X))

/-- The actual iterated commutators of an original nearest-neighbour regional
sum remain local and have factorial norm growth. Auxiliary to AKL14,
arXiv:1406.3898, low70.tex, lines 804–877; no imaginary-time sum is asserted. -/
private theorem iterated_nearest_neighbour_commutator_support_norm {L q c : ℕ}
    (s : Finset (Fin (L - 1)))
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hs : ∀ i ∈ s, Entropy.IsSupportedOn (n := fun _ ↦ q) (h i)
      (interval L i.val (i.val + 2)))
    (h0 : ∀ i ∈ s, 0 ≤ h i) (h1 : ∀ i ∈ s, h i ≤ 1)
    (O : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hO : Entropy.IsSupportedOn (n := fun _ ↦ q) O (interval L c (c + 2))) (m : ℕ) :
    let H : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := ∑ i ∈ s, h i
    let ad : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ →
        Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := fun X ↦ H * X - X * H
    Entropy.IsSupportedOn (n := fun _ ↦ q) (ad^[m] O)
      (interval L (c - m) (c + 2 + m)) ∧
      ‖ad^[m] O‖ ≤ (4 : ℝ) ^ m * (m.factorial : ℝ) * ‖O‖ := by
  intro H ad
  induction m with
  | zero =>
    simpa only [Function.iterate_zero_apply, Nat.sub_zero, Nat.add_zero, pow_zero,
      Nat.factorial_zero, Nat.cast_one, one_mul] using And.intro hO (le_refl ‖O‖)
  | succ m ih =>
    obtain ⟨hsupport, hnorm⟩ := nearest_neighbour_commutator_step s h hs h0 h1
      (ad^[m] O) ih.1
    refine ⟨?_, ?_⟩
    · simpa only [Function.iterate_succ_apply'] using hsupport
    · rw [Function.iterate_succ_apply']
      calc
        ‖ad (ad^[m] O)‖ ≤ (4 : ℝ) * ((m : ℝ) + 1) * ‖ad^[m] O‖ := hnorm
        _ ≤ (4 : ℝ) * ((m : ℝ) + 1) *
            ((4 : ℝ) ^ m * (m.factorial : ℝ) * ‖O‖) :=
          mul_le_mul_of_nonneg_left ih.2 (by positivity)
        _ = (4 : ℝ) ^ (m + 1) * ((m + 1).factorial : ℝ) * ‖O‖ := by
          rw [pow_succ, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
          ring

end TNLean.MPS.AreaLaw


namespace TNLean.MPS.AreaLaw

/-- Imaginary-time conjugation by an original nearest-neighbour regional sum
has a uniform short-time bound, also after an arbitrary scalar shift.
This supplies the local estimate in AKL14, arXiv:1406.3898, low70.tex,
lines 795–880. The generator is the original regional sum; no locality
property of a clipped Hamiltonian is required. -/
theorem norm_exp_conjugation_nearest_neighbour_shift_le_two {L q c : ℕ}
    (I : Finset (Fin (L - 1)))
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hs : ∀ i ∈ I, Entropy.IsSupportedOn (n := fun _ ↦ q) (h i)
      (interval L i.val (i.val + 2)))
    (h0 : ∀ i ∈ I, 0 ≤ h i) (h1 : ∀ i ∈ I, h i ≤ 1)
    (O : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hO : Entropy.IsSupportedOn (n := fun _ ↦ q) O (interval L c (c + 2)))
    (z : ℂ) (t : ℝ) (ht0 : 0 ≤ t) (ht : t ≤ 1 / 8) :
    let H : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := ∑ i ∈ I, h i
    ‖NormedSpace.exp ((t : ℂ) • (H - z • 1)) * O *
      NormedSpace.exp (-((t : ℂ) • (H - z • 1)))‖ ≤ 2 * ‖O‖ := by
  intro H
  apply Matrix.norm_exp_conjugation_le_two (H - z • 1) O t ht0 ht
  intro m
  have had :
      (fun X : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ ↦
        (H - z • 1) * X - X * (H - z • 1)) =
      (fun X : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ ↦ H * X - X * H) := by
    funext X
    simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
    abel
  rw [had]
  exact (iterated_nearest_neighbour_commutator_support_norm I h hs h0 h1 O hO m).2

end TNLean.MPS.AreaLaw
