/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.Huang.GridHamiltonian
import TNLean.MPS.AreaLaw.LiebRobinson

/-!
# Localization of the omitted boundary terms

The retained interactions are an explicitly selected subfamily of the original
nearest-neighbor interactions. At most two of them meet a site, so their per-site norm
budget is at most two when each original term has norm at most one. The existing chain
Lieb--Robinson theorem then localizes each omitted term to its actual grid buffer.

Source: Osborne, arXiv:quant-ph/0508031v2, equations (6)--(12), and Huang,
arXiv:1406.6355v6, Section 5.4, Lemma 19.
-/

open Matrix QuantumCircuit
open scoped BigOperators Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw

variable {L q w : ℕ}

/-- The designated range-one support of an original nearest-neighbor interaction.
Osborne, arXiv:quant-ph/0508031v2, the Hamiltonian preceding equation (2). -/
def nearestNeighborChainSupport (i : Fin (L - 1)) : ChainSupport L 1 :=
  ⟨interval L i.val (i.val + 2),
    ⟨⟨⟨i.val, lt_of_lt_of_le i.isLt (Nat.sub_le L 1)⟩,
      mem_interval.mpr (show i.val ≤ i.val ∧ i.val < i.val + 2 by omega)⟩,
      fun x hx y hy ↦ by rw [mem_interval] at hx hy; omega⟩⟩

/-- The retained original interaction, with precisely the grid-boundary terms set to zero.
Osborne, Figure 2. -/
noncomputable def chainGridRetainedTerm (hw : 0 < w)
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) (i : Fin (L - 1)) :=
  if i ∈ chainGridBoundaryEdges hw then 0 else h i

/-- Summing the retained interactions gives the constructed within-block Hamiltonian.
Osborne, Figure 2 and equation (3). -/
theorem sum_chainGridRetainedTerm (hw : 0 < w)
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) :
    (∑ i, chainGridRetainedTerm hw h i) = chainGridRetainedHamiltonian hw h := by
  classical
  rw [chainGridRetainedHamiltonian_eq_sum_filter]
  simp only [chainGridRetainedTerm, Finset.sum_filter, ite_not]

/-- The original one-dimensional nearest-neighbor incidence count is at most two.
Osborne, the nearest-neighbor Hamiltonian preceding equation (2). -/
theorem card_nearestNeighborChainSupport_containing_le_two (x : Fin L) :
    (Finset.univ.filter
      (fun i : Fin (L - 1) ↦ x ∈ (nearestNeighborChainSupport i).val)).card ≤ 2 := by
  classical
  apply (Finset.card_le_card_of_injOn (fun i : Fin (L - 1) ↦ i.val)
    (s := Finset.univ.filter fun i ↦ x ∈ (nearestNeighborChainSupport i).val)
    (t := {x.val - 1, x.val}) ?_ Fin.val_injective.injOn).trans Finset.card_le_two
  intro i hi
  have hx := (Finset.mem_filter.mp hi).2
  change x ∈ interval L i.val (i.val + 2) at hx
  rw [mem_interval] at hx
  change i.val ∈ ({x.val - 1, x.val} : Finset ℕ)
  simp only [Finset.mem_insert, Finset.mem_singleton]
  omega

private theorem retained_support (hw : 0 < w)
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hs : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) (h i)
      (interval L i.val (i.val + 2))) (i : Fin (L - 1)) :
    Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) (chainGridRetainedTerm hw h i)
      (nearestNeighborChainSupport i).val := by
  classical
  unfold chainGridRetainedTerm
  split_ifs
  · exact isSupportedOn_of_mem_supportedOperators (Submodule.zero_mem _)
  · exact hs i

private theorem retained_hermitian (hw : 0 < w)
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hHerm : ∀ i, (h i).IsHermitian) (i : Fin (L - 1)) :
    (chainGridRetainedTerm hw h i).IsHermitian := by
  classical
  unfold chainGridRetainedTerm
  split_ifs
  · exact isHermitian_zero
  · exact hHerm i

private theorem retained_norm_le_one (hw : 0 < w)
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hnorm : ∀ i, ‖h i‖ ≤ 1) (i : Fin (L - 1)) : ‖chainGridRetainedTerm hw h i‖ ≤ 1 := by
  classical
  unfold chainGridRetainedTerm
  split_ifs
  · simp
  · exact hnorm i

/-- The retained physical interaction has site norm budget at most two, derived from
the original norm bounds. Osborne, equations (6)--(12). -/
theorem chainGridRetained_site_budget (hw : 0 < w)
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hnorm : ∀ i, ‖h i‖ ≤ 1) (x : Fin L) :
    (∑ i ∈ Finset.univ.filter (fun i ↦ x ∈ (nearestNeighborChainSupport i).val),
      ‖chainGridRetainedTerm hw h i‖) ≤ 2 := by
  calc
    _ ≤ ∑ i ∈ Finset.univ.filter (fun i ↦ x ∈ (nearestNeighborChainSupport i).val), (1 : ℝ) :=
      Finset.sum_le_sum fun i _ ↦ retained_norm_le_one hw h hnorm i
    _ = ((Finset.univ.filter
        (fun i : Fin (L - 1) ↦ x ∈ (nearestNeighborChainSupport i).val)).card : ℝ) := by simp
    _ ≤ 2 := by exact_mod_cast card_nearestNeighborChainSupport_containing_le_two x

/-- An omitted term is supported on its actual adjacent pair.
Osborne, Figure 1 and equation (3). -/
theorem chainGridBoundaryTerm_supported (hw : 0 < w)
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hs : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) (h i)
      (interval L i.val (i.val + 2))) (k : Fin ((L - 1) / w)) :
    Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) (chainGridBoundaryTerm hw h k)
      (chainCutPair L (chainGridCut w k.val)) := by
  have hneg := isSupportedOn_of_mem_supportedOperators
    (Submodule.neg_mem _
      (mem_supportedOperators_of_isSupportedOn (hs (chainGridBoundaryEdge hw k))))
  rw [chainGrid_boundary_edge_eq_pair k (chainGridBoundaryEdge_val_succ hw k).symm] at hneg
  exact hneg

/-- Explicit localization constants for the retained nearest-neighbor interaction.
Osborne, equations (6)--(12), with the library's chain Lieb--Robinson constants. -/
noncomputable def chainGridLRVelocity : ℝ := 8 * Real.exp 2 + 1

/-- The constant includes the square of the two-site boundary-pair cardinality.
Osborne, equations (6)--(12). -/
noncomputable def chainGridLRPrefactor : ℝ :=
  8 * (2 + 8 * Real.exp 2) * Real.exp 1 / (1 - Real.exp (-(1 / 2)))

/-- The physical localization prefactor is strictly positive.
Osborne, arXiv:quant-ph/0508031v2, equations (6)--(12). -/
theorem chainGridLRPrefactor_pos : 0 < chainGridLRPrefactor := by
  have hden : 0 < 1 - Real.exp (-(1 / 2)) := by
    have h := Real.exp_lt_one_iff.mpr (by norm_num : -(1 / 2 : ℝ) < 0)
    linarith
  unfold chainGridLRPrefactor
  positivity

/-- The actual projected-generator error at an original grid boundary is derived from
the original support, Hermiticity and norm bounds. No localization estimate is an input.
Osborne, arXiv:quant-ph/0508031v2, equations (6)--(12), and Huang, Lemma 19. -/
theorem norm_chainGridBoundaryTerm_sub_siteExpectation_le
    (hq : 1 ≤ q) (hw : 0 < w)
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hs : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) (h i)
      (interval L i.val (i.val + 2))) (hHerm : ∀ i, (h i).IsHermitian)
    (hnorm : ∀ i, ‖h i‖ ≤ 1) (k : Fin ((L - 1) / w)) (r : ℕ) (t : ℝ) :
    ‖heisenbergEvolution (chainGridRetainedHamiltonian hw h) t (chainGridBoundaryTerm hw h k) -
      siteExpectation q (chainCutBuffer L (chainGridCut w k.val) r)
        (heisenbergEvolution (chainGridRetainedHamiltonian hw h) t
          (chainGridBoundaryTerm hw h k))‖ ≤
      chainGridLRPrefactor * Real.exp (chainGridLRVelocity * |t| - (r : ℝ) / 2) := by
  let C : ℝ := 2 * (2 + 8 * Real.exp 2) * Real.exp 1 / (1 - Real.exp (-(1 / 2)))
  let S := chainCutPair L (chainGridCut w k.val)
  have hden : 0 < 1 - Real.exp (-(1 / 2)) := by
    have h := Real.exp_lt_one_iff.mpr (by norm_num : -(1 / 2 : ℝ) < 0)
    linarith
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hcard : (S.card : ℝ) ^ 2 ≤ 4 := by
    have hc : S.card ≤ 2 :=
      (card_interval_le (chainGridCut w k.val - 1) (chainGridCut w k.val + 1)).trans (by omega)
    have hcR : (S.card : ℝ) ≤ 2 := by exact_mod_cast hc
    nlinarith [(Nat.cast_nonneg S.card : (0 : ℝ) ≤ S.card)]
  have hB : ‖chainGridBoundaryTerm hw h k‖ ≤ 1 := by
    simpa only [chainGridBoundaryTerm, norm_neg] using hnorm (chainGridBoundaryEdge hw k)
  have hcoef : C * (S.card : ℝ) ^ 2 * ‖chainGridBoundaryTerm hw h k‖ ≤ chainGridLRPrefactor := by
    calc
      _ ≤ C * 4 * 1 := by gcongr
      _ = chainGridLRPrefactor := by unfold C chainGridLRPrefactor; ring
  have hLR := norm_heisenberg_sub_siteExpectation_chainNeighborhood_le
    nearestNeighborChainSupport (chainGridRetainedTerm hw h) (retained_hermitian hw h hHerm)
    (retained_support hw h hs) 2 (chainGridRetained_site_budget hw h hnorm) hq S
    (chainGridBoundaryTerm_supported hw h hs k) (r : ℝ) (Nat.cast_nonneg r) t
  rw [sum_chainGridRetainedTerm,
    chainNeighborhood_chainCutPair_eq (chainGridCut_bounds hw k).1 (chainGridCut_bounds hw k).2 r]
    at hLR
  have hLR' : ‖heisenbergEvolution (chainGridRetainedHamiltonian hw h) t
        (chainGridBoundaryTerm hw h k) -
      siteExpectation q (chainCutBuffer L (chainGridCut w k.val) r)
        (heisenbergEvolution (chainGridRetainedHamiltonian hw h) t
          (chainGridBoundaryTerm hw h k))‖ ≤
      C * (S.card : ℝ) ^ 2 * ‖chainGridBoundaryTerm hw h k‖ *
        Real.exp (chainGridLRVelocity * |t| - (r : ℝ) / 2) := by
    convert hLR using 1
    norm_num [C, chainGridLRVelocity]
  exact hLR'.trans (mul_le_mul_of_nonneg_right hcoef (Real.exp_pos _).le)

end TNLean.MPS.AreaLaw
