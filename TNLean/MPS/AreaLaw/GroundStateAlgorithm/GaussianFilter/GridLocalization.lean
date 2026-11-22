/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.GroundStateAlgorithm.GaussianFilter.GridHamiltonian
import TNLean.MPS.AreaLaw.Chain.LiebRobinson

/-!
# Localization of the omitted boundary terms

The retained interactions are an explicitly selected subfamily of the original
nearest-neighbor interactions. At most two of them meet a site, so their per-site norm
budget is at most two when each original term has norm at most one. The existing chain
Lieb--Robinson theorem then localizes each omitted term to its actual grid buffer.

Source: Osborne, arXiv:quant-ph/0508031v2, equations (6)--(12), and Huang,
arXiv:1406.6355v6, Section 5.4, Lemma 19.

## The original positive nearest-neighbor chain as a finite-range Hamiltonian

The original interaction on each adjacent pair is assigned to that exact range-one
support; every other support receives zero. This is the range-one chain interaction
`ManyBody.BondInteraction.toChainInteraction` of the bond terms. Its operator is exactly the
original interaction sum (`ManyBody.Interaction.hamiltonian_extend`), and for positive
contractions its terms are positive contractions (`ManyBody.Interaction.extend_term_nonneg`,
`ManyBody.Interaction.extend_term_le_one`, `ManyBody.Interaction.norm_extend_term_le`). This
file adds that a bond has two sites, so that the single-site terms vanish.

Source: Landau, Vazirani and Vidick, arXiv:1307.5143v1, `algo53.tex`, the nearest-neighbor
Hamiltonian and local positive-contraction assumptions preceding the viable-set algorithm;
Huang, arXiv:1406.6355v6, Section 5.4, Lemmas 18--19. This identification changes neither
the physical operator nor the spectral hypotheses used by the two constructions.
-/

section

open ManyBody (ChainSupport bondSupport card_interval_le interval mem_interval)

open Matrix QuantumCircuit
open scoped BigOperators Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw

variable {L q w : ℕ}

/-- The retained original interaction, with precisely the grid-boundary terms set to zero.
Osborne, Figure 2. -/
noncomputable def chainGridRetainedTerm (hw : 0 < w)
    (Φ : ManyBody.BondInteraction L q) (i : Fin (L - 1)) :=
  if i ∈ chainGridBoundaryEdges hw then 0 else Φ.term i

/-- Summing the retained interactions gives the constructed within-block Hamiltonian.
Osborne, Figure 2 and equation (3). -/
theorem sum_chainGridRetainedTerm (hw : 0 < w)
    (Φ : ManyBody.BondInteraction L q) :
    (∑ i, chainGridRetainedTerm hw Φ i) = chainGridRetainedHamiltonian hw Φ := by
  classical
  rw [chainGridRetainedHamiltonian_eq_sum_filter]
  simp only [chainGridRetainedTerm, Finset.sum_filter, ite_not]

/-- The original one-dimensional nearest-neighbor incidence count is at most two: a site
lies on at most two bonds. Osborne, the nearest-neighbor Hamiltonian preceding equation (2). -/
theorem card_filter_mem_bondSupport_le_two (x : Fin L) :
    (Finset.univ.filter
      (fun i : Fin (L - 1) ↦ x ∈ (bondSupport i).val)).card ≤ 2 := by
  classical
  apply (Finset.card_le_card_of_injOn (fun i : Fin (L - 1) ↦ i.val)
    (s := Finset.univ.filter fun i ↦ x ∈ (bondSupport i).val)
    (t := {x.val - 1, x.val}) ?_ Fin.val_injective.injOn).trans Finset.card_le_two
  intro i hi
  have hx := (Finset.mem_filter.mp hi).2
  change x ∈ interval L i.val (i.val + 2) at hx
  rw [mem_interval] at hx
  change i.val ∈ ({x.val - 1, x.val} : Finset ℕ)
  simp only [Finset.mem_insert, Finset.mem_singleton]
  omega

private theorem retained_support (hw : 0 < w)
    (Φ : ManyBody.BondInteraction L q) (i : Fin (L - 1)) :
    ManyBody.IsSupportedOn (X := fun _ ↦ Fin q) (chainGridRetainedTerm hw Φ i)
      (bondSupport i).val := by
  change _ ∈ ManyBody.supportedOperators _ _
  classical
  unfold chainGridRetainedTerm
  split_ifs
  · exact zero_mem (ManyBody.supportedOperators (fun _ : Fin L ↦ Fin q) _)
  · exact Φ.mem i

private theorem retained_hermitian (hw : 0 < w)
    (Φ : ManyBody.BondInteraction L q)
    (hHerm : ∀ i, (Φ.term i).IsHermitian) (i : Fin (L - 1)) :
    (chainGridRetainedTerm hw Φ i).IsHermitian := by
  classical
  unfold chainGridRetainedTerm
  split_ifs
  · exact isHermitian_zero
  · exact hHerm i

private theorem retained_norm_le_one (hw : 0 < w)
    (Φ : ManyBody.BondInteraction L q)
    (hnorm : ∀ i, ‖Φ.term i‖ ≤ 1) (i : Fin (L - 1)) : ‖chainGridRetainedTerm hw Φ i‖ ≤ 1 := by
  classical
  unfold chainGridRetainedTerm
  split_ifs
  · simp
  · exact hnorm i

/-- The retained physical interaction has site norm budget at most two, derived from
the original norm bounds. Osborne, equations (6)--(12). -/
theorem chainGridRetained_site_budget (hw : 0 < w)
    (Φ : ManyBody.BondInteraction L q)
    (hnorm : ∀ i, ‖Φ.term i‖ ≤ 1) (x : Fin L) :
    (∑ i ∈ Finset.univ.filter (fun i ↦ x ∈ (bondSupport i).val),
      ‖chainGridRetainedTerm hw Φ i‖) ≤ 2 := by
  calc
    _ ≤ ∑ i ∈ Finset.univ.filter (fun i ↦ x ∈ (bondSupport i).val), (1 : ℝ) :=
      Finset.sum_le_sum fun i _ ↦ retained_norm_le_one hw Φ hnorm i
    _ = ((Finset.univ.filter
        (fun i : Fin (L - 1) ↦ x ∈ (bondSupport i).val)).card : ℝ) := by simp
    _ ≤ 2 := by exact_mod_cast card_filter_mem_bondSupport_le_two x

/-- An omitted term is supported on its actual adjacent pair.
Osborne, Figure 1 and equation (3). -/
theorem chainGridBoundaryTerm_supported (hw : 0 < w)
    (Φ : ManyBody.BondInteraction L q) (k : Fin ((L - 1) / w)) :
    ManyBody.IsSupportedOn (X := fun _ ↦ Fin q) (chainGridBoundaryTerm hw Φ k)
      (chainCutPair L (chainGridCut w k.val)) := by
  change _ ∈ ManyBody.supportedOperators _ _
  have hneg := neg_mem (show _ ∈ ManyBody.supportedOperators _ _ from
    Φ.mem (chainGridBoundaryEdge hw k))
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
theorem norm_chainGridBoundaryTerm_sub_regionExpectation_le
    (hw : 0 < w)
    (Φ : ManyBody.BondInteraction L q) (hHerm : ∀ i, (Φ.term i).IsHermitian)
    (hnorm : ∀ i, ‖Φ.term i‖ ≤ 1) (k : Fin ((L - 1) / w)) (r : ℕ) (t : ℝ) :
    ‖ManyBody.heisenbergEvolution (chainGridRetainedHamiltonian hw Φ) t (chainGridBoundaryTerm hw Φ
        k) -
      ManyBody.regionExpectation (chainCutBuffer L (chainGridCut w k.val) r)
        (ManyBody.heisenbergEvolution (chainGridRetainedHamiltonian hw Φ) t
          (chainGridBoundaryTerm hw Φ k))‖ ≤
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
  have hB : ‖chainGridBoundaryTerm hw Φ k‖ ≤ 1 := by
    simpa only [chainGridBoundaryTerm, norm_neg] using hnorm (chainGridBoundaryEdge hw k)
  have hcoef : C * (S.card : ℝ) ^ 2 * ‖chainGridBoundaryTerm hw Φ k‖ ≤ chainGridLRPrefactor := by
    calc
      _ ≤ C * 4 * 1 := by gcongr
      _ = chainGridLRPrefactor := by unfold C chainGridLRPrefactor; ring
  have hLR := norm_heisenberg_sub_regionExpectation_chainNeighborhood_le
    bondSupport (chainGridRetainedTerm hw Φ) (retained_hermitian hw Φ hHerm)
    (retained_support hw Φ) 2 (chainGridRetained_site_budget hw Φ hnorm) S
    (chainGridBoundaryTerm_supported hw Φ k) (r : ℝ) (Nat.cast_nonneg r) t
  rw [sum_chainGridRetainedTerm,
    chainNeighborhood_chainCutPair_eq (chainGridCut_bounds hw k).1 (chainGridCut_bounds hw k).2 r]
    at hLR
  have hLR' : ‖ManyBody.heisenbergEvolution (chainGridRetainedHamiltonian hw Φ) t
        (chainGridBoundaryTerm hw Φ k) -
      ManyBody.regionExpectation (chainCutBuffer L (chainGridCut w k.val) r)
        (ManyBody.heisenbergEvolution (chainGridRetainedHamiltonian hw Φ) t
          (chainGridBoundaryTerm hw Φ k))‖ ≤
      C * (S.card : ℝ) ^ 2 * ‖chainGridBoundaryTerm hw Φ k‖ *
        Real.exp (chainGridLRVelocity * |t| - (r : ℝ) / 2) := by
    convert hLR using 1
    norm_num [C, chainGridLRVelocity]
  exact hLR'.trans (mul_le_mul_of_nonneg_right hcoef (Real.exp_pos _).le)

end TNLean.MPS.AreaLaw

end

section

open ManyBody (ChainSupport bondSupport mem_interval)

namespace TNLean.MPS.AreaLaw

/-- Every bond contains exactly two sites. This is the adjacent-pair support convention of
LVV13, `algo53.tex`, used in Huang, Section 5.4. -/
theorem card_bondSupport {L : ℕ} (i : Fin (L - 1)) : (bondSupport i).val.card = 2 := by
  let x : Fin L := ⟨i.val, lt_of_lt_of_le i.isLt (Nat.sub_le L 1)⟩
  let y : Fin L := ⟨i.val + 1, by omega⟩
  have hset : (bondSupport i).val = {x, y} := by
    ext v
    simp only [bondSupport, mem_interval, Finset.mem_insert,
      Finset.mem_singleton, Fin.ext_iff, x, y]
    omega
  rw [hset, Finset.card_pair]
  exact fun h ↦ by have := congrArg Fin.val h; dsimp only [x, y] at this; omega

/-- All singleton terms of a bond interaction, read as a range-one chain interaction, are
zero. This preserves the original adjacent-pair model of LVV13, `algo53.tex`. -/
theorem _root_.ManyBody.BondInteraction.toChainInteraction_term_eq_zero_of_card_one {L q : ℕ}
    (Φ : ManyBody.BondInteraction L q) (X : ChainSupport L 1) (hX : X.val.card = 1) :
    Φ.toChainInteraction.term X = 0 := by
  refine ManyBody.Interaction.extend_term_eq_zero fun i hi ↦ ?_
  have := card_bondSupport i
  rw [hi] at this
  omega

end TNLean.MPS.AreaLaw

end
