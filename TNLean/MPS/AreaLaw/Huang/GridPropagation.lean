/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.Huang.GridEvolution
import TNLean.MPS.AreaLaw.Huang.GridLocalization
import TNLean.MPS.AreaLaw.Huang.BlockProductBonds
import TNLean.Circuit.DisjointRelativeEvolution

/-!
# A physical two-layer approximation to chain propagation

The support layouts, within-block Hamiltonians, omitted edges and localized boundary
evolutions are all constructed from the original nearest-neighbor terms. The resulting
single full-chain operator has a simultaneous operator-Schmidt bound at every cut and
an operator-norm error estimated from the derived Lieb--Robinson generator errors.

Source: Osborne, arXiv:quant-ph/0508031v2, Figure 2 and equations (2)--(13);
Huang, arXiv:1406.6355v6, Section 5.4, Lemma 19.
-/

open Matrix QuantumCircuit
open scoped BigOperators Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw

variable {L q w r : ℕ}

private theorem rank_two_grid_layers_le (hq : 1 ≤ q) (hwidth : 2 * r + 2 ≤ w)
    (P : Fin (L / w + 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (Q : Fin ((L - 1) / w) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hP : ∀ j, P j ∈ supportedOperators q (chainGridBlock L w j.val : Set (Fin L)))
    (hQ : ∀ j, Q j ∈ supportedOperators q
      (chainCutBuffer L (chainGridCut w j.val) r : Set (Fin L))) :
    ∀ cut : ℕ, operatorSchmidtRank (Entropy.cutOperator (n := fun _ : Fin L ↦ q)
      (leftBlock L cut) ((List.ofFn P).prod * (List.ofFn Q).prod)) ≤
        q ^ (2 * (w + (2 * r + 2))) := by
  have hpairP : (List.ofFn (fun j : Fin (L / w + 1) ↦ j)).Pairwise
      (fun j k ↦ Disjoint (interval L (j.val * w) ((j.val + 1) * w))
        (interval L (k.val * w) ((k.val + 1) * w))) :=
    List.pairwise_ofFn.mpr fun _ _ hjk ↦ pairwise_disjoint_chainGridBlock L w (ne_of_lt hjk)
  have hpairQ : (List.ofFn (fun j : Fin ((L - 1) / w) ↦ j)).Pairwise
      (fun j k ↦ Disjoint
        (chainCutBuffer L (chainGridCut w j.val) r)
        (chainCutBuffer L (chainGridCut w k.val) r)) :=
    List.pairwise_ofFn.mpr fun _ _ hjk ↦ pairwise_disjoint_chainGridBuffer L hwidth (ne_of_lt hjk)
  have h := operatorSchmidtRank_two_interval_layers_le hq
    (fun j : Fin (L / w + 1) ↦ j.val * w) (fun j ↦ (j.val + 1) * w)
    (fun j : Fin ((L - 1) / w) ↦ chainGridCut w j.val - 1 - r)
    (fun j ↦ chainGridCut w j.val + r + 1) P Q
    (fun j ↦ isSupportedOn_of_mem_supportedOperators (hP j))
    (fun j ↦ isSupportedOn_of_mem_supportedOperators (hQ j))
    (List.ofFn (fun j : Fin (L / w + 1) ↦ j))
    (List.ofFn (fun j : Fin ((L - 1) / w) ↦ j)) hpairP hpairQ w (2 * r + 2)
    (fun j _ ↦ (chainGridBlock_width w j.val).le)
    (fun j _ ↦ chainCutBuffer_width_le (chainGridCut w j.val) r)
  simpa only [List.map_ofFn, Function.comp_def] using h

/-- The original physical interaction determines one two-layer propagator approximation
with simultaneous cut-rank bounds. Neither a partition, supported propagator nor
Lieb--Robinson error is supplied as a hypothesis. Osborne,
arXiv:quant-ph/0508031v2, equations (2)--(13); Huang, Section 5.4, Lemma 19. -/
theorem exists_chainGrid_propagator_approximation (hq : 1 ≤ q) (hwidth : 2 * r + 2 ≤ w)
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hs : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) (h i)
      (interval L i.val (i.val + 2))) (hHerm : ∀ i, (h i).IsHermitian)
    (hnorm : ∀ i, ‖h i‖ ≤ 1) :
    ∃ K : ℝ → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ, ∀ t : ℝ,
      ‖hermitianUnitaryPath (∑ i, h i) (-t) - K t‖ ≤
        (((L - 1) / w : ℕ) : ℝ) * chainGridLRPrefactor *
          Real.exp (chainGridLRVelocity * |t| - (r : ℝ) / 2) * |t| ∧
      ∀ cut : ℕ, operatorSchmidtRank
        (Entropy.cutOperator (n := fun _ : Fin L ↦ q) (leftBlock L cut) (K t)) ≤
          q ^ (2 * (w + (2 * r + 2))) := by
  classical
  let : NeZero q := ⟨by omega⟩
  have hw : 0 < w := by omega
  let A := chainGridRetainedHamiltonian hw h
  let B := chainGridBoundaryTerm hw h
  let buffers := fun k : Fin ((L - 1) / w) ↦ chainCutBuffer L (chainGridCut w k.val) r
  have hA : A.IsHermitian :=
    Matrix.isHermitian_sum _ fun j _ ↦ isHermitian_chainGridBlockHamiltonian hw h hHerm j
  have hB : ∀ k, (B k).IsHermitian := fun k ↦ (hHerm (chainGridBoundaryEdge hw k)).neg
  have hbuffers : Pairwise fun j k ↦ Disjoint (buffers j : Set (Fin L)) (buffers k : Set (Fin L)) :=
    fun j k hjk ↦ Finset.disjoint_coe.mpr (pairwise_disjoint_chainGridBuffer L hwidth
      (show j.val ≠ k.val from fun heq ↦ hjk (Fin.ext heq)))
  obtain ⟨U, _hU0, _hUd, _hUunit, hUsupport, hcompare⟩ :=
    exists_disjoint_projected_propagator_approximation q buffers hbuffers hA B hB
  let K := fun t : ℝ ↦
    (List.ofFn fun j ↦ hermitianUnitaryPath (chainGridBlockHamiltonian hw h j) (-t)).prod *
      (List.ofFn fun j ↦ U j t).prod
  refine ⟨K, ?_⟩
  intro t
  constructor
  · have herror (k : Fin ((L - 1) / w)) (s : ℝ) (hs' : s ∈ Set.uIcc 0 t) :
        ‖heisenbergEvolution A s (B k) -
          siteExpectation q (buffers k) (heisenbergEvolution A s (B k))‖ ≤
          chainGridLRPrefactor * Real.exp (chainGridLRVelocity * |t| - (r : ℝ) / 2) := by
      have hst : |s| ≤ |t| := by
        simpa only [sub_zero] using Set.abs_sub_left_of_mem_uIcc hs'
      have hv : 0 ≤ chainGridLRVelocity := by unfold chainGridLRVelocity; positivity
      exact (norm_chainGridBoundaryTerm_sub_siteExpectation_le hq hw h hs hHerm hnorm k r s).trans
        (mul_le_mul_of_nonneg_left
          (Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_left hst hv]))
          chainGridLRPrefactor_pos.le)
    have herr := hcompare t (fun _ ↦ chainGridLRPrefactor *
      Real.exp (chainGridLRVelocity * |t| - (r : ℝ) / 2)) herror
    change ‖hermitianUnitaryPath
        (chainGridRetainedHamiltonian hw h - ∑ j, chainGridBoundaryTerm hw h j) (-t) -
      hermitianUnitaryPath (chainGridRetainedHamiltonian hw h) (-t) *
        (List.ofFn fun j ↦ U j t).prod‖ ≤ _ at herr
    rw [← sum_eq_chainGridRetained_sub_boundary hw h,
      hermitianUnitaryPath_chainGridRetained_eq_prod hw h hs] at herr
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      mul_assoc] using herr
  · exact rank_two_grid_layers_le hq hwidth _ _
      (fun j ↦ chainGridBlockEvolution_mem_supported hw h hs j (-t))
      (fun j ↦ hUsupport j t)

end TNLean.MPS.AreaLaw
