/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.GroundStateAlgorithm.GaussianFilter.GridEvolution
import QICLean.ManyBody.Sites.Lattice.ChainBlocks
import TNLean.MPS.AreaLaw.GroundStateAlgorithm.GaussianFilter.GridLocalization
import TNLean.MPS.AreaLaw.GroundStateAlgorithm.GaussianFilter.BlockProductBonds
import QICLean.ManyBody.Dynamics.DisjointRelativeEvolution
import QICLean.ManyBody.Sites.PlacedConfiguration
import QICLean.ManyBody.Sites.Product.ProductVector
import QICLean.ManyBody.Entropy.Filter.Optimizer
import QICLean.ManyBody.Dynamics.GraphLocalization

/-!
# A physical two-layer approximation to chain propagation

The support layouts, within-block Hamiltonians, omitted edges and localized boundary
evolutions are all constructed from the original nearest-neighbor terms. The resulting
single full-chain operator has a simultaneous operator-Schmidt bound at every cut and
an operator-norm error estimated from the derived Lieb--Robinson generator errors.

Source: Osborne, arXiv:quant-ph/0508031v2, Figure 2 and equations (2)--(13);
Huang, arXiv:1406.6355v6, Section 5.4, Lemma 19.
-/

open ManyBody (interval)

open Matrix QuantumCircuit
open scoped BigOperators Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw

variable {L q w r : ℕ}

private theorem rank_two_grid_layers_le (hq : 1 ≤ q) (hwidth : 2 * r + 2 ≤ w)
    (P : Fin (L / w + 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (Q : Fin ((L - 1) / w) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hP : ∀ j, P j ∈ ManyBody.supportedOperators (fun _ ↦ Fin q)
        (ManyBody.chainGridBlock L w j.val : Finset (Fin L)))
    (hQ : ∀ j, Q j ∈ ManyBody.supportedOperators (fun _ ↦ Fin q)
      (ManyBody.chainCutBuffer L (ManyBody.chainGridCut w j.val) r : Finset (Fin L))) :
    ∀ cut : ℕ, operatorSchmidtRank (ManyBody.cutOperator (X := fun _ ↦ Fin q)
      (interval L 0 cut) ((List.ofFn P).prod * (List.ofFn Q).prod)) ≤
        q ^ (2 * (w + (2 * r + 2))) := by
  have hpairP : (List.ofFn (fun j : Fin (L / w + 1) ↦ j)).Pairwise
      (fun j k ↦ Disjoint (interval L (j.val * w) ((j.val + 1) * w))
        (interval L (k.val * w) ((k.val + 1) * w))) :=
    List.pairwise_ofFn.mpr fun _ _ hjk ↦
      ManyBody.pairwise_disjoint_chainGridBlock L w (ne_of_lt hjk)
  have hpairQ : (List.ofFn (fun j : Fin ((L - 1) / w) ↦ j)).Pairwise
      (fun j k ↦ Disjoint
        (ManyBody.chainCutBuffer L (ManyBody.chainGridCut w j.val) r)
        (ManyBody.chainCutBuffer L (ManyBody.chainGridCut w k.val) r)) :=
    List.pairwise_ofFn.mpr fun _ _ hjk ↦
      ManyBody.pairwise_disjoint_chainGridBuffer L hwidth (ne_of_lt hjk)
  have h := operatorSchmidtRank_two_interval_layers_le hq
    (fun j : Fin (L / w + 1) ↦ j.val * w) (fun j ↦ (j.val + 1) * w)
    (fun j : Fin ((L - 1) / w) ↦ ManyBody.chainGridCut w j.val - 1 - r)
    (fun j ↦ ManyBody.chainGridCut w j.val + r + 1) P Q
    (fun j ↦ (hP j))
    (fun j ↦ (hQ j))
    (List.ofFn (fun j : Fin (L / w + 1) ↦ j))
    (List.ofFn (fun j : Fin ((L - 1) / w) ↦ j)) hpairP hpairQ w (2 * r + 2)
    (fun j _ ↦ (ManyBody.chainGridBlock_width w j.val).le)
    (fun j _ ↦ ManyBody.chainCutBuffer_width_le (ManyBody.chainGridCut w j.val) r)
  simpa only [List.map_ofFn, Function.comp_def] using h

/-- **The two-layer grid propagator.** The product of the block evolutions of the retained
Hamiltonian, followed by the product of the chosen projected propagators of the omitted
boundary terms on their buffers. Osborne, arXiv:quant-ph/0508031v2, Figure 2 and
equations (2)--(13); Huang, arXiv:1406.6355v6, Section 5.4, Lemma 19. -/
noncomputable def chainGridPropagator (hw : 0 < w) (r : ℕ)
    (Φ : ManyBody.BondInteraction L q)
    (hHerm : ∀ i, (Φ.term i).IsHermitian) (t : ℝ) : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ :=
  (List.ofFn fun j ↦ hermitianUnitaryPath (chainGridBlockHamiltonian hw Φ j) (-t)).prod *
    (List.ofFn fun j ↦ ManyBody.disjointProjectedPropagator
      (fun k : Fin ((L - 1) / w) ↦ ManyBody.chainCutBuffer L (ManyBody.chainGridCut w k.val) r)
      (A := chainGridRetainedHamiltonian hw Φ)
      (Matrix.isHermitian_sum _ fun j _ ↦ isHermitian_chainGridBlockHamiltonian hw Φ hHerm j)
      (chainGridBoundaryTerm hw Φ) (fun k ↦ (hHerm (chainGridBoundaryEdge hw k)).neg) j t).prod

/-- The grid propagator approximates the chain evolution with the Lieb--Robinson error of
the omitted boundary terms, and has simultaneous cut-rank bounds. Neither a partition,
supported propagator nor Lieb--Robinson error is supplied as a hypothesis. Osborne,
arXiv:quant-ph/0508031v2, equations (2)--(13); Huang, Section 5.4, Lemma 19. -/
theorem chainGridPropagator_spec (hq : 1 ≤ q) (hwidth : 2 * r + 2 ≤ w)
    (Φ : ManyBody.BondInteraction L q) (hHerm : ∀ i, (Φ.term i).IsHermitian)
    (hnorm : ∀ i, ‖Φ.term i‖ ≤ 1) (t : ℝ) :
    ‖hermitianUnitaryPath Φ.hamiltonian (-t) -
        chainGridPropagator (w := w) (by omega) r Φ hHerm t‖ ≤
        (((L - 1) / w : ℕ) : ℝ) * chainGridLRPrefactor *
          Real.exp (chainGridLRVelocity * |t| - (r : ℝ) / 2) * |t| ∧
      ∀ cut : ℕ, operatorSchmidtRank
        (ManyBody.cutOperator (X := fun _ ↦ Fin q) (interval L 0 cut)
          (chainGridPropagator (w := w) (by omega) r Φ hHerm t)) ≤
          q ^ (2 * (w + (2 * r + 2))) := by
  classical
  let : NeZero q := ⟨by omega⟩
  have hw : 0 < w := by omega
  let A := chainGridRetainedHamiltonian hw Φ
  let B := chainGridBoundaryTerm hw Φ
  let buffers := fun k : Fin ((L - 1) / w) ↦
    ManyBody.chainCutBuffer L (ManyBody.chainGridCut w k.val) r
  have hA : A.IsHermitian :=
    Matrix.isHermitian_sum _ fun j _ ↦ isHermitian_chainGridBlockHamiltonian hw Φ hHerm j
  have hB : ∀ k, (B k).IsHermitian := fun k ↦ (hHerm (chainGridBoundaryEdge hw k)).neg
  have hbuffers : Pairwise fun j k ↦ Disjoint (buffers j) (buffers k) :=
    fun j k hjk ↦ ManyBody.pairwise_disjoint_chainGridBuffer L hwidth
      (show j.val ≠ k.val from fun heq ↦ hjk (Fin.ext heq))
  obtain ⟨_hU0, _hUd, _hUunit, hUsupport, hcompare⟩ :=
    ManyBody.disjointProjectedPropagator_spec buffers hbuffers hA B hB
  let U := ManyBody.disjointProjectedPropagator buffers hA B hB
  have hK : chainGridPropagator (w := w) (by omega) r Φ hHerm t =
      (List.ofFn fun j ↦ hermitianUnitaryPath (chainGridBlockHamiltonian hw Φ j) (-t)).prod *
        (List.ofFn fun j ↦ U j t).prod := rfl
  rw [hK]
  constructor
  · have herror (k : Fin ((L - 1) / w)) (s : ℝ) (hs' : s ∈ Set.uIcc 0 t) :
        ‖ManyBody.heisenbergEvolution A s (B k) -
          ManyBody.regionExpectation (buffers k) (ManyBody.heisenbergEvolution A s (B k))‖ ≤
          chainGridLRPrefactor * Real.exp (chainGridLRVelocity * |t| - (r : ℝ) / 2) := by
      have hst : |s| ≤ |t| := by
        simpa only [sub_zero] using Set.abs_sub_left_of_mem_uIcc hs'
      have hv : 0 ≤ chainGridLRVelocity := by unfold chainGridLRVelocity; positivity
      exact (norm_chainGridBoundaryTerm_sub_regionExpectation_le hw Φ hHerm hnorm k r s).trans
        (mul_le_mul_of_nonneg_left
          (Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_left hst hv]))
          chainGridLRPrefactor_pos.le)
    have herr := hcompare t (fun _ ↦ chainGridLRPrefactor *
      Real.exp (chainGridLRVelocity * |t| - (r : ℝ) / 2)) fun k s hs ↦ by
        exact herror k s hs
    change ‖hermitianUnitaryPath
        (chainGridRetainedHamiltonian hw Φ - ∑ j, chainGridBoundaryTerm hw Φ j) (-t) -
      hermitianUnitaryPath (chainGridRetainedHamiltonian hw Φ) (-t) *
        (List.ofFn fun j ↦ U j t).prod‖ ≤ _ at herr
    rw [← sum_eq_chainGridRetained_sub_boundary hw Φ,
      hermitianUnitaryPath_chainGridRetained_eq_prod hw Φ] at herr
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      mul_assoc] using herr
  · exact rank_two_grid_layers_le hq hwidth _ _
      (fun j ↦ chainGridBlockEvolution_mem_supported hw Φ j (-t))
      (fun j ↦ (hUsupport j t))

/-- The original physical interaction determines one two-layer propagator approximation
with simultaneous cut-rank bounds: the existence form of `chainGridPropagator_spec`.
Osborne, arXiv:quant-ph/0508031v2, equations (2)--(13); Huang, Section 5.4, Lemma 19. -/
theorem exists_chainGrid_propagator_approximation (hq : 1 ≤ q) (hwidth : 2 * r + 2 ≤ w)
    (Φ : ManyBody.BondInteraction L q) (hHerm : ∀ i, (Φ.term i).IsHermitian)
    (hnorm : ∀ i, ‖Φ.term i‖ ≤ 1) :
    ∃ K : ℝ → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ, ∀ t : ℝ,
      ‖hermitianUnitaryPath Φ.hamiltonian (-t) - K t‖ ≤
        (((L - 1) / w : ℕ) : ℝ) * chainGridLRPrefactor *
          Real.exp (chainGridLRVelocity * |t| - (r : ℝ) / 2) * |t| ∧
      ∀ cut : ℕ, operatorSchmidtRank
        (ManyBody.cutOperator (X := fun _ ↦ Fin q) (interval L 0 cut) (K t)) ≤
          q ^ (2 * (w + (2 * r + 2))) :=
  ⟨chainGridPropagator (w := w) (by omega) r Φ hHerm,
    chainGridPropagator_spec hq hwidth Φ hHerm hnorm⟩

end TNLean.MPS.AreaLaw
