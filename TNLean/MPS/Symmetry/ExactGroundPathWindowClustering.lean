/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.ExactGroundPathClustering
import TNLean.MPS.Symmetry.PositiveRayExpectations
import TNLean.MPS.Preparation.WindowSeparation

/-!
# Physical clustering for the actual two-window MPS correlator

Place the two length-L observables on a ring of length L+t+L+n, with
n at least t. The two actual windows have separation greater than t;
their embeddings are contractive and the first support has at most L
sites. The common physical clustering bound therefore controls exactly
the finite correlator whose return-length limit defines the transfer
correlation. Equality of positive periodic rays transports the estimate
to any other representative without choosing its gauge continuously.

Source: Hastings–Koma, arXiv:math-ph/0507008, Section 3; SPC11,
arXiv:1010.3732, Section II.F, lines 929–953; arXiv:2307.01696,
Supplemental Material, Lemma 2, the two-window connected correlator.
-/

noncomputable section

open TNLean.Lattice Matrix QuantumCircuit MPSPreparation
open scoped Matrix.Norms.L2Operator InnerProductSpace

namespace MPSTensor

private def windowFinset (N a L : ℕ) : Finset (Fin N) :=
  Finset.univ.filter fun k ↦ a ≤ k.val ∧ k.val < a + L

private theorem coe_windowFinset (N a L : ℕ) :
    (windowFinset N a L : Set (Fin N)) = window N a L := by
  ext k
  simp [windowFinset, window]

private theorem card_windowFinset_le (N a L : ℕ) : (windowFinset N a L).card ≤ L := by
  have hMaps : Set.MapsTo (fun k : Fin N ↦ k.val - a)
      (windowFinset N a L) (Finset.range L) := by
    intro k hk
    simp only [windowFinset, Finset.mem_filter, Finset.mem_univ, true_and] at hk
    simp only [Finset.mem_coe, Finset.mem_range]
    omega
  have hInj : Set.InjOn (fun k : Fin N ↦ k.val - a) (windowFinset N a L) := by
    intro i hi j hj heq
    simp only [windowFinset, Finset.mem_coe, Finset.mem_filter,
      Finset.mem_univ, true_and] at hi hj
    exact Fin.ext (by omega)
  simpa only [Finset.card_range] using
    Finset.card_le_card_of_injOn (fun k : Fin N ↦ k.val - a) hMaps hInj

private theorem norm_window_le {d N a L : ℕ} (ha : a < N) (haL : a + L ≤ N)
    (X : Matrix (Fin L → Fin d) (Fin L → Fin d) ℂ) :
    ‖chainWindowOperator N a X‖ ≤ ‖X‖ := by
  rw [chainWindowOperator_eq_embedLocalOperatorAlgHom ha haL]
  exact MPOTensor.norm_embedLocalOperator_le L N (by omega) ⟨a, ha⟩ X

variable {G : Type} [Group G] {d : ℕ}
  {U : G →* Matrix.unitaryGroup (Fin d) ℂ}
  {h₀ h₁ : MPOTensor.ChainOperator d 2}
  {P : SymmetricGappedInteractionPath U h₀ h₁}

/-- The actual finite two-window connected correlator has one common
exponential rate from the physical MPS gap. Both cyclic gaps are derived
from the return length n≥t; no separation or finite-size convergence
estimate is supplied as an additional premise.
Source: Hastings–Koma, arXiv:math-ph/0507008, Section 3; SPC11,
arXiv:1010.3732, Section II.F, lines 929–953. -/
theorem ExactMPSGroundPath.exists_uniform_window_correlation_bound
    (Q : ExactMPSGroundPath P) :
    ∃ K κ : ℝ, 0 < K ∧ 0 < κ ∧
      ∀ γ ∈ Set.Icc (0 : ℝ) 1, ∀ L : ℕ, 0 < L →
      ∀ X Y : Matrix (Fin L → Fin d) (Fin L → Fin d) ℂ,
      ∀ t : ℕ, 1 ≤ t → ∀ n : ℕ, t ≤ n →
        ‖mpvConnectedCorrelator (Q.tensor γ) (L + t + L + n) 0 (L + t) X Y‖ ≤
          K * ((L : ℝ) + 1) * ‖X‖ * ‖Y‖ * Real.exp (-κ * t) := by
  classical
  obtain ⟨K, κ, hK, hκ, hEst⟩ := Q.exists_uniform_connected_exponential_clustering
  refine ⟨K, κ, hK, hκ, ?_⟩
  intro γ hγ L hL X Y t ht n hn
  let N := L + t + L + n
  have hN : 2 ≤ N := by dsimp only [N]; omega
  let : NeZero N := ⟨by omega⟩
  let F := windowFinset N 0 L
  let F' := windowFinset N (L + t) L
  have hF : F.Nonempty := by
    refine ⟨⟨0, by omega⟩, ?_⟩
    simp [F, windowFinset, hL]
  have hF' : F'.Nonempty := by
    refine ⟨⟨L + t, by dsimp only [N]; omega⟩, ?_⟩
    simp [F', windowFinset, hL]
  have hSep : IsSeparatedBy (F : Set (Fin N)) (F' : Set (Fin N)) t := by
    rw [show (F : Set (Fin N)) = window N 0 L from coe_windowFinset N 0 L,
      show (F' : Set (Fin N)) = window N (L + t) L from coe_windowFinset N (L + t) L]
    exact isSeparatedBy_window (by omega) (by dsimp only [N]; omega)
  have hDist : (t : ℝ) ≤ ringSupportDistance (F : Set (Fin N))
      (F' : Set (Fin N)) hF hF' := by
    exact_mod_cast ((isSeparatedBy_iff_lt_ringSupportDistance _ _ hF hF' t).mp hSep).le
  have hDisj : Disjoint (F : Set (Fin N)) (F' : Set (Fin N)) := by
    apply Set.disjoint_left.mpr
    intro k hk hk'
    simp only [F, F', windowFinset, Finset.mem_coe, Finset.mem_filter,
      Finset.mem_univ, true_and] at hk hk'
    omega
  have hX : chainWindowOperator N 0 X ∈ supportedOperators d (F : Set (Fin N)) := by
    rw [show (F : Set (Fin N)) = window N 0 L from coe_windowFinset N 0 L]
    exact chainWindowOperator_mem_supportedOperators_window (by omega)
      (by dsimp only [N]; omega) X
  have hY : chainWindowOperator N (L + t) Y ∈ supportedOperators d (F' : Set (Fin N)) := by
    rw [show (F' : Set (Fin N)) = window N (L + t) L from coe_windowFinset N (L + t) L]
    exact chainWindowOperator_mem_supportedOperators_window (by dsimp only [N]; omega)
      (by dsimp only [N]; omega) Y
  have h := hEst γ hγ N hN (chainWindowOperator N 0 X)
    (chainWindowOperator N (L + t) Y) F F' hF hF' hX hY hDisj t (by exact_mod_cast ht) hDist
  have hNormX := norm_window_le (N := N) (a := 0) (by omega)
    (by dsimp only [N]; omega) X
  have hNormY := norm_window_le (N := N) (a := L + t) (by dsimp only [N]; omega)
    (by dsimp only [N]; omega) Y
  have hCard : (F.card : ℝ) ≤ L := by exact_mod_cast card_windowFinset_le N 0 L
  change ‖mpvConnectedCorrelator (Q.tensor γ) N 0 (L + t) X Y‖ ≤ _
  simp only [mpvConnectedCorrelator, mpvExpectation_eq_normalizedVectorExpectation]
  exact h.trans (by gcongr)

/-- The same physical window estimate holds for every tensor with the
same positive periodic rays, irrespective of its bond dimension or gauge.
Source: SPC11, arXiv:1010.3732, Section II.F, lines 929–953. -/
theorem ExactMPSGroundPath.exists_uniform_ray_window_correlation_bound
    (Q : ExactMPSGroundPath P) :
    ∃ K κ : ℝ, 0 < K ∧ 0 < κ ∧
      ∀ γ ∈ Set.Icc (0 : ℝ) 1, ∀ D : ℕ, ∀ A : MPSTensor d D,
      SamePositiveMpvRay (Q.tensor γ) A → ∀ L : ℕ, 0 < L →
      ∀ X Y : Matrix (Fin L → Fin d) (Fin L → Fin d) ℂ,
      ∀ t : ℕ, 1 ≤ t → ∀ n : ℕ, t ≤ n →
        ‖mpvConnectedCorrelator A (L + t + L + n) 0 (L + t) X Y‖ ≤
          K * ((L : ℝ) + 1) * ‖X‖ * ‖Y‖ * Real.exp (-κ * t) := by
  obtain ⟨K, κ, hK, hκ, hEst⟩ := Q.exists_uniform_window_correlation_bound
  refine ⟨K, κ, hK, hκ, ?_⟩
  intro γ hγ D A hRay L hL X Y t ht n hn
  rw [← hRay.mpvConnectedCorrelator_eq (by omega) 0 (L + t) X Y]
  exact hEst γ hγ L hL X Y t ht n hn

end MPSTensor
