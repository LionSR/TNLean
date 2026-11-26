/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.GroundPath.ExactGroundPathGaussianFilter
import TNLean.MPS.Symmetry.PeriodicRay.PositiveRayExpectations
import TNLean.MPS.CanonicalForm.Correlation.WindowSeparation
import QICLean.ManyBody.Sites.Placement.PlaceAlong
import QICLean.ManyBody.Sites.Lattice.Chain

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

open Matrix QuantumCircuit MPSPreparation
open scoped Matrix.Norms.L2Operator InnerProductSpace

namespace MPSTensor

private theorem card_window_le (N a L : ℕ) : (window N a L).card ≤ L := by
  have hMaps : Set.MapsTo (fun k : Fin N ↦ k.val - a)
      (window N a L) (Finset.range L) := by
    intro k hk
    simp only [window, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ,
      true_and] at hk
    simp only [Finset.mem_coe, Finset.mem_range]
    omega
  have hInj : Set.InjOn (fun k : Fin N ↦ k.val - a) (window N a L) := by
    intro i hi j hj heq
    simp only [window, Finset.mem_coe, Finset.mem_filter,
      Finset.mem_univ, true_and] at hi hj
    have heq' : (i : ℕ) - a = (j : ℕ) - a := heq
    exact Fin.ext (by omega)
  simpa only [Finset.card_range] using
    Finset.card_le_card_of_injOn (fun k : Fin N ↦ k.val - a) hMaps hInj

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
  let F := window N 0 L
  let F' := window N (L + t) L
  have hF : F.Nonempty := by
    refine ⟨⟨0, by omega⟩, ?_⟩
    simp [F, window, hL]
  have hF' : F'.Nonempty := by
    refine ⟨⟨L + t, by dsimp only [N]; omega⟩, ?_⟩
    simp [F', window, hL]
  have hSep : ManyBody.IsGraphSeparated (SimpleGraph.cycleGraph N) F F' t := by
    exact isGraphSeparated_window (by omega) (by dsimp only [N]; omega)
  have hDist : (t : ℝ) ≤ ManyBody.ringSupportDistance (F : Set (Fin N))
      (F' : Set (Fin N)) hF hF' := by
    exact_mod_cast
      ((ManyBody.isGraphSeparated_iff_lt_ringSupportDistance _ _ hF hF' t).mp hSep).le
  have hDisj : Disjoint (F : Set (Fin N)) (F' : Set (Fin N)) := by
    apply Set.disjoint_left.mpr
    intro k hk hk'
    simp only [F, F', window, Finset.mem_coe, Finset.mem_filter,
      Finset.mem_univ, true_and] at hk hk'
    omega
  have h0 : 0 + L ≤ N := by dsimp only [N]; omega
  have hLt : L + t + L ≤ N := by dsimp only [N]; omega
  have hX : ManyBody.placeAlong (X := fun _ ↦ Fin d) (ManyBody.chainWindow 0 h0) X ∈
      ManyBody.supportedOperators (fun _ ↦ Fin d) F := by
    have hmem := ManyBody.placeAlong_mem_supportedOperators (X := fun _ ↦ Fin d)
      (ManyBody.chainWindow 0 h0) X
    rw [ManyBody.map_chainWindow] at hmem
    exact hmem
  have hY : ManyBody.placeAlong (X := fun _ ↦ Fin d) (ManyBody.chainWindow (L + t) hLt) Y ∈
      ManyBody.supportedOperators (fun _ ↦ Fin d) F' := by
    have hmem := ManyBody.placeAlong_mem_supportedOperators (X := fun _ ↦ Fin d)
      (ManyBody.chainWindow (L + t) hLt) Y
    rw [ManyBody.map_chainWindow] at hmem
    exact hmem
  have h := hEst γ hγ N hN (ManyBody.placeAlong (X := fun _ ↦ Fin d) (ManyBody.chainWindow 0 h0) X)
    (ManyBody.placeAlong (X := fun _ ↦ Fin d) (ManyBody.chainWindow (L + t) hLt) Y)
    F F' hF hF' hX hY hDisj t (by exact_mod_cast ht) hDist
  have hNormX := ManyBody.norm_placeAlong_le (X := fun _ ↦ Fin d) (ManyBody.chainWindow 0 h0) X
  have hNormY := ManyBody.norm_placeAlong_le (X := fun _ ↦ Fin d)
    (ManyBody.chainWindow (L + t) hLt) Y
  have hCard : (F.card : ℝ) ≤ L := by exact_mod_cast card_window_le N 0 L
  change ‖mpvConnectedCorrelator (Q.tensor γ) N 0 (L + t) X Y‖ ≤ _
  simp only [mpvConnectedCorrelator, mpvExpectation_eq_inner_div_norm_sq]
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
