/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Circuit.Measurement.CoherentRounds
import TNLean.Circuit.Teleportation.ZeroSubspace
import TNLean.MPS.Preparation.UnequalRegisterTreeState

/-!
# Measurement implementation of coherent isometry trees

Binary trees with fixed-width registers and uniformly bounded physical leaves have
measurement implementations in depth proportional to their height. The virtual dimension
is arbitrary. Each round implements the same linear map on every admissible input, with an
outcome scalar independent of that input, so superpositions across canonical sectors remain
coherent. The output equality includes all physical sites, including the temporary registers.

Source: arXiv:2307.01696, eq. (16) and "Tree-RG circuit with measurements".

## References

* arXiv:2307.01696, "Tree-RG circuit with measurements" and
  "Long-range MPS using measurements".
-/

open Matrix MPSTensor
open scoped BigOperators
open QuantumCircuit TeleportHop

namespace MPSPreparation

/-- Trees on arbitrary disjoint blocks are implemented by measurement rounds in depth
`C (h + 1)`, where `C` depends only on the physical dimension, register width and leaf bound.
The rounds act simultaneously on all inputs having zero at the interior scratch sites.

Source: arXiv:2307.01696, "Tree-RG circuit with measurements". -/
theorem exists_rounds_blockLayerOp_treeBlockOp (d s c : ℕ) [NeZero d] [NeZero s] :
    ∃ C : ℕ, ∀ {χ : ℕ} (V : (m : ℕ) → Matrix (Cfg d m) (Fin χ) ℂ)
      (W : ℕ → ℕ → Matrix (Fin (blockPhysDim χ 2)) (Fin χ) ℂ)
      (h : ℕ) {M N : ℕ} [NeZero N] (ℓ : Fin M → ℕ) (hN : ∑ b, ℓ b = N)
      (w : Fin M → ℕ → ℕ) (hT : ∀ b, IsTreeLayout h s (ℓ b) (w b)),
      (∀ b (p : Fin (2 ^ (h + 1))), leafLen h (ℓ b) (w b) p ≤ c) →
      ∀ (ι₀ : Fin M → Fin χ → Cfg d (s + s)) (enc : Fin χ → Cfg d s),
      ∃ Rs : List (MeasurementRound d N),
        (Rs.map MeasurementRound.depth).sum ≤ C * (h + 1) ∧
        MeasurementRound.IsRoundsImplementationOn Rs
          {v | IsZeroOn (treeCentralSites h s hN w) v}
          (blockLayerOp hN fun b => treeBlockOp (hT b) V W (ι₀ b) enc) ∧
        ∀ m : MeasurementRound.OutcomeHistory Rs, ∃ a : ℂ,
          ∀ v, IsZeroOn (treeCentralSites h s hN w) v →
            MeasurementRound.historyKraus Rs m *ᵥ v =
              a • ((blockLayerOp hN fun b => treeBlockOp (hT b) V W (ι₀ b) enc) *ᵥ v) := by
  classical
  have hd : 0 < d := NeZero.pos d
  have hs : 1 ≤ s := NeZero.pos s
  obtain ⟨K, hK⟩ := exists_isPairProduct (n := s + s) hd (by omega)
  have hleaf : ∀ n : Fin (c + 1), ∃ K' : ℕ, 2 ≤ n.val →
      ∀ X ∈ unitary (Matrix (Cfg d n) (Cfg d n) ℂ), IsPairProduct d n K' X := fun n => by
    by_cases hn : 2 ≤ n.val
    · obtain ⟨K', hK'⟩ := exists_isPairProduct hd hn
      exact ⟨K', fun _ => hK'⟩
    · exact ⟨0, fun h' => absurd h' hn⟩
  choose Kl hKl using hleaf
  refine ⟨4 * s + K + ∑ n, Kl n + 4,
    fun {χ} V W h {M N} _ ℓ hN w hT hbound ι₀ enc => ?_⟩
  set X := fun b => treeNodeGate (h := h) (n := ℓ b) (w := w b) W (ι₀ b) enc
  set U := fun b => treeLeafGate (hT b) V (ι₀ b) enc
  obtain ⟨Rs, hRs, hRsE⟩ := exists_rounds_blockLayerOp_treeLevelsOp (hN := hN) (hT := hT)
    (X := X) (K := K) fun b j p => hK _ (treeNodeGate_mem_unitary W (ι₀ b) enc j p)
  obtain ⟨Ll, hLl, -, hLlU⟩ := isCircuitOn_blockLayerOp_treeLeafOp (hN := hN) (hT := hT) U
    (K := ∑ n, Kl n) fun b p => by
      have h1 := two_mul_le_leafLen (hT b) p.isLt
      have h2 := hbound b p
      exact (hKl ⟨_, (by omega : leafLen h (ℓ b) (w b) p < c + 1)⟩
        (by simp only; omega) _ (treeLeafGate_mem_unitary (hT b) V (ι₀ b) enc p)).mono
        (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ _))
  have hleafR : MeasurementRound.IsRoundsImplementationOn [round Ll [] valid_nil] Set.univ
      (blockLayerOp hN fun b => treeLeafOp (hT b) (U b)) := by
    have := (isImplementationOn_round (d := d) Ll (valid_nil (N := N))).isRoundsImplementationOn
    rw [chainPerm_nil, Matrix.one_mul, ← hLlU] at this
    exact this.mono fun v _ => fun _ _ _ h => h.elim
  have hall : MeasurementRound.IsRoundsImplementationOn (Rs ++ [round Ll [] valid_nil])
      {v | IsZeroOn (treeCentralSites h s hN w) v}
      (blockLayerOp hN fun b => treeBlockOp (hT b) V W (ι₀ b) enc) := by
    have := hRsE.append hleafR fun _ _ => trivial
    simpa only [← blockLayerOp_mul, treeBlockOp, X, U] using this
  have hunitary : (blockLayerOp hN fun b => treeBlockOp (hT b) V W (ι₀ b) enc) ∈
      unitary (Matrix (Cfg d N) (Cfg d N) ℂ) := by
    rw [blockLayerOp_eq_list_prod]
    apply Submonoid.list_prod_mem
    intro Z hZ
    obtain ⟨b, -, rfl⟩ := List.mem_map.mp hZ
    exact embedOp_mem_unitary (blockSite_injective hN b)
      (treeBlockOp_mem_unitary (hT b) V W (ι₀ b) enc)
  refine ⟨Rs ++ [round Ll [] valid_nil], ?_, hall, ?_⟩
  · simp only [List.map_append, List.sum_append, hRs, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, depth_round, hLl]
    nlinarith
  · exact fun m => hall.exists_history_scalar
      (E := zeroOnSubmodule (treeCentralSites h s hN w)) hunitary m

end MPSPreparation
