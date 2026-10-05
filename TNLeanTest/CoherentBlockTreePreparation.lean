/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.SupportedLogLogPreparation

/-! Regression checks for actual-ring support and exact root-register placement.

## References

* arXiv:2307.01696, eqs. (11), (16), and "Tree-RG circuit with measurements".
-/

open Matrix MPSTensor MPSPreparation QuantumCircuit
open scoped BigOperators

-- A one-block exact consumer asks for support only at M = 1, never at all ring sizes.
example {d D : ℕ} (hd : 2 ≤ d) (A : MPSTensor d D) (S : Finset (Fin D × Fin D)) (L : ℕ)
    (hinj : ∀ m, L ≤ m → IsInjectiveOn (blockTensor A m) (S : Set _)) :
    ∃ s C : ℕ, 2 ≤ s ∧ L ≤ s ∧ ∀ h N [NeZero N],
      2 ^ (h + 2) * s ≤ N → N ≤ 2 ^ (h + 1) * (8 * s) →
      ∀ (ω : Fin D × Fin D → ℂ), (∑ p, star (ω p) * ω p = 1) →
      (∀ x : Fin 1 → Fin D × Fin D, pairProductState ω x ≠ 0 → ∀ k, x k ∈ S) →
      IsPreparedWithMeasurementRoundsInDepth (C * (h + 1))
        (fun x => blockIsometryState A ω (N := N) (ℓ := fun _ : Fin 1 => N) (by simp) x) := by
  obtain ⟨s, C, hs, hLs, hC⟩ := exists_supported_block_preparation_constants hd A S 1 L hinj
  refine ⟨s, C, hs, hLs, fun h N _ hlo hhi ω hω hωS => ?_⟩
  have hp := hC (b := 1) le_rfl h (N := N) (fun _ : Fin 1 => N) (by simp) (fun _ => hlo)
    (fun _ => hhi) (fun _ => ω) (fun j j' => by simpa [Subsingleton.elim j j'] using hω)
    (fun _ x => hωS x) (fun _ => 1) (by simp)
  simpa only [Fin.sum_univ_one, one_mul] using hp

private def diagonalPair (p : Fin 2 × Fin 2) : ℂ := if p.1 = p.2 then 1 else 0

-- This distinction is substantive: a coherent diagonal pair has one-block diagonal support.
example (x : Fin 1 → Fin 2 × Fin 2) (hx : pairProductState diagonalPair x ≠ 0) :
    ∀ k, (x k).1 = (x k).2 := by
  have hrot : finRotate 1 0 = 0 := Subsingleton.elim _ _
  simp only [pairProductState, Fin.prod_univ_one, hrot, diagonalPair] at hx
  intro k
  rw [Subsingleton.elim k 0]
  split_ifs at hx with h
  · exact h.symm
  · exact (hx rfl).elim

-- The same pair has a nonzero two-block amplitude on off-diagonal block inputs.
example : pairProductState diagonalPair ![(0, 1), (1, 0)] = 1 := by
  have h0 : finRotate 2 0 = 1 := by decide
  have h1 : finRotate 2 1 = 0 := by decide
  norm_num [pairProductState, diagonalPair, Fin.prod_univ_two, h0, h1]

-- Both even and odd singleton block lengths align the padded physical inputs exactly.
example (δ : Fin 2) (l r : Fin 2) :
    let n := 8 + δ.val
    let dig : Fin 2 → Cfg 2 2 := fun a => ![a, 0]
    let hT := isTreeLayout_balancedWidths (h := 0) (s := 2) (L := n) (by omega)
    blockInputCfg (by decide) n dig l r =
      placeCfg (fun p : Fin (2 ^ 0) => nodeWindow hT 0 p)
        (fun _ => blockInputCfg (by decide) n dig l r ∘ nodeWindow hT 0 0) := by
  dsimp only
  exact blockInputCfg_eq_placeCfg _ (le_leafOffset_balancedWidths_add_one 0 (8 + δ.val))
    (fun _ => by simp) l r
