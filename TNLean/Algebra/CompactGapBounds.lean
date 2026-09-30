/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Topology.Compactness.Compact
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Lattice.Fold

/-!
# Uniform bounds from local bounds on a compact set

A neighborhood bound at each parameter can be made uniform on a compact
parameter set when it persists after decreasing its positive real constant
and increasing its natural-number threshold. The finite subcover provides
finitely many local bounds; their minimum and maximum give the uniform ones.

This is the compactness step in the gap argument of arXiv:1010.3732,
Appendix A. No spectral assertion is built into this lemma.
-/

open scoped Topology

namespace IsCompact

/-- A positive constant and a natural-number threshold, valid locally at
every point of a compact set, can be chosen uniformly when the assertion is
monotone under weakening these bounds. Source: arXiv:1010.3732, Appendix A. -/
theorem exists_uniform_pos_nat_bounds {X : Type*} [TopologicalSpace X]
    {S : Set X} (hS : IsCompact S) (P : ℝ → ℕ → X → Prop)
    (hδ : ∀ {δ δ' : ℝ} {N : ℕ} {x : X}, δ ≤ δ' → P δ' N x → P δ N x)
    (hN : ∀ {δ : ℝ} {N N' : ℕ} {x : X}, N ≤ N' → P δ N x → P δ N' x)
    (hlocal : ∀ x ∈ S, ∃ δ : ℝ, 0 < δ ∧
      ∃ N : ℕ, ∀ᶠ y in 𝓝 x, P δ N y) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ N : ℕ, ∀ x ∈ S, P δ N x := by
  classical
  have hlocal' : ∀ x : S, ∃ b : ℝ × ℕ,
      0 < b.1 ∧ ∀ᶠ y in 𝓝 (x : X), P b.1 b.2 y := by
    intro x
    obtain ⟨δ, hδpos, N, hnear⟩ := hlocal x x.property
    exact ⟨(δ, N), hδpos, hnear⟩
  choose b hb using hlocal'
  let U : ∀ x ∈ S, Set X := fun x hx ↦
    {y | P (b ⟨x, hx⟩).1 (b ⟨x, hx⟩).2 y}
  obtain ⟨t, hcover⟩ := hS.elim_nhds_subcover' U (by
    intro x hx
    exact (hb ⟨x, hx⟩).2)
  by_cases ht : t.Nonempty
  · let δ : ℝ := t.inf' ht (fun x ↦ (b x).1)
    let N : ℕ := t.sup (fun x ↦ (b x).2)
    have hδpos : 0 < δ := (Finset.lt_inf'_iff _).2 (by
      intro x _
      exact (hb x).1)
    refine ⟨δ, hδpos, N, ?_⟩
    intro x hx
    have hxcover := hcover hx
    simp only [Set.mem_iUnion] at hxcover
    obtain ⟨j, hj, hxj⟩ := hxcover
    have hδj : δ ≤ (b j).1 := Finset.inf'_le _ hj
    have hNj : (b j).2 ≤ N := Finset.le_sup (f := fun x ↦ (b x).2) hj
    exact hN hNj (hδ hδj hxj)
  · have ht0 : t = ∅ := Finset.not_nonempty_iff_eq_empty.mp ht
    refine ⟨1, zero_lt_one, 0, ?_⟩
    intro x hx
    have hfalse : False := by simpa [ht0] using (hcover hx)
    exact hfalse.elim

end IsCompact
