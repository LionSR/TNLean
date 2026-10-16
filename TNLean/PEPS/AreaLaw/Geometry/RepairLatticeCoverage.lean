/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.InitialLatticePartition
import TNLean.PEPS.AreaLaw.Geometry.RepairMarkMesh
import TNLean.PEPS.AreaLaw.Geometry.RepairReplacementLatticeCoverage

/-!
# Lattice coverage during simultaneous repair

A simultaneous repair preserves coverage of integer lattice points when
terminal-square interiors are included. Nonterminal squares contribute open
replacement regions; terminal squares contribute their interiors. The
translated integer mesh excludes lattice points from either kind of boundary.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 11, replacement instructions, lines 393–417,
and the lattice partition argument, lines 545–561.
Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Written from the manuscript; no upstream Lean text is reused.
-/

noncomputable section

namespace TNLean.PEPS.AreaLaw.Geometry

/-- A lattice point covered before repair belongs either to a next current
region or to a terminal-square interior. The parent centers lie on the
prescribed translated integer mesh, and their scales are at least one.
Source: area-law Section 11, lines 393–417 and 545–561. -/
theorem exists_mem_repairNextCurrentRegion_or_terminalInterior
    {ι κ : Type*} (j : ℕ) (R : ι → Set (ℝ × ℝ))
    (v : κ → ℝ × ℝ) (S : κ → ℝ) (Sstar : ℝ)
    (ξ : ι → Fin 2) (σ : κ → RepairFanSlot → ι)
    (hmesh : ∀ p, v p ∈ affineMesh dyadicOrigin 1)
    (hscale : ∀ p, 1 ≤ S p) (z : ℤ × ℤ)
    (hz : ∃ i, integerPoint z ∈ R i) :
    (∃ i : RepairRegionIndex j S Sstar ξ σ,
      integerPoint z ∈ repairNextCurrentRegion j R v S Sstar ξ σ i) ∨
      integerPoint z ∈ repairTerminalInteriorSet v S Sstar := by
  classical
  by_cases hrem : integerPoint z ∈ repairRemovalSet v S
  · obtain ⟨p, hp⟩ := Set.mem_iUnion.mp hrem
    obtain ⟨H, hH⟩ := exists_mem_repairReplacementOpenRegion_of_mem_repairSquare
      ξ (σ p) (hmesh p) (hscale p) hp
    by_cases hterm : repairHalfSide (S p) < Sstar
    · exact Or.inr (Set.mem_iUnion.mpr ⟨⟨p, hterm⟩,
        interior_mono (repairReplacementBirthRegion_subset_repairSquare _ _ _ _ H) hH⟩)
    · exact Or.inl ⟨.inr (⟨j + 1, rfl⟩, ⟨⟨p, le_of_not_gt hterm⟩, H⟩), hH⟩
  · exact hz.elim fun i hi ↦ Or.inl ⟨.inl i, hi, hrem⟩

variable {Λ : Finset (ℤ × ℤ)} {A : Finset (Site Λ)} {C k₀ : ℕ}
  {hC : 2 ≤ C} {h₀ : 50000000 ≤ k₀} {Sstar : ℝ}

local notation "𝔇" => repairStage dyadicOrigin Λ A C k₀ hC h₀ Sstar

namespace RepairMetricHypotheses

/-- Every lattice point belongs either to an actual current region or to a
terminal-square interior from a strictly earlier generation.
Source: area-law Section 11, lines 393–417 and 545–561; the positive-boundary
assumption of Proposition two-families is at lines 102–105. -/
theorem lattice_mem_current_or_terminal_before {a₀ : ℝ}
    (h : RepairMetricHypotheses (o := dyadicOrigin) (Λ := Λ) (A := A)
      (C := C) (k₀ := k₀) (hC := hC) (h₀ := h₀) (Sstar := Sstar) a₀)
    (hSstar : 1 ≤ Sstar) (hboundary : 0 < (edgeBoundary Λ A).card)
    (j : ℕ) (z : ℤ × ℤ) :
    (∃ i : (𝔇 j).regionIndex, integerPoint z ∈ (𝔇 j).current i) ∨
      ∃ t < j, integerPoint z ∈
        repairTerminalInteriorSet (𝔇 t).location (𝔇 t).scale Sstar := by
  classical
  have hZ : (boundaryEndpoints Λ A).Nonempty :=
    (Finset.card_pos.mp hboundary).elim fun e he ↦
      (Sym2.mk_surjective e).elim fun uv huv ↦
        ⟨uv.1.1, mem_boundaryEndpoints_of_mem_edgeBoundary he
          (huv ▸ Sym2.mem_mk_left uv.1 uv.2)⟩
  induction j with
  | zero =>
    exact Or.inl (exists_unique_initialOpenRegion_integerPoint
      k₀ (boundaryEndpoints Λ A) C _ _ hC h₀ hZ z).exists
  | succ j ih =>
    rcases ih with hi | ht
    · let : Nonempty (𝔇 j).regionIndex := ⟨(𝔇 j).dummy⟩
      rcases exists_mem_repairNextCurrentRegion_or_terminalInterior j
        (𝔇 j).current (𝔇 j).location (𝔇 j).scale Sstar (𝔇 j).color
        (repairCurrentAssignments (𝔇 j).current (𝔇 j).location (𝔇 j).scale)
        (h.repairStage_location_mem_affineMesh hSstar j)
        (fun p ↦ hSstar.trans (h.le_scale j p)) z hi with hnew | hterm
      · exact Or.inl hnew
      · exact Or.inr ⟨j, Nat.lt_succ_self j, hterm⟩
    · exact ht.elim fun t htt ↦ Or.inr ⟨t, Nat.lt_succ_of_lt htt.1, htt.2⟩

end RepairMetricHypotheses

end TNLean.PEPS.AreaLaw.Geometry
