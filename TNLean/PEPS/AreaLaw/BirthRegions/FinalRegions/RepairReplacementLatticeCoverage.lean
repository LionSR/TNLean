/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.ManyBody.Sites.Dyadic.DyadicOrigin
import TNLean.PEPS.AreaLaw.BirthRegions.Layers.MeshGeometry
import TNLean.PEPS.AreaLaw.BirthRegions.Stars.RepairChildStarStep
import TNLean.PEPS.AreaLaw.BirthRegions.RepairStages.SimultaneousRepair
import TNLean.PEPS.AreaLaw.BirthRegions.InitialRegions.InitialRegionBoundaries
import TNLean.PEPS.AreaLaw.BirthRegions.Stars.RepairInductionMetric

/-!
# Lattice points in the open replacement regions

For a center in the prescribed translated integer mesh and scale at least one,
every integer lattice point of the closed removal square belongs to an open
replacement region. The assignment of identifiers and their binary labels is
arbitrary. No convexity of a whole replacement run is required.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 11, replacement instructions, lines 404–417, and
the translated supporting-line argument, lines 545–561.
Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Written from the manuscript; no upstream Lean text is reused.

It also contains the following results.

* `TNLean.PEPS.AreaLaw.Geometry.exists_mem_repairNextCurrentRegion_or_terminalInterior`,
  `TNLean.PEPS.AreaLaw.Geometry.RepairMetricHypotheses.lattice_mem_current_or_terminal_before`:
  lattice coverage during simultaneous repair.
* `TNLean.PEPS.AreaLaw.Geometry.RepairMetricHypotheses.repairStage_location_mem_affineMesh`:
  integral coordinates of the recursive repair marks.
-/

open ManyBody (IsAllowedSlope TemplatePolygon boundaryEndpoints dyadicOrigin
  dyadicOrigin_supporting_lines_avoid_lattice integerPoint
  mem_boundaryEndpoints_of_mem_edgeBoundary)

section RepairReplacementLatticeCoverage

noncomputable section

namespace TNLean.PEPS.AreaLaw.Geometry

/-- Every lattice point of a removal square with translated integral center
and scale at least one lies in the interior of one of its replacement runs.
Source: area-law Section 11, lines 404–417 and 545–561. -/
theorem exists_mem_repairReplacementOpenRegion_of_mem_repairSquare
    {ι : Type*} (ξ : ι → Fin 2) (σ : RepairFanSlot → ι)
    {v : ℝ × ℝ} {S : ℝ} {z : ℤ × ℤ}
    (hv : v ∈ affineMesh dyadicOrigin 1) (hS : 1 ≤ S)
    (hz : integerPoint z ∈ repairSquare v S) :
    ∃ H : RepairFanRun ξ σ, integerPoint z ∈ repairReplacementOpenRegion v S ξ σ H := by
  obtain ⟨m, hm⟩ := hv
  have hvm : v = dyadicOrigin + integerPoint m := by
    simpa only [one_smul] using hm.symm
  have hv₁ : v.1 = dyadicOrigin.1 + (m.1 : ℝ) := by
    simpa only [Prod.fst_add, integerPoint] using congrArg Prod.fst hvm
  have hv₂ : v.2 = dyadicOrigin.2 + (m.2 : ℝ) := by
    simpa only [Prod.snd_add, integerPoint] using congrArg Prod.snd hvm
  have hnot : ¬ IsAllowedSlope (integerPoint z - v) := by
    intro h
    simp only [IsAllowedSlope, Prod.fst_sub, Prod.snd_sub, integerPoint] at h
    rcases h with h | h | h | h
    · apply (dyadicOrigin_supporting_lines_avoid_lattice z m.1).1
      linarith [hv₁]
    · apply (dyadicOrigin_supporting_lines_avoid_lattice z m.2).2.1
      linarith [hv₂]
    · apply (dyadicOrigin_supporting_lines_avoid_lattice z (m.1 - m.2)).2.2.2
      push_cast
      linarith [hv₁, hv₂]
    · apply (dyadicOrigin_supporting_lines_avoid_lattice z (m.1 + m.2)).2.2.1
      push_cast
      linarith [hv₁, hv₂]
  obtain ⟨n, hn⟩ := exists_natCast_repairHalfSide hS
  have hd : 0 < repairHalfSide S := repairHalfSide_pos S
  have hnorm_le : ‖integerPoint z - v‖ ≤ repairHalfSide S := by
    simpa only [repairSquare, Metric.mem_closedBall, dist_eq_norm] using hz
  have hbounds : |(z.1 : ℝ) - v.1| ≤ repairHalfSide S ∧
      |(z.2 : ℝ) - v.2| ≤ repairHalfSide S := by
    simpa only [Prod.norm_def, Real.norm_eq_abs, Prod.fst_sub, Prod.snd_sub,
      integerPoint, max_le_iff] using hnorm_le
  have hcoord (a b o : ℝ) (k : ℤ) (hb : b = o + (k : ℝ))
      (ha : ∀ j : ℤ, a ≠ o + (j : ℝ)) (hle : |a - b| ≤ repairHalfSide S) :
      |a - b| < repairHalfSide S := by
    apply lt_of_le_of_ne hle
    intro he
    by_cases hsign : 0 ≤ a - b
    · rw [abs_of_nonneg hsign, hn] at he
      apply ha (k + (n : ℤ))
      push_cast
      linarith [hb]
    · rw [abs_of_neg (lt_of_not_ge hsign), hn] at he
      apply ha (k - (n : ℤ))
      push_cast
      linarith [hb]
  have h₁ := hcoord (z.1 : ℝ) v.1 dyadicOrigin.1 m.1 hv₁
    (fun j ↦ (dyadicOrigin_supporting_lines_avoid_lattice z j).1) hbounds.1
  have h₂ := hcoord (z.2 : ℝ) v.2 dyadicOrigin.2 m.2 hv₂
    (fun j ↦ (dyadicOrigin_supporting_lines_avoid_lattice z j).2.1) hbounds.2
  have hnorm_lt : ‖integerPoint z - v‖ < repairHalfSide S := by
    simpa only [Prod.norm_def, Real.norm_eq_abs, Prod.fst_sub, Prod.snd_sub,
      integerPoint] using max_lt_iff.mpr ⟨h₁, h₂⟩
  obtain ⟨s, hs⟩ := exists_mem_repairFanCone (integerPoint z - v)
  have hslope_smul {u : ℝ × ℝ} (hu : IsAllowedSlope u) (t : ℝ) :
      IsAllowedSlope (t • u) := by
    rcases hu with h | h | h | h <;> simp [IsAllowedSlope, h, smul_eq_mul]
  have hradial (P : TemplatePolygon) :
      match P with
      | .triangle a b c _ _ _ _ => IsAllowedSlope (b - a) ∧ IsAllowedSlope (a - c)
      | .rectangle _ _ _ _ _ _ _ _ => True := by
    cases P with
    | triangle _ _ _ _ hab _ hca => exact ⟨hab, hca⟩
    | rectangle => trivial
  have hr := hradial (cellFanPolygon (-1, -1) 1 (0, 0) repairFanSplit s)
  change IsAllowedSlope
      (cellFanStart (-1, -1) 1 (0, 0) repairFanSplit s - cellFanCenter (-1, -1) 1 (0, 0)) ∧
    IsAllowedSlope
      (cellFanCenter (-1, -1) 1 (0, 0) - cellFanEnd (-1, -1) 1 (0, 0) repairFanSplit s) at hr
  have hc : cellFanCenter (-1, -1) 1 (0, 0) = 0 := by
    ext <;> simp [cellFanCenter]
  have hstart : IsAllowedSlope (repairFanStart s) := by
    simpa only [repairFanStart, hc, sub_zero] using hr.1
  have hdir : IsAllowedSlope (repairFanDirection s) := by
    simpa only [repairFanDirection, hc, zero_sub, neg_one_smul, neg_neg]
      using hslope_smul hr.2 (-1)
  have hopen : integerPoint z - v ∈ repairFanOpenCone s := by
    constructor
    · apply lt_of_le_of_ne hs.1
      intro hzero
      apply hnot
      have hdet : repairCross (-repairFanDirection s) (repairFanStart s) = 1 := by
        calc
          _ = repairCross (repairFanStart s) (repairFanDirection s) := by
            simp only [repairCross, Prod.fst_neg, Prod.snd_neg]
            ring
          _ = 1 := repairCross_start_direction s
      have hzero' : repairCross (integerPoint z - v) (repairFanStart s) = 0 := by
        calc
          _ = -repairCross (repairFanStart s) (integerPoint z - v) := by
            simp only [repairCross]
            ring
          _ = 0 := by rw [← hzero, neg_zero]
      rw [eq_repairCross_smul_of_repairCross_eq_zero hdet hzero']
      exact hslope_smul hstart _
    · apply lt_of_le_of_ne hs.2
      intro hzero
      apply hnot
      rw [eq_repairCross_smul_of_repairCross_eq_zero
        (repairCross_start_direction s) hzero.symm]
      exact hslope_smul hdir _
  have htriangle : integerPoint z ∈
      interior (repairCurrentFanTriangle v (repairHalfSide S) s) := by
    rw [interior_repairCurrentFanTriangle hd s]
    exact ⟨hopen, hnorm_lt⟩
  have hsubset : repairCurrentFanTriangle v (repairHalfSide S) s ⊆
      repairReplacementBirthRegion v S ξ σ (repairFanRunOf ξ σ s) := by
    intro x hx
    have hx' := (mem_repairCurrentFanTriangle_iff hd s x).mp hx
    exact (mem_repairReplacementBirthRegion_iff (repairFanRunOf ξ σ s)).mpr
      ⟨s, rfl, hx'.1, hx'.2⟩
  exact ⟨repairFanRunOf ξ σ s, interior_mono hsubset htriangle⟩

end TNLean.PEPS.AreaLaw.Geometry

end

end RepairReplacementLatticeCoverage

section RepairMarkMesh

/-!
## Integral coordinates of the recursive repair marks

Every mark of the actual repair construction lies on the translated integer
mesh of its initial origin. Initial marks lie on dyadic meshes whose spacing
is an integer. Each subsequent mark is obtained from its parent by adding an
integer multiple of a centered offset with coordinates in {-1, 0, 1}.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 11, initial marks, lines 325–363; recursive
marks, lines 404–409 and 506–514; integral coordinates, lines 545–558.
Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

namespace TNLean.PEPS.AreaLaw.Geometry

variable {o : ℝ × ℝ} {Λ : Finset (ℤ × ℤ)} {A : Finset ↥Λ} {C k₀ : ℕ}
  {hC : 2 ≤ C} {h₀ : 50000000 ≤ k₀} {Sstar : ℝ}

local notation "𝔇" => repairStage o Λ A C k₀ hC h₀ Sstar

namespace RepairMetricHypotheses

/-- Every mark of every actual generation belongs to the initial translated
integer mesh when the stopping scale is at least one.
Source: area-law Section 11, integral recursion, lines 545–551. -/
theorem repairStage_location_mem_affineMesh {a₀ : ℝ}
    (h : RepairMetricHypotheses (o := o) (Λ := Λ) (A := A)
      (C := C) (k₀ := k₀) (hC := hC) (h₀ := h₀) (Sstar := Sstar) a₀)
    (hSstar : 1 ≤ Sstar) (j : ℕ) (p : (𝔇 j).markIndex) :
    (𝔇 j).location p ∈ affineMesh o 1 := by
  induction j with
  | zero =>
    classical
    obtain ⟨_, k, z, hk, hz, hp, _⟩ :=
      (initialRepairStage_mark_spec o Λ A C k₀ hC h₀).2.2.1 p
    have hf : fineScaleIndex 2 = 1 := by
      norm_num [fineScaleIndex, Exponents.zeta, Exponents.geometryDelta, Nat.floor_eq_iff']
    have hm := fineScaleIndex_mono (show 2 ≤ k by omega)
    change p.val ∈ affineMesh o 1
    change p.val ∈ beltCellMarks o (fineScaleIndex k) z at hp
    simpa only [show (2 : ℝ) ^ 2 / 4 = 1 by norm_num] using
      beltMarks_subset_affineMesh o 2 (fineScaleIndex k) _ (by omega)
        (Finset.mem_biUnion.mpr ⟨z, hz, hp⟩)
  | succ j ih =>
    obtain ⟨z, hz⟩ := ih p.2.1.val
    obtain ⟨n, hn⟩ := exists_natCast_repairHalfSide
      (hSstar.trans (h.le_scale j p.2.1.val))
    refine ⟨(z.1 + (n : ℤ) * ((p.2.2.1.val : ℤ) - 1),
      z.2 + (n : ℤ) * ((p.2.2.2.val : ℤ) - 1)), ?_⟩
    change _ = (𝔇 j).location p.2.1.val +
      repairHalfSide ((𝔇 j).scale p.2.1.val) • repairChildOffset p.2.2
    rw [← hz, hn]
    simp [integerPoint, repairChildOffset, add_assoc]

end RepairMetricHypotheses

end TNLean.PEPS.AreaLaw.Geometry

end RepairMarkMesh

section RepairLatticeCoverage

/-!
## Lattice coverage during simultaneous repair

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

open ManyBody (edgeBoundary planeDomainGraph)

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

variable {Λ : Finset (ℤ × ℤ)} {A : Finset ↥Λ} {C k₀ : ℕ}
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
    (hSstar : 1 ≤ Sstar) (hboundary : 0 < (edgeBoundary (planeDomainGraph Λ) A).card)
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

end

end RepairLatticeCoverage
