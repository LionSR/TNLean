/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.DyadicOrigin
import TNLean.PEPS.AreaLaw.Geometry.MeshGeometry
import TNLean.PEPS.AreaLaw.Geometry.RepairChildStarStep
import TNLean.PEPS.AreaLaw.Geometry.RepairHalfSideArithmetic

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
-/

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
