/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.RepairHalfSideArithmetic
import TNLean.PEPS.AreaLaw.Geometry.RepairInductionMetric

/-!
# Integral coordinates of the recursive repair marks

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

variable {o : ℝ × ℝ} {Λ : Finset (ℤ × ℤ)} {A : Finset (Site Λ)} {C k₀ : ℕ}
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
