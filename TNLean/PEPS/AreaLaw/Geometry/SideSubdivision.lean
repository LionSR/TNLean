/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.CellFans
import TNLean.PEPS.AreaLaw.Geometry.LocalLayers
import TNLean.PEPS.AreaLaw.Geometry.AdjacentScales
import TNLean.PEPS.AreaLaw.Geometry.MeshGeometry
import TNLean.PEPS.AreaLaw.Geometry.LayerPartition
import Mathlib.LinearAlgebra.AffineSpace.Midpoint

/-!
# Opposing corners on fine-cell sides

An actual opposing fine-cell corner on a whole side of a sufficiently late
fine-layer cell is a side endpoint or its midpoint. At the common point,
closed-layer locality forces adjacent layers. Their dyadic scales put the
opposing corner on the half-side mesh of the reference cell.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 11, lines 299–306 and 352–356.
Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Independently proved from the manuscript; no upstream Lean proof text is reused.
-/


namespace TNLean.PEPS.AreaLaw.Geometry

/-- A corner of the actual translated dyadic cell, with each endpoint chosen by
a binary coordinate. Source: area-law Section 11, lines 299–306 and 352–356. -/
def dyadicCellCorner (o : ℝ × ℝ) (ℓ : ℕ) (z : ℤ × ℤ)
    (ε : Fin 2 × Fin 2) : ℝ × ℝ :=
  (o.1 + (2 : ℝ) ^ ℓ * ((z.1 : ℝ) + ε.1.val),
    o.2 + (2 : ℝ) ^ ℓ * ((z.2 : ℝ) + ε.2.val))

private theorem half_parameter_trichotomy {q θ : ℝ} (hq : 0 < q)
    (hθ : θ ∈ Set.Icc (0 : ℝ) 1) (n : ℤ)
    (he : q * (n : ℝ) = 2 * q * θ) : θ = 0 ∨ θ = 1 / 2 ∨ θ = 1 := by
  have hnθ : (n : ℝ) = 2 * θ := mul_left_cancel₀ hq.ne' (by nlinarith [he])
  have hn0 : (0 : ℤ) ≤ n := by exact_mod_cast (show (0 : ℝ) ≤ n by linarith [hθ.1])
  have hn2 : n ≤ (2 : ℤ) := by exact_mod_cast (show (n : ℝ) ≤ 2 by linarith [hθ.2])
  have hn : n = 0 ∨ n = 1 ∨ n = 2 := by omega
  rcases hn with rfl | rfl | rfl
  · exact Or.inl (by simpa using hnθ)
  · exact Or.inr (Or.inl (by norm_num at hnθ; linarith))
  · exact Or.inr (Or.inr (by simpa using hnθ))

private theorem halfMesh_on_side (o : ℝ × ℝ) (ℓ : ℕ) (z : ℤ × ℤ)
    (s : Fin 4) (x : ℝ × ℝ)
    (hx : x ∈ affineMesh o ((2 : ℝ) ^ ℓ / 2))
    (hs : x ∈ segment ℝ
      (cellFanStart o ℓ z (fun _ ↦ false) ⟨s, 0⟩)
      (cellFanEnd o ℓ z (fun _ ↦ false) ⟨s, 0⟩)) :
    x = cellFanStart o ℓ z (fun _ ↦ false) ⟨s, 0⟩ ∨
      x = midpoint ℝ (cellFanStart o ℓ z (fun _ ↦ false) ⟨s, 0⟩)
        (cellFanEnd o ℓ z (fun _ ↦ false) ⟨s, 0⟩) ∨
      x = cellFanEnd o ℓ z (fun _ ↦ false) ⟨s, 0⟩ := by
  obtain ⟨m, rfl⟩ := hx
  rw [segment_eq_image'] at hs
  obtain ⟨θ, hθ, he⟩ := hs
  have hn : ∃ n : ℤ, (2 : ℝ) ^ ℓ / 2 * (n : ℝ) = 2 * ((2 : ℝ) ^ ℓ / 2) * θ := by
    fin_cases s
    · refine ⟨m.2 - 2 * z.2, ?_⟩
      have he' := congrArg Prod.snd he
      change (o.2 + 2 ^ ℓ * z.2 + 2 ^ ℓ / 2 + 2 ^ ℓ / 2 * (-1)) +
        θ * ((o.2 + 2 ^ ℓ * z.2 + 2 ^ ℓ / 2 + 2 ^ ℓ / 2 * 1) -
          (o.2 + 2 ^ ℓ * z.2 + 2 ^ ℓ / 2 + 2 ^ ℓ / 2 * (-1))) =
        o.2 + 2 ^ ℓ / 2 * (m.2 : ℝ) at he'
      push_cast
      nlinarith [he']
    · refine ⟨2 * z.1 + 2 - m.1, ?_⟩
      have he' := congrArg Prod.fst he
      change (o.1 + 2 ^ ℓ * z.1 + 2 ^ ℓ / 2 + 2 ^ ℓ / 2 * (-(-1))) +
        θ * ((o.1 + 2 ^ ℓ * z.1 + 2 ^ ℓ / 2 + 2 ^ ℓ / 2 * (-1)) -
          (o.1 + 2 ^ ℓ * z.1 + 2 ^ ℓ / 2 + 2 ^ ℓ / 2 * (-(-1)))) =
        o.1 + 2 ^ ℓ / 2 * (m.1 : ℝ) at he'
      push_cast
      nlinarith [he']
    · refine ⟨2 * z.2 + 2 - m.2, ?_⟩
      have he' := congrArg Prod.snd he
      change (o.2 + 2 ^ ℓ * z.2 + 2 ^ ℓ / 2 + 2 ^ ℓ / 2 * (-(-1))) +
        θ * ((o.2 + 2 ^ ℓ * z.2 + 2 ^ ℓ / 2 + 2 ^ ℓ / 2 * (-1)) -
          (o.2 + 2 ^ ℓ * z.2 + 2 ^ ℓ / 2 + 2 ^ ℓ / 2 * (-(-1)))) =
        o.2 + 2 ^ ℓ / 2 * (m.2 : ℝ) at he'
      push_cast
      nlinarith [he']
    · refine ⟨m.1 - 2 * z.1, ?_⟩
      have he' := congrArg Prod.fst he
      change (o.1 + 2 ^ ℓ * z.1 + 2 ^ ℓ / 2 + 2 ^ ℓ / 2 * (-1)) +
        θ * ((o.1 + 2 ^ ℓ * z.1 + 2 ^ ℓ / 2 + 2 ^ ℓ / 2 * 1) -
          (o.1 + 2 ^ ℓ * z.1 + 2 ^ ℓ / 2 + 2 ^ ℓ / 2 * (-1))) =
        o.1 + 2 ^ ℓ / 2 * (m.1 : ℝ) at he'
      push_cast
      nlinarith [he']
  obtain ⟨n, hn⟩ := hn
  rcases half_parameter_trichotomy (by positivity) hθ n hn with ht | ht | ht
  · left
    simpa [ht] using he.symm
  · right; left
    rw [← he, ht, midpoint_eq_smul_add]
    norm_num
    module
  · right; right
    simpa [ht] using he.symm

private theorem dyadicCellCorner_mem_closure (o : ℝ × ℝ) (ℓ : ℕ)
    (z : ℤ × ℤ) (ε : Fin 2 × Fin 2) :
    dyadicCellCorner o ℓ z ε ∈ closure (dyadicCell o ℓ z) := by
  have hbound (a : ℝ) (i : ℤ) (e : Fin 2) :
      a + (2 : ℝ) ^ ℓ * ((i : ℝ) + e.val) ∈
        Set.Icc (a + (2 : ℝ) ^ ℓ * i) (a + (2 : ℝ) ^ ℓ * (i + 1)) := by
    have he0 : (0 : ℝ) ≤ e.val := Nat.cast_nonneg _
    have he1 : (e.val : ℝ) ≤ 1 := by exact_mod_cast (show e.val ≤ 1 by omega)
    have ht : 0 < (2 : ℝ) ^ ℓ := by positivity
    constructor <;> nlinarith
  rw [closure_dyadicCell]
  exact ⟨hbound o.1 z.1 ε.1, hbound o.2 z.2 ε.2⟩

private theorem wholeSide_mem_closure (o : ℝ × ℝ) (ℓ : ℕ)
    (z : ℤ × ℤ) (s : Fin 4) (x : ℝ × ℝ)
    (hx : x ∈ segment ℝ
      (cellFanStart o ℓ z (fun _ ↦ false) ⟨s, 0⟩)
      (cellFanEnd o ℓ z (fun _ ↦ false) ⟨s, 0⟩)) :
    x ∈ closure (dyadicCell o ℓ z) := by
  have hc : Convex ℝ (closure (dyadicCell o ℓ z)) := by
    rw [closure_dyadicCell]
    exact (convex_Icc _ _).prod (convex_Icc _ _)
  have hv := (cellFan_vertices_mem_beltCellMarks o ℓ z (fun _ ↦ false)).2 ⟨s, 0⟩
  exact hc.segment_subset
    (beltCellMarks_subset_closure_dyadicCell o ℓ z hv.1)
    (beltCellMarks_subset_closure_dyadicCell o ℓ z hv.2) hx

private theorem fineCell_mem_closed_layer (o : ℝ × ℝ) (k : ℕ)
    (Z : Finset (ℤ × ℤ)) (C : ℕ) (z : ℤ × ℤ) (x : ℝ × ℝ)
    (hz : z ∈ fineLayerIndices o k (fineScaleIndex k) Z C)
    (hx : x ∈ closure (dyadicCell o (fineScaleIndex k) z)) :
    x ∈ closure (dyadicLayer o k Z C) := by
  have hcell := dyadicCell_subset_dyadicLayer_of_mem_fineLayerIndices
    o k (fineScaleIndex k) Z C z (fineScaleIndex_le k) hz
  exact closure_mono hcell hx

private theorem dyadicCellCorner_mem_halfMesh (o : ℝ × ℝ) (ℓ j : ℕ)
    (z : ℤ × ℤ) (ε : Fin 2 × Fin 2) (hℓj : ℓ ≤ j + 1) :
    dyadicCellCorner o j z ε ∈ affineMesh o ((2 : ℝ) ^ ℓ / 2) := by
  have hp : ((2 : ℝ) ^ ℓ / 2) * (2 : ℝ) ^ (j + 1 - ℓ) = (2 : ℝ) ^ j := by
    rw [div_mul_eq_mul_div, ← pow_add, Nat.add_sub_of_le hℓj, pow_succ]
    ring
  refine ⟨((2 : ℤ) ^ (j + 1 - ℓ) * (z.1 + ε.1.val),
    (2 : ℤ) ^ (j + 1 - ℓ) * (z.2 + ε.2.val)), ?_⟩
  apply Prod.ext <;> dsimp [integerPoint, dyadicCellCorner] <;>
    push_cast <;> rw [← mul_assoc, hp]

/-- An actual opposing fine-cell corner on a whole side of a late fine-layer cell
is its start, midpoint or end. The opposing layer need not satisfy a separate
lower bound. Source: area-law Section 11, lines 299–306 and 352–356. -/
theorem fineLayer_corner_on_side (o : ℝ × ℝ) (k h : ℕ)
    (Z : Finset (ℤ × ℤ)) (C : ℕ) (z w : ℤ × ℤ) (s : Fin 4)
    (ε : Fin 2 × Fin 2) (hC : 2 ≤ C) (hk : 50000000 ≤ k)
    (hz : z ∈ fineLayerIndices o k (fineScaleIndex k) Z C)
    (hw : w ∈ fineLayerIndices o h (fineScaleIndex h) Z C)
    (hside : dyadicCellCorner o (fineScaleIndex h) w ε ∈ segment ℝ
      (cellFanStart o (fineScaleIndex k) z (fun _ ↦ false) ⟨s, 0⟩)
      (cellFanEnd o (fineScaleIndex k) z (fun _ ↦ false) ⟨s, 0⟩)) :
    dyadicCellCorner o (fineScaleIndex h) w ε =
        cellFanStart o (fineScaleIndex k) z (fun _ ↦ false) ⟨s, 0⟩ ∨
      dyadicCellCorner o (fineScaleIndex h) w ε = midpoint ℝ
        (cellFanStart o (fineScaleIndex k) z (fun _ ↦ false) ⟨s, 0⟩)
        (cellFanEnd o (fineScaleIndex k) z (fun _ ↦ false) ⟨s, 0⟩) ∨
      dyadicCellCorner o (fineScaleIndex h) w ε =
        cellFanEnd o (fineScaleIndex k) z (fun _ ↦ false) ⟨s, 0⟩ := by
  let x := dyadicCellCorner o (fineScaleIndex h) w ε
  have hxk := fineCell_mem_closed_layer o k Z C z x hz
    (wholeSide_mem_closure o (fineScaleIndex k) z s x hside)
  have hxh := fineCell_mem_closed_layer o h Z C w x hw
    (dyadicCellCorner_mem_closure o (fineScaleIndex h) w ε)
  have hkh := (dyadicLayer_nearby_indices o k h Z C x x hC hk hxk hxh
    (by simp)).2
  have hmono := fineScaleIndex_mono hkh
  have hstep := fineScaleIndex_succ h
  have hscale : fineScaleIndex k ≤ fineScaleIndex h + 1 := by omega
  exact halfMesh_on_side o (fineScaleIndex k) z s x
    (dyadicCellCorner_mem_halfMesh o (fineScaleIndex k) (fineScaleIndex h) w ε hscale) hside

end TNLean.PEPS.AreaLaw.Geometry
