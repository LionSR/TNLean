/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# Nearest-point projection onto a complete convex set

This file records the Hilbert projection theorem from Mathlib as a reusable
nearest-point projection on a nonempty complete convex set in a real inner
product space, together with uniqueness, nonexpansiveness, and continuity.
-/

open scoped Topology

namespace ConvexProjection

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

private noncomputable def nearestPointData
    (K : Set F) (hK_nonempty : K.Nonempty) (hK_complete : IsComplete K)
    (hK_convex : Convex ℝ K) (u : F) :
    {v : F // v ∈ K ∧ ‖u - v‖ = ⨅ w : K, ‖u - w‖} := by
  classical
  refine ⟨Classical.choose
    (exists_norm_eq_iInf_of_complete_convex hK_nonempty hK_complete hK_convex u), ?_⟩
  exact Classical.choose_spec
    (exists_norm_eq_iInf_of_complete_convex hK_nonempty hK_complete hK_convex u)

/-- The nearest-point projection onto a nonempty complete convex set. -/
noncomputable def nearestPoint
    (K : Set F) (hK_nonempty : K.Nonempty) (hK_complete : IsComplete K)
    (hK_convex : Convex ℝ K) (u : F) : K :=
  ⟨(nearestPointData K hK_nonempty hK_complete hK_convex u).1,
    (nearestPointData K hK_nonempty hK_complete hK_convex u).2.1⟩

@[simp]
theorem nearestPoint_mem
    (K : Set F) (hK_nonempty : K.Nonempty) (hK_complete : IsComplete K)
    (hK_convex : Convex ℝ K) (u : F) :
    (nearestPoint K hK_nonempty hK_complete hK_convex u : F) ∈ K :=
  (nearestPoint K hK_nonempty hK_complete hK_convex u).2

theorem nearestPoint_spec
    (K : Set F) (hK_nonempty : K.Nonempty) (hK_complete : IsComplete K)
    (hK_convex : Convex ℝ K) (u : F) :
    ‖u - (nearestPoint K hK_nonempty hK_complete hK_convex u : F)‖ =
      ⨅ w : K, ‖u - w‖ :=
  (nearestPointData K hK_nonempty hK_complete hK_convex u).2.2

theorem inner_sub_nearestPoint_nonpos
    (K : Set F) (hK_nonempty : K.Nonempty) (hK_complete : IsComplete K)
    (hK_convex : Convex ℝ K) (u : F) :
    ∀ w ∈ K,
      inner ℝ (u - (nearestPoint K hK_nonempty hK_complete hK_convex u : F))
        (w - (nearestPoint K hK_nonempty hK_complete hK_convex u : F)) ≤ 0 := by
  refine (norm_eq_iInf_iff_real_inner_le_zero hK_convex ?_).1 ?_
  · exact nearestPoint_mem K hK_nonempty hK_complete hK_convex u
  · exact nearestPoint_spec K hK_nonempty hK_complete hK_convex u

theorem eq_nearestPoint_of_mem_of_norm_eq_iInf
    (K : Set F) (hK_nonempty : K.Nonempty) (hK_complete : IsComplete K)
    (hK_convex : Convex ℝ K) {u v : F} (hvK : v ∈ K)
    (hvmin : ‖u - v‖ = ⨅ w : K, ‖u - w‖) :
    v = (nearestPoint K hK_nonempty hK_complete hK_convex u : F) := by
  let p : F := nearestPoint K hK_nonempty hK_complete hK_convex u
  have hpK : p ∈ K := nearestPoint_mem K hK_nonempty hK_complete hK_convex u
  have hp : inner ℝ (u - p) (v - p) ≤ 0 :=
    inner_sub_nearestPoint_nonpos K hK_nonempty hK_complete hK_convex u v hvK
  have hv : inner ℝ (u - v) (p - v) ≤ 0 :=
    (norm_eq_iInf_iff_real_inner_le_zero hK_convex hvK).1 hvmin p hpK
  have hv' : 0 ≤ inner ℝ (u - v) (v - p) := by
    have hneg : 0 ≤ inner ℝ (u - v) (-(p - v)) := by
      rw [inner_neg_right]
      exact neg_nonneg.mpr hv
    have hsub : -(p - v) = v - p := by
      abel
    rwa [hsub] at hneg
  have hle : inner ℝ (v - p) (v - p) ≤ 0 := by
    have hrewrite : inner ℝ (v - p) (v - p) =
        inner ℝ (u - p) (v - p) - inner ℝ (u - v) (v - p) := by
      calc
        inner ℝ (v - p) (v - p) = inner ℝ ((u - p) - (u - v)) (v - p) := by
          congr 1
          abel
        _ = inner ℝ (u - p) (v - p) - inner ℝ (u - v) (v - p) := by
          rw [inner_sub_left]
    rw [hrewrite]
    exact sub_nonpos.mpr <| le_trans hp hv'
  have hnonneg : 0 ≤ inner ℝ (v - p) (v - p) := by
    simp
  have hzero : inner ℝ (v - p) (v - p) = 0 := le_antisymm hle hnonneg
  have hsq0 : ‖v - p‖ ^ 2 = 0 := by
    simpa [real_inner_self_eq_norm_sq] using hzero
  have hnorm0 : ‖v - p‖ = 0 := by
    nlinarith
  exact sub_eq_zero.mp (norm_eq_zero.mp hnorm0)

theorem nearestPoint_eq_self
    (K : Set F) (hK_nonempty : K.Nonempty) (hK_complete : IsComplete K)
    (hK_convex : Convex ℝ K) {u : F} (huK : u ∈ K) :
    (nearestPoint K hK_nonempty hK_complete hK_convex u : F) = u := by
  letI : Nonempty K := hK_nonempty.to_subtype
  symm
  apply eq_nearestPoint_of_mem_of_norm_eq_iInf K hK_nonempty hK_complete hK_convex huK
  have hbdd : BddBelow (Set.range fun w : K => ‖u - w‖) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨w, rfl⟩
    exact norm_nonneg _
  have hle : (⨅ w : K, ‖u - w‖) ≤ ‖u - (⟨u, huK⟩ : K)‖ := by
    exact ciInf_le hbdd ⟨u, huK⟩
  have hle0 : (⨅ w : K, ‖u - w‖) ≤ 0 := by
    simpa using hle
  have h0le : 0 ≤ (⨅ w : K, ‖u - w‖) := by
    exact le_ciInf fun w => norm_nonneg _
  have hEq : (⨅ w : K, ‖u - w‖) = 0 := le_antisymm hle0 h0le
  simp [hEq]

theorem dist_nearestPoint_nearestPoint_le
    (K : Set F) (hK_nonempty : K.Nonempty) (hK_complete : IsComplete K)
    (hK_convex : Convex ℝ K) (u v : F) :
    dist (nearestPoint K hK_nonempty hK_complete hK_convex u : F)
      (nearestPoint K hK_nonempty hK_complete hK_convex v : F) ≤ dist u v := by
  let p : F := nearestPoint K hK_nonempty hK_complete hK_convex u
  let q : F := nearestPoint K hK_nonempty hK_complete hK_convex v
  have hpq_nonneg : 0 ≤ inner ℝ (u - p) (p - q) := by
    have h : inner ℝ (u - p) (q - p) ≤ 0 :=
      inner_sub_nearestPoint_nonpos K hK_nonempty hK_complete hK_convex u q
        (nearestPoint_mem K hK_nonempty hK_complete hK_convex v)
    have hneg : 0 ≤ inner ℝ (u - p) (-(q - p)) := by
      rw [inner_neg_right]
      exact neg_nonneg.mpr h
    have hsub : -(q - p) = p - q := by
      abel
    rwa [hsub] at hneg
  have hqp_nonpos : inner ℝ (v - q) (p - q) ≤ 0 :=
    inner_sub_nearestPoint_nonpos K hK_nonempty hK_complete hK_convex v p
      (nearestPoint_mem K hK_nonempty hK_complete hK_convex u)
  have hsquare : ‖p - q‖ ^ 2 ≤ ‖u - v‖ * ‖p - q‖ := by
    have hmain_sq : ‖p - q‖ ^ 2 ≤ inner ℝ (u - v) (p - q) := by
      have hrewrite : ‖p - q‖ ^ 2 =
          inner ℝ (u - v) (p - q) - (inner ℝ (u - p) (p - q) - inner ℝ (v - q) (p - q)) := by
        calc
          ‖p - q‖ ^ 2 = inner ℝ (p - q) (p - q) := by
            rw [real_inner_self_eq_norm_sq]
          _ = inner ℝ (u - v) (p - q) - inner ℝ ((u - p) - (v - q)) (p - q) := by
            rw [show p - q = (u - v) - ((u - p) - (v - q)) by abel, inner_sub_left]
          _ = inner ℝ (u - v) (p - q) -
                (inner ℝ (u - p) (p - q) - inner ℝ (v - q) (p - q)) := by
            congr 1
            rw [inner_sub_left]
      rw [hrewrite]
      have : 0 ≤ inner ℝ (u - p) (p - q) - inner ℝ (v - q) (p - q) :=
        sub_nonneg.mpr <| le_trans hqp_nonpos hpq_nonneg
      linarith
    have hcs : inner ℝ (u - v) (p - q) ≤ ‖u - v‖ * ‖p - q‖ := by
      exact le_trans (le_abs_self _) (abs_real_inner_le_norm _ _)
    exact le_trans hmain_sq hcs
  rw [dist_eq_norm, dist_eq_norm]
  by_cases hpq : p = q
  · simp [p, q, hpq]
  · have hpq_norm : 0 < ‖p - q‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hpq)
    nlinarith [hsquare, norm_nonneg (u - v), hpq_norm]

theorem lipschitzWith_nearestPoint
    (K : Set F) (hK_nonempty : K.Nonempty) (hK_complete : IsComplete K)
    (hK_convex : Convex ℝ K) :
    LipschitzWith 1 fun u : F => (nearestPoint K hK_nonempty hK_complete hK_convex u : F) := by
  intro u v
  rw [edist_dist, edist_dist]
  simpa using ENNReal.ofReal_le_ofReal
    (dist_nearestPoint_nearestPoint_le K hK_nonempty hK_complete hK_convex u v)

theorem continuous_nearestPoint
    (K : Set F) (hK_nonempty : K.Nonempty) (hK_complete : IsComplete K)
    (hK_convex : Convex ℝ K) :
    Continuous fun u : F => (nearestPoint K hK_nonempty hK_complete hK_convex u : F) :=
  (lipschitzWith_nearestPoint K hK_nonempty hK_complete hK_convex).continuous

end ConvexProjection
