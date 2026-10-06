/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.TorusCutCanonicalBondSpan
import TNLean.PEPS.TorusBondFlatConnection

/-!
# Plaquette constraints on the extracted four-cut coefficients

The trace-dual coefficient of a canonical cut vector vanishes unless its
four uncut bonds satisfy the plaquette compatibility relation. Applying all
four cuts eliminates every nonflat bond-label configuration from the actual
coherent expansion. No termwise comparison of unextracted sums is used.
-/

open scoped BigOperators Matrix

namespace TNLean.PEPS

variable {G V : Type*} [Group G] [Fintype G] [Fintype V] [DecidableEq V]
variable {width height : ℕ} [NeZero width] [NeZero height]
local notation "X" => TorusVertex width height

/-- Apply every actual bond's trace-dual functional to the expanded canonical
operator network, preserving its entire coherent vertex-label sum. -/
theorem torusBondCoefficientExtraction_averagingSite
    (Uh Uv : X → G →* Matrix V V ℂ) (Oh Ov : X → Matrix V V ℂ)
    (p : TorusBondLabels width height G) :
    torusBondCoefficientExtraction Uh Uv p
        (fun σ ↦ torusBondNetwork
          (fun v t ↦ representationAveragingSite (torusMatchedLegRep Uh Uv v)
            t.1 t.2.1 t.2.2.1 t.2.2.2 (σ v)) Oh Ov) =
      (Fintype.card G : ℂ)⁻¹ ^ Fintype.card X *
        ∑ q : X → G, ∏ v,
          torusDeltaPairing (Uh v) (p.1 v)
            (Uh v (q (v.1 + 1, v.2)) * Oh v * Uh v (q v)⁻¹) *
          torusDeltaPairing (Uv v) (p.2 v)
            (Uv v (q v) * Ov v * Uv v (q (v.1, v.2 + 1))⁻¹) := by
  have hnet : (fun σ : X → V × V × V × V ↦ torusBondNetwork
      (fun v t ↦ representationAveragingSite (torusMatchedLegRep Uh Uv v)
            t.1 t.2.1 t.2.2.1 t.2.2.2 (σ v)) Oh Ov) =
      (Fintype.card G : ℂ)⁻¹ ^ Fintype.card X • ∑ q : X → G,
        (fun σ : X → V × V × V × V ↦ ∏ v,
          (Uh v (q (v.1 + 1, v.2)) * Oh v * Uh v (q v)⁻¹)
            (σ (v.1 + 1, v.2)).2.2.2 (σ v).2.1 *
          (Uv v (q v) * Ov v * Uv v (q (v.1, v.2 + 1))⁻¹)
            (σ v).1 (σ (v.1, v.2 + 1)).2.2.1) := by
    funext σ
    simpa only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul] using
      torusBondNetwork_representationAveragingSite Uh Uv σ Oh Ov
  rw [hnet, map_smul, map_sum]
  simp only [smul_eq_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro q _
  exact torusOutputBondPairing_bondProduct _ _ _ _

/-- A cut leaves a square of uncut bonds. Any nonzero extracted term must
obey the square's nonabelian compatibility equation. -/
theorem torusBondCoefficientExtraction_cutNetwork_eq_zero
    (Uh Uv : TorusVertex 2 2 → G →* Matrix V V ℂ)
    (hU : IsSemiRegularTorusBondFamily Uh Uv)
    (c r : ZMod 2) (Oh Ov : TorusVertex 2 2 → Matrix V V ℂ)
    (hOh : ∀ v, v.1 + 1 ≠ c → Oh v = 1)
    (hOv : ∀ v, v.2 + 1 ≠ r → Ov v = 1)
    (p : TorusBondLabels 2 2 G)
    (hp : p.2 (c + 1, r) * p.1 (c, r + 1) ≠ p.1 (c, r) * p.2 (c, r)) :
    torusBondCoefficientExtraction Uh Uv p
        (fun σ ↦ torusBondNetwork
          (fun v t ↦ representationAveragingSite (torusMatchedLegRep Uh Uv v)
            t.1 t.2.1 t.2.2.1 t.2.2.2 (σ v)) Oh Ov) = 0 := by
  classical
  rw [torusBondCoefficientExtraction_averagingSite]
  suffices h : (∑ q : TorusVertex 2 2 → G, ∏ v,
      torusDeltaPairing (Uh v) (p.1 v)
        (Uh v (q (v.1 + 1, v.2)) * Oh v * Uh v (q v)⁻¹) *
      torusDeltaPairing (Uv v) (p.2 v)
        (Uv v (q v) * Ov v * Uv v (q (v.1, v.2 + 1))⁻¹)) = 0 by rw [h, mul_zero]
  apply Finset.sum_eq_zero
  intro q _
  by_contra hn
  have hH (v : TorusVertex 2 2) (hv : v.1 + 1 ≠ c) :
      p.1 v = q (v.1 + 1, v.2) * (q v)⁻¹ := by
    have hne := (mul_ne_zero_iff.mp ((Finset.prod_ne_zero_iff.mp hn) v (Finset.mem_univ v))).1
    rw [hOh v hv, Matrix.mul_one, ← map_mul, torusDeltaPairing_apply_rep (Uh v) (hU.1 v)] at hne
    exact of_decide_eq_true (by simpa using hne)
  have hV (v : TorusVertex 2 2) (hv : v.2 + 1 ≠ r) :
      p.2 v = q v * (q (v.1, v.2 + 1))⁻¹ := by
    have hne := (mul_ne_zero_iff.mp ((Finset.prod_ne_zero_iff.mp hn) v (Finset.mem_univ v))).2
    rw [hOv v hv, Matrix.mul_one, ← map_mul, torusDeltaPairing_apply_rep (Uv v) (hU.2 v)] at hne
    exact of_decide_eq_true (by simpa using hne)
  have hc : c + 1 ≠ c := by simp
  have hr : r + 1 ≠ r := by simp
  apply hp
  rw [hV (c + 1, r) hr, hH (c, r + 1) hc, hH (c, r) hc, hV (c, r) hr]
  simp only [mul_assoc, inv_mul_cancel_left]

/-- The source plaquette constraint holds coefficientwise throughout the
whole cut range, including arbitrary correlated boundary inputs. -/
theorem torusBondCoefficientExtraction_eq_zero_of_mem_torusCutSpace
    (Uh Uv : TorusVertex 2 2 → G →* Matrix V V ℂ)
    (hU : IsSemiRegularTorusBondFamily Uh Uv)
    (c r : ZMod 2) (p : TorusBondLabels 2 2 G)
    (hp : p.2 (c + 1, r) * p.1 (c, r + 1) ≠ p.1 (c, r) * p.2 (c, r))
    {ψ : (TorusVertex 2 2 → V × V × V × V) → ℂ}
    (hψ : ψ ∈ torusCutSpace (torusMatchedAveragingSites Uh Uv) c r) :
    torusBondCoefficientExtraction Uh Uv p ψ = 0 := by
  classical
  let L := torusBondCoefficientExtraction Uh Uv p
  have hle : torusCutSpace (torusMatchedAveragingSites Uh Uv) c r ≤ L.ker := by
    rw [torusCutSpace_eq_span_single]
    apply Submodule.span_le.mpr
    rintro _ ⟨η, rfl⟩
    change L (torusCutMap (torusMatchedAveragingSites Uh Uv) c r (Pi.single η 1)) = 0
    have hnet : torusCutMap (torusMatchedAveragingSites Uh Uv) c r (Pi.single η 1) =
        fun σ ↦ torusBondNetwork
          (fun v t ↦ representationAveragingSite (torusMatchedLegRep Uh Uv v)
            t.1 t.2.1 t.2.2.1 t.2.2.2 (σ v))
          (fun v ↦ if v.1 + 1 = c then torusCutHorizontalUnit η v else 1)
          (fun v ↦ if v.2 + 1 = r then torusCutVerticalUnit η v else 1) :=
      funext (torusCutMap_single_eq_bondNetwork _ c r η)
    rw [hnet]
    exact torusBondCoefficientExtraction_cutNetwork_eq_zero Uh Uv hU c r _ _
      (fun v hv ↦ ite_eq_right hv) (fun v hv ↦ ite_eq_right hv) p hp
  exact hle hψ

/-- Simultaneous membership in all four cuts kills every nonflat coefficient
of the derived bond-product expansion. -/
theorem torusBondCoefficientExtraction_eq_zero_of_mem_fourTorusCutSpace_not_flat
    (Uh Uv : TorusVertex 2 2 → G →* Matrix V V ℂ)
    (hU : IsSemiRegularTorusBondFamily Uh Uv)
    (p : TorusBondLabels 2 2 G) (hp : ¬IsTorusBondFlat p)
    {ψ : (TorusVertex 2 2 → V × V × V × V) → ℂ}
    (hψ : ψ ∈ fourTorusCutSpace (torusMatchedAveragingSites Uh Uv)) :
    torusBondCoefficientExtraction Uh Uv p ψ = 0 := by
  classical
  obtain ⟨v, hv⟩ := not_forall.mp hp
  exact torusBondCoefficientExtraction_eq_zero_of_mem_torusCutSpace Uh Uv hU v.1 v.2 p hv
    ((mem_torusCutSpace_iff _ _ _ _).mpr ((mem_fourTorusCutSpace_iff _ _).mp hψ v.1 v.2))

end TNLean.PEPS
