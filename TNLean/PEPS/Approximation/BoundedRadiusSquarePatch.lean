/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.NestedCylinderSquarePatch
import TNLean.PEPS.Approximation.SquarePatchIntegerCoordinates

/-!
# Exact square patches at bounded radius

A square of radius at most four contains at most 81 integer sites. Taking
its full inside space in the nested-cylinder construction gives zero
approximation error with at most \(q^{81}\) cylinder terms.

Source: polynomial-PEPS manuscript, Proposition 4.1, `03-patches.tex`,
lines 53–54, revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

Independently formalized from the manuscript; no upstream Lean proof text is reused.
-/

open scoped BigOperators Matrix

namespace TNLean.PEPS.Approximation

/-- Every square of radius at most four admits an exact square-patch expansion
with at most `q ^ 81` terms. The input vector is arbitrary, and the domain and
sample may be empty. The residual uses the literal sum of cylinder projectors.

Source: polynomial-PEPS manuscript, Proposition 4.1, `03-patches.tex`,
lines 53–54, revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
The same counting argument includes the endpoint `u = 4`. -/
theorem exists_squarePatch_integerCoordinates_of_radius_le_four
    (Λ : Finset (ℤ × ℤ)) {q : ℕ} (hq : 1 ≤ q)
    (z : ℝ × ℝ) {u : ℝ} (hu : 0 < u) (hu4 : u ≤ 4)
    (Ω : EuclideanSpace ℂ
      ((w : (Finset.univ : Finset (Lattice.Site Λ))) → Fin q)) :
    letI : LinearOrder (Lattice.Site Λ) :=
      (Fintype.equivFin (Lattice.Site Λ)).linearOrder
    ∃ P : EncodedFrame.SquarePatch
        (fun x : Lattice.Site Λ ↦ ((x.1.1 : ℝ), (x.1.2 : ℝ))) q,
      P.center = z ∧ P.scale = u ∧
      (∑ j, P.dim j) ≤ q ^ 81 ∧
      ‖Lattice.Sheet.act (1 - P.cylSum)
        (dependentGlobalConfigIsometry (Out := fun _ : Lattice.Site Λ ↦ Fin q) Ω)‖ = 0 := by
  classical
  let : LinearOrder (Lattice.Site Λ) :=
    (Fintype.equivFin (Lattice.Site Λ)).linearOrder
  obtain ⟨P, _, hz, hs, _, hd, he⟩ :=
    EncodedFrame.exists_squarePatch_of_mem_iSup_dependentRegionCylinder
      (fun x : Lattice.Site Λ ↦ ((x.1.1 : ℝ), (x.1.2 : ℝ))) z hu
      (fun _ : Fin 1 ↦ u) monotone_const (fun _ ↦ le_rfl) (fun _ ↦ by linarith)
      (fun _ ↦ ⊤) Ω Ω (Submodule.mem_iSup_of_mem (0 : Fin 1)
        ((mem_dependentRegionCylinder _ _ _).mpr (fun _ ↦ Submodule.mem_top)))
  refine ⟨P, hz, hs, ?_, ?_⟩
  · refine hd.trans ?_
    simp only [Fin.sum_univ_one, finrank_top, Module.finrank_fintype_fun_eq_card,
      Fintype.card_fun, Fintype.card_fin, Fintype.card_coe]
    simpa only [squareSample_integerCoordinates] using
      pow_le_pow_right' hq
        (AreaLaw.Geometry.card_closedSquareSample_le_eightyOne Λ z hu.le hu4)
  · exact le_antisymm (by simpa only [sub_self, norm_zero] using he) (norm_nonneg _)

end TNLean.PEPS.Approximation
