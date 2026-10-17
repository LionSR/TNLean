/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.RegularizedPatchMinimum
import TNLean.PEPS.AreaLaw.Cylinder
import QICLean.Analysis.ShiftedDensityTruncation

/-!
# Approximation by cylinders from ordered inverse filters

The inverse of the descending filter product is expanded in ascending order
according to the first factor contributing its spectral head. The preceding
tails act inside the current region, so their action does not increase the
inside dimension. The term containing only tails controls the approximation
error.

Source: OpenAI, Polynomial PEPS approximation of gapped square-grid ground states,
`03-patches.tex`, lines 484–532, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Independently formalized from the manuscript; no upstream Lean text is reused.
-/

open scoped BigOperators Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace TNLean.PEPS

/-- Expanding an ordered product according to its first head preserves the order
of every factor. The remaining term contains only tails.

Source: OpenAI, Polynomial PEPS approximation of gapped square-grid ground states,
`03-patches.tex`, lines 504–514, equation `eq:patch-first-head-expansion`. -/
private theorem prod_ofFn_add_eq_sum_first_head_add_prod
    {A : Type*} [Semiring A] {n : ℕ} (H T : Fin n → A) :
    (List.ofFn (fun j ↦ H j + T j)).prod =
      (∑ j : Fin n,
        ((List.ofFn T).take j.val).prod * H j *
          ((List.ofFn (fun i ↦ H i + T i)).drop (j.val + 1)).prod) +
        (List.ofFn T).prod := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [List.ofFn_succ, List.prod_cons, Fin.sum_univ_succ, Fin.val_zero,
      List.take_zero, List.prod_nil, one_mul, List.drop_succ_cons,
      List.drop_zero, Fin.val_succ, List.take_succ_cons]
    simpa only [add_mul, mul_add, Finset.mul_sum, mul_assoc, add_assoc] using
      congrArg (fun z ↦ H 0 * (List.ofFn fun i ↦ H i.succ + T i.succ).prod + T 0 * z)
        (ih (fun i ↦ H i.succ) (fun i ↦ T i.succ))

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Out : V → Type*} [∀ v, Fintype (Out v)] {m : ℕ}

/-- A feasible ordered filter tuple gives an approximation in a sum of regional
cylinders. Each inside dimension is at most the reciprocal spectral threshold.
The error is controlled by the norm of this same tuple's filtered output.

Source: OpenAI, Polynomial PEPS approximation of gapped square-grid ground states,
`03-patches.tex`, lines 484–532, equations `eq:patch-head-tail-bounds` and
`eq:patch-first-head-expansion`, revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
The assertion applies before minimizing the output norm. It includes repeated
regions, zero weights, singular densities, and an empty family of filters. -/
theorem exists_mem_iSup_dependentRegionCylinder_norm_sub_le
    (regions : Fin m → Finset V) (hregions : Monotone regions)
    (a : Fin m → ℝ) (ha : ∀ j, 0 ≤ a j) {b : ℝ} (hb : 0 < b)
    (Ω : EuclideanSpace ℂ ((w : (Finset.univ : Finset V)) → Out w.1))
    (_hΩ : ‖Ω‖ = 1)
    {x : ∀ j, Matrix ((w : regions j) → Out w.1)
      ((w : regions j) → Out w.1) ℂ}
    (hx : x ∈ regularizedPatchDomain (Out := Out) regions) :
    ∃ (S : (j : Fin m) → Submodule ℂ (((w : regions j) → Out w.1) → ℂ))
      (v : EuclideanSpace ℂ ((w : (Finset.univ : Finset V)) → Out w.1)),
      (∀ j, (Module.finrank ℂ (S j) : ℝ) ≤ 1 / b) ∧
      (v : (((w : (Finset.univ : Finset V)) → Out w.1) → ℂ)) ∈
        (⨆ j, dependentRegionCylinder (Out := Out) (regions j) (S j)) ∧
      ‖Ω - v‖ ≤ regularizedPatchObjective regions a b Ω x *
        (2 * b) ^ ((∑ j, a j) / 2) := by
  classical
  let H (j : Fin m) := Matrix.shiftedPowerHead (x j) b (a j / 2)
  let T (j : Fin m) := Matrix.shiftedPowerTail (x j) b (a j / 2)
  let P (j : Fin m) :=
    (List.ofFn fun i : Fin j.val ↦
      dependentSubregionOperatorLift
        (regions ⟨i.val, Nat.lt_trans i.isLt j.isLt⟩) (regions j)
        (hregions (Fin.le_iff_val_le_val.mpr (Nat.le_of_lt i.isLt)))
        (T ⟨i.val, Nat.lt_trans i.isLt j.isLt⟩)).prod
  let S (j : Fin m) := ((P j * H j).mulVecLin).range
  have hS (j : Fin m) : (Module.finrank ℂ (S j) : ℝ) ≤ 1 / b :=
    (show ((P j * H j).rank : ℝ) ≤ (H j).rank from
      Nat.cast_le.mpr (Matrix.rank_mul_le_right (P j) (H j))).trans
        ((hx j).1.rank_shiftedPowerHead_le (hx j).2 hb (a j / 2))
  let lift (j : Fin m) :
      Matrix ((w : regions j) → Out w.1) ((w : regions j) → Out w.1) ℂ →*
        Matrix ((w : (Finset.univ : Finset V)) → Out w.1)
          ((w : (Finset.univ : Finset V)) → Out w.1) ℂ :=
    { toFun := dependentRegionOperatorLift (Out := Out) (regions j)
      map_one' := dependentRegionOperatorLift_one (Out := Out) (regions j)
      map_mul' := dependentRegionOperatorLift_mul (Out := Out) (regions j) }
  have hP (j : Fin m) : lift j (P j) =
      (List.ofFn fun i : Fin j.val ↦
        dependentRegionOperatorLift (regions ⟨i.val, Nat.lt_trans i.isLt j.isLt⟩)
          (T ⟨i.val, Nat.lt_trans i.isLt j.isLt⟩)).prod := by
    simp only [P, map_list_prod, List.map_ofFn, Function.comp_def, lift,
      MonoidHom.coe_mk, OneHom.coe_mk, dependentRegionOperatorLift_subregion]
  have hrange (j : Fin m) : (lift j (P j * H j)).mulVecLin.range =
      dependentRegionCylinder (Out := Out) (regions j) (S j) :=
    range_dependentRegionOperatorLift (Out := Out) (regions j) (P j * H j)
  have hcancel (j : Fin m) :
      dependentRegionOperatorLift (Out := Out) (regions j)
          ((x j + b • 1) ^ (a j / 2)) *
        regularizedPatchFilter regions a b x j = 1 := by
    rw [regularizedPatchFilter, ← dependentRegionOperatorLift_mul, neg_div,
      (hx j).1.add_smul_one_rpow_mul_neg hb (a j / 2),
      dependentRegionOperatorLift_one (Out := Out)]
  let F (j : Fin m) := dependentRegionOperatorLift (Out := Out) (regions j)
    ((x j + b • 1) ^ (a j / 2))
  have hcancelList (l : List (Fin m)) : (l.map F).prod *
      ((l.map (regularizedPatchFilter regions a b x)).reverse).prod = 1 := by
    induction l with
    | nil => simp
    | cons j l ih =>
      simp only [List.map_cons, List.reverse_cons, List.prod_cons, List.prod_append,
        List.prod_nil, mul_one]
      calc
        _ = F j * ((l.map F).prod *
            ((l.map (regularizedPatchFilter regions a b x)).reverse).prod) *
            regularizedPatchFilter regions a b x j := by simp only [mul_assoc]
        _ = 1 := by rw [ih, mul_one, hcancel]
  have hundo : (List.ofFn F).prod * regularizedPatchOperator regions a b x = 1 := by
    simpa only [List.ofFn_eq_map, regularizedPatchOperator] using
      hcancelList (List.finRange m)
  have hsplit (j : Fin m) : lift j (H j) + lift j (T j) = F j := by
    change dependentRegionOperatorLift (Out := Out) (regions j) (H j) +
      dependentRegionOperatorLift (Out := Out) (regions j) (T j) =
      dependentRegionOperatorLift (Out := Out) (regions j) _
    rw [← Matrix.shiftedPowerHead_add_shiftedPowerTail, ← eq_sub_iff_add_eq,
      ← dependentRegionOperatorLift_sub, add_sub_cancel_right]
  have hexpand := prod_ofFn_add_eq_sum_first_head_add_prod
    (fun j ↦ lift j (H j)) (fun j ↦ lift j (T j))
  simp only [hsplit] at hexpand
  have hPtake (j : Fin m) :
      ((List.ofFn fun i ↦ lift i (T i)).take j.val).prod = lift j (P j) := by
    rw [hP]
    congr 1
    apply List.ext_getElem
    · simp
    · intro i hi hi'
      simp only [List.getElem_take, List.getElem_ofFn]
      rfl
  let G (j : Fin m) := lift j (P j * H j) *
    ((List.ofFn F).drop (j.val + 1)).prod
  have hsum : (List.ofFn F).prod = (∑ j, G j) +
      (List.ofFn fun j ↦ lift j (T j)).prod := by
    simpa only [G, hPtake, map_mul] using hexpand
  let ξ := regularizedPatchOutput regions a b Ω x
  let v : EuclideanSpace ℂ ((w : (Finset.univ : Finset V)) → Out w.1) :=
    WithLp.toLp 2 ((∑ j, G j) *ᵥ ξ)
  have hv : (v : (((w : (Finset.univ : Finset V)) → Out w.1) → ℂ)) ∈
      (⨆ j, dependentRegionCylinder (Out := Out) (regions j) (S j)) := by
    change ((∑ j, G j) *ᵥ ξ) ∈ _
    rw [Matrix.sum_mulVec]
    apply Submodule.sum_mem
    intro j _
    apply Submodule.mem_iSup_of_mem j
    rw [← hrange]
    refine ⟨((List.ofFn F).drop (j.val + 1)).prod *ᵥ ξ, ?_⟩
    exact Matrix.mulVec_mulVec _ _ _
  have hrecover : (Ω : _ → ℂ) = (List.ofFn F).prod *ᵥ ξ := by
    change (Ω : _ → ℂ) = (List.ofFn F).prod *ᵥ
      (regularizedPatchOperator regions a b x *ᵥ Ω)
    rw [Matrix.mulVec_mulVec, hundo, Matrix.one_mulVec]
  have herr : Ω - v = WithLp.toLp 2
      ((List.ofFn fun j ↦ lift j (T j)).prod *ᵥ ξ) := by
    rw [hsum, Matrix.add_mulVec, add_comm] at hrecover
    ext η
    exact congrFun (sub_eq_iff_eq_add.mpr hrecover) η
  have hT (j : Fin m)
      (ζ : EuclideanSpace ℂ ((w : (Finset.univ : Finset V)) → Out w.1)) :
      ‖WithLp.toLp 2 (lift j (T j) *ᵥ ζ)‖ ≤ (2 * b) ^ (a j / 2) * ‖ζ‖ :=
    (norm_dependentRegionOperatorLift_mulVec_le (regions j) (T j) ζ).trans
      (mul_le_mul_of_nonneg_right
        ((hx j).1.l2_opNorm_shiftedPowerTail_le hb (div_nonneg (ha j) (by positivity)))
        (norm_nonneg ζ))
  have htail (l : List (Fin m))
      (ζ : EuclideanSpace ℂ ((w : (Finset.univ : Finset V)) → Out w.1)) :
      ‖WithLp.toLp 2 ((l.map fun j ↦ lift j (T j)).prod *ᵥ ζ)‖ ≤
        (l.map fun j ↦ (2 * b) ^ (a j / 2)).prod * ‖ζ‖ := by
    induction l generalizing ζ with
    | nil => simp
    | cons j l ih =>
      calc
        _ ≤ (2 * b) ^ (a j / 2) *
            ‖WithLp.toLp 2 ((l.map fun i ↦ lift i (T i)).prod *ᵥ ζ)‖ := by
          simpa only [List.map_cons, List.prod_cons, ← Matrix.mulVec_mulVec,
            WithLp.ofLp_toLp] using
            hT j (WithLp.toLp 2 ((l.map fun i ↦ lift i (T i)).prod *ᵥ ζ))
        _ ≤ (2 * b) ^ (a j / 2) *
            ((l.map fun i ↦ (2 * b) ^ (a i / 2)).prod * ‖ζ‖) :=
          mul_le_mul_of_nonneg_left (ih ζ) (Real.rpow_nonneg (by positivity) _)
        _ = _ := by simp only [List.map_cons, List.prod_cons, mul_assoc]
  refine ⟨S, v, hS, hv, ?_⟩
  rw [herr]
  have ht := htail (List.finRange m) ξ
  simp only [← List.ofFn_eq_map, List.prod_ofFn] at ht
  rw [← Real.rpow_sum_of_pos (show 0 < 2 * b by positivity), ← Finset.sum_div] at ht
  simpa only [regularizedPatchObjective, ξ, mul_comm] using ht

end TNLean.PEPS
