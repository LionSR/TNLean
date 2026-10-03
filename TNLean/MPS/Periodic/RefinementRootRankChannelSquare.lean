/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Periodic.RefinementRootRankCounterexample

/-!
# Square of the seven-dimensional cyclic-reset channel

Two successive reset steps discard the input within its sector and prepare
the normalized identity in the sector two positions later.

Source context: arXiv:1708.00029, Theorem 4.1 converse. This identity
concerns a specified channel root and makes no assertion about the rank of
all roots.
-/

open scoped Matrix BigOperators

namespace MPSTensor.CyclicResetCounterexample

private theorem weightedUnit_map_apply (w : ℂ) (r c a b : Fin 7)
    (X : Matrix (Fin 7) (Fin 7) ℂ) :
    ((w • Matrix.stdBasis ℂ (Fin 7) (Fin 7) (r, c)) * X *
      (w • Matrix.stdBasis ℂ (Fin 7) (Fin 7) (r, c))ᴴ) a b =
      if a = r ∧ b = r then (w * star w) * X c c else 0 := by
  simp only [Matrix.stdBasis_eq_single]
  by_cases ha : a = r <;> by_cases hb : b = r <;>
    simp [ha, hb, mul_comm, mul_left_comm, mul_assoc]

private theorem weightedUnits_map_apply {n : ℕ}
    {P : (Fin 7 × Fin 7) → Prop}
    [Fintype {p : Fin 7 × Fin 7 // P p}]
    (e : Fin n ≃ {p : Fin 7 × Fin 7 // P p})
    (X : Matrix (Fin 7) (Fin 7) ℂ) (a b : Fin 7) :
    (Kraus.mapLM (fun i : Fin n ↦
      outputWeight (e i).1.1 • Matrix.stdBasis ℂ (Fin 7) (Fin 7) (e i).1) X) a b =
      ∑ p : {p : Fin 7 × Fin 7 // P p},
        if a = p.1.1 ∧ b = p.1.1 then
          (outputWeight p.1.1 * star (outputWeight p.1.1)) * X p.1.2 p.1.2
        else 0 := by
  classical
  simp only [Kraus.mapLM_apply, Kraus.map_apply, Matrix.sum_apply]
  rw [← Fintype.sum_equiv e]
  intro x
  exact weightedUnit_map_apply _ _ _ a b X

private theorem resetMap_apply {n : ℕ} (k : Fin 5)
    (e : Fin n ≃ {p : Fin 7 × Fin 7 // sector p.1 = sector p.2 + k})
    (X : Matrix (Fin 7) (Fin 7) ℂ) (a b : Fin 7) :
    (Kraus.mapLM (fun i : Fin n ↦
      outputWeight (e i).1.1 • Matrix.stdBasis ℂ (Fin 7) (Fin 7) (e i).1) X) a b =
      if a = b then
        (outputWeight a * star (outputWeight a)) *
          ∑ c : Fin 7, if sector a = sector c + k then X c c else 0
      else 0 := by
  classical
  rw [weightedUnits_map_apply e]
  let f : Fin 7 × Fin 7 → ℂ := fun p ↦
    if a = p.1 ∧ b = p.1 then
      (outputWeight p.1 * star (outputWeight p.1)) * X p.2 p.2 else 0
  change (∑ p : {p : Fin 7 × Fin 7 // sector p.1 = sector p.2 + k}, f p.1) = _
  rw [← Finset.subtype_univ (fun p : Fin 7 × Fin 7 => sector p.1 = sector p.2 + k)]
  rw [Finset.sum_subtype_eq_sum_filter]
  rw [Finset.sum_filter]
  simp only [Fintype.sum_prod_type]
  by_cases hab : a = b
  · subst b
    simp only [f, and_self, ↓reduceIte]
    rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro c _
    have hsum :
        (∑ r : Fin 7,
          if sector r = sector c + k then
            if a = r then outputWeight r * (star (outputWeight r) * X c c) else 0
          else 0) =
        (if sector a = sector c + k then
          if a = a then outputWeight a * (star (outputWeight a) * X c c) else 0
        else 0) := by
      apply Finset.sum_eq_single a
      · intro r _ hr
        simp [Ne.symm hr]
      · simp
    simpa only [mul_assoc, mul_ite, mul_zero, ite_true] using hsum
  · have hrow (r : Fin 7) : ¬(a = r ∧ b = r) := by
      rintro ⟨har, hbr⟩
      exact hab (har.trans hbr.symm)
    simp [f, hab, hrow]

private theorem root_map_diag (X : Matrix (Fin 7) (Fin 7) ℂ)
    (a b : Fin 7) :
    (Kraus.mapLM root X) a b =
      if a = b then
        (outputWeight a * star (outputWeight a)) *
          ∑ c : Fin 7, if sector a = sector c + 1 then X c c else 0
      else 0 := by
  change (Kraus.mapLM (fun i : Fin 10 ↦
    outputWeight (adjacentIndex i).1.1 •
      Matrix.stdBasis ℂ (Fin 7) (Fin 7) (adjacentIndex i).1) X) a b = _
  exact resetMap_apply 1 adjacentIndex X a b

private theorem square_map_diag (X : Matrix (Fin 7) (Fin 7) ℂ)
    (a b : Fin 7) :
    (Kraus.mapLM square X) a b =
      if a = b then
        (outputWeight a * star (outputWeight a)) *
          ∑ c : Fin 7, if sector a = sector c + 2 then X c c else 0
      else 0 := by
  change (Kraus.mapLM (fun i : Fin 9 ↦
    outputWeight (twoStepIndex i).1.1 •
      Matrix.stdBasis ℂ (Fin 7) (Fin 7) (twoStepIndex i).1) X) a b = _
  exact resetMap_apply 2 twoStepIndex X a b

/-- Two successive cyclic resets equal the direct two-step reset channel.
Source context: arXiv:1708.00029, Theorem 4.1 converse. -/
theorem transferMap_square_eq_pow :
    Kraus.transferMap square = (Kraus.transferMap root) ^ 2 := by
  apply LinearMap.ext
  intro X
  ext a b
  change (Kraus.mapLM square X) a b =
    (((Kraus.mapLM root) ^ 2) X) a b
  rw [pow_two]
  change (Kraus.mapLM square X) a b =
    (Kraus.mapLM root (Kraus.mapLM root X)) a b
  rw [square_map_diag, root_map_diag]
  by_cases hab : a = b
  · subst b
    simp only [↓reduceIte]
    simp_rw [root_map_diag X]
    fin_cases a <;>
      simp [sector, outputWeight, Complex.invSqrtTwo_mul_self,
        Fin.sum_univ_succ] <;> ring
  · simp [hab]

end MPSTensor.CyclicResetCounterexample
