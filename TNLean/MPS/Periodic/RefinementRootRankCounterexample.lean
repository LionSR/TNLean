/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.KrausSpanRank
import TNLean.Algebra.ComplexSqrt
import TNLean.MPS.Periodic.Defs
import QICLean.Channel.KrausMap
import QICLean.Kraus.MapIterate

/-!
# A cyclic-reset channel whose square has smaller Kraus rank

Five sectors of dimensions \(1,2,2,1,1\) give a seven-dimensional channel.
Its Kraus operators are normalized matrix units from each sector to the next.
The channel has Kraus rank ten, whereas its square has Kraus rank nine.

**Scope restriction (arXiv:1708.00029, Theorem 4.1 converse):** This example
concerns a specified root. It does not rule out choosing a different root of
the same square with fewer Kraus operators. See
`docs/paper-gaps/dccsp17_root_kraus_rank_thm41.tex`.
-/

open scoped Matrix BigOperators

namespace MPSTensor.CyclicResetCounterexample

/-- The five cyclic sectors have dimensions \(1,2,2,1,1\). -/
def sector : Fin 7 → Fin 5 := ![0, 1, 1, 2, 2, 3, 4]

/-- Matrix-unit indices from a sector to its successor. -/
abbrev AdjacentPair := {p : Fin 7 × Fin 7 // sector p.1 = sector p.2 + 1}

/-- Matrix-unit indices from a sector to its second successor. -/
abbrev TwoStepPair := {p : Fin 7 × Fin 7 // sector p.1 = sector p.2 + 2}

private theorem card_adjacentPair : Fintype.card AdjacentPair = 10 := by
  decide

private theorem card_twoStepPair : Fintype.card TwoStepPair = 9 := by
  decide

/-- The chosen order of the ten adjacent-sector matrix units. -/
noncomputable def adjacentIndex : Fin 10 ≃ AdjacentPair :=
  (finCongr card_adjacentPair.symm).trans (Fintype.equivFin AdjacentPair).symm

/-- The chosen order of the nine two-step matrix units. -/
noncomputable def twoStepIndex : Fin 9 ≃ TwoStepPair :=
  (finCongr card_twoStepPair.symm).trans (Fintype.equivFin TwoStepPair).symm

/-- The normalization of a matrix unit with the given output row. -/
noncomputable def outputWeight (row : Fin 7) : ℂ :=
  if sector row = 1 ∨ sector row = 2 then Complex.invSqrtTwo else 1

/-- The seven-dimensional cyclic-reset root, on ten physical letters. -/
noncomputable def root : MPSTensor 10 7 := fun i ↦
  outputWeight (adjacentIndex i).1.1 •
    Matrix.stdBasis ℂ (Fin 7) (Fin 7) (adjacentIndex i).1

/-- The square of the cyclic-reset channel, on its minimal nine-letter alphabet. -/
noncomputable def square : MPSTensor 9 7 := fun i ↦
  outputWeight (twoStepIndex i).1.1 •
    Matrix.stdBasis ℂ (Fin 7) (Fin 7) (twoStepIndex i).1

theorem outputWeight_ne_zero (row : Fin 7) : outputWeight row ≠ 0 := by
  unfold outputWeight
  split_ifs <;> simp [Complex.invSqrtTwo_ne_zero]

private theorem weighted_matrixUnits_linearIndependent {n : ℕ}
    {P : (Fin 7 × Fin 7) → Prop}
    (e : Fin n ≃ {p : Fin 7 × Fin 7 // P p}) :
    LinearIndependent ℂ (fun i : Fin n ↦
      outputWeight (e i).1.1 • Matrix.stdBasis ℂ (Fin 7) (Fin 7) (e i).1) := by
  classical
  have hinj : Function.Injective (fun i : Fin n ↦ (e i).1) := by
    intro i j h
    apply e.injective
    exact Subtype.ext h
  have hli : LinearIndependent ℂ (fun i : Fin n ↦
      Matrix.stdBasis ℂ (Fin 7) (Fin 7) (e i).1) :=
    (Matrix.stdBasis ℂ (Fin 7) (Fin 7)).linearIndependent.comp _ hinj
  let w : Fin n → ℂˣ := fun i ↦ Units.mk0 _ (outputWeight_ne_zero (e i).1.1)
  convert hli.units_smul w using 1
  ext i
  simp [w, Pi.smul_apply']

/-- The root channel has Kraus rank ten. -/
theorem choiRank_root : Channel.choiRank (Kraus.mapLM root) = 10 := by
  rw [Channel.choiRank_mapLM_eq_finrank_span]
  have hli : LinearIndependent ℂ root := by
    exact weighted_matrixUnits_linearIndependent adjacentIndex
  simpa using finrank_span_eq_card hli

/-- The square channel has Kraus rank nine. -/
theorem choiRank_square : Channel.choiRank (Kraus.mapLM square) = 9 := by
  rw [Channel.choiRank_mapLM_eq_finrank_span]
  have hli : LinearIndependent ℂ square := by
    exact weighted_matrixUnits_linearIndependent twoStepIndex
  simpa using finrank_span_eq_card hli

private theorem weighted_matrixUnit_conj_mul (w : ℂ) (p : Fin 7 × Fin 7) :
    (w • Matrix.stdBasis ℂ (Fin 7) (Fin 7) p)ᴴ *
      (w • Matrix.stdBasis ℂ (Fin 7) (Fin 7) p) =
        (star w * w) • Matrix.stdBasis ℂ (Fin 7) (Fin 7) (p.2, p.2) := by
  rcases p with ⟨a, b⟩
  simp [Matrix.stdBasis_eq_single, Matrix.conjTranspose_single,
    Matrix.single_mul_single_same]

theorem outputWeight_norm (row : Fin 7) :
    star (outputWeight row) * outputWeight row =
      if sector row = 1 ∨ sector row = 2 then (2 : ℂ)⁻¹ else 1 := by
  unfold outputWeight
  split_ifs <;> simp [Complex.invSqrtTwo_mul_self]

/-- The cyclic-reset root is trace preserving. -/
theorem root_isTP : Kraus.IsTP root := by
  classical
  unfold Kraus.IsTP
  have hreindex :
      (∑ i : Fin 10, (root i)ᴴ * root i) =
        ∑ p : AdjacentPair,
          (outputWeight p.1.1 • Matrix.stdBasis ℂ (Fin 7) (Fin 7) p.1)ᴴ *
            (outputWeight p.1.1 • Matrix.stdBasis ℂ (Fin 7) (Fin 7) p.1) := by
    refine Fintype.sum_equiv adjacentIndex _ _ ?_
    intro i
    rfl
  rw [hreindex]
  simp only [weighted_matrixUnit_conj_mul, outputWeight_norm]
  ext b c
  simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.stdBasis_eq_single,
    Matrix.single_apply, Matrix.one_apply]
  by_cases hbc : b = c
  · subst c
    simp only [and_self]
    rw [← Finset.sum_subtype
        (p := fun p : Fin 7 × Fin 7 ↦ sector p.1 = sector p.2 + 1)
        (s := Finset.univ.filter (fun p : Fin 7 × Fin 7 ↦
          sector p.1 = sector p.2 + 1))
        (h := by simp)
        (f := fun p ↦ (if sector p.1 = 1 ∨ sector p.1 = 2
          then (2 : ℂ)⁻¹ else 1) • if p.2 = b then (1 : ℂ) else 0)]
    fin_cases b <;>
      (rw [Finset.sum_filter]
       rw [Fintype.sum_prod_type]
       simp +decide [Fin.sum_univ_succ, sector] <;> norm_num)
  · have h : ∀ x : Fin 7, ¬(x = b ∧ x = c) := by
      intro x hx
      exact hbc (hx.1.symm.trans hx.2)
    simp only [h, ite_false, smul_zero, Finset.sum_const_zero, hbc]

/-- The nine-letter tensor for the square is trace preserving. -/
theorem square_isTP : Kraus.IsTP square := by
  classical
  unfold Kraus.IsTP
  have hreindex :
      (∑ i : Fin 9, (square i)ᴴ * square i) =
        ∑ p : TwoStepPair,
          (outputWeight p.1.1 • Matrix.stdBasis ℂ (Fin 7) (Fin 7) p.1)ᴴ *
            (outputWeight p.1.1 • Matrix.stdBasis ℂ (Fin 7) (Fin 7) p.1) := by
    refine Fintype.sum_equiv twoStepIndex _ _ ?_
    intro i
    rfl
  rw [hreindex]
  simp only [weighted_matrixUnit_conj_mul, outputWeight_norm]
  ext b c
  simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.stdBasis_eq_single,
    Matrix.single_apply, Matrix.one_apply]
  by_cases hbc : b = c
  · subst c
    simp only [and_self]
    rw [← Finset.sum_subtype
        (p := fun p : Fin 7 × Fin 7 ↦ sector p.1 = sector p.2 + 2)
        (s := Finset.univ.filter (fun p : Fin 7 × Fin 7 ↦
          sector p.1 = sector p.2 + 2))
        (h := by simp)
        (f := fun p ↦ (if sector p.1 = 1 ∨ sector p.1 = 2
          then (2 : ℂ)⁻¹ else 1) • if p.2 = b then (1 : ℂ) else 0)]
    fin_cases b <;>
      (rw [Finset.sum_filter]
       rw [Fintype.sum_prod_type]
       simp +decide [Fin.sum_univ_succ, sector] <;> norm_num)
  · have h : ∀ x : Fin 7, ¬(x = b ∧ x = c) := by
      intro x hx
      exact hbc (hx.1.symm.trans hx.2)
    simp only [h, ite_false, smul_zero, Finset.sum_const_zero, hbc]

/-- The specified cyclic-reset root defines a quantum channel. -/
theorem root_isChannel : IsChannel (Kraus.mapLM root) :=
  Kraus.isChannel_mapLM root root_isTP

/-- The nine-letter tensor defines a quantum channel. -/
theorem square_isChannel : IsChannel (Kraus.mapLM square) :=
  Kraus.isChannel_mapLM square square_isTP

end MPSTensor.CyclicResetCounterexample
