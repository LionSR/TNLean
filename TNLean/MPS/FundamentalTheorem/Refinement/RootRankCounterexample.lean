/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Kraus.ChoiRankSpan
import QICLean.Analysis.Real.ComplexSqrt
import TNLean.MPS.Transfer.Irreducible.Periodic
import QICLean.Channel.KrausMap.KrausMap
import QICLean.Kraus.Transfer
import TNLean.MPS.FundamentalTheorem.Refinement.RootIrreducibility
import TNLean.MPS.Tensor.Physical.BlockingTransfer
import QICLean.Kraus.IrreducibleAction

/-!
# A cyclic-reset channel whose square has smaller Kraus rank

Five sectors of dimensions \(1,2,2,1,1\) give a seven-dimensional channel.
Its Kraus operators are normalized matrix units from each sector to the next.
The channel has Kraus rank ten, whereas its square has Kraus rank nine.

**Scope restriction (arXiv:1708.00029, Theorem 4.1 converse):** This example
concerns a specified root. It does not rule out choosing a different root of
the same square with fewer Kraus operators. See
`docs/paper-gaps/dccsp17_root_kraus_rank_thm41.tex`.

It also contains the following results.

* `MPSTensor.CyclicResetCounterexample.square_map_apply`,
  `MPSTensor.CyclicResetCounterexample.transferMap_square_eq_pow`: square of the seven-dimensional
  cyclic-reset channel.
* `MPSTensor.CyclicResetCounterexample.square_isIrreducibleFamily`,
  `MPSTensor.CyclicResetCounterexample.root_isIrreducibleFamily`: irreducibility of the
  seven-dimensional cyclic-reset channel.
-/

section RootRankCounterexample

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
       simp +decide [Fin.sum_univ_succ, sector, show (2 : ℂ)⁻¹ + 2⁻¹ = 1 by norm_num])
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
       simp +decide [Fin.sum_univ_succ, sector, show (2 : ℂ)⁻¹ + 2⁻¹ = 1 by norm_num])
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

end RootRankCounterexample

section RootRankChannelSquare

/-!
## Square of the seven-dimensional cyclic-reset channel

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

/-- The two-step reset discards off-diagonal entries and prepares the
normalized identity in the sector two positions later. -/
theorem square_map_apply (X : Matrix (Fin 7) (Fin 7) ℂ)
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
  rw [square_map_apply, root_map_diag]
  by_cases hab : a = b
  · subst b
    simp only [↓reduceIte]
    simp_rw [root_map_diag X]
    fin_cases a <;>
      simp [sector, outputWeight, Complex.invSqrtTwo_mul_self,
        Fin.sum_univ_succ] <;> ring
  · simp [hab]

end MPSTensor.CyclicResetCounterexample

end RootRankChannelSquare

section RootRankIrreducibility

/-!
## Irreducibility of the seven-dimensional cyclic-reset channel

The two-step matrix units act transitively on the five cyclic sectors.
Consequently the square channel, and hence its root, have no nontrivial
invariant subspace.

Source context: arXiv:1708.00029, Theorem 4.1. The example concerns the
rank of a specified channel root; it does not obstruct selecting another root.
-/

open scoped Matrix

namespace MPSTensor.CyclicResetCounterexample

private theorem square_unit_preserves
    (W : Submodule ℂ (Fin 7 → ℂ))
    (hW : Matrix.IsInvariantSubmodule square W)
    (a b : Fin 7) (hab : sector a = sector b + 2)
    (v : Fin 7 → ℂ) (hv : v ∈ W) :
    (Matrix.stdBasis ℂ (Fin 7) (Fin 7) (a, b)).mulVec v ∈ W := by
  let i : Fin 9 := twoStepIndex.symm ⟨(a,b),hab⟩
  have hi := hW i v hv
  have hi' : outputWeight a •
      (Matrix.stdBasis ℂ (Fin 7) (Fin 7) (a,b)).mulVec v ∈ W := by
    simpa only [square, i, Equiv.apply_symm_apply, Matrix.smul_mulVec] using hi
  have := W.smul_mem (outputWeight a)⁻¹ hi'
  simpa only [smul_smul, inv_mul_cancel₀ (outputWeight_ne_zero a), one_smul] using this

private def sectorRepresentative : Fin 5 → Fin 7 := ![0, 1, 3, 5, 6]

private theorem sector_sectorRepresentative (s : Fin 5) :
    sector (sectorRepresentative s) = s := by
  fin_cases s <;> decide

private theorem five_two_steps_cover (s t : Fin 5) :
    t = s + 2 ∨
    t = (s + 2) + 2 ∨
    t = ((s + 2) + 2) + 2 ∨
    t = (((s + 2) + 2) + 2) + 2 ∨
    t = ((((s + 2) + 2) + 2) + 2) + 2 := by
  fin_cases s <;> fin_cases t <;> decide

private theorem standardUnit_mulVec (a b : Fin 7) (v : Fin 7 → ℂ) :
    (Matrix.stdBasis ℂ (Fin 7) (Fin 7) (a, b)).mulVec v =
      v b • Pi.single a (1 : ℂ) := by
  ext x
  simp [Matrix.stdBasis_eq_single, Matrix.single_mulVec, Pi.single_apply,
    Function.update_apply]

/-- The nine two-step matrix units act irreducibly on the seven-dimensional
bond space. Source context: arXiv:1708.00029, Theorem 4.1 converse. -/
theorem square_isIrreducibleFamily : Kraus.IsIrreducibleFamily square := by
  classical
  apply Kraus.isIrreducibleFamily_of_isIrreducibleAction square
  intro W hW
  by_cases hbot : W = ⊥
  · exact Or.inl hbot
  right
  obtain ⟨v, hv, hv0⟩ := W.ne_bot_iff.mp hbot
  obtain ⟨b, hb⟩ : ∃ b : Fin 7, v b ≠ 0 := by
    by_contra h
    push Not at h
    exact hv0 (funext h)
  have hstep (a b : Fin 7) (hab : sector a = sector b + 2)
      (v : Fin 7 → ℂ) (hv : v ∈ W) (hvb : v b ≠ 0) :
      Pi.single a (1 : ℂ) ∈ W := by
    have h := square_unit_preserves W hW a b hab v hv
    rw [standardUnit_mulVec] at h
    have h' := W.smul_mem (v b)⁻¹ h
    simpa only [smul_smul, inv_mul_cancel₀ hvb, one_smul] using h'
  have hnext (s : Fin 5)
      (hs : ∀ a : Fin 7, sector a = s → Pi.single a (1 : ℂ) ∈ W) :
      ∀ a : Fin 7, sector a = s + 2 → Pi.single a (1 : ℂ) ∈ W := by
    intro a ha
    let b := sectorRepresentative s
    have hbW : Pi.single b (1 : ℂ) ∈ W :=
      hs b (sector_sectorRepresentative s)
    apply hstep a b (by simpa only [b, sector_sectorRepresentative] using ha)
      (Pi.single b (1 : ℂ)) hbW
    simp [b]
  let s := sector b
  have h1 : ∀ a : Fin 7, sector a = s + 2 → Pi.single a (1 : ℂ) ∈ W := by
    intro a ha
    exact hstep a b ha v hv hb
  have h2 := hnext (s + 2) h1
  have h3 := hnext ((s + 2) + 2) h2
  have h4 := hnext (((s + 2) + 2) + 2) h3
  have h5 := hnext ((((s + 2) + 2) + 2) + 2) h4
  have hall (a : Fin 7) : Pi.single a (1 : ℂ) ∈ W := by
    rcases five_two_steps_cover s (sector a) with h | h | h | h | h
    · exact h1 a h
    · exact h2 a h
    · exact h3 a h
    · exact h4 a h
    · exact h5 a h
  apply top_unique
  intro w _
  rw [← Finset.univ_sum_single w]
  apply Submodule.sum_mem
  intro a _
  have heq : Pi.single a (w a) = w a • Pi.single a (1 : ℂ) := by
    ext x
    by_cases h : x = a <;> simp [h]
  rw [heq]
  exact W.smul_mem (w a) (hall a)

/-- The original cyclic-reset root is irreducible because its square is.
Source context: arXiv:1708.00029, Theorem 4.1 converse. -/
theorem root_isIrreducibleFamily : Kraus.IsIrreducibleFamily root := by
  apply isIrreducibleFamily_of_transferMap_eq_blockTensor square root 2
    square_isIrreducibleFamily
  rw [transferMap_blockTensor]
  exact transferMap_square_eq_pow

end MPSTensor.CyclicResetCounterexample

end RootRankIrreducibility
