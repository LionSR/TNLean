/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Basic.Complex.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Logic.Equiv.Finset
import Mathlib.Tactic.Ring

/-!
# One-magnon vectors and exchange interactions

A one-magnon vector is a superposition of the configurations with precisely
one down spin. Exchanging two sites exchanges the corresponding coefficients.
For a permutation without fixed points, the sum of the edge singlet terms
acts on these coefficients by one half of the graph Laplacian.

Source: Koma--Nachtergaele, arXiv:cond-mat/9512120, Lemma 4, equation (3.13).
The exchange sum below applies to finite cyclic edges independently of a tensor.
-/

open scoped BigOperators

namespace SpinChain

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A configuration with its unique down spin at the specified site. -/
def singleDown (j : ι) : ι → Fin 2 := fun k => if k = j then 1 else 0

/-- The configuration amplitudes of a one-magnon vector. -/
def oneMagnon (f : ι → ℂ) (σ : ι → Fin 2) : ℂ :=
  ∑ j, if σ = singleDown j then f j else 0

omit [Fintype ι] in
/-- The down-spin configurations at distinct sites are distinct. -/
theorem singleDown_injective : Function.Injective (singleDown (ι := ι)) := by
  intro i j h
  have hij := congrFun h i
  simpa [singleDown] using hij

/-- The coefficient at a one-down-spin configuration is its site amplitude. -/
@[simp] theorem oneMagnon_singleDown (f : ι → ℂ) (j : ι) :
    oneMagnon f (singleDown j) = f j := by
  simp [oneMagnon, singleDown_injective.eq_iff]

/-- A nonzero coefficient function gives a nonzero one-magnon vector. -/
theorem oneMagnon_ne_zero {f : ι → ℂ} (hf : f ≠ 0) : oneMagnon f ≠ 0 := by
  intro h
  apply hf
  funext j
  have hj := congrFun h (singleDown j)
  simpa using hj

omit [Fintype ι] in
/-- Relabelling a one-down-spin configuration moves its distinguished site. -/
theorem singleDown_comp_perm (e : Equiv.Perm ι) (j : ι) :
    singleDown j ∘ e = singleDown (e.symm j) := by
  funext k
  simp [singleDown, e.eq_symm_apply]

/-- Multiplying every site amplitude multiplies the one-magnon vector. -/
theorem oneMagnon_smul (c : ℂ) (f : ι → ℂ) (σ : ι → Fin 2) :
    oneMagnon (fun j => c * f j) σ = c * oneMagnon f σ := by
  simp only [oneMagnon, Finset.mul_sum, mul_ite, mul_zero]

/-- A configuration outside the one-down-spin sector has zero amplitude. -/
theorem oneMagnon_eq_zero_of_not_singleDown (f : ι → ℂ) {σ : ι → Fin 2}
    (hσ : ∀ j, σ ≠ singleDown j) : oneMagnon f σ = 0 := by
  simp [oneMagnon, hσ]

/-- Exchanging two physical sites exchanges the corresponding coefficients. -/
theorem oneMagnon_comp_swap (f : ι → ℂ) (a b : ι) (σ : ι → Fin 2) :
    oneMagnon f (σ ∘ Equiv.swap a b) = oneMagnon (f ∘ Equiv.swap a b) σ := by
  by_cases hσ : ∃ j, σ = singleDown j
  · obtain ⟨j, rfl⟩ := hσ
    simp [singleDown_comp_perm]
  · have hσ' : ∀ j, σ ≠ singleDown j := by simpa using hσ
    have hcomp : ∀ j, σ ∘ Equiv.swap a b ≠ singleDown j := by
      intro j h
      apply hσ' (Equiv.swap a b j)
      calc
        σ = (σ ∘ Equiv.swap a b) ∘ Equiv.swap a b := by
          funext k
          simp
        _ = singleDown j ∘ Equiv.swap a b :=
          congrArg (fun g : ι → Fin 2 => g ∘ Equiv.swap a b) h
        _ = singleDown (Equiv.swap a b j) := by
          simpa using singleDown_comp_perm (Equiv.swap a b) j
    rw [oneMagnon_eq_zero_of_not_singleDown f hcomp,
      oneMagnon_eq_zero_of_not_singleDown _ hσ']

/-- Summing exchange differences along a permutation gives the cyclic
nearest-neighbour Laplacian on the coefficient function. -/
theorem sum_sub_swap_eq (e : Equiv.Perm ι) (he : ∀ i, e i ≠ i)
    (f : ι → ℂ) (j : ι) :
    ∑ i, (f j - f (Equiv.swap i (e i) j)) =
      2 * f j - f (e j) - f (e.symm j) := by
  have hprev : j ≠ e.symm j :=
    fun h => he j ((congrArg e h).trans (e.apply_symm_apply j))
  have hterm (i : ι) : f j - f (Equiv.swap i (e i) j) =
      (if i = j then f j - f (e j) else 0) +
      (if i = e.symm j then f j - f (e.symm j) else 0) := by
    by_cases hi : i = j
    · simp [hi, hprev]
    · by_cases hp : i = e.symm j
      · simp [hp, Ne.symm hprev]
      · have hji : j ≠ e i := fun h =>
          hp ((e.symm_apply_apply i).symm.trans (congrArg e.symm h.symm))
        simp [Equiv.swap_apply_def, hi, Ne.symm hi, hp, hji]
  simp [hterm, Finset.sum_add_distrib]
  ring

/-- The exchange Hamiltonian along a permutation without fixed points acts
on one-magnon coefficients by one half of the cyclic graph Laplacian. -/
theorem oneMagnon_edge_sum (e : Equiv.Perm ι) (he : ∀ i, e i ≠ i)
    (f : ι → ℂ) (σ : ι → Fin 2) :
    (∑ i, (oneMagnon f σ - oneMagnon f (σ ∘ Equiv.swap i (e i)))) / 2 =
      oneMagnon (fun j => f j - (f (e j) + f (e.symm j)) / 2) σ := by
  simp_rw [oneMagnon_comp_swap]
  by_cases hσ : ∃ j, σ = singleDown j
  · obtain ⟨j, rfl⟩ := hσ
    simp only [oneMagnon_singleDown, Function.comp_apply]
    rw [sum_sub_swap_eq e he]
    ring
  · have hσ' : ∀ j, σ ≠ singleDown j := by simpa using hσ
    simp [oneMagnon_eq_zero_of_not_singleDown _ hσ']

end SpinChain
