/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.Huang.GridHamiltonian
import TNLean.Circuit.SiteExpectationOrder
import QICLean.Analysis.HermitianUnitaryPath
import Mathlib.Data.List.OfFn

/-!
# Exact evolution inside the explicit grid blocks

The within-block Hamiltonians have pairwise disjoint supports. Their exponential is
therefore the ordered product of their individual exponentials, each supported on its
actual block. No block propagator is supplied as additional data.

Source: Osborne, arXiv:quant-ph/0508031v2, Figures 1--2 and equations (2)--(3);
Huang, arXiv:1406.6355v6, Section 5.4, Lemma 19.
-/

open Matrix QuantumCircuit
open scoped BigOperators Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw

private theorem hermitianUnitaryPath_add_of_commute
    {n : Type*} [Fintype n] [DecidableEq n] (A B : Matrix n n ℂ) (hAB : Commute A B)
    (t : ℝ) : hermitianUnitaryPath (A + B) t =
      hermitianUnitaryPath A t * hermitianUnitaryPath B t := by
  unfold hermitianUnitaryPath
  rw [smul_add, smul_add]
  exact Matrix.exp_add_of_commute _ _
    ((((hAB.smul_left Complex.I).smul_right Complex.I).smul_left t).smul_right t)

private theorem hermitianUnitaryPath_fin_sum_of_commute
    {n : Type*} [Fintype n] [DecidableEq n] {m : ℕ}
    (A : Fin m → Matrix n n ℂ) (hc : Pairwise fun j k ↦ Commute (A j) (A k)) (t : ℝ) :
    hermitianUnitaryPath (∑ j, A j) t =
      (List.ofFn fun j ↦ hermitianUnitaryPath (A j) t).prod := by
  induction m with
  | zero => simp [hermitianUnitaryPath]
  | succ m ih =>
    have h0 : Commute (A 0) (∑ j : Fin m, A j.succ) :=
      Commute.sum_right Finset.univ (fun j : Fin m ↦ A j.succ) (A 0)
        (fun j _ ↦ hc (Fin.succ_ne_zero j).symm)
    rw [Fin.sum_univ_succ, List.ofFn_succ, List.prod_cons,
      hermitianUnitaryPath_add_of_commute _ _ h0]
    rw [ih (fun j ↦ A j.succ) (fun j k h ↦ hc (by simpa using h))]

/-- The exponential path of an operator supported on a region stays in its supported
operator algebra. This supplies the block factors in Osborne, Figure 2. -/
theorem hermitianUnitaryPath_mem_supported
    {ι : Type*} [Fintype ι] [DecidableEq ι] (q : ℕ) [NeZero q] (S : Finset ι)
    {H : Matrix (ι → Fin q) (ι → Fin q) ℂ}
    (hH : H ∈ supportedOperators q (S : Set ι)) (t : ℝ) :
    hermitianUnitaryPath H t ∈ supportedOperators q (S : Set ι) := by
  apply mem_supportedOperators_of_forall_commute S
  intro B hB
  have hc := commute_of_mem_supportedOperators disjoint_compl_right hH hB
  exact ((hc.smul_left Complex.I).smul_left t).exp_left

variable {L q w : ℕ}

/-- The explicitly constructed block Hamiltonians commute pairwise.
Osborne, arXiv:quant-ph/0508031v2, Figure 2. -/
theorem commute_chainGridBlockHamiltonian (hw : 0 < w)
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hs : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) (h i)
      (interval L i.val (i.val + 2))) :
    Pairwise fun j k : Fin (L / w + 1) ↦
      Commute (chainGridBlockHamiltonian hw h j) (chainGridBlockHamiltonian hw h k) := by
  intro j k hjk
  have hdisj := pairwise_disjoint_chainGridBlock L w
    (show j.val ≠ k.val from fun heq ↦ hjk (Fin.ext heq))
  exact commute_of_mem_supportedOperators (Finset.disjoint_coe.mpr hdisj)
    (chainGridBlockHamiltonian_mem_supported hw h hs j)
    (chainGridBlockHamiltonian_mem_supported hw h hs k)

/-- The retained Hamiltonian has an exact product of its actual block evolutions.
The support layout and each factor are constructed from the original interaction terms.
Osborne, arXiv:quant-ph/0508031v2, Figures 1--2 and equation (3). -/
theorem hermitianUnitaryPath_chainGridRetained_eq_prod (hw : 0 < w)
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hs : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) (h i)
      (interval L i.val (i.val + 2))) (t : ℝ) :
    hermitianUnitaryPath (chainGridRetainedHamiltonian hw h) t =
      (List.ofFn fun j ↦ hermitianUnitaryPath (chainGridBlockHamiltonian hw h j) t).prod :=
  hermitianUnitaryPath_fin_sum_of_commute _ (commute_chainGridBlockHamiltonian hw h hs) t

/-- Every factor of the exact block evolution is supported on its own grid block.
Osborne, arXiv:quant-ph/0508031v2, Figure 2. -/
theorem chainGridBlockEvolution_mem_supported [NeZero q] (hw : 0 < w)
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hs : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) (h i)
      (interval L i.val (i.val + 2))) (j : Fin (L / w + 1)) (t : ℝ) :
    hermitianUnitaryPath (chainGridBlockHamiltonian hw h j) t ∈
      supportedOperators q (chainGridBlock L w j.val : Set (Fin L)) :=
  hermitianUnitaryPath_mem_supported q _ (chainGridBlockHamiltonian_mem_supported hw h hs j) t

end TNLean.MPS.AreaLaw
