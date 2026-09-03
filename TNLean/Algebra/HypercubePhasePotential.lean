/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.ZMod.Basic
import TNLean.Algebra.GeneralizeDecide

/-!
# Phase potentials on the hypercube

The hypercube $\mathbb F_2^r$ is connected by the coordinate flips
$\gamma\mapsto\gamma+e_j$. A family of phases $\varphi_j(\gamma)$ attached to
the edges $(\gamma,\gamma+e_j)$ is *flat* when it is involutive along every
edge and commutes around every square:

$\varphi_j(\gamma)\varphi_j(\gamma+e_j)=1$,
$\varphi_j(\gamma)\varphi_k(\gamma+e_j)=\varphi_k(\gamma)\varphi_j(\gamma+e_k)$.

Flat phases have a potential: a function $\Phi$ with $\Phi(0)=1$ and
$\Phi(\gamma+e_j)=\varphi_j(\gamma)\Phi(\gamma)$ for every edge. This is the
path-independence statement behind the monomial fixed-space criterion in the
gauge-invariant subspace count for the CZX circuit tuple.

## Main results

* `TNLean.Algebra.hypercube_induction`: a predicate holding at the origin and
  stable under coordinate flips holds on the whole hypercube.
* `TNLean.Algebra.exists_potential_of_flat`: flat phases with values in a
  commutative group have a potential.
-/

namespace TNLean.Algebra

open Finset Matrix

/-- A predicate on the hypercube $\mathbb F_2^r$ that holds at the origin and is
stable under every coordinate flip holds everywhere. -/
theorem hypercube_induction {r : ℕ} {P : (Fin r → ZMod 2) → Prop} (h0 : P 0)
    (hstep : ∀ (j : Fin r) (γ : Fin r → ZMod 2), P γ → P (γ + Pi.single j 1))
    (γ : Fin r → ZMod 2) : P γ := by
  have key : ∀ S : Finset (Fin r), P (∑ j ∈ S, Pi.single j 1) := by
    intro S
    induction S using Finset.induction_on with
    | empty => simpa using h0
    | insert j S hj ih =>
      rw [Finset.sum_insert hj, add_comm]
      exact hstep j _ ih
  have hγ : γ = ∑ j ∈ Finset.univ.filter (fun j ↦ γ j = 1), Pi.single j 1 := by
    funext k
    rw [Finset.sum_apply]
    simp only [Pi.single_apply]
    rw [Finset.sum_ite_eq]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    generalize_decide γ k
  rw [hγ]
  exact key _

/-- Adding the first coordinate flip to a vector with prescribed first coordinate. -/
theorem vecCons_add_single_zero {r : ℕ} (a : ZMod 2) (γ : Fin r → ZMod 2) :
    vecCons a γ + Pi.single (0 : Fin (r + 1)) 1 = vecCons (a + 1) γ := by
  ext i
  refine Fin.cases ?_ ?_ i
  · simp
  · intro m
    simp [Fin.succ_ne_zero]

/-- Adding a later coordinate flip to a vector with prescribed first coordinate. -/
theorem vecCons_add_single_succ {r : ℕ} (a : ZMod 2) (γ : Fin r → ZMod 2) (k : Fin r) :
    vecCons a γ + Pi.single k.succ 1 = vecCons a (γ + Pi.single k 1) := by
  ext i
  refine Fin.cases ?_ ?_ i
  · simp [(Fin.succ_ne_zero k).symm]
  · intro m
    simp [Pi.single_apply, Fin.succ_inj]

/-- Every element of `ZMod 2` is zero or one. -/
theorem zmod_two_eq_zero_or_one (a : ZMod 2) : a = 0 ∨ a = 1 := by
  revert a
  decide

/-- **Flat phases have a potential.** If a family of edge phases on the hypercube
$\mathbb F_2^r$ is involutive along every edge and commutes around every square,
then there is a function $\Phi$ with $\Phi(0)=1$ and
$\Phi(\gamma+e_j)=\varphi_j(\gamma)\Phi(\gamma)$ for every $j$ and $\gamma$. -/
theorem exists_potential_of_flat {M : Type*} [CommGroup M] :
    ∀ (r : ℕ) (φ : Fin r → (Fin r → ZMod 2) → M),
      (∀ (j : Fin r) (γ : Fin r → ZMod 2), φ j γ * φ j (γ + Pi.single j 1) = 1) →
      (∀ (j k : Fin r) (γ : Fin r → ZMod 2),
        φ j γ * φ k (γ + Pi.single j 1) = φ k γ * φ j (γ + Pi.single k 1)) →
      ∃ Φ : (Fin r → ZMod 2) → M, Φ 0 = 1 ∧
        ∀ (j : Fin r) (γ : Fin r → ZMod 2), Φ (γ + Pi.single j 1) = φ j γ * Φ γ := by
  intro r
  induction r with
  | zero =>
    intro φ _ _
    exact ⟨fun _ ↦ 1, rfl, fun j ↦ j.elim0⟩
  | succ r ih =>
    intro φ hinv hflat
    obtain ⟨Φ', hΦ'0, hΦ'⟩ := ih (fun j γ' ↦ φ j.succ (vecCons 0 γ'))
      (fun j γ' ↦ by simpa [vecCons_add_single_succ] using hinv j.succ (vecCons 0 γ'))
      (fun j k γ' ↦ by
        simpa [vecCons_add_single_succ] using hflat j.succ k.succ (vecCons 0 γ'))
    refine ⟨fun γ ↦ (if γ 0 = 0 then 1 else φ 0 (vecCons 0 (vecTail γ))) * Φ' (vecTail γ),
      ?_, ?_⟩
    · have h0 : vecTail (0 : Fin (r + 1) → ZMod 2) = 0 := rfl
      simp [h0, hΦ'0]
    · intro j γ
      dsimp only
      rw [← cons_head_tail γ]
      generalize vecHead γ = a
      generalize vecTail γ = γ'
      refine Fin.cases ?_ ?_ j
      · rw [vecCons_add_single_zero]
        rcases zmod_two_eq_zero_or_one a with rfl | rfl
        · simp
        · have h := hinv 0 (vecCons 0 γ')
          rw [vecCons_add_single_zero, zero_add] at h
          simp only [cons_val_zero, tail_cons, one_ne_zero, ↓reduceIte, one_mul,
            show (1 : ZMod 2) + 1 = 0 by decide]
          rw [← mul_assoc, mul_comm (φ 0 (vecCons 1 γ')), h, one_mul]
      · intro k
        rw [vecCons_add_single_succ]
        simp only [cons_val_zero, tail_cons]
        rw [hΦ' k γ']
        rcases zmod_two_eq_zero_or_one a with rfl | rfl
        · simp
        · have h := hflat k.succ 0 (vecCons 0 γ')
          rw [vecCons_add_single_succ, vecCons_add_single_zero, zero_add] at h
          simp only [one_ne_zero, ↓reduceIte]
          calc φ 0 (vecCons 0 (γ' + Pi.single k 1)) * (φ k.succ (vecCons 0 γ') * Φ' γ')
              = (φ k.succ (vecCons 0 γ') * φ 0 (vecCons 0 (γ' + Pi.single k 1))) * Φ' γ' := by
                rw [← mul_assoc, mul_comm (φ 0 _)]
            _ = (φ 0 (vecCons 0 γ') * φ k.succ (vecCons 1 γ')) * Φ' γ' := by rw [h]
            _ = φ k.succ (vecCons 1 γ') * (φ 0 (vecCons 0 γ') * Φ' γ') := by
                rw [mul_comm (φ 0 _), mul_assoc]

end TNLean.Algebra
