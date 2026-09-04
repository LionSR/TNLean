/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Kraus.NormalCommutant
import TNLean.MPS.Chain.OneSidedInverse

/-!
# Cross-product rigidity of a commuting family

Two families of square matrices $A$ and $B$ that satisfy the cross relation
$B_iA_j=A_iB_j$ for all pairs of physical indices describe a tensor that
commutes with the tensor of $A$ on a two-site chain.  When $A$ is normal the
cross relation forces $B$ to be a single scalar multiple of $A$.

The argument decomposes the identity in the span of the length-$N$ words of
$A$, where $N$ is a positive blocking length at which $A$ becomes injective.
Moving the marked letter of $B$ one step to the right through such a word
produces a matrix $C$ with $B_i=A_iC$, and the cross relation then makes $C$
commute with every letter of $A$; a matrix commuting with every letter of a
normal family is scalar.

## Main results

* `Kraus.IsNormal.eq_smul_of_cross_mul_eq` — cross-product rigidity for a
  normal family.
* `Kraus.IsInjective.eq_smul_of_cross_mul_eq` — the injective special case.

## References

* Cirac--Garre-Rubio--Pérez-García--Ruiz-de-Alarcón--Schuch, arXiv:2502.20257,
  the commuting-tensor step in the proof of Proposition `prop:MPUsplus`, lines
  1255--1325.
-/

open scoped Matrix BigOperators

namespace Kraus

variable {d D : ℕ}

/-- A nonempty word of a family annihilates on the right every matrix that is
annihilated on the right by each letter. -/
private theorem evalWord_mul_eq_zero_of_ne_nil
    {A : Fin d → Matrix (Fin D) (Fin D) ℂ} {X : Matrix (Fin D) (Fin D) ℂ}
    (hX : ∀ i, A i * X = 0) :
    ∀ w : List (Fin d), w ≠ [] → Kraus.evalWord A w * X = 0 := by
  intro w
  induction w with
  | nil => exact fun h => absurd rfl h
  | cons i w ih =>
      cases w with
      | nil => intro _; simpa using hX i
      | cons j t =>
          intro _
          rw [Kraus.evalWord_cons, Matrix.mul_assoc, ih (List.cons_ne_nil j t),
            Matrix.mul_zero]

/-- **Cross-product rigidity for a normal family.** If $B_iA_j=A_iB_j$ holds
for all physical indices and the family $A$ is normal, then $B$ is a single
scalar multiple of $A$.

This is the step "the tensor labeled $s$ commutes with the MPU tensor
$\mathcal U$. Because $\mathcal U$ is normal, this implies that there exists
$\delta\in\mathbb C$ such that ..." in the proof of Proposition `prop:MPUsplus`
of arXiv:2502.20257, lines 1255--1325.  The paper first treats an injective
$\mathcal U$ and then, when $\mathcal U$ is not injective, replaces the middle
tensor by enough copies for their blocking to be injective; the proof below
runs the blocked argument directly, so the injective case is the special case
of blocking length one. -/
theorem IsNormal.eq_smul_of_cross_mul_eq
    {A B : Fin d → Matrix (Fin D) (Fin D) ℂ} (hA : Kraus.IsNormal A)
    (hcross : ∀ i j, B i * A j = A i * B j) :
    ∃ c : ℂ, ∀ i, B i = c • A i := by
  obtain ⟨N, hNpos, hN⟩ := (Kraus.isNormal_iff A).mp hA
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, (Nat.succ_pred_eq_of_pos hNpos).symm⟩
  -- Decompose the identity in the span of the length-`M + 1` words of `A`.
  obtain ⟨c, hone⟩ : ∃ c : (Fin (M + 1) → Fin d) → ℂ,
      ∑ σ : Fin (M + 1) → Fin d, c σ • Kraus.evalWord A (List.ofFn σ) = 1 :=
    ⟨Kraus.blockDecompositionMap hN 1, Kraus.blockDecompositionMap_sum hN 1⟩
  -- Moving the marked letter of `B` one step to the right through a word of `A`.
  have hmove : ∀ (i : Fin d) (σ : Fin (M + 1) → Fin d),
      B i * Kraus.evalWord A (List.ofFn σ) =
        A i * (B (σ 0) * Kraus.evalWord A (List.ofFn fun k : Fin M => σ k.succ)) := by
    intro i σ
    rw [List.ofFn_succ, Kraus.evalWord_cons, ← Matrix.mul_assoc, hcross, Matrix.mul_assoc]
  obtain ⟨C, hBC⟩ : ∃ C : Matrix (Fin D) (Fin D) ℂ, ∀ i, B i = A i * C := by
    refine ⟨∑ σ : Fin (M + 1) → Fin d,
      c σ • (B (σ 0) * Kraus.evalWord A (List.ofFn fun k : Fin M => σ k.succ)), fun i => ?_⟩
    calc
      B i = B i * ∑ σ : Fin (M + 1) → Fin d, c σ • Kraus.evalWord A (List.ofFn σ) := by
            rw [hone, Matrix.mul_one]
      _ = ∑ σ : Fin (M + 1) → Fin d,
            c σ • (A i * (B (σ 0) *
              Kraus.evalWord A (List.ofFn fun k : Fin M => σ k.succ))) := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun σ _ => by rw [mul_smul_comm, hmove i σ]
      _ = A i * ∑ σ : Fin (M + 1) → Fin d,
            c σ • (B (σ 0) *
              Kraus.evalWord A (List.ofFn fun k : Fin M => σ k.succ)) := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun σ _ => (mul_smul_comm _ _ _).symm
  -- The cross relation makes `C` commute with every letter of `A`.
  have hcomm : ∀ j, C * A j = A j * C := by
    intro j
    have hzero : ∀ i, A i * (C * A j - A j * C) = 0 := by
      intro i
      have h := hcross i j
      rw [hBC i, hBC j] at h
      rw [Matrix.mul_sub, ← Matrix.mul_assoc, h, sub_self]
    have hsum : (1 : Matrix (Fin D) (Fin D) ℂ) * (C * A j - A j * C) = 0 := by
      rw [← hone, Finset.sum_mul]
      refine Finset.sum_eq_zero fun σ _ => ?_
      rw [smul_mul_assoc,
        evalWord_mul_eq_zero_of_ne_nil hzero _
          (by rw [List.ofFn_succ]; exact List.cons_ne_nil _ _),
        smul_zero]
    rw [Matrix.one_mul, sub_eq_zero] at hsum
    exact hsum
  obtain ⟨z, hz⟩ := hA.eq_smul_one_of_commute hcomm
  exact ⟨z, fun i => by rw [hBC i, hz, mul_smul_comm, Matrix.mul_one]⟩

/-- **Cross-product rigidity for an injective family.** If $B_iA_j=A_iB_j$
holds for all physical indices and the family $A$ is injective, then $B$ is a
single scalar multiple of $A$.

This is the injective case treated first in the proof of Proposition
`prop:MPUsplus` of arXiv:2502.20257, lines 1255--1325. -/
theorem IsInjective.eq_smul_of_cross_mul_eq
    {A B : Fin d → Matrix (Fin D) (Fin D) ℂ} (hA : Kraus.IsInjective A)
    (hcross : ∀ i j, B i * A j = A i * B j) :
    ∃ c : ℂ, ∀ i, B i = c • A i :=
  hA.isNormal.eq_smul_of_cross_mul_eq hcross

end Kraus
