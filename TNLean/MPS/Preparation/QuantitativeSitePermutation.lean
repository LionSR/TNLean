/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.BlockUnitary
import TNLean.MPS.Preparation.CleanImplementationPlacement
import Mathlib.GroupTheory.Perm.Sign

/-!
# Additive routing cost for site permutations

A permutation of `n` sites is a product of at most `n` swaps. Routing each
swap gives at most `2 * n ^ 2` neighboring-pair gates. Conjugation therefore
adds at most `4 * n ^ 2` gates to an existing circuit, independently of its
length. Permuting logical sites while fixing the appended workspace also
preserves the clean implementation identity on every logical input.

Source: register regrouping in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`; the factorization is
Mathlib's `Equiv.Perm.swapFactors`.
-/

open Matrix MPSTensor

namespace Equiv.Perm

variable {α : Type*} [DecidableEq α]

/-- The swap-factor algorithm uses at most one swap per listed site. Source:
Mathlib's `swapFactorsAux`, used for register routing in Section 5 of the
circuit audit. -/
theorem swapFactorsAux_length_le (l : List α) (τ : Perm α)
    (h : ∀ {x}, τ x ≠ x → x ∈ l) :
    (swapFactorsAux l τ h).val.length ≤ l.length := by
  induction l generalizing τ with
  | nil => simp [swapFactorsAux]
  | cons x l ih =>
    rw [swapFactorsAux]
    dsimp only
    split_ifs with hfx
    · have htail : ∀ {y}, τ y ≠ y → y ∈ l := by
        intro y hy
        refine List.mem_of_ne_of_mem ?_ (h hy)
        intro hyx
        subst y
        exact hy hfx.symm
      exact (ih τ htail).trans (Nat.le_succ _)
    · have htail : ∀ {y}, (swap x (τ x) * τ) y ≠ y → y ∈ l := by
        intro y hy
        have hne := ne_and_ne_of_swap_mul_apply_ne_self hy
        exact List.mem_of_ne_of_mem hne.2 (h hne.1)
      exact Nat.succ_le_succ (ih (swap x (τ x) * τ) htail)

/-- The concrete swap factorization has at most one factor per site. Source:
Mathlib's `swapFactors`, used for register routing in Section 5 of the audit. -/
theorem swapFactors_length_le_card [Fintype α] [LinearOrder α] (τ : Perm α) :
    (swapFactors τ).val.length ≤ Fintype.card α := by
  unfold swapFactors
  exact (swapFactorsAux_length_le (Finset.univ.sort) τ
    (fun {_ _} ↦ (Finset.mem_sort _).2 (Finset.mem_univ _))).trans (by
      simpa only [Finset.card_univ] using
        (Finset.length_sort (s := (Finset.univ : Finset α)) (· ≤ ·)).le)

end Equiv.Perm

namespace MPSPreparation

variable {d n a K : ℕ}

/-- Site permutation operators preserve products exactly, with no scalar
phase discarded. Source: swap routing in Section 5 of the circuit audit. -/
theorem permOp_list_prod (l : List (Equiv.Perm (Fin n))) :
    permOp (d := d) l.prod = (l.map (permOp (d := d))).prod := by
  induction l with
  | nil => simp
  | cons τ l ih => simp only [List.prod_cons, permOp_mul, List.map_cons, ih]

/-- Every actual site permutation has an additive quadratic routing bound.
No swap factorization or circuit witness is supplied. Source: logical
register regrouping in Section 5 of the circuit audit. -/
theorem isPairProduct_permOp (τ : Equiv.Perm (Fin n)) :
    IsPairProduct d n (2 * n ^ 2) (permOp τ) := by
  let l := (Equiv.Perm.swapFactors τ).val
  have hprod : l.prod = τ := (Equiv.Perm.swapFactors τ).property.1
  have hswap : ∀ σ ∈ l, Equiv.Perm.IsSwap σ := (Equiv.Perm.swapFactors τ).property.2
  have hlength : l.length ≤ n := by
    simpa only [Fintype.card_fin] using Equiv.Perm.swapFactors_length_le_card τ
  rw [← hprod, permOp_list_prod]
  apply IsPairProduct.mono (K := (l.map (permOp (d := d))).length * (2 * n))
  · simp only [List.length_map]
    calc
      l.length * (2 * n) ≤ n * (2 * n) := Nat.mul_le_mul_right _ hlength
      _ = 2 * n ^ 2 := by ring
  · apply IsPairProduct.list_prod
    intro X hX
    obtain ⟨σ, hσ, rfl⟩ := List.mem_map.mp hX
    obtain ⟨i, j, _, rfl⟩ := hswap σ hσ
    exact isPairProduct_permOp_swap i j

/-- Conjugating by a site permutation adds its forward and inverse routing
cost instead of multiplying the original gate count. Source: register
regrouping in Section 5 of the circuit audit. -/
theorem IsPairProduct.conjugate_permOp (τ : Equiv.Perm (Fin n))
    {U : Matrix (Cfg d n) (Cfg d n) ℂ} (hU : IsPairProduct d n K U) :
    IsPairProduct d n (K + 4 * n ^ 2) (permOp τ * U * (permOp τ)ᴴ) := by
  have hτ := isPairProduct_permOp (d := d) τ
  simpa only [Matrix.star_eq_conjTranspose,
    show 2 * n ^ 2 + K + 2 * n ^ 2 = K + 4 * n ^ 2 by omega] using
      (hτ.mul hU).mul hτ.star

/-- Extend a logical site permutation by the identity on appended workspace.
Source: common-pool register regrouping in Section 5 of the circuit audit. -/
def workspaceFixedSitePerm (τ : Equiv.Perm (Fin n)) : Equiv.Perm (Fin (n + a)) :=
  (finSumFinEquiv.symm.trans (Equiv.sumCongr τ (Equiv.refl (Fin a)))).trans finSumFinEquiv

/-- Logical sites follow the prescribed permutation. Source: register
regrouping in Section 5 of the circuit audit. -/
@[simp] theorem workspaceFixedSitePerm_castAdd (τ : Equiv.Perm (Fin n)) (i : Fin n) :
    workspaceFixedSitePerm (a := a) τ (Fin.castAdd a i) = Fin.castAdd a (τ i) := by
  simp [workspaceFixedSitePerm]

/-- Appended workspace sites are fixed. Source: reusable workspace in
Section 5 of the circuit audit. -/
@[simp] theorem workspaceFixedSitePerm_natAdd (τ : Equiv.Perm (Fin n)) (i : Fin a) :
    workspaceFixedSitePerm (a := a) τ (Fin.natAdd n i) = Fin.natAdd n i := by
  simp [workspaceFixedSitePerm]

variable [NeZero d]

/-- Logical routing preserves the full initialized logical space and fixes
workspace on every logical input. Source: common-pool routing in Section 5
of the circuit audit. -/
theorem isCleanImplementation_permOp_workspaceFixedSitePerm (τ : Equiv.Perm (Fin n)) :
    IsCleanImplementation
      (initializedBasisMatrix (zeroWorkspaceEmbedding (d := d) (n := n) (a := a)))
      (permOp (workspaceFixedSitePerm (a := a) τ)) (permOp τ) := by
  classical
  change permOp (workspaceFixedSitePerm (a := a) τ) *
    initializedBasisMatrix (zeroWorkspaceEmbedding (d := d) (n := n) (a := a)) = _
  rw [mul_initializedBasisMatrix]
  ext z x
  rw [initializedBasisMatrix_zeroWorkspace_mul_apply]
  change (if Fin.append x 0 = z ∘ workspaceFixedSitePerm (a := a) τ then (1 : ℂ) else 0) =
    if ∀ i, z (Fin.natAdd n i) = 0 then
      (if x = (fun j ↦ z (Fin.castAdd a j)) ∘ τ then 1 else 0) else 0
  have hcfg : Fin.append x (0 : Cfg d a) = z ∘ workspaceFixedSitePerm (a := a) τ ↔
      (∀ i, z (Fin.natAdd n i) = 0) ∧
        x = (fun j ↦ z (Fin.castAdd a j)) ∘ τ := by
    constructor
    · intro h
      constructor
      · intro i
        have hi := congrFun h (Fin.natAdd n i)
        simpa only [Fin.append_right, Pi.zero_apply, Function.comp_apply,
          workspaceFixedSitePerm_natAdd] using hi.symm
      · funext i
        have hi := congrFun h (Fin.castAdd a i)
        simpa only [Fin.append_left, Function.comp_apply,
          workspaceFixedSitePerm_castAdd] using hi
    · rintro ⟨hw, hx⟩
      funext i
      refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i
      · simpa only [Fin.append_left, Function.comp_apply,
          workspaceFixedSitePerm_castAdd] using congrFun hx j
      · simpa only [Fin.append_right, Pi.zero_apply, Function.comp_apply,
          workspaceFixedSitePerm_natAdd] using (hw j).symm
  simp only [hcfg, ite_and]

/-- Clean implementation is preserved by logical coordinate regrouping;
workspace remains fixed and the equality holds on every logical input.
Source: recursive common-pool routing in Section 5 of the circuit audit. -/
theorem IsCleanImplementation.conjugate_workspaceFixedSitePerm
    (τ : Equiv.Perm (Fin n))
    {U : Matrix (Cfg d (n + a)) (Cfg d (n + a)) ℂ}
    {Z : Matrix (Cfg d n) (Cfg d n) ℂ}
    (h : IsCleanImplementation
      (initializedBasisMatrix (zeroWorkspaceEmbedding (d := d) (n := n) (a := a))) U Z) :
    IsCleanImplementation
      (initializedBasisMatrix (zeroWorkspaceEmbedding (d := d) (n := n) (a := a)))
      (permOp (workspaceFixedSitePerm (a := a) τ) * U *
        (permOp (workspaceFixedSitePerm (a := a) τ))ᴴ)
      (permOp τ * Z * (permOp τ)ᴴ) := by
  have hp := isCleanImplementation_permOp_workspaceFixedSitePerm (d := d) (a := a) τ
  have hs := hp.conjTranspose (permOp_mem_unitary _) (permOp_mem_unitary _)
  exact (hp.mul h).mul hs

/-- The same actual regrouping has both an additive routing budget and the
clean all-input identity. No ambient cleanup witness is assumed. Source:
recursive register regrouping in Section 5 of the circuit audit. -/
theorem isPairProduct_isCleanImplementation_conjugate_workspaceFixedSitePerm
    (τ : Equiv.Perm (Fin n))
    {U : Matrix (Cfg d (n + a)) (Cfg d (n + a)) ℂ}
    {Z : Matrix (Cfg d n) (Cfg d n) ℂ}
    (hU : IsPairProduct d (n + a) K U)
    (hclean : IsCleanImplementation
      (initializedBasisMatrix (zeroWorkspaceEmbedding (d := d) (n := n) (a := a))) U Z) :
    IsPairProduct d (n + a) (K + 4 * (n + a) ^ 2)
        (permOp (workspaceFixedSitePerm (a := a) τ) * U *
          (permOp (workspaceFixedSitePerm (a := a) τ))ᴴ) ∧
      IsCleanImplementation
        (initializedBasisMatrix (zeroWorkspaceEmbedding (d := d) (n := n) (a := a)))
        (permOp (workspaceFixedSitePerm (a := a) τ) * U *
          (permOp (workspaceFixedSitePerm (a := a) τ))ᴴ)
        (permOp τ * Z * (permOp τ)ᴴ) :=
  ⟨hU.conjugate_permOp _, hclean.conjugate_workspaceFixedSitePerm τ⟩

end MPSPreparation
