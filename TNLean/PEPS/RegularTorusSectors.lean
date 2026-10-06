/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.RegularTorusSite
import TNLean.PEPS.TorusGClosure
import TNLean.PEPS.RegularTorusGram
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

/-!
# Independent regular isometric torus closure sectors

The actual torus PEPS vectors with different simultaneous conjugacy classes of closures
are orthogonal. The self-overlap counts the common centralizer of the two closures and
is nonzero. Consequently the class-indexed family, and in particular its commuting
subfamily, is linearly independent.

**Scope restriction (regular isometric sites):** independence of the commuting subfamily
is the regular `G`-isometric specialization of the independence statement in Schuch,
Cirac, and Pérez-García, arXiv:1001.3807, Theorem 5.9 (`Papers/1001.3807/paper_v3.tex`,
lines 1582–1621). Orthogonality and independence for all pair classes are auxiliary
refinements and extensions of that closure-vector argument. The isometry assumption
for regular virtual representations is removed in `TNLean.PEPS.RegularGInjectiveTorus`.
Independence for general semi-regular virtual representations is proved in
`TNLean.PEPS.GInjectiveTorusSectors`; identification with the parent-Hamiltonian ground
space remains separate. See
`docs/paper-gaps/rmp_peps_quantum_double_g_isometry.tex`.

Rectangular tori, including size-one dimensions, are algebraic extensions of the overlap
calculation. These statements do not extend the source's \(2\times2\) parent-Hamiltonian
construction to such dimensions.
-/

open scoped BigOperators Matrix
open Matrix

namespace TNLean.PEPS

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

private theorem closure_transporter_sum_eq_zero {g h g' h' : G}
    (hpq : pairConjugacyClass G (g, h) ≠ pairConjugacyClass G (g', h')) :
    (∑ x : G, if h * x = x * h' ∧ g * x = x * g' then (1 : ℂ) else 0) = 0 := by
  apply Finset.sum_eq_zero
  intro x _
  apply ite_eq_right
  intro hx
  apply hpq
  apply (pairConjugacyClass_eq_iff _ _).mpr
  exact ⟨x, (eq_mul_inv_iff_mul_eq).mpr hx.2, (eq_mul_inv_iff_mul_eq).mpr hx.1⟩

private theorem closure_transporter_self_sum (g h : G) :
    (∑ x : G, if h * x = x * h ∧ g * x = x * g then (1 : ℂ) else 0) =
      (Nat.card (Subgroup.centralizer ({g, h} : Set G)) : ℂ) := by
  classical
  have hm (x : G) : h * x = x * h ∧ g * x = x * g ↔
      x ∈ Subgroup.centralizer ({g, h} : Set G) := by
    simp only [Subgroup.mem_centralizer_iff, Set.mem_insert_iff, Set.mem_singleton_iff,
      forall_eq_or_imp, forall_eq, and_comm]
  simp only [hm, Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.sum_boole]

variable {width height : ℕ} [NeZero width] [NeZero height]
variable {Phys : Type*} [Fintype Phys]

/-- Distinct pair-conjugacy classes give orthogonal actual regular isometric torus
closure vectors. This refines the closure-vector argument of SCP10, Theorem 5.9. -/
theorem IsGIsometric.torusGClosure_dotProduct_eq_zero_of_pairConjugacyClass_ne
    {a : G → G → G → G → Phys → ℂ}
    (ha : IsGIsometric (torusLegRep (leftRegularMatrix G)) (siteMap a))
    {g h g' h' : G}
    (hpq : pairConjugacyClass G (g, h) ≠ pairConjugacyClass G (g', h')) :
    star (torusGClosure (width := width) (height := height) (leftRegularMatrix G) a g h) ⬝ᵥ
      torusGClosure (leftRegularMatrix G) a g' h' = 0 := by
  obtain ⟨c, _, hoverlap⟩ := ha.exists_torusGClosure_overlap (width := width) (height := height)
  simp only [dotProduct, Pi.star_apply]
  rw [hoverlap, closure_transporter_sum_eq_zero hpq, mul_zero]

/-- The squared norm of a regular isometric torus closure vector is its positive
site factor times the order of the common centralizer. -/
theorem IsGIsometric.exists_torusGClosure_dotProduct_self
    {a : G → G → G → G → Phys → ℂ}
    (ha : IsGIsometric (torusLegRep (leftRegularMatrix G)) (siteMap a)) :
    ∃ c : ℝ, 0 < c ∧ ∀ g h : G,
      star (torusGClosure (width := width) (height := height) (leftRegularMatrix G) a g h) ⬝ᵥ
        torusGClosure (leftRegularMatrix G) a g h =
          (c : ℂ) ^ Fintype.card (TorusVertex width height) *
            (Fintype.card G : ℂ) ^ Fintype.card (TorusVertex width height) *
              (Nat.card (Subgroup.centralizer ({g, h} : Set G)) : ℂ) := by
  obtain ⟨c, hc, hoverlap⟩ := ha.exists_torusGClosure_overlap (width := width) (height := height)
  refine ⟨c, hc, fun g h => ?_⟩
  simp only [dotProduct, Pi.star_apply]
  rw [hoverlap, closure_transporter_self_sum]

/-- Every closure vector of a regular isometric tensor has nonzero squared norm,
since the common centralizer contains the identity. -/
theorem IsGIsometric.torusGClosure_dotProduct_self_ne_zero
    {a : G → G → G → G → Phys → ℂ}
    (ha : IsGIsometric (torusLegRep (leftRegularMatrix G)) (siteMap a)) (g h : G) :
    star (torusGClosure (width := width) (height := height) (leftRegularMatrix G) a g h) ⬝ᵥ
      torusGClosure (leftRegularMatrix G) a g h ≠ 0 := by
  obtain ⟨c, hc, hnorm⟩ :=
    ha.exists_torusGClosure_dotProduct_self (width := width) (height := height)
  rw [hnorm]
  exact mul_ne_zero
    (mul_ne_zero (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr hc.ne'))
      (pow_ne_zero _ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)))
    (Nat.cast_ne_zero.mpr Nat.card_pos.ne')

/-- The actual regular isometric torus vector is nonzero for every closure pair,
including pairs that do not commute. No ground-space membership is asserted. -/
theorem IsGIsometric.torusGClosure_ne_zero
    {a : G → G → G → G → Phys → ℂ}
    (ha : IsGIsometric (torusLegRep (leftRegularMatrix G)) (siteMap a)) (g h : G) :
    torusGClosure (width := width) (height := height) (leftRegularMatrix G) a g h ≠ 0 := by
  intro hzero
  have hnorm := ha.torusGClosure_dotProduct_self_ne_zero (width := width) (height := height) g h
  exact hnorm (by rw [hzero, star_zero, zero_dotProduct])

/-- Distinct class-indexed actual torus vectors are orthogonal. -/
theorem IsGIsometric.torusGClosureClass_orthogonal
    {a : G → G → G → G → Phys → ℂ}
    (ha : IsGIsometric (torusLegRep (leftRegularMatrix G)) (siteMap a))
    {C D : PairConjugacyClass G} (hCD : C ≠ D) :
    star (torusGClosureClass (width := width) (height := height)
        (leftRegularMatrix G) a ha.invariant C) ⬝ᵥ
      torusGClosureClass (leftRegularMatrix G) a ha.invariant D = 0 := by
  revert hCD
  refine Quotient.inductionOn₂ C D (fun p q hpq => ?_)
  exact ha.torusGClosure_dotProduct_eq_zero_of_pairConjugacyClass_ne hpq

/-- The actual class-indexed torus closure vectors are linearly independent for
regular isometric sites. This extends the closure-vector argument of SCP10, Theorem 5.9,
to noncommuting pair classes. -/
theorem IsGIsometric.linearIndependent_torusGClosureClass
    {a : G → G → G → G → Phys → ℂ}
    (ha : IsGIsometric (torusLegRep (leftRegularMatrix G)) (siteMap a)) :
    LinearIndependent ℂ (torusGClosureClass (width := width) (height := height)
      (leftRegularMatrix G) a ha.invariant) := by
  let v := torusGClosureClass (width := width) (height := height)
    (leftRegularMatrix G) a ha.invariant
  have hnorm (C : PairConjugacyClass G) : star (v C) ⬝ᵥ v C ≠ 0 := by
    refine Quotient.inductionOn C (fun p => ?_)
    exact ha.torusGClosure_dotProduct_self_ne_zero p.1 p.2
  apply LinearIndependent.of_pairwise_dual_eq_zero_one v
    (fun C => (star (v C) ⬝ᵥ v C)⁻¹ • dotProductBilin ℂ ℂ (star (v C)))
  · intro C D hCD
    change (star (v C) ⬝ᵥ v C)⁻¹ * (star (v C) ⬝ᵥ v D) = 0
    rw [ha.torusGClosureClass_orthogonal hCD, mul_zero]
  · intro C
    change (star (v C) ⬝ᵥ v C)⁻¹ * (star (v C) ⬝ᵥ v C) = 1
    exact inv_mul_cancel₀ (hnorm C)

/-- Restricting to commuting classes gives the independent actual closure family indexed
by SCP10, Theorem 5.9, in the regular isometric case. -/
theorem IsGIsometric.linearIndependent_torusGClosureClass_commuting
    {a : G → G → G → G → Phys → ℂ}
    (ha : IsGIsometric (torusLegRep (leftRegularMatrix G)) (siteMap a)) :
    LinearIndependent ℂ (fun C : CommutingPairConjugacyClass G =>
      torusGClosureClass (width := width) (height := height)
        (leftRegularMatrix G) a ha.invariant C.1) :=
  ha.linearIndependent_torusGClosureClass.comp Subtype.val Subtype.val_injective

end TNLean.PEPS
