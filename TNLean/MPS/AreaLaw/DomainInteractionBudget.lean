/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ComponentReduction
import TNLean.MPS.AreaLaw.InteractionBudget
import TNLean.MPS.AreaLaw.BoundaryCounting

/-!
# Interaction budgets on finite integer domains

An admissible support in a finite induced integer domain is also an admissible
support in the chain of its increasing labels. Restricting the existing chain
estimates gives the same per-site interaction budget and a crossing count linear
in the number of domain sites. These statements include the empty domain.

Source: TNLean one-dimensional note, `part0_preamble.tex`, eq:ham, lines 191–201,
and `part2a_mps_information.tex`, lines 260–265 and 355–363.
-/

open scoped Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw

variable {Λ : Finset ℤ} {q R : ℕ} {J : ℝ}

/-- Regard an admissible domain support as a chain support on the same labelled
sites. Source: TNLean note, part0_preamble.tex, eq:ham, lines 191–201. -/
def DomainSupport.toChainSupport (X : DomainSupport Λ R) : ChainSupport Λ.card R :=
  ⟨X.1, X.2.isChainSupport⟩

/-- Increasing labels do not identify distinct interaction supports.
Source: TNLean note, part0_preamble.tex, eq:ham, lines 191–201. -/
theorem DomainSupport.toChainSupport_injective :
    Function.Injective (DomainSupport.toChainSupport (Λ := Λ) (R := R)) := by
  exact fun X Y h ↦ Subtype.ext (congrArg (fun Z : ChainSupport Λ.card R ↦ Z.1) h)

/-- Zero extension preserves the interaction at each original domain support.
Source: TNLean note, `part0_preamble.tex`, eq:ham, lines 191–201. -/
@[simp] lemma DomainHamiltonian.toChain_term (h : DomainHamiltonian Λ q R J)
    (hJ : 0 ≤ J) (X : DomainSupport Λ R) :
    (h.toChain hJ).term X.toChainSupport = h.term X := by
  simp [DomainHamiltonian.toChain, DomainSupport.toChainSupport, X.2]

/-- A single domain site is an admissible support at every range.
Source: TNLean note, part0_preamble.tex, eq:ham, lines 191–201. -/
lemma IsDomainSupport.singleton (x : Fin Λ.card) : IsDomainSupport Λ R {x} := by
  simp [IsDomainSupport]

/-- The interaction bound is nonnegative at every actual domain site.
Source: TNLean note, part0_preamble.tex, eq:ham, lines 191–201. -/
lemma DomainHamiltonian.norm_bound_nonneg (h : DomainHamiltonian Λ q R J)
    (x : Fin Λ.card) : 0 ≤ J := by
  exact (norm_nonneg (h.term ⟨{x}, IsDomainSupport.singleton x⟩)).trans (h.norm_le _)

/-- The original domain interactions satisfy the chain per-site norm budget.
No sign or nonempty-domain hypothesis is added.
Source: TNLean note, part2a_mps_information.tex, lines 260–265. -/
lemma DomainHamiltonian.sum_norm_terms_containing_le (h : DomainHamiltonian Λ q R J)
    (x : Fin Λ.card) :
    (∑ X ∈ Finset.univ.filter (fun X : DomainSupport Λ R ↦ x ∈ X.1),
      ‖h.term X‖) ≤ ((2 ^ (2 * R + 1) : ℕ) : ℝ) * J := by
  refine (Finset.sum_le_sum_of_injOn
    (g := fun Y : ChainSupport Λ.card R ↦ ‖(h.toChain (h.norm_bound_nonneg x)).term Y‖)
    DomainSupport.toChainSupport DomainSupport.toChainSupport_injective.injOn
    ?_ ?_ (fun _ _ _ ↦ norm_nonneg _)).trans
      ((h.toChain (h.norm_bound_nonneg x)).sum_norm_terms_containing_le x)
  · exact fun Y hY ↦ (Finset.mem_image.mp hY).elim fun X hX ↦
      hX.2 ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hX.1).2⟩
  · exact fun X _ ↦ le_of_eq (congrArg norm (h.toChain_term (h.norm_bound_nonneg x) X).symm)

/-- The original domain crossing supports inject into the chain crossing supports.
The chain boundary is used only as an upper counting bound.
Source: TNLean note, part1_arealaw.tex, eq:count, and
part2a_mps_information.tex, lines 355–363. -/
lemma card_domain_crossingTerms_le_mul_card_boundaryEdges (Λ : Finset ℤ) (R : ℕ)
    (D : Finset (Fin Λ.card)) :
    (Entropy.crossingTerms (fun X : DomainSupport Λ R ↦ X.1) D).card ≤
      2 ^ (2 * R) * (boundaryEdges Λ.card D).card := by
  refine (Finset.card_le_card_of_injOn
    DomainSupport.toChainSupport ?_
    DomainSupport.toChainSupport_injective.injOn).trans
      (card_crossingTerms_le_mul_card_boundaryEdges Λ.card R D)
  exact fun X hX ↦ by
    simpa only [Entropy.crossingTerms, Finset.mem_coe, Finset.mem_filter,
      Finset.mem_univ, true_and, DomainSupport.toChainSupport] using hX

/-- Counting both replicas of the actual crossing supports gives a bound linear
in the number of domain sites, with the same range constant as on a chain.
Source: TNLean note, part2a_mps_information.tex, lines 355–363. -/
lemma card_domain_crossingTerms_mul_two_le (Λ : Finset ℤ) (R : ℕ)
    (D : Finset (Fin Λ.card)) :
    (Entropy.crossingTerms (fun X : DomainSupport Λ R ↦ X.1) D).card * 2 ≤
      chainCrossConst R * Λ.card := by
  have hb : (boundaryEdges Λ.card D).card ≤ Λ.card :=
    (Finset.card_filter_le _ _).trans
      ((Finset.card_range (Λ.card - 1)).le.trans (Nat.sub_le _ _))
  simpa only [chainCrossConst, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
    Nat.mul_le_mul_right 2
      ((card_domain_crossingTerms_le_mul_card_boundaryEdges Λ R D).trans
        (Nat.mul_le_mul_left (2 ^ (2 * R)) hb))

end TNLean.MPS.AreaLaw
