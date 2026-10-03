/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Algebra.Group.Commute.Hom
import Mathlib.Algebra.Group.Action.Prod
import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.Data.Fintype.Quotient
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Pair-conjugacy classes of virtual closures

Two pairs of group elements are pair-conjugate when one simultaneous conjugation
takes one pair to the other. The pair-conjugacy classes of commuting pairs are the
indices of the torus ground states in Schuch, Cirac, Pérez-García 2010,
arXiv:1001.3807, Definition 5.8 and Theorem 5.9 (`def:2d:pair-cc`,
`thm:2d:gs-struct`, lines 1560–1621 of `Papers/1001.3807/paper_v3.tex`).

The equivalence relation is Mathlib's orbit relation for the diagonal conjugation
action. Commutation is constant on each orbit. For an abelian group, every orbit
is a singleton, so the number of commuting pair-conjugacy classes is `|G|²`.
These assertions concern the group elements labelling closures; they do not assert
the ground-space theorem.

## References

- [arXiv:1001.3807](https://arxiv.org/abs/1001.3807) -- N. Schuch, J. I. Cirac,
  D. Pérez-García, *PEPS as ground states: degeneracy and topology*
-/

namespace TNLean.PEPS

variable (G : Type*) [Group G]

/-- Simultaneous conjugacy classes of pairs, as in arXiv:1001.3807,
Definition 5.8 (`def:2d:pair-cc`). -/
abbrev PairConjugacyClass := MulAction.orbitRel.Quotient (ConjAct G) (G × G)

/-- The pair-conjugacy class of a virtual closure `(g,h)`. -/
def pairConjugacyClass (p : G × G) : PairConjugacyClass G :=
  Quotient.mk (MulAction.orbitRel (ConjAct G) (G × G)) p

variable {G}

/-- The orbit relation is precisely the simultaneous conjugation in
arXiv:1001.3807, Definition 5.8 (`def:2d:pair-cc`). -/
theorem pairConjugacyClass_eq_iff (p q : G × G) :
    pairConjugacyClass G p = pairConjugacyClass G q ↔
      ∃ x : G, p.1 = x * q.1 * x⁻¹ ∧ p.2 = x * q.2 * x⁻¹ := by
  rw [pairConjugacyClass, pairConjugacyClass, Quotient.eq,
    MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  simp only [eq_comm, Prod.ext_iff, Prod.smul_fst, ConjAct.smul_def, Prod.smul_snd]
  exact ConjAct.ofConjAct.exists_congr_left

/-- The commuting pairs form a union of whole pair-conjugacy classes, as in
arXiv:1001.3807, Theorem 5.9 (`thm:2d:gs-struct`). -/
theorem commute_iff_of_pairConjugacyClass_eq {p q : G × G}
    (hpq : pairConjugacyClass G p = pairConjugacyClass G q) :
    Commute p.1 p.2 ↔ Commute q.1 q.2 := by
  obtain ⟨x, h₁, h₂⟩ := (pairConjugacyClass_eq_iff p q).mp hpq
  rw [h₁, h₂]
  exact commute_map_iff (MulAut.conj x).injective

namespace PairConjugacyClass

/-- A pair-conjugacy class is commuting when its representatives commute.
Source: arXiv:1001.3807, Theorem 5.9 (`thm:2d:gs-struct`). -/
def IsCommuting (C : PairConjugacyClass G) : Prop :=
  Quotient.lift (fun p : G × G ↦ Commute p.1 p.2)
    (fun _ _ h ↦ propext (commute_iff_of_pairConjugacyClass_eq (Quotient.sound h))) C

@[simp]
theorem isCommuting_pairConjugacyClass (p : G × G) :
    (pairConjugacyClass G p).IsCommuting ↔ Commute p.1 p.2 := Iff.rfl

end PairConjugacyClass

variable (G)

/-- The commuting pair-conjugacy classes indexing the torus closures in
arXiv:1001.3807, Theorem 5.9 (`thm:2d:gs-struct`). -/
abbrev CommutingPairConjugacyClass := {C : PairConjugacyClass G // C.IsCommuting}

variable {G}

/-- Once the first element is fixed, simultaneous conjugacy is conjugacy of the
second element by the centralizer of the first. This is the group-theoretic
classification following Theorem 5.9 in arXiv:1001.3807, lines 1613–1621. -/
theorem pairConjugacyClass_eq_iff_centralizer (g h k : G) :
    pairConjugacyClass G (g, h) = pairConjugacyClass G (g, k) ↔
      ∃ x : Subgroup.centralizer ({g} : Set G), h = (x : G) * k * (x : G)⁻¹ := by
  rw [pairConjugacyClass_eq_iff]
  simp [Subtype.exists, Subgroup.mem_centralizer_singleton_iff, eq_mul_inv_iff_mul_eq,
    eq_comm]

section Abelian

variable {A : Type*} [CommGroup A]

/-- Simultaneous conjugation is trivial for an abelian group. -/
theorem pairConjugacyClass_eq_iff_of_commGroup (p q : A × A) :
    pairConjugacyClass A p = pairConjugacyClass A q ↔ p = q := by
  rw [pairConjugacyClass_eq_iff]
  simp [Prod.ext_iff]

/-- For an abelian group, pair-conjugacy classes are individual pairs.
This describes the closure labels in arXiv:1001.3807, Definition 5.8. -/
def pairConjugacyClassEquivOfCommGroup : PairConjugacyClass A ≃ A × A where
  toFun := Quotient.lift id fun p q h ↦
    (pairConjugacyClass_eq_iff_of_commGroup p q).mp (Quotient.sound h)
  invFun := pairConjugacyClass A
  left_inv C := Quotient.inductionOn C fun _ ↦ rfl
  right_inv _ := rfl

/-- For an abelian group all pairs commute, so the torus closure labels are
exactly the pairs of group elements. -/
def commutingPairConjugacyClassEquivOfCommGroup : CommutingPairConjugacyClass A ≃ A × A where
  toFun C := pairConjugacyClassEquivOfCommGroup C.1
  invFun p := ⟨pairConjugacyClass A p, mul_comm p.1 p.2⟩
  left_inv C := by
    apply Subtype.ext
    exact pairConjugacyClassEquivOfCommGroup.symm_apply_apply C.1
  right_inv _ := rfl

/-- A finite abelian group has `|G|²` commuting pair-conjugacy classes. This
counts closure labels, independently of the ground-space theorem. -/
theorem card_commutingPairConjugacyClass_of_commGroup [Finite A] :
    Nat.card (CommutingPairConjugacyClass A) = Nat.card A ^ 2 := by
  rw [Nat.card_congr commutingPairConjugacyClassEquivOfCommGroup, Nat.card_prod, pow_two]

end Abelian

end TNLean.PEPS
