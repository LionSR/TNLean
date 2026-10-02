/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.PairConjugacy
import Mathlib.Algebra.Group.ConjFinite
import Mathlib.Logic.Equiv.Sum
import Mathlib.Data.Fintype.Sigma

/-!
# Centralizer conjugacy classes and commuting torus closures

A simultaneous-conjugacy class of a commuting pair is specified by the
conjugacy class of its first element and a conjugacy class in the centralizer
of a representative of that class. Consequently, the number of commuting
pair classes is the sum of the numbers of centralizer conjugacy classes.

Source: Schuch, Cirac, and Pérez-García, arXiv:1001.3807, the discussion
following Theorem 5.9, `Papers/1001.3807/paper_v3.tex`, lines 1613–1621.
The source calls the subgroup consisting of elements commuting with a fixed
element its normalizer; the subgroup in the displayed formula is its
centralizer. This module counts the closure labels. Identification with a
parent-Hamiltonian ground space requires the separate ground-space theorem.
-/

namespace TNLean.PEPS

noncomputable section

open scoped BigOperators

variable {G : Type*} [Group G]

/-- The first conjugacy class of a simultaneous-conjugacy class. Source:
SCP10, the discussion following Theorem 5.9, lines 1613–1621. -/
def PairConjugacyClass.firstConjClass (C : PairConjugacyClass G) : ConjClasses G :=
  Quotient.lift (fun p : G × G ↦ ConjClasses.mk p.1) (by
    intro p q hpq
    obtain ⟨x, hx, _⟩ := (pairConjugacyClass_eq_iff p q).mp (Quotient.sound hpq)
    apply ConjClasses.mk_eq_mk_iff_isConj.mpr
    exact (isConj_iff.mpr ⟨x, hx.symm⟩).symm) C

@[simp]
theorem PairConjugacyClass.firstConjClass_pairConjugacyClass (p : G × G) :
    (pairConjugacyClass G p).firstConjClass = ConjClasses.mk p.1 := rfl

private theorem pairConjugacyClass_centralizer_eq_iff (g : G)
    (h k : Subgroup.centralizer ({g} : Set G)) :
    pairConjugacyClass G (g, h) = pairConjugacyClass G (g, k) ↔
      ConjClasses.mk h = ConjClasses.mk k := by
  rw [pairConjugacyClass_eq_iff_centralizer, ConjClasses.mk_eq_mk_iff_isConj,
    isConj_comm, isConj_iff]
  simp only [Subtype.ext_iff, Subgroup.coe_mul, Subgroup.coe_inv, eq_comm]

/-- A centralizer conjugacy class determines a commuting pair class with first
conjugacy class prescribed. Source: SCP10, following Theorem 5.9, lines 1613–1621. -/
def centralizerConjClassToCommutingPair (g : G)
    (C : ConjClasses (Subgroup.centralizer ({g} : Set G))) :
    {C : CommutingPairConjugacyClass G // C.1.firstConjClass = ConjClasses.mk g} :=
  Quotient.lift (fun h : Subgroup.centralizer ({g} : Set G) ↦
    ⟨⟨pairConjugacyClass G (g, h), by
      rw [PairConjugacyClass.isCommuting_pairConjugacyClass]
      exact (Subgroup.mem_centralizer_singleton_iff.mp h.2).symm⟩, rfl⟩) (by
      intro h k hhk
      apply Subtype.ext
      apply Subtype.ext
      exact (pairConjugacyClass_centralizer_eq_iff g h k).mpr (Quotient.sound hhk)) C

private theorem centralizerConjClassToCommutingPair_injective (g : G) :
    Function.Injective (centralizerConjClassToCommutingPair g) := by
  intro C D
  refine Quotient.inductionOn₂ C D (fun h k hhk ↦ ?_)
  apply (pairConjugacyClass_centralizer_eq_iff g h k).mp
  exact congrArg (fun C ↦ C.1.1) hhk

private theorem centralizerConjClassToCommutingPair_surjective (g : G) :
    Function.Surjective (centralizerConjClassToCommutingPair g) := by
  rintro ⟨⟨C, hcomm⟩, hfirst⟩
  revert hcomm hfirst
  refine Quotient.inductionOn C (fun p ↦ ?_)
  intro hcomm hfirst
  have hpcomm : Commute p.1 p.2 :=
    PairConjugacyClass.isCommuting_pairConjugacyClass p |>.mp hcomm
  have hpfirst : ConjClasses.mk p.1 = ConjClasses.mk g := hfirst
  obtain ⟨x, hx⟩ := isConj_iff.mp (ConjClasses.mk_eq_mk_iff_isConj.mp hpfirst)
  have hkcomm : Commute g (x * p.2 * x⁻¹) := by
    have h := hpcomm.map (MulAut.conj x).toMonoidHom
    change Commute (x * p.1 * x⁻¹) (x * p.2 * x⁻¹) at h
    rwa [hx] at h
  let k : Subgroup.centralizer ({g} : Set G) :=
    ⟨x * p.2 * x⁻¹, Subgroup.mem_centralizer_singleton_iff.mpr hkcomm.symm⟩
  refine ⟨ConjClasses.mk k, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  apply (pairConjugacyClass_eq_iff (g, (k : G)) p).mpr
  exact ⟨x, hx.symm, rfl⟩

/-- Conjugacy classes in the centralizer of `g` are precisely the commuting
pair classes whose first conjugacy class is `[g]`. Source: SCP10, following
Theorem 5.9, lines 1613–1621. -/
def centralizerConjClassEquivCommutingPairFiber (g : G) :
    ConjClasses (Subgroup.centralizer ({g} : Set G)) ≃
      {C : CommutingPairConjugacyClass G // C.1.firstConjClass = ConjClasses.mk g} :=
  Equiv.ofBijective (centralizerConjClassToCommutingPair g)
    ⟨centralizerConjClassToCommutingPair_injective g,
      centralizerConjClassToCommutingPair_surjective g⟩

/-- For any choice of representatives, commuting pair classes are conjugacy
classes together with centralizer conjugacy classes. Source: SCP10, following
Theorem 5.9, lines 1613–1621. -/
def commutingPairConjugacyClassEquivSigmaCentralizerOfRepresentatives
    (r : ConjClasses G → G) (hr : ∀ C, ConjClasses.mk (r C) = C) :
    CommutingPairConjugacyClass G ≃
      (C : ConjClasses G) × ConjClasses (Subgroup.centralizer ({r C} : Set G)) :=
  (Equiv.sigmaFiberEquiv (fun C : CommutingPairConjugacyClass G ↦
    C.1.firstConjClass)).symm.trans (Equiv.sigmaCongrRight fun C ↦ by
      simpa only [hr C] using (centralizerConjClassEquivCommutingPairFiber (r C)).symm)

/-- A commuting pair class is a conjugacy class `[g]` together with a conjugacy
class in the centralizer of a representative of `[g]`. Source: SCP10,
following Theorem 5.9, lines 1613–1621. -/
def commutingPairConjugacyClassEquivSigmaCentralizer :
    CommutingPairConjugacyClass G ≃
      (C : ConjClasses G) × ConjClasses (Subgroup.centralizer ({C.out} : Set G)) :=
  commutingPairConjugacyClassEquivSigmaCentralizerOfRepresentatives
    Quotient.out Quotient.out_eq

open Classical in
/-- The centralizer count is valid for every choice of conjugacy-class
representatives. Source: SCP10, following Theorem 5.9, lines 1613–1621. -/
theorem card_commutingPairConjugacyClass_eq_sum_card_centralizer_of_representatives
    [Fintype G] (r : ConjClasses G → G) (hr : ∀ C, ConjClasses.mk (r C) = C) :
    Nat.card (CommutingPairConjugacyClass G) =
      ∑ C : ConjClasses G, Nat.card (ConjClasses (Subgroup.centralizer ({r C} : Set G))) := by
  rw [Nat.card_congr
    (commutingPairConjugacyClassEquivSigmaCentralizerOfRepresentatives r hr), Nat.card_sigma]

open Classical in
/-- The number of commuting torus closure labels is the sum, over conjugacy
classes `[g]`, of the numbers of conjugacy classes of the centralizers of `g`.
Source: SCP10, following Theorem 5.9, lines 1613–1621. -/
theorem card_commutingPairConjugacyClass_eq_sum_card_centralizer [Fintype G] :
    Nat.card (CommutingPairConjugacyClass G) =
      ∑ C : ConjClasses G, Nat.card (ConjClasses (Subgroup.centralizer ({C.out} : Set G))) := by
  exact card_commutingPairConjugacyClass_eq_sum_card_centralizer_of_representatives
    Quotient.out Quotient.out_eq

end

end TNLean.PEPS
