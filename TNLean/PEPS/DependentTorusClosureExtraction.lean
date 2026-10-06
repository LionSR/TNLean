/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.DependentTorusClosureTheorem
import TNLean.PEPS.PairConjugacy

/-!
# Trace-dual extraction of independently represented torus closures

The product of the eight actual bond trace-dual functionals detects a
simultaneous conjugacy class. Every surviving vertex gauge is constant,
and the diagonal scalar is exactly the common-centralizer cardinality
divided by the fourth power of the group cardinality. All eight virtual
alphabets and their representations remain independent.

Source: SCP10, arXiv:1001.3807, Lemma 4.6 and the independence argument of
Theorem 5.9, lines 1582–1621. This concerns the actual four-block closure
vectors, not the microscopic parent-Hamiltonian identification.
-/

noncomputable section
open scoped BigOperators
namespace TNLean.PEPS.DependentTorus

local notation "tail" => (torusLabelledBondTail (width := 2) (height := 2))
local notation "head" => (torusLabelledBondHead (width := 2) (height := 2))

variable {G : Type*} [Group G]

/-- Constant vertex conjugation acts on both seam labels simultaneously.
Source: SCP10, Definition 5.8, lines 1560–1580. -/
theorem closureLabels_conjugate (x g h : G) (e : Bond) :
    torusLabelledClosure (x * g * x⁻¹) (x * h * x⁻¹) e =
      x * torusLabelledClosure g h e * x⁻¹ := by
  unfold torusLabelledClosure
  split_ifs <;> simp

/-- A gauge relating two standard closures is constant away from the seams.
All four vertices synchronize, including for noncommuting closure pairs. -/
theorem nonseamCompatible_of_closureLabels_eq
    (p r : G × G) (q : Vertex → G)
    (hq : ∀ e, torusLabelledClosure p.1 p.2 e =
      q (head e) * torusLabelledClosure r.1 r.2 e * (q (tail e))⁻¹) :
    IsTorusNonseamCompatible q := by
  intro v
  constructor
  · intro hv
    have he := hq (v, false)
    simpa [torusLabelledClosure, torusLabelledBondHead, torusLabelledBondTail,
      hv, mul_inv_eq_one] using he.symm
  · intro hv
    have he := hq (v, true)
    simpa [torusLabelledClosure, torusLabelledBondHead, torusLabelledBondTail,
      hv, mul_inv_eq_one] using he.symm

/-- Equality of the eight gauged closure labels is exactly constant vertex
labels and simultaneous conjugation of the two seam labels. -/
theorem closureLabels_eq_iff (p r : G × G) (q : Vertex → G) :
    (∀ e, torusLabelledClosure p.1 p.2 e =
      q (head e) * torusLabelledClosure r.1 r.2 e * (q (tail e))⁻¹) ↔
      IsTorusNonseamCompatible q ∧
        p.1 = q (0, 0) * r.1 * (q (0, 0))⁻¹ ∧
        p.2 = q (0, 0) * r.2 * (q (0, 0))⁻¹ := by
  constructor
  · intro hq
    have hc := nonseamCompatible_of_closureLabels_eq p r q hq
    refine ⟨hc, ?_, ?_⟩
    · simpa only [torusLabelledClosure, neg_add_cancel, Bool.false_eq_true,
        ↓reduceIte, hc.eq_origin] using hq ((0, -1), true)
    · simpa only [torusLabelledClosure, neg_add_cancel, Bool.false_eq_true,
        ↓reduceIte, hc.eq_origin] using hq ((-1, 0), false)
  · rintro ⟨hc, hg, hh⟩ e
    simp only [hc.eq_origin, hg, hh]
    exact closureLabels_conjugate _ _ _ e

variable [Fintype G]
variable (D : Bond → Type*) [∀ e, Fintype (D e)] [∀ e, DecidableEq (D e)]

open Classical in
/-- Trace-dual extraction applied to all eight actual bonds of a canonical
closure counts simultaneous conjugations, with the four local averages.
Source: SCP10, Lemma 4.6 and Theorem 5.9, lines 1582–1610. -/
theorem bondCoefficientExtraction_closure
    (U : (e : Bond) → G →* Matrix (D e) (D e) ℂ)
    (hU : ∀ e, Representation.IsSemiRegular (Matrix.toLinAlgEquiv'.toMonoidHom.comp (U e)))
    (p r : G × G) :
    DependentBondNetwork.bondCoefficientExtraction tail head D U
        (torusLabelledClosure p.1 p.2)
        (closure D U (canonicalSites D U) r.1 r.2) =
      (Fintype.card G : ℂ)⁻¹ ^ 4 *
        ∑ x : G, if p.1 = x * r.1 * x⁻¹ ∧ p.2 = x * r.2 * x⁻¹ then 1 else 0 := by
  classical
  rw [closure, DependentBondNetwork.bondCoefficientExtraction_network_averagingSite]
  simp only [← map_mul, torusDeltaPairing_apply_rep _ (hU _), Fintype.prod_boole,
    closureLabels_eq_iff, show Fintype.card Vertex = 4 by decide]
  congr 1
  refine (Fintype.sum_of_injective (fun x : G => fun _ : Vertex => x)
    (fun x y hxy => congrFun hxy (0, 0)) _ _ ?_ ?_).symm
  · intro q hq
    apply ite_eq_right
    rintro ⟨hc, _⟩
    exact hq ⟨q (0, 0), (funext hc.eq_origin).symm⟩
  · intro x
    have hc : IsTorusNonseamCompatible (fun _ : Vertex => x) :=
      fun _ => ⟨fun _ => rfl, fun _ => rfl⟩
    simp only [hc, true_and]

/-- Different simultaneous-conjugacy classes are separated by the genuine
per-bond trace-dual extraction. -/
theorem bondCoefficientExtraction_closure_eq_zero_of_class_ne
    (U : (e : Bond) → G →* Matrix (D e) (D e) ℂ)
    (hU : ∀ e, Representation.IsSemiRegular (Matrix.toLinAlgEquiv'.toMonoidHom.comp (U e)))
    {p r : G × G} (hpr : pairConjugacyClass G p ≠ pairConjugacyClass G r) :
    DependentBondNetwork.bondCoefficientExtraction tail head D U
        (torusLabelledClosure p.1 p.2)
        (closure D U (canonicalSites D U) r.1 r.2) = 0 := by
  classical
  rw [bondCoefficientExtraction_closure D U hU]
  apply mul_eq_zero_of_right
  apply Finset.sum_eq_zero
  intro x _
  apply ite_eq_right
  intro hx
  exact hpr ((pairConjugacyClass_eq_iff p r).mpr ⟨x, hx⟩)

/-- The diagonal extracted value is the exact common-centralizer cardinality
with normalization from the four canonical projectors. -/
theorem bondCoefficientExtraction_closure_self
    (U : (e : Bond) → G →* Matrix (D e) (D e) ℂ)
    (hU : ∀ e, Representation.IsSemiRegular (Matrix.toLinAlgEquiv'.toMonoidHom.comp (U e)))
    (p : G × G) :
    DependentBondNetwork.bondCoefficientExtraction tail head D U
        (torusLabelledClosure p.1 p.2)
        (closure D U (canonicalSites D U) p.1 p.2) =
      (Fintype.card G : ℂ)⁻¹ ^ 4 *
        (Nat.card (Subgroup.centralizer ({p.1, p.2} : Set G)) : ℂ) := by
  classical
  rw [bondCoefficientExtraction_closure D U hU]
  have hm (x : G) : (p.1 = x * p.1 * x⁻¹ ∧ p.2 = x * p.2 * x⁻¹) ↔
      x ∈ Subgroup.centralizer ({p.1, p.2} : Set G) := by
    simp only [eq_mul_inv_iff_mul_eq, Subgroup.mem_centralizer_iff,
      Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]
  simp only [hm, Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.sum_boole]

/-- The extracted diagonal is nonzero because the common centralizer contains
identity and the finite group has nonzero cardinality in the complex field. -/
theorem bondCoefficientExtraction_closure_self_ne_zero
    (U : (e : Bond) → G →* Matrix (D e) (D e) ℂ)
    (hU : ∀ e, Representation.IsSemiRegular (Matrix.toLinAlgEquiv'.toMonoidHom.comp (U e)))
    (p : G × G) :
    DependentBondNetwork.bondCoefficientExtraction tail head D U
        (torusLabelledClosure p.1 p.2)
        (closure D U (canonicalSites D U) p.1 p.2) ≠ 0 := by
  rw [bondCoefficientExtraction_closure_self D U hU]
  exact mul_ne_zero (pow_ne_zero _ (inv_ne_zero (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)))
    (Nat.cast_ne_zero.mpr Nat.card_pos.ne')

end TNLean.PEPS.DependentTorus
