/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.CharacterProjectorTwirl
import TNLean.PEPS.PairConjugacy
import Mathlib.LinearAlgebra.Contraction
import Mathlib.LinearAlgebra.TensorProduct.Matrix

/-!
# Independent operator sums over simultaneous conjugacy classes

For a semi-regular representation, the operators obtained by summing
`ρ(x h x⁻¹) ⊗ ρ(x g x⁻¹)` over the group depend only on the simultaneous conjugacy class
of `(g,h)` and are linearly independent as the class varies. Tensor products
of the trace-dual functionals of Lemma 4.6 detect the class; on its own representative
the functional counts the common centralizer.

Source: Schuch, Cirac, Pérez-García, arXiv:1001.3807, Theorem 5.9,
`Papers/1001.3807/paper_v3.tex` lines 1582–1621, with Lemma 4.6, lines 1015–1029.
These are auxiliary operator statements. No identification with physical torus vectors
or with a parent-Hamiltonian ground space is asserted. The operator independence also
holds for noncommuting pairs.

## References

- [arXiv:1001.3807](https://arxiv.org/abs/1001.3807) -- N. Schuch, J. I. Cirac,
  D. Pérez-García, *PEPS as ground states: degeneracy and topology*
-/

open scoped BigOperators TensorProduct Kronecker

namespace TNLean.PEPS

variable {G E : Type*} [Group G] [Fintype G]
variable [AddCommGroup E] [Module ℂ E]

/-- The simultaneous-conjugacy sum, with horizontal and vertical factors in that order.
Source: SCP10, operator extraction in the proof of Theorem 5.9, lines 1595–1610. -/
def pairConjugacyOperator (ρ : Representation ℂ G E) (p : G × G) :
    Module.End ℂ E ⊗[ℂ] Module.End ℂ E :=
  ∑ x : G, ρ (x * p.2 * x⁻¹) ⊗ₜ[ℂ] ρ (x * p.1 * x⁻¹)

/-- The simultaneous-conjugacy sum depends only on the pair class.
Source: SCP10, Definition 5.8 and Theorem 5.9, lines 1560–1610. -/
theorem pairConjugacyOperator_eq_of_pairConjugacyClass_eq (ρ : Representation ℂ G E)
    {p q : G × G} (hpq : pairConjugacyClass G p = pairConjugacyClass G q) :
    pairConjugacyOperator ρ p = pairConjugacyOperator ρ q := by
  obtain ⟨y, hg, hh⟩ := (pairConjugacyClass_eq_iff p q).mp hpq
  unfold pairConjugacyOperator
  apply Fintype.sum_equiv (Equiv.mulRight y)
  intro x
  simp only [Equiv.coe_mulRight, hg, hh]
  congr 2 <;> group

/-- The operator associated with a pair-conjugacy class.
Source: SCP10, Theorem 5.9, lines 1582–1610. -/
def pairConjugacyClassOperator (ρ : Representation ℂ G E) (C : PairConjugacyClass G) :
    Module.End ℂ E ⊗[ℂ] Module.End ℂ E :=
  Quotient.lift (pairConjugacyOperator ρ)
    (fun _ _ h => pairConjugacyOperator_eq_of_pairConjugacyClass_eq ρ (Quotient.sound h)) C

@[simp]
theorem pairConjugacyClassOperator_pairConjugacyClass (ρ : Representation ℂ G E)
    (p : G × G) :
    pairConjugacyClassOperator ρ (pairConjugacyClass G p) = pairConjugacyOperator ρ p := rfl

variable [FiniteDimensional ℂ E]

/-- Tensor product of the trace-dual functionals at `(h,g)`.
Source: SCP10, Lemma 4.6 and the proof of Theorem 5.9, lines 1015–1029 and 1595–1610. -/
noncomputable def pairOperatorDeltaPairing (ρ : Representation ℂ G E) (p : G × G) :
    (Module.End ℂ E ⊗[ℂ] Module.End ℂ E) →ₗ[ℂ] ℂ :=
  (TensorProduct.lid ℂ ℂ).toLinearMap ∘ₗ
    TensorProduct.map (Representation.deltaPairing ρ p.2) (Representation.deltaPairing ρ p.1)

/-- On a simple tensor the trace-dual functional is the product of its two factors. -/
theorem pairOperatorDeltaPairing_tmul (ρ : Representation ℂ G E) (p : G × G)
    (A B : Module.End ℂ E) :
    pairOperatorDeltaPairing ρ p (A ⊗ₜ[ℂ] B) =
      Representation.deltaPairing ρ p.2 A * Representation.deltaPairing ρ p.1 B := by
  simp [pairOperatorDeltaPairing]

open Classical in
/-- The trace-dual tensor functional counts simultaneous conjugations onto the detected
pair. Source: SCP10, Lemma 4.6 and Theorem 5.9, lines 1015–1029 and 1595–1610. -/
theorem pairOperatorDeltaPairing_pairConjugacyOperator
    (ρ : Representation ℂ G E) (hρ : ρ.IsSemiRegular) (p q : G × G) :
    pairOperatorDeltaPairing ρ p (pairConjugacyOperator ρ q) =
      ∑ x : G, if p.1 = x * q.1 * x⁻¹ ∧ p.2 = x * q.2 * x⁻¹ then (1 : ℂ) else 0 := by
  simp only [pairConjugacyOperator, map_sum, pairOperatorDeltaPairing_tmul,
    Representation.deltaPairing_rep_of_isSemiRegular ρ hρ]
  apply Finset.sum_congr rfl
  intro x _
  split_ifs <;> simp_all

/-- Different pair classes are separated by the trace-dual tensor functional.
Source: SCP10, proof of Theorem 5.9, lines 1595–1610. -/
theorem pairOperatorDeltaPairing_eq_zero_of_pairConjugacyClass_ne
    (ρ : Representation ℂ G E) (hρ : ρ.IsSemiRegular) {p q : G × G}
    (hpq : pairConjugacyClass G p ≠ pairConjugacyClass G q) :
    pairOperatorDeltaPairing ρ p (pairConjugacyOperator ρ q) = 0 := by
  classical
  rw [pairOperatorDeltaPairing_pairConjugacyOperator ρ hρ]
  apply Finset.sum_eq_zero
  intro x _
  apply ite_eq_right
  intro hx
  exact hpq ((pairConjugacyClass_eq_iff p q).mpr ⟨x, hx⟩)

/-- On its own pair, the trace-dual tensor functional counts the common centralizer.
Source: SCP10, coefficient detection in the proof of Theorem 5.9, lines 1595–1610. -/
theorem pairOperatorDeltaPairing_self_eq_card_centralizer
    (ρ : Representation ℂ G E) (hρ : ρ.IsSemiRegular) (p : G × G) :
    pairOperatorDeltaPairing ρ p (pairConjugacyOperator ρ p) =
      (Nat.card (Subgroup.centralizer ({p.1, p.2} : Set G)) : ℂ) := by
  classical
  rw [pairOperatorDeltaPairing_pairConjugacyOperator ρ hρ]
  have hm (x : G) : (p.1 = x * p.1 * x⁻¹ ∧ p.2 = x * p.2 * x⁻¹) ↔
      x ∈ Subgroup.centralizer ({p.1, p.2} : Set G) := by
    simp only [eq_mul_inv_iff_mul_eq, Subgroup.mem_centralizer_iff,
      Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]
  simp only [hm, Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.sum_boole]

/-- The diagonal value of the trace-dual tensor functional is nonzero, since the common
centralizer contains the identity. -/
theorem pairOperatorDeltaPairing_self_ne_zero
    (ρ : Representation ℂ G E) (hρ : ρ.IsSemiRegular) (p : G × G) :
    pairOperatorDeltaPairing ρ p (pairConjugacyOperator ρ p) ≠ 0 := by
  rw [pairOperatorDeltaPairing_self_eq_card_centralizer ρ hρ]
  have hn : 0 < Nat.card (Subgroup.centralizer ({p.1, p.2} : Set G)) := Nat.card_pos
  exact Nat.cast_ne_zero.mpr hn.ne'

/-- Simultaneous-conjugacy operator sums for a semi-regular representation are linearly
independent over all pair classes. Restricting to commuting classes gives the operator
independence used in SCP10, Theorem 5.9, lines 1595–1610. This is not a ground-space claim. -/
theorem linearIndependent_pairConjugacyClassOperator
    (ρ : Representation ℂ G E) (hρ : ρ.IsSemiRegular) :
    LinearIndependent ℂ (pairConjugacyClassOperator ρ) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro μ hμ C₀
  let p : G × G := C₀.out
  have hp : pairConjugacyClass G p = C₀ := Quotient.out_eq C₀
  have hrep (C : PairConjugacyClass G) :
      pairConjugacyClassOperator ρ C = pairConjugacyOperator ρ C.out := by
    have hout : pairConjugacyClass G C.out = C := Quotient.out_eq C
    exact (congrArg (pairConjugacyClassOperator ρ) hout).symm
  have hzero (C : PairConjugacyClass G) (hC : C ≠ C₀) :
      pairOperatorDeltaPairing ρ p (pairConjugacyClassOperator ρ C) = 0 := by
    rw [hrep]
    apply pairOperatorDeltaPairing_eq_zero_of_pairConjugacyClass_ne ρ hρ
    rw [hp, show pairConjugacyClass G C.out = C from Quotient.out_eq C]
    exact Ne.symm hC
  have h := congrArg (pairOperatorDeltaPairing ρ p) hμ
  simp only [map_sum, map_smul, smul_eq_mul, map_zero] at h
  rw [Finset.sum_eq_single C₀ (fun C _ hC => by rw [hzero C hC, mul_zero])
    (fun hC => absurd (Finset.mem_univ C₀) hC)] at h
  have hn : pairOperatorDeltaPairing ρ p (pairConjugacyClassOperator ρ C₀) ≠ 0 := by
    rw [← hp, pairConjugacyClassOperator_pairConjugacyClass]
    exact pairOperatorDeltaPairing_self_ne_zero ρ hρ p
  exact (mul_eq_zero.mp h).resolve_right hn

section Coordinates

variable {V : Type*} [Fintype V] [DecidableEq V]

private noncomputable def coordinateEndTensorEquiv :
    (Module.End ℂ (V → ℂ) ⊗[ℂ] Module.End ℂ (V → ℂ)) ≃ₗ[ℂ]
      Matrix (V × V) (V × V) ℂ :=
  homTensorHomEquiv ℂ (V → ℂ) (V → ℂ) (V → ℂ) (V → ℂ) ≪≫ₗ
    LinearMap.toMatrix ((Pi.basisFun ℂ V).tensorProduct (Pi.basisFun ℂ V))
      ((Pi.basisFun ℂ V).tensorProduct (Pi.basisFun ℂ V))

private theorem coordinateEndTensorEquiv_tmul (A B : Module.End ℂ (V → ℂ)) :
    coordinateEndTensorEquiv (A ⊗ₜ[ℂ] B) = LinearMap.toMatrix' A ⊗ₖ LinearMap.toMatrix' B := by
  change LinearMap.toMatrix ((Pi.basisFun ℂ V).tensorProduct (Pi.basisFun ℂ V))
    ((Pi.basisFun ℂ V).tensorProduct (Pi.basisFun ℂ V)) (TensorProduct.map A B) = _
  rw [TensorProduct.toMatrix_map, LinearMap.toMatrix_eq_toMatrix']

/-- The simultaneous-conjugacy operator in the coordinate basis of two virtual bonds.
Source: SCP10, operator extraction in the proof of Theorem 5.9, lines 1595–1610. -/
noncomputable def pairConjugacyClassKroneckerOperator (U : G →* Matrix V V ℂ)
    (C : PairConjugacyClass G) : Matrix (V × V) (V × V) ℂ :=
  coordinateEndTensorEquiv
    (pairConjugacyClassOperator (Matrix.toLinAlgEquiv'.toMonoidHom.comp U) C)

/-- For a representative `(g,h)`, the coordinate operator is the sum of
`U(x h x⁻¹) ⊗ₖ U(x g x⁻¹)`. Source: SCP10, Theorem 5.9, lines 1595–1610. -/
theorem pairConjugacyClassKroneckerOperator_pairConjugacyClass
    (U : G →* Matrix V V ℂ) (p : G × G) :
    pairConjugacyClassKroneckerOperator U (pairConjugacyClass G p) =
      ∑ x : G, U (x * p.2 * x⁻¹) ⊗ₖ U (x * p.1 * x⁻¹) := by
  simp only [pairConjugacyClassKroneckerOperator,
    pairConjugacyClassOperator_pairConjugacyClass, pairConjugacyOperator, map_sum,
    coordinateEndTensorEquiv_tmul]
  apply Finset.sum_congr rfl
  intro x _
  change LinearMap.toMatrix' (Matrix.toLin' (U (x * p.2 * x⁻¹))) ⊗ₖ
    LinearMap.toMatrix' (Matrix.toLin' (U (x * p.1 * x⁻¹))) = _
  simp only [LinearMap.toMatrix'_toLin']

/-- The coordinate Kronecker operators are independent for a semi-regular virtual
representation. This is the operator independence used in SCP10, Theorem 5.9,
lines 1595–1610; no physical-vector or ground-space assertion is made. -/
theorem linearIndependent_pairConjugacyClassKroneckerOperator
    (U : G →* Matrix V V ℂ)
    (hU : Representation.IsSemiRegular (Matrix.toLinAlgEquiv'.toMonoidHom.comp U)) :
    LinearIndependent ℂ (pairConjugacyClassKroneckerOperator U) := by
  exact (linearIndependent_pairConjugacyClassOperator _ hU).map'
    coordinateEndTensorEquiv.toLinearMap
    (LinearMap.ker_eq_bot.mpr coordinateEndTensorEquiv.injective)

end Coordinates

end TNLean.PEPS
