/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.DependentTorusClosureDimension
import TNLean.Algebra.SemiRegularGroupAlgebra

/-! # Dependent closure independence and dimension with nonabelian, nonregular bonds -/

noncomputable section
open TNLean.PEPS
open scoped BigOperators

namespace DependentTorusClosureDimensionTest

local notation "tail" => (torusLabelledBondTail (width := 2) (height := 2))
local notation "head" => (torusLabelledBondHead (width := 2) (height := 2))

section GeneralSignatures

variable {G : Type*} [Group G] [Finite G]
variable (D : DependentTorus.Bond → Type*) [∀ e, Fintype (D e)] [∀ e, DecidableEq (D e)]
variable {Phys : DependentTorus.Vertex → Type*} [∀ v, Finite (Phys v)]
variable (U : (e : DependentTorus.Bond) → G →* Matrix (D e) (D e) ℂ)
variable (hU : ∀ e, Representation.IsSemiRegular
  (Matrix.toLinAlgEquiv'.toMonoidHom.comp (U e)))
variable (A : (v : DependentTorus.Vertex) → DependentTorus.LocalConfig D v → Phys v → ℂ)
variable (hA : ∀ v, IsGInjective (DependentBondNetwork.incidentRepresentation tail head D U v)
  (DependentBondNetwork.localSiteMap tail head D A v))

-- Neither a common bond alphabet nor an isometric or independence premise is accepted.
example : LinearIndependent ℂ
    (DependentTorus.closureClass D U A (fun v => (hA v).invariant)) :=
  DependentTorus.linearIndependent_closureClass D U hU A hA

example : LinearIndependent ℂ (fun C : CommutingPairConjugacyClass G =>
    DependentTorus.closureClass D U A (fun v => (hA v).invariant) C.1) :=
  DependentTorus.linearIndependent_closureClass_commuting D U hU A hA

example : Module.finrank ℂ (DependentTorus.commutingClosureSpan D U A) =
    Nat.card (CommutingPairConjugacyClass G) :=
  DependentTorus.finrank_commutingClosureSpan D U hU A hA

example : Module.finrank ℂ (DependentTorus.fourCutSpace D A) =
    Nat.card (CommutingPairConjugacyClass G) :=
  DependentTorus.finrank_fourCutSpace D U hU A hA

end GeneralSignatures

-- Left translation on the first factor gives m actual regular copies.
private def copyPermutation {G : Type*} [Group G] (m : ℕ) :
    G →* Equiv.Perm (G × Fin m) where
  toFun g := Equiv.prodCongr (MulAction.toPermHom G G g) (Equiv.refl _)
  map_one' := by ext x <;> simp
  map_mul' g h := by ext x <;> simp [mul_assoc]

private def regularCopies {G : Type*} [Group G] [Fintype G] [DecidableEq G] (m : ℕ) :
    G →* Matrix (G × Fin m) (G × Fin m) ℂ :=
  Matrix.permMatrixHom.comp (copyPermutation m)

private theorem regularCopies_apply {G : Type*} [Group G] [Fintype G] [DecidableEq G]
    (m : ℕ) (g : G) (x : G × Fin m → ℂ) (a : G × Fin m) :
    Matrix.toLinAlgEquiv' (regularCopies m g) x a = x (g⁻¹ * a.1, a.2) := by
  rcases a with ⟨a, i⟩
  simp [regularCopies, copyPermutation, Matrix.toLinAlgEquiv'_apply,
    Matrix.permMatrixHom_apply, Matrix.permMatrix_mulVec, MulAction.toPerm_symm_apply,
    smul_eq_mul]

private theorem regularCopies_semiRegular {G : Type*} [Group G] [Fintype G] [DecidableEq G]
    (m : ℕ) (hm : 0 < m) : Representation.IsSemiRegular
    (Matrix.toLinAlgEquiv'.toMonoidHom.comp (regularCopies (G := G) m)) := by
  classical
  apply Representation.isSemiRegular_of_linearIndependent
  rw [Fintype.linearIndependent_iff]
  intro c hc g
  let z : Fin m := ⟨0, hm⟩
  have heval (k : G) :
      (Matrix.toLinAlgEquiv'.toMonoidHom.comp (regularCopies m) k)
        (Pi.single (1, z) 1) (g, z) = if k = g then 1 else 0 := by
    change Matrix.toLinAlgEquiv' (regularCopies m k) _ _ = _
    rw [regularCopies_apply]
    simp [Pi.single_apply, inv_mul_eq_one, eq_comm]
  have h := congrArg (fun L : Module.End ℂ (G × Fin m → ℂ) =>
    L (Pi.single (1, z) 1) (g, z)) hc
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul, heval, LinearMap.zero_apply, Pi.zero_apply] at h
  simpa using h

private abbrev S3 := Equiv.Perm (Fin 3)
private def transposition : S3 := Equiv.swap 0 1

example : Fintype.card S3 = 6 := by decide
example : ¬ ∀ g h : S3, g * h = h * g := by decide

-- The eight multiplicities are 2,3,4,5,6,7,8,9, so none of the edges is regular.
private def edgeMultiplicity (e : DependentTorus.Bond) : ℕ :=
  4 * e.1.1.val + 2 * e.1.2.val + e.2.toNat + 2
private abbrev BondAlphabet (e : DependentTorus.Bond) := S3 × Fin (edgeMultiplicity e)
private def U (e : DependentTorus.Bond) : S3 →* Matrix (BondAlphabet e) (BondAlphabet e) ℂ :=
  regularCopies (edgeMultiplicity e)
private theorem U_semiRegular (e : DependentTorus.Bond) : Representation.IsSemiRegular
    (Matrix.toLinAlgEquiv'.toMonoidHom.comp (U e)) :=
  regularCopies_semiRegular _ (by unfold edgeMultiplicity; omega)

example : Function.Injective (fun e : DependentTorus.Bond => Fintype.card (BondAlphabet e)) :=
  by decide
private theorem card_bondAlphabet_gt (e : DependentTorus.Bond) :
    Fintype.card S3 < Fintype.card (BondAlphabet e) := by
  have : 2 ≤ edgeMultiplicity e := by unfold edgeMultiplicity; omega
  simp only [BondAlphabet, Fintype.card_prod, Fintype.card_fin]
  have hcard : Fintype.card S3 = 6 := by decide
  rw [hcard]
  omega

-- In particular, no edge representation is even linearly equivalent to one regular copy.
example (e : DependentTorus.Bond) :
    ¬ Nonempty ((BondAlphabet e → ℂ) ≃ₗ[ℂ] (S3 → ℂ)) := by
  rintro ⟨L⟩
  have h := L.finrank_eq
  simp only [Module.finrank_fintype_fun_eq_card] at h
  exact (card_bondAlphabet_gt e).ne' h

example : Fintype.card (BondAlphabet ((0, 0), false)) = 12 := by decide
example : Fintype.card (BondAlphabet ((1, 1), true)) = 54 := by decide

-- All four canonical physical configuration spaces have different dimensions too.
example : Function.Injective (fun v : DependentTorus.Vertex =>
    Fintype.card (DependentTorus.LocalConfig BondAlphabet v)) := by
  simp only [DependentTorus.LocalConfig, DependentBondNetwork.LocalConfig,
    Fintype.card_pi, BondAlphabet, Fintype.card_prod, Fintype.card_fin]
  decide

-- These conclusions concern the canonical tensors on the actual unequal alphabets.
example : LinearIndependent ℂ (DependentTorus.closureClass BondAlphabet U
    (DependentTorus.canonicalSites BondAlphabet U)
    (fun v =>
      (DependentBondNetwork.isGInjective_averagingSite tail head BondAlphabet U v).invariant)) :=
  DependentTorus.linearIndependent_closureClass_canonical BondAlphabet U U_semiRegular

example : Module.finrank ℂ (DependentTorus.fourCutSpace BondAlphabet
    (DependentTorus.canonicalSites BondAlphabet U)) = Nat.card (CommutingPairConjugacyClass S3) :=
  DependentTorus.finrank_fourCutSpace BondAlphabet U U_semiRegular _
    (DependentBondNetwork.isGInjective_averagingSite tail head BondAlphabet U)

-- The same nonregular family also accepts four arbitrary physical alphabets and maps.
example {Phys : DependentTorus.Vertex → Type*} [∀ v, Finite (Phys v)]
    (A : (v : DependentTorus.Vertex) →
      DependentTorus.LocalConfig BondAlphabet v → Phys v → ℂ)
    (hA : ∀ v, IsGInjective
      (DependentBondNetwork.incidentRepresentation tail head BondAlphabet U v)
      (DependentBondNetwork.localSiteMap tail head BondAlphabet A v)) :
    Module.finrank ℂ (DependentTorus.fourCutSpace BondAlphabet A) =
      Nat.card (CommutingPairConjugacyClass S3) :=
  DependentTorus.finrank_fourCutSpace BondAlphabet U U_semiRegular A hA

example : DependentBondNetwork.bondCoefficientExtraction tail head BondAlphabet U
    (torusLabelledClosure (1 : S3) 1)
    (DependentTorus.closure BondAlphabet U (DependentTorus.canonicalSites BondAlphabet U) 1 1) =
      (1 / 216 : ℂ) := by
  rw [DependentTorus.bondCoefficientExtraction_closure BondAlphabet U U_semiRegular (1, 1) (1, 1)]
  simp
  norm_num [Fintype.card_perm]

-- Two distinct transpositions yield the same closure after simultaneous conjugation.
-- This test uses arbitrary invariant physical tensors, without injectivity or finiteness.
example {Phys : DependentTorus.Vertex → Type*}
    (A : (v : DependentTorus.Vertex) →
      DependentTorus.LocalConfig BondAlphabet v → Phys v → ℂ)
    (hA : ∀ v g, DependentBondNetwork.localSiteMap tail head BondAlphabet A v ∘ₗ
      DependentBondNetwork.incidentRepresentation tail head BondAlphabet U v g =
        DependentBondNetwork.localSiteMap tail head BondAlphabet A v) :
    DependentTorus.closure BondAlphabet U A transposition 1 =
      DependentTorus.closure BondAlphabet U A (Equiv.swap 1 2) 1 := by
  have hconj : (Equiv.swap 0 2 : S3) * transposition * (Equiv.swap 0 2 : S3)⁻¹ =
      Equiv.swap 1 2 := by decide
  simpa only [hconj, mul_one, mul_inv_cancel] using
    (DependentTorus.closure_conjugate BondAlphabet U A hA (Equiv.swap 0 2) transposition 1).symm

-- A noncentral commuting pair has a smaller, explicitly checked diagonal.
example : DependentBondNetwork.bondCoefficientExtraction tail head BondAlphabet U
    (torusLabelledClosure transposition (1 : S3))
    (DependentTorus.closure BondAlphabet U (DependentTorus.canonicalSites BondAlphabet U)
      transposition 1) = (1 / 648 : ℂ) := by
  rw [DependentTorus.bondCoefficientExtraction_closure BondAlphabet U U_semiRegular
    (transposition, 1) (transposition, 1)]
  simp only [mul_one, mul_inv_cancel, and_true, Finset.sum_boole]
  have hcard : (Finset.univ.filter fun x : S3 =>
      transposition = x * transposition * x⁻¹).card = 2 := by decide
  rw [hcard]
  norm_num [Fintype.card_perm]

-- Distinct simultaneous-conjugacy classes have zero cross-extraction.
example : DependentBondNetwork.bondCoefficientExtraction tail head BondAlphabet U
    (torusLabelledClosure transposition (1 : S3))
    (DependentTorus.closure BondAlphabet U
      (DependentTorus.canonicalSites BondAlphabet U) 1 1) = 0 :=
  DependentTorus.bondCoefficientExtraction_closure_eq_zero_of_class_ne
    BondAlphabet U U_semiRegular (p := (transposition, 1)) (r := (1, 1)) (by
      intro h
      obtain ⟨x, hx, _⟩ := (pairConjugacyClass_eq_iff _ _).mp h
      have hne : transposition ≠ 1 := by decide
      exact hne (by simpa using hx))

end DependentTorusClosureDimensionTest

set_option linter.hashCommand false

/--
info: 'TNLean.PEPS.DependentTorus.bondCoefficientExtraction_closure_self' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.DependentTorus.bondCoefficientExtraction_closure_self

/--
info: 'TNLean.PEPS.DependentTorus.linearIndependent_closureClass' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.DependentTorus.linearIndependent_closureClass

/--
info: 'TNLean.PEPS.DependentTorus.linearIndependent_closureClass_commuting' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.DependentTorus.linearIndependent_closureClass_commuting

/--
info: 'TNLean.PEPS.DependentTorus.finrank_commutingClosureSpan' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.DependentTorus.finrank_commutingClosureSpan

/--
info: 'TNLean.PEPS.DependentTorus.finrank_fourCutSpace' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.DependentTorus.finrank_fourCutSpace
