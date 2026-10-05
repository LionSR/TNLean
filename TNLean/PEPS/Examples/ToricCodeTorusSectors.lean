/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.SemiRegularGroupAlgebra
import TNLean.PEPS.Examples.ToricCodePrimal
import TNLean.PEPS.GInjectiveTorusSectorCount

/-!
# Four independent primal toric-code torus closures

The one-bond representation of \(\mathbb Z_2\) sends its nontrivial element to
\(Z=\operatorname{diag}(1,-1)\). Its oriented four-leg action is exactly the virtual
parity action of the primal toric-code tensor. The matrices \(I\) and \(Z\) are
linearly independent, so this representation is semi-regular.

For every positive rectangular torus, the four actual contractions with \(I\) or
\(Z\) on each of the two seams are linearly independent. Their span has dimension
four. Identification of this span with a parent-Hamiltonian ground space is a
separate assertion; no ground-space spanning statement is made here.

The local tensor is the primal tensor of arXiv:2011.12127, Appendix A,
equation `eq:app:tcode-rep-primal`, lines 2451–2465. Independence is the
\(\mathbb Z_2\) specialization of the independence argument in SCP10, Theorem 5.9,
lines 1582–1621. Rectangular and size-one tori are algebraic extensions of its
square-torus setting.
-/

open scoped BigOperators Kronecker Matrix

namespace TNLean.PEPS

/-- The bond representation \(U_0=I\), \(U_1=Z\) for the primal toric-code tensor.
Source: arXiv:2011.12127, Appendix A, equation `eq:app:tcode-rep-primal`. -/
def toricCodeBondRep : ToricCodeGroup →* Matrix ToricCodeGroup ToricCodeGroup ℂ where
  toFun g := Matrix.diagonal fun i =>
    (-1 : ℂ) ^ ((Multiplicative.toAdd g).val * (Multiplicative.toAdd i).val)
  map_one' := by simp
  map_mul' g h := by
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    change (-1 : ℂ) ^ ((Multiplicative.toAdd g + Multiplicative.toAdd h).val *
      (Multiplicative.toAdd i).val) = _
    rw [ZMod.val_add, pow_mul, ← neg_one_pow_eq_pow_mod_two, pow_add, mul_pow,
      ← pow_mul, ← pow_mul]

/-- The one-bond action is diagonal in the group basis, with its binary character
on each entry. -/
theorem toricCodeBondRep_diagonal (g : ToricCodeGroup) :
    toricCodeBondRep g = Matrix.diagonal (fun i =>
      (-1 : ℂ) ^ ((Multiplicative.toAdd g).val * (Multiplicative.toAdd i).val)) := rfl

/-- The nontrivial bond action is the Pauli matrix \(Z\). -/
@[simp]
theorem toricCodeBondRep_generator :
    toricCodeBondRep (Multiplicative.ofAdd (1 : ZMod 2)) = toricCodeZ := by
  change Matrix.diagonal (fun i : ToricCodeGroup =>
    (-1 : ℂ) ^ ((1 : ZMod 2).val * (Multiplicative.toAdd i).val)) =
      Matrix.diagonal (fun i => (-1 : ℂ) ^ (Multiplicative.toAdd i).val)
  norm_num [ZMod.val_one_eq_one_mod]

/-- The oriented four-leg action of the bond representation is the primal tensor's
parity action \(Z^{\otimes4}\). Source: arXiv:2011.12127, Appendix A,
equation `eq:app:tcode-rep-primal`, lines 2464–2465. -/
theorem torusLegRep_toricCodeBondRep :
    torusLegRep toricCodeBondRep = toricCodePrimalVirtualRep := by
  apply MonoidHom.ext
  intro g
  have hg : ∀ g : ToricCodeGroup, g = 1 ∨ g = Multiplicative.ofAdd (1 : ZMod 2) := by decide
  rcases hg g with rfl | rfl
  · simp
  · rw [toricCodePrimalVirtualRep_generator]
    change (torusLegKernel (toricCodeBondRep (Multiplicative.ofAdd (1 : ZMod 2)))
      (toricCodeBondRep (Multiplicative.ofAdd (1 : ZMod 2))⁻¹)).mulVecLin = _
    rw [show (Multiplicative.ofAdd (1 : ZMod 2))⁻¹ =
      Multiplicative.ofAdd (1 : ZMod 2) from rfl, toricCodeBondRep_generator]
    simp [torusLegKernel, toricCodePrimalParityMatrix, toricCodeZ]

private theorem linearIndependent_toricCodeBondRep :
    LinearIndependent ℂ (fun g => toricCodeBondRep g) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc g
  have hsum : (∑ a : ToricCodeGroup, c a • toricCodeBondRep a) =
      c 1 • toricCodeBondRep 1 +
        c (Multiplicative.ofAdd (1 : ZMod 2)) •
          toricCodeBondRep (Multiplicative.ofAdd (1 : ZMod 2)) := Fin.sum_univ_two _
  rw [hsum] at hc
  have h₀ := congrArg (fun M : Matrix ToricCodeGroup ToricCodeGroup ℂ => M 1 1) hc
  have h₁ := congrArg (fun M : Matrix ToricCodeGroup ToricCodeGroup ℂ =>
    M (Multiplicative.ofAdd (1 : ZMod 2)) (Multiplicative.ofAdd (1 : ZMod 2))) hc
  simp [toricCodeBondRep, ZMod.val_one_eq_one_mod] at h₀ h₁
  have hg : ∀ g : ToricCodeGroup, g = 1 ∨ g = Multiplicative.ofAdd (1 : ZMod 2) := by decide
  rcases hg g with rfl | rfl
  · linear_combination (h₀ + h₁) / 2
  · linear_combination (h₀ - h₁) / 2

/-- The bond action contains both irreducible representations of \(\mathbb Z_2\).
This verifies the semi-regularity hypothesis of SCP10, Theorem 5.9. -/
theorem isSemiRegular_toricCodeBondRep :
    Representation.IsSemiRegular (Matrix.toLinAlgEquiv'.toMonoidHom.comp toricCodeBondRep) := by
  apply Representation.isSemiRegular_of_linearIndependent
  exact linearIndependent_toricCodeBondRep.map'
    Matrix.toLinAlgEquiv'.toLinearEquiv.toLinearMap
    (LinearMap.ker_eq_bot.mpr Matrix.toLinAlgEquiv'.injective)

variable {width height : ℕ} [NeZero width] [NeZero height]

/-- The actual primal toric-code torus vector with the two bond closures \((g,h)\).
The vertical seam carries \(U_g\) and the horizontal seam carries \(U_h\).
Source: SCP10, Definition 5.6, and arXiv:2011.12127, Appendix A,
equation `eq:app:tcode-rep-primal`. -/
def toricCodeTorusState (g h : ToricCodeGroup) :
    (TorusVertex width height →
      ToricCodeGroup × ToricCodeGroup × ToricCodeGroup × ToricCodeGroup) → ℂ :=
  torusGClosure toricCodeBondRep (quantumDoublePrimalTensor ToricCodeGroup) g h

private theorem isGInjective_toricCodePrimalTensor_bondRep :
    IsGInjective (torusLegRep toricCodeBondRep)
      (siteMap (quantumDoublePrimalTensor ToricCodeGroup)) := by
  rw [torusLegRep_toricCodeBondRep]
  exact isGIsometric_toricCodePrimalTensor.toIsGInjective

/-- The four actual primal toric-code closures are linearly independent on every
positive rectangular torus. This is the \(\mathbb Z_2\) independence assertion
of SCP10, Theorem 5.9; no parent-Hamiltonian spanning claim is included. -/
theorem linearIndependent_toricCodeTorusState :
    LinearIndependent ℂ (fun p : ToricCodeGroup × ToricCodeGroup =>
      toricCodeTorusState (width := width) (height := height) p.1 p.2) := by
  exact (IsGInjective.linearIndependent_torusGClosureClass_commuting_of_isSemiRegular
    isGInjective_toricCodePrimalTensor_bondRep isSemiRegular_toricCodeBondRep).comp
    (commutingPairConjugacyClassEquivOfCommGroup (A := ToricCodeGroup)).symm
    (commutingPairConjugacyClassEquivOfCommGroup (A := ToricCodeGroup)).symm.injective

/-- The span of the four actual primal toric-code torus closures has complex
dimension four. Source: the closure-count assertion of SCP10, Theorem 5.9,
specialized to \(\mathbb Z_2\). -/
theorem finrank_span_toricCodeTorusState :
    Module.finrank ℂ (Submodule.span ℂ (Set.range
      (fun p : ToricCodeGroup × ToricCodeGroup =>
        toricCodeTorusState (width := width) (height := height) p.1 p.2))) = 4 := by
  let e := commutingPairConjugacyClassEquivOfCommGroup (A := ToricCodeGroup)
  let F := fun C : CommutingPairConjugacyClass ToricCodeGroup =>
    torusGClosureClass (width := width) (height := height) toricCodeBondRep
      (quantumDoublePrimalTensor ToricCodeGroup)
      isGInjective_toricCodePrimalTensor_bondRep.invariant C.1
  change Module.finrank ℂ (Submodule.span ℂ (Set.range (F ∘ e.symm))) = 4
  rw [e.symm.surjective.range_comp,
    IsGInjective.finrank_span_torusGClosureClass_commuting_of_isSemiRegular
      isGInjective_toricCodePrimalTensor_bondRep isSemiRegular_toricCodeBondRep,
    card_commutingPairConjugacyClass_of_commGroup]
  norm_num [Nat.card_eq_fintype_card, ToricCodeGroup]

end TNLean.PEPS
