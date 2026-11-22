/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Analysis.Topology.MatrixGroupJoined
import TNLean.MPS.MPU.Simple.VirtualSandwichBlocking
import TNLean.MPS.MPU.Index.BondPadding

/-!
# Paths of matrix product unitaries through gauges and padding

Two operations on matrix product unitary tensors keep every periodic operator
of length greater than one: a virtual gauge \(W\mapsto XWX^{-1}\) by an
invertible matrix, and adjoining unused bond directions. This file turns them
into statements about paths of MPU tensors.

* A tensor is joined to each of its virtual gauges by a path of MPU tensors,
  namely \(t\mapsto X(t)WX(t)^{-1}\) for a path \(X(t)\) of invertible matrices
  from the identity to \(X\).
* Adjoining unused bond directions, or relabelling the physical legs, carries a
  path of MPU tensors to a path of MPU tensors.

These are the bookkeeping steps that connect a tensor to its standard form in
the proof of arXiv:1703.09188, Theorem `IndexTh` (iv), lines 857--865.
-/

open scoped Matrix

namespace MPOTensor

variable {d D : ℕ}

/-- **A tensor is joined to each of its virtual gauges through MPU tensors.**
For an MPU tensor \(W\) and an invertible bond matrix \(X\), the gauge
\(XWX^{-1}\) is joined to \(W\) by the path \(t\mapsto X(t)WX(t)^{-1}\), where
\(X(t)\) is a path of invertible matrices from the identity to \(X\).

Source: the gauge freedom of arXiv:1703.09188, lines 294 and 356, used in the
proof of Theorem `IndexTh` (iv), lines 857--865. -/
theorem IsMPU.joinedIn_virtualSandwich {W : MPOTensor d D} (hW : IsMPU W)
    {X : Matrix (Fin D) (Fin D) ℂ} (hX : IsUnit X.det) :
    JoinedIn {V : MPOTensor d D | IsMPU V} W (MPOTensor.virtualSandwich X W X⁻¹) := by
  obtain ⟨γ, hγ⟩ := Matrix.joinedIn_isUnit_det_one hX
  have hdet : ∀ t, (γ t).det ≠ 0 := fun t ↦ (hγ t).ne_zero
  have hinv : Continuous fun t ↦ (γ t)⁻¹ := by
    simp_rw [Matrix.inv_def, Ring.inverse_eq_inv']
    exact ((γ.continuous.matrix_det).inv₀ hdet).smul γ.continuous.matrix_adjugate
  have hcont : Continuous fun t ↦ MPOTensor.virtualSandwich (γ t) W (γ t)⁻¹ := by
    refine continuous_pi fun i ↦ continuous_pi fun j ↦ ?_
    simp only [virtualSandwich_apply]
    exact (γ.continuous.matrix_mul continuous_const).matrix_mul hinv
  refine ⟨⟨⟨fun t ↦ MPOTensor.virtualSandwich (γ t) W (γ t)⁻¹, hcont⟩, ?_, ?_⟩, fun t ↦ ?_⟩
  · funext i j
    simp
  · simp
  · exact hW.virtualSandwich _ _ (Matrix.nonsing_inv_mul _ (hγ t))

/-- Adjoining unused bond directions depends continuously on the tensor. -/
theorem continuous_padBond (D' : ℕ) (h : D ≤ D') :
    Continuous fun W : MPOTensor d D ↦ padBond W D' h := by
  refine continuous_pi fun i ↦ continuous_pi fun j ↦ ?_
  exact (continuous_const.matrix_mul
    ((continuous_apply j).comp (continuous_apply i))).matrix_mul continuous_const

/-- **Adjoining unused bond directions carries paths of MPU tensors to paths of
MPU tensors.**

Source: the bond-dimension convention for strict equivalence,
arXiv:1703.09188, lines 708--714; see
`docs/paper-gaps/mpu_equivalence_fixed_bond.tex`. -/
theorem JoinedIn.padBond {W V : MPOTensor d D}
    (hWV : JoinedIn {X : MPOTensor d D | IsMPU X} W V) (D' : ℕ) (h : D ≤ D') :
    JoinedIn {X : MPOTensor d D' | IsMPU X} (padBond W D' h) (padBond V D' h) := by
  obtain ⟨γ, hγ⟩ := hWV
  exact ⟨γ.map (continuous_padBond D' h), fun t ↦ (hγ t).padBond D' h⟩

/-- Relabelling the physical legs carries paths of MPU tensors to paths of MPU
tensors. -/
theorem JoinedIn.reindexPhysical {d' : ℕ} (e : Fin d' ≃ Fin d) {W V : MPOTensor d D}
    (hWV : JoinedIn {X : MPOTensor d D | IsMPU X} W V) :
    JoinedIn {X : MPOTensor d' D | IsMPU X}
      (MPOTensor.reindexPhysical e W) (MPOTensor.reindexPhysical e V) := by
  obtain ⟨γ, hγ⟩ := hWV
  have hc : Continuous fun X : MPOTensor d D ↦ MPOTensor.reindexPhysical e X :=
    continuous_pi fun i ↦ continuous_pi fun j ↦
      (continuous_apply (e j)).comp (continuous_apply (e i))
  exact ⟨γ.map hc, fun t ↦ (hγ t).reindexPhysical e⟩

/-- Adjoining unused bond directions in two steps is adjoining them at once. -/
theorem padBond_padBond (W : MPOTensor d D) {D₁ D₂ : ℕ} (h₁ : D ≤ D₁) (h₂ : D₁ ≤ D₂) :
    padBond (padBond W D₁ h₁) D₂ h₂ = padBond W D₂ (h₁.trans h₂) := by
  have hcomp : bondInclusion D₁ D₂ h₂ * bondInclusion D D₁ h₁ =
      bondInclusion D D₂ (h₁.trans h₂) := by
    ext a b
    simp only [bondInclusion, Matrix.mul_apply, Matrix.of_apply]
    by_cases hab : (a : ℕ) = b
    · rw [Finset.sum_eq_single ⟨b, by omega⟩]
      · simp [hab]
      · intro c _ hc
        have : (c : ℕ) ≠ b := fun e ↦ hc (Fin.ext e)
        simp [this]
      · simp
    · simp only [hab, ite_false]
      apply Finset.sum_eq_zero
      intro c _
      by_cases hc : (c : ℕ) = b
      · have : (a : ℕ) ≠ c := by omega
        simp [this]
      · simp [hc]
  funext i j
  simp only [padBond, ← Matrix.mul_assoc]
  rw [hcomp, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.conjTranspose_mul, hcomp,
    Matrix.mul_assoc]

end MPOTensor
