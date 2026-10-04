/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Defs
import QICLean.Algebra.SkolemNoether
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Matrix realization from a framed principal left ideal

A finite-dimensional complex algebra identified pointwise with a full matrix algebra can be
represented on a principal left ideal of the defining matrix dimension. A supplied frame and
left inverse give explicit matrices for this representation. The representation is an inner
conjugate of the pointwise identification, and therefore preserves its trace.

This is an algebraic auxiliary result towards reconstruction from finite-ring trace data,
motivated by arXiv:1010.3732, Section II.F.2, lines 953–993 of the local source. The frame and its
left inverse are supplied. Their continuous construction is separate; no continuous choice of
the pointwise matrix-algebra identification is required. No physical-gap implication or
varying-rank phase invariance is asserted here.

The inner-conjugacy and matrix-algebra equivalence statements concern positive matrix dimension.
Idempotence of the element defining the ideal is unnecessary for these algebraic statements.
-/

set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option linter.mathlibStandardSet true
open scoped Matrix BigOperators

namespace Matrix

/-- Left multiplication represented in a supplied frame with a left inverse. -/
noncomputable def leftIdealFrameAction {r D : ℕ}
    (μ : (Fin r → ℂ) →ₗ[ℂ] (Fin r → ℂ) →ₗ[ℂ] (Fin r → ℂ))
    (J : (Fin D → ℂ) →ₗ[ℂ] (Fin r → ℂ))
    (H : (Fin r → ℂ) →ₗ[ℂ] (Fin D → ℂ)) :
    (Fin r → ℂ) →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ :=
  LinearMap.toMatrix'.toLinearMap.comp ((μ.compl₂ J).compr₂ H)

/-- Evaluation of the matrix representing framed left multiplication. -/
theorem leftIdealFrameAction_mulVec {r D : ℕ}
    (μ : (Fin r → ℂ) →ₗ[ℂ] (Fin r → ℂ) →ₗ[ℂ] (Fin r → ℂ))
    (J : (Fin D → ℂ) →ₗ[ℂ] (Fin r → ℂ))
    (H : (Fin r → ℂ) →ₗ[ℂ] (Fin D → ℂ)) (x : Fin r → ℂ) (v : Fin D → ℂ) :
    leftIdealFrameAction μ J H x *ᵥ v = H (μ x (J v)) := by
  simp only [leftIdealFrameAction, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearMap.toMatrix'_mulVec, LinearMap.compr₂_apply, LinearMap.compl₂_apply]

/-- A frame spanning a principal left ideal intertwines its framed action
with the original left multiplication. -/
theorem leftIdealFrameAction_intertwines {r D : ℕ}
    (μ : (Fin r → ℂ) →ₗ[ℂ] (Fin r → ℂ) →ₗ[ℂ] (Fin r → ℂ))
    (hAssoc : ∀ x y z, μ (μ x y) z = μ x (μ y z)) (p : Fin r → ℂ)
    (J : (Fin D → ℂ) →ₗ[ℂ] (Fin r → ℂ))
    (H : (Fin r → ℂ) →ₗ[ℂ] (Fin D → ℂ)) (hHJ : H.comp J = LinearMap.id)
    (hRange : LinearMap.range J = LinearMap.range (μ.flip p)) :
    ∀ x v, J (leftIdealFrameAction μ J H x *ᵥ v) = μ x (J v) := by
  intro x v
  obtain ⟨y, hy⟩ : J v ∈ LinearMap.range (μ.flip p) :=
    hRange ▸ (show J v ∈ LinearMap.range J from ⟨v, rfl⟩)
  change μ y p = J v at hy
  have hmem : μ x (J v) ∈ LinearMap.range J := by
    rw [hRange]
    exact ⟨μ x y, by simp only [LinearMap.flip_apply, hAssoc, hy]⟩
  obtain ⟨w, hw⟩ := hmem
  rw [leftIdealFrameAction_mulVec, ← hw]
  simpa only [LinearMap.comp_apply, LinearMap.id_apply]
    using congrArg (fun f => J (f w)) hHJ

/-- A D-dimensional faithful frame of a left action realizes the quotient
matrix algebra by a bond gauge. The frame intertwining is supplied here;
its derivation from an invariant minimal left ideal is separate. -/
theorem exists_inner_of_framed_leftAction {r D : ℕ} [NeZero D]
    (μ : (Fin r → ℂ) →ₗ[ℂ] (Fin r → ℂ) →ₗ[ℂ] (Fin r → ℂ))
    (E : (Fin r → ℂ) ≃ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (hE : ∀ x y, E (μ x y) = E x * E y)
    (J : (Fin D → ℂ) →ₗ[ℂ] (Fin r → ℂ)) (hJ : Function.Injective J)
    (L : (Fin r → ℂ) →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (hAction : ∀ x v, J (L x *ᵥ v) = μ x (J v)) :
    ∃ X : GL (Fin D) ℂ, ∀ x,
      L x = (X : Matrix (Fin D) (Fin D) ℂ) * E x *
        ((X⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) := by
  let : Mul (Fin r → ℂ) := ⟨fun x y => μ x y⟩
  let : Semigroup (Fin r → ℂ) := E.injective.semigroup E hE
  have hAssoc : ∀ x y z, μ (μ x y) z = μ x (μ y z) := mul_assoc
  have hMul : ∀ x y, L (μ x y) = L x * L y := by
    intro x y
    apply Matrix.toLin'.injective
    apply LinearMap.ext
    intro v
    apply hJ
    simp only [Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, hAction, hAssoc]
  let : One (Fin r → ℂ) := ⟨E.symm 1⟩
  let : MulOneClass (Fin r → ℂ) :=
    E.injective.mulOneClass E (E.apply_symm_apply 1) hE
  have hUnit : ∀ x, μ (E.symm 1) x = x := one_mul
  have hOne : L (E.symm 1) = 1 := by
    apply Matrix.toLin'.injective
    apply LinearMap.ext
    intro v
    apply hJ
    simp only [Matrix.toLin'_apply, hAction, hUnit, Matrix.one_mulVec]
  let T := L.comp E.symm.toLinearMap
  have hTMul : ∀ M N, T (M * N) = T M * T N := by
    intro M N
    have hInv : μ (E.symm M) (E.symm N) = E.symm (M * N) := E.injective (by
      simp only [hE, E.apply_symm_apply])
    change L (E.symm (M * N)) = L (E.symm M) * L (E.symm N)
    rw [← hInv, hMul]
  obtain ⟨X, hX⟩ := Matrix.exists_inner_of_linear_mul_endomorphism T hTMul
    (Matrix.linearMap_ne_zero_of_map_one T hOne)
  exact ⟨X, fun x => by
    simpa only [T, LinearMap.comp_apply, LinearEquiv.coe_coe, E.symm_apply_apply]
      using hX (E x)⟩

/-- A full frame of a D-dimensional principal left ideal realizes the full
matrix algebra by the explicit framed action. -/
theorem exists_inner_of_leftIdealFrame {r D : ℕ} [NeZero D]
    (μ : (Fin r → ℂ) →ₗ[ℂ] (Fin r → ℂ) →ₗ[ℂ] (Fin r → ℂ))
    (E : (Fin r → ℂ) ≃ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (hE : ∀ x y, E (μ x y) = E x * E y) (p : Fin r → ℂ)
    (J : (Fin D → ℂ) →ₗ[ℂ] (Fin r → ℂ))
    (H : (Fin r → ℂ) →ₗ[ℂ] (Fin D → ℂ)) (hHJ : H.comp J = LinearMap.id)
    (hRange : LinearMap.range J = LinearMap.range (μ.flip p)) :
    ∃ X : GL (Fin D) ℂ, ∀ x,
      leftIdealFrameAction μ J H x = (X : Matrix (Fin D) (Fin D) ℂ) * E x *
        ((X⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) := by
  let : Mul (Fin r → ℂ) := ⟨fun x y => μ x y⟩
  let : Semigroup (Fin r → ℂ) := E.injective.semigroup E hE
  exact exists_inner_of_framed_leftAction μ E hE J
    (LinearMap.injective_of_comp_eq_id J H hHJ) (leftIdealFrameAction μ J H)
    (leftIdealFrameAction_intertwines μ mul_assoc
      p J H hHJ hRange)

/-- The framed left-ideal action is a multiplicative linear equivalence and
preserves the trace determined by any pointwise matrix-algebra identification. -/
theorem exists_linearEquiv_leftIdealFrameAction {r D : ℕ} [NeZero D]
    (μ : (Fin r → ℂ) →ₗ[ℂ] (Fin r → ℂ) →ₗ[ℂ] (Fin r → ℂ))
    (E : (Fin r → ℂ) ≃ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (hE : ∀ x y, E (μ x y) = E x * E y) (p : Fin r → ℂ)
    (J : (Fin D → ℂ) →ₗ[ℂ] (Fin r → ℂ))
    (H : (Fin r → ℂ) →ₗ[ℂ] (Fin D → ℂ)) (hHJ : H.comp J = LinearMap.id)
    (hRange : LinearMap.range J = LinearMap.range (μ.flip p)) :
    ∃ Θ : (Fin r → ℂ) ≃ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ,
      (∀ x, Θ x = leftIdealFrameAction μ J H x) ∧
      (∀ x y, Θ (μ x y) = Θ x * Θ y) ∧
      (∀ x, Matrix.trace (Θ x) = Matrix.trace (E x)) := by
  obtain ⟨X, hX⟩ := exists_inner_of_leftIdealFrame μ E hE p J H hHJ hRange
  let Θ := (E.trans (Units.mulLeftLinearEquiv ℂ (Matrix (Fin D) (Fin D) ℂ) X)).trans
    (Units.mulRightLinearEquiv ℂ X⁻¹)
  have hΘ : ∀ x, Θ x = leftIdealFrameAction μ J H x := by
    intro x
    simpa only [Θ, LinearEquiv.trans_apply, Units.mulLeftLinearEquiv_apply,
      Units.mulRightLinearEquiv_apply] using (hX x).symm
  refine ⟨Θ, hΘ, ?_, ?_⟩
  · intro x y
    simp [Θ, hE, Matrix.mul_assoc]
  · intro x
    rw [hΘ, hX]
    exact Matrix.trace_units_conj X (E x)

end Matrix

namespace MPSTensor

/-- Evaluating letters in a framed principal left ideal preserves their tensor gauge class.
The letters are compared with their supplied pointwise matrix-algebra identification; no
claim about all positive-length vectors of an unrelated ambient tensor is made. -/
theorem gaugeEquiv_leftIdealFrameAction {d r D : ℕ} [NeZero D]
    (μ : (Fin r → ℂ) →ₗ[ℂ] (Fin r → ℂ) →ₗ[ℂ] (Fin r → ℂ))
    (E : (Fin r → ℂ) ≃ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (hE : ∀ x y, E (μ x y) = E x * E y) (p : Fin r → ℂ)
    (J : (Fin D → ℂ) →ₗ[ℂ] (Fin r → ℂ))
    (H : (Fin r → ℂ) →ₗ[ℂ] (Fin D → ℂ)) (hHJ : H.comp J = LinearMap.id)
    (hRange : LinearMap.range J = LinearMap.range (μ.flip p)) (v : Fin d → Fin r → ℂ) :
    GaugeEquiv (fun i => E (v i)) (fun i => Matrix.leftIdealFrameAction μ J H (v i)) := by
  obtain ⟨X, hX⟩ := Matrix.exists_inner_of_leftIdealFrame μ E hE p J H hHJ hRange
  exact ⟨X, fun i => hX (v i)⟩

end MPSTensor
