/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Analysis.NeumannInverse
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Range projectors of injective finite-dimensional maps

For an injective map \(T\) with finite-dimensional Hilbert domain and complete
Hilbert codomain, this file develops the inverse Gram operator
\((T^\dagger T)^{-1}\), identifies it with the canonical and ring inverses, and
records the range-projector formula
\[
  P_{\operatorname{ran} T}=T(T^\dagger T)^{-1}T^\dagger.
\]
It also derives the quantitative bound
\(\lVert(T^\dagger T)^{-1}\rVert\le(1-a)^{-1}\) from
\(\lVert 1-T^\dagger T\rVert\le a<1\).
-/


namespace ContinuousLinearMap

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- The continuous inverse of the Gram endomorphism of an injective
finite-dimensional continuous linear map. -/
noncomputable def inverseGram (T : E →L[𝕜] F) (hT : Function.Injective T) : E →L[𝕜] E :=
  LinearMap.toContinuousLinearMap <|
    (LinearEquiv.ofInjectiveEndo (T.adjoint.comp T).toLinearMap
      ((T.adjoint_comp_self_injective_iff).2 hT)).symm.toLinearMap

/-- The inverse Gram operator is a left inverse of the Gram operator. -/
@[simp]
theorem inverseGram_comp_adjoint_comp_self (T : E →L[𝕜] F)
    (hT : Function.Injective T) :
    (inverseGram T hT).comp (T.adjoint.comp T) = ContinuousLinearMap.id 𝕜 E := by
  ext x
  exact (LinearEquiv.ofInjectiveEndo (T.adjoint.comp T).toLinearMap
    ((T.adjoint_comp_self_injective_iff).2 hT)).symm_apply_apply x

/-- The inverse Gram operator is a right inverse of the Gram operator. -/
@[simp]
theorem adjoint_comp_self_comp_inverseGram (T : E →L[𝕜] F)
    (hT : Function.Injective T) :
    (T.adjoint.comp T).comp (inverseGram T hT) = ContinuousLinearMap.id 𝕜 E := by
  ext x
  exact (LinearEquiv.ofInjectiveEndo (T.adjoint.comp T).toLinearMap
    ((T.adjoint_comp_self_injective_iff).2 hT)).apply_symm_apply x

/-- The inverse Gram operator agrees with the inverse operation on continuous linear maps. -/
theorem inverseGram_eq_inverse (T : E →L[𝕜] F) (hT : Function.Injective T) :
    inverseGram T hT = (T.adjoint.comp T).inverse := by
  symm
  exact ContinuousLinearMap.inverse_eq
    (adjoint_comp_self_comp_inverseGram T hT)
    (inverseGram_comp_adjoint_comp_self T hT)

/-- The inverse Gram operator agrees with the ring-theoretic inverse. -/
theorem inverseGram_eq_ringInverse (T : E →L[𝕜] F) (hT : Function.Injective T) :
    inverseGram T hT = Ring.inverse (T.adjoint.comp T) := by
  rw [ContinuousLinearMap.ringInverse_eq_inverse]
  exact inverseGram_eq_inverse T hT

/-- If the Gram operator is within norm \(a<1\) of the identity, then its inverse
has norm at most \((1-a)^{-1}\). The denominator is the Neumann inverse bound. -/
theorem norm_inverseGram_le_of_norm_one_sub_adjoint_comp_self_le
    (T : E →L[𝕜] F) (hT : Function.Injective T) {a : ℝ}
    (ha : ‖1 - T.adjoint.comp T‖ ≤ a) (ha_lt_one : a < 1) :
    ‖inverseGram T hT‖ ≤ (1 - a)⁻¹ := by
  cases subsingleton_or_nontrivial E with
  | inl hE =>
      letI : Subsingleton E := hE
      have hzero : inverseGram T hT = 0 := Subsingleton.elim _ _
      rw [hzero, norm_zero]
      exact inv_nonneg.mpr (sub_nonneg.mpr ha_lt_one.le)
  | inr hE =>
      letI : Nontrivial E := hE
      rw [inverseGram_eq_ringInverse]
      simpa only [sub_sub_cancel] using
        NormedRing.norm_inverse_one_sub_le (1 - T.adjoint.comp T) ha ha_lt_one

/-- The inverse Gram operator is symmetric (and hence self-adjoint).
This follows from `(T^† T) ∘ V = id` and self-adjointness of `T^† T`. -/
theorem inverseGram_isSymmetric (T : E →L[𝕜] F) (hT : Function.Injective T) :
    ((inverseGram T hT : E →L[𝕜] E) : E →ₗ[𝕜] E).IsSymmetric := by
  have h_gram_adj : (T.adjoint.comp T).adjoint = T.adjoint.comp T := by
    calc
      (T.adjoint.comp T).adjoint = (T.adjoint ∘L T).adjoint := rfl
      _ = T.adjoint ∘L (T.adjoint).adjoint := by rw [adjoint_comp]
      _ = T.adjoint ∘L T := by rw [adjoint_adjoint]
      _ = T.adjoint.comp T := rfl
  have h_right_inv : (T.adjoint.comp T).comp (inverseGram T hT) =
      ContinuousLinearMap.id 𝕜 E := adjoint_comp_self_comp_inverseGram T hT
  intro x y
  calc
    inner 𝕜 ((inverseGram T hT) x) y =
        inner 𝕜 ((inverseGram T hT) x)
          (((T.adjoint.comp T).comp (inverseGram T hT)) y) := by
      rw [h_right_inv, ContinuousLinearMap.id_apply]
    _ = inner 𝕜 ((inverseGram T hT) x)
        ((T.adjoint.comp T) ((inverseGram T hT) y)) := rfl
    _ = inner 𝕜 ((T.adjoint.comp T).adjoint ((inverseGram T hT) x))
        ((inverseGram T hT) y) := by rw [adjoint_inner_left]
    _ = inner 𝕜 ((T.adjoint.comp T) ((inverseGram T hT) x))
        ((inverseGram T hT) y) := by rw [h_gram_adj]
    _ = inner 𝕜 x ((inverseGram T hT) y) := by
      have : (T.adjoint.comp T) ((inverseGram T hT) x) = x := by
        calc
          (T.adjoint.comp T) ((inverseGram T hT) x) =
              ((T.adjoint.comp T).comp (inverseGram T hT)) x := rfl
          _ = (ContinuousLinearMap.id 𝕜 E) x := by rw [h_right_inv]
          _ = x := rfl
      rw [this]

/-- The exact norm identity for the composition `T ∘ (T^†T)⁻¹`.
For an injective map `T` on a finite-dimensional complex Hilbert space,
`‖T (T^†T)⁻¹‖ = √‖(T^†T)⁻¹‖`. This is an exact equality, not an inequality.
The proof uses the C*-identity, self-adjointness of the inverse Gram operator,
and the defining inverse relations. -/
theorem norm_T_comp_inverseGram_eq_sqrt (T : E →L[𝕜] F) (hT : Function.Injective T) :
    ‖T.comp (inverseGram T hT)‖ = Real.sqrt ‖inverseGram T hT‖ := by
  have h_sa_adj : (inverseGram T hT).adjoint = inverseGram T hT :=
    (inverseGram_isSymmetric T hT).isSelfAdjoint.adjoint_eq
  set S := T.comp (inverseGram T hT) with hS
  have hS_adj : S.adjoint = (inverseGram T hT).adjoint.comp T.adjoint :=
    adjoint_comp _ _
  have h_sq : ‖S‖ ^ 2 = ‖inverseGram T hT‖ := by
    calc
      ‖S‖ ^ 2 = ‖S‖ * ‖S‖ := by ring
      _ = ‖S.adjoint.comp S‖ := by rw [norm_adjoint_comp_self S]
      _ = ‖(((inverseGram T hT).adjoint).comp T.adjoint).comp S‖ := by rw [hS_adj]
      _ = ‖((inverseGram T hT).comp T.adjoint).comp
            (T.comp (inverseGram T hT))‖ := by rw [h_sa_adj]
      _ = ‖(inverseGram T hT).comp
            ((T.adjoint.comp T).comp (inverseGram T hT))‖ := by
        simp [ContinuousLinearMap.comp_assoc]
      _ = ‖(inverseGram T hT).comp (ContinuousLinearMap.id 𝕜 E)‖ := by
        rw [adjoint_comp_self_comp_inverseGram T hT]
      _ = ‖inverseGram T hT‖ := by simp
  have h_nonneg : 0 ≤ ‖S‖ := norm_nonneg _
  calc
    ‖S‖ = Real.sqrt (‖S‖ ^ 2) := by rw [Real.sqrt_sq h_nonneg]
    _ = Real.sqrt ‖inverseGram T hT‖ := by rw [h_sq]

/-- The adjoint version of the norm identity.
For an injective map `T` on a finite-dimensional complex Hilbert space,
`‖(T^†T)⁻¹ T^†‖ = √‖(T^†T)⁻¹‖`.
Derived from the previous theorem via `norm_adjoint`. -/
theorem norm_inverseGram_comp_adjoint_eq_sqrt (T : E →L[𝕜] F) (hT : Function.Injective T) :
    ‖(inverseGram T hT).comp T.adjoint‖ = Real.sqrt ‖inverseGram T hT‖ := by
  have h_sa_adj : (inverseGram T hT).adjoint = inverseGram T hT :=
    (inverseGram_isSymmetric T hT).isSelfAdjoint.adjoint_eq
  have h_norm_adj : ‖(T.comp (inverseGram T hT)).adjoint‖ =
      ‖T.comp (inverseGram T hT)‖ :=
    LinearIsometryEquiv.norm_map (adjoint (𝕜 := 𝕜) (E := E) (F := F)) _
  calc
    ‖(inverseGram T hT).comp T.adjoint‖ =
        ‖(T.comp (inverseGram T hT)).adjoint‖ := by
      rw [adjoint_comp, h_sa_adj]
    _ = ‖T.comp (inverseGram T hT)‖ := by rw [h_norm_adj]
    _ = Real.sqrt ‖inverseGram T hT‖ := norm_T_comp_inverseGram_eq_sqrt T hT

/-- The continuous range projector written through the inverse Gram operator. -/
noncomputable def injectiveRangeProjector (T : E →L[𝕜] F)
    (hT : Function.Injective T) : F →L[𝕜] F :=
  T.comp ((inverseGram T hT).comp T.adjoint)

/-- The continuous inverse-Gram formula is exactly the orthogonal projector
onto the range of an injective finite-dimensional map. -/
theorem injectiveRangeProjector_eq_starProjection (T : E →L[𝕜] F)
    (hT : Function.Injective T) :
    injectiveRangeProjector T hT = T.range.starProjection := by
  ext x
  symm
  apply Submodule.eq_starProjection_of_mem_orthogonal
  · exact ⟨inverseGram T hT (T.adjoint x), rfl⟩
  · rw [Submodule.mem_orthogonal']
    intro _ hy
    obtain ⟨y, rfl⟩ := hy
    change inner 𝕜 (x - injectiveRangeProjector T hT x) (T y) = 0
    rw [← T.adjoint_inner_left y (x - injectiveRangeProjector T hT x)]
    suffices T.adjoint (x - injectiveRangeProjector T hT x) = 0 by rw [this, inner_zero_left]
    rw [map_sub, injectiveRangeProjector, comp_apply, comp_apply]
    change T.adjoint x - (T.adjoint.comp T)
      (inverseGram T hT (T.adjoint x)) = 0
    have hGram :
        (T.adjoint.comp T) (inverseGram T hT (T.adjoint x)) = T.adjoint x := by
      change ((T.adjoint.comp T).comp (inverseGram T hT)) (T.adjoint x) = T.adjoint x
      rw [adjoint_comp_self_comp_inverseGram]
      rfl
    rw [hGram, sub_self]

/-- Exact residual identity for three injective maps with a common factorization.
If \(C=T\circ J₁=L\circ J₂\), the difference of the range projectors of \(T\) and \(L\),
after composition, factors through the mixed-Gram residual
\[
  T^†L-(T^†T)J₁(C^†C)^{-1}J₂^†(L^†L).
\]
This identity is purely algebraic and does not assert a norm bound. -/
theorem injectiveRangeProjector_comp_sub_of_factorizations
    {G H : Type*}
    [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [FiniteDimensional 𝕜 G]
      [CompleteSpace G]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [FiniteDimensional 𝕜 H]
      [CompleteSpace H]
    (T : E →L[𝕜] F) (L : G →L[𝕜] F) (C : H →L[𝕜] F)
    (J₁ : H →L[𝕜] E) (J₂ : H →L[𝕜] G)
    (hT : Function.Injective T) (hL : Function.Injective L)
    (hC : Function.Injective C)
    (hTC : T.comp J₁ = C) (hLC : L.comp J₂ = C) :
    (injectiveRangeProjector T hT).comp (injectiveRangeProjector L hL) -
        injectiveRangeProjector C hC =
      T.comp ((inverseGram T hT).comp
        ((T.adjoint.comp L -
          (T.adjoint.comp T).comp (J₁.comp ((inverseGram C hC).comp
            (J₂.adjoint.comp (L.adjoint.comp L))))).comp
          ((inverseGram L hL).comp L.adjoint))) := by
  have hLCadj : J₂.adjoint.comp L.adjoint = C.adjoint := by
    rw [← ContinuousLinearMap.adjoint_comp, hLC]
  have hTGram (x : E) :
      inverseGram T hT (T.adjoint (T x)) = x := by
    exact congrArg (fun Q : E →L[𝕜] E => Q x)
      (inverseGram_comp_adjoint_comp_self T hT)
  have hLGram (x : G) :
      L.adjoint (L (inverseGram L hL x)) = x := by
    exact congrArg (fun Q : G →L[𝕜] G => Q x)
      (adjoint_comp_self_comp_inverseGram L hL)
  have hsecond :
      T.comp ((inverseGram T hT).comp
        (((T.adjoint.comp T).comp (J₁.comp ((inverseGram C hC).comp
          (J₂.adjoint.comp (L.adjoint.comp L))))).comp
            ((inverseGram L hL).comp L.adjoint))) =
        C.comp ((inverseGram C hC).comp C.adjoint) := by
    ext x
    simp only [comp_apply, hTGram, hLGram]
    rw [show J₂.adjoint (L.adjoint x) = C.adjoint x by
      exact congrArg (fun Q : F →L[𝕜] H => Q x) hLCadj]
    exact congrArg (fun Q : H →L[𝕜] F =>
      Q (inverseGram C hC (C.adjoint x))) hTC
  rw [injectiveRangeProjector, injectiveRangeProjector, injectiveRangeProjector]
  simp only [comp_sub, sub_comp]
  rw [hsecond]
  simp only [comp_assoc]

end ContinuousLinearMap
