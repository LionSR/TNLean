/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.HermitianHelpers
import TNLean.Analysis.MatrixSqrt
import TNLean.Channel.PartialTrace
import TNLean.Channel.TensorMap
import TNLean.Channel.WolfProps

/-!
# A finite informationally complete family of effects

This file constructs a finite family of positive effects whose complex span is
the full matrix algebra.  The construction uses the four rank-one effects in
the polarization identity.

This is the finite separation device for the conditional states in Hayden,
Jozsa, Petz and Winter, arXiv:quant-ph/0304007v2, Theorem 6, lines 499--505.

## Main declarations

* `Matrix.ICEffectIndex`: indices for the finite effect family.
* `Matrix.informationallyCompleteEffect`: the effects.
* `Matrix.informationallyCompleteEffect_posSemidef`: every family member is
  positive semidefinite.
* `Matrix.informationallyCompleteEffect_le_one`: every family member is at most
  the identity.
* `Matrix.linearMap_eq_zero_of_apply_informationallyCompleteEffect_eq_zero`:
  vanishing on the family forces a linear map to vanish.
* `Matrix.eq_of_conditionalSlice_informationallyCompleteEffect_eq`: the
  conditional slices against the finite family separate bipartite matrices.
-/

open scoped ComplexOrder MatrixOrder Kronecker

namespace Matrix

variable {D : ℕ}

/-- Indices for a distinguished identity effect and the four polarization
effects for every ordered pair of coordinate vectors. -/
abbrev ICEffectIndex (D : ℕ) :=
  Unit ⊕ (Fin D × Fin D × Fin 4)

/-- The coordinate vector scaled by one half. -/
noncomputable def halfCoordinateVector (i : Fin D) : Fin D → ℂ :=
  (2 : ℂ)⁻¹ • Pi.single i 1

/-- The four scaled vectors used by the polarization identity. -/
noncomputable def informationallyCompleteVector
    (i j : Fin D) (t : Fin 4) : Fin D → ℂ :=
  halfCoordinateVector i +
    ![(1 : ℂ), -1, Complex.I, -Complex.I] t • halfCoordinateVector j

/-- A finite informationally complete family of positive effects.

The distinguished member is the identity.  Every other member is the
rank-one effect formed from one of the four scaled polarization vectors. -/
noncomputable def informationallyCompleteEffect
    (s : ICEffectIndex D) : Matrix (Fin D) (Fin D) ℂ :=
  match s with
  | Sum.inl _ => 1
  | Sum.inr ⟨i, j, t⟩ =>
      vecMulVec (informationallyCompleteVector i j t)
        (star (informationallyCompleteVector i j t))

/-- Every informationally complete effect is positive semidefinite. -/
theorem informationallyCompleteEffect_posSemidef
    (s : ICEffectIndex D) :
    (informationallyCompleteEffect s).PosSemidef := by
  rcases s with _ | ⟨i, j, t⟩
  · exact Matrix.PosSemidef.one
  · exact Matrix.posSemidef_vecMulVec_self_star _

/-- Every polarization vector has squared norm at most one. -/
theorem informationallyCompleteVector_sum_norm_sq_le_one
    (i j : Fin D) (t : Fin 4) :
    ∑ k, ‖informationallyCompleteVector i j t k‖ ^ 2 ≤ 1 := by
  let u : EuclideanSpace ℂ (Fin D) :=
    WithLp.toLp 2 (halfCoordinateVector i)
  let v : EuclideanSpace ℂ (Fin D) :=
    WithLp.toLp 2 (halfCoordinateVector j)
  let c : ℂ := ![(1 : ℂ), -1, Complex.I, -Complex.I] t
  rw [← EuclideanSpace.norm_sq_eq
    (WithLp.toLp 2 (informationallyCompleteVector i j t))]
  change ‖u + c • v‖ ^ 2 ≤ 1
  have hu : ‖u‖ = 1 / 2 := by
    change ‖(2 : ℂ)⁻¹ • PiLp.single 2 i 1‖ = 1 / 2
    rw [norm_smul, PiLp.norm_single]
    norm_num
  have hv : ‖v‖ = 1 / 2 := by
    change ‖(2 : ℂ)⁻¹ • PiLp.single 2 j 1‖ = 1 / 2
    rw [norm_smul, PiLp.norm_single]
    norm_num
  have hc : ‖c‖ = 1 := by
    fin_cases t <;> norm_num [c, Complex.normSq_apply]
  have hnorm : ‖u + c • v‖ ≤ 1 := by
    calc
      ‖u + c • v‖ ≤ ‖u‖ + ‖c • v‖ := norm_add_le _ _
      _ = 1 := by rw [norm_smul, hu, hv, hc]; norm_num
  nlinarith [norm_nonneg (u + c • v)]

/-- Every informationally complete effect is bounded above by the identity. -/
theorem informationallyCompleteEffect_le_one
    (s : ICEffectIndex D) :
    informationallyCompleteEffect s ≤ 1 := by
  rcases s with _ | ⟨i, j, t⟩
  · rfl
  · exact one_sub_vecMulVec_posSemidef_of_sum_normSq_le_one _
      (informationallyCompleteVector_sum_norm_sq_le_one i j t)

/-- A complex-linear map that vanishes on the informationally complete effects
vanishes everywhere. -/
theorem linearMap_eq_zero_of_apply_informationallyCompleteEffect_eq_zero
    {N : Type*} [AddCommGroup N] [Module ℂ N]
    (T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] N)
    (hT : ∀ s, T (informationallyCompleteEffect s) = 0) :
    T = 0 := by
  classical
  have hsingle (i j : Fin D) : T (Matrix.single i j 1) = 0 := by
    have hpolarization :=
      (WolfProps.vecMulVec_star_eq_polarization
        (halfCoordinateVector i) (halfCoordinateVector j))
    have h0 (t : Fin 4) :
        T (vecMulVec (informationallyCompleteVector i j t)
          (star (informationallyCompleteVector i j t))) = 0 := by
      simpa only [informationallyCompleteEffect] using
        hT (Sum.inr ⟨i, j, t⟩)
    have hleft :
        (4 : ℂ) •
            vecMulVec (halfCoordinateVector i) (star (halfCoordinateVector j)) =
          Matrix.single i j 1 := by
      ext a b
      by_cases hai : i = a
      · subst a
        by_cases hbj : j = b
        · subst b
          norm_num [halfCoordinateVector, Matrix.vecMulVec_apply, Matrix.single]
        · simp [halfCoordinateVector, Matrix.vecMulVec_apply,
            Matrix.single, hbj]
      · simp [halfCoordinateVector, Matrix.vecMulVec_apply,
          Matrix.single, hai]
    rw [hleft] at hpolarization
    have h0₀ : T (vecMulVec (halfCoordinateVector i + halfCoordinateVector j)
        (star (halfCoordinateVector i + halfCoordinateVector j))) = 0 := by
      simpa [informationallyCompleteVector] using h0 0
    have h0₁ : T (vecMulVec (halfCoordinateVector i - halfCoordinateVector j)
        (star (halfCoordinateVector i - halfCoordinateVector j))) = 0 := by
      simpa [informationallyCompleteVector, sub_eq_add_neg] using h0 1
    have h0₂ : T (vecMulVec
        (halfCoordinateVector i + Complex.I • halfCoordinateVector j)
        (star (halfCoordinateVector i + Complex.I • halfCoordinateVector j))) = 0 := by
      simpa [informationallyCompleteVector] using h0 2
    have h0₃ : T (vecMulVec
        (halfCoordinateVector i - Complex.I • halfCoordinateVector j)
        (star (halfCoordinateVector i - Complex.I • halfCoordinateVector j))) = 0 := by
      simpa [informationallyCompleteVector, sub_eq_add_neg] using h0 3
    rw [hpolarization, map_sub, map_add, map_sub, map_smul, map_smul,
      h0₀, h0₁, h0₂, h0₃]
    simp
  exact LinearMap.ext_on_range (Matrix.stdBasis ℂ (Fin D) (Fin D)).span_eq
    fun ⟨i, j⟩ ↦ by
      rw [Matrix.stdBasis_eq_single, hsingle]
      rfl

/-! ## Conditional-slice separation -/

variable {A B : ℕ}

/-- The subnormalized conditional slice obtained by testing the first factor
against `M`.

This is HJPW, arXiv:quant-ph/0304007v2, Theorem 6, lines 499--502:
`Tr_A(ρ_AB (M ⊗ 1))`. -/
noncomputable def conditionalSlice
    (ρ : Matrix (Fin A × Fin B) (Fin A × Fin B) ℂ)
    (M : Matrix (Fin A) (Fin A) ℂ) :
    Matrix (Fin B) (Fin B) ℂ :=
  fun k l ↦ ∑ i, ∑ j, ρ (i, k) (j, l) * M j i

/-- The entrywise conditional slice agrees with the partial-trace formula in
HJPW. -/
theorem conditionalSlice_eq_partialTraceLeft
    (ρ : Matrix (Fin A × Fin B) (Fin A × Fin B) ℂ)
    (M : Matrix (Fin A) (Fin A) ℂ) :
    conditionalSlice ρ M =
      partialTraceLeft (ρ * (M ⊗ₖ (1 : Matrix (Fin B) (Fin B) ℂ))) := by
  classical
  ext k l
  simp only [conditionalSlice, partialTraceLeft_apply, Matrix.mul_apply,
    Matrix.kroneckerMap_apply, Matrix.one_apply]
  simp_rw [Fintype.sum_prod_type]
  simp

/-- The left partial trace is cyclic with respect to an operator acting only
on the traced factor. -/
theorem partialTraceLeft_mul_kronecker_one_comm
    (X : Matrix (Fin A × Fin B) (Fin A × Fin B) ℂ)
    (M : Matrix (Fin A) (Fin A) ℂ) :
    partialTraceLeft (X * (M ⊗ₖ (1 : Matrix (Fin B) (Fin B) ℂ))) =
      partialTraceLeft ((M ⊗ₖ (1 : Matrix (Fin B) (Fin B) ℂ)) * X) := by
  classical
  ext k l
  simp only [partialTraceLeft_apply, Matrix.mul_apply,
    Matrix.kroneckerMap_apply, Matrix.one_apply]
  simp_rw [Fintype.sum_prod_type]
  simp only [mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  simp_rw [show ∀ x : Fin B, k = x ↔ x = k from fun x ↦ eq_comm]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  calc
    (∑ x, ∑ y, X (x, k) (y, l) * M y x) =
        ∑ x, ∑ y, M y x * X (x, k) (y, l) := by
      apply Finset.sum_congr rfl
      intro x _
      exact Finset.sum_congr rfl fun y _ ↦ mul_comm _ _
    _ = ∑ y, ∑ x, M y x * X (x, k) (y, l) := Finset.sum_comm

/-- A positive bipartite matrix has positive conditional slices against
positive effects. -/
theorem PosSemidef.conditionalSlice
    {ρ : Matrix (Fin A × Fin B) (Fin A × Fin B) ℂ}
    {M : Matrix (Fin A) (Fin A) ℂ}
    (hρ : ρ.PosSemidef) (hM : M.PosSemidef) :
    (conditionalSlice ρ M).PosSemidef := by
  let S := hM.isHermitian.cfc Real.sqrt
  let K := S ⊗ₖ (1 : Matrix (Fin B) (Fin B) ℂ)
  have hS : Sᴴ = S := hM.cfc_sqrt_isHermitian.eq
  have hSS : S * S = M := hM.cfc_sqrt_mul_self
  have hK : Kᴴ = K := by
    simp only [K, Matrix.conjTranspose_kronecker, hS, Matrix.conjTranspose_one]
  rw [conditionalSlice_eq_partialTraceLeft,
    partialTraceLeft_mul_kronecker_one_comm]
  have hMM :
      M ⊗ₖ (1 : Matrix (Fin B) (Fin B) ℂ) = K * K := by
    simp only [K, ← Matrix.mul_kronecker_mul, hSS, Matrix.one_mul]
  rw [hMM, Matrix.mul_assoc]
  rw [← partialTraceLeft_mul_kronecker_one_comm
    (X := K * ρ) (M := S)]
  simpa only [hK] using
    (hρ.mul_mul_conjTranspose_same K).partialTraceLeft

/-- The trace of a conditional slice is the probability of the tested
effect. -/
theorem trace_conditionalSlice
    (ρ : Matrix (Fin A × Fin B) (Fin A × Fin B) ℂ)
    (M : Matrix (Fin A) (Fin A) ℂ) :
    (conditionalSlice ρ M).trace =
      (ρ * (M ⊗ₖ (1 : Matrix (Fin B) (Fin B) ℂ))).trace := by
  rw [conditionalSlice_eq_partialTraceLeft, trace_partialTraceLeft]

/-- Conditional slicing is a finite linear combination of bipartite blocks. -/
theorem conditionalSlice_eq_sum_smul_bipartiteBlock
    (ρ : Matrix (Fin A × Fin B) (Fin A × Fin B) ℂ)
    (M : Matrix (Fin A) (Fin A) ℂ) :
    conditionalSlice ρ M =
      ∑ i, ∑ j, M j i • bipartiteBlock ρ i j := by
  classical
  ext k l
  simp only [conditionalSlice, Matrix.sum_apply, Matrix.smul_apply,
    bipartiteBlock_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- A linear map on the retained factor commutes with conditional slicing. -/
theorem map_conditionalSlice
    {C : ℕ}
    (T : Matrix (Fin B) (Fin B) ℂ →ₗ[ℂ] Matrix (Fin C) (Fin C) ℂ)
    (ρ : Matrix (Fin A × Fin B) (Fin A × Fin B) ℂ)
    (M : Matrix (Fin A) (Fin A) ℂ) :
    T (conditionalSlice ρ M) =
      conditionalSlice (idTensorMapLM (δ := Fin A) T ρ) M := by
  classical
  rw [conditionalSlice_eq_sum_smul_bipartiteBlock, map_sum]
  simp_rw [map_sum, map_smul]
  rw [conditionalSlice_eq_sum_smul_bipartiteBlock]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply congrArg (M j i • ·)
  ext k l
  simp [idTensorMapLM_apply, idTensorMap_apply]

/-- Conditional slicing as a complex-linear map in the tested effect. -/
noncomputable def conditionalSliceLM
    (ρ : Matrix (Fin A × Fin B) (Fin A × Fin B) ℂ) :
    Matrix (Fin A) (Fin A) ℂ →ₗ[ℂ] Matrix (Fin B) (Fin B) ℂ where
  toFun := conditionalSlice ρ
  map_add' := by
    intro M N
    ext k l
    simp [conditionalSlice, mul_add, Finset.sum_add_distrib]
  map_smul' := by
    intro c M
    ext k l
    simp only [conditionalSlice, Matrix.smul_apply, smul_eq_mul]
    change (∑ i, ∑ j, ρ (i, k) (j, l) * (c * M j i)) =
      (RingHom.id ℂ) c * (∑ i, ∑ j, ρ (i, k) (j, l) * M j i)
    have hterm (i j : Fin A) :
        ρ (i, k) (j, l) * (c * M j i) =
          c * (ρ (i, k) (j, l) * M j i) := by ring
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ ↦ hterm i j

@[simp]
theorem conditionalSliceLM_apply
    (ρ : Matrix (Fin A × Fin B) (Fin A × Fin B) ℂ)
    (M : Matrix (Fin A) (Fin A) ℂ) :
    conditionalSliceLM ρ M = conditionalSlice ρ M := rfl

/-- The finite informationally complete effects separate bipartite matrices by
their conditional slices.

This supplies the finite replacement for “varying `M`” in HJPW,
arXiv:quant-ph/0304007v2, Theorem 6, lines 499--505. -/
theorem eq_of_conditionalSlice_informationallyCompleteEffect_eq
    (X Y : Matrix (Fin A × Fin B) (Fin A × Fin B) ℂ)
    (h : ∀ s, conditionalSlice X (informationallyCompleteEffect s) =
      conditionalSlice Y (informationallyCompleteEffect s)) :
    X = Y := by
  classical
  let T := conditionalSliceLM (X - Y)
  have hT : ∀ s, T (informationallyCompleteEffect s) = 0 := by
    intro s
    change conditionalSlice (X - Y) (informationallyCompleteEffect s) = 0
    ext k l
    have hs := congrFun (congrFun (h s) k) l
    simpa [conditionalSlice, sub_mul, Finset.sum_sub_distrib] using sub_eq_zero.mpr hs
  have hTzero :=
    linearMap_eq_zero_of_apply_informationallyCompleteEffect_eq_zero T hT
  ext ⟨i, k⟩ ⟨j, l⟩
  have hentry := congrFun (congrFun
    (LinearMap.congr_fun hTzero (Matrix.single j i 1)) k) l
  change conditionalSlice (X - Y) (Matrix.single j i 1) k l = 0 at hentry
  simp only [conditionalSlice, Matrix.sub_apply, Matrix.single] at hentry
  change (∑ x, ∑ y, (X (x, k) (y, l) - Y (x, k) (y, l)) *
    (if j = y ∧ i = x then 1 else 0)) = 0 at hentry
  simp only [mul_ite, mul_one, mul_zero] at hentry
  have hsum :
      X (i, k) (j, l) - Y (i, k) (j, l) =
        ∑ x, ∑ y, if j = y ∧ i = x then
          X (x, k) (y, l) - Y (x, k) (y, l) else 0 := by
    have hinner (x : Fin A) :
        (∑ y, if j = y ∧ i = x then
          X (x, k) (y, l) - Y (x, k) (y, l) else 0) =
          if i = x then X (x, k) (j, l) - Y (x, k) (j, l) else 0 := by
      by_cases hix : i = x
      · subst x
        simp
      · simp [hix]
    simp_rw [hinner]
    simp
  rw [← hsum] at hentry
  exact sub_eq_zero.mp hentry

end Matrix
