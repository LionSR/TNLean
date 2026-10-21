/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Analysis.PureStateTraceDistance
import QICLean.Entropy.FiniteProductContinuity
import QICLean.Entropy.FiniteProductInformation

/-!
# The final entropy comparison of the amplification proposition

The proof of the amplification proposition ends with a local unitary `U'` that moves
the original state `φ` to within `δ` of a vector `η` whose joint reduction on two
regions `X, J` is a product. Because `U'` acts on neither `X` nor `J`, the joint
reduction of `U' φ` on `X ∪ J` is that of `φ`. Continuity of the mutual information
with the dimension of `X` alone then gives
`I_φ(X : J) ≤ 8 √δ log(e dim X)`. With `δ ≤ C n^(-K/2)` and `log dim X ≤ C n²` this is
at most a constant times `n^(2-K/4)`, and the source's choice `K ≥ 4(M + 3)` makes it
at most a constant times `n^(-M)`.

The regions and the local dimensions are arbitrary, so ancillary systems are
included by enlarging the site set. The state `φ` may be entangled with every other
system, and only the dimension of `X` enters.

## Main statements

* `traceDistance_vecMulVec_le_norm_sub`: the trace distance of two pure states is at
  most the distance of the unit vectors.
* `FiniteProduct.reducedPure_unitary_compl`: a unitary on the complement of a region
  leaves the reduced state of that region unchanged.
* `FiniteProduct.mutualInformation_le_of_unitary_sub_le`: the comparison
  `I_φ(X : J) ≤ 8 √δ log(e dim X)`.
* `FiniteProduct.mutualInformation_le_inv_pow_of_unitary_sub_le`: the bound
  `C n^(-M)` of `eq:amplification-output` for every subset of `X`, from
  `K ≥ 4(M + 2)`, which the source's choice `K ≥ 4(M + 3)` satisfies.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*, September 24,
  2026, proof of Proposition 10.2 (`prop:amplification`), `09-amplification.tex`,
  lines 547–561, and Lemma 2.1 (`lem:continuity`), `01-preliminaries.tex`,
  lines 33–46 and 76–77, revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

Independently formalized from the manuscript; no upstream Lean proof text is reused.
-/

open Matrix
open scoped Kronecker InnerProductSpace ComplexOrder MatrixOrder

namespace TNLean.Lattice

/-- The trace distance of two pure states is at most the distance of the unit
vectors representing them.
Source: `01-preliminaries.tex`, lines 76–77. -/
theorem traceDistance_vecMulVec_le_norm_sub {n : Type*} [Fintype n] [DecidableEq n]
    {ψ φ : EuclideanSpace ℂ n} (hψ : ‖ψ‖ = 1) (hφ : ‖φ‖ = 1) :
    traceDistance (vecMulVec (WithLp.ofLp ψ) (star (WithLp.ofLp ψ)))
        (vecMulVec (WithLp.ofLp φ) (star (WithLp.ofLp φ))) ≤ ‖ψ - φ‖ := by
  rw [traceDistance_vecMulVec_eq hψ hφ]
  have hre : RCLike.re ⟪ψ, φ⟫_ℂ ≤ ‖⟪ψ, φ⟫_ℂ‖ := RCLike.re_le_norm _
  have hsq : ‖ψ - φ‖ ^ 2 = 2 - 2 * RCLike.re ⟪ψ, φ⟫_ℂ := by
    rw [@norm_sub_sq ℂ, hψ, hφ]
    ring
  refine Real.sqrt_le_iff.mpr ⟨norm_nonneg _, ?_⟩
  rw [hsq]
  nlinarith [sq_nonneg (1 - ‖⟪ψ, φ⟫_ℂ‖)]

end TNLean.Lattice

namespace FiniteProduct

open TNLean.Lattice

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (β : V → Type*) [∀ v, Fintype (β v)] [∀ v, DecidableEq (β v)]

/-- The reduced states of two normalized pure states on a region are no farther
apart in trace distance than the pure states themselves.
Source: `01-preliminaries.tex`, lines 76–80, and `09-amplification.tex`, lines 550–553. -/
theorem traceDistance_reducedPure_le (ψ η : EuclideanSpace ℂ ((v : V) → β v))
    (hψ : ‖ψ‖ = 1) (hη : ‖η‖ = 1) (R : Finset V) :
    traceDistance (reducedPure β ψ R) (reducedPure β η R) ≤
      traceDistance (vecMulVec (WithLp.ofLp ψ) (star (WithLp.ofLp ψ)))
        (vecMulVec (WithLp.ofLp η) (star (WithLp.ofLp η))) :=
  (traceDistance_partialTraceRight_le
      ((posSemidef_vecMulVec_self_star _).submatrix (splitEquiv β R).symm).isHermitian
      ((posSemidef_vecMulVec_self_star _).submatrix (splitEquiv β R).symm).isHermitian
      ((trace_partialTraceRight _).symm.trans
        ((trace_reducedPure β ψ hψ R).trans
          ((trace_reducedPure β η hη R).symm.trans (trace_partialTraceRight _))))).trans_eq
    (traceDistance_submatrix_equiv (splitEquiv β R).symm
      (posSemidef_vecMulVec_self_star _).isHermitian
      (posSemidef_vecMulVec_self_star _).isHermitian)

/-- Mutual information of two disjoint regions depends only on the reduced state of
their union.
Source: `09-amplification.tex`, lines 547–550. -/
theorem mutualInformation_eq_of_reducedPure_union_eq
    {ψ φ : EuclideanSpace ℂ ((v : V) → β v)} {X J : Finset V} (hXJ : Disjoint X J)
    (h : reducedPure β ψ (X ∪ J) = reducedPure β φ (X ∪ J)) :
    mutualInformation β ψ X J = mutualInformation β φ X J := by
  rw [mutualInformation_eq_matrix β ψ X J hXJ, mutualInformation_eq_matrix β φ X J hXJ]
  have hj : jointMatrix β ψ X J hXJ = jointMatrix β φ X J hXJ := by
    simp only [jointMatrix, h]
  simp only [_root_.mutualInformation, hj]

/-- **A unitary on the complement leaves a region unchanged.** Let `U` be a unitary
on the configurations of the complement `Rᶜ`, acting as `1 ⊗ U` on the whole system.
Then every vector `φ` and its image have the same reduced state on `R`. The vector
`φ` may be entangled across the cut.
Source: `09-amplification.tex`, lines 547–550. -/
theorem reducedPure_unitary_compl (φ : EuclideanSpace ℂ ((v : V) → β v)) (R : Finset V)
    (U : Matrix (Configuration β Rᶜ) (Configuration β Rᶜ) ℂ) (hU : Uᴴ * U = 1) :
    reducedPure β (toEuclideanCLM (𝕜 := ℂ)
        (((1 : Matrix (Configuration β R) (Configuration β R) ℂ) ⊗ₖ U).submatrix
          (splitEquiv β R) (splitEquiv β R)) φ) R = reducedPure β φ R := by
  set e := splitEquiv β R
  set W : Matrix _ _ ℂ := (1 : Matrix (Configuration β R) (Configuration β R) ℂ) ⊗ₖ U
  have hconj (M : Matrix ((v : V) → β v) ((v : V) → β v) ℂ)
      (x : ((v : V) → β v) → ℂ) :
      vecMulVec (M *ᵥ x) (star (M *ᵥ x)) = M * vecMulVec x (star x) * Mᴴ := by
    rw [mul_vecMulVec, vecMulVec_mul, vecMul_conjTranspose, star_star]
  rw [reducedPure, reducedPure, reducedMatrix, reducedMatrix, ofLp_toEuclideanCLM, hconj,
    conjTranspose_submatrix]
  set P := vecMulVec (WithLp.ofLp φ) (star (WithLp.ofLp φ))
  have hP : P = (P.submatrix e.symm e.symm).submatrix e e := by simp
  have key : (W.submatrix e e * P * Wᴴ.submatrix e e).submatrix e.symm e.symm =
      W * P.submatrix e.symm e.symm * Wᴴ := by
    conv_lhs => rw [hP]
    rw [submatrix_mul_equiv _ _ _ e _, submatrix_mul_equiv _ _ _ e _]
    simp
  rw [key, partialTraceRight_kronecker_conj_of_right_isometry 1 U hU]
  simp only [Matrix.one_mul, conjTranspose_one, Matrix.mul_one]
  rfl

omit [∀ v, DecidableEq (β v)] in
/-- The trace of a reduced pure state is the squared norm of the vector. -/
theorem trace_reducedPure_eq_norm_sq (ψ : EuclideanSpace ℂ ((v : V) → β v)) (R : Finset V) :
    (reducedPure β ψ R).trace = ((‖ψ‖ ^ 2 : ℝ) : ℂ) := by
  rw [reducedPure, trace_reducedMatrix, Matrix.trace_vecMulVec,
    ← EuclideanSpace.inner_eq_star_dotProduct, inner_self_eq_norm_sq_to_K]
  simp

/-- **Continuity against a product reduction.** Let `ψ, η` be unit vectors and `X, J`
disjoint regions on which `η` has no mutual information, as for a product joint
reduction. Then `I_ψ(X : J) ≤ 8 √‖ψ - η‖ log(e dim X)`. Only the dimension of `X`
enters; that of `J` and of the remaining systems does not.
Source: Lemma 2.1, `01-preliminaries.tex`, lines 33–46 and 76–77, as applied in
`09-amplification.tex`, lines 550–555. -/
theorem mutualInformation_le_of_norm_sub_le {ψ η : EuclideanSpace ℂ ((v : V) → β v)}
    (hψ : ‖ψ‖ = 1) (hη : ‖η‖ = 1) {X J : Finset V} (hXJ : Disjoint X J)
    (hprod : mutualInformation β η X J = 0) :
    mutualInformation β ψ X J ≤
      8 * √‖ψ - η‖ * Real.log (Real.exp 1 * Fintype.card (Configuration β X)) := by
  have htr (χ : EuclideanSpace ℂ ((v : V) → β v)) (hχ : ‖χ‖ = 1) :
      (jointMatrix β χ X J hXJ).trace = 1 := by
    unfold jointMatrix
    rw [trace_submatrix_equiv]
    exact trace_reducedPure β χ hχ _
  have h := Entropy.abs_mutualInformation_sub_le_sqrt_fin
    (jointMatrix_posSemidef β ψ X J hXJ) (jointMatrix_posSemidef β η X J hXJ)
    (htr ψ hψ) (htr η hη)
  have hψI : Entropy.mutualInformation (jointMatrix β ψ X J hXJ)
      (jointMatrix_posSemidef β ψ X J hXJ).isHermitian = mutualInformation β ψ X J :=
    (mutualInformation_eq_matrix β ψ X J hXJ).symm
  have hηI : Entropy.mutualInformation (jointMatrix β η X J hXJ)
      (jointMatrix_posSemidef β η X J hXJ).isHermitian = mutualInformation β η X J :=
    (mutualInformation_eq_matrix β η X J hXJ).symm
  rw [hψI, hηI, hprod, sub_zero] at h
  have hdist : traceDistance (jointMatrix β ψ X J hXJ) (jointMatrix β η X J hXJ) ≤
      ‖ψ - η‖ := by
    unfold jointMatrix
    rw [traceDistance_submatrix_equiv _ (reducedPure_posSemidef β ψ _).isHermitian
      (reducedPure_posSemidef β η _).isHermitian]
    exact (traceDistance_reducedPure_le β ψ η hψ hη _).trans
      (traceDistance_vecMulVec_le_norm_sub hψ hη)
  have hlog : 0 ≤ Real.log (Real.exp 1 * Fintype.card (Configuration β X)) :=
    Real.log_nonneg (one_le_mul_of_one_le_of_one_le (Real.one_le_exp zero_le_one)
      (Nat.one_le_cast.mpr (Fintype.card_pos_iff.mpr
        (Entropy.Matrix.PosSemidef.nonempty_of_trace_eq_one
          (trace_reducedPure β ψ hψ X)))))
  calc mutualInformation β ψ X J ≤ |mutualInformation β ψ X J| := le_abs_self _
    _ ≤ _ := h
    _ ≤ _ := by gcongr

/-- **The entropy comparison after the local unitary.** Let `U` be a unitary on the
configurations outside `X ∪ J`, acting as `1 ⊗ U` on the whole system, and let
`η` be a unit vector with `I_η(X : J) = 0`. Every unit vector `φ` then satisfies
`I_φ(X : J) ≤ 8 √δ log(e dim X)` with `δ = ‖(1 ⊗ U) φ - η‖`. The unitary changes
neither `X` nor `J`, so `φ` and its image have the same joint reduction on `X ∪ J`.
Source: `09-amplification.tex`, lines 547–555. -/
theorem mutualInformation_le_of_unitary_sub_le {φ η : EuclideanSpace ℂ ((v : V) → β v)}
    (hφ : ‖φ‖ = 1) (hη : ‖η‖ = 1) {X J : Finset V} (hXJ : Disjoint X J)
    (U : Matrix (Configuration β (X ∪ J)ᶜ) (Configuration β (X ∪ J)ᶜ) ℂ)
    (hU : Uᴴ * U = 1)
    (hprod : mutualInformation β η X J = 0) :
    mutualInformation β φ X J ≤
      8 * √‖toEuclideanCLM (𝕜 := ℂ)
          (((1 : Matrix (Configuration β (X ∪ J)) _ ℂ) ⊗ₖ U).submatrix
            (splitEquiv β (X ∪ J)) (splitEquiv β (X ∪ J))) φ - η‖ *
        Real.log (Real.exp 1 * Fintype.card (Configuration β X)) := by
  set ψ := toEuclideanCLM (𝕜 := ℂ)
    (((1 : Matrix (Configuration β (X ∪ J)) _ ℂ) ⊗ₖ U).submatrix
      (splitEquiv β (X ∪ J)) (splitEquiv β (X ∪ J))) φ
  have hred : reducedPure β ψ (X ∪ J) = reducedPure β φ (X ∪ J) :=
    reducedPure_unitary_compl β φ (X ∪ J) U hU
  have hψ : ‖ψ‖ = 1 := by
    have h := congrArg Matrix.trace hred
    rw [trace_reducedPure_eq_norm_sq, trace_reducedPure_eq_norm_sq, hφ] at h
    have h' : ‖ψ‖ ^ 2 = 1 ^ 2 := by exact_mod_cast h
    nlinarith [norm_nonneg ψ, sq_nonneg (‖ψ‖ - 1)]
  rw [← mutualInformation_eq_of_reducedPure_union_eq β hXJ hred]
  exact mutualInformation_le_of_norm_sub_le β hψ hη hXJ hprod

/-- **The polynomial scale of the comparison.** In the setting of
`mutualInformation_le_of_unitary_sub_le`, suppose the unitary error is at most
`C₁ n^(-K/2)` and `log dim X ≤ C₂ n²` for an integer `n ≥ 1`. Then
`I_φ(X : J) ≤ 8 √C₁ (1 + C₂) n^(2-K/4)`. The constant depends only on `C₁` and `C₂`.
Source: `09-amplification.tex`, lines 545 and 550–557. -/
theorem mutualInformation_le_rpow_of_unitary_sub_le
    {φ η : EuclideanSpace ℂ ((v : V) → β v)}
    (hφ : ‖φ‖ = 1) (hη : ‖η‖ = 1) {X J : Finset V} (hXJ : Disjoint X J)
    (U : Matrix (Configuration β (X ∪ J)ᶜ) (Configuration β (X ∪ J)ᶜ) ℂ)
    (hU : Uᴴ * U = 1)
    (hprod : mutualInformation β η X J = 0) {C₁ C₂ K : ℝ} {n : ℕ} (hn : 1 ≤ n)
    (hδ : ‖toEuclideanCLM (𝕜 := ℂ)
          (((1 : Matrix (Configuration β (X ∪ J)) _ ℂ) ⊗ₖ U).submatrix
            (splitEquiv β (X ∪ J)) (splitEquiv β (X ∪ J))) φ - η‖ ≤
      C₁ * (n : ℝ) ^ (-K / 2))
    (hdim : Real.log (Fintype.card (Configuration β X)) ≤ C₂ * (n : ℝ) ^ 2) :
    mutualInformation β φ X J ≤ 8 * √C₁ * (1 + C₂) * (n : ℝ) ^ (2 - K / 4) := by
  have hbase := mutualInformation_le_of_unitary_sub_le β hφ hη hXJ U hU hprod
  set δ := ‖toEuclideanCLM (𝕜 := ℂ)
          (((1 : Matrix (Configuration β (X ∪ J)) _ ℂ) ⊗ₖ U).submatrix
            (splitEquiv β (X ∪ J)) (splitEquiv β (X ∪ J))) φ - η‖
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hcard : (1 : ℝ) ≤ Fintype.card (Configuration β X) :=
    Nat.one_le_cast.mpr (Fintype.card_pos_iff.mpr
      (Entropy.Matrix.PosSemidef.nonempty_of_trace_eq_one (trace_reducedPure β φ hφ X)))
  have hlog : Real.log (Real.exp 1 * Fintype.card (Configuration β X)) =
      1 + Real.log (Fintype.card (Configuration β X)) := by
    rw [Real.log_mul (Real.exp_pos 1).ne' (by positivity), Real.log_exp]
  have hlog0 : 0 ≤ Real.log (Real.exp 1 * Fintype.card (Configuration β X)) := by
    rw [hlog]
    linarith [Real.log_nonneg hcard]
  have hL : Real.log (Real.exp 1 * Fintype.card (Configuration β X)) ≤
      (1 + C₂) * (n : ℝ) ^ (2 : ℝ) := by
    rw [hlog, Real.rpow_two]
    nlinarith
  have hsqrt : √δ ≤ √C₁ * (n : ℝ) ^ (-K / 4) := by
    calc √δ ≤ √(C₁ * (n : ℝ) ^ (-K / 2)) := Real.sqrt_le_sqrt hδ
      _ = √C₁ * (n : ℝ) ^ (-K / 4) := by
        rw [Real.sqrt_mul' _ (by positivity), Real.sqrt_eq_rpow ((n : ℝ) ^ (-K / 2)),
          ← Real.rpow_mul hn0.le]
        ring_nf
  calc mutualInformation β φ X J
      ≤ 8 * √δ * Real.log (Real.exp 1 * Fintype.card (Configuration β X)) := hbase
    _ ≤ 8 * (√C₁ * (n : ℝ) ^ (-K / 4)) * ((1 + C₂) * (n : ℝ) ^ (2 : ℝ)) := by
        gcongr
    _ = 8 * √C₁ * (1 + C₂) * (n : ℝ) ^ (2 - K / 4) := by
        rw [show (2 : ℝ) - K / 4 = -K / 4 + 2 by ring, Real.rpow_add hn0]
        ring

/-- **`eq:amplification-output` from the unitary error.** In the setting of
`mutualInformation_le_rpow_of_unitary_sub_le`, with integers `M` and `K ≥ 4(M + 2)`,
the unitary error `C₁ n^(-K/2)` and `log dim X ≤ C₂ n²` give
`I_φ(X' : J) ≤ 8 √C₁ (1 + C₂) n^(-M)` for every subset `X' ⊆ X`. The source fixes
`K ≥ 4(M + 3)`, which satisfies this hypothesis. The constant depends only on `C₁` and `C₂`.
Source: `09-amplification.tex`, lines 545 and 550–561. -/
theorem mutualInformation_le_inv_pow_of_unitary_sub_le
    {φ η : EuclideanSpace ℂ ((v : V) → β v)}
    (hφ : ‖φ‖ = 1) (hη : ‖η‖ = 1) {X J : Finset V} (hXJ : Disjoint X J)
    (U : Matrix (Configuration β (X ∪ J)ᶜ) (Configuration β (X ∪ J)ᶜ) ℂ)
    (hU : Uᴴ * U = 1)
    (hprod : mutualInformation β η X J = 0) {C₁ C₂ : ℝ} {n M K : ℕ} (hn : 1 ≤ n)
    (hK : 4 * (M + 2) ≤ K)
    (hδ : ‖toEuclideanCLM (𝕜 := ℂ)
          (((1 : Matrix (Configuration β (X ∪ J)) _ ℂ) ⊗ₖ U).submatrix
            (splitEquiv β (X ∪ J)) (splitEquiv β (X ∪ J))) φ - η‖ ≤
      C₁ * (n : ℝ) ^ (-(K : ℝ) / 2))
    (hdim : Real.log (Fintype.card (Configuration β X)) ≤ C₂ * (n : ℝ) ^ 2) :
    ∀ X' ⊆ X, mutualInformation β φ X' J ≤
      8 * √C₁ * (1 + C₂) * ((n : ℝ) ^ M)⁻¹ := by
  intro X' hX'
  refine (mutualInformation_mono_left β φ X' X J hX' hXJ).trans ?_
  have h := mutualInformation_le_rpow_of_unitary_sub_le β hφ hη hXJ U hU hprod hn hδ hdim
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hcard : (1 : ℝ) ≤ Fintype.card (Configuration β X) :=
    Nat.one_le_cast.mpr (Fintype.card_pos_iff.mpr
      (Entropy.Matrix.PosSemidef.nonempty_of_trace_eq_one (trace_reducedPure β φ hφ X)))
  have hC₂ : 0 ≤ C₂ := by
    have h0 := (Real.log_nonneg hcard).trans hdim
    have hn2 : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
    nlinarith
  have hKr : (4 * ((M : ℝ) + 2)) ≤ K := by exact_mod_cast hK
  have hpow : (n : ℝ) ^ (2 - (K : ℝ) / 4) ≤ ((n : ℝ) ^ M)⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_neg (by positivity)]
    exact Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
  exact h.trans (by gcongr)

end FiniteProduct
