/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.BoundaryNormalization
import QICLean.Algebra.HermitianHelpers

/-!
# Superpositions with a common regular boundary density

Suppose that a cut map has Gram matrix proportional to the invariant-boundary projector,
and that the projected mixed Gram matrices of the complementary maps are scalar multiples
of the same projector. Every nonzero superposition then has the same normalized reduced
density operator on the first side of the cut. Positivity of its normalization factor is
a consequence of nonvanishing, rather than an additional assumption on the coefficients.

These are conditional matrix statements underlying the superposition argument in Schuch,
Cirac, and Pérez-García, arXiv:1001.3807, Theorem 6.9, proof, lines 2043–2076 of
`Papers/1001.3807/paper_v3.tex`. Identification of the mixed Gram matrices for a particular
PEPS contraction is separate; see `docs/paper-gaps/rmp_peps_quantum_double_g_isometry.tex`.
-/

open scoped BigOperators Matrix ComplexOrder
open Matrix

namespace TNLean.PEPS

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]
variable {α β S : Type*} [Fintype α] [Fintype β] [Fintype S]

/-- The complementary map of a finite superposition, restricted to the invariant boundary. -/
noncomputable def regularClosureSuperpositionMap {n : ℕ}
    (N : S → Matrix β (Fin (n + 1) → G) ℂ) (w : S → ℂ) :
    Matrix β (Fin (n + 1) → G) ℂ :=
  (∑ s, w s • N s) * regularBoundaryProjector (n + 1)

/-- The quadratic form obtained from the projected mixed Gram factors. -/
noncomputable def regularClosureSuperpositionFactor (k : S → S → ℂ) (w : S → ℂ) : ℂ :=
  ∑ s, ∑ t, star (w s) * w t * k s t

/-- The mixed Gram kernel determines the Gram matrix of every finite superposition. -/
theorem regularClosureSuperpositionMap_conjTranspose_mul (n : ℕ)
    (N : S → Matrix β (Fin (n + 1) → G) ℂ) (w : S → ℂ) (k : S → S → ℂ)
    (hk : ∀ s t, regularBoundaryProjector (n + 1) * (N s).conjTranspose * N t *
      regularBoundaryProjector (n + 1) = k s t • regularBoundaryProjector (n + 1)) :
    (regularClosureSuperpositionMap N w).conjTranspose * regularClosureSuperpositionMap N w =
      regularClosureSuperpositionFactor k w • regularBoundaryProjector (n + 1) := by
  simp only [regularClosureSuperpositionMap, conjTranspose_mul,
    regularBoundaryProjector_conjTranspose, conjTranspose_sum, conjTranspose_smul,
    Matrix.sum_mul, Matrix.mul_sum, Matrix.smul_mul, Matrix.mul_smul]
  simp only [← Matrix.mul_assoc, hk, smul_smul]
  simp only [regularClosureSuperpositionFactor, Finset.sum_smul, Finset.smul_sum,
    smul_smul, mul_assoc]
  rw [Finset.sum_comm]
  congr 1
  funext s
  congr 1
  funext t
  congr 1
  ring

omit [Fintype β] in
/-- The superposition map vanishes on the orthogonal complement of the invariant boundary. -/
theorem regularClosureSuperpositionMap_mul_projector (n : ℕ)
    (N : S → Matrix β (Fin (n + 1) → G) ℂ) (w : S → ℂ) :
    regularClosureSuperpositionMap N w * regularBoundaryProjector (n + 1) =
      regularClosureSuperpositionMap N w := by
  rw [regularClosureSuperpositionMap, Matrix.mul_assoc,
    regularBoundaryProjector_mul_self]

private theorem exists_positive_factor_of_gram (n : ℕ)
    (B : Matrix β (Fin (n + 1) → G) ℂ) {κ : ℂ}
    (hB : B.conjTranspose * B = κ • regularBoundaryProjector (n + 1)) (hne : B ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ κ = (c : ℂ) := by
  have htr := (posSemidef_conjTranspose_mul_self B).trace_pos_of_ne_zero
    (mt Matrix.conjTranspose_mul_self_eq_zero.mp hne)
  have ht : (B.conjTranspose * B).trace = κ * (Fintype.card G : ℂ) ^ n := by
    rw [hB, Matrix.trace_smul, trace_regularBoundaryProjector, smul_eq_mul]
  have hp := Complex.pos_iff.mp htr
  have hG : 0 < (Fintype.card G : ℝ) ^ n :=
    pow_pos (Nat.cast_pos.mpr Fintype.card_pos) n
  refine ⟨(B.conjTranspose * B).trace.re / (Fintype.card G : ℝ) ^ n,
    div_pos hp.1 hG, ?_⟩
  rw [Complex.ofReal_div, Complex.ofReal_pow, Complex.ofReal_natCast]
  apply (eq_div_iff (pow_ne_zero n (Nat.cast_ne_zero.mpr Fintype.card_ne_zero))).mpr
  rw [← ht]
  apply Complex.ext <;> simp [hp.2.symm]

/-- The bipartite coefficient vector of the projected complementary superposition. -/
noncomputable def regularClosureSuperpositionState {n : ℕ}
    (A : Matrix α (Fin (n + 1) → G) ℂ)
    (N : S → Matrix β (Fin (n + 1) → G) ℂ) (w : S → ℂ) : α × β → ℂ :=
  fun p => (A * (regularClosureSuperpositionMap N w).transpose) p.1 p.2

omit [Fintype α] [Fintype β] in
/-- The coefficient vector is the linear combination of the projected cut vectors. -/
theorem regularClosureSuperpositionState_eq_sum (n : ℕ)
    (A : Matrix α (Fin (n + 1) → G) ℂ)
    (N : S → Matrix β (Fin (n + 1) → G) ℂ) (w : S → ℂ) :
    regularClosureSuperpositionState A N w =
      ∑ s, w s • (fun p : α × β =>
        (A * regularBoundaryProjector (G := G) (n + 1) * (N s).transpose) p.1 p.2) := by
  funext p
  simp only [regularClosureSuperpositionState, regularClosureSuperpositionMap,
    transpose_mul, regularBoundaryProjector_transpose, transpose_sum, transpose_smul,
    ← Matrix.mul_assoc, Matrix.mul_sum, Matrix.mul_smul, Finset.sum_apply,
    Matrix.sum_apply, Matrix.smul_apply, Pi.smul_apply]

omit [Fintype β] in
/-- A cut map with scalar invariant-boundary Gram matrix absorbs the boundary projector;
hence the projected coefficient vector is the ordinary superposition of cut vectors. -/
theorem regularClosureSuperpositionState_eq_sum_of_gram (n : ℕ)
    (A : Matrix α (Fin (n + 1) → G) ℂ)
    (N : S → Matrix β (Fin (n + 1) → G) ℂ) (w : S → ℂ) {c : ℂ}
    (hA : A.conjTranspose * A = c • regularBoundaryProjector (n + 1)) :
    regularClosureSuperpositionState A N w =
      ∑ s, w s • (fun p : α × β => (A * (N s).transpose) p.1 p.2) := by
  have hz : (A.conjTranspose * A) * (1 - regularBoundaryProjector (n + 1)) = 0 := by
    rw [hA, Matrix.smul_mul, Matrix.mul_sub, Matrix.mul_one,
      regularBoundaryProjector_mul_self, sub_self, smul_zero]
  have hAP : A * regularBoundaryProjector (n + 1) = A := by
    have h := (Matrix.conjTranspose_mul_self_mul_eq_zero A _).mp hz
    rw [Matrix.mul_sub, Matrix.mul_one, sub_eq_zero] at h
    exact h.symm
  rw [regularClosureSuperpositionState_eq_sum n A N w]
  simp only [hAP]

variable [DecidableEq α]

/-- Every nonzero superposition with scalar projected mixed Gram matrices has the same
normalized reduced density on the first side of the cut. Its rank, flat spectrum, and
entropy are determined solely by the number of regular boundary bonds. No positivity
hypothesis is imposed on the mixed Gram factors or on the superposition coefficients. -/
theorem exists_normalization_regularClosureSuperpositionState (n : ℕ)
    (A : Matrix α (Fin (n + 1) → G) ℂ)
    (N : S → Matrix β (Fin (n + 1) → G) ℂ) (w : S → ℂ) (k : S → S → ℂ)
    {cA : ℝ} (hcA : 0 < cA)
    (hA : A.conjTranspose * A = (cA : ℂ) • regularBoundaryProjector (n + 1))
    (hk : ∀ s t, regularBoundaryProjector (n + 1) * (N s).conjTranspose * N t *
      regularBoundaryProjector (n + 1) = k s t • regularBoundaryProjector (n + 1))
    (hne : regularClosureSuperpositionState A N w ≠ 0) :
    ∃ z : ℝ, 0 < z ∧
      let ψ := (z : ℂ) • regularClosureSuperpositionState A N w
      let ρ := partialTraceRight (vecMulVec ψ (star ψ))
      ρ = physicalRegularBoundaryDensity n (normalizedRegularBoundaryMap cA A) ∧
        star ψ ⬝ᵥ ψ = 1 ∧ ρ.rank = Fintype.card G ^ n ∧
        ρ * ρ = ((Fintype.card G : ℂ) ^ n)⁻¹ • ρ ∧
        vonNeumannEntropy ρ
          (posSemidef_vecMulVec_self_star ψ).partialTraceRight.isHermitian =
            (n : ℝ) * Real.log (Fintype.card G : ℝ) := by
  classical
  let B := regularClosureSuperpositionMap N w
  have hBne : B ≠ 0 := by
    intro hB
    apply hne
    funext p
    change (A * B.transpose) p.1 p.2 = 0
    simp only [hB, transpose_zero, Matrix.mul_zero, Matrix.zero_apply]
  obtain ⟨cB, hcB, hfactor⟩ := exists_positive_factor_of_gram n B
    (regularClosureSuperpositionMap_conjTranspose_mul n N w k hk) hBne
  have hB : B.conjTranspose * B = (cB : ℂ) • regularBoundaryProjector (n + 1) := by
    rw [← hfactor]
    exact regularClosureSuperpositionMap_conjTranspose_mul n N w k hk
  let A₀ := normalizedRegularBoundaryMap cA A
  let B₀ := normalizedRegularBoundaryMap cB B
  have hA₀ := normalizedRegularBoundaryMap_conjTranspose_mul n A hcA hA
  have hB₀ := normalizedRegularBoundaryMap_conjTranspose_mul n B hcB hB
  have hPB : regularBoundaryProjector (n + 1) * B.transpose = B.transpose := by
    have h := congrArg Matrix.transpose (regularClosureSuperpositionMap_mul_projector n N w)
    simpa only [transpose_mul, regularBoundaryProjector_transpose] using h
  let z := (Real.sqrt cA)⁻¹ * (Real.sqrt cB)⁻¹ *
    (Real.sqrt (Fintype.card G ^ n : ℝ))⁻¹
  have hG : 0 < (Fintype.card G : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  have hz : 0 < z := mul_pos
    (mul_pos (inv_pos.mpr (Real.sqrt_pos.mpr hcA)) (inv_pos.mpr (Real.sqrt_pos.mpr hcB)))
    (inv_pos.mpr (Real.sqrt_pos.mpr (pow_pos hG n)))
  have hψ : physicalRegularBoundaryState n A₀ B₀ =
      (z : ℂ) • regularClosureSuperpositionState A N w := by
    funext p
    change physicalRegularBoundarySchmidtMatrix n A₀ B₀ p.1 p.2 = _
    rw [physicalRegularBoundarySchmidtMatrix_normalizedRegularBoundaryMap,
      Matrix.mul_assoc, hPB]
    simp only [z, Complex.ofReal_mul, Complex.ofReal_inv, Matrix.smul_apply,
      Pi.smul_apply, smul_eq_mul, regularClosureSuperpositionState, B]
  have hρ := partialTrace_physicalRegularBoundaryState n A₀ B₀ hB₀
  rw [hψ] at hρ
  have hnorm : star (physicalRegularBoundaryState n A₀ B₀) ⬝ᵥ
      physicalRegularBoundaryState n A₀ B₀ = 1 := by
    rw [Matrix.star_dotProduct_eq_trace_conjTranspose_mul, Matrix.trace_mul_comm]
    change (physicalRegularBoundarySchmidtMatrix n A₀ B₀ *
      (physicalRegularBoundarySchmidtMatrix n A₀ B₀).conjTranspose).trace = 1
    rw [physicalRegularBoundarySchmidtMatrix_mul_conjTranspose n A₀ B₀ hB₀,
      trace_physicalRegularBoundaryDensity n A₀ hA₀]
  rw [hψ] at hnorm
  refine ⟨z, hz, hρ, hnorm, ?_, ?_, ?_⟩
  · rw [hρ]
    exact rank_physicalRegularBoundaryDensity n A₀ hA₀
  · rw [hρ]
    exact physicalRegularBoundaryDensity_mul_self n A₀ hA₀
  · exact (vonNeumannEntropy_congr hρ _ _).trans
      (vonNeumannEntropy_physicalRegularBoundaryDensity n A₀ hA₀)

end TNLean.PEPS
