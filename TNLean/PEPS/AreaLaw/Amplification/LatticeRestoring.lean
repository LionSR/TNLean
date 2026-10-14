/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Amplification.TypicalProjectors
import TNLean.PEPS.AreaLaw.TwoFamilies
import QICLean.Entropy.RestoringNorm
import QICLean.Entropy.RestoringGroundComponent
import QICLean.Entropy.RestoringVectors
import QICLean.Entropy.SchmidtPinning

/-!
# The restoring operator of the amplification proposition on the lattice

The proof of the amplification proposition builds a restoring operator `R₀` and a
column operator `B₀` from the three typical projections `P_X`, `T_Y`, `Q_{S₀}` of the
original ground state, for disjoint regions `X, Y` with `S₀ = X ∪ Y` and remote region
`Z' = Λ ∖ S₀`. Three estimates are established before the constraint products enter:
the operator norms are at most `M₀ = exp ((𝓘 + 3w)/2)` with `𝓘 = I_Ω(X : Z')`, the
adjoint identity holds with error `3 √δ + ‖L'^† Ω - Ω‖` for every physical operator `L'`,
and the physical ground component of `R₀ φ` has norm at most one.

The finite-matrix restoration algebra is generic. This module supplies its lattice
input: the coordinates `((X, Y), Z')` of the configuration space, the full eigenbasis
of `ρ_X`, the vector `Ω` written in that basis, and the typical projection of `S₀` in
the same coordinates. It proves the hypotheses of the generic estimates for the
original ground state: the diagonal `X`-marginal, the `Y`-marginal, commutation and the
spectral inequalities `Q ≤ e^{S(S₀)+w} ρ_{S₀}` and `T_Y ρ_Y T_Y ≤ e^{-S(Y)+w} T_Y`, the
three failure bounds `√δ`, and the purity identity `S(X) + S(S₀) - S(Y) = I(X : Z')`.
At large scales `w = n^(3/5)` and `δ = n^(-2K)`.

The constraint products, the choice of a good clock realization, the polar
correction and the final entropy comparison are not treated here.

## Main definitions

* `TNLean.PEPS.AreaLaw.restoringVector`: `Ω` in the coordinates `((X, Y), Z')`, with
  `X` written in the eigenbasis of `ρ_X`.
* `TNLean.PEPS.AreaLaw.restoringCutProjection`: the typical projection of `S₀` in the
  same coordinates.

## Main statements

* `TNLean.PEPS.AreaLaw.mutualInformation_compl_eq`: `I(X : Z') = S(X) + S(S₀) - S(Y)`.
* `TNLean.PEPS.AreaLaw.restoringOperator_estimates`:
  `eq:amplification-operator-norm`, `eq:amplification-adjoint-error` and
  `eq:amplification-ground-component` for given failure probabilities `δ`.
* `TNLean.PEPS.AreaLaw.exists_restoringOperator_estimates`: the same at all large
  scales, with `w = n^(3/5)` and `δ = n^(-2K)`.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*,
  September 24, 2026, proof of Proposition 10.2 (`prop:amplification`),
  `09-amplification.tex`, lines 304–447: `eq:amplification-typical-error`,
  `eq:amplification-restoring-operator`, `eq:amplification-column-operator`,
  `eq:amplification-operator-norm`, `eq:amplification-adjoint-error` and
  `eq:amplification-ground-component`.
  Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

Independently formalized from the manuscript; no upstream Lean proof text is reused.
-/

open Matrix
open scoped Kronecker ComplexOrder MatrixOrder InnerProductSpace Matrix.Norms.L2Operator

namespace Matrix

section PartialTrace

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]

/-- Conjugating the first factor commutes with the partial trace over the second:
`tr₂((A ⊗ 1) M (B ⊗ 1)) = A tr₂(M) B`. -/
theorem partialTraceRight_kronecker_one_mul_mul (A B : Matrix α α ℂ)
    (M : Matrix (α × β) (α × β) ℂ) :
    partialTraceRight ((A ⊗ₖ (1 : Matrix β β ℂ)) * M * (B ⊗ₖ (1 : Matrix β β ℂ))) =
      A * partialTraceRight M * B := by
  ext i j
  simp only [partialTraceRight_apply, mul_apply, Fintype.sum_prod_type, kroneckerMap_apply,
    one_apply, mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq,
    Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [Finset.sum_comm]

/-- The partial trace over the first factor is invariant under a similarity of that
factor: `tr₁((A ⊗ 1) M (B ⊗ 1)) = tr₁(M)` when `B A = 1`. -/
theorem partialTraceLeft_kronecker_one_conj [DecidableEq α] {A B : Matrix α α ℂ}
    (hBA : B * A = 1) (M : Matrix (α × β) (α × β) ℂ) :
    partialTraceLeft ((A ⊗ₖ (1 : Matrix β β ℂ)) * M * (B ⊗ₖ (1 : Matrix β β ℂ))) =
      partialTraceLeft M := by
  ext i j
  simp only [partialTraceLeft_apply, mul_apply, Fintype.sum_prod_type, kroneckerMap_apply,
    one_apply, mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq,
    Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, Finset.sum_mul]
  calc ∑ k, ∑ x, ∑ y, A k y * M (y, i) (x, j) * B x k
      = ∑ x, ∑ y, M (y, i) (x, j) * (B * A) x y := by
        simp only [mul_apply, Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun x _ ↦ ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun y _ ↦ Finset.sum_congr rfl fun k _ ↦ ?_
        ring
    _ = _ := by simp [hBA, one_apply]

end PartialTrace

/-- A Kronecker product of orthogonal projections is an orthogonal projection. -/
theorem isStarProjection_kronecker {A B : Type*} [Fintype A] [Fintype B]
    {P : Matrix A A ℂ} {Q : Matrix B B ℂ}
    (hP : IsStarProjection P) (hQ : IsStarProjection Q) : IsStarProjection (P ⊗ₖ Q) where
  isIdempotentElem := by
    change (P ⊗ₖ Q) * (P ⊗ₖ Q) = P ⊗ₖ Q
    rw [← mul_kronecker_mul, hP.isIdempotentElem.eq, hQ.isIdempotentElem.eq]
  isSelfAdjoint := by
    change (P ⊗ₖ Q)ᴴ = P ⊗ₖ Q
    rw [conjTranspose_kronecker, show Pᴴ = P from hP.isSelfAdjoint,
      show Qᴴ = Q from hQ.isSelfAdjoint]

/-- The squared distance by which an orthogonal projection moves a vector is its squared
norm minus the expectation of the projection: `‖P ψ - ψ‖² = ‖ψ‖² - Re tr(|ψ⟩⟨ψ| P)`. -/
theorem norm_projection_mulVec_sub_sq {ι : Type*} [Fintype ι]
    {P : Matrix ι ι ℂ} (hP : IsStarProjection P) (ψ : EuclideanSpace ℂ ι) :
    ‖WithLp.toLp 2 (P *ᵥ ψ.ofLp) - ψ‖ ^ 2 =
      ‖ψ‖ ^ 2 - (vecMulVec ψ.ofLp (star ψ.ofLp) * P).trace.re := by
  classical
  have hY : (1 - P)ᴴ * (1 - P) = 1 - P := by
    rw [conjTranspose_sub, conjTranspose_one, ← star_eq_conjTranspose,
      hP.isSelfAdjoint.star_eq, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub,
      Matrix.mul_one, hP.isIdempotentElem.eq, sub_self, sub_zero]
  have h1P : toEuclideanLin (1 - P) ψ = ψ - toEuclideanLin P ψ := by
    ext i
    simp [toLpLin_apply]
  have hv : WithLp.toLp 2 (P *ᵥ ψ.ofLp) - ψ = -toEuclideanLin (1 - P) ψ := by
    rw [h1P, neg_sub, toLpLin_apply]
  have htr : (vecMulVec ψ.ofLp (star ψ.ofLp) * P).trace = ⟪ψ, toEuclideanLin P ψ⟫_ℂ := by
    rw [EuclideanSpace.inner_eq_star_dotProduct, toLpLin_apply]
    simp only [trace, diag, mul_apply, vecMulVec_apply, dotProduct, mulVec, Pi.star_apply,
      Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ by ring
  rw [hv, norm_neg, Entropy.norm_toEuclideanLin_sq, hY, h1P, htr, inner_sub_right,
    Complex.sub_re, inner_self_eq_norm_sq_to_K]
  norm_cast

section Spectral

variable {n : Type*} [Fintype n] [DecidableEq n] {ρ : Matrix n n ℂ}

private theorem IsHermitian.spectralSelection_eq_conj (hρ : ρ.IsHermitian) (E : Finset n) :
    hρ.spectralSelection E = (hρ.eigenvectorUnitary : Matrix n n ℂ) *
      diagonal (fun i ↦ if i ∈ E then (1 : ℂ) else 0) *
        (hρ.eigenvectorUnitary : Matrix n n ℂ)ᴴ := by
  rw [IsHermitian.spectralSelection, Unitary.conjStarAlgAut_apply, star_eq_conjTranspose]

private theorem IsHermitian.eq_conj (hρ : ρ.IsHermitian) :
    ρ = (hρ.eigenvectorUnitary : Matrix n n ℂ) *
      diagonal (fun i ↦ ((hρ.eigenvalues i : ℝ) : ℂ)) *
        (hρ.eigenvectorUnitary : Matrix n n ℂ)ᴴ := by
  conv_lhs => rw [hρ.spectral_theorem]
  rw [Unitary.conjStarAlgAut_apply, star_eq_conjTranspose]
  rfl

/-- A spectral selection of a positive matrix is at most `c ρ` when every selected
eigenvalue is at least `1 / c`. -/
theorem PosSemidef.spectralSelection_le_smul (hρ : ρ.PosSemidef) {E : Finset n} {c : ℝ}
    (hc : 0 ≤ c) (h : ∀ i ∈ E, 1 ≤ c * hρ.isHermitian.eigenvalues i) :
    hρ.isHermitian.spectralSelection E ≤ c • ρ := by
  rw [Matrix.le_iff]
  set U := (hρ.isHermitian.eigenvectorUnitary : Matrix n n ℂ)
  have hd : c • ρ - hρ.isHermitian.spectralSelection E = U * diagonal (fun i ↦
      ((c * hρ.isHermitian.eigenvalues i : ℝ) : ℂ) - if i ∈ E then 1 else 0) * Uᴴ := by
    rw [hρ.isHermitian.spectralSelection_eq_conj]
    conv_lhs => arg 1; rw [hρ.isHermitian.eq_conj]
    rw [← Matrix.smul_mul, ← Matrix.mul_smul, ← Matrix.sub_mul, ← Matrix.mul_sub]
    congr 2
    ext i j
    by_cases hij : i = j
    · subst hij; simp
    · simp [diagonal_apply_ne _ hij]
  rw [hd]
  refine PosSemidef.mul_mul_conjTranspose_same (PosSemidef.diagonal fun i ↦ ?_) U
  change (0 : ℂ) ≤ _
  by_cases hi : i ∈ E
  · simp only [hi, ↓reduceIte]
    exact_mod_cast sub_nonneg.mpr (h i hi)
  · simp only [hi, ↓reduceIte, sub_zero]
    exact_mod_cast mul_nonneg hc (hρ.eigenvalues_nonneg i)

/-- A spectral selection compresses `ρ` below `b` times itself when every selected
eigenvalue is at most `b`. -/
theorem IsHermitian.spectralSelection_mul_mul_le_smul (hρ : ρ.IsHermitian) {E : Finset n}
    {b : ℝ} (h : ∀ i ∈ E, hρ.eigenvalues i ≤ b) :
    hρ.spectralSelection E * ρ * hρ.spectralSelection E ≤ b • hρ.spectralSelection E := by
  rw [Matrix.le_iff]
  set U := (hρ.eigenvectorUnitary : Matrix n n ℂ)
  have hU : Uᴴ * U = 1 := by
    simp only [U, ← star_eq_conjTranspose]; exact Unitary.coe_star_mul_self _
  have hd : b • hρ.spectralSelection E - hρ.spectralSelection E * ρ * hρ.spectralSelection E =
      U * diagonal (fun i ↦ if i ∈ E then ((b - hρ.eigenvalues i : ℝ) : ℂ) else 0) * Uᴴ := by
    rw [hρ.spectralSelection_eq_conj]
    conv_lhs => arg 2; arg 1; arg 2; rw [hρ.eq_conj]
    have hcollapse : U * diagonal (fun i ↦ if i ∈ E then (1 : ℂ) else 0) * Uᴴ *
        (U * diagonal (fun i ↦ ((hρ.eigenvalues i : ℝ) : ℂ)) * Uᴴ) *
        (U * diagonal (fun i ↦ if i ∈ E then (1 : ℂ) else 0) * Uᴴ) =
        U * (diagonal (fun i ↦ if i ∈ E then (1 : ℂ) else 0) *
          diagonal (fun i ↦ ((hρ.eigenvalues i : ℝ) : ℂ)) *
          diagonal (fun i ↦ if i ∈ E then (1 : ℂ) else 0)) * Uᴴ := by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc Uᴴ U, hU, Matrix.one_mul, ← Matrix.mul_assoc Uᴴ U, hU,
        Matrix.one_mul]
    rw [hcollapse, diagonal_mul_diagonal, diagonal_mul_diagonal, ← Matrix.smul_mul,
      ← Matrix.mul_smul, ← Matrix.sub_mul, ← Matrix.mul_sub]
    congr 2
    ext i j
    by_cases hij : i = j
    · subst hij; by_cases hi : i ∈ E <;> simp [hi]
    · simp [diagonal_apply_ne _ hij]
  rw [hd]
  refine PosSemidef.mul_mul_conjTranspose_same (PosSemidef.diagonal fun i ↦ ?_) U
  change (0 : ℂ) ≤ _
  by_cases hi : i ∈ E
  · simp only [hi, ↓reduceIte]
    exact_mod_cast sub_nonneg.mpr (h i hi)
  · simp only [hi, ↓reduceIte, le_refl]

end Spectral

end Matrix

namespace TNLean.PEPS.AreaLaw

/-- Configurations of a region of a finite domain, with `q` levels at each site.
Source: area-law Section 1, the regional tensor factors. -/
abbrev RegionalConfiguration {Λ : Finset (ℤ × ℤ)} (q : ℕ) (A : Finset (Site Λ)) :=
  FiniteProduct.Configuration (fun _ : Site Λ ↦ Fin q) A

/-- Shortcut instance, which keeps instance terms on products of regional
configurations small. -/
instance {Λ : Finset (ℤ × ℤ)} (q : ℕ) (A : Finset (Site Λ)) :
    DecidableEq (RegionalConfiguration q A) := inferInstance

/-- Shortcut instance, which keeps instance terms on products of regional
configurations small. -/
instance {Λ : Finset (ℤ × ℤ)} (q : ℕ) (A : Finset (Site Λ)) :
    Fintype (RegionalConfiguration q A) := inferInstance

variable {Λ : Finset (ℤ × ℤ)} {q : ℕ}

/-- The coordinates `((X, Y), Z')` of the configuration space for disjoint regions
`X, Y`, with `Z' = Λ ∖ (X ∪ Y)`. Source: `09-amplification.tex`, lines 263–268. -/
def restoringSplit (q : ℕ) (X Y : Finset (Site Λ)) (hXY : Disjoint X Y) :
    Configuration Λ q ≃ (RegionalConfiguration q X × RegionalConfiguration q Y) ×
      RegionalConfiguration q (X ∪ Y)ᶜ :=
  (FiniteProduct.splitEquiv (fun _ : Site Λ ↦ Fin q) (X ∪ Y)).trans
    ((FiniteProduct.unionEquiv (fun _ : Site Λ ↦ Fin q) X Y hXY).prodCongr (Equiv.refl _))

/-- The vector `Ω` in the coordinates `((X, Y), Z')`, with the factor `X` written in the
full eigenbasis `{|x⟩}` of `ρ_X`. Source: `09-amplification.tex`, lines 324–329. -/
noncomputable def restoringVector (Ω : StateSpace Λ q) (X Y : Finset (Site Λ))
    (hXY : Disjoint X Y) :
    EuclideanSpace ℂ ((RegionalConfiguration q X × RegionalConfiguration q Y) ×
      RegionalConfiguration q (X ∪ Y)ᶜ) :=
  WithLp.toLp 2 (((((reducedState_isHermitian Λ q Ω X).eigenvectorUnitary :
      Matrix (RegionalConfiguration q X) (RegionalConfiguration q X) ℂ)ᴴ ⊗ₖ
      (1 : Matrix (RegionalConfiguration q Y) (RegionalConfiguration q Y) ℂ)) ⊗ₖ
      (1 : Matrix (RegionalConfiguration q (X ∪ Y)ᶜ)
        (RegionalConfiguration q (X ∪ Y)ᶜ) ℂ)) *ᵥ
    fun i ↦ Ω ((restoringSplit q X Y hXY).symm i))

/-- The typical projection `Q = Q_{S₀}` of `S₀ = X ∪ Y` at width `w`, in the
coordinates `(X, Y)` with `X` written in the eigenbasis of `ρ_X`.
Source: `09-amplification.tex`, lines 304–313 and 348–350. -/
noncomputable def restoringCutProjection (Ω : StateSpace Λ q) (X Y : Finset (Site Λ))
    (hXY : Disjoint X Y) (w : ℝ) :
    Matrix (RegionalConfiguration q X × RegionalConfiguration q Y)
      (RegionalConfiguration q X × RegionalConfiguration q Y) ℂ :=
  Entropy.restoringBasisCoordinates (reducedState_isHermitian Λ q Ω X).eigenvectorUnitary
    ((typicalProjection Λ q Ω (X ∪ Y) w).submatrix
      (FiniteProduct.unionEquiv (fun _ : Site Λ ↦ Fin q) X Y hXY).symm
      (FiniteProduct.unionEquiv (fun _ : Site Λ ↦ Fin q) X Y hXY).symm)

/-- The eigenbasis change on `X`, extended by the identity on `Y`, is unitary. -/
private theorem eigen_kronecker_unitary (Ω : StateSpace Λ q) (X Y : Finset (Site Λ)) :
    let U := ((reducedState_isHermitian Λ q Ω X).eigenvectorUnitary :
      Matrix (RegionalConfiguration q X) (RegionalConfiguration q X) ℂ)
    (Uᴴ ⊗ₖ (1 : Matrix (RegionalConfiguration q Y) (RegionalConfiguration q Y) ℂ))ᴴ =
        U ⊗ₖ (1 : Matrix (RegionalConfiguration q Y) (RegionalConfiguration q Y) ℂ) ∧
      (U ⊗ₖ (1 : Matrix (RegionalConfiguration q Y) (RegionalConfiguration q Y) ℂ)) *
        (Uᴴ ⊗ₖ (1 : Matrix (RegionalConfiguration q Y) (RegionalConfiguration q Y) ℂ)) = 1 ∧
      U * Uᴴ = 1 := by
  intro U
  have h2 : U * Uᴴ = 1 := by
    simp only [U, ← star_eq_conjTranspose]; exact Unitary.coe_mul_star_self _
  exact ⟨by rw [conjTranspose_kronecker, conjTranspose_conjTranspose, conjTranspose_one],
    by rw [← mul_kronecker_mul, h2, Matrix.one_mul, one_kronecker_one], h2⟩

/-- The reduced density of the restoring vector on `X ⊗ Y` is `ρ_{S₀}` conjugated into
the eigenbasis of `ρ_X`. -/
theorem restoringReducedDensity_restoringVector (Ω : StateSpace Λ q)
    (X Y : Finset (Site Λ)) (hXY : Disjoint X Y) :
    Entropy.restoringReducedDensity (restoringVector Ω X Y hXY) =
      (((reducedState_isHermitian Λ q Ω X).eigenvectorUnitary :
          Matrix (RegionalConfiguration q X) (RegionalConfiguration q X) ℂ)ᴴ ⊗ₖ
          (1 : Matrix (RegionalConfiguration q Y) (RegionalConfiguration q Y) ℂ)) *
        (reducedState Λ q Ω (X ∪ Y)).submatrix
          (FiniteProduct.unionEquiv (fun _ : Site Λ ↦ Fin q) X Y hXY).symm
          (FiniteProduct.unionEquiv (fun _ : Site Λ ↦ Fin q) X Y hXY).symm *
        (((reducedState_isHermitian Λ q Ω X).eigenvectorUnitary :
          Matrix (RegionalConfiguration q X) (RegionalConfiguration q X) ℂ) ⊗ₖ
          (1 : Matrix (RegionalConfiguration q Y) (RegionalConfiguration q Y) ℂ)) := by
  obtain ⟨hW, -, -⟩ := eigen_kronecker_unitary Ω X Y
  set W := (((reducedState_isHermitian Λ q Ω X).eigenvectorUnitary :
    Matrix (RegionalConfiguration q X) (RegionalConfiguration q X) ℂ)ᴴ ⊗ₖ
    (1 : Matrix (RegionalConfiguration q Y) (RegionalConfiguration q Y) ℂ))
  set φ : (RegionalConfiguration q X × RegionalConfiguration q Y) ×
      RegionalConfiguration q (X ∪ Y)ᶜ → ℂ :=
    fun i ↦ Ω ((restoringSplit q X Y hXY).symm i)
  set I₃ := (1 : Matrix (RegionalConfiguration q (X ∪ Y)ᶜ)
    (RegionalConfiguration q (X ∪ Y)ᶜ) ℂ)
  have hvec : vecMulVec (restoringVector Ω X Y hXY).ofLp
      (star (restoringVector Ω X Y hXY).ofLp) =
      (W ⊗ₖ I₃) * vecMulVec φ (star φ) * (Wᴴ ⊗ₖ I₃) := by
    have h1 : (W ⊗ₖ I₃)ᴴ = Wᴴ ⊗ₖ I₃ := by rw [conjTranspose_kronecker, conjTranspose_one]
    rw [← h1, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.vecMul_conjTranspose,
      star_star]
    rfl
  have hφ : partialTraceRight (vecMulVec φ (star φ)) =
      (reducedState Λ q Ω (X ∪ Y)).submatrix
        (FiniteProduct.unionEquiv (fun _ : Site Λ ↦ Fin q) X Y hXY).symm
        (FiniteProduct.unionEquiv (fun _ : Site Λ ↦ Fin q) X Y hXY).symm := by
    ext a b
    rw [reducedState_eq_finiteProduct]
    simp only [partialTraceRight_apply, vecMulVec_apply, Pi.star_apply, submatrix_apply,
      FiniteProduct.reducedPure, FiniteProduct.reducedMatrix_apply, φ]
    rfl
  rw [Entropy.restoringReducedDensity, hvec, partialTraceRight_kronecker_one_mul_mul, hφ, hW]

/-- The `X`-marginal of the restoring vector is diagonal, with the eigenvalues of `ρ_X`
on the diagonal. Source: `09-amplification.tex`, lines 324–329. -/
theorem partialTraceRight_restoringReducedDensity_restoringVector (Ω : StateSpace Λ q)
    (X Y : Finset (Site Λ)) (hXY : Disjoint X Y) :
    partialTraceRight (Entropy.restoringReducedDensity (restoringVector Ω X Y hXY)) =
      diagonal fun x ↦ ((reducedState_isHermitian Λ q Ω X).eigenvalues x : ℂ) := by
  have hX : partialTraceRight ((reducedState Λ q Ω (X ∪ Y)).submatrix
      (FiniteProduct.unionEquiv (fun _ : Site Λ ↦ Fin q) X Y hXY).symm
      (FiniteProduct.unionEquiv (fun _ : Site Λ ↦ Fin q) X Y hXY).symm) =
      reducedState Λ q Ω X := by
    rw [reducedState_eq_finiteProduct, reducedState_eq_finiteProduct]
    exact FiniteProduct.partialTraceRight_reducedMatrix_union _ _ X Y hXY
  rw [restoringReducedDensity_restoringVector, partialTraceRight_kronecker_one_mul_mul, hX]
  have h := (reducedState_isHermitian Λ q Ω X).conjStarAlgAut_star_eigenvectorUnitary
  rw [Unitary.conjStarAlgAut_apply, Unitary.coe_star, star_star, star_eq_conjTranspose] at h
  exact h

/-- The `Y`-marginal of the restoring vector is the regional state `ρ_Y`. -/
theorem partialTraceLeft_restoringReducedDensity_restoringVector (Ω : StateSpace Λ q)
    (X Y : Finset (Site Λ)) (hXY : Disjoint X Y) :
    partialTraceLeft (Entropy.restoringReducedDensity (restoringVector Ω X Y hXY)) =
      reducedState Λ q Ω Y := by
  obtain ⟨-, -, h2⟩ := eigen_kronecker_unitary Ω X Y
  rw [restoringReducedDensity_restoringVector, partialTraceLeft_kronecker_one_conj h2,
    reducedState_eq_finiteProduct, reducedState_eq_finiteProduct]
  exact FiniteProduct.partialTraceLeft_reducedMatrix_union _ _ X Y hXY

/-- The restoring vector of a unit vector is a unit vector. -/
theorem norm_restoringVector (Ω : StateSpace Λ q) (hΩ : ‖Ω‖ = 1)
    (X Y : Finset (Site Λ)) (hXY : Disjoint X Y) :
    ‖restoringVector Ω X Y hXY‖ = 1 := by
  set ψ := restoringVector Ω X Y hXY
  have htr : (vecMulVec ψ.ofLp (star ψ.ofLp)).trace = 1 := by
    rw [← trace_partialTraceRight, ← Entropy.restoringReducedDensity,
      ← trace_partialTraceLeft, partialTraceLeft_restoringReducedDensity_restoringVector,
      trace_reducedState Ω hΩ]
  have hsq : ‖ψ‖ ^ 2 = 1 := by
    have h := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) ψ
    rw [EuclideanSpace.inner_eq_star_dotProduct, ← trace_vecMulVec, htr] at h
    have h' := congrArg Complex.re h
    simp only [Complex.one_re] at h'
    rw [h']
    norm_cast
  nlinarith [norm_nonneg ψ]

/-- The expectation of `N ⊗ 1` is the trace against the reduced density of the first
factor. -/
private theorem trace_vecMulVec_kronecker_one {A Z : Type*} [Fintype A]
    [Fintype Z] [DecidableEq Z] (ψ : EuclideanSpace ℂ (A × Z)) (N : Matrix A A ℂ) :
    (vecMulVec ψ.ofLp (star ψ.ofLp) * (N ⊗ₖ (1 : Matrix Z Z ℂ))).trace =
      (partialTraceRight (vecMulVec ψ.ofLp (star ψ.ofLp)) * N).trace :=
  (trace_partialTraceRight_mul N _).symm

/-- **First failure bound of `eq:amplification-adjoint-error`.** In the eigenbasis of
`ρ_X`, the typical projection `P_X` is the selected coordinate projection. It moves the
restoring vector by at most `√δ` when `1 - tr(ρ_X P_X) ≤ δ`.
Source: `09-amplification.tex`, lines 409–415. -/
theorem norm_selectedProjection_restoringVector_sub_le (Ω : StateSpace Λ q)
    (hΩ : ‖Ω‖ = 1) (X Y : Finset (Site Λ)) (hXY : Disjoint X Y) (w δ : ℝ)
    (hδ : 1 - (reducedState Λ q Ω X * typicalProjection Λ q Ω X w).trace.re ≤ δ) :
    ‖WithLp.toLp 2 (((Entropy.restoringSelectedProjection
        (Entropy.typicalSet (reducedState_isHermitian Λ q Ω X).eigenvalues
          (regionalEntropy Λ q Ω X) w) ⊗ₖ
        (1 : Matrix (RegionalConfiguration q Y) (RegionalConfiguration q Y) ℂ)) ⊗ₖ
        (1 : Matrix (RegionalConfiguration q (X ∪ Y)ᶜ)
          (RegionalConfiguration q (X ∪ Y)ᶜ) ℂ)) *ᵥ
          (restoringVector Ω X Y hXY).ofLp) - restoringVector Ω X Y hXY‖ ≤ √δ := by
  set E := Entropy.typicalSet (reducedState_isHermitian Λ q Ω X).eigenvalues
    (regionalEntropy Λ q Ω X) w
  set I₂ := (1 : Matrix (RegionalConfiguration q Y) (RegionalConfiguration q Y) ℂ)
  set I₃ := (1 : Matrix (RegionalConfiguration q (X ∪ Y)ᶜ)
    (RegionalConfiguration q (X ∪ Y)ᶜ) ℂ)
  have hP : IsStarProjection (Entropy.restoringSelectedProjection E) :=
    ⟨Entropy.restoringSelectedProjection_mul_self E,
      Entropy.restoringSelectedProjection_isHermitian E⟩
  have hPP := isStarProjection_kronecker
    (isStarProjection_kronecker hP (IsStarProjection.one (Matrix (RegionalConfiguration q Y)
      (RegionalConfiguration q Y) ℂ)))
    (IsStarProjection.one (Matrix (RegionalConfiguration q (X ∪ Y)ᶜ)
      (RegionalConfiguration q (X ∪ Y)ᶜ) ℂ))
  have hmass : (reducedState Λ q Ω X * typicalProjection Λ q Ω X w).trace =
      (vecMulVec (restoringVector Ω X Y hXY).ofLp (star (restoringVector Ω X Y hXY).ofLp) *
        ((Entropy.restoringSelectedProjection E ⊗ₖ I₂) ⊗ₖ I₃)).trace := by
    rw [trace_vecMulVec_kronecker_one (restoringVector Ω X Y hXY)]
    change _ = (Entropy.restoringReducedDensity (restoringVector Ω X Y hXY) * _).trace
    rw [← trace_partialTraceRight_mul (Entropy.restoringSelectedProjection E),
      partialTraceRight_restoringReducedDensity_restoringVector, typicalProjection,
      trace_mul_spectralSelection, Entropy.restoringSelectedProjection,
      diagonal_mul_diagonal, trace_diagonal, IsHermitian.spectralRestrictionMass]
    push_cast
    simp only [mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_mem, Finset.univ_inter]
  have hsq := norm_projection_mulVec_sub_sq hPP (restoringVector Ω X Y hXY)
  rw [norm_restoringVector Ω hΩ X Y hXY, ← hmass] at hsq
  exact Real.le_sqrt_of_sq_le (by rw [hsq]; linarith)

/-- **Second failure bound of `eq:amplification-adjoint-error`.** The typical projection
`T_Y` moves the restoring vector by at most `√δ` when `1 - tr(ρ_Y T_Y) ≤ δ`.
Source: `09-amplification.tex`, lines 409–415. -/
theorem norm_typicalProjection_restoringVector_sub_le (Ω : StateSpace Λ q)
    (hΩ : ‖Ω‖ = 1) (X Y : Finset (Site Λ)) (hXY : Disjoint X Y) (w δ : ℝ)
    (hδ : 1 - (reducedState Λ q Ω Y * typicalProjection Λ q Ω Y w).trace.re ≤ δ) :
    ‖WithLp.toLp 2 ((((1 : Matrix (RegionalConfiguration q X)
          (RegionalConfiguration q X) ℂ) ⊗ₖ typicalProjection Λ q Ω Y w) ⊗ₖ
        (1 : Matrix (RegionalConfiguration q (X ∪ Y)ᶜ)
          (RegionalConfiguration q (X ∪ Y)ᶜ) ℂ)) *ᵥ
          (restoringVector Ω X Y hXY).ofLp) - restoringVector Ω X Y hXY‖ ≤ √δ := by
  set I₁ := (1 : Matrix (RegionalConfiguration q X) (RegionalConfiguration q X) ℂ)
  set I₃ := (1 : Matrix (RegionalConfiguration q (X ∪ Y)ᶜ)
    (RegionalConfiguration q (X ∪ Y)ᶜ) ℂ)
  have hT := (typicalProjection_failure_le_surprisalTail Ω hΩ Y w).1
  have hPP := isStarProjection_kronecker
    (isStarProjection_kronecker (IsStarProjection.one (Matrix (RegionalConfiguration q X)
      (RegionalConfiguration q X) ℂ)) hT)
    (IsStarProjection.one (Matrix (RegionalConfiguration q (X ∪ Y)ᶜ)
      (RegionalConfiguration q (X ∪ Y)ᶜ) ℂ))
  have hmass : (reducedState Λ q Ω Y * typicalProjection Λ q Ω Y w).trace =
      (vecMulVec (restoringVector Ω X Y hXY).ofLp (star (restoringVector Ω X Y hXY).ofLp) *
        ((I₁ ⊗ₖ typicalProjection Λ q Ω Y w) ⊗ₖ I₃)).trace := by
    rw [trace_vecMulVec_kronecker_one (restoringVector Ω X Y hXY)]
    change _ = (Entropy.restoringReducedDensity (restoringVector Ω X Y hXY) * _).trace
    rw [← trace_partialTraceLeft_mul,
      partialTraceLeft_restoringReducedDensity_restoringVector]
  have hsq := norm_projection_mulVec_sub_sq hPP (restoringVector Ω X Y hXY)
  rw [norm_restoringVector Ω hΩ X Y hXY, ← hmass] at hsq
  exact Real.le_sqrt_of_sq_le (by rw [hsq]; linarith)

/-- The cut projection is the typical projection of `S₀ = X ∪ Y` conjugated into the
eigenbasis of `ρ_X`. -/
theorem restoringCutProjection_eq (Ω : StateSpace Λ q) (X Y : Finset (Site Λ))
    (hXY : Disjoint X Y) (w : ℝ) :
    restoringCutProjection Ω X Y hXY w =
      (((reducedState_isHermitian Λ q Ω X).eigenvectorUnitary :
          Matrix (RegionalConfiguration q X) (RegionalConfiguration q X) ℂ)ᴴ ⊗ₖ
          (1 : Matrix (RegionalConfiguration q Y) (RegionalConfiguration q Y) ℂ)) *
        (typicalProjection Λ q Ω (X ∪ Y) w).submatrix
          (FiniteProduct.unionEquiv (fun _ : Site Λ ↦ Fin q) X Y hXY).symm
          (FiniteProduct.unionEquiv (fun _ : Site Λ ↦ Fin q) X Y hXY).symm *
        (((reducedState_isHermitian Λ q Ω X).eigenvectorUnitary :
          Matrix (RegionalConfiguration q X) (RegionalConfiguration q X) ℂ) ⊗ₖ
          (1 : Matrix (RegionalConfiguration q Y) (RegionalConfiguration q Y) ℂ)) := rfl

/-- The cut projection is an orthogonal projection commuting with the reduced density of
the restoring vector, as `Q_{S₀}` commutes with `ρ_{S₀}`.
Source: `09-amplification.tex`, lines 304–313 and 422–424. -/
theorem restoringCutProjection_isStarProjection_commute (Ω : StateSpace Λ q)
    (hΩ : ‖Ω‖ = 1) (X Y : Finset (Site Λ)) (hXY : Disjoint X Y) (w : ℝ) :
    IsStarProjection (restoringCutProjection Ω X Y hXY w) ∧
      Commute (Entropy.restoringReducedDensity (restoringVector Ω X Y hXY))
        (restoringCutProjection Ω X Y hXY w) := by
  obtain ⟨hW, hWW, -⟩ := eigen_kronecker_unitary Ω X Y
  obtain ⟨hP, hc, -, -⟩ := typicalProjection_failure_le_surprisalTail Ω hΩ (X ∪ Y) w
  set e := (FiniteProduct.unionEquiv (fun _ : Site Λ ↦ Fin q) X Y hXY).symm
  set W := (((reducedState_isHermitian Λ q Ω X).eigenvectorUnitary :
    Matrix (RegionalConfiguration q X) (RegionalConfiguration q X) ℂ)ᴴ ⊗ₖ
    (1 : Matrix (RegionalConfiguration q Y) (RegionalConfiguration q Y) ℂ))
  set P' := (typicalProjection Λ q Ω (X ∪ Y) w).submatrix e e
  set ρ' := (reducedState Λ q Ω (X ∪ Y)).submatrix e e
  have hQ : restoringCutProjection Ω X Y hXY w = W * P' * Wᴴ := by
    rw [restoringCutProjection_eq, hW]
  have hρ : Entropy.restoringReducedDensity (restoringVector Ω X Y hXY) = W * ρ' * Wᴴ := by
    rw [restoringReducedDensity_restoringVector, hW]
  have hWW' : Wᴴ * W = 1 := by rw [hW]; exact hWW
  have hP' : P' * P' = P' := by
    simp only [P', submatrix_mul_equiv, hP.isIdempotentElem.eq]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · change restoringCutProjection Ω X Y hXY w * restoringCutProjection Ω X Y hXY w =
      restoringCutProjection Ω X Y hXY w
    rw [hQ]
    calc W * P' * Wᴴ * (W * P' * Wᴴ) = W * (P' * (Wᴴ * W) * P') * Wᴴ := by
          simp only [Matrix.mul_assoc]
      _ = W * P' * Wᴴ := by rw [hWW', Matrix.mul_one, hP']
  · change (restoringCutProjection Ω X Y hXY w)ᴴ = restoringCutProjection Ω X Y hXY w
    rw [hQ, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose,
      Matrix.mul_assoc, conjTranspose_submatrix, show (typicalProjection Λ q Ω (X ∪ Y) w)ᴴ =
        typicalProjection Λ q Ω (X ∪ Y) w from hP.isSelfAdjoint]
  · rw [hQ, hρ]
    have hcomm : ρ' * P' = P' * ρ' := by
      simp only [ρ', P', submatrix_mul_equiv]
      rw [hc.eq]
    change W * ρ' * Wᴴ * (W * P' * Wᴴ) = W * P' * Wᴴ * (W * ρ' * Wᴴ)
    calc W * ρ' * Wᴴ * (W * P' * Wᴴ) = W * (ρ' * (Wᴴ * W) * P') * Wᴴ := by
          simp only [Matrix.mul_assoc]
      _ = W * (P' * (Wᴴ * W) * ρ') * Wᴴ := by
          rw [hWW', Matrix.mul_one, Matrix.mul_one, hcomm]
      _ = W * P' * Wᴴ * (W * ρ' * Wᴴ) := by simp only [Matrix.mul_assoc]

/-- **Third failure bound of `eq:amplification-adjoint-error`.** The cut projection
moves the restoring vector by at most `√δ` when `1 - tr(ρ_{S₀} Q_{S₀}) ≤ δ`.
Source: `09-amplification.tex`, lines 409–415. -/
theorem norm_restoringCutProjection_restoringVector_sub_le (Ω : StateSpace Λ q)
    (hΩ : ‖Ω‖ = 1) (X Y : Finset (Site Λ)) (hXY : Disjoint X Y) (w δ : ℝ)
    (hδ : 1 - (reducedState Λ q Ω (X ∪ Y) * typicalProjection Λ q Ω (X ∪ Y) w).trace.re ≤
      δ) :
    ‖WithLp.toLp 2 ((restoringCutProjection Ω X Y hXY w ⊗ₖ
        (1 : Matrix (RegionalConfiguration q (X ∪ Y)ᶜ)
          (RegionalConfiguration q (X ∪ Y)ᶜ) ℂ)) *ᵥ
          (restoringVector Ω X Y hXY).ofLp) - restoringVector Ω X Y hXY‖ ≤ √δ := by
  obtain ⟨hW, hWW, -⟩ := eigen_kronecker_unitary Ω X Y
  have hPP := isStarProjection_kronecker
    (restoringCutProjection_isStarProjection_commute Ω hΩ X Y hXY w).1
    (IsStarProjection.one (Matrix (RegionalConfiguration q (X ∪ Y)ᶜ)
      (RegionalConfiguration q (X ∪ Y)ᶜ) ℂ))
  set e := (FiniteProduct.unionEquiv (fun _ : Site Λ ↦ Fin q) X Y hXY).symm
  set W := (((reducedState_isHermitian Λ q Ω X).eigenvectorUnitary :
    Matrix (RegionalConfiguration q X) (RegionalConfiguration q X) ℂ)ᴴ ⊗ₖ
    (1 : Matrix (RegionalConfiguration q Y) (RegionalConfiguration q Y) ℂ))
  have hmass : (reducedState Λ q Ω (X ∪ Y) * typicalProjection Λ q Ω (X ∪ Y) w).trace =
      (vecMulVec (restoringVector Ω X Y hXY).ofLp (star (restoringVector Ω X Y hXY).ofLp) *
        (restoringCutProjection Ω X Y hXY w ⊗ₖ
          (1 : Matrix (RegionalConfiguration q (X ∪ Y)ᶜ)
            (RegionalConfiguration q (X ∪ Y)ᶜ) ℂ))).trace := by
    rw [trace_vecMulVec_kronecker_one (restoringVector Ω X Y hXY)]
    change _ = (Entropy.restoringReducedDensity (restoringVector Ω X Y hXY) * _).trace
    rw [restoringReducedDensity_restoringVector, restoringCutProjection_eq, ← hW]
    change _ = (W * _ * Wᴴ * (W * _ * Wᴴ)).trace
    have hWW' : Wᴴ * W = 1 := by rw [hW]; exact hWW
    rw [show W * (reducedState Λ q Ω (X ∪ Y)).submatrix e e * Wᴴ *
        (W * (typicalProjection Λ q Ω (X ∪ Y) w).submatrix e e * Wᴴ) =
        W * ((reducedState Λ q Ω (X ∪ Y)).submatrix e e * (Wᴴ * W) *
          (typicalProjection Λ q Ω (X ∪ Y) w).submatrix e e) * Wᴴ by
          simp only [Matrix.mul_assoc],
      hWW', Matrix.mul_one, trace_mul_cycle, hWW', Matrix.one_mul, submatrix_mul_equiv,
      trace_submatrix_equiv]
  have hsq := norm_projection_mulVec_sub_sq hPP (restoringVector Ω X Y hXY)
  rw [norm_restoringVector Ω hΩ X Y hXY, ← hmass] at hsq
  exact Real.le_sqrt_of_sq_le (by rw [hsq]; linarith)

/-- **Mutual information as an entropy combination.** For disjoint `X, Y` with
`S₀ = X ∪ Y` and `Z' = Λ ∖ S₀`, purity gives `I_Ω(X : Z') = S(X) + S(S₀) - S(Y)`.
No normalization is needed. Source: `09-amplification.tex`, lines 395–397. -/
theorem mutualInformation_compl_eq (Ω : StateSpace Λ q) (X Y : Finset (Site Λ))
    (hXY : Disjoint X Y) :
    FiniteProduct.mutualInformation (fun _ : Site Λ ↦ Fin q) Ω X (X ∪ Y)ᶜ =
      regionalEntropy Λ q Ω X + regionalEntropy Λ q Ω (X ∪ Y) -
        regionalEntropy Λ q Ω Y := by
  have hY : X ∪ (X ∪ Y)ᶜ = Yᶜ := by
    ext v
    simp only [Finset.mem_union, Finset.mem_compl, not_or]
    constructor
    · rintro (hv | ⟨-, hv⟩)
      · exact Finset.disjoint_left.mp hXY hv
      · exact hv
    · intro hv
      by_cases hvX : v ∈ X
      · exact Or.inl hvX
      · exact Or.inr ⟨hvX, hv⟩
  rw [FiniteProduct.mutualInformation, hY, FiniteProduct.entropy_compl,
    FiniteProduct.entropy_compl, regionalEntropy_eq_finiteProduct,
    regionalEntropy_eq_finiteProduct, regionalEntropy_eq_finiteProduct]

/-- **The typical spectral inequalities of `eq:amplification-operator-norm`.** In the
coordinates of the restoring vector, `Q ≤ e^{S(S₀)+w} ρ_{S₀}` and
`T_Y ρ_Y T_Y ≤ e^{-S(Y)+w} T_Y`. Source: `09-amplification.tex`, lines 383–390. -/
theorem restoringCutProjection_le_and_typicalProjection_le (Ω : StateSpace Λ q)
    (X Y : Finset (Site Λ)) (hXY : Disjoint X Y) (w : ℝ) :
    restoringCutProjection Ω X Y hXY w ≤
        Real.exp (regionalEntropy Λ q Ω (X ∪ Y) + w) •
          Entropy.restoringReducedDensity (restoringVector Ω X Y hXY) ∧
      typicalProjection Λ q Ω Y w *
          partialTraceLeft (Entropy.restoringReducedDensity (restoringVector Ω X Y hXY)) *
          typicalProjection Λ q Ω Y w ≤
        Real.exp (-regionalEntropy Λ q Ω Y + w) • typicalProjection Λ q Ω Y w := by
  obtain ⟨hW, -, -⟩ := eigen_kronecker_unitary Ω X Y
  set e := (FiniteProduct.unionEquiv (fun _ : Site Λ ↦ Fin q) X Y hXY).symm
  set W := (((reducedState_isHermitian Λ q Ω X).eigenvectorUnitary :
    Matrix (RegionalConfiguration q X) (RegionalConfiguration q X) ℂ)ᴴ ⊗ₖ
    (1 : Matrix (RegionalConfiguration q Y) (RegionalConfiguration q Y) ℂ))
  constructor
  · have hle := Matrix.PosSemidef.spectralSelection_le_smul
      (reducedState_posSemidef Λ q Ω (X ∪ Y))
      (E := Entropy.typicalSet (reducedState_isHermitian Λ q Ω (X ∪ Y)).eigenvalues
        (regionalEntropy Λ q Ω (X ∪ Y)) w)
      (Real.exp_pos _).le fun i hi ↦ by
        have h := (Entropy.exp_le_of_mem_typicalSet hi).1
        calc (1 : ℝ) = Real.exp (regionalEntropy Λ q Ω (X ∪ Y) + w) *
              Real.exp (-regionalEntropy Λ q Ω (X ∪ Y) - w) := by
              rw [← Real.exp_add]; ring_nf; exact Real.exp_zero.symm
          _ ≤ _ := mul_le_mul_of_nonneg_left h (Real.exp_pos _).le
    rw [Matrix.le_iff] at hle ⊢
    rw [restoringCutProjection_eq, restoringReducedDensity_restoringVector, ← hW]
    change (Real.exp (regionalEntropy Λ q Ω (X ∪ Y) + w) • (W * _ * Wᴴ) -
      W * _ * Wᴴ).PosSemidef
    rw [← Matrix.smul_mul, ← Matrix.mul_smul, ← Matrix.sub_mul, ← Matrix.mul_sub]
    convert (hle.submatrix e).mul_mul_conjTranspose_same W using 2
    congr 1
  · rw [partialTraceLeft_restoringReducedDensity_restoringVector]
    exact Matrix.IsHermitian.spectralSelection_mul_mul_le_smul
      (reducedState_isHermitian Λ q Ω Y) fun i hi ↦
        (Entropy.exp_le_of_mem_typicalSet hi).2

/-- **The restoring operator of the amplification proposition on the lattice.** Let `Ω`
be a unit vector, let `X, Y` be disjoint with `S₀ = X ∪ Y` and `Z' = Λ ∖ S₀`, and let
`w, δ` be real with failure probabilities `1 - tr(ρ_A P_A^w) ≤ δ` for the typical
projections of `A = X, Y, S₀`. Write `p` for the eigenvalues of `ρ_X`, `E` for the
selected eigenvalue indices of `P_X`, `T = T_Y`, `Q` for the cut projection and `ψ` for
`Ω` in the eigenbasis of `ρ_X`. For unit blank vectors on the two ancillas:

* `ψ` is a unit vector;
* `‖R₀‖, ‖B₀‖ ≤ M₀ = exp ((𝓘 + 3w)/2)` with `𝓘 = I_Ω(X : Z')`
  (`eq:amplification-operator-norm`);
* the physical ground component of `R₀ φ` has norm at most one
  (`eq:amplification-ground-component`);
* for every physical operator `L'`, `‖R₀^† L'^† η - φ‖ ≤ 3 √δ + ‖L'^† Ω - Ω‖`
  (`eq:amplification-adjoint-error`).

Source: `09-amplification.tex`, lines 324–447. -/
theorem restoringOperator_estimates (Ω : StateSpace Λ q) (hΩ : ‖Ω‖ = 1)
    (X Y : Finset (Site Λ)) (hXY : Disjoint X Y) (w δ : ℝ)
    (hδX : 1 - (reducedState Λ q Ω X * typicalProjection Λ q Ω X w).trace.re ≤ δ)
    (hδY : 1 - (reducedState Λ q Ω Y * typicalProjection Λ q Ω Y w).trace.re ≤ δ)
    (hδS : 1 - (reducedState Λ q Ω (X ∪ Y) * typicalProjection Λ q Ω (X ∪ Y) w).trace.re ≤
      δ)
    (sBlank xBlank eBlank : RegionalConfiguration q X → ℂ)
    (hs : ‖WithLp.toLp 2 sBlank‖ = 1) (hx : ‖WithLp.toLp 2 xBlank‖ = 1)
    (he : ‖WithLp.toLp 2 eBlank‖ = 1) :
    let p := (reducedState_isHermitian Λ q Ω X).eigenvalues
    let E := Entropy.typicalSet p (regionalEntropy Λ q Ω X) w
    let T := typicalProjection Λ q Ω Y w
    let Q := restoringCutProjection Ω X Y hXY w
    let ψ := restoringVector Ω X Y hXY
    let I := FiniteProduct.mutualInformation (fun _ : Site Λ ↦ Fin q) Ω X (X ∪ Y)ᶜ
    ‖ψ‖ = 1 ∧
      ‖Entropy.restoringOperator E p sBlank xBlank Q T‖ ≤ Real.exp ((I + 3 * w) / 2) ∧
      ‖Entropy.columnOperator E p sBlank eBlank Q T‖ ≤ Real.exp ((I + 3 * w) / 2) ∧
      ‖Entropy.restoringGroundComponent E p sBlank xBlank Q T ψ‖ ≤ 1 ∧
      ∀ L : Matrix ((RegionalConfiguration q X × RegionalConfiguration q Y) ×
          RegionalConfiguration q (X ∪ Y)ᶜ) ((RegionalConfiguration q X ×
            RegionalConfiguration q Y) × RegionalConfiguration q (X ∪ Y)ᶜ) ℂ,
        ‖WithLp.toLp 2 ((Entropy.restoringGlobal E p sBlank xBlank Q T)ᴴ *ᵥ
            ((Entropy.restoringPhysicalLift L)ᴴ *ᵥ (Entropy.restoringRestored p ψ).ofLp)) -
          Entropy.restoringCopy sBlank xBlank ψ‖ ≤
          3 * √δ + ‖WithLp.toLp 2 (Lᴴ *ᵥ ψ.ofLp) - ψ‖ := by
  intro p E T Q ψ I
  have hψ : ‖ψ‖ = 1 := norm_restoringVector Ω hΩ X Y hXY
  have hp : ∀ x ∈ E, 0 < p x := fun x hx ↦ (Entropy.mem_typicalSet.mp hx).1
  have hpX : ∀ x ∈ E, (p x)⁻¹ ≤ Real.exp (regionalEntropy Λ q Ω X + w) := by
    intro x hx
    have h := inv_anti₀ (Real.exp_pos _) (Entropy.exp_le_of_mem_typicalSet hx).1
    rwa [show -regionalEntropy Λ q Ω X - w = -(regionalEntropy Λ q Ω X + w) by ring,
      Real.exp_neg, inv_inv] at h
  obtain ⟨hQ, hρQ⟩ := restoringCutProjection_isStarProjection_commute Ω hΩ X Y hXY w
  have hT : IsStarProjection T := (typicalProjection_failure_le_surprisalTail Ω hΩ Y w).1
  obtain ⟨hQρ, hρY⟩ := restoringCutProjection_le_and_typicalProjection_le Ω X Y hXY w
  obtain ⟨hR, hB⟩ := Entropy.restoringOperators_norm_le_exp E p hp sBlank xBlank eBlank
    hs hx he hQ hT (regionalEntropy Λ q Ω X) (regionalEntropy Λ q Ω (X ∪ Y))
    (regionalEntropy Λ q Ω Y) w I (mutualInformation_compl_eq Ω X Y hXY) hpX hQρ hρY
  refine ⟨hψ, hR, hB, ?_, fun L ↦ ?_⟩
  · exact Entropy.restoringGroundComponent_norm_le_one E p hp sBlank xBlank hs hx ψ hψ hQ
      hρQ hT (partialTraceRight_restoringReducedDensity_restoringVector Ω X Y hXY)
  · exact Entropy.restoringGlobal_adjoint_error_le E p hp sBlank xBlank hs hx hQ hT L ψ √δ
      (norm_selectedProjection_restoringVector_sub_le Ω hΩ X Y hXY w δ hδX)
      (norm_typicalProjection_restoringVector_sub_le Ω hΩ X Y hXY w δ hδY)
      (norm_restoringCutProjection_restoringVector_sub_le Ω hΩ X Y hXY w δ hδS)

/-- The square root of `n^(-2K)` is `n^(-K)`. -/
private theorem sqrt_rpow_neg_two_mul (n K : ℕ) :
    √((n : ℝ) ^ (-(2 * K : ℝ))) = ((n : ℝ) ^ K)⁻¹ := by
  rw [Real.rpow_neg (Nat.cast_nonneg n),
    show (2 * K : ℝ) = ((2 * K : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast, pow_mul',
    ← inv_pow, Real.sqrt_sq (by positivity)]

/-- **The restoring operator at large scales.** Fix `q ≥ 1`, a range `R`, a strength
`J ≥ 0`, a gap `Δ > 0`, `C₀ ≥ 0` and an integer `K`. Beyond a threshold depending only on
these data, the following holds at every scale `n` for every gapped ground vector `Ω` of
a range-`R` Hamiltonian of strength `J` on a finite domain, every two disjoint regions
`X, Y` such that `X`, `Y` and `S₀ = X ∪ Y` have at most `C₀ n` crossing edges each, and
all unit blank vectors. With the typical projections at width `w = n^(3/5)`, the
restoring and column operators have norm at most `exp ((𝓘 + 3w)/2)` with
`𝓘 = I_Ω(X : Z')`, the physical ground component of `R₀ φ` has norm at most one, and
`‖R₀^† L'^† η - φ‖ ≤ 3 n^(-K) + ‖L'^† Ω - Ω‖` for every physical operator `L'`.
This combines `eq:amplification-typical-error` (`δ = n^(-2K)`) with
`restoringOperator_estimates`. Source: `09-amplification.tex`, lines 304–447. -/
theorem exists_restoringOperator_estimates (hq : 1 ≤ q) (R : ℕ) {J : ℝ}
    (hJ : 0 ≤ J) {Δ : ℝ} (hΔ : 0 < Δ) {C₀ : ℝ} (hC₀ : 0 ≤ C₀) (K : ℕ) :
    ∃ N : ℕ, 1 ≤ N ∧
      ∀ (n : ℕ), N ≤ n → ∀ (Λ : Finset (ℤ × ℤ)) (h : LocalHamiltonian Λ q R J)
        (E₀ : ℝ) (Ω : StateSpace Λ q), IsGappedGroundState Λ q h.operator E₀ Ω Δ →
        ∀ (X Y : Finset (Site Λ)) (hXY : Disjoint X Y),
          ((edgeBoundary Λ X).card : ℝ) ≤ C₀ * n →
          ((edgeBoundary Λ Y).card : ℝ) ≤ C₀ * n →
          ((edgeBoundary Λ (X ∪ Y)).card : ℝ) ≤ C₀ * n →
          ∀ (sBlank xBlank eBlank : RegionalConfiguration q X → ℂ),
            ‖WithLp.toLp 2 sBlank‖ = 1 → ‖WithLp.toLp 2 xBlank‖ = 1 →
            ‖WithLp.toLp 2 eBlank‖ = 1 →
            let w := (n : ℝ) ^ ((3 : ℝ) / 5)
            let p := (reducedState_isHermitian Λ q Ω X).eigenvalues
            let E := Entropy.typicalSet p (regionalEntropy Λ q Ω X) w
            let T := typicalProjection Λ q Ω Y w
            let Q := restoringCutProjection Ω X Y hXY w
            let ψ := restoringVector Ω X Y hXY
            let I := FiniteProduct.mutualInformation (fun _ : Site Λ ↦ Fin q) Ω X
              (X ∪ Y)ᶜ
            ‖ψ‖ = 1 ∧
              ‖Entropy.restoringOperator E p sBlank xBlank Q T‖ ≤
                Real.exp ((I + 3 * w) / 2) ∧
              ‖Entropy.columnOperator E p sBlank eBlank Q T‖ ≤
                Real.exp ((I + 3 * w) / 2) ∧
              ‖Entropy.restoringGroundComponent E p sBlank xBlank Q T ψ‖ ≤ 1 ∧
              ∀ L : Matrix ((RegionalConfiguration q X × RegionalConfiguration q Y) ×
                  RegionalConfiguration q (X ∪ Y)ᶜ) ((RegionalConfiguration q X ×
                    RegionalConfiguration q Y) × RegionalConfiguration q (X ∪ Y)ᶜ) ℂ,
                ‖WithLp.toLp 2 ((Entropy.restoringGlobal E p sBlank xBlank Q T)ᴴ *ᵥ
                    ((Entropy.restoringPhysicalLift L)ᴴ *ᵥ
                      (Entropy.restoringRestored p ψ).ofLp)) -
                  Entropy.restoringCopy sBlank xBlank ψ‖ ≤
                  3 * ((n : ℝ) ^ K)⁻¹ + ‖WithLp.toLp 2 (Lᴴ *ᵥ ψ.ofLp) - ψ‖ := by
  obtain ⟨N, hN1, hN⟩ := exists_typicalProjectors_three_cuts (J := J) hq R hJ hΔ hC₀ K
  refine ⟨N, hN1, ?_⟩
  intro n hn Λ h E₀ Ω hgs X Y hXY hX hY hS sBlank xBlank eBlank hs hx he
  have hfail := hN n hn Λ h E₀ Ω hgs X Y (X ∪ Y) hX hY hS
  have hmain := restoringOperator_estimates Ω hgs.1 X Y hXY ((n : ℝ) ^ ((3 : ℝ) / 5))
    ((n : ℝ) ^ (-(2 * K : ℝ))) (hfail X (by simp)).2.2.2 (hfail Y (by simp)).2.2.2
    (hfail (X ∪ Y) (by simp)).2.2.2 sBlank xBlank eBlank hs hx he
  rwa [sqrt_rpow_neg_two_mul] at hmain

end TNLean.PEPS.AreaLaw
