/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Operators.RestoringOperator.TypicalProjectors
import TNLean.PEPS.AreaLaw.Collar.Scales.Exponents
import QICLean.ManyBody.Entropy.Template.TwoFamilies
import QICLean.Channel.Dilation.RestoringNorm
import QICLean.Channel.Dilation.RestoringGroundComponent
import QICLean.Analysis.Isometry.RestoringVectors
import QICLean.ManyBody.Entropy.Filter.SchmidtPinning
import QICLean.ManyBody.Hamiltonian.GroundSpace

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

open ManyBody (IsGapped groundSpace PlaneInteraction)

namespace Matrix

end Matrix

namespace TNLean.PEPS.AreaLaw

/-- Configurations of a region of a finite domain, with `q` levels at each site.
Source: area-law Section 1, the regional tensor factors. -/
abbrev RegionalConfiguration {Λ : Finset (ℤ × ℤ)} (q : ℕ) (A : Finset ↥Λ) :=
  ManyBody.RegionConfig (fun _ : ↥Λ ↦ Fin q) A

/-- Shortcut instance, which keeps instance terms on products of regional
configurations small. -/
instance {Λ : Finset (ℤ × ℤ)} (q : ℕ) (A : Finset ↥Λ) :
    DecidableEq (RegionalConfiguration q A) := inferInstance

/-- Shortcut instance, which keeps instance terms on products of regional
configurations small. -/
instance {Λ : Finset (ℤ × ℤ)} (q : ℕ) (A : Finset ↥Λ) :
    Fintype (RegionalConfiguration q A) := inferInstance

/-- Shortcut instance, which keeps instance terms on products with the configurations of the
complement of a region small. -/
instance {Λ : Finset (ℤ × ℤ)} (q : ℕ) (A : Finset ↥Λ) :
    DecidableEq ({v : ↥Λ // v ∉ A} → Fin q) := inferInstance

/-- Shortcut instance, which keeps instance terms on products with the configurations of the
complement of a region small. -/
instance {Λ : Finset (ℤ × ℤ)} (q : ℕ) (A : Finset ↥Λ) :
    Fintype ({v : ↥Λ // v ∉ A} → Fin q) := inferInstance

variable {Λ : Finset (ℤ × ℤ)} {q : ℕ}

/-- The coordinates `((X, Y), Z')` of the configuration space for disjoint regions
`X, Y`, with `Z' = Λ ∖ (X ∪ Y)`. Source: `09-amplification.tex`, lines 263–268. -/
def restoringSplit (q : ℕ) (X Y : Finset ↥Λ) (hXY : Disjoint X Y) :
    (↥Λ → Fin q) ≃ (RegionalConfiguration q X × RegionalConfiguration q Y) ×
      ({v // v ∉ X ∪ Y} → Fin q) :=
  (ManyBody.cutEquiv (fun _ : ↥Λ ↦ Fin q) (X ∪ Y)).trans
    ((ManyBody.regionUnionEquiv (β := fun _ : ↥Λ ↦ Fin q) hXY).prodCongr (Equiv.refl _))

/-- The vector `Ω` in the coordinates `((X, Y), Z')`, with the factor `X` written in the
full eigenbasis `{|x⟩}` of `ρ_X`. Source: `09-amplification.tex`, lines 324–329. -/
noncomputable def restoringVector (Ω : EuclideanSpace ℂ (↥Λ → Fin q)) (X Y : Finset ↥Λ)
    (hXY : Disjoint X Y) :
    EuclideanSpace ℂ ((RegionalConfiguration q X × RegionalConfiguration q Y) ×
      ({v // v ∉ X ∪ Y} → Fin q)) :=
  WithLp.toLp 2 (((((ManyBody.regionState_isHermitian X Ω).eigenvectorUnitary :
      Matrix (RegionalConfiguration q X) (RegionalConfiguration q X) ℂ)ᴴ ⊗ₖ
      (1 : Matrix (RegionalConfiguration q Y) (RegionalConfiguration q Y) ℂ)) ⊗ₖ
      (1 : Matrix ({v // v ∉ X ∪ Y} → Fin q)
        ({v // v ∉ X ∪ Y} → Fin q) ℂ)) *ᵥ
    fun i ↦ Ω ((restoringSplit q X Y hXY).symm i))

/-- The typical projection `Q = Q_{S₀}` of `S₀ = X ∪ Y` at width `w`, in the
coordinates `(X, Y)` with `X` written in the eigenbasis of `ρ_X`.
Source: `09-amplification.tex`, lines 304–313 and 348–350. -/
noncomputable def restoringCutProjection (Ω : EuclideanSpace ℂ (↥Λ → Fin q)) (X Y : Finset ↥Λ)
    (hXY : Disjoint X Y) (w : ℝ) :
    Matrix (RegionalConfiguration q X × RegionalConfiguration q Y)
      (RegionalConfiguration q X × RegionalConfiguration q Y) ℂ :=
  Entropy.restoringBasisCoordinates (ManyBody.regionState_isHermitian X Ω).eigenvectorUnitary
    ((typicalProjection Λ q Ω (X ∪ Y) w).submatrix
      (ManyBody.regionUnionEquiv (β := fun _ : ↥Λ ↦ Fin q) hXY).symm
      (ManyBody.regionUnionEquiv (β := fun _ : ↥Λ ↦ Fin q) hXY).symm)

/-- The eigenbasis change on `X`, extended by the identity on `Y`, is unitary. -/
private theorem eigen_kronecker_unitary (Ω : EuclideanSpace ℂ (↥Λ → Fin q)) (X Y : Finset ↥Λ) :
    let U := ((ManyBody.regionState_isHermitian X Ω).eigenvectorUnitary :
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
theorem restoringReducedDensity_restoringVector (Ω : EuclideanSpace ℂ (↥Λ → Fin q))
    (X Y : Finset ↥Λ) (hXY : Disjoint X Y) :
    Entropy.restoringReducedDensity (restoringVector Ω X Y hXY) =
      (((ManyBody.regionState_isHermitian X Ω).eigenvectorUnitary :
          Matrix (RegionalConfiguration q X) (RegionalConfiguration q X) ℂ)ᴴ ⊗ₖ
          (1 : Matrix (RegionalConfiguration q Y) (RegionalConfiguration q Y) ℂ)) *
        (ManyBody.regionState Ω (X ∪ Y)).submatrix
          (ManyBody.regionUnionEquiv (β := fun _ : ↥Λ ↦ Fin q) hXY).symm
          (ManyBody.regionUnionEquiv (β := fun _ : ↥Λ ↦ Fin q) hXY).symm *
        (((ManyBody.regionState_isHermitian X Ω).eigenvectorUnitary :
          Matrix (RegionalConfiguration q X) (RegionalConfiguration q X) ℂ) ⊗ₖ
          (1 : Matrix (RegionalConfiguration q Y) (RegionalConfiguration q Y) ℂ)) := by
  obtain ⟨hW, -, -⟩ := eigen_kronecker_unitary Ω X Y
  set W := (((ManyBody.regionState_isHermitian X Ω).eigenvectorUnitary :
    Matrix (RegionalConfiguration q X) (RegionalConfiguration q X) ℂ)ᴴ ⊗ₖ
    (1 : Matrix (RegionalConfiguration q Y) (RegionalConfiguration q Y) ℂ))
  set φ : (RegionalConfiguration q X × RegionalConfiguration q Y) ×
      ({v // v ∉ X ∪ Y} → Fin q) → ℂ :=
    fun i ↦ Ω ((restoringSplit q X Y hXY).symm i)
  set I₃ := (1 : Matrix ({v // v ∉ X ∪ Y} → Fin q)
    ({v // v ∉ X ∪ Y} → Fin q) ℂ)
  have hvec : vecMulVec (restoringVector Ω X Y hXY).ofLp
      (star (restoringVector Ω X Y hXY).ofLp) =
      (W ⊗ₖ I₃) * vecMulVec φ (star φ) * (Wᴴ ⊗ₖ I₃) := by
    have h1 : (W ⊗ₖ I₃)ᴴ = Wᴴ ⊗ₖ I₃ := by rw [conjTranspose_kronecker, conjTranspose_one]
    rw [← h1, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.vecMul_conjTranspose,
      star_star]
    rfl
  have hφ : partialTraceRight (vecMulVec φ (star φ)) =
      (ManyBody.regionState Ω (X ∪ Y)).submatrix
        (ManyBody.regionUnionEquiv (β := fun _ : ↥Λ ↦ Fin q) hXY).symm
        (ManyBody.regionUnionEquiv (β := fun _ : ↥Λ ↦ Fin q) hXY).symm := by
    ext a b
    simp only [partialTraceRight_apply, vecMulVec_apply, Pi.star_apply, submatrix_apply,
      ManyBody.regionState, ManyBody.regionMatrix_apply, φ]
    rfl
  rw [Entropy.restoringReducedDensity, hvec, partialTraceRight_kronecker_one_mul_mul, hφ, hW]

/-- The `X`-marginal of the restoring vector is diagonal, with the eigenvalues of `ρ_X`
on the diagonal. Source: `09-amplification.tex`, lines 324–329. -/
theorem partialTraceRight_restoringReducedDensity_restoringVector
    (Ω : EuclideanSpace ℂ (↥Λ → Fin q))
    (X Y : Finset ↥Λ) (hXY : Disjoint X Y) :
    partialTraceRight (Entropy.restoringReducedDensity (restoringVector Ω X Y hXY)) =
      diagonal fun x ↦ ((ManyBody.regionState_isHermitian X Ω).eigenvalues x : ℂ) := by
  have hX : partialTraceRight ((ManyBody.regionState Ω (X ∪ Y)).submatrix
      (ManyBody.regionUnionEquiv (β := fun _ : ↥Λ ↦ Fin q) hXY).symm
      (ManyBody.regionUnionEquiv (β := fun _ : ↥Λ ↦ Fin q) hXY).symm) =
      ManyBody.regionState Ω X := by
    exact ManyBody.partialTraceRight_regionMatrix_union _ _ X Y hXY
  rw [restoringReducedDensity_restoringVector, partialTraceRight_kronecker_one_mul_mul, hX]
  have h := (ManyBody.regionState_isHermitian X Ω).conjStarAlgAut_star_eigenvectorUnitary
  rw [Unitary.conjStarAlgAut_apply, Unitary.coe_star, star_star, star_eq_conjTranspose] at h
  exact h

/-- The `Y`-marginal of the restoring vector is the regional state `ρ_Y`. -/
theorem partialTraceLeft_restoringReducedDensity_restoringVector (Ω : EuclideanSpace ℂ (↥Λ → Fin q))
    (X Y : Finset ↥Λ) (hXY : Disjoint X Y) :
    partialTraceLeft (Entropy.restoringReducedDensity (restoringVector Ω X Y hXY)) =
      ManyBody.regionState Ω Y := by
  obtain ⟨-, -, h2⟩ := eigen_kronecker_unitary Ω X Y
  rw [restoringReducedDensity_restoringVector, partialTraceLeft_kronecker_one_conj h2]
  exact ManyBody.partialTraceLeft_regionMatrix_union _ _ X Y hXY

/-- The restoring vector of a unit vector is a unit vector. -/
theorem norm_restoringVector (Ω : EuclideanSpace ℂ (↥Λ → Fin q)) (hΩ : ‖Ω‖ = 1)
    (X Y : Finset ↥Λ) (hXY : Disjoint X Y) :
    ‖restoringVector Ω X Y hXY‖ = 1 := by
  set ψ := restoringVector Ω X Y hXY
  have htr : (vecMulVec ψ.ofLp (star ψ.ofLp)).trace = 1 := by
    rw [← trace_partialTraceRight, ← Entropy.restoringReducedDensity,
      ← trace_partialTraceLeft, partialTraceLeft_restoringReducedDensity_restoringVector,
      ManyBody.trace_regionState_eq_one hΩ]
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

/-- A projection `P` on `X ⊗ Y` moves the restoring vector by at most `√δ` when its
mass `t = tr(ρ P)` against the reduced density satisfies `1 - Re t ≤ δ`. -/
private theorem norm_kronecker_one_restoringVector_sub_le (Ω : EuclideanSpace ℂ (↥Λ → Fin q))
    (hΩ : ‖Ω‖ = 1) (X Y : Finset ↥Λ) (hXY : Disjoint X Y) {δ : ℝ}
    {P : Matrix (RegionalConfiguration q X × RegionalConfiguration q Y)
      (RegionalConfiguration q X × RegionalConfiguration q Y) ℂ}
    (hP : IsStarProjection P) {t : ℂ}
    (ht : t = (Entropy.restoringReducedDensity (restoringVector Ω X Y hXY) * P).trace)
    (hδ : 1 - t.re ≤ δ) :
    ‖WithLp.toLp 2 ((P ⊗ₖ (1 : Matrix ({v // v ∉ X ∪ Y} → Fin q)
          ({v // v ∉ X ∪ Y} → Fin q) ℂ)) *ᵥ
          (restoringVector Ω X Y hXY).ofLp) - restoringVector Ω X Y hXY‖ ≤ √δ := by
  have hsq := norm_projection_mulVec_sub_sq
    (isStarProjection_kronecker hP (IsStarProjection.one _)) (restoringVector Ω X Y hXY)
  rw [norm_restoringVector Ω hΩ X Y hXY, trace_vecMulVec_kronecker_one] at hsq
  rw [← Entropy.restoringReducedDensity, ← ht] at hsq
  exact Real.le_sqrt_of_sq_le (by rw [hsq]; linarith)

/-- **First failure bound of `eq:amplification-adjoint-error`.** In the eigenbasis of
`ρ_X`, the typical projection `P_X` is the selected coordinate projection. It moves the
restoring vector by at most `√δ` when `1 - tr(ρ_X P_X) ≤ δ`.
Source: `09-amplification.tex`, lines 409–415. -/
theorem norm_selectedProjection_restoringVector_sub_le (Ω : EuclideanSpace ℂ (↥Λ → Fin q))
    (hΩ : ‖Ω‖ = 1) (X Y : Finset ↥Λ) (hXY : Disjoint X Y) (w δ : ℝ)
    (hδ : 1 - (ManyBody.regionState Ω X * typicalProjection Λ q Ω X w).trace.re ≤ δ) :
    ‖WithLp.toLp 2 (((Entropy.restoringSelectedProjection
        (Entropy.typicalSet (ManyBody.regionState_isHermitian X Ω).eigenvalues
          (ManyBody.regionEntropy Ω X) w) ⊗ₖ
        (1 : Matrix (RegionalConfiguration q Y) (RegionalConfiguration q Y) ℂ)) ⊗ₖ
        (1 : Matrix ({v // v ∉ X ∪ Y} → Fin q)
          ({v // v ∉ X ∪ Y} → Fin q) ℂ)) *ᵥ
          (restoringVector Ω X Y hXY).ofLp) - restoringVector Ω X Y hXY‖ ≤ √δ := by
  set E := Entropy.typicalSet (ManyBody.regionState_isHermitian X Ω).eigenvalues
    (ManyBody.regionEntropy Ω X) w
  have hP : IsStarProjection (Entropy.restoringSelectedProjection E) :=
    ⟨Entropy.restoringSelectedProjection_mul_self E,
      Entropy.restoringSelectedProjection_isHermitian E⟩
  refine norm_kronecker_one_restoringVector_sub_le Ω hΩ X Y hXY
    (isStarProjection_kronecker hP (IsStarProjection.one _)) ?_ hδ
  rw [← trace_partialTraceRight_mul (Entropy.restoringSelectedProjection E),
    partialTraceRight_restoringReducedDensity_restoringVector, typicalProjection,
    trace_mul_spectralSelection, Entropy.restoringSelectedProjection,
    diagonal_mul_diagonal, trace_diagonal, IsHermitian.spectralRestrictionMass]
  push_cast
  simp only [mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_mem, Finset.univ_inter]

/-- **Second failure bound of `eq:amplification-adjoint-error`.** The typical projection
`T_Y` moves the restoring vector by at most `√δ` when `1 - tr(ρ_Y T_Y) ≤ δ`.
Source: `09-amplification.tex`, lines 409–415. -/
theorem norm_typicalProjection_restoringVector_sub_le (Ω : EuclideanSpace ℂ (↥Λ → Fin q))
    (hΩ : ‖Ω‖ = 1) (X Y : Finset ↥Λ) (hXY : Disjoint X Y) (w δ : ℝ)
    (hδ : 1 - (ManyBody.regionState Ω Y * typicalProjection Λ q Ω Y w).trace.re ≤ δ) :
    ‖WithLp.toLp 2 ((((1 : Matrix (RegionalConfiguration q X)
          (RegionalConfiguration q X) ℂ) ⊗ₖ typicalProjection Λ q Ω Y w) ⊗ₖ
        (1 : Matrix ({v // v ∉ X ∪ Y} → Fin q)
          ({v // v ∉ X ∪ Y} → Fin q) ℂ)) *ᵥ
          (restoringVector Ω X Y hXY).ofLp) - restoringVector Ω X Y hXY‖ ≤ √δ := by
  refine norm_kronecker_one_restoringVector_sub_le Ω hΩ X Y hXY
    (isStarProjection_kronecker (IsStarProjection.one _)
      (typicalProjection_failure_le_surprisalTail Ω hΩ Y w).1) ?_ hδ
  rw [← trace_partialTraceLeft_mul,
    partialTraceLeft_restoringReducedDensity_restoringVector]

/-- The cut projection is the typical projection of `S₀ = X ∪ Y` conjugated into the
eigenbasis of `ρ_X`. -/
theorem restoringCutProjection_eq (Ω : EuclideanSpace ℂ (↥Λ → Fin q)) (X Y : Finset ↥Λ)
    (hXY : Disjoint X Y) (w : ℝ) :
    restoringCutProjection Ω X Y hXY w =
      (((ManyBody.regionState_isHermitian X Ω).eigenvectorUnitary :
          Matrix (RegionalConfiguration q X) (RegionalConfiguration q X) ℂ)ᴴ ⊗ₖ
          (1 : Matrix (RegionalConfiguration q Y) (RegionalConfiguration q Y) ℂ)) *
        (typicalProjection Λ q Ω (X ∪ Y) w).submatrix
          (ManyBody.regionUnionEquiv (β := fun _ : ↥Λ ↦ Fin q) hXY).symm
          (ManyBody.regionUnionEquiv (β := fun _ : ↥Λ ↦ Fin q) hXY).symm *
        (((ManyBody.regionState_isHermitian X Ω).eigenvectorUnitary :
          Matrix (RegionalConfiguration q X) (RegionalConfiguration q X) ℂ) ⊗ₖ
          (1 : Matrix (RegionalConfiguration q Y) (RegionalConfiguration q Y) ℂ)) := rfl

/-- The cut projection is an orthogonal projection commuting with the reduced density of
the restoring vector, as `Q_{S₀}` commutes with `ρ_{S₀}`.
Source: `09-amplification.tex`, lines 304–313 and 422–424. -/
theorem restoringCutProjection_isStarProjection_commute (Ω : EuclideanSpace ℂ (↥Λ → Fin q))
    (hΩ : ‖Ω‖ = 1) (X Y : Finset ↥Λ) (hXY : Disjoint X Y) (w : ℝ) :
    IsStarProjection (restoringCutProjection Ω X Y hXY w) ∧
      Commute (Entropy.restoringReducedDensity (restoringVector Ω X Y hXY))
        (restoringCutProjection Ω X Y hXY w) := by
  obtain ⟨hW, hWW, -⟩ := eigen_kronecker_unitary Ω X Y
  obtain ⟨hP, hc, -, -⟩ := typicalProjection_failure_le_surprisalTail Ω hΩ (X ∪ Y) w
  set e := (ManyBody.regionUnionEquiv (β := fun _ : ↥Λ ↦ Fin q) hXY).symm
  set W := (((ManyBody.regionState_isHermitian X Ω).eigenvectorUnitary :
    Matrix (RegionalConfiguration q X) (RegionalConfiguration q X) ℂ)ᴴ ⊗ₖ
    (1 : Matrix (RegionalConfiguration q Y) (RegionalConfiguration q Y) ℂ))
  set P' := (typicalProjection Λ q Ω (X ∪ Y) w).submatrix e e
  set ρ' := (ManyBody.regionState Ω (X ∪ Y)).submatrix e e
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
theorem norm_restoringCutProjection_restoringVector_sub_le (Ω : EuclideanSpace ℂ (↥Λ → Fin q))
    (hΩ : ‖Ω‖ = 1) (X Y : Finset ↥Λ) (hXY : Disjoint X Y) (w δ : ℝ)
    (hδ : 1 - (ManyBody.regionState Ω (X ∪ Y) * typicalProjection Λ q Ω (X ∪ Y) w).trace.re ≤
      δ) :
    ‖WithLp.toLp 2 ((restoringCutProjection Ω X Y hXY w ⊗ₖ
        (1 : Matrix ({v // v ∉ X ∪ Y} → Fin q)
          ({v // v ∉ X ∪ Y} → Fin q) ℂ)) *ᵥ
          (restoringVector Ω X Y hXY).ofLp) - restoringVector Ω X Y hXY‖ ≤ √δ := by
  obtain ⟨hW, hWW, -⟩ := eigen_kronecker_unitary Ω X Y
  refine norm_kronecker_one_restoringVector_sub_le Ω hΩ X Y hXY
    (restoringCutProjection_isStarProjection_commute Ω hΩ X Y hXY w).1 ?_ hδ
  set e := (ManyBody.regionUnionEquiv (β := fun _ : ↥Λ ↦ Fin q) hXY).symm
  set W := (((ManyBody.regionState_isHermitian X Ω).eigenvectorUnitary :
    Matrix (RegionalConfiguration q X) (RegionalConfiguration q X) ℂ)ᴴ ⊗ₖ
    (1 : Matrix (RegionalConfiguration q Y) (RegionalConfiguration q Y) ℂ))
  rw [restoringReducedDensity_restoringVector, restoringCutProjection_eq, ← hW]
  change _ = (W * _ * Wᴴ * (W * _ * Wᴴ)).trace
  have hWW' : Wᴴ * W = 1 := by rw [hW]; exact hWW
  rw [show W * (ManyBody.regionState Ω (X ∪ Y)).submatrix e e * Wᴴ *
      (W * (typicalProjection Λ q Ω (X ∪ Y) w).submatrix e e * Wᴴ) =
      W * ((ManyBody.regionState Ω (X ∪ Y)).submatrix e e * (Wᴴ * W) *
        (typicalProjection Λ q Ω (X ∪ Y) w).submatrix e e) * Wᴴ by
        simp only [Matrix.mul_assoc],
    hWW', Matrix.mul_one, trace_mul_cycle, hWW', Matrix.one_mul, submatrix_mul_equiv,
    trace_submatrix_equiv]

/-- **Mutual information as an entropy combination.** For disjoint `X, Y` with
`S₀ = X ∪ Y` and `Z' = Λ ∖ S₀`, purity gives `I_Ω(X : Z') = S(X) + S(S₀) - S(Y)`.
No normalization is needed. Source: `09-amplification.tex`, lines 395–397. -/
theorem mutualInformation_compl_eq (Ω : EuclideanSpace ℂ (↥Λ → Fin q)) (X Y : Finset ↥Λ)
    (hXY : Disjoint X Y) :
    ManyBody.regionMutualInformation Ω X (X ∪ Y)ᶜ =
      ManyBody.regionEntropy Ω X + ManyBody.regionEntropy Ω (X ∪ Y) -
        ManyBody.regionEntropy Ω Y := by
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
  rw [ManyBody.regionMutualInformation, hY, ManyBody.regionEntropy_compl,
    ManyBody.regionEntropy_compl]

/-- **The typical spectral inequalities of `eq:amplification-operator-norm`.** In the
coordinates of the restoring vector, `Q ≤ e^{S(S₀)+w} ρ_{S₀}` and
`T_Y ρ_Y T_Y ≤ e^{-S(Y)+w} T_Y`. Source: `09-amplification.tex`, lines 383–390. -/
theorem restoringCutProjection_le_and_typicalProjection_le (Ω : EuclideanSpace ℂ (↥Λ → Fin q))
    (X Y : Finset ↥Λ) (hXY : Disjoint X Y) (w : ℝ) :
    restoringCutProjection Ω X Y hXY w ≤
        Real.exp (ManyBody.regionEntropy Ω (X ∪ Y) + w) •
          Entropy.restoringReducedDensity (restoringVector Ω X Y hXY) ∧
      typicalProjection Λ q Ω Y w *
          partialTraceLeft (Entropy.restoringReducedDensity (restoringVector Ω X Y hXY)) *
          typicalProjection Λ q Ω Y w ≤
        Real.exp (-ManyBody.regionEntropy Ω Y + w) • typicalProjection Λ q Ω Y w := by
  obtain ⟨hW, -, -⟩ := eigen_kronecker_unitary Ω X Y
  set e := (ManyBody.regionUnionEquiv (β := fun _ : ↥Λ ↦ Fin q) hXY).symm
  set W := (((ManyBody.regionState_isHermitian X Ω).eigenvectorUnitary :
    Matrix (RegionalConfiguration q X) (RegionalConfiguration q X) ℂ)ᴴ ⊗ₖ
    (1 : Matrix (RegionalConfiguration q Y) (RegionalConfiguration q Y) ℂ))
  constructor
  · have hle := Matrix.PosSemidef.spectralSelection_le_smul
      (ManyBody.regionState_posSemidef (X ∪ Y) Ω)
      (E := Entropy.typicalSet (ManyBody.regionState_isHermitian (X ∪ Y) Ω).eigenvalues
        (ManyBody.regionEntropy Ω (X ∪ Y)) w)
      (Real.exp_pos _).le fun i hi ↦ by
        have h := (Entropy.exp_le_of_mem_typicalSet hi).1
        calc (1 : ℝ) = Real.exp (ManyBody.regionEntropy Ω (X ∪ Y) + w) *
              Real.exp (-ManyBody.regionEntropy Ω (X ∪ Y) - w) := by
              rw [← Real.exp_add]; ring_nf; exact Real.exp_zero.symm
          _ ≤ _ := mul_le_mul_of_nonneg_left h (Real.exp_pos _).le
    rw [Matrix.le_iff] at hle ⊢
    rw [restoringCutProjection_eq, restoringReducedDensity_restoringVector, ← hW]
    change (Real.exp (ManyBody.regionEntropy Ω (X ∪ Y) + w) • (W * _ * Wᴴ) -
      W * _ * Wᴴ).PosSemidef
    rw [← Matrix.smul_mul, ← Matrix.mul_smul, ← Matrix.sub_mul, ← Matrix.mul_sub]
    convert (hle.submatrix e).mul_mul_conjTranspose_same W using 2
    congr 1
  · rw [partialTraceLeft_restoringReducedDensity_restoringVector]
    exact Matrix.IsHermitian.spectralSelection_mul_mul_le_smul
      (ManyBody.regionState_isHermitian Y Ω) fun i hi ↦
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
theorem restoringOperator_estimates (Ω : EuclideanSpace ℂ (↥Λ → Fin q)) (hΩ : ‖Ω‖ = 1)
    (X Y : Finset ↥Λ) (hXY : Disjoint X Y) (w δ : ℝ)
    (hδX : 1 - (ManyBody.regionState Ω X * typicalProjection Λ q Ω X w).trace.re ≤ δ)
    (hδY : 1 - (ManyBody.regionState Ω Y * typicalProjection Λ q Ω Y w).trace.re ≤ δ)
    (hδS : 1 - (ManyBody.regionState Ω (X ∪ Y) * typicalProjection Λ q Ω (X ∪ Y) w).trace.re ≤
      δ)
    (sBlank xBlank eBlank : RegionalConfiguration q X → ℂ)
    (hs : ‖WithLp.toLp 2 sBlank‖ = 1) (hx : ‖WithLp.toLp 2 xBlank‖ = 1)
    (he : ‖WithLp.toLp 2 eBlank‖ = 1) :
    let p := (ManyBody.regionState_isHermitian X Ω).eigenvalues
    let E := Entropy.typicalSet p (ManyBody.regionEntropy Ω X) w
    let T := typicalProjection Λ q Ω Y w
    let Q := restoringCutProjection Ω X Y hXY w
    let ψ := restoringVector Ω X Y hXY
    let I := ManyBody.regionMutualInformation Ω X (X ∪ Y)ᶜ
    ‖ψ‖ = 1 ∧
      ‖Entropy.restoringOperator E p sBlank xBlank Q T‖ ≤ Real.exp ((I + 3 * w) / 2) ∧
      ‖Entropy.columnOperator E p sBlank eBlank Q T‖ ≤ Real.exp ((I + 3 * w) / 2) ∧
      ‖Entropy.restoringGroundComponent E p sBlank xBlank Q T ψ‖ ≤ 1 ∧
      ∀ L : Matrix ((RegionalConfiguration q X × RegionalConfiguration q Y) ×
          ({v // v ∉ X ∪ Y} → Fin q)) ((RegionalConfiguration q X ×
            RegionalConfiguration q Y) × ({v // v ∉ X ∪ Y} → Fin q)) ℂ,
        ‖WithLp.toLp 2 ((Entropy.restoringGlobal E p sBlank xBlank Q T)ᴴ *ᵥ
            ((Entropy.restoringPhysicalLift L)ᴴ *ᵥ (Entropy.restoringRestored p ψ).ofLp)) -
          Entropy.restoringCopy sBlank xBlank ψ‖ ≤
          3 * √δ + ‖WithLp.toLp 2 (Lᴴ *ᵥ ψ.ofLp) - ψ‖ := by
  intro p E T Q ψ I
  have hψ : ‖ψ‖ = 1 := norm_restoringVector Ω hΩ X Y hXY
  have hp : ∀ x ∈ E, 0 < p x := fun x hx ↦ (Entropy.mem_typicalSet.mp hx).1
  have hpX : ∀ x ∈ E, (p x)⁻¹ ≤ Real.exp (ManyBody.regionEntropy Ω X + w) := by
    intro x hx
    have h := inv_anti₀ (Real.exp_pos _) (Entropy.exp_le_of_mem_typicalSet hx).1
    rwa [show -ManyBody.regionEntropy Ω X - w = -(ManyBody.regionEntropy Ω X + w) by ring,
      Real.exp_neg, inv_inv] at h
  obtain ⟨hQ, hρQ⟩ := restoringCutProjection_isStarProjection_commute Ω hΩ X Y hXY w
  have hT : IsStarProjection T := (typicalProjection_failure_le_surprisalTail Ω hΩ Y w).1
  obtain ⟨hQρ, hρY⟩ := restoringCutProjection_le_and_typicalProjection_le Ω X Y hXY w
  obtain ⟨hR, hB⟩ := Entropy.restoringOperators_norm_le_exp E p hp sBlank xBlank eBlank
    hs hx he hQ hT (ManyBody.regionEntropy Ω X) (ManyBody.regionEntropy Ω (X ∪ Y))
    (ManyBody.regionEntropy Ω Y) w I (mutualInformation_compl_eq Ω X Y hXY) hpX hQρ hρY
  refine ⟨hψ, hR, hB, ?_, fun L ↦ ?_⟩
  · exact Entropy.restoringGroundComponent_norm_le_one E p hp sBlank xBlank hs hx ψ hψ hQ
      hρQ hT (partialTraceRight_restoringReducedDensity_restoringVector Ω X Y hXY)
  · exact Entropy.restoringGlobal_adjoint_error_le E p hp sBlank xBlank hs hx hQ hT L ψ √δ
      (norm_selectedProjection_restoringVector_sub_le Ω hΩ X Y hXY w δ hδX)
      (norm_typicalProjection_restoringVector_sub_le Ω hΩ X Y hXY w δ hδY)
      (norm_restoringCutProjection_restoringVector_sub_le Ω hΩ X Y hXY w δ hδS)

/-- The square root of `n^(-2K)` is `n^(-K)`. -/
theorem sqrt_rpow_neg_two_mul (n K : ℕ) :
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
      ∀ (n : ℕ), N ≤ n → ∀ (Λ : Finset (ℤ × ℤ)) (h : PlaneInteraction Λ q R)
          (_ : ∀ X, (h.term X).IsHermitian) (_ : ∀ X, ‖h.term X‖ ≤ J)
        (E₀ : ℝ) (Ω : EuclideanSpace ℂ (↥Λ → Fin q)), ‖Ω‖ = 1 → IsGapped h.hamiltonian E₀ Δ →
        groundSpace h.hamiltonian E₀ = Submodule.span ℂ {Ω} →
        ∀ (X Y : Finset ↥Λ) (hXY : Disjoint X Y),
          ((ManyBody.edgeBoundary (ManyBody.planeDomainGraph Λ) X).card : ℝ) ≤ C₀ * n →
          ((ManyBody.edgeBoundary (ManyBody.planeDomainGraph Λ) Y).card : ℝ) ≤ C₀ * n →
          ((ManyBody.edgeBoundary (ManyBody.planeDomainGraph Λ) (X ∪ Y)).card : ℝ) ≤ C₀ * n →
          ∀ (sBlank xBlank eBlank : RegionalConfiguration q X → ℂ),
            ‖WithLp.toLp 2 sBlank‖ = 1 → ‖WithLp.toLp 2 xBlank‖ = 1 →
            ‖WithLp.toLp 2 eBlank‖ = 1 →
            let w := (n : ℝ) ^ ((3 : ℝ) / 5)
            let p := (ManyBody.regionState_isHermitian X Ω).eigenvalues
            let E := Entropy.typicalSet p (ManyBody.regionEntropy Ω X) w
            let T := typicalProjection Λ q Ω Y w
            let Q := restoringCutProjection Ω X Y hXY w
            let ψ := restoringVector Ω X Y hXY
            let I := ManyBody.regionMutualInformation Ω X
              (X ∪ Y)ᶜ
            ‖ψ‖ = 1 ∧
              ‖Entropy.restoringOperator E p sBlank xBlank Q T‖ ≤
                Real.exp ((I + 3 * w) / 2) ∧
              ‖Entropy.columnOperator E p sBlank eBlank Q T‖ ≤
                Real.exp ((I + 3 * w) / 2) ∧
              ‖Entropy.restoringGroundComponent E p sBlank xBlank Q T ψ‖ ≤ 1 ∧
              ∀ L : Matrix ((RegionalConfiguration q X × RegionalConfiguration q Y) ×
                  ({v // v ∉ X ∪ Y} → Fin q)) ((RegionalConfiguration q X ×
                    RegionalConfiguration q Y) × ({v // v ∉ X ∪ Y} → Fin q)) ℂ,
                ‖WithLp.toLp 2 ((Entropy.restoringGlobal E p sBlank xBlank Q T)ᴴ *ᵥ
                    ((Entropy.restoringPhysicalLift L)ᴴ *ᵥ
                      (Entropy.restoringRestored p ψ).ofLp)) -
                  Entropy.restoringCopy sBlank xBlank ψ‖ ≤
                  3 * ((n : ℝ) ^ K)⁻¹ + ‖WithLp.toLp 2 (Lᴴ *ᵥ ψ.ofLp) - ψ‖ := by
  obtain ⟨N, hN1, hN⟩ := exists_typicalProjectors_three_cuts (J := J) hq R hJ hΔ hC₀ K
  refine ⟨N, hN1, ?_⟩
  intro n hn Λ h hh hhJ E₀ Ω hΩ hgap hspan X Y hXY hX hY hS sBlank xBlank eBlank hs hx he
  have hfail := hN n hn Λ h hh hhJ E₀ Ω hΩ hgap hspan X Y (X ∪ Y) hX hY hS
  have hmain := restoringOperator_estimates Ω hΩ X Y hXY ((n : ℝ) ^ ((3 : ℝ) / 5))
    ((n : ℝ) ^ (-(2 * K : ℝ))) (hfail X (by simp)).2.2.2 (hfail Y (by simp)).2.2.2
    (hfail (X ∪ Y) (by simp)).2.2.2 sBlank xBlank eBlank hs hx he
  rwa [sqrt_rpow_neg_two_mul] at hmain

end TNLean.PEPS.AreaLaw
