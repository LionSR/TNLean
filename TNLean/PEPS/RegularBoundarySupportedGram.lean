/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.RegularBoundaryGibbsSupport
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic

/-!
# The boundary Gram operator on the invariant support

The virtual Gram operator of a regular G-injective map is positive definite
after restriction to the invariant boundary. In the normalized orbit basis
it therefore has a Hermitian logarithm and a finite Gibbs representation.
This conclusion uses injectivity on the support, not an isometry assumption.
It does not establish locality of the logarithm on the original virtual legs.

Source: Schuch, Cirac, and Pérez-García, arXiv:1001.3807,
Definition 5.1 and the regular invariant boundary of Theorem 6.9,
lines 1278–1296 and 2043–2076. The finite Gibbs representation is an
auxiliary fact relevant to arXiv:1903.09439,
Conjecture `gap2Dboundary1dlocal`, lines 980–1024.
-/

open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace TNLean.PEPS

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

/-- Normalized orbit coordinates embed into the invariant virtual boundary.
Source: SCP10, regular orbit sums in Theorem 6.9, lines 2054–2076. -/
noncomputable def regularBoundarySupportEmbedding (n : ℕ) :
    ((Fin n → G) → ℂ) →ₗ[ℂ] ((Fin (n + 1) → G) → ℂ) :=
  (Real.sqrt (Fintype.card G : ℝ) : ℂ)⁻¹ •
    ((regularBoundaryRepresentation (G := G) (n + 1)).invariants.subtype ∘ₗ
      (regularBoundaryInvariantsEquiv n).symm.toLinearMap)

/-- Entries of the normalized orbit embedding. Source: SCP10,
Theorem 6.9, lines 2054–2076. -/
@[simp]
theorem regularBoundarySupportEmbedding_apply (n : ℕ) (a : Fin (n + 1) → G)
    (r : Fin n → G) :
    LinearMap.toMatrix' (regularBoundarySupportEmbedding (G := G) n) a r =
      (Real.sqrt (Fintype.card G : ℝ) : ℂ)⁻¹ *
        if r = (regularBoundaryRelativeEquiv n a).2 then 1 else 0 := by
  simp [regularBoundarySupportEmbedding, regularBoundaryInvariantsEquiv,
    LinearMap.toMatrix'_apply, Pi.single_apply, eq_comm]

omit [DecidableEq G] in
/-- The support embedding takes values in the invariant boundary.
Source: SCP10, Theorem 6.9, lines 2054–2076. -/
theorem regularBoundarySupportEmbedding_mem_invariants (n : ℕ)
    (x : (Fin n → G) → ℂ) :
    regularBoundarySupportEmbedding (G := G) n x ∈
      (regularBoundaryRepresentation (G := G) (n + 1)).invariants := by
  exact Submodule.smul_mem _ _ ((regularBoundaryInvariantsEquiv n).symm x).2

/-- The normalized orbit embedding is isometric for the usual boundary
inner products. Source: SCP10, normalized orbit sums in Theorem 6.9,
lines 2054–2076. -/
theorem regularBoundarySupportEmbedding_conjTranspose_mul (n : ℕ) :
    (LinearMap.toMatrix' (regularBoundarySupportEmbedding (G := G) n)).conjTranspose *
      LinearMap.toMatrix' (regularBoundarySupportEmbedding (G := G) n) = 1 := by
  let c : ℂ := (Real.sqrt (Fintype.card G : ℝ) : ℂ)⁻¹
  have hcol (r : Fin n → G) :
      (fun a => LinearMap.toMatrix' (regularBoundarySupportEmbedding (G := G) n) a r) =
        c • (regularBoundaryOrbitBasis n r).1 := by
    funext a
    simp [regularBoundarySupportEmbedding, regularBoundaryOrbitBasis, c,
      LinearMap.toMatrix'_apply, Pi.basisFun_apply]
  have hnorm : star c * c * (Fintype.card G : ℂ) = 1 := by
    simp only [c, star_inv₀, Complex.star_def, Complex.conj_ofReal]
    rw [Complex.ofReal_sqrt_inv_mul_self _ (Nat.cast_nonneg _)]
    simp [Nat.cast_ne_zero.mpr Fintype.card_ne_zero]
  ext r s
  change star (fun a => LinearMap.toMatrix' (regularBoundarySupportEmbedding (G := G) n) a r) ⬝ᵥ
    (fun a => LinearMap.toMatrix' (regularBoundarySupportEmbedding (G := G) n) a s) = _
  rw [hcol r, hcol s, star_smul, smul_dotProduct, dotProduct_smul,
    regularBoundaryOrbitBasis_dotProduct]
  by_cases h : r = s
  · simp only [h, ite_true, Matrix.one_apply, smul_eq_mul]
    simpa only [mul_assoc] using hnorm
  · simp [h]

/-- The normalized orbit embedding has the invariant projector as its
range projection. Source: SCP10, Theorem 6.9, lines 2054–2076. -/
theorem regularBoundarySupportEmbedding_mul_conjTranspose (n : ℕ) :
    LinearMap.toMatrix' (regularBoundarySupportEmbedding (G := G) n) *
      (LinearMap.toMatrix' (regularBoundarySupportEmbedding (G := G) n)).conjTranspose =
        regularBoundaryProjector (G := G) (n + 1) := by
  ext a b
  rw [regularBoundaryProjector_apply]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply,
    regularBoundarySupportEmbedding_apply]
  by_cases h : (regularBoundaryRelativeEquiv n a).2 =
      (regularBoundaryRelativeEquiv n b).2
  · simp [h,
      Complex.ofReal_sqrt_inv_mul_self _ (Nat.cast_nonneg _)]
  · simp [h,
      mul_ite, ite_mul]

variable {Phys : Type*} [Fintype Phys]

/-- Restrict an open map to normalized invariant boundary coordinates.
Source: SCP10, Definition 5.1 and Theorem 6.9, lines 1278–1296 and 2043–2076. -/
noncomputable def regularBoundaryRestrictedMap (n : ℕ)
    (T : ((Fin (n + 1) → G) → ℂ) →ₗ[ℂ] (Phys → ℂ)) :
    ((Fin n → G) → ℂ) →ₗ[ℂ] (Phys → ℂ) :=
  T ∘ₗ regularBoundarySupportEmbedding (G := G) n

omit [DecidableEq G] [Fintype Phys] in
/-- G-injectivity gives ordinary injectivity in invariant boundary coordinates.
Source: SCP10, Definition 5.1, lines 1278–1296. -/
theorem IsGInjective.injective_regularBoundaryRestrictedMap (n : ℕ)
    {T : ((Fin (n + 1) → G) → ℂ) →ₗ[ℂ] (Phys → ℂ)}
    (hT : IsGInjective (regularBoundaryRepresentation (G := G) (n + 1)) T) :
    Function.Injective (regularBoundaryRestrictedMap n T) := by
  apply (injective_iff_map_eq_zero _).2
  intro x hx
  have hz := hT.injOn_invariants _ (regularBoundarySupportEmbedding_mem_invariants n x) hx
  have hc : (Real.sqrt (Fintype.card G : ℝ) : ℂ)⁻¹ ≠ 0 := by
    exact inv_ne_zero (Complex.ofReal_ne_zero.mpr
      (Real.sqrt_pos.mpr (Nat.cast_pos.mpr Fintype.card_pos)).ne')
  have hzero : ((regularBoundaryInvariantsEquiv n).symm x).1 = 0 :=
    (smul_eq_zero.mp hz).resolve_left hc
  apply (regularBoundaryInvariantsEquiv n).symm.injective
  apply Subtype.ext
  simpa only [map_zero, Submodule.coe_zero] using hzero

/-- The Gram operator in normalized invariant boundary coordinates.
Source: SCP10, Definition 5.1 and Theorem 6.9, lines 1278–1296 and 2043–2076. -/
noncomputable def regularBoundarySupportedGram (n : ℕ)
    (T : ((Fin (n + 1) → G) → ℂ) →ₗ[ℂ] (Phys → ℂ)) :
    Matrix (Fin n → G) (Fin n → G) ℂ :=
  (LinearMap.toMatrix' (regularBoundaryRestrictedMap n T)).conjTranspose *
    LinearMap.toMatrix' (regularBoundaryRestrictedMap n T)

/-- The supported Gram operator is the orthonormal compression of the
full virtual Gram operator. Source: SCP10, Definition 5.1 and the regular
boundary coordinates of Theorem 6.9, lines 1278–1296 and 2054–2076. -/
theorem regularBoundarySupportedGram_eq_compression (n : ℕ)
    (T : ((Fin (n + 1) → G) → ℂ) →ₗ[ℂ] (Phys → ℂ)) :
    regularBoundarySupportedGram n T =
      (LinearMap.toMatrix' (regularBoundarySupportEmbedding (G := G) n)).conjTranspose *
        ((LinearMap.toMatrix' T).conjTranspose * LinearMap.toMatrix' T) *
          LinearMap.toMatrix' (regularBoundarySupportEmbedding (G := G) n) := by
  classical
  simp only [regularBoundarySupportedGram, regularBoundaryRestrictedMap,
    LinearMap.toMatrix'_comp, Matrix.conjTranspose_mul, Matrix.mul_assoc]

/-- A G-injective open map's full virtual Gram operator is recovered from
its restriction to the invariant boundary. Source: SCP10, Definition 5.1
and Theorem 6.9, lines 1278–1296 and 2043–2076. -/
theorem IsGInjective.regularBoundaryGram_eq_support_compression (n : ℕ)
    {T : ((Fin (n + 1) → G) → ℂ) →ₗ[ℂ] (Phys → ℂ)}
    (hT : IsGInjective (regularBoundaryRepresentation (G := G) (n + 1)) T) :
    (LinearMap.toMatrix' T).conjTranspose * LinearMap.toMatrix' T =
      LinearMap.toMatrix' (regularBoundarySupportEmbedding (G := G) n) *
        regularBoundarySupportedGram n T *
          (LinearMap.toMatrix' (regularBoundarySupportEmbedding (G := G) n)).conjTranspose := by
  classical
  let : Invertible (Fintype.card G : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
  have hTP : LinearMap.toMatrix' T * regularBoundaryProjector (G := G) (n + 1) =
      LinearMap.toMatrix' T := by
    rw [regularBoundaryProjector, ← LinearMap.toMatrix'_comp]
    congr 1
    exact LinearMap.ext (apply_averageMap_of_forall_comp_eq hT.invariant)
  symm
  calc
    _ = (LinearMap.toMatrix' T *
        (LinearMap.toMatrix' (regularBoundarySupportEmbedding (G := G) n) *
          (LinearMap.toMatrix'
            (regularBoundarySupportEmbedding (G := G) n)).conjTranspose)).conjTranspose *
      (LinearMap.toMatrix' T *
        (LinearMap.toMatrix' (regularBoundarySupportEmbedding (G := G) n) *
          (LinearMap.toMatrix' (regularBoundarySupportEmbedding (G := G) n)).conjTranspose)) := by
      simp only [regularBoundarySupportedGram_eq_compression, Matrix.conjTranspose_mul,
        Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
    _ = _ := by rw [regularBoundarySupportEmbedding_mul_conjTranspose, hTP]

/-- The boundary Gram operator is positive definite on its invariant support.
Source: SCP10, Definition 5.1, lines 1278–1296. -/
theorem IsGInjective.regularBoundarySupportedGram_posDef (n : ℕ)
    {T : ((Fin (n + 1) → G) → ℂ) →ₗ[ℂ] (Phys → ℂ)}
    (hT : IsGInjective (regularBoundaryRepresentation (G := G) (n + 1)) T) :
    (regularBoundarySupportedGram n T).PosDef := by
  apply Matrix.PosDef.conjTranspose_mul_self
  have hact : (LinearMap.toMatrix' (regularBoundaryRestrictedMap n T)).mulVec =
      regularBoundaryRestrictedMap n T := by
    funext x
    change Matrix.toLin' (LinearMap.toMatrix' (regularBoundaryRestrictedMap n T)) x = _
    rw [Matrix.toLin'_toMatrix']
  rw [hact]
  exact hT.injective_regularBoundaryRestrictedMap n

/-- A finite boundary Hamiltonian on the invariant support.
Source: finite-dimensional consequence of SCP10, Definition 5.1;
compare arXiv:1903.09439, Conjecture `gap2Dboundary1dlocal`. -/
noncomputable def regularBoundaryGramHamiltonian (n : ℕ)
    (T : ((Fin (n + 1) → G) → ℂ) →ₗ[ℂ] (Phys → ℂ)) :
    Matrix (Fin n → G) (Fin n → G) ℂ :=
  -CFC.log (regularBoundarySupportedGram n T)

/-- The supported boundary Hamiltonian is Hermitian.
Source: finite-dimensional logarithm of the invariant boundary Gram operator
of SCP10, Definition 5.1 and Theorem 6.9, lines 1278–1296 and 2043–2076. -/
theorem regularBoundaryGramHamiltonian_isHermitian (n : ℕ)
    (T : ((Fin (n + 1) → G) → ℂ) →ₗ[ℂ] (Phys → ℂ)) :
    (regularBoundaryGramHamiltonian n T).IsHermitian := by
  exact (IsSelfAdjoint.neg IsSelfAdjoint.log).isHermitian

/-- Every regular G-injective open map has a finite Gibbs representation
on its invariant boundary support. No locality or bulk gap is asserted.
Source: auxiliary consequence of SCP10, Definition 5.1, relevant to
arXiv:1903.09439, Conjecture `gap2Dboundary1dlocal`. -/
theorem IsGInjective.regularBoundarySupportedGram_eq_exp (n : ℕ)
    {T : ((Fin (n + 1) → G) → ℂ) →ₗ[ℂ] (Phys → ℂ)}
    (hT : IsGInjective (regularBoundaryRepresentation (G := G) (n + 1)) T) :
    regularBoundarySupportedGram n T =
      NormedSpace.exp (-regularBoundaryGramHamiltonian n T) := by
  rw [regularBoundaryGramHamiltonian, neg_neg]
  exact (CFC.exp_log _ (hT.regularBoundarySupportedGram_posDef n).isStrictlyPositive).symm

/-- The full singular virtual Gram operator is a Gibbs operator compressed
to its invariant support. Source: finite-dimensional consequence of
SCP10, Definition 5.1 and Theorem 6.9, relevant to arXiv:1903.09439,
Conjecture `gap2Dboundary1dlocal`. -/
theorem IsGInjective.regularBoundaryGram_eq_compressed_exp (n : ℕ)
    {T : ((Fin (n + 1) → G) → ℂ) →ₗ[ℂ] (Phys → ℂ)}
    (hT : IsGInjective (regularBoundaryRepresentation (G := G) (n + 1)) T) :
    (LinearMap.toMatrix' T).conjTranspose * LinearMap.toMatrix' T =
      LinearMap.toMatrix' (regularBoundarySupportEmbedding (G := G) n) *
        NormedSpace.exp (-regularBoundaryGramHamiltonian n T) *
          (LinearMap.toMatrix' (regularBoundarySupportEmbedding (G := G) n)).conjTranspose := by
  rw [hT.regularBoundaryGram_eq_support_compression n,
    hT.regularBoundarySupportedGram_eq_exp n]

end TNLean.PEPS
