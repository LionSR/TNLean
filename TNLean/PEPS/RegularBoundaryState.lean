/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.RegularBoundary
import TNLean.Algebra.RepresentationTensorProduct
import TNLean.Algebra.ComplexSqrt
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.Trace
import QICLean.Channel.MaximalOverlap

/-!
# The bipartite regular boundary state

The virtual boundary state used in the proof of Schuch, Cirac, and Pérez-García,
arXiv:1001.3807, Theorem 6.9 (`Papers/1001.3807/paper_v3.tex`, lines 2043–2072),
is the sum over one simultaneous group translation between the two sides of the cut.
Its coefficient matrix is proportional to the invariant-boundary averaging projector.
After normalization, its reduced density operator is that projector divided by its rank.

These statements concern the virtual bipartite state. Identifying it with a physical PEPS
across a cut requires the separate tensor-contraction and local-isometry arguments.
-/

open scoped BigOperators Matrix ComplexOrder
open Module Representation

namespace TNLean.PEPS

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

noncomputable local instance : Invertible (Fintype.card G : ℂ) :=
  invertibleOfNonzero (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)

/-- Source: arXiv:1001.3807, proof of Theorem 6.9, lines 2043–2076. The normalized
average of the simultaneous regular action projects onto invariant boundary vectors. -/
noncomputable def regularBoundaryProjector (b : ℕ) :
    Matrix (Fin b → G) (Fin b → G) ℂ :=
  LinearMap.toMatrix' (regularBoundaryRepresentation (G := G) b).averageMap

/-- The boundary average is idempotent. -/
theorem regularBoundaryProjector_mul_self (b : ℕ) :
    regularBoundaryProjector (G := G) b * regularBoundaryProjector b =
      regularBoundaryProjector b := by
  simpa only [regularBoundaryProjector, Module.End.mul_eq_comp,
    LinearMap.toMatrix'_comp] using congrArg LinearMap.toMatrix'
    (regularBoundaryRepresentation (G := G) b).isProj_averageMap.isIdempotentElem.eq

/-- The boundary projector has exactly the dimension of the invariant boundary space.
Source: arXiv:1001.3807, Theorem 6.9, lines 2027–2037. -/
theorem rank_regularBoundaryProjector (b : ℕ) (hb : 0 < b) :
    (regularBoundaryProjector (G := G) b).rank = Fintype.card G ^ (b - 1) := by
  rw [Matrix.rank_eq_finrank_range_toLin _ (Pi.basisFun ℂ _) (Pi.basisFun ℂ _),
    Matrix.toLin_eq_toLin', regularBoundaryProjector, Matrix.toLin'_toMatrix',
    (regularBoundaryRepresentation (G := G) b).isProj_averageMap.range,
    finrank_regularBoundaryInvariants b hb]

/-- Two boundary configurations have nonzero projector pairing exactly when their
relative coordinates agree. Source: arXiv:1001.3807, proof of Theorem 6.9, lines 2054–2076. -/
theorem regularBoundaryProjector_apply (n : ℕ) (a b : Fin (n + 1) → G) :
    regularBoundaryProjector (G := G) (n + 1) a b =
      if (regularBoundaryRelativeEquiv n a).2 = (regularBoundaryRelativeEquiv n b).2
      then (Fintype.card G : ℂ)⁻¹ else 0 := by
  have hEq (g : G) : g⁻¹ • a = b ↔
      g = a 0 * (b 0)⁻¹ ∧
        (regularBoundaryRelativeEquiv n a).2 = (regularBoundaryRelativeEquiv n b).2 := by
    rw [← (regularBoundaryRelativeEquiv n).injective.eq_iff,
      regularBoundaryRelativeEquiv_smul]
    rw [Prod.ext_iff]
    change (g⁻¹ * a 0 = b 0 ∧
      (regularBoundaryRelativeEquiv n a).2 = (regularBoundaryRelativeEquiv n b).2) ↔
        (g = a 0 * (b 0)⁻¹ ∧
          (regularBoundaryRelativeEquiv n a).2 = (regularBoundaryRelativeEquiv n b).2)
    rw [inv_mul_eq_iff_eq_mul, eq_mul_inv_iff_mul_eq]
    exact and_congr_left fun _ => eq_comm
  rw [regularBoundaryProjector, LinearMap.toMatrix'_apply,
    Representation.averageMap_apply_eq_sum]
  simp only [Pi.smul_apply, Finset.sum_apply, regularBoundaryRepresentation_apply,
    Pi.single_apply, hEq]
  by_cases hr : (regularBoundaryRelativeEquiv n a).2 =
      (regularBoundaryRelativeEquiv n b).2 <;> simp [hr, invOf_eq_inv]

/-- The invariant-boundary average is an orthogonal projector. -/
theorem regularBoundaryProjector_conjTranspose (n : ℕ) :
    (regularBoundaryProjector (G := G) (n + 1)).conjTranspose =
      regularBoundaryProjector (n + 1) := by
  ext a b
  by_cases h : (regularBoundaryRelativeEquiv n a).2 =
      (regularBoundaryRelativeEquiv n b).2 <;>
    simp [Matrix.conjTranspose_apply, regularBoundaryProjector_apply, h, eq_comm]

/-- The boundary projector has trace `|G| ^ n` on `n + 1` legs. -/
theorem trace_regularBoundaryProjector (n : ℕ) :
    (regularBoundaryProjector (G := G) (n + 1)).trace = (Fintype.card G : ℂ) ^ n := by
  have hG : (Fintype.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simp [Matrix.trace, Matrix.diag, regularBoundaryProjector_apply,
    Fintype.card_fin, pow_succ, hG]

/-- The boundary averaging projector is also real symmetric. -/
theorem regularBoundaryProjector_transpose (n : ℕ) :
    (regularBoundaryProjector (G := G) (n + 1)).transpose =
      regularBoundaryProjector (n + 1) := by
  ext a b
  simp [Matrix.transpose_apply, regularBoundaryProjector_apply, eq_comm]

/-- Source: arXiv:1001.3807, proof of Theorem 6.9, lines 2043–2072. The normalized
coefficient matrix of the virtual boundary state is `P / √(|G| ^ n)`. -/
noncomputable def regularBoundarySchmidtMatrix (n : ℕ) :
    Matrix (Fin (n + 1) → G) (Fin (n + 1) → G) ℂ :=
  (Real.sqrt (Fintype.card G ^ n : ℝ) : ℂ)⁻¹ • regularBoundaryProjector (n + 1)

/-- Source: arXiv:1001.3807, proof of Theorem 6.9, lines 2043–2072. The normalized
virtual bipartite vector is obtained by reading its coefficient matrix on the two boundaries. -/
noncomputable def regularBoundaryState (n : ℕ) :
    ((Fin (n + 1) → G) × (Fin (n + 1) → G)) → ℂ :=
  fun p => regularBoundarySchmidtMatrix n p.1 p.2

/-- Source: arXiv:1001.3807, Theorem 6.9, lines 2027–2037. The virtual reduced density
operator is the invariant-boundary projector divided by its rank. -/
noncomputable def regularBoundaryDensity (n : ℕ) :
    Matrix (Fin (n + 1) → G) (Fin (n + 1) → G) ℂ :=
  ((Fintype.card G : ℂ) ^ n)⁻¹ • regularBoundaryProjector (n + 1)

/-- The normalized coefficient matrix is supported on the invariant boundary on its right. -/
theorem regularBoundarySchmidtMatrix_mul_projector (n : ℕ) :
    regularBoundarySchmidtMatrix (G := G) n * regularBoundaryProjector (n + 1) =
      regularBoundarySchmidtMatrix n := by
  simp only [regularBoundarySchmidtMatrix, Matrix.smul_mul,
    regularBoundaryProjector_mul_self]

/-- The normalized coefficient matrix is supported on the invariant boundary on its left. -/
theorem regularBoundaryProjector_mul_schmidtMatrix (n : ℕ) :
    regularBoundaryProjector (G := G) (n + 1) * regularBoundarySchmidtMatrix n =
      regularBoundarySchmidtMatrix n := by
  simp only [regularBoundarySchmidtMatrix, Matrix.mul_smul,
    regularBoundaryProjector_mul_self]

/-- The coefficient matrix squared gives the flat invariant-boundary density operator. -/
theorem regularBoundarySchmidtMatrix_mul_conjTranspose (n : ℕ) :
    regularBoundarySchmidtMatrix (G := G) n * (regularBoundarySchmidtMatrix n).conjTranspose =
      regularBoundaryDensity n := by
  simp only [regularBoundarySchmidtMatrix, regularBoundaryDensity, Matrix.conjTranspose_smul,
    regularBoundaryProjector_conjTranspose, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    regularBoundaryProjector_mul_self]
  congr 1
  simp only [star_inv₀, Complex.star_def, Complex.conj_ofReal]
  simpa only [Complex.ofReal_pow, Complex.ofReal_natCast] using
    Complex.ofReal_sqrt_inv_mul_self (Fintype.card G ^ n : ℝ)
      (pow_nonneg (Nat.cast_nonneg _) _)

/-- Reading the bipartite vector as a coefficient matrix recovers its defining matrix. -/
theorem schmidtCoeffMatrix_regularBoundaryState (n : ℕ) :
    Matrix.schmidtCoeffMatrix (regularBoundaryState (G := G) n) =
      regularBoundarySchmidtMatrix n := rfl

/-- The virtual boundary state has reduced density operator `P / |G| ^ n`.
Source: arXiv:1001.3807, Theorem 6.9 and its proof, lines 2027–2072. -/
theorem partialTrace_regularBoundaryState (n : ℕ) :
    Matrix.partialTraceRight
      (Matrix.vecMulVec (regularBoundaryState (G := G) n) (star (regularBoundaryState n))) =
        regularBoundaryDensity n := by
  rw [Matrix.partialTraceRight_vecMulVec_eq, schmidtCoeffMatrix_regularBoundaryState,
    regularBoundarySchmidtMatrix_mul_conjTranspose]

/-- The virtual boundary density operator is positive semidefinite. -/
theorem regularBoundaryDensity_posSemidef (n : ℕ) :
    (regularBoundaryDensity (G := G) n).PosSemidef := by
  rw [← regularBoundarySchmidtMatrix_mul_conjTranspose]
  exact Matrix.posSemidef_self_mul_conjTranspose _

/-- The normalized virtual boundary density operator has unit trace. -/
theorem trace_regularBoundaryDensity (n : ℕ) :
    (regularBoundaryDensity (G := G) n).trace = 1 := by
  rw [regularBoundaryDensity, Matrix.trace_smul, trace_regularBoundaryProjector]
  simp [Nat.cast_ne_zero.mpr Fintype.card_ne_zero]

/-- The virtual bipartite boundary vector is normalized. -/
theorem regularBoundaryState_dotProduct (n : ℕ) :
    star (regularBoundaryState (G := G) n) ⬝ᵥ regularBoundaryState n = 1 := by
  rw [Matrix.star_dotProduct_eq_trace_conjTranspose_mul,
    schmidtCoeffMatrix_regularBoundaryState, Matrix.trace_mul_comm,
    regularBoundarySchmidtMatrix_mul_conjTranspose, trace_regularBoundaryDensity]

/-- Source: arXiv:1001.3807, Theorem 6.9, lines 2027–2037. The virtual density
operator has rank `|G| ^ n`, the dimension of the invariant boundary space. -/
theorem rank_regularBoundaryDensity (n : ℕ) :
    (regularBoundaryDensity (G := G) n).rank = Fintype.card G ^ n := by
  rw [regularBoundaryDensity, Matrix.rank_smul_of_mem_nonZeroDivisors _
    (mem_nonZeroDivisors_of_ne_zero (inv_ne_zero (pow_ne_zero _
      (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)))),
    rank_regularBoundaryProjector (n + 1) (Nat.succ_pos n)]
  simp

/-- The virtual reduced density operator satisfies the flat-spectrum polynomial.
Source: arXiv:1001.3807, Theorem 6.9, lines 2027–2037. -/
theorem regularBoundaryDensity_mul_self (n : ℕ) :
    regularBoundaryDensity (G := G) n * regularBoundaryDensity n =
      ((Fintype.card G : ℂ) ^ n)⁻¹ • regularBoundaryDensity n := by
  simp only [regularBoundaryDensity, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    regularBoundaryProjector_mul_self]

/-- The boundary averaging projector fixes every invariant boundary vector. -/
theorem regularBoundaryProjector_mulVec_of_mem_invariants (b : ℕ) (x : (Fin b → G) → ℂ)
    (hx : x ∈ (regularBoundaryRepresentation (G := G) b).invariants) :
    regularBoundaryProjector b *ᵥ x = x := by
  change Matrix.toLin' (regularBoundaryProjector b) x = x
  rw [regularBoundaryProjector, Matrix.toLin'_toMatrix',
    Representation.averageMap_id _ x hx]

/-- The virtual reduced density operator acts by `|G| ^ (-n)` on its invariant support.
Source: arXiv:1001.3807, Theorem 6.9, lines 2027–2037. -/
theorem regularBoundaryDensity_mulVec_of_mem_invariants (n : ℕ)
    (x : (Fin (n + 1) → G) → ℂ)
    (hx : x ∈ (regularBoundaryRepresentation (G := G) (n + 1)).invariants) :
    regularBoundaryDensity n *ᵥ x = ((Fintype.card G : ℂ) ^ n)⁻¹ • x := by
  rw [regularBoundaryDensity, Matrix.smul_mulVec,
    regularBoundaryProjector_mulVec_of_mem_invariants _ x hx]

/-- Source: arXiv:1001.3807, proof of Theorem 6.9, lines 2043–2076. The unnormalized
virtual boundary vector sums the `|μ(z)⟩` products over a common group translation `z`. -/
noncomputable def regularBoundaryTranslationState (n : ℕ) :
    ((Fin (n + 1) → G) × (Fin (n + 1) → G)) → ℂ :=
  fun p => ∑ g : G, if p.1 = g • p.2 then 1 else 0

/-- The group-translation boundary vector is `|G|` times the averaging projector.
Source: arXiv:1001.3807, proof of Theorem 6.9, lines 2043–2076. -/
theorem regularBoundaryTranslationState_apply (n : ℕ)
    (a b : Fin (n + 1) → G) :
    regularBoundaryTranslationState n (a, b) =
      (Fintype.card G : ℂ) * regularBoundaryProjector (n + 1) a b := by
  rw [regularBoundaryProjector, LinearMap.toMatrix'_apply,
    Representation.averageMap_apply_eq_sum]
  simp only [regularBoundaryTranslationState, Pi.smul_apply, Finset.sum_apply,
    regularBoundaryRepresentation_apply, Pi.single_apply, smul_eq_mul,
    ← mul_assoc, mul_invOf_self, one_mul, inv_smul_eq_iff]

/-- The translation-state coefficient is the product of the one-leg Kronecker deltas,
summed over a common translation. Source: arXiv:1001.3807, proof of Theorem 6.9,
lines 2043–2076. -/
theorem regularBoundaryTranslationState_eq_sum_prod (n : ℕ)
    (a b : Fin (n + 1) → G) :
    regularBoundaryTranslationState n (a, b) =
      ∑ g : G, ∏ i : Fin (n + 1), if a i = g * b i then (1 : ℂ) else 0 := by
  simp [regularBoundaryTranslationState, Fintype.prod_ite_zero, funext_iff]

/-- The normalized virtual vector is the translation-state vector divided by
`|G| √(|G| ^ n)`. Source: arXiv:1001.3807, proof of Theorem 6.9, lines 2043–2072. -/
theorem regularBoundaryState_eq_smul_translationState (n : ℕ) :
    regularBoundaryState (G := G) n =
      ((Fintype.card G : ℂ)⁻¹ * (Real.sqrt (Fintype.card G ^ n : ℝ) : ℂ)⁻¹) •
        regularBoundaryTranslationState n := by
  have hG : (Fintype.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  funext ⟨a, b⟩
  simp [regularBoundaryState, regularBoundarySchmidtMatrix, Matrix.smul_apply,
    regularBoundaryTranslationState_apply, mul_assoc, mul_left_comm, hG]

end TNLean.PEPS
