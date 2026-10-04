/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.FinSumPermutation
import TNLean.Algebra.ComplexSqrt
import Mathlib.GroupTheory.Subgroup.Centralizer
import TNLean.Algebra.UnitaryVectorSwap
import TNLean.Algebra.PermutationMatrixUnitary
import QICLean.Algebra.MatrixReindexUnitary


/-!
# Normalized conjugacy-class creation on accessible group registers

The sum over conjugating elements retains every centralizer multiplicity. Its
squared norm is |G| times the size of the centralizer. After normalization it is
an invariant unit vector, orthogonal to the identity basis vector unless the
flux is trivial. A reflection exchanges these two vectors and commutes with
conjugation. On a pair of accessible registers, applying this reflection to the
relative coordinate a b⁻¹ leaves the reference register b unchanged.

Source: Schuch, Cirac, and Pérez-García, arXiv:1001.3807, Theorem 6.17,
`eq:anyons:make-chargeless-fluxon`, local source lines 2304–2340. The printed
replacement is an unnormalized sum; the unitary below includes the scalar
(|G| |C_G(g)|)^(-1/2) required to preserve the norm of the diagonal pair.

**Local fix (conjugacy-sum normalization):** The printed conjugacy sum is
multiplied by its positive norm reciprocal so that the operation is unitary.
The exact factor is recorded in
`docs/paper-gaps/rmp_peps_quantum_double_g_isometry.tex`.

**Scope restriction (accessible-register operation):** These are exact finite
Hilbert-space operations. Their implementation on an actual PEPS block and
transport to the original G-isometric physical tensors are separate assertions;
see `docs/paper-gaps/rmp_peps_quantum_double_g_isometry.tex`.
-/

noncomputable section
open scoped BigOperators Matrix Kronecker
namespace TNLean.PEPS
variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

/-- The conjugacy sum, with one summand for each conjugating group element.
Source: SCP10, Theorem 6.17, lines 2304–2340. -/
def regularFluxClassVector (g t : G) : ℂ :=
  ∑ z : G, if t = z * g * z⁻¹ then 1 else 0

/-- The conjugacy sum divided by its exact positive norm.
Source: SCP10, Theorem 6.17, lines 2304–2340. -/
def normalizedRegularFluxClassVector (g : G) : G → ℂ :=
  (Real.sqrt ((Fintype.card G : ℝ) * Nat.card (Subgroup.centralizer ({g} : Set G))) : ℂ)⁻¹ •
    regularFluxClassVector g

private theorem conjugacy_self_count (g z : G) :
    (∑ w : G, if z * g * z⁻¹ = w * g * w⁻¹ then (1 : ℂ) else 0) =
      (Nat.card (Subgroup.centralizer ({g} : Set G)) : ℂ) := by
  classical
  rw [← Equiv.sum_comp (Equiv.mulLeft z)]
  have hi (w : G) : z * g * z⁻¹ = (z * w) * g * (z * w)⁻¹ ↔
      w ∈ Subgroup.centralizer ({g} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    simp only [Set.mem_singleton_iff, forall_eq]
    constructor
    · intro h
      have he := congrArg (fun a => z⁻¹ * a * z) h
      have he' : g = w * g * w⁻¹ := by simpa [mul_assoc] using he
      exact (eq_mul_inv_iff_mul_eq.mp he')
    · intro h
      have he' : g = w * g * w⁻¹ := eq_mul_inv_iff_mul_eq.mpr h
      simpa [mul_assoc] using congrArg (fun a => z * a * z⁻¹) he'
  simp only [Equiv.coe_mulLeft, hi, Nat.card_eq_fintype_card, Fintype.card_subtype,
    Finset.sum_boole]

/-- The squared norm of the conjugacy sum includes the centralizer multiplicity.
Source: SCP10, Theorem 6.17, lines 2304–2340. -/
theorem regularFluxClassVector_dotProduct (g : G) :
    star (regularFluxClassVector g) ⬝ᵥ regularFluxClassVector g =
      (Fintype.card G : ℂ) * Nat.card (Subgroup.centralizer ({g} : Set G)) := by
  simp only [dotProduct, regularFluxClassVector, Pi.star_apply, star_sum, apply_ite star,
    star_one, star_zero, Finset.sum_mul, Finset.mul_sum]
  rw [Fintype.sum_reverse_three]
  simp only [ite_mul, one_mul, zero_mul]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  simp_rw [conjugacy_self_count]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- The conjugacy sum is invariant under every simultaneous conjugation.
Source: SCP10, Theorem 6.17, lines 2304–2340. -/
theorem regularFluxClassVector_conjugation (g x t : G) :
    regularFluxClassVector g (x * t * x⁻¹) = regularFluxClassVector g t := by
  unfold regularFluxClassVector
  rw [← Equiv.sum_comp (Equiv.mulLeft x)]
  apply Finset.sum_congr rfl
  intro z _
  have hi : x * t * x⁻¹ = (x * z) * g * (x * z)⁻¹ ↔ t = z * g * z⁻¹ := by
    constructor
    · intro h
      simpa [mul_assoc] using congrArg (fun a => x⁻¹ * a * x) h
    · intro h
      simpa [mul_assoc] using congrArg (fun a => x * a * x⁻¹) h
  simp only [Equiv.coe_mulLeft, hi]

/-- A nontrivial flux class has no coefficient at the identity.
Source: SCP10, Theorem 6.17, lines 2304–2340. -/
theorem regularFluxClassVector_one_eq_zero {g : G} (hg : g ≠ 1) :
    regularFluxClassVector g 1 = 0 := by
  apply Finset.sum_eq_zero
  intro z _
  apply ite_eq_right
  intro h
  have h' := congrArg (fun a => z⁻¹ * a * z) h
  exact hg (by simpa [mul_assoc] using h'.symm)

/-- The normalized class vector has squared norm one.
Source: SCP10, Theorem 6.17, lines 2304–2340. -/
theorem normalizedRegularFluxClassVector_dotProduct (g : G) :
    star (normalizedRegularFluxClassVector g) ⬝ᵥ normalizedRegularFluxClassVector g = 1 := by
  have hn : (Fintype.card G : ℝ) * Nat.card (Subgroup.centralizer ({g} : Set G)) ≠ 0 :=
    mul_ne_zero (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
      (Nat.cast_ne_zero.mpr (Nat.card_pos (α := Subgroup.centralizer ({g} : Set G))).ne')
  let c : ℂ := (Real.sqrt
    ((Fintype.card G : ℝ) * Nat.card (Subgroup.centralizer ({g} : Set G))) : ℂ)⁻¹
  have hc : star c = c := by simp [c]
  change star (c • regularFluxClassVector g) ⬝ᵥ (c • regularFluxClassVector g) = 1
  rw [star_smul, hc, smul_dotProduct, dotProduct_smul,
    regularFluxClassVector_dotProduct]
  change c * (c * ((Fintype.card G : ℂ) *
    Nat.card (Subgroup.centralizer ({g} : Set G)))) = 1
  rw [← mul_assoc]
  dsimp only [c]
  rw [Complex.ofReal_sqrt_inv_mul_self _ (by positivity)]
  norm_cast
  exact inv_mul_cancel₀ (by simpa only [Nat.cast_mul] using hn)

/-- For nontrivial flux the class vector is orthogonal to the identity basis vector.
Source: SCP10, Theorem 6.17, lines 2304–2340. -/
theorem normalizedRegularFluxClassVector_orthogonal {g : G} (hg : g ≠ 1) :
    star (Pi.single (1 : G) (1 : ℂ)) ⬝ᵥ normalizedRegularFluxClassVector g = 0 := by
  rw [Pi.star_single, star_one, single_dotProduct, one_mul]
  simp only [normalizedRegularFluxClassVector, Pi.smul_apply, smul_eq_mul,
    regularFluxClassVector_one_eq_zero hg, mul_zero]

/-- Normalization preserves conjugation invariance.
Source: SCP10, Theorem 6.17, lines 2304–2340. -/
theorem normalizedRegularFluxClassVector_conjugation (g x t : G) :
    normalizedRegularFluxClassVector g (x * t * x⁻¹) =
      normalizedRegularFluxClassVector g t := by
  change _ * regularFluxClassVector g (x * t * x⁻¹) = _ * regularFluxClassVector g t
  rw [regularFluxClassVector_conjugation]

/-- The normalized trivial class is precisely the identity basis vector.
Source: SCP10, Theorem 6.17, lines 2304–2340. -/
theorem normalizedRegularFluxClassVector_one :
    normalizedRegularFluxClassVector (1 : G) = Pi.single 1 1 := by
  have hc : Subgroup.centralizer ({(1 : G)} : Set G) = ⊤ := by
    ext x
    simp [Subgroup.mem_centralizer_iff]
  have hn : Nat.card (Subgroup.centralizer ({(1 : G)} : Set G)) = Fintype.card G := by
    rw [hc]
    have he : (⊤ : Subgroup G) ≃ G :=
      (Subgroup.topEquiv : (⊤ : Subgroup G) ≃* G).toEquiv
    exact (Nat.card_congr he).trans Nat.card_eq_fintype_card
  funext t
  simp only [normalizedRegularFluxClassVector, regularFluxClassVector, hn,
    Pi.smul_apply, smul_eq_mul, mul_one, mul_inv_cancel,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    Real.sqrt_mul_self (Nat.cast_nonneg _), Pi.single_apply]
  by_cases ht : t = 1
  · subst t
    simp only [ite_true, mul_one]
    exact inv_mul_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
  · simp only [ite_eq_right ht, mul_zero]

/-- The actual accessible pair sum, expressed in its relative group coordinate.
Source: SCP10, Theorem 6.17, lines 2304–2340. -/
def regularFluxPairVector (g : G) (p : G × G) : ℂ :=
  regularFluxClassVector g (p.1 * p.2⁻¹)

/-- The relative-coordinate formula is the pair sum printed in the source.
Source: SCP10, Theorem 6.17, lines 2304–2340. -/
theorem regularFluxPairVector_eq_sum (g a b : G) :
    regularFluxPairVector g (a, b) =
      ∑ z : G, if a = (z * g * z⁻¹) * b then (1 : ℂ) else 0 := by
  simp only [regularFluxPairVector, regularFluxClassVector, mul_inv_eq_iff_eq_mul]

/-- The pair sum has one additional factor |G| from its reference register.
Source: SCP10, Theorem 6.17, lines 2304–2340. -/
theorem regularFluxPairVector_dotProduct (g : G) :
    star (regularFluxPairVector g) ⬝ᵥ regularFluxPairVector g =
      (Fintype.card G : ℂ) ^ 2 * Nat.card (Subgroup.centralizer ({g} : Set G)) := by
  simp only [dotProduct, Pi.star_apply, Fintype.sum_prod_type, regularFluxPairVector]
  rw [Finset.sum_comm]
  have h (b : G) :
      (∑ a : G, star (regularFluxClassVector g (a * b⁻¹)) *
        regularFluxClassVector g (a * b⁻¹)) =
      (Fintype.card G : ℂ) * Nat.card (Subgroup.centralizer ({g} : Set G)) := by
    rw [← Equiv.sum_comp (Equiv.mulRight b)]
    simpa only [Equiv.coe_mulRight, mul_inv_cancel_right, dotProduct, Pi.star_apply] using
      regularFluxClassVector_dotProduct g
  simp only [h, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, pow_two, mul_assoc]

/-- Exchange the identity and normalized class vectors, fixing their orthogonal complement.
Source: SCP10, Theorem 6.17, lines 2304–2340. -/
def regularFluxCreationMatrix (g : G) : Matrix G G ℂ :=
  Matrix.unitaryVectorSwap (Pi.single 1 1) (normalizedRegularFluxClassVector g)

private theorem single_one_dotProduct :
    star (Pi.single (1 : G) (1 : ℂ)) ⬝ᵥ Pi.single 1 1 = 1 := by
  rw [Pi.star_single, star_one, single_dotProduct]
  simp

/-- The class creation matrix is unitary, including the trivial flux.
Source: SCP10, Theorem 6.17, lines 2304–2340. -/
theorem regularFluxCreationMatrix_mem_unitaryGroup (g : G) :
    regularFluxCreationMatrix g ∈ Matrix.unitaryGroup G ℂ := by
  by_cases hg : g = 1
  · subst g
    simp only [regularFluxCreationMatrix, normalizedRegularFluxClassVector_one,
      Matrix.unitaryVectorSwap, sub_self, Matrix.zero_vecMulVec, sub_zero]
    exact (Matrix.unitaryGroup G ℂ).one_mem
  · exact Matrix.unitaryVectorSwap_mem_unitaryGroup _ _ single_one_dotProduct
      (normalizedRegularFluxClassVector_dotProduct g)
      (normalizedRegularFluxClassVector_orthogonal hg)

/-- The class operation creates the normalized conjugacy sum from the identity.
Source: SCP10, Theorem 6.17, lines 2304–2340. -/
theorem regularFluxCreationMatrix_mulVec_single (g : G) :
    regularFluxCreationMatrix g *ᵥ Pi.single 1 1 = normalizedRegularFluxClassVector g := by
  by_cases hg : g = 1
  · subst g
    simp only [regularFluxCreationMatrix, normalizedRegularFluxClassVector_one,
      Matrix.unitaryVectorSwap, sub_self, Matrix.zero_vecMulVec, sub_zero,
      Matrix.one_mulVec]
  · exact Matrix.unitaryVectorSwap_mulVec_left _ _ single_one_dotProduct
      (normalizedRegularFluxClassVector_orthogonal hg)

/-- The class operation commutes with every group conjugation.
Source: SCP10, Theorem 6.17, lines 2304–2340. -/
theorem regularFluxCreationMatrix_commute_conjugation (g x : G) :
    Commute (regularFluxCreationMatrix g)
      ((show Equiv.Perm G from (MulAut.conj x).toEquiv).permMatrix ℂ) := by
  apply Matrix.unitaryVectorSwap_commute
  · exact (show Equiv.Perm G from (MulAut.conj x).toEquiv).permMatrix_mem_unitaryGroup
  · rw [Matrix.permMatrix_mulVec]
    funext t
    simp [Function.comp_apply, Pi.single_apply, MulAut.conj_apply]
  · rw [Matrix.permMatrix_mulVec]
    funext t
    exact normalizedRegularFluxClassVector_conjugation g x t


private def fluxPairRelativeEquiv : (G × G) ≃ (G × G) where
  toFun p := (p.1 * p.2⁻¹, p.2)
  invFun p := (p.1 * p.2, p.2)
  left_inv p := by simp
  right_inv p := by simp

/-- Apply class creation to a b⁻¹ and the identity to the reference register b.
Source: SCP10, Theorem 6.17, lines 2304–2340. -/
def regularFluxPairCreationMatrix (g : G) : Matrix (G × G) (G × G) ℂ :=
  (regularFluxCreationMatrix g ⊗ₖ (1 : Matrix G G ℂ)).submatrix
    fluxPairRelativeEquiv fluxPairRelativeEquiv

/-- Creation on the actual two registers is unitary.
Source: SCP10, Theorem 6.17, lines 2304–2340. -/
theorem regularFluxPairCreationMatrix_mem_unitaryGroup (g : G) :
    regularFluxPairCreationMatrix g ∈ Matrix.unitaryGroup (G × G) ℂ := by
  exact Matrix.reindex_mem_unitaryGroup fluxPairRelativeEquiv.symm _
    (Matrix.kronecker_mem_unitary (regularFluxCreationMatrix_mem_unitaryGroup g)
      (Matrix.unitaryGroup G ℂ).one_mem)

/-- The unitary replaces the diagonal pair by the exactly normalized source pair sum.
Source: SCP10, Theorem 6.17, lines 2304–2340. -/
theorem regularFluxPairCreationMatrix_mulVec_diagonal (g : G) :
    regularFluxPairCreationMatrix g *ᵥ (fun p => if p.1 = p.2 then 1 else 0) =
      fun p => normalizedRegularFluxClassVector g (p.1 * p.2⁻¹) := by
  funext p
  simp only [Matrix.mulVec, dotProduct]
  rw [← Equiv.sum_comp fluxPairRelativeEquiv.symm, Fintype.sum_prod_type]
  simp only [regularFluxPairCreationMatrix, Matrix.submatrix_apply,
    Matrix.kronecker_apply, fluxPairRelativeEquiv, Equiv.coe_fn_mk,
    Equiv.symm_mk, mul_inv_cancel_right, Matrix.one_apply]
  have he (t b : G) : t * b = b ↔ t = 1 := by
    constructor
    · intro h
      simpa using congrArg (fun z => z * b⁻¹) h
    · intro h
      simp [h]
  simp only [he, mul_ite, mul_one, mul_zero]
  have h := congrFun (regularFluxCreationMatrix_mulVec_single g) (p.1 * p.2⁻¹)
  simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using h

end TNLean.PEPS
