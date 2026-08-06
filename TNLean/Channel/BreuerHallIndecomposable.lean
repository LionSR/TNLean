/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Channel.BreuerHallMap
import TNLean.Channel.DecomposablePPT
import TNLean.Channel.MaximallyEntangled

/-!
# Indecomposability of the Breuer-Hall map

This file completes **Wolf Chapter 3, Example 3.1**: for an antisymmetric unitary `U`
(`Uᵀ = -U`, `Uᴴ U = 1`) on an even dimension `d ≥ 4`, the Breuer-Hall map `T_BH` is not
decomposable. Combined with `Matrix.breuerHallMap_isPositiveMap`, this shows `T_BH` is an
indecomposable positive map.

Wolf's notes state the fact without proof, citing external theorem numbers not present in
the local source; the argument below follows the original construction of Breuer
[Breuer2006Optimal], adapted to an elementary trace-identity form that avoids the
representation-theoretic (total angular momentum) machinery of the original paper.

## The witness

Write `F` for the SWAP operator (`Matrix.swapMatrix d`) and `Ψ(i,k) = U(i,k)` for the
`U`-twisted maximally entangled vector, with projector `P₀ = |Ψ⟩⟨Ψ|`
(`Matrix.twistedOmegaProj U`). The PPT witness is

  `ρ = P₀ + (Uᴴ ⊗ 1)(1 + F)(U ⊗ 1)`,

a sum of two positive semidefinite terms, hence itself positive semidefinite. Antisymmetry
and unitarity of `U` give the exact identity `(ρ)^{T₁} = ρ` (`ρ` is a fixed point of the
first-factor partial transpose), so `ρ` is a PPT state. A direct trace computation shows

  `⟨Ψ| (T_BH ⊗ id)(ρ) |Ψ⟩ = d(1 - d) < 0` for `d ≥ 2`,

so `(T_BH ⊗ id)(ρ)` is not positive semidefinite (pairing against the positive
semidefinite `P₀` would otherwise force a nonnegative trace). By
`not_isDecomposablePositiveMap_of_isPPT_not_tensorMapId_posSemidef`, `T_BH` is not
decomposable.

The restriction `d ≥ 4` is necessary, not an artifact of this proof: for `d = 2`,
`breuerHallMap_apply` shows `T_BH` reduces to the zero map (Wolf's contraction hypothesis
`Uᴴ U ≤ 1` collapses the subtracted terms to the identity), which is trivially
decomposable. See `docs/paper-gaps/breuer_hall_even_dim_restriction.tex`.

## Main declarations

* `Matrix.twistedOmegaVec`, `Matrix.twistedOmegaProj` -- the `U`-twisted maximally
  entangled vector `Ψ(i, k) = U(i, k)` and its rank-one projector `P₀ = |Ψ⟩⟨Ψ|`.
* `Matrix.breuerHallSymmetricWitness` -- the conjugated symmetric-subspace projector
  `(Uᴴ ⊗ 1)(1 + F)(U ⊗ 1)`.
* `Matrix.breuerHallWitnessState` -- the PPT witness `ρ = P₀ + breuerHallSymmetricWitness U`.
* `Matrix.breuerHallMap_isIndecomposablePositiveMap` -- **Wolf Chapter 3, Example 3.1.**
  For antisymmetric unitary `U` on an even dimension `d ≥ 4`, `breuerHallMap U` is an
  indecomposable positive map.

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Chapter 3, Example 3.1][Wolf2012QChannels]
* [H.-P. Breuer, *Optimal entanglement criterion for mixed quantum states*,
  Phys. Rev. Lett. 97, 080501 (2006), arXiv:quant-ph/0605036]
-/

open scoped Matrix ComplexOrder MatrixOrder Kronecker
open Matrix Finset

variable {d : ℕ}

namespace Matrix

/-! ## The twisted maximally entangled projector -/

/-- The `U`-twisted maximally entangled vector `Ψ(i, k) = U(i, k)`, unnormalized. Its
projector `twistedOmegaProj U` is the Breuer-Hall entanglement witness carrier. -/
noncomputable def twistedOmegaVec (U : Matrix (Fin d) (Fin d) ℂ) : Fin d × Fin d → ℂ :=
  fun p => U p.1 p.2

theorem twistedOmegaVec_apply (U : Matrix (Fin d) (Fin d) ℂ) (i k : Fin d) :
    twistedOmegaVec U (i, k) = U i k := rfl

/-- The rank-one projector `P₀ = |Ψ⟩⟨Ψ|` onto the `U`-twisted maximally entangled vector. -/
noncomputable def twistedOmegaProj (U : Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  Matrix.vecMulVec (twistedOmegaVec U) (star (twistedOmegaVec U))

theorem twistedOmegaProj_apply (U : Matrix (Fin d) (Fin d) ℂ) (p q : Fin d × Fin d) :
    twistedOmegaProj U p q = U p.1 p.2 * star (U q.1 q.2) := by
  simp [twistedOmegaProj, Matrix.vecMulVec_apply, twistedOmegaVec]

theorem twistedOmegaProj_posSemidef (U : Matrix (Fin d) (Fin d) ℂ) :
    (twistedOmegaProj U).PosSemidef :=
  Matrix.posSemidef_vecMulVec_self_star (twistedOmegaVec U)

/-- `Tr(P₀) = d` for unitary `U`. -/
theorem trace_twistedOmegaProj {U : Matrix (Fin d) (Fin d) ℂ} (hU : U * Uᴴ = 1) :
    (twistedOmegaProj U).trace = (d : ℂ) := by
  have h1 : (twistedOmegaProj U).trace = (U * Uᴴ).trace := by
    simp only [Matrix.trace, Matrix.diag, twistedOmegaProj_apply, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Fintype.sum_prod_type]
  rw [h1, hU, Matrix.trace_one, Fintype.card_fin]

/-! ## Positivity of the symmetric-subspace projector -/

/-- `Tr(F) = d`: the SWAP operator has trace equal to the factor dimension. -/
theorem trace_swapMatrix (d : ℕ) : (Matrix.swapMatrix d).trace = (d : ℂ) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.swapMatrix_apply, Fintype.sum_prod_type]
  simp_rw [show ∀ i₁ i₂ : Fin d, (if i₁ = i₂ ∧ i₂ = i₁ then (1 : ℂ) else 0) =
    (if i₁ = i₂ then (1 : ℂ) else 0) from fun i₁ i₂ => by
      congr 1; exact propext ⟨fun h => h.1, fun h => ⟨h, h.symm⟩⟩]
  simp

/-- `1 + F` is positive semidefinite, where `F` is the SWAP operator: it is `2` times the
projector onto the permutation-symmetric subspace. The quadratic form pairs up
`(i₁, i₂)` with `(i₂, i₁)` and completes a square,
`⟨w, (1+F)w⟩ = (1/2) Σ |w(i₁,i₂) + w(i₂,i₁)|² ≥ 0`. -/
theorem one_add_swapMatrix_posSemidef (d : ℕ) :
    ((1 : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) + Matrix.swapMatrix d).PosSemidef := by
  classical
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · exact isHermitian_one.add (by
      rw [Matrix.IsHermitian]; exact Matrix.swapMatrix_conjTranspose)
  · intro w
    have hFw : ∀ p : Fin d × Fin d,
        ((Matrix.swapMatrix d) *ᵥ w) p = w (p.2, p.1) := by
      rintro ⟨i₁, i₂⟩
      change ∑ q : Fin d × Fin d, Matrix.swapMatrix d (i₁, i₂) q * w q = w (i₂, i₁)
      rw [Finset.sum_eq_single (i₂, i₁)]
      · simp
      · rintro ⟨j₁, j₂⟩ _ hj
        have : ¬ (i₁ = j₂ ∧ i₂ = j₁) := by
          rintro ⟨rfl, rfl⟩; exact hj rfl
        simp [Matrix.swapMatrix_apply, this]
      · simp
    have hQ : star w ⬝ᵥ (((1 : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
          + Matrix.swapMatrix d) *ᵥ w)
        = ∑ p : Fin d × Fin d, star (w p) * (w p + w (p.2, p.1)) := by
      change ∑ p : Fin d × Fin d, star (w p) * (((1 : Matrix _ _ ℂ) + Matrix.swapMatrix d) *ᵥ w) p
        = _
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [Matrix.add_mulVec, Matrix.one_mulVec, Pi.add_apply, hFw]
    have hsplit : ∀ p : Fin d × Fin d,
        star (w p) * (w p + w (p.2, p.1)) + star (w (p.2, p.1)) * (w (p.2, p.1) + w p)
          = ((‖w p + w (p.2, p.1)‖ ^ 2 : ℝ) : ℂ) := by
      intro p
      have heq : star (w p) * (w p + w (p.2, p.1)) + star (w (p.2, p.1)) * (w (p.2, p.1) + w p)
          = (w p + w (p.2, p.1)) * star (w p + w (p.2, p.1)) := by
        rw [star_add]; ring
      rw [heq]
      exact_mod_cast RCLike.mul_conj (w p + w (p.2, p.1))
    have hpair : ∑ p : Fin d × Fin d, star (w (p.2, p.1)) * (w (p.2, p.1) + w p)
        = ∑ p : Fin d × Fin d, star (w p) * (w p + w (p.2, p.1)) :=
      Equiv.sum_comp (Equiv.prodComm (Fin d) (Fin d)) (fun p => star (w p) * (w p + w (p.2, p.1)))
    have htwice : (2 : ℂ) * (star w ⬝ᵥ (((1 : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
          + Matrix.swapMatrix d) *ᵥ w))
        = ((∑ p : Fin d × Fin d, ‖w p + w (p.2, p.1)‖ ^ 2 : ℝ) : ℂ) := by
      rw [hQ, show (2 : ℂ) * ∑ p : Fin d × Fin d, star (w p) * (w p + w (p.2, p.1))
          = (∑ p : Fin d × Fin d, star (w p) * (w p + w (p.2, p.1)))
            + ∑ p : Fin d × Fin d, star (w (p.2, p.1)) * (w (p.2, p.1) + w p) from by
        rw [hpair]; ring]
      push_cast
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun p _ => by exact_mod_cast hsplit p
    have hnonneg : (0 : ℝ) ≤ ∑ p : Fin d × Fin d, ‖w p + w (p.2, p.1)‖ ^ 2 :=
      Finset.sum_nonneg fun p _ => sq_nonneg _
    have hS : star w ⬝ᵥ (((1 : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
          + Matrix.swapMatrix d) *ᵥ w)
        = (((∑ p : Fin d × Fin d, ‖w p + w (p.2, p.1)‖ ^ 2) / 2 : ℝ) : ℂ) := by
      refine mul_left_cancel₀ (two_ne_zero (α := ℂ)) ?_
      rw [htwice]; push_cast; ring
    rw [hS, Complex.zero_le_real]
    positivity

/-! ## Antisymmetry consequences -/

/-- The conjugate transpose of the transpose of an antisymmetric matrix is minus its own
conjugate transpose: `(Uᵀ)ᴴ = -Uᴴ`. -/
theorem transpose_conjTranspose_of_antisymmetric {U : Matrix (Fin d) (Fin d) ℂ}
    (hUanti : Uᵀ = -U) : (Uᵀ)ᴴ = -Uᴴ := by
  rw [hUanti]; simp

/-- For antisymmetric unitary `U`, `Uᵀ * (Uᵀ)ᴴ = 1`. -/
theorem transpose_mul_transpose_conjTranspose_eq_one {U : Matrix (Fin d) (Fin d) ℂ}
    (hUanti : Uᵀ = -U) (hUunit : Uᴴ * U = 1) : Uᵀ * (Uᵀ)ᴴ = 1 := by
  rw [transpose_conjTranspose_of_antisymmetric hUanti, hUanti, neg_mul_neg,
    mul_eq_one_comm.mp hUunit]

/-! ## The conjugated symmetric-subspace witness -/

/-- The projector onto the symmetric subspace, conjugated by `Uᴴ` on the left and `U` on
the right: `(Uᴴ ⊗ 1)(1 + F)(U ⊗ 1)`. Its first-factor partial transpose recovers
`1 + twistedOmegaProj U` (`partialTransposeLeft_breuerHallSymmetricWitness`). -/
noncomputable def breuerHallSymmetricWitness (U : Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  (Uᴴ ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ)) * (1 + Matrix.swapMatrix d) *
    (U ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ))

theorem breuerHallSymmetricWitness_posSemidef (U : Matrix (Fin d) (Fin d) ℂ) :
    (breuerHallSymmetricWitness U).PosSemidef := by
  have hconj : (Uᴴ ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ))ᴴ = U ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ) := by
    rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_conjTranspose,
      Matrix.conjTranspose_one]
  rw [breuerHallSymmetricWitness, ← hconj]
  exact (one_add_swapMatrix_posSemidef d).mul_mul_conjTranspose_same _

/-! ## Partial-transpose identities -/

theorem partialTransposeLeft_one (d d' : ℕ) :
    Matrix.partialTransposeLeft (1 : Matrix (Fin d × Fin d') (Fin d × Fin d') ℂ) = 1 := by
  ext p q
  simp only [Matrix.partialTransposeLeft_apply, Matrix.one_apply, Prod.ext_iff]
  congr 1
  simp [eq_comm]

/-- The first-factor partial transpose is additive. -/
theorem partialTransposeLeft_add {d d' : ℕ} (A B : Matrix (Fin d × Fin d') (Fin d × Fin d') ℂ) :
    Matrix.partialTransposeLeft (A + B)
      = Matrix.partialTransposeLeft A + Matrix.partialTransposeLeft B := by
  ext p q; simp [Matrix.partialTransposeLeft_apply, Matrix.add_apply]

/-- The first-factor partial transpose of the SWAP operator is the (identity-)twisted
maximally entangled projector: `F^{T₁} = twistedOmegaProj 1`. -/
theorem partialTransposeLeft_swapMatrix (d : ℕ) :
    Matrix.partialTransposeLeft (Matrix.swapMatrix d) =
      twistedOmegaProj (1 : Matrix (Fin d) (Fin d) ℂ) := by
  ext p q
  simp only [Matrix.partialTransposeLeft_apply, Matrix.swapMatrix_apply, twistedOmegaProj_apply,
    Matrix.one_apply]
  by_cases h1 : p.1 = p.2 <;> by_cases h2 : q.1 = q.2 <;>
    simp [h1, h2, eq_comm]

/-- A general conjugation identity: conjugating a rank-one outer product `v vᴴ` by `M`
recovers the rank-one outer product of `M *ᵥ v`. -/
theorem vecMulVec_mulVec_conjTranspose {m n : Type*} [Fintype n]
    (M : Matrix m n ℂ) (v : n → ℂ) :
    M * Matrix.vecMulVec v (star v) * Mᴴ =
      Matrix.vecMulVec (M *ᵥ v) (star (M *ᵥ v)) := by
  rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.vecMul_conjTranspose, star_star]

/-- `(Uᵀ ⊗ 1)` applied to the identity-twisted vector `twistedOmegaVec 1` reads off the
transpose entry `U(k, i)`. -/
theorem transpose_kronecker_one_mulVec_twistedOmegaVec_one (U : Matrix (Fin d) (Fin d) ℂ) :
    (Uᵀ ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ)) *ᵥ twistedOmegaVec (1 : Matrix (Fin d) (Fin d) ℂ)
      = fun p => U p.2 p.1 := by
  ext p
  change ∑ q : Fin d × Fin d, (Uᵀ ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ)) p q *
      twistedOmegaVec (1 : Matrix (Fin d) (Fin d) ℂ) q = U p.2 p.1
  rw [Finset.sum_eq_single (p.2, p.2)]
  · simp [Matrix.kroneckerMap_apply, twistedOmegaVec, Matrix.transpose_apply]
  · rintro ⟨j1, j2⟩ _ hj
    rcases eq_or_ne j2 p.2 with hj2 | hj2
    · subst hj2
      have hne : j1 ≠ p.2 := fun h => hj (by rw [h])
      simp [Matrix.kroneckerMap_apply, twistedOmegaVec, Matrix.one_apply_ne hne]
    · have hz : (1 : Matrix (Fin d) (Fin d) ℂ) p.2 j2 = 0 := Matrix.one_apply_ne hj2.symm
      simp [Matrix.kroneckerMap_apply, twistedOmegaVec, hz]
  · simp

/-- For antisymmetric `U`, `(Uᵀ ⊗ 1) *ᵥ twistedOmegaVec 1 = -twistedOmegaVec U`. -/
theorem transpose_kronecker_one_mulVec_twistedOmegaVec_one_of_antisymmetric
    {U : Matrix (Fin d) (Fin d) ℂ} (hUanti : Uᵀ = -U) :
    (Uᵀ ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ)) *ᵥ twistedOmegaVec (1 : Matrix (Fin d) (Fin d) ℂ)
      = -twistedOmegaVec U := by
  rw [transpose_kronecker_one_mulVec_twistedOmegaVec_one]
  funext p
  have hp : U p.2 p.1 = Uᵀ p.1 p.2 := rfl
  simp only [Pi.neg_apply, twistedOmegaVec, hp, hUanti, Matrix.neg_apply]

/-- **Key identity.** The first-factor partial transpose of the conjugated symmetric-subspace
witness recovers `1 + twistedOmegaProj U`. This is the precise sense in which the PPT
witness state built below is a fixed point of the partial transpose. -/
theorem partialTransposeLeft_breuerHallSymmetricWitness {U : Matrix (Fin d) (Fin d) ℂ}
    (hUanti : Uᵀ = -U) (hUunit : Uᴴ * U = 1) :
    Matrix.partialTransposeLeft (breuerHallSymmetricWitness U) = 1 + twistedOmegaProj U := by
  have hPTadd : Matrix.partialTransposeLeft
        ((1 : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) + Matrix.swapMatrix d)
      = 1 + twistedOmegaProj (1 : Matrix (Fin d) (Fin d) ℂ) := by
    rw [partialTransposeLeft_add, Matrix.partialTransposeLeft_one, partialTransposeLeft_swapMatrix]
  have hstep : Matrix.partialTransposeLeft (breuerHallSymmetricWitness U)
      = (Uᵀ ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ)) *
          (1 + twistedOmegaProj (1 : Matrix (Fin d) (Fin d) ℂ)) *
          ((Uᴴ)ᵀ ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ)) := by
    rw [breuerHallSymmetricWitness,
      Matrix.partialTransposeLeft_conj_kronecker_one Uᴴ U (1 + Matrix.swapMatrix d), hPTadd]
  rw [hstep, ← Matrix.conjTranspose_transpose_eq_transpose_conjTranspose U,
    transpose_conjTranspose_of_antisymmetric hUanti]
  have hnegk : (-Uᴴ : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ)
      = -(Uᴴ ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ)) := by
    ext p q; simp [Matrix.kroneckerMap_apply]
  rw [hnegk, mul_neg, mul_add, add_mul, mul_one]
  have hA : (Uᵀ ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ)) * (Uᴴ ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ))
      = -(1 : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) := by
    rw [← Matrix.mul_kronecker_mul, hUanti]
    have hUUH : -U * Uᴴ = -1 := by rw [neg_mul, mul_eq_one_comm.mp hUunit]
    rw [hUUH]
    ext p q
    simp only [Matrix.kroneckerMap_apply, Matrix.one_apply, Matrix.neg_apply, Prod.ext_iff]
    by_cases h1 : p.1 = q.1 <;> by_cases h2 : p.2 = q.2 <;> simp [h1, h2]
  have hMconj : (Uᵀ ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ))ᴴ
      = -(Uᴴ ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ)) := by
    rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
      transpose_conjTranspose_of_antisymmetric hUanti]
    exact hnegk
  have hMconj' : (Uᴴ : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ)
      = -((Uᵀ ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ))ᴴ) := by
    rw [hMconj, neg_neg]
  have hB : (Uᵀ ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ)) *
        twistedOmegaProj (1 : Matrix (Fin d) (Fin d) ℂ) * (Uᴴ ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ))
      = -twistedOmegaProj U := by
    rw [twistedOmegaProj, hMconj', mul_neg, vecMulVec_mulVec_conjTranspose,
      transpose_kronecker_one_mulVec_twistedOmegaVec_one_of_antisymmetric hUanti]
    congr 1
    ext p q
    simp [twistedOmegaProj_apply, Matrix.vecMulVec_apply, Pi.star_apply, twistedOmegaVec]
  rw [hA, hB]
  abel

/-! ## The PPT witness state -/

/-- The PPT witness for the Breuer-Hall map: the sum of the twisted maximally entangled
projector and the conjugated symmetric-subspace witness. It is positive semidefinite (a
sum of positive semidefinite terms) and, by antisymmetry and unitarity of `U`, a fixed
point of the first-factor partial transpose, hence a PPT state
(`breuerHallWitnessState_isPPT`). -/
noncomputable def breuerHallWitnessState (U : Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  twistedOmegaProj U + breuerHallSymmetricWitness U

theorem breuerHallWitnessState_posSemidef (U : Matrix (Fin d) (Fin d) ℂ) :
    (breuerHallWitnessState U).PosSemidef :=
  (twistedOmegaProj_posSemidef U).add (breuerHallSymmetricWitness_posSemidef U)

/-- The witness state is a fixed point of the first-factor partial transpose. -/
theorem partialTransposeLeft_breuerHallWitnessState {U : Matrix (Fin d) (Fin d) ℂ}
    (hUanti : Uᵀ = -U) (hUunit : Uᴴ * U = 1) :
    Matrix.partialTransposeLeft (breuerHallWitnessState U) = breuerHallWitnessState U := by
  have hinvol := partialTransposeLeft_breuerHallSymmetricWitness hUanti hUunit
  have hPT0 : Matrix.partialTransposeLeft (twistedOmegaProj U)
      = breuerHallSymmetricWitness U - 1 := by
    have hthis := congrArg Matrix.partialTransposeLeft hinvol
    rw [Matrix.partialTransposeLeft_partialTransposeLeft, partialTransposeLeft_add,
      Matrix.partialTransposeLeft_one] at hthis
    rw [hthis]; abel
  change Matrix.partialTransposeLeft (twistedOmegaProj U + breuerHallSymmetricWitness U)
    = twistedOmegaProj U + breuerHallSymmetricWitness U
  rw [partialTransposeLeft_add, hPT0, hinvol]
  abel

theorem breuerHallWitnessState_isPPT {U : Matrix (Fin d) (Fin d) ℂ}
    (hUanti : Uᵀ = -U) (hUunit : Uᴴ * U = 1) :
    Matrix.IsPPT (breuerHallWitnessState U) := by
  change (Matrix.partialTransposeLeft (breuerHallWitnessState U)).PosSemidef
  rw [partialTransposeLeft_breuerHallWitnessState hUanti hUunit]
  exact breuerHallWitnessState_posSemidef U

/-! ## The key quadratic-form identity -/

/-- Pairing a matrix `A` with `twistedOmegaProj U` under the trace form is the quadratic
form of `A` at the twisted maximally entangled vector. -/
theorem trace_mul_twistedOmegaProj (A : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    (U : Matrix (Fin d) (Fin d) ℂ) :
    (A * twistedOmegaProj U).trace = star (twistedOmegaVec U) ⬝ᵥ (A *ᵥ twistedOmegaVec U) := by
  rw [twistedOmegaProj, Matrix.mul_vecMulVec, Matrix.trace_vecMulVec, dotProduct_comm]

end Matrix
