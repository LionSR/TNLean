/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.FinSum
import TNLean.Channel.BreuerHallMap
import TNLean.Channel.DecomposablePPT
import TNLean.Channel.MaximallyEntangled

/-!
# Indecomposability of the Breuer-Hall map

This file completes **Wolf Chapter 3, Example 3.1**: for an antisymmetric unitary `U`
(`Uᵀ = -U`, `Uᴴ U = 1`) in dimension `d > 2`, the Breuer-Hall map `T_BH` is not
decomposable. Combined with `Matrix.breuerHallMap_isPositiveMap`, this shows `T_BH` is an
indecomposable positive map.

Wolf's notes state the fact without proof, in the surrounding context that antisymmetric
unitaries exist only for even `d`. The argument below follows the standard PPT detection
route: a decomposable positive map preserves positivity on PPT states
(`IsDecomposablePositiveMap.tensorMapId_posSemidef_of_isPPT`), so a PPT state on which the
ampliation of `T_BH` fails to be positive semidefinite witnesses indecomposability.

## The witness

Write `F` for the SWAP operator (`Matrix.swapMatrix d`) and `Ψ(i,k) = U(i,k)` for the
`U`-twisted maximally entangled vector, with unnormalized projector `P₀ = |Ψ⟩⟨Ψ|`
(`Matrix.twistedOmegaProj U`). The PPT witness is

  `ρ = (1 + F) + P₀`,

a sum of two positive semidefinite terms, hence itself positive semidefinite. Its
first-factor partial transpose is `ρ^{T₁} = P₁ + (Uᴴ ⊗ 1)(1 + F)(U ⊗ 1)`, where
`P₁ = twistedOmegaProj 1` is the untwisted maximally entangled projector: antisymmetry and
unitarity of `U` give `(P₀)^{T₁} = (Uᴴ ⊗ 1)(1 + F)(U ⊗ 1) - 1` (combine
`partialTransposeLeft_breuerHallSymmetricWitness` with the involution of the partial
transpose), so `ρ^{T₁}` is again a sum of positive semidefinite terms and `ρ` is PPT.

The carrying identity is the trace evaluation

  `Tr[(T_BH ⊗ id)(ρ) · P₀] = Tr ρ - Tr(ρ P₀) - Tr(F ρ)`

(`trace_tensorMapId_breuerHallMap_mul_twistedOmegaProj`), valid for every bipartite `ρ`.
At the witness the three traces evaluate to `Tr ρ = d² + 2d`, `Tr(ρ P₀) = d²` and
`Tr(F ρ) = d²` (the last two via `F *ᵥ Ψ = -Ψ`, i.e. antisymmetry of `U`), giving

  `Tr[(T_BH ⊗ id)(ρ) · P₀] = d(2 - d) < 0` for `d > 2`,

so `(T_BH ⊗ id)(ρ)` is not positive semidefinite (its quadratic form at `Ψ` is negative).
By `not_isDecomposablePositiveMap_of_isPPT_not_tensorMapId_posSemidef`, `T_BH` is not
decomposable.

The restriction `d > 2` is necessary, not an artifact of this proof: for `d = 2` every
antisymmetric unitary is a phase times `J = [[0, 1], [-1, 0]]`, and
`J Xᵀ Jᴴ = Tr(X) 1 - X` for all `2 × 2` matrices `X`, so `T_BH` reduces to the zero map,
which is trivially decomposable. See
`docs/paper-gaps/breuer_hall_even_dim_restriction.tex`.

## Main declarations

* `Matrix.twistedOmegaVec`, `Matrix.twistedOmegaProj` -- the `U`-twisted maximally
  entangled vector `Ψ(i, k) = U(i, k)` and its rank-one projector `P₀ = |Ψ⟩⟨Ψ|`.
* `Matrix.breuerHallSymmetricWitness` -- the conjugated symmetric-subspace projector
  `(Uᴴ ⊗ 1)(1 + F)(U ⊗ 1)`.
* `Matrix.breuerHallWitnessState` -- the PPT witness `ρ = (1 + F) + twistedOmegaProj U`.
* `Matrix.trace_tensorMapId_breuerHallMap_mul_twistedOmegaProj` -- the carrying trace
  identity `Tr[(T_BH ⊗ id)(ρ) · P₀] = Tr ρ - Tr(ρ P₀) - Tr(F ρ)`.
* `Matrix.breuerHallMap_isIndecomposablePositiveMap` -- **Wolf Chapter 3, Example 3.1.**
  For antisymmetric unitary `U` in dimension `d > 2`, `breuerHallMap U` is an
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

/-- The PPT witness for the Breuer-Hall map: the sum of the (unnormalized)
symmetric-subspace projector `1 + F` and the twisted maximally entangled projector
`P₀ = twistedOmegaProj U`. It is positive semidefinite (a sum of positive semidefinite
terms), and its first-factor partial transpose is
`twistedOmegaProj 1 + breuerHallSymmetricWitness U`
(`partialTransposeLeft_breuerHallWitnessState`), again a sum of positive semidefinite
terms, so the state is PPT (`breuerHallWitnessState_isPPT`). -/
noncomputable def breuerHallWitnessState (U : Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  (1 + Matrix.swapMatrix d) + twistedOmegaProj U

theorem breuerHallWitnessState_posSemidef (U : Matrix (Fin d) (Fin d) ℂ) :
    (breuerHallWitnessState U).PosSemidef :=
  (one_add_swapMatrix_posSemidef d).add (twistedOmegaProj_posSemidef U)

/-- The first-factor partial transpose of the witness state: the partial transpose of
`1 + F` contributes `1 + twistedOmegaProj 1`, and the partial transpose of the twisted
projector contributes `breuerHallSymmetricWitness U - 1` (the involution of the partial
transpose applied to `partialTransposeLeft_breuerHallSymmetricWitness`), so the identity
summands cancel. -/
theorem partialTransposeLeft_breuerHallWitnessState {U : Matrix (Fin d) (Fin d) ℂ}
    (hUanti : Uᵀ = -U) (hUunit : Uᴴ * U = 1) :
    Matrix.partialTransposeLeft (breuerHallWitnessState U)
      = twistedOmegaProj (1 : Matrix (Fin d) (Fin d) ℂ) + breuerHallSymmetricWitness U := by
  have hPT0 : Matrix.partialTransposeLeft (twistedOmegaProj U)
      = breuerHallSymmetricWitness U - 1 := by
    have hthis := congrArg Matrix.partialTransposeLeft
      (partialTransposeLeft_breuerHallSymmetricWitness hUanti hUunit)
    rw [Matrix.partialTransposeLeft_partialTransposeLeft, partialTransposeLeft_add,
      Matrix.partialTransposeLeft_one] at hthis
    rw [hthis]; abel
  change Matrix.partialTransposeLeft ((1 + Matrix.swapMatrix d) + twistedOmegaProj U) = _
  rw [partialTransposeLeft_add, partialTransposeLeft_add, Matrix.partialTransposeLeft_one,
    partialTransposeLeft_swapMatrix, hPT0]
  abel

/-- The witness state is PPT: its partial transpose is a sum of two positive semidefinite
terms. -/
theorem breuerHallWitnessState_isPPT {U : Matrix (Fin d) (Fin d) ℂ}
    (hUanti : Uᵀ = -U) (hUunit : Uᴴ * U = 1) :
    Matrix.IsPPT (breuerHallWitnessState U) := by
  change (Matrix.partialTransposeLeft (breuerHallWitnessState U)).PosSemidef
  rw [partialTransposeLeft_breuerHallWitnessState hUanti hUunit]
  exact (twistedOmegaProj_posSemidef _).add (breuerHallSymmetricWitness_posSemidef U)

/-! ## The key quadratic-form identity -/

/-- Pairing a matrix `A` with `twistedOmegaProj U` under the trace form is the quadratic
form of `A` at the twisted maximally entangled vector. -/
theorem trace_mul_twistedOmegaProj (A : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    (U : Matrix (Fin d) (Fin d) ℂ) :
    (A * twistedOmegaProj U).trace = star (twistedOmegaVec U) ⬝ᵥ (A *ᵥ twistedOmegaVec U) := by
  rw [twistedOmegaProj, Matrix.mul_vecMulVec, Matrix.trace_vecMulVec, dotProduct_comm]

/-- Unitarity contracts two columns of `U` to a Kronecker delta. -/
private theorem unitarity_column_contraction
    {U : Matrix (Fin d) (Fin d) ℂ} (hUunit : Uᴴ * U = 1) :
    ∀ i2 j2 : Fin d,
      ∑ i1 : Fin d, star (U i1 i2) * U i1 j2 = if i2 = j2 then (1 : ℂ) else 0 := by
  intro i2 j2
  have heq : (Uᴴ * U) i2 j2 = ∑ i1 : Fin d, star (U i1 i2) * U i1 j2 := rfl
  rw [← heq, hUunit, Matrix.one_apply]

/-- The quadratic form of `U * Mᵀ * Uᴴ` at two columns of a unitary `U` reads off
the corresponding transposed entry of `M`. -/
private theorem unitarity_sandwich_contraction
    {U : Matrix (Fin d) (Fin d) ℂ} (hUunit : Uᴴ * U = 1) :
    ∀ (M : Matrix (Fin d) (Fin d) ℂ) (i2 j2 : Fin d),
      ∑ i1 : Fin d, ∑ j1 : Fin d,
      star (U i1 i2) * (U * Mᵀ * Uᴴ) i1 j1 * U j1 j2 = M j2 i2 := by
  intro M i2 j2
  have hL : ∑ i1 : Fin d, ∑ j1 : Fin d,
      star (U i1 i2) * (U * Mᵀ * Uᴴ) i1 j1 * U j1 j2
      = (fun k => star (U k i2)) ⬝ᵥ ((U * Mᵀ * Uᴴ) *ᵥ (fun k => U k j2)) := by
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i1 _ => Finset.sum_congr rfl fun j1 _ => ?_
    ring
  rw [hL, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  have hstep1 : Uᴴ *ᵥ (fun k => U k j2) = fun k => if k = j2 then (1 : ℂ) else 0 := by
    funext k
    change ∑ l : Fin d, Uᴴ k l * U l j2 = _
    simp_rw [Matrix.conjTranspose_apply]
    exact unitarity_column_contraction hUunit k j2
  have hstep2 : Mᵀ *ᵥ (fun k => if k = j2 then (1 : ℂ) else 0) = fun a => M j2 a := by
    funext a
    change ∑ l : Fin d, Mᵀ a l * (if l = j2 then (1 : ℂ) else 0) = _
    rw [Finset.sum_eq_single j2]
    · simp [Matrix.transpose_apply]
    · intro l _ hl; simp [hl]
    · simp
  rw [hstep1, hstep2]
  change ∑ i1 : Fin d, star (U i1 i2) * (∑ a : Fin d, U i1 a * M j2 a) = M j2 i2
  have hstep3 : ∀ i1 : Fin d, star (U i1 i2) * (∑ a : Fin d, U i1 a * M j2 a)
      = ∑ a : Fin d, M j2 a * (star (U i1 i2) * U i1 a) := by
    intro i1
    simpa only [mul_comm, mul_left_comm, mul_assoc] using
      (Fintype.sum_mul_mul_eq_mul_sum_mul (star (U i1 i2))
        (fun a => U i1 a) (fun a => M j2 a)).symm
  simp_rw [hstep3]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, unitarity_column_contraction hUunit]
  rw [Finset.sum_eq_single i2]
  · simp
  · intro a _ ha; simp [Ne.symm ha]
  · simp

/-- Reorder a quadruple sum so that the two slice indices are outermost. -/
private theorem sum_reindex_slice_outside : ∀ f : Fin d → Fin d → Fin d → Fin d → ℂ,
    (∑ i1 : Fin d, ∑ i2 : Fin d, ∑ j1 : Fin d, ∑ j2 : Fin d, f i1 i2 j1 j2)
      = ∑ i2 : Fin d, ∑ j2 : Fin d, ∑ i1 : Fin d, ∑ j1 : Fin d, f i1 i2 j1 j2 := by
  intro f
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i2 _ => ?_
  rw [show (∑ i1 : Fin d, ∑ j1 : Fin d, ∑ j2 : Fin d, f i1 i2 j1 j2)
      = ∑ i1 : Fin d, ∑ j2 : Fin d, ∑ j1 : Fin d, f i1 i2 j1 j2 from
    Finset.sum_congr rfl fun i1 _ => Finset.sum_comm]
  exact Finset.sum_comm

/-- The trace summand in the expanded Breuer--Hall pairing contracts to `ρ.trace`. -/
private theorem trace_breuerHall_trace_summand
    {U : Matrix (Fin d) (Fin d) ℂ} (hUunit : Uᴴ * U = 1)
    (ρ : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    (∑ i1 : Fin d, ∑ i2 : Fin d, ∑ j1 : Fin d, ∑ j2 : Fin d,
      star (U i1 i2) * (Matrix.bipartiteSlice ρ i2 j2).trace *
        (if i1 = j1 then (1 : ℂ) else 0) * U j1 j2)
    = ρ.trace := by
  have hc1 : ∀ i1 i2 : Fin d, (∑ j1 : Fin d, ∑ j2 : Fin d,
        star (U i1 i2) * (Matrix.bipartiteSlice ρ i2 j2).trace *
          (if i1 = j1 then (1 : ℂ) else 0) * U j1 j2)
      = ∑ j2 : Fin d, star (U i1 i2) * (Matrix.bipartiteSlice ρ i2 j2).trace * U i1 j2 := by
    intro i1 i2
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j2 _ => ?_
    rw [Finset.sum_eq_single i1]
    · rw [if_pos rfl]; ring
    · intro j1 _ hj1; rw [if_neg (Ne.symm hj1)]; ring
    · simp
  simp_rw [hc1]
  rw [Finset.sum_comm]
  have hc2 : ∀ i2 : Fin d, (∑ i1 : Fin d, ∑ j2 : Fin d,
        star (U i1 i2) * (Matrix.bipartiteSlice ρ i2 j2).trace * U i1 j2)
      = (Matrix.bipartiteSlice ρ i2 i2).trace := by
    intro i2
    have h1 : (∑ i1 : Fin d, ∑ j2 : Fin d,
          star (U i1 i2) * (Matrix.bipartiteSlice ρ i2 j2).trace * U i1 j2)
        = ∑ j2 : Fin d, (Matrix.bipartiteSlice ρ i2 j2).trace *
            (∑ i1 : Fin d, star (U i1 i2) * U i1 j2) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j2 _ => ?_
      simpa only [mul_comm, mul_left_comm, mul_assoc] using
        Fintype.sum_mul_mul_eq_mul_sum_mul
          ((Matrix.bipartiteSlice ρ i2 j2).trace)
          (fun i1 => star (U i1 i2)) (fun i1 => U i1 j2)
    rw [h1]
    simp_rw [unitarity_column_contraction hUunit]
    rw [Finset.sum_eq_single i2]
    · simp
    · intro j2 _ hj2; simp [Ne.symm hj2]
    · simp
  simp_rw [hc2]
  have htr : ∀ i2 : Fin d, (Matrix.bipartiteSlice ρ i2 i2).trace
      = ∑ x : Fin d, ρ (x, i2) (x, i2) := by
    intro i2
    simp only [Matrix.trace, Matrix.diag, Matrix.bipartiteSlice_apply]
  simp_rw [htr]
  simp only [Matrix.trace, Matrix.diag, Fintype.sum_prod_type]
  rw [Finset.sum_comm]

/-- The identity summand in the expanded Breuer--Hall pairing is the pairing with the
twisted maximally entangled projector. -/
private theorem trace_breuerHall_identity_summand
    (U : Matrix (Fin d) (Fin d) ℂ)
    (ρ : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    (∑ i1 : Fin d, ∑ i2 : Fin d, ∑ j1 : Fin d, ∑ j2 : Fin d,
      star (U i1 i2) * (Matrix.bipartiteSlice ρ i2 j2) i1 j1 * U j1 j2)
    = (ρ * twistedOmegaProj U).trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Fintype.sum_prod_type,
    twistedOmegaProj_apply, Matrix.bipartiteSlice_apply]
  refine Finset.sum_congr rfl fun i1 _ => Finset.sum_congr rfl fun i2 _ =>
    Finset.sum_congr rfl fun j1 _ => Finset.sum_congr rfl fun j2 _ => ?_
  ring

/-- The twisted-transpose summand in the expanded Breuer--Hall pairing contracts to the
swap pairing. -/
private theorem trace_breuerHall_transpose_summand
    {U : Matrix (Fin d) (Fin d) ℂ} (hUunit : Uᴴ * U = 1)
    (ρ : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    (∑ i1 : Fin d, ∑ i2 : Fin d, ∑ j1 : Fin d, ∑ j2 : Fin d,
      star (U i1 i2) * (U * (Matrix.bipartiteSlice ρ i2 j2)ᵀ * Uᴴ) i1 j1 * U j1 j2)
    = (Matrix.swapMatrix d * ρ).trace := by
  rw [sum_reindex_slice_outside]
  simp_rw [unitarity_sandwich_contraction hUunit]
  have htrace : (Matrix.swapMatrix d * ρ).trace
      = ∑ p : Fin d × Fin d, ρ (p.2, p.1) (p.1, p.2) := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun ⟨p1, p2⟩ _ => ?_
    rw [Finset.sum_eq_single (p2, p1)]
    · simp [Matrix.swapMatrix_apply]
    · rintro ⟨q1, q2⟩ _ hq
      have hne : ¬ (p1 = q2 ∧ p2 = q1) := by
        rintro ⟨h1, h2⟩
        exact hq (Prod.ext h2.symm h1.symm)
      rw [Matrix.swapMatrix_apply, if_neg hne, zero_mul]
    · simp
  rw [htrace]
  simp only [Fintype.sum_prod_type, Matrix.bipartiteSlice_apply]

/-- **Key quadratic-form identity.** For unitary `U`, pairing the ampliation of the
Breuer-Hall map applied to any bipartite `ρ` against the twisted maximally entangled
projector reduces to an elementary combination of three traces of `ρ`. The three terms
come from the three summands of `breuerHallMap_apply`: the trace term contracts to
`ρ.trace` via `Uᴴ * U = 1`, the identity term contracts to `(ρ * twistedOmegaProj U).trace`,
and the twisted-transpose term contracts to `(swapMatrix d * ρ).trace`, again via
`Uᴴ * U = 1` (no antisymmetry is needed for this identity). -/
theorem trace_tensorMapId_breuerHallMap_mul_twistedOmegaProj
    {U : Matrix (Fin d) (Fin d) ℂ} (hUunit : Uᴴ * U = 1)
    (ρ : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    (Matrix.tensorMapId (Matrix.breuerHallMap U) ρ * twistedOmegaProj U).trace
      = ρ.trace - (ρ * twistedOmegaProj U).trace - (Matrix.swapMatrix d * ρ).trace := by
  classical
  -- Expand the pairing into the three summands of `breuerHallMap_apply`.
  have hexpand : star (twistedOmegaVec U) ⬝ᵥ
        (Matrix.tensorMapId (Matrix.breuerHallMap U) ρ *ᵥ twistedOmegaVec U)
      = ∑ i1 : Fin d, ∑ i2 : Fin d, ∑ j1 : Fin d, ∑ j2 : Fin d,
          (star (U i1 i2) * (Matrix.bipartiteSlice ρ i2 j2).trace *
              (if i1 = j1 then (1 : ℂ) else 0) * U j1 j2
            - star (U i1 i2) * (Matrix.bipartiteSlice ρ i2 j2) i1 j1 * U j1 j2
            - star (U i1 i2) * (U * (Matrix.bipartiteSlice ρ i2 j2)ᵀ * Uᴴ) i1 j1 * U j1 j2) := by
    simp only [dotProduct, Matrix.mulVec, Fintype.sum_prod_type, Matrix.tensorMapId_apply,
      Finset.mul_sum, Pi.star_apply, twistedOmegaVec_apply]
    refine Finset.sum_congr rfl fun i1 _ => Finset.sum_congr rfl fun i2 _ =>
      Finset.sum_congr rfl fun j1 _ => Finset.sum_congr rfl fun j2 _ => ?_
    rw [Matrix.breuerHallMap_apply]
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    ring
  rw [trace_mul_twistedOmegaProj, hexpand]
  simp_rw [Finset.sum_sub_distrib]
  rw [trace_breuerHall_trace_summand hUunit ρ,
    trace_breuerHall_identity_summand U ρ,
    trace_breuerHall_transpose_summand hUunit ρ]

/-! ## Evaluation of the carrying identity at the witness -/

/-- For unitary `U`, the squared norm of the twisted maximally entangled vector is `d`
(it is the trace of `twistedOmegaProj U`). -/
theorem twistedOmegaVec_dotProduct_star_self {U : Matrix (Fin d) (Fin d) ℂ}
    (hU : U * Uᴴ = 1) :
    twistedOmegaVec U ⬝ᵥ star (twistedOmegaVec U) = (d : ℂ) := by
  have htr := trace_twistedOmegaProj (d := d) hU
  rw [twistedOmegaProj, Matrix.trace_vecMulVec] at htr
  exact htr

/-- For unitary `U`, `star Ψ ⬝ᵥ Ψ = d`. -/
theorem star_twistedOmegaVec_dotProduct_self {U : Matrix (Fin d) (Fin d) ℂ}
    (hU : U * Uᴴ = 1) :
    star (twistedOmegaVec U) ⬝ᵥ twistedOmegaVec U = (d : ℂ) := by
  rw [dotProduct_comm]
  exact twistedOmegaVec_dotProduct_star_self hU

/-- For antisymmetric `U`, the SWAP operator sends the twisted maximally entangled vector
to its negative: entrywise, `Ψ(k, i) = U(k, i) = -U(i, k) = -Ψ(i, k)`. This is where
antisymmetry enters the witness evaluation. -/
theorem swapMatrix_mulVec_twistedOmegaVec {U : Matrix (Fin d) (Fin d) ℂ}
    (hUanti : Uᵀ = -U) :
    (Matrix.swapMatrix d) *ᵥ twistedOmegaVec U = -twistedOmegaVec U := by
  funext p
  rcases p with ⟨i, k⟩
  change ∑ q : Fin d × Fin d, Matrix.swapMatrix d (i, k) q * twistedOmegaVec U q = _
  rw [Finset.sum_eq_single (k, i)]
  · have h1 : U k i = -U i k := by
      have h2 := Matrix.transpose_apply U i k
      rw [hUanti, Matrix.neg_apply] at h2
      rw [← h2]
    simp [Matrix.swapMatrix_apply, twistedOmegaVec_apply, h1]
  · rintro ⟨j1, j2⟩ _ hj
    have hne : ¬ (i = j2 ∧ k = j1) := by
      rintro ⟨h1, h2⟩
      exact hj (Prod.ext h2.symm h1.symm)
    simp [Matrix.swapMatrix_apply, hne]
  · simp

/-- The trace of `F · P₀` is `-d`: it is the quadratic form of `F` at `Ψ`, and
`F *ᵥ Ψ = -Ψ` by antisymmetry. -/
theorem trace_swapMatrix_mul_twistedOmegaProj {U : Matrix (Fin d) (Fin d) ℂ}
    (hUanti : Uᵀ = -U) (hUunit : Uᴴ * U = 1) :
    ((Matrix.swapMatrix d) * twistedOmegaProj U).trace = -(d : ℂ) := by
  rw [trace_mul_twistedOmegaProj, swapMatrix_mulVec_twistedOmegaVec hUanti,
    dotProduct_neg, star_twistedOmegaVec_dotProduct_self (mul_eq_one_comm.mp hUunit)]

/-- The trace of `P₀²` is `d²`: since `P₀ *ᵥ Ψ = d • Ψ`, the quadratic form of `P₀` at
`Ψ` is `d` times the squared norm of `Ψ`. -/
theorem trace_twistedOmegaProj_mul_self {U : Matrix (Fin d) (Fin d) ℂ}
    (hUunit : Uᴴ * U = 1) :
    (twistedOmegaProj U * twistedOmegaProj U).trace = (d : ℂ) ^ 2 := by
  rw [trace_mul_twistedOmegaProj, twistedOmegaProj, Matrix.vecMulVec_mulVec,
    star_twistedOmegaVec_dotProduct_self (mul_eq_one_comm.mp hUunit),
    dotProduct_comm, smul_dotProduct, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op,
    twistedOmegaVec_dotProduct_star_self (mul_eq_one_comm.mp hUunit)]
  ring

/-- The trace of the witness state is `d² + 2d`. -/
theorem trace_breuerHallWitnessState {U : Matrix (Fin d) (Fin d) ℂ} (hU : U * Uᴴ = 1) :
    (breuerHallWitnessState U).trace = (d : ℂ) ^ 2 + 2 * d := by
  rw [breuerHallWitnessState, Matrix.trace_add, Matrix.trace_add, Matrix.trace_one,
    trace_swapMatrix, trace_twistedOmegaProj hU]
  simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul]
  ring

/-- The pairing of the witness state with the twisted projector has trace `d²`: the
`1 + F` summand contributes `d + (-d) = 0` and the `P₀` summand contributes `d²`. -/
theorem trace_breuerHallWitnessState_mul_twistedOmegaProj {U : Matrix (Fin d) (Fin d) ℂ}
    (hUanti : Uᵀ = -U) (hUunit : Uᴴ * U = 1) :
    (breuerHallWitnessState U * twistedOmegaProj U).trace = (d : ℂ) ^ 2 := by
  have hU : U * Uᴴ = 1 := mul_eq_one_comm.mp hUunit
  rw [breuerHallWitnessState, add_mul, Matrix.trace_add, add_mul, Matrix.trace_add,
    one_mul, trace_twistedOmegaProj hU,
    trace_swapMatrix_mul_twistedOmegaProj hUanti hUunit,
    trace_twistedOmegaProj_mul_self hUunit]
  ring

/-- The pairing of SWAP with the witness state has trace `d²`: SWAP is an involution of
trace `d`, so the `1 + F` summand contributes `d + d²` and the `P₀` summand contributes
`-d` by antisymmetry. -/
theorem trace_swapMatrix_mul_breuerHallWitnessState {U : Matrix (Fin d) (Fin d) ℂ}
    (hUanti : Uᵀ = -U) (hUunit : Uᴴ * U = 1) :
    (Matrix.swapMatrix d * breuerHallWitnessState U).trace = (d : ℂ) ^ 2 := by
  rw [breuerHallWitnessState, mul_add, Matrix.trace_add, mul_add, mul_one,
    Matrix.swapMatrix_mul_self, Matrix.trace_add, trace_swapMatrix, Matrix.trace_one,
    trace_swapMatrix_mul_twistedOmegaProj hUanti hUunit]
  simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul]
  ring

/-- **The carrying identity evaluated at the witness.** Pairing the ampliation of the
Breuer-Hall map applied to the witness state against the twisted maximally entangled
projector gives `d(2 - d)`. -/
theorem trace_tensorMapId_breuerHallMap_witness_mul_twistedOmegaProj
    {U : Matrix (Fin d) (Fin d) ℂ} (hUanti : Uᵀ = -U) (hUunit : Uᴴ * U = 1) :
    ((Matrix.tensorMapId (Matrix.breuerHallMap U) (breuerHallWitnessState U))
        * twistedOmegaProj U).trace
      = (d : ℂ) * (2 - d) := by
  have hU : U * Uᴴ = 1 := mul_eq_one_comm.mp hUunit
  rw [trace_tensorMapId_breuerHallMap_mul_twistedOmegaProj hUunit,
    trace_breuerHallWitnessState hU,
    trace_breuerHallWitnessState_mul_twistedOmegaProj hUanti hUunit,
    trace_swapMatrix_mul_breuerHallWitnessState hUanti hUunit]
  ring

/-! ## Indecomposability -/

/-- The ampliation of the Breuer-Hall map applied to the witness state is not positive
semidefinite in dimension `d > 2`: its quadratic form at the twisted maximally entangled
vector equals `d(2 - d) < 0`. -/
theorem not_posSemidef_tensorMapId_breuerHallMap_witness (hd : 2 < d)
    {U : Matrix (Fin d) (Fin d) ℂ} (hUanti : Uᵀ = -U) (hUunit : Uᴴ * U = 1) :
    ¬ (Matrix.tensorMapId (Matrix.breuerHallMap U) (breuerHallWitnessState U)).PosSemidef := by
  intro hQ
  have hform := hQ.dotProduct_mulVec_nonneg (twistedOmegaVec U)
  rw [← trace_mul_twistedOmegaProj,
    trace_tensorMapId_breuerHallMap_witness_mul_twistedOmegaProj hUanti hUunit] at hform
  have hcast : (d : ℂ) * (2 - d) = ((d * (2 - d) : ℝ) : ℂ) := by push_cast; ring
  rw [hcast, Complex.zero_le_real] at hform
  have hd' : (2 : ℝ) < d := by exact_mod_cast hd
  have hpos : (0 : ℝ) < (d - 2) * d :=
    mul_pos (sub_pos.mpr hd') (lt_trans two_pos hd')
  nlinarith

/-- **Wolf Chapter 3, Example 3.1 (indecomposability).** For an antisymmetric unitary `U`
in dimension `d > 2`, the Breuer-Hall map is not decomposable: the witness state
`breuerHallWitnessState U` is PPT (`breuerHallWitnessState_isPPT`), but its image under
the ampliation of `T_BH` is not positive semidefinite
(`not_posSemidef_tensorMapId_breuerHallMap_witness`). -/
theorem breuerHallMap_not_isDecomposablePositiveMap (hd : 2 < d)
    {U : Matrix (Fin d) (Fin d) ℂ} (hUanti : Uᵀ = -U) (hUunit : Uᴴ * U = 1) :
    ¬ IsDecomposablePositiveMap (Matrix.breuerHallMap U) :=
  not_isDecomposablePositiveMap_of_isPPT_not_tensorMapId_posSemidef
    (breuerHallWitnessState_posSemidef U)
    (breuerHallWitnessState_isPPT hUanti hUunit)
    (not_posSemidef_tensorMapId_breuerHallMap_witness hd hUanti hUunit)

/-- **Wolf Chapter 3, Example 3.1.** For an antisymmetric unitary `U` in dimension
`d > 2` (in particular for every even `d ≥ 4`, since antisymmetric unitaries require `d`
even), the Breuer-Hall map `T_BH` is an indecomposable positive map. -/
theorem breuerHallMap_isIndecomposablePositiveMap (hd : 2 < d)
    {U : Matrix (Fin d) (Fin d) ℂ} (hUanti : Uᵀ = -U) (hUunit : Uᴴ * U = 1) :
    IsIndecomposablePositiveMap (Matrix.breuerHallMap U) :=
  ⟨Matrix.breuerHallMap_isPositiveMap U hUanti (le_of_eq hUunit),
    breuerHallMap_not_isDecomposablePositiveMap hd hUanti hUunit⟩

end Matrix
