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

open scoped Matrix ComplexOrder MatrixOrder
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

end Matrix
