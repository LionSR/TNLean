/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.RegularBoundaryState
import TNLean.PEPS.GInjectiveRangeEquivalence
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# Gibbs operators and the invariant regular boundary support

For a nontrivial finite group, the regular boundary density is singular on
the full virtual space. It therefore cannot be a matrix exponential there.
On its invariant support it is a positive scalar multiple of the identity,
and is the Gibbs operator of a constant Hamiltonian.

The density is the regular virtual boundary state of Schuch, Cirac, and
Pérez-García, arXiv:1001.3807, Theorem 6.9, lines 2027–2076. These finite
dimensional statements clarify the support needed when considering the
Gibbs representation in the bulk–boundary conjecture of
arXiv:1903.09439, Conjecture `gap2Dboundary1dlocal`, local source lines
980–1024. They do not establish locality of a boundary Hamiltonian or a
uniform bulk spectral gap.

## References

- [arXiv:1001.3807](https://arxiv.org/abs/1001.3807) -- N. Schuch, J. I. Cirac,
  D. Pérez-García, *PEPS as ground states: degeneracy and topology*
- [arXiv:1903.09439](https://arxiv.org/abs/1903.09439) -- J. I. Cirac, J. Garre-Rubio,
  D. Pérez-García, *Mathematical open problems in Projected Entangled Pair States*
-/

open scoped Matrix ComplexOrder

namespace TNLean.PEPS

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

/-- The regular boundary density has a proper support for a nontrivial group.
Source: SCP10, Theorem 6.9, lines 2027–2076. -/
theorem rank_regularBoundaryDensity_lt_card (n : ℕ) (hG : 1 < Fintype.card G) :
    (regularBoundaryDensity (G := G) n).rank < Fintype.card (Fin (n + 1) → G) := by
  rw [rank_regularBoundaryDensity, Fintype.card_fun, Fintype.card_fin]
  exact Nat.pow_lt_pow_right hG (Nat.lt_succ_self n)

/-- The regular virtual boundary density is not invertible on the full
boundary space for a nontrivial group. Source: SCP10, Theorem 6.9,
lines 2027–2076. -/
theorem not_isUnit_regularBoundaryDensity (n : ℕ) (hG : 1 < Fintype.card G) :
    ¬ IsUnit (regularBoundaryDensity (G := G) n) := by
  intro h
  exact (rank_regularBoundaryDensity_lt_card n hG).ne
    (Matrix.rank_of_isUnit _ h)

/-- No finite matrix Hamiltonian has the full-space regular boundary density
as its exponential when the group is nontrivial. This is a support
obstruction, rather than a spectral-gap assertion, relevant to the Gibbs
representation in arXiv:1903.09439, Conjecture `gap2Dboundary1dlocal`. -/
theorem regularBoundaryDensity_ne_exp (n : ℕ) (hG : 1 < Fintype.card G)
    (H : Matrix (Fin (n + 1) → G) (Fin (n + 1) → G) ℂ) :
    regularBoundaryDensity (G := G) n ≠ NormedSpace.exp H := by
  intro h
  apply not_isUnit_regularBoundaryDensity n hG
  rw [h]
  exact Matrix.isUnit_exp H

/-- The density in the relative-coordinate basis of its invariant support.
Source: SCP10, Theorem 6.9, lines 2027–2076. -/
noncomputable def regularBoundarySupportedDensity (n : ℕ) :
    Matrix (Fin n → G) (Fin n → G) ℂ :=
  ((Fintype.card G : ℂ) ^ n)⁻¹ • 1

/-- A constant Hamiltonian on the invariant support, with inverse
temperature absorbed into its definition. Source: the flat support density
in SCP10, Theorem 6.9, lines 2027–2076. -/
noncomputable def regularBoundarySupportedHamiltonian (n : ℕ) :
    Matrix (Fin n → G) (Fin n → G) ℂ :=
  (Real.log (Fintype.card G ^ n : ℝ) : ℂ) • 1

/-- Relative coordinates identify the action of the full density on an
invariant vector with its supported density. Source: SCP10, Theorem 6.9,
lines 2027–2076. -/
theorem regularBoundarySupportedDensity_mulVec (n : ℕ)
    (x : (regularBoundaryRepresentation (G := G) (n + 1)).invariants) :
    regularBoundarySupportedDensity n *ᵥ regularBoundaryInvariantsEquiv n x =
      regularBoundaryInvariantsEquiv n
        ⟨regularBoundaryDensity n *ᵥ x.1, by
          rw [regularBoundaryDensity_mulVec_of_mem_invariants n x.1 x.2]
          exact Submodule.smul_mem _ _ x.2⟩ := by
  rw [regularBoundarySupportedDensity, Matrix.smul_mulVec, Matrix.one_mulVec]
  have hx := regularBoundaryDensity_mulVec_of_mem_invariants n x.1 x.2
  apply congrArg (regularBoundaryInvariantsEquiv n)
    (show ((Fintype.card G : ℂ) ^ n)⁻¹ • x =
        ⟨regularBoundaryDensity n *ᵥ x.1, _⟩ from Subtype.ext hx.symm)

/-- On its invariant support the flat regular boundary density is a Gibbs
operator of a constant Hamiltonian. This makes no locality assertion for
the original virtual legs. Source: SCP10, Theorem 6.9, lines 2027–2076;
compare arXiv:1903.09439, Conjecture `gap2Dboundary1dlocal`. -/
theorem regularBoundarySupportedDensity_eq_exp (n : ℕ) :
    regularBoundarySupportedDensity (G := G) n =
      NormedSpace.exp (-regularBoundarySupportedHamiltonian (G := G) n) := by
  have hpos : 0 < (Fintype.card G ^ n : ℝ) :=
    pow_pos (Nat.cast_pos.mpr Fintype.card_pos) n
  have hexp : NormedSpace.exp (-(Real.log (Fintype.card G ^ n : ℝ) : ℂ)) =
      ((Fintype.card G : ℂ) ^ n)⁻¹ := by
    rw [← Complex.exp_eq_exp_ℂ, Complex.exp_neg, ← Complex.ofReal_exp,
      Real.exp_log hpos]
    simp only [Complex.ofReal_pow, Complex.ofReal_natCast]
  rw [regularBoundarySupportedHamiltonian, regularBoundarySupportedDensity]
  rw [show -((Real.log (Fintype.card G ^ n : ℝ) : ℂ) •
      (1 : Matrix (Fin n → G) (Fin n → G) ℂ)) =
      Matrix.diagonal (fun _ => -(Real.log (Fintype.card G ^ n : ℝ) : ℂ)) by
        ext i j
        by_cases h : i = j <;> simp [h]]
  rw [Matrix.exp_diagonal]
  ext i j
  simp only [Pi.exp_def, Matrix.diagonal_apply, Matrix.smul_apply,
    Matrix.one_apply, smul_eq_mul, mul_ite, mul_one, mul_zero, hexp]

variable {Phys : Type*} [Fintype Phys]

/-- Tracing a regular G-injective open map over its physical index produces
a virtual Gram operator of rank equal to the invariant-boundary dimension.
No isometry assumption is needed. Source: SCP10, Definition 5.1 and the
regular boundary construction in Theorem 6.9, lines 1278–1296 and 2043–2076. -/
theorem IsGInjective.rank_regularBoundaryGram (n : ℕ)
    {T : ((Fin (n + 1) → G) → ℂ) →ₗ[ℂ] (Phys → ℂ)}
    (hT : IsGInjective (regularBoundaryRepresentation (G := G) (n + 1)) T) :
    ((LinearMap.toMatrix' T).conjTranspose * LinearMap.toMatrix' T).rank =
      Fintype.card G ^ n := by
  rw [Matrix.rank_conjTranspose_mul_self]
  change Module.finrank ℂ (Matrix.toLin' (LinearMap.toMatrix' T)).range = _
  rw [Matrix.toLin'_toMatrix', hT.finrank_range, finrank_regularBoundaryInvariants_succ]

/-- The virtual Gram operator of a regular G-injective open map cannot be
a full-space Gibbs exponential for a nontrivial group. This is the support
qualification needed for the Gibbs question in arXiv:1903.09439,
Conjecture `gap2Dboundary1dlocal`; no gap assertion is made. -/
theorem IsGInjective.regularBoundaryGram_ne_exp (n : ℕ)
    {T : ((Fin (n + 1) → G) → ℂ) →ₗ[ℂ] (Phys → ℂ)}
    (hT : IsGInjective (regularBoundaryRepresentation (G := G) (n + 1)) T)
    (hG : 1 < Fintype.card G)
    (H : Matrix (Fin (n + 1) → G) (Fin (n + 1) → G) ℂ) :
    (LinearMap.toMatrix' T).conjTranspose * LinearMap.toMatrix' T ≠
      NormedSpace.exp H := by
  intro h
  have hr := Matrix.rank_of_isUnit _ (h.symm ▸ Matrix.isUnit_exp H)
  rw [hT.rank_regularBoundaryGram n, Fintype.card_fun, Fintype.card_fin] at hr
  exact (Nat.pow_lt_pow_right hG (Nat.lt_succ_self n)).ne hr

end TNLean.PEPS
