/-
Copyright (c) 2026 Sirui Lu and TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import TNLean.Channel.NPositivityChainStrict
import TNLean.Channel.PartialTrace
import TNLean.Channel.TensorMap

/-!
# Wolf's reduction criterion

Wolf's Chapter 3, Example 3.1 records the one-parameter family of `n`-positive
maps `T_n(X) = tr(X) • 1 − n⁻¹ • X` on `M_d(ℂ)` and derives the **reduction
criterion** (Wolf eq. (3.18)): for a bipartite state `ρ` of Schmidt number at
most `n` one has
`n • (ρ₁ ⊗ 1) ≥ ρ` and `n • (1 ⊗ ρ₂) ≥ ρ`,
where `ρ₁` and `ρ₂` are the two reduced density matrices.  The witness operator
attached to `T_n` is `W_n = d⁻¹ • 1 − n⁻¹ • |Ω⟩⟨Ω|`.

This file collects the reduction-criterion content that is provable from the
foundations already in the development.

## Reconciliation of the two reduction maps

The development carries two definitions of the same map: `Matrix.reductionMap D
k` (parametrized by `k : ℕ`) in `PositiveExamples.lean`, and the later
`Matrix.tEta D η` (parametrized by `η : ℝ`) in `NPositivityChainStrict.lean`.
They agree at `η = k`: `reductionMap D k = tEta D (k : ℝ)`, since the only
difference is the scalar `(k : ℂ)⁻¹` versus `((k : ℝ) : ℂ)⁻¹`, and the natural
and real casts of `k` into `ℂ` coincide.  The bridge lemma
`Matrix.reductionMap_eq_tEta` makes this identification, so the `n`-positivity
threshold (`Matrix.isNPositiveMap_tEta_iff`), the Choi formula
(`ChoiJamiolkowski.choiMatrix_tEta`), and the self-duality
(`Matrix.traceAdjointMap_reductionMap`) all describe one object.  No third
definition of the map is introduced.

## The operator implication

The core of Wolf eq. (3.18) is the elementary identity
`(T_n ⊗ id)(ρ) = (1 ⊗ ρ₂) − n⁻¹ • ρ`,
where the partial trace over the first factor produces `ρ₂`.  Positivity of the
left-hand side is therefore equivalent, after scaling by `n > 0`, to
`n • (1 ⊗ ρ₂) ≥ ρ`; applying the map to the second factor instead gives the
symmetric bound `n • (ρ₁ ⊗ 1) ≥ ρ`.  The implications are recorded as
`Matrix.reductionCriterion_left` and `Matrix.reductionCriterion_right`.

## Main definitions

* `Matrix.reductionWitness` -- Wolf's witness `W_n = d⁻¹ • 1 − n⁻¹ • |Ω⟩⟨Ω|`.

## Main results

* `Matrix.reductionMap_eq_tEta` -- the bridge `reductionMap D k = tEta D (k : ℝ)`.
* `ChoiJamiolkowski.choiMatrix_reductionMap_eq_reductionWitness` -- the Choi
  operator of `T_n` is the witness `W_n`.
* `Matrix.tensorMapId_tEta_eq` -- `(T_n ⊗ id)(ρ) = (1 ⊗ ρ₂) − n⁻¹ • ρ`.
* `Matrix.reductionCriterion_left` and `Matrix.reductionCriterion_right` --
  **Wolf eq. (3.18):** positivity of `(T_n ⊗ id)(ρ)` (resp. `(id ⊗ T_n)(ρ)`)
  yields `n • (1 ⊗ ρ₂) ≥ ρ` (resp. `n • (ρ₁ ⊗ 1) ≥ ρ`).

## Scope

The *entanglement* form of the reduction criterion (a separable state satisfies
eq. (3.18)) requires a separable-state predicate, which is not yet part of the
development; the operator implication above is the separability-free content.
The other entanglement criteria of Example 3.1 (PPT / partial transpose, the
Breuer–Hall map, the Choi-type maps) need a bipartite partial-transpose object
and indecomposability, which are likewise absent.

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Chapter 3,
  Example 3.1, equation (3.18)][Wolf2012QChannels]
-/

open scoped BigOperators Matrix ComplexOrder MatrixOrder Kronecker
open Matrix

namespace Matrix

variable {D : ℕ}

/-- **Reconciliation of the two reduction maps.** The natural-parameter
reduction map `reductionMap D k` coincides with the real-parameter map
`tEta D (k : ℝ)`: the two definitions differ only by the scalar `(k : ℂ)⁻¹`
versus `((k : ℝ) : ℂ)⁻¹`, and the natural and real casts of `k` into `ℂ` agree.
-/
theorem reductionMap_eq_tEta (D k : ℕ) : reductionMap D k = tEta D (k : ℝ) := by
  apply LinearMap.ext
  intro X
  rw [reductionMap_apply, tEta_apply, Complex.ofReal_natCast]

end Matrix

namespace ChoiJamiolkowski

variable {D : ℕ}

/-- The Choi operator of `reductionMap D k` is the same matrix as that of
`tEta D k`, since the two maps coincide. -/
theorem choiMatrix_reductionMap_eq_choiMatrix_tEta [NeZero D] (k : ℕ) :
    choiMatrix (Matrix.reductionMap D k) = choiMatrix (Matrix.tEta D (k : ℝ)) := by
  rw [Matrix.reductionMap_eq_tEta]

end ChoiJamiolkowski

namespace Matrix

variable {D : ℕ}

/-- **Wolf's reduction witness.** The entanglement witness attached to `T_n` is
`W_n = D⁻¹ • 1 − n⁻¹ • |Ω⟩⟨Ω|` on `M_D(ℂ) ⊗ M_D(ℂ)`.  It is exactly the Choi
operator of `T_n`. -/
noncomputable def reductionWitness (D n : ℕ) :
    Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ :=
  ((D : ℂ)⁻¹) • (1 : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ) -
    ((n : ℂ)⁻¹) • Matrix.omegaProj D

@[simp]
theorem reductionWitness_apply (D n : ℕ) (x y : Fin D × Fin D) :
    reductionWitness D n x y =
      ((D : ℂ)⁻¹) • (1 : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ) x y -
        ((n : ℂ)⁻¹) • Matrix.omegaProj D x y := rfl

end Matrix

namespace ChoiJamiolkowski

variable {D : ℕ}

/-- **Wolf Chapter 3, Example 3.1.** The Choi operator of the reduction map
`T_n(X) = tr(X) • 1 − n⁻¹ • X` is the reduction witness
`W_n = D⁻¹ • 1 − n⁻¹ • |Ω⟩⟨Ω|`. -/
theorem choiMatrix_reductionMap_eq_reductionWitness [NeZero D] (n : ℕ) :
    choiMatrix (Matrix.reductionMap D n) = Matrix.reductionWitness D n := by
  rw [Matrix.reductionMap_eq_tEta, ChoiJamiolkowski.choiMatrix_tEta]
  ext x y
  rw [Matrix.reductionWitness, Complex.ofReal_natCast]

end ChoiJamiolkowski

namespace Matrix

variable {D D' : ℕ}

/-- The trace of the `(i₂, j₂)`-slice of a bipartite matrix is the `(i₂, j₂)`
entry of the partial trace over the first factor: `tr(ρ_{·,i₂,·,j₂}) = (ρ₂)_{i₂ j₂}`.
-/
theorem trace_bipartiteSlice (ρ : Matrix (Fin D × Fin D') (Fin D × Fin D') ℂ)
    (i₂ j₂ : Fin D') :
    Matrix.trace (bipartiteSlice ρ i₂ j₂) = traceLeft ρ i₂ j₂ := by
  simp only [Matrix.trace, Matrix.diag, bipartiteSlice_apply, traceLeft_apply]

/-- **The reduction-criterion identity (Wolf eq. (3.18)).** Applying `T_n` to the
first tensor factor of a bipartite matrix gives
`(T_n ⊗ id)(ρ) = (1 ⊗ ρ₂) − n⁻¹ • ρ`,
where `ρ₂ = traceLeft ρ` is the reduced density on the second factor. -/
theorem tensorMapId_tEta_eq (η : ℝ) (ρ : Matrix (Fin D × Fin D') (Fin D × Fin D') ℂ) :
    tensorMapId (tEta D η) ρ
      = (1 : Matrix (Fin D) (Fin D) ℂ) ⊗ₖ traceLeft ρ - ((η : ℂ)⁻¹) • ρ := by
  ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
  rw [tensorMapId_apply, tEta_apply]
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, bipartiteSlice_apply,
    trace_bipartiteSlice, kroneckerMap_apply, smul_eq_mul]
  by_cases hij : i₁ = j₁ <;> simp [hij]

/-- **Wolf's reduction criterion, equation (3.18), first form.** If applying
`T_n` to the first tensor factor of a bipartite matrix `ρ` yields a positive
semidefinite operator, then `n • (1 ⊗ ρ₂) ≥ ρ`, where `ρ₂ = traceLeft ρ` is the
reduced density on the second factor.

This is the separability-free operator content of the reduction criterion: it
takes positivity of `(T_n ⊗ id)(ρ)` as a hypothesis rather than deriving it from
a separability assumption on `ρ`. -/
theorem reductionCriterion_left {n : ℕ} (hn : 0 < n)
    (ρ : Matrix (Fin D × Fin D') (Fin D × Fin D') ℂ)
    (hpos : (tensorMapId (tEta D (n : ℝ)) ρ).PosSemidef) :
    ρ ≤ (n : ℂ) • ((1 : Matrix (Fin D) (Fin D) ℂ) ⊗ₖ traceLeft ρ) := by
  rw [Matrix.le_iff]
  have hnC : (0 : ℂ) ≤ (n : ℂ) := by exact_mod_cast Nat.zero_le n
  have hscaled := hpos.smul hnC
  have hrw :
      (n : ℂ) • tensorMapId (tEta D (n : ℝ)) ρ
        = (n : ℂ) • ((1 : Matrix (Fin D) (Fin D) ℂ) ⊗ₖ traceLeft ρ) - ρ := by
    rw [tensorMapId_tEta_eq, smul_sub, smul_smul]
    have hcancel : (n : ℂ) * ((n : ℝ) : ℂ)⁻¹ = 1 := by
      rw [Complex.ofReal_natCast, mul_inv_cancel₀]
      exact_mod_cast hn.ne'
    rw [hcancel, one_smul]
  rwa [hrw] at hscaled

/-- **Wolf's reduction criterion, equation (3.18), second form.** If applying
`T_n` to the second tensor factor of a bipartite matrix `ρ` yields a positive
semidefinite operator, then `n • (ρ₁ ⊗ 1) ≥ ρ`, where `ρ₁ = traceRight ρ` is the
reduced density on the first factor.

The second factor is handled by reindexing to the first, applying the first
form, and reindexing back; positive semidefiniteness and the order are invariant
under the simultaneous index swap. -/
theorem reductionCriterion_right {n : ℕ} (hn : 0 < n)
    (ρ : Matrix (Fin D × Fin D') (Fin D × Fin D') ℂ)
    (hpos : (tensorMapId (tEta D' (n : ℝ))
        (ρ.submatrix Prod.swap Prod.swap)).PosSemidef) :
    ρ ≤ (n : ℂ) • (traceRight ρ ⊗ₖ (1 : Matrix (Fin D') (Fin D') ℂ)) := by
  -- Swap the two tensor factors and apply the first form, then swap back.
  set σ : Matrix (Fin D' × Fin D) (Fin D' × Fin D) ℂ :=
    ρ.submatrix Prod.swap Prod.swap with hσ
  have hleft := reductionCriterion_left (D := D') (D' := D) hn σ hpos
  rw [Matrix.le_iff] at hleft ⊢
  -- Reindex the inequality witness back through the factor swap.
  have hsub :
      ((n : ℂ) • (traceRight ρ ⊗ₖ (1 : Matrix (Fin D') (Fin D') ℂ)) - ρ)
        = ((n : ℂ) • ((1 : Matrix (Fin D') (Fin D') ℂ) ⊗ₖ traceLeft σ) - σ).submatrix
            Prod.swap Prod.swap := by
    ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.submatrix_apply, smul_eq_mul,
      kroneckerMap_apply, Matrix.one_apply, Prod.swap_prod_mk, hσ,
      traceLeft_apply, traceRight_apply]
    by_cases hi : i₂ = j₂ <;> by_cases hj : i₁ = j₁ <;>
      simp [hi, hj, mul_comm]
  rw [hsub]
  exact hleft.submatrix Prod.swap

end Matrix
