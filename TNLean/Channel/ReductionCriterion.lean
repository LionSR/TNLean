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
and real casts of `k` into `ℂ` coincide.  The identification lemma
`Matrix.reductionMap_eq_tEta` records this, so the `n`-positivity
threshold (`Matrix.isNPositiveMap_tEta_iff`), the Choi formula
(`ChoiJamiolkowski.choiMatrix_tEta`), and the self-duality
(`Matrix.traceAdjointMap_reductionMap`) all describe one object.  No third
definition of the map is introduced.

## The operator-implication step

Wolf reaches eq. (3.18) in two steps:
`Schmidt-number(ρ) ≤ n ⟹ (T_n ⊗ id)(ρ) ≥ 0 ⟹ n • (1 ⊗ ρ₂) ≥ ρ`,
the first step by `n`-positivity of `T_n` and the second by the elementary
identity
`(T_n ⊗ id)(ρ) = (1 ⊗ ρ₂) − n⁻¹ • ρ`,
where the partial trace over the first factor produces `ρ₂`.  This file
formalizes the **second step**: positivity of `(T_n ⊗ id)(ρ)` is equivalent,
after scaling by `n > 0`, to `n • (1 ⊗ ρ₂) ≥ ρ`; applying the map to the second
factor instead gives the symmetric bound `n • (ρ₁ ⊗ 1) ≥ ρ`.  The implications
are recorded as `Matrix.reductionCriterion_left` and
`Matrix.reductionCriterion_right`.  The first step (the Schmidt-number premise)
is formalized in `SchmidtNumber.lean`, where the two steps are composed into the
full criterion `Matrix.reductionCriterion_left_of_hasSchmidtNumberLE` and
`Matrix.reductionCriterion_right_of_hasSchmidtNumberLE`.

## Main definitions

* `Matrix.reductionWitness` -- Wolf's witness `W_n = d⁻¹ • 1 − n⁻¹ • |Ω⟩⟨Ω|`.

## Main results

* `Matrix.reductionMap_eq_tEta` -- the identification `reductionMap D k = tEta D (k : ℝ)`.
* `ChoiJamiolkowski.choiMatrix_reductionMap_eq_reductionWitness` -- the Choi
  operator of `T_n` is the witness `W_n`.
* `Matrix.tensorMapId_tEta_eq` -- `(T_n ⊗ id)(ρ) = (1 ⊗ ρ₂) − n⁻¹ • ρ`.
* `Matrix.reductionCriterion_left` and `Matrix.reductionCriterion_right` -- the
  **operator-implication step of Wolf eq. (3.18):** positivity of `(T_n ⊗ id)(ρ)`
  yields `n • (1 ⊗ ρ₂) ≥ ρ`, and positivity of `(T_n ⊗ id)(ρ^swap)` --
  equivalently Wolf's symmetric condition `(id ⊗ T_n)(ρ) ≥ 0` -- yields
  `n • (ρ₁ ⊗ 1) ≥ ρ`.  Wolf's Schmidt-number premise is supplied in
  `SchmidtNumber.lean`, which composes these with the first step into the full
  criterion.

## Scope

These theorems isolate the second of Wolf's two steps: the operator implication
from `(T_n ⊗ id)(ρ) ≥ 0` to the inequalities of eq. (3.18), with no premise on
the Schmidt number.  The first step (a state of Schmidt number at most `n` has
`(T_n ⊗ id)(ρ) ≥ 0`) and the resulting full criterion with its Schmidt-number
premise are formalized in `SchmidtNumber.lean`.

The other entanglement criteria of Example 3.1 (the Breuer–Hall map, the
Choi-type maps, indecomposability) are a further step and are not part of this
file.

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

/-- **Wolf Chapter 3, Example 3.1 (Proposition 3.2).** The reduction map
`T_k(X) = tr(X) • 1 − k⁻¹ • X` is `k`-positive for `1 ≤ k < D`. It is the family
map `tEta D k` at parameter `η = k`, and `tEta D η` is `k`-positive exactly when
`η ≥ k`, so the threshold is attained at `η = k`. -/
theorem reductionMap_isNPositiveMap [NeZero D] {k : ℕ} (hk1 : 1 ≤ k) (hk : k < D) :
    IsNPositiveMap k (reductionMap D k) := by
  rw [reductionMap_eq_tEta]
  have hη : (0 : ℝ) < (k : ℝ) := by
    have : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
    linarith
  exact (isNPositiveMap_tEta_iff hη hk1 hk).mpr le_rfl

/-- **Wolf's reduction witness.** The entanglement witness attached to `T_n` is
`W_n = D⁻¹ • 1 − n⁻¹ • |Ω⟩⟨Ω|` on `M_D(ℂ) ⊗ M_D(ℂ)`.  It is exactly the Choi
operator of `T_n`. -/
noncomputable def reductionWitness (D n : ℕ) :
    Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ :=
  ((D : ℂ)⁻¹) • (1 : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ) -
    ((n : ℂ)⁻¹) • Matrix.omegaProj D

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

This is an internal auxiliary fact relating `bipartiteSlice` and `traceLeft`,
used only to prove `tensorMapId_tEta_eq` below. -/
private theorem trace_bipartiteSlice (ρ : Matrix (Fin D × Fin D') (Fin D × Fin D') ℂ)
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

/-- **Operator-implication step of Wolf's reduction criterion (eq. (3.18)), first
form.** If applying `T_n` to the first tensor factor of a bipartite matrix `ρ`
yields a positive semidefinite operator, then `n • (1 ⊗ ρ₂) ≥ ρ`, where
`ρ₂ = traceLeft ρ` is the reduced density on the second factor.

This is the second of Wolf's two steps: the path to the inequality is
`Schmidt-number(ρ) ≤ n ⟹ (T_n ⊗ id)(ρ) ≥ 0 ⟹ n • (1 ⊗ ρ₂) ≥ ρ`, and this
theorem takes `(T_n ⊗ id)(ρ) ≥ 0` as a hypothesis.  The first step and the
composed full criterion with its Schmidt-number premise are
`Matrix.reductionCriterion_left_of_hasSchmidtNumberLE` in `SchmidtNumber.lean`. -/
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

/-- **Operator-implication step of Wolf's reduction criterion (eq. (3.18)),
second form.** Let `ρ` be a bipartite matrix and
`ρ^swap = ρ.submatrix Prod.swap Prod.swap` its image under the factor swap.  If
`(T_n ⊗ id)(ρ^swap)` is positive semidefinite, then `n • (ρ₁ ⊗ 1) ≥ ρ`, where
`ρ₁ = traceRight ρ` is the reduced density on the first factor.

Because the factor swap is a unitary reindexing, `(T_n ⊗ id)(ρ^swap) ≥ 0` is
equivalent to Wolf's symmetric condition `(id ⊗ T_n)(ρ) ≥ 0`, which applies
`T_n` to the second factor.  The proof reindexes to the first factor, applies
the first form, and reindexes back; positive semidefiniteness and the order are
invariant under the swap.

As with the first form, this is the second of Wolf's two steps, taking
`(T_n ⊗ id)(ρ^swap) ≥ 0` as a hypothesis.  The first step and the composed full
criterion with its Schmidt-number premise are
`Matrix.reductionCriterion_right_of_hasSchmidtNumberLE` in
`SchmidtNumber.lean`. -/
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
