/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.FundamentalTheorem.Arbitrary.Corollaries.GaugeScalars

/-!
# Normal blocks: blocks and weights agree exactly

In the class form for weighted sums with every representative normal of positive bond dimension, the
gauge scalars are trivial, so two weighted sums agree at every positive length exactly when a
bijection of the index sets preserves the classes and the weights. This is the block-and-weight form
of the fundamental theorem for canonical forms.

## Main results

* `MPSTensor.forall_sum_pow_mul_mpv_eq_iff_exists_equiv_eq_and_eq_of_isNormal`.

## References

* Cirac, Pérez-García, Schuch, Verstraete, arXiv:1606.00608 (canonical forms); Molnár, Ge,
  Schuch, Cirac, arXiv:1706.07329 (the same form for canonical forms of matrix product states).
-/

namespace MPSTensor

variable {d : ℕ}

/-- **Blocks and weights for normal representatives.** For normal representatives `R j` of positive
bond dimension, pairwise not related by a scalar and a gauge, two weighted sums `∑_s μ_s ^ N
V_N(R_{cls s})` and `∑_t μ'_t ^ N V_N(R_{cls' t})` with nonzero weights agree at every positive
length exactly when a bijection `τ` of the index types preserves the classes and the weights. -/
theorem forall_sum_pow_mul_mpv_eq_iff_exists_equiv_eq_and_eq_of_isNormal {J : Type*}
    {DR : J → ℕ} {R : ∀ j, MPSTensor d (DR j)} (hR : ∀ j, Kraus.IsNormal (R j))
    (hD : ∀ j, 0 < DR j)
    (hsep : ∀ j j', j ≠ j' → ∀ c : ℂ, ¬ IsGaugeRelated (c • R j) (R j'))
    {I K : Type*} [Fintype I] [Fintype K] (cls : I → J) (cls' : K → J) {μ : I → ℂ}
    {μ' : K → ℂ} (hμ : ∀ s, μ s ≠ 0) (hμ' : ∀ t, μ' t ≠ 0) :
    (∀ N, 0 < N → ∀ σ : Fin N → Fin d,
        ∑ s, μ s ^ N * mpv (R (cls s)) σ = ∑ t, μ' t ^ N * mpv (R (cls' t)) σ) ↔
      ∃ τ : I ≃ K, ∀ s, cls' (τ s) = cls s ∧ μ' (τ s) = μ s := by
  have hirr : ∀ j, Matrix.IsIrreducibleAction (R j) :=
    fun j => isIrreducibleAction_of_isNormal _ (hR j) (hD j)
  have hlet : ∀ j, ∃ i, R j i ≠ 0 := fun j => by
    have : NeZero (DR j) := ⟨(hD j).ne'⟩
    exact exists_ne_zero_of_isNormal (hR j)
  refine (forall_sum_pow_mul_mpv_eq_iff_exists_equiv_eq_and_div_mem_gaugeScalars hirr hlet hsep
    cls cls' hμ hμ').trans
      (exists_congr fun τ => forall_congr' fun s => and_congr_right fun _ => ?_)
  rw [gaugeScalars_eq_singleton_one_of_isNormal (hR _) (hD _), Set.mem_singleton_iff,
    div_eq_one_iff_eq (hμ' (τ s)), eq_comm]

end MPSTensor
