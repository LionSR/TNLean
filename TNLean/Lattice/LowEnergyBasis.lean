/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.LowEnergyCommutator

/-!
# A basis of a two-dimensional ground space

Hastings, *Solving gapped Hamiltonians locally*, arXiv:cond-mat/0508554v3,
`References/cond-mat_0508554/proj3new.tex`, lines 1678–1693, chooses a basis of a ground space
of dimension `n = 2` that diagonalizes the compression `P M_j P` of one approximate term, with
eigenvalue difference `δλ_j`. In that basis the off-diagonal part of each other compression
`P M_i P` has norm `o(i) ≤ ‖[P M_i P, P M_j P]‖ / δλ_j`, and the ground states then satisfy
eq. `low` up to `o(i)` (lines 476–491):
`‖M_i Ψ_a - ⟨Ψ_a, M_i Ψ_a⟩ Ψ_a‖ ≤ ‖(1 - P) M_i Ψ_a‖ + o(i)`.

Here the basis is an orthonormal pair `v`, `w`, and the off-diagonal part of an operator `B` in
it is `⟨v, B w⟩ |v⟩⟨w| + ⟨w, B v⟩ |w⟩⟨v|`, the source's "matrix which has zeros on the
diagonal, but whose off-diagonal elements are the same as" those of `B` (lines 476–480).

## Main statements

* `offDiagonalPart`, `norm_offDiagonalPart_le`: the off-diagonal part and its norm, at most the
  larger of the two off-diagonal elements.
* `norm_offDiagonalPart_le_norm_commutator_div`: `o(i) ≤ ‖[A, B]‖ / |r - s|` in an eigenbasis
  of `A` with eigenvalues `r ≠ s`.
* `sum_norm_offDiagonalPart_le`: the sum of the `o(i)` over any finite family.
* `norm_apply_sub_inner_smul_le_add_offDiagonalPart`: eq. `low` up to `o(i)`.

**Scope restriction (two-dimensional ground space, summed bound):** only the case `n = 2` is
treated, as in the source, which only sketches `n > 2` (lines 1695–1705). The pair `v`, `w` is
taken as an orthonormal eigenbasis of `A = P M_j P` on the ground space, whose existence is the
spectral theorem; the choice of `j` maximizing `δλ_j` is not made, since every bound here holds
for any `j`. The summation of the decaying commutator bound over `i` into eq. `oibu`, which the
source states only to order of magnitude, is left as the sum of the commutators. Documented in
`docs/paper-gaps/hastings05_filtered_term_approximation.tex`.
-/

open scoped InnerProductSpace

namespace TNLean.Lattice

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]

/-- The off-diagonal part `⟨v, B w⟩ |v⟩⟨w| + ⟨w, B v⟩ |w⟩⟨v|` of `B` in the pair `v`, `w`.
Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 476–480. -/
noncomputable def offDiagonalPart (v w : E) (B : E →L[𝕜] E) : E →L[𝕜] E :=
  ⟪v, B w⟫_𝕜 • InnerProductSpace.rankOne 𝕜 v w + ⟪w, B v⟫_𝕜 • InnerProductSpace.rankOne 𝕜 w v

omit [CompleteSpace E] in
theorem offDiagonalPart_apply (v w : E) (B : E →L[𝕜] E) (x : E) :
    offDiagonalPart v w B x =
      (⟪v, B w⟫_𝕜 * ⟪w, x⟫_𝕜) • v + (⟪w, B v⟫_𝕜 * ⟪v, x⟫_𝕜) • w := by
  simp [offDiagonalPart, InnerProductSpace.rankOne_apply, smul_smul]

omit [CompleteSpace E] in
/-- **The norm of the off-diagonal part.** For an orthonormal pair `v`, `w`, the off-diagonal
part of `B` has norm at most the larger of `‖⟨v, B w⟩‖` and `‖⟨w, B v⟩‖`. -/
theorem norm_offDiagonalPart_le {v w : E} (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) (hvw : ⟪v, w⟫_𝕜 = 0)
    (B : E →L[𝕜] E) :
    ‖offDiagonalPart v w B‖ ≤ max ‖⟪v, B w⟫_𝕜‖ ‖⟪w, B v⟫_𝕜‖ := by
  set m := max ‖⟪v, B w⟫_𝕜‖ ‖⟪w, B v⟫_𝕜‖
  have hm : 0 ≤ m := le_max_of_le_left (norm_nonneg _)
  have hon : Orthonormal 𝕜 ![v, w] := by
    rw [orthonormal_iff_ite]
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [hvw, inner_self_eq_norm_sq_to_K, hv, hw, inner_eq_zero_symm.mp hvw]
  refine ContinuousLinearMap.opNorm_le_bound _ hm fun x => ?_
  have hbessel := hon.sum_inner_products_le (s := Finset.univ) x
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one] at hbessel
  have horth : ⟪(⟪v, B w⟫_𝕜 * ⟪w, x⟫_𝕜) • v, (⟪w, B v⟫_𝕜 * ⟪v, x⟫_𝕜) • w⟫_𝕜 = 0 := by
    rw [inner_smul_left, inner_smul_right, hvw, mul_zero, mul_zero]
  have hsq : ‖offDiagonalPart v w B x‖ ^ 2 =
      (‖⟪v, B w⟫_𝕜‖ * ‖⟪w, x⟫_𝕜‖) ^ 2 + (‖⟪w, B v⟫_𝕜‖ * ‖⟪v, x⟫_𝕜‖) ^ 2 := by
    rw [offDiagonalPart_apply, sq, norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ horth,
      norm_smul, norm_smul, hv, hw, norm_mul, norm_mul]
    ring
  have h1 : (‖⟪v, B w⟫_𝕜‖ * ‖⟪w, x⟫_𝕜‖) ^ 2 ≤ (m * ‖⟪w, x⟫_𝕜‖) ^ 2 := by
    gcongr
    exact le_max_left _ _
  have h2 : (‖⟪w, B v⟫_𝕜‖ * ‖⟪v, x⟫_𝕜‖) ^ 2 ≤ (m * ‖⟪v, x⟫_𝕜‖) ^ 2 := by
    gcongr
    exact le_max_right _ _
  have h3 : ‖offDiagonalPart v w B x‖ ^ 2 ≤ (m * ‖x‖) ^ 2 := by
    rw [hsq]
    nlinarith [sq_nonneg m]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h3

/-- **The off-diagonal part in an eigenbasis, `o(i) ≤ ‖[P M_i P, P M_j P]‖ / δλ_j`.** Let `A` be
self-adjoint with `A v = r v`, `A w = s w`, `r ≠ s`, for an orthonormal pair `v`, `w`. Then the
off-diagonal part of any `B` in this pair has norm at most `‖[A, B]‖ / |r - s|`. With
`A = P M_j P` and `B = P M_i P` this is Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`,
lines 1683–1690. -/
theorem norm_offDiagonalPart_le_norm_commutator_div {A : E →L[𝕜] E} (hA : IsSelfAdjoint A)
    (B : E →L[𝕜] E) {v w : E} (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) (hvw : ⟪v, w⟫_𝕜 = 0) {r s : ℝ}
    (hAv : A v = (r : 𝕜) • v) (hAw : A w = (s : 𝕜) • w) (hrs : r ≠ s) :
    ‖offDiagonalPart v w B‖ ≤ ‖A * B - B * A‖ / |r - s| := by
  refine (norm_offDiagonalPart_le hv hw hvw B).trans (max_le ?_ ?_)
  · simpa [hv, hw] using norm_inner_le_norm_commutator_div hA B hAv hAw hrs
  · simpa [hv, hw, abs_sub_comm] using norm_inner_le_norm_commutator_div hA B hAw hAv hrs.symm

/-- **The sum of the off-diagonal parts.** In an eigenbasis of `A` with eigenvalue difference
`δλ = |r - s| > 0`, `∑ᵢ o(i) ≤ (∑ᵢ ‖[A, Bᵢ]‖) / δλ` for any finite family `Bᵢ`. With
`A = P M_j P`, `Bᵢ = P M_i P` and the decay of the low-energy commutators in `d(i, j)`
(`norm_groundCompression_commutator_le_graphNeighborhood`), this is the step from the bound on
each `o(i)` to eq. `oibu`, Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 1689–1694. -/
theorem sum_norm_offDiagonalPart_le {ι : Type*} (t : Finset ι) {A : E →L[𝕜] E}
    (hA : IsSelfAdjoint A) (B : ι → E →L[𝕜] E) {v w : E} (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    (hvw : ⟪v, w⟫_𝕜 = 0) {r s : ℝ} (hAv : A v = (r : 𝕜) • v) (hAw : A w = (s : 𝕜) • w)
    (hrs : r ≠ s) :
    ∑ i ∈ t, ‖offDiagonalPart v w (B i)‖ ≤ (∑ i ∈ t, ‖A * B i - B i * A‖) / |r - s| := by
  rw [Finset.sum_div]
  exact Finset.sum_le_sum fun i _ =>
    norm_offDiagonalPart_le_norm_commutator_div hA (B i) hv hw hvw hAv hAw hrs

omit [CompleteSpace E] in
/-- **Eq. `low` up to `o(i)`.** Let `P` be the orthogonal projection onto a closed subspace `K`
with `v ∈ K` a unit vector, `⟨v, w⟩ = 0`, and every vector `u` of `K` equal to
`⟨v, u⟩ v + ⟨w, u⟩ w`, as when `v`, `w` is an orthonormal pair spanning `K`. Then for every `M`,
`‖M v - ⟨v, M v⟩ v‖ ≤ ‖(1 - P) M v‖ + ‖o‖`, where `o` is the off-diagonal part of `P M P` in the
pair. Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 476–491; the first term is the
one bounded by eq. `facld` (`norm_sub_starProjection_apply_le_of_gaussianFilteredTerm`). -/
theorem norm_apply_sub_inner_smul_le_add_offDiagonalPart (K : Submodule 𝕜 E)
    [K.HasOrthogonalProjection] {v w : E} (hv : ‖v‖ = 1) (hvw : ⟪v, w⟫_𝕜 = 0)
    (hvK : v ∈ K) (hspan : ∀ u ∈ K, u = ⟪v, u⟫_𝕜 • v + ⟪w, u⟫_𝕜 • w) (M : E →L[𝕜] E) :
    ‖M v - ⟪v, M v⟫_𝕜 • v‖ ≤
      ‖M v - K.starProjection (M v)‖ +
        ‖offDiagonalPart v w (K.starProjection * M * K.starProjection)‖ := by
  set P := K.starProjection
  have hPv : P v = v := K.starProjection_eq_self_iff.mpr hvK
  have hsa : ∀ x y, ⟪x, P y⟫_𝕜 = ⟪P x, y⟫_𝕜 := fun x y =>
    (K.starProjection_isSymmetric x y).symm
  have hdecomp := hspan (P (M v)) (K.starProjection_apply_mem _)
  have hvv : ⟪v, P (M v)⟫_𝕜 = ⟪v, M v⟫_𝕜 := by rw [hsa, hPv]
  have hoff : offDiagonalPart v w (P * M * P) v = ⟪w, P (M v)⟫_𝕜 • w := by
    rw [offDiagonalPart_apply, inner_eq_zero_symm.mp hvw, inner_self_eq_norm_sq_to_K, hv]
    simp [hPv]
  have hP : P (M v) - ⟪v, M v⟫_𝕜 • v = ⟪w, P (M v)⟫_𝕜 • w := by
    nth_rw 1 [hdecomp]
    rw [hvv]
    abel
  have hsplit : M v - ⟪v, M v⟫_𝕜 • v =
      (M v - P (M v)) + offDiagonalPart v w (P * M * P) v := by
    rw [hoff, ← hP]
    abel
  rw [hsplit]
  refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
  simpa [hv] using (offDiagonalPart v w (P * M * P)).le_opNorm v

end TNLean.Lattice
