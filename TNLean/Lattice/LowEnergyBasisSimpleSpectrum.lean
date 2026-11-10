/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.LowEnergyBasis

/-!
# A basis of a ground space diagonalizing one compression with simple spectrum

Hastings, *Solving gapped Hamiltonians locally*, arXiv:cond-mat/0508554v3,
`References/cond-mat_0508554/proj3new.tex`, lines 1678–1705, bounds the off-diagonal parts
`o(i)` of the compressions `P M_i P` of the approximate terms in a basis of the ground space that
diagonalizes one compression `A = P M_j P`. For `n = 2` this is `LowEnergyBasis.lean`; for
`n > 2` the source sketches an iteration over several compressions.

Here the ground space has an orthonormal basis `v : Fin n → E` of eigenvectors of `A` whose
eigenvalues are pairwise at least `δ > 0` apart. The off-diagonal part of an operator `B` in this
basis is the sum, over `k ≠ 0`, of the cyclic shifts
`S_k = ∑_a ⟨v_a, B v_{a+k}⟩ |v_a⟩⟨v_{a+k}|`. Each shift maps the coordinates of a vector to
orthogonal directions, so by Bessel's inequality its norm is at most its largest element, and
every element is at most `‖[A, B]‖ / δ`. Hence `o ≤ (n - 1) ‖[A, B]‖ / δ`, and the ground states
satisfy eq. `low` up to `o` (lines 476–491). For `n = 2` the bound is that of
`norm_offDiagonalPart_le_norm_commutator_div`.

## Main statements

* `shiftPart`, `norm_shiftPart_le`: the cyclic shift by `k` and its norm, at most its largest
  element.
* `offDiagonalPartFamily`, `norm_offDiagonalPartFamily_le`: the off-diagonal part, at most
  `n - 1` times the largest off-diagonal element.
* `norm_offDiagonalPartFamily_le_norm_commutator_div`: `o ≤ (n - 1) ‖[A, B]‖ / δ` in an
  eigenbasis of `A` with eigenvalue spacing at least `δ`.
* `sum_norm_offDiagonalPartFamily_le`: the sum of the `o(i)` over any finite family.
* `norm_apply_sub_inner_smul_le_add_offDiagonalPartFamily`: eq. `low` up to `o` for every basis
  vector.

These results are the one-level case of the source's iteration (lines 1695–1705), with `δ` a given
lower bound on the eigenvalue spacing; repeated eigenvalues of `M_j`, resolved by further
compressions `M_k`, are treated in `LowEnergyBasisIteration.lean`.

The summation of the decaying commutator bound over `i` into eq. `oibu` is carried out in
`LowEnergyCommutatorSum.lean`.
-/

open scoped InnerProductSpace

namespace TNLean.Lattice

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  {n : ℕ} [NeZero n]

/-- The cyclic shift by `k` of the off-diagonal part of `B` in the family `v`:
`∑_a ⟨v_a, B v_{a+k}⟩ |v_a⟩⟨v_{a+k}|`. -/
noncomputable def shiftPart (v : Fin n → E) (B : E →L[𝕜] E) (k : Fin n) : E →L[𝕜] E :=
  ∑ a, ⟪v a, B (v (a + k))⟫_𝕜 • InnerProductSpace.rankOne 𝕜 (v a) (v (a + k))

omit [NeZero n] in
theorem shiftPart_apply (v : Fin n → E) (B : E →L[𝕜] E) (k : Fin n) (x : E) :
    shiftPart v B k x = ∑ a, (⟪v a, B (v (a + k))⟫_𝕜 * ⟪v (a + k), x⟫_𝕜) • v a := by
  simp [shiftPart, InnerProductSpace.rankOne_apply, smul_smul]

/-- **The norm of a cyclic shift.** For an orthonormal family `v`, if every element
`⟨v_a, B v_{a+k}⟩` has norm at most `m`, then the shift by `k` has norm at most `m`. -/
theorem norm_shiftPart_le {v : Fin n → E} (hv : Orthonormal 𝕜 v) (B : E →L[𝕜] E) (k : Fin n)
    {m : ℝ} (hm : 0 ≤ m) (hB : ∀ a, ‖⟪v a, B (v (a + k))⟫_𝕜‖ ≤ m) :
    ‖shiftPart v B k‖ ≤ m := by
  refine ContinuousLinearMap.opNorm_le_bound _ hm fun x => ?_
  set l : Fin n → 𝕜 := fun a => ⟪v a, B (v (a + k))⟫_𝕜 * ⟪v (a + k), x⟫_𝕜
  have hsq : ‖shiftPart v B k x‖ ^ 2 = ∑ a, ‖l a‖ ^ 2 := by
    rw [shiftPart_apply, ← inner_self_eq_norm_sq (𝕜 := 𝕜), hv.inner_sum l l Finset.univ]
    simp only [RCLike.conj_mul, map_sum]
    norm_cast
  have hle : ∑ a, ‖l a‖ ^ 2 ≤ m ^ 2 * ∑ a, ‖⟪v (a + k), x⟫_𝕜‖ ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun a _ => ?_
    simp only [l, norm_mul, mul_pow]
    gcongr
    exact hB a
  have hshift : ∑ a, ‖⟪v (a + k), x⟫_𝕜‖ ^ 2 = ∑ b, ‖⟪v b, x⟫_𝕜‖ ^ 2 :=
    Fintype.sum_equiv (Equiv.addRight k) _ _ fun _ => rfl
  have hbessel := hv.sum_inner_products_le (s := Finset.univ) (x := x)
  have h : ‖shiftPart v B k x‖ ^ 2 ≤ (m * ‖x‖) ^ 2 := by
    rw [hsq, mul_pow]
    calc ∑ a, ‖l a‖ ^ 2 ≤ m ^ 2 * ∑ b, ‖⟪v b, x⟫_𝕜‖ ^ 2 := hshift ▸ hle
      _ ≤ m ^ 2 * ‖x‖ ^ 2 := by gcongr
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h

/-- The off-diagonal part of `B` in the family `v`, the sum of the cyclic shifts by `k ≠ 0`:
the operator with the same off-diagonal elements `⟨v_a, B v_b⟩`, `a ≠ b`, as `B` and zeros on the
diagonal. Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 476–480. -/
noncomputable def offDiagonalPartFamily (v : Fin n → E) (B : E →L[𝕜] E) : E →L[𝕜] E :=
  ∑ k ∈ Finset.univ.erase 0, shiftPart v B k

/-- **The norm of the off-diagonal part.** For an orthonormal family `v : Fin n → E`, if every
off-diagonal element `⟨v_a, B v_b⟩`, `a ≠ b`, has norm at most `m`, then the off-diagonal part
of `B` has norm at most `(n - 1) m`. -/
theorem norm_offDiagonalPartFamily_le {v : Fin n → E} (hv : Orthonormal 𝕜 v) (B : E →L[𝕜] E)
    {m : ℝ} (hm : 0 ≤ m) (hB : ∀ a b, a ≠ b → ‖⟪v a, B (v b)⟫_𝕜‖ ≤ m) :
    ‖offDiagonalPartFamily v B‖ ≤ (n - 1 : ℕ) * m := by
  refine (norm_sum_le _ _).trans ?_
  have hcard : (Finset.univ.erase (0 : Fin n)).card = n - 1 := by simp
  calc ∑ k ∈ Finset.univ.erase 0, ‖shiftPart v B k‖
      ≤ ∑ _k ∈ Finset.univ.erase (0 : Fin n), m := by
        refine Finset.sum_le_sum fun k hk => norm_shiftPart_le hv B k hm fun a => hB _ _ ?_
        intro h
        exact (Finset.ne_of_mem_erase hk) (by simpa using h)
    _ = (n - 1 : ℕ) * m := by rw [Finset.sum_const, hcard, nsmul_eq_mul]

/-- **The off-diagonal part in an eigenbasis with simple spectrum, `o ≤ (n - 1) ‖[A, B]‖ / δ`.**
Let `A` be self-adjoint with `A v_a = r_a v_a` for an orthonormal family `v : Fin n → E`, with
eigenvalues pairwise at least `δ > 0` apart. Then the off-diagonal part of any `B` in this family
has norm at most `(n - 1) ‖[A, B]‖ / δ`. With `A = P M_j P` and `B = P M_i P` this is the bound on
`o(i)` of Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 1683–1705, for a compression
`P M_j P` with simple spectrum on the ground space. -/
theorem norm_offDiagonalPartFamily_le_norm_commutator_div [CompleteSpace E] {A : E →L[𝕜] E}
    (hA : IsSelfAdjoint A) (B : E →L[𝕜] E) {v : Fin n → E} (hv : Orthonormal 𝕜 v) {r : Fin n → ℝ}
    (hAv : ∀ a, A (v a) = (r a : 𝕜) • v a) {δ : ℝ} (hδ : 0 < δ)
    (hgap : ∀ a b, a ≠ b → δ ≤ |r a - r b|) :
    ‖offDiagonalPartFamily v B‖ ≤ (n - 1 : ℕ) * (‖A * B - B * A‖ / δ) := by
  refine norm_offDiagonalPartFamily_le hv B (by positivity) fun a b hab => ?_
  have hrs : r a ≠ r b := fun h => by
    have := hgap a b hab
    rw [h, sub_self, abs_zero] at this
    linarith
  have h := norm_inner_le_norm_commutator_div hA B (hAv a) (hAv b) hrs
  rw [(hv.1 a), (hv.1 b), mul_one, mul_one] at h
  exact h.trans (div_le_div_of_nonneg_left (norm_nonneg _) hδ (hgap a b hab))

/-- **The sum of the off-diagonal parts.** In an eigenbasis of `A` with eigenvalue spacing at
least `δ > 0`, `∑ᵢ o(i) ≤ (n - 1) (∑ᵢ ‖[A, Bᵢ]‖) / δ` for any finite family `Bᵢ`. With
`A = P M_j P` and `Bᵢ = P M_i P`, this is the step from the bound on each `o(i)` to eq. `oibu`,
Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 1689–1705. -/
theorem sum_norm_offDiagonalPartFamily_le [CompleteSpace E] {ι : Type*} (t : Finset ι)
    {A : E →L[𝕜] E} (hA : IsSelfAdjoint A) (B : ι → E →L[𝕜] E) {v : Fin n → E}
    (hv : Orthonormal 𝕜 v)
    {r : Fin n → ℝ} (hAv : ∀ a, A (v a) = (r a : 𝕜) • v a) {δ : ℝ} (hδ : 0 < δ)
    (hgap : ∀ a b, a ≠ b → δ ≤ |r a - r b|) :
    ∑ i ∈ t, ‖offDiagonalPartFamily v (B i)‖ ≤
      (n - 1 : ℕ) * ((∑ i ∈ t, ‖A * B i - B i * A‖) / δ) := by
  rw [Finset.sum_div, Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ =>
    norm_offDiagonalPartFamily_le_norm_commutator_div hA (B i) hv hAv hδ hgap

/-- The off-diagonal part applied to a basis vector: `o v_a = ∑_{b ≠ a} ⟨v_b, B v_a⟩ v_b`. -/
theorem offDiagonalPartFamily_apply_self {v : Fin n → E} (hv : Orthonormal 𝕜 v)
    (B : E →L[𝕜] E) (a : Fin n) :
    offDiagonalPartFamily v B (v a) = ∑ b ∈ Finset.univ.erase a, ⟪v b, B (v a)⟫_𝕜 • v b := by
  have hshift (k : Fin n) : shiftPart v B k (v a) = ⟪v (a - k), B (v a)⟫_𝕜 • v (a - k) := by
    rw [shiftPart_apply]
    have hterm (b : Fin n) : (⟪v b, B (v (b + k))⟫_𝕜 * ⟪v (b + k), v a⟫_𝕜) • v b =
        if b = a - k then ⟪v (a - k), B (v a)⟫_𝕜 • v (a - k) else 0 := by
      rw [orthonormal_iff_ite.mp hv]
      by_cases hb : b = a - k
      · subst hb
        simp
      · have : b + k ≠ a := fun h => hb (eq_sub_of_add_eq h)
        simp [this, hb]
    simp_rw [hterm]
    simp
  rw [offDiagonalPartFamily, sum_apply]
  simp_rw [hshift]
  refine Finset.sum_nbij' (fun k => a - k) (fun b => a - b) ?_ ?_ ?_ ?_ ?_
  · intro k hk
    simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hk ⊢
    intro h
    exact hk (by simpa using (sub_eq_self.mp h))
  · intro b hb
    simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hb ⊢
    intro h
    exact hb (sub_eq_zero.mp h).symm
  · intro k _
    simp
  · intro b _
    simp
  · intro k _
    rfl

/-- **Eq. `low` up to `o` for every basis vector.** Let `P` be the orthogonal projection onto a
closed subspace `K` with orthonormal basis `v : Fin n → E`, so that every `u ∈ K` equals
`∑_b ⟨v_b, u⟩ v_b`. Then for every `M` and every `a`,
`‖M v_a - ⟨v_a, M v_a⟩ v_a‖ ≤ ‖(1 - P) M v_a‖ + ‖o‖`, where `o` is the off-diagonal part of
`P M P` in the basis. Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 476–491; the
first term is the one bounded by eq. `facld`
(`norm_sub_starProjection_apply_le_of_gaussianFilteredTerm`). -/
theorem norm_apply_sub_inner_smul_le_add_offDiagonalPartFamily [CompleteSpace E]
    (K : Submodule 𝕜 E) [K.HasOrthogonalProjection] {v : Fin n → E} (hv : Orthonormal 𝕜 v)
    (hvK : ∀ b, v b ∈ K) (hspan : ∀ u ∈ K, u = ∑ b, ⟪v b, u⟫_𝕜 • v b) (M : E →L[𝕜] E)
    (a : Fin n) :
    ‖M (v a) - ⟪v a, M (v a)⟫_𝕜 • v a‖ ≤
      ‖M (v a) - K.starProjection (M (v a))‖ +
        ‖offDiagonalPartFamily v (K.starProjection * M * K.starProjection)‖ := by
  set P := K.starProjection
  have hPv : P (v a) = v a := K.starProjection_eq_self_iff.mpr (hvK a)
  have hsym : ∀ x y, ⟪x, P y⟫_𝕜 = ⟪P x, y⟫_𝕜 := fun x y =>
    (K.starProjection_isSymmetric x y).symm
  have hsa (b : Fin n) : ⟪v b, P (M (v a))⟫_𝕜 = ⟪v b, M (v a)⟫_𝕜 := by
    have hPb : P (v b) = v b := K.starProjection_eq_self_iff.mpr (hvK b)
    rw [hsym, hPb]
  have hdecomp := hspan (P (M (v a))) (K.starProjection_apply_mem _)
  have hoff : offDiagonalPartFamily v (P * M * P) (v a) =
      P (M (v a)) - ⟪v a, M (v a)⟫_𝕜 • v a := by
    rw [offDiagonalPartFamily_apply_self hv]
    have hPMP (b : Fin n) : ⟪v b, (P * M * P) (v a)⟫_𝕜 = ⟪v b, P (M (v a))⟫_𝕜 := by
      simp [hPv]
    simp_rw [hPMP]
    conv_rhs => rw [hdecomp, ← Finset.add_sum_erase _ _ (Finset.mem_univ a), hsa a]
    abel
  have hsplit : M (v a) - ⟪v a, M (v a)⟫_𝕜 • v a =
      (M (v a) - P (M (v a))) + offDiagonalPartFamily v (P * M * P) (v a) := by
    rw [hoff]
    abel
  rw [hsplit]
  refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
  simpa [hv.1 a] using (offDiagonalPartFamily v (P * M * P)).le_opNorm (v a)

end TNLean.Lattice
