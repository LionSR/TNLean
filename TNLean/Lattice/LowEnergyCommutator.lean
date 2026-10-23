/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.GaussianFilteredTermLocalization

/-!
# Low-energy commutators of Gaussian-filtered terms

Let every eigenvalue of a Hermitian `H` equal the ground energy `E₀` or be at least
`E₀ + ΔE`, and let `P` be the orthogonal projection onto the ground eigenspace. For an
operator `W`, write `P W P` for its compression to the ground space and `W_tilde` for its
Gaussian-filtered version. This file proves Hastings' bounds on the commutators of such
compressions, which decide whether the compressed local terms can be diagonalized together
when the ground space is degenerate.

* `norm_groundCompression_commutator_le`: for all operators `W` and `B`,
  `‖[P W P, P B P]‖ ≤ ‖[W_tilde, B]‖ + 2 ‖W‖ ‖B‖ e^{-q/2}`. The proof uses
  `P W_tilde P = P W P` and the bounds `‖(1 - P) W_tilde P‖, ‖P W_tilde (1 - P)‖ ≤
  ‖W‖ e^{-q/2}`.
* `norm_commutator_gaussianFilteredTerm_le_of_disjoint`: on a finite graph, if `W` acts on `S`
  and `B` acts on a set disjoint from the sites within distance `l` of `S`, then `‖[W_tilde, B]‖`
  is at most `2 ‖B‖` times the localization bound of
  `norm_gaussianFilteredTerm_sub_siteExpectation_le_graphNeighborhood`.
* `norm_groundCompression_commutator_le_graphNeighborhood`: the two combined, so that the
  low-energy commutator of two separated local operators is small.
* `abs_sub_mul_norm_inner_le_norm_commutator`, `norm_inner_le_norm_commutator_div`: if `A` is
  self-adjoint with eigenvectors `v` and `w` of eigenvalues `r ≠ s`, then
  `‖⟪v, B w⟫‖ ≤ ‖[A, B]‖ ‖v‖ ‖w‖ / |r - s|`. With `A = P M_j P` and `B = P M_i P`, and `v`, `w`
  ground vectors, this bounds the off-diagonal matrix elements of `M_i` in a basis of the ground
  space that diagonalizes `M_j`.

**Local fix (the commutator with a separated operator, eq. `lc`):** the commutator
`[W_tilde, B]` is bounded through the partial trace of `W_tilde` onto the `l`-neighbourhood of
`S`, which commutes with `B`, rather than by applying the Lieb–Robinson bound site by site to
the `N_M` sites of `B`. The term `N_M g(c₁ l, l)` of eq. `lc` is therefore replaced by the
localization term of eq. `apb` as formalized, and the bound does not depend on the size of the
support of `B`. Documented in `docs/paper-gaps/hastings05_filtered_term_approximation.tex`.

The operators `W` and `B` are arbitrary operators acting on the given sets; in the source they
are the approximations `M_i` and `M_j`, and the filter on `M_i` uses a parameter `q` chosen
afresh (line 1551). The statements keep `q` and the splitting time `T` free; the source's
eq. `blecm` is the case `T = c₁ l`, `q = c₁ l ΔE`.

Not formalized here: the translation-invariant case (lines 1603–1642), the example of
lines 1655–1676, and the summed bound `∑ᵢ o(i) ≤ O(J² / (c₁ l ΔE δλ_j))` of eq. `oibu`, which
the source states only to order of magnitude. The basis construction for more than two ground
states (lines 1700–1708) is only sketched in the source; the pairwise matrix-element bound
proved here is its basic step.

## References

Hastings, *Solving Gapped Hamiltonians Locally*, arXiv:cond-mat/0508554v3, `proj3new.tex`:
the degenerate ground space at lines 395–491, eq. `lc` (lines 1548–1561), eq. `blecm`
(lines 1562–1601), and the off-diagonal elements `o(i)` before eq. `oibu` (lines 1678–1708).
-/

open GaussianFilter Matrix QuantumCircuit
open scoped Matrix.Norms.L2Operator InnerProductSpace

namespace TNLean.Lattice

section Ground

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The compression `P W P` of an operator `W` to the ground eigenspace of `H` at energy `E₀`,
as an operator on the Euclidean space, where `P` is the orthogonal projection onto that
eigenspace. This is `P_low W P_low` in Hastings, arXiv:cond-mat/0508554v3, lines 1562–1601. -/
noncomputable def groundCompression (H : Matrix n n ℂ) (E₀ : ℝ) (W : Matrix n n ℂ) :
    EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n :=
  (groundEigenspace H E₀).starProjection * toEuclideanCLM (n := n) (𝕜 := ℂ) W *
    (groundEigenspace H E₀).starProjection

/-- The filtered operator and `W` have the same compression to the ground space:
`P W_tilde P = P W P`. Hastings, arXiv:cond-mat/0508554v3, line 1562. -/
theorem groundCompression_gaussianFilteredTerm {q ΔE : ℝ} (hq : 0 ≤ q) {H : Matrix n n ℂ}
    (hH : H.IsHermitian) (E₀ : ℝ) (W : Matrix n n ℂ) :
    groundCompression H E₀ (gaussianFilteredTerm q ΔE H W) = groundCompression H E₀ W := by
  set K := groundEigenspace H E₀
  ext1 x
  refine ext_inner_left ℂ fun y => ?_
  simp only [groundCompression, mul_apply_eq_comp]
  rw [← K.inner_starProjection_left_eq_right, ← K.inner_starProjection_left_eq_right]
  exact inner_gaussianFilteredTerm_ground hq hH W
    (mem_groundEigenspace_iff.mp (K.starProjection_apply_mem y))
    (mem_groundEigenspace_iff.mp (K.starProjection_apply_mem x))

/-- The filtered operator maps the ground space nearly into itself:
`‖(1 - P) W_tilde P‖ ≤ ‖W‖ e^{-q/2}`. Hastings, arXiv:cond-mat/0508554v3, line 1585,
following eq. `gs`. -/
theorem norm_one_sub_starProjection_mul_gaussianFilteredTerm_mul_le {q ΔE : ℝ} (hq : 0 ≤ q)
    (hΔE : 0 < ΔE) {H : Matrix n n ℂ} (hH : H.IsHermitian) {E₀ : ℝ}
    (hgap : ∀ k, hH.eigenvalues k = E₀ ∨ E₀ + ΔE ≤ hH.eigenvalues k) (W : Matrix n n ℂ) :
    ‖(1 - (groundEigenspace H E₀).starProjection) *
        toEuclideanCLM (n := n) (𝕜 := ℂ) (gaussianFilteredTerm q ΔE H W) *
        (groundEigenspace H E₀).starProjection‖ ≤ ‖W‖ * Real.exp (-q / 2) := by
  set K := groundEigenspace H E₀
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun x => ?_
  simp only [mul_apply_eq_comp, _root_.sub_apply, one_apply_eq_self]
  refine (norm_sub_starProjection_gaussianFilteredTerm_le hq hΔE hH hgap W
    (K.starProjection_apply_mem x)).trans ?_
  gcongr
  exact K.norm_starProjection_apply_le x

/-- The adjoint statement: `‖P W_tilde (1 - P)‖ ≤ ‖W‖ e^{-q/2}`, since the adjoint of
`W_tilde` is the filtered version of `Wᴴ`. Hastings, arXiv:cond-mat/0508554v3, line 1586. -/
theorem norm_starProjection_mul_gaussianFilteredTerm_mul_one_sub_le {q ΔE : ℝ} (hq : 0 ≤ q)
    (hΔE : 0 < ΔE) {H : Matrix n n ℂ} (hH : H.IsHermitian) {E₀ : ℝ}
    (hgap : ∀ k, hH.eigenvalues k = E₀ ∨ E₀ + ΔE ≤ hH.eigenvalues k) (W : Matrix n n ℂ) :
    ‖(groundEigenspace H E₀).starProjection *
        toEuclideanCLM (n := n) (𝕜 := ℂ) (gaussianFilteredTerm q ΔE H W) *
        (1 - (groundEigenspace H E₀).starProjection)‖ ≤ ‖W‖ * Real.exp (-q / 2) := by
  set P := (groundEigenspace H E₀).starProjection
  have hP : star P = P := (isSelfAdjoint_starProjection _).star_eq
  have hstar : star (toEuclideanCLM (n := n) (𝕜 := ℂ) (gaussianFilteredTerm q ΔE H W)) =
      toEuclideanCLM (n := n) (𝕜 := ℂ) (gaussianFilteredTerm q ΔE H Wᴴ) := by
    rw [← map_star, star_eq_conjTranspose]
    exact congrArg _ (gaussianIntertwiner_conjTranspose _ hH hH W)
  have h := norm_one_sub_starProjection_mul_gaussianFilteredTerm_mul_le hq hΔE hH hgap Wᴴ
  rw [l2_opNorm_conjTranspose, ← hstar] at h
  rw [← norm_star]
  simpa only [star_mul, star_sub, star_one, hP, mul_assoc] using h

/-- **The low-energy commutator, eq. `blecm`.** Let every eigenvalue of `H` equal `E₀` or be at
least `E₀ + ΔE`, with `ΔE > 0` and `q ≥ 0`. For all operators `W` and `B`, the compressions to
the ground space satisfy `‖[P W P, P B P]‖ ≤ ‖[W_tilde, B]‖ + 2 ‖W‖ ‖B‖ e^{-q/2}`.
Hastings, arXiv:cond-mat/0508554v3, lines 1562–1593, with `W = M_i` and `B = M_j`: the
compression of `W` equals that of `W_tilde`, and the triangle inequality after line 1566
together with eq. `gs` bounds the difference. -/
theorem norm_groundCompression_commutator_le {q ΔE : ℝ} (hq : 0 ≤ q) (hΔE : 0 < ΔE)
    {H : Matrix n n ℂ} (hH : H.IsHermitian) {E₀ : ℝ}
    (hgap : ∀ k, hH.eigenvalues k = E₀ ∨ E₀ + ΔE ≤ hH.eigenvalues k) (W B : Matrix n n ℂ) :
    ‖groundCompression H E₀ W * groundCompression H E₀ B -
        groundCompression H E₀ B * groundCompression H E₀ W‖ ≤
      ‖gaussianFilteredTerm q ΔE H W * B - B * gaussianFilteredTerm q ΔE H W‖ +
        2 * ‖W‖ * ‖B‖ * Real.exp (-q / 2) := by
  have hlow := norm_one_sub_starProjection_mul_gaussianFilteredTerm_mul_le hq hΔE hH hgap W
  have hhigh := norm_starProjection_mul_gaussianFilteredTerm_mul_one_sub_le hq hΔE hH hgap W
  rw [← groundCompression_gaussianFilteredTerm (ΔE := ΔE) hq hH E₀ W]
  set P := (groundEigenspace H E₀).starProjection
  set A := toEuclideanCLM (n := n) (𝕜 := ℂ) (gaussianFilteredTerm q ΔE H W)
  set B' := toEuclideanCLM (n := n) (𝕜 := ℂ) B
  have hPP : P * P = P := (groundEigenspace H E₀).isIdempotentElem_starProjection.eq
  have hP : ‖P‖ ≤ 1 := (groundEigenspace H E₀).starProjection_norm_le
  have hB : ‖B'‖ = ‖B‖ := l2_opNorm_toEuclideanCLM B
  have hWe : 0 ≤ ‖W‖ * Real.exp (-q / 2) := mul_nonneg (norm_nonneg _) (Real.exp_pos _).le
  have hAB : ‖A * B' - B' * A‖ =
      ‖gaussianFilteredTerm q ΔE H W * B - B * gaussianFilteredTerm q ΔE H W‖ := by
    rw [← l2_opNorm_toEuclideanCLM, map_sub, map_mul, map_mul]
  have hsplit : P * A * P * (P * B' * P) - P * B' * P * (P * A * P) =
      P * (A * B' - B' * A) * P - P * A * (1 - P) * (B' * P) +
        P * B' * ((1 - P) * A * P) := by
    have h1 : P * A * P * (P * B' * P) = P * A * (P * P) * B' * P := by simp only [mul_assoc]
    have h2 : P * B' * P * (P * A * P) = P * B' * (P * P) * A * P := by simp only [mul_assoc]
    rw [h1, h2, hPP]
    noncomm_ring
  have hC : ‖P * (A * B' - B' * A) * P‖ ≤ ‖A * B' - B' * A‖ := by
    calc ‖P * (A * B' - B' * A) * P‖ ≤ ‖P‖ * ‖A * B' - B' * A‖ * ‖P‖ := norm_mul₃_le
      _ ≤ 1 * ‖A * B' - B' * A‖ * 1 := by gcongr
      _ = _ := by ring
  have hD : ‖P * A * (1 - P) * (B' * P)‖ ≤ ‖W‖ * Real.exp (-q / 2) * ‖B‖ := by
    calc ‖P * A * (1 - P) * (B' * P)‖ ≤ ‖P * A * (1 - P)‖ * (‖B'‖ * ‖P‖) :=
          (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ ‖W‖ * Real.exp (-q / 2) * (‖B‖ * 1) := by
          rw [hB]
          exact mul_le_mul hhigh (mul_le_mul_of_nonneg_left hP (norm_nonneg _))
            (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hWe
      _ = _ := by rw [mul_one]
  have hE : ‖P * B' * ((1 - P) * A * P)‖ ≤ ‖W‖ * Real.exp (-q / 2) * ‖B‖ := by
    calc ‖P * B' * ((1 - P) * A * P)‖ ≤ ‖P‖ * ‖B'‖ * ‖(1 - P) * A * P‖ := norm_mul₃_le
      _ ≤ 1 * ‖B‖ * (‖W‖ * Real.exp (-q / 2)) := by
          rw [hB]
          exact mul_le_mul (mul_le_mul_of_nonneg_right hP (norm_nonneg _)) hlow (norm_nonneg _)
            (mul_nonneg zero_le_one (norm_nonneg _))
      _ = _ := by ring
  simp only [groundCompression]
  rw [hsplit, ← hAB]
  calc _ ≤ ‖P * (A * B' - B' * A) * P - P * A * (1 - P) * (B' * P)‖ +
        ‖P * B' * ((1 - P) * A * P)‖ := norm_add_le _ _
    _ ≤ ‖P * (A * B' - B' * A) * P‖ + ‖P * A * (1 - P) * (B' * P)‖ +
        ‖P * B' * ((1 - P) * A * P)‖ := by gcongr; exact norm_sub_le _ _
    _ ≤ _ := by linarith

end Ground

section Graph

variable {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] {κ : Type*} [Fintype κ]
  (G : SimpleGraph ι) (X : κ → Finset ι) (a : κ → ι) (ha : ∀ k, a k ∈ X k)
  (h : κ → Matrix (ι → Fin d) (ι → Fin d) ℂ) (hHerm : ∀ k, (h k).IsHermitian)
  (hSupport : ∀ k, h k ∈ supportedOperators d (X k : Set ι))
  (R : ℕ) (hDiam : ∀ k, ∀ x ∈ X k, ∀ z ∈ X k, G.edist x z ≤ R)
  (vR : ℕ) (hCard : ∀ k, (X k).card ≤ vR)
  (b₀ : ℝ) (hBudget : ∀ x, ∑ j ∈ Finset.univ.filter (fun j => x ∈ X j), ‖h j‖ ≤ b₀)

include ha hHerm hSupport hDiam hCard hBudget

/-- **The commutator of a filtered term with a separated operator, eq. `lc`.** Let `W` act on
`S`, and let `B` act on a set `Y` disjoint from the set of sites within graph distance `l` of
`S`. Then `‖[W_tilde, B]‖` is at most `2 ‖B‖` times the bound of
`norm_gaussianFilteredTerm_sub_siteExpectation_le_graphNeighborhood`, for every `T ≥ 0`: the
partial trace of `W_tilde` onto that neighbourhood commutes with `B`. Hastings,
arXiv:cond-mat/0508554v3, eq. `lc` (lines 1548–1561), with the localization term in place of
`N_M g(c₁ l, l)`. -/
theorem norm_commutator_gaussianFilteredTerm_le_of_disjoint [NeZero d] (Kg : ℝ) (kg : ℕ)
    (hGrowth : ∀ x (r : ℕ),
      ((Finset.univ.filter fun y => G.edist x y = r).card : ℝ) ≤ Kg * ((r : ℝ) + 1) ^ kg)
    {q ΔE : ℝ} (hq : 0 ≤ q) (S : Finset ι) {W B : Matrix (ι → Fin d) (ι → Fin d) ℂ}
    (hW : W ∈ supportedOperators d (S : Set ι)) (l : ℕ) (Y : Set ι)
    (hY : Disjoint ((S.biUnion fun x => graphBall G x l : Finset ι) : Set ι) Y)
    (hB : B ∈ supportedOperators d Y) {T : ℝ} (hT : 0 ≤ T) :
    ‖gaussianFilteredTerm q ΔE (∑ k, h k) W * B - B * gaussianFilteredTerm q ΔE (∑ k, h k) W‖ ≤
      2 * ‖B‖ *
        ((2 + 4 * |b₀| * Real.exp (2 * R)) * (S.card : ℝ) ^ 2 * ‖W‖ * Kg *
            (2 ^ kg * kg.factorial * Real.exp (1 / 2) / (1 - Real.exp (-(1 / 2)))) *
            Real.exp ((2 * vR * |b₀| * Real.exp (2 * R) + 1) * T - l / 2) +
          2 * ‖W‖ * Real.exp (-(T * ΔE) ^ 2 / (2 * q))) := by
  set F := gaussianFilteredTerm q ΔE (∑ k, h k) W
  set M := siteExpectation d (S.biUnion fun x => graphBall G x l) F
  have hloc := norm_gaussianFilteredTerm_sub_siteExpectation_le_graphNeighborhood G X a ha h
    hHerm hSupport R hDiam vR hCard b₀ hBudget Kg kg hGrowth (ΔE := ΔE) hq S hW l hT
  have hcomm : Commute M B :=
    commute_of_mem_supportedOperators hY (siteExpectation_mem_supportedOperators _ _) hB
  have hsplit : F * B - B * F = (F - M) * B - B * (F - M) := by
    rw [sub_mul, mul_sub, hcomm.eq]; abel
  rw [hsplit]
  calc _ ≤ ‖(F - M) * B‖ + ‖B * (F - M)‖ := norm_sub_le _ _
    _ ≤ ‖F - M‖ * ‖B‖ + ‖B‖ * ‖F - M‖ := add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ = 2 * ‖B‖ * ‖F - M‖ := by ring
    _ ≤ _ := by gcongr

/-- **The low-energy commutator of separated operators, eq. `blecm` on a finite graph.** Let
every eigenvalue of `H = ∑ₖ hₖ` equal `E₀` or be at least `E₀ + ΔE`, let `W` act on `S`, and
let `B` act on a set disjoint from the sites within graph distance `l` of `S`. Then the
compressions to the ground space satisfy
`‖[P W P, P B P]‖ ≤ 2 ‖B‖ (C' |S|² ‖W‖ e^{vT - l/2} + 2 ‖W‖ e^{-(TΔE)²/(2q)}) +
2 ‖W‖ ‖B‖ e^{-q/2}` for all `q ≥ 0` and `T ≥ 0`, with the constants of
`norm_gaussianFilteredTerm_sub_siteExpectation_le_graphNeighborhood`. Hastings,
arXiv:cond-mat/0508554v3, eq. `blecm` (lines 1562–1601), with `W = M_i` and `B = M_j`; the
source takes `T = c₁ l` and `q = c₁ l ΔE`. -/
theorem norm_groundCompression_commutator_le_graphNeighborhood [NeZero d] (Kg : ℝ) (kg : ℕ)
    (hGrowth : ∀ x (r : ℕ),
      ((Finset.univ.filter fun y => G.edist x y = r).card : ℝ) ≤ Kg * ((r : ℝ) + 1) ^ kg)
    {q ΔE : ℝ} (hq : 0 ≤ q) (hΔE : 0 < ΔE) (hH : (∑ k, h k).IsHermitian) {E₀ : ℝ}
    (hgap : ∀ k, hH.eigenvalues k = E₀ ∨ E₀ + ΔE ≤ hH.eigenvalues k)
    (S : Finset ι) {W B : Matrix (ι → Fin d) (ι → Fin d) ℂ}
    (hW : W ∈ supportedOperators d (S : Set ι)) (l : ℕ) (Y : Set ι)
    (hY : Disjoint ((S.biUnion fun x => graphBall G x l : Finset ι) : Set ι) Y)
    (hB : B ∈ supportedOperators d Y) {T : ℝ} (hT : 0 ≤ T) :
    ‖groundCompression (∑ k, h k) E₀ W * groundCompression (∑ k, h k) E₀ B -
        groundCompression (∑ k, h k) E₀ B * groundCompression (∑ k, h k) E₀ W‖ ≤
      2 * ‖B‖ *
          ((2 + 4 * |b₀| * Real.exp (2 * R)) * (S.card : ℝ) ^ 2 * ‖W‖ * Kg *
              (2 ^ kg * kg.factorial * Real.exp (1 / 2) / (1 - Real.exp (-(1 / 2)))) *
              Real.exp ((2 * vR * |b₀| * Real.exp (2 * R) + 1) * T - l / 2) +
            2 * ‖W‖ * Real.exp (-(T * ΔE) ^ 2 / (2 * q))) +
        2 * ‖W‖ * ‖B‖ * Real.exp (-q / 2) :=
  (norm_groundCompression_commutator_le hq hΔE hH hgap W B).trans <| add_le_add_left
    (norm_commutator_gaussianFilteredTerm_le_of_disjoint G X a ha h hHerm hSupport R hDiam vR
      hCard b₀ hBudget Kg kg hGrowth hq S hW l Y hY hB hT) _

end Graph

section OffDiagonal

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]

/-- **Matrix elements between eigenvectors from a commutator.** If `A` is self-adjoint with
`A v = r v` and `A w = s w`, then `|r - s| ‖⟪v, B w⟫‖ ≤ ‖[A, B]‖ ‖v‖ ‖w‖` for every `B`, since
`⟪v, [A, B] w⟫ = (r - s) ⟪v, B w⟫`. Hastings, arXiv:cond-mat/0508554v3, lines 1678–1690. -/
theorem abs_sub_mul_norm_inner_le_norm_commutator {A : E →L[𝕜] E} (hA : IsSelfAdjoint A)
    (B : E →L[𝕜] E) {v w : E} {r s : ℝ} (hv : A v = (r : 𝕜) • v) (hw : A w = (s : 𝕜) • w) :
    |r - s| * ‖⟪v, B w⟫_𝕜‖ ≤ ‖A * B - B * A‖ * ‖v‖ * ‖w‖ := by
  have hkey : ⟪v, (A * B - B * A) w⟫_𝕜 = ((r - s : ℝ) : 𝕜) * ⟪v, B w⟫_𝕜 := by
    have hsymm : ⟪v, A (B w)⟫_𝕜 = ⟪A v, B w⟫_𝕜 := (hA.isSymmetric v (B w)).symm
    simp only [_root_.sub_apply, mul_apply_eq_comp, inner_sub_right,
      hsymm, hv, hw, map_smul, inner_smul_left, inner_smul_right, RCLike.conj_ofReal]
    push_cast
    ring
  calc |r - s| * ‖⟪v, B w⟫_𝕜‖ = ‖⟪v, (A * B - B * A) w⟫_𝕜‖ := by
        rw [hkey, norm_mul, RCLike.norm_ofReal]
    _ ≤ ‖v‖ * ‖(A * B - B * A) w‖ := norm_inner_le_norm _ _
    _ ≤ ‖v‖ * (‖A * B - B * A‖ * ‖w‖) := by gcongr; exact (A * B - B * A).le_opNorm w
    _ = _ := by ring

/-- **Off-diagonal elements in an eigenbasis.** If `A` is self-adjoint with `A v = r v`,
`A w = s w` and `r ≠ s`, then `‖⟪v, B w⟫‖ ≤ ‖[A, B]‖ ‖v‖ ‖w‖ / |r - s|` for every `B`. With
`A = P M_j P`, `B = P M_i P` and unit ground vectors `v`, `w`, this is Hastings' bound
`o(i) ≤ ‖[P M_i P, P M_j P]‖ / δλ_j` on the off-diagonal elements of `M_i` in a basis of the
ground space diagonalizing `M_j`, arXiv:cond-mat/0508554v3, lines 1678–1690. -/
theorem norm_inner_le_norm_commutator_div {A : E →L[𝕜] E} (hA : IsSelfAdjoint A)
    (B : E →L[𝕜] E) {v w : E} {r s : ℝ} (hv : A v = (r : 𝕜) • v) (hw : A w = (s : 𝕜) • w)
    (hrs : r ≠ s) :
    ‖⟪v, B w⟫_𝕜‖ ≤ ‖A * B - B * A‖ * ‖v‖ * ‖w‖ / |r - s| := by
  rw [le_div_iff₀ (abs_pos.mpr (sub_ne_zero.mpr hrs)), mul_comm]
  exact abs_sub_mul_norm_inner_le_norm_commutator hA B hv hw

end OffDiagonal

end TNLean.Lattice
