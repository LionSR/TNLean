/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Circuit.LiebRobinson.GraphLocalization
import TNLean.Circuit.SiteExpectationOrder
import TNLean.Lattice.GaussianFilteredGround
import TNLean.Lattice.GaussianFilteredLocality

/-!
# Locality of Gaussian-filtered terms on a finite graph

Let `H = ∑ₖ hₖ` be a local Hamiltonian on a finite graph with local dimension `d`: each term
`hₖ` is Hermitian and acts on a set `Xₖ` of diameter at most `R` and at most `v_R` sites, and
the terms containing any one site have norms summing to at most `b₀`. For an operator `W`
acting on a set `S`, let `W_tilde` be its Gaussian-filtered version
`(ΔE / √(2πq)) ∫ e^{iHt} W e^{-iHt} e^{-(tΔE)²/(2q)} dt`. This file proves the locality of
`W_tilde` that Hastings derives from the Lieb–Robinson bound, and its consequences.

* `norm_commutator_gaussianFilteredTerm_le_graphDistance`: for `B` acting on one site `y` at
  graph distance at least `l` from `S`, `‖[W_tilde, B]‖` is at most the Lieb–Robinson term
  `C |S| ‖W‖ ‖B‖ e^{vT - μl}` plus `2 ‖W‖ ‖B‖ e^{-(TΔE)²/(2q)}`, for every `T ≥ 0`.
* `exists_local_approx_gaussianFilteredTerm`: an operator `M` acting on the sites within
  distance `l` of `S`, with `‖M‖ ≤ ‖W‖`, Hermitian when `W` is, and `‖W_tilde - M‖` bounded
  by the localization term `C' |S|² ‖W‖ e^{vT - l/2}` plus `2 ‖W‖ e^{-(TΔE)²/(2q)}`.
* `norm_sub_starProjection_apply_le_of_gaussianFilteredTerm`: the excited component of
  `M ψ`, for a ground vector `ψ`, is at most `(‖W‖ e^{-q/2} + ‖W_tilde - M‖) ‖ψ‖`.
* `norm_apply_sub_inner_smul_le_of_gaussianFilteredTerm`: for a unique gapped ground state
  `Ω`, `‖M Ω - ⟨Ω, M Ω⟩ Ω‖ ≤ ‖W‖ e^{-q/2} + ‖W_tilde - M‖`.
* `norm_sum_sub_le_of_sum_eq`: if the terms `Wᵢ` sum to `H`, then any operators `Mᵢ` satisfy
  `‖∑ᵢ Mᵢ - H‖ ≤ ∑ᵢ ‖W_tildeᵢ - Mᵢ‖`.

The approximation `M` is the normalized partial trace of `W_tilde` onto the `l`-neighbourhood
of `S`. The source builds its `M_i` instead by evolving `H_i` under the terms within distance
`l_proj - R` of `i` (eqs. `mid`, `odef`, `hpdef`). What the later argument uses is the
support of `M_i`, the bound `‖M_i‖ ≤ J`, and eq. `apb`, and the partial trace has all three.
The constants of the Lieb–Robinson bound are those of
`QuantumCircuit.norm_heisenberg_commutator_le_graphDistance_finset` and
`QuantumCircuit.norm_heisenberg_sub_siteExpectation_graphNeighborhood_le`. The source's
`g(c₁ l, l)` and `N(l_proj) g(c₁ l_proj, l_proj)` are these terms at `T = c₁ l`, and its
`O(e^{-l_proj/l_fac})` in eq. `facld` is the sum of the three terms at `q = c₁ l_proj ΔE`;
the statements here keep `q` and `T` free.

## References

Hastings, *Solving Gapped Hamiltonians Locally*, arXiv:cond-mat/0508554v3, `proj3new.tex`:
the setting at lines 169–190, eq. `lbnd` (lines 266–283, proved at lines 1419–1456), the
approximation `M_i` with eqs. `mid`, `odef`, `hpdef` and `apb` (lines 285–320, proved at
lines 1458–1533), eq. `facld` (lines 322–348), the sum `M = ∑ᵢ M_i` at lines 359–374, and
the unique ground state at lines 375–387. The overlap of the ground states of `M` and `H`
(lines 362–367) is stated there only to order of magnitude and is not formalized here.
The source writes `exp[-(tΔE)²/2]` in eq. `mid`; the exponent of eq. `thd`, `-(tΔE)²/(2q)`,
is meant.
-/

open GaussianFilter Matrix QuantumCircuit
open scoped Matrix.Norms.L2Operator InnerProductSpace

namespace TNLean.Lattice

/-- A filtered Hermitian operator is Hermitian. -/
theorem isHermitian_gaussianFilteredTerm {n : Type*} [Fintype n] [DecidableEq n] (q ΔE : ℝ)
    {H W : Matrix n n ℂ} (hH : H.IsHermitian) (hW : W.IsHermitian) :
    (gaussianFilteredTerm q ΔE H W).IsHermitian := by
  change (gaussianIntertwiner _ H H W)ᴴ = gaussianIntertwiner _ H H W
  rw [gaussianIntertwiner_conjTranspose _ hH hH W, hW.eq]

section Graph

variable {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] {κ : Type*} [Fintype κ]
  (G : SimpleGraph ι) (X : κ → Finset ι) (a : κ → ι) (ha : ∀ k, a k ∈ X k)
  (h : κ → Matrix (ι → Fin d) (ι → Fin d) ℂ) (hHerm : ∀ k, (h k).IsHermitian)
  (hSupport : ∀ k, h k ∈ supportedOperators d (X k : Set ι))
  (R : ℕ) (hDiam : ∀ k, ∀ x ∈ X k, ∀ z ∈ X k, G.edist x z ≤ R)
  (vR : ℕ) (hCard : ∀ k, (X k).card ≤ vR)
  (b₀ : ℝ) (hBudget : ∀ x, ∑ j ∈ Finset.univ.filter (fun j => x ∈ X j), ‖h j‖ ≤ b₀)

include ha hHerm hSupport hDiam hCard hBudget

/-- **Locality of a filtered term on a finite graph.** Let `W` act on `S` and `B` on one site
`y` at graph distance at least `l` from every site of `S`. For every `μ ≥ 0` and `T ≥ 0`,
`‖[W_tilde, B]‖ ≤ C |S| ‖W‖ ‖B‖ e^{vT - μl} + 2 ‖W‖ ‖B‖ e^{-(TΔE)²/(2q)}`, with
`C = 2 + 4 |b₀| e^{2μR}` and `v = 2 v_R |b₀| e^{2μR} + 1`.
Hastings, arXiv:cond-mat/0508554v3, eq. `lbnd` (lines 266–283), proved at lines 1419–1456:
the filter integral is split at `|t| = T`, the Lieb–Robinson bound controls `|t| ≤ T`, and the
Gaussian tail controls the rest. -/
theorem norm_commutator_gaussianFilteredTerm_le_graphDistance {q ΔE : ℝ} (hq : 0 ≤ q)
    (S : Finset ι) {W B : Matrix (ι → Fin d) (ι → Fin d) ℂ}
    (hW : W ∈ supportedOperators d (S : Set ι)) (y : ι)
    (hB : B ∈ supportedOperators d ({y} : Set ι)) (μ : ℝ) (hμ : 0 ≤ μ) (l : ℕ)
    (hl : ∀ x ∈ S, (l : ℕ∞) ≤ G.edist x y) {T : ℝ} (hT : 0 ≤ T) :
    ‖gaussianFilteredTerm q ΔE (∑ k, h k) W * B - B * gaussianFilteredTerm q ΔE (∑ k, h k) W‖ ≤
      (2 + 4 * |b₀| * Real.exp (2 * μ * R)) * (S.card : ℝ) * ‖W‖ * ‖B‖ *
          Real.exp ((2 * vR * |b₀| * Real.exp (2 * μ * R) + 1) * T - μ * l) +
        2 * ‖W‖ * ‖B‖ * Real.exp (-(T * ΔE) ^ 2 / (2 * q)) := by
  have hH : (∑ k, h k).IsHermitian :=
    isSelfAdjoint_sum Finset.univ fun j _ => (hHerm j).isSelfAdjoint
  refine norm_commutator_gaussianFilteredTerm_le hq hH W B hT (by positivity) fun t ht => ?_
  have hLR := norm_heisenberg_commutator_le_graphDistance_finset G X a ha h hHerm hSupport R
    hDiam vR hCard b₀ hBudget S hW y hB μ hμ l hl t
  refine hLR.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity))
  have hv : 0 ≤ 2 * vR * |b₀| * Real.exp (2 * μ * R) + 1 := by positivity
  have htT : |t| ≤ T := abs_le.mpr ht
  nlinarith

/-- **The localized filtered term on a finite graph.** Let `W` act on `S`, and let `K` be the
set of sites within graph distance `l` of `S`. The normalized partial trace of `W_tilde` onto
`K` approximates `W_tilde` within
`C' |S|² ‖W‖ e^{vT - l/2} + 2 ‖W‖ e^{-(TΔE)²/(2q)}` for every `T ≥ 0`, where
`C' = (2 + 4 |b₀| e^{2R}) K_g 2^{k_g} k_g! e^{1/2} / (1 - e^{-1/2})` and
`v = 2 v_R |b₀| e^{2R} + 1`, when every sphere of radius `r` has at most `K_g (r + 1)^{k_g}`
sites. Hastings, arXiv:cond-mat/0508554v3, eq. `apb` (lines 300–320), proved at
lines 1458–1533, with the partial trace in place of the truncated dynamics of eq. `mid`. -/
theorem norm_gaussianFilteredTerm_sub_siteExpectation_le_graphNeighborhood [NeZero d]
    (Kg : ℝ) (kg : ℕ)
    (hGrowth : ∀ x (r : ℕ),
      ((Finset.univ.filter fun y => G.edist x y = r).card : ℝ) ≤ Kg * ((r : ℝ) + 1) ^ kg)
    {q ΔE : ℝ} (hq : 0 ≤ q) (S : Finset ι) {W : Matrix (ι → Fin d) (ι → Fin d) ℂ}
    (hW : W ∈ supportedOperators d (S : Set ι)) (l : ℕ) {T : ℝ} (hT : 0 ≤ T) :
    ‖gaussianFilteredTerm q ΔE (∑ k, h k) W -
        siteExpectation d (S.biUnion fun x => graphBall G x l)
          (gaussianFilteredTerm q ΔE (∑ k, h k) W)‖ ≤
      (2 + 4 * |b₀| * Real.exp (2 * R)) * (S.card : ℝ) ^ 2 * ‖W‖ * Kg *
          (2 ^ kg * kg.factorial * Real.exp (1 / 2) / (1 - Real.exp (-(1 / 2)))) *
          Real.exp ((2 * vR * |b₀| * Real.exp (2 * R) + 1) * T - l / 2) +
        2 * ‖W‖ * Real.exp (-(T * ΔE) ^ 2 / (2 * q)) := by
  have hH : (∑ k, h k).IsHermitian :=
    isSelfAdjoint_sum Finset.univ fun j _ => (hHerm j).isSelfAdjoint
  set v : ℝ := 2 * vR * |b₀| * Real.exp (2 * R) + 1 with hv_def
  set P : ℝ := (2 + 4 * |b₀| * Real.exp (2 * R)) * (S.card : ℝ) ^ 2 * ‖W‖ * Kg *
    (2 ^ kg * kg.factorial * Real.exp (1 / 2) / (1 - Real.exp (-(1 / 2)))) with hP_def
  have hden : 0 < 1 - Real.exp (-(1 / 2) : ℝ) :=
    sub_pos.mpr (Real.exp_lt_one_iff.mpr (by norm_num))
  have hP : 0 ≤ P := by
    rcases S.eq_empty_or_nonempty with hS | ⟨x, -⟩
    · simp [hP_def, hS]
    · have hKg : 0 ≤ Kg := by
        have := hGrowth x 0
        simp only [Nat.cast_zero, zero_add, one_pow, mul_one] at this
        exact (Nat.cast_nonneg _).trans this
      positivity
  have hv : 0 ≤ v := by positivity
  refine norm_sub_siteExpectation_gaussianFilteredTerm_le hq hH W _ hT (by positivity)
    fun t ht => ?_
  have hLR := norm_heisenberg_sub_siteExpectation_graphNeighborhood_le G X a ha h hHerm
    hSupport R hDiam vR hCard b₀ hBudget Kg kg hGrowth S hW l t
  refine hLR.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hP)
  have htT : |t| ≤ T := abs_le.mpr ht
  nlinarith

/-- **The approximation `M` of a filtered term on a finite graph.** Let `W` act on `S`, and let
`K` be the set of sites within graph distance `l` of `S`. There is an operator `M` acting on
`K` with `‖M‖ ≤ ‖W‖`, Hermitian when `W` is, and with `‖W_tilde - M‖` at most the bound of
`norm_gaussianFilteredTerm_sub_siteExpectation_le_graphNeighborhood`. With `W = H_i` and
`‖H_i‖ ≤ J`, these are the properties of `M_i` in Hastings, arXiv:cond-mat/0508554v3,
lines 285–320: `M_i` acts within distance `l_proj` of `i`, `‖M_i‖ ≤ J`, and eq. `apb`. -/
theorem exists_local_approx_gaussianFilteredTerm [NeZero d] (Kg : ℝ) (kg : ℕ)
    (hGrowth : ∀ x (r : ℕ),
      ((Finset.univ.filter fun y => G.edist x y = r).card : ℝ) ≤ Kg * ((r : ℝ) + 1) ^ kg)
    {q ΔE : ℝ} (hq : 0 ≤ q) (S : Finset ι) {W : Matrix (ι → Fin d) (ι → Fin d) ℂ}
    (hW : W ∈ supportedOperators d (S : Set ι)) (l : ℕ) {T : ℝ} (hT : 0 ≤ T) :
    ∃ M : Matrix (ι → Fin d) (ι → Fin d) ℂ,
      M ∈ supportedOperators d ((S.biUnion fun x => graphBall G x l : Finset ι) : Set ι) ∧
      ‖M‖ ≤ ‖W‖ ∧ (W.IsHermitian → M.IsHermitian) ∧
      ‖gaussianFilteredTerm q ΔE (∑ k, h k) W - M‖ ≤
        (2 + 4 * |b₀| * Real.exp (2 * R)) * (S.card : ℝ) ^ 2 * ‖W‖ * Kg *
            (2 ^ kg * kg.factorial * Real.exp (1 / 2) / (1 - Real.exp (-(1 / 2)))) *
            Real.exp ((2 * vR * |b₀| * Real.exp (2 * R) + 1) * T - l / 2) +
          2 * ‖W‖ * Real.exp (-(T * ΔE) ^ 2 / (2 * q)) := by
  have hH : (∑ k, h k).IsHermitian :=
    isSelfAdjoint_sum Finset.univ fun j _ => (hHerm j).isSelfAdjoint
  exact ⟨_, siteExpectation_mem_supportedOperators _ _,
    (norm_siteExpectation_le _ _).trans (norm_gaussianFilteredTerm_le q ΔE hH W),
    fun hW' => isHermitian_siteExpectation _ (isHermitian_gaussianFilteredTerm q ΔE hH hW'),
    norm_gaussianFilteredTerm_sub_siteExpectation_le_graphNeighborhood G X a ha h hHerm
      hSupport R hDiam vR hCard b₀ hBudget Kg kg hGrowth hq S hW l hT⟩

end Graph

section Ground

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Excited component of an approximation of a filtered term.** Let every eigenvalue of `H`
equal `E₀` or be at least `E₀ + ΔE`, and let `ψ` be a ground vector. For every operator `M`,
the component of `M ψ` orthogonal to the ground eigenspace has norm at most
`(‖W‖ e^{-q/2} + ‖W_tilde - M‖) ‖ψ‖`. Hastings, arXiv:cond-mat/0508554v3, the triangle
inequality before eq. `facld` (lines 322–348); with `M` as in
`exists_local_approx_gaussianFilteredTerm`, the bound is eq. `facld` with `q` and `T` free. -/
theorem norm_sub_starProjection_apply_le_of_gaussianFilteredTerm {q ΔE : ℝ} (hq : 0 ≤ q)
    (hΔE : 0 < ΔE) {H : Matrix n n ℂ} (hH : H.IsHermitian) {E₀ : ℝ}
    (hgap : ∀ k, hH.eigenvalues k = E₀ ∨ E₀ + ΔE ≤ hH.eigenvalues k)
    (W M : Matrix n n ℂ) {ψ : EuclideanSpace ℂ n} (hψ : ψ ∈ groundEigenspace H E₀) :
    ‖toEuclideanLin M ψ - (groundEigenspace H E₀).starProjection (toEuclideanLin M ψ)‖ ≤
      (‖W‖ * Real.exp (-q / 2) + ‖gaussianFilteredTerm q ΔE H W - M‖) * ‖ψ‖ := by
  set K := groundEigenspace H E₀
  set x := toEuclideanLin (gaussianFilteredTerm q ΔE H W) ψ
  set z := toEuclideanLin (M - gaussianFilteredTerm q ΔE H W) ψ
  have hMxz : toEuclideanLin M ψ = x + z := by
    simp only [x, z, map_sub, LinearMap.sub_apply, add_sub_cancel]
  have hsplit : toEuclideanLin M ψ - K.starProjection (toEuclideanLin M ψ) =
      (x - K.starProjection x) + (z - K.starProjection z) := by
    rw [hMxz, map_add]; abel
  have hz : ‖z - K.starProjection z‖ ≤ ‖z‖ := by
    have := K.starProjection_add_starProjection_orthogonal z
    rw [show z - K.starProjection z = Kᗮ.starProjection z from
      sub_eq_iff_eq_add'.mpr this.symm]
    exact Kᗮ.norm_starProjection_apply_le z
  have hzψ : ‖z‖ ≤ ‖gaussianFilteredTerm q ΔE H W - M‖ * ‖ψ‖ := by
    rw [norm_sub_rev, ← l2_opNorm_toEuclideanCLM]
    exact (toEuclideanCLM (n := n) (𝕜 := ℂ) (M - gaussianFilteredTerm q ΔE H W)).le_opNorm ψ
  rw [hsplit, add_mul]
  exact (norm_add_le _ _).trans (add_le_add
    (norm_sub_starProjection_gaussianFilteredTerm_le hq hΔE hH hgap W hψ) (hz.trans hzψ))

/-- **A unique gapped ground state is nearly an eigenvector of the approximation.** If `Ω` is a
unique ground state of `H` with gap `ΔE > 0`, then for every operator `M`,
`‖M Ω - ⟨Ω, M Ω⟩ Ω‖ ≤ ‖W‖ e^{-q/2} + ‖W_tilde - M‖`. Hastings, arXiv:cond-mat/0508554v3,
the case of one ground state (lines 375–387), where `M = M_i`. -/
theorem norm_apply_sub_inner_smul_le_of_gaussianFilteredTerm {q ΔE : ℝ} (hq : 0 ≤ q)
    (hΔE : 0 < ΔE) {H : Matrix n n ℂ} {E₀ : ℝ} {Ω : EuclideanSpace ℂ n}
    (hgs : IsGappedGroundState H E₀ Ω ΔE) (W M : Matrix n n ℂ) :
    ‖toEuclideanLin M Ω - ⟪Ω, toEuclideanLin M Ω⟫_ℂ • Ω‖ ≤
      ‖W‖ * Real.exp (-q / 2) + ‖gaussianFilteredTerm q ΔE H W - M‖ := by
  obtain ⟨hH, hgap⟩ := eigenvalues_eq_or_le_of_isGappedGroundState hgs hΔE
  have hspan : groundEigenspace H E₀ = Submodule.span ℂ {Ω} := hgs.eigenspace_eq_span hΔE
  have hΩ : Ω ∈ groundEigenspace H E₀ := by
    rw [hspan]; exact Submodule.mem_span_singleton_self Ω
  have h := norm_sub_starProjection_apply_le_of_gaussianFilteredTerm hq hΔE hH hgap W M hΩ
  rwa [hspan, Submodule.starProjection_unit_singleton ℂ hgs.1, hgs.1, mul_one] at h

/-- **The sum of the approximations.** If the terms `Wᵢ` sum to `H`, then any operators `Mᵢ`
satisfy `‖∑ᵢ Mᵢ - H‖ ≤ ∑ᵢ ‖W_tildeᵢ - Mᵢ‖`, since the filtered terms also sum to `H`.
Hastings, arXiv:cond-mat/0508554v3, lines 359–374: the difference between `H` and
`M = ∑ᵢ Mᵢ` is at most the sum of the errors of eq. `apb`. -/
theorem norm_sum_sub_le_of_sum_eq {κ : Type*} (s : Finset κ) (q ΔE : ℝ) {H : Matrix n n ℂ}
    (hH : H.IsHermitian) {W M : κ → Matrix n n ℂ} (hsum : ∑ i ∈ s, W i = H) :
    ‖∑ i ∈ s, M i - H‖ ≤ ∑ i ∈ s, ‖gaussianFilteredTerm q ΔE H (W i) - M i‖ := by
  have hW := sum_gaussianFilteredTerm s q ΔE hH hsum
  calc ‖∑ i ∈ s, M i - H‖
      = ‖∑ i ∈ s, (M i - gaussianFilteredTerm q ΔE H (W i))‖ := by
        rw [Finset.sum_sub_distrib, hW]
    _ ≤ ∑ i ∈ s, ‖M i - gaussianFilteredTerm q ΔE H (W i)‖ := norm_sum_le _ _
    _ = _ := Finset.sum_congr rfl fun i _ => norm_sub_rev _ _

end Ground

end TNLean.Lattice
