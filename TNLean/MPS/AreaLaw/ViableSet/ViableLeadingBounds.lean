/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ViableSet.ViableLeadingVector
import TNLean.MPS.AreaLaw.ViableSet.GluingBounds
import TNLean.MPS.AreaLaw.LocalSolution.HierarchicalEnergy
import QICLean.Analysis.DensityMaxEigenvector
import QICLean.Analysis.DominantEigenvectorUniqueness

/-!
# Every minimizing boundary state and its top eigenvector

Fix a supported decomposition of the Hamiltonian before choosing the ground vector.
Viability then supplies witness data for which the energy and overlap bounds hold for every
feasible global minimizer of the left energy and every unit eigenvector associated with its
largest eigenvalue.

Source: Landau, Vazirani and Vidick, arXiv:1307.5143v1, `algo53.tex`, equation `eq:conv`,
lines 472–476, Lemma `l:leading`, lines 493–505, and Lemma `l:within`, lines 509–515.

**Scope restriction (nontrivial chains and bond bound):** The theorem assumes `0 < L` and
`2 ≤ q` and uses the library bound `constantCutBond q 1 1 Δ c`, rather than the quantitative
AKLV bound; see `docs/paper-gaps/lvv13_nontrivial_chain.tex` and
`docs/paper-gaps/lvv13_constant_bond.tex`. Boundary points are quantified on the actual bond
space. No finite-net cardinality assertion is made; see
`docs/paper-gaps/lvv13_leading_net_point.tex`.
-/

open Matrix
open scoped InnerProductSpace ComplexOrder Kronecker Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw

variable {L q k : ℕ}

/-- The largest eigenvalue of a low-energy density matrix is at least its ground-state
population.  Under a gap `Δ`, an energy excess `e` therefore gives the quantitative
bound `1 - e / Δ ≤ μ`.  This is the spectral separation estimate implicit in the
leading-vector step of LVV13, `algo53.tex`, lines 497--502. -/
theorem Matrix.PosSemidef.one_sub_energyExcess_div_gap_le_maxEigenvalue
    {n : Type*} [Fintype n] [DecidableEq n]
    {σ H : Matrix n n ℂ} {E₀ Δ e μ : ℝ} {Ω : EuclideanSpace ℂ n}
    (hσ : σ.PosSemidef) (htr : σ.trace = 1)
    (hgap : (H - (E₀ : ℂ) • 1 -
      (Δ : ℂ) • (1 - vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω)))).PosSemidef)
    (hΩ : ‖Ω‖ = 1) (hΔ : 0 < Δ) (henergy : (σ * H).trace.re ≤ E₀ + e)
    (hmax : ∀ (ν : ℝ) (z : EuclideanSpace ℂ n), z ≠ 0 →
      σ *ᵥ WithLp.ofLp z = (ν : ℂ) • WithLp.ofLp z → ν ≤ μ) :
    1 - e / Δ ≤ μ := by
  classical
  let hS := hσ.isHermitian
  let b := hS.eigenvectorBasis
  let lam := hS.eigenvalues
  let E : n → ℝ := fun i ↦ (⟪b i, toEuclideanLin H (b i)⟫_ℂ).re
  have hb1 (i : n) : ‖b i‖ = 1 := b.orthonormal.1 i
  have hlam0 (i : n) : 0 ≤ lam i := hσ.eigenvalues_nonneg i
  have hlam1 : ∑ i, lam i = 1 := by
    have hh := congrArg Complex.re hS.trace_eq_sum_eigenvalues
    rw [htr, Complex.re_sum] at hh
    simpa [lam] using hh.symm
  have hgap_i (i : n) :
      Δ * (1 - ‖⟪Ω, b i⟫_ℂ‖ ^ 2) ≤ E i - E₀ := by
    have hh := hgap.gap_le (b i)
    rw [hb1, one_pow, mul_one] at hh
    exact hh
  have hsum : ∑ i, lam i * (E i - E₀) ≤ e := by
    have hh : (σ * H).trace.re = ∑ i, lam i * E i :=
      hS.re_trace_mul_eq_sum_eigenvalues_mul H
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hlam1, one_mul]
    linarith
  have hweighted :
      Δ * ∑ i, lam i * (1 - ‖⟪Ω, b i⟫_ℂ‖ ^ 2) ≤ e := by
    calc
      _ = ∑ i, lam i * (Δ * (1 - ‖⟪Ω, b i⟫_ℂ‖ ^ 2)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ ≤ ∑ i, lam i * (E i - E₀) := Finset.sum_le_sum fun i _ ↦
        mul_le_mul_of_nonneg_left (hgap_i i) (hlam0 i)
      _ ≤ e := hsum
  have hpopulation : 1 - e / Δ ≤ ∑ i, lam i * ‖⟪Ω, b i⟫_ℂ‖ ^ 2 := by
    have hid : ∑ i, lam i * (1 - ‖⟪Ω, b i⟫_ℂ‖ ^ 2) =
        1 - ∑ i, lam i * ‖⟪Ω, b i⟫_ℂ‖ ^ 2 := by
      simp only [mul_sub, mul_one, Finset.sum_sub_distrib, hlam1]
    rw [hid] at hweighted
    field_simp [ne_of_gt hΔ]
    nlinarith only [hweighted]
  have hlamμ (i : n) : lam i ≤ μ := by
    apply hmax (lam i) (b i) (by
      intro hz
      have hi := hb1 i
      rw [hz, norm_zero] at hi
      norm_num at hi)
    exact hS.mulVec_eigenvectorBasis i
  have hparseval : ∑ i, ‖⟪Ω, b i⟫_ℂ‖ ^ 2 = 1 := by
    have hh := b.sum_sq_norm_inner_right Ω
    rw [hΩ, one_pow] at hh
    simpa only [norm_inner_symm] using hh
  calc
    1 - e / Δ ≤ ∑ i, lam i * ‖⟪Ω, b i⟫_ℂ‖ ^ 2 := hpopulation
    _ ≤ ∑ i, μ * ‖⟪Ω, b i⟫_ℂ‖ ^ 2 :=
      Finset.sum_le_sum fun i _ ↦ mul_le_mul_of_nonneg_right (hlamμ i) (sq_nonneg _)
    _ = μ := by rw [← Finset.mul_sum, hparseval, mul_one]

/-- At the LVV leading-vector energy scale, the maximal density eigenvalue is uniformly
bounded away from one half: energy excess at most `Δ / 24` gives `23 / 24 ≤ μ`.
This is the quantitative conditioning needed for a numerical leading-eigenvector solve. -/
theorem Matrix.PosSemidef.twentyThree_div_twentyFour_le_maxEigenvalue
    {n : Type*} [Fintype n] [DecidableEq n]
    {σ H : Matrix n n ℂ} {E₀ Δ μ : ℝ} {Ω : EuclideanSpace ℂ n}
    (hσ : σ.PosSemidef) (htr : σ.trace = 1)
    (hgap : (H - (E₀ : ℂ) • 1 -
      (Δ : ℂ) • (1 - vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω)))).PosSemidef)
    (hΩ : ‖Ω‖ = 1) (hΔ : 0 < Δ) (henergy : (σ * H).trace.re ≤ E₀ + Δ / 24)
    (hmax : ∀ (ν : ℝ) (z : EuclideanSpace ℂ n), z ≠ 0 →
      σ *ᵥ WithLp.ofLp z = (ν : ℂ) • WithLp.ofLp z → ν ≤ μ) :
    23 / 24 ≤ μ := by
  have hh := Matrix.PosSemidef.one_sub_energyExcess_div_gap_le_maxEigenvalue
    hσ htr hgap hΩ hΔ henergy hmax
  have heq : 1 - (Δ / 24) / Δ = (23 : ℝ) / 24 := by
    field_simp [ne_of_gt hΔ]
    ring
  rwa [heq] at hh

/-- For a trace-one positive matrix, an eigenvalue `μ > 1 / 2` leaves at most
`1 - μ` on the orthogonal complement of its unit eigenvector.  This is the
spectral separation used to certify a numerical leading eigenvector in LVV13,
`algo53.tex`, Lemma `l:leading`, lines 493--505. -/
theorem Matrix.PosSemidef.re_inner_le_one_sub_eigenvalue_of_orthogonal
    {n : Type*} [Fintype n] [DecidableEq n]
    {σ : Matrix n n ℂ} (hσ : σ.PosSemidef) (htr : σ.trace = 1)
    {u : EuclideanSpace ℂ n} {μ : ℝ} (hu : ‖u‖ = 1)
    (huσ : σ *ᵥ WithLp.ofLp u = (μ : ℂ) • WithLp.ofLp u)
    (hμ : 1 / 2 < μ) {w : EuclideanSpace ℂ n} (huw : ⟪u, w⟫_ℂ = 0) :
    (⟪w, toEuclideanLin σ w⟫_ℂ).re ≤ (1 - μ) * ‖w‖ ^ 2 := by
  classical
  let hS := hσ.isHermitian
  let b := hS.eigenvectorBasis
  let lam := hS.eigenvalues
  let L := toEuclideanLin σ
  have hsum : ∑ i, lam i = 1 := by
    have hh := congrArg Complex.re hS.trace_eq_sum_eigenvalues
    rw [htr, Complex.re_sum] at hh
    simpa [lam] using hh.symm
  have huL : L u = (μ : ℂ) • u := by
    apply WithLp.ofLp_injective 2
    simpa only [L, toLpLin_apply, WithLp.ofLp_toLp, WithLp.ofLp_smul] using huσ
  have hcoord (x : EuclideanSpace ℂ n) (i : n) :
      b.repr (L x) i = (lam i : ℂ) * b.repr x i := by
    calc
      b.repr (L x) i = ⟪b i, L x⟫_ℂ := b.repr_apply_apply (L x) i
      _ = ⟪L (b i), x⟫_ℂ :=
        ((isSymmetric_toEuclideanLin_iff.mpr hS) (b i) x).symm
      _ = (lam i : ℂ) * b.repr x i := by
        have hb : L (b i) = (lam i : ℂ) • b i := by
          apply WithLp.ofLp_injective 2
          simp only [L, toLpLin_apply, WithLp.ofLp_toLp, WithLp.ofLp_smul]
          exact (hS.mulVec_eigenvectorBasis i).trans (Complex.coe_smul _ _).symm
        rw [hb, inner_smul_left, Complex.conj_ofReal, ← b.repr_apply_apply]
  obtain ⟨j, hj⟩ : ∃ j, b.repr u j ≠ 0 := by
    by_contra! hz
    have hu0 : u = 0 := b.repr.injective (by ext i; simpa using hz i)
    rw [hu0, norm_zero] at hu
    norm_num at hu
  have hlamj : lam j = μ := by
    have hh := hcoord u j
    rw [huL, map_smul] at hh
    change (μ : ℂ) * b.repr u j = (lam j : ℂ) * b.repr u j at hh
    exact Complex.ofReal_injective (mul_right_cancel₀ hj hh.symm)
  have hbσ : σ *ᵥ WithLp.ofLp (b j) = (lam j : ℂ) • WithLp.ofLp (b j) :=
    (hS.mulVec_eigenvectorBasis j).trans (Complex.coe_smul _ _).symm
  obtain ⟨_, z, hz, hbphase⟩ :=
    hσ.eigenvalue_eq_and_exists_unit_smul_of_gt_half htr hu (b.orthonormal.1 j)
      huσ hbσ hμ (hlamj ▸ hμ)
  have hwj : b.repr w j = 0 := by
    rw [b.repr_apply_apply, hbphase, inner_smul_left, huw, mul_zero]
  have hlam (i : n) (hij : i ≠ j) : lam i ≤ 1 - μ := by
    have hpair : lam i + lam j ≤ ∑ k, lam k := by
      rw [← Finset.sum_pair (f := lam) hij]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        fun k _ _ ↦ hσ.eigenvalues_nonneg k
    rw [hsum, hlamj] at hpair
    linarith
  have hform : (⟪w, L w⟫_ℂ).re =
      ∑ i, lam i * Complex.normSq (b.repr w i) := by
    have hc : ⟪w, L w⟫_ℂ =
        ∑ i, (lam i : ℂ) * (Complex.normSq (b.repr w i) : ℂ) := by
      calc
        ⟪w, L w⟫_ℂ = ⟪b.repr w, b.repr (L w)⟫_ℂ :=
          (b.repr.inner_map_map w (L w)).symm
        _ = _ := by
          rw [EuclideanSpace.inner_eq_star_dotProduct]
          simp_rw [dotProduct, hcoord]
          simp [mul_assoc, Complex.mul_conj]
    have hh := congrArg Complex.re hc
    simpa only [Complex.re_sum, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero] using hh
  have hnorm : ∑ i, Complex.normSq (b.repr w i) = ‖w‖ ^ 2 := by
    rw [← b.repr.norm_map, EuclideanSpace.norm_sq_eq]
    simp_rw [Complex.normSq_eq_norm_sq]
  change (⟪w, L w⟫_ℂ).re ≤ (1 - μ) * ‖w‖ ^ 2
  rw [hform, ← hnorm, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  by_cases hij : i = j
  · subst i
    rw [hwj, Complex.normSq_zero, mul_zero, mul_zero]
  · exact mul_le_mul_of_nonneg_right (hlam i hij) (Complex.normSq_nonneg _)

/-- The uniform bound `23 / 24 ≤ μ` leaves a spectral separation of at least
`11 / 12` between `μ` and the interval `[0, 1 - μ]`.  Consequently division by
this separation costs at most the factor `12 / 11`. -/
theorem leading_residual_div_separation_le
    {r μ : ℝ} (hr : 0 ≤ r) (hμ : 23 / 24 ≤ μ) :
    r / (2 * μ - 1) ≤ (12 / 11) * r := by
  have hsep : (11 : ℝ) / 12 ≤ 2 * μ - 1 := by linarith only [hμ]
  have hpos : 0 < 2 * μ - 1 := lt_of_lt_of_le (by norm_num) hsep
  apply (div_le_iff₀ hpos).2
  nlinarith only [hr, hsep]

/-- The maximal eigenvalue in the numerical gluing problem retains the full quantitative
ground-population bound.  Objective error `ξ` and boundary error `τ` enter through the
same total excess `e + ξ + ‖K‖ τ` as in the LVV leading-vector estimate. -/
theorem maxEigenvalue_lower_bound_of_gluing_with_objective_slack
    {a s r b : Type*} [Fintype a] [Fintype s] [Fintype r] [Fintype b]
    [DecidableEq a] [DecidableEq s] [DecidableEq r] [DecidableEq b]
    (W : Matrix r b ℂ) (hW : Wᴴ * W = 1)
    (HL : Matrix (a × s) (a × s) ℂ) (K : Matrix (s × r) (s × r) ℂ)
    {E₀ Δ e τ ξ μ : ℝ} {Γ : EuclideanSpace ℂ ((a × s) × r)}
    (hgap : (HL ⊗ₖ (1 : Matrix r r ℂ) +
        reindex (Equiv.prodAssoc a s r).symm (Equiv.prodAssoc a s r).symm
          ((1 : Matrix a a ℂ) ⊗ₖ K) - (E₀ : ℂ) • 1 -
      (Δ : ℂ) • (1 - vecMulVec (WithLp.ofLp Γ) (star (WithLp.ofLp Γ)))).PosSemidef)
    (hΓ : ‖Γ‖ = 1) (hΔ : 0 < Δ)
    {σ : Matrix ((a × s) × b) ((a × s) × b) ℂ}
    (hσ : σ.PosSemidef) (htr : σ.trace = 1) (x : (a × s) × b → ℂ)
    (hopt : (σ * (HL ⊗ₖ (1 : Matrix b b ℂ))).trace.re ≤
      (vecMulVec x (star x) * (HL ⊗ₖ (1 : Matrix b b ℂ))).trace.re + ξ)
    (hτ : rectangularTraceNorm
      (partialTraceFirst σ - partialTraceFirst (vecMulVec x (star x))) ≤ τ)
    (hw : (vecMulVec (((1 : Matrix (a × s) (a × s) ℂ) ⊗ₖ W) *ᵥ x)
        (star (((1 : Matrix (a × s) (a × s) ℂ) ⊗ₖ W) *ᵥ x)) *
      (HL ⊗ₖ (1 : Matrix r r ℂ) +
        reindex (Equiv.prodAssoc a s r).symm (Equiv.prodAssoc a s r).symm
          ((1 : Matrix a a ℂ) ⊗ₖ K))).trace.re ≤ E₀ + e)
    (hmax : ∀ (ν : ℝ) (z : EuclideanSpace ℂ ((a × s) × b)), z ≠ 0 →
      σ *ᵥ WithLp.ofLp z = (ν : ℂ) • WithLp.ofLp z → ν ≤ μ) :
    1 - (e + ξ + ‖K‖ * τ) / Δ ≤ μ := by
  classical
  let J := (1 : Matrix (a × s) (a × s) ℂ) ⊗ₖ W
  let Hf := HL ⊗ₖ (1 : Matrix r r ℂ) +
    reindex (Equiv.prodAssoc a s r).symm (Equiv.prodAssoc a s r).symm
      ((1 : Matrix a a ℂ) ⊗ₖ K)
  let σ' := J * σ * Jᴴ
  have hJJ : Jᴴ * J = 1 := by
    simp only [J, conjTranspose_kronecker, conjTranspose_one, ← mul_kronecker_mul,
      Matrix.one_mul, hW, one_kronecker_one]
  have hσ' : σ'.PosSemidef := hσ.mul_mul_conjTranspose_same J
  have htr' : σ'.trace = 1 := by
    rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hJJ, Matrix.one_mul, htr]
  have hglue := re_trace_gluing_le W hW σ x HL K
  have hxv : (vecMulVec x (star x) * (HL ⊗ₖ (1 : Matrix b b ℂ))).trace =
      (vecMulVec (J *ᵥ x) (star (J *ᵥ x)) * (HL ⊗ₖ (1 : Matrix r r ℂ))).trace := by
    have hv : vecMulVec (J *ᵥ x) (star (J *ᵥ x)) = J * vecMulVec x (star x) * Jᴴ := by
      rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.vecMul_conjTranspose, star_star]
    rw [hv, trace_gluing_mul_kronecker_one W hW]
  have henergy : (σ' * Hf).trace.re ≤ E₀ + (e + ξ + ‖K‖ * τ) := by
    have hsplit : (vecMulVec (J *ᵥ x) (star (J *ᵥ x)) * Hf).trace.re =
        (vecMulVec (J *ᵥ x) (star (J *ᵥ x)) *
          (HL ⊗ₖ (1 : Matrix r r ℂ))).trace.re +
        (vecMulVec (J *ᵥ x) (star (J *ᵥ x)) *
          reindex (Equiv.prodAssoc a s r).symm (Equiv.prodAssoc a s r).symm
            ((1 : Matrix a a ℂ) ⊗ₖ K)).trace.re := by
      simp only [Hf, Matrix.mul_add, trace_add, Complex.add_re]
    rw [← hxv] at hsplit
    have hscaled := mul_le_mul_of_nonneg_left hτ (norm_nonneg K)
    simp only [σ', J] at hglue ⊢
    linarith
  obtain ⟨u₀, μ₀, hu₀, hu₀eig, hμ₀, -⟩ :=
    Matrix.PosSemidef.exists_unit_eigenvector_max_eigenvalue hσ htr
  have hμ : 0 < μ := hμ₀.trans_le (hmax μ₀ u₀ (by
    intro hz
    simp only [hz, norm_zero, zero_ne_one] at hu₀) hu₀eig)
  have hmax' : ∀ (ν : ℝ) (z : EuclideanSpace ℂ ((a × s) × r)), z ≠ 0 →
      σ' *ᵥ WithLp.ofLp z = (ν : ℂ) • WithLp.ofLp z → ν ≤ μ := by
    intro ν z hz heig
    by_cases hν : ν = 0
    · simpa only [hν] using hμ.le
    have hpull : Jᴴ *ᵥ WithLp.ofLp z ≠ 0 := by
      intro hpull0
      have hzero : σ' *ᵥ WithLp.ofLp z = 0 := by
        rw [show σ' = J * σ * Jᴴ from rfl,
          ← Matrix.mulVec_mulVec, hpull0, Matrix.mulVec_zero]
      rw [heig] at hzero
      exact hz (WithLp.ofLp_injective 2 (smul_eq_zero.mp hzero |>.resolve_left
        (Complex.ofReal_ne_zero.mpr hν)))
    have hpulleig := congrArg (fun y ↦ Jᴴ *ᵥ y) heig
    simp only [σ', Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hJJ, Matrix.one_mul,
      Matrix.mulVec_smul] at hpulleig
    rw [← Matrix.mulVec_mulVec] at hpulleig
    exact hmax ν (WithLp.toLp 2 (Jᴴ *ᵥ WithLp.ofLp z))
      (by
        intro hzpull
        apply hpull
        change Jᴴ *ᵥ WithLp.ofLp z = WithLp.ofLp
          (0 : EuclideanSpace ℂ ((a × s) × b))
        exact congrArg WithLp.ofLp hzpull) (by
        simpa only [WithLp.ofLp_toLp] using hpulleig)
  exact Matrix.PosSemidef.one_sub_energyExcess_div_gap_le_maxEigenvalue
    hσ' htr' hgap hΓ hΔ henergy hmax'

/-- Chain-coordinate form of the quantitative maximal-eigenvalue gluing bound. -/
theorem maxEigenvalue_lower_bound_chain_with_objective_slack [NeZero q]
    {HL K : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ}
    (hHL : Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) HL (leftBlock L k))
    {D : Finset (Fin L)} (hK : Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) K D)
    (hDA : Disjoint D (leftBlock L (k - 1))) {E₀ Δ e τ ξ μ : ℝ}
    {Γ : EuclideanSpace ℂ (Fin L → Fin q)} (hΔ : 0 < Δ)
    (hgs : IsGappedGroundState (HL + K) E₀ Γ Δ) {m : ℕ}
    (W : Matrix (CutRight L q k) (Fin m) ℂ) (hW : Wᴴ * W = 1)
    (x : (CutLeft L q k × CutSite L q k) × Fin m → ℂ)
    {w : EuclideanSpace ℂ (Fin L → Fin q)}
    (hwx : WithLp.ofLp w ∘ (gluingCut L q k).symm =
      ((1 : Matrix (CutLeft L q k × CutSite L q k)
        (CutLeft L q k × CutSite L q k) ℂ) ⊗ₖ W) *ᵥ x)
    (hwE : (⟪w, toEuclideanLin (HL + K) w⟫_ℂ).re ≤ E₀ + e)
    {σ : Matrix ((CutLeft L q k × CutSite L q k) × Fin m)
      ((CutLeft L q k × CutSite L q k) × Fin m) ℂ}
    (hσ : σ.PosSemidef) (htr : σ.trace = 1)
    (hopt : (σ * (leftCutOperator k HL ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ))).trace.re ≤
      (vecMulVec x (star x) *
        (leftCutOperator k HL ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ))).trace.re + ξ)
    (hτ : rectangularTraceNorm
      (partialTraceFirst σ - partialTraceFirst (vecMulVec x (star x))) ≤ τ)
    (hmax : ∀ (ν : ℝ) (z : EuclideanSpace ℂ
      ((CutLeft L q k × CutSite L q k) × Fin m)), z ≠ 0 →
      σ *ᵥ WithLp.ofLp z = (ν : ℂ) • WithLp.ofLp z → ν ≤ μ) :
    1 - (e + ξ + ‖K‖ * τ) / Δ ≤ μ := by
  classical
  let E := gluingCut L q k
  let J := (1 : Matrix (CutLeft L q k × CutSite L q k)
    (CutLeft L q k × CutSite L q k) ℂ) ⊗ₖ W
  let K' := rightCutOperator k K
  let Γ' : EuclideanSpace ℂ
      ((CutLeft L q k × CutSite L q k) × CutRight L q k) :=
    WithLp.toLp 2 (WithLp.ofLp Γ ∘ E.symm)
  have hsplit := reindex_gluingCut_eq hHL hK hDA
  obtain ⟨hΓ, -, hgap⟩ := isGappedGroundState_iff.mp hgs
  have hΓ' : ‖Γ'‖ = 1 :=
    ((LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ E).norm_map Γ).trans hΓ
  have hgap' : (reindex E E (HL + K) - (E₀ : ℂ) • 1 -
      (Δ : ℂ) • (1 - vecMulVec (WithLp.ofLp Γ') (star (WithLp.ofLp Γ')))).PosSemidef := by
    have hh := hgap.submatrix E.symm
    convert hh using 1
    ext i j
    simp [reindex_apply, Γ', one_apply, vecMulVec_apply, E.symm.injective.eq_iff]
  rw [hsplit] at hgap'
  have hw' : (vecMulVec (J *ᵥ x) (star (J *ᵥ x)) *
      (leftCutOperator k HL ⊗ₖ
          (1 : Matrix (CutRight L q k) (CutRight L q k) ℂ) +
        reindex (Equiv.prodAssoc _ _ _).symm (Equiv.prodAssoc _ _ _).symm
          ((1 : Matrix (CutLeft L q k) (CutLeft L q k) ℂ) ⊗ₖ K'))).trace.re ≤ E₀ + e := by
    rw [← hsplit, ← hwx, trace_mul_comm, mul_vecMulVec, trace_vecMulVec]
    have hh := inner_toEuclideanLin_reindex E (HL + K) w
    simp only [EuclideanSpace.inner_eq_star_dotProduct, toLpLin_apply] at hh
    rw [hh]
    exact hwE
  have hKK : ‖K'‖ ≤ ‖K‖ := by
    have hr := hK.reindex_threeCutEquiv_eq_one_kronecker
      (leftBlock_mono (Nat.sub_le k 1)) hDA (fun _ ↦ 0)
    have hn : ‖reindex E E K‖ = ‖K‖ := l2_opNorm_reindex_equiv E K
    rw [show reindex E E K = _ from hr, l2_opNorm_reindex_equiv] at hn
    exact (l2_opNorm_one_kronecker (X := CutLeft L q k) K').symm.le.trans hn.le
  have hbase := maxEigenvalue_lower_bound_of_gluing_with_objective_slack
    W hW (leftCutOperator k HL) K' hgap' hΓ' hΔ hσ htr x hopt hτ hw' hmax
  have hτ0 : 0 ≤ τ := (rectangularTraceNorm_nonneg _).trans hτ
  have hfrac : (e + ξ + ‖K'‖ * τ) / Δ ≤
      (e + ξ + ‖K‖ * τ) / Δ := by
    apply div_le_div_of_nonneg_right _ hΔ.le
    linarith only [mul_le_mul_of_nonneg_right hKK hτ0]
  linarith only [hbase, hfrac]

/-- The energy and ground-state overlap bounds are stable under a numerical perturbation
of the unit witness.  If `v'` is within distance `ζ` of `v`, its energy increases by at
most `2 ‖H‖ ζ`, while its overlap with a fixed unit vector decreases by at most `ζ`. -/
theorem nearby_unit_vector_energy_and_overlap_bounds
    {n : Type*} [Fintype n] [DecidableEq n] (H : Matrix n n ℂ)
    {Γ v v' : EuclideanSpace ℂ n} {E a ζ : ℝ}
    (hΓ : ‖Γ‖ = 1) (hv : ‖v‖ = 1) (hv' : ‖v'‖ = 1)
    (hE : (⟪v, toEuclideanLin H v⟫_ℂ).re ≤ E)
    (ha : a ≤ ‖⟪Γ, v⟫_ℂ‖) (hdist : ‖v' - v‖ ≤ ζ) :
    (⟪v', toEuclideanLin H v'⟫_ℂ).re ≤ E + 2 * ‖H‖ * ζ ∧
      a - ζ ≤ ‖⟪Γ, v'⟫_ℂ‖ := by
  constructor
  · have henergy := LocalSolution.abs_re_inner_sub_re_inner_le H hv' hv
    rw [abs_le] at henergy
    have hscaled : 2 * ‖H‖ * ‖v' - v‖ ≤ 2 * ‖H‖ * ζ :=
      mul_le_mul_of_nonneg_left hdist (mul_nonneg (by norm_num) (norm_nonneg H))
    linarith only [henergy.2, hE, hscaled]
  · have hinner : ‖⟪Γ, v⟫_ℂ‖ ≤ ‖⟪Γ, v'⟫_ℂ‖ + ‖v' - v‖ := by
      calc
        ‖⟪Γ, v⟫_ℂ‖ = ‖⟪Γ, v'⟫_ℂ + ⟪Γ, v - v'⟫_ℂ‖ := by
          rw [inner_sub_right]
          congr 2
          abel
        _ ≤ ‖⟪Γ, v'⟫_ℂ‖ + ‖⟪Γ, v - v'⟫_ℂ‖ := norm_add_le _ _
        _ ≤ ‖⟪Γ, v'⟫_ℂ‖ + ‖v - v'‖ := by
          gcongr
          simpa only [hΓ, one_mul] using norm_inner_le_norm (𝕜 := ℂ) Γ (v - v')
        _ = ‖⟪Γ, v'⟫_ℂ‖ + ‖v' - v‖ := by rw [norm_sub_rev]
    linarith only [ha, hinner, hdist]

/-- For a range-one chain Hamiltonian, perturbing a unit witness by distance at most `ζ`
costs at most `4 L ζ` in energy and `ζ` in ground-state overlap. -/
theorem ChainHamiltonian.nearby_unit_vector_energy_and_overlap_bounds
    {L q : ℕ} (h : ChainHamiltonian L q 1 1)
    {Γ v v' : EuclideanSpace ℂ (Fin L → Fin q)} {E a ζ : ℝ}
    (hΓ : ‖Γ‖ = 1) (hv : ‖v‖ = 1) (hv' : ‖v'‖ = 1)
    (hE : (⟪v, toEuclideanLin h.operator v⟫_ℂ).re ≤ E)
    (ha : a ≤ ‖⟪Γ, v⟫_ℂ‖) (hdist : ‖v' - v‖ ≤ ζ) :
    (⟪v', toEuclideanLin h.operator v'⟫_ℂ).re ≤ E + 4 * L * ζ ∧
      a - ζ ≤ ‖⟪Γ, v'⟫_ℂ‖ := by
  obtain ⟨henergy, hoverlap⟩ :=
    TNLean.MPS.AreaLaw.nearby_unit_vector_energy_and_overlap_bounds
      h.operator hΓ hv hv' hE ha hdist
  refine ⟨henergy.trans ?_, hoverlap⟩
  have hop : ‖h.operator‖ ≤ 2 * L := by
    simpa only [mul_one] using h.norm_operator_le_of_range_one
  have hζ : 0 ≤ ζ := (norm_nonneg (v' - v)).trans hdist
  nlinarith only [hop, hζ]

/-- Applying the right-bond isometry and returning from cut coordinates preserves the
distance between two compressed vectors exactly. -/
theorem norm_glued_vectors_sub_eq {L q k m : ℕ}
    (W : Matrix (CutRight L q k) (Fin m) ℂ) (hW : Wᴴ * W = 1)
    (u u' : EuclideanSpace ℂ ((CutLeft L q k × CutSite L q k) × Fin m)) :
    ‖WithLp.toLp 2
          ((((1 : Matrix (CutLeft L q k × CutSite L q k)
            (CutLeft L q k × CutSite L q k) ℂ) ⊗ₖ W) *ᵥ WithLp.ofLp u') ∘
              gluingCut L q k) -
        WithLp.toLp 2
          ((((1 : Matrix (CutLeft L q k × CutSite L q k)
            (CutLeft L q k × CutSite L q k) ℂ) ⊗ₖ W) *ᵥ WithLp.ofLp u) ∘
              gluingCut L q k)‖ = ‖u' - u‖ := by
  classical
  let J := (1 : Matrix (CutLeft L q k × CutSite L q k)
    (CutLeft L q k × CutSite L q k) ℂ) ⊗ₖ W
  have hJ : Jᴴ * J = 1 := by
    simp only [J, conjTranspose_kronecker, conjTranspose_one, ← mul_kronecker_mul,
      Matrix.one_mul, hW, one_kronecker_one]
  have hsub : WithLp.toLp 2 ((J *ᵥ WithLp.ofLp u') ∘ gluingCut L q k) -
      WithLp.toLp 2 ((J *ᵥ WithLp.ofLp u) ∘ gluingCut L q k) =
      WithLp.toLp 2 ((J *ᵥ WithLp.ofLp (u' - u)) ∘ gluingCut L q k) := by
    apply WithLp.ofLp_injective 2
    ext i
    simp only [WithLp.ofLp_sub, Pi.sub_apply, Function.comp_apply,
      Matrix.mulVec_sub]
  change ‖WithLp.toLp 2 ((J *ᵥ WithLp.ofLp u') ∘ gluingCut L q k) -
      WithLp.toLp 2 ((J *ᵥ WithLp.ofLp u) ∘ gluingCut L q k)‖ = _
  rw [hsub]
  exact ((LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (gluingCut L q k).symm).norm_map
    (WithLp.toLp 2 (J *ᵥ WithLp.ofLp (u' - u)))).trans
      (norm_toLp_mulVec_of_isometry J hJ (u' - u))

/-- The physical gluing map is complex-linear: changing the phase of a compressed
vector changes the phase of the resulting chain vector by the same amount. -/
theorem gluedVector_smul {L q k m : ℕ}
    (W : Matrix (CutRight L q k) (Fin m) ℂ) (c : ℂ)
    (u : EuclideanSpace ℂ ((CutLeft L q k × CutSite L q k) × Fin m)) :
    WithLp.toLp 2
        ((((1 : Matrix (CutLeft L q k × CutSite L q k)
          (CutLeft L q k × CutSite L q k) ℂ) ⊗ₖ W) *ᵥ WithLp.ofLp (c • u)) ∘
            gluingCut L q k) =
      c • WithLp.toLp 2
        ((((1 : Matrix (CutLeft L q k × CutSite L q k)
          (CutLeft L q k × CutSite L q k) ℂ) ⊗ₖ W) *ᵥ WithLp.ofLp u) ∘
            gluingCut L q k) := by
  apply WithLp.ofLp_injective 2
  ext i
  simp only [WithLp.ofLp_smul, mulVec_smul, Function.comp_apply, Pi.smul_apply]

/-- The energy expectation and the absolute overlap of a glued vector are invariant
under a phase change of its compressed representative. -/
theorem gluedVector_phase_invariants {L q k m : ℕ}
    (W : Matrix (CutRight L q k) (Fin m) ℂ)
    (u : EuclideanSpace ℂ ((CutLeft L q k × CutSite L q k) × Fin m))
    (θ : ℝ) (H : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (Γ : EuclideanSpace ℂ (Fin L → Fin q)) :
    let c := Complex.exp (θ * Complex.I)
    let v := WithLp.toLp 2
      ((((1 : Matrix (CutLeft L q k × CutSite L q k)
        (CutLeft L q k × CutSite L q k) ℂ) ⊗ₖ W) *ᵥ WithLp.ofLp u) ∘
          gluingCut L q k)
    let vθ := WithLp.toLp 2
      ((((1 : Matrix (CutLeft L q k × CutSite L q k)
        (CutLeft L q k × CutSite L q k) ℂ) ⊗ₖ W) *ᵥ WithLp.ofLp (c • u)) ∘
          gluingCut L q k)
    (⟪vθ, toEuclideanLin H vθ⟫_ℂ).re = (⟪v, toEuclideanLin H v⟫_ℂ).re ∧
      ‖⟪Γ, vθ⟫_ℂ‖ = ‖⟪Γ, v⟫_ℂ‖ := by
  dsimp only
  rw [gluedVector_smul]
  have hc : ‖Complex.exp ((θ : ℂ) * Complex.I)‖ = 1 := by
    rw [Complex.norm_exp]
    norm_num
  constructor
  · simp only [map_smul, inner_smul_left, inner_smul_right, ← mul_assoc]
    have hunit : Complex.exp ((θ : ℂ) * Complex.I) *
        (starRingEnd ℂ) (Complex.exp ((θ : ℂ) * Complex.I)) = 1 := by
      simpa only [hc, one_pow, Complex.ofReal_one] using
        Complex.mul_conj' (Complex.exp ((θ : ℂ) * Complex.I))
    rw [hunit, one_mul]
  · simp only [inner_smul_right, norm_mul, hc, one_mul]

/-- A nearby compressed unit vector fixed by the left support projection gives a physical
left-supported unit vector.  Its distance from the exact physical witness is the original
compressed distance, so its range-one energy and ground-state overlap incur only the
corresponding perturbation losses. -/
theorem ChainHamiltonian.nearby_glued_vector_bounds
    {L q k m : ℕ} (h : ChainHamiltonian L q 1 1)
    {Γ : EuclideanSpace ℂ (Fin L → Fin q)} (hΓ : ‖Γ‖ = 1)
    {S : Set (LeftBlockVector L q k)}
    (W : Matrix (CutRight L q k) (Fin m) ℂ) (hW : Wᴴ * W = 1)
    (u u' : EuclideanSpace ℂ ((CutLeft L q k × CutSite L q k) × Fin m))
    (hu : ‖u‖ = 1) (hu' : ‖u'‖ = 1)
    (hu'P : (reindex
        (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
        (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
        (spanProjection S) ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)) *ᵥ WithLp.ofLp u' =
      WithLp.ofLp u')
    {E a ζ : ℝ}
    (hE : (⟪WithLp.toLp 2
        ((((1 : Matrix (CutLeft L q k × CutSite L q k)
          (CutLeft L q k × CutSite L q k) ℂ) ⊗ₖ W) *ᵥ WithLp.ofLp u) ∘
            gluingCut L q k),
        toEuclideanLin h.operator (WithLp.toLp 2
          ((((1 : Matrix (CutLeft L q k × CutSite L q k)
            (CutLeft L q k × CutSite L q k) ℂ) ⊗ₖ W) *ᵥ WithLp.ofLp u) ∘
              gluingCut L q k))⟫_ℂ).re ≤ E)
    (ha : a ≤ ‖⟪Γ, WithLp.toLp 2
      ((((1 : Matrix (CutLeft L q k × CutSite L q k)
        (CutLeft L q k × CutSite L q k) ℂ) ⊗ₖ W) *ᵥ WithLp.ofLp u) ∘
          gluingCut L q k)⟫_ℂ‖)
    (hdist : ‖u' - u‖ ≤ ζ) :
    let v' := WithLp.toLp 2
      ((((1 : Matrix (CutLeft L q k × CutSite L q k)
        (CutLeft L q k × CutSite L q k) ℂ) ⊗ₖ W) *ᵥ WithLp.ofLp u') ∘
          gluingCut L q k)
    ‖v'‖ = 1 ∧ v' ∈ leftSupportSubmodule S ∧
      (⟪v', toEuclideanLin h.operator v'⟫_ℂ).re ≤ E + 4 * L * ζ ∧
      a - ζ ≤ ‖⟪Γ, v'⟫_ℂ‖ := by
  classical
  let P := reindex
    (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
    (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
    (spanProjection S)
  let J := (1 : Matrix (CutLeft L q k × CutSite L q k)
    (CutLeft L q k × CutSite L q k) ℂ) ⊗ₖ W
  let v := WithLp.toLp 2 ((J *ᵥ WithLp.ofLp u) ∘ gluingCut L q k)
  let v' := WithLp.toLp 2 ((J *ᵥ WithLp.ofLp u') ∘ gluingCut L q k)
  have hJ : Jᴴ * J = 1 := by
    simp only [J, conjTranspose_kronecker, conjTranspose_one, ← mul_kronecker_mul,
      Matrix.one_mul, hW, one_kronecker_one]
  have hv : ‖v‖ = 1 :=
    ((LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (gluingCut L q k).symm).norm_map
      (WithLp.toLp 2 (J *ᵥ WithLp.ofLp u))).trans
        ((norm_toLp_mulVec_of_isometry J hJ u).trans hu)
  have hv' : ‖v'‖ = 1 :=
    ((LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (gluingCut L q k).symm).norm_map
      (WithLp.toLp 2 (J *ᵥ WithLp.ofLp u'))).trans
        ((norm_toLp_mulVec_of_isometry J hJ u').trans hu')
  have hinter : (P ⊗ₖ (1 : Matrix (CutRight L q k) (CutRight L q k) ℂ)) * J =
      J * (P ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)) := by
    simp only [J, ← mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul]
  have hv'P : (P ⊗ₖ (1 : Matrix (CutRight L q k) (CutRight L q k) ℂ)) *ᵥ
      (J *ᵥ WithLp.ofLp u') = J *ᵥ WithLp.ofLp u' := by
    rw [mulVec_mulVec, hinter, ← mulVec_mulVec]
    change J *ᵥ ((P ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)) *ᵥ WithLp.ofLp u') = _
    rw [hu'P]
  have hv'S : v' ∈ leftSupportSubmodule S :=
    mem_leftSupportSubmodule_of_gluingCut_fixed S (J *ᵥ WithLp.ofLp u') hv'P
  have hvdist : ‖v' - v‖ ≤ ζ := by
    change ‖WithLp.toLp 2 ((J *ᵥ WithLp.ofLp u') ∘ gluingCut L q k) -
      WithLp.toLp 2 ((J *ᵥ WithLp.ofLp u) ∘ gluingCut L q k)‖ ≤ ζ
    rw [norm_glued_vectors_sub_eq W hW u u']
    exact hdist
  have hbounds := h.nearby_unit_vector_energy_and_overlap_bounds
    hΓ hv hv' hE ha hvdist
  exact ⟨hv', hv'S, hbounds⟩

/-- With the perturbation losses reserved in advance, a nearby compressed numerical vector
has the original LVV viability bounds `Δ / 12` and `1 / 12`. -/
theorem ChainHamiltonian.nearby_glued_vector_viable_bounds
    {L q k m : ℕ} (h : ChainHamiltonian L q 1 1)
    {E₀ Δ ζ : ℝ} {Γ : EuclideanSpace ℂ (Fin L → Fin q)} (hΓ : ‖Γ‖ = 1)
    {S : Set (LeftBlockVector L q k)}
    (W : Matrix (CutRight L q k) (Fin m) ℂ) (hW : Wᴴ * W = 1)
    (u u' : EuclideanSpace ℂ ((CutLeft L q k × CutSite L q k) × Fin m))
    (hu : ‖u‖ = 1) (hu' : ‖u'‖ = 1)
    (hu'P : (reindex
        (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
        (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
        (spanProjection S) ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)) *ᵥ WithLp.ofLp u' =
      WithLp.ofLp u')
    (hE : (⟪WithLp.toLp 2
        ((((1 : Matrix (CutLeft L q k × CutSite L q k)
          (CutLeft L q k × CutSite L q k) ℂ) ⊗ₖ W) *ᵥ WithLp.ofLp u) ∘
            gluingCut L q k),
        toEuclideanLin h.operator (WithLp.toLp 2
          ((((1 : Matrix (CutLeft L q k × CutSite L q k)
            (CutLeft L q k × CutSite L q k) ℂ) ⊗ₖ W) *ᵥ WithLp.ofLp u) ∘
              gluingCut L q k))⟫_ℂ).re ≤ E₀ + Δ / 12 - 4 * L * ζ)
    (ha : 1 - 1 / 12 + ζ ≤ ‖⟪Γ, WithLp.toLp 2
      ((((1 : Matrix (CutLeft L q k × CutSite L q k)
        (CutLeft L q k × CutSite L q k) ℂ) ⊗ₖ W) *ᵥ WithLp.ofLp u) ∘
          gluingCut L q k)⟫_ℂ‖)
    (hdist : ‖u' - u‖ ≤ ζ) :
    let v' := WithLp.toLp 2
      ((((1 : Matrix (CutLeft L q k × CutSite L q k)
        (CutLeft L q k × CutSite L q k) ℂ) ⊗ₖ W) *ᵥ WithLp.ofLp u') ∘
          gluingCut L q k)
    ‖v'‖ = 1 ∧ v' ∈ leftSupportSubmodule S ∧
      (⟪v', toEuclideanLin h.operator v'⟫_ℂ).re ≤ E₀ + Δ / 12 ∧
      1 - 1 / 12 ≤ ‖⟪Γ, v'⟫_ℂ‖ := by
  obtain ⟨hv', hv'S, henergy, hoverlap⟩ := h.nearby_glued_vector_bounds
    hΓ W hW u u' hu hu' hu'P hE ha hdist
  refine ⟨hv', hv'S, ?_, ?_⟩
  · linarith only [henergy]
  · linarith only [hoverlap]

/-- Viability supplies cut data valid for every feasible global minimizer and every unit top
eigenvector. Auxiliary library-bond form of LVV13, `algo53.tex`, equation `eq:conv`,
lines 472–476, Lemma `l:leading`, lines 493–505, and Lemma `l:within`, lines 509–515. -/
theorem ChainHamiltonian.exists_uniform_leading_bounds_of_isViable
    (h : ChainHamiltonian L q 1 1) (hpos : ∀ X, (h.term X).PosSemidef)
    (hL : 0 < L) (hq : 2 ≤ q) {E₀ Δ : ℝ} (hΔ : 0 < Δ)
    (HL B : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hsplit : h.operator = HL + B)
    (hHL : Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) HL (leftBlock L k))
    (hBS : Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) B (leftBlock L (k - 1))ᶜ)
    (hBn : ‖B‖ ≤ 2 * L)
    {Γ : EuclideanSpace ℂ (Fin L → Fin q)}
    (hgs : IsGappedGroundState h.operator E₀ Γ Δ)
    {S : Set (LeftBlockVector L q k)}
    (hviable : IsViable Γ (((Δ / 169) ^ 2) / L) S) :
    let : NeZero q := ⟨by omega⟩
    let c : ℝ := (Δ / 169) ^ 2
    let D := constantCutBond q 1 1 Δ c
    let P := reindex
      (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
      (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
      (spanProjection S)
    ∃ (w : EuclideanSpace ℂ (Fin L → Fin q)) (m : ℕ)
      (W : Matrix (CutRight L q k) (Fin m) ℂ)
      (x : (CutLeft L q k × CutSite L q k) × Fin m → ℂ),
      ‖w‖ = 1 ∧ w ∈ leftSupportSubmodule S ∧
      (cutMatrix w k).rank ≤ D ∧
      (⟪w, toEuclideanLin h.operator w⟫_ℂ).re ≤ E₀ + 6 * √c ∧
      Wᴴ * W = 1 ∧ m ≤ D ∧
      WithLp.ofLp w ∘ (gluingCut L q k).symm =
        ((1 : Matrix (CutLeft L q k × CutSite L q k)
          (CutLeft L q k × CutSite L q k) ℂ) ⊗ₖ W) *ᵥ x ∧
      ‖WithLp.toLp 2 x‖ = 1 ∧ (P ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)) *ᵥ x = x ∧
      ∀ X : Matrix (CutSite L q k × Fin m) (CutSite L q k × Fin m) ℂ,
        rectangularTraceNorm (partialTraceFirst (vecMulVec x (star x)) - X) ≤ c / (2 * L) →
        ∀ σ : Matrix ((CutLeft L q k × CutSite L q k) × Fin m)
            ((CutLeft L q k × CutSite L q k) × Fin m) ℂ,
          σ.PosSemidef → σ.trace = 1 →
          (P ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)) * σ = σ →
          rectangularTraceNorm (partialTraceFirst σ - X) ≤ c / (2 * L) →
          (∀ ρ : Matrix ((CutLeft L q k × CutSite L q k) × Fin m)
              ((CutLeft L q k × CutSite L q k) × Fin m) ℂ,
            ρ.PosSemidef → ρ.trace = 1 →
            (P ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)) * ρ = ρ →
            rectangularTraceNorm (partialTraceFirst ρ - X) ≤ c / (2 * L) →
            (σ * (leftCutOperator k HL ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ))).trace.re ≤
              (ρ * (leftCutOperator k HL ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ))).trace.re) →
          ∀ (u : EuclideanSpace ℂ ((CutLeft L q k × CutSite L q k) × Fin m)) (μ : ℝ),
            ‖u‖ = 1 → σ *ᵥ WithLp.ofLp u = (μ : ℂ) • WithLp.ofLp u →
            (∀ (ν : ℝ) (z : EuclideanSpace ℂ ((CutLeft L q k × CutSite L q k) × Fin m)),
              z ≠ 0 → σ *ᵥ WithLp.ofLp z = (ν : ℂ) • WithLp.ofLp z → ν ≤ μ) →
            let v : EuclideanSpace ℂ (Fin L → Fin q) := WithLp.toLp 2
              ((((1 : Matrix (CutLeft L q k × CutSite L q k)
                (CutLeft L q k × CutSite L q k) ℂ) ⊗ₖ W) *ᵥ WithLp.ofLp u) ∘ gluingCut L q k)
            1 / 2 < μ ∧
            (P ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)) *ᵥ WithLp.ofLp u = WithLp.ofLp u ∧
            ‖v‖ = 1 ∧ v ∈ leftSupportSubmodule S ∧
            (⟪v, toEuclideanLin h.operator v⟫_ℂ).re ≤ E₀ + Δ / 12 ∧
            1 - 1 / 12 ≤ ‖⟪Γ, v⟫_ℂ‖ := by
  classical
  let : NeZero q := ⟨by omega⟩
  let c : ℝ := (Δ / 169) ^ 2
  let D := constantCutBond q 1 1 Δ c
  let P := reindex
    (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
    (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
    (spanProjection S)
  obtain ⟨_, _, w, m, W, x, -, -, -, -, hw, hwS, hwD, hwE, hW, hmD,
      hwx, hxnorm, hxP, -⟩ :=
    h.exists_boundary_minimizer_leading_vector_of_isViable hpos hL hq hΔ hgs hviable
  refine ⟨w, m, W, x, hw, hwS, hwD, hwE, hW, hmD,
    hwx, hxnorm, hxP, ?_⟩
  intro X hX σ hσ htr hσP hσX hmin u μ hu huσ hmax
  let ρx := vecMulVec x (star x)
  have hρxp : ρx.PosSemidef := posSemidef_vecMulVec_self_star x
  have hρxt : ρx.trace = 1 := by
    change (vecMulVec (WithLp.ofLp (WithLp.toLp 2 x))
      (star (WithLp.ofLp (WithLp.toLp 2 x)))).trace = 1
    rw [trace_vecMulVec, ← EuclideanSpace.inner_eq_star_dotProduct,
      inner_self_eq_norm_sq_to_K, hxnorm]
    norm_num
  have hρxP : (P ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)) * ρx = ρx := by
    dsimp only [ρx]
    rw [mul_vecMulVec, hxP]
  have hopt := hmin ρx hρxp hρxt hρxP hX
  let η := c / (2 * L)
  change rectangularTraceNorm (partialTraceFirst ρx - X) ≤ η at hX
  change rectangularTraceNorm (partialTraceFirst σ - X) ≤ η at hσX
  have hneg : rectangularTraceNorm (X - partialTraceFirst ρx) =
      rectangularTraceNorm (partialTraceFirst ρx - X) := by
    rw [show X - partialTraceFirst ρx = (-1 : ℂ) • (partialTraceFirst ρx - X) by
      simp, rectangularTraceNorm_smul]
    norm_num
  have hτ : rectangularTraceNorm (partialTraceFirst σ - partialTraceFirst ρx) ≤ 2 * η := by
    calc
      rectangularTraceNorm (partialTraceFirst σ - partialTraceFirst ρx) =
          rectangularTraceNorm ((partialTraceFirst σ - X) + (X - partialTraceFirst ρx)) := by
            rw [sub_add_sub_cancel]
      _ ≤ rectangularTraceNorm (partialTraceFirst σ - X) +
          rectangularTraceNorm (X - partialTraceFirst ρx) := rectangularTraceNorm_add_le _ _
      _ ≤ 2 * η := by rw [hneg]; linarith only [hσX, hX]
  have hΔ4 : Δ ≤ 4 := by
    simpa only [mul_one] using h.gap_le_four_mul_of_range_one hL hq hgs
  have hsqrt : √c = Δ / 169 := Real.sqrt_sq (div_nonneg hΔ.le (by norm_num))
  have hcr : 2 * c ≤ √c := by
    rw [hsqrt]
    dsimp only [c]
    nlinarith only [mul_nonneg hΔ.le (sub_nonneg.mpr hΔ4), hΔ]
  have hL0 : (L : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hL.ne'
  have hηeq : 2 * η = c / L := by dsimp only [η]; field_simp [hL0]
  have hBτ : ‖B‖ * (2 * η) ≤ 2 * c := by
    rw [hηeq]
    calc
      ‖B‖ * (c / L) ≤ (2 * L) * (c / L) :=
        mul_le_mul_of_nonneg_right hBn (div_nonneg (sq_nonneg _) (Nat.cast_nonneg _))
      _ = 2 * c := by field_simp [hL0]
  have htwo : 2 * (6 * √c + ‖B‖ * (2 * η)) ≤ 14 * √c := by
    linarith only [hBτ, hcr]
  have hgood : 14 * √c < Δ / 12 := by rw [hsqrt]; linarith only [hΔ]
  have h4 : 4 * (6 * √c + ‖B‖ * (2 * η)) < Δ := by
    linarith only [htwo, hgood, hΔ]
  have hgs' : IsGappedGroundState (HL + B) E₀ Γ Δ := by rw [← hsplit]; exact hgs
  have hwE' : (⟪w, toEuclideanLin (HL + B) w⟫_ℂ).re ≤ E₀ + 6 * √c := by
    rw [← hsplit]
    exact hwE
  obtain ⟨u₀, ν, hu₀, hu₀σ, hν, -, -⟩ :=
    exists_leading_eigenvector_chain (L := L) (q := q) (k := k) (e := 6 * √c) (τ := 2 * η)
      hHL hBS disjoint_compl_left hΔ hgs' W hW x hwx hwE' hσ htr hopt hτ h4
  have hu₀0 : u₀ ≠ 0 := by
    intro hz
    simp only [hz, norm_zero, zero_ne_one] at hu₀
  have hμ : 1 / 2 < μ := hν.trans_le (hmax ν u₀ hu₀0 hu₀σ)
  obtain ⟨huE, huov⟩ :=
    leading_eigenvector_bounds_chain (L := L) (q := q) (k := k) (e := 6 * √c) (τ := 2 * η)
      hHL hBS disjoint_compl_left hΔ hgs' W hW x hwx hwE' hσ htr hopt hτ h4 u μ hu huσ hμ
  have hμ0 : (μ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith only [hμ])
  have hQu : (P ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)) *ᵥ WithLp.ofLp u =
      WithLp.ofLp u := by
    apply smul_right_injective _ hμ0
    simpa only [← mulVec_mulVec, huσ, mulVec_smul] using
      congrArg (fun A ↦ A *ᵥ WithLp.ofLp u) hσP
  let J := (1 : Matrix (CutLeft L q k × CutSite L q k)
    (CutLeft L q k × CutSite L q k) ℂ) ⊗ₖ W
  have hJ : Jᴴ * J = 1 := by
    simp only [J, conjTranspose_kronecker, conjTranspose_one, ← mul_kronecker_mul,
      Matrix.one_mul, hW, one_kronecker_one]
  let v := WithLp.toLp 2 ((J *ᵥ WithLp.ofLp u) ∘ gluingCut L q k)
  have hv : ‖v‖ = 1 :=
    ((LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (gluingCut L q k).symm).norm_map
      (WithLp.toLp 2 (J *ᵥ WithLp.ofLp u))).trans
        ((norm_toLp_mulVec_of_isometry J hJ u).trans hu)
  have hinter : (P ⊗ₖ (1 : Matrix (CutRight L q k) (CutRight L q k) ℂ)) * J =
      J * (P ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)) := by
    simp only [J, ← mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul]
  have hvP : (P ⊗ₖ (1 : Matrix (CutRight L q k) (CutRight L q k) ℂ)) *ᵥ
      (J *ᵥ WithLp.ofLp u) = J *ᵥ WithLp.ofLp u := by
    rw [mulVec_mulVec, hinter, ← mulVec_mulVec, hQu]
  have hvS : v ∈ leftSupportSubmodule S :=
    mem_leftSupportSubmodule_of_gluingCut_fixed S (J *ᵥ WithLp.ofLp u) hvP
  refine ⟨hμ, hQu, hv, hvS, ?_, ?_⟩
  · rw [← hsplit] at huE
    exact huE.trans (add_le_add le_rfl (htwo.trans hgood.le))
  · have herr : 2 * (6 * √c + ‖B‖ * (2 * η)) / Δ ≤ 1 / 12 := by
      apply (div_le_iff₀ hΔ).mpr
      linarith only [htwo, hgood]
    linarith only [huov, herr]

/-- A numerically feasible boundary density gives the same LVV viable-vector bounds provided
the combined objective and boundary errors fit in the unused constant margin.  Here `ξ` is
the additive left-energy error and `δ` is the enlargement of the boundary tolerance.  The
condition `2 * (ξ + ‖B‖ * δ) ≤ Δ / 2028` is exactly the margin between
`14 * (Δ / 169)` and `Δ / 12`. -/
theorem ChainHamiltonian.leading_bounds_of_approximate_boundary_solution [NeZero q]
    (h : ChainHamiltonian L q 1 1) (hL : 0 < L) (hq : 2 ≤ q)
    {E₀ Δ : ℝ} (hΔ : 0 < Δ)
    (HL B : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hsplit : h.operator = HL + B)
    (hHL : Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) HL (leftBlock L k))
    (hBS : Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) B (leftBlock L (k - 1))ᶜ)
    (hBn : ‖B‖ ≤ 2 * L) {Γ : EuclideanSpace ℂ (Fin L → Fin q)}
    (hgs : IsGappedGroundState h.operator E₀ Γ Δ) {S : Set (LeftBlockVector L q k)}
    {m : ℕ} (W : Matrix (CutRight L q k) (Fin m) ℂ) (hW : Wᴴ * W = 1)
    (x : (CutLeft L q k × CutSite L q k) × Fin m → ℂ)
    {w : EuclideanSpace ℂ (Fin L → Fin q)} (hwx : WithLp.ofLp w ∘ (gluingCut L q k).symm =
      ((1 : Matrix (CutLeft L q k × CutSite L q k)
        (CutLeft L q k × CutSite L q k) ℂ) ⊗ₖ W) *ᵥ x)
    (hwE : (⟪w, toEuclideanLin h.operator w⟫_ℂ).re ≤ E₀ + 6 * √((Δ / 169) ^ 2))
    (X : Matrix (CutSite L q k × Fin m) (CutSite L q k × Fin m) ℂ)
    (hX : rectangularTraceNorm (partialTraceFirst (vecMulVec x (star x)) - X) ≤
      ((Δ / 169) ^ 2) / (2 * L))
    {δ ξ : ℝ} (herr : 2 * (ξ + ‖B‖ * δ) ≤ Δ / 2028)
    {σ : Matrix ((CutLeft L q k × CutSite L q k) × Fin m)
      ((CutLeft L q k × CutSite L q k) × Fin m) ℂ}
    (hσ : σ.PosSemidef) (htr : σ.trace = 1)
    (hσP : (reindex
        (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
        (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
        (spanProjection S) ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)) * σ = σ)
    (hσX : rectangularTraceNorm (partialTraceFirst σ - X) ≤
      ((Δ / 169) ^ 2) / (2 * L) + δ)
    (hopt : (σ * (leftCutOperator k HL ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ))).trace.re ≤
      (vecMulVec x (star x) *
        (leftCutOperator k HL ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ))).trace.re + ξ)
    (u : EuclideanSpace ℂ ((CutLeft L q k × CutSite L q k) × Fin m)) (μ : ℝ)
    (hu : ‖u‖ = 1) (huσ : σ *ᵥ WithLp.ofLp u = (μ : ℂ) • WithLp.ofLp u)
    (hmax : ∀ (ν : ℝ) (z : EuclideanSpace ℂ ((CutLeft L q k × CutSite L q k) × Fin m)),
      z ≠ 0 → σ *ᵥ WithLp.ofLp z = (ν : ℂ) • WithLp.ofLp z → ν ≤ μ) :
    let P := reindex
      (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
      (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
      (spanProjection S)
    let v : EuclideanSpace ℂ (Fin L → Fin q) := WithLp.toLp 2
      ((((1 : Matrix (CutLeft L q k × CutSite L q k)
        (CutLeft L q k × CutSite L q k) ℂ) ⊗ₖ W) *ᵥ WithLp.ofLp u) ∘ gluingCut L q k)
    1 / 2 < μ ∧ (P ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)) *ᵥ WithLp.ofLp u = WithLp.ofLp u ∧
      ‖v‖ = 1 ∧ v ∈ leftSupportSubmodule S ∧
      (⟪v, toEuclideanLin h.operator v⟫_ℂ).re ≤ E₀ + Δ / 12 ∧
      1 - 1 / 12 ≤ ‖⟪Γ, v⟫_ℂ‖ ∧
      (⟪v, toEuclideanLin h.operator v⟫_ℂ).re ≤ E₀ +
        2 * (6 * (Δ / 169) + ξ + ‖B‖ *
          (2 * (((Δ / 169) ^ 2) / (2 * L)) + δ)) ∧
      1 - 2 * (6 * (Δ / 169) + ξ + ‖B‖ *
          (2 * (((Δ / 169) ^ 2) / (2 * L)) + δ)) / Δ ≤ ‖⟪Γ, v⟫_ℂ‖ ∧
      1 - (6 * (Δ / 169) + ξ + ‖B‖ *
          (2 * (((Δ / 169) ^ 2) / (2 * L)) + δ)) / Δ ≤ μ := by
  classical
  let c : ℝ := (Δ / 169) ^ 2
  let η := c / (2 * L)
  let P := reindex
    (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
    (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
    (spanProjection S)
  let ρx := vecMulVec x (star x)
  change rectangularTraceNorm (partialTraceFirst ρx - X) ≤ η at hX
  change rectangularTraceNorm (partialTraceFirst σ - X) ≤ η + δ at hσX
  change (P ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)) * σ = σ at hσP
  have hneg : rectangularTraceNorm (X - partialTraceFirst ρx) =
      rectangularTraceNorm (partialTraceFirst ρx - X) := by
    rw [show X - partialTraceFirst ρx = (-1 : ℂ) • (partialTraceFirst ρx - X) by
      simp, rectangularTraceNorm_smul]
    norm_num
  have hτ : rectangularTraceNorm (partialTraceFirst σ - partialTraceFirst ρx) ≤
      2 * η + δ := by
    calc
      rectangularTraceNorm (partialTraceFirst σ - partialTraceFirst ρx) =
          rectangularTraceNorm ((partialTraceFirst σ - X) +
            (X - partialTraceFirst ρx)) := by rw [sub_add_sub_cancel]
      _ ≤ rectangularTraceNorm (partialTraceFirst σ - X) +
          rectangularTraceNorm (X - partialTraceFirst ρx) := rectangularTraceNorm_add_le _ _
      _ ≤ 2 * η + δ := by rw [hneg]; linarith only [hσX, hX]
  have hΔ4 : Δ ≤ 4 := by
    simpa only [mul_one] using h.gap_le_four_mul_of_range_one hL hq hgs
  have hsqrt : √c = Δ / 169 := Real.sqrt_sq (div_nonneg hΔ.le (by norm_num))
  have hcr : 2 * c ≤ √c := by
    rw [hsqrt]
    dsimp only [c]
    nlinarith only [mul_nonneg hΔ.le (sub_nonneg.mpr hΔ4), hΔ]
  have hL0 : (L : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hL.ne'
  have hηeq : 2 * η = c / L := by dsimp only [η]; field_simp [hL0]
  have hBτ : ‖B‖ * (2 * η) ≤ 2 * c := by
    rw [hηeq]
    calc
      ‖B‖ * (c / L) ≤ (2 * L) * (c / L) :=
        mul_le_mul_of_nonneg_right hBn (div_nonneg (sq_nonneg _) (Nat.cast_nonneg _))
      _ = 2 * c := by field_simp [hL0]
  have hbase : 2 * (6 * √c + ‖B‖ * (2 * η)) ≤ 14 * √c := by
    linarith only [hBτ, hcr]
  have htotal : 2 * (6 * √c + ξ + ‖B‖ * (2 * η + δ)) ≤ Δ / 12 := by
    calc
      2 * (6 * √c + ξ + ‖B‖ * (2 * η + δ)) =
          2 * (6 * √c + ‖B‖ * (2 * η)) + 2 * (ξ + ‖B‖ * δ) := by ring
      _ ≤ 14 * √c + Δ / 2028 := add_le_add hbase herr
      _ = Δ / 12 := by rw [hsqrt]; ring
  have h4 : 4 * (6 * √c + ξ + ‖B‖ * (2 * η + δ)) < Δ := by
    nlinarith only [htotal, hΔ]
  have hgs' : IsGappedGroundState (HL + B) E₀ Γ Δ := by rw [← hsplit]; exact hgs
  have hwE' : (⟪w, toEuclideanLin (HL + B) w⟫_ℂ).re ≤ E₀ + 6 * √c := by
    rw [← hsplit]
    exact hwE
  obtain ⟨u₀, ν, hu₀, hu₀σ, hν, -, -⟩ :=
    exists_leading_eigenvector_chain_with_objective_slack
      (L := L) (q := q) (k := k) (e := 6 * √c) (τ := 2 * η + δ) (ξ := ξ)
      hHL hBS disjoint_compl_left hΔ hgs' W hW x hwx hwE' hσ htr hopt hτ h4
  have hu₀0 : u₀ ≠ 0 := by
    intro hz
    simp only [hz, norm_zero, zero_ne_one] at hu₀
  have hμ : 1 / 2 < μ := hν.trans_le (hmax ν u₀ hu₀0 hu₀σ)
  have hμquant := maxEigenvalue_lower_bound_chain_with_objective_slack
    hHL hBS disjoint_compl_left hΔ hgs' W hW x hwx hwE' hσ htr hopt hτ hmax
  obtain ⟨huE, huov⟩ :=
    leading_eigenvector_bounds_chain_with_objective_slack
      (L := L) (q := q) (k := k) (e := 6 * √c) (τ := 2 * η + δ) (ξ := ξ)
      hHL hBS disjoint_compl_left hΔ hgs' W hW x hwx hwE' hσ htr hopt hτ h4
      u μ hu huσ hμ
  have hμ0 : (μ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith only [hμ])
  have hQu : (P ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)) *ᵥ WithLp.ofLp u =
      WithLp.ofLp u := by
    apply smul_right_injective _ hμ0
    simpa only [← mulVec_mulVec, huσ, mulVec_smul] using
      congrArg (fun A ↦ A *ᵥ WithLp.ofLp u) hσP
  let J := (1 : Matrix (CutLeft L q k × CutSite L q k)
    (CutLeft L q k × CutSite L q k) ℂ) ⊗ₖ W
  have hJ : Jᴴ * J = 1 := by
    simp only [J, conjTranspose_kronecker, conjTranspose_one, ← mul_kronecker_mul,
      Matrix.one_mul, hW, one_kronecker_one]
  let v := WithLp.toLp 2 ((J *ᵥ WithLp.ofLp u) ∘ gluingCut L q k)
  have hv : ‖v‖ = 1 :=
    ((LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (gluingCut L q k).symm).norm_map
      (WithLp.toLp 2 (J *ᵥ WithLp.ofLp u))).trans
        ((norm_toLp_mulVec_of_isometry J hJ u).trans hu)
  have hinter : (P ⊗ₖ (1 : Matrix (CutRight L q k) (CutRight L q k) ℂ)) * J =
      J * (P ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)) := by
    simp only [J, ← mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul]
  have hvP : (P ⊗ₖ (1 : Matrix (CutRight L q k) (CutRight L q k) ℂ)) *ᵥ
      (J *ᵥ WithLp.ofLp u) = J *ᵥ WithLp.ofLp u := by
    rw [mulVec_mulVec, hinter, ← mulVec_mulVec, hQu]
  have hvS : v ∈ leftSupportSubmodule S :=
    mem_leftSupportSubmodule_of_gluingCut_fixed S (J *ᵥ WithLp.ofLp u) hvP
  refine ⟨hμ, hQu, hv, hvS, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hsplit] at huE
    exact huE.trans (add_le_add le_rfl htotal)
  · have hover : 2 * (6 * √c + ξ + ‖B‖ * (2 * η + δ)) / Δ ≤ 1 / 12 :=
      (div_le_iff₀ hΔ).2 (by nlinarith only [htotal])
    linarith only [huov, hover]
  · rw [← hsplit] at huE
    simpa only [hsqrt, c, η] using huE
  · simpa only [hsqrt, c, η] using huov
  · simpa only [hsqrt, c, η] using hμquant

end TNLean.MPS.AreaLaw
