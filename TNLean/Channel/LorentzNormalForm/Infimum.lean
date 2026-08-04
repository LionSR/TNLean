/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Analysis.MatrixTraceInequalities
import TNLean.Analysis.MatrixSqrt
import TNLean.Algebra.HermitianHelpers
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Order
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Lorentz normal form: infimum attainment and the AM–GM optimality lemmas

This module formalizes the compactness and optimality arguments of Wolf
Section 2.3 (Equation (2.36)): for a positive-definite operator `τ` on
`ℂ^{d₂} ⊗ ℂ^{d₁}`, the infimum of `tr[(S₂ ⊗ₖ S₁) τ (S₂ ⊗ₖ S₁)†]` over
`(S₁, S₂) ∈ SL(d₁, ℂ) × SL(d₂, ℂ)` is attained, and at the minimiser each
partial trace saturates the trace–determinant AM–GM bound, hence is scalar.

## Main results

* `Wolf.exists_sl_normalize` — an `SL(D, ℂ)` congruence normalizes a
  positive-definite matrix to a scalar matrix
* `Wolf.posDef_orbit_min_isScalar` — the AM–GM equality case: a
  trace-minimising determinant-preserving congruence orbit point is scalar
* `Wolf.infimum_is_attained` — the infimum is attained (extreme value theorem
  on a compact Frobenius ball; coercivity from the smallest-eigenvalue bound
  and the determinant AM–GM estimate)

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Section 2.3][Wolf2012QChannels]
-/

open scoped Matrix BigOperators ComplexOrder Kronecker Matrix.Norms.Frobenius
open Matrix Finset

namespace Wolf

section InfimumAttainment

variable {D : ℕ}

/-- **Key lemma.**  For a positive-definite Choi matrix τ on
`ℂ^{d₂} ⊗ ℂ^{d₁}`, the infimum of `tr[(S₂ ⊗ₖ S₁) τ (S₂ ⊗ₖ S₁)†]` over
`S₁ ∈ SL(d₁, ℂ)`, `S₂ ∈ SL(d₂, ℂ)` is attained.  That is, the continuous
function `(S₁, S₂) ↦ tr[(S₂ ⊗ₖ S₁) τ (S₂ ⊗ₖ S₁)†]` achieves its minimum on
the domain SL(d₁, ℂ) × SL(d₂, ℂ) — the two factors may have different
dimensions (Wolf, Section 2.3, Equation (2.36)).

**Proof** (Wolf Section 2.3).  Throughout, `‖·‖` denotes the Frobenius
(Hilbert–Schmidt) norm `‖M‖² = tr[M M†]`; the coercivity bounds below are false
for the operator norm (e.g. `‖I‖_op² = 1 < n`).  Writing `X = S₂ ⊗ₖ S₁`, the
smallest-eigenvalue bound for a positive-definite matrix gives
`λ_min(τ) · tr[Xᴴ X] ≤ tr[X τ Xᴴ]`, Hilbert–Schmidt multiplicativity of the
Kronecker product gives `tr[Xᴴ X] = tr[S₂ᴴ S₂] · tr[S₁ᴴ S₁]`, and the determinant
AM–GM estimate gives `tr[Sᵢᴴ Sᵢ] = ‖Sᵢ‖² ≥ dᵢ` whenever `det Sᵢ = 1`.
Combining these, `tr[X τ Xᴴ] ≥ λ_min(τ) · d₂ · ‖S₁‖²` and
`tr[X τ Xᴴ] ≥ λ_min(τ) · d₁ · ‖S₂‖²`, so any minimiser is confined to bounded
sets `{S₁ | ‖S₁‖ ≤ C₁}`, `{S₂ | ‖S₂‖ ≤ C₂}`.  Intersecting with the closed
set
`det S = 1` gives a compact set on which the continuous trace functional attains
its minimum by the extreme value theorem; a value outside the sublevel set is
automatically larger than the value at the identity, so this minimiser is
global. -/

lemma infimum_is_attained
    {d₁ d₂ : ℕ} {τ : Matrix (Fin d₂ × Fin d₁) (Fin d₂ × Fin d₁) ℂ}
    (hτ_posDef : τ.PosDef) :
    ∃ (S₁ : Matrix (Fin d₁) (Fin d₁) ℂ) (S₂ : Matrix (Fin d₂) (Fin d₂) ℂ),
      S₁.det = 1 ∧ S₂.det = 1 ∧
      ∀ (T₁ : Matrix (Fin d₁) (Fin d₁) ℂ) (T₂ : Matrix (Fin d₂) (Fin d₂) ℂ),
        T₁.det = 1 → T₂.det = 1 →
        (Matrix.trace (((T₂ ⊗ₖ T₁) * τ * ((T₂ ⊗ₖ T₁)ᴴ)))).re ≥
          (Matrix.trace (((S₂ ⊗ₖ S₁) * τ * ((S₂ ⊗ₖ S₁)ᴴ)))).re := by
  classical
  -- The degenerate cases: if either dimension is zero, the matrices live on an
  -- empty index type and every trace vanishes.
  rcases Nat.eq_zero_or_pos d₁ with hD₁ | hD₁
  · subst hD₁
    refine ⟨1, 1, Matrix.det_one, Matrix.det_one, ?_⟩
    intro T₁ T₂ _ _
    simp [Matrix.trace, Matrix.diag]
  rcases Nat.eq_zero_or_pos d₂ with hD₂ | hD₂
  · subst hD₂
    refine ⟨1, 1, Matrix.det_one, Matrix.det_one, ?_⟩
    intro T₁ T₂ _ _
    simp [Matrix.trace, Matrix.diag]
  haveI : Nonempty (Fin d₁) := ⟨⟨0, hD₁⟩⟩
  haveI : Nonempty (Fin d₂) := ⟨⟨0, hD₂⟩⟩
  haveI : Nonempty (Fin d₂ × Fin d₁) := ⟨(⟨0, hD₂⟩, ⟨0, hD₁⟩)⟩
  haveI : ProperSpace
      (Matrix (Fin d₁) (Fin d₁) ℂ × Matrix (Fin d₂) (Fin d₂) ℂ) :=
    FiniteDimensional.proper_rclike ℂ _
  -- The functional to minimise, as a function of the pair `(S₁, S₂)`.
  let g : Matrix (Fin d₁) (Fin d₁) ℂ × Matrix (Fin d₂) (Fin d₂) ℂ → ℝ :=
    fun p => (Matrix.trace ((p.2 ⊗ₖ p.1) * τ * ((p.2 ⊗ₖ p.1)ᴴ))).re
  set lam : ℝ := minEigenvalue hτ_posDef.isHermitian with hlam_def
  have hlam : 0 < lam := minEigenvalue_pos_of_posDef hτ_posDef.isHermitian hτ_posDef
  set cardR₁ : ℝ := (Fintype.card (Fin d₁) : ℝ) with hcardR₁
  set cardR₂ : ℝ := (Fintype.card (Fin d₂) : ℝ) with hcardR₂
  have hcardR₁_pos : 0 < cardR₁ := by
    rw [hcardR₁]; exact_mod_cast Fintype.card_pos
  have hcardR₂_pos : 0 < cardR₂ := by
    rw [hcardR₂]; exact_mod_cast Fintype.card_pos
  -- Coercivity: the value dominates `λ · ‖S₂‖² · ‖S₁‖²`.
  have key : ∀ (S₁ : Matrix (Fin d₁) (Fin d₁) ℂ)
      (S₂ : Matrix (Fin d₂) (Fin d₂) ℂ),
      lam * ((Matrix.trace (S₂ᴴ * S₂)).re * (Matrix.trace (S₁ᴴ * S₁)).re) ≤
        g (S₁, S₂) := by
    intro S₁ S₂
    have hle := (Complex.le_def.mp
      (posDef_minEigenvalue_mul_trace_conjTranspose_mul_self_le hτ_posDef (S₂ ⊗ₖ S₁))).1
    rw [Complex.re_ofReal_mul, trace_conjTranspose_mul_self_re_kronecker] at hle
    exact hle
  -- The bound at the identity confines minimisers to Frobenius balls (one per
  -- factor, since the two dimensions may differ).
  set B : ℝ := g (1, 1) with hB
  set C₁ : ℝ := Real.sqrt (B / (lam * cardR₂)) with hC₁
  set C₂ : ℝ := Real.sqrt (B / (lam * cardR₁)) with hC₂
  have hbound : ∀ (S₁ : Matrix (Fin d₁) (Fin d₁) ℂ)
      (S₂ : Matrix (Fin d₂) (Fin d₂) ℂ), S₁.det = 1 → S₂.det = 1 →
      g (S₁, S₂) ≤ B → ‖S₁‖ ≤ C₁ ∧ ‖S₂‖ ≤ C₂ := by
    intro S₁ S₂ h1 h2 hgB
    have hd1 : ‖S₁.det‖ = 1 := by rw [h1]; simp
    have hd2 : ‖S₂.det‖ = 1 := by rw [h2]; simp
    have hn1 : cardR₁ ≤ (Matrix.trace (S₁ᴴ * S₁)).re :=
      card_le_trace_conjTranspose_mul_self_re_of_det_norm_eq_one S₁ hd1
    have hn2 : cardR₂ ≤ (Matrix.trace (S₂ᴴ * S₂)).re :=
      card_le_trace_conjTranspose_mul_self_re_of_det_norm_eq_one S₂ hd2
    have ht1 : 0 ≤ (Matrix.trace (S₁ᴴ * S₁)).re := hcardR₁_pos.le.trans hn1
    have ht2 : 0 ≤ (Matrix.trace (S₂ᴴ * S₂)).re := hcardR₂_pos.le.trans hn2
    have hδ₁ : 0 < lam * cardR₂ := mul_pos hlam hcardR₂_pos
    have hδ₂ : 0 < lam * cardR₁ := mul_pos hlam hcardR₁_pos
    -- Bound on `‖S₁‖`.
    have hsq1 : ‖S₁‖ ^ 2 ≤ B / (lam * cardR₂) := by
      have hchain : (lam * cardR₂) * (Matrix.trace (S₁ᴴ * S₁)).re ≤ B := by
        calc (lam * cardR₂) * (Matrix.trace (S₁ᴴ * S₁)).re
            = lam * (cardR₂ * (Matrix.trace (S₁ᴴ * S₁)).re) := by ring
          _ ≤ lam * ((Matrix.trace (S₂ᴴ * S₂)).re *
              (Matrix.trace (S₁ᴴ * S₁)).re) := by
                exact mul_le_mul_of_nonneg_left
                  (mul_le_mul_of_nonneg_right hn2 ht1) hlam.le
          _ ≤ g (S₁, S₂) := key S₁ S₂
          _ ≤ B := hgB
      rw [← trace_conjTranspose_mul_self_re_eq_frobenius_norm_sq, le_div_iff₀ hδ₁, mul_comm]
      exact hchain
    have hsq2 : ‖S₂‖ ^ 2 ≤ B / (lam * cardR₁) := by
      have hchain : (lam * cardR₁) * (Matrix.trace (S₂ᴴ * S₂)).re ≤ B := by
        calc (lam * cardR₁) * (Matrix.trace (S₂ᴴ * S₂)).re
            = lam * ((Matrix.trace (S₂ᴴ * S₂)).re * cardR₁) := by ring
          _ ≤ lam * ((Matrix.trace (S₂ᴴ * S₂)).re *
              (Matrix.trace (S₁ᴴ * S₁)).re) := by
                exact mul_le_mul_of_nonneg_left
                  (mul_le_mul_of_nonneg_left hn1 ht2) hlam.le
          _ ≤ g (S₁, S₂) := key S₁ S₂
          _ ≤ B := hgB
      rw [← trace_conjTranspose_mul_self_re_eq_frobenius_norm_sq, le_div_iff₀ hδ₂, mul_comm]
      exact hchain
    refine ⟨?_, ?_⟩
    · rw [hC₁, ← Real.sqrt_sq (norm_nonneg S₁)]; exact Real.sqrt_le_sqrt hsq1
    · rw [hC₂, ← Real.sqrt_sq (norm_nonneg S₂)]; exact Real.sqrt_le_sqrt hsq2
  -- The compact constraint set.
  set Kc : Set (Matrix (Fin d₁) (Fin d₁) ℂ × Matrix (Fin d₂) (Fin d₂) ℂ) :=
    {p | p.1.det = 1 ∧ p.2.det = 1 ∧ ‖p.1‖ ≤ C₁ ∧ ‖p.2‖ ≤ C₂} with hKc
  have hgcont : Continuous g := by
    have hk : Continuous fun p : Matrix (Fin d₁) (Fin d₁) ℂ ×
        Matrix (Fin d₂) (Fin d₂) ℂ =>
        p.2 ⊗ₖ p.1 := Continuous.matrix_kronecker continuous_snd continuous_fst
    exact Complex.continuous_re.comp
      ((hk.matrix_mul continuous_const).matrix_mul hk.matrix_conjTranspose).matrix_trace
  have hclosed : IsClosed Kc := by
    have c1 : IsClosed {p : Matrix (Fin d₁) (Fin d₁) ℂ × Matrix (Fin d₂) (Fin d₂) ℂ |
        p.1.det = 1} :=
      isClosed_eq continuous_fst.matrix_det continuous_const
    have c2 : IsClosed {p : Matrix (Fin d₁) (Fin d₁) ℂ × Matrix (Fin d₂) (Fin d₂) ℂ |
        p.2.det = 1} :=
      isClosed_eq continuous_snd.matrix_det continuous_const
    have c3 : IsClosed {p : Matrix (Fin d₁) (Fin d₁) ℂ × Matrix (Fin d₂) (Fin d₂) ℂ |
        ‖p.1‖ ≤ C₁} :=
      isClosed_le (continuous_norm.comp continuous_fst) continuous_const
    have c4 : IsClosed {p : Matrix (Fin d₁) (Fin d₁) ℂ × Matrix (Fin d₂) (Fin d₂) ℂ |
        ‖p.2‖ ≤ C₂} :=
      isClosed_le (continuous_norm.comp continuous_snd) continuous_const
    have hset : Kc = {p | p.1.det = 1} ∩ {p | p.2.det = 1} ∩
        {p | ‖p.1‖ ≤ C₁} ∩ {p | ‖p.2‖ ≤ C₂} := by
      rw [hKc]; ext p; simp only [Set.mem_inter_iff, Set.mem_setOf_eq]; tauto
    rw [hset]; exact ((c1.inter c2).inter c3).inter c4
  have hbdd : Bornology.IsBounded Kc := by
    refine (Metric.isBounded_closedBall (x := (0 : Matrix (Fin d₁) (Fin d₁) ℂ ×
      Matrix (Fin d₂) (Fin d₂) ℂ)) (r := max C₁ C₂)).subset ?_
    intro p hp
    rw [hKc, Set.mem_setOf_eq] at hp
    rw [Metric.mem_closedBall]
    calc dist p 0 = max (dist p.1 0) (dist p.2 0) := Prod.dist_eq
      _ = max ‖p.1‖ ‖p.2‖ := by rw [dist_zero_right, dist_zero_right]
      _ ≤ max C₁ C₂ := max_le_max hp.2.2.1 hp.2.2.2
  have hKcompact : IsCompact Kc := Metric.isCompact_of_isClosed_isBounded hclosed hbdd
  have h11mem : (1, 1) ∈ Kc := by
    rw [hKc, Set.mem_setOf_eq]
    obtain ⟨hc1, hc2⟩ := hbound 1 1 Matrix.det_one Matrix.det_one (le_of_eq hB.symm)
    exact ⟨Matrix.det_one, Matrix.det_one, hc1, hc2⟩
  obtain ⟨pmin, hpmin_mem, hpmin_min⟩ :=
    hKcompact.exists_isMinOn ⟨(1, 1), h11mem⟩ hgcont.continuousOn
  rw [hKc, Set.mem_setOf_eq] at hpmin_mem
  refine ⟨pmin.1, pmin.2, hpmin_mem.1, hpmin_mem.2.1, ?_⟩
  intro T₁ T₂ hT₁ hT₂
  by_cases hcase : g (T₁, T₂) ≤ B
  · have hmem : (T₁, T₂) ∈ Kc := by
      rw [hKc, Set.mem_setOf_eq]
      obtain ⟨hc1, hc2⟩ := hbound T₁ T₂ hT₁ hT₂ hcase
      exact ⟨hT₁, hT₂, hc1, hc2⟩
    exact isMinOn_iff.mp hpmin_min (T₁, T₂) hmem
  · have hpB : g pmin ≤ B := isMinOn_iff.mp hpmin_min (1, 1) h11mem
    exact le_trans hpB (le_of_lt (not_le.mp hcase))
end InfimumAttainment

section OrbitOptimality

variable {D : ℕ}

/-- A positive-definite matrix can be normalized to a scalar matrix by an
`SL(D, ℂ)` congruence: there exists `S` with `det S = 1` and
`S M S† = r • 1` for some `r ≥ 0`.  Take `S = c · √M⁻¹` with `cᴰ = det √M`. -/

lemma exists_sl_normalize [NeZero D] {M : Matrix (Fin D) (Fin D) ℂ}
    (hM : M.PosDef) :
    ∃ S : Matrix (Fin D) (Fin D) ℂ, S.det = 1 ∧
      ∃ r : ℝ, 0 ≤ r ∧ S * M * Sᴴ = (r : ℂ) • 1 := by
  classical
  set R : Matrix (Fin D) (Fin D) ℂ := hM.posSemidef.isHermitian.cfc Real.sqrt with hR_def
  have hR_herm : R.IsHermitian := hM.posSemidef.cfc_sqrt_isHermitian
  have hRR : R * R = M := hM.posSemidef.cfc_sqrt_mul_self
  have hMdet : M.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det M).mp hM.isUnit).ne_zero
  have hRdet : R.det ≠ 0 := by
    intro h; apply hMdet; rw [← hRR, Matrix.det_mul, h, zero_mul]
  have hRunit : IsUnit R.det := isUnit_iff_ne_zero.mpr hRdet
  have hDpos : 0 < D := Nat.pos_of_ne_zero (NeZero.ne D)
  obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq R.det hDpos
  refine ⟨c • R⁻¹, ?_, Complex.normSq c, Complex.normSq_nonneg c, ?_⟩
  · rw [Matrix.det_smul, Fintype.card_fin, Matrix.det_nonsing_inv, hc,
      Ring.mul_inverse_cancel _ hRunit]
  · have hRinvH : (R⁻¹)ᴴ = R⁻¹ := by rw [Matrix.conjTranspose_nonsing_inv, hR_herm.eq]
    have hRinvMul : R⁻¹ * M * R⁻¹ = 1 := by
      rw [← hRR]
      simp only [Matrix.mul_assoc]
      rw [Matrix.mul_nonsing_inv _ hRunit, Matrix.mul_one, Matrix.nonsing_inv_mul _ hRunit]
    rw [Matrix.conjTranspose_smul, hRinvH, Matrix.smul_mul, Matrix.smul_mul,
      Matrix.mul_smul, smul_smul, hRinvMul, Complex.star_def, Complex.mul_conj]

/-- **Optimality forces a scalar.**  If `N` is a positive-semidefinite matrix
with the same determinant as a positive-definite `M`, and `tr N` is the minimum
of `tr (S M S†)` over `det S = 1`, then `N` is a scalar matrix.  This is the
AM–GM equality argument: the minimum saturates `Dᴰ det = (tr)ᴰ`. -/

lemma posDef_orbit_min_isScalar [NeZero D] {M N : Matrix (Fin D) (Fin D) ℂ}
    (hM : M.PosDef) (hN : N.PosSemidef) (hdet : N.det = M.det)
    (hmin : ∀ S : Matrix (Fin D) (Fin D) ℂ, S.det = 1 →
      (Matrix.trace N).re ≤ (Matrix.trace (S * M * Sᴴ)).re) :
    ∃ c : ℂ, N = c • 1 := by
  obtain ⟨S₀, hS₀, r, hr0, hP⟩ := exists_sl_normalize hM
  have hDpos : 0 < D := Nat.pos_of_ne_zero (NeZero.ne D)
  have hdetP : (S₀ * M * S₀ᴴ).det = M.det := by
    rw [Matrix.det_mul, Matrix.det_mul, hS₀, Matrix.det_conjTranspose, hS₀]; simp
  have hNdet : N.det = ((r ^ D : ℝ) : ℂ) := by
    rw [hdet, ← hdetP, hP, Matrix.det_smul, Fintype.card_fin, Matrix.det_one, mul_one,
      ← Complex.ofReal_pow]
  have hNdet_re : N.det.re = r ^ D := by rw [hNdet]; exact Complex.ofReal_re _
  have hPtr : Matrix.trace (S₀ * M * S₀ᴴ) = ((r * D : ℝ) : ℂ) := by
    rw [hP, Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin, smul_eq_mul]
    push_cast; ring
  have hub : (Matrix.trace N).re ≤ r * D := by
    refine (hmin S₀ hS₀).trans_eq ?_; rw [hPtr]; exact Complex.ofReal_re _
  have htrN0 : 0 ≤ (Matrix.trace N).re := by
    simpa using (Complex.le_def.mp hN.trace_nonneg).1
  have hAGM := Matrix.PosSemidef.pow_card_mul_det_re_le_trace_re_pow hN
  rw [hNdet_re] at hAGM
  have hlb : (D : ℝ) * r ≤ (Matrix.trace N).re := by
    rw [← mul_pow] at hAGM
    exact (pow_le_pow_iff_left₀ (mul_nonneg (Nat.cast_nonneg D) hr0) htrN0 (NeZero.ne D)).mp hAGM
  have htrace_eq : (Matrix.trace N).re = (D : ℝ) * r :=
    le_antisymm (hub.trans_eq (mul_comm r (D : ℝ))) hlb
  exact ⟨_, (Matrix.PosSemidef.pow_card_mul_det_re_eq_trace_re_pow_iff hN).mp
    (by rw [hNdet_re, htrace_eq, mul_pow])⟩
end OrbitOptimality

end Wolf
