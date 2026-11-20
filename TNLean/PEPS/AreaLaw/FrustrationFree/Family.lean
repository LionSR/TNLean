/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.ManyBody.Hamiltonian.GroundSpace
import TNLean.PEPS.AreaLaw.FrustrationFree.RangeProjection

/-!
# Frustration-free families of positive terms

A finite family of matrices `k_i` is *frustration free with strength `J` and gap `Δ`* at the unit
vector `Ω` when

`0 ≤ k_i ≤ J`, `k_i Ω = 0`, `‖Ω‖ = 1`, `Δ (1 - |Ω⟩⟨Ω|) ≤ ∑_i k_i`.

The predicate records no supports. The finite-range model of the frustration-free area-law note,
`eq:model`, is the family of terms of a finite-range interaction
(`IsFrustrationFreeGapped`); the positive quasi-local constraints of Proposition 4.3 of the
two-dimensional area law, with `0 ≤ k_i ≤ 1`, `k_i Ω = 0` and `(Δ/c)(1 - P) ≤ ∑_i k_i`
(`exists_latticePositiveConstraints`), are a frustration-free family with strength `1` and gap
`Δ/c` whose terms have quasi-local tails. Everything here uses only the predicate: the sum is
gapped at energy zero with ground space `span {Ω}`, and the range projections `Π_i` of the terms
annihilate `Ω` and keep the gap, `(Δ/J)(1 - P) ≤ ∑_i Π_i`, which is the input of the sweep
contraction `eq:sweep`.

## Main definitions

* `TNLean.PEPS.AreaLaw.FrustrationFree.IsFrustrationFree`: the predicate.
* `IsFrustrationFree.termProj`: the range projection `Π_i` of the term `k_i`.

## Main statements

* `IsFrustrationFree.isGapped`, `IsFrustrationFree.groundSpace_eq`: `∑_i k_i` has gap `Δ` at
  energy zero and ground space `span {Ω}`.
* `IsFrustrationFree.norm_term_le`: `‖k_i‖ ≤ J`.
* `IsFrustrationFree.smul_sub_le_sum_termProj`: `(Δ/J)(1 - P) ≤ ∑_i Π_i`.
* `IsFrustrationFree.mul_norm_sq_le_re_inner_sum_termProj`: `(Δ/J) ‖v‖² ≤ ⟨v, ∑_i Π_i v⟩` for
  `v ⟂ Ω`.

## References

* Reading note *Entanglement across a cut in two-dimensional frustration-free ground states*,
  November 18, 2026, `docs/audits/2026-11-18_finite_range_frustration_free_area_law.tex`,
  `eq:model` and "Contraction in one sweep".
* OpenAI, *A two-dimensional area law from a global spectral gap*, September 24, 2026,
  Proposition 4.3 (`prop:positive`, `03-quasilocal.tex`, lines 220–246).
-/

open Matrix
open scoped InnerProductSpace MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open ManyBody (IsGapped groundSpace)

namespace TNLean.PEPS.AreaLaw.FrustrationFree

variable {n ι : Type*} [Fintype n] [DecidableEq n] [Fintype ι]

local notation "clm" => toEuclideanCLM (n := n) (𝕜 := ℂ)

/-- **Frustration-free family** (`eq:model` of the frustration-free area-law note, without the
supports; also the conclusion of Proposition 4.3 of the two-dimensional area law): every term
satisfies `0 ≤ k_i ≤ J` and annihilates the unit vector `Ω`, and the sum satisfies
`∑_i k_i ≥ Δ (1 - |Ω⟩⟨Ω|)`. -/
structure IsFrustrationFree (k : ι → Matrix n n ℂ) (J Δ : ℝ) (Ω : EuclideanSpace ℂ n) :
    Prop where
  /-- Every term is positive semidefinite. -/
  posSemidef : ∀ i, (k i).PosSemidef
  /-- Every term is at most `J`. -/
  le_bound : ∀ i, k i ≤ J • (1 : Matrix n n ℂ)
  /-- Every term annihilates `Ω`. -/
  mulVec_eq_zero : ∀ i, k i *ᵥ WithLp.ofLp Ω = 0
  /-- `Ω` is a unit vector. -/
  norm_eq_one : ‖Ω‖ = 1
  /-- The gap inequality `∑_i k_i ≥ Δ (1 - |Ω⟩⟨Ω|)`. -/
  gap : (Δ : ℂ) • (1 - vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω))) ≤ ∑ i, k i

namespace IsFrustrationFree

variable {k : ι → Matrix n n ℂ} {J Δ : ℝ} {Ω : EuclideanSpace ℂ n}

/-- The terms are Hermitian. -/
theorem isHermitian (hk : IsFrustrationFree k J Δ Ω) (i : ι) : (k i).IsHermitian :=
  (hk.posSemidef i).isHermitian

/-- The sum of the terms annihilates `Ω`. -/
theorem sum_mulVec_eq_zero (hk : IsFrustrationFree k J Δ Ω) :
    (∑ i, k i) *ᵥ WithLp.ofLp Ω = 0 := by
  rw [sum_mulVec]
  exact Finset.sum_eq_zero fun i _ ↦ hk.mulVec_eq_zero i

/-- The sum of the terms is gapped at energy zero with gap `Δ` and has the ground space
`span {Ω}`, in the form of `ManyBody.isGapped_and_groundSpace_eq_span_iff`. -/
theorem isGapped_and_groundSpace_eq (hk : IsFrustrationFree k J Δ Ω) (hΔ : 0 < Δ) :
    IsGapped (∑ i, k i) 0 Δ ∧ groundSpace (∑ i, k i) 0 = Submodule.span ℂ {Ω} := by
  have hiff := (ManyBody.isGapped_and_groundSpace_eq_span_iff (H := ∑ i, k i) (E₀ := 0)
    hΔ Ω).mp ⟨hk.norm_eq_one, ?_, ?_⟩
  · exact ⟨hiff.2.2.1, hiff.2.2.2⟩
  · rw [Complex.ofReal_zero, zero_smul]
    change WithLp.toLp 2 ((∑ i, k i) *ᵥ WithLp.ofLp Ω) = 0
    rw [hk.sum_mulVec_eq_zero]
    rfl
  · have := Matrix.le_iff.mp hk.gap
    simpa using this

/-- The sum of the terms is gapped at energy zero with gap `Δ`. -/
theorem isGapped (hk : IsFrustrationFree k J Δ Ω) (hΔ : 0 < Δ) : IsGapped (∑ i, k i) 0 Δ :=
  (hk.isGapped_and_groundSpace_eq hΔ).1

/-- The ground space of the sum of the terms is the line through `Ω`. -/
theorem groundSpace_eq (hk : IsFrustrationFree k J Δ Ω) (hΔ : 0 < Δ) :
    groundSpace (∑ i, k i) 0 = Submodule.span ℂ {Ω} :=
  (hk.isGapped_and_groundSpace_eq hΔ).2

/-- Every term has operator norm at most `J`. -/
theorem norm_term_le (hk : IsFrustrationFree k J Δ Ω) (hJ : 0 ≤ J) (i : ι) : ‖k i‖ ≤ J :=
  (CStarAlgebra.norm_le_iff_le_algebraMap _ hJ (hk.posSemidef i).nonneg).mpr
    (by simpa [Algebra.algebraMap_eq_smul_one] using hk.le_bound i)

/-- **The range projections keep the gap.** With `Π_i` the range projection of `k_i`,
`(Δ / J) (1 - |Ω⟩⟨Ω|) ≤ ∑_i Π_i`. Source:
`docs/audits/2026-11-18_finite_range_frustration_free_area_law.tex`, "Contraction in one sweep",
where `∑_i k_i ≥ g (1 - P)` with `g = Δ / J`; here `Π_i ≥ k_i / J`. -/
theorem smul_sub_le_sum_supportProj (hk : IsFrustrationFree k J Δ Ω) (hJ : 0 < J) :
    ((Δ / J : ℝ) : ℂ) • (1 - vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω))) ≤
      ∑ i, (hk.posSemidef i).supportProj := by
  have hsum : ∑ i, k i ≤ J • ∑ i, (hk.posSemidef i).supportProj := by
    rw [Finset.smul_sum]
    exact Finset.sum_le_sum fun i _ ↦ (hk.posSemidef i).le_smul_supportProj (hk.le_bound i)
  have h1 := hk.gap.trans hsum
  have hJ' : (0 : ℝ) < J⁻¹ := inv_pos.mpr hJ
  have h2 := smul_le_smul_of_nonneg_left h1 hJ'.le
  rw [smul_smul, inv_mul_cancel₀ hJ.ne', one_smul] at h2
  convert h2 using 1
  rw [div_eq_inv_mul, Complex.ofReal_mul, mul_smul, Complex.coe_smul]

/-- The range projection `Π_i` of the term `k_i`. -/
noncomputable def termProj (hk : IsFrustrationFree k J Δ Ω) (i : ι) : Matrix n n ℂ :=
  (hk.isHermitian i).supportProj

theorem termProj_mulVec (hk : IsFrustrationFree k J Δ Ω) (i : ι) :
    hk.termProj i *ᵥ WithLp.ofLp Ω = 0 :=
  (hk.isHermitian i).supportProj_mulVec_eq_zero_of_mulVec_eq_zero _ (hk.mulVec_eq_zero i)

theorem factor_mulVec (hk : IsFrustrationFree k J Δ Ω) (i : ι) :
    (1 - hk.termProj i) *ᵥ WithLp.ofLp Ω = WithLp.ofLp Ω := by
  rw [sub_mulVec, one_mulVec, hk.termProj_mulVec, sub_zero]

theorem conjTranspose_factor_mulVec (hk : IsFrustrationFree k J Δ Ω) (i : ι) :
    (1 - hk.termProj i)ᴴ *ᵥ WithLp.ofLp Ω = WithLp.ofLp Ω := by
  have h0 := hk.factor_mulVec i
  unfold termProj at h0 ⊢
  rw [conjTranspose_sub, conjTranspose_one, (hk.isHermitian i).supportProj_isHermitian.eq, h0]

/-- **The range projections keep the gap**, in terms of `termProj`. -/
theorem smul_sub_le_sum_termProj (hk : IsFrustrationFree k J Δ Ω) (hJ : 0 < J) :
    ((Δ / J : ℝ) : ℂ) • (1 - vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω))) ≤
      ∑ i, hk.termProj i :=
  hk.smul_sub_le_sum_supportProj hJ

/-- The quadratic form of the range projections dominates `(Δ / J) ‖v‖²` on `Ω^⊥`. Source:
`docs/audits/2026-11-18_finite_range_frustration_free_area_law.tex`, "Contraction in one
sweep". -/
theorem mul_norm_sq_le_re_inner_sum_termProj (hk : IsFrustrationFree k J Δ Ω) (hJ : 0 < J)
    {v : EuclideanSpace ℂ n} (hv : ⟪Ω, v⟫_ℂ = 0) :
    Δ / J * ‖v‖ ^ 2 ≤ RCLike.re ⟪v, clm (∑ i, hk.termProj i) v⟫_ℂ := by
  have hle := Matrix.le_iff.mp (hk.smul_sub_le_sum_termProj hJ)
  have h0 := (isPositive_toEuclideanLin_iff.mpr hle).re_inner_nonneg_right v
  have hP : toEuclideanLin (vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω))) v = 0 := by
    have : star (WithLp.ofLp Ω) ⬝ᵥ WithLp.ofLp v = 0 := by
      rw [← hv, EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
    ext c
    simp [toEuclideanLin, vecMulVec_mulVec, this]
  rw [map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply, map_sub,
    LinearMap.sub_apply, hP, sub_zero, inner_sub_right, inner_smul_right] at h0
  have h1 : toEuclideanLin (1 : Matrix n n ℂ) v = v := by simp
  rw [h1, inner_self_eq_norm_sq_to_K, map_sub, sub_nonneg] at h0
  refine le_of_eq_of_le ?_ h0
  simp only [RCLike.re_to_complex]
  norm_cast
  rw [Complex.re_ofReal_mul]
  rfl

end IsFrustrationFree

end TNLean.PEPS.AreaLaw.FrustrationFree
