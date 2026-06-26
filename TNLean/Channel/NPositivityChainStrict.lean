/-
Copyright (c) 2026 Sirui Lu and TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import TNLean.Channel.PositiveExamples
import TNLean.Channel.MaximalOverlap
import TNLean.Channel.Schwarz.ChoiCompression

/-!
# The map `T_η` and strictness of the n-positivity chain

Wolf's Chapter 3 closes the discussion of the n-positivity hierarchy with the
one-parameter family of maps
`T_η(ρ) = tr(ρ) • 1 − η⁻¹ • ρ` on `M_D(ℂ)` (Wolf eq. (3.11)).  The map `tEta` is
defined for every real `η` (at `η = 0` it reduces to `ρ ↦ tr(ρ) • 1`); the
n-positivity threshold theorems below assume `0 < η`, matching Wolf's
`η ∈ ℝ₊`.  Its
Choi–Jamiolkowski operator is `τ_η = D⁻¹ • 1 − η⁻¹ • |Ω⟩⟨Ω|`, whose positive
eigenvalues all equal `1/D` and whose single negative eigenvalue is
`ν₋ = 1/D − 1/η` (present when `η < D`), with reduced density `1/D • 1` on the
first factor.  The expectation of `τ_η` in a normalized vector `ψ` of Schmidt
rank at most `k` is `1/D − η⁻¹ |⟨Ω|ψ⟩|²`, and the maximal-overlap principle
(Wolf Lemma 3.1) gives `sup_ψ |⟨Ω|ψ⟩|² = ‖1/D • 1‖₍ₖ₎ = k/D`.  The two bounds
of Wolf's Proposition 3.2 therefore coincide at `1/D − (k/D)/η`, which is
nonnegative exactly when `η ≥ k`.  Hence `T_η` is `k`-positive if and only if
`η ≥ k`.

Because the threshold is the parameter `η` itself, choosing `η` strictly between
two successive integers produces a map that is `k`-positive but not
`(k+1)`-positive.  This witnesses that every inclusion in Wolf's chain (3.3)
`T_cp = T_D ⊆ T_{D-1} ⊆ ⋯ ⊆ T_1` is strict.

The argument here follows the maximal-overlap route directly rather than the
abstract spectral decomposition: for normalized `ψ` the Choi quadratic form is
the elementary expression `1/D − η⁻¹ |⟨Ω|ψ⟩|²`, the overlap bound and its
attainment are supplied by the maximal-overlap principle, and the Schmidt-rank
Choi criterion converts the resulting sign condition into `k`-positivity.

## Main definitions

* `Matrix.tEta` -- Wolf's map `T_η(ρ) = tr(ρ) • 1 − η⁻¹ • ρ`.

## Main results

* `ChoiJamiolkowski.choiMatrix_tEta` -- the Choi operator of `T_η` is
  `D⁻¹ • 1 − η⁻¹ • |Ω⟩⟨Ω|`.
* `Matrix.IsHermitian.kyFanNorm_smul_one` -- the Ky-Fan `k`-norm of a
  nonnegative scalar multiple `c • 1` of the identity is `k • c` for `k < card`.
* `Matrix.isNPositiveMap_tEta_iff` -- **Wolf eq. (3.11):** for `0 < η` and
  `1 ≤ k < D`, the map `T_η` is `k`-positive if and only if `η ≥ k`.
* `Matrix.isNPositiveMap_tEta_card_iff` -- **Wolf eq. (3.11) at the top index
  `k = D`:** for `0 < η`, the map `T_η` is `D`-positive (i.e. completely positive)
  if and only if `η ≥ D`.
* `Matrix.tEta_isNPositiveMap_not_succ` and
  `Matrix.exists_isNPositiveMap_not_succ` -- the strictness witness: a
  `k`-positive map that is not `(k+1)`-positive, for `1 ≤ k` with `k + 1 < D`.

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Chapter 3,
  equation (3.11)][Wolf2012QChannels]
* [K. Fan, *On a theorem of Weyl concerning eigenvalues of linear
  transformations*][Fan1949Theorem]
-/

open scoped BigOperators Matrix ComplexOrder MatrixOrder
open Matrix

namespace Matrix

variable {D : ℕ}

/-- **Wolf Chapter 3, equation (3.11).** The map
`T_η(ρ) = tr(ρ) • 1 − η⁻¹ • ρ` on `M_D(ℂ)`, with real parameter `η`. -/
noncomputable def tEta (D : ℕ) (η : ℝ) :
    Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ where
  toFun X := Matrix.trace X • (1 : Matrix (Fin D) (Fin D) ℂ) - ((η : ℂ)⁻¹) • X
  map_add' X Y := by
    ext i j
    simp [Matrix.trace_add, add_smul, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  map_smul' c X := by
    ext i j
    simp only [Matrix.trace_smul, smul_smul, smul_sub, smul_eq_mul, RingHom.id_apply]
    ring_nf

@[simp]
theorem tEta_apply (η : ℝ) (X : Matrix (Fin D) (Fin D) ℂ) :
    tEta D η X = Matrix.trace X • (1 : Matrix (Fin D) (Fin D) ℂ) - ((η : ℂ)⁻¹) • X :=
  rfl

end Matrix

namespace ChoiJamiolkowski

variable {D : ℕ}

/-- The Choi operator of `T_η(X) = tr(X) • 1 − η⁻¹ • X` is
`D⁻¹ • 1 − η⁻¹ • |Ω⟩⟨Ω|`. -/
theorem choiMatrix_tEta [NeZero D] (η : ℝ) :
    choiMatrix (Matrix.tEta D η) =
      ((D : ℂ)⁻¹) • (1 : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ) -
        ((η : ℂ)⁻¹) • Matrix.omegaProj D := by
  classical
  have hDpos : (0 : ℝ) < D := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne D)
  have hcoeff :
      (D : ℂ)⁻¹ = (((D : ℝ).sqrt : ℂ)⁻¹ * (((D : ℝ).sqrt : ℂ)⁻¹)) := by
    rw [← _root_.mul_inv_rev]
    congr
    have hsqrt : (D : ℝ) = (D : ℝ).sqrt * (D : ℝ).sqrt := by
      exact (by
        nth_rw 1 [← Real.sq_sqrt hDpos.le]
        ring)
    exact_mod_cast hsqrt
  ext x y
  rcases x with ⟨i, a⟩
  rcases y with ⟨j, b⟩
  by_cases hij : i = j <;> by_cases hab : a = b <;>
    by_cases hia : i = a <;> by_cases hjb : j = b <;>
      simp_all [choiMatrix_apply, Matrix.tEta, omegaSlice_eq_single,
        Matrix.omegaProj_apply, Matrix.omegaVec_apply, eq_comm]

end ChoiJamiolkowski

namespace Matrix.IsHermitian

variable {N : Type*} [Fintype N] [DecidableEq N]

omit [Fintype N] in
/-- A real scalar multiple of the identity is Hermitian. -/
theorem isHermitian_smul_one (c : ℝ) :
    ((c : ℂ) • (1 : Matrix N N ℂ)).IsHermitian := by
  refine isHermitian_one.smul ?_
  rw [isSelfAdjoint_iff, Complex.star_def, Complex.conj_ofReal]

/-- **Ky-Fan norm of a scalar multiple of the identity.** For `k < card N` the
Ky-Fan `k`-norm of `c • 1` equals `k · c`: every rank-`k` orthogonal projection
realizes the trace `c · k`, so the maximum principle pins the norm to that
value. -/
theorem kyFanNorm_smul_one (c : ℝ) {k : ℕ} (hk : k < Fintype.card N) :
    (isHermitian_smul_one (N := N) c).kyFanNorm k = (k : ℝ) * c := by
  classical
  set A : Matrix N N ℂ := (c : ℂ) • (1 : Matrix N N ℂ) with hA
  have hAh : A.IsHermitian := isHermitian_smul_one (N := N) c
  -- The maximum principle gives a rank-`k` projection realizing the norm.
  obtain ⟨P, _hPh, _hPi, _hPr, hPt⟩ := hAh.exists_isProj_trace_eq_kyFanNorm k
  -- For that projection, `tr(P · A) = c · tr P = c · k`.
  have htrPA : (Matrix.trace (P * A)).re = c * (Matrix.trace P).re := by
    have hmul : P * A = (c : ℂ) • P := by
      rw [hA, Matrix.mul_smul, Matrix.mul_one]
    rw [hmul, Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul]
  have hPr' : (Matrix.trace P).re = (k : ℝ) := by
    rw [_hPr, min_eq_left (by exact_mod_cast le_of_lt hk)]
  rw [← hPt, htrPA, hPr', mul_comm]

end Matrix.IsHermitian

namespace Matrix

variable {D : ℕ}

/-- The Schmidt coefficient matrix of the maximally entangled vector is
`(√D)⁻¹ • 1`. -/
theorem schmidtCoeffMatrix_omegaVec :
    schmidtCoeffMatrix (omegaVec D)
      = (((D : ℝ).sqrt : ℂ)⁻¹) • (1 : Matrix (Fin D) (Fin D) ℂ) := by
  ext i j
  by_cases hij : i = j
  · subst hij; simp [schmidtCoeffMatrix, omegaVec, one_div]
  · simp [schmidtCoeffMatrix, omegaVec, hij, Matrix.one_apply_ne hij]

/-- The reduced density `C C†` of the maximally entangled vector is `D⁻¹ • 1`. -/
theorem omega_reducedDensity_eq [NeZero D] :
    schmidtCoeffMatrix (omegaVec D) * (schmidtCoeffMatrix (omegaVec D))ᴴ =
      ((D : ℂ)⁻¹) • (1 : Matrix (Fin D) (Fin D) ℂ) := by
  have hDpos : (0 : ℝ) < D := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne D)
  rw [schmidtCoeffMatrix_omegaVec, Matrix.smul_mul, Matrix.one_mul,
    Matrix.conjTranspose_smul, Matrix.conjTranspose_one, smul_smul]
  congr 1
  have hstar : star (((D : ℝ).sqrt : ℂ)⁻¹) = ((D : ℝ).sqrt : ℂ)⁻¹ := by
    rw [Complex.star_def, map_inv₀, Complex.conj_ofReal]
  rw [hstar, ← _root_.mul_inv_rev]
  congr 1
  have hsqrt : (D : ℝ).sqrt * (D : ℝ).sqrt = (D : ℝ) := Real.mul_self_sqrt hDpos.le
  rw [← Complex.ofReal_mul, hsqrt, Complex.ofReal_natCast]

/-- The Ky-Fan `k`-norm of the reduced density of the maximally entangled
vector is `k/D`. -/
theorem omega_kyFanNorm_eq [NeZero D] {k : ℕ} (hk : k < D) :
    (posSemidef_self_mul_conjTranspose (schmidtCoeffMatrix (omegaVec D))).isHermitian.kyFanNorm k
      = (k : ℝ) / D := by
  have hDpos : (0 : ℝ) < D := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne D)
  -- Both Hermitian witnesses are for the same matrix `D⁻¹ • 1`.
  have hmat := omega_reducedDensity_eq (D := D)
  have hcard : k < Fintype.card (Fin D) := by simpa using hk
  have hkfn :
      (posSemidef_self_mul_conjTranspose (schmidtCoeffMatrix (omegaVec D))).isHermitian.kyFanNorm k
        = (IsHermitian.isHermitian_smul_one (N := Fin D) ((D : ℝ)⁻¹)).kyFanNorm k := by
    congr 1
    · rw [hmat]; push_cast; rfl
  rw [hkfn, IsHermitian.kyFanNorm_smul_one ((D : ℝ)⁻¹) hcard]
  rw [div_eq_mul_inv]

/-- The real part of the self inner product `star ψ ⬝ᵥ ψ` is the sum of the
squared moduli of the entries; in particular it is nonnegative. -/
theorem dotProduct_star_self_re {ι : Type*} [Fintype ι] (ψ : ι → ℂ) :
    (star ψ ⬝ᵥ ψ).re = ∑ p, ‖ψ p‖ ^ 2 := by
  rw [dotProduct, Complex.re_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Pi.star_apply, Complex.star_def, ← Complex.normSq_eq_conj_mul_self,
    Complex.ofReal_re, Complex.normSq_eq_norm_sq]

/-- The self inner product `star ψ ⬝ᵥ ψ` is a nonnegative real number. -/
theorem dotProduct_star_self_ofReal {ι : Type*} [Fintype ι] (ψ : ι → ℂ) :
    star ψ ⬝ᵥ ψ = (((star ψ ⬝ᵥ ψ).re : ℝ) : ℂ) := by
  rw [Complex.ext_iff]
  refine ⟨by rw [Complex.ofReal_re], ?_⟩
  rw [Complex.ofReal_im, dotProduct, Complex.im_sum]
  refine Finset.sum_eq_zero fun p _ => ?_
  rw [Pi.star_apply, Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_im]

/-- Scaling a vector by a complex constant scales its self inner product by the
squared modulus of the constant. -/
theorem dotProduct_star_self_smul {ι : Type*} [Fintype ι] (c : ℂ) (ψ : ι → ℂ) :
    star (c • ψ) ⬝ᵥ (c • ψ) = ((‖c‖ ^ 2 : ℝ) : ℂ) * (star ψ ⬝ᵥ ψ) := by
  rw [star_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul,
    ← mul_assoc]
  congr 1
  rw [Complex.star_def, mul_comm, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]

/-- The expectation of `|Ω⟩⟨Ω|` in `ψ` is the squared overlap `|⟨Ω|ψ⟩|²`. -/
theorem omegaProj_quadraticForm (ψ : Fin D × Fin D → ℂ) :
    star ψ ⬝ᵥ (omegaProj D *ᵥ ψ)
      = ((‖star (omegaVec D) ⬝ᵥ ψ‖ ^ 2 : ℝ) : ℂ) := by
  -- `omegaProj *ᵥ ψ = (star omegaVec ⬝ᵥ ψ) • omegaVec` (right action on the vector).
  have hmv : omegaProj D *ᵥ ψ
      = MulOpposite.op (star (omegaVec D) ⬝ᵥ ψ) • omegaVec D := by
    rw [omegaProj, vecMulVec_mulVec]
  rw [hmv]
  -- The op-scalar pulls out of the dot product as right multiplication.
  have hdp : star ψ ⬝ᵥ (MulOpposite.op (star (omegaVec D) ⬝ᵥ ψ) • omegaVec D)
      = (star ψ ⬝ᵥ omegaVec D) * (star (omegaVec D) ⬝ᵥ ψ) := by
    simp only [dotProduct, Pi.smul_apply, op_smul_eq_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [hdp]
  -- `(star ψ ⬝ᵥ omegaVec) = star (star omegaVec ⬝ᵥ ψ)` and `star omegaVec = omegaVec`.
  set z : ℂ := star (omegaVec D) ⬝ᵥ ψ with hz
  have h2 : star ψ ⬝ᵥ omegaVec D = star z := by
    rw [hz, dotProduct_comm, ← star_omegaVec (d := D)]
    simp [dotProduct, Pi.star_apply, mul_comm]
  rw [h2, Complex.star_def, ← Complex.normSq_eq_conj_mul_self,
    Complex.normSq_eq_norm_sq]

/-- The Choi quadratic form of `T_η` in a vector `ψ` is
`D⁻¹ ‖ψ‖² − η⁻¹ |⟨Ω|ψ⟩|²`. -/
theorem choiMatrix_tEta_quadraticForm [NeZero D] (η : ℝ) (ψ : Fin D × Fin D → ℂ) :
    star ψ ⬝ᵥ (ChoiJamiolkowski.choiMatrix (tEta D η) *ᵥ ψ)
      = (((D : ℝ)⁻¹ * (star ψ ⬝ᵥ ψ).re
          - η⁻¹ * ‖star (omegaVec D) ⬝ᵥ ψ‖ ^ 2 : ℝ) : ℂ) := by
  rw [ChoiJamiolkowski.choiMatrix_tEta, Matrix.sub_mulVec, dotProduct_sub,
    smul_mulVec, smul_mulVec, Matrix.one_mulVec,
    dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul,
    omegaProj_quadraticForm, dotProduct_star_self_ofReal]
  rw [Complex.ofReal_re]
  push_cast
  ring

/-- **Homogeneous maximal-overlap bound.** For a vector `ψ` of Schmidt rank at
most `k` (with `1 ≤ k < D`), the squared overlap with the maximally entangled
vector is bounded by `(k/D)` times the squared norm of `ψ`.  This is the
maximal-overlap principle (Wolf Lemma 3.1) made degree-`2` homogeneous, so it
applies to vectors that are not normalized. -/
theorem normSq_omega_overlap_le [NeZero D] {k : ℕ} (hk1 : 1 ≤ k) (hk : k < D)
    {ψ : Fin D × Fin D → ℂ} (hrank : HasSchmidtRankLE k ψ) :
    ‖star (omegaVec D) ⬝ᵥ ψ‖ ^ 2 ≤ ((k : ℝ) / D) * (star ψ ⬝ᵥ ψ).re := by
  classical
  have hDpos : (0 : ℝ) < D := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne D)
  have hcard : k < Fintype.card (Fin D) := by simpa using hk
  -- The squared norm `(star ψ ⬝ᵥ ψ).re = Σ |ψ p|² ≥ 0`.
  have hresum : (star ψ ⬝ᵥ ψ).re = ∑ p, ‖ψ p‖ ^ 2 := dotProduct_star_self_re ψ
  have hsnn : 0 ≤ (star ψ ⬝ᵥ ψ).re := by rw [hresum]; positivity
  rcases eq_or_lt_of_le hsnn with hzero | hpos
  · -- `ψ = 0`: both sides vanish.
    have hψ0 : ∀ p, ψ p = 0 := by
      have hsum : (∑ p, ‖ψ p‖ ^ 2) = 0 := by rw [← hresum, ← hzero]
      intro p
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun q _ => by positivity)).mp hsum p
        (Finset.mem_univ p)
      simpa using this
    have hoverlap : star (omegaVec D) ⬝ᵥ ψ = 0 := by
      rw [dotProduct]; exact Finset.sum_eq_zero fun p _ => by rw [hψ0 p, mul_zero]
    rw [hoverlap, ← hzero]; simp
  · -- Nonzero `ψ`: normalize and apply the maximal-overlap bound.
    set s : ℝ := Real.sqrt ((star ψ ⬝ᵥ ψ).re) with hs
    have hspos : 0 < s := Real.sqrt_pos.mpr hpos
    have hssq : s ^ 2 = (star ψ ⬝ᵥ ψ).re := by rw [hs, Real.sq_sqrt hsnn]
    set φ : Fin D × Fin D → ℂ := (s : ℂ)⁻¹ • ψ with hφ
    -- `φ` is normalized: scaling by `s⁻¹` scales the squared norm by `s⁻²`.
    have hnorms : (‖(s : ℂ)⁻¹‖ ^ 2 : ℝ) = ((star ψ ⬝ᵥ ψ).re)⁻¹ := by
      rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hspos, inv_pow, hssq]
    have hφnorm : star φ ⬝ᵥ φ = 1 := by
      rw [hφ, dotProduct_star_self_smul, dotProduct_star_self_ofReal, hnorms,
        ← Complex.ofReal_mul, inv_mul_cancel₀ (ne_of_gt hpos), Complex.ofReal_one]
    -- `φ` has Schmidt rank at most `k`.
    have hφrank : HasSchmidtRankLE k φ := by
      rw [HasSchmidtRankLE, schmidtRank] at hrank ⊢
      rw [hφ, show schmidtCoeffMatrix ((s : ℂ)⁻¹ • ψ)
          = (s : ℂ)⁻¹ • schmidtCoeffMatrix ψ from rfl,
        rank_smul_of_ne_zero (by simp [ne_of_gt hspos])]
      exact hrank
    -- The maximal-overlap bound for the normalized `φ` (Wolf Lemma 3.1).
    have hΩnorm : star (omegaVec D) ⬝ᵥ (omegaVec D) = 1 := by
      rw [star_omegaVec]; exact omegaVec_dotProduct_self (Nat.pos_of_ne_zero (NeZero.ne D))
    have hgreat := maximalSchmidtOverlap_eq_kyFanNorm (omegaVec D) hΩnorm hk1 hcard
    have hmem : ‖star (omegaVec D) ⬝ᵥ φ‖ ^ 2 ∈
        {r : ℝ | ∃ ψ' : Fin D × Fin D → ℂ, star ψ' ⬝ᵥ ψ' = 1 ∧
          HasSchmidtRankLE k ψ' ∧ ‖star (omegaVec D) ⬝ᵥ ψ'‖ ^ 2 = r} :=
      ⟨φ, hφnorm, hφrank, rfl⟩
    have hφbound := hgreat.2 hmem
    -- Translate the normalized bound into the homogeneous one.
    have hkfn : (posSemidef_self_mul_conjTranspose
        (schmidtCoeffMatrix (omegaVec D))).isHermitian.kyFanNorm k = (k : ℝ) / D :=
      omega_kyFanNorm_eq hk
    rw [hkfn] at hφbound
    -- `‖⟨Ω|φ⟩‖² = ‖⟨Ω|ψ⟩‖² / s²`.
    have hoverlapφ :
        star (omegaVec D) ⬝ᵥ φ = (s : ℂ)⁻¹ * (star (omegaVec D) ⬝ᵥ ψ) := by
      rw [hφ, dotProduct_smul, smul_eq_mul]
    have hsq :
        ‖star (omegaVec D) ⬝ᵥ φ‖ ^ 2 = ‖star (omegaVec D) ⬝ᵥ ψ‖ ^ 2 / s ^ 2 := by
      rw [hoverlapφ, norm_mul, mul_pow, norm_inv, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hspos]
      rw [div_eq_inv_mul, inv_pow]
    rw [hsq] at hφbound
    rw [div_le_iff₀ (by positivity)] at hφbound
    rw [← hssq]
    linarith [hφbound]

/-- **Wolf eq. (3.11), `n`-positivity threshold of `T_η`.** For `0 < η` and
`1 ≤ k < D`, the map `T_η(ρ) = tr(ρ) • 1 − η⁻¹ • ρ` on `M_D(ℂ)` is `k`-positive
if and only if `η ≥ k`.

The Choi operator of `T_η` is `D⁻¹ • 1 − η⁻¹ • |Ω⟩⟨Ω|`, whose expectation in a
normalized Schmidt-rank-`k` vector `ψ` is `D⁻¹ − η⁻¹ |⟨Ω|ψ⟩|²`.  The
maximal-overlap principle gives `sup_ψ |⟨Ω|ψ⟩|² = k/D`, so the infimum
expectation is `D⁻¹(1 − k/η)`, nonnegative exactly when `η ≥ k`.

**Scope restriction (k < D):** the threshold is stated for Schmidt rank
`1 ≤ k < D`.  The omitted top index `k = D` (where `k`-positivity is complete
positivity) is inherited from the maximal-overlap principle (Wolf Lemma 3.1) and
is documented in `docs/paper-gaps/wolf_t_eta_top_index_scope.tex`. -/
theorem isNPositiveMap_tEta_iff [NeZero D] {η : ℝ} (hη : 0 < η) {k : ℕ}
    (hk1 : 1 ≤ k) (hk : k < D) :
    IsNPositiveMap k (tEta D η) ↔ (k : ℝ) ≤ η := by
  classical
  have hDpos : (0 : ℝ) < D := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne D)
  have hcard : k < Fintype.card (Fin D) := by simpa using hk
  rw [ChoiJamiolkowski.isNPositiveMap_iff_forall_hasSchmidtRankLE_choiMatrix_quadraticForm_nonneg]
  constructor
  · -- `k`-positive ⟹ `k ≤ η`, via the overlap-attaining normalized vector.
    intro hpos
    by_contra hlt
    rw [not_le] at hlt
    -- A normalized Schmidt-rank-`k` vector with `|⟨Ω|ψ⟩|² = k/D`.
    have hΩnorm : star (omegaVec D) ⬝ᵥ (omegaVec D) = 1 := by
      rw [star_omegaVec]; exact omegaVec_dotProduct_self (Nat.pos_of_ne_zero (NeZero.ne D))
    obtain ⟨ψ, hψnorm, hψrank, hψeq⟩ :=
      (maximalSchmidtOverlap_eq_kyFanNorm (omegaVec D) hΩnorm hk1 hcard).1
    rw [omega_kyFanNorm_eq hk] at hψeq
    -- Its Choi expectation is `D⁻¹(1 − k/η) < 0`, contradicting nonnegativity.
    have hquad := choiMatrix_tEta_quadraticForm (D := D) η ψ
    rw [hψeq, hψnorm, Complex.one_re] at hquad
    have hval := hpos ψ hψrank
    rw [hquad, ← Complex.ofReal_zero, Complex.real_le_real, mul_one,
      div_eq_mul_inv] at hval
    -- `D⁻¹ − η⁻¹ · k · D⁻¹ ≥ 0` forces `k ≤ η`.
    have hηinv : 0 < η⁻¹ := inv_pos.mpr hη
    have hDinv : 0 < (D : ℝ)⁻¹ := inv_pos.mpr hDpos
    have hcancelD : (D : ℝ)⁻¹ * D = 1 := inv_mul_cancel₀ (ne_of_gt hDpos)
    have hcancelη : η⁻¹ * η = 1 := inv_mul_cancel₀ (ne_of_gt hη)
    -- Multiply `hval` by `D > 0`: `1 − η⁻¹ k ≥ 0`; then by `η > 0`: `η − k ≥ 0`.
    have hstep : 0 ≤ 1 - η⁻¹ * (k : ℝ) := by
      have := mul_le_mul_of_nonneg_right hval (le_of_lt hDpos)
      nlinarith [this, hcancelD, hDpos]
    have hkη : (k : ℝ) ≤ η := by nlinarith [hstep, hη, hcancelη]
    exact absurd hkη (not_le.mpr hlt)
  · -- `k ≤ η` ⟹ `k`-positive, via the homogeneous overlap bound.
    intro hkη ψ hψrank
    have hquad := choiMatrix_tEta_quadraticForm (D := D) η ψ
    rw [hquad, ← Complex.ofReal_zero, Complex.real_le_real]
    -- The bound `|⟨Ω|ψ⟩|² ≤ (k/D) ‖ψ‖²` makes the quadratic form nonnegative.
    have hbound := normSq_omega_overlap_le (D := D) hk1 hk hψrank
    have hnormnn : 0 ≤ (star ψ ⬝ᵥ ψ).re := by
      rw [dotProduct_star_self_re]; positivity
    have hηinv : 0 < η⁻¹ := inv_pos.mpr hη
    have hDinv : 0 < (D : ℝ)⁻¹ := inv_pos.mpr hDpos
    set w : ℝ := (star ψ ⬝ᵥ ψ).re with hw
    set q : ℝ := ‖star (omegaVec D) ⬝ᵥ ψ‖ ^ 2 with hq
    rw [div_eq_mul_inv] at hbound
    have hcancelD : (D : ℝ)⁻¹ * D = 1 := inv_mul_cancel₀ (ne_of_gt hDpos)
    have hkw : η⁻¹ * (k : ℝ) ≤ 1 := by
      rw [← div_eq_inv_mul, div_le_one hη]; exact hkη
    -- `η⁻¹ q ≤ η⁻¹ (k D⁻¹) w` and `η⁻¹ k ≤ 1` give `η⁻¹ q ≤ D⁻¹ w`.
    have h1 : η⁻¹ * q ≤ η⁻¹ * ((k : ℝ) * (D : ℝ)⁻¹ * w) :=
      mul_le_mul_of_nonneg_left hbound (le_of_lt hηinv)
    have hwD : 0 ≤ (D : ℝ)⁻¹ * w := mul_nonneg (le_of_lt hDinv) hnormnn
    -- `η⁻¹ (k D⁻¹) w = (η⁻¹ k) (D⁻¹ w) ≤ 1 · (D⁻¹ w) = D⁻¹ w`.
    have h2 : η⁻¹ * ((k : ℝ) * (D : ℝ)⁻¹ * w) ≤ (D : ℝ)⁻¹ * w := by
      have hrw : η⁻¹ * ((k : ℝ) * (D : ℝ)⁻¹ * w)
          = (η⁻¹ * (k : ℝ)) * ((D : ℝ)⁻¹ * w) := by ring
      rw [hrw]
      calc (η⁻¹ * (k : ℝ)) * ((D : ℝ)⁻¹ * w)
          ≤ 1 * ((D : ℝ)⁻¹ * w) := mul_le_mul_of_nonneg_right hkw hwD
        _ = (D : ℝ)⁻¹ * w := one_mul _
    linarith [h1, h2]

/-- **Wolf eq. (3.11) at the top index n = D.**  Since D-positivity on M_D(ℂ) is
complete positivity, T_η is D-positive iff its Choi operator is positive
semidefinite, and — the maximally entangled vector being the worst case — this
holds iff D ≤ η.  Together with the lower-range threshold equivalence
`isNPositiveMap_tEta_iff` (the range 1 ≤ k < D) this completes Wolf's threshold
criterion over k = 1, …, D. -/
theorem isNPositiveMap_tEta_card_iff [NeZero D] {η : ℝ} (hη : 0 < η) :
    IsNPositiveMap D (tEta D η) ↔ (D : ℝ) ≤ η := by
  classical
  have hDpos : (0 : ℝ) < D := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne D)
  have hΩself : star (omegaVec D) ⬝ᵥ (omegaVec D) = 1 := by
    rw [star_omegaVec]; exact omegaVec_dotProduct_self (Nat.pos_of_ne_zero (NeZero.ne D))
  rw [ChoiJamiolkowski.isNPositiveMap_iff_forall_hasSchmidtRankLE_choiMatrix_quadraticForm_nonneg]
  constructor
  · intro hpos
    have hΩrank : Matrix.HasSchmidtRankLE D (omegaVec D) :=
      Matrix.hasSchmidtRankLE_iff.mpr (by simpa using Matrix.schmidtRank_le_left (omegaVec D))
    have hquad := choiMatrix_tEta_quadraticForm (D := D) η (omegaVec D)
    rw [hΩself] at hquad
    simp only [Complex.one_re, norm_one, one_pow] at hquad
    have hval := hpos (omegaVec D) hΩrank
    rw [hquad, ← Complex.ofReal_zero, Complex.real_le_real] at hval
    simp only [mul_one] at hval
    exact (inv_le_inv₀ hη hDpos).mp (by linarith)
  · intro hDη ψ _
    have hquad := choiMatrix_tEta_quadraticForm (D := D) η ψ
    rw [hquad, ← Complex.ofReal_zero, Complex.real_le_real]
    set w : ℝ := (star ψ ⬝ᵥ ψ).re with hwdef
    have hwnn : 0 ≤ w := by rw [hwdef, dotProduct_star_self_re]; positivity
    have hcs : ‖star (omegaVec D) ⬝ᵥ ψ‖ ^ 2 ≤ w := by
      have key : (inner (𝕜 := ℂ) (WithLp.toLp 2 (omegaVec D))
          (WithLp.toLp 2 ψ : EuclideanSpace ℂ (Fin D × Fin D)) : ℂ)
          = star (omegaVec D) ⬝ᵥ ψ := by
        rw [EuclideanSpace.inner_eq_star_dotProduct]; exact dotProduct_comm _ _
      have hΩn : ‖(WithLp.toLp 2 (omegaVec D) : EuclideanSpace ℂ (Fin D × Fin D))‖ = 1 := by
        have h2 : ‖(WithLp.toLp 2 (omegaVec D) : EuclideanSpace ℂ (Fin D × Fin D))‖ ^ 2 = 1 := by
          rw [← @inner_self_eq_norm_sq ℂ]
          have hii : (inner (𝕜 := ℂ) (WithLp.toLp 2 (omegaVec D))
              (WithLp.toLp 2 (omegaVec D) : EuclideanSpace ℂ (Fin D × Fin D)) : ℂ)
              = star (omegaVec D) ⬝ᵥ (omegaVec D) := by
            rw [EuclideanSpace.inner_eq_star_dotProduct]; exact dotProduct_comm _ _
          rw [hii, hΩself]; simp
        nlinarith [norm_nonneg (WithLp.toLp 2 (omegaVec D) : EuclideanSpace ℂ (Fin D × Fin D)), h2]
      have hψn : ‖(WithLp.toLp 2 ψ : EuclideanSpace ℂ (Fin D × Fin D))‖ ^ 2 = w := by
        rw [← @inner_self_eq_norm_sq ℂ, hwdef]
        have hii : (inner (𝕜 := ℂ) (WithLp.toLp 2 ψ)
            (WithLp.toLp 2 ψ : EuclideanSpace ℂ (Fin D × Fin D)) : ℂ) = star ψ ⬝ᵥ ψ := by
          rw [EuclideanSpace.inner_eq_star_dotProduct]; exact dotProduct_comm _ _
        rw [hii]; rfl
      calc ‖star (omegaVec D) ⬝ᵥ ψ‖ ^ 2
          = ‖(inner (𝕜 := ℂ) (WithLp.toLp 2 (omegaVec D))
              (WithLp.toLp 2 ψ : EuclideanSpace ℂ (Fin D × Fin D)) : ℂ)‖ ^ 2 := by rw [key]
        _ ≤ (‖(WithLp.toLp 2 (omegaVec D) : EuclideanSpace ℂ (Fin D × Fin D))‖
              * ‖(WithLp.toLp 2 ψ : EuclideanSpace ℂ (Fin D × Fin D))‖) ^ 2 := by
            gcongr; exact norm_inner_le_norm _ _
        _ = w := by rw [hΩn, one_mul, hψn]
    have hinvle : η⁻¹ ≤ (D : ℝ)⁻¹ := by rw [inv_le_inv₀ hη hDpos]; exact hDη
    nlinarith [hcs, hwnn, hinvle, inv_pos.mpr hη, inv_pos.mpr hDpos]

/-- **Strictness witness for Wolf's chain (3.3).** For `1 ≤ k` with `k + 1 < D`,
the map `T_η` with `k ≤ η < k + 1` is `k`-positive but not `(k+1)`-positive. -/
theorem tEta_isNPositiveMap_not_succ [NeZero D] {η : ℝ} {k : ℕ}
    (hk1 : 1 ≤ k) (hk : k + 1 < D) (hηlb : (k : ℝ) ≤ η) (hηub : η < (k : ℝ) + 1) :
    IsNPositiveMap k (tEta D η) ∧ ¬ IsNPositiveMap (k + 1) (tEta D η) := by
  have hη : 0 < η := lt_of_lt_of_le (by exact_mod_cast hk1) hηlb
  refine ⟨(isNPositiveMap_tEta_iff hη hk1 (by omega)).mpr hηlb, ?_⟩
  rw [isNPositiveMap_tEta_iff hη (by omega) hk]
  push_cast
  exact not_le.mpr hηub

/-- **Strictness of every inclusion in Wolf's chain (3.3).** For `1 ≤ k` with
`k + 1 < D`, there is a map on `M_D(ℂ)` that is `k`-positive but not
`(k+1)`-positive; hence the cone of `k`-positive maps strictly contains the cone
of `(k+1)`-positive maps. -/
theorem exists_isNPositiveMap_not_succ [NeZero D] {k : ℕ}
    (hk1 : 1 ≤ k) (hk : k + 1 < D) :
    ∃ T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ,
      IsNPositiveMap k T ∧ ¬ IsNPositiveMap (k + 1) T :=
  ⟨tEta D (k : ℝ), tEta_isNPositiveMap_not_succ hk1 hk le_rfl (by linarith)⟩

end Matrix
