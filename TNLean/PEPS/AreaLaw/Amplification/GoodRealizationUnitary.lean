/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Analysis.PolarUnitaryCorrectionKronecker

/-!
# From a good clock realization to a local unitary

In the proof of the amplification proposition, one clock realization is
selected on which the excited component, the omitted events and the radius
truncation are all small. This module carries out the deterministic steps
that follow that selection. The truncated product `L'` applied to the
restoring vector `ζ = R₀ φ` has norm at most `1 + 3ε`, and its adjoint almost
fixes every vector fixed by the adjoint of the retained product. An adjoint
error `a` and a direct norm bound `1 + b` for a square operator `R'` between
unit vectors `φ` and `η` bound `‖R' φ - η‖²` by `2a + 2b + b²`. Finally the
unitary polar factor of a local `R'`, tensored with the identity on the
remaining systems, moves `φ` to within `a + √(2a + 2b + b²)` of `η`.

All vectors may be entangled with the remaining systems, and no invertibility
of `R'` is assumed. The probabilistic selection of the realization, the
restoring operator and the final entropy comparison are not formalized here.

## Main statements

* `norm_truncated_restoring_le`: the first estimate of
  `eq:amplification-before-polar`.
* `norm_truncated_adjoint_sub_le`: the second estimate of
  `eq:amplification-before-polar`.
* `norm_sub_sq_le_of_adjoint_error`: `eq:amplification-direct-error`.
* `exists_unitary_kronecker_sub_le`: `eq:amplification-unitary-error`.
* `exists_unitary_kronecker_sub_le_of_good_realization`: the three steps
  composed, with `b = 3ε`.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*,
  September 24, 2026, `09-amplification.tex`, lines 501–545, equations
  `eq:amplification-before-polar`, `eq:amplification-direct-error` and
  `eq:amplification-unitary-error`.
  Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

Independently formalized from the manuscript; no upstream Lean proof text is reused.
-/

open Matrix
open scoped Kronecker

namespace TNLean.PEPS.AreaLaw

section SameSpace

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

local notation "L" => toEuclideanCLM (n := ι) (𝕜 := ℂ)

/-- The Euclidean operator of a conjugate transpose is the adjoint operator. -/
private theorem toEuclideanCLM_conjTranspose (A : Matrix ι ι ℂ) :
    L Aᴴ = ContinuousLinearMap.adjoint (L A) := by
  rw [← star_eq_conjTranspose, map_star, ContinuousLinearMap.star_eq_adjoint]

/-- **First estimate of `eq:amplification-before-polar`.** Let `g` be the ground
component of the restoring vector `ζ`, fixed by the full product `D` and of norm at
most one. If the excited component, the omitted events and the radius truncation
contribute at most `ε` each on the chosen realization, with `‖ζ‖ ≤ M₀`, then the
truncated product `L'` satisfies `‖L' ζ‖ ≤ 1 + 3ε`.
Source: `09-amplification.tex`, lines 493–508, `eq:amplification-good-trajectory`
and `eq:amplification-before-polar`. -/
theorem norm_truncated_restoring_le {D Dret L' : Matrix ι ι ℂ}
    {ζ g : EuclideanSpace ℂ ι} {M₀ ε : ℝ}
    (hg : L D g = g) (hgn : ‖g‖ ≤ 1)
    (hexc : ‖L D (ζ - g)‖ ≤ ε) (hret : ‖L (D - Dret) ζ‖ ≤ ε)
    (htrunc : M₀ * ‖L (Dret - L')‖ ≤ ε) (hζ : ‖ζ‖ ≤ M₀) :
    ‖L L' ζ‖ ≤ 1 + 3 * ε := by
  have htr : ‖L (Dret - L') ζ‖ ≤ ε :=
    calc ‖L (Dret - L') ζ‖ ≤ ‖L (Dret - L')‖ * ‖ζ‖ := (L (Dret - L')).le_opNorm ζ
      _ ≤ ‖L (Dret - L')‖ * M₀ := mul_le_mul_of_nonneg_left hζ (norm_nonneg _)
      _ ≤ ε := by rw [mul_comm]; exact htrunc
  have hsplit : L L' ζ =
      g + L D (ζ - g) - L (D - Dret) ζ - L (Dret - L') ζ := by
    simp only [map_sub, _root_.sub_apply, hg]
    abel
  rw [hsplit]
  calc ‖g + L D (ζ - g) - L (D - Dret) ζ - L (Dret - L') ζ‖
      ≤ ‖g‖ + ‖L D (ζ - g)‖ + ‖L (D - Dret) ζ‖ + ‖L (Dret - L') ζ‖ :=
        (norm_sub_le _ _).trans (add_le_add_left
          ((norm_sub_le _ _).trans (add_le_add_left (norm_add_le _ _) _)) _)
    _ ≤ 1 + 3 * ε := by linarith only [hgn, hexc, hret, htr]

/-- **Second estimate of `eq:amplification-before-polar`.** If the adjoint of
the retained product fixes a vector `w` of norm at most one, then the adjoint of
the truncated product moves `w` by at most `ε`, provided `M₀ ≥ 1`.
Source: `09-amplification.tex`, lines 501–508. -/
theorem norm_truncated_adjoint_sub_le {Dret L' : Matrix ι ι ℂ}
    {w : EuclideanSpace ℂ ι} {M₀ ε : ℝ}
    (hfix : L Dretᴴ w = w) (hw : ‖w‖ ≤ 1) (hM₀ : 1 ≤ M₀)
    (htrunc : M₀ * ‖L (Dret - L')‖ ≤ ε) :
    ‖L L'ᴴ w - w‖ ≤ ε := by
  have hdiff : L L'ᴴ w - w = L (L' - Dret)ᴴ w := by
    simp only [conjTranspose_sub, map_sub, _root_.sub_apply, hfix]
  have hnorm : ‖L (L' - Dret)ᴴ‖ = ‖L (Dret - L')‖ := by
    rw [toEuclideanCLM_conjTranspose, ContinuousLinearMap.adjoint.norm_map, ← norm_neg,
      ← map_neg, neg_sub]
  have hle : ‖L (Dret - L')‖ ≤ ε :=
    (le_mul_of_one_le_left (norm_nonneg _) hM₀).trans htrunc
  rw [hdiff]
  calc ‖L (L' - Dret)ᴴ w‖ ≤ ‖L (L' - Dret)ᴴ‖ * ‖w‖ := (L (L' - Dret)ᴴ).le_opNorm w
    _ ≤ ‖L (L' - Dret)ᴴ‖ * 1 := mul_le_mul_of_nonneg_left hw (norm_nonneg _)
    _ ≤ ε := by rw [mul_one, hnorm]; exact hle

/-- **`eq:amplification-direct-error`.** For unit vectors `φ, η`, an adjoint error
`‖R'ᴴ η - φ‖ ≤ a` and a direct bound `‖R' φ‖ ≤ 1 + b` give
`‖R' φ - η‖² ≤ 2a + 2b + b²`. The real overlap `Re ⟨η, R' φ⟩` is at least `1 - a`.
Source: `09-amplification.tex`, lines 510–522. -/
theorem norm_sub_sq_le_of_adjoint_error (R : Matrix ι ι ℂ)
    {φ η : EuclideanSpace ℂ ι} (hφ : ‖φ‖ = 1) (hη : ‖η‖ = 1) {a b : ℝ}
    (hadj : ‖L Rᴴ η - φ‖ ≤ a) (hdir : ‖L R φ‖ ≤ 1 + b) :
    ‖L R φ - η‖ ^ 2 ≤ 2 * a + 2 * b + b ^ 2 := by
  have hinner : RCLike.re (inner ℂ (L R φ) η) =
      RCLike.re (inner ℂ φ φ) + RCLike.re (inner ℂ φ (L Rᴴ η - φ)) := by
    rw [toEuclideanCLM_conjTranspose, inner_sub_right,
      ContinuousLinearMap.adjoint_inner_right, map_sub]
    ring
  have hφφ : RCLike.re (inner ℂ φ φ) = 1 := by
    rw [inner_self_eq_norm_sq, hφ]; norm_num
  have hcs : -a ≤ RCLike.re (inner ℂ φ (L Rᴴ η - φ)) := by
    have h1 := (abs_le.mp ((RCLike.abs_re_le_norm (inner ℂ φ (L Rᴴ η - φ))).trans
      (norm_inner_le_norm φ (L Rᴴ η - φ)))).1
    rw [hφ, one_mul] at h1
    linarith only [h1, hadj]
  have hsq : ‖L R φ‖ ^ 2 ≤ (1 + b) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hdir 2
  rw [@norm_sub_sq ℂ, hη]
  nlinarith only [hinner, hφφ, hcs, hsq]

end SameSpace

section Spectator

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {m : Type*} [Fintype m] [DecidableEq m]

local notation "L₂" => toEuclideanCLM (n := n × m) (𝕜 := ℂ)

/-- **`eq:amplification-unitary-error`, with the direct error.** Let a local square
operator `R'` act on `n`, tensored with the identity on the remaining systems `m`.
For unit vectors `φ, η` of the product space, possibly entangled across the two
factors, the bounds `‖R'ᴴ η - φ‖ ≤ a` and `‖R' φ‖ ≤ 1 + b` give a unitary `U` on `n`
alone with `‖(U ⊗ I) φ - η‖ ≤ a + √(2a + 2b + b²)`. The unitary is the polar factor
of `R'`, which may be singular.
Source: `09-amplification.tex`, lines 510–545. -/
theorem exists_unitary_kronecker_sub_le (R : Matrix n n ℂ)
    {φ η : EuclideanSpace ℂ (n × m)} (hφ : ‖φ‖ = 1) (hη : ‖η‖ = 1) {a b : ℝ}
    (hadj : ‖L₂ (R ⊗ₖ (1 : Matrix m m ℂ))ᴴ η - φ‖ ≤ a)
    (hdir : ‖L₂ (R ⊗ₖ (1 : Matrix m m ℂ)) φ‖ ≤ 1 + b) :
    ∃ U : unitaryGroup n ℂ,
      ‖L₂ ((U : Matrix n n ℂ) ⊗ₖ (1 : Matrix m m ℂ)) φ - η‖ ≤
        a + √(2 * a + 2 * b + b ^ 2) := by
  obtain ⟨U, hU, -, -⟩ := exists_unitary_polar_correction R
  refine ⟨U, ?_⟩
  have hcorr := (unitary_polar_correction_kronecker_one (m := m) R U hU).2.2.2 φ η
  have hdirect := Real.abs_le_sqrt
    (norm_sub_sq_le_of_adjoint_error (R ⊗ₖ (1 : Matrix m m ℂ)) hφ hη hadj hdir)
  rw [abs_of_nonneg (norm_nonneg _)] at hdirect
  linarith only [hcorr, hdirect, hadj]

/-- **The deterministic steps after the choice of a good realization**
(`eq:amplification-before-polar` through `eq:amplification-unitary-error`). Let
`R₀` and `L'` be local operators on `n`, with `M₀ ≥ 1` bounding the restoring vector
`ζ = (R₀ ⊗ I) φ`. Suppose the full product `D` fixes the ground component `g` of `ζ`,
`‖g‖ ≤ 1`, and on the chosen realization the excited component, the omitted events
and `M₀` times the truncation error are at most `ε`. If the adjoint error of
`R' = L' R₀` is at most `a`, then some unitary `U` on `n` alone satisfies
`‖(U ⊗ I) φ - η‖ ≤ a + √(2a + 6ε + 9ε²)`.
Source: `09-amplification.tex`, lines 493–545. -/
theorem exists_unitary_kronecker_sub_le_of_good_realization
    (R₀ L' : Matrix n n ℂ) {D Dret : Matrix (n × m) (n × m) ℂ}
    {φ η g : EuclideanSpace ℂ (n × m)} (hφ : ‖φ‖ = 1) (hη : ‖η‖ = 1)
    {M₀ ε a : ℝ}
    (hζ : ‖L₂ (R₀ ⊗ₖ (1 : Matrix m m ℂ)) φ‖ ≤ M₀)
    (hg : L₂ D g = g) (hgn : ‖g‖ ≤ 1)
    (hexc : ‖L₂ D (L₂ (R₀ ⊗ₖ (1 : Matrix m m ℂ)) φ - g)‖ ≤ ε)
    (hret : ‖L₂ (D - Dret) (L₂ (R₀ ⊗ₖ (1 : Matrix m m ℂ)) φ)‖ ≤ ε)
    (htrunc : M₀ * ‖L₂ (Dret - L' ⊗ₖ (1 : Matrix m m ℂ))‖ ≤ ε)
    (hadj : ‖L₂ ((L' * R₀) ⊗ₖ (1 : Matrix m m ℂ))ᴴ η - φ‖ ≤ a) :
    ∃ U : unitaryGroup n ℂ,
      ‖L₂ ((U : Matrix n n ℂ) ⊗ₖ (1 : Matrix m m ℂ)) φ - η‖ ≤
        a + √(2 * a + 6 * ε + 9 * ε ^ 2) := by
  have hdir := norm_truncated_restoring_le hg hgn hexc hret htrunc hζ
  have hprod : L₂ ((L' * R₀) ⊗ₖ (1 : Matrix m m ℂ)) φ =
      L₂ (L' ⊗ₖ (1 : Matrix m m ℂ)) (L₂ (R₀ ⊗ₖ (1 : Matrix m m ℂ)) φ) := by
    rw [← mul_apply_eq_comp, ← map_mul, ← mul_kronecker_mul, one_mul]
  rw [← hprod] at hdir
  obtain ⟨U, hU⟩ := exists_unitary_kronecker_sub_le (L' * R₀) hφ hη hadj hdir
  refine ⟨U, hU.trans_eq ?_⟩
  congr 2
  ring

end Spectator

end TNLean.PEPS.AreaLaw
