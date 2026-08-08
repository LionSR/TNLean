/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import TNLean.Channel.Wigner.Upstream.CocycleConsistency

/-!
# Projective Wigner rigidity: complex probes, ray reconstruction, and the local unitary/antiunitary dichotomy

This module is adapted from
`CsdLean4/Mathlib/LinearAlgebra/Projectivization/WignerRigidity.lean` in
`zblore/csd-lean4` at commit
`55ac6758832291c8b0fb94d78e10dc47b1cb8a06`, under the Apache License 2.0.
The upstream single source file was split mechanically at semantic section
boundaries, preserving declaration order, to satisfy TNLean's module-size policy.
The only proof-level adaptation is inherited from the reduced Lean 4.32 import
cone; this section's upstream proof text is otherwise unchanged.
-/

@[expose] public section

open scoped LinearAlgebra.Projectivization ComplexOrder
open Matrix

namespace Projectivization

variable {N : ℕ}
variable {f : ℙ ℂ (EuclideanSpace ℂ (Fin N)) → ℙ ℂ (EuclideanSpace ℂ (Fin N))}

/-! ## Stage 3 piece 3 (W5): the complex probe, the global sign, and the dichotomy

Piece 3 is the finish. Pieces 1–2 established the phase-cocycle **coboundary
structure** through **real-coordinate** probes, which cannot see the global
unitary/antiunitary sign (they are fixed by the identity and by coordinatewise
conjugation alike). Piece 3 introduces the **complex probe** `mk (b i₀ + I • b i)`,
whose ray is *not* conjugation-invariant, so it **distinguishes** the two branches,
and assembles the global dichotomy.

The layout:

* **Imaginary relative phase.** The `I`-probe overlap
  (`transProb_two_level_I`, `transProb_two_level_negI`) pins the *imaginary*
  part of the relative phase, the datum invisible to piece 2:
  `two_level_imrelphase_of_fixes` (from a fixed complex ray) and
  `two_level_imrelphase_of_flips` (from a flipped one, the antiunitary reading).
* **Reconstruction.** Given a `TransProbPreserving` map fixing every basis ray,
  every real two-level ray `mk (b i + b j)`, and every complex two-level ray
  `mk (b i + I • b j)`, the full Gram datum `conj dᵢ · dⱼ · ‖ψ‖² =
  conj cᵢ · cⱼ · ‖φ‖²` is pinned, forcing `φ = λ • ψ`, i.e. the map is the
  **identity on rays** (`eq_id_of_fixes_all_two_level`). If instead the complex
  rays are *flipped*, the datum conjugates and the map is **coordinatewise
  conjugation** in the basis `b` (`eq_bconj_of_flips_complex`). ℂ-linearity is an
  **output** of this reconstruction, never an input.
* **The complex probe local dichotomy.** For each `i ≠ i₀` the diagonally reduced
  map sends `mk (b i₀ + I • b i)` to `mk (b i₀ + I • b i)` (plus branch) or
  `mk (b i₀ - I • b i)` (minus branch): the anchored real-part relation forces the
  image phase to have zero real part, and unit modulus leaves exactly `± I`
  (`diagReducedMap_complex_probe`).

No ℂ-linearity is assumed anywhere below. -/

/-- The imaginary-part conversion `(x · I · conj y).re = (conj x · y).im`,
a coordinate identity in `ℂ`. -/
lemma re_mul_I_eq_im (x y : ℂ) :
    (x * Complex.I * (starRingEnd ℂ) y).re = ((starRingEnd ℂ) x * y).im := by
  simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.conj_re, Complex.conj_im]; ring

/-- **Complex "difference" parallelogram.** `‖A - I·B‖² = ‖A‖² + ‖B‖²
+ 2·(conj A · B).im`. Pure real-coordinate algebra via `Complex.normSq`. -/
lemma cnorm_sub_I_sq (A B : ℂ) :
    ‖A - Complex.I * B‖ ^ 2 = ‖A‖ ^ 2 + ‖B‖ ^ 2 + 2 * ((starRingEnd ℂ) A * B).im := by
  rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re,
    Complex.mul_im, Complex.I_re, Complex.I_im, Complex.conj_re, Complex.conj_im]
  ring

/-- **Complex "sum" parallelogram with `I`.** `‖A + I·B‖² = ‖A‖² + ‖B‖²
- 2·(conj A · B).im`. Pure real-coordinate algebra via `Complex.normSq`. -/
lemma cnorm_add_I_sq (A B : ℂ) :
    ‖A + Complex.I * B‖ ^ 2 = ‖A‖ ^ 2 + ‖B‖ ^ 2 - 2 * ((starRingEnd ℂ) A * B).im := by
  rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re,
    Complex.mul_im, Complex.I_re, Complex.I_im, Complex.conj_re, Complex.conj_im]
  ring

/-! ### The `I`-probe `b i + I • b j` -/

/-- Squared norm of the `I`-probe: `‖b i + I • b j‖² = 2` (Pythagoras,
`‖I • b j‖ = ‖b j‖ = 1`). -/
lemma Iadd_basis_norm_sq
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N)))
    {i j : Fin N} (hij : i ≠ j) :
    ‖(b i + Complex.I • b j : EuclideanSpace ℂ (Fin N))‖ ^ 2 = 2 := by
  have hperp : (inner ℂ (b i) (Complex.I • b j) : ℂ) = 0 := by
    rw [inner_smul_right, orthonormal_iff_ite.mp b.orthonormal i j, if_neg hij, mul_zero]
  rw [sq, norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (b i) (Complex.I • b j) hperp,
      b.orthonormal.norm_eq_one i, norm_smul, Complex.norm_I, one_mul,
      b.orthonormal.norm_eq_one j]
  norm_num

/-- The `I`-probe is nonzero (norm² = 2). -/
lemma Iadd_basis_ne_zero
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N)))
    {i j : Fin N} (hij : i ≠ j) :
    (b i + Complex.I • b j : EuclideanSpace ℂ (Fin N)) ≠ 0 := by
  intro h
  have hn := Iadd_basis_norm_sq b hij
  rw [h, norm_zero, zero_pow (by norm_num)] at hn
  norm_num at hn

/-- Inner product of `ψ` with the `I`-probe:
`⟪ψ, b i + I • b j⟫ = conj cᵢ + I · conj cⱼ`. -/
lemma inner_Iadd_basis
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N)))
    (ψ : EuclideanSpace ℂ (Fin N)) (i j : Fin N) :
    (inner ℂ ψ (b i + Complex.I • b j) : ℂ)
      = (starRingEnd ℂ) (b.repr ψ i) + Complex.I * (starRingEnd ℂ) (b.repr ψ j) := by
  rw [inner_add_right, inner_smul_right, inner_eq_conj_repr b ψ i, inner_eq_conj_repr b ψ j]

/-- **`I`-probe overlap.** `transProb (mk ψ) (mk (b i + I • b j))
= ‖cᵢ - I · cⱼ‖² / (‖ψ‖² · 2)`. The numerator conjugate identity
`conj cᵢ + I · conj cⱼ = conj (cᵢ - I · cⱼ)` plus `RCLike.norm_conj` puts it in the
`c`-coordinate form. -/
lemma transProb_two_level_I
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N)))
    {ψ : EuclideanSpace ℂ (Fin N)} (hψ : ψ ≠ 0) {i j : Fin N} (hij : i ≠ j) :
    transProb (Projectivization.mk ℂ ψ hψ)
        (Projectivization.mk ℂ (b i + Complex.I • b j) (Iadd_basis_ne_zero b hij))
      = ‖b.repr ψ i - Complex.I * b.repr ψ j‖ ^ 2 / (‖ψ‖ ^ 2 * 2) := by
  have hnum : ((starRingEnd ℂ) (b.repr ψ i) + Complex.I * (starRingEnd ℂ) (b.repr ψ j))
      = (starRingEnd ℂ) (b.repr ψ i - Complex.I * b.repr ψ j) := by
    rw [map_sub, map_mul, Complex.conj_I]; ring
  rw [transProb_mk hψ (Iadd_basis_ne_zero b hij)]
  unfold transProbVec
  rw [inner_Iadd_basis, Iadd_basis_norm_sq b hij, hnum, RCLike.norm_conj]

/-- **Imaginary relative-phase constraint (fixed complex ray).** Let `g` be
`TransProbPreserving`, fixing every basis ray and the complex two-level ray
`mk (b i + I • b j)`. Writing `g (mk ψ) = mk φ`, the *imaginary* part of the
relative phase is preserved: `Im(conj dᵢ · dⱼ) / ‖φ‖² = Im(conj cᵢ · cⱼ) / ‖ψ‖²`.
The `I`-probe is *not* conjugation-invariant, so this is the datum piece 2 could
not reach. Pure overlap algebra; no ℂ-linearity. -/
theorem two_level_imrelphase_of_fixes
    {g : ℙ ℂ (EuclideanSpace ℂ (Fin N)) → ℙ ℂ (EuclideanSpace ℂ (Fin N))}
    (hg : TransProbPreserving g)
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N)))
    (hfixb : ∀ k, g (srcPoint b k) = srcPoint b k)
    {i j : Fin N} (hij : i ≠ j)
    (hfixI : g (Projectivization.mk ℂ (b i + Complex.I • b j) (Iadd_basis_ne_zero b hij))
      = Projectivization.mk ℂ (b i + Complex.I • b j) (Iadd_basis_ne_zero b hij))
    {ψ : EuclideanSpace ℂ (Fin N)} (hψ : ψ ≠ 0) :
    ((starRingEnd ℂ) (b.repr (g (Projectivization.mk ℂ ψ hψ)).rep i)
          * b.repr (g (Projectivization.mk ℂ ψ hψ)).rep j).im
        / ‖(g (Projectivization.mk ℂ ψ hψ)).rep‖ ^ 2
      = ((starRingEnd ℂ) (b.repr ψ i) * b.repr ψ j).im / ‖ψ‖ ^ 2 := by
  have hA := hg.transProb_of_fixed hfixI (Projectivization.mk ℂ ψ hψ)
  rw [transProb_two_level_I b hψ hij] at hA
  have md0 := coord_modulus_of_fixes_basis hg b hfixb hψ i
  have mdi := coord_modulus_of_fixes_basis hg b hfixb hψ j
  set q := g (Projectivization.mk ℂ ψ hψ) with hq
  have hLHS : transProb q
        (Projectivization.mk ℂ (b i + Complex.I • b j) (Iadd_basis_ne_zero b hij))
      = ‖b.repr q.rep i - Complex.I * b.repr q.rep j‖ ^ 2 / (‖q.rep‖ ^ 2 * 2) := by
    conv_lhs => rw [← q.mk_rep]
    exact transProb_two_level_I b q.rep_nonzero hij
  rw [hLHS] at hA
  have hDφ : ‖q.rep‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr q.rep_nonzero)
  have hDψ : ‖ψ‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hψ)
  have hcross := (div_eq_div_iff (mul_ne_zero hDφ (by norm_num : (2 : ℝ) ≠ 0))
    (mul_ne_zero hDψ (by norm_num : (2 : ℝ) ≠ 0))).mp hA
  rw [cnorm_sub_I_sq, cnorm_sub_I_sq] at hcross
  have hm0 := (div_eq_div_iff hDφ hDψ).mp md0
  have hmi := (div_eq_div_iff hDφ hDψ).mp mdi
  rw [div_eq_div_iff hDφ hDψ]
  linear_combination (1 / 4 : ℝ) * hcross - (1 / 2 : ℝ) * hm0 - (1 / 2 : ℝ) * hmi

/-! ### The `-I`-probe `b i - I • b j` (the flipped complex ray) -/

/-- Squared norm of the `-I`-probe: `‖b i - I • b j‖² = 2`. -/
lemma subI_basis_norm_sq
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N)))
    {i j : Fin N} (hij : i ≠ j) :
    ‖(b i - Complex.I • b j : EuclideanSpace ℂ (Fin N))‖ ^ 2 = 2 := by
  have hperp : (inner ℂ (b i) (-(Complex.I • b j)) : ℂ) = 0 := by
    rw [inner_neg_right, inner_smul_right, orthonormal_iff_ite.mp b.orthonormal i j,
        if_neg hij, mul_zero, neg_zero]
  rw [sub_eq_add_neg, sq,
      norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (b i) (-(Complex.I • b j)) hperp,
      b.orthonormal.norm_eq_one i, norm_neg, norm_smul, Complex.norm_I, one_mul,
      b.orthonormal.norm_eq_one j]
  norm_num

/-- The `-I`-probe is nonzero (norm² = 2). -/
lemma subI_basis_ne_zero
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N)))
    {i j : Fin N} (hij : i ≠ j) :
    (b i - Complex.I • b j : EuclideanSpace ℂ (Fin N)) ≠ 0 := by
  intro h
  have hn := subI_basis_norm_sq b hij
  rw [h, norm_zero, zero_pow (by norm_num)] at hn
  norm_num at hn

/-- Inner product of `ψ` with the `-I`-probe:
`⟪ψ, b i - I • b j⟫ = conj cᵢ - I · conj cⱼ`. -/
lemma inner_subI_basis
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N)))
    (ψ : EuclideanSpace ℂ (Fin N)) (i j : Fin N) :
    (inner ℂ ψ (b i - Complex.I • b j) : ℂ)
      = (starRingEnd ℂ) (b.repr ψ i) - Complex.I * (starRingEnd ℂ) (b.repr ψ j) := by
  rw [inner_sub_right, inner_smul_right, inner_eq_conj_repr b ψ i, inner_eq_conj_repr b ψ j]

/-- **`-I`-probe overlap.** `transProb (mk ψ) (mk (b i - I • b j))
= ‖cᵢ + I · cⱼ‖² / (‖ψ‖² · 2)`. -/
lemma transProb_two_level_negI
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N)))
    {ψ : EuclideanSpace ℂ (Fin N)} (hψ : ψ ≠ 0) {i j : Fin N} (hij : i ≠ j) :
    transProb (Projectivization.mk ℂ ψ hψ)
        (Projectivization.mk ℂ (b i - Complex.I • b j) (subI_basis_ne_zero b hij))
      = ‖b.repr ψ i + Complex.I * b.repr ψ j‖ ^ 2 / (‖ψ‖ ^ 2 * 2) := by
  have hnum : ((starRingEnd ℂ) (b.repr ψ i) - Complex.I * (starRingEnd ℂ) (b.repr ψ j))
      = (starRingEnd ℂ) (b.repr ψ i + Complex.I * b.repr ψ j) := by
    rw [map_add, map_mul, Complex.conj_I]; ring
  rw [transProb_mk hψ (subI_basis_ne_zero b hij)]
  unfold transProbVec
  rw [inner_subI_basis, subI_basis_norm_sq b hij, hnum, RCLike.norm_conj]

/-- **Imaginary relative-phase constraint (flipped complex ray).** If `g`
`TransProbPreserving` fixes every basis ray and *flips* the complex two-level ray,
`g (mk (b i + I • b j)) = mk (b i - I • b j)`, then the imaginary part of the
relative phase is **negated**: `Im(conj dᵢ · dⱼ) / ‖φ‖² = -Im(conj cᵢ · cⱼ) / ‖ψ‖²`.
This is the antiunitary reading. No ℂ-linearity. -/
theorem two_level_imrelphase_of_flips
    {g : ℙ ℂ (EuclideanSpace ℂ (Fin N)) → ℙ ℂ (EuclideanSpace ℂ (Fin N))}
    (hg : TransProbPreserving g)
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N)))
    (hfixb : ∀ k, g (srcPoint b k) = srcPoint b k)
    {i j : Fin N} (hij : i ≠ j)
    (hflipI : g (Projectivization.mk ℂ (b i + Complex.I • b j) (Iadd_basis_ne_zero b hij))
      = Projectivization.mk ℂ (b i - Complex.I • b j) (subI_basis_ne_zero b hij))
    {ψ : EuclideanSpace ℂ (Fin N)} (hψ : ψ ≠ 0) :
    ((starRingEnd ℂ) (b.repr (g (Projectivization.mk ℂ ψ hψ)).rep i)
          * b.repr (g (Projectivization.mk ℂ ψ hψ)).rep j).im
        / ‖(g (Projectivization.mk ℂ ψ hψ)).rep‖ ^ 2
      = (-((starRingEnd ℂ) (b.repr ψ i) * b.repr ψ j).im) / ‖ψ‖ ^ 2 := by
  have hA := hg (Projectivization.mk ℂ ψ hψ)
    (Projectivization.mk ℂ (b i + Complex.I • b j) (Iadd_basis_ne_zero b hij))
  rw [hflipI, transProb_two_level_I b hψ hij] at hA
  have md0 := coord_modulus_of_fixes_basis hg b hfixb hψ i
  have mdi := coord_modulus_of_fixes_basis hg b hfixb hψ j
  set q := g (Projectivization.mk ℂ ψ hψ) with hq
  have hLHS : transProb q
        (Projectivization.mk ℂ (b i - Complex.I • b j) (subI_basis_ne_zero b hij))
      = ‖b.repr q.rep i + Complex.I * b.repr q.rep j‖ ^ 2 / (‖q.rep‖ ^ 2 * 2) := by
    conv_lhs => rw [← q.mk_rep]
    exact transProb_two_level_negI b q.rep_nonzero hij
  rw [hLHS] at hA
  have hDφ : ‖q.rep‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr q.rep_nonzero)
  have hDψ : ‖ψ‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hψ)
  have hcross := (div_eq_div_iff (mul_ne_zero hDφ (by norm_num : (2 : ℝ) ≠ 0))
    (mul_ne_zero hDψ (by norm_num : (2 : ℝ) ≠ 0))).mp hA
  rw [cnorm_add_I_sq, cnorm_sub_I_sq] at hcross
  have hm0 := (div_eq_div_iff hDφ hDψ).mp md0
  have hmi := (div_eq_div_iff hDφ hDψ).mp mdi
  rw [div_eq_div_iff hDφ hDψ]
  linear_combination (-(1 / 4) : ℝ) * hcross + (1 / 2 : ℝ) * hm0 + (1 / 2 : ℝ) * hmi

/-! ### Reconstruction: from the Gram datum to the identity / conjugation -/

/-- Real part of a product with a real scalar on the right: `(z · r).re = z.re · r`. -/
lemma mul_ofReal_re (z : ℂ) (r : ℝ) : (z * (r : ℂ)).re = z.re * r := by
  rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]

/-- Imaginary part of a product with a real scalar on the right: `(z · r).im = z.im · r`. -/
lemma mul_ofReal_im (z : ℂ) (r : ℝ) : (z * (r : ℂ)).im = z.im * r := by
  rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_add]

/-- **Reconstruction (unitary branch).** A `TransProbPreserving` map `g` fixing
every basis ray, every real two-level ray `mk (b i + b j)`, and every complex
two-level ray `mk (b i + I • b j)` is the **identity on rays**:
`g (mk ψ) = mk ψ` for every `ψ ≠ 0`.

The real relations (`two_level_relphase_of_fixes`) and the imaginary relations
(`two_level_imrelphase_of_fixes`) together pin the full Gram datum
`conj dᵢ · dⱼ · ‖ψ‖² = conj cᵢ · cⱼ · ‖φ‖²` for every pair; taking a reference
index `i₁` with `c_{i₁} ≠ 0` gives `dⱼ = λ · cⱼ` with `λ` fixed, so `φ = λ • ψ`.
**ℂ-linearity is an output here, not an input.** -/
theorem eq_id_of_fixes_all_two_level
    {g : ℙ ℂ (EuclideanSpace ℂ (Fin N)) → ℙ ℂ (EuclideanSpace ℂ (Fin N))}
    (hg : TransProbPreserving g)
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N)))
    (hfixb : ∀ k, g (srcPoint b k) = srcPoint b k)
    (hR : ∀ i j (hij : i ≠ j),
      g (Projectivization.mk ℂ (b i + b j) (add_basis_ne_zero b hij))
        = Projectivization.mk ℂ (b i + b j) (add_basis_ne_zero b hij))
    (hI : ∀ i j (hij : i ≠ j),
      g (Projectivization.mk ℂ (b i + Complex.I • b j) (Iadd_basis_ne_zero b hij))
        = Projectivization.mk ℂ (b i + Complex.I • b j) (Iadd_basis_ne_zero b hij))
    {ψ : EuclideanSpace ℂ (Fin N)} (hψ : ψ ≠ 0) :
    g (Projectivization.mk ℂ ψ hψ) = Projectivization.mk ℂ ψ hψ := by
  set φ := (g (Projectivization.mk ℂ ψ hψ)).rep with hφ_def
  have hφne : φ ≠ 0 := Projectivization.rep_nonzero _
  have hDφ : ‖φ‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hφne)
  have hDψ : ‖ψ‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hψ)
  -- reference index with nonzero source coordinate
  obtain ⟨i₁, hi₁⟩ : ∃ i₁, b.repr ψ i₁ ≠ 0 := by
    by_contra h; push Not at h
    apply hψ
    have hsum := b.sum_repr ψ
    rw [← hsum]; exact Finset.sum_eq_zero (fun j _ => by rw [h j, zero_smul])
  -- the full Gram datum
  have key : ∀ j, (starRingEnd ℂ) (b.repr φ i₁) * b.repr φ j * ((‖ψ‖ ^ 2 : ℝ) : ℂ)
      = (starRingEnd ℂ) (b.repr ψ i₁) * b.repr ψ j * ((‖φ‖ ^ 2 : ℝ) : ℂ) := by
    intro j
    rcases eq_or_ne i₁ j with h | h
    · subst h
      have hm := coord_modulus_of_fixes_basis hg b hfixb hψ i₁
      rw [← hφ_def] at hm
      have hmc := (div_eq_div_iff hDφ hDψ).mp hm
      have e1 : (starRingEnd ℂ) (b.repr φ i₁) * b.repr φ i₁ = ((‖b.repr φ i₁‖ ^ 2 : ℝ) : ℂ) := by
        rw [RCLike.conj_mul]; norm_cast
      have e2 : (starRingEnd ℂ) (b.repr ψ i₁) * b.repr ψ i₁ = ((‖b.repr ψ i₁‖ ^ 2 : ℝ) : ℂ) := by
        rw [RCLike.conj_mul]; norm_cast
      rw [e1, e2]; exact_mod_cast hmc
    · have hre := two_level_relphase_of_fixes hg b hfixb h (hR i₁ j h) hψ
      have him := two_level_imrelphase_of_fixes hg b hfixb h (hI i₁ j h) hψ
      rw [← hφ_def] at hre him
      have hrec := (div_eq_div_iff hDφ hDψ).mp hre
      have himc := (div_eq_div_iff hDφ hDψ).mp him
      apply Complex.ext
      · rw [mul_ofReal_re, mul_ofReal_re]; exact hrec
      · rw [mul_ofReal_im, mul_ofReal_im]; exact himc
  -- `d_{i₁} ≠ 0`
  have hd1 : b.repr φ i₁ ≠ 0 := by
    have hm := coord_modulus_of_fixes_basis hg b hfixb hψ i₁
    rw [← hφ_def] at hm
    intro h0
    rw [h0, norm_zero, zero_pow (by norm_num), zero_div] at hm
    have hz : ‖b.repr ψ i₁‖ ^ 2 / ‖ψ‖ ^ 2 = 0 := hm.symm
    rcases div_eq_zero_iff.mp hz with hh | hh
    · exact hi₁ (norm_eq_zero.mp (pow_eq_zero_iff (by norm_num) |>.mp hh))
    · exact hDψ hh
  set lam : ℂ := (starRingEnd ℂ) (b.repr ψ i₁) * ((‖φ‖ ^ 2 : ℝ) : ℂ)
      / ((starRingEnd ℂ) (b.repr φ i₁) * ((‖ψ‖ ^ 2 : ℝ) : ℂ)) with hlam
  have hden' : (starRingEnd ℂ) (b.repr φ i₁) * ((‖ψ‖ ^ 2 : ℝ) : ℂ) ≠ 0 :=
    mul_ne_zero (by simpa using hd1) (by exact_mod_cast hDψ)
  have hcoord : ∀ j, b.repr φ j = lam * b.repr ψ j := by
    intro j
    rw [hlam, div_mul_eq_mul_div, eq_div_iff hden']
    linear_combination (key j)
  have hlamne : lam ≠ 0 := by
    rw [hlam]
    apply div_ne_zero
    · exact mul_ne_zero (by simpa using hi₁) (by exact_mod_cast hDφ)
    · exact hden'
  have hφlam : φ = lam • ψ := by
    rw [← b.sum_repr φ, ← b.sum_repr ψ, Finset.smul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [hcoord j, smul_smul]
  have hmkψ : g (Projectivization.mk ℂ ψ hψ) = Projectivization.mk ℂ φ hφne :=
    (Projectivization.mk_rep _).symm
  rw [hmkψ]
  exact (Projectivization.mk_eq_mk_iff' ℂ φ ψ hφne hψ).mpr ⟨lam, hφlam.symm⟩

/-- Coordinatewise complex conjugation **in the basis `b`**:
`bConjVec b ψ = ∑ⱼ conj(b.repr ψ j) • b j`. Its `k`-th coordinate is
`conj(b.repr ψ k)` (`repr_bConjVec`). For the standard basis this is `conjVec`. -/
noncomputable def bConjVec
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N)))
    (ψ : EuclideanSpace ℂ (Fin N)) : EuclideanSpace ℂ (Fin N) :=
  ∑ j, (starRingEnd ℂ) (b.repr ψ j) • b j

/-- The `k`-th coordinate of `bConjVec b ψ` is `conj (b.repr ψ k)`. -/
lemma repr_bConjVec
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N)))
    (ψ : EuclideanSpace ℂ (Fin N)) (k : Fin N) :
    b.repr (bConjVec b ψ) k = (starRingEnd ℂ) (b.repr ψ k) := by
  rw [b.repr_apply_apply]
  unfold bConjVec
  rw [inner_sum, Finset.sum_eq_single k]
  · rw [inner_smul_right, orthonormal_iff_ite.mp b.orthonormal k k, if_pos rfl, mul_one]
  · intro j _ hjk
    rw [inner_smul_right, orthonormal_iff_ite.mp b.orthonormal k j, if_neg (Ne.symm hjk),
        mul_zero]
  · intro h; exact absurd (Finset.mem_univ k) h

/-- `bConjVec b ψ` is nonzero when `ψ` is (some conjugate coordinate is nonzero). -/
lemma bConjVec_ne_zero
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N)))
    {ψ : EuclideanSpace ℂ (Fin N)} (hψ : ψ ≠ 0) : bConjVec b ψ ≠ 0 := by
  obtain ⟨k, hk⟩ : ∃ k, b.repr ψ k ≠ 0 := by
    by_contra h; push Not at h; apply hψ
    rw [← b.sum_repr ψ]; exact Finset.sum_eq_zero (fun j _ => by rw [h j, zero_smul])
  intro h0
  have hk0 : (starRingEnd ℂ) (b.repr ψ k) = 0 := by
    rw [← repr_bConjVec b ψ k, h0]; simp
  exact hk (by simpa using hk0)

/-- A unit-modulus complex number with zero real part is `± I`. Squaring the norm,
`ε.im² = 1`, so `ε.im = ±1` and `ε = ⟨0, ±1⟩`. -/
lemma unit_re_zero_eq_I_or_negI {ε : ℂ} (h1 : ‖ε‖ = 1) (h2 : ε.re = 0) :
    ε = Complex.I ∨ ε = -Complex.I := by
  have hkey : ε.re * ε.re + ε.im * ε.im = 1 := by
    rw [← Complex.normSq_apply, Complex.normSq_eq_norm_sq, h1]; norm_num
  rw [h2] at hkey
  have him : ε.im = 1 ∨ ε.im = -1 := by
    have hii : ε.im * ε.im = 1 := by linarith
    exact mul_self_eq_one_iff.mp hii
  rcases him with h | h
  · left; apply Complex.ext
    · rw [h2, Complex.I_re]
    · rw [h, Complex.I_im]
  · right; apply Complex.ext
    · rw [h2, Complex.neg_re, Complex.I_re, neg_zero]
    · rw [h, Complex.neg_im, Complex.I_im]

/-- **Reconstruction (antiunitary branch).** A `TransProbPreserving` map `g` fixing
every basis ray, every real two-level ray `mk (b i + b j)`, and *flipping* every
complex two-level ray, `g (mk (b i + I • b j)) = mk (b i - I • b j)`, is
**coordinatewise conjugation** in the basis `b`:
`g (mk ψ) = mk (bConjVec b ψ)` for every `ψ ≠ 0`.

The real relations survive, but the imaginary relations are negated
(`two_level_imrelphase_of_flips`), conjugating the Gram datum to
`conj dᵢ · dⱼ · ‖ψ‖² = cᵢ · conj cⱼ · ‖φ‖²`, so `dⱼ = μ · conj cⱼ` and
`φ = μ • bConjVec b ψ`. **No ℂ-linearity is assumed**; this is the genuine
antiunitary branch of the Wigner disjunction. -/
theorem eq_bconj_of_flips_complex
    {g : ℙ ℂ (EuclideanSpace ℂ (Fin N)) → ℙ ℂ (EuclideanSpace ℂ (Fin N))}
    (hg : TransProbPreserving g)
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N)))
    (hfixb : ∀ k, g (srcPoint b k) = srcPoint b k)
    (hR : ∀ i j (hij : i ≠ j),
      g (Projectivization.mk ℂ (b i + b j) (add_basis_ne_zero b hij))
        = Projectivization.mk ℂ (b i + b j) (add_basis_ne_zero b hij))
    (hflip : ∀ i j (hij : i ≠ j),
      g (Projectivization.mk ℂ (b i + Complex.I • b j) (Iadd_basis_ne_zero b hij))
        = Projectivization.mk ℂ (b i - Complex.I • b j) (subI_basis_ne_zero b hij))
    {ψ : EuclideanSpace ℂ (Fin N)} (hψ : ψ ≠ 0) :
    g (Projectivization.mk ℂ ψ hψ)
      = Projectivization.mk ℂ (bConjVec b ψ) (bConjVec_ne_zero b hψ) := by
  set φ := (g (Projectivization.mk ℂ ψ hψ)).rep with hφ_def
  have hφne : φ ≠ 0 := Projectivization.rep_nonzero _
  have hDφ : ‖φ‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hφne)
  have hDψ : ‖ψ‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hψ)
  obtain ⟨i₁, hi₁⟩ : ∃ i₁, b.repr ψ i₁ ≠ 0 := by
    by_contra h; push Not at h
    apply hψ
    rw [← b.sum_repr ψ]; exact Finset.sum_eq_zero (fun j _ => by rw [h j, zero_smul])
  have key : ∀ j, (starRingEnd ℂ) (b.repr φ i₁) * b.repr φ j * ((‖ψ‖ ^ 2 : ℝ) : ℂ)
      = (starRingEnd ℂ) ((starRingEnd ℂ) (b.repr ψ i₁) * b.repr ψ j) * ((‖φ‖ ^ 2 : ℝ) : ℂ) := by
    intro j
    rcases eq_or_ne i₁ j with h | h
    · subst h
      have hm := coord_modulus_of_fixes_basis hg b hfixb hψ i₁
      rw [← hφ_def] at hm
      have hmc := (div_eq_div_iff hDφ hDψ).mp hm
      have e1 : (starRingEnd ℂ) (b.repr φ i₁) * b.repr φ i₁ = ((‖b.repr φ i₁‖ ^ 2 : ℝ) : ℂ) := by
        rw [RCLike.conj_mul]; norm_cast
      have e2 : (starRingEnd ℂ) (b.repr ψ i₁) * b.repr ψ i₁ = ((‖b.repr ψ i₁‖ ^ 2 : ℝ) : ℂ) := by
        rw [RCLike.conj_mul]; norm_cast
      have hconj_real : (starRingEnd ℂ) ((starRingEnd ℂ) (b.repr ψ i₁) * b.repr ψ i₁)
          = (starRingEnd ℂ) (b.repr ψ i₁) * b.repr ψ i₁ := by
        rw [map_mul, Complex.conj_conj, mul_comm]
      rw [e1, hconj_real, e2, ← Complex.ofReal_mul, ← Complex.ofReal_mul, Complex.ofReal_inj]
      exact hmc
    · have hre := two_level_relphase_of_fixes hg b hfixb h (hR i₁ j h) hψ
      have him := two_level_imrelphase_of_flips hg b hfixb h (hflip i₁ j h) hψ
      rw [← hφ_def] at hre him
      have hrec := (div_eq_div_iff hDφ hDψ).mp hre
      have himc := (div_eq_div_iff hDφ hDψ).mp him
      apply Complex.ext
      · rw [mul_ofReal_re, mul_ofReal_re, Complex.conj_re]; exact hrec
      · rw [mul_ofReal_im, mul_ofReal_im, Complex.conj_im]; exact himc
  have hd1 : b.repr φ i₁ ≠ 0 := by
    have hm := coord_modulus_of_fixes_basis hg b hfixb hψ i₁
    rw [← hφ_def] at hm
    intro h0
    rw [h0, norm_zero, zero_pow (by norm_num), zero_div] at hm
    have hz : ‖b.repr ψ i₁‖ ^ 2 / ‖ψ‖ ^ 2 = 0 := hm.symm
    rcases div_eq_zero_iff.mp hz with hh | hh
    · exact hi₁ (norm_eq_zero.mp (pow_eq_zero_iff (by norm_num) |>.mp hh))
    · exact hDψ hh
  set mu : ℂ := b.repr ψ i₁ * ((‖φ‖ ^ 2 : ℝ) : ℂ)
      / ((starRingEnd ℂ) (b.repr φ i₁) * ((‖ψ‖ ^ 2 : ℝ) : ℂ)) with hmu
  have hden' : (starRingEnd ℂ) (b.repr φ i₁) * ((‖ψ‖ ^ 2 : ℝ) : ℂ) ≠ 0 :=
    mul_ne_zero (by simpa using hd1) (by exact_mod_cast hDψ)
  have hcoord : ∀ j, b.repr φ j = mu * (starRingEnd ℂ) (b.repr ψ j) := by
    intro j
    have hk : (starRingEnd ℂ) (b.repr φ i₁) * b.repr φ j * ((‖ψ‖ ^ 2 : ℝ) : ℂ)
        = b.repr ψ i₁ * (starRingEnd ℂ) (b.repr ψ j) * ((‖φ‖ ^ 2 : ℝ) : ℂ) := by
      have := key j
      rwa [map_mul, Complex.conj_conj] at this
    rw [hmu, div_mul_eq_mul_div, eq_div_iff hden']
    linear_combination hk
  have hmune : mu ≠ 0 := by
    rw [hmu]
    exact div_ne_zero (mul_ne_zero hi₁ (by exact_mod_cast hDφ)) hden'
  have hφmu : φ = mu • bConjVec b ψ := by
    rw [← b.sum_repr φ]
    unfold bConjVec
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [hcoord j, smul_smul]
  have hmkψ : g (Projectivization.mk ℂ ψ hψ) = Projectivization.mk ℂ φ hφne :=
    (Projectivization.mk_rep _).symm
  rw [hmkψ]
  exact (Projectivization.mk_eq_mk_iff' ℂ φ (bConjVec b ψ) hφne (bConjVec_ne_zero b hψ)).mpr
    ⟨mu, hφmu.symm⟩

/-! ### The complex probe: the branch-distinguishing local dichotomy -/

/-- **HEADLINE (the complex probe).** For `i ≠ i₀` the diagonally reduced map sends
the complex probe ray `mk (b i₀ + I • b i)` to *either* itself (**plus** branch)
*or* `mk (b i₀ - I • b i)` (**minus** branch).

Unlike the real probes of pieces 1–2, the complex probe ray is *not* invariant
under coordinatewise conjugation (`conjVec (b i₀ + I • b i) = b i₀ - I • b i`), so
it **distinguishes** the unitary branch (`+`) from the antiunitary branch (`-`).

Proof. Stage-1 moduli restrict the image `φ` to support `{i₀, i}` with equal
coordinate moduli. The anchored real relation
(`diagReducedMap_two_level_relphase`) at the source coordinates `c_{i₀} = 1`,
`c_i = I` gives `Re(conj d_{i₀} · d_i) = 0`, so the ratio `ε := d_i / d_{i₀}` has
zero real part and unit modulus, hence `ε = ± I` (`unit_re_zero_eq_I_or_negI`).
The two signs are the two branches. No ℂ-linearity is assumed. -/
theorem diagReducedMap_complex_probe
    (hf : TransProbPreserving f)
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N))) {i₀ i : Fin N} (hii : i₀ ≠ i) :
    diagReducedMap hf b i₀
        (Projectivization.mk ℂ (b i₀ + Complex.I • b i) (Iadd_basis_ne_zero b hii))
      = Projectivization.mk ℂ (b i₀ + Complex.I • b i) (Iadd_basis_ne_zero b hii)
    ∨ diagReducedMap hf b i₀
        (Projectivization.mk ℂ (b i₀ + Complex.I • b i) (Iadd_basis_ne_zero b hii))
      = Projectivization.mk ℂ (b i₀ - Complex.I • b i) (subI_basis_ne_zero b hii) := by
  have hg : TransProbPreserving (diagReducedMap hf b i₀) :=
    diagReducedMap_transProbPreserving hf b i₀
  have hfixb : ∀ k, diagReducedMap hf b i₀ (srcPoint b k) = srcPoint b k := fun k => by
    rw [srcPoint_eq]; exact diagReducedMap_fixes_basis hf b i₀ k
  set w : EuclideanSpace ℂ (Fin N) := b i₀ + Complex.I • b i with hw
  have hwne : w ≠ 0 := Iadd_basis_ne_zero b hii
  have hwnorm : ‖w‖ ^ 2 = 2 := Iadd_basis_norm_sq b hii
  -- coordinates of `w`
  have hw_i0 : b.repr w i₀ = 1 := by
    rw [hw, b.repr_apply_apply, inner_add_right, inner_smul_right,
        orthonormal_iff_ite.mp b.orthonormal i₀ i₀, if_pos rfl,
        orthonormal_iff_ite.mp b.orthonormal i₀ i, if_neg hii, mul_zero, add_zero]
  have hw_i : b.repr w i = Complex.I := by
    rw [hw, b.repr_apply_apply, inner_add_right, inner_smul_right,
        orthonormal_iff_ite.mp b.orthonormal i i₀, if_neg (Ne.symm hii),
        orthonormal_iff_ite.mp b.orthonormal i i, if_pos rfl, mul_one, zero_add]
  have hw_zero : ∀ k, k ≠ i₀ → k ≠ i → b.repr w k = 0 := by
    intro k hk0 hki
    rw [hw, b.repr_apply_apply, inner_add_right, inner_smul_right,
        orthonormal_iff_ite.mp b.orthonormal k i₀, if_neg hk0,
        orthonormal_iff_ite.mp b.orthonormal k i, if_neg hki, mul_zero, add_zero]
  set φ := (diagReducedMap hf b i₀ (Projectivization.mk ℂ w hwne)).rep with hφ
  have hφne : φ ≠ 0 := Projectivization.rep_nonzero _
  have hφpos : (0 : ℝ) < ‖φ‖ ^ 2 := pow_pos (norm_pos_iff.mpr hφne) 2
  have hden : ‖φ‖ ^ 2 ≠ 0 := ne_of_gt hφpos
  have hcm : ∀ k, ‖b.repr φ k‖ ^ 2 / ‖φ‖ ^ 2 = ‖b.repr w k‖ ^ 2 / ‖w‖ ^ 2 := by
    intro k
    have h := coord_modulus_of_fixes_basis hg b hfixb hwne k
    rwa [← hφ] at h
  -- support of `φ` is `{i₀, i}`
  have hsupp : ∀ k, k ≠ i₀ → k ≠ i → b.repr φ k = 0 := by
    intro k hk0 hki
    have hm := hcm k
    rw [hw_zero k hk0 hki, norm_zero, zero_pow (by norm_num), zero_div] at hm
    have hz : ‖b.repr φ k‖ ^ 2 = 0 := by
      rcases div_eq_zero_iff.mp hm with h | h
      · exact h
      · exact absurd h hden
    rwa [pow_eq_zero_iff (by norm_num), norm_eq_zero] at hz
  -- `d_{i₀} ≠ 0` and modulus equality
  have ha : b.repr φ i₀ ≠ 0 := by
    intro h0
    have hm := hcm i₀
    rw [h0, norm_zero, zero_pow (by norm_num), zero_div, hw_i0, norm_one, one_pow, hwnorm] at hm
    norm_num at hm
  have hmod : ‖b.repr φ i‖ = ‖b.repr φ i₀‖ := by
    have hi := hcm i
    have hi0 := hcm i₀
    rw [hw_i, Complex.norm_I, one_pow, hwnorm] at hi
    rw [hw_i0, norm_one, one_pow, hwnorm] at hi0
    have hd := hi.trans hi0.symm
    rw [div_eq_div_iff hden hden] at hd
    have heq2 : ‖b.repr φ i‖ ^ 2 = ‖b.repr φ i₀‖ ^ 2 := mul_right_cancel₀ hden hd
    rw [← Real.sqrt_sq (norm_nonneg (b.repr φ i)),
        ← Real.sqrt_sq (norm_nonneg (b.repr φ i₀)), heq2]
  -- the phase `ε := d_i / d_{i₀}` and `d_i = ε · d_{i₀}`
  set ε : ℂ := b.repr φ i / b.repr φ i₀ with hε
  have hεnorm : ‖ε‖ = 1 := by rw [hε, norm_div, hmod, div_self (norm_ne_zero_iff.mpr ha)]
  have hdi : b.repr φ i = ε * b.repr φ i₀ := by rw [hε, div_mul_cancel₀ _ ha]
  -- the anchored real relation forces `Re ε = 0`
  have hrel := diagReducedMap_two_level_relphase hf b i₀ hii hwne
  rw [← hφ, hw_i0, hw_i, hwnorm, map_one, one_mul, Complex.I_re, zero_div] at hrel
  have hRe : ((starRingEnd ℂ) (b.repr φ i₀) * b.repr φ i).re = 0 := by
    rcases div_eq_zero_iff.mp hrel with h | h
    · exact h
    · exact absurd h hden
  have hεre : ε.re = 0 := by
    rw [hdi] at hRe
    have hr : (starRingEnd ℂ) (b.repr φ i₀) * (ε * b.repr φ i₀)
        = ε * ((‖b.repr φ i₀‖ ^ 2 : ℝ) : ℂ) := by
      rw [show (starRingEnd ℂ) (b.repr φ i₀) * (ε * b.repr φ i₀)
            = ε * ((starRingEnd ℂ) (b.repr φ i₀) * b.repr φ i₀) from by ring, RCLike.conj_mul]
      norm_cast
    rw [hr, mul_ofReal_re] at hRe
    have hpos : (0 : ℝ) < ‖b.repr φ i₀‖ ^ 2 := pow_pos (norm_pos_iff.mpr ha) 2
    exact (mul_eq_zero.mp hRe).resolve_right (ne_of_gt hpos)
  -- the reconstruction of `mk w`'s image and the ± dichotomy
  have hgw : diagReducedMap hf b i₀ (Projectivization.mk ℂ w hwne)
      = Projectivization.mk ℂ φ hφne := (Projectivization.mk_rep _).symm
  have hpair : φ = b.repr φ i₀ • b i₀ + b.repr φ i • b i :=
    repr_eq_pair_of_support b φ hii hsupp
  rcases unit_re_zero_eq_I_or_negI hεnorm hεre with hI | hnI
  · left
    have hval : b.repr φ i₀ • w = φ := by
      conv_rhs => rw [hpair, hdi, hI]
      rw [hw]; module
    rw [hgw]
    exact (Projectivization.mk_eq_mk_iff' ℂ φ w hφne hwne).mpr ⟨b.repr φ i₀, hval⟩
  · right
    have hval : b.repr φ i₀ • (b i₀ - Complex.I • b i) = φ := by
      conv_rhs => rw [hpair, hdi, hnI]
      module
    rw [hgw]
    exact (Projectivization.mk_eq_mk_iff' ℂ φ (b i₀ - Complex.I • b i) hφne
      (subI_basis_ne_zero b hii)).mpr ⟨b.repr φ i₀, hval⟩

/-! ### The reduced-map dichotomy (conditional on the global complex sign) -/

/-- The diagonally reduced map fixes **every** real two-level ray `mk (b i + b j)`,
`i ≠ j` (anchored via `diagReducedMap_fixes_two_level`, non-anchored via
`diagReducedMap_fixes_two_level_general`, with an `add_comm` swap for the `j = i₀`
case). Discharges the `hR` hypothesis of the reconstruction lemmas for the
concrete diagonally reduced map. -/
theorem diagReducedMap_fixes_real_all
    (hf : TransProbPreserving f)
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N))) (i₀ : Fin N) :
    ∀ i j (hij : i ≠ j),
      diagReducedMap hf b i₀ (Projectivization.mk ℂ (b i + b j) (add_basis_ne_zero b hij))
        = Projectivization.mk ℂ (b i + b j) (add_basis_ne_zero b hij) := by
  intro i j hij
  rcases eq_or_ne i i₀ with rfl | hi
  · exact diagReducedMap_fixes_two_level hf b hij
  · rcases eq_or_ne j i₀ with rfl | hj
    · have hfix := diagReducedMap_fixes_two_level hf b (Ne.symm hij)
      have heq : Projectivization.mk ℂ (b i + b j) (add_basis_ne_zero b hij)
          = Projectivization.mk ℂ (b j + b i) (add_basis_ne_zero b (Ne.symm hij)) :=
        (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr ⟨1, by rw [one_smul, add_comm]⟩
      rw [heq, hfix]
    · exact diagReducedMap_fixes_two_level_general hf b (Ne.symm hi) (Ne.symm hj) hij

/-- **The reduced-map Wigner dichotomy (conditional on the global sign).**
Given the **global complex-sign closure** `hsign` — either the diagonally reduced
map `g := diagReducedMap hf b i₀` fixes *every* complex two-level ray
`mk (b i + I • b j)`, or it flips *every* one to `mk (b i - I • b j)` — the map is
**globally** the identity on rays, or **globally** coordinatewise conjugation in
the basis `b`:

* fixes-all branch ⟹ `g (mk ψ) = mk ψ` for all `ψ` (the **unitary** class);
* flips-all branch ⟹ `g (mk ψ) = mk (bConjVec b ψ)` for all `ψ` (the **antiunitary**
  class).

The real fixings are discharged internally (`diagReducedMap_fixes_real_all`); the
two disjuncts feed the two reconstruction lemmas. **The antiunitary branch is
genuinely present** and **ℂ-linearity is an output**, never assumed. The single
residual to an unconditional Wigner converse is `hsign`, for which
`diagReducedMap_complex_probe` supplies the per-pair `± I` datum; see the
`Stage 3 (residual)` note. -/
theorem diagReducedMap_dichotomy_of_complexSign
    (hf : TransProbPreserving f)
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N))) (i₀ : Fin N)
    (hsign :
      (∀ i j (hij : i ≠ j),
        diagReducedMap hf b i₀
            (Projectivization.mk ℂ (b i + Complex.I • b j) (Iadd_basis_ne_zero b hij))
          = Projectivization.mk ℂ (b i + Complex.I • b j) (Iadd_basis_ne_zero b hij))
      ∨ (∀ i j (hij : i ≠ j),
        diagReducedMap hf b i₀
            (Projectivization.mk ℂ (b i + Complex.I • b j) (Iadd_basis_ne_zero b hij))
          = Projectivization.mk ℂ (b i - Complex.I • b j) (subI_basis_ne_zero b hij))) :
    (∀ (ψ : EuclideanSpace ℂ (Fin N)) (hψ : ψ ≠ 0),
        diagReducedMap hf b i₀ (Projectivization.mk ℂ ψ hψ) = Projectivization.mk ℂ ψ hψ)
    ∨ (∀ (ψ : EuclideanSpace ℂ (Fin N)) (hψ : ψ ≠ 0),
        diagReducedMap hf b i₀ (Projectivization.mk ℂ ψ hψ)
          = Projectivization.mk ℂ (bConjVec b ψ) (bConjVec_ne_zero b hψ)) := by
  have hg : TransProbPreserving (diagReducedMap hf b i₀) :=
    diagReducedMap_transProbPreserving hf b i₀
  have hfixb : ∀ k, diagReducedMap hf b i₀ (srcPoint b k) = srcPoint b k := fun k => by
    rw [srcPoint_eq]; exact diagReducedMap_fixes_basis hf b i₀ k
  have hR := diagReducedMap_fixes_real_all hf b i₀
  rcases hsign with hfix | hflip
  · exact Or.inl (fun ψ hψ => eq_id_of_fixes_all_two_level hg b hfixb hR hfix hψ)
  · exact Or.inr (fun ψ hψ => eq_bconj_of_flips_complex hg b hfixb hR hflip hψ)

theorem diagReducedMap_relphase_all
    (hf : TransProbPreserving f)
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N))) (i₀ : Fin N)
    {i j : Fin N} (hij : i ≠ j)
    {ψ : EuclideanSpace ℂ (Fin N)} (hψ : ψ ≠ 0) :
    ((starRingEnd ℂ) (b.repr (diagReducedMap hf b i₀ (Projectivization.mk ℂ ψ hψ)).rep i)
          * b.repr (diagReducedMap hf b i₀ (Projectivization.mk ℂ ψ hψ)).rep j).re
        / ‖(diagReducedMap hf b i₀ (Projectivization.mk ℂ ψ hψ)).rep‖ ^ 2
      = ((starRingEnd ℂ) (b.repr ψ i) * b.repr ψ j).re / ‖ψ‖ ^ 2 :=
  two_level_relphase_of_fixes (diagReducedMap_transProbPreserving hf b i₀) b
    (fun k => by rw [srcPoint_eq]; exact diagReducedMap_fixes_basis hf b i₀ k)
    hij (diagReducedMap_fixes_real_all hf b i₀ i j hij) hψ

theorem diagReducedMap_complex_probe_general
    (hf : TransProbPreserving f)
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N))) (i₀ : Fin N)
    {i j : Fin N} (hij : i ≠ j) :
    diagReducedMap hf b i₀
        (Projectivization.mk ℂ (b i + Complex.I • b j) (Iadd_basis_ne_zero b hij))
      = Projectivization.mk ℂ (b i + Complex.I • b j) (Iadd_basis_ne_zero b hij)
    ∨ diagReducedMap hf b i₀
        (Projectivization.mk ℂ (b i + Complex.I • b j) (Iadd_basis_ne_zero b hij))
      = Projectivization.mk ℂ (b i - Complex.I • b j) (subI_basis_ne_zero b hij) := by
  have hg : TransProbPreserving (diagReducedMap hf b i₀) :=
    diagReducedMap_transProbPreserving hf b i₀
  set w : EuclideanSpace ℂ (Fin N) := b i + Complex.I • b j with hw
  have hwne : w ≠ 0 := Iadd_basis_ne_zero b hij
  have hwnorm : ‖w‖ ^ 2 = 2 := Iadd_basis_norm_sq b hij
  have hw_i : b.repr w i = 1 := by
    rw [hw, b.repr_apply_apply, inner_add_right, inner_smul_right,
        orthonormal_iff_ite.mp b.orthonormal i i, if_pos rfl,
        orthonormal_iff_ite.mp b.orthonormal i j, if_neg hij, mul_zero, add_zero]
  have hw_j : b.repr w j = Complex.I := by
    rw [hw, b.repr_apply_apply, inner_add_right, inner_smul_right,
        orthonormal_iff_ite.mp b.orthonormal j i, if_neg (Ne.symm hij),
        orthonormal_iff_ite.mp b.orthonormal j j, if_pos rfl, mul_one, zero_add]
  have hw_zero : ∀ k, k ≠ i → k ≠ j → b.repr w k = 0 := by
    intro k hki hkj
    rw [hw, b.repr_apply_apply, inner_add_right, inner_smul_right,
        orthonormal_iff_ite.mp b.orthonormal k i, if_neg hki,
        orthonormal_iff_ite.mp b.orthonormal k j, if_neg hkj, mul_zero, add_zero]
  set φ := (diagReducedMap hf b i₀ (Projectivization.mk ℂ w hwne)).rep with hφ
  have hφne : φ ≠ 0 := Projectivization.rep_nonzero _
  have hφpos : (0 : ℝ) < ‖φ‖ ^ 2 := pow_pos (norm_pos_iff.mpr hφne) 2
  have hden : ‖φ‖ ^ 2 ≠ 0 := ne_of_gt hφpos
  have hcm : ∀ k, ‖b.repr φ k‖ ^ 2 / ‖φ‖ ^ 2 = ‖b.repr w k‖ ^ 2 / ‖w‖ ^ 2 := by
    intro k
    have h := coord_modulus_of_fixes_basis hg b
      (fun m => by rw [srcPoint_eq]; exact diagReducedMap_fixes_basis hf b i₀ m) hwne k
    rwa [← hφ] at h
  have hsupp : ∀ k, k ≠ i → k ≠ j → b.repr φ k = 0 := by
    intro k hki hkj
    have hm := hcm k
    rw [hw_zero k hki hkj, norm_zero, zero_pow (by norm_num), zero_div] at hm
    have hz : ‖b.repr φ k‖ ^ 2 = 0 := by
      rcases div_eq_zero_iff.mp hm with h | h
      · exact h
      · exact absurd h hden
    rwa [pow_eq_zero_iff (by norm_num), norm_eq_zero] at hz
  have ha : b.repr φ i ≠ 0 := by
    intro h0
    have hm := hcm i
    rw [h0, norm_zero, zero_pow (by norm_num), zero_div, hw_i, norm_one, one_pow, hwnorm] at hm
    norm_num at hm
  have hmod : ‖b.repr φ j‖ = ‖b.repr φ i‖ := by
    have hi := hcm j
    have hi0 := hcm i
    rw [hw_j, Complex.norm_I, one_pow, hwnorm] at hi
    rw [hw_i, norm_one, one_pow, hwnorm] at hi0
    have hd := hi.trans hi0.symm
    rw [div_eq_div_iff hden hden] at hd
    have heq2 : ‖b.repr φ j‖ ^ 2 = ‖b.repr φ i‖ ^ 2 := mul_right_cancel₀ hden hd
    rw [← Real.sqrt_sq (norm_nonneg (b.repr φ j)),
        ← Real.sqrt_sq (norm_nonneg (b.repr φ i)), heq2]
  set ε : ℂ := b.repr φ j / b.repr φ i with hε
  have hεnorm : ‖ε‖ = 1 := by rw [hε, norm_div, hmod, div_self (norm_ne_zero_iff.mpr ha)]
  have hdj : b.repr φ j = ε * b.repr φ i := by rw [hε, div_mul_cancel₀ _ ha]
  have hrel := diagReducedMap_relphase_all hf b i₀ hij hwne
  rw [← hφ, hw_i, hw_j, map_one, one_mul, Complex.I_re, zero_div] at hrel
  have hRe : ((starRingEnd ℂ) (b.repr φ i) * b.repr φ j).re = 0 := by
    rcases div_eq_zero_iff.mp hrel with h | h
    · exact h
    · exact absurd h hden
  have hεre : ε.re = 0 := by
    rw [hdj] at hRe
    have hr : (starRingEnd ℂ) (b.repr φ i) * (ε * b.repr φ i)
        = ε * ((‖b.repr φ i‖ ^ 2 : ℝ) : ℂ) := by
      rw [show (starRingEnd ℂ) (b.repr φ i) * (ε * b.repr φ i)
            = ε * ((starRingEnd ℂ) (b.repr φ i) * b.repr φ i) from by ring, RCLike.conj_mul]
      norm_cast
    rw [hr, mul_ofReal_re] at hRe
    have hpos : (0 : ℝ) < ‖b.repr φ i‖ ^ 2 := pow_pos (norm_pos_iff.mpr ha) 2
    exact (mul_eq_zero.mp hRe).resolve_right (ne_of_gt hpos)
  have hgw : diagReducedMap hf b i₀ (Projectivization.mk ℂ w hwne)
      = Projectivization.mk ℂ φ hφne := (Projectivization.mk_rep _).symm
  have hpair : φ = b.repr φ i • b i + b.repr φ j • b j :=
    repr_eq_pair_of_support b φ hij hsupp
  rcases unit_re_zero_eq_I_or_negI hεnorm hεre with hI | hnI
  · left
    have hval : b.repr φ i • w = φ := by
      conv_rhs => rw [hpair, hdj, hI]
      rw [hw]; module
    rw [hgw]
    exact (Projectivization.mk_eq_mk_iff' ℂ φ w hφne hwne).mpr ⟨b.repr φ i, hval⟩
  · right
    have hval : b.repr φ i • (b i - Complex.I • b j) = φ := by
      conv_rhs => rw [hpair, hdj, hnI]
      module
    rw [hgw]
    exact (Projectivization.mk_eq_mk_iff' ℂ φ (b i - Complex.I • b j) hφne
      (subI_basis_ne_zero b hij)).mpr ⟨b.repr φ i, hval⟩

/-- Gram datum for a fixed complex ray. -/
theorem diagReducedMap_gram_of_fixed
    (hf : TransProbPreserving f)
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N))) (i₀ : Fin N)
    {i j : Fin N} (hij : i ≠ j)
    (hfixI : diagReducedMap hf b i₀
        (Projectivization.mk ℂ (b i + Complex.I • b j) (Iadd_basis_ne_zero b hij))
      = Projectivization.mk ℂ (b i + Complex.I • b j) (Iadd_basis_ne_zero b hij))
    {ψ : EuclideanSpace ℂ (Fin N)} (hψ : ψ ≠ 0) :
    (starRingEnd ℂ) (b.repr (diagReducedMap hf b i₀ (Projectivization.mk ℂ ψ hψ)).rep i)
          * b.repr (diagReducedMap hf b i₀ (Projectivization.mk ℂ ψ hψ)).rep j
          * ((‖ψ‖ ^ 2 : ℝ) : ℂ)
      = (starRingEnd ℂ) (b.repr ψ i) * b.repr ψ j
          * ((‖(diagReducedMap hf b i₀ (Projectivization.mk ℂ ψ hψ)).rep‖ ^ 2 : ℝ) : ℂ) := by
  have hg : TransProbPreserving (diagReducedMap hf b i₀) :=
    diagReducedMap_transProbPreserving hf b i₀
  have hfixb : ∀ k, diagReducedMap hf b i₀ (srcPoint b k) = srcPoint b k := fun k => by
    rw [srcPoint_eq]; exact diagReducedMap_fixes_basis hf b i₀ k
  have hre := diagReducedMap_relphase_all hf b i₀ hij hψ
  have him := two_level_imrelphase_of_fixes hg b hfixb hij hfixI hψ
  set φ := (diagReducedMap hf b i₀ (Projectivization.mk ℂ ψ hψ)).rep with hφ
  have hDφ : ‖φ‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr (Projectivization.rep_nonzero _))
  have hDψ : ‖ψ‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hψ)
  have hrec := (div_eq_div_iff hDφ hDψ).mp hre
  have himc := (div_eq_div_iff hDφ hDψ).mp him
  apply Complex.ext
  · rw [mul_ofReal_re, mul_ofReal_re]; exact hrec
  · rw [mul_ofReal_im, mul_ofReal_im]; exact himc

/-- Gram datum for a flipped complex ray. -/
theorem diagReducedMap_gram_of_flips
    (hf : TransProbPreserving f)
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N))) (i₀ : Fin N)
    {i j : Fin N} (hij : i ≠ j)
    (hflipI : diagReducedMap hf b i₀
        (Projectivization.mk ℂ (b i + Complex.I • b j) (Iadd_basis_ne_zero b hij))
      = Projectivization.mk ℂ (b i - Complex.I • b j) (subI_basis_ne_zero b hij))
    {ψ : EuclideanSpace ℂ (Fin N)} (hψ : ψ ≠ 0) :
    (starRingEnd ℂ) (b.repr (diagReducedMap hf b i₀ (Projectivization.mk ℂ ψ hψ)).rep i)
          * b.repr (diagReducedMap hf b i₀ (Projectivization.mk ℂ ψ hψ)).rep j
          * ((‖ψ‖ ^ 2 : ℝ) : ℂ)
      = (starRingEnd ℂ) ((starRingEnd ℂ) (b.repr ψ i) * b.repr ψ j)
          * ((‖(diagReducedMap hf b i₀ (Projectivization.mk ℂ ψ hψ)).rep‖ ^ 2 : ℝ) : ℂ) := by
  have hg : TransProbPreserving (diagReducedMap hf b i₀) :=
    diagReducedMap_transProbPreserving hf b i₀
  have hfixb : ∀ k, diagReducedMap hf b i₀ (srcPoint b k) = srcPoint b k := fun k => by
    rw [srcPoint_eq]; exact diagReducedMap_fixes_basis hf b i₀ k
  have hre := diagReducedMap_relphase_all hf b i₀ hij hψ
  have him := two_level_imrelphase_of_flips hg b hfixb hij hflipI hψ
  set φ := (diagReducedMap hf b i₀ (Projectivization.mk ℂ ψ hψ)).rep with hφ
  have hDφ : ‖φ‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr (Projectivization.rep_nonzero _))
  have hDψ : ‖ψ‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hψ)
  have hrec := (div_eq_div_iff hDφ hDψ).mp hre
  have himc := (div_eq_div_iff hDφ hDψ).mp him
  apply Complex.ext
  · rw [mul_ofReal_re, mul_ofReal_re, Complex.conj_re]; exact hrec
  · rw [mul_ofReal_im, mul_ofReal_im, Complex.conj_im]; exact himc

/-- Gram datum on the diagonal (moduli). -/
theorem diagReducedMap_gram_diag
    (hf : TransProbPreserving f)
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N))) (i₀ : Fin N) (i : Fin N)
    {ψ : EuclideanSpace ℂ (Fin N)} (hψ : ψ ≠ 0) :
    (starRingEnd ℂ) (b.repr (diagReducedMap hf b i₀ (Projectivization.mk ℂ ψ hψ)).rep i)
          * b.repr (diagReducedMap hf b i₀ (Projectivization.mk ℂ ψ hψ)).rep i
          * ((‖ψ‖ ^ 2 : ℝ) : ℂ)
      = (starRingEnd ℂ) (b.repr ψ i) * b.repr ψ i
          * ((‖(diagReducedMap hf b i₀ (Projectivization.mk ℂ ψ hψ)).rep‖ ^ 2 : ℝ) : ℂ) := by
  have hg : TransProbPreserving (diagReducedMap hf b i₀) :=
    diagReducedMap_transProbPreserving hf b i₀
  have hfixb : ∀ k, diagReducedMap hf b i₀ (srcPoint b k) = srcPoint b k := fun k => by
    rw [srcPoint_eq]; exact diagReducedMap_fixes_basis hf b i₀ k
  have hm := coord_modulus_of_fixes_basis hg b hfixb hψ i
  set φ := (diagReducedMap hf b i₀ (Projectivization.mk ℂ ψ hψ)).rep with hφ
  have hDφ : ‖φ‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr (Projectivization.rep_nonzero _))
  have hDψ : ‖ψ‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hψ)
  have hmc := (div_eq_div_iff hDφ hDψ).mp hm
  have e1 : (starRingEnd ℂ) (b.repr φ i) * b.repr φ i = ((‖b.repr φ i‖ ^ 2 : ℝ) : ℂ) := by
    rw [RCLike.conj_mul]; norm_cast
  have e2 : (starRingEnd ℂ) (b.repr ψ i) * b.repr ψ i = ((‖b.repr ψ i‖ ^ 2 : ℝ) : ℂ) := by
    rw [RCLike.conj_mul]; norm_cast
  rw [e1, e2, ← Complex.ofReal_mul, ← Complex.ofReal_mul, Complex.ofReal_inj]
  exact hmc

end Projectivization
