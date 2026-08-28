/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.CPSVExample412Literal
import TNLean.MPS.MPDO.SimpleScaling

/-!
# The density-normalized channel fixed point of CPSV16 Example 4.12

CPSV16 Example 4.12 prints a tensor `M` generating
`I^{⊗ N} + σ_z^{⊗ N}`. Its positive-length trace is `2 ^ N`, so the tensor-level
rescaling
\[
  \widehat M=\tfrac12 M
\]
generates the normalized density family. This file proves the exact scalar law,
constructs parity coarse-graining and refinement channels, and proves the two
trace-preserving completely positive map equations of CPSV16 Definition 4.1.

The horizontal normal-block weights of `\widehat M` have modulus `1 / √2`, not
one. Thus the theorem here concerns the bare channel predicate `IsRFPViaTS`; it
does not assert the line-246 global unit-weight convention. This scale tension
is documented in `docs/paper-gaps/cpsv16_unit_weight_rfp_scale_tension.tex`.

**Local fix (normalization):** The source prints the unscaled tensor, whose
physical-trace transfer is not idempotent. See
`docs/paper-gaps/cpsv16_example_4_12_normalization.tex`.

## Main results

* `Mhat`: the density-normalized representative `(1 / 2) • M`.
* `mpo_Mhat_eq_normalizedMPO_M`: its positive-length MPO is the normalized MPO
  of the printed tensor.
* `Mhat_isMPDO`: the corrected representative generates positive operators.
* `coarseMap`, `refineMap`: the explicit parity channels.
* `Mhat_isRFPViaTS`: the corrected representative satisfies both channel
  equations of Definition 4.1.

## References

* Cirac--Perez-Garcia--Schuch--Verstraete, arXiv:1606.00608, Definition 4.1,
  lines 638--660, and Example 4.12, lines 932--939.
-/

open scoped Matrix BigOperators ComplexOrder

noncomputable section

namespace MPOTensor.CPSVExample412NormalizedRFP

/-- The density-normalized representative of the tensor printed in CPSV16
Example 4.12.

**Local fix (normalization):** The source omits the factor `1 / 2`; see
`docs/paper-gaps/cpsv16_example_4_12_normalization.tex`.

Source comparison: CPSV16, arXiv:1606.00608, Example 4.12, lines 932--938. -/
def Mhat : MPOTensor 2 2 :=
  ((1 / 2 : ℝ) : ℂ) • CPSVExample412Literal.M

/-- Scaling the printed tensor by `1 / 2` scales its length-`N` periodic MPO by
`(1 / 2) ^ N`.

Source formula: CPSV16, arXiv:1606.00608, Example 4.12, lines 933--936. -/
theorem mpo_Mhat (N : ℕ) :
    mpo Mhat N = (((1 / 2 : ℝ) : ℂ) ^ N) • mpo CPSVExample412Literal.M N := by
  simpa [Mhat] using
    MPOTensor.mpo_smul (((1 / 2 : ℝ) : ℂ)) CPSVExample412Literal.M N

/-- At every positive length, `Mhat` generates the normalized density operator
of the tensor printed in CPSV16 Example 4.12.

**Local fix (normalization):** The equality uses the omitted tensor factor
`1 / 2`; see `docs/paper-gaps/cpsv16_example_4_12_normalization.tex`.

Source comparison: CPSV16, arXiv:1606.00608, Example 4.12, lines 933--938. -/
theorem mpo_Mhat_eq_normalizedMPO_M (N : ℕ) (hN : 0 < N) :
    mpo Mhat N = normalizedMPO CPSVExample412Literal.M N := by
  rw [mpo_Mhat, normalizedMPO, CPSVExample412Literal.trace_rho N hN,
    ← inv_pow]
  norm_num

/-- The positive-length periodic MPO of `Mhat` has trace one.

**Local fix (normalization):** The printed tensor instead has trace `2 ^ N`;
see `docs/paper-gaps/cpsv16_example_4_12_normalization.tex`.

Source comparison: CPSV16, arXiv:1606.00608, Example 4.12, lines 933--938. -/
theorem trace_mpo_Mhat (N : ℕ) (hN : 0 < N) :
    Matrix.trace (mpo Mhat N) = 1 := by
  rw [mpo_Mhat, Matrix.trace_smul, CPSVExample412Literal.trace_rho N hN]
  change (((1 / 2 : ℝ) : ℂ) ^ N) * (2 : ℂ) ^ N = 1
  rw [← mul_pow]
  norm_num

/-- The density-normalized representative generates positive semidefinite
operators at every positive length.

Source comparison: CPSV16, arXiv:1606.00608, Example 4.12, lines 933--938. -/
theorem Mhat_isMPDO : IsMPDO Mhat := by
  simpa [Mhat] using CPSVExample412Literal.M_isMPDO.smul_ofReal
    (r := (1 / 2 : ℝ)) (by norm_num)

/-- The parity of a pair of physical bits.

Construction witnessing the channel claim in CPSV16, arXiv:1606.00608,
Example 4.12, lines 932--939; the source does not print the maps. -/
def pairParity (p : Fin 2 × Fin 2) : Fin 2 :=
  if p.1 = p.2 then 0 else 1

/-- The deterministic Kraus operator sending a pair of bits to its parity.

Construction witnessing the channel claim in CPSV16, arXiv:1606.00608,
Example 4.12, lines 932--939; the source does not print the maps. -/
def coarseKraus (p : Fin 2 × Fin 2) :
    Matrix (Fin 2) (Fin 2 × Fin 2) ℂ :=
  Matrix.single (pairParity p) p 1

/-- The amplitude distributing one parity label uniformly over its two pairs.

Construction witnessing the channel claim in CPSV16, arXiv:1606.00608,
Example 4.12, lines 932--939; the source does not print the maps. -/
def refinementAmplitude : ℝ :=
  1 / Real.sqrt 2

/-- The Kraus operator refining one parity label into a fixed pair.

Construction witnessing the channel claim in CPSV16, arXiv:1606.00608,
Example 4.12, lines 932--939; the source does not print the maps. -/
def refineKraus (p : Fin 2 × Fin 2) :
    Matrix (Fin 2 × Fin 2) (Fin 2) ℂ :=
  Matrix.single p (pairParity p) refinementAmplitude

private lemma refinementAmplitude_sq : refinementAmplitude ^ 2 = 1 / 2 := by
  rw [refinementAmplitude, div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), one_pow]

private lemma star_refinementAmplitude_mul :
    star (refinementAmplitude : ℂ) * refinementAmplitude = 1 / 2 := by
  calc
    star (refinementAmplitude : ℂ) * refinementAmplitude =
        ((refinementAmplitude ^ 2 : ℝ) : ℂ) := by
      rw [Complex.star_def, Complex.conj_ofReal]
      norm_num [pow_two]
    _ = ((1 / 2 : ℝ) : ℂ) := by rw [refinementAmplitude_sq]
    _ = 1 / 2 := by norm_num

private lemma refinementAmplitude_mul_star :
    (refinementAmplitude : ℂ) * star (refinementAmplitude : ℂ) = 1 / 2 := by
  simpa [mul_comm] using star_refinementAmplitude_mul

private lemma parity_fiber_half_sum (k : Fin 2) :
    (∑ p : Fin 2 × Fin 2,
      if pairParity p = k then (1 / 2 : ℂ) else 0) = 1 := by
  rw [Fintype.sum_prod_type]
  fin_cases k <;> norm_num [pairParity, Fin.sum_univ_two]

private lemma coarseKraus_resolution :
    ∑ p, (coarseKraus p)ᴴ * coarseKraus p =
      (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) := by
  simpa [coarseKraus, Matrix.conjTranspose_single] using
    (Matrix.sum_single_one (m := Fin 2 × Fin 2) (α := ℂ))

private lemma refineKraus_resolution :
    ∑ p, (refineKraus p)ᴴ * refineKraus p =
      (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext q r
  simp only [refineKraus, Matrix.conjTranspose_single,
    Matrix.single_mul_single_same, star_refinementAmplitude_mul,
    Matrix.sum_apply]
  by_cases hqr : q = r
  · subst r
    rw [Matrix.one_apply_eq]
    simpa [Matrix.single_apply] using parity_fiber_half_sum q
  · rw [Matrix.one_apply_ne hqr]
    apply Finset.sum_eq_zero
    intro p _
    rw [Matrix.single_apply]
    split_ifs with hp
    · exact (hqr (hp.1.symm.trans hp.2)).elim
    · rfl

/-- The trace-preserving parity coarse-graining channel from two sites to one.

Source: CPSV16, arXiv:1606.00608, Definition 4.1, equations `eq:Smap` and
`RFPMixedTS`, lines 645--660; specialized to Example 4.12, lines 932--939. -/
def coarseMap :
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ →ₗ[ℂ]
      Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.rectangularKrausMap coarseKraus

/-- The trace-preserving parity refinement channel from one site to two.

Source: CPSV16, arXiv:1606.00608, Definition 4.1, equations `eq:Tmap` and
`RFPMixedTS`, lines 650--660; specialized to Example 4.12, lines 932--939. -/
def refineMap :
    Matrix (Fin 2) (Fin 2) ℂ →ₗ[ℂ]
      Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  Matrix.rectangularKrausMap refineKraus

/-- The parity coarse-graining map is trace-preserving and completely positive.

Source: CPSV16, arXiv:1606.00608, Definition 4.1, lines 638--660. -/
theorem coarseMap_isKrausCPTP : IsKrausCPTP coarseMap := by
  exact Matrix.rectangularKrausMap_isKrausCPTP coarseKraus coarseKraus_resolution

/-- The parity refinement map is trace-preserving and completely positive.

Source: CPSV16, arXiv:1606.00608, Definition 4.1, lines 638--660. -/
theorem refineMap_isKrausCPTP : IsKrausCPTP refineMap := by
  exact Matrix.rectangularKrausMap_isKrausCPTP refineKraus refineKraus_resolution

private lemma Mhat_diagonal_mul (p : Fin 2 × Fin 2) :
    Mhat p.1 p.1 * Mhat p.2 p.2 =
      (1 / 2 : ℂ) • Mhat (pairParity p) (pairParity p) := by
  obtain ⟨i, j⟩ := p
  ext a b
  fin_cases i <;> fin_cases j <;> fin_cases a <;> fin_cases b <;>
    norm_num [Mhat, pairParity, CPSVExample412Literal.M,
      CPSVExample412Literal.sigmaZ, SpinCover.pauli, Matrix.mul_apply,
      Fin.sum_univ_two]

private lemma physClose2_Mhat_diagonal (X : Matrix (Fin 2) (Fin 2) ℂ)
    (p : Fin 2 × Fin 2) :
    physClose2 Mhat X p p =
      (1 / 2 : ℂ) * physClose1 Mhat X (pairParity p) (pairParity p) := by
  rw [physClose2_apply, physClose1_apply, Mhat_diagonal_mul,
    Matrix.smul_mul, Matrix.trace_smul]
  simp [smul_eq_mul]

private lemma physClose1_Mhat_of_ne (X : Matrix (Fin 2) (Fin 2) ℂ)
    {i j : Fin 2} (hij : i ≠ j) :
    physClose1 Mhat X i j = 0 := by
  rw [physClose1_apply]
  simp [Mhat, CPSVExample412Literal.M, hij]

private lemma physClose2_Mhat_of_ne (X : Matrix (Fin 2) (Fin 2) ℂ)
    {p q : Fin 2 × Fin 2} (hpq : p ≠ q) :
    physClose2 Mhat X p q = 0 := by
  rw [physClose2_apply]
  by_cases hfirst : p.1 = q.1
  · have hsecond : p.2 ≠ q.2 := by
      intro h
      exact hpq (Prod.ext hfirst h)
    simp [Mhat, CPSVExample412Literal.M, hsecond]
  · simp [Mhat, CPSVExample412Literal.M, hfirst]

/-- The parity coarse-graining channel sends the two-site physical closure of
`Mhat` to its one-site closure for every virtual operator.

**Local fix (normalization):** This equation holds for `Mhat = (1 / 2) • M`,
not for the tensor printed without the scalar. See
`docs/paper-gaps/cpsv16_example_4_12_normalization.tex`.

Source comparison: CPSV16, arXiv:1606.00608, equations `eq:Smap` and
`RFPMixedTS`, lines 645--660, and Example 4.12, lines 932--939. -/
theorem coarseMap_physClose2 (X : Matrix (Fin 2) (Fin 2) ℂ) :
    coarseMap (physClose2 Mhat X) = physClose1 Mhat X := by
  ext k l
  simp only [coarseMap, Matrix.rectangularKrausMap, LinearMap.coe_mk,
    AddHom.coe_mk, coarseKraus, Matrix.conjTranspose_single,
    Matrix.single_mul_mul_single, star_one, one_mul, mul_one, Matrix.sum_apply]
  by_cases hkl : k = l
  · subst l
    simp_rw [Matrix.single_apply]
    simp only [and_self]
    simp_rw [physClose2_Mhat_diagonal]
    have hreplace :
        (∑ p : Fin 2 × Fin 2,
          if pairParity p = k then
            (1 / 2 : ℂ) * physClose1 Mhat X (pairParity p) (pairParity p)
          else 0) =
        ∑ p : Fin 2 × Fin 2,
          (if pairParity p = k then (1 / 2 : ℂ) else 0) *
            physClose1 Mhat X k k := by
      apply Finset.sum_congr rfl
      intro p _
      by_cases hp : pairParity p = k <;> simp [hp]
    rw [hreplace, ← Finset.sum_mul, parity_fiber_half_sum, one_mul]
  · rw [physClose1_Mhat_of_ne X hkl]
    apply Finset.sum_eq_zero
    intro p _
    rw [Matrix.single_apply]
    split_ifs with hp
    · exact (hkl (hp.1.symm.trans hp.2)).elim
    · rfl

/-- The parity refinement channel sends the one-site physical closure of
`Mhat` to its two-site closure for every virtual operator.

**Local fix (normalization):** This equation holds for `Mhat = (1 / 2) • M`,
not for the tensor printed without the scalar. See
`docs/paper-gaps/cpsv16_example_4_12_normalization.tex`.

Source comparison: CPSV16, arXiv:1606.00608, equations `eq:Tmap` and
`RFPMixedTS`, lines 650--660, and Example 4.12, lines 932--939. -/
theorem refineMap_physClose1 (X : Matrix (Fin 2) (Fin 2) ℂ) :
    refineMap (physClose1 Mhat X) = physClose2 Mhat X := by
  ext p q
  simp only [refineMap, Matrix.rectangularKrausMap, LinearMap.coe_mk,
    AddHom.coe_mk, refineKraus, Matrix.conjTranspose_single,
    Matrix.single_mul_mul_single, Matrix.sum_apply]
  by_cases hpq : p = q
  · subst q
    rw [Finset.sum_eq_single p]
    · rw [Matrix.single_apply_same, physClose2_Mhat_diagonal]
      rw [← refinementAmplitude_mul_star]
      ring
    · intro q _ hqp
      rw [Matrix.single_apply]
      simp [hqp]
    · simp
  · rw [physClose2_Mhat_of_ne X hpq]
    apply Finset.sum_eq_zero
    intro r _
    rw [Matrix.single_apply]
    split_ifs with hr
    · exact (hpq (hr.1.symm.trans hr.2)).elim
    · rfl

/-- The density-normalized representative of CPSV16 Example 4.12 satisfies the
two trace-preserving completely positive map equations of Definition 4.1.

**Local fix (normalization):** The source prints the unscaled tensor, for which
the channel equations are impossible. This theorem concerns
`Mhat = (1 / 2) • M`; see
`docs/paper-gaps/cpsv16_example_4_12_normalization.tex`.

**Scope restriction (canonical weight):** `IsRFPViaTS` isolates the two channel
equations. This theorem does not assert the line-246 unit-weight horizontal
canonical convention; see
`docs/paper-gaps/cpsv16_unit_weight_rfp_scale_tension.tex`.

Source comparison: CPSV16, arXiv:1606.00608, Definition 4.1, lines 638--660,
and Example 4.12, lines 932--939. -/
theorem Mhat_isRFPViaTS : IsRFPViaTS Mhat := by
  exact ⟨coarseMap, refineMap, coarseMap_isKrausCPTP,
    refineMap_isKrausCPTP, coarseMap_physClose2, refineMap_physClose1⟩

end MPOTensor.CPSVExample412NormalizedRFP
