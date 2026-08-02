/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.ActiveSectorSpanningAreaLaw
import TNLean.MPS.MPDO.RFPViaTSBlocking

/-!
# Renormalization maps for the four-sector classical tensor

The four-sector tensor from `ActiveSectorSpanningCounterexample` satisfies the
trace-preserving completely positive map definition of a renormalization fixed
point. Its two-site sector products are stochastic refinements of its one-site
sectors. Rectangular Kraus families obtained from those transition weights give
the two maps in Definition 4.1.

The source-normalized scalar representative behaves differently: its two-site
blocking has physical-trace transfer `(16 / 5) P`, where `P` is a nonzero
projection. This matrix is not idempotent, whereas Definition 4.1 forces literal
idempotence. Thus the renormalization-fixed-point condition is sensitive to the
normalization of the tensor, unlike the scale-invariant `IsSourceZCL` predicate
used in this development. The paper's literal zero-correlation-length diagram
has the same normalization sensitivity and is not the up-to-scalar predicate.

This classification concerns the explicit tensor. It does not prove the
general implication from the strong area law and zero correlation length to a
renormalization fixed point in Theorem 4.9; the printed proof of that implication
still passes through the normalization-sensitive rank-one step of Lemma C.5.

## Main results

* `tensor_isRFPViaTS`: the explicit four-sector tensor satisfies Definition 4.1.
* `blockTwo_tensor_isRFPViaTS`: its two-site physical blocking also satisfies
  Definition 4.1.
* `blockTwo_normalizedTensor_not_isRFPViaTS`: the two-site blocking of the
  source-normalized representative does not satisfy Definition 4.1.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Definition 4.1, lines 645--659; Theorem 4.9, lines 851--893; and the
  proposed implication at lines 1810--1825.
-/

open scoped Matrix BigOperators ComplexOrder

namespace MPOTensor.ActiveSectorSpanningCounterexample

attribute [local instance] Classical.decEq Classical.propDecidable

/-- The scalar representative selected by the global unit-weight normalization
of the singleton normal tensor underlying the four-sector witness.

Source: arXiv:1606.00608, the global BNT normalization at line 246 and the BNT
expansion at lines 287--289. -/
noncomputable def normalizedTensor : MPOTensor 4 2 :=
  (4 / Real.sqrt 5 : ℂ) • tensor

/-- The physical sector represented by a consecutive pair of classical sectors. -/
private def pairLabel (p : Fin 4 × Fin 4) : Fin 4 :=
  ![![0, 0, 2, 2], ![1, 1, 3, 3], ![0, 0, 2, 2], ![1, 1, 3, 3]] p.1 p.2

private lemma sectorMatrix_mul (i j : Fin 4) :
    sectorMatrix i * sectorMatrix j =
      (rightPairing * leftPairing) i j • sectorMatrix (pairLabel (i, j)) := by
  rw [rightPairing_mul_leftPairing]
  ext a b
  fin_cases i <;> fin_cases j <;> fin_cases a <;> fin_cases b <;>
    norm_num [sectorMatrix, pairLabel, leftPairing, rightPairing,
      Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMulVec_apply,
      Matrix.cons_val_two, Matrix.cons_val_three]

/-- The nonnegative amplitude assigned to a pair of consecutive sectors. -/
private noncomputable def refinementAmplitude (p : Fin 4 × Fin 4) : ℂ :=
  Real.sqrt ((rightPairing * leftPairing) p.1 p.2).re

private lemma refinementAmplitude_mul_star (p : Fin 4 × Fin 4) :
    refinementAmplitude p * star (refinementAmplitude p) =
      (rightPairing * leftPairing) p.1 p.2 := by
  obtain ⟨i, j⟩ := p
  let w := ((rightPairing * leftPairing) i j).re
  have hw : 0 ≤ w := (rightPairing_mul_leftPairing_re_pos i j).le
  have hz : (w : ℂ) = (rightPairing * leftPairing) i j := by
    fin_cases i <;> fin_cases j <;>
      norm_num [w, rightPairing_mul_leftPairing, Matrix.cons_val_two,
        Matrix.cons_val_three]
  calc
    refinementAmplitude (i, j) * star (refinementAmplitude (i, j)) =
        ((Real.sqrt w) ^ 2 : ℝ) := by
          simp [refinementAmplitude, w, pow_two]
    _ = (w : ℂ) := by rw [Real.sq_sqrt hw]
    _ = (rightPairing * leftPairing) i j := hz

private lemma star_refinementAmplitude_mul (p : Fin 4 × Fin 4) :
    star (refinementAmplitude p) * refinementAmplitude p =
      (rightPairing * leftPairing) p.1 p.2 := by
  simpa [mul_comm] using refinementAmplitude_mul_star p

/-- The deterministic Kraus operator which merges one pair of sectors. -/
private noncomputable def coarseningKraus (p : Fin 4 × Fin 4) :
    Matrix (Fin 4) (Fin 4 × Fin 4) ℂ :=
  Matrix.single (pairLabel p) p 1

/-- The Kraus operator which refines one sector into a fixed pair. -/
private noncomputable def refinementKraus (p : Fin 4 × Fin 4) :
    Matrix (Fin 4 × Fin 4) (Fin 4) ℂ :=
  Matrix.single p (pairLabel p) (refinementAmplitude p)

private lemma coarseningKraus_resolution :
    ∑ p, (coarseningKraus p)ᴴ * coarseningKraus p =
      (1 : Matrix (Fin 4 × Fin 4) (Fin 4 × Fin 4) ℂ) := by
  simpa [coarseningKraus, Matrix.conjTranspose_single] using
    (Matrix.sum_single_one (m := Fin 4 × Fin 4) (α := ℂ))

private lemma refinement_weight_fiber_sum (k : Fin 4) :
    (∑ p : Fin 4 × Fin 4,
        if pairLabel p = k then (rightPairing * leftPairing) p.1 p.2 else 0) = 1 := by
  rw [Fintype.sum_prod_type, rightPairing_mul_leftPairing]
  fin_cases k <;>
    norm_num [pairLabel, Fin.sum_univ_four, Matrix.cons_val_two,
      Matrix.cons_val_three] <;>
    split_ifs <;> norm_num at * <;> simp_all [Fin.ext_iff]

private lemma refinementKraus_resolution :
    ∑ p, (refinementKraus p)ᴴ * refinementKraus p =
      (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
  ext q r
  simp only [refinementKraus, Matrix.conjTranspose_single,
    Matrix.single_mul_single_same, star_refinementAmplitude_mul, Matrix.sum_apply]
  by_cases hqr : q = r
  · subst r
    rw [Matrix.one_apply_eq]
    simpa [Matrix.single_apply] using refinement_weight_fiber_sum q
  · rw [Matrix.one_apply_ne hqr]
    apply Finset.sum_eq_zero
    intro p _
    rw [Matrix.single_apply]
    split_ifs with hp
    · exact (hqr (hp.1.symm.trans hp.2)).elim
    · rfl

/-- The two-to-one classical coarse-graining channel. -/
private noncomputable def coarseningMap :
    Matrix (Fin 4 × Fin 4) (Fin 4 × Fin 4) ℂ →ₗ[ℂ] Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.rectangularKrausMap coarseningKraus

/-- The one-to-two classical refinement channel. -/
private noncomputable def refinementMap :
    Matrix (Fin 4) (Fin 4) ℂ →ₗ[ℂ] Matrix (Fin 4 × Fin 4) (Fin 4 × Fin 4) ℂ :=
  Matrix.rectangularKrausMap refinementKraus

private lemma coarseningMap_isKrausCPTP : IsKrausCPTP coarseningMap :=
  Matrix.rectangularKrausMap_isKrausCPTP coarseningKraus coarseningKraus_resolution

private lemma refinementMap_isKrausCPTP : IsKrausCPTP refinementMap :=
  Matrix.rectangularKrausMap_isKrausCPTP refinementKraus refinementKraus_resolution

private lemma physClose2_tensor_diagonal (X : Matrix (Fin 2) (Fin 2) ℂ)
    (p : Fin 4 × Fin 4) :
    physClose2 tensor X p p =
      (rightPairing * leftPairing) p.1 p.2 *
        physClose1 tensor X (pairLabel p) (pairLabel p) := by
  obtain ⟨i, j⟩ := p
  rw [physClose2_apply, physClose1_apply]
  simp only [tensor, if_pos]
  rw [sectorMatrix_mul, Matrix.smul_mul, Matrix.trace_smul]
  rfl

private lemma coarseningMap_physClose2 (X : Matrix (Fin 2) (Fin 2) ℂ) :
    coarseningMap (physClose2 tensor X) = physClose1 tensor X := by
  ext k l
  simp only [coarseningMap, Matrix.rectangularKrausMap, LinearMap.coe_mk,
    AddHom.coe_mk, coarseningKraus, Matrix.conjTranspose_single,
    Matrix.single_mul_mul_single, star_one, one_mul, mul_one, Matrix.sum_apply]
  by_cases hkl : k = l
  · subst l
    simp_rw [Matrix.single_apply]
    simp only [and_self]
    simp_rw [physClose2_tensor_diagonal]
    have hreplace :
        (∑ p : Fin 4 × Fin 4,
          if pairLabel p = k then
            (rightPairing * leftPairing) p.1 p.2 *
              physClose1 tensor X (pairLabel p) (pairLabel p)
          else 0) =
        ∑ p : Fin 4 × Fin 4,
          (if pairLabel p = k then (rightPairing * leftPairing) p.1 p.2 else 0) *
            physClose1 tensor X k k := by
      apply Finset.sum_congr rfl
      intro p _
      by_cases hp : pairLabel p = k <;> simp [hp]
    rw [hreplace, ← Finset.sum_mul, refinement_weight_fiber_sum, one_mul]
  · rw [physClose1_apply]
    rw [tensor, if_neg hkl]
    simp only [Matrix.zero_mul, Matrix.trace_zero]
    apply Finset.sum_eq_zero
    intro p _
    rw [Matrix.single_apply]
    split_ifs with hp
    · exact (hkl (hp.1.symm.trans hp.2)).elim
    · rfl

private lemma physClose2_tensor_of_ne (X : Matrix (Fin 2) (Fin 2) ℂ)
    {p q : Fin 4 × Fin 4} (hpq : p ≠ q) :
    physClose2 tensor X p q = 0 := by
  rw [physClose2_apply]
  by_cases hfirst : p.1 = q.1
  · have hsecond : p.2 ≠ q.2 := by
      intro h
      exact hpq (Prod.ext hfirst h)
    rw [tensor, if_pos hfirst, tensor, if_neg hsecond, Matrix.mul_zero,
      Matrix.zero_mul, Matrix.trace_zero]
  · rw [tensor, if_neg hfirst, Matrix.zero_mul, Matrix.zero_mul,
      Matrix.trace_zero]

private lemma refinementMap_physClose1 (X : Matrix (Fin 2) (Fin 2) ℂ) :
    refinementMap (physClose1 tensor X) = physClose2 tensor X := by
  ext p q
  simp only [refinementMap, Matrix.rectangularKrausMap, LinearMap.coe_mk,
    AddHom.coe_mk, refinementKraus, Matrix.conjTranspose_single,
    Matrix.single_mul_mul_single, Matrix.sum_apply]
  by_cases hpq : p = q
  · subst q
    rw [Finset.sum_eq_single p]
    · rw [Matrix.single_apply_same, physClose2_tensor_diagonal]
      rw [← refinementAmplitude_mul_star]
      ring
    · intro q _ hqp
      rw [Matrix.single_apply]
      simp [hqp]
    · simp
  · rw [physClose2_tensor_of_ne X hpq]
    apply Finset.sum_eq_zero
    intro r _
    rw [Matrix.single_apply]
    split_ifs with hr
    · exact (hpq (hr.1.symm.trans hr.2)).elim
    · rfl

/-- The explicit four-sector tensor satisfies the trace-preserving completely
positive map definition of a renormalization fixed point. The refinement map
sends a sector to consecutive sector pairs with the neighboring transition
weights, while the coarse-graining map returns each pair to its represented
sector.

This is a classification of this explicit tensor, not a proof of the general
strong-area-law and zero-correlation-length implication in Theorem 4.9.

Source: arXiv:1606.00608, Definition 4.1, lines 645--659, and the proposed
implication in Theorem 4.9 at lines 1810--1825. -/
theorem tensor_isRFPViaTS : IsRFPViaTS tensor :=
  ⟨coarseningMap, refinementMap, coarseningMap_isKrausCPTP,
    refinementMap_isKrausCPTP, coarseningMap_physClose2,
    refinementMap_physClose1⟩

/-- The two-site physical blocking of the explicit four-sector tensor is a
renormalization fixed point. Its maps are obtained by applying the one-site
coarse-graining and refinement maps twice and passing to blocked coordinates.

This proves the renormalization-fixed-point conclusion for this witness only;
it does not prove the universal implication from the hypotheses of Theorem 4.9.

Source: arXiv:1606.00608, Definition 4.1, lines 645--659, and the twice-applied
channel construction for Theorem 4.9 at lines 1810--1825. -/
theorem blockTwo_tensor_isRFPViaTS : IsRFPViaTS (MPOTensor.blockTwo tensor) :=
  tensor_isRFPViaTS.blockTwo

private lemma physTraceTransfer_blockTwo {d D : ℕ} (M : MPOTensor d D) :
    physTraceTransfer (blockTwo M) = physTraceTransfer M * physTraceTransfer M := by
  rw [physTraceTransfer, physTraceTransfer]
  ext a b
  simp only [Matrix.sum_apply, blockTwo_apply, Matrix.mul_apply]
  rw [← finProdFinEquiv.sum_comp]
  simp only [Equiv.symm_apply_apply, Fintype.sum_prod_type,
    Finset.sum_mul, Finset.mul_sum]
  calc
    _ = ∑ i : Fin d, ∑ k : Fin D, ∑ j : Fin d,
        M i i a k * M j j k b := by
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_comm
    _ = ∑ k : Fin D, ∑ i : Fin d, ∑ j : Fin d,
        M i i a k * M j j k b := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k _
      exact Finset.sum_comm

private lemma physTraceTransfer_normalizedTensor :
    physTraceTransfer normalizedTensor =
      (4 / Real.sqrt 5 : ℂ) • !![1, 0; 0, 0] := by
  rw [show physTraceTransfer normalizedTensor =
      (4 / Real.sqrt 5 : ℂ) • physTraceTransfer tensor by
    simp [physTraceTransfer, normalizedTensor, Finset.smul_sum]]
  rw [physTraceTransfer_tensor, leftPairing_mul_rightPairing]

private lemma physTraceTransfer_blockTwo_normalizedTensor :
    physTraceTransfer (blockTwo normalizedTensor) =
      (16 / 5 : ℂ) • !![1, 0; 0, 0] := by
  have hsqrt_sq : (Real.sqrt 5 : ℂ) ^ 2 = 5 := by
    exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  rw [physTraceTransfer_blockTwo, physTraceTransfer_normalizedTensor]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  field_simp
  rw [hsqrt_sq]
  norm_num

/-- The two-site physical blocking of the source-normalized four-sector tensor
does not satisfy the trace-preserving completely positive map condition of
Definition 4.1. Its physical-trace transfer is `(16 / 5) P` for the nonzero
projection `P = !![1, 0; 0, 0]`, and is therefore not idempotent. Definition 4.1
would force literal idempotence.

This is the normalization-sensitive obstruction corresponding to the global
unit-weight convention of the source. The `IsSourceZCL` predicate used in this
development asks for idempotence up to a positive scalar and is therefore
scale-invariant; the paper's literal zero-correlation-length diagram is not.

Source: arXiv:1606.00608, the global BNT normalization at line 246,
Definition 4.1 at lines 645--659, and the trace identity at lines 1333--1340. -/
theorem blockTwo_normalizedTensor_not_isRFPViaTS :
    ¬ IsRFPViaTS (blockTwo normalizedTensor) := by
  intro h
  have hsq := physTraceTransfer_sq_of_isRFPViaTS (blockTwo normalizedTensor) h
  rw [physTraceTransfer_blockTwo_normalizedTensor] at hsq
  have h00 := congrFun (congrFun hsq 0) 0
  norm_num [Matrix.mul_apply, Fin.sum_univ_two] at h00

end MPOTensor.ActiveSectorSpanningCounterexample
