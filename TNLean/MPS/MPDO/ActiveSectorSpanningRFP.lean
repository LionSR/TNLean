/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.ActiveSectorSpanningAreaLaw
import TNLean.MPS.MPDO.PhysicalSectorPairPreservingObstruction
import TNLean.MPS.MPDO.RFPViaTSBlocking

/-!
# Renormalization maps for the four-sector classical tensor

The four-sector tensor from `ActiveSectorSpanningCounterexample` satisfies the
two trace-preserving completely positive map equations underlying Definition
4.1. Its two-site sector products are stochastic refinements of its one-site
sectors. Rectangular Kraus families obtained from those transition weights give
the two maps. The raw tensor is not in canonical form, so Definition 4.1 does
not classify this representative itself as a renormalization fixed point.

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

* `tensor_isRFPViaTS`: the explicit four-sector tensor satisfies the bare
  two-channel equations, without the source's canonical-form hypothesis.
* `blockTwo_tensor_isRFPViaTS`: its two-site physical blocking satisfies the
  same bare equations.
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
  simp only [tensor, ite_eq_left]
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
    rw [tensor, ite_eq_right hkl]
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
    rw [tensor, ite_eq_left hfirst, tensor, ite_eq_right hsecond, Matrix.mul_zero,
      Matrix.zero_mul, Matrix.trace_zero]
  · rw [tensor, ite_eq_right hfirst, Matrix.zero_mul, Matrix.zero_mul,
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

/-- The explicit four-sector tensor satisfies the bare trace-preserving
completely positive map equations represented by `IsRFPViaTS`. The refinement
map sends a sector to consecutive sector pairs with the neighboring transition
weights, while the coarse-graining map returns each pair to its represented
sector.

**Scope restriction (bare predicate, no canonical form):** Definition 4.1
assumes that the tensor is in canonical form. The raw tensor here does not
satisfy the global unit-weight canonical normalization, while the Lean
predicate `IsRFPViaTS` records only the two channel equations. Thus this
theorem is not an instance of Definition 4.1 for the raw representative.
Documented in
`docs/paper-gaps/cpsv16_zcl_canonical_form_normalization.tex`.

This is a classification of this explicit tensor, not a proof of the general
strong-area-law and zero-correlation-length implication in Theorem 4.9.

Source: arXiv:1606.00608, Definition 4.1, lines 645--659, and the proposed
implication in Theorem 4.9 at lines 1810--1825. -/
theorem tensor_isRFPViaTS : IsRFPViaTS tensor :=
  ⟨coarseningMap, refinementMap, coarseningMap_isKrausCPTP,
    refinementMap_isKrausCPTP, coarseningMap_physClose2,
    refinementMap_physClose1⟩

/-- The two-site physical blocking of the explicit four-sector tensor satisfies
the bare `IsRFPViaTS` equations. Its maps are obtained by applying the one-site
coarse-graining and refinement maps twice and passing to blocked coordinates.

**Scope restriction (bare predicate, no canonical form):** This theorem
inherits the scope restriction of `tensor_isRFPViaTS`. It proves the two channel
equations after blocking, but does not supply the canonical-form hypothesis of
Definition 4.1. Documented in
`docs/paper-gaps/cpsv16_zcl_canonical_form_normalization.tex`.

This proves the bare channel equations for this witness only; it does not prove
the universal implication from the hypotheses of Theorem 4.9.

Source: arXiv:1606.00608, Definition 4.1, lines 645--659, and the twice-applied
channel construction for Theorem 4.9 at lines 1810--1825. -/
theorem blockTwo_tensor_isRFPViaTS : IsRFPViaTS (MPOTensor.blockTwo tensor) :=
  tensor_isRFPViaTS.blockTwo

/-- The trace matrix of the directly written four-sector factorization is the
opposite rectangular product `rightPairing * leftPairing`.  The neighboring
operators of this factorization agree with those of the source-selected
inverse-map factorization by `inverseMapFactorization_neighboringOperator`.

Source: arXiv:1606.00608, Appendix C.2, equations `etarl` and `Tkn`, lines
1441--1482. -/
lemma factorization_neighboringTraceMatrix :
    factorization.neighboringTraceMatrix = rightPairing * leftPairing := by
  ext k h
  rw [PhysicalSectorFactorization.neighboringTraceMatrix_apply]
  rw [neighboringOperator_eq (show Fin 4 from k) (show Fin 4 from h)]
  change (∑ _ : Fin 1 × Fin 1, (rightPairing * leftPairing) k h) = _
  simp

/-- The selected four-sector trace matrix satisfies `C ^ 2 = C ^ 3`, the
consequence of the rectangular idempotence in the zero-correlation-length
calculation.

Source: arXiv:1606.00608, Appendix C.2, lines 1490--1497. -/
lemma factorization_neighboringTraceMatrix_pow_two_eq_pow_three :
    factorization.neighboringTraceMatrix ^ 2 =
      factorization.neighboringTraceMatrix ^ 3 := by
  rw [factorization_neighboringTraceMatrix]
  apply Matrix.pow_two_eq_pow_three_of_rectangular_idempotent
    leftPairing rightPairing
  change (leftPairing * rightPairing) * (leftPairing * rightPairing) =
    leftPairing * rightPairing
  rw [← physTraceTransfer_tensor]
  exact physTraceTransfer_tensor_idempotent

/-- The selected four-sector trace matrix does not satisfy the equality
`C = C ^ 3` required by a two-to-four-site channel which preserves every
outer sector pair.

This is a direct calculation for the inverse-map-selected factorization,
whose neighboring operators are identified at
`inverseMapFactorization_neighboringOperator`.  The equality `C ^ 2 = C ^ 3`
coming from literal zero correlation length is strictly weaker here.

Source comparison: arXiv:1606.00608, Appendix C.2, lines 1490--1498 and the
twice-iterated maps at lines 1821--1825. -/
lemma factorization_neighboringTraceMatrix_ne_pow_three :
    factorization.neighboringTraceMatrix ≠
      factorization.neighboringTraceMatrix ^ 3 := by
  rw [factorization_neighboringTraceMatrix]
  intro h
  apply rightPairing_mul_leftPairing_ne_idempotent
  have hsq3 := factorization_neighboringTraceMatrix_pow_two_eq_pow_three
  rw [factorization_neighboringTraceMatrix] at hsq3
  rw [← pow_two]
  exact hsq3.trans h.symm

/-- No trace-preserving family can coarse-grain the four-site neighboring
operator to the two-site neighboring operator while retaining each pair of
outer labels `k,h` in the selected four-sector factorization.

**Scope restriction (selected four-sector factorization):** this excludes
only the inverse-map-selected four-sector decomposition.  It does not exclude
mixing or coarsening those labels, nor a different physical-sector
factorization.  Documented in `docs/paper-gaps/cpgsv17_pf_rank_one.tex`.

Derived from the sector-controlled, twice-iterated maps in
arXiv:1606.00608, Appendix C.2, lines 1522--1555 and 1821--1825. -/
theorem not_exists_pairwise_fourSite_coarsening :
    ¬ ∃ S : (k h : Fin 4) →
        Matrix
            (PhysicalSectorFactorization.FourSiteMiddleIndex factorization k h)
            (PhysicalSectorFactorization.FourSiteMiddleIndex factorization k h) ℂ →ₗ[ℂ]
          Matrix
            (PhysicalSectorFactorization.NeighborIndex factorization k h)
            (PhysicalSectorFactorization.NeighborIndex factorization k h) ℂ,
      (∀ k h X, (S k h X).trace = X.trace) ∧
        ∀ k h,
          S k h (factorization.fourSiteNeighboringOperator k h) =
            factorization.neighboringOperator k h := by
  rintro ⟨S, htrace, hmap⟩
  exact factorization_neighboringTraceMatrix_ne_pow_three
    (factorization.neighboringTraceMatrix_eq_pow_three_of_pairwise_coarsening
      S htrace hmap)

/-- No trace-preserving family can refine the two-site neighboring operator
to the four-site neighboring operator while retaining each pair of outer
labels `k,h` in the selected four-sector factorization.

**Scope restriction (selected four-sector factorization):** this excludes
only the inverse-map-selected four-sector decomposition.  It does not exclude
mixing or coarsening those labels, nor a different physical-sector
factorization.  Documented in `docs/paper-gaps/cpgsv17_pf_rank_one.tex`.

Derived from the sector-controlled, twice-iterated maps in
arXiv:1606.00608, Appendix C.2, lines 1522--1555 and 1821--1825. -/
theorem not_exists_pairwise_fourSite_refinement :
    ¬ ∃ T : (k h : Fin 4) →
        Matrix
            (PhysicalSectorFactorization.NeighborIndex factorization k h)
            (PhysicalSectorFactorization.NeighborIndex factorization k h) ℂ →ₗ[ℂ]
          Matrix
            (PhysicalSectorFactorization.FourSiteMiddleIndex factorization k h)
            (PhysicalSectorFactorization.FourSiteMiddleIndex factorization k h) ℂ,
      (∀ k h X, (T k h X).trace = X.trace) ∧
        ∀ k h,
          T k h (factorization.neighboringOperator k h) =
            factorization.fourSiteNeighboringOperator k h := by
  rintro ⟨T, htrace, hmap⟩
  exact factorization_neighboringTraceMatrix_ne_pow_three
    (factorization.neighboringTraceMatrix_eq_pow_three_of_pairwise_refinement
      T htrace hmap)

/-- The blocked tensor has trace-preserving completely positive
renormalization maps even though the selected four-sector trace matrix fails
`C = C ^ 3`.  The exhibited maps mix or coarsen the selected sector labels;
concretely, `coarseningMap` merges `(i,j)` to `pairLabel (i,j)`.

This does not contradict the pair-preserving obstructions above: the bare
`IsRFPViaTS` equations do not require a channel to retain each outer-sector
pair of a chosen nonminimal decomposition.

**Scope restriction (bare predicate and selected decomposition):** documented
in `docs/paper-gaps/cpsv16_zcl_canonical_form_normalization.tex` and
`docs/paper-gaps/cpgsv17_pf_rank_one.tex`.

Source comparison: arXiv:1606.00608, Definition 4.1, lines 645--659, and the
sector-projected construction at Appendix C.2, lines 1810--1825. -/
theorem blockTwo_tensor_isRFPViaTS_and_pairwise_trace_obstruction :
    IsRFPViaTS (MPOTensor.blockTwo tensor) ∧
      factorization.neighboringTraceMatrix ≠
        factorization.neighboringTraceMatrix ^ 3 :=
  ⟨blockTwo_tensor_isRFPViaTS,
    factorization_neighboringTraceMatrix_ne_pow_three⟩

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
