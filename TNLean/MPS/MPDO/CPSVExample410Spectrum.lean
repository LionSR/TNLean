/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Analysis.EntropyDecomposition
import QICLean.Channel.SingleKrausPositivity
import QICLean.Algebra.MatrixIsometryKronecker
import TNLean.MPS.MPDO.CPSVExample410CorrelatedFlip
import TNLean.MPS.MPDO.CPSVExample410Operator
import TNLean.MPS.MPDO.SourceZCLMarginal

/-!
# Reduced-state spectra of corrected CPSV16 Example 4.10

The corrected tensor is a mixture of products of Bell states. A flip configuration on the four
spins determines the cyclic difference pattern on the four bonds. The corresponding sixteen
Bell-network vectors form an orthonormal family, while the eight odd-parity patterns have zero
weight. Successive prefix partial traces give the one-, two-, and three-site spectra from this
four-site decomposition at flip probability one quarter.

**Local fix (left-right correlated flip):** CPSV16 lines 901--902 repeat the left-qubit label.
This module uses the left-right flip defined in `CPSVExample410Operator`, whose bond-pattern
weights agree with the entropy values printed at source line 904. See
`docs/paper-gaps/cpsv16_examples_4_10_4_11_entropy.tex`.

## Main results

* `charpoly_roots_one`: the one-site state has four roots $1/4$.
* `charpoly_roots_two`: the two-site state has eight zero roots and nonzero roots $5/32$ and
  $3/32$, each four times.
* `charpoly_roots_three`: the three-site state has 48 zero roots, root $7/64$ four times, and
  root $3/64$ twelve times.
* `charpoly_roots_four`: the normalized four-site state has nonzero roots $41/128$ once,
  $15/128$ four times, and $9/128$ three times.

## Reference

* Cirac--Perez-Garcia--Schuch--Verstraete, arXiv:1606.00608, Example 4.10,
  lines 897--905.
-/

open scoped Matrix BigOperators ComplexOrder Kronecker
noncomputable section

namespace MPOTensor.CPSVExample410Spectrum
open MPOTensor MPOTensor.CPSVExample410Operator

private lemma single_mul_single_eq_if {a b c : Type*} [Fintype b]
    [DecidableEq a] [DecidableEq b] [DecidableEq c]
    (i : a) (j k : b) (l : c) (x y : ℂ) :
    Matrix.single i j x * Matrix.single k l y =
      if j = k then Matrix.single i l (x * y) else 0 := by
  split_ifs with h
  · subst k
    exact Matrix.single_mul_single_same x i j l y
  · exact Matrix.single_mul_single_of_ne x i j k h y

private lemma trace_single_eq_if {a : Type*} [Fintype a] [DecidableEq a]
    (i j : a) (x : ℂ) :
    Matrix.trace (Matrix.single i j x) = if i = j then x else 0 := by
  split_ifs with h
  · subst j
    exact Matrix.trace_single_eq_same i x
  · simp [Matrix.trace, h]

private lemma trace_ite {a : Type*} [Fintype a] (p : Prop) [Decidable p]
    (A B : Matrix a a ℂ) :
    Matrix.trace (if p then A else B) = if p then Matrix.trace A else Matrix.trace B := by
  split_ifs <;> rfl

private lemma trace_zero {a : Type*} [Fintype a] :
    Matrix.trace (0 : Matrix a a ℂ) = 0 := by simp [Matrix.trace]

private def toggle (k x : Fin 2) : Fin 2 := if k = 0 then x else 1 - x

private lemma toggle_eq_iff_xor_eq (k l x y : Fin 2) :
    toggle k x = toggle l y ↔
      xor (finTwoEquiv x) (finTwoEquiv y) = xor (finTwoEquiv k) (finTwoEquiv l) := by
  fin_cases k <;> fin_cases l <;> fin_cases x <;> fin_cases y <;> decide

private lemma purifier_eq_single (i : Fin 4) (k : Fin 2) :
    purifier i k = Matrix.single (toggle k (pairEquiv i).1) (toggle k (pairEquiv i).2)
      (channelCoeff k / Real.sqrt 2) := by
  fin_cases k <;>
    simp [purifier, correlatedFlip, toggle, Matrix.smul_single, smul_eq_mul]

private def boolOfFin (x : Fin 2) : Bool := finTwoEquiv x

private def flipTuple (κ : Fin 4 → Fin 2) : Bool × Bool × Bool × Bool :=
  (boolOfFin (κ 0), boolOfFin (κ 1), boolOfFin (κ 2), boolOfFin (κ 3))

private def physicalBondPattern (σ : Fin 4 → Fin 4) : Bool × Bool × Bool × Bool :=
  (xor (finTwoEquiv (pairEquiv (σ 0)).2) (finTwoEquiv (pairEquiv (σ 1)).1),
   xor (finTwoEquiv (pairEquiv (σ 1)).2) (finTwoEquiv (pairEquiv (σ 2)).1),
   xor (finTwoEquiv (pairEquiv (σ 2)).2) (finTwoEquiv (pairEquiv (σ 3)).1),
   xor (finTwoEquiv (pairEquiv (σ 3)).2) (finTwoEquiv (pairEquiv (σ 0)).1))

private def bellEmbedding : Matrix (Fin 2 × Fin 2) Bool ℂ := fun x u =>
  if xor (finTwoEquiv x.1) (finTwoEquiv x.2) = u then (Real.sqrt 2 : ℂ)⁻¹ else 0

private def rawFour : Matrix
    ((Fin 2 × Fin 2) × ((Fin 2 × Fin 2) × ((Fin 2 × Fin 2) × (Fin 2 × Fin 2))))
    (Bool × Bool × Bool × Bool) ℂ :=
  bellEmbedding ⊗ₖ (bellEmbedding ⊗ₖ (bellEmbedding ⊗ₖ bellEmbedding))

private def rowFourEquiv :
    ((Fin 2 × Fin 2) × ((Fin 2 × Fin 2) × ((Fin 2 × Fin 2) × (Fin 2 × Fin 2)))) ≃
      (Fin 4 → Fin 4) where
  toFun x n := if n = 0 then pairEquiv.symm (x.2.2.2.2, x.1.1)
    else if n = 1 then pairEquiv.symm (x.1.2, x.2.1.1)
    else if n = 2 then pairEquiv.symm (x.2.1.2, x.2.2.1.1)
    else pairEquiv.symm (x.2.2.1.2, x.2.2.2.1)
  invFun σ := (
    ((pairEquiv (σ 0)).2, (pairEquiv (σ 1)).1),
    (((pairEquiv (σ 1)).2, (pairEquiv (σ 2)).1),
      (((pairEquiv (σ 2)).2, (pairEquiv (σ 3)).1),
        ((pairEquiv (σ 3)).2, (pairEquiv (σ 0)).1))))
  left_inv x := by
    rcases x with ⟨⟨r0, l1⟩, ⟨⟨r1, l2⟩, ⟨⟨r2, l3⟩, ⟨r3, l0⟩⟩⟩⟩
    simp
  right_inv σ := by
    funext n
    fin_cases n <;> simp

private def VFour : Matrix (Fin 4 → Fin 4) (Bool × Bool × Bool × Bool) ℂ :=
  Matrix.reindex rowFourEquiv (Equiv.refl _) rawFour

private lemma VFour_apply (σ : Fin 4 → Fin 4) (t : Bool × Bool × Bool × Bool) :
    VFour σ t = if physicalBondPattern σ = t then 1 / 4 else 0 := by
  have hsqrtTwoSq : ((↑(Real.sqrt 2) : ℂ) ^ 2) = 2 :=
    Complex.ofReal_sqrt_sq 2 (by positivity)
  have hsqrtTwoFourth : ((↑(Real.sqrt 2) : ℂ) ^ 4) = 4 := by
    rw [show ((↑(Real.sqrt 2) : ℂ) ^ 4) = ((↑(Real.sqrt 2) : ℂ) ^ 2) ^ 2 by ring,
      hsqrtTwoSq]
    norm_num
  have hsqrtTwoNe : (↑(Real.sqrt 2) : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2))
  rcases t with ⟨t0, t1, t2, t3⟩
  simp [VFour, rawFour, rowFourEquiv, bellEmbedding, physicalBondPattern,
    Matrix.kroneckerMap_apply]
  split_ifs <;> simp_all
  field_simp
  ring_nf at hsqrtTwoFourth ⊢
  rw [hsqrtTwoFourth]

private lemma bellEmbedding_isometry : bellEmbeddingᴴ * bellEmbedding = 1 := by
  ext u v
  rcases u <;> rcases v <;>
    norm_num [bellEmbedding, Matrix.mul_apply, Fintype.sum_prod_type,
      Fin.sum_univ_two, Matrix.conjTranspose_apply] <;>
    rw [← pow_two, ← Complex.ofReal_inv, ← Complex.ofReal_pow, inv_pow,
      Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)] <;>
    norm_num

set_option linter.unusedFintypeInType false in
private lemma reindex_isometry {a b a' b' : Type*} [Fintype a] [Fintype b]
    [Fintype a'] [Fintype b'] [DecidableEq b] [DecidableEq b']
    (A : Matrix a b ℂ) (ha : a ≃ a') (hb : b ≃ b') (hA : Aᴴ * A = 1) :
    (Matrix.reindex ha hb A)ᴴ * Matrix.reindex ha hb A = 1 := by
  rw [Matrix.conjTranspose_reindex]
  change Aᴴ.submatrix hb.symm ha.symm * A.submatrix ha.symm hb.symm = 1
  rw [Matrix.submatrix_mul_equiv, hA, Matrix.submatrix_one_equiv]

private lemma rawFour_isometry : rawFourᴴ * rawFour = 1 := by
  apply Matrix.IsIsometry.kronecker bellEmbedding _ bellEmbedding_isometry
  apply Matrix.IsIsometry.kronecker bellEmbedding _ bellEmbedding_isometry
  exact Matrix.IsIsometry.kronecker bellEmbedding bellEmbedding bellEmbedding_isometry
    bellEmbedding_isometry

private theorem VFour_isometry : VFourᴴ * VFour = 1 :=
  reindex_isometry rawFour rowFourEquiv (Equiv.refl _) rawFour_isometry

private theorem amplitude (κ : Fin 4 → Fin 2) (σ : Fin 4 → Fin 4) :
    Matrix.trace ((List.ofFn fun l => purifier (σ l) (κ l)).prod) =
      (∏ n, channelCoeff (κ n)) * VFour σ
        (CPSVExample410CorrelatedFlip.bondPattern (flipTuple κ)) := by
  have hsqrtTwoSq : ((↑(Real.sqrt 2) : ℂ) ^ 2) = 2 :=
    Complex.ofReal_sqrt_sq 2 (by positivity)
  have hsqrtTwoFourth : ((↑(Real.sqrt 2) : ℂ) ^ 4) = 4 := by
    rw [show ((↑(Real.sqrt 2) : ℂ) ^ 4) = ((↑(Real.sqrt 2) : ℂ) ^ 2) ^ 2 by ring,
      hsqrtTwoSq]
    norm_num
  have hsqrtTwoNe : (↑(Real.sqrt 2) : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2))
  simp [List.ofFn_succ, purifier_eq_single, single_mul_single_eq_if]
  simp only [trace_ite, trace_zero, trace_single_eq_if, toggle_eq_iff_xor_eq]
  simp [VFour_apply, physicalBondPattern, flipTuple, boolOfFin,
    CPSVExample410CorrelatedFlip.bondPattern, Fin.prod_univ_succ]
  have hcommPhysical := Bool.xor_comm (finTwoEquiv (pairEquiv (σ 0)).1)
    (finTwoEquiv (pairEquiv (σ 3)).2)
  have hcommFlip := Bool.xor_comm (finTwoEquiv (κ 0)) (finTwoEquiv (κ 3))
  split_ifs <;> simp_all
  field_simp
  ring_nf at hsqrtTwoFourth ⊢
  rw [hsqrtTwoFourth]
  ring


private def flipConfigEquiv : (Fin 4 → Fin 2) ≃ (Bool × Bool × Bool × Bool) where
  toFun := flipTuple
  invFun s n := if n = 0 then finTwoEquiv.symm s.1
    else if n = 1 then finTwoEquiv.symm s.2.1
    else if n = 2 then finTwoEquiv.symm s.2.2.1
    else finTwoEquiv.symm s.2.2.2
  left_inv κ := by
    funext n
    fin_cases n <;> simp [flipTuple, boolOfFin]
  right_inv s := by
    rcases s with ⟨s0, s1, s2, s3⟩
    simp [flipTuple, boolOfFin]

private lemma channelCoeff_normSq (k : Fin 2) :
    channelCoeff k * (starRingEnd ℂ) (channelCoeff k) =
      (CPSVExample410CorrelatedFlip.flipWeight (boolOfFin k) : ℂ) := by
  have h0 : finTwoEquiv (0 : Fin 2) = false := by decide
  have h1 : finTwoEquiv (1 : Fin 2) = true := by decide
  fin_cases k
  · simp [channelCoeff, boolOfFin, CPSVExample410CorrelatedFlip.flipWeight, h0]
    have hsqrtThreeSq : ((↑(Real.sqrt 3) : ℂ) ^ 2) = 3 :=
      Complex.ofReal_sqrt_sq 3 (by positivity)
    field_simp
    ring_nf at hsqrtThreeSq ⊢
    rw [hsqrtThreeSq]
    norm_num [map_ofNat]
  · norm_num [channelCoeff, boolOfFin, CPSVExample410CorrelatedFlip.flipWeight, h1,
      map_ofNat]

private lemma channelCoeff_prod_normSq (κ : Fin 4 → Fin 2) :
    (∏ n, channelCoeff (κ n)) * star (∏ n, channelCoeff (κ n)) =
      (CPSVExample410CorrelatedFlip.flipProb (flipTuple κ) : ℂ) := by
  rw [Fin.prod_univ_four]
  change channelCoeff (κ 0) * channelCoeff (κ 1) * channelCoeff (κ 2) *
      channelCoeff (κ 3) *
      (starRingEnd ℂ) (channelCoeff (κ 0) * channelCoeff (κ 1) *
        channelCoeff (κ 2) * channelCoeff (κ 3)) = _
  rw [map_mul, map_mul, map_mul]
  rw [show channelCoeff (κ 0) * channelCoeff (κ 1) * channelCoeff (κ 2) *
      channelCoeff (κ 3) *
      ((starRingEnd ℂ) (channelCoeff (κ 0)) *
        (starRingEnd ℂ) (channelCoeff (κ 1)) *
        (starRingEnd ℂ) (channelCoeff (κ 2)) *
        (starRingEnd ℂ) (channelCoeff (κ 3))) =
      (channelCoeff (κ 0) * (starRingEnd ℂ) (channelCoeff (κ 0))) *
        (channelCoeff (κ 1) * (starRingEnd ℂ) (channelCoeff (κ 1))) *
        (channelCoeff (κ 2) * (starRingEnd ℂ) (channelCoeff (κ 2))) *
        (channelCoeff (κ 3) * (starRingEnd ℂ) (channelCoeff (κ 3))) by ring]
  rw [channelCoeff_normSq, channelCoeff_normSq, channelCoeff_normSq,
    channelCoeff_normSq]
  simp [CPSVExample410CorrelatedFlip.flipProb, flipTuple, boolOfFin]

private lemma star_VFour (σ : Fin 4 → Fin 4) (t : Bool × Bool × Bool × Bool) :
    (starRingEnd ℂ) (VFour σ t) = VFour σ t := by
  rw [VFour_apply]
  split_ifs <;> norm_num [map_ofNat]

private lemma mul_mul_star_mul_of_real (a b c d : ℂ)
    (hc : (starRingEnd ℂ) c = c) (ha : a * (starRingEnd ℂ) a = d) :
    a * b * (starRingEnd ℂ) (a * c) = d * b * c := by
  rw [map_mul, hc]
  calc
    a * b * ((starRingEnd ℂ) a * c) =
        (a * (starRingEnd ℂ) a) * b * c := by ring
    _ = d * b * c := by rw [ha]

private lemma singleKrausMap_diagonal_apply_of_real
    {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β]
    (V : Matrix β α ℂ) (w : α → ℂ)
    (hV : ∀ i t, (starRingEnd ℂ) (V i t) = V i t) (i j : β) :
    singleKrausMap V (Matrix.diagonal w) i j = ∑ t, w t * V i t * V j t := by
  rw [singleKrausMap_apply, Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro t _
  rw [Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_eq_single t]
  · simp only [Matrix.diagonal_apply, ite_true]
    change V i t * w t * (starRingEnd ℂ) (V j t) = _
    rw [hV]
    ring
  · intro u _ hut
    simp [hut]
  · simp

private lemma sum_bondWeight_mul (f : (Bool × Bool × Bool × Bool) → ℂ) :
    ∑ t, (CPSVExample410CorrelatedFlip.bondWeight t : ℂ) * f t =
      ∑ s, (CPSVExample410CorrelatedFlip.flipProb s : ℂ) *
        f (CPSVExample410CorrelatedFlip.bondPattern s) := by
  simp only [CPSVExample410CorrelatedFlip.bondWeight, Complex.ofReal_sum]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  rcases s with ⟨_ | _, _ | _, _ | _, _ | _⟩ <;>
    simp [CPSVExample410CorrelatedFlip.bondPattern, Fintype.sum_prod_type]

private theorem mpo_four_eq_purification :
    mpo M 4 = ∑ κ : Fin 4 → Fin 2,
      Matrix.vecMulVec
        (fun σ => Matrix.trace ((List.ofFn fun l => purifier (σ l) (κ l)).prod))
        (star (fun σ => Matrix.trace ((List.ofFn fun l => purifier (σ l) (κ l)).prod))) := by
  ext σ τ
  simp only [mpo_apply, mpoMatrixEntry, MPOTensor.evalWord_ofFn]
  have hM : ∀ i j : Fin 4, M i j = (∑ k : Fin 2,
      purifier i k ⊗ₖ (purifier j k).map (starRingEnd ℂ)).submatrix
        (↑pairEquiv) (↑pairEquiv) := fun _ _ => rfl
  rw [MPOTensor.lpdo_prod_decomp purifier pairEquiv hM σ τ]
  have trace_sub : ∀ (X : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ),
      Matrix.trace (X.submatrix (↑pairEquiv) (↑pairEquiv)) = Matrix.trace X := by
    intro X
    simp only [Matrix.trace, Matrix.diag, Matrix.submatrix_apply]
    exact pairEquiv.sum_comp (fun p => X p p)
  rw [trace_sub, Matrix.trace_sum]
  simp_rw [Matrix.trace_kronecker]
  simp_rw [← AddMonoidHom.map_trace (starRingEnd ℂ)]
  simp only [Matrix.sum_apply, Matrix.vecMulVec_apply, Pi.star_apply, starRingEnd_apply]


private theorem mpo_four_eq_bellDiagonal :
    mpo M 4 = singleKrausMap VFour
      (Matrix.diagonal fun t =>
        (CPSVExample410CorrelatedFlip.bondWeight t : ℂ)) := by
  rw [mpo_four_eq_purification]
  ext σ τ
  simp only [Matrix.sum_apply, Matrix.vecMulVec_apply, Pi.star_apply]
  simp_rw [amplitude]
  have hsummand (κ : Fin 4 → Fin 2) :
      (∏ n, channelCoeff (κ n)) *
          VFour σ (CPSVExample410CorrelatedFlip.bondPattern (flipTuple κ)) *
        (starRingEnd ℂ) ((∏ n, channelCoeff (κ n)) *
          VFour τ (CPSVExample410CorrelatedFlip.bondPattern (flipTuple κ))) =
      (CPSVExample410CorrelatedFlip.flipProb (flipTuple κ) : ℂ) *
        VFour σ (CPSVExample410CorrelatedFlip.bondPattern (flipTuple κ)) *
        VFour τ (CPSVExample410CorrelatedFlip.bondPattern (flipTuple κ)) := by
    exact mul_mul_star_mul_of_real _ _ _ _
      (star_VFour τ (CPSVExample410CorrelatedFlip.bondPattern (flipTuple κ)))
      (channelCoeff_prod_normSq κ)
  have hsumκ :
      (∑ κ : Fin 4 → Fin 2,
        (∏ n, channelCoeff (κ n)) *
            VFour σ (CPSVExample410CorrelatedFlip.bondPattern (flipTuple κ)) *
          star ((∏ n, channelCoeff (κ n)) *
            VFour τ (CPSVExample410CorrelatedFlip.bondPattern (flipTuple κ)))) =
      ∑ κ : Fin 4 → Fin 2,
        (CPSVExample410CorrelatedFlip.flipProb (flipTuple κ) : ℂ) *
          VFour σ (CPSVExample410CorrelatedFlip.bondPattern (flipTuple κ)) *
          VFour τ (CPSVExample410CorrelatedFlip.bondPattern (flipTuple κ)) := by
    apply Finset.sum_congr rfl
    intro κ _
    change (∏ n, channelCoeff (κ n)) *
        VFour σ (CPSVExample410CorrelatedFlip.bondPattern (flipTuple κ)) *
      (starRingEnd ℂ) ((∏ n, channelCoeff (κ n)) *
        VFour τ (CPSVExample410CorrelatedFlip.bondPattern (flipTuple κ))) = _
    exact hsummand κ
  rw [hsumκ]
  let g : (Bool × Bool × Bool × Bool) → ℂ := fun s ↦
    (CPSVExample410CorrelatedFlip.flipProb s : ℂ) *
      VFour σ (CPSVExample410CorrelatedFlip.bondPattern s) *
      VFour τ (CPSVExample410CorrelatedFlip.bondPattern s)
  have hsum : (∑ x, g (flipConfigEquiv x)) = ∑ s, g s := flipConfigEquiv.sum_comp g
  change (∑ x, g (flipConfigEquiv x)) = _
  rw [hsum]
  dsimp only [g]
  rw [singleKrausMap_diagonal_apply_of_real VFour _ star_VFour]
  simpa only [mul_assoc] using
    (sum_bondWeight_mul (fun t ↦ VFour σ t * VFour τ t)).symm

private theorem trace_mpo_four : (mpo M 4).trace = 1 := by
  rw [trace_mpo_eq_trace_verticalLoop_pow, verticalLoop_eq_physTraceTransfer,
    physTraceTransfer_M]
  have hp : traceProjector ^ 4 = traceProjector := by
    calc
      traceProjector ^ 4 = traceProjector ^ 2 * traceProjector ^ 2 := by noncomm_ring
      _ = traceProjector := by simp only [pow_two, traceProjector_sq]
  rw [hp, Matrix.trace, Fin.sum_univ_four]
  change (1 / 2 : ℂ) + 0 + 0 + 1 / 2 = 1
  norm_num

private theorem reduced_four_eq_bellDiagonal :
    reducedBlockState M 4 4 (by omega) = singleKrausMap VFour
      (Matrix.diagonal fun t =>
        (CPSVExample410CorrelatedFlip.bondWeight t : ℂ)) := by
  ext σ τ
  rw [reducedBlockState_apply_eq_trace_evalWord_mul_verticalLoop_pow,
    trace_mpo_four]
  simp only [inv_one, one_mul, Nat.sub_self, pow_zero, Matrix.mul_one]
  change mpo M 4 σ τ = _
  rw [mpo_four_eq_bellDiagonal]

private lemma VFour_apply_bell (σ : Fin 4 → Fin 4)
    (t : Bool × Bool × Bool × Bool) :
    VFour σ t =
      bellEmbedding ((pairEquiv (σ 0)).2, (pairEquiv (σ 1)).1) t.1 *
        (bellEmbedding ((pairEquiv (σ 1)).2, (pairEquiv (σ 2)).1) t.2.1 *
          (bellEmbedding ((pairEquiv (σ 2)).2, (pairEquiv (σ 3)).1) t.2.2.1 *
            bellEmbedding ((pairEquiv (σ 3)).2, (pairEquiv (σ 0)).1) t.2.2.2)) := by
  rfl

private def bitEmbedding : Matrix (Fin 2) Bool ℂ := fun i b =>
  if finTwoEquiv i = b then 1 else 0

private lemma bitEmbedding_isometry : bitEmbeddingᴴ * bitEmbedding = 1 := by
  ext b c
  rcases b <;> rcases c <;>
    norm_num [bitEmbedding, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.conjTranspose_apply, Matrix.one_apply, finTwoEquiv]

private def rawThree : Matrix
    (Fin 2 × ((Fin 2 × Fin 2) × ((Fin 2 × Fin 2) × Fin 2)))
    (Bool × Bool × Bool × Bool) ℂ :=
  bitEmbedding ⊗ₖ (bellEmbedding ⊗ₖ (bellEmbedding ⊗ₖ bitEmbedding))

private def rowThreeEquiv :
    (Fin 2 × ((Fin 2 × Fin 2) × ((Fin 2 × Fin 2) × Fin 2))) ≃
      (Fin 3 → Fin 4) where
  toFun x n := if n = 0 then pairEquiv.symm (x.1, x.2.1.1)
    else if n = 1 then pairEquiv.symm (x.2.1.2, x.2.2.1.1)
    else pairEquiv.symm (x.2.2.1.2, x.2.2.2)
  invFun σ := ((pairEquiv (σ 0)).1,
    (((pairEquiv (σ 0)).2, (pairEquiv (σ 1)).1),
      ((pairEquiv (σ 1)).2, (pairEquiv (σ 2)).1), (pairEquiv (σ 2)).2))
  left_inv x := by rcases x with ⟨l0, ⟨⟨r0, l1⟩, ⟨⟨r1, l2⟩, r2⟩⟩⟩; simp
  right_inv σ := by funext n; fin_cases n <;> simp

private def VThree : Matrix (Fin 3 → Fin 4) (Bool × Bool × Bool × Bool) ℂ :=
  Matrix.reindex rowThreeEquiv (Equiv.refl _) rawThree

private lemma VThree_apply (σ : Fin 3 → Fin 4) (x : Bool × Bool × Bool × Bool) :
    VThree σ x =
      bitEmbedding (pairEquiv (σ 0)).1 x.1 *
        (bellEmbedding ((pairEquiv (σ 0)).2, (pairEquiv (σ 1)).1) x.2.1 *
          (bellEmbedding ((pairEquiv (σ 1)).2, (pairEquiv (σ 2)).1) x.2.2.1 *
            bitEmbedding (pairEquiv (σ 2)).2 x.2.2.2)) := by
  rfl

private lemma VThree_isometry : VThreeᴴ * VThree = 1 := by
  apply reindex_isometry rawThree rowThreeEquiv (Equiv.refl _)
  apply Matrix.IsIsometry.kronecker bitEmbedding _ bitEmbedding_isometry
  apply Matrix.IsIsometry.kronecker bellEmbedding _ bellEmbedding_isometry
  exact Matrix.IsIsometry.kronecker bellEmbedding bitEmbedding bellEmbedding_isometry
    bitEmbedding_isometry

private def rawTwo : Matrix
    (Fin 2 × ((Fin 2 × Fin 2) × Fin 2)) (Bool × Bool × Bool) ℂ :=
  bitEmbedding ⊗ₖ (bellEmbedding ⊗ₖ bitEmbedding)

private def rowTwoEquiv :
    (Fin 2 × ((Fin 2 × Fin 2) × Fin 2)) ≃ (Fin 2 → Fin 4) where
  toFun x n := if n = 0 then pairEquiv.symm (x.1, x.2.1.1)
    else pairEquiv.symm (x.2.1.2, x.2.2)
  invFun σ := ((pairEquiv (σ 0)).1,
    ((pairEquiv (σ 0)).2, (pairEquiv (σ 1)).1), (pairEquiv (σ 1)).2)
  left_inv x := by rcases x with ⟨l0, ⟨⟨r0, l1⟩, r1⟩⟩; simp
  right_inv σ := by funext n; fin_cases n <;> simp

private def VTwo : Matrix (Fin 2 → Fin 4) (Bool × Bool × Bool) ℂ :=
  Matrix.reindex rowTwoEquiv (Equiv.refl _) rawTwo

private lemma VTwo_apply (σ : Fin 2 → Fin 4) (x : Bool × Bool × Bool) :
    VTwo σ x = bitEmbedding (pairEquiv (σ 0)).1 x.1 *
      (bellEmbedding ((pairEquiv (σ 0)).2, (pairEquiv (σ 1)).1) x.2.1 *
        bitEmbedding (pairEquiv (σ 1)).2 x.2.2) := by
  rfl

private lemma VTwo_isometry : VTwoᴴ * VTwo = 1 := by
  apply reindex_isometry rawTwo rowTwoEquiv (Equiv.refl _)
  apply Matrix.IsIsometry.kronecker bitEmbedding _ bitEmbedding_isometry
  exact Matrix.IsIsometry.kronecker bellEmbedding bitEmbedding bellEmbedding_isometry
    bitEmbedding_isometry

private def rawOne : Matrix (Fin 2 × Fin 2) (Bool × Bool) ℂ :=
  bitEmbedding ⊗ₖ bitEmbedding

private def rowOneEquiv : (Fin 2 × Fin 2) ≃ (Fin 1 → Fin 4) where
  toFun x _ := pairEquiv.symm x
  invFun σ := pairEquiv (σ 0)
  left_inv x := by simp
  right_inv σ := by funext n; fin_cases n; simp

private def VOne : Matrix (Fin 1 → Fin 4) (Bool × Bool) ℂ :=
  Matrix.reindex rowOneEquiv (Equiv.refl _) rawOne

private lemma VOne_apply (σ : Fin 1 → Fin 4) (x : Bool × Bool) :
    VOne σ x = bitEmbedding (pairEquiv (σ 0)).1 x.1 *
      bitEmbedding (pairEquiv (σ 0)).2 x.2 := by
  rfl

private lemma VOne_isometry : VOneᴴ * VOne = 1 := by
  apply reindex_isometry rawOne rowOneEquiv (Equiv.refl _)
  exact Matrix.IsIsometry.kronecker bitEmbedding bitEmbedding bitEmbedding_isometry
    bitEmbedding_isometry

private lemma sqrt_two_sq_inv : (((↑(Real.sqrt 2) : ℂ) ^ 2)⁻¹) = 1 / 2 := by
  rw [Complex.ofReal_sqrt_sq 2 (by norm_num)]
  norm_num

private lemma bellEmbedding_partial_right (a b : Fin 2) (u : Bool) :
    ∑ z : Fin 2, bellEmbedding (a, z) u * bellEmbedding (b, z) u =
      if a = b then 1 / 2 else 0 := by
  fin_cases a <;> fin_cases b <;> rcases u <;>
    norm_num [bellEmbedding, Fin.sum_univ_two, finTwoEquiv, ← pow_two,
      sqrt_two_sq_inv]

private lemma bellEmbedding_partial_left (a b : Fin 2) (u : Bool) :
    ∑ z : Fin 2, bellEmbedding (z, a) u * bellEmbedding (z, b) u =
      if a = b then 1 / 2 else 0 := by
  fin_cases a <;> fin_cases b <;> rcases u <;>
    norm_num [bellEmbedding, Fin.sum_univ_two, finTwoEquiv, ← pow_two,
      sqrt_two_sq_inv]

private lemma star_bitEmbedding (i : Fin 2) (b : Bool) :
    star (bitEmbedding i b) = bitEmbedding i b := by
  simp [bitEmbedding]

private lemma star_bellEmbedding (a b : Fin 2) (u : Bool) :
    star (bellEmbedding (a, b) u) = bellEmbedding (a, b) u := by
  simp only [RCLike.star_def]
  simp [bellEmbedding]
  split_ifs <;> norm_num

private lemma star_mul_of_fixed (a b : ℂ) (ha : star a = a) (hb : star b = b) :
    star (a * b) = a * b := by
  change (starRingEnd ℂ) a = a at ha
  change (starRingEnd ℂ) b = b at hb
  change (starRingEnd ℂ) (a * b) = a * b
  rw [map_mul, ha, hb]

private lemma star_VThree (σ : Fin 3 → Fin 4) (x : Bool × Bool × Bool × Bool) :
    star (VThree σ x) = VThree σ x := by
  rw [VThree_apply]
  exact star_mul_of_fixed _ _ (star_bitEmbedding _ _)
    (star_mul_of_fixed _ _ (star_bellEmbedding _ _ _)
      (star_mul_of_fixed _ _ (star_bellEmbedding _ _ _) (star_bitEmbedding _ _)))

private lemma star_VTwo (σ : Fin 2 → Fin 4) (x : Bool × Bool × Bool) :
    star (VTwo σ x) = VTwo σ x := by
  rw [VTwo_apply]
  exact star_mul_of_fixed _ _ (star_bitEmbedding _ _)
    (star_mul_of_fixed _ _ (star_bellEmbedding _ _ _) (star_bitEmbedding _ _))

private lemma star_VOne (σ : Fin 1 → Fin 4) (x : Bool × Bool) :
    star (VOne σ x) = VOne σ x := by
  rw [VOne_apply]
  exact star_mul_of_fixed _ _ (star_bitEmbedding _ _) (star_bitEmbedding _ _)

private lemma VFour_append_one (σ : Fin 3 → Fin 4) (q : Fin 2 × Fin 2)
    (t : Bool × Bool × Bool × Bool) :
    VFour (Fin.append σ (rowOneEquiv q)) t =
      bellEmbedding ((pairEquiv (σ 0)).2, (pairEquiv (σ 1)).1) t.1 *
        (bellEmbedding ((pairEquiv (σ 1)).2, (pairEquiv (σ 2)).1) t.2.1 *
          (bellEmbedding ((pairEquiv (σ 2)).2, q.1) t.2.2.1 *
            bellEmbedding (q.2, (pairEquiv (σ 0)).1) t.2.2.2)) := by
  rw [VFour_apply_bell]
  have h0 : Fin.append σ (rowOneEquiv q) 0 = σ 0 := rfl
  have h1 : Fin.append σ (rowOneEquiv q) 1 = σ 1 := rfl
  have h2 : Fin.append σ (rowOneEquiv q) 2 = σ 2 := rfl
  have h3 : Fin.append σ (rowOneEquiv q) 3 = pairEquiv.symm q := rfl
  rw [h0, h1, h2, h3]
  simp

private lemma sum_two_four_factors {ι κ : Type*} [Fintype ι] [Fintype κ]
    (a b : ℂ) (f : ι → ℂ) (g : κ → ℂ) :
    (∑ l, ∑ r, a * b * f l * g r) = a * b * (∑ l, f l) * ∑ r, g r := by
  simp_rw [← Finset.mul_sum, ← Finset.sum_mul]
  congr 1
  rw [Finset.mul_sum]

private lemma VFour_collapse_one (σ τ : Fin 3 → Fin 4)
    (t : Bool × Bool × Bool × Bool) :
    ∑ z : Fin 1 → Fin 4, VFour (Fin.append σ z) t * VFour (Fin.append τ z) t =
      (bellEmbedding ((pairEquiv (σ 0)).2, (pairEquiv (σ 1)).1) t.1 *
        bellEmbedding ((pairEquiv (τ 0)).2, (pairEquiv (τ 1)).1) t.1) *
      (bellEmbedding ((pairEquiv (σ 1)).2, (pairEquiv (σ 2)).1) t.2.1 *
        bellEmbedding ((pairEquiv (τ 1)).2, (pairEquiv (τ 2)).1) t.2.1) *
      (if (pairEquiv (σ 2)).2 = (pairEquiv (τ 2)).2 then 1 / 2 else 0) *
      (if (pairEquiv (σ 0)).1 = (pairEquiv (τ 0)).1 then 1 / 2 else 0) := by
  rw [← rowOneEquiv.sum_comp, Fintype.sum_prod_type]
  simp_rw [VFour_append_one]
  simp_rw [show ∀ (l r : Fin 2),
      (bellEmbedding ((pairEquiv (σ 0)).2, (pairEquiv (σ 1)).1) t.1 *
        (bellEmbedding ((pairEquiv (σ 1)).2, (pairEquiv (σ 2)).1) t.2.1 *
          (bellEmbedding ((pairEquiv (σ 2)).2, l) t.2.2.1 *
            bellEmbedding (r, (pairEquiv (σ 0)).1) t.2.2.2))) *
      (bellEmbedding ((pairEquiv (τ 0)).2, (pairEquiv (τ 1)).1) t.1 *
        (bellEmbedding ((pairEquiv (τ 1)).2, (pairEquiv (τ 2)).1) t.2.1 *
          (bellEmbedding ((pairEquiv (τ 2)).2, l) t.2.2.1 *
            bellEmbedding (r, (pairEquiv (τ 0)).1) t.2.2.2))) =
      (bellEmbedding ((pairEquiv (σ 0)).2, (pairEquiv (σ 1)).1) t.1 *
        bellEmbedding ((pairEquiv (τ 0)).2, (pairEquiv (τ 1)).1) t.1) *
      (bellEmbedding ((pairEquiv (σ 1)).2, (pairEquiv (σ 2)).1) t.2.1 *
        bellEmbedding ((pairEquiv (τ 1)).2, (pairEquiv (τ 2)).1) t.2.1) *
      (bellEmbedding ((pairEquiv (σ 2)).2, l) t.2.2.1 *
        bellEmbedding ((pairEquiv (τ 2)).2, l) t.2.2.1) *
      (bellEmbedding (r, (pairEquiv (σ 0)).1) t.2.2.2 *
        bellEmbedding (r, (pairEquiv (τ 0)).1) t.2.2.2) by intros; ring]
  rw [sum_two_four_factors]
  rw [bellEmbedding_partial_right, bellEmbedding_partial_left]

private def collapseThreeEntry (σ τ : Fin 3 → Fin 4)
    (t : Bool × Bool × Bool × Bool) : ℂ :=
  (bellEmbedding ((pairEquiv (σ 0)).2, (pairEquiv (σ 1)).1) t.1 *
    bellEmbedding ((pairEquiv (τ 0)).2, (pairEquiv (τ 1)).1) t.1) *
  (bellEmbedding ((pairEquiv (σ 1)).2, (pairEquiv (σ 2)).1) t.2.1 *
    bellEmbedding ((pairEquiv (τ 1)).2, (pairEquiv (τ 2)).1) t.2.1) *
  (if (pairEquiv (σ 2)).2 = (pairEquiv (τ 2)).2 then 1 / 2 else 0) *
  (if (pairEquiv (σ 0)).1 = (pairEquiv (τ 0)).1 then 1 / 2 else 0)

private lemma weighted_collapse_one {n : ℕ} {β : Type*}
    (V : Matrix (Fin (n + 1) → Fin 4) β ℂ) (w : β → ℂ)
    (entry : (Fin n → Fin 4) → (Fin n → Fin 4) → β → ℂ)
    (hcollapse : ∀ σ τ t,
      ∑ z : Fin 1 → Fin 4, V (Fin.append σ z) t * V (Fin.append τ z) t = entry σ τ t)
    (σ τ : Fin n → Fin 4) (t : β) :
    (∑ z : Fin 1 → Fin 4, w t * V (Fin.append σ z) t * V (Fin.append τ z) t) =
      w t * entry σ τ t := by
  simpa only [Finset.mul_sum, mul_assoc] using congrArg (w t * ·) (hcollapse σ τ t)

private lemma bitEmbedding_norm (b : Bool) :
    ∑ i : Fin 2, bitEmbedding i b * bitEmbedding i b = 1 := by
  rcases b <;> norm_num [bitEmbedding, Fin.sum_univ_two, finTwoEquiv]

private lemma VThree_append_one (σ : Fin 2 → Fin 4) (q : Fin 2 × Fin 2)
    (x : Bool × Bool × Bool × Bool) :
    VThree (Fin.append σ (rowOneEquiv q)) x =
      bitEmbedding (pairEquiv (σ 0)).1 x.1 *
        (bellEmbedding ((pairEquiv (σ 0)).2, (pairEquiv (σ 1)).1) x.2.1 *
          (bellEmbedding ((pairEquiv (σ 1)).2, q.1) x.2.2.1 *
            bitEmbedding q.2 x.2.2.2)) := by
  rw [VThree_apply]
  have h0 : Fin.append σ (rowOneEquiv q) 0 = σ 0 := rfl
  have h1 : Fin.append σ (rowOneEquiv q) 1 = σ 1 := rfl
  have h2 : Fin.append σ (rowOneEquiv q) 2 = pairEquiv.symm q := rfl
  rw [h0, h1, h2]
  simp

private lemma VThree_collapse_one (σ τ : Fin 2 → Fin 4)
    (x : Bool × Bool × Bool × Bool) :
    ∑ z : Fin 1 → Fin 4, VThree (Fin.append σ z) x * VThree (Fin.append τ z) x =
      (bitEmbedding (pairEquiv (σ 0)).1 x.1 * bitEmbedding (pairEquiv (τ 0)).1 x.1) *
      (bellEmbedding ((pairEquiv (σ 0)).2, (pairEquiv (σ 1)).1) x.2.1 *
        bellEmbedding ((pairEquiv (τ 0)).2, (pairEquiv (τ 1)).1) x.2.1) *
      (if (pairEquiv (σ 1)).2 = (pairEquiv (τ 1)).2 then 1 / 2 else 0) := by
  rw [← rowOneEquiv.sum_comp, Fintype.sum_prod_type]
  simp_rw [VThree_append_one]
  simp_rw [show ∀ (l r : Fin 2),
      (bitEmbedding (pairEquiv (σ 0)).1 x.1 *
        (bellEmbedding ((pairEquiv (σ 0)).2, (pairEquiv (σ 1)).1) x.2.1 *
          (bellEmbedding ((pairEquiv (σ 1)).2, l) x.2.2.1 * bitEmbedding r x.2.2.2))) *
      (bitEmbedding (pairEquiv (τ 0)).1 x.1 *
        (bellEmbedding ((pairEquiv (τ 0)).2, (pairEquiv (τ 1)).1) x.2.1 *
          (bellEmbedding ((pairEquiv (τ 1)).2, l) x.2.2.1 * bitEmbedding r x.2.2.2))) =
      (bitEmbedding (pairEquiv (σ 0)).1 x.1 * bitEmbedding (pairEquiv (τ 0)).1 x.1) *
      (bellEmbedding ((pairEquiv (σ 0)).2, (pairEquiv (σ 1)).1) x.2.1 *
        bellEmbedding ((pairEquiv (τ 0)).2, (pairEquiv (τ 1)).1) x.2.1) *
      (bellEmbedding ((pairEquiv (σ 1)).2, l) x.2.2.1 *
        bellEmbedding ((pairEquiv (τ 1)).2, l) x.2.2.1) *
      (bitEmbedding r x.2.2.2 * bitEmbedding r x.2.2.2) by intros; ring]
  rw [sum_two_four_factors, bellEmbedding_partial_right, bitEmbedding_norm]
  ring

private lemma VTwo_append_one (σ : Fin 1 → Fin 4) (q : Fin 2 × Fin 2)
    (x : Bool × Bool × Bool) :
    VTwo (Fin.append σ (rowOneEquiv q)) x =
      bitEmbedding (pairEquiv (σ 0)).1 x.1 *
        (bellEmbedding ((pairEquiv (σ 0)).2, q.1) x.2.1 * bitEmbedding q.2 x.2.2) := by
  rw [VTwo_apply]
  have h0 : Fin.append σ (rowOneEquiv q) 0 = σ 0 := rfl
  have h1 : Fin.append σ (rowOneEquiv q) 1 = pairEquiv.symm q := rfl
  rw [h0, h1]
  simp

private lemma VTwo_collapse_one (σ τ : Fin 1 → Fin 4) (x : Bool × Bool × Bool) :
    ∑ z : Fin 1 → Fin 4, VTwo (Fin.append σ z) x * VTwo (Fin.append τ z) x =
      (bitEmbedding (pairEquiv (σ 0)).1 x.1 * bitEmbedding (pairEquiv (τ 0)).1 x.1) *
      (if (pairEquiv (σ 0)).2 = (pairEquiv (τ 0)).2 then 1 / 2 else 0) := by
  rw [← rowOneEquiv.sum_comp, Fintype.sum_prod_type]
  simp_rw [VTwo_append_one]
  simp_rw [show ∀ (l r : Fin 2),
      (bitEmbedding (pairEquiv (σ 0)).1 x.1 *
        (bellEmbedding ((pairEquiv (σ 0)).2, l) x.2.1 * bitEmbedding r x.2.2)) *
      (bitEmbedding (pairEquiv (τ 0)).1 x.1 *
        (bellEmbedding ((pairEquiv (τ 0)).2, l) x.2.1 * bitEmbedding r x.2.2)) =
      (bitEmbedding (pairEquiv (σ 0)).1 x.1 * bitEmbedding (pairEquiv (τ 0)).1 x.1) *
      (bellEmbedding ((pairEquiv (σ 0)).2, l) x.2.1 *
        bellEmbedding ((pairEquiv (τ 0)).2, l) x.2.1) *
      (bitEmbedding r x.2.2 * bitEmbedding r x.2.2) by intros; ring]
  simp_rw [← Finset.mul_sum, bitEmbedding_norm, mul_one]
  trans (bitEmbedding (pairEquiv (σ 0)).1 x.1 *
      bitEmbedding (pairEquiv (τ 0)).1 x.1) *
    ∑ l, bellEmbedding ((pairEquiv (σ 0)).2, l) x.2.1 *
      bellEmbedding ((pairEquiv (τ 0)).2, l) x.2.1
  · rw [Finset.mul_sum]
  · rw [bellEmbedding_partial_right]

private def collapseTwoEntry (σ τ : Fin 2 → Fin 4)
    (x : Bool × Bool × Bool × Bool) : ℂ :=
  (bitEmbedding (pairEquiv (σ 0)).1 x.1 * bitEmbedding (pairEquiv (τ 0)).1 x.1) *
  (bellEmbedding ((pairEquiv (σ 0)).2, (pairEquiv (σ 1)).1) x.2.1 *
    bellEmbedding ((pairEquiv (τ 0)).2, (pairEquiv (τ 1)).1) x.2.1) *
  (if (pairEquiv (σ 1)).2 = (pairEquiv (τ 1)).2 then 1 / 2 else 0)

private def collapseOneEntry (σ τ : Fin 1 → Fin 4) (x : Bool × Bool × Bool) : ℂ :=
  (bitEmbedding (pairEquiv (σ 0)).1 x.1 * bitEmbedding (pairEquiv (τ 0)).1 x.1) *
  (if (pairEquiv (σ 0)).2 = (pairEquiv (τ 0)).2 then 1 / 2 else 0)

private theorem reduced_three_eq_bellDiagonal :
    reducedBlockState M 4 3 (by omega) = singleKrausMap VThree
      (Matrix.diagonal fun x =>
        (CPSVExample410CorrelatedFlip.windowWeightThree x : ℂ)) := by
  ext σ τ
  have hcollapse := collapse_last M (N := 4) (a := 3) (b := 0) (c := 1)
    (by omega) σ τ
  change (∑ z : Fin 1 → Fin 4,
      reducedBlockState M 4 4 (by omega) (Fin.append σ z) (Fin.append τ z)) = _
    at hcollapse
  rw [← hcollapse]
  simp_rw [reduced_four_eq_bellDiagonal]
  simp only [singleKrausMap_diagonal_apply_of_real VFour _ star_VFour]
  rw [singleKrausMap_diagonal_apply_of_real VThree _ star_VThree]
  rw [Finset.sum_comm]
  trans ∑ t, (CPSVExample410CorrelatedFlip.bondWeight t : ℂ) *
    collapseThreeEntry σ τ t
  · apply Finset.sum_congr rfl
    intro t _
    exact weighted_collapse_one VFour
      (fun t => (CPSVExample410CorrelatedFlip.bondWeight t : ℂ))
      collapseThreeEntry VFour_collapse_one σ τ t
  · simp_rw [CPSVExample410CorrelatedFlip.windowWeightThree,
      CPSVExample410CorrelatedFlip.twoBondWeight_eq_marginal]
    rcases hσl : finTwoEquiv (pairEquiv (σ 0)).1 with _ | _ <;>
      rcases hτl : finTwoEquiv (pairEquiv (τ 0)).1 with _ | _ <;>
      rcases hσr : finTwoEquiv (pairEquiv (σ 2)).2 with _ | _ <;>
      rcases hτr : finTwoEquiv (pairEquiv (τ 2)).2 with _ | _ <;>
      simp [collapseThreeEntry, VThree_apply, bitEmbedding,
        ← finTwoEquiv.apply_eq_iff_eq, hσl, hτl, hσr, hτr,
        Fintype.sum_prod_type] <;> ring

private theorem reduced_two_eq_bellDiagonal :
    reducedBlockState M 4 2 (by omega) = singleKrausMap VTwo
      (Matrix.diagonal fun x =>
        (CPSVExample410CorrelatedFlip.windowWeightTwo x : ℂ)) := by
  ext σ τ
  have hcollapse := collapse_last M (N := 4) (a := 2) (b := 0) (c := 1)
    (by omega) σ τ
  change (∑ z : Fin 1 → Fin 4,
      reducedBlockState M 4 3 (by omega) (Fin.append σ z) (Fin.append τ z)) = _
    at hcollapse
  rw [← hcollapse]
  simp_rw [reduced_three_eq_bellDiagonal]
  simp only [singleKrausMap_diagonal_apply_of_real VThree _ star_VThree]
  rw [singleKrausMap_diagonal_apply_of_real VTwo _ star_VTwo, Finset.sum_comm]
  trans ∑ x, (CPSVExample410CorrelatedFlip.windowWeightThree x : ℂ) *
    collapseTwoEntry σ τ x
  · apply Finset.sum_congr rfl
    intro x _
    exact weighted_collapse_one VThree
      (fun x => (CPSVExample410CorrelatedFlip.windowWeightThree x : ℂ))
      collapseTwoEntry VThree_collapse_one σ τ x
  · simp_rw [CPSVExample410CorrelatedFlip.windowWeightThree,
      CPSVExample410CorrelatedFlip.windowWeightTwo,
      CPSVExample410CorrelatedFlip.twoBondWeight_eq_marginal,
      CPSVExample410CorrelatedFlip.oneBondWeight_eq_marginal]
    rcases hσl : finTwoEquiv (pairEquiv (σ 0)).1 with _ | _ <;>
      rcases hτl : finTwoEquiv (pairEquiv (τ 0)).1 with _ | _ <;>
      rcases hσr : finTwoEquiv (pairEquiv (σ 1)).2 with _ | _ <;>
      rcases hτr : finTwoEquiv (pairEquiv (τ 1)).2 with _ | _ <;>
      simp [collapseTwoEntry, VTwo_apply, bitEmbedding,
        ← finTwoEquiv.apply_eq_iff_eq, hσl, hτl, hσr, hτr,
        Fintype.sum_prod_type] <;> ring

private theorem reduced_one_eq_bellDiagonal :
    reducedBlockState M 4 1 (by omega) = singleKrausMap VOne
      (Matrix.diagonal fun x =>
        (CPSVExample410CorrelatedFlip.windowWeightOne x : ℂ)) := by
  ext σ τ
  have hcollapse := collapse_last M (N := 4) (a := 1) (b := 0) (c := 1)
    (by omega) σ τ
  change (∑ z : Fin 1 → Fin 4,
      reducedBlockState M 4 2 (by omega) (Fin.append σ z) (Fin.append τ z)) = _
    at hcollapse
  rw [← hcollapse]
  simp_rw [reduced_two_eq_bellDiagonal]
  simp only [singleKrausMap_diagonal_apply_of_real VTwo _ star_VTwo]
  rw [singleKrausMap_diagonal_apply_of_real VOne _ star_VOne, Finset.sum_comm]
  trans ∑ x, (CPSVExample410CorrelatedFlip.windowWeightTwo x : ℂ) *
    collapseOneEntry σ τ x
  · apply Finset.sum_congr rfl
    intro x _
    exact weighted_collapse_one VTwo
      (fun x => (CPSVExample410CorrelatedFlip.windowWeightTwo x : ℂ))
      collapseOneEntry VTwo_collapse_one σ τ x
  · rcases hσl : finTwoEquiv (pairEquiv (σ 0)).1 with _ | _ <;>
      rcases hτl : finTwoEquiv (pairEquiv (τ 0)).1 with _ | _ <;>
      rcases hσr : finTwoEquiv (pairEquiv (σ 0)).2 with _ | _ <;>
      rcases hτr : finTwoEquiv (pairEquiv (τ 0)).2 with _ | _ <;>
      simp [collapseOneEntry, VOne_apply, bitEmbedding,
        ← finTwoEquiv.apply_eq_iff_eq, hσl, hτl, hσr, hτr,
        CPSVExample410CorrelatedFlip.windowWeightTwo,
        CPSVExample410CorrelatedFlip.windowWeightOne,
        CPSVExample410CorrelatedFlip.oneBondWeight_false,
        CPSVExample410CorrelatedFlip.oneBondWeight_true,
        Fintype.sum_prod_type] <;> ring

/-- The normalized one-site state has four characteristic-polynomial roots equal to $1/4$.
This spectrum is a project-derived consequence of the corrected $p=1/4$ reading of CPSV16
Example 4.10. -/
theorem charpoly_roots_one :
    (reducedBlockState M 4 1 (by omega)).charpoly.roots = 4 • {(1 / 4 : ℂ)} := by
  rw [reduced_one_eq_bellDiagonal,
    Matrix.singleKrausMap_charpoly_roots_eq_zero_add_of_isometry VOne VOne_isometry]
  simp only [Fintype.card_fun, Fintype.card_fin, Fintype.card_prod, Fintype.card_bool,
    Nat.reducePow]
  rw [Matrix.charpoly_roots_diagonal_ofReal]
  have huniv : (Finset.univ.val : Multiset (Bool × Bool)) =
      {(false, false), (false, true), (true, false), (true, true)} := by decide
  rw [huniv]
  norm_num [CPSVExample410CorrelatedFlip.windowWeightOne]
  simp only [← Multiset.singleton_add]
  abel

/-- The normalized two-site state has eight zero roots, four roots $5/32$, and four roots
$3/32$. This spectrum is a project-derived consequence of the corrected $p=1/4$ reading of
CPSV16 Example 4.10. -/
theorem charpoly_roots_two :
    (reducedBlockState M 4 2 (by omega)).charpoly.roots =
      8 • {(0 : ℂ)} + 4 • {(5 / 32 : ℂ)} + 4 • {(3 / 32 : ℂ)} := by
  rw [reduced_two_eq_bellDiagonal,
    Matrix.singleKrausMap_charpoly_roots_eq_zero_add_of_isometry VTwo VTwo_isometry]
  simp only [Fintype.card_fun, Fintype.card_fin, Fintype.card_prod, Fintype.card_bool,
    Nat.reducePow]
  rw [Matrix.charpoly_roots_diagonal_ofReal]
  have huniv : (Finset.univ.val : Multiset (Bool × Bool × Bool)) =
      {(false, false, false), (false, false, true),
        (false, true, false), (false, true, true),
        (true, false, false), (true, false, true),
        (true, true, false), (true, true, true)} := by decide
  rw [huniv]
  norm_num [CPSVExample410CorrelatedFlip.windowWeightTwo,
    CPSVExample410CorrelatedFlip.oneBondWeight_false,
    CPSVExample410CorrelatedFlip.oneBondWeight_true]
  simp only [← Multiset.singleton_add]
  abel

/-- The normalized three-site state has 48 zero roots, four roots $7/64$, and twelve roots
$3/64$. This spectrum is a project-derived consequence of the corrected $p=1/4$ reading of
CPSV16 Example 4.10. -/
theorem charpoly_roots_three :
    (reducedBlockState M 4 3 (by omega)).charpoly.roots =
      48 • {(0 : ℂ)} + 4 • {(7 / 64 : ℂ)} + 12 • {(3 / 64 : ℂ)} := by
  rw [reduced_three_eq_bellDiagonal,
    Matrix.singleKrausMap_charpoly_roots_eq_zero_add_of_isometry VThree VThree_isometry]
  simp only [Fintype.card_fun, Fintype.card_fin, Fintype.card_prod, Fintype.card_bool,
    Nat.reducePow]
  rw [Matrix.charpoly_roots_diagonal_ofReal]
  have huniv : (Finset.univ.val : Multiset (Bool × Bool × Bool × Bool)) =
      {(false, false, false, false), (false, false, false, true),
        (false, false, true, false), (false, false, true, true),
        (false, true, false, false), (false, true, false, true),
        (false, true, true, false), (false, true, true, true),
        (true, false, false, false), (true, false, false, true),
        (true, false, true, false), (true, false, true, true),
        (true, true, false, false), (true, true, false, true),
        (true, true, true, false), (true, true, true, true)} := by decide
  rw [huniv]
  norm_num [CPSVExample410CorrelatedFlip.windowWeightThree,
    CPSVExample410CorrelatedFlip.twoBondWeight_false_false,
    CPSVExample410CorrelatedFlip.twoBondWeight_of_pair_ne_false_false]
  simp only [← Multiset.singleton_add]
  abel

set_option maxRecDepth 10000 in
/-- The normalized four-site state has nonzero eigenvalues $41/128$ once, $15/128$ four times,
and $9/128$ three times. Its remaining 248 characteristic-polynomial roots are zero. CPSV16
Example 4.10, lines 897--905. -/
theorem charpoly_roots_four :
    (reducedBlockState M 4 4 (by omega)).charpoly.roots =
      248 • {(0 : ℂ)} + {(41 / 128 : ℂ)} + 4 • {(15 / 128 : ℂ)} +
        3 • {(9 / 128 : ℂ)} := by
  rw [reduced_four_eq_bellDiagonal,
    Matrix.singleKrausMap_charpoly_roots_eq_zero_add_of_isometry VFour VFour_isometry]
  simp only [Fintype.card_fun, Fintype.card_fin, Fintype.card_prod, Fintype.card_bool]
  rw [Matrix.charpoly_roots_diagonal_ofReal]
  rw [CPSVExample410CorrelatedFlip.bondWeight_eq_bondWeightValue]
  have huniv :
      (Finset.univ.val : Multiset (Bool × Bool × Bool × Bool)) =
        {(true, false, false, false), (false, true, false, false),
          (false, false, true, false), (false, false, false, true),
          (true, true, true, false), (true, true, false, true),
          (true, false, true, true), (false, true, true, true),
          (false, false, false, false),
          (true, true, false, false), (false, true, true, false),
          (false, false, true, true), (true, false, false, true),
          (true, false, true, false), (false, true, false, true),
          (true, true, true, true)} := by decide
  rw [huniv]
  norm_num [CPSVExample410CorrelatedFlip.bondWeightValue]
  simp only [← Multiset.singleton_add]
  abel

end MPOTensor.CPSVExample410Spectrum
