/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Analysis.EntropyDecomposition
import TNLean.MPS.MPDO.CPSVExample410CorrelatedFlip
import TNLean.MPS.MPDO.CPSVExample410Operator
import TNLean.MPS.MPDO.SourceZCLMarginal

/-!
# Four-site spectrum of corrected CPSV16 Example 4.10

The corrected tensor is a mixture of products of Bell states. A flip configuration on the four
spins determines the cyclic difference pattern on the four bonds. The corresponding sixteen
Bell-network vectors form an orthonormal family, while the eight odd-parity patterns have zero
weight. This gives the full four-site spectrum at flip probability one quarter.

**Local fix (left-right correlated flip):** CPSV16 lines 901--902 repeat the left-qubit label.
This module uses the left-right flip defined in `CPSVExample410Operator`, whose bond-pattern
weights agree with the entropy values printed at source line 904. See
`docs/paper-gaps/cpsv16_examples_4_10_4_11_entropy.tex`.

## Main result

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
private lemma kron_isometry {a b c d : Type*} [Fintype a] [Fintype b]
    [Fintype c] [Fintype d] [DecidableEq b] [DecidableEq d]
    (A : Matrix a b ℂ) (B : Matrix c d ℂ) (hA : Aᴴ * A = 1) (hB : Bᴴ * B = 1) :
    (A ⊗ₖ B)ᴴ * (A ⊗ₖ B) = 1 := by
  rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul, hA, hB,
    Matrix.one_kronecker_one]

set_option linter.unusedFintypeInType false in
private lemma reindex_isometry {a b a' b' : Type*} [Fintype a] [Fintype b]
    [Fintype a'] [Fintype b'] [DecidableEq b] [DecidableEq b']
    (A : Matrix a b ℂ) (ha : a ≃ a') (hb : b ≃ b') (hA : Aᴴ * A = 1) :
    (Matrix.reindex ha hb A)ᴴ * Matrix.reindex ha hb A = 1 := by
  rw [Matrix.conjTranspose_reindex]
  change Aᴴ.submatrix hb.symm ha.symm * A.submatrix ha.symm hb.symm = 1
  rw [Matrix.submatrix_mul_equiv, hA, Matrix.submatrix_one_equiv]

private lemma rawFour_isometry : rawFourᴴ * rawFour = 1 := by
  apply kron_isometry bellEmbedding _ bellEmbedding_isometry
  apply kron_isometry bellEmbedding _ bellEmbedding_isometry
  exact kron_isometry bellEmbedding bellEmbedding bellEmbedding_isometry
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
