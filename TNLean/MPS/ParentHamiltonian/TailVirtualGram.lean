/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.GramConvergence
import TNLean.MPS.ParentHamiltonian.SpectatorBoundaryGram

/-!
# Tail virtual Gram operator

This file identifies the adjoint-self composition of the tail virtual map with right
multiplication by an iterated transfer-map value. It also bounds the fourth power of the
operator norm of the tail virtual map by the squared entrywise mass of that value.

## Main results

* `MPSTensor.tailVirtualMapES_adjoint_comp_self_apply`
* `MPSTensor.tailVirtualMapES_norm_four_pow_le_transferMap_pow_one_entry_norm_sq`
* `MPSTensor.IsPrimitiveMPS.tailVirtualMapES_norm_uniform`
-/

open scoped Matrix

namespace MPSTensor

variable {d D : ℕ}

section FrobeniusCoordinate

open scoped Matrix.Norms.Frobenius

/-! ### Exact adjoint-self formula with matrix input -/

/-- The adjoint-self composition of the tail virtual map acts by right multiplication by the
iterated transfer map applied to the identity. -/
theorem tailVirtualMapES_adjoint_comp_self_apply (A : MPSTensor d D) (K : ℕ)
    (X : Matrix (Fin D) (Fin D) ℂ) :
    (tailVirtualMapES A K).adjoint (tailVirtualMapES A K
      (Matrix.frobeniusEquivEuclidean (Fin D) (Fin D) X)) =
    Matrix.frobeniusEquivEuclidean (Fin D) (Fin D) (X * ((transferMap A) ^ K) 1) := by
  rw [tailVirtualMapES_adjoint_apply]
  simp_rw [boundaryFamilyEquiv_tailVirtualMapES_apply,
    (Matrix.frobeniusEquivEuclidean (Fin D) (Fin D)).symm_apply_apply]
  have hsum : (∑ u : Cfg d K, evalWord A (List.ofFn u) * (evalWord A (List.ofFn u))ᴴ) =
      ((transferMap (d := d) (D := D) A) ^ K) 1 := by
    symm
    simpa only [Matrix.mul_one] using transferMap_pow_apply' A K 1
  simpa only [Matrix.mul_assoc, Matrix.mul_sum] using
    congrArg (fun M => Matrix.frobeniusEquivEuclidean (Fin D) (Fin D) (X * M)) hsum

/-! ### Frobenius-isometric matrix product bound -/

/-- The squared norm of a Frobenius-vectorized matrix is the sum of its squared entry
norms. -/
private lemma frobeniusEquivEuclidean_norm_sq (X : Matrix (Fin D) (Fin D) ℂ) :
    ‖Matrix.frobeniusEquivEuclidean (Fin D) (Fin D) X‖ ^ 2 =
      ∑ i : Fin D, ∑ j : Fin D, ‖X i j‖ ^ 2 := by
  rw [LinearIsometryEquiv.norm_map, Matrix.frobenius_norm_def, ← Real.sqrt_eq_rpow,
    Real.sq_sqrt (by positivity)]
  simp only [Real.rpow_two]

/-- The squared Frobenius-vector norm of a matrix product is at most the product of the
squared Frobenius-vector norms. -/
private lemma frobenius_vec_mul_norm_sq_le (X M : Matrix (Fin D) (Fin D) ℂ) :
    ‖(Matrix.frobeniusEquivEuclidean (Fin D) (Fin D)) (X * M)‖ ^ 2 ≤
    ‖(Matrix.frobeniusEquivEuclidean (Fin D) (Fin D)) X‖ ^ 2 *
    ‖(Matrix.frobeniusEquivEuclidean (Fin D) (Fin D)) M‖ ^ 2 := by
  simp only [LinearIsometryEquiv.norm_map]
  nlinarith [Matrix.frobenius_norm_mul X M, norm_nonneg X, norm_nonneg M,
    norm_nonneg (X * M)]

/-! ### Fourth-power operator-norm bound by entrywise mass -/

/-- The fourth power of the tail virtual map norm is bounded by the squared entrywise mass
of the iterated transfer map applied to the identity. -/
theorem tailVirtualMapES_norm_four_pow_le_transferMap_pow_one_entry_norm_sq
    (A : MPSTensor d D) (K : ℕ) :
    ‖tailVirtualMapES A K‖ ^ 4 ≤
      ∑ p : (Fin D × Fin D),
        ‖(((transferMap (d := d) (D := D) A) ^ K) 1) p.1 p.2‖ ^ 2 := by
  let M := ((transferMap (d := d) (D := D) A) ^ K) 1
  let U := Matrix.frobeniusEquivEuclidean (Fin D) (Fin D)
  have hnorm_adj_sq : ‖(tailVirtualMapES A K).adjoint ∘L (tailVirtualMapES A K)‖ =
      ‖tailVirtualMapES A K‖ * ‖tailVirtualMapES A K‖ :=
    ContinuousLinearMap.norm_adjoint_comp_self (tailVirtualMapES A K)
  have hsq : ‖tailVirtualMapES A K‖ ^ 2 = ‖(tailVirtualMapES A K).adjoint ∘L
      (tailVirtualMapES A K)‖ := by
    simpa only [pow_two] using hnorm_adj_sq.symm
  let S := (tailVirtualMapES A K).adjoint ∘L (tailVirtualMapES A K)
  have hS_bound (x : EuclideanSpace ℂ (Fin D × Fin D)) : ‖S x‖ ≤ ‖x‖ * ‖U M‖ := by
    let X := U.symm x
    have hx : x = U X := (U.apply_symm_apply x).symm
    have hSx : S (U X) = U (X * M) := by
      dsimp [S]
      simpa [M, U, ContinuousLinearMap.coe_comp] using
        tailVirtualMapES_adjoint_comp_self_apply A K X
    rw [hx, hSx]
    have h_sq : ‖U (X * M)‖ ^ 2 ≤ ‖U X‖ ^ 2 * ‖U M‖ ^ 2 := by
      simpa [U] using frobenius_vec_mul_norm_sq_le X M
    rw [← sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _)), mul_pow]
    exact h_sq
  have hS_opNorm : ‖S‖ ≤ ‖U M‖ :=
    ContinuousLinearMap.opNorm_le_bound S (norm_nonneg _) fun x => by
      simpa [mul_comm] using hS_bound x
  have hU_sq : ‖U M‖ ^ 2 = ∑ i : Fin D, ∑ j : Fin D, ‖M i j‖ ^ 2 := by
    simpa only [U] using frobeniusEquivEuclidean_norm_sq M
  have hRHS : (∑ p : (Fin D × Fin D), ‖M p.1 p.2‖ ^ 2) = ‖U M‖ ^ 2 := by
    rw [hU_sq, Fintype.sum_prod_type]
  calc
    ‖tailVirtualMapES A K‖ ^ 4 = (‖tailVirtualMapES A K‖ ^ 2) ^ 2 := by ring
    _ = ‖S‖ ^ 2 := by rw [hsq]
    _ ≤ ‖U M‖ ^ 2 := by nlinarith [hS_opNorm, norm_nonneg (U M)]
    _ = ∑ p : (Fin D × Fin D), ‖M p.1 p.2‖ ^ 2 := by rw [hRHS]

end FrobeniusCoordinate

section UniformBound

open scoped Matrix.Norms.L2Operator

/-! ### Uniform bound for primitive tensors -/

/-- The fourth powers of the tail virtual-map norms are uniformly bounded for a primitive
MPS tensor. Positive transfer-map powers split into the fixed-point projection and a
geometrically bounded complementary power. The entrywise mass from the Gram estimate is
then controlled by the L² operator norm with an explicit bond-dimension factor. No
positive-definiteness assumption on the fixed point is needed. -/
theorem IsPrimitiveMPS.tailVirtualMapES_norm_four_pow_uniform
    [NeZero D] {A : MPSTensor d D} {ρ : Matrix (Fin D) (Fin D) ℂ}
    (hP : IsPrimitiveMPS A ρ) :
    ∃ C : ℝ, 0 < C ∧ ∀ K : ℕ, ‖tailVirtualMapES A K‖ ^ 4 ≤ C := by
  letI : NormedRing (Matrix (Fin D) (Fin D) ℂ) := Matrix.instL2OpNormedRing
  let E := transferMap (d := d) (D := D) A
  have htr : Matrix.trace ρ ≠ 0 := by
    intro h
    exact hP.fixedPoint_ne_zero
      ((Matrix.PosSemidef.trace_eq_zero_iff hP.fixedPoint_psd).1 h)
  let P := fixedPointProj (D := D) ρ htr
  let N := E - P
  let T := (Module.End.toContinuousLinearMap (Matrix (Fin D) (Fin D) ℂ)) N
  have hTP : IsTracePreservingMap E := by
    intro X
    exact trace_transferMap A X hP.norm
  have hgap : spectralRadius ℂ T < 1 := by
    dsimp only [T, N, E, P]
    convert hP.complementary_transfer_map_gap using 1
    congr 2
  obtain ⟨C, r, hC, hr_pos, hr_lt_one, hgeom⟩ :=
    geometric_bound_of_spectralRadius_lt_one T hgap
  let B := ‖P 1‖ + C * ‖(1 : Matrix (Fin D) (Fin D) ℂ)‖
  let Q := (D : ℝ) * (‖(1 : Matrix (Fin D) (Fin D) ℂ)‖ ^ 2 + B ^ 2) + 1
  have hD : 0 ≤ (D : ℝ) := Nat.cast_nonneg D
  have hQ : 0 < Q := by
    dsimp [Q]
    positivity
  refine ⟨Q, hQ, ?_⟩
  intro K
  let M := (E ^ K) 1
  have hentry :
      (∑ p : Fin D × Fin D, ‖M p.1 p.2‖ ^ 2) ≤ (D : ℝ) * ‖M‖ ^ 2 := by
    simpa only [Fintype.card_fin] using Matrix.sum_entry_norm_sq_le_card_mul_norm_sq M
  refine (tailVirtualMapES_norm_four_pow_le_transferMap_pow_one_entry_norm_sq A K).trans ?_
  change (∑ p : Fin D × Fin D, ‖M p.1 p.2‖ ^ 2) ≤ Q
  refine hentry.trans ?_
  by_cases hK : K = 0
  · subst K
    simp only [M, E, pow_zero, Module.End.one_apply]
    dsimp [Q]
    exact (mul_le_mul_of_nonneg_left
      (le_add_of_nonneg_right (sq_nonneg B)) hD).trans
      (le_add_of_nonneg_right zero_le_one)
  · have hK1 : 1 ≤ K := Nat.one_le_iff_ne_zero.mpr hK
    have hpow : E ^ K = P + N ^ K := by
      simpa [N, E, P] using
        pow_eq_fixedPointProj_add_compl_pow (E := E) (ρ := ρ) htr hTP
          hP.fixedPoint_is_fixed hK1
    have hN_apply : ‖(N ^ K) 1‖ ≤ C * ‖(1 : Matrix (Fin D) (Fin D) ℂ)‖ := by
      calc
        ‖(N ^ K) 1‖ = ‖((Module.End.toContinuousLinearMap
            (Matrix (Fin D) (Fin D) ℂ)) (N ^ K)) 1‖ := rfl
        _ ≤ ‖(Module.End.toContinuousLinearMap (Matrix (Fin D) (Fin D) ℂ))
            (N ^ K)‖ * ‖(1 : Matrix (Fin D) (Fin D) ℂ)‖ :=
          ((Module.End.toContinuousLinearMap (Matrix (Fin D) (Fin D) ℂ))
            (N ^ K)).le_opNorm (1 : Matrix (Fin D) (Fin D) ℂ)
        _ = ‖T ^ K‖ * ‖(1 : Matrix (Fin D) (Fin D) ℂ)‖ := by
          rw [map_pow (Module.End.toContinuousLinearMap
            (Matrix (Fin D) (Fin D) ℂ)) N K]
        _ ≤ (C * r ^ K) * ‖(1 : Matrix (Fin D) (Fin D) ℂ)‖ := by
          gcongr
          exact hgeom K
        _ ≤ C * ‖(1 : Matrix (Fin D) (Fin D) ℂ)‖ := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_of_le_one_right hC.le
              (pow_le_one₀ (le_of_lt hr_pos) (le_of_lt hr_lt_one))) (norm_nonneg _)
    have hM : M = P 1 + (N ^ K) 1 := by
      have happ := congrArg
        (fun F : Module.End ℂ (Matrix (Fin D) (Fin D) ℂ) => F 1) hpow
      simpa only [M, LinearMap.add_apply] using happ
    have hB : 0 ≤ B := by
      dsimp [B]
      positivity
    have hM_norm : ‖M‖ ≤ B := by
      rw [hM]
      exact (norm_add_le _ _).trans (by
        simpa only [B] using add_le_add_right hN_apply ‖P 1‖)
    have hM_sq : ‖M‖ ^ 2 ≤ B ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) hB).2 hM_norm
    dsimp [Q]
    exact (mul_le_mul_of_nonneg_left
      (hM_sq.trans (le_add_of_nonneg_left (sq_nonneg ‖(1 : Matrix
        (Fin D) (Fin D) ℂ)‖))) hD).trans (le_add_of_nonneg_right zero_le_one)

/-- For a primitive MPS tensor, the tail virtual maps have a uniform operator-norm bound,
independent of the tail length. The proof preserves the fourth-power Gram normalization:
it first bounds the fourth powers uniformly and then chooses a strictly positive bound for
the norms themselves. No positive-definiteness assumption on the fixed point is required. -/
theorem IsPrimitiveMPS.tailVirtualMapES_norm_uniform
    [NeZero D] {A : MPSTensor d D} {ρ : Matrix (Fin D) (Fin D) ℂ}
    (hP : IsPrimitiveMPS A ρ) :
    ∃ C : ℝ, 0 < C ∧ ∀ K : ℕ, ‖tailVirtualMapES A K‖ ≤ C := by
  obtain ⟨Q, hQ, hbound⟩ := hP.tailVirtualMapES_norm_four_pow_uniform
  refine ⟨Q + 1, by positivity, ?_⟩
  intro K
  by_cases hnorm : ‖tailVirtualMapES A K‖ ≤ 1
  · exact hnorm.trans (by linarith)
  · exact (le_self_pow₀ (lt_of_not_ge hnorm).le (by norm_num : 4 ≠ 0)).trans
      ((hbound K).trans (by linarith))

end UniformBound


end MPSTensor
