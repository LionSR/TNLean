/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.UncleGroundSpace

/-!
# Two-domain-wall trial vectors and interior local cancellation

The source trial sums one R wall in a first interval and one L wall in a
second interval. All other sites carry the corresponding uniform blocks.
The rectangular wall sums below are the actual source sums, not ordinary
products of uncle matrices. A local pair wholly inside either moving-wall
interval belongs to the actual uncle local kernel, with arbitrary fixed
exterior contractions. This is the cancellation needed before estimating
the four interval-end terms in the variational energy.

Source: arXiv:1210.6613, equation phiN-def and Lemma lowenergystates,
lines 1196–1296. The source asymptotic argument additionally uses the
normalized standard form in lines 254–282 and 773–787. No norm growth,
energy asymptotic or gaplessness conclusion is asserted here.
-/

noncomputable section

open scoped Matrix BigOperators

namespace MPSTensor

variable {d a b : ℕ}

/-- The exact five-segment coefficient with one wall in each moving interval.
Source: arXiv:1210.6613, phiN-def, lines 1196–1224. -/
def uncleTwoWallCoefficient (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (L : Fin d → Matrix (Fin b) (Fin a) ℂ)
    (u v w x y : List (Fin d)) : ℂ :=
  Matrix.trace (Kraus.evalWord A u * uncleDomainWallWord A B R v *
    Kraus.evalWord B w * uncleDomainWallWord B A L x * Kraus.evalWord A y)

/-- Both wall positions are summed independently and occur exactly once.
Source: arXiv:1210.6613, phiN-def, lines 1196–1224. -/
theorem uncleTwoWallCoefficient_eq_sum (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (L : Fin d → Matrix (Fin b) (Fin a) ℂ) (u v w x y : List (Fin d)) :
    uncleTwoWallCoefficient A B R L u v w x y =
      ∑ i : Fin v.length, ∑ j : Fin x.length,
        Matrix.trace (Kraus.evalWord A u *
          (Kraus.evalWord A (v.take i) * R (v.get i) *
            Kraus.evalWord B (v.drop (i + 1))) * Kraus.evalWord B w *
          (Kraus.evalWord B (x.take j) * L (x.get j) *
            Kraus.evalWord A (x.drop (j + 1))) * Kraus.evalWord A y) := by
  rw [uncleTwoWallCoefficient, uncleDomainWallWord_eq_sum A B R v]
  simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.trace_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [uncleDomainWallWord_eq_sum B A L x]
  simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.trace_sum]

/-- The finite two-wall trial on five consecutive segments. The moving
interval lengths are r and s; no norm or nonvanishing is assumed.
Source: arXiv:1210.6613, phiN-def, lines 1196–1224. -/
def uncleTwoWallTrial (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (L : Fin d → Matrix (Fin b) (Fin a) ℂ) (p r q s t : ℕ) :
    NSiteSpace d (p + r + q + s + t) := fun σ ↦
  let z := List.ofFn σ
  uncleTwoWallCoefficient A B R L (z.take p) ((z.drop p).take r)
    ((z.drop (p + r)).take q) ((z.drop (p + r + q)).take s)
    (z.drop (p + r + q + s))

/-- The source trial on 6N+1 sites, with wall intervals N through 2N and
4N through 5N in zero-based coordinates. For N positive the five lengths
are N, N+1, 2N-1, N+1, N, giving exactly the source two separated windows.
Source: arXiv:1210.6613, phiN-def, lines 1196–1224. -/
def uncleTwoWallTrialSource (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (L : Fin d → Matrix (Fin b) (Fin a) ℂ) (N : ℕ) : NSiteSpace d (6 * N + 1) := fun σ ↦
  let z := List.ofFn σ
  uncleTwoWallCoefficient A B R L (z.take N) ((z.drop N).take (N + 1))
    ((z.drop (2 * N + 1)).take (2 * N - 1))
    ((z.drop (4 * N)).take (N + 1)) (z.drop (5 * N + 1))

/-- Arbitrary fixed exterior words and a linear virtual contraction preserve
membership of a varying local pair in the actual two-site boundary space.
This is the local cancellation step of arXiv:1210.6613, lines 1289–1296. -/
theorem uncleBoundaryWord_slice_mem
    (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (L : Fin d → Matrix (Fin b) (Fin a) ℂ)
    (f : Matrix (Fin (a + b)) (Fin (a + b)) ℂ →ₗ[ℂ] ℂ)
    (u v : List (Fin d)) :
    (fun σ : Fin 2 → Fin d ↦ f (uncleBoundaryWord A B R L (u ++ List.ofFn σ ++ v))) ∈
      uncleBoundarySpace A B R L 2 := by
  obtain ⟨X, hX⟩ := Matrix.exists_trace_representation
    (f.comp ((uncleBoundaryMulLeft (uncleBoundaryWord A B R L u)).comp
      (uncleBoundaryMulRight (uncleBoundaryWord A B R L v))))
  refine ⟨X, ?_⟩
  ext σ
  simpa only [uncleBoundaryMap_apply, LinearMap.comp_apply, uncleBoundaryMulLeft_apply,
    uncleBoundaryMulRight_apply, uncleBoundaryWord_append, uncleBoundaryMul_assoc,
    Matrix.trace_mul_comm] using (hX (uncleBoundaryWord A B R L (List.ofFn σ))).symm

private def uncleBoundaryBlockTrace {p q : ℕ}
    (e : Fin p → Fin a ⊕ Fin b) (f : Fin q → Fin a ⊕ Fin b)
    (P : Matrix (Fin p) (Fin p) ℂ) (Q : Matrix (Fin q) (Fin p) ℂ) :
    Matrix (Fin (a + b)) (Fin (a + b)) ℂ →ₗ[ℂ] ℂ where
  toFun M := Matrix.trace (P *
    ((Matrix.reindexAlgEquiv ℂ ℂ finSumFinEquiv).symm M).submatrix e f * Q)
  map_add' M N := by
    simp [map_add, Matrix.submatrix_add, Matrix.mul_add, Matrix.add_mul, Matrix.trace_add]
  map_smul' c M := by
    simp [map_smul, Matrix.submatrix_smul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.trace_smul]

private theorem uncleBoundaryBlockTrace_upper_word
    (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (L : Fin d → Matrix (Fin b) (Fin a) ℂ)
    (P : Matrix (Fin a) (Fin a) ℂ) (Q : Matrix (Fin b) (Fin a) ℂ) (w : List (Fin d)) :
    uncleBoundaryBlockTrace Sum.inl Sum.inr P Q (uncleBoundaryWord A B R L w) =
      Matrix.trace (P * uncleDomainWallWord A B R w * Q) := by
  rw [uncleBoundaryWord_block]
  change Matrix.trace (P *
    ((Matrix.reindexAlgEquiv ℂ ℂ finSumFinEquiv).symm
      ((Matrix.reindexAlgEquiv ℂ ℂ finSumFinEquiv)
        (Matrix.fromBlocks _ _ _ _))).toBlocks₁₂ * Q) = _
  rw [AlgEquiv.symm_apply_apply]
  rfl

private theorem uncleBoundaryBlockTrace_lower_word
    (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (L : Fin d → Matrix (Fin b) (Fin a) ℂ)
    (P : Matrix (Fin b) (Fin b) ℂ) (Q : Matrix (Fin a) (Fin b) ℂ) (w : List (Fin d)) :
    uncleBoundaryBlockTrace Sum.inr Sum.inl P Q (uncleBoundaryWord A B R L w) =
      Matrix.trace (P * uncleDomainWallWord B A L w * Q) := by
  rw [uncleBoundaryWord_block]
  change Matrix.trace (P *
    ((Matrix.reindexAlgEquiv ℂ ℂ finSumFinEquiv).symm
      ((Matrix.reindexAlgEquiv ℂ ℂ finSumFinEquiv)
        (Matrix.fromBlocks _ _ _ _))).toBlocks₂₁ * Q) = _
  rw [AlgEquiv.symm_apply_apply]
  rfl

/-- Inside the R-wall interval, both adjacent wall positions sum to a vector
in the actual uncle projector kernel, even with arbitrary exterior factors.
No perturbation injectivity or canonical normalization is needed for this
algebraic cancellation. Source: arXiv:1210.6613, lines 1289–1296. -/
theorem uncleInteractionES_upper_wall_slice_eq_zero
    (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (L : Fin d → Matrix (Fin b) (Fin a) ℂ)
    (P : Matrix (Fin a) (Fin a) ℂ) (Q : Matrix (Fin b) (Fin a) ℂ)
    (u v : List (Fin d)) :
    uncleInteractionES A B R L ((WithLp.linearEquiv 2 ℂ (NSiteSpace d 2)).symm
      (fun σ ↦ Matrix.trace (P * uncleDomainWallWord A B R (u ++ List.ofFn σ ++ v) * Q))) =
      0 := by
  apply (mem_uncleBoundarySpace_two_iff A B R L _).mp
  simpa only [uncleBoundaryBlockTrace_upper_word] using
    uncleBoundaryWord_slice_mem A B R L (uncleBoundaryBlockTrace Sum.inl Sum.inr P Q) u v

/-- Inside the L-wall interval the same actual local cancellation holds,
with the second rectangular wall orientation. Source: arXiv:1210.6613,
lines 1289–1296. -/
theorem uncleInteractionES_lower_wall_slice_eq_zero
    (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (L : Fin d → Matrix (Fin b) (Fin a) ℂ)
    (P : Matrix (Fin b) (Fin b) ℂ) (Q : Matrix (Fin a) (Fin b) ℂ)
    (u v : List (Fin d)) :
    uncleInteractionES A B R L ((WithLp.linearEquiv 2 ℂ (NSiteSpace d 2)).symm
      (fun σ ↦ Matrix.trace (P * uncleDomainWallWord B A L (u ++ List.ofFn σ ++ v) * Q))) =
      0 := by
  apply (mem_uncleBoundarySpace_two_iff A B R L _).mp
  simpa only [uncleBoundaryBlockTrace_lower_word] using
    uncleBoundaryWord_slice_mem A B R L (uncleBoundaryBlockTrace Sum.inr Sum.inl P Q) u v

/-- The actual two-wall coefficient is killed by a pair inside the first
moving interval, with every exterior physical letter fixed. This includes
all wall positions in that interval, not just the two local positions.
Source: arXiv:1210.6613, lines 1289–1296. -/
theorem uncleInteractionES_twoWall_slice_first_eq_zero
    (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (L : Fin d → Matrix (Fin b) (Fin a) ℂ)
    (p u v w x y : List (Fin d)) :
    uncleInteractionES A B R L ((WithLp.linearEquiv 2 ℂ (NSiteSpace d 2)).symm
      (fun σ ↦ uncleTwoWallCoefficient A B R L p (u ++ List.ofFn σ ++ v) w x y)) = 0 := by
  simpa only [uncleTwoWallCoefficient, Matrix.mul_assoc] using
    uncleInteractionES_upper_wall_slice_eq_zero A B R L (Kraus.evalWord A p)
      (Kraus.evalWord B w * uncleDomainWallWord B A L x * Kraus.evalWord A y) u v

/-- The actual two-wall coefficient is also killed by a pair inside the
second moving interval. The rectangular trace identity moves the exterior
first wall around the periodic trace. Source: arXiv:1210.6613, lines 1289–1296. -/
theorem uncleInteractionES_twoWall_slice_second_eq_zero
    (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (L : Fin d → Matrix (Fin b) (Fin a) ℂ)
    (p r w u v y : List (Fin d)) :
    uncleInteractionES A B R L ((WithLp.linearEquiv 2 ℂ (NSiteSpace d 2)).symm
      (fun σ ↦ uncleTwoWallCoefficient A B R L p r w (u ++ List.ofFn σ ++ v) y)) = 0 := by
  have hslice :
      (fun σ : Fin 2 → Fin d ↦
        uncleTwoWallCoefficient A B R L p r w (u ++ List.ofFn σ ++ v) y) =
      (fun σ ↦ Matrix.trace (Kraus.evalWord B w *
        uncleDomainWallWord B A L (u ++ List.ofFn σ ++ v) *
          (Kraus.evalWord A y * Kraus.evalWord A p * uncleDomainWallWord A B R r))) := by
    funext σ
    unfold uncleTwoWallCoefficient
    calc
      _ = Matrix.trace ((Kraus.evalWord A p * uncleDomainWallWord A B R r) *
          (Kraus.evalWord B w * uncleDomainWallWord B A L (u ++ List.ofFn σ ++ v) *
            Kraus.evalWord A y)) := by simp only [Matrix.mul_assoc]
      _ = Matrix.trace ((Kraus.evalWord B w *
          uncleDomainWallWord B A L (u ++ List.ofFn σ ++ v) * Kraus.evalWord A y) *
            (Kraus.evalWord A p * uncleDomainWallWord A B R r)) :=
        Matrix.trace_mul_comm _ _
      _ = _ := by simp only [Matrix.mul_assoc]
  rw [hslice]
  exact uncleInteractionES_lower_wall_slice_eq_zero A B R L (Kraus.evalWord B w)
    (Kraus.evalWord A y * Kraus.evalWord A p * uncleDomainWallWord A B R r) u v

end MPSTensor
