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

/-- Rotate the first rectangular wall around the actual two-wall trace.
Source: arXiv:1210.6613, the two-wall coefficient in phiN-def. -/
theorem uncleTwoWallCoefficient_rotate (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (L : Fin d → Matrix (Fin b) (Fin a) ℂ) (p r w x y : List (Fin d)) :
    uncleTwoWallCoefficient A B R L p r w x y =
      Matrix.trace (Kraus.evalWord B w * uncleDomainWallWord B A L x *
        (Kraus.evalWord A y * Kraus.evalWord A p * uncleDomainWallWord A B R r)) := by
  simpa only [uncleTwoWallCoefficient, Matrix.mul_assoc] using
    Matrix.trace_mul_comm (Kraus.evalWord A p * uncleDomainWallWord A B R r)
      (Kraus.evalWord B w * uncleDomainWallWord B A L x * Kraus.evalWord A y)

/-- Concatenating a one-wall word separates walls in its left and right
pieces. Source: arXiv:1210.6613, the one-wall sums in phiN-def. -/
theorem uncleDomainWallWord_append (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ) (u v : List (Fin d)) :
    uncleDomainWallWord A B R (u ++ v) =
      Kraus.evalWord A u * uncleDomainWallWord A B R v +
        uncleDomainWallWord A B R u * Kraus.evalWord B v := by
  induction u with
  | nil => simp [uncleDomainWallWord]
  | cons i u ih =>
      simp only [List.cons_append, uncleDomainWallWord, ih, Kraus.evalWord_cons,
        Kraus.evalWord_append, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
      abel

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

/-- The physical word on a numbered consecutive segment. -/
def uncleConfigSegment {T : ℕ} (σ : Cfg d T) (s n : ℕ) (h : s + n ≤ T) :
    List (Fin d) := List.ofFn fun j : Fin n ↦ σ ⟨s + j.val, by omega⟩

/-- The source trial on 6N+1 sites, with wall intervals N through 2N and
4N through 5N in zero-based coordinates. For N positive the five lengths
are N, N+1, 2N-1, N+1, N, giving exactly the source two separated windows.
Source: arXiv:1210.6613, phiN-def, lines 1196–1224. -/
def uncleTwoWallTrialSource (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (L : Fin d → Matrix (Fin b) (Fin a) ℂ) (N : ℕ) : NSiteSpace d (6 * N + 1) := fun σ ↦
  uncleTwoWallCoefficient A B R L
    (uncleConfigSegment σ 0 N (by omega))
    (uncleConfigSegment σ N (N + 1) (by omega))
    (uncleConfigSegment σ (2 * N + 1) (2 * N - 1) (by omega))
    (uncleConfigSegment σ (4 * N) (N + 1) (by omega))
    (uncleConfigSegment σ (5 * N + 1) N (by omega))

private theorem uncleTwoWallCoefficient_five_list_cuts
    (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (L : Fin d → Matrix (Fin b) (Fin a) ℂ) (u r w x y : List (Fin d)) :
    let z := u ++ (r ++ (w ++ (x ++ y)))
    uncleTwoWallCoefficient A B R L (z.take u.length) ((z.drop u.length).take r.length)
      ((z.drop (u.length + r.length)).take w.length)
      ((z.drop (u.length + r.length + w.length)).take x.length)
      (z.drop (u.length + r.length + w.length + x.length)) =
        uncleTwoWallCoefficient A B R L u r w x y := by
  simp only [← List.drop_drop, List.drop_left, List.take_left]

/-- Evaluate the actual five-segment trial on the nested physical append.
This identifies the finite tuple coefficient used in the source norm sum,
arXiv:1210.6613, phiN-def and the proof of Lemma lowenergystates. -/
theorem uncleTwoWallTrial_append_apply
    (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (L : Fin d → Matrix (Fin b) (Fin a) ℂ) (p r q s t : ℕ)
    (u : Cfg d p) (v : Cfg d r) (w : Cfg d q) (x : Cfg d s) (y : Cfg d t) :
    uncleTwoWallTrial A B R L p r q s t
        (Fin.append (Fin.append (Fin.append (Fin.append u v) w) x) y) =
      uncleTwoWallCoefficient A B R L
        (List.ofFn u) (List.ofFn v) (List.ofFn w) (List.ofFn x) (List.ofFn y) := by
  simp only [uncleTwoWallTrial, List.ofFn_fin_append]
  simpa only [List.length_ofFn, List.append_assoc] using
    uncleTwoWallCoefficient_five_list_cuts A B R L
      (List.ofFn u) (List.ofFn v) (List.ofFn w) (List.ofFn x) (List.ofFn y)

/-- A numbered physical segment is the corresponding exact list slice. -/
theorem uncleConfigSegment_eq_drop_take {T : ℕ} (σ : Cfg d T)
    (s n : ℕ) (hs : s + n ≤ T) :
    uncleConfigSegment σ s n hs = ((List.ofFn σ).drop s).take n := by
  apply List.ext_getElem
  · simp only [uncleConfigSegment, List.length_ofFn, List.length_take, List.length_drop]
    omega
  · intro j hj hk
    simp [uncleConfigSegment]

/-- Every coefficient of the general trial uses its five exact numbered
physical segments. The last segment reaches the end of the chain. -/
theorem uncleTwoWallTrial_apply_segments
    (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (L : Fin d → Matrix (Fin b) (Fin a) ℂ) (p r q s t : ℕ)
    (σ : Cfg d (p + r + q + s + t)) :
    uncleTwoWallTrial A B R L p r q s t σ =
      uncleTwoWallCoefficient A B R L
        (uncleConfigSegment σ 0 p (by omega))
        (uncleConfigSegment σ p r (by omega))
        (uncleConfigSegment σ (p + r) q (by omega))
        (uncleConfigSegment σ (p + r + q) s (by omega))
        (uncleConfigSegment σ (p + r + q + s) t (by omega)) := by
  simp only [uncleTwoWallTrial, uncleConfigSegment_eq_drop_take, List.drop_zero]
  have hlast : (((List.ofFn σ).drop (p + r + q + s)).take t) =
      (List.ofFn σ).drop (p + r + q + s) := by
    apply List.take_of_length_le
    simp only [List.length_drop, List.length_ofFn]
    omega
  rw [hlast]

/-- Numbered physical segments commute with the actual finite-length cast. -/
theorem uncleConfigSegment_cast {T U : ℕ} (h : T = U) (σ : Cfg d U)
    (s n : ℕ) (hs : s + n ≤ T) :
    uncleConfigSegment (σ ∘ Fin.cast h) s n hs =
      uncleConfigSegment σ s n (by omega) := by
  apply congrArg List.ofFn
  funext j
  exact congrArg σ (Fin.ext rfl)

/-- The actual source trial is the five-segment trial transported by the
finite-length equality, for every positive source size. Source:
arXiv:1210.6613, phiN-def, lines 1196–1224. -/
theorem uncleTwoWallTrialSource_cast_apply
    (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (L : Fin d → Matrix (Fin b) (Fin a) ℂ)
    (N : ℕ) (hN : 0 < N) (σ : Cfg d (6 * N + 1)) :
    uncleTwoWallTrialSource A B R L N σ =
      uncleTwoWallTrial A B R L N (N + 1) (2 * N - 1) (N + 1) N
        (σ ∘ Fin.cast (by omega : N + (N + 1) + (2 * N - 1) + (N + 1) + N =
          6 * N + 1)) := by
  rw [uncleTwoWallTrial_apply_segments]
  simp only [uncleConfigSegment_cast, uncleTwoWallTrialSource,
    show N + (N + 1) = 2 * N + 1 by omega,
    show 2 * N + 1 + (2 * N - 1) = 4 * N by omega,
    show 4 * N + (N + 1) = 5 * N + 1 by omega]

private theorem norm_config_cast {T U : ℕ} (h : T = U) (f : NSiteSpace d T) :
    ‖(WithLp.linearEquiv 2 ℂ (NSiteSpace d U)).symm (fun σ ↦ f (σ ∘ Fin.cast h))‖ =
      ‖(WithLp.linearEquiv 2 ℂ (NSiteSpace d T)).symm f‖ := by
  cases h
  rfl

/-- The actual source norm is exactly the five-segment trial norm; the
finite-length transport is a reindexing, not a norm approximation.
Source: arXiv:1210.6613, phiN-def and Lemma lowenergystates. -/
theorem norm_uncleTwoWallTrialSource_eq
    (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (L : Fin d → Matrix (Fin b) (Fin a) ℂ) (N : ℕ) (hN : 0 < N) :
    ‖(WithLp.linearEquiv 2 ℂ (NSiteSpace d (6 * N + 1))).symm
        (uncleTwoWallTrialSource A B R L N)‖ =
      ‖(WithLp.linearEquiv 2 ℂ
          (NSiteSpace d (N + (N + 1) + (2 * N - 1) + (N + 1) + N))).symm
        (uncleTwoWallTrial A B R L N (N + 1) (2 * N - 1) (N + 1) N)‖ := by
  have hfun : uncleTwoWallTrialSource A B R L N =
      fun σ ↦ uncleTwoWallTrial A B R L N (N + 1) (2 * N - 1) (N + 1) N
        (σ ∘ Fin.cast (by omega : N + (N + 1) + (2 * N - 1) + (N + 1) + N =
          6 * N + 1)) := by
    funext σ
    exact uncleTwoWallTrialSource_cast_apply A B R L N hN σ
  rw [hfun]
  exact norm_config_cast (by omega) _

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
  let f' := f.comp ((uncleBoundaryMulLeft (uncleBoundaryWord A B R L u)).comp
    (uncleBoundaryMulRight (uncleBoundaryWord A B R L v)))
  let X := ((Matrix.traceBilinForm (Fin (a + b))).toDual
    Matrix.traceBilinForm_nondegenerate).symm f'
  have hX (M : Matrix (Fin (a + b)) (Fin (a + b)) ℂ) :
      f' M = Matrix.trace (X * M) := by
    rw [← Matrix.traceBilinForm_apply, LinearMap.BilinForm.apply_toDual_symm_apply]
  refine ⟨X, ?_⟩
  ext σ
  change Matrix.trace (uncleBoundaryWord A B R L (List.ofFn σ) * X) =
    f (uncleBoundaryWord A B R L (u ++ List.ofFn σ ++ v))
  simp only [uncleBoundaryWord_append, uncleBoundaryMul_assoc]
  exact (Matrix.trace_mul_comm _ _).trans (hX (uncleBoundaryWord A B R L (List.ofFn σ))).symm

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
  let e : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) ℂ ≃ₐ[ℂ]
      Matrix (Fin (a + b)) (Fin (a + b)) ℂ :=
    Matrix.reindexAlgEquiv ℂ ℂ finSumFinEquiv
  rw [uncleBoundaryWord_block]
  change Matrix.trace (P *
    (e.symm (e (Matrix.fromBlocks (Kraus.evalWord A w) (uncleDomainWallWord A B R w)
      (uncleDomainWallWord B A L w) (Kraus.evalWord B w)))).toBlocks₁₂ * Q) = _
  rw [AlgEquiv.symm_apply_apply]
  rfl

private theorem uncleBoundaryBlockTrace_lower_word
    (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (L : Fin d → Matrix (Fin b) (Fin a) ℂ)
    (P : Matrix (Fin b) (Fin b) ℂ) (Q : Matrix (Fin a) (Fin b) ℂ) (w : List (Fin d)) :
    uncleBoundaryBlockTrace Sum.inr Sum.inl P Q (uncleBoundaryWord A B R L w) =
      Matrix.trace (P * uncleDomainWallWord B A L w * Q) := by
  let e : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) ℂ ≃ₐ[ℂ]
      Matrix (Fin (a + b)) (Fin (a + b)) ℂ :=
    Matrix.reindexAlgEquiv ℂ ℂ finSumFinEquiv
  rw [uncleBoundaryWord_block]
  change Matrix.trace (P *
    (e.symm (e (Matrix.fromBlocks (Kraus.evalWord A w) (uncleDomainWallWord A B R w)
      (uncleDomainWallWord B A L w) (Kraus.evalWord B w)))).toBlocks₂₁ * Q) = _
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
    exact uncleTwoWallCoefficient_rotate A B R L p r w (u ++ List.ofFn σ ++ v) y
  rw [hslice]
  exact uncleInteractionES_lower_wall_slice_eq_zero A B R L (Kraus.evalWord B w)
    (Kraus.evalWord A y * Kraus.evalWord A p * uncleDomainWallWord A B R r) u v

end MPSTensor
