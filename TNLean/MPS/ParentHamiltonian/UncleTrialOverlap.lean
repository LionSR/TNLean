/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.UncleTrialTransferNorm
import TNLean.MPS.Overlap.Basic
import QICLean.Analysis.SpectralRadiusPowerDecay
import QICLean.Channel.Peripheral.UnitalKraus
import QICLean.Kraus.MixedMap.SpectralRadius
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Exact overlaps of the finite uncle trial with pure ground sectors

The overlap with a pure periodic sector is the trace of an actual ordered
mixed-transfer composition. The moving intervals retain their actual
single-domain-wall sums. This finite identity precedes the spectral estimate;
no overlap rate or orthogonality premise enters its statement.

Source: arXiv:1210.6613, proof of Lemma lowenergystates, item 2,
lines 1277–1287. The numbered source trial has separations 2N−1 in B
and 2N in A after joining the exterior intervals.
-/

noncomputable section

open scoped Matrix BigOperators InnerProductSpace

namespace MPSTensor

variable {d a b c : ℕ}

private def familyMixedMap {ι : Type*} [Fintype ι] {u v : ℕ}
    (U : ι → Matrix (Fin u) (Fin v) ℂ) (V : ι → Matrix (Fin c) (Fin c) ℂ) :
    Matrix (Fin v) (Fin c) ℂ →ₗ[ℂ] Matrix (Fin u) (Fin c) ℂ :=
  ∑ i, (mulLeftLinearMap (n := Fin c) ℂ (U i)).comp
    (mulRightLinearMap (l := Fin v) ℂ ((V i)ᴴ))

private theorem familyMixedMap_apply {ι : Type*} [Fintype ι] {u v : ℕ}
    (U : ι → Matrix (Fin u) (Fin v) ℂ) (V : ι → Matrix (Fin c) (Fin c) ℂ)
    (X : Matrix (Fin v) (Fin c) ℂ) :
    familyMixedMap U V X = ∑ i, U i * X * (V i)ᴴ := by
  simp [familyMixedMap, Matrix.mul_assoc]

private theorem familyMixedMap_comp {ι κ : Type*} [Fintype ι] [Fintype κ]
    {u v w : ℕ} (U : ι → Matrix (Fin u) (Fin v) ℂ)
    (V : ι → Matrix (Fin c) (Fin c) ℂ)
    (S : κ → Matrix (Fin v) (Fin w) ℂ) (T : κ → Matrix (Fin c) (Fin c) ℂ) :
    (familyMixedMap U V).comp (familyMixedMap S T) =
      familyMixedMap (fun z : ι × κ ↦ U z.1 * S z.2)
        (fun z : ι × κ ↦ V z.1 * T z.2) := by
  apply LinearMap.ext
  intro X
  simp only [LinearMap.comp_apply, familyMixedMap_apply,
    Matrix.mul_sum, Matrix.sum_mul, Fintype.sum_prod_type,
    Matrix.conjTranspose_mul, Matrix.mul_assoc]

private theorem wordMixedMap_eq_pow (A : MPSTensor d a) (C : MPSTensor d c) (n : ℕ) :
    familyMixedMap (fun σ : Cfg d n ↦ Kraus.evalWord A (List.ofFn σ))
        (fun σ : Cfg d n ↦ Kraus.evalWord C (List.ofFn σ)) =
      Kraus.mixedMapLM A C ^ n := by
  apply LinearMap.ext
  intro X
  simpa only [familyMixedMap_apply] using (Kraus.mixedMapLM_pow_apply A C n X).symm

private theorem trace_familyMixedMap {ι : Type*} [Fintype ι]
    (U : ι → Matrix (Fin a) (Fin a) ℂ) (V : ι → Matrix (Fin c) (Fin c) ℂ) :
    LinearMap.trace ℂ (Matrix (Fin a) (Fin c) ℂ) (familyMixedMap U V) =
      ∑ z, Matrix.trace (U z) * star (Matrix.trace (V z)) := by
  classical
  rw [Matrix.linearMap_trace_eq_sum_apply_single]
  simp only [familyMixedMap_apply, Matrix.sum_apply, Matrix.entry_mul_single_mul]
  rw [Finset.sum_comm_cycle]
  apply Finset.sum_congr rfl
  intro z _
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.conjTranspose_apply,
    star_sum, Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_comm

/-- The actual wall-word map paired with a pure sector of the same physical
alphabet. Its two rectangular endpoint spaces are retained. Source:
arXiv:1210.6613, proof of Lemma lowenergystates, item 2. -/
def uncleWallMixedMap (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ) (C : MPSTensor d c) (n : ℕ) :
    Matrix (Fin b) (Fin c) ℂ →ₗ[ℂ] Matrix (Fin a) (Fin c) ℂ :=
  familyMixedMap (fun σ : Cfg d n ↦ uncleDomainWallWord A B R (List.ofFn σ))
    (fun σ : Cfg d n ↦ Kraus.evalWord C (List.ofFn σ))

/-- The actual wall mixed map is its finite coefficient contraction.
Source: arXiv:1210.6613, proof of Lemma lowenergystates, item 2. -/
theorem uncleWallMixedMap_apply (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ) (C : MPSTensor d c) (n : ℕ)
    (X : Matrix (Fin b) (Fin c) ℂ) :
    uncleWallMixedMap A B R C n X = ∑ σ : Cfg d n,
      uncleDomainWallWord A B R (List.ofFn σ) * X *
        (Kraus.evalWord C (List.ofFn σ))ᴴ := familyMixedMap_apply _ _ _

private theorem uncleWallMixedMap_zero (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ) (C : MPSTensor d c) :
    uncleWallMixedMap A B R C 0 = 0 := by
  apply LinearMap.ext
  intro X
  simp [uncleWallMixedMap_apply, uncleDomainWallWord]

private theorem uncleWallMixedMap_succ_left
    (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ) (C : MPSTensor d c) (n : ℕ) :
    uncleWallMixedMap A B R C (n + 1) =
      (Kraus.mixedMapLM A C).comp (uncleWallMixedMap A B R C n) +
        (familyMixedMap R C).comp (Kraus.mixedMapLM B C ^ n) := by
  classical
  apply LinearMap.ext
  intro X
  simp only [LinearMap.add_apply, LinearMap.comp_apply, uncleWallMixedMap_apply,
    familyMixedMap_apply, Kraus.mixedMapLM_apply, Kraus.mixedMapLM_pow_apply]
  rw [← (Fin.consEquiv (fun _ : Fin (n + 1) ↦ Fin d)).sum_comp]
  have hcons (i : Fin d) (τ : Cfg d n) :
      (Fin.consEquiv (fun _ : Fin (n + 1) ↦ Fin d)) (i, τ) = Fin.cons i τ := rfl
  simp only [Fintype.sum_prod_type, hcons, List.ofFn_cons,
    uncleDomainWallWord, Kraus.evalWord_cons, Matrix.conjTranspose_mul,
    Matrix.add_mul, Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_assoc,
    Finset.sum_add_distrib]

private theorem uncleWallMixedMap_succ_right
    (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ) (C : MPSTensor d c) (n : ℕ) :
    uncleWallMixedMap A B R C (n + 1) =
      (uncleWallMixedMap A B R C n).comp (Kraus.mixedMapLM B C) +
        (Kraus.mixedMapLM A C ^ n).comp (familyMixedMap R C) := by
  classical
  apply LinearMap.ext
  intro X
  simp only [LinearMap.add_apply, LinearMap.comp_apply, uncleWallMixedMap_apply,
    familyMixedMap_apply, Kraus.mixedMapLM_apply, Kraus.mixedMapLM_pow_apply]
  rw [← (Fin.snocEquiv (fun _ : Fin (n + 1) ↦ Fin d)).sum_comp]
  simp only [Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  have hsnocEquiv (i : Fin d) (τ : Cfg d n) :
      (Fin.snocEquiv (fun _ : Fin (n + 1) ↦ Fin d)) (i, τ) = Fin.snoc τ i := rfl
  have hsnoc (i : Fin d) (τ : Cfg d n) :
      List.ofFn (Fin.snoc τ i) = List.ofFn τ ++ [i] := by
    rw [List.ofFn_succ']
    simp only [Fin.snoc_castSucc, Fin.snoc_last, List.concat_eq_append]
  simp only [hsnocEquiv, hsnoc, uncleDomainWallWord_append,
    uncleDomainWallWord, Kraus.evalWord_append, Kraus.evalWord_cons,
    Kraus.evalWord_nil, Matrix.mul_zero, zero_add,
    Matrix.mul_one, Matrix.conjTranspose_mul, Matrix.add_mul, Matrix.mul_sum,
    Matrix.sum_mul, Matrix.mul_assoc, Finset.sum_add_distrib]
  exact add_comm _ _

/-- The ordered mixed-transfer contraction for the actual five-segment
trial against one pure periodic sector. Source: arXiv:1210.6613,
proof of Lemma lowenergystates, item 2. -/
def uncleTwoWallMixedTransfer (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (L : Fin d → Matrix (Fin b) (Fin a) ℂ) (C : MPSTensor d c) (p r q s t : ℕ) :
    Matrix (Fin a) (Fin c) ℂ →ₗ[ℂ] Matrix (Fin a) (Fin c) ℂ :=
  (Kraus.mixedMapLM A C ^ p).comp ((uncleWallMixedMap A B R C r).comp
    ((Kraus.mixedMapLM B C ^ q).comp
      ((uncleWallMixedMap B A L C s).comp (Kraus.mixedMapLM A C ^ t))))

/-- Exact finite mixed trace, with the actual five-segment coefficients
and the conjugated pure-sector coefficient on their concatenated word.
Source: arXiv:1210.6613, proof of Lemma lowenergystates, item 2. -/
theorem trace_uncleTwoWallMixedTransfer_eq_sum
    (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (L : Fin d → Matrix (Fin b) (Fin a) ℂ) (C : MPSTensor d c) (p r q s t : ℕ) :
    LinearMap.trace ℂ (Matrix (Fin a) (Fin c) ℂ)
        (uncleTwoWallMixedTransfer A B R L C p r q s t) =
      ∑ u : Cfg d p, ∑ v : Cfg d r, ∑ w : Cfg d q,
        ∑ x : Cfg d s, ∑ y : Cfg d t,
          uncleTwoWallCoefficient A B R L (List.ofFn u) (List.ofFn v)
              (List.ofFn w) (List.ofFn x) (List.ofFn y) *
            star (Matrix.trace (Kraus.evalWord C
              (List.ofFn u ++ List.ofFn v ++ List.ofFn w ++ List.ofFn x ++ List.ofFn y))) := by
  unfold uncleTwoWallMixedTransfer uncleWallMixedMap
  rw [← wordMixedMap_eq_pow A C p, ← wordMixedMap_eq_pow B C q,
    ← wordMixedMap_eq_pow A C t]
  simp only [familyMixedMap_comp]
  rw [trace_familyMixedMap]
  simp only [Fintype.sum_prod_type, uncleTwoWallCoefficient, Kraus.evalWord_append,
    Matrix.mul_assoc]

/-- The actual inner product of a pure periodic state with the five-segment
trial is the ordered mixed-transfer trace. No overlap estimate is assumed.
Source: arXiv:1210.6613, proof of Lemma lowenergystates, item 2. -/
theorem inner_mpvState_uncleTwoWallTrial_eq_trace
    (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (L : Fin d → Matrix (Fin b) (Fin a) ℂ) (C : MPSTensor d c) (p r q s t : ℕ) :
    ⟪mpvState C (p + r + q + s + t),
      (WithLp.linearEquiv 2 ℂ (NSiteSpace d (p + r + q + s + t))).symm
        (uncleTwoWallTrial A B R L p r q s t)⟫_ℂ =
      LinearMap.trace ℂ (Matrix (Fin a) (Fin c) ℂ)
        (uncleTwoWallMixedTransfer A B R L C p r q s t) := by
  classical
  rw [PiLp.inner_apply]
  change (∑ σ : Cfg d (p + r + q + s + t),
    uncleTwoWallTrial A B R L p r q s t σ * star (mpv C σ)) = _
  rw [← (uncleFiveConfigEquiv (d := d) p r q s t).sum_comp
    (fun σ ↦ uncleTwoWallTrial A B R L p r q s t σ * star (mpv C σ))]
  simp only [Fintype.sum_prod_type, uncleFiveConfigEquiv_apply,
    uncleTwoWallTrial_append_apply, mpv, coeff_eq, List.ofFn_fin_append,
    trace_uncleTwoWallMixedTransfer_eq_sum, List.append_assoc]

/-- Joining the two exterior intervals preserves the actual mixed trace.
For the numbered source trial their joined A separation is exactly 2N.
Source: arXiv:1210.6613, proof of Lemma lowenergystates, item 2. -/
theorem trace_uncleTwoWallMixedTransfer_join_exterior
    (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (L : Fin d → Matrix (Fin b) (Fin a) ℂ) (C : MPSTensor d c) (p r q s t : ℕ) :
    LinearMap.trace ℂ (Matrix (Fin a) (Fin c) ℂ)
        (uncleTwoWallMixedTransfer A B R L C p r q s t) =
      LinearMap.trace ℂ (Matrix (Fin a) (Fin c) ℂ)
        (uncleTwoWallMixedTransfer A B R L C (p + t) r q s 0) := by
  let E := Kraus.mixedMapLM A C
  let M := (uncleWallMixedMap A B R C r).comp
    ((Kraus.mixedMapLM B C ^ q).comp (uncleWallMixedMap B A L C s))
  change LinearMap.trace ℂ (Matrix (Fin a) (Fin c) ℂ) (E ^ p * (M * E ^ t)) =
    LinearMap.trace ℂ (Matrix (Fin a) (Fin c) ℂ) (E ^ (p + t) * (M * E ^ 0))
  rw [pow_zero, mul_one, ← mul_assoc,
    LinearMap.trace_mul_comm (R := ℂ) (M := Matrix (Fin a) (Fin c) ℂ)
      (E ^ p * M) (E ^ t), ← mul_assoc, ← pow_add, Nat.add_comm t p]

private theorem inner_mpvState_config_cast {n m : ℕ} (h : n = m)
    (C : MPSTensor d c) (f : NSiteSpace d n) :
    ⟪mpvState C m, (WithLp.linearEquiv 2 ℂ (NSiteSpace d m)).symm
      (fun σ ↦ f (σ ∘ Fin.cast h))⟫_ℂ =
      ⟪mpvState C n, (WithLp.linearEquiv 2 ℂ (NSiteSpace d n)).symm f⟫_ℂ := by
  subst m
  rfl

/-- The actual source trial overlap has its exact numbered separation lengths:
2N in A after closing the exterior intervals and 2N−1 in B.
Source: arXiv:1210.6613, proof of Lemma lowenergystates, item 2. -/
theorem inner_mpvState_uncleTwoWallTrialSource_eq_trace
    (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (L : Fin d → Matrix (Fin b) (Fin a) ℂ) (C : MPSTensor d c)
    (N : ℕ) (hN : 0 < N) :
    ⟪mpvState C (6 * N + 1),
      (WithLp.linearEquiv 2 ℂ (NSiteSpace d (6 * N + 1))).symm
        (uncleTwoWallTrialSource A B R L N)⟫_ℂ =
      LinearMap.trace ℂ (Matrix (Fin a) (Fin c) ℂ)
        (uncleTwoWallMixedTransfer A B R L C (2 * N) (N + 1)
          (2 * N - 1) (N + 1) 0) := by
  have hlen : N + (N + 1) + (2 * N - 1) + (N + 1) + N = 6 * N + 1 := by omega
  have hfun : uncleTwoWallTrialSource A B R L N = fun σ ↦
      uncleTwoWallTrial A B R L N (N + 1) (2 * N - 1) (N + 1) N
        (σ ∘ Fin.cast hlen) := funext (uncleTwoWallTrialSource_cast_apply A B R L N hN)
  rw [hfun, inner_mpvState_config_cast hlen,
    inner_mpvState_uncleTwoWallTrial_eq_trace]
  simpa only [two_mul] using
    trace_uncleTwoWallMixedTransfer_join_exterior A B R L C N (N + 1)
      (2 * N - 1) (N + 1) N

open scoped TNOperatorSpace in
private theorem mixedMapSpectralRadius_eq_end (A : MPSTensor d a) (B : MPSTensor d b) :
    Kraus.mixedMapSpectralRadius A B = spectralRadius ℂ (Kraus.mixedMapLM A B) := by
  unfold Kraus.mixedMapSpectralRadius
  simp only [spectralRadius_eq_of_unital, AlgEquiv.spectrum_eq]

section OperatorNorm

open scoped Matrix.Norms.L2Operator

private theorem mixed_pow_norm_le_geometric (A : MPSTensor d a) (B : MPSTensor d b)
    (hSpect : Kraus.mixedMapSpectralRadius A B < 1) :
    ∃ K r : ℝ, 0 < K ∧ 0 < r ∧ r < 1 ∧ ∀ (n : ℕ)
      (X : Matrix (Fin a) (Fin b) ℂ),
      ‖((Kraus.mixedMapLM A B) ^ n) X‖ ≤ K * r ^ n * ‖X‖ := by
  let e : Module.End ℂ (Matrix (Fin a) (Fin b) ℂ) ≃ₐ[ℂ]
      (Matrix (Fin a) (Fin b) ℂ →L[ℂ] Matrix (Fin a) (Fin b) ℂ) :=
    Module.End.toContinuousLinearMap (Matrix (Fin a) (Fin b) ℂ)
  let F : Matrix (Fin a) (Fin b) ℂ →L[ℂ] Matrix (Fin a) (Fin b) ℂ :=
    e (Kraus.mixedMapLM A B)
  have hF : spectralRadius ℂ F < 1 := by
    rw [mixedMapSpectralRadius_eq_end] at hSpect
    change spectralRadius ℂ (e (Kraus.mixedMapLM A B)) < 1
    simpa only [spectralRadius_eq_of_unital, AlgEquiv.spectrum_eq] using hSpect
  obtain ⟨K, r, hK, hr, hr1, hbound⟩ :=
    geometric_apply_bound_of_spectralRadius_lt_one F hF
  refine ⟨K, r, hK, hr, hr1, fun n X ↦ ?_⟩
  have hApply : (F ^ n) X = ((Kraus.mixedMapLM A B) ^ n) X := by
    rw [show F = e (Kraus.mixedMapLM A B) from rfl, ← map_pow]
    rfl
  simpa only [hApply] using hbound n X

private theorem unital_transfer_norm_le (A : MPSTensor d a)
    (hA : Kraus.mapLM A 1 = 1) (X : Matrix (Fin a) (Fin a) ℂ) :
    ‖Kraus.mapLM A X‖ ≤ ‖X‖ := by
  have hCP : IsKrausCP (Kraus.mapLM A) := Kraus.isCPMap_mapLM A
  exact hCP.norm_apply_le_of_map_one_eq_one hA X

/-- The actual wall mixed map against its left pure sector is uniformly
linear in the interval length. Strict mixed damping supplies bounded powers;
no overlap estimate is assumed. Source: arXiv:1210.6613,
proof of Lemma lowenergystates, item 2. -/
theorem uncleWallMixedMap_left_norm_le_mul
    (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (hA : Kraus.mapLM A 1 = 1) (hSpect : Kraus.mixedMapSpectralRadius B A < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (X : Matrix (Fin b) (Fin a) ℂ),
      ‖uncleWallMixedMap A B R A n X‖ ≤ C * n * ‖X‖ := by
  obtain ⟨K, r, hK, hr, hr1, hbound⟩ := mixed_pow_norm_le_geometric B A hSpect
  let S := LinearMap.toContinuousLinearMap (familyMixedMap R A)
  let D := ‖S‖ + 1
  have hD : 0 < D := by dsimp [D]; positivity
  have hS (X : Matrix (Fin b) (Fin a) ℂ) : ‖familyMixedMap R A X‖ ≤ D * ‖X‖ :=
    (S.le_opNorm X).trans (mul_le_mul_of_nonneg_right
      (by dsimp [D]; linarith) (norm_nonneg X))
  have hpow (n : ℕ) (X : Matrix (Fin b) (Fin a) ℂ) :
      ‖((Kraus.mixedMapLM B A) ^ n) X‖ ≤ K * ‖X‖ :=
    (hbound n X).trans (mul_le_mul_of_nonneg_right
      (mul_le_of_le_one_right hK.le (pow_le_one₀ hr.le hr1.le)) (norm_nonneg X))
  refine ⟨D * K, mul_pos hD hK, ?_⟩
  intro n
  induction n with
  | zero => intro X; simp [uncleWallMixedMap_zero]
  | succ n ih =>
    intro X
    rw [uncleWallMixedMap_succ_left]
    change ‖Kraus.mixedMapLM A A (uncleWallMixedMap A B R A n X) +
      familyMixedMap R A (((Kraus.mixedMapLM B A) ^ n) X)‖ ≤ _
    rw [Kraus.mixedMapLM_self]
    calc
      _ ≤ ‖Kraus.mapLM A (uncleWallMixedMap A B R A n X)‖ +
          ‖familyMixedMap R A (((Kraus.mixedMapLM B A) ^ n) X)‖ := norm_add_le _ _
      _ ≤ ‖uncleWallMixedMap A B R A n X‖ +
          D * ‖((Kraus.mixedMapLM B A) ^ n) X‖ :=
        add_le_add (unital_transfer_norm_le A hA _) (hS _)
      _ ≤ (D * K) * n * ‖X‖ + D * (K * ‖X‖) :=
        add_le_add (ih X) (mul_le_mul_of_nonneg_left (hpow n X) hD.le)
      _ = _ := by push_cast; ring

/-- The complementary actual wall mixed map against its right pure sector
has the same uniform linear control. Source: arXiv:1210.6613,
proof of Lemma lowenergystates, item 2. -/
theorem uncleWallMixedMap_right_norm_le_mul
    (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (hB : Kraus.mapLM B 1 = 1) (hSpect : Kraus.mixedMapSpectralRadius A B < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (X : Matrix (Fin b) (Fin b) ℂ),
      ‖uncleWallMixedMap A B R B n X‖ ≤ C * n * ‖X‖ := by
  obtain ⟨K, r, hK, hr, hr1, hbound⟩ := mixed_pow_norm_le_geometric A B hSpect
  let S := LinearMap.toContinuousLinearMap (familyMixedMap R B)
  let D := ‖S‖ + 1
  have hD : 0 < D := by dsimp [D]; positivity
  have hS (X : Matrix (Fin b) (Fin b) ℂ) : ‖familyMixedMap R B X‖ ≤ D * ‖X‖ :=
    (S.le_opNorm X).trans (mul_le_mul_of_nonneg_right
      (by dsimp [D]; linarith) (norm_nonneg X))
  have hpow (n : ℕ) (X : Matrix (Fin a) (Fin b) ℂ) :
      ‖((Kraus.mixedMapLM A B) ^ n) X‖ ≤ K * ‖X‖ :=
    (hbound n X).trans (mul_le_mul_of_nonneg_right
      (mul_le_of_le_one_right hK.le (pow_le_one₀ hr.le hr1.le)) (norm_nonneg X))
  refine ⟨K * D, mul_pos hK hD, ?_⟩
  intro n
  induction n with
  | zero => intro X; simp [uncleWallMixedMap_zero]
  | succ n ih =>
    intro X
    rw [uncleWallMixedMap_succ_right]
    change ‖uncleWallMixedMap A B R B n (Kraus.mixedMapLM B B X) +
      ((Kraus.mixedMapLM A B) ^ n) (familyMixedMap R B X)‖ ≤ _
    rw [Kraus.mixedMapLM_self]
    calc
      _ ≤ ‖uncleWallMixedMap A B R B n (Kraus.mapLM B X)‖ +
          ‖((Kraus.mixedMapLM A B) ^ n) (familyMixedMap R B X)‖ := norm_add_le _ _
      _ ≤ (K * D) * n * ‖Kraus.mapLM B X‖ + K * ‖familyMixedMap R B X‖ :=
        add_le_add (ih _) (hpow n _)
      _ ≤ (K * D) * n * ‖X‖ + K * (D * ‖X‖) := add_le_add
        (mul_le_mul_of_nonneg_left (unital_transfer_norm_le B hB X)
          (by positivity)) (mul_le_mul_of_nonneg_left (hS X) hK.le)
      _ = _ := by push_cast; ring

private theorem exists_trace_norm_bound (u v : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (T : Module.End ℂ (Matrix (Fin u) (Fin v) ℂ))
      (D : ℝ), 0 ≤ D → (∀ X, ‖T X‖ ≤ D * ‖X‖) →
        ‖LinearMap.trace ℂ (Matrix (Fin u) (Fin v) ℂ) T‖ ≤ K * D := by
  let e : Module.End ℂ (Matrix (Fin u) (Fin v) ℂ) ≃ₐ[ℂ]
      (Matrix (Fin u) (Fin v) ℂ →L[ℂ] Matrix (Fin u) (Fin v) ℂ) :=
    Module.End.toContinuousLinearMap (Matrix (Fin u) (Fin v) ℂ)
  let tr : (Matrix (Fin u) (Fin v) ℂ →L[ℂ] Matrix (Fin u) (Fin v) ℂ) →L[ℂ] ℂ :=
    LinearMap.toContinuousLinearMap
    ((LinearMap.trace ℂ (Matrix (Fin u) (Fin v) ℂ)).comp e.symm.toLinearMap)
  refine ⟨‖tr‖ + 1, by positivity, fun T D hD hT ↦ ?_⟩
  have hnorm : ‖e T‖ ≤ D := ContinuousLinearMap.opNorm_le_bound _ hD hT
  calc
    _ = ‖tr (e T)‖ := by
      change ‖LinearMap.trace ℂ (Matrix (Fin u) (Fin v) ℂ) T‖ =
        ‖LinearMap.trace ℂ (Matrix (Fin u) (Fin v) ℂ) (e.symm (e T))‖
      rw [e.symm_apply_apply]
    _ ≤ ‖tr‖ * ‖e T‖ := tr.le_opNorm _
    _ ≤ (‖tr‖ + 1) * D :=
      (mul_le_mul_of_nonneg_left hnorm (norm_nonneg tr)).trans
        (mul_le_mul_of_nonneg_right (by linarith) hD)

/-- Against the A ground sector the actual source overlap has a polynomial
prefactor and a strict geometric rate. Its separating B interval is
2N−1, which is at least N for N>0. Source: arXiv:1210.6613,
proof of Lemma lowenergystates, item 2. -/
theorem norm_inner_mpvState_left_uncleTwoWallTrialSource_le_geometric_mul
    (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (L : Fin d → Matrix (Fin b) (Fin a) ℂ)
    (hA : Kraus.mapLM A 1 = 1) (hSpect : Kraus.mixedMapSpectralRadius B A < 1) :
    ∃ C r : ℝ, 0 < C ∧ 0 < r ∧ r < 1 ∧ ∀ N : ℕ, 0 < N →
      ‖⟪mpvState A (6 * N + 1),
        (WithLp.linearEquiv 2 ℂ (NSiteSpace d (6 * N + 1))).symm
          (uncleTwoWallTrialSource A B R L N)⟫_ℂ‖ ≤ C * (N : ℝ) ^ 2 * r ^ N := by
  obtain ⟨CR, hCR, hR⟩ := uncleWallMixedMap_left_norm_le_mul A B R hA hSpect
  obtain ⟨CL, hCL, hL⟩ := uncleWallMixedMap_right_norm_le_mul B A L hA hSpect
  obtain ⟨K, r, hK, hr, hr1, hpow⟩ := mixed_pow_norm_le_geometric B A hSpect
  obtain ⟨T, hT, htrace⟩ := exists_trace_norm_bound a a
  refine ⟨4 * T * CR * K * CL, r, by positivity, hr, hr1, ?_⟩
  intro N hN
  rw [inner_mpvState_uncleTwoWallTrialSource_eq_trace A B R L A N hN]
  have hsep : r ^ (2 * N - 1) ≤ r ^ N :=
    pow_le_pow_of_le_one hr.le hr1.le (by omega)
  have hTotal (X : Matrix (Fin a) (Fin a) ℂ) :
      ‖uncleTwoWallMixedTransfer A B R L A (2 * N) (N + 1) (2 * N - 1)
        (N + 1) 0 X‖ ≤ (CR * K * CL * ((N + 1 : ℕ) : ℝ) ^ 2 * r ^ N) * ‖X‖ := by
    change ‖((Kraus.mixedMapLM A A) ^ (2 * N))
      (uncleWallMixedMap A B R A (N + 1)
        (((Kraus.mixedMapLM B A) ^ (2 * N - 1))
          (uncleWallMixedMap B A L A (N + 1)
            (((Kraus.mixedMapLM A A) ^ 0) X))))‖ ≤ _
    simp only [Kraus.mixedMapLM_self, pow_zero, Module.End.one_apply]
    calc
      _ ≤ ‖uncleWallMixedMap A B R A (N + 1)
          (((Kraus.mixedMapLM B A) ^ (2 * N - 1))
            (uncleWallMixedMap B A L A (N + 1) X))‖ :=
        norm_mapLM_pow_apply_le_of_mapLM_one A hA (2 * N) _
      _ ≤ CR * ((N + 1 : ℕ) : ℝ) * ‖((Kraus.mixedMapLM B A) ^ (2 * N - 1))
          (uncleWallMixedMap B A L A (N + 1) X)‖ := hR _ _
      _ ≤ CR * ((N + 1 : ℕ) : ℝ) * (K * r ^ (2 * N - 1) *
          ‖uncleWallMixedMap B A L A (N + 1) X‖) :=
        mul_le_mul_of_nonneg_left (hpow _ _) (by positivity)
      _ ≤ CR * ((N + 1 : ℕ) : ℝ) * (K * r ^ N * (CL * ((N + 1 : ℕ) : ℝ) * ‖X‖)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul
          (mul_le_mul_of_nonneg_left hsep hK.le) (hL _ _)
          (norm_nonneg _) (by positivity)) (by positivity)
      _ = _ := by push_cast; ring
  have hmain := htrace _ _ (by positivity) hTotal
  have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast (Nat.succ_le_iff.mpr hN)
  calc
    _ ≤ T * (CR * K * CL * ((N + 1 : ℕ) : ℝ) ^ 2 * r ^ N) := hmain
    _ ≤ (4 * T * CR * K * CL) * (N : ℝ) ^ 2 * r ^ N := by
      push_cast
      have hsquare : ((N : ℝ) + 1) ^ 2 ≤ 4 * (N : ℝ) ^ 2 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left hsquare
        (show 0 ≤ T * CR * K * CL * r ^ N by positivity)]

/-- Against the B ground sector it is the joined exterior A interval,
of exact length 2N, that supplies geometric damping. Source:
arXiv:1210.6613, proof of Lemma lowenergystates, item 2. -/
theorem norm_inner_mpvState_right_uncleTwoWallTrialSource_le_geometric_mul
    (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (L : Fin d → Matrix (Fin b) (Fin a) ℂ)
    (hB : Kraus.mapLM B 1 = 1) (hSpect : Kraus.mixedMapSpectralRadius A B < 1) :
    ∃ C r : ℝ, 0 < C ∧ 0 < r ∧ r < 1 ∧ ∀ N : ℕ, 0 < N →
      ‖⟪mpvState B (6 * N + 1),
        (WithLp.linearEquiv 2 ℂ (NSiteSpace d (6 * N + 1))).symm
          (uncleTwoWallTrialSource A B R L N)⟫_ℂ‖ ≤ C * (N : ℝ) ^ 2 * r ^ N := by
  obtain ⟨CR, hCR, hR⟩ := uncleWallMixedMap_right_norm_le_mul A B R hB hSpect
  obtain ⟨CL, hCL, hL⟩ := uncleWallMixedMap_left_norm_le_mul B A L hB hSpect
  obtain ⟨K, r, hK, hr, hr1, hpow⟩ := mixed_pow_norm_le_geometric A B hSpect
  obtain ⟨T, hT, htrace⟩ := exists_trace_norm_bound a b
  refine ⟨4 * T * K * CR * CL, r, by positivity, hr, hr1, ?_⟩
  intro N hN
  rw [inner_mpvState_uncleTwoWallTrialSource_eq_trace A B R L B N hN]
  have hsep : r ^ (2 * N) ≤ r ^ N :=
    pow_le_pow_of_le_one hr.le hr1.le (by omega)
  have hTotal (X : Matrix (Fin a) (Fin b) ℂ) :
      ‖uncleTwoWallMixedTransfer A B R L B (2 * N) (N + 1) (2 * N - 1)
        (N + 1) 0 X‖ ≤ (K * CR * CL * ((N + 1 : ℕ) : ℝ) ^ 2 * r ^ N) * ‖X‖ := by
    change ‖((Kraus.mixedMapLM A B) ^ (2 * N))
      (uncleWallMixedMap A B R B (N + 1)
        (((Kraus.mixedMapLM B B) ^ (2 * N - 1))
          (uncleWallMixedMap B A L B (N + 1)
            (((Kraus.mixedMapLM A B) ^ 0) X))))‖ ≤ _
    simp only [Kraus.mixedMapLM_self, pow_zero, Module.End.one_apply]
    calc
      _ ≤ K * r ^ (2 * N) * ‖uncleWallMixedMap A B R B (N + 1)
          (((Kraus.mapLM B) ^ (2 * N - 1))
            (uncleWallMixedMap B A L B (N + 1) X))‖ := hpow _ _
      _ ≤ K * r ^ N * (CR * ((N + 1 : ℕ) : ℝ) * ‖((Kraus.mapLM B) ^ (2 * N - 1))
          (uncleWallMixedMap B A L B (N + 1) X)‖) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hsep hK.le) (hR _ _)
          (norm_nonneg _) (by positivity)
      _ ≤ K * r ^ N * (CR * ((N + 1 : ℕ) : ℝ) * ‖uncleWallMixedMap B A L B (N + 1) X‖) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
          (norm_mapLM_pow_apply_le_of_mapLM_one B hB (2 * N - 1) _) (by positivity)) (by positivity)
      _ ≤ K * r ^ N * (CR * ((N + 1 : ℕ) : ℝ) * (CL * ((N + 1 : ℕ) : ℝ) * ‖X‖)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hL _ _) (by positivity))
          (by positivity)
      _ = _ := by push_cast; ring
  have hmain := htrace _ _ (by positivity) hTotal
  have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast (Nat.succ_le_iff.mpr hN)
  calc
    _ ≤ T * (K * CR * CL * ((N + 1 : ℕ) : ℝ) ^ 2 * r ^ N) := hmain
    _ ≤ (4 * T * K * CR * CL) * (N : ℝ) ^ 2 * r ^ N := by
      push_cast
      have hsquare : ((N : ℝ) + 1) ^ 2 ≤ 4 * (N : ℝ) ^ 2 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left hsquare
        (show 0 ≤ T * K * CR * CL * r ^ N by positivity)]

private theorem absorb_quadratic_geometric {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    ∃ D z : ℝ, 0 < D ∧ 0 < z ∧ z < 1 ∧ ∀ n : ℕ,
      (n : ℝ) ^ 2 * r ^ n ≤ D * z ^ n := by
  let z := (r + 1) / 2
  have hz : 0 < z := by dsimp [z]; linarith
  have hrz : r < z := by dsimp [z]; linarith
  have hz1 : z < 1 := by dsimp [z]; linarith
  have hratio : ‖r / z‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (div_pos hr hz)]
    exact (div_lt_one hz).mpr hrz
  have hsum := summable_norm_pow_mul_geometric_of_norm_lt_one 2 hratio
  let D := (∑' n : ℕ, ‖(n : ℝ) ^ 2 * (r / z) ^ n‖) + 1
  have hD : 0 < D := by
    dsimp [D]
    exact add_pos_of_nonneg_of_pos (tsum_nonneg fun _ ↦ abs_nonneg _) zero_lt_one
  refine ⟨D, z, hD, hz, hz1, fun n ↦ ?_⟩
  have hterm : (n : ℝ) ^ 2 * (r / z) ^ n ≤ D := by
    have hle := hsum.le_tsum n (fun _ _ ↦ abs_nonneg _)
    have hn : 0 ≤ (n : ℝ) ^ 2 * (r / z) ^ n := by positivity
    rw [Real.norm_eq_abs, abs_of_nonneg hn] at hle
    exact hle.trans (by dsimp [D]; linarith)
  calc
    (n : ℝ) ^ 2 * r ^ n = ((n : ℝ) ^ 2 * (r / z) ^ n) * z ^ n := by
      symm
      rw [mul_assoc, ← mul_pow, div_mul_cancel₀ _ hz.ne']
    _ ≤ D * z ^ n := mul_le_mul_of_nonneg_right hterm (pow_nonneg hz.le n)

/-- The actual overlap with the A periodic ground sector decays at a strict
geometric rate. The polynomial number of possible wall positions is absorbed
by a weaker rate between the derived mixed rate and one; no fixed printed
exponent is assumed. Source: arXiv:1210.6613, Lemma lowenergystates, item 2. -/
theorem norm_inner_mpvState_left_uncleTwoWallTrialSource_le_geometric
    (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (L : Fin d → Matrix (Fin b) (Fin a) ℂ)
    (hA : Kraus.mapLM A 1 = 1) (hSpect : Kraus.mixedMapSpectralRadius B A < 1) :
    ∃ C z : ℝ, 0 < C ∧ 0 < z ∧ z < 1 ∧ ∀ N : ℕ, 0 < N →
      ‖⟪mpvState A (6 * N + 1),
        (WithLp.linearEquiv 2 ℂ (NSiteSpace d (6 * N + 1))).symm
          (uncleTwoWallTrialSource A B R L N)⟫_ℂ‖ ≤ C * z ^ N := by
  obtain ⟨C, r, hC, hr, hr1, hbound⟩ :=
    norm_inner_mpvState_left_uncleTwoWallTrialSource_le_geometric_mul A B R L hA hSpect
  obtain ⟨D, z, hD, hz, hz1, habsorb⟩ := absorb_quadratic_geometric hr hr1
  refine ⟨C * D, z, mul_pos hC hD, hz, hz1, fun N hN ↦ ?_⟩
  calc
    _ ≤ C * (N : ℝ) ^ 2 * r ^ N := hbound N hN
    _ = C * ((N : ℝ) ^ 2 * r ^ N) := mul_assoc _ _ _
    _ ≤ C * (D * z ^ N) := mul_le_mul_of_nonneg_left (habsorb N) hC.le
    _ = (C * D) * z ^ N := (mul_assoc _ _ _).symm

/-- The actual overlap with the B periodic ground sector also decays
geometrically, with its rate derived from strict mixed damping.
Source: arXiv:1210.6613, Lemma lowenergystates, item 2. -/
theorem norm_inner_mpvState_right_uncleTwoWallTrialSource_le_geometric
    (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (L : Fin d → Matrix (Fin b) (Fin a) ℂ)
    (hB : Kraus.mapLM B 1 = 1) (hSpect : Kraus.mixedMapSpectralRadius A B < 1) :
    ∃ C z : ℝ, 0 < C ∧ 0 < z ∧ z < 1 ∧ ∀ N : ℕ, 0 < N →
      ‖⟪mpvState B (6 * N + 1),
        (WithLp.linearEquiv 2 ℂ (NSiteSpace d (6 * N + 1))).symm
          (uncleTwoWallTrialSource A B R L N)⟫_ℂ‖ ≤ C * z ^ N := by
  obtain ⟨C, r, hC, hr, hr1, hbound⟩ :=
    norm_inner_mpvState_right_uncleTwoWallTrialSource_le_geometric_mul A B R L hB hSpect
  obtain ⟨D, z, hD, hz, hz1, habsorb⟩ := absorb_quadratic_geometric hr hr1
  refine ⟨C * D, z, mul_pos hC hD, hz, hz1, fun N hN ↦ ?_⟩
  calc
    _ ≤ C * (N : ℝ) ^ 2 * r ^ N := hbound N hN
    _ = C * ((N : ℝ) ^ 2 * r ^ N) := mul_assoc _ _ _
    _ ≤ C * (D * z ^ N) := mul_le_mul_of_nonneg_left (habsorb N) hC.le
    _ = (C * D) * z ^ N := (mul_assoc _ _ _).symm

/-- The actual A-sector overlap tends to zero along the numbered source
trial, as a consequence of the derived geometric estimate.
Source: arXiv:1210.6613, Lemma lowenergystates, item 2. -/
theorem inner_mpvState_left_uncleTwoWallTrialSource_tendsto_zero
    (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (L : Fin d → Matrix (Fin b) (Fin a) ℂ)
    (hA : Kraus.mapLM A 1 = 1) (hSpect : Kraus.mixedMapSpectralRadius B A < 1) :
    Filter.Tendsto (fun N : ℕ ↦ ⟪mpvState A (6 * N + 1),
      (WithLp.linearEquiv 2 ℂ (NSiteSpace d (6 * N + 1))).symm
        (uncleTwoWallTrialSource A B R L N)⟫_ℂ) Filter.atTop (nhds 0) := by
  obtain ⟨C, z, _, hz, hz1, hbound⟩ :=
    norm_inner_mpvState_left_uncleTwoWallTrialSource_le_geometric A B R L hA hSpect
  apply squeeze_zero_norm' (a := fun N : ℕ ↦ C * z ^ N)
  · exact Filter.eventually_atTop.mpr ⟨1, fun N hN ↦ hbound N (by omega)⟩
  · simpa only [mul_zero] using tendsto_const_nhds.mul
      (tendsto_pow_atTop_nhds_zero_of_lt_one hz.le hz1)

/-- The actual B-sector overlap tends to zero along the numbered source
trial, without supplying an orthogonality hypothesis.
Source: arXiv:1210.6613, Lemma lowenergystates, item 2. -/
theorem inner_mpvState_right_uncleTwoWallTrialSource_tendsto_zero
    (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (L : Fin d → Matrix (Fin b) (Fin a) ℂ)
    (hB : Kraus.mapLM B 1 = 1) (hSpect : Kraus.mixedMapSpectralRadius A B < 1) :
    Filter.Tendsto (fun N : ℕ ↦ ⟪mpvState B (6 * N + 1),
      (WithLp.linearEquiv 2 ℂ (NSiteSpace d (6 * N + 1))).symm
        (uncleTwoWallTrialSource A B R L N)⟫_ℂ) Filter.atTop (nhds 0) := by
  obtain ⟨C, z, _, hz, hz1, hbound⟩ :=
    norm_inner_mpvState_right_uncleTwoWallTrialSource_le_geometric A B R L hB hSpect
  apply squeeze_zero_norm' (a := fun N : ℕ ↦ C * z ^ N)
  · exact Filter.eventually_atTop.mpr ⟨1, fun N hN ↦ hbound N (by omega)⟩
  · simpa only [mul_zero] using tendsto_const_nhds.mul
      (tendsto_pow_atTop_nhds_zero_of_lt_one hz.le hz1)

end OperatorNorm

end MPSTensor
