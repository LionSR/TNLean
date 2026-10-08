/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.MatrixReindexGap
import TNLean.MPS.ParentHamiltonian.BlockedInteractionWindow
import TNLean.MPS.ParentHamiltonian.BlockedGroundSpaceTransport
import TNLean.MPS.ParentHamiltonian.Martingale.PositiveComparisonGap

/-!
# Positive interactions on a regrouped chain

For an interaction of range \(R>0\), group \(L>0\) original sites into
one site. The coarse interaction on \(K>0\) grouped sites is the open
original interaction sum on \(KL\) sites, expressed in blocked coordinates.
Its open Hamiltonian decodes to the sum of all original terms inside the
length-\(KL\) windows whose starts are multiples of \(L\).

If \(R+L\leq KL+1\) and \(N\geq K\), these windows cover every original
interaction term on \(NL\) sites. Positivity then gives
\[
 H_h(NL)\leq \mathcal R(H_{h_B}(N))
 \leq (KL-R+1)H_h(NL).
\]
In particular, the two operators have exactly the same kernel. An eventual
original MPS-kernel identity therefore persists under blocking, after the
explicit transport of ground spaces.

Source: Nachtergaele, arXiv:cond-mat/9410110, Section 3, equations
(3.12)--(3.14), lines 1547--1570. These are derived regrouping and positive
counting statements for arbitrary positive interactions, requiring no local
MPS-kernel condition. The blocking and comparison results assume positive
physical dimension; the definition and local positivity certificate do not.
No normality, primitivity, or translation-invariance hypothesis is imposed.
-/

open scoped ComplexOrder MatrixOrder
namespace MPSTensor
variable {d R L K N : ℕ}

private theorem aligned_window_cover_bounds (hL : 0 < L)
    (hK : K ≤ N) (hcover : R + L ≤ K * L + 1) {s : ℕ} (hs : s + R ≤ N * L) :
    let i := min (s / L) (N - K)
    i < N + 1 - K ∧ s - i * L < K * L + 1 - R ∧ s = i * L + (s - i * L) := by
  let i := min (s / L) (N - K)
  have hi : i * L ≤ s := (Nat.mul_le_mul_right L (min_le_left _ _)).trans
    (Nat.div_mul_le_self s L)
  change i < N + 1 - K ∧ s - i * L < K * L + 1 - R ∧ s = i * L + (s - i * L)
  refine ⟨?_, ?_, by omega⟩
  · have hiN : i ≤ N - K := min_le_right _ _
    omega
  · by_cases hq : s / L ≤ N - K
    · simp only [i, min_eq_left hq]
      have hmod := Nat.mod_lt s hL
      have hsplit := Nat.mod_add_div s L
      rw [Nat.mul_comm L] at hsplit
      omega
    · simp only [i, min_eq_right (le_of_not_ge hq)]
      have hsplit : (N - K) * L + K * L = N * L := by
        rw [← Nat.add_mul, Nat.sub_add_cancel hK]
      omega

/-- The coarse interaction is the original open sum on \(KL\) sites,
expressed on \(K\) blocked sites. Source: the regrouping convention of
Nachtergaele, arXiv:cond-mat/9410110, Section 3, equations (3.12)--(3.14). -/
noncomputable def blockedInteractionMatrix (h : Matrix (Cfg d R) (Cfg d R) ℂ)
    (L K : ℕ) : Matrix (Cfg (blockPhysDim d L) K) (Cfg (blockPhysDim d L) K) ℂ :=
  Matrix.reindex (blockedConfigEquiv d K L).symm (blockedConfigEquiv d K L).symm
    (openInteractionMatrix h (K * L))

/-- Decoding the coarse interaction recovers its defining original open
sum. Source: Nachtergaele, arXiv:cond-mat/9410110, Section 3,
equations (3.12)--(3.14). -/
@[simp] theorem reindex_blockedInteractionMatrix (h : Matrix (Cfg d R) (Cfg d R) ℂ)
    (L K : ℕ) :
    Matrix.reindex (blockedConfigEquiv d K L) (blockedConfigEquiv d K L)
      (blockedInteractionMatrix h L K) = openInteractionMatrix h (K * L) := by
  exact (Matrix.reindex (blockedConfigEquiv d K L) (blockedConfigEquiv d K L)).apply_symm_apply _

private theorem chainWindowOperator_openInteractionMatrix {W n b : ℕ}
    (h : Matrix (Cfg d R) (Cfg d R) ℂ) (hR : 0 < R) (hRW : R ≤ W) (hb : b + W ≤ n) :
    chainWindowOperator n b (openInteractionMatrix h W) =
      ∑ j ∈ Finset.range (W + 1 - R), chainWindowOperator n (b + j) h := by
  rw [chainWindowOperator_eq_embedLocalOperatorAlgHom (by omega) hb,
    openInteractionMatrix, map_sum]
  simp only [← chainWindowOperator_eq_embedLocalOperatorAlgHom (by omega : b < n) hb]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' := Finset.mem_range.mp hj
  exact chainWindowOperator_chainWindowOperator (by omega) hb (by omega) (by omega) h


private theorem chainWindowOperator_posSemidef (h : Matrix (Cfg d R) (Cfg d R) ℂ)
    (hh : h.PosSemidef) (hR : 0 < R) {n b : ℕ} (hb : b + R ≤ n) :
    (chainWindowOperator n b h).PosSemidef := by
  rw [chainWindowOperator_eq_embedLocalOperatorAlgHom (by omega) hb]
  exact Matrix.nonneg_iff_posSemidef.mp
    (map_nonneg (chainWindowStarAlgHom R n b (by omega) hb) hh.nonneg)

/-- A positive local interaction gives a positive open interaction sum at
every volume, including volumes shorter than its range. Source:
Nachtergaele, arXiv:cond-mat/9410110, equation (3.12). -/
theorem openInteractionMatrix_posSemidef (h : Matrix (Cfg d R) (Cfg d R) ℂ)
    (hh : h.PosSemidef) (hR : 0 < R) (n : ℕ) : (openInteractionMatrix h n).PosSemidef := by
  rw [openInteractionMatrix]
  exact Matrix.nonneg_iff_posSemidef.mp (Finset.sum_nonneg fun b hb =>
    (chainWindowOperator_posSemidef h hh hR (by
      have hb' := Finset.mem_range.mp hb
      omega)).nonneg)

/-- Positive original interactions give positive coarse interactions,
including coarse windows shorter than the original range. Source:
Nachtergaele, arXiv:cond-mat/9410110, equation (3.12), positivity of its sums. -/
theorem blockedInteractionMatrix_posSemidef (h : Matrix (Cfg d R) (Cfg d R) ℂ)
    (hh : h.PosSemidef) (hR : 0 < R) (L K : ℕ) : (blockedInteractionMatrix h L K).PosSemidef :=
  (openInteractionMatrix_posSemidef h hh hR (K * L)).submatrix (blockedConfigEquiv d K L)

variable [NeZero d] [NeZero L]

/-- The decoded coarse open sum is the sum over aligned coarse starts and
all internal original starts. Source: a regrouping identity for
Nachtergaele, arXiv:cond-mat/9410110, equation (3.12). -/
theorem openInteractionMatrix_blockedInteractionMatrix_reindex
    (h : Matrix (Cfg d R) (Cfg d R) ℂ) (hR : 0 < R) (hK : 0 < K)
    (hRW : R ≤ K * L) (hKN : K ≤ N) :
    Matrix.reindex (blockedConfigEquiv d N L) (blockedConfigEquiv d N L)
      (openInteractionMatrix (blockedInteractionMatrix h L K) N) =
      ∑ i ∈ Finset.range (N + 1 - K), ∑ j ∈ Finset.range (K * L + 1 - R),
        chainWindowOperator (N * L) (i * L + j) h := by
  rw [openInteractionMatrix_blocking_reindex _ hK, reindex_blockedInteractionMatrix]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i + K ≤ N := by
    have hi'' := Finset.mem_range.mp hi
    omega
  exact chainWindowOperator_openInteractionMatrix h hR hRW
    (by simpa only [Nat.add_mul] using Nat.mul_le_mul_right L hi')


omit [NeZero d] in
private theorem sum_aligned_windows_le (h : Matrix (Cfg d R) (Cfg d R) ℂ)
    (hh : h.PosSemidef) (hR : 0 < R) :
    (∑ i ∈ Finset.range (N + 1 - K), ∑ j ∈ Finset.range (K * L + 1 - R),
      chainWindowOperator (N * L) (i * L + j) h) ≤
      ((K * L + 1 - R : ℕ) : ℂ) • openInteractionMatrix h (N * L) := by
  rw [Finset.sum_comm]
  calc
    _ ≤ ∑ j ∈ Finset.range (K * L + 1 - R), openInteractionMatrix h (N * L) := by
      refine Finset.sum_le_sum fun j hj => ?_
      rw [openInteractionMatrix]
      refine Finset.sum_le_sum_of_injOn (fun i : ℕ => i * L + j) ?_ ?_
        (fun _ _ => le_rfl) ?_
      · intro i _ i' _ he
        exact mul_left_injective₀ (NeZero.ne L) (Nat.add_right_cancel he)
      · rintro a ha
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
        have hiN : i + K ≤ N := by
          have hi' := Finset.mem_range.mp hi
          omega
        have hscaled := Nat.mul_le_mul_right L hiN
        rw [Nat.add_mul] at hscaled
        have hj' := Finset.mem_range.mp hj
        exact Finset.mem_range.mpr (by omega)
      · intro a ha _
        exact (chainWindowOperator_posSemidef h hh hR (by
          have ha' := Finset.mem_range.mp ha
          omega)).nonneg
    _ = _ := by simp [Nat.cast_smul_eq_nsmul ℂ]


omit [NeZero d] in
private theorem openInteractionMatrix_le_sum_aligned_windows
    (h : Matrix (Cfg d R) (Cfg d R) ℂ) (hh : h.PosSemidef) (hR : 0 < R)
    (hKN : K ≤ N) (hcover : R + L ≤ K * L + 1) :
    openInteractionMatrix h (N * L) ≤
      ∑ i ∈ Finset.range (N + 1 - K), ∑ j ∈ Finset.range (K * L + 1 - R),
        chainWindowOperator (N * L) (i * L + j) h := by
  let f : ℕ → ℕ × ℕ := fun s =>
    (min (s / L) (N - K), s - min (s / L) (N - K) * L)
  have hf : ∀ s ∈ Finset.range (N * L + 1 - R),
      (f s).1 < N + 1 - K ∧ (f s).2 < K * L + 1 - R ∧
        s = (f s).1 * L + (f s).2 := by
    intro s hs
    exact aligned_window_cover_bounds (NeZero.pos L) hKN hcover (by
      have hs' := Finset.mem_range.mp hs
      omega)
  rw [openInteractionMatrix, ← Finset.sum_product _ _
    (fun q : ℕ × ℕ => chainWindowOperator (N * L) (q.1 * L + q.2) h)]
  refine Finset.sum_le_sum_of_injOn f ?_ ?_ ?_ ?_
  · intro s hs t ht he
    exact (hf s hs).2.2.trans
      ((congrArg (fun q : ℕ × ℕ => q.1 * L + q.2) he).trans (hf t ht).2.2.symm)
  · rintro q hq
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hq
    exact Finset.mem_product.mpr
      ⟨Finset.mem_range.mpr (hf s hs).1, Finset.mem_range.mpr (hf s hs).2.1⟩
  · intro s hs
    exact le_of_eq (congrArg (fun j => chainWindowOperator (N * L) j h) (hf s hs).2.2)
  · intro q hq _
    obtain ⟨hi, hj⟩ := Finset.mem_product.mp hq
    have hiN : q.1 + K ≤ N := by
      have hi' := Finset.mem_range.mp hi
      omega
    have hscaled := Nat.mul_le_mul_right L hiN
    rw [Nat.add_mul] at hscaled
    have hj' := Finset.mem_range.mp hj
    exact (chainWindowOperator_posSemidef h hh hR (by omega)).nonneg


/-- Covering every original term gives two-sided positive comparison,
with upper multiplicity \(KL-R+1\), independent of volume.
Source: a positive-term counting form of Nachtergaele,
arXiv:cond-mat/9410110, Section 3, equations (3.12)--(3.14). -/
theorem openInteractionMatrix_blockedInteractionMatrix_comparison
    (h : Matrix (Cfg d R) (Cfg d R) ℂ) (hh : h.PosSemidef) (hR : 0 < R)
    (hK : 0 < K) (hKN : K ≤ N) (hcover : R + L ≤ K * L + 1) :
    openInteractionMatrix h (N * L) ≤
        Matrix.reindex (blockedConfigEquiv d N L) (blockedConfigEquiv d N L)
          (openInteractionMatrix (blockedInteractionMatrix h L K) N) ∧
      Matrix.reindex (blockedConfigEquiv d N L) (blockedConfigEquiv d N L)
          (openInteractionMatrix (blockedInteractionMatrix h L K) N) ≤
        ((K * L + 1 - R : ℕ) : ℂ) • openInteractionMatrix h (N * L) := by
  rw [openInteractionMatrix_blockedInteractionMatrix_reindex h hR hK
    (by have hL := NeZero.pos L; omega) hKN]
  exact ⟨openInteractionMatrix_le_sum_aligned_windows h hh hR hKN hcover,
    sum_aligned_windows_le h hh hR⟩

/-- The coarse and original open Hamiltonians have the same kernel after
configuration decoding. Source: the positive comparison mechanism of
Nachtergaele, arXiv:cond-mat/9410110, Section 3, equations (3.13)--(3.14). -/
theorem ker_toEuclideanLin_openInteractionMatrix_blockedInteractionMatrix_reindex
    (h : Matrix (Cfg d R) (Cfg d R) ℂ) (hh : h.PosSemidef) (hR : 0 < R)
    (hK : 0 < K) (hKN : K ≤ N) (hcover : R + L ≤ K * L + 1) :
    LinearMap.ker (Matrix.toEuclideanLin
      (Matrix.reindex (blockedConfigEquiv d N L) (blockedConfigEquiv d N L)
        (openInteractionMatrix (blockedInteractionMatrix h L K) N))) =
      LinearMap.ker (Matrix.toEuclideanLin (openInteractionMatrix h (N * L))) := by
  obtain ⟨hLower, hUpper⟩ :=
    openInteractionMatrix_blockedInteractionMatrix_comparison h hh hR hK hKN hcover
  have hLower' : Matrix.toEuclideanLin (openInteractionMatrix h (N * L)) ≤
      Matrix.toEuclideanLin (Matrix.reindex (blockedConfigEquiv d N L)
        (blockedConfigEquiv d N L) (openInteractionMatrix (blockedInteractionMatrix h L K) N)) := by
    rw [LinearMap.le_def, ← map_sub, Matrix.isPositive_toEuclideanLin_iff]
    exact Matrix.le_iff.mp hLower
  have hUpper' : Matrix.toEuclideanLin (Matrix.reindex (blockedConfigEquiv d N L)
      (blockedConfigEquiv d N L) (openInteractionMatrix (blockedInteractionMatrix h L K) N)) ≤
      ((K * L + 1 - R : ℕ) : ℂ) • Matrix.toEuclideanLin (openInteractionMatrix h (N * L)) := by
    rw [← map_smul, LinearMap.le_def, ← map_sub, Matrix.isPositive_toEuclideanLin_iff]
    exact Matrix.le_iff.mp hUpper
  have hP := Matrix.isPositive_toEuclideanLin_iff.mpr
    (openInteractionMatrix_posSemidef h hh hR (N * L))
  have hQ := LinearMap.nonneg_iff_isPositive.mp
    ((LinearMap.nonneg_iff_isPositive.mpr hP).trans hLower')
  have hC : 0 < ((K * L + 1 - R : ℕ) : ℝ) := by
    have hL := NeZero.pos L
    exact_mod_cast (show 0 < K * L + 1 - R by omega)
  exact (hP.ker_eq_of_smul_le_of_le_smul hQ zero_lt_one zero_lt_one hC
    (by simpa only [Complex.ofReal_one, one_smul] using hLower')
    (by simpa using hUpper')).symm


/-- Eventual exact original MPS kernels persist for the decoded coarse
Hamiltonian, with the blocked ground space transported by the canonical
configuration isometry. Source: Nachtergaele, arXiv:cond-mat/9410110,
Theorem 1.2 and Section 3, equations (3.12)--(3.14). -/
theorem eventually_ker_blockedInteractionMatrix_reindex_eq_groundSpace
    {D : ℕ} (A : MPSTensor d D) (h : Matrix (Cfg d R) (Cfg d R) ℂ)
    (hh : h.PosSemidef) (hR : 0 < R) (hK : 0 < K)
    (hcover : R + L ≤ K * L + 1)
    (hker : ∀ᶠ n in Filter.atTop,
      LinearMap.ker (openInteractionHamiltonianES (Matrix.toEuclideanLin h) n) =
        groundSpaceES A n) :
    ∀ᶠ N in Filter.atTop, LinearMap.ker (Matrix.toEuclideanLin
      (Matrix.reindex (blockedConfigEquiv d N L) (blockedConfigEquiv d N L)
        (openInteractionMatrix (blockedInteractionMatrix h L K) N))) =
      (groundSpaceES (blockTensor A L) N).map
        (blockedConfigLinearIsometryEquiv d N L).toLinearEquiv.toLinearMap := by
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.1 hker
  filter_upwards [Filter.eventually_ge_atTop (max K M)] with N hN
  have hKN : K ≤ N := (le_max_left K M).trans hN
  have hRN : R ≤ N * L := by
    have hL := NeZero.pos L
    have hscaled := Nat.mul_le_mul_right L hKN
    omega
  rw [ker_toEuclideanLin_openInteractionMatrix_blockedInteractionMatrix_reindex
    h hh hR hK hKN hcover,
    ← openInteractionHamiltonianES_eq_toEuclideanLin_openInteractionMatrix h hR hRN,
    hM (N * L) ((le_max_right K M).trans (hN.trans (Nat.le_mul_of_pos_right N (NeZero.pos L))))]
  exact (groundSpaceES_blockTensor_map A L N).symm

/-- The configuration isometry maps the complete coarse open kernel onto
the original open kernel. Source: the regrouping and positive comparison
mechanism of Nachtergaele, arXiv:cond-mat/9410110,
Section 3, equations (3.12)--(3.14). -/
theorem ker_openInteractionHamiltonianES_blockedInteractionMatrix_map
    (h : Matrix (Cfg d R) (Cfg d R) ℂ) (hh : h.PosSemidef) (hR : 0 < R)
    (hK : 0 < K) (hKN : K ≤ N) (hcover : R + L ≤ K * L + 1) :
    (LinearMap.ker (openInteractionHamiltonianES
      (Matrix.toEuclideanLin (blockedInteractionMatrix h L K)) N)).map
      (blockedConfigLinearIsometryEquiv d N L).toLinearEquiv.toLinearMap =
      LinearMap.ker (openInteractionHamiltonianES (Matrix.toEuclideanLin h) (N * L)) := by
  have hRN : R ≤ N * L := by
    have hL := NeZero.pos L
    have hscaled := Nat.mul_le_mul_right L hKN
    omega
  rw [openInteractionHamiltonianES_eq_toEuclideanLin_openInteractionMatrix _ hK hKN,
    openInteractionHamiltonianES_eq_toEuclideanLin_openInteractionMatrix h hR hRN]
  exact (Matrix.ker_toEuclideanLin_reindex_map (blockedConfigEquiv d N L) _).trans
    (ker_toEuclideanLin_openInteractionMatrix_blockedInteractionMatrix_reindex
      h hh hR hK hKN hcover)

/-- An eventual exact MPS kernel for the original interaction gives the
exact blocked-tensor kernel for the coarse interaction at all sufficiently
large blocked volumes. Source: Nachtergaele, arXiv:cond-mat/9410110,
Theorem 1.2 and Section 3, equations (3.12)--(3.14). -/
theorem eventually_ker_openInteractionHamiltonianES_blockedInteractionMatrix_eq_groundSpaceES
    {D : ℕ} (A : MPSTensor d D) (h : Matrix (Cfg d R) (Cfg d R) ℂ)
    (hh : h.PosSemidef) (hR : 0 < R) (hK : 0 < K)
    (hcover : R + L ≤ K * L + 1)
    (hker : ∀ᶠ n in Filter.atTop,
      LinearMap.ker (openInteractionHamiltonianES (Matrix.toEuclideanLin h) n) =
        groundSpaceES A n) :
    ∀ᶠ N in Filter.atTop,
      LinearMap.ker (openInteractionHamiltonianES
        (Matrix.toEuclideanLin (blockedInteractionMatrix h L K)) N) =
          groundSpaceES (blockTensor A L) N := by
  filter_upwards [eventually_ker_blockedInteractionMatrix_reindex_eq_groundSpace
    A h hh hR hK hcover hker, Filter.eventually_ge_atTop K] with N hN hKN
  apply Submodule.map_injective_of_injective
    (blockedConfigLinearIsometryEquiv d N L).injective
  rw [openInteractionHamiltonianES_eq_toEuclideanLin_openInteractionMatrix _ hK hKN,
    blockedConfigLinearIsometryEquiv, Matrix.ker_toEuclideanLin_reindex_map]
  exact hN


end MPSTensor
