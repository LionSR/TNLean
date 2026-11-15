/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.ContinuousSupportFrames
import TNLean.MPS.MPU.GeneralIndexContinuity
import TNLean.MPS.MPU.SimpleSupportCompression

/-!
# Continuous reduced tensors in local support coordinates

For a continuous reduced projection `T`, local isometric frames `J` give the
continuous tensor `Jᴴ W J`. The source support absorptions `W P = W = Q W`
ensure that this tensor has exactly the positive-length periodic operators
of `W`, where `T` is the reduced projection of `P` and `Q`. Thus MPU
unitarity is preserved. Simplicity passes to these coordinates under the
existing rank-one transfer hypothesis. Continuous positive ambient matrices
compress to continuous positive definite matrices on the reduced range.

The transition between overlapping support frames is unitary, with the exact
covariance `Kᴴ W K = (Jᴴ K)ᴴ (Jᴴ W J) (Jᴴ K)`.

**Scope restriction (continuous reduced support):** Continuity of the actual
reduced projection is an explicit hypothesis. No continuity of support
projections follows just from continuity of positive semidefinite matrices.
The module does not choose continuous diagonalizing bases, source-cut SVDs,
or standard-form gates. It is an auxiliary part of #6024/#6140, not a proof
of the unrestricted source corollary. See
`docs/paper-gaps/mpu_canonical_form_full_support.tex`.

Source: arXiv:1703.09188, Proposition IV.5, lines 773–804, and
Corollary IV.7 (`coruvSF`), lines 867–950.
-/

open scoped Matrix Matrix.Norms.L2Operator

namespace MPOTensor

/-- Rectangular compression preserves continuity when the tensor and both
rectangular matrices vary continuously. Auxiliary to CPSV17, Proposition
IV.5, restriction to the reduced support, lines 773–804. -/
theorem continuous_rectangularSandwich
    {T : Type*} [TopologicalSpace T] {d D r : ℕ}
    {A : T → Matrix (Fin r) (Fin D) ℂ} {W : T → MPOTensor d D}
    {B : T → Matrix (Fin D) (Fin r) ℂ}
    (hA : Continuous A) (hW : Continuous W) (hB : Continuous B) :
    Continuous (fun t i j => A t * W t i j * B t : T → MPOTensor d r) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  exact (hA.matrix_mul ((continuous_apply j).comp
    ((continuous_apply i).comp hW))).matrix_mul hB

/-- Orthonormal coordinates on the actual reduced support preserve every
positive-length periodic operator. Source: CPSV17, Proposition IV.5,
lines 773–783. No equality at length zero is asserted. -/
theorem mpo_supportCoordinates_reducedProjection
    {d D r : ℕ} (W : MPOTensor d D)
    (P Q : Matrix (Fin D) (Fin D) ℂ) (hP : IsOrthogonalProjection P)
    (hWP : ∀ i j, W i j * P = W i j)
    (hQW : ∀ i j, Q * W i j = W i j)
    (J : Matrix (Fin D) (Fin r) ℂ) (hJ : J.IsIsometry)
    (hrange : J * Jᴴ = Matrix.reducedProjection P Q)
    (N : ℕ) (hN : 0 < N) :
    mpo (fun i j => Jᴴ * W i j * J) N = mpo W N := by
  let T := Matrix.reducedProjection P Q
  let M := virtualSandwich T W T
  have hTJ : T * J = J := by
    rw [← hrange, Matrix.mul_assoc, show Jᴴ * J = 1 from hJ, Matrix.mul_one]
  have hJT : Jᴴ * T = Jᴴ := by
    rw [← hrange, ← Matrix.mul_assoc, show Jᴴ * J = 1 from hJ, Matrix.one_mul]
  have hcompress : (fun i j => Jᴴ * W i j * J : MPOTensor d r) =
      (fun i j => Jᴴ * M i j * J) := by
    funext i j
    change Jᴴ * W i j * J = Jᴴ * (T * W i j * T) * J
    calc
      Jᴴ * W i j * J = (Jᴴ * T) * W i j * (T * J) := by rw [hJT, hTJ]
      _ = Jᴴ * (T * W i j * T) * J := by simp only [Matrix.mul_assoc]
  have habsorb : ∀ i j, M i j * (J * Jᴴ) = M i j := by
    intro i j
    change (T * W i j * T) * (J * Jᴴ) = T * W i j * T
    rw [hrange, Matrix.mul_assoc, (Matrix.reducedProjection_isOrthogonalProjection P Q).2]
  rw [hcompress, mpo_rectangularSandwich_of_absorb M Jᴴ J habsorb hN]
  exact mpo_virtualSandwich_reducedProjection_eq W P Q hP hWP hQW N

/-- Continuous reduced support gives continuous local reduced MPU tensors,
without assuming a frame family, a constant reduced dimension along the
entire path, or a continuous SVD. The local dimension is the rank at the
chosen base point. Auxiliary to CPSV17, Corollary IV.7 and Proposition IV.5. -/
theorem exists_local_continuous_reduced_support
    {T : Type*} [TopologicalSpace T] {d D : ℕ}
    (W : T → MPOTensor d D) (hW : Continuous W) (hMPU : ∀ t, IsMPU (W t))
    (P Q : T → Matrix (Fin D) (Fin D) ℂ)
    (hP : ∀ t, IsOrthogonalProjection (P t))
    (hWP : ∀ t i j, W t i j * P t = W t i j)
    (hQW : ∀ t i j, Q t * W t i j = W t i j)
    (hT : Continuous fun t => Matrix.reducedProjection (P t) (Q t)) (t₀ : T) :
    ∃ (r : ℕ) (S : Set T), IsOpen S ∧ t₀ ∈ S ∧
      ∃ (J : S → Matrix (Fin D) (Fin r) ℂ) (B : S → MPOTensor d r),
        Continuous J ∧ Continuous B ∧ ∀ t,
          (J t).IsIsometry ∧
          J t * (J t)ᴴ = Matrix.reducedProjection (P t) (Q t) ∧
          B t = (fun i j => (J t)ᴴ * W t i j * J t) ∧
          (∀ N, 0 < N → mpo (B t) N = mpo (W t) N) ∧ IsMPU (B t) := by
  obtain ⟨r, J₀, -, hJ₀, hbase⟩ :=
    (Matrix.reducedProjection_isOrthogonalProjection (P t₀) (Q t₀)).exists_support_isometry
  obtain ⟨S, hS, ht₀, hcont, -, hFrame⟩ :=
    Matrix.exists_local_continuous_support_frame
      (fun t => Matrix.reducedProjection (P t) (Q t)) hT
      (fun t => Matrix.reducedProjection_isOrthogonalProjection (P t) (Q t))
      t₀ J₀ hJ₀ hbase.symm
  let J : S → Matrix (Fin D) (Fin r) ℂ :=
    fun t => Matrix.polarIso (Matrix.reducedProjection (P t) (Q t) * J₀)
  have hJ : Continuous J := continuousOn_iff_continuous_domRestrict.mp hcont
  refine ⟨r, S, hS, ht₀, J, (fun t i j => (J t)ᴴ * W t i j * J t), hJ,
    continuous_rectangularSandwich hJ.matrix_conjTranspose
      (hW.comp continuous_subtype_val) hJ, ?_⟩
  intro t
  have hmpo : ∀ N, 0 < N →
      mpo (fun i j => (J t)ᴴ * W t i j * J t) N = mpo (W t) N :=
    fun N hN => mpo_supportCoordinates_reducedProjection (W t) (P t) (Q t)
      (hP t) (hWP t) (hQW t) (J t) (hFrame t t.property).1
      (hFrame t t.property).2 N hN
  refine ⟨(hFrame t t.property).1, (hFrame t t.property).2, rfl, hmpo, ?_⟩
  intro N hN
  rw [hmpo N (by omega)]
  exact hMPU t N hN

/-- Continuous positive ambient matrices compress to continuous positive
definite matrices in full reduced-support coordinates. Positivity uses
reduced-range transversality, not an assumed continuous eigenbasis.
Source: CPSV17, Proposition IV.5, lines 756 and 778–781. -/
theorem continuous_reduced_fixed_pair
    {T : Type*} [TopologicalSpace T] {D r : ℕ}
    (L R : T → Matrix (Fin D) (Fin D) ℂ)
    (hLcont : Continuous L) (hRcont : Continuous R)
    (hL : ∀ t, (L t).PosSemidef) (hR : ∀ t, (R t).PosSemidef)
    (J : T → Matrix (Fin D) (Fin r) ℂ) (hJcont : Continuous J)
    (hJ : ∀ t, (J t).IsIsometry)
    (hrange : ∀ t, J t * (J t)ᴴ =
      Matrix.reducedProjection (hL t).supportProj (hR t).supportProj) :
    Continuous (fun t => (J t)ᴴ * L t * J t) ∧
      Continuous (fun t => (J t)ᴴ * R t * J t) ∧
      ∀ t, ((J t)ᴴ * L t * J t).PosDef ∧ ((J t)ᴴ * R t * J t).PosDef := by
  refine ⟨(hJcont.matrix_conjTranspose.matrix_mul hLcont).matrix_mul hJcont,
    (hJcont.matrix_conjTranspose.matrix_mul hRcont).matrix_mul hJcont, ?_⟩
  intro t
  exact compressed_fixed_pair_posDef_reducedProjection (L t) (R t)
    (hL t).supportProj (hR t).supportProj (hL t) (hR t) rfl rfl
    (J t) (hJ t) (hrange t)

/-- Reduction to a full isometric support frame preserves simplicity under
the actual two support absorptions and the rank-one normalized transfer
matrix identity. Source: CPSV17, Proposition IV.5, lines 773–804. -/
theorem IsMPUSimple.supportCoordinates_reducedProjection
    {d D r : ℕ} [NeZero d] {W : MPOTensor d D} (hW : W.IsMPUSimple)
    (P Q : Matrix (Fin D) (Fin D) ℂ) (hP : IsOrthogonalProjection P)
    (hWP : ∀ i j, W i j * P = W i j)
    (hQW : ∀ i j, Q * W i j = W i j)
    (ρ Φ : Fin (D * D) → ℂ)
    (hE : normalizedDiagonal (doubleLayerTensor W) = Matrix.vecMulVec ρ Φ)
    (J : Matrix (Fin D) (Fin r) ℂ) (hJ : J.IsIsometry)
    (hrange : J * Jᴴ = Matrix.reducedProjection P Q) :
    IsMPUSimple (fun i j => Jᴴ * W i j * J) :=
  isMPUSimple_supportCoordinates W (Matrix.reducedProjection P Q) J hJ hrange
    (hW.reducedProjection P Q hP hWP hQW ρ Φ hE)

/-- Overlapping full support frames give unitarily conjugate reduced
tensors. Together with continuity of `Jᴴ K`, this supplies exact continuous
transition matrices without selecting singular vectors.
Auxiliary to CPSV17, Proposition IV.5 and Corollary IV.7. -/
theorem supportCoordinates_eq_unitary_conj
    {d D r : ℕ} (W : MPOTensor d D)
    (J K : Matrix (Fin D) (Fin r) ℂ) (hJ : J.IsIsometry) (hK : K.IsIsometry)
    (hrange : J * Jᴴ = K * Kᴴ) :
    Jᴴ * K ∈ Matrix.unitaryGroup (Fin r) ℂ ∧
      ∀ i j, Kᴴ * W i j * K =
        (Jᴴ * K)ᴴ * (Jᴴ * W i j * J) * (Jᴴ * K) := by
  obtain ⟨hunit, hJK⟩ := Matrix.support_frame_transition J K hJ hK hrange
  refine ⟨hunit, ?_⟩
  intro i j
  calc
    Kᴴ * W i j * K = (J * (Jᴴ * K))ᴴ * W i j * (J * (Jᴴ * K)) := by rw [hJK]
    _ = _ := by simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]

end MPOTensor
