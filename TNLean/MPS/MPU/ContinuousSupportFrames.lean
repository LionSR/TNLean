/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.IdempotentRankContinuity
import TNLean.MPS.Symmetry.ContinuousProjectionFrame
import QICLean.Algebra.OrthogonalProjection

/-!
# Local unitary lifts of continuous support projections

Projecting a fixed orthonormal frame and taking its polar isometry gives a
local frame with the prescribed value at the base point. The rank is locally
constant because the projection is continuous; no rank hypothesis along the
family and no singular-value decomposition are supplied. Applying this to a
projection and its complement gives a local unitary conjugating the base
projection to the varying projection.

Two full orthonormal frames of the same support differ by the explicit
unitary `Jᴴ * K`. This also gives continuous transition matrices on overlaps.

These are auxiliary support-orbit results for arXiv:1703.09188, Proposition
IV.5, lines 773–804, and Corollary IV.7 (`coruvSF`), lines 867–950.
They concern a supplied continuous orthogonal projection family. They do not
derive that family from an arbitrary MPU path or lift the local tensor-product
gauge orbit of the standard-form gates. Those obligations remain in #6024 and
#6140; see `docs/paper-gaps/mpu_canonical_form_full_support.tex`.
-/

open scoped Matrix Matrix.Norms.L2Operator

namespace Matrix

/-- A continuous orthogonal projection has local full orthonormal frames
extending any prescribed base frame. The rank condition follows locally
from idempotence. Auxiliary to CPSV17, Proposition IV.5 and Corollary IV.7. -/
theorem exists_local_continuous_support_frame
    {T : Type*} [TopologicalSpace T] {D r : ℕ}
    (P : T → Matrix (Fin D) (Fin D) ℂ) (hP : Continuous P)
    (hproj : ∀ t, IsOrthogonalProjection (P t))
    (t₀ : T) (J₀ : Matrix (Fin D) (Fin r) ℂ)
    (hJ₀ : J₀.IsIsometry) (hbase : P t₀ = J₀ * J₀ᴴ) :
    ∃ S : Set T, IsOpen S ∧ t₀ ∈ S ∧
      ContinuousOn (fun t => polarIso (P t * J₀)) S ∧
      polarIso (P t₀ * J₀) = J₀ ∧
      ∀ t ∈ S, (polarIso (P t * J₀)).IsIsometry ∧
        polarIso (P t * J₀) * (polarIso (P t * J₀))ᴴ = P t := by
  obtain ⟨S, hS, ht₀, hrank⟩ :=
    exists_open_constantRank_of_idempotent P hP (fun t => (hproj t).2) t₀
  have hrank₀ : (P t₀).rank = Fintype.card (Fin r) := by
    simpa only [hbase, rank_self_mul_conjTranspose] using hJ₀.rank_eq_card J₀
  obtain ⟨R, hR, ht₀R, hcont, hFrame⟩ :=
    exists_local_continuous_projection_frame
      (fun t : S => P t) (hP.comp continuous_subtype_val)
      (fun t => (hproj t).1) (fun t => (hproj t).2)
      (fun t => (hrank t t.property).trans hrank₀) ⟨t₀, ht₀⟩ J₀ hJ₀ hbase
  refine ⟨Subtype.val '' R, hS.isOpenMap_subtype_val R hR,
    ⟨⟨t₀, ht₀⟩, ht₀R, rfl⟩,
    Topology.IsInducing.subtypeVal.continuousOn_image_iff.mpr hcont, ?_, ?_⟩
  · refine polarIso_eq_of_eq_mul (Q := (1 : Matrix (Fin r) (Fin r) ℂ)) (E := 1)
      ?_ PosSemidef.one hJ₀ isHermitian_one (one_mul _) rfl
    simp only [hbase, Matrix.mul_assoc, show J₀ᴴ * J₀ = 1 from hJ₀, Matrix.mul_one]
  · rintro t ⟨s, hs, rfl⟩
    exact hFrame s hs

/-- Full isometric frames of the same support are related by `Jᴴ K`, a
unitary matrix. Auxiliary coordinate change in CPSV17, Proposition IV.5,
lines 773–804. -/
theorem support_frame_transition
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (J K : Matrix m n ℂ) (hJ : J.IsIsometry) (hK : K.IsIsometry)
    (hrange : J * Jᴴ = K * Kᴴ) :
    Jᴴ * K ∈ unitaryGroup n ℂ ∧ J * (Jᴴ * K) = K := by
  classical
  constructor
  · rw [mem_unitaryGroup_iff, star_eq_conjTranspose, conjTranspose_mul,
      conjTranspose_conjTranspose]
    calc
      (Jᴴ * K) * (Kᴴ * J) = Jᴴ * (K * Kᴴ) * J := by
        simp only [Matrix.mul_assoc]
      _ = Jᴴ * (J * Jᴴ) * J := by rw [hrange]
      _ = 1 := by
        rw [← Matrix.mul_assoc, show Jᴴ * J = 1 from hJ, Matrix.one_mul, hJ]
  · rw [← Matrix.mul_assoc, hrange, Matrix.mul_assoc,
      show Kᴴ * K = 1 from hK, Matrix.mul_one]

/-- Changes between continuous support frames are continuous, without any
choice of spectral coordinates. Auxiliary to CPSV17, Corollary IV.7. -/
theorem continuous_support_frame_transition
    {T m n : Type*} [TopologicalSpace T] [Fintype m] [Fintype n]
    [DecidableEq n] {J K : T → Matrix m n ℂ}
    (hJ : Continuous J) (hK : Continuous K)
    (hJiso : ∀ t, (J t).IsIsometry) (hKiso : ∀ t, (K t).IsIsometry)
    (hrange : ∀ t, J t * (J t)ᴴ = K t * (K t)ᴴ) :
    Continuous (fun t => (J t)ᴴ * K t) ∧
      ∀ t, (J t)ᴴ * K t ∈ unitaryGroup n ℂ ∧
        J t * ((J t)ᴴ * K t) = K t :=
  ⟨hJ.matrix_conjTranspose.matrix_mul hK,
    fun t => support_frame_transition (J t) (K t) (hJiso t) (hKiso t) (hrange t)⟩

private theorem adjoint_mul_eq_zero_of_orthogonal_frames
    {D r s : ℕ} (J : Matrix (Fin D) (Fin r) ℂ)
    (K : Matrix (Fin D) (Fin s) ℂ) (hJ : J.IsIsometry) (hK : K.IsIsometry)
    (horth : (J * Jᴴ) * (K * Kᴴ) = 0) : Jᴴ * K = 0 := by
  have hleft : Jᴴ * (J * Jᴴ) = Jᴴ := by
    rw [← Matrix.mul_assoc, show Jᴴ * J = 1 from hJ, Matrix.one_mul]
  have hright : (K * Kᴴ) * K = K := by
    rw [Matrix.mul_assoc, show Kᴴ * K = 1 from hK, Matrix.mul_one]
  calc
    Jᴴ * K = (Jᴴ * (J * Jᴴ)) * ((K * Kᴴ) * K) := by rw [hleft, hright]
    _ = Jᴴ * ((J * Jᴴ) * (K * Kᴴ)) * K := by simp only [Matrix.mul_assoc]
    _ = 0 := by rw [horth, Matrix.mul_zero, Matrix.zero_mul]

/-- A continuous orthogonal projection family lifts locally to unitary
conjugations of the base projection, with the identity at the base point.
This is a support-orbit lift, not the tensor-product gate-orbit lift of
CPSV17, Corollary IV.7, lines 939–950. -/
theorem exists_local_continuous_support_unitary
    {T : Type*} [TopologicalSpace T] {D : ℕ}
    (P : T → Matrix (Fin D) (Fin D) ℂ) (hP : Continuous P)
    (hproj : ∀ t, IsOrthogonalProjection (P t)) (t₀ : T) :
    ∃ (S : Set T) (U : T → Matrix (Fin D) (Fin D) ℂ),
      IsOpen S ∧ t₀ ∈ S ∧ ContinuousOn U S ∧ U t₀ = 1 ∧
      ∀ t ∈ S, U t ∈ unitaryGroup (Fin D) ℂ ∧
        U t * P t₀ * (U t)ᴴ = P t := by
  obtain ⟨r, J₀, hJ₀, hJJ₀⟩ := (hproj t₀).exists_range_isometry
  obtain ⟨s, K₀, hK₀, hKK₀⟩ := (hproj t₀).one_sub.exists_range_isometry
  obtain ⟨S, hS, htS, hJcont, hJbase, hJ⟩ :=
    exists_local_continuous_support_frame P hP hproj t₀ J₀ hJ₀ hJJ₀.symm
  obtain ⟨R, hR, htR, hKcont, hKbase, hK⟩ :=
    exists_local_continuous_support_frame (fun t => 1 - P t)
      (continuous_const.sub hP) (fun t => (hproj t).one_sub)
      t₀ K₀ hK₀ hKK₀.symm
  let J := fun t => polarIso (P t * J₀)
  let K := fun t => polarIso ((1 - P t) * K₀)
  let U := fun t => J t * J₀ᴴ + K t * K₀ᴴ
  have horth : (J₀ * J₀ᴴ) * (K₀ * K₀ᴴ) = 0 := by
    rw [hJJ₀, hKK₀, Matrix.mul_sub, Matrix.mul_one, (hproj t₀).2, sub_self]
  have hJK := adjoint_mul_eq_zero_of_orthogonal_frames J₀ K₀ hJ₀ hK₀ horth
  have hKJ : K₀ᴴ * J₀ = 0 := by
    simpa only [conjTranspose_mul, conjTranspose_conjTranspose, conjTranspose_zero] using
      congrArg conjTranspose hJK
  have hUcont : ContinuousOn U (S ∩ R) := by
    rw [continuousOn_iff_continuous_domRestrict]
    have hJc : Continuous (fun t : S ∩ R => J t) :=
      continuousOn_iff_continuous_domRestrict.mp (hJcont.mono Set.inter_subset_left)
    have hKc : Continuous (fun t : S ∩ R => K t) :=
      continuousOn_iff_continuous_domRestrict.mp (hKcont.mono Set.inter_subset_right)
    exact (hJc.matrix_mul continuous_const).add (hKc.matrix_mul continuous_const)
  refine ⟨S ∩ R, U, hS.inter hR, ⟨htS, htR⟩, hUcont, ?_, ?_⟩
  · change polarIso (P t₀ * J₀) * J₀ᴴ + polarIso ((1 - P t₀) * K₀) * K₀ᴴ = 1
    rw [hJbase, hKbase, hJJ₀, hKK₀]
    abel
  · intro t ht
    have hJU : U t * J₀ = J t := by
      simp only [U, Matrix.add_mul, Matrix.mul_assoc, hJ₀, hKJ,
        Matrix.mul_one, Matrix.mul_zero, add_zero]
    refine ⟨?_, ?_⟩
    · rw [mem_unitaryGroup_iff, star_eq_conjTranspose]
      change (J t * J₀ᴴ + K t * K₀ᴴ) * (J t * J₀ᴴ + K t * K₀ᴴ)ᴴ = 1
      calc
        _ = (J t * (J₀ᴴ * J₀) * (J t)ᴴ +
            J t * (J₀ᴴ * K₀) * (K t)ᴴ) +
            (K t * (K₀ᴴ * J₀) * (J t)ᴴ +
              K t * (K₀ᴴ * K₀) * (K t)ᴴ) := by
          simp only [conjTranspose_add, conjTranspose_mul,
            conjTranspose_conjTranspose, Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc]
        _ = J t * (J t)ᴴ + K t * (K t)ᴴ := by
          rw [hJ₀, hK₀, hJK, hKJ]
          simp only [Matrix.mul_one, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
        _ = 1 := by
          rw [(hJ t ht.1).2, (hK t ht.2).2]
          abel
    · calc
        U t * P t₀ * (U t)ᴴ = (U t * J₀) * (U t * J₀)ᴴ := by
          rw [← hJJ₀, conjTranspose_mul]
          simp only [Matrix.mul_assoc]
        _ = P t := by rw [hJU, (hJ t ht.1).2]

end Matrix
