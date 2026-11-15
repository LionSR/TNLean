/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Analysis.HermitianMatrixCone
import QICLean.Channel.ChoiJamiolkowski
import QICLean.Channel.KrausRank
import TNLean.Algebra.AnnihilatingPowerPerturbation
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Topology.Order.Compact

/-!
# Rank reduction at the boundary of a positive matrix pencil

A nonzero Hermitian trace-zero direction through a positive-definite
matrix reaches a singular positive-semidefinite matrix. Isometric
compression gives the same conclusion on a singular Choi face.
A supported annihilating direction therefore produces a channel of
smaller Choi rank with all powers from the square onward preserved.
This supplies the positivity step in the written cyclic root-selection
proofs associated with arXiv:1708.00029, Theorem 4.1. The direction and
its Choi-face coordinates remain explicit hypotheses.
-/

open scoped Matrix ComplexOrder Matrix.Norms.Frobenius Topology
open SemidefiniteProgram Topology

namespace Matrix

private theorem isCompact_posSemidef_trace_eq {D : ℕ}
    (A : Matrix (Fin D) (Fin D) ℂ) :
    IsCompact {B : Matrix (Fin D) (Fin D) ℂ | B.PosSemidef ∧ B.trace = A.trace} := by
  let _ : ProperSpace (Matrix (Fin D) (Fin D) ℂ) := FiniteDimensional.proper_rclike ℂ _
  apply Metric.isCompact_of_isClosed_isBounded
  · exact Matrix.posSemidef_is_closed.inter
      (isClosed_eq continuous_id.matrix_trace continuous_const)
  · exact (posSemidef_trace_bounded_isBounded (D := D) ‖A.trace‖).subset
      fun B hB => ⟨hB.1, (congrArg norm hB.2).le⟩

/-- A nonzero Hermitian trace-zero direction through a positive-definite
matrix meets the positive-semidefinite boundary with strictly smaller
rank. No trace-one normalization or nonzero-dimension assumption is
needed. This is the boundary step in the cyclic root-selection argument
for arXiv:1708.00029, Theorem 4.1, not a root selector by itself. -/
theorem exists_posSemidef_rank_lt_on_trace_zero_line {D : ℕ}
    {A H : Matrix (Fin D) (Fin D) ℂ} (hA : A.PosDef)
    (hH : H.IsHermitian) (hHne : H ≠ 0) (hTrace : H.trace = 0) :
    ∃ t : ℝ, t ≠ 0 ∧ (A + t • H).PosSemidef ∧
      (A + t • H).rank < A.rank := by
  classical
  let F : ℝ → Matrix (Fin D) (Fin D) ℂ := fun t => A + t • H
  let S : Set ℝ := {t | (F t).PosSemidef}
  have hF : IsClosedEmbedding F :=
    (Homeomorph.addLeft A).isClosedEmbedding.comp
      (isClosedEmbedding_smul_left (𝕜 := ℝ) hHne)
  have hTraceF (t : ℝ) : (F t).trace = A.trace := by
    simp only [F, Matrix.trace_add, Matrix.trace_smul, hTrace, smul_zero, add_zero]
  have hCompact : IsCompact S := by
    have h := hF.isCompact_preimage (isCompact_posSemidef_trace_eq A)
    have hEq : F ⁻¹' {B | B.PosSemidef ∧ B.trace = A.trace} = S := by
      ext t
      change ((F t).PosSemidef ∧ (F t).trace = A.trace) ↔ (F t).PosSemidef
      rw [hTraceF]
      simp
    rwa [hEq] at h
  have hZero : 0 ∈ S := by
    change (A + (0 : ℝ) • H).PosSemidef
    simpa only [zero_smul, add_zero] using hA.posSemidef
  obtain ⟨t, ht⟩ := hCompact.exists_isGreatest ⟨0, hZero⟩
  have hPSD : (F t).PosSemidef := ht.1
  have hBoundary : ¬ (F t).PosDef := by
    intro hPD
    let f : ℝ → HermitianMatrix (Fin D) := fun s =>
      HermitianMatrix.ofMatrix (Fin D) A hA.isHermitian +
        s • HermitianMatrix.ofMatrix (Fin D) H hH
    have hf : Continuous f := continuous_const.add (continuous_id.smul continuous_const)
    have hCompat (s : ℝ) : HermitianMatrix.toMatrix (Fin D) (f s) = F s := by
      simp only [f, F, HermitianMatrix.toMatrix_add, HermitianMatrix.toMatrix_smul,
        HermitianMatrix.toMatrix_ofMatrix]
      ext i j
      change A i j + (s : ℂ) * H i j = A i j + s • H i j
      exact congrArg (fun z : ℂ => A i j + z)
        (RCLike.real_smul_eq_coe_mul (K := ℂ) s (H i j)).symm
    have hPD' : (HermitianMatrix.toMatrix (Fin D) (f t)).PosDef := by
      rwa [hCompat]
    have hInterior :=
      (HermitianMatrix.mem_interior_psdCone_iff_posDef (Fin D) (f t)).mpr hPD'
    have hN := mem_interior_iff_mem_nhds.mp hInterior
    have hPull : f ⁻¹' (HermitianMatrix.psdCone (Fin D) : Set (HermitianMatrix (Fin D)))
        ∈ 𝓝 t := hf.continuousAt.preimage_mem_nhds hN
    obtain ⟨ε, hε, hBall⟩ := Metric.mem_nhds_iff.mp hPull
    have hNear : t + ε / 2 ∈ Metric.ball t ε := by
      rw [Metric.mem_ball, Real.dist_eq]
      rw [show t + ε / 2 - t = ε / 2 by ring, abs_of_pos (by linarith)]
      linarith
    have hRight : t + ε / 2 ∈ S := by
      have h := hBall hNear
      change (HermitianMatrix.toMatrix (Fin D) (f (t + ε / 2))).PosSemidef at h
      rwa [hCompat] at h
    have hLe : t + ε / 2 ≤ t := ht.2 hRight
    linarith
  have htne : t ≠ 0 := by
    intro h
    apply hBoundary
    simpa only [F, h, zero_smul, add_zero] using hA
  have hRankA : A.rank = D := by
    have hUnit : IsUnit A := hA.posSemidef.posDef_iff_isUnit.mp hA
    simpa only [Fintype.card_fin] using Matrix.rank_of_isUnit A hUnit
  have hRankNe : (F t).rank ≠ D := by
    intro hRank
    have hSurj : Function.Surjective (F t).mulVec :=
      Matrix.mulVec_surjective_iff_rank_eq_card.mpr (by simpa using hRank)
    exact hBoundary (hPSD.posDef_iff_isUnit.mpr
      (Matrix.mulVec_surjective_iff_isUnit.mp hSurj))
  have hRankLe := Matrix.rank_le_card_width (F t)
  simp only [Fintype.card_fin] at hRankLe
  refine ⟨t, htne, hPSD, ?_⟩
  change (F t).rank < A.rank
  omega

private theorem rank_isometric_congruence {α : Type*} [Fintype α]
    {r : ℕ} (V : Matrix α (Fin r) ℂ) (hV : Vᴴ * V = 1)
    (B : Matrix (Fin r) (Fin r) ℂ) : (V * B * Vᴴ).rank = B.rank := by
  have hRecover : Vᴴ * (V * B * Vᴴ) * V = B := by
    calc
      Vᴴ * (V * B * Vᴴ) * V = (Vᴴ * V) * B * (Vᴴ * V) := by
        simp only [Matrix.mul_assoc]
      _ = B := by rw [hV, Matrix.one_mul, Matrix.mul_one]
  apply le_antisymm
  · exact (Matrix.rank_mul_le_left (V * B) Vᴴ).trans (Matrix.rank_mul_le_right V B)
  · calc
      B.rank = (Vᴴ * (V * B * Vᴴ) * V).rank := congrArg Matrix.rank hRecover.symm
      _ ≤ (V * B * Vᴴ).rank :=
        (Matrix.rank_mul_le_left (Vᴴ * (V * B * Vᴴ)) V).trans
          (Matrix.rank_mul_le_right Vᴴ (V * B * Vᴴ))

/-- A trace-zero Hermitian direction inside an isometrically represented
positive face reaches a matrix of smaller rank. The ambient matrix may
be singular. The isometry and face coordinates are supplied explicitly;
this is the singular Choi-face boundary step for the cyclic selection
arguments associated with arXiv:1708.00029, Theorem 4.1. -/
theorem exists_posSemidef_rank_lt_on_isometric_face {D r : ℕ}
    (V : Matrix (Fin D) (Fin r) ℂ) (hV : Vᴴ * V = 1)
    {G J : Matrix (Fin r) (Fin r) ℂ} (hG : G.PosDef)
    (hJ : J.IsHermitian) (hJne : J ≠ 0) (hTrace : J.trace = 0) :
    ∃ t : ℝ, t ≠ 0 ∧
      (V * G * Vᴴ + t • (V * J * Vᴴ)).PosSemidef ∧
      (V * G * Vᴴ + t • (V * J * Vᴴ)).rank < (V * G * Vᴴ).rank := by
  obtain ⟨t, ht, hPSD, hRank⟩ :=
    exists_posSemidef_rank_lt_on_trace_zero_line hG hJ hJne hTrace
  have hExpand : V * (G + t • J) * Vᴴ = V * G * Vᴴ + t • (V * J * Vᴴ) := by
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]
  refine ⟨t, ht, ?_, ?_⟩
  · rw [← hExpand]
    exact hPSD.mul_mul_conjTranspose_same V
  · calc
      (V * G * Vᴴ + t • (V * J * Vᴴ)).rank = (G + t • J).rank := by
        rw [← hExpand]
        exact rank_isometric_congruence V hV _
      _ < G.rank := hRank
      _ = (V * G * Vᴴ).rank := (rank_isometric_congruence V hV G).symm

end Matrix

namespace Channel

/-- An annihilating direction supported inside a channel's Choi face gives
a channel with strictly smaller Choi rank and the same powers from the
square onward. The direction has zero output trace, and its face
coordinates are a nonzero Hermitian matrix. The isometry and both Choi
identities are explicit hypotheses. This proves the complete-positivity
step for such a direction in the root-selection argument associated with
arXiv:1708.00029, Theorem 4.1, without asserting that every root admits one. -/
theorem exists_channel_choiRank_lt_of_supported_annihilating_direction
    {D r : ℕ} [NeZero D]
    (F K : Module.End ℂ (Matrix (Fin D) (Fin D) ℂ)) (hF : IsChannel F)
    (hTrace : ∀ X, (K X).trace = 0)
    (hFK : F * K = 0) (hKF : K * F = 0) (hKK : K * K = 0)
    (V : Matrix (Fin D × Fin D) (Fin r) ℂ) (hV : Vᴴ * V = 1)
    (G J : Matrix (Fin r) (Fin r) ℂ) (hG : G.PosDef)
    (hJ : J.IsHermitian) (hJne : J ≠ 0)
    (hChoiF : ChoiJamiolkowski.choiMatrix F = V * G * Vᴴ)
    (hChoiK : ChoiJamiolkowski.choiMatrix K = V * J * Vᴴ) :
    ∃ t : ℝ, t ≠ 0 ∧ IsChannel (F + (t : ℂ) • K) ∧
      choiRank (F + (t : ℂ) • K) < choiRank F ∧
      (∀ p : ℕ, 2 ≤ p → (F + (t : ℂ) • K) ^ p = F ^ p) := by
  have hTP (c : ℂ) : IsTracePreservingMap (F + c • K) := by
    intro X
    simp only [LinearMap.add_apply, LinearMap.smul_apply, Matrix.trace_add,
      Matrix.trace_smul, hF.tp X, hTrace X, smul_zero, add_zero]
  have hTraceJ : J.trace = 0 := by
    have h := ChoiJamiolkowski.trace_choiMatrix_of_tp (NeZero.pos D)
      (F + (1 : ℂ) • K) (hTP 1)
    rw [one_smul, ChoiJamiolkowski.choiMatrix_add, Matrix.trace_add,
      ChoiJamiolkowski.trace_choiMatrix_of_tp (NeZero.pos D) F hF.tp,
      hChoiK, Matrix.trace_mul_cycle, hV, Matrix.one_mul] at h
    exact add_left_cancel (h.trans (add_zero (1 : ℂ)).symm)
  obtain ⟨t, ht, hPSD, hRank⟩ :=
    Matrix.exists_posSemidef_rank_lt_on_trace_zero_line hG hJ hJne hTraceJ
  have hChoi : ChoiJamiolkowski.choiMatrix (F + (t : ℂ) • K) =
      V * (G + t • J) * Vᴴ := by
    rw [ChoiJamiolkowski.choiMatrix_add, ChoiJamiolkowski.choiMatrix_smul,
      hChoiF, hChoiK]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
      Complex.coe_smul]
  have hChannel : IsChannel (F + (t : ℂ) • K) := by
    refine ⟨(ChoiJamiolkowski.cp_iff_choi_posSemidef _).mpr ?_, hTP _⟩
    rw [hChoi]
    exact hPSD.mul_mul_conjTranspose_same V
  refine ⟨t, ht, hChannel, ?_, ?_⟩
  · change (ChoiJamiolkowski.choiMatrix (F + (t : ℂ) • K)).rank <
      (ChoiJamiolkowski.choiMatrix F).rank
    rw [hChoi, hChoiF, Matrix.rank_isometric_congruence V hV,
      Matrix.rank_isometric_congruence V hV]
    exact hRank
  · intro p hp
    apply add_pow_eq_of_annihilating_square_zero (F := F) (H := (t : ℂ) • K) ?_ ?_ ?_ hp
    · rw [Algebra.mul_smul_comm, hFK, smul_zero]
    · rw [smul_mul_assoc, hKF, smul_zero]
    · rw [smul_mul_assoc, Algebra.mul_smul_comm, hKK, smul_zero, smul_zero]

end Channel
