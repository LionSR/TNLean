/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Channel.PSDConeAutomorphism.FaceDimension
import QICLean.Channel.FixedPoint.DirectSumBlockRetraction
import QICLean.Channel.LocalizedKrausCPTP
import QICLean.Channel.KrausRank
import QICLean.Channel.Semigroup.CPClosure
import TNLean.Algebra.MatrixRankReindex

/-!
# Rank under identity- and trace-preserving positive maps

A positive endomorphism preserving identity and trace cannot lower the rank
of a positive semidefinite matrix. Its action on a support projection is a
positive contraction in the output support corner, so comparing traces gives
the rank inequality. Amplification gives the corresponding Choi-rank bound
under postcomposition by a unital channel, even when that channel is singular.
These bounds support arXiv:1708.00029, Theorem 4.1, converse.
-/

open scoped Matrix ComplexOrder MatrixOrder BigOperators

namespace Matrix

private theorem posSemidef_of_hermitian_idempotent {D : ℕ}
    {P : Matrix (Fin D) (Fin D) ℂ} (hP : P.IsHermitian) (hIdem : P * P = P) :
    P.PosSemidef := by
  simpa only [hP.eq, Matrix.mul_one, hIdem] using
    (Matrix.PosSemidef.one.conjTranspose_mul_mul_same P)

private theorem rank_le_rank_map_of_unital_tracePreserving_fin {D : ℕ}
    {T : Module.End ℂ (Matrix (Fin D) (Fin D) ℂ)}
    (hT : IsPositiveMap T) (hTP : IsTracePreservingMap T) (hOne : T 1 = 1)
    {X : Matrix (Fin D) (Fin D) ℂ} (hX : X.PosSemidef) : X.rank ≤ (T X).rank := by
  classical
  let P := hX.supportProj
  have hP : P.PosSemidef :=
    posSemidef_of_hermitian_idempotent hX.supportProj_isHermitian hX.supportProj_idem
  have hComp : (1 - P).PosSemidef :=
    posSemidef_of_hermitian_idempotent hX.isHermitian.one_sub_supportProj_isHermitian
      hX.isHermitian.one_sub_supportProj_idem
  have hFace : P ∈ psdConeFace X := by
    apply (mem_psdConeFace_iff X P hX).mpr
    refine ⟨hP, ?_⟩
    change P * P * P = P
    rw [hX.supportProj_idem, hX.supportProj_idem]
  have hImageFace : T P ∈ psdConeFace (T X) := by
    obtain ⟨c, hc, hzero, hle⟩ := hFace
    refine ⟨c, hc, ?_, ?_⟩
    · simpa only [LinearMap.map_smul_of_tower, map_zero] using hT.map_le_map hzero
    · simpa only [LinearMap.map_smul_of_tower] using hT.map_le_map hle
  have hTX := hT X hX
  let Q := hTX.supportProj
  have hCorner : Q * T P * Q = T P :=
    ((mem_psdConeFace_iff (T X) (T P) hTX).mp hImageFace).2
  have hContraction : (1 - T P).PosSemidef := by
    simpa only [map_sub, hOne] using hT (1 - P) hComp
  have hDiff : (Q - T P).PosSemidef := by
    have h := hContraction.conjTranspose_mul_mul_same Q
    have hEq : Qᴴ * (1 - T P) * Q = Q - T P := by
      rw [hTX.supportProj_isHermitian.eq, Matrix.mul_sub, Matrix.sub_mul,
        Matrix.mul_one, hTX.supportProj_idem, hCorner]
    rwa [hEq] at h
  have hPTrace : P.trace = (X.rank : ℂ) := hX.supportProj_trace
  have hQTrace : Q.trace = ((T X).rank : ℂ) := hTX.supportProj_trace
  have hTrace := hDiff.trace_nonneg
  rw [Matrix.trace_sub, hQTrace, hTP P, hPTrace] at hTrace
  have hRe := (Complex.nonneg_iff.mp hTrace).1
  simp only [Complex.sub_re, Complex.natCast_re] at hRe
  exact_mod_cast (sub_nonneg.mp hRe)

/-- A positive matrix endomorphism preserving identity and trace cannot
lower the rank of a positive semidefinite input. No injectivity assumption
is needed. This is the rank comparison used for unital roots in the
converse of arXiv:1708.00029, Theorem 4.1. -/
theorem rank_le_rank_map_of_unital_tracePreserving
    {α : Type*} [Fintype α] [DecidableEq α]
    {T : Module.End ℂ (Matrix α α ℂ)}
    (hT : IsPositiveMap T) (hTP : IsTracePreservingMap T) (hOne : T 1 = 1)
    {X : Matrix α α ℂ} (hX : X.PosSemidef) : X.rank ≤ (T X).rank := by
  classical
  let e : α ≃ Fin (Fintype.card α) := Fintype.equivFin α
  apply rank_le_rank_map_of_reindexEndomorphism e T ?_ hX
  intro Y hY
  have hSOne : reindexEndomorphism e T 1 = 1 := by
    simp [reindexEndomorphism_apply, Matrix.reindex_apply, hOne]
  exact rank_le_rank_map_of_unital_tracePreserving_fin
    (Matrix.IsPositiveMap.reindexEndomorphism hT e)
    (Matrix.IsTracePreservingMap.reindexEndomorphism hTP e) hSOne hY

end Matrix

namespace Channel

private theorem tensorMapIdLM_one {D : ℕ}
    {F : Module.End ℂ (Matrix (Fin D) (Fin D) ℂ)} (hOne : F 1 = 1) :
    Matrix.tensorMapIdLM (δ := Fin D) F 1 = 1 := by
  simpa only [Matrix.tensorMapIdLM_apply, Matrix.one_kronecker_one, hOne] using
    Matrix.tensorMapId_kronecker F (1 : Matrix (Fin D) (Fin D) ℂ)
      (1 : Matrix (Fin D) (Fin D) ℂ)

/-- Postcomposition by a unital channel cannot lower the Choi rank of a
completely positive map. This includes singular postcomposing channels.
Source context: arXiv:1708.00029, Theorem 4.1, converse. -/
theorem choiRank_le_comp_of_unital {D : ℕ}
    {F G : Module.End ℂ (Matrix (Fin D) (Fin D) ℂ)}
    (hF : IsChannel F) (hOne : F 1 = 1) (hG : IsCPMap G) :
    choiRank G ≤ choiRank (F ∘ₗ G) := by
  by_cases hD : D = 0
  · subst D
    have hleft : ChoiRectangular.choiMatrix G = 0 := Subsingleton.elim _ _
    have hright : ChoiRectangular.choiMatrix (F ∘ₗ G) = 0 := Subsingleton.elim _ _
    simp [choiRank, hleft, hright]
  let : NeZero D := ⟨hD⟩
  have hGChoi : (ChoiJamiolkowski.choiMatrix G).PosSemidef :=
    (ChoiRectangular.isKrausCP_iff_choiMatrix_posSemidef (T := G)).mp hG
  have hFCPTP : IsKrausCPTP F :=
    isKrausCPTP_of_isKrausCP_trace_preserving hF.cp hF.tp
  have hAmp := Matrix.tensorMapIdLM_isKrausCPTP (δ := Fin D) hFCPTP
  have hRank := Matrix.rank_le_rank_map_of_unital_tracePreserving
    hAmp.isKrausCP.isPositiveMap hAmp.trace_map (tensorMapIdLM_one hOne) hGChoi
  change (ChoiJamiolkowski.choiMatrix G).rank ≤
    (ChoiJamiolkowski.choiMatrix (F ∘ₗ G)).rank
  exact hRank

/-- Every unital channel has Choi rank at most that of each positive
power. No injectivity or irreducibility assumption is needed. This bounds
unital roots in arXiv:1708.00029, Theorem 4.1, converse. -/
theorem choiRank_le_pow_of_unital {D : ℕ}
    {F : Module.End ℂ (Matrix (Fin D) (Fin D) ℂ)}
    (hF : IsChannel F) (hOne : F 1 = 1) {p : ℕ} (hp : 0 < p) :
    choiRank F ≤ choiRank (F ^ p) := by
  have hStep (n : ℕ) : choiRank (F ^ n) ≤ choiRank (F ^ (n + 1)) := by
    simpa only [pow_succ', Module.End.mul_eq_comp] using
      choiRank_le_comp_of_unital hF hOne (hF.cp.pow n)
  have hBound (n : ℕ) : choiRank F ≤ choiRank (F ^ (n + 1)) := by
    induction n with
    | zero => simp
    | succ n ih => exact ih.trans (hStep (n + 1))
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hp.ne'
  exact hBound n

end Channel
