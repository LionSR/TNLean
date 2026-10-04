/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.ContinuousSpectralCorner
import TNLean.MPS.Symmetry.ContinuousProjectionFrame

/-!
# Local spectral corners and prescribed isometric frames

A continuous Hermitian matrix family admits a separated spectral corner near
any positive semidefinite base value. Its rank is locally constant, and its
value at the base is the support projection. A prescribed isometric frame of
that support extends continuously to frames of the nearby spectral corners.

The construction selects the positive spectrum surviving from the base
matrix. Nearby matrices may have additional small positive eigenvalues.
Continuity of the Hermitian family is an explicit hypothesis. These are
finite-dimensional auxiliary results in the context of arXiv:1010.3732,
Appendix C, lines 2653–2717; no physical-gap conclusion is asserted.
-/

set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option linter.mathlibStandardSet true

open scoped Matrix Matrix.Norms.L2Operator ComplexOrder Topology
open Filter Set

namespace Matrix

/-- A strict gap in the real spectrum persists locally with weak endpoints,
by upper hemicontinuity of the finite-dimensional spectrum. -/
theorem eventually_spectral_separation_of_continuousAt
    {T n : Type*} [TopologicalSpace T] [Fintype n] [DecidableEq n]
    (A : T → Matrix n n ℂ) {t₀ : T} (hA : ContinuousAt A t₀)
    {a b : ℝ} (hgap : ∀ x ∈ spectrum ℝ (A t₀), x < a ∨ b < x) :
    ∀ᶠ t in 𝓝 t₀, ∀ x ∈ spectrum ℝ (A t), x ≤ a ∨ b ≤ x := by
  have hnear := ((upperHemicontinuous_spectrum ℝ (Matrix n n ℂ)).upperHemicontinuousAt
    (A t₀)).comp hA |>.forall_isOpen (Iio a ∪ Ioi b)
      (isOpen_Iio.union isOpen_Ioi) hgap
  filter_upwards [hnear] with t ht x hx
  exact (ht hx).imp le_of_lt le_of_lt

/-- The finite real spectrum admits positive cutoffs below every positive
spectral value. -/
theorem exists_positive_spectral_cutoffs {n : Type*} [Fintype n] [DecidableEq n]
    (B : Matrix n n ℂ) :
    ∃ a b : ℝ, 0 < a ∧ a < b ∧ ∀ x ∈ spectrum ℝ B, x ≤ 0 ∨ b < x := by
  have hclosed : IsClosed (spectrum ℝ B \ {0}) :=
    B.finite_real_spectrum.sdiff.isClosed
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp
    (hclosed.compl_mem_nhds (x := (0 : ℝ)) (by simp))
  refine ⟨ε / 3, 2 * ε / 3, by positivity, by linarith, ?_⟩
  intro x hx
  by_contra h
  have hxball : x ∈ Metric.ball (0 : ℝ) ε := by
    grind [Metric.mem_ball, Real.dist_eq, abs_lt]
  exact hball hxball ⟨hx, by grind⟩

/-- A cutoff below all positive spectral values recovers the support
projection of a positive semidefinite matrix. -/
theorem spectralCorner_eq_supportProj_of_nonzero_spectrum_separation
    {n : Type*} [Fintype n] [DecidableEq n]
    {B : Matrix n n ℂ} (hB : B.PosSemidef) {a b : ℝ}
    (ha : 0 < a) (hab : a < b)
    (hgap : ∀ x ∈ spectrum ℝ B, x ≤ 0 ∨ b ≤ x) :
    spectralCorner a b B = hB.supportProj := by
  rw [spectralCorner, hB.isHermitian.cfc_eq, IsHermitian.cfc,
    Unitary.conjStarAlgAut_apply, PosSemidef.supportProj, IsHermitian.supportProj]
  congr 2
  apply congrArg diagonal
  funext i
  have he := hgap _ (hB.isHermitian.eigenvalues_mem_spectrum_real i)
  have he0 := hB.eigenvalues_nonneg i
  rcases he with hlow | hhigh
  · simp only [Function.comp_apply, le_antisymm hlow he0,
      spectralCornerRamp_eq_zero_of_le hab ha.le, RCLike.ofReal_zero,
      ne_eq, not_true_eq_false, ite_false]
  · have hne : hB.isHermitian.eigenvalues i ≠ 0 :=
      ne_of_gt ((ha.trans hab).trans_le hhigh)
    simp only [Function.comp_apply, spectralCornerRamp_eq_one_of_le hab hhigh,
      RCLike.ofReal_one]
    change (1 : ℂ) = if hB.isHermitian.eigenvalues i ≠ 0 then 1 else 0
    exact (ite_eq_left hne).symm

/-- A continuous Hermitian family admits a spectral projection of constant
rank locally, whose base value is the support of the base matrix.
Source context: arXiv:1010.3732, Appendix C, lines 2653–2717. -/
theorem exists_open_constantRank_spectralCorner
    {T n : Type*} [TopologicalSpace T] [Fintype n] [DecidableEq n]
    (A : T → Matrix n n ℂ) (hA : Continuous A)
    (hHerm : ∀ t, (A t).IsHermitian) (t₀ : T) (hbase : (A t₀).PosSemidef) :
    ∃ a b : ℝ, ∃ S : Set T, 0 < a ∧ a < b ∧ IsOpen S ∧ t₀ ∈ S ∧
      spectralCorner a b (A t₀) = hbase.supportProj ∧
      ∀ t ∈ S, spectralCorner a b (A t) * spectralCorner a b (A t) =
        spectralCorner a b (A t) ∧
        (spectralCorner a b (A t)).rank = (spectralCorner a b (A t₀)).rank := by
  obtain ⟨a, b, ha, hab, hgap₀⟩ := exists_positive_spectral_cutoffs (A t₀)
  have hnear := eventually_spectral_separation_of_continuousAt A hA.continuousAt
    (fun x hx => (hgap₀ x hx).imp (fun h => h.trans_lt ha) id)
  obtain ⟨S, hSgap, hS, ht₀⟩ := mem_nhds_iff.mp hnear
  have hlocal := isLocallyConstant_rank_spectralCorner_family hab
    (fun t : S => A t) (hA.comp continuous_subtype_val)
    (fun t => hHerm t) (fun t => hSgap t.property)
  let R : Set S := {t | (spectralCorner a b (A t)).rank =
    (spectralCorner a b (A t₀)).rank}
  refine ⟨a, b, Subtype.val '' R, ha, hab,
    hS.isOpenMap_subtype_val R (hlocal.isOpen_fiber _),
    ⟨⟨t₀, ht₀⟩, rfl, rfl⟩,
    spectralCorner_eq_supportProj_of_nonzero_spectrum_separation hbase ha hab
      (fun x hx => (hgap₀ x hx).imp id le_of_lt), ?_⟩
  rintro t ⟨s, hs, rfl⟩
  exact ⟨spectralCorner_mul_self hab _ (hSgap s.property), hs⟩

/-- A prescribed isometric frame of the base support extends continuously
to frames of a separated spectral corner on an open neighborhood. The polar
construction preserves the base frame exactly.
Source context: arXiv:1010.3732, Appendix C, lines 2653–2717. -/
theorem exists_local_continuous_spectral_frame
    {T m n : Type*} [TopologicalSpace T]
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : T → Matrix m m ℂ) (hA : Continuous A)
    (hHerm : ∀ t, (A t).IsHermitian) (t₀ : T) (hbase : (A t₀).PosSemidef)
    (J₀ : Matrix m n ℂ) (hJ₀ : J₀.IsIsometry)
    (hsupport : hbase.supportProj = J₀ * J₀ᴴ) :
    ∃ a b : ℝ, ∃ S : Set T, 0 < a ∧ a < b ∧ IsOpen S ∧ t₀ ∈ S ∧
      ContinuousOn (fun t => polarIso (spectralCorner a b (A t) * J₀)) S ∧
      polarIso (spectralCorner a b (A t₀) * J₀) = J₀ ∧
      ∀ t ∈ S, (polarIso (spectralCorner a b (A t) * J₀)).IsIsometry ∧
        polarIso (spectralCorner a b (A t) * J₀) *
          (polarIso (spectralCorner a b (A t) * J₀))ᴴ = spectralCorner a b (A t) := by
  obtain ⟨a, b, S, ha, hab, hS, ht₀, hP₀, hP⟩ :=
    exists_open_constantRank_spectralCorner A hA hHerm t₀ hbase
  have hrank₀ : (spectralCorner a b (A t₀)).rank = Fintype.card n := by
    simpa only [hP₀, hsupport, rank_self_mul_conjTranspose] using hJ₀.rank_eq_card J₀
  obtain ⟨R, hR, ht₀R, hcont, hFrame⟩ :=
    exists_local_continuous_projection_frame
      (fun t : S => spectralCorner a b (A t))
      ((continuous_spectralCorner_family a b A hA hHerm).comp continuous_subtype_val)
      (fun t => isHermitian_spectralCorner a b (A t))
      (fun t => (hP t t.property).1)
      (fun t => (hP t t.property).2.trans hrank₀)
      ⟨t₀, ht₀⟩ J₀ hJ₀ (hP₀.trans hsupport)
  refine ⟨a, b, Subtype.val '' R, ha, hab,
    hS.isOpenMap_subtype_val R hR, ⟨⟨t₀, ht₀⟩, ht₀R, rfl⟩, ?_, ?_, ?_⟩
  · exact Topology.IsInducing.subtypeVal.continuousOn_image_iff.mpr hcont
  · refine polarIso_eq_of_eq_mul (Q := (1 : Matrix n n ℂ)) (E := 1) ?_
      PosSemidef.one hJ₀ isHermitian_one (one_mul _) rfl
    simp only [hP₀, hsupport, Matrix.mul_assoc,
      show J₀ᴴ * J₀ = 1 from hJ₀, Matrix.mul_one]
  · rintro t ⟨s, hs, rfl⟩
    exact hFrame s hs

/-- A positive spectral cutoff is contained in the support of a positive
semidefinite matrix. Spectral separation is not required for this inclusion.
Source context: arXiv:1010.3732, Appendix C, lines 2653–2717. -/
theorem supportProj_mul_spectralCorner
    {n : Type*} [Fintype n] [DecidableEq n]
    {σ : Matrix n n ℂ} (hσ : σ.PosSemidef) {a b : ℝ}
    (ha : 0 < a) (hab : a < b) :
    hσ.supportProj * spectralCorner a b σ = spectralCorner a b σ := by
  rw [spectralCorner, hσ.isHermitian.cfc_eq, IsHermitian.cfc,
    Unitary.conjStarAlgAut_apply, PosSemidef.supportProj, IsHermitian.supportProj]
  have hU : star (hσ.isHermitian.eigenvectorUnitary : Matrix n n ℂ) *
      (hσ.isHermitian.eigenvectorUnitary : Matrix n n ℂ) = 1 :=
    mem_unitaryGroup_iff'.mp hσ.isHermitian.eigenvectorUnitary.property
  simp only [Matrix.mul_assoc,
    ← Matrix.mul_assoc (star (hσ.isHermitian.eigenvectorUnitary : Matrix n n ℂ))
      (hσ.isHermitian.eigenvectorUnitary : Matrix n n ℂ), hU, Matrix.one_mul]
  have hdiag :
      (diagonal fun i => if hσ.isHermitian.eigenvalues i ≠ 0 then (1 : ℂ) else 0) *
        diagonal (RCLike.ofReal ∘ spectralCornerRamp a b ∘ hσ.isHermitian.eigenvalues) =
      diagonal (RCLike.ofReal ∘ spectralCornerRamp a b ∘ hσ.isHermitian.eigenvalues) := by
    rw [diagonal_mul_diagonal]
    apply congrArg diagonal
    funext i
    by_cases he : hσ.isHermitian.eigenvalues i = 0
    · simp only [Function.comp_apply, he, spectralCornerRamp_eq_zero_of_le hab ha.le,
        RCLike.ofReal_zero, mul_zero]
    · simp only [ite_eq_left he, one_mul]
  simpa only [Matrix.mul_assoc] using congrArg
    (fun M => (hσ.isHermitian.eigenvectorUnitary : Matrix n n ℂ) * M *
      star (hσ.isHermitian.eigenvectorUnitary : Matrix n n ℂ)) hdiag



end Matrix
