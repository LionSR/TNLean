/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Algebra.PosSemidefSupport
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Continuity
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.LocallyConstant.Basic

/-!
# Continuous separated spectral corners

A fixed spectral cutoff separated from the spectra of a Hermitian matrix
family selects a continuous orthogonal projection. Operators commuting with
the original matrices preserve these projection ranges.

This is an auxiliary finite-dimensional construction in the context of
Schuch–Pérez-García–Cirac, arXiv:1010.3732, Appendix C, lines 2653–2717.
Spectral separation and density continuity are supplied explicitly; their
derivation from a physical gap and canonical MPS data remains open, as
recorded in `docs/paper-gaps/spc11_spt_interpolation_upper_range.tex`.
-/

open scoped Matrix Matrix.Norms.L2Operator Topology

namespace Matrix

/-- A continuous ramp which selects the high spectral component outside
the interval between two cutoffs. Source context: arXiv:1010.3732,
Appendix C, lines 2653–2717. -/
noncomputable def spectralCornerRamp (a b x : ℝ) : ℝ := min 1 (max 0 ((x - a) / (b - a)))

/-- Continuity of the cutoff ramp. Source context: arXiv:1010.3732,
Appendix C, lines 2653–2717. -/
theorem continuous_spectralCornerRamp (a b : ℝ) : Continuous (spectralCornerRamp a b) :=
  continuous_const.min (continuous_const.max ((continuous_id.sub continuous_const).div_const _))

/-- The cutoff ramp vanishes below its lower cutoff. Source context:
arXiv:1010.3732, Appendix C, lines 2653–2717. -/
theorem spectralCornerRamp_eq_zero_of_le {a b x : ℝ} (hab : a < b) (hx : x ≤ a) :
    spectralCornerRamp a b x = 0 := by
  have hratio : (x - a) / (b - a) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hx) (sub_nonneg.mpr hab.le)
  simp only [spectralCornerRamp, max_eq_left hratio, min_eq_right zero_le_one]

/-- The cutoff ramp equals one above its upper cutoff. Source context:
arXiv:1010.3732, Appendix C, lines 2653–2717. -/
theorem spectralCornerRamp_eq_one_of_le {a b x : ℝ} (hab : a < b) (hx : b ≤ x) :
    spectralCornerRamp a b x = 1 := by
  have hratio : 1 ≤ (x - a) / (b - a) :=
    (le_div_iff₀ (sub_pos.mpr hab)).mpr (by linarith)
  simp only [spectralCornerRamp, max_eq_right (zero_le_one.trans hratio), min_eq_left hratio]

/-- The spectral corner selected by a separated pair of cutoffs.
Source context: arXiv:1010.3732, Appendix C, lines 2653–2717. -/
noncomputable def spectralCorner {n : Type*} [Fintype n] [DecidableEq n]
    (a b : ℝ) (A : Matrix n n ℂ) : Matrix n n ℂ := cfc (spectralCornerRamp a b) A

/-- Real functional calculus makes the cutoff corner Hermitian. Source context:
arXiv:1010.3732, Appendix C, lines 2653–2717. -/
theorem isHermitian_spectralCorner {n : Type*} [Fintype n] [DecidableEq n]
    (a b : ℝ) (A : Matrix n n ℂ) :
    (spectralCorner a b A).IsHermitian :=
  IsSelfAdjoint.cfc (R := ℝ) (f := spectralCornerRamp a b)

/-- Spectral separation makes the cutoff corner idempotent. Source context:
arXiv:1010.3732, Appendix C, lines 2653–2717. -/
theorem spectralCorner_mul_self {n : Type*} [Fintype n] [DecidableEq n]
    {a b : ℝ} (hab : a < b) (A : Matrix n n ℂ)
    (hgap : ∀ x ∈ spectrum ℝ A, x ≤ a ∨ b ≤ x) :
    spectralCorner a b A * spectralCorner a b A = spectralCorner a b A := by
  rw [spectralCorner, ← cfc_mul _ _ A (continuous_spectralCornerRamp a b).continuousOn
    (continuous_spectralCornerRamp a b).continuousOn]
  apply cfc_congr
  intro x hx
  change spectralCornerRamp a b x * spectralCornerRamp a b x = spectralCornerRamp a b x
  rcases hgap x hx with hlow | hhigh
  · rw [spectralCornerRamp_eq_zero_of_le hab hlow, zero_mul]
  · rw [spectralCornerRamp_eq_one_of_le hab hhigh, one_mul]

/-- A continuous Hermitian family has a continuous cutoff corner.
Spectral separation is needed for idempotence, rather than continuity of
the ramp functional calculus. Source context: arXiv:1010.3732,
Appendix C, lines 2653–2717. -/
theorem continuous_spectralCorner_family
    {T n : Type*} [TopologicalSpace T] [Fintype n] [DecidableEq n]
    (a b : ℝ) (A : T → Matrix n n ℂ) (hA : Continuous A)
    (hHerm : ∀ t, (A t).IsHermitian) : Continuous fun t => spectralCorner a b (A t) :=
  Continuous.cfc_of_mem_nhdsSet (spectralCornerRamp a b) (s := Set.univ)
    (by simp) hA hHerm (continuous_spectralCornerRamp a b).continuousOn

/-- Under spectral separation the ramp calculus equals the high-spectrum
indicator calculus. Thus the continuous corner is precisely the projection
onto spectral values at or above the upper cutoff. Source context:
arXiv:1010.3732, Appendix C, lines 2653–2717. -/
theorem spectralCorner_eq_cfc_highIndicator
    {n : Type*} [Fintype n] [DecidableEq n]
    {a b : ℝ} (hab : a < b) (A : Matrix n n ℂ)
    (hgap : ∀ x ∈ spectrum ℝ A, x ≤ a ∨ b ≤ x) :
    spectralCorner a b A = cfc (fun x : ℝ => if b ≤ x then 1 else 0) A := by
  rw [spectralCorner]
  apply cfc_congr
  intro x hx
  change spectralCornerRamp a b x = if b ≤ x then 1 else 0
  rcases hgap x hx with hlow | hhigh
  · rw [spectralCornerRamp_eq_zero_of_le hab hlow, ite_eq_right (by linarith)]
  · rw [spectralCornerRamp_eq_one_of_le hab hhigh, ite_eq_left hhigh]

/-- An operator commuting with the original density also commutes with
the separated spectral corner. Source context: arXiv:1010.3732,
Appendix C, lines 2653–2717. -/
theorem commute_spectralCorner_of_commute
    {n : Type*} [Fintype n] [DecidableEq n]
    (a b : ℝ) (U A : Matrix n n ℂ) (hComm : Commute U A) :
    Commute U (spectralCorner a b A) :=
  (hComm.symm.cfc_real (spectralCornerRamp a b)).symm

/-- A unitary symmetry commuting with a density preserves its cutoff
corner under conjugation. Source context: arXiv:1010.3732,
Appendix C, lines 2653–2717. -/
theorem unitary_conj_spectralCorner_eq
    {n : Type*} [Fintype n] [DecidableEq n]
    (a b : ℝ) (U A : Matrix n n ℂ) (hU : U ∈ unitaryGroup n ℂ)
    (hComm : Commute U A) : U * spectralCorner a b A * Uᴴ = spectralCorner a b A := by
  have hUU : U * Uᴴ = 1 := by
    simpa only [star_eq_conjTranspose] using mem_unitaryGroup_iff.mp hU
  rw [(commute_spectralCorner_of_commute a b U A hComm).eq, Matrix.mul_assoc,
    hUU, Matrix.mul_one]

/-- The rank of a continuous orthogonal projection family is locally
constant, since rank equals its continuous real trace. Source context:
arXiv:1010.3732, Appendix C, lines 2653–2717. -/
theorem isLocallyConstant_rank_of_continuous_projection_family
    {T n : Type*} [TopologicalSpace T] [Fintype n]
    (P : T → Matrix n n ℂ) (hP : Continuous P)
    (hHerm : ∀ t, (P t).IsHermitian) (hid : ∀ t, P t * P t = P t) :
    IsLocallyConstant fun t => (P t).rank := by
  apply (IsLocallyConstant.iff_eventually_eq _).mpr
  intro t₀
  have hc := Complex.continuous_re.comp hP.matrix_trace
  have hnear : ∀ᶠ t in 𝓝 t₀, |(P t).trace.re - (P t₀).trace.re| < 1 :=
    ((hc.continuousAt.sub continuousAt_const).abs).eventually
      (Iio_mem_nhds (by simp))
  filter_upwards [hnear] with t ht
  rw [← (hHerm t).rank_eq_trace_re_of_idem (hid t),
    ← (hHerm t₀).rank_eq_trace_re_of_idem (hid t₀)] at ht
  have hlt : (P t).rank < (P t₀).rank + 1 := by
    exact_mod_cast (show ((P t).rank : ℝ) < (P t₀).rank + 1 by
      linarith [(abs_lt.mp ht).2])
  have hgt : (P t₀).rank < (P t).rank + 1 := by
    exact_mod_cast (show ((P t₀).rank : ℝ) < (P t).rank + 1 by
      linarith [(abs_lt.mp ht).1])
  omega

/-- A separated spectral corner has locally constant rank, even when the
rank of the underlying Hermitian density changes. Source context:
arXiv:1010.3732, Appendix C, lines 2653–2717. -/
theorem isLocallyConstant_rank_spectralCorner_family
    {T n : Type*} [TopologicalSpace T] [Fintype n] [DecidableEq n]
    {a b : ℝ} (hab : a < b) (A : T → Matrix n n ℂ) (hA : Continuous A)
    (hHerm : ∀ t, (A t).IsHermitian)
    (hgap : ∀ t, ∀ x ∈ spectrum ℝ (A t), x ≤ a ∨ b ≤ x) :
    IsLocallyConstant fun t => (spectralCorner a b (A t)).rank :=
  isLocallyConstant_rank_of_continuous_projection_family
    (fun t => spectralCorner a b (A t)) (continuous_spectralCorner_family a b A hA hHerm)
    (fun t => isHermitian_spectralCorner a b (A t))
    (fun t => spectralCorner_mul_self hab _ (hgap t))

end Matrix
