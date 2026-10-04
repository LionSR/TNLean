/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Algebra.SkolemNoether
import TNLean.MPS.Structure.FiniteRingTraceAlgebra
import TNLean.MPS.Symmetry.ExactMPSPhaseGaugeInvariance

/-!
# Reconstruction of injective tensors from two finite rings

The periodic vectors of a one-site injective tensor at lengths two and three
determine its positive-length periodic ray family. The two-site vector
identifies the kernel of the physical coefficient map and determines the
minimal bond dimension. The three-site vector recovers multiplication on
that quotient. A scalar normalization then gives an algebra isomorphism;
Skolem–Noether identifies it with a bond gauge.

The trace form used here is complex bilinear. It is not a Hermitian positive
form, and no positivity argument is used. Nonzero two- and three-site
proportionality constants give the tensor scalar `c₃ / c₂`. Zero-dimensional
matrix spaces are permitted; no scalar consistency identity is asserted in
that degenerate case.

These are finite-data consequences relevant to the extraction of tensor data
in arXiv:1010.3732, Section II.F.2, lines 953–993. Continuity of a canonical
realization through a changing minimal bond dimension remains a separate
problem; see `docs/paper-gaps/spc11_spt_interpolation_upper_range.tex`.
-/

set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option linter.mathlibStandardSet true

open scoped Matrix BigOperators

namespace MPSTensor

/-- Two- and three-site periodic trace rays determine an injective tensor up
to a nonzero scalar and a bond gauge. The scalar is the ratio of the
three-site and two-site normalization constants. The zero bond dimension
case is included, but no scalar consistency identity is asserted there.
This is a finite-data reconstruction consequence, not the unrestricted
phase classification. Source context: arXiv:1010.3732, Section II.F.2,
lines 953–993. -/
theorem gaugeEquiv_smul_of_two_three_trace_eq
    {d D : ℕ} {A B : MPSTensor d D}
    (hA : Kraus.IsInjective A) (hB : Kraus.IsInjective B)
    (c₂ c₃ : ℂ) (hc₂ : c₂ ≠ 0) (hc₃ : c₃ ≠ 0)
    (hpair : ∀ i j, Matrix.trace (B i * B j) = c₂ * Matrix.trace (A i * A j))
    (htriple : ∀ i j k, Matrix.trace (B i * B j * B k) =
      c₃ * Matrix.trace (A i * A j * A k)) :
    GaugeEquiv ((c₃ / c₂) • A) B := by
  rcases D.eq_zero_or_pos with rfl | hD
  · exact ⟨1, fun i => Subsingleton.elim _ _⟩
  let : NeZero D := ⟨Nat.ne_of_gt hD⟩
  obtain ⟨T, hT, -⟩ := linearExtension_exists_unique_of_twoSite_trace_eq hA hB c₂ hpair
  have hMul := linearExtension_mul_of_two_three_trace_eq hA hB c₂ c₃ hc₃ hpair htriple T hT
  let S := (c₂ / c₃) • T
  have hSMul : ∀ M N, S (M * N) = S M * S N := by
    intro M N
    simp only [S, LinearMap.smul_apply, hMul, Matrix.smul_mul,
      Matrix.mul_smul, smul_smul]
  have hTsurj : Function.Surjective T := by
    rw [← LinearMap.range_eq_top]
    apply eq_top_iff.mpr
    rw [← hB.span_eq_top]
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨i, rfl⟩
    exact ⟨A i, hT i⟩
  obtain ⟨X, hX⟩ := Matrix.exists_inner_of_linear_mul_endomorphism S hSMul
    (smul_ne_zero (div_ne_zero hc₂ hc₃) (LinearMap.ne_zero_of_surjective hTsurj))
  have hcancel : (c₃ / c₂) * (c₂ / c₃) = 1 := by field_simp
  refine ⟨X, fun i => ?_⟩
  have h := congrArg (fun M => (c₃ / c₂) • M) (hX (A i))
  simpa only [S, LinearMap.smul_apply, hT, smul_smul, hcancel, one_smul,
    Pi.smul_apply, Matrix.smul_mul, Matrix.mul_smul] using h

/-- Two- and three-site trace rays of injective tensors determine the periodic
ray at every positive length, even when their bond dimensions are initially
different. Nonzero proportionality constants are required; zero-dimensional
tensors are allowed. Auxiliary context: arXiv:1010.3732, Section II.F.2,
lines 953–993. -/
theorem samePositiveMpvRay_of_two_three_trace_eq
    {d D E : ℕ} {A : MPSTensor d D} {B : MPSTensor d E}
    (hA : Kraus.IsInjective A) (hB : Kraus.IsInjective B)
    (c₂ c₃ : ℂ) (hc₂ : c₂ ≠ 0) (hc₃ : c₃ ≠ 0)
    (hpair : ∀ i j, Matrix.trace (B i * B j) = c₂ * Matrix.trace (A i * A j))
    (htriple : ∀ i j k, Matrix.trace (B i * B j * B k) =
      c₃ * Matrix.trace (A i * A j * A k)) :
    SamePositiveMpvRay A B := by
  have hDE := bondDimension_eq_of_twoSite_trace_eq hA hB c₂ hc₂ hpair
  subst E
  exact samePositiveMpvRay_of_smul_gaugeEquiv (c₃ / c₂) (div_ne_zero hc₃ hc₂)
    (gaugeEquiv_smul_of_two_three_trace_eq hA hB c₂ c₃ hc₂ hc₃ hpair htriple)

/-- The periodic vectors of an injective tensor at lengths two and three
already determine its entire positive-length ray family. This is a
finite-ring reconstruction statement; it does not assert continuity of a
canonical realization through a changing bond dimension. Auxiliary context:
arXiv:1010.3732, Section II.F.2, lines 953–993. -/
theorem samePositiveMpvRay_of_mpv_two_three_eq_smul
    {d D E : ℕ} {A : MPSTensor d D} {B : MPSTensor d E}
    (hA : Kraus.IsInjective A) (hB : Kraus.IsInjective B)
    (c₂ c₃ : ℂ) (hc₂ : c₂ ≠ 0) (hc₃ : c₃ ≠ 0)
    (hpair : ∀ s : Fin 2 → Fin d, mpv B s = c₂ * mpv A s)
    (htriple : ∀ s : Fin 3 → Fin d, mpv B s = c₃ * mpv A s) :
    SamePositiveMpvRay A B := by
  apply samePositiveMpvRay_of_two_three_trace_eq hA hB c₂ c₃ hc₂ hc₃
  · intro i j
    simpa [mpv, coeff, Kraus.evalWord_cons, Kraus.evalWord_nil] using hpair ![i, j]
  · intro i j k
    simpa [mpv, coeff, Kraus.evalWord_cons, Kraus.evalWord_nil, Matrix.mul_assoc]
      using htriple ![i, j, k]

end MPSTensor
