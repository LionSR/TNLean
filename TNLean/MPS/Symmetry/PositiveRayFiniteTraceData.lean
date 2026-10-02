/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.ExactMPSGappedPhase
import TNLean.MPS.FundamentalTheorem.InjectivePhase

/-!
# Nonzero two- and three-site trace normalizations

Equality of positive-length periodic rays with a one-site injective tensor of
positive bond dimension supplies nonzero proportionality constants at lengths
two and three. These finite trace data are auxiliary to arXiv:1010.3732,
Section II.F.2, lines 953–993; they do not by themselves reconstruct every
longer periodic ray of an arbitrary noninjective tensor.
-/

set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option linter.mathlibStandardSet true

open scoped Matrix

namespace MPSTensor

private theorem exists_nonzero_mpv_scalar_of_samePositiveMpvRay
    {d D E N : ℕ} [NeZero D] {A : MPSTensor d D} {B : MPSTensor d E}
    (hA : Kraus.IsInjective A) (hRay : SamePositiveMpvRay B A) (hN : 0 < N) :
    ∃ c : ℂ, c ≠ 0 ∧ ∀ σ : Fin N → Fin d, mpv B σ = c * mpv A σ := by
  obtain ⟨σ, hσ⟩ := exists_mpv_ne_zero_of_isInjective hA hN
  have hmemA : (mpv A : (Fin N → Fin d) → ℂ) ∈
      Submodule.span ℂ {(mpv B : (Fin N → Fin d) → ℂ)} :=
    hRay N hN ▸ Submodule.mem_span_singleton_self _
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hmemA
  have hmemB : (mpv B : (Fin N → Fin d) → ℂ) ∈
      Submodule.span ℂ {(mpv A : (Fin N → Fin d) → ℂ)} :=
    (hRay N hN).symm ▸ Submodule.mem_span_singleton_self _
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmemB
  refine ⟨c, ?_, fun τ => ?_⟩
  · intro hzero
    have hBzero : (mpv B : (Fin N → Fin d) → ℂ) = 0 := by
      simpa only [hzero, zero_smul] using hc.symm
    exact hσ (by simpa only [hBzero, smul_zero, Pi.zero_apply] using congrFun ha.symm σ)
  · exact (congrFun hc τ).symm

/-- Positive-length ray equality supplies the nonzero two- and three-site
normalizations used to recover the coefficient quotient and its product.
Source context: arXiv:1010.3732, Section II.F.2, lines 953–993. -/
theorem exists_nonzero_two_three_trace_scalars_of_samePositiveMpvRay
    {d D E : ℕ} [NeZero D] {A : MPSTensor d D} {B : MPSTensor d E}
    (hA : Kraus.IsInjective A) (hRay : SamePositiveMpvRay B A) :
    ∃ a₂ a₃ : ℂ, a₂ ≠ 0 ∧ a₃ ≠ 0 ∧
      (∀ i j, Matrix.trace (B i * B j) = a₂ * Matrix.trace (A i * A j)) ∧
      ∀ i j k, Matrix.trace (B i * B j * B k) =
        a₃ * Matrix.trace (A i * A j * A k) := by
  obtain ⟨a₂, ha₂, h₂⟩ := exists_nonzero_mpv_scalar_of_samePositiveMpvRay hA hRay
    (show 0 < 2 by omega)
  obtain ⟨a₃, ha₃, h₃⟩ := exists_nonzero_mpv_scalar_of_samePositiveMpvRay hA hRay
    (show 0 < 3 by omega)
  refine ⟨a₂, a₃, ha₂, ha₃, ?_, ?_⟩
  · intro i j
    simpa [mpv, coeff, Kraus.evalWord_cons, Kraus.evalWord_nil] using h₂ ![i, j]
  · intro i j k
    simpa [mpv, coeff, Kraus.evalWord_cons, Kraus.evalWord_nil, Matrix.mul_assoc]
      using h₃ ![i, j, k]

end MPSTensor

#print axioms MPSTensor.exists_nonzero_two_three_trace_scalars_of_samePositiveMpvRay
