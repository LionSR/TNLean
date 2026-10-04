/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.ExactMPSGappedPhase
import TNLean.MPS.ParentHamiltonian.GroundSpaceMapContinuity

/-!
# Periodic ground-state lines under tensor limits

Equality of two nonzero limiting periodic lines follows from eventual line
equality along a convergent family. The proof passes the vanishing two by two
coordinate minors to the limit and uses a nonzero coordinate to recover the
scalar of proportionality. No choice of proportionality scalars is needed
along the family. Nonvanishing of both limiting vectors is essential.

This is an auxiliary limit result for the exact MPS families of
arXiv:1010.3732, Section II.F.2 and Appendix C, lines 2653–2717.
-/

set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option linter.mathlibStandardSet true
open scoped Topology
open Filter

private theorem span_singleton_eq_of_tendsto
    {X I : Type*} {l : Filter X} [NeBot l]
    (a b : X → I → ℂ) (v w : I → ℂ)
    (ha : Tendsto a l (𝓝 v)) (hb : Tendsto b l (𝓝 w))
    (hspan : ∀ᶠ x in l, Submodule.span ℂ {a x} = Submodule.span ℂ {b x})
    (hv : v ≠ 0) (hw : w ≠ 0) :
    Submodule.span ℂ {v} = Submodule.span ℂ {w} := by
  classical
  have hcross : ∀ i j, v i * w j = w i * v j := by
    intro i j
    have hevent : ∀ᶠ x in l, a x i * b x j = b x i * a x j := by
      filter_upwards [hspan] with x hx
      have hm : b x ∈ Submodule.span ℂ {a x} := by
        rw [hx]
        exact Submodule.mem_span_singleton_self _
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hm
      rw [← hc]
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    exact tendsto_nhds_unique_of_eventuallyEq
      ((tendsto_pi_nhds.mp ha i).mul (tendsto_pi_nhds.mp hb j))
      ((tendsto_pi_nhds.mp hb i).mul (tendsto_pi_nhds.mp ha j)) hevent
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra! h
    exact hv (funext h)
  let c : ℂ := w i / v i
  have hcw : c • v = w := by
    ext j
    simp only [Pi.smul_apply, smul_eq_mul, c]
    apply (div_mul_eq_mul_div ..).trans
    exact (div_eq_iff hi).mpr (by simpa only [mul_comm] using (hcross i j).symm)
  have hc : c ≠ 0 := by
    intro h
    apply hw
    rw [← hcw, h, zero_smul]
  rw [← hcw, Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr hc)]

/-- Nonzero limiting periodic vectors retain equality of their lines. The
nonvanishing requirement excludes collapse of a line to the zero vector. -/
theorem MPSTensor.mpv_span_eq_of_tendsto
    {X : Type*} {l : Filter X} [NeBot l] {d D E N : ℕ}
    (A : X → MPSTensor d D) (B : X → MPSTensor d E)
    (a : MPSTensor d D) (b : MPSTensor d E)
    (hA : Tendsto A l (𝓝 a)) (hB : Tendsto B l (𝓝 b))
    (hRay : ∀ᶠ x in l, Submodule.span ℂ {(mpv (A x) : (Fin N → Fin d) → ℂ)} =
      Submodule.span ℂ {(mpv (B x) : (Fin N → Fin d) → ℂ)})
    (ha : (mpv a : (Fin N → Fin d) → ℂ) ≠ 0)
    (hb : (mpv b : (Fin N → Fin d) → ℂ) ≠ 0) :
    Submodule.span ℂ {(mpv a : (Fin N → Fin d) → ℂ)} =
      Submodule.span ℂ {(mpv b : (Fin N → Fin d) → ℂ)} := by
  apply span_singleton_eq_of_tendsto _ _ _ _ ?_ ?_ hRay ha hb
  · apply tendsto_pi_nhds.mpr
    intro σ
    have h := (continuous_evalWord_family (D := D) id continuous_id (List.ofFn σ)).matrix_trace
    exact (h.tendsto a).comp hA
  · apply tendsto_pi_nhds.mpr
    intro σ
    have h := (continuous_evalWord_family (D := E) id continuous_id (List.ofFn σ)).matrix_trace
    exact (h.tendsto b).comp hB
