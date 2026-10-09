/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Amplification.GraphChannelSpatialOmission
import TNLean.PEPS.AreaLaw.LatticeConstraints

/-!
# Expected spatial omission error for lattice positive-constraint channels

The actual positive constraints of a gapped lattice Hamiltonian supply the
effect tails and component support. The lattice counts supply quadratic ball
growth and anchor multiplicity, and finiteness supplies a common cutoff for
all original labels. Thus the expected full/retained channel-word error has
constants depending only on the filter parameter, interaction range, strength
and spectral gap, before the domain, local dimension and finite spectator.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`09-amplification.tex`, lines 139–215, with `03-quasilocal.tex`, lines 220–246,
and `01-preliminaries.tex`, lines 82–103, at revision
`openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Independently formalized from the manuscript; no upstream Lean text is reused.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option linter.mathlibStandardSet true

open QuantumCircuit SpectralFilter Matrix MeasureTheory
open scoped BigOperators ENNReal NNReal Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace TNLean.PEPS.AreaLaw

/-- Uniform expected omission error for the actual lattice positive-constraint
channels. The effect tails, physical kernel and growth, ball counts, anchor
fibers and finite cutoff are all derived. The support may be empty and the
observable need not be Hermitian. Source: area law, `09-amplification.tex`,
lines 139–215, and Proposition 4.3, `03-quasilocal.tex`, lines 220–246. -/
theorem exists_lattice_integrable_and_integral_channelWordOmissionDefect_le
    {p : ℕ} (hp : 1 ≤ p) (R : ℕ) {J Δ : ℝ} (hJ : 0 ≤ J) (hΔ : 0 < Δ) :
    ∃ D v γ : ℝ, 0 ≤ D ∧ 0 < v ∧ 0 < γ ∧
      ∀ {q : ℕ} [NeZero q] (Λ : Finset (ℤ × ℤ)) (h : LocalHamiltonian Λ q R J)
        (a : AdmissibleSupport Λ R → Site Λ), (∀ X, a X ∈ X.1) →
        ∀ (E₀ : ℝ) (Ω : StateSpace Λ q), IsGappedGroundState Λ q h.operator E₀ Ω Δ →
        ∀ (P : AdmissibleSupport Λ R → Prop) [DecidablePred P]
          (Aux : Type*) [Fintype Aux] [DecidableEq Aux] (S : Finset (Site Λ))
          (B : Matrix (Configuration Λ q × Aux) (Configuration Λ q × Aux) ℂ),
          (∀ x y : Aux, (Matrix.of fun σ τ => B (σ, x) (τ, y)) ∈
            supportedOperators q (S : Set (Site Λ))) →
          ∀ (r : ℝ), 0 ≤ r →
            (∀ i, ¬ P i → ∀ s ∈ S,
              ENNReal.ofReal r < ((domainGraph Λ).edist (a i) s : ℝ≥0∞)) →
            ∀ T : ℝ≥0,
              let k := fun i => positiveConstraint (positiveNormalization p (Δ / 2) J)
                (centeredFilter p (Δ / 2) h.operator Ω (h.term i))
              Integrable (fun w : PoissonWord.Word (AdmissibleSupport Λ R) =>
                channelWordOmissionDefect k P (List.ofFn w.2) B)
                (PoissonWord.measure (AdmissibleSupport Λ R) T) ∧
              (∫ w : PoissonWord.Word (AdmissibleSupport Λ R),
                channelWordOmissionDefect k P (List.ofFn w.2) B
                  ∂PoissonWord.measure (AdmissibleSupport Λ R) T) ≤
                D * S.card * ‖B‖ * Real.exp (v * T - γ * r ^ kernelExponent p) := by
  obtain ⟨C, c, hC, hc, hpos⟩ := exists_latticePositiveConstraints hp R hJ hΔ
  obtain ⟨D, v, γ, hD, hv, hγ, _, hbound⟩ :=
    exists_integrable_and_integral_channelWordOmissionDefect_le hC (K := 2) zero_le_two
      (μ := ((2 ^ ((1 + 2 * R * (R + 1)) - 1) : ℕ) : ℝ)) (Nat.cast_nonneg _)
      hc (kernelExponent_pos hp) (kernelExponent_le_one p)
  refine ⟨D, v, γ, hD, hv, hγ, ?_⟩
  intro q _ Λ h a ha E₀ Ω hgs P _ Aux _ _ S B hB r hr hfar T k
  classical
  obtain ⟨_, hk, _, _, _, htail, hcomp⟩ := hpos Λ h a ha E₀ Ω hgs
  let N := Finset.univ.sup fun i : AdmissibleSupport Λ R =>
    Finset.univ.sup ((domainGraph Λ).dist (a i))
  have hN (i : AdmissibleSupport Λ R) :
      Finset.univ.sup ((domainGraph Λ).dist (a i)) ≤ N :=
    Finset.le_sup (f := fun j => Finset.univ.sup ((domainGraph Λ).dist (a j)))
      (Finset.mem_univ i)
  exact hbound (Site Λ) (AdmissibleSupport Λ R) Aux q (domainGraph Λ) a k
    (fun i => (hk i).1) (fun i => (hk i).2.1) hcomp card_graphBall_domainGraph_le
    (fun x => by exact_mod_cast card_anchor_fiber_le a ha x)
    N hN (fun i l _ => (htail i l).2.2) P S B hB r hr hfar T

end TNLean.PEPS.AreaLaw
