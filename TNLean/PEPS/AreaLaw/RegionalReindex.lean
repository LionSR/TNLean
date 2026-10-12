/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.RegionalEntropyBridge
import QICLean.Entropy.RegionCovariance

/-!
# Regional states under a relabelling of sites

A site bijection preserving a chosen region identifies the regional
configuration spaces, and its pullback on coefficients transports the pure
vector. The reduced state is covariant under this identification and the von
Neumann entropy is invariant. Neither normalization nor preservation of lattice
adjacency is required for these finite-dimensional identities.

The statements are the constant-dimension case of QICLean's covariance of
regional states under bijections of tensor factors
(`Entropy.regionState_relabel`, `Entropy.regionEntropy_relabel`), with every
basis bijection the identity, read through `reducedState_eq_regionState`.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 2 (`sec:prelim`), lines 10–25, finite tensor-factor
conventions. Source revision:
`openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Independently proved from the manuscript and existing QICLean partial-trace
and entropy results; no upstream Lean proof text is reused.
-/

namespace TNLean.PEPS.AreaLaw

/-- Configuration transport of a region preserved by a site bijection.
Source: area-law `sec:prelim`, lines 10–25, finite tensor factors. -/
def regionConfigurationEquiv {Λ Λ' : Finset (ℤ × ℤ)} (q : ℕ)
    (A : Finset (Site Λ)) (A' : Finset (Site Λ'))
    (e : Site Λ ≃ Site Λ') (hA : ∀ x, x ∈ A ↔ e x ∈ A') :
    ({x : Site Λ // x ∈ A} → Fin q) ≃ ({x : Site Λ' // x ∈ A'} → Fin q) :=
  Entropy.regionConfigurationEquiv (n := fun _ ↦ q) (n' := fun _ ↦ q) A A' e hA
    fun _ ↦ Equiv.refl _

/-- The same physical vector written after relabelling its sites.
Source: area-law `sec:prelim`, lines 10–25, finite tensor factors. -/
noncomputable def relabelState {Λ Λ' : Finset (ℤ × ℤ)} (q : ℕ)
    (e : Site Λ ≃ Site Λ') (Ω : StateSpace Λ q) : StateSpace Λ' q :=
  Entropy.relabelVector (n := fun _ ↦ q) (n' := fun _ ↦ q) e (fun _ ↦ Equiv.refl _) Ω

/-- A reduced pure-state matrix is covariant under a site relabelling that
preserves the chosen region. No normalization or lattice-adjacency assumption
is required. Source: area-law `sec:prelim`, lines 10–25, finite tensor-factor
conventions. -/
theorem reducedState_relabel {Λ Λ' : Finset (ℤ × ℤ)} (q : ℕ)
    (A : Finset (Site Λ)) (A' : Finset (Site Λ'))
    (e : Site Λ ≃ Site Λ') (hA : ∀ x, x ∈ A ↔ e x ∈ A')
    (Ω : StateSpace Λ q) :
    reducedState Λ' q (relabelState q e Ω) A' =
      (reducedState Λ q Ω A).submatrix
        (regionConfigurationEquiv q A A' e hA).symm
        (regionConfigurationEquiv q A A' e hA).symm := by
  rw [reducedState_eq_regionState, reducedState_eq_regionState]
  exact Entropy.regionState_relabel (n := fun _ ↦ q) (n' := fun _ ↦ q) A A' e hA
    (fun _ ↦ Equiv.refl _) Ω

/-- Regional entropy is unchanged by relabelling the physical sites and region.
Source: area-law `sec:prelim`, lines 10–25, finite tensor-factor conventions. -/
theorem regionalEntropy_relabel {Λ Λ' : Finset (ℤ × ℤ)} (q : ℕ)
    (A : Finset (Site Λ)) (A' : Finset (Site Λ'))
    (e : Site Λ ≃ Site Λ') (hA : ∀ x, x ∈ A ↔ e x ∈ A')
    (Ω : StateSpace Λ q) :
    regionalEntropy Λ' q (relabelState q e Ω) A' = regionalEntropy Λ q Ω A := by
  rw [regionalEntropy_eq_regionEntropy, regionalEntropy_eq_regionEntropy]
  exact Entropy.regionEntropy_relabel (n := fun _ ↦ q) (n' := fun _ ↦ q) A A' e hA
    (fun _ ↦ Equiv.refl _) Ω

/-- Relabelling sites preserves the Euclidean norm of a physical vector.
Source: area-law `sec:prelim`, lines 10–25, finite tensor factors. -/
@[simp] theorem norm_relabelState {Λ Λ' : Finset (ℤ × ℤ)} (q : ℕ)
    (e : Site Λ ≃ Site Λ') (Ω : StateSpace Λ q) :
    ‖relabelState q e Ω‖ = ‖Ω‖ :=
  Entropy.norm_relabelVector (n := fun _ ↦ q) (n' := fun _ ↦ q) e _ Ω

end TNLean.PEPS.AreaLaw
