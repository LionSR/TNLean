/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.Periodic.Symmetry
import TNLean.Algebra.ProjectiveRepresentation
import TNLean.Algebra.CocycleCohomology

/-!
# Periodic MPS — conditional projective representation after the symmetry corollary

This file starts from the conditional group-action reformulation
`MPSTensor.cor_4_1_physical_symmetry_zgauge_explicit`. The source paper
arXiv:1708.00029, Section 4.2, lines 834--845, proves a symmetry-to-`Z`-gauge
corollary for a single local unitary and then says that its consequences will be
explored elsewhere. It does not choose the virtual gauges coherently over a
group, prove a scalar cocycle, or prove the cohomological interpretation
recorded below. Under an additional coherence hypothesis, this file constructs
a projective representation of the symmetry group `G` on the bond space.

The injective analogue is `MPSTensor.virtual_rep_of_symmetric_injective`
(in `MPS/Symmetry/VirtualRepresentation.lean`): there, gauge uniqueness
(`MPS/Symmetry/GaugeUniqueness.lean`) reduces associativity of the induced
virtual action to a scalar 2-cocycle on `G`. In the genuinely periodic case
there is a non-trivial `Z`-gauge ambiguity (`Z_g^{m_g} = 1`), so an additional
analytic input is required to reduce the full rigidity back to a scalar
cocycle. Following the established repository
pattern (see `PeriodicEqualCaseFT`), that input is exposed as an explicit
hypothesis `PeriodicProjectiveRigidity`. The remaining projective-representation
conclusions - the cocycle identity and the construction of a
`ProjectiveRepresentation` on the bond space - are formalized here.

## Main definitions and results

* `MPSTensor.PeriodicProjectiveRigidity` — the analytic hypothesis recording
  the existence of a compatible family `Y : G → GL (Fin D) ℂ` together with a
  scalar 2-cochain `u : G × G → ℂˣ` satisfying the projective law on the
  bond space, while every `Y g` realizes the pointwise `Z`-gauge intertwining
  modeled on the symmetry corollary.
* `MPSTensor.cor_4_1_projective_rep` — the conditional projective-representation
  construction:
  from `PeriodicProjectiveRigidity`, produce a
  `TNLean.Algebra.ProjectiveRepresentation` on the bond space together with
  the intertwining relation between `A` and the twisted tensors.
* `MPSTensor.cor_4_1_projective_rep_cocycle` — if `D > 0`, the factor system
  satisfies the 2-cocycle identity (via
  `ProjectiveRepresentation.cocycle_of_assoc`).

## References

* arXiv:1708.00029 Section 4.2 (De las Cuevas–Cirac–Schuch–Pérez-García, 2017) —
  the symmetry-to-`Z`-gauge corollary used as input.
* arXiv:0802.0447 — projective-representation construction for injective MPS.
* Chen, Gu, Wen, *Classification of gapped symmetric phases in one-dimensional
  spin systems*, Phys. Rev. B 83, 035107 (2011).
* `MPS/Symmetry/VirtualRepresentation.lean` — injective analogue.
-/

open scoped Matrix BigOperators

namespace MPSTensor

open TNLean.Algebra

variable {d D : ℕ} {G : Type*} [Group G]

/-! ## Periodic projective-representation rigidity hypothesis -/

/-- **Periodic projective-representation rigidity hypothesis.**

For an on-site symmetry `U : G →* Mat_d(ℂ)` of a periodic tensor `A`,
`PeriodicProjectiveRigidity A U` records a coherent choice extending the
pointwise `Z`-gauge conclusion modeled on the source symmetry corollary: there is a family
`Y : G → GL (Fin D) ℂ` and a scalar 2-cochain `u : G × G → ℂˣ` such that

1. Each `Y g`, together with some `Z`-matrix (satisfying the period, commutation
   and gauge-intertwining conditions), realizes the pointwise `Z`-gauge
   intertwining between `A` and the `g`-twisted tensor.
2. The family satisfies the projective multiplication law on the bond space:
   `(Y h) · (Y g) = u(g, h) • Y (g * h)` as matrices.

In the injective case (period `1`), this hypothesis reduces to
`gauge_unique_up_to_scalar` applied to `A`; in the genuinely periodic case the
`Z`-commutant of `A` is non-trivial, so an additional analytic input is required.
Callers committing to this Prop are committing to a finiteness/rigidity result
analogous to `MPSTensor.PeriodicEqualCaseFT`. -/
def PeriodicProjectiveRigidity
    (A : MPSTensor d D) (U : G →* Matrix (Fin d) (Fin d) ℂ) : Prop :=
  ∃ (Y : G → GL (Fin D) ℂ) (u : G → G → Units ℂ),
    (∀ g : G, ∃ (m : ℕ) (Z : Matrix (Fin D) (Fin D) ℂ),
      0 < m ∧ Z ^ m = 1 ∧ (∀ i : Fin d, Z * A i = A i * Z) ∧
      (∀ i : Fin d,
        Z * A i =
          (Y g : Matrix (Fin D) (Fin D) ℂ) * twistedTensor A U g i *
            (((Y g)⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ))) ∧
    ∀ g h : G,
      ((Y h : Matrix (Fin D) (Fin D) ℂ) * (Y g : Matrix (Fin D) (Fin D) ℂ)) =
        (u g h : ℂ) • ((Y (g * h) : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)

/-! ## Projective representation from the rigidity hypothesis -/

/-- **Conditional projective representation from the group-action reformulation.**

If the pointwise virtual gauges in `PeriodicProjectiveRigidity` can be chosen
coherently, then the bond-space gauges assemble into a projective representation
of `G`: there exist a scalar 2-cochain `ω : G × G → ℂˣ` and a
`TNLean.Algebra.ProjectiveRepresentation` on the bond space whose virtual gauges
still realize the pointwise `Z`-gauge intertwining with the twisted tensors.

The source paper arXiv:1708.00029, Section 4.2, lines 834--845, supplies only
the `Z`-gauge conclusion for a single local unitary. The coherent family
`(Y_g)_{g ∈ G}` and the scalar projective law are the extra content of
`PeriodicProjectiveRigidity`.

The construction uses the *inversion convention* of
`MPS/Symmetry/VirtualRepresentation.lean`: the virtual representation is
`X g := Y (g⁻¹)`, so that the projective multiplication law takes the standard
form `X g · X h = ω(g, h) • X (g * h)` with `ω(g, h) := u(h⁻¹, g⁻¹)`. -/
theorem cor_4_1_projective_rep
    (A : MPSTensor d D)
    (U : G →* Matrix (Fin d) (Fin d) ℂ)
    (hRigidity : PeriodicProjectiveRigidity A U) :
    ∃ (ω : ScalarCocycle G) (ρ : ProjectiveRepresentation (D := D) ω),
      ∀ g : G, ∃ (m : ℕ) (Z : Matrix (Fin D) (Fin D) ℂ),
        0 < m ∧ Z ^ m = 1 ∧ (∀ i : Fin d, Z * A i = A i * Z) ∧
        (∀ i : Fin d,
          Z * A i =
            ((ρ.X (g⁻¹) : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) *
              twistedTensor A U g i *
              (((ρ.X (g⁻¹))⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)) := by
  obtain ⟨Y, u, hY, hmul⟩ := hRigidity
  refine ⟨fun g h => u (h⁻¹) (g⁻¹),
    { X := fun g => Y (g⁻¹)
      map_mul' := by
        intro g h
        have h₁ := hmul (h⁻¹) (g⁻¹)
        simpa [mul_inv_rev] using h₁ },
    ?_⟩
  intro g
  simpa using hY g

/-- **Cocycle condition for the conditional projective-representation construction.**

For positive bond dimension, the factor system produced by `cor_4_1_projective_rep`
satisfies the multiplicative 2-cocycle identity on `G`. This is a consequence of
associativity of matrix multiplication via
`ProjectiveRepresentation.cocycle_of_assoc`. -/
theorem cor_4_1_projective_rep_cocycle
    (A : MPSTensor d D)
    (U : G →* Matrix (Fin d) (Fin d) ℂ)
    (hRigidity : PeriodicProjectiveRigidity A U)
    (hD : 0 < D) :
    ∃ (ω : ScalarCocycle G) (_ρ : ProjectiveRepresentation (D := D) ω),
      ScalarCocycle.IsCocycle ω := by
  obtain ⟨ω, ρ, _⟩ := cor_4_1_projective_rep A U hRigidity
  exact ⟨ω, ρ, ScalarCocycle.isCocycle_of_projRep ρ hD⟩

/-! ## Bundled constructor from the rigidity hypothesis -/

/-- **Projective representation from the periodic projective-rigidity hypothesis.**

High-level consequence of `cor_4_1_projective_rep` together with the cocycle
condition of `cor_4_1_projective_rep_cocycle`: the explicit rigidity hypothesis
turns the assumed bond-space gauges into a coherent projective representation
of `G` on the bond space, with factor system satisfying the 2-cocycle identity
whenever `D > 0`.

The irreducible-form and unitarity hypotheses belong to the theorem producing
`PeriodicProjectiveRigidity A U`; this theorem records only the resulting
projective representation on the bond space. -/
theorem projectiveRep_of_symmetry
    (A : MPSTensor d D)
    (U : G →* Matrix (Fin d) (Fin d) ℂ)
    (hRigidity : PeriodicProjectiveRigidity A U) :
    ∃ (ω : ScalarCocycle G) (ρ : ProjectiveRepresentation (D := D) ω),
      (∀ g : G, ∃ (m : ℕ) (Z : Matrix (Fin D) (Fin D) ℂ),
        0 < m ∧ Z ^ m = 1 ∧ (∀ i : Fin d, Z * A i = A i * Z) ∧
        (∀ i : Fin d,
          Z * A i =
            ((ρ.X (g⁻¹) : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) *
              twistedTensor A U g i *
              (((ρ.X (g⁻¹))⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ))) ∧
      (0 < D → ScalarCocycle.IsCocycle ω) := by
  obtain ⟨ω, ρ, hIntertwine⟩ := cor_4_1_projective_rep A U hRigidity
  exact ⟨ω, ρ, hIntertwine, fun hD => ScalarCocycle.isCocycle_of_projRep ρ hD⟩

end MPSTensor
