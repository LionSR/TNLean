/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.InverseCompatibleSourceProperties

/-!
# Source properties at an involutive element of a canonical MPU family

At an involutive group element, use the existing chosen dagger-inverse gauge
and scalar to construct the actual inverse-compatible source factors. The
three pairs of physical closures and source-rank normalizations then follow
from the existing transported source properties.

The source explicitly assumes simplicity of the adjoint in its Appendix
proposition (arXiv:2502.20257, `main.tex` line 5344) and in `prop:MPUsplus`.
For this selected canonical-form-II tensor, that premise is discharged locally:
physical adjunction preserves the available canonical data, exchanges the two
source ranks, and hence preserves the rank-product criterion for simplicity.
This uses the canonical-form-II equivalence from arXiv:1703.09188, Theorem
`ThmFund1`, not the gauge, comparison, or source Gram normalization argument.
The existing source-property theorems retain their explicit adjoint-simplicity
premises unchanged.

Global left-canonicality of the normalized family flattenings and the selected
tensor's canonical form II are separate hypotheses. No new gauge or scalar is
chosen. This result supplies only `eq:MPUnice2`, `eq:MPUnice3`, and `eq:MPUnice4`
via the transport at lines 5486–5487, not the full Appendix proposition or the
truncated-symmetry complement identity.
-/

open scoped ComplexOrder Matrix BigOperators

namespace MPOTensor

/-- Locally discharge the source's adjoint-simplicity premise using the
canonical-form-II rank-product criterion and rank exchange under adjunction.
Source: arXiv:1703.09188, `ThmFund1` (lines 563–601) and `defnrl`;
the discharged premise occurs in arXiv:2502.20257, line 5344. -/
private theorem adjoint_simple_of_canonical_simple {d D : ℕ} {U : MPOTensor d D}
    (hU : IsMPUCanonicalFormII U) (hsimple : IsMPUSimple U) :
    IsMPUSimple (physicalAdjointTensor U) := by
  have hrank : r[U] * ℓ[U] = d * d := (hU.isMPUSimple_tfae.out 0 1).mp hsimple
  apply (hU.physicalAdjointTensor.isMPUSimple_tfae.out 0 1).mpr
  rw [rightRank_physicalAdjointTensor, leftRank_physicalAdjointTensor, mul_comm]
  exact hrank

namespace GroupFamily

/-- The three paired source properties for the actual inverse-compatible
record at an involutive element, using the existing chosen gauge and scalar.
Simplicity comes from the representation; adjoint simplicity is derived
locally from the selected canonical form II, not imposed as a new premise.
Source: arXiv:2502.20257, `eq:defT`, `eq:intro_sigma` (lines 1552–1562),
`eq:MPUnice2`–`eq:MPUnice4`, and their transport at lines 5486–5487. -/
theorem IsRepresentation.inverseCompatibleSourceProperties_of_inv_eq
    {G : Type*} [Group G] {d : ℕ} (F : MPOTensor.GroupFamily G d) (hF : F.IsRepresentation)
    (hcanonical : ∀ g : G,
      MPSTensor.IsLeftCanonical (F.tensor g).normalizedFlattening)
    (g : G) (hg : g⁻¹ = g) (hU : IsMPUCanonicalFormII (F.tensor g)) :
    let T := hF.daggerInverseGauge F hcanonical g
    let σ := hF.daggerInverseScalar F hcanonical g
    let S := inverseCompatibleSourceFactors (F.tensor g) T hU (hF.isSimple g)
      (hF.physicalAdjointTensor_eq_daggerInverseGauge_of_inv_eq F hcanonical g hg) σ
      (hF.daggerInverseGauge_mul_mapStar_self_eq_smul_one_of_inv_eq F hcanonical g hg)
    (∀ p q : Fin d,
      (∑ r : Fin r[F.tensor g], ∑ α : Fin (F.bondDim g),
        star (S.Y₁ r (α, p)) * S.Y₁ r (α, q)) = (if p = q then 1 else 0) ∧
      (∑ l : Fin ℓ[F.tensor g], ∑ α : Fin (F.bondDim g), ∑ β : Fin (F.bondDim g),
        star (S.Y₂ l (p, α)) * S.Y₂ l (q, β) * hU.ρ β α) =
          (if p = q then 1 else 0)) ∧
    (S.Y₁ * S.Y₁ᴴ = ((d : ℂ) / (r[F.tensor g] : ℂ)) • 1 ∧
      S.Y₂ * sourceWeight (d := d) hU.ρ * S.Y₂ᴴ =
        ((d : ℂ) / (ℓ[F.tensor g] : ℂ)) • 1) ∧
    (∀ i j : Fin d,
      (∑ r : Fin r[F.tensor g], ∑ α : Fin (F.bondDim g), ∑ β : Fin (F.bondDim g),
        S.X₁ (i, α) r * hU.ρ β α * star (S.X₁ (j, β) r)) =
          ((r[F.tensor g] : ℂ) / (d : ℂ)) * (if i = j then 1 else 0) ∧
      (∑ l : Fin ℓ[F.tensor g], ∑ x : Fin (F.bondDim g),
        S.X₂ (x, i) l * star (S.X₂ (x, j) l)) =
          ((ℓ[F.tensor g] : ℂ) / (d : ℂ)) * (if i = j then 1 else 0)) := by
  let T := hF.daggerInverseGauge F hcanonical g
  let σ := hF.daggerInverseScalar F hcanonical g
  have hT := hF.physicalAdjointTensor_eq_daggerInverseGauge_of_inv_eq F hcanonical g hg
  have hσ := hF.daggerInverseGauge_mul_mapStar_self_eq_smul_one_of_inv_eq F hcanonical g hg
  have hadjoint := adjoint_simple_of_canonical_simple hU (hF.isSimple g)
  exact ⟨inverseCompatibleSourceFactors_Y_physical_contractions
      (F.tensor g) T hU (hF.isSimple g) hT σ hσ,
    inverseCompatibleSourceFactors_Y_rank_normalizations
      (F.tensor g) T hU (hF.isSimple g) hT σ hσ hadjoint,
    inverseCompatibleSourceFactors_X_physical_contractions
      (F.tensor g) T hU (hF.isSimple g) hT σ hσ hadjoint⟩

end GroupFamily

end MPOTensor
