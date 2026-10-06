/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.TorusDualRectangle
import TNLean.PEPS.TorusDualFluxString

/-!
# Flux deformation in an embedded finite rectangular bulk

Combine the rectangle's derived homotopy with the actual native matrix
contraction, keeping arbitrary fixed exterior matrices off the swept bonds.
Source: SCP10, arXiv:1001.3807v3, Lemma 6.14, lines 2199–2214.

**Scope restriction (embedded finite rectangular bulk):** Paths share lifted
endpoints inside one rectangle. No arbitrary-region avoidance, change of winding
class, or vacuum-density equality is asserted. See
`docs/paper-gaps/scp10_dual_flux_string_deformation.tex`.
-/

namespace TNLean.PEPS

variable {width height : ℕ} [NeZero width] [NeZero height]
variable {G V : Type*} [Group G] [Fintype V] [DecidableEq V]
variable {Phys : TorusVertex width height → Type*}
local notation "X" => TorusVertex width height

/-- Equal lifted endpoints in an embedded rectangle suffice for equality of
actual contractions, with site invariance required only on swept primal sites.
The homotopy is derived from the paths, rather than supplied as a hypothesis. -/
theorem TorusDualRectangle.torusBondNetwork_eq_with_exterior
    (P : TorusDualRectangle width height) {a b : ℕ × ℕ}
    (p q : @Quiver.Path (ℕ × ℕ) (rectDualQuiver P.cols P.rows) a b)
    (U : G →* Matrix V V ℂ) (A : ∀ v, V → V → V → V → Phys v → ℂ)
    (hA : ∀ v, v ∈ torusRectInterior P.origin.1 P.origin.2 P.cols P.rows →
      ∀ g, siteMap (A v) ∘ₗ torusLegRep U g = siteMap (A v))
    (σ : ∀ v, Phys v) (g : G)
    (E : (X → Matrix V V ℂ) × (X → Matrix V V ℂ)) :
    let R := torusRectInterior P.origin.1 P.origin.2 P.cols P.rows
    let pT := rectDualPathToTorus P.origin.1 P.origin.2 p
    let qT := rectDualPathToTorus P.origin.1 P.origin.2 q
    torusBondNetwork (fun v c => A v c.1 c.2.1 c.2.2.1 c.2.2.2 (σ v))
        (torusFluxMatricesWithExterior U R E (torusDualFluxLabels g qT)).1
        (torusFluxMatricesWithExterior U R E (torusDualFluxLabels g qT)).2 =
      torusBondNetwork (fun v c => A v c.1 c.2.1 c.2.2.1 c.2.2.2 (σ v))
        (torusFluxMatricesWithExterior U R E (torusDualFluxLabels g pT)).1
        (torusFluxMatricesWithExterior U R E (torusDualFluxLabels g pT)).2 := by
  exact (P.homotopy p q).torusBondNetwork_eq_with_exterior U A hA σ g E

end TNLean.PEPS
