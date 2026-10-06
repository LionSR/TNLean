/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.RegularRegionGaugeContraction

/-!
# Vertex gauges in a closed regular PEPS

Changing every inserted bond operator by its endpoint gauges leaves the actual
closed PEPS vector unchanged. This follows from local regular invariance and a
bijective change of the summed bond labels; no isometry or connectedness is
required. It is the algebraic operation behind deformation of closure strings.

Source: Schuch, Cirac, and Pérez-García, arXiv:1001.3807,
`eq:2d:move-strings`, local source lines 1622–1647. This identity does not
assert that a prescribed region admits a gauge removing its incident twists.
-/

open scoped BigOperators

namespace TNLean.PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj] {d : ℕ}
variable {G : Type*} [Group G] [Fintype G]

/-- The inserted operators after a gauge at every vertex.
Source: SCP10, deformation of closure strings, lines 1622–1647. -/
def regularVertexGaugeOperators (k : V → G) (u : Edge Γ → G) : Edge Γ → G :=
  fun e => (k e.1.2)⁻¹ * u e * k e.1.1

/-- Local regular invariance makes the original and gauged closed contractions
equal as physical PEPS vectors. Source: SCP10, `eq:2d:move-strings`,
lines 1622–1647. -/
theorem sameState_regularVertexGauge
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ)
    (ha : ∀ g v η s, a v (fun e => g * η e) s = a v η s)
    (k : V → G) (u : Edge Γ → G) :
    SameState (groupBondTensor (regularTwistedSite a u))
      (groupBondTensor (regularTwistedSite a (regularVertexGaugeOperators k u))) := by
  classical
  intro σ
  let E : (Edge Γ → G) ≃ VirtualConfig (groupBondTensor a) :=
    Equiv.piCongrRight fun _ => Fintype.equivFin G
  let F : (Edge Γ → G) ≃ (Edge Γ → G) :=
    Equiv.piCongrRight fun e => Equiv.mulLeft (k e.1.1)⁻¹
  unfold stateCoeff
  rw [← Equiv.sum_comp E, ← Equiv.sum_comp E]
  simp only [groupBondTensor, E, Equiv.piCongrRight_apply, Pi.map_apply,
    Equiv.symm_apply_apply]
  conv_rhs => rw [← Equiv.sum_comp F]
  apply Finset.sum_congr rfl
  intro η _
  apply Finset.prod_congr rfl
  intro v _
  have hlabels : regularTwistedLabels (regularVertexGaugeOperators k u) v
      (fun e => F η e.1) = fun e => (k v)⁻¹ * regularTwistedLabels u v
        (fun e => η e.1) e := by
    funext e
    simp only [regularTwistedLabels, F, Equiv.piCongrRight_apply, Pi.map_apply,
      regularVertexGaugeOperators]
    by_cases hh : v = e.1.1.2
    · simp [hh, mul_assoc]
    · have ht : e.1.1.1 = v := e.2.resolve_right (Ne.symm hh)
      simp [hh, ht]
  simp only [regularTwistedSite, hlabels, ha]

end TNLean.PEPS
