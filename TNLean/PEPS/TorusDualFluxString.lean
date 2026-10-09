/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.TorusDualHomotopy
import TNLean.PEPS.TorusGroupGaugeContraction

/-!
# Physical equality under genuine flux-string path deformations

A finite dual path inserts the indicated integer power of one group element
on each actual native bond. The group may be nonabelian. Square moves derive
an integer vertex potential; its group powers give the native vertex gauge,
whose invariance is proved on the actual contracted tensor network.

Source: SCP10, arXiv:1001.3807, Definition 6.13 and Lemma 6.14,
lines 2181–2214. These are finite generated homotopies, with their swept
vertices specified. Equal endpoints alone do not imply equal torus states.

**Scope restriction (finite generated homotopies on a closed labelled torus):** See
`docs/paper-gaps/scp10_dual_flux_string_deformation.tex` for the distinction
from unrestricted source wording and arbitrary open-boundary geometries.
-/

namespace TNLean.PEPS

variable {width height : ℕ} {G : Type*} [Group G]
local notation "X" => TorusVertex width height

/-- Raise one group element to the signed counts on the two native bond families. -/
def torusFluxPowerLabels (g : G) (n : (X → ℤ) × (X → ℤ)) :
    TorusBondLabels width height G := (fun v => g ^ n.1 v, fun v => g ^ n.2 v)

/-- The literal group insertions of a dual path, with multiplicities and signs.
Source: SCP10, Definition 6.13, including the orientation in its figure. -/
def torusDualFluxLabels (g : G) {a b : X} (p : TorusDualPath a b) :
    TorusBondLabels width height G := torusFluxPowerLabels g (torusDualPathCrossings p)

/-- An integer gradient exponentiates to the actual native group gauge. All
powers have the same base, so no commutativity hypothesis on the group is used. -/
theorem torusFluxPowerLabels_add_gradient (g : G) (n : (X → ℤ) × (X → ℤ)) (f : X → ℤ) :
    torusFluxPowerLabels g (n + torusFluxGradient f) =
      torusBondGauge (fun v => g ^ f v) (torusFluxPowerLabels g n) := by
  ext v <;>
    simp only [torusFluxPowerLabels, torusFluxGradient, torusBondGauge,
      Prod.fst_add, Prod.snd_add, Pi.add_apply, ← zpow_neg, ← zpow_add] <;>
    congr 1 <;> omega

/-- A gauge for the real inserted bond assignment is derived from each
endpoint-preserving geometric homotopy. It is identity off the swept set. -/
theorem TorusDualHomotopy.exists_fluxGauge {R : Set X} {a b : X}
    {p q : TorusDualPath a b} (h : TorusDualHomotopy R p q) (g : G) :
    ∃ k : X → G, (∀ v, v ∉ R → k v = 1) ∧
      torusDualFluxLabels g q = torusBondGauge k (torusDualFluxLabels g p) := by
  obtain ⟨f, hf, heq⟩ := h.exists_potential
  refine ⟨fun v => g ^ f v, fun v hv => by simp [hf v hv], ?_⟩
  simp only [torusDualFluxLabels, heq, torusFluxPowerLabels_add_gradient]

variable {V : Type*} [Fintype V] [DecidableEq V]
variable [NeZero width] [NeZero height]
variable {Phys : TorusVertex width height → Type*}

/-- The physical coefficient vector obtained by inserting a dual flux path
into the actual native matrix contraction. Source: SCP10, Definition 6.13. -/
def torusDualFluxState (U : G →* Matrix V V ℂ)
    (A : ∀ v, V → V → V → V → Phys v → ℂ) (g : G)
    {a b : X} (p : TorusDualPath a b) (σ : ∀ v, Phys v) : ℂ :=
  torusBondNetwork (fun v c => A v c.1 c.2.1 c.2.2.1 c.2.2.2 (σ v))
    (fun v => U ((torusDualFluxLabels g p).1 v))
    (fun v => U ((torusDualFluxLabels g p).2 v))

/-- Genuine endpoint-preserving square/backtrack deformations leave the actual
physical coefficient unchanged. Only the swept sites need virtual invariance;
all other site tensors are arbitrary. Source: SCP10, Lemma 6.14. -/
theorem TorusDualHomotopy.torusBondNetwork_eq {R : Set X} {a b : X}
    {p q : TorusDualPath a b} (h : TorusDualHomotopy R p q)
    (U : G →* Matrix V V ℂ) (A : ∀ v, V → V → V → V → Phys v → ℂ)
    (hA : ∀ v, v ∈ R → ∀ g, siteMap (A v) ∘ₗ torusLegRep U g = siteMap (A v))
    (σ : ∀ v, Phys v) (g : G) :
    torusBondNetwork (fun v c => A v c.1 c.2.1 c.2.2.1 c.2.2.2 (σ v))
        (fun v => U ((torusDualFluxLabels g q).1 v))
        (fun v => U ((torusDualFluxLabels g q).2 v)) =
      torusBondNetwork (fun v c => A v c.1 c.2.1 c.2.2.1 c.2.2.2 (σ v))
        (fun v => U ((torusDualFluxLabels g p).1 v))
        (fun v => U ((torusDualFluxLabels g p).2 v)) := by
  obtain ⟨k, hk, heq⟩ := h.exists_fluxGauge g
  rw [heq]
  exact torusBondNetwork_torusBondGauge_of_invariant_on U A R k hk hA σ _

/-- Equality of the actual physical vectors for generated finite homotopies.
No gauge or equality-of-states premise is supplied. Source: SCP10, Lemma 6.14. -/
theorem TorusDualHomotopy.torusDualFluxState_eq {R : Set X} {a b : X}
    {p q : TorusDualPath a b} (h : TorusDualHomotopy R p q)
    (U : G →* Matrix V V ℂ) (A : ∀ v, V → V → V → V → Phys v → ℂ)
    (hA : ∀ v, v ∈ R → ∀ g, siteMap (A v) ∘ₗ torusLegRep U g = siteMap (A v))
    (g : G) : torusDualFluxState U A g q = torusDualFluxState U A g p := by
  funext σ
  exact h.torusBondNetwork_eq U A hA σ g

/-- On bonds incident to the swept vertices use the prescribed flux string;
elsewhere retain arbitrary fixed matrices. This represents unchanged exterior
data without requiring it to commute with the flux label. -/
noncomputable def torusFluxMatricesWithExterior (U : G →* Matrix V V ℂ)
    (R : Set X) (E : (X → Matrix V V ℂ) × (X → Matrix V V ℂ))
    (p : TorusBondLabels width height G) :
    (X → Matrix V V ℂ) × (X → Matrix V V ℂ) := by
  classical
  exact (fun v => if v ∈ R ∨ (v.1 + 1, v.2) ∈ R then U (p.1 v) else E.1 v,
    fun v => if v ∈ R ∨ (v.1, v.2 + 1) ∈ R then U (p.2 v) else E.2 v)

/-- Fixed arbitrary exterior matrices and tensors do not obstruct a deformation
whose swept vertices lie inside the invariant patch. In particular the exterior
is neither trivialized nor assumed to commute with the flux group element.
Source: SCP10, bulk string deformation in Lemma 6.14. -/
theorem TorusDualHomotopy.torusBondNetwork_eq_with_exterior {R : Set X} {a b : X}
    {p q : TorusDualPath a b} (h : TorusDualHomotopy R p q)
    (U : G →* Matrix V V ℂ) (A : ∀ v, V → V → V → V → Phys v → ℂ)
    (hA : ∀ v, v ∈ R → ∀ g, siteMap (A v) ∘ₗ torusLegRep U g = siteMap (A v))
    (σ : ∀ v, Phys v) (g : G)
    (E : (X → Matrix V V ℂ) × (X → Matrix V V ℂ)) :
    torusBondNetwork (fun v c => A v c.1 c.2.1 c.2.2.1 c.2.2.2 (σ v))
        (torusFluxMatricesWithExterior U R E (torusDualFluxLabels g q)).1
        (torusFluxMatricesWithExterior U R E (torusDualFluxLabels g q)).2 =
      torusBondNetwork (fun v c => A v c.1 c.2.1 c.2.2.1 c.2.2.2 (σ v))
        (torusFluxMatricesWithExterior U R E (torusDualFluxLabels g p)).1
        (torusFluxMatricesWithExterior U R E (torusDualFluxLabels g p)).2 := by
  classical
  obtain ⟨k, hk, heq⟩ := h.exists_fluxGauge g
  have hh : (torusFluxMatricesWithExterior U R E (torusDualFluxLabels g q)).1 =
      fun v => U (k (v.1 + 1, v.2)) *
        (torusFluxMatricesWithExterior U R E (torusDualFluxLabels g p)).1 v * U (k v)⁻¹ := by
    funext v
    by_cases hv : v ∈ R ∨ (v.1 + 1, v.2) ∈ R
    · simp [torusFluxMatricesWithExterior, hv, heq, torusBondGauge, map_mul]
    · simp [torusFluxMatricesWithExterior, hv, hk v (not_or.mp hv).1,
        hk _ (not_or.mp hv).2]
  have hv : (torusFluxMatricesWithExterior U R E (torusDualFluxLabels g q)).2 =
      fun v => U (k v) *
        (torusFluxMatricesWithExterior U R E (torusDualFluxLabels g p)).2 v *
          U (k (v.1, v.2 + 1))⁻¹ := by
    funext v
    by_cases hv : v ∈ R ∨ (v.1, v.2 + 1) ∈ R
    · simp [torusFluxMatricesWithExterior, hv, heq, torusBondGauge, map_mul]
    · simp [torusFluxMatricesWithExterior, hv, hk v (not_or.mp hv).1,
        hk _ (not_or.mp hv).2]
  rw [hh, hv]
  exact torusBondNetwork_groupGauge_of_invariant_on U A R k hk hA σ _ _

end TNLean.PEPS
