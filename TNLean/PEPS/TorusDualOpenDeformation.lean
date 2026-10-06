/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.TorusDualCollar
import TNLean.PEPS.TorusLabelledOpenCoefficient

/-!
# Open-boundary deformation inside a collared rectangle

Equal lifted endpoints give a supported homotopy, hence a derived gauge.
The explicit one-site collar makes that gauge identity at both endpoints of
crossing bonds. Delta completion then gives equality of actual open coefficients
and contraction with an arbitrary correlated boundary tensor.

This is the collared rectangular specialization of SCP10, arXiv:1001.3807v3,
Lemma 6.14. It does not prove arbitrary-region avoidance, cross-winding equality,
or equality with a vacuum reduced density matrix.
-/

noncomputable section
open scoped BigOperators

namespace TNLean.PEPS
open DependentBondNetwork

variable {width height : ℕ} [NeZero width] [NeZero height]
variable {G V : Type*} [Group G] [Fintype V] [DecidableEq V]
local notation "X" => TorusVertex width height
local notation "E" => TorusLabelledBond width height

open Classical in
/-- Matrix insertions of a dual flux path on the actual labelled bonds. -/
def torusDualFluxBondMatrices (U : G →* Matrix V V ℂ) (g : G)
    {a b : X} (p : TorusDualPath a b) (e : E) : Matrix V V ℂ :=
  if e.2 then U ((torusDualFluxLabels g p).2 e.1)
  else U ((torusDualFluxLabels g p).1 e.1)

open Classical in
/-- Empty virtual alphabets give zero on a nonempty native region, since even
one region vertex has an incidence whose label cannot be assigned. -/
theorem torusOpenCoefficient_eq_zero_of_isEmpty [IsEmpty V]
    (R : Set X) (v : R) (A : R → (V × V × V × V) → ℂ)
    (O : E → Matrix V V ℂ)
    (θ : RegionBoundaryEndpoint torusLabelledBondTail torusLabelledBondHead R → V) :
    torusOpenCoefficient R A O θ = 0 := by
  let : IsEmpty (RegionSiteConfig torusLabelledBondTail torusLabelledBondHead R (V := V)) :=
    ⟨fun η ↦ isEmptyElim (η v (torusIncidentEndpoint v.1 (false, false)))⟩
  simp [torusOpenCoefficient, openCoefficient]

omit [NeZero width] [NeZero height] in
open Classical in
/-- The homotopy-derived gauge survives replacing noninternal matrices by
identity: the collar puts both endpoints of every such bond off its support. -/
theorem TorusDualCollar.exists_internalFluxGauge
    (C : TorusDualCollar width height) {a b : ℕ × ℕ}
    (p q : @Quiver.Path (ℕ × ℕ) (rectDualQuiver C.patch.cols C.patch.rows) a b)
    (U : G →* Matrix V V ℂ) (g : G) :
    ∃ k : X → G, (∀ v, v ∉ C.swept → k v = 1) ∧ ∀ e : E,
      internalBondMatrices torusLabelledBondTail torusLabelledBondHead C.region
          (torusDualFluxBondMatrices U g
            (rectDualPathToTorus C.patch.origin.1 C.patch.origin.2 q)) e =
      U (k (torusLabelledBondHead e)) *
        internalBondMatrices torusLabelledBondTail torusLabelledBondHead C.region
          (torusDualFluxBondMatrices U g
            (rectDualPathToTorus C.patch.origin.1 C.patch.origin.2 p)) e *
        U (k (torusLabelledBondTail e))⁻¹ := by
  obtain ⟨k, hk, heq⟩ := (C.patch.homotopy p q).exists_fluxGauge g
  refine ⟨k, hk, ?_⟩
  intro e
  by_cases he : torusLabelledBondTail e ∈ C.region ∧ torusLabelledBondHead e ∈ C.region
  · simp only [internalBondMatrices, he]
    rcases e with ⟨v, d⟩
    cases d <;> simp [torusDualFluxBondMatrices, heq, torusBondGauge,
      torusLabelledBondHead, torusLabelledBondTail, map_mul]
  · obtain ⟨ht, hh⟩ := C.noninternal_outside e he
    simp [internalBondMatrices, he, hk _ ht, hk _ hh]

variable {Phys : TorusVertex width height → Type*}

open Classical in
/-- Actual open coefficients agree for arbitrary labelled paths with the same
lifted endpoints inside the embedded patch. The gauge and its boundary behavior
are derived, not hypotheses. No nonempty virtual-alphabet assumption is needed. -/
theorem TorusDualCollar.openCoefficient_eq
    (C : TorusDualCollar width height) {a b : ℕ × ℕ}
    (p q : @Quiver.Path (ℕ × ℕ) (rectDualQuiver C.patch.cols C.patch.rows) a b)
    (U : G →* Matrix V V ℂ) (A : ∀ v, V → V → V → V → Phys v → ℂ)
    (hA : ∀ v, v ∈ C.swept → ∀ g, siteMap (A v) ∘ₗ torusLegRep U g = siteMap (A v))
    (σ : ∀ v : C.region, Phys v.1) (g : G)
    (θ : RegionBoundaryEndpoint torusLabelledBondTail torusLabelledBondHead C.region → V) :
    torusOpenCoefficient C.region
      (fun v c ↦ A v.1 c.1 c.2.1 c.2.2.1 c.2.2.2 (σ v))
      (torusDualFluxBondMatrices U g
        (rectDualPathToTorus C.patch.origin.1 C.patch.origin.2 q)) θ =
    torusOpenCoefficient C.region
      (fun v c ↦ A v.1 c.1 c.2.1 c.2.2.1 c.2.2.2 (σ v))
      (torusDualFluxBondMatrices U g
        (rectDualPathToTorus C.patch.origin.1 C.patch.origin.2 p)) θ := by
  classical
  by_cases hn : Nonempty V
  · obtain ⟨v₀⟩ := hn
    let F : C.region → (V × V × V × V) → ℂ :=
      fun v c ↦ A v.1 c.1 c.2.1 c.2.2.1 c.2.2.2 (σ v)
    obtain ⟨k, hk, he⟩ := C.exists_internalFluxGauge p q U g
    rw [← torusBondNetwork_deltaCompletedTensor _ _ _ v₀,
      ← torusBondNetwork_deltaCompletedTensor _ _ _ v₀]
    have hh := fun v ↦ he (v, false)
    have hv := fun v ↦ he (v, true)
    simp only [torusLabelledBondHead, torusLabelledBondTail, Bool.false_eq_true,
      ite_false, ite_true] at hh hv
    simp_rw [hh, hv]
    apply torusBondNetwork_groupGauge_of_vecMul_eq U
    intro v hkv
    have hs : v ∈ C.swept := by
      by_contra hs
      exact hkv (hk v hs)
    have hr := (C.neighbors_mem hs).1
    have hinside : torusDeltaCompletedTensor C.region F v₀ θ v = F ⟨v, hr⟩ := by
      funext c
      simp [torusDeltaCompletedTensor, deltaCompletedTensor, hr]
    change Matrix.vecMul (torusDeltaCompletedTensor C.region F v₀ θ v)
      (torusLegMatrix U (k v)) = torusDeltaCompletedTensor C.region F v₀ θ v
    rw [hinside]
    exact vecMul_torusLegMatrix_of_comp_eq U (A v) (hA v hs) (k v) (σ ⟨v, hr⟩)
  · let : IsEmpty V := not_nonempty_iff.mp hn
    rw [torusOpenCoefficient_eq_zero_of_isEmpty _ ⟨C.patch.origin, C.origin_mem⟩,
      torusOpenCoefficient_eq_zero_of_isEmpty _ ⟨C.patch.origin, C.origin_mem⟩]

open Classical in
/-- Deformation commutes with contraction against an arbitrary joint boundary
amplitude. No tensor-product or factorization hypothesis is imposed on it. -/
theorem TorusDualCollar.correlatedBoundary_eq
    (C : TorusDualCollar width height) {a b : ℕ × ℕ}
    (p q : @Quiver.Path (ℕ × ℕ) (rectDualQuiver C.patch.cols C.patch.rows) a b)
    (U : G →* Matrix V V ℂ) (A : ∀ v, V → V → V → V → Phys v → ℂ)
    (hA : ∀ v, v ∈ C.swept → ∀ g, siteMap (A v) ∘ₗ torusLegRep U g = siteMap (A v))
    (σ : ∀ v : C.region, Phys v.1) (g : G)
    (B : (RegionBoundaryEndpoint torusLabelledBondTail torusLabelledBondHead C.region → V) → ℂ) :
    (∑ θ, B θ * torusOpenCoefficient C.region
      (fun v c ↦ A v.1 c.1 c.2.1 c.2.2.1 c.2.2.2 (σ v))
      (torusDualFluxBondMatrices U g
        (rectDualPathToTorus C.patch.origin.1 C.patch.origin.2 q)) θ) =
    ∑ θ, B θ * torusOpenCoefficient C.region
      (fun v c ↦ A v.1 c.1 c.2.1 c.2.2.1 c.2.2.2 (σ v))
      (torusDualFluxBondMatrices U g
        (rectDualPathToTorus C.patch.origin.1 C.patch.origin.2 p)) θ := by
  apply Finset.sum_congr rfl
  intro θ _
  rw [C.openCoefficient_eq p q U A hA σ g θ]

end TNLean.PEPS
