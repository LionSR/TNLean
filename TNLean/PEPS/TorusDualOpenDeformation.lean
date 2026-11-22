/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.TorusDualCollar
import TNLean.PEPS.TorusLabelledOpenCoefficient

/-!
# Open-boundary deformation with internal swept vertex stars

For a generated homotopy supported on a set of vertices, assume every bond
incident to that set is internal to the open region. The derived gauge is then
identity at both endpoints of every crossing bond. Delta completion gives
equality of actual open coefficients and contraction with an arbitrary joint
boundary tensor. The region need not be rectangular or connected. The collared
rectangle results follow from their geometric internal-star theorem.

**Scope restriction (supported open-boundary deformation):** These results
extend SCP10, arXiv:1001.3807v3, Lemma 6.14 to arbitrary open regions with
internal swept vertex stars, conditional on the generated geometric homotopy.
They do not construct a deformation avoiding an arbitrary region, classify
homotopies, identify winding sectors, or equate vacuum reduced density matrices.
The collared rectangular specialization retains `W + 1 < w` and `H + 1 < h`.
Documented in `docs/paper-gaps/scp10_dual_flux_string_deformation.tex`, section
"Supported open-boundary continuation".
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
/-- The gauge derived from a generated homotopy also transforms the internal
matrices of any region containing every swept vertex star. On noninternal
bonds both endpoint gauges are identity. Source: SCP10, Lemma 6.14. -/
theorem TorusDualHomotopy.exists_internalFluxGauge
    {S R : Set X} {a b : X} {p q : TorusDualPath a b}
    (h : TorusDualHomotopy S p q)
    (hR : ∀ e : E, torusLabelledBondTail e ∈ S ∨ torusLabelledBondHead e ∈ S →
      torusLabelledBondTail e ∈ R ∧ torusLabelledBondHead e ∈ R)
    (U : G →* Matrix V V ℂ) (g : G) :
    ∃ k : X → G, (∀ v, v ∉ S → k v = 1) ∧ ∀ e : E,
      internalBondMatrices torusLabelledBondTail torusLabelledBondHead R
          (torusDualFluxBondMatrices U g q) e =
      U (k (torusLabelledBondHead e)) *
        internalBondMatrices torusLabelledBondTail torusLabelledBondHead R
          (torusDualFluxBondMatrices U g p) e *
        U (k (torusLabelledBondTail e))⁻¹ := by
  obtain ⟨k, hk, heq⟩ := h.exists_fluxGauge g
  refine ⟨k, hk, ?_⟩
  intro e
  by_cases he : torusLabelledBondTail e ∈ R ∧ torusLabelledBondHead e ∈ R
  · simp only [internalBondMatrices, he]
    rcases e with ⟨v, d⟩
    cases d <;> simp [torusDualFluxBondMatrices, heq, torusBondGauge,
      torusLabelledBondHead, torusLabelledBondTail, map_mul]
  · have ht : torusLabelledBondTail e ∉ S := fun hv ↦ he (hR e (.inl hv))
    have hh : torusLabelledBondHead e ∉ S := fun hv ↦ he (hR e (.inr hv))
    simp [internalBondMatrices, he, hk _ ht, hk _ hh]

omit [NeZero width] [NeZero height] in
open Classical in
/-- The collar contains every swept vertex star, so the homotopy-derived gauge
transforms its internal matrices. Source: SCP10, Lemma 6.14. -/
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
        U (k (torusLabelledBondTail e))⁻¹ :=
  (C.patch.homotopy p q).exists_internalFluxGauge C.incident_internal U g

variable {Phys : TorusVertex width height → Type*}

open Classical in
/-- Generated homotopies with internal swept vertex stars preserve every fixed
open boundary coefficient on an arbitrary region. The gauge and its boundary
behavior are derived; empty regions and empty virtual alphabets are allowed.
Source: SCP10, arXiv:1001.3807v3, Lemma 6.14. -/
theorem TorusDualHomotopy.openCoefficient_eq
    {S R : Set X} {a b : X} {p q : TorusDualPath a b}
    (h : TorusDualHomotopy S p q)
    (hR : ∀ e : E, torusLabelledBondTail e ∈ S ∨ torusLabelledBondHead e ∈ S →
      torusLabelledBondTail e ∈ R ∧ torusLabelledBondHead e ∈ R)
    (U : G →* Matrix V V ℂ) (A : ∀ v, V → V → V → V → Phys v → ℂ)
    (hA : ∀ v, v ∈ S → ∀ g, siteMap (A v) ∘ₗ torusLegRep U g = siteMap (A v))
    (σ : ∀ v : R, Phys v.1) (g : G)
    (θ : RegionBoundaryEndpoint torusLabelledBondTail torusLabelledBondHead R → V) :
    torusOpenCoefficient R
      (fun v c ↦ A v.1 c.1 c.2.1 c.2.2.1 c.2.2.2 (σ v))
      (torusDualFluxBondMatrices U g q) θ =
    torusOpenCoefficient R
      (fun v c ↦ A v.1 c.1 c.2.1 c.2.2.1 c.2.2.2 (σ v))
      (torusDualFluxBondMatrices U g p) θ := by
  classical
  by_cases hn : Nonempty V
  · obtain ⟨v₀⟩ := hn
    let F : R → (V × V × V × V) → ℂ :=
      fun v c ↦ A v.1 c.1 c.2.1 c.2.2.1 c.2.2.2 (σ v)
    obtain ⟨k, hk, he⟩ := h.exists_internalFluxGauge hR U g
    rw [← torusBondNetwork_deltaCompletedTensor _ _ _ v₀,
      ← torusBondNetwork_deltaCompletedTensor _ _ _ v₀]
    have hh := fun v ↦ he (v, false)
    have hv := fun v ↦ he (v, true)
    simp only [torusLabelledBondHead, torusLabelledBondTail, Bool.false_eq_true,
      ite_false, ite_true] at hh hv
    simp_rw [hh, hv]
    apply torusBondNetwork_groupGauge_of_vecMul_eq U
    intro v hkv
    have hs : v ∈ S := by
      by_contra hs
      exact hkv (hk v hs)
    have hr : v ∈ R := (hR (v, false) (.inl hs)).1
    have hinside : torusDeltaCompletedTensor R F v₀ θ v = F ⟨v, hr⟩ := by
      funext c
      simp [torusDeltaCompletedTensor, deltaCompletedTensor, hr]
    change Matrix.vecMul (torusDeltaCompletedTensor R F v₀ θ v)
      (torusLegMatrix U (k v)) = torusDeltaCompletedTensor R F v₀ θ v
    rw [hinside]
    exact vecMul_torusLegMatrix_of_comp_eq U (A v) (hA v hs) (k v) (σ ⟨v, hr⟩)
  · let : IsEmpty V := not_nonempty_iff.mp hn
    have he : torusDualFluxBondMatrices U g q = torusDualFluxBondMatrices U g p := by
      funext e i
      exact isEmptyElim i
    rw [he]

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
        (rectDualPathToTorus C.patch.origin.1 C.patch.origin.2 p)) θ :=
  (C.patch.homotopy p q).openCoefficient_eq C.incident_internal U A hA σ g θ

open Classical in
/-- Generated homotopies with internal swept vertex stars preserve contraction
against every joint boundary tensor on an arbitrary region. No factorization
hypothesis is imposed. Source: SCP10, arXiv:1001.3807v3, Lemma 6.14. -/
theorem TorusDualHomotopy.correlatedBoundary_eq
    {S R : Set X} {a b : X} {p q : TorusDualPath a b}
    (h : TorusDualHomotopy S p q)
    (hR : ∀ e : E, torusLabelledBondTail e ∈ S ∨ torusLabelledBondHead e ∈ S →
      torusLabelledBondTail e ∈ R ∧ torusLabelledBondHead e ∈ R)
    (U : G →* Matrix V V ℂ) (A : ∀ v, V → V → V → V → Phys v → ℂ)
    (hA : ∀ v, v ∈ S → ∀ g, siteMap (A v) ∘ₗ torusLegRep U g = siteMap (A v))
    (σ : ∀ v : R, Phys v.1) (g : G)
    (B : (RegionBoundaryEndpoint torusLabelledBondTail torusLabelledBondHead R → V) → ℂ) :
    (∑ θ, B θ * torusOpenCoefficient R
      (fun v c ↦ A v.1 c.1 c.2.1 c.2.2.1 c.2.2.2 (σ v))
      (torusDualFluxBondMatrices U g q) θ) =
    ∑ θ, B θ * torusOpenCoefficient R
      (fun v c ↦ A v.1 c.1 c.2.1 c.2.2.1 c.2.2.2 (σ v))
      (torusDualFluxBondMatrices U g p) θ := by
  apply Finset.sum_congr rfl
  intro θ _
  rw [h.openCoefficient_eq hR U A hA σ g θ]

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
        (rectDualPathToTorus C.patch.origin.1 C.patch.origin.2 p)) θ :=
  (C.patch.homotopy p q).correlatedBoundary_eq C.incident_internal U A hA σ g B

end TNLean.PEPS
