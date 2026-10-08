/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.TorusBondFlatConnection
import TNLean.PEPS.TorusOperatorString

/-!
# Group gauge changes in the labelled torus contraction

A vertex gauge can be absorbed by locally invariant four-leg tensors in the
actual torus contraction. The tensors may differ from vertex to vertex, and
only vertices where the gauge is nontrivial need to be invariant. In particular,
one can sweep an explicit set of vertices with completely arbitrary tensors
and bond matrices in the exterior. Bonds with both endpoints outside the sweep
are unchanged, including the distinct parallel bonds of a two-by-two torus.

These are the local contraction identities behind Schuch, Cirac, and
Pérez-García, arXiv:1001.3807, `eq:2d:move-strings`, and the deformation part of
Lemma 6.14, lines 2205–2214. No flatness, semi-regularity, unitarity or injectivity
is needed beyond the virtual invariance used in that proof. These statements
concern a closed torus and do not assert an open-boundary identity.
-/

namespace TNLean.PEPS

variable {G V : Type*} [Group G] [Fintype V] [DecidableEq V]
variable {width height : ℕ} [NeZero width] [NeZero height]

/-- A group gauge change can be absorbed at its nontrivial vertices. The site
tensors and bond matrices elsewhere are arbitrary. Only invariance under the
particular group element applied at each vertex is needed.
Source: arXiv:1001.3807, `eq:2d:move-strings` and Lemma 6.14. -/
theorem torusBondNetwork_groupGauge_of_vecMul_eq (U : G →* Matrix V V ℂ)
    (A : TorusVertex width height → (V × V × V × V) → ℂ)
    (Oh Ov : TorusVertex width height → Matrix V V ℂ)
    (q : TorusVertex width height → G)
    (hA : ∀ v, q v ≠ 1 → Matrix.vecMul (A v) (torusLegMatrix U (q v)) = A v) :
    torusBondNetwork A
        (fun v ↦ U (q (v.1 + 1, v.2)) * Oh v * U (q v)⁻¹)
        (fun v ↦ U (q v) * Ov v * U (q (v.1, v.2 + 1))⁻¹) =
      torusBondNetwork A Oh Ov := by
  rw [torusBondNetwork_gauge _ Oh Ov (fun v ↦ U (q v)) (fun v ↦ U (q v)⁻¹)]
  congr 1
  funext v
  change Matrix.vecMul (A v) (torusLegMatrix U (q v)) = A v
  by_cases hv : q v = 1
  · simp [hv]
  · exact hA v hv

variable {Phys : TorusVertex width height → Type*}

/-- Sweeping a set of vertices leaves the contraction unchanged when the local
four-leg tensors in that set are invariant. All exterior tensors and original
bond matrices are arbitrary; physical index spaces may also vary with the
vertex. Source: arXiv:1001.3807, `eq:2d:move-strings` and Lemma 6.14. -/
theorem torusBondNetwork_groupGauge_of_invariant_on (U : G →* Matrix V V ℂ)
    (a : ∀ v, V → V → V → V → Phys v → ℂ)
    (S : Set (TorusVertex width height)) (q : TorusVertex width height → G)
    (hq : ∀ v, v ∉ S → q v = 1)
    (ha : ∀ v, v ∈ S → ∀ g, siteMap (a v) ∘ₗ torusLegRep U g = siteMap (a v))
    (σ : ∀ v, Phys v) (Oh Ov : TorusVertex width height → Matrix V V ℂ) :
    torusBondNetwork (fun v c ↦ a v c.1 c.2.1 c.2.2.1 c.2.2.2 (σ v))
        (fun v ↦ U (q (v.1 + 1, v.2)) * Oh v * U (q v)⁻¹)
        (fun v ↦ U (q v) * Ov v * U (q (v.1, v.2 + 1))⁻¹) =
      torusBondNetwork (fun v c ↦ a v c.1 c.2.1 c.2.2.1 c.2.2.2 (σ v)) Oh Ov := by
  apply torusBondNetwork_groupGauge_of_vecMul_eq
  intro v hv
  have hvs : v ∈ S := by
    by_contra hvs
    exact hv (hq v hvs)
  exact vecMul_torusLegMatrix_of_comp_eq U (a v) (ha v hvs) (q v) (σ v)

/-- Inhomogeneous locally invariant four-leg tensors absorb arbitrary group
gauges, with arbitrary initial matrices on every bond.
Source: arXiv:1001.3807, `eq:2d:move-strings` and Lemma 6.14. -/
theorem torusBondNetwork_groupGauge (U : G →* Matrix V V ℂ)
    (a : ∀ v, V → V → V → V → Phys v → ℂ)
    (ha : ∀ v g, siteMap (a v) ∘ₗ torusLegRep U g = siteMap (a v))
    (σ : ∀ v, Phys v) (q : TorusVertex width height → G)
    (Oh Ov : TorusVertex width height → Matrix V V ℂ) :
    torusBondNetwork (fun v c ↦ a v c.1 c.2.1 c.2.2.1 c.2.2.2 (σ v))
        (fun v ↦ U (q (v.1 + 1, v.2)) * Oh v * U (q v)⁻¹)
        (fun v ↦ U (q v) * Ov v * U (q (v.1, v.2 + 1))⁻¹) =
      torusBondNetwork (fun v c ↦ a v c.1 c.2.1 c.2.2.1 c.2.2.2 (σ v)) Oh Ov := by
  apply torusBondNetwork_groupGauge_of_vecMul_eq
  exact fun v _ ↦ vecMul_torusLegMatrix_of_comp_eq U (a v) (ha v) (q v) (σ v)

/-- A gauge of the actual horizontal and vertical group labels gives the same
contraction for inhomogeneous locally invariant tensors. Parallel bonds remain
distinct, and this includes positive periods one and two.
Source: arXiv:1001.3807, `eq:2d:move-strings` and Lemma 6.14. -/
theorem torusBondNetwork_torusBondGauge (U : G →* Matrix V V ℂ)
    (a : ∀ v, V → V → V → V → Phys v → ℂ)
    (ha : ∀ v g, siteMap (a v) ∘ₗ torusLegRep U g = siteMap (a v))
    (σ : ∀ v, Phys v) (q : TorusVertex width height → G)
    (p : TorusBondLabels width height G) :
    torusBondNetwork (fun v c ↦ a v c.1 c.2.1 c.2.2.1 c.2.2.2 (σ v))
        (fun v ↦ U ((torusBondGauge q p).1 v))
        (fun v ↦ U ((torusBondGauge q p).2 v)) =
      torusBondNetwork (fun v c ↦ a v c.1 c.2.1 c.2.2.1 c.2.2.2 (σ v))
        (fun v ↦ U (p.1 v)) (fun v ↦ U (p.2 v)) := by
  simpa only [torusBondGauge, map_mul] using
    torusBondNetwork_groupGauge U a ha σ q (fun v ↦ U (p.1 v)) (fun v ↦ U (p.2 v))

/-- The group-label contraction identity also holds for a gauge supported on a
set of invariant sites, leaving all other tensors unrestricted.
Source: arXiv:1001.3807, `eq:2d:move-strings` and Lemma 6.14. -/
theorem torusBondNetwork_torusBondGauge_of_invariant_on (U : G →* Matrix V V ℂ)
    (a : ∀ v, V → V → V → V → Phys v → ℂ)
    (S : Set (TorusVertex width height)) (q : TorusVertex width height → G)
    (hq : ∀ v, v ∉ S → q v = 1)
    (ha : ∀ v, v ∈ S → ∀ g, siteMap (a v) ∘ₗ torusLegRep U g = siteMap (a v))
    (σ : ∀ v, Phys v) (p : TorusBondLabels width height G) :
    torusBondNetwork (fun v c ↦ a v c.1 c.2.1 c.2.2.1 c.2.2.2 (σ v))
        (fun v ↦ U ((torusBondGauge q p).1 v))
        (fun v ↦ U ((torusBondGauge q p).2 v)) =
      torusBondNetwork (fun v c ↦ a v c.1 c.2.1 c.2.2.1 c.2.2.2 (σ v))
        (fun v ↦ U (p.1 v)) (fun v ↦ U (p.2 v)) := by
  simpa only [torusBondGauge, map_mul] using
    torusBondNetwork_groupGauge_of_invariant_on U a S q hq ha σ
      (fun v ↦ U (p.1 v)) (fun v ↦ U (p.2 v))

omit [Fintype V] [DecidableEq V] [NeZero width] [NeZero height] in
/-- A horizontal bond is untouched when the gauges at both endpoints are the
identity. The bond is indexed by its initial vertex, even at period two. -/
theorem torusBondGauge_fst_eq_of_eq_one (q : TorusVertex width height → G)
    (p : TorusBondLabels width height G) (v : TorusVertex width height)
    (hv : q v = 1) (hr : q (v.1 + 1, v.2) = 1) :
    (torusBondGauge q p).1 v = p.1 v := by
  simp [torusBondGauge, hv, hr]

omit [Fintype V] [DecidableEq V] [NeZero width] [NeZero height] in
/-- A vertical bond is untouched when the gauges at both endpoints are the
identity, in the native downward insertion convention. -/
theorem torusBondGauge_snd_eq_of_eq_one (q : TorusVertex width height → G)
    (p : TorusBondLabels width height G) (v : TorusVertex width height)
    (hv : q v = 1) (hu : q (v.1, v.2 + 1) = 1) :
    (torusBondGauge q p).2 v = p.2 v := by
  simp [torusBondGauge, hv, hu]

omit [Fintype V] [DecidableEq V] [NeZero width] [NeZero height] in
/-- Every horizontal bond with both endpoints outside a swept set is unchanged. -/
theorem torusBondGauge_fst_eq_of_not_mem (S : Set (TorusVertex width height))
    (q : TorusVertex width height → G) (hq : ∀ v, v ∉ S → q v = 1)
    (p : TorusBondLabels width height G) (v : TorusVertex width height)
    (hv : v ∉ S) (hr : (v.1 + 1, v.2) ∉ S) :
    (torusBondGauge q p).1 v = p.1 v :=
  torusBondGauge_fst_eq_of_eq_one q p v (hq v hv) (hq _ hr)

omit [Fintype V] [DecidableEq V] [NeZero width] [NeZero height] in
/-- Every vertical bond with both endpoints outside a swept set is unchanged. -/
theorem torusBondGauge_snd_eq_of_not_mem (S : Set (TorusVertex width height))
    (q : TorusVertex width height → G) (hq : ∀ v, v ∉ S → q v = 1)
    (p : TorusBondLabels width height G) (v : TorusVertex width height)
    (hv : v ∉ S) (hu : (v.1, v.2 + 1) ∉ S) :
    (torusBondGauge q p).2 v = p.2 v :=
  torusBondGauge_snd_eq_of_eq_one q p v (hq v hv) (hq _ hu)

end TNLean.PEPS
