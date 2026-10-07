/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.TorusCutBoundary
import TNLean.PEPS.TorusClosureSeams

/-!
# Commuting closures belong to the four actual cut spaces

For site-dependent invariant tensors, each commuting closure has an explicit
boundary tensor on every cut. Thus the commuting closure span lies in the
intersection of the four two-by-two cut spaces of SCP10, Theorem 5.5.
This proves the first inclusion using actual contractions and arbitrary
correlated-boundary range spaces, without any parent-kernel classification.

The representation in this file is the same on every bond. Matching virtual
representations are therefore explicit: both endpoints of every horizontal
and vertical bond use `U`. Neither semi-regularity nor local injectivity is
needed for this inclusion. The reverse inclusion, and the source's allowance
of distinct matching semi-regular representations on different bonds, are
not asserted here.
-/

namespace TNLean.PEPS

variable {G V Phys : Type*} [Group G] [Fintype V] [DecidableEq V]
variable {width height : ℕ} [NeZero width] [NeZero height]

/-- An actual native closure with a possibly different tensor at every site.
Source: SCP10, Theorem 5.5, with its four tensors `A,B,C,D`. -/
def sitewiseTorusGClosure (U : G →* Matrix V V ℂ)
    (a : TorusVertex width height → V → V → V → V → Phys → ℂ)
    (g h : G) (σ : TorusVertex width height → Phys) : ℂ :=
  torusBondNetwork (fun v t ↦ a v t.1 t.2.1 t.2.2.1 t.2.2.2 (σ v))
    (torusHorizontalClosure U h) (torusVerticalClosure U g)

/-- For a constant site family, the sitewise closure is the existing native closure. -/
@[simp]
theorem sitewiseTorusGClosure_const (U : G →* Matrix V V ℂ)
    (a : V → V → V → V → Phys → ℂ) (g h : G) :
    sitewiseTorusGClosure (width := width) (height := height) U (fun _ ↦ a) g h =
      torusGClosure U a g h := rfl

/-- The source's seam-displacement identity permits distinct local tensors.
The proof tags the physical alphabet by its site and uses each site's own
invariance identity. Source: SCP10, Theorem 5.5 and `eq:2d:move-strings`. -/
theorem torusBondNetwork_closureAt_eq_sitewiseTorusGClosure
    (U : G →* Matrix V V ℂ)
    (a : TorusVertex width height → V → V → V → V → Phys → ℂ)
    (ha : ∀ v g, siteMap (a v) ∘ₗ torusLegRep U g = siteMap (a v))
    (g h : G) (hgh : Commute g h) (c : ZMod width) (r : ZMod height)
    (σ : TorusVertex width height → Phys) :
    torusBondNetwork (fun v t ↦ a v t.1 t.2.1 t.2.2.1 t.2.2.2 (σ v))
        (torusHorizontalClosureAt U h c) (torusVerticalClosureAt U g r) =
      sitewiseTorusGClosure U a g h σ := by
  let b : V → V → V → V → (TorusVertex width height × Phys) → ℂ :=
    fun t r d l p ↦ a p.1 t r d l p.2
  have hb : ∀ k, siteMap b ∘ₗ torusLegRep U k = siteMap b := by
    intro k
    apply LinearMap.ext
    intro x
    funext p
    exact congrFun (LinearMap.congr_fun (ha p.1 k) x) p.2
  exact torusBondNetwork_closureAt_eq_torusGClosure U b hb g h hgh c r
    (fun v ↦ (v, σ v))

/-- A product of the actual representation matrices is a concrete boundary
witness for each commuting closure, on every cut. -/
theorem torusCutMap_closureBoundary (U : G →* Matrix V V ℂ)
    (a : TorusVertex width height → V → V → V → V → Phys → ℂ)
    (ha : ∀ v g, siteMap (a v) ∘ₗ torusLegRep U g = siteMap (a v))
    (g h : G) (hgh : Commute g h) (c : ZMod width) (r : ZMod height) :
    torusCutMap a c r (torusCutBondBoundary c r (fun _ ↦ U h) (fun _ ↦ U g)) =
      sitewiseTorusGClosure U a g h := by
  funext σ
  rw [torusCutMap_apply, torusCutCoeff_bondBoundary]
  exact torusBondNetwork_closureAt_eq_sitewiseTorusGClosure U a ha g h hgh c r σ

/-- Actual commuting closures belong to each actual arbitrary-boundary cut space. -/
theorem sitewiseTorusGClosure_mem_torusCutSpace (U : G →* Matrix V V ℂ)
    (a : TorusVertex width height → V → V → V → V → Phys → ℂ)
    (ha : ∀ v g, siteMap (a v) ∘ₗ torusLegRep U g = siteMap (a v))
    (g h : G) (hgh : Commute g h) (c : ZMod width) (r : ZMod height) :
    sitewiseTorusGClosure U a g h ∈ torusCutSpace a c r :=
  ⟨torusCutBondBoundary c r (fun _ ↦ U h) (fun _ ↦ U g),
    torusCutMap_closureBoundary U a ha g h hgh c r⟩

/-- The span uses commuting labels and actual site-dependent native closures. -/
def sitewiseCommutingClosureSpan (U : G →* Matrix V V ℂ)
    (a : TorusVertex width height → V → V → V → V → Phys → ℂ) :
    Submodule ℂ ((TorusVertex width height → Phys) → ℂ) :=
  Submodule.span ℂ (Set.range fun p : {p : G × G // Commute p.1 p.2} ↦
    sitewiseTorusGClosure U a p.1.1 p.1.2)

/-- The forward inclusion of the four-block closure theorem for arbitrary
site-dependent invariant tensors with one matching bond representation.
Source: SCP10, Theorem 5.5, the first sentence of its proof. -/
theorem sitewiseCommutingClosureSpan_le_fourTorusCutSpace
    (U : G →* Matrix V V ℂ)
    (a : TorusVertex 2 2 → V → V → V → V → Phys → ℂ)
    (ha : ∀ v g, siteMap (a v) ∘ₗ torusLegRep U g = siteMap (a v)) :
    sitewiseCommutingClosureSpan U a ≤ fourTorusCutSpace a := by
  apply Submodule.span_le.mpr
  rintro _ ⟨p, rfl⟩
  apply (mem_fourTorusCutSpace_iff a _).mpr
  intro c r
  exact (mem_torusCutSpace_iff a c r _).mp
    (sitewiseTorusGClosure_mem_torusCutSpace U a ha p.1.1 p.1.2 p.2 c r)

end TNLean.PEPS
