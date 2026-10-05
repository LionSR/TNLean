/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.TorusCutClosureMembership
import TNLean.PEPS.GInjectiveTorusProjector

/-!
# Site-dependent physical maps on the actual cut contractions

A different rectangular physical map may be applied at each site, before or
after contracting an arbitrary correlated cut boundary. This is the actual
local-inverse operation in the proof of SCP10, Theorem 5.5, rather than an
assumed relation between abstract boundary spaces.
-/

open scoped BigOperators Matrix

namespace TNLean.PEPS

variable {V Phys Out : Type*} [Fintype V] [DecidableEq V] [Fintype Phys]
variable {width height : ℕ} [NeZero width] [NeZero height]

/-- A product of site-dependent physical matrices on the torus. -/
def torusSitewisePhysicalMap
    (F : TorusVertex width height → Matrix Out Phys ℂ) :
    ((TorusVertex width height → Phys) → ℂ) →ₗ[ℂ]
      ((TorusVertex width height → Out) → ℂ) :=
  Matrix.mulVecLin (fun τ σ ↦ ∏ v, F v (τ v) (σ v))

/-- Site-dependent physical maps commute with an arbitrary correlated cut
boundary contraction. Source: SCP10, Theorem 5.5, `eq:2d:closure-inv`. -/
theorem torusSitewisePhysicalMap_torusCutMap
    (F : TorusVertex width height → Matrix Out Phys ℂ)
    (a : TorusVertex width height → V → V → V → V → Phys → ℂ)
    (c : ZMod width) (r : ZMod height)
    (M : TorusCutBoundaryConfig width height V → ℂ) :
    torusSitewisePhysicalMap F (torusCutMap a c r M) =
      torusCutMap (fun v ↦ physicalMapSite (F v) (a v)) c r M := by
  funext τ
  change (∑ σ, (∏ v, F v (τ v) (σ v)) * torusCutCoeff a c r M σ) = _
  simp only [torusCutMap_apply, torusCutCoeff, physicalMapSite, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun β _ ↦ ?_
  rw [Fintype.prod_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ ↦ ?_
  simp only [Finset.prod_mul_distrib]
  ring

omit [DecidableEq V] in
/-- The same site-dependent map identity for the uncut operator network. -/
theorem torusSitewisePhysicalMap_torusBondNetwork
    (F : TorusVertex width height → Matrix Out Phys ℂ)
    (a : TorusVertex width height → V → V → V → V → Phys → ℂ)
    (Oh Ov : TorusVertex width height → Matrix V V ℂ) :
    torusSitewisePhysicalMap F
        (fun σ ↦ torusBondNetwork (fun v t ↦ a v t.1 t.2.1 t.2.2.1 t.2.2.2 (σ v)) Oh Ov) =
      fun τ ↦ torusBondNetwork
        (fun v t ↦ physicalMapSite (F v) (a v) t.1 t.2.1 t.2.2.1 t.2.2.2 (τ v)) Oh Ov := by
  funext τ
  change (∑ σ : TorusVertex width height → Phys, (∏ v, F v (τ v) (σ v)) * _) = _
  simp only [torusBondNetwork, physicalMapSite, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun β _ ↦ ?_
  rw [Fintype.prod_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ ↦ ?_
  simp only [Finset.prod_mul_distrib]
  ring

variable {G : Type*} [Group G]

/-- Applying distinct local physical maps sends each actual native closure to
the corresponding closure of the transformed tensors. -/
theorem torusSitewisePhysicalMap_sitewiseTorusGClosure
    (U : G →* Matrix V V ℂ)
    (F : TorusVertex width height → Matrix Out Phys ℂ)
    (a : TorusVertex width height → V → V → V → V → Phys → ℂ) (g h : G) :
    torusSitewisePhysicalMap F (sitewiseTorusGClosure U a g h) =
      sitewiseTorusGClosure U (fun v ↦ physicalMapSite (F v) (a v)) g h :=
  torusSitewisePhysicalMap_torusBondNetwork F a _ _

end TNLean.PEPS
