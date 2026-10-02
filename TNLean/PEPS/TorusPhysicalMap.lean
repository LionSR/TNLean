/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.TorusGClosure
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Physical linear maps on actual torus contractions

Applying one rectangular linear map at every physical site commutes with the
contraction of the virtual bonds. The product of the physical matrix entries is
the matrix of the full physical map. Expanding the actual bond-network sum then
reduces its action to the corresponding map of each site coefficient.

This is the contraction identity used when applying a local G-injective left
inverse in Schuch, Cirac, and Pérez-García, arXiv:1001.3807, Theorem 5.9,
`Papers/1001.3807/paper_v3.tex`, lines 1582–1621. The identity itself requires
neither G-injectivity nor isometry and permits arbitrary bond operators.
-/

open scoped BigOperators Matrix

namespace TNLean.PEPS

variable {V Phys Out : Type*} [Fintype Phys]

/-- The four-leg site tensor after a rectangular physical linear map is applied.
Source: SCP10, local left-inverse operation in Theorem 5.9, lines 1582–1621. -/
def physicalMapSite (F : Matrix Out Phys ℂ)
    (a : V → V → V → V → Phys → ℂ) (t r b l : V) (q : Out) : ℂ :=
  ∑ s : Phys, F q s * a t r b l s

/-- Applying a physical matrix to the coefficients composes the original site
map with that same linear map. Source: SCP10, Theorem 5.9, lines 1582–1621. -/
theorem siteMap_physicalMapSite [Fintype V] (F : Matrix Out Phys ℂ)
    (a : V → V → V → V → Phys → ℂ) :
    siteMap (physicalMapSite F a) = Matrix.mulVecLin F ∘ₗ siteMap a := by
  simp only [siteMap, ← Matrix.mulVecLin_mul]
  congr 1

/-- The product matrix of one physical map on a finite set of sites.
Rows and columns may have different physical dimensions.
Source: SCP10, Theorem 5.9, lines 1582–1621. -/
def physicalProductMatrix (Site : Type*) [Fintype Site] (F : Matrix Out Phys ℂ) :
    Matrix (Site → Out) (Site → Phys) ℂ :=
  fun τ σ => ∏ v, F (τ v) (σ v)

/-- The physical linear map acting at every site in a finite set.
Source: SCP10, Theorem 5.9, lines 1582–1621. -/
def physicalProductMap (Site : Type*) [Fintype Site] [DecidableEq Site]
    (F : Matrix Out Phys ℂ) : ((Site → Phys) → ℂ) →ₗ[ℂ] ((Site → Out) → ℂ) :=
  Matrix.mulVecLin (physicalProductMatrix Site F)

/-- The coefficient of a product of physical linear maps. -/
theorem physicalProductMap_apply (Site : Type*) [Fintype Site] [DecidableEq Site]
    (F : Matrix Out Phys ℂ) (ψ : (Site → Phys) → ℂ) (τ : Site → Out) :
    physicalProductMap Site F ψ τ = ∑ σ : Site → Phys,
      (∏ v, F (τ v) (σ v)) * ψ σ := rfl

variable {width height : ℕ} [NeZero width] [NeZero height]

/-- The physical product map on the actual torus vector.
Source: SCP10, Theorem 5.9, lines 1582–1621. -/
abbrev torusPhysicalMap (F : Matrix Out Phys ℂ) :
    ((TorusVertex width height → Phys) → ℂ) →ₗ[ℂ]
      ((TorusVertex width height → Out) → ℂ) :=
  physicalProductMap (TorusVertex width height) F

/-- The full physical map is the sum of its product matrix entries against the
original physical coefficients. -/
theorem torusPhysicalMap_apply (F : Matrix Out Phys ℂ)
    (ψ : (TorusVertex width height → Phys) → ℂ) (τ : TorusVertex width height → Out) :
    torusPhysicalMap F ψ τ = ∑ σ : TorusVertex width height → Phys,
      (∏ v, F (τ v) (σ v)) * ψ σ := rfl

variable [Fintype V]

/-- Source: SCP10, Theorem 5.9, lines 1582–1621. A physical linear map at each
site can be applied before or after the actual virtual-bond contraction.
The original horizontal and vertical bond matrices are retained. -/
theorem torusPhysicalMap_torusBondNetwork
    (F : Matrix Out Phys ℂ)
    (a : TorusVertex width height → (V × V × V × V) → Phys → ℂ)
    (Oh Ov : TorusVertex width height → Matrix V V ℂ) :
    torusPhysicalMap F
        (fun σ => torusBondNetwork (fun v c => a v c (σ v)) Oh Ov) =
      fun τ => torusBondNetwork
        (fun v c => ∑ s : Phys, F (τ v) s * a v c s) Oh Ov := by
  funext τ
  simp only [torusPhysicalMap_apply, torusBondNetwork, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro β _
  rw [Fintype.prod_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  simp only [Finset.prod_mul_distrib]
  ring

variable {G : Type*} [Group G] [DecidableEq V]

/-- Source: SCP10, Theorem 5.9, lines 1582–1621. Applying the product physical
map to an actual native closure equals closing the physically transformed site
coefficients. This permits arbitrary rectangular physical matrices. -/
theorem torusPhysicalMap_torusGClosure (U : G →* Matrix V V ℂ)
    (F : Matrix Out Phys ℂ) (a : V → V → V → V → Phys → ℂ) (g h : G) :
    torusPhysicalMap (width := width) (height := height) F (torusGClosure U a g h) =
      torusGClosure U (physicalMapSite F a) g h := by
  exact torusPhysicalMap_torusBondNetwork F
      (fun (_ : TorusVertex width height) c s => a c.1 c.2.1 c.2.2.1 c.2.2.2 s)
      (torusHorizontalClosure U h) (torusVerticalClosure U g)

end TNLean.PEPS
