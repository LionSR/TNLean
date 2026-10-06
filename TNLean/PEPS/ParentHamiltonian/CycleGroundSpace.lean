/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.ParentHamiltonian.RegionGroundSpace
import TNLean.PEPS.CycleMPSInjectivity
import TNLean.MPS.ParentHamiltonian.GroundSpace

/-!
# Regional PEPS ground spaces on a cycle

On a nonempty proper arc of a cycle, a matrix product tensor has two
open boundary bonds. A general boundary condition on those two bonds
is a matrix, and contraction gives the usual trace pairing with the
ordered word product. Consequently the regional PEPS ground space is
the local matrix product ground space, after enumerating the arc sites.

Source: Cirac, Pérez-García, Schuch, and Verstraete, arXiv:2011.12127,
Section IV.C.1, the one-dimensional definition at lines 1987–2000 and
the corresponding graph construction at lines 2003–2011.
-/

open scoped BigOperators Matrix

namespace TNLean.PEPS

variable {n d D L : ℕ} [NeZero n]

/-- Physical configurations ordered along the arc.
Source: arXiv:2011.12127, local MPS physical space, lines 1987–2000. -/
def cycleArcConfigEquiv (hLn : L < n) (s : Fin n) :
    (Fin L → Fin d) ≃ RegionPhysicalConfig (d := d) (cycleArcFrom s L) :=
  Equiv.arrowCongr (arcSiteEquiv hLn s) (Equiv.refl (Fin d))

/-- Reading an arc configuration in site order is the inverse of its coordinate
enumeration. Source: arXiv:2011.12127, lines 1987–2000. -/
theorem arcWord_cycleArcConfigEquiv (hLn : L < n) (s : Fin n) (σ : Fin L → Fin d) :
    arcWord hLn s (cycleArcConfigEquiv hLn s σ) = σ := by
  funext j
  exact congrArg σ ((arcSiteEquiv hLn s).left_inv j)

/-- The two free boundary bonds are parametrized by their ordered endpoint values.
Source: arXiv:2011.12127, arbitrary MPS boundary conditions, lines 1987–2000. -/
def cycleArcBoundaryEquiv (hn : 3 ≤ n) (hL : 0 < L) (hLn : L < n)
    (A : MPSTensor d D) (s : Fin n) :
    (Fin D × Fin D) ≃ RegionBoundaryConfig (cycleTensorOfMPS hn A) (cycleArcFrom s L) where
  toFun p := arcBoundaryConfig hn hL hLn A s p.1 p.2
  invFun μ := (μ (arcLeftBoundary hn hL hLn s), μ (arcRightBoundary hn hL hLn s))
  left_inv p := by simp
  right_inv μ := arcBoundaryConfig_recon hn hL hLn A s μ

/-- A coefficient on the two open bonds is a boundary matrix, with the order
chosen so that contraction is the trace pairing.
Source: arXiv:2011.12127, lines 1987–2000. -/
def cycleArcBoundaryMatrixEquiv (hn : 3 ≤ n) (hL : 0 < L) (hLn : L < n)
    (A : MPSTensor d D) (s : Fin n) :
    (RegionBoundaryConfig (cycleTensorOfMPS hn A) (cycleArcFrom s L) → ℂ) ≃ₗ[ℂ]
      Matrix (Fin D) (Fin D) ℂ where
  toFun x b a := x (arcBoundaryConfig hn hL hLn A s a b)
  invFun X μ := X (μ (arcRightBoundary hn hL hLn s)) (μ (arcLeftBoundary hn hL hLn s))
  left_inv x := by
    funext μ
    exact congrArg x (arcBoundaryConfig_recon hn hL hLn A s μ)
  right_inv X := by
    funext b a
    simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Reordering physical coordinates identifies the regional and MPS physical spaces.
Source: arXiv:2011.12127, lines 1987–2011. -/
def cycleArcPhysicalEquiv (hLn : L < n) (s : Fin n) :
    (RegionPhysicalConfig (d := d) (cycleArcFrom s L) → ℂ) ≃ₗ[ℂ]
      MPSTensor.NSiteSpace d L :=
  LinearEquiv.funCongrLeft ℂ ℂ (cycleArcConfigEquiv hLn s)

/-- The globally indexed arc contraction and the genuine open contraction differ
only by the exterior assignment multiplicity. With the boundary matrix identified,
both give the usual MPS trace pairing. Source: arXiv:2011.12127,
one-dimensional and graph parent spaces, lines 1987–2011. -/
theorem exterior_mul_openRegionMap_cycleTensorOfMPS (hn : 3 ≤ n) (hL : 0 < L)
    (hLn : L < n) (A : MPSTensor d D) (s : Fin n)
    (x : RegionBoundaryConfig (cycleTensorOfMPS hn A) (cycleArcFrom s L) → ℂ) :
    (regionExteriorMultiplicity (cycleTensorOfMPS hn A) (cycleArcFrom s L) : ℂ) •
      cycleArcPhysicalEquiv hLn s (openRegionMap (cycleTensorOfMPS hn A) (cycleArcFrom s L) x) =
      (D : ℂ) ^ (n - (L + 1)) •
        MPSTensor.groundSpaceMap A L (cycleArcBoundaryMatrixEquiv hn hL hLn A s x) := by
  funext σ
  change (regionExteriorMultiplicity (cycleTensorOfMPS hn A) (cycleArcFrom s L) : ℂ) *
    (openRegionMap (cycleTensorOfMPS hn A) (cycleArcFrom s L) x)
      (cycleArcConfigEquiv hLn s σ) =
    (D : ℂ) ^ (n - (L + 1)) *
      MPSTensor.groundSpaceMap A L (cycleArcBoundaryMatrixEquiv hn hL hLn A s x) σ
  rw [openRegionMap_apply]
  have hweight (μ : RegionBoundaryConfig (cycleTensorOfMPS hn A) (cycleArcFrom s L)) :
      (regionExteriorMultiplicity (cycleTensorOfMPS hn A) (cycleArcFrom s L) : ℂ) *
        openRegionWeight (cycleTensorOfMPS hn A) (cycleArcFrom s L) μ
          (cycleArcConfigEquiv hLn s σ) =
      (D : ℂ) ^ (n - (L + 1)) * Kraus.evalWord A (List.ofFn σ)
        (μ (arcLeftBoundary hn hL hLn s)) (μ (arcRightBoundary hn hL hLn s)) := by
    rw [← regionBlockedWeight_eq_exterior_mul_openRegionWeight,
      regionBlockedWeight_cycleTensorOfMPS hn hL hLn A s, arcWord_cycleArcConfigEquiv]
  calc
    _ = ∑ μ, x μ * ((regionExteriorMultiplicity (cycleTensorOfMPS hn A)
        (cycleArcFrom s L) : ℂ) * openRegionWeight (cycleTensorOfMPS hn A)
          (cycleArcFrom s L) μ (cycleArcConfigEquiv hLn s σ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro μ _
      exact mul_left_comm _ _ _
    _ = (D : ℂ) ^ (n - (L + 1)) * ∑ μ, x μ * Kraus.evalWord A (List.ofFn σ)
        (μ (arcLeftBoundary hn hL hLn s)) (μ (arcRightBoundary hn hL hLn s)) := by
      simp only [hweight, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro μ _
      exact mul_left_comm _ _ _
    _ = _ := by
      congr 1
      rw [← Equiv.sum_comp (cycleArcBoundaryEquiv hn hL hLn A s), Fintype.sum_prod_type]
      simp only [cycleArcBoundaryEquiv, Equiv.coe_fn_mk, arcBoundaryConfig_left,
        arcBoundaryConfig_right, MPSTensor.groundSpaceMap_apply, Matrix.trace,
        Matrix.diag_apply, Matrix.mul_apply, cycleArcBoundaryMatrixEquiv,
        mul_comm]
      rfl

/-- For a positive bond dimension, the open-region map is the MPS boundary map
after an invertible scalar change of boundary coordinates. Source: arXiv:2011.12127,
the equivalence of the one-dimensional and graph definitions, lines 1987–2011. -/
theorem cycleArcPhysical_openRegionMap_eq_groundSpaceMap (hn : 3 ≤ n) (hL : 0 < L)
    (hLn : L < n) (hD : 0 < D) (A : MPSTensor d D) (s : Fin n)
    (x : RegionBoundaryConfig (cycleTensorOfMPS hn A) (cycleArcFrom s L) → ℂ) :
    cycleArcPhysicalEquiv hLn s (openRegionMap (cycleTensorOfMPS hn A) (cycleArcFrom s L) x) =
      MPSTensor.groundSpaceMap A L
        (((regionExteriorMultiplicity (cycleTensorOfMPS hn A) (cycleArcFrom s L) : ℂ)⁻¹ *
          (D : ℂ) ^ (n - (L + 1))) • cycleArcBoundaryMatrixEquiv hn hL hLn A s x) := by
  have hC : (regionExteriorMultiplicity (cycleTensorOfMPS hn A) (cycleArcFrom s L) : ℂ) ≠ 0 := by
    exact Nat.cast_ne_zero.mpr (regionExteriorMultiplicity_ne_zero _ _ (fun _ => Nat.ne_of_gt hD))
  have h := congrArg
    (fun v => (regionExteriorMultiplicity (cycleTensorOfMPS hn A) (cycleArcFrom s L) : ℂ)⁻¹ • v)
    (exterior_mul_openRegionMap_cycleTensorOfMPS hn hL hLn A s x)
  simpa only [map_smul, smul_smul, inv_mul_cancel₀ hC, one_smul] using h

/-- The graph-regional PEPS ground space on an arc is the usual local MPS ground
space, after ordering the physical sites. This holds also at bond dimension zero;
no injectivity hypothesis is required. Source: arXiv:2011.12127,
the one-dimensional specialization of the graph construction, lines 1987–2011. -/
theorem map_regionGroundSpace_cycleTensorOfMPS (hn : 3 ≤ n) (hL : 0 < L)
    (hLn : L < n) (A : MPSTensor d D) (s : Fin n) :
    (regionGroundSpace (cycleTensorOfMPS hn A) (cycleArcFrom s L)).map
      (cycleArcPhysicalEquiv hLn s).toLinearMap = MPSTensor.groundSpace A L := by
  by_cases hD : D = 0
  · subst D
    let : IsEmpty (RegionBoundaryConfig (cycleTensorOfMPS hn A) (cycleArcFrom s L)) :=
      ⟨fun μ => Fin.elim0 (μ (arcLeftBoundary hn hL hLn s))⟩
    apply le_antisymm
    · rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
      have hx : x = 0 := Subsingleton.elim _ _
      rw [hx, map_zero, map_zero]
      exact Submodule.zero_mem _
    · rintro _ ⟨X, rfl⟩
      have hX : X = 0 := Subsingleton.elim _ _
      rw [hX, map_zero]
      exact Submodule.zero_mem _
  · have hDpos : 0 < D := Nat.pos_of_ne_zero hD
    let c : ℂ := (regionExteriorMultiplicity (cycleTensorOfMPS hn A)
      (cycleArcFrom s L) : ℂ)⁻¹ * (D : ℂ) ^ (n - (L + 1))
    have hc : c ≠ 0 := by
      exact mul_ne_zero (inv_ne_zero (Nat.cast_ne_zero.mpr
        (regionExteriorMultiplicity_ne_zero _ _ (fun _ => hD))))
          (pow_ne_zero _ (Nat.cast_ne_zero.mpr hD))
    apply le_antisymm
    · rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
      exact ⟨c • cycleArcBoundaryMatrixEquiv hn hL hLn A s x,
        (cycleArcPhysical_openRegionMap_eq_groundSpaceMap hn hL hLn hDpos A s x).symm⟩
    · rintro _ ⟨X, rfl⟩
      let x := (cycleArcBoundaryMatrixEquiv hn hL hLn A s).symm (c⁻¹ • X)
      refine ⟨openRegionMap (cycleTensorOfMPS hn A) (cycleArcFrom s L) x, ⟨x, rfl⟩, ?_⟩
      change cycleArcPhysicalEquiv hLn s
        (openRegionMap (cycleTensorOfMPS hn A) (cycleArcFrom s L) x) = _
      rw [cycleArcPhysical_openRegionMap_eq_groundSpaceMap hn hL hLn hDpos A s]
      change MPSTensor.groundSpaceMap A L
        (c • cycleArcBoundaryMatrixEquiv hn hL hLn A s x) = _
      simp [x, smul_smul, hc]

end TNLean.PEPS
