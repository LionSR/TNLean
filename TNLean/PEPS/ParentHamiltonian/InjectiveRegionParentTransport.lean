/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.ParentHamiltonian.InjectiveVertexCoordinates
import TNLean.PEPS.ParentHamiltonian.RegionParentHamiltonian
import QICLean.Algebra.MatrixAux
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Positive interactions transported through injective site maps

An injective product of site maps need not fill the physical region.
Conjugating a virtual interaction by the product left inverse therefore
leaves additional physical vectors in its kernel. Adding the square of
the reconstruction defect removes precisely those vectors. The resulting
positive interaction has the image of the virtual kernel as its kernel.

This is a finite-region consequence of the inverse-adjoint deformation
argument in CPGSV21, arXiv:2011.12127, Section IV.C.1,
lines 2017–2044. The reconstruction penalty acts on the entire chosen
region; locality of a sum of edge interactions is a separate assertion.

**Local fix (physical reconstruction):** The bare inverse-adjoint formula
`eq:4:deformed-parent-1` does not have the claimed exact physical kernel for
rectangular injective site maps. The reconstruction penalty corrects this
source error, as documented in
`docs/paper-gaps/cpgsv21_injective_parent_reconstruction.tex`.
-/

open scoped Matrix ComplexOrder

namespace TNLean.PEPS

private theorem injective_transport_mulVec_eq_zero_iff
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (T : Matrix J I ℂ) (L : Matrix I J ℂ) (hLT : L * T = 1)
    (H : Matrix I I ℂ) (hH : H.PosSemidef) (ψ : J → ℂ) :
    (L.conjTranspose * H * L +
      (1 - T * L).conjTranspose * (1 - T * L)) *ᵥ ψ = 0 ↔
      H *ᵥ (L *ᵥ ψ) = 0 ∧ T *ᵥ (L *ᵥ ψ) = ψ := by
  let Q := 1 - T * L
  have hp : (L.conjTranspose * H * L).PosSemidef := hH.conjTranspose_mul_mul_same L
  have hq : (Q.conjTranspose * Q).PosSemidef := Matrix.posSemidef_conjTranspose_mul_self Q
  have hTL : T.conjTranspose * L.conjTranspose = 1 := by
    rw [← Matrix.conjTranspose_mul, hLT, Matrix.conjTranspose_one]
  have hQ : Q *ᵥ ψ = 0 ↔ T *ᵥ (L *ᵥ ψ) = ψ := by
    simp only [Q, Matrix.sub_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec,
      sub_eq_zero, eq_comm]
  constructor
  · intro hψ
    have hh := hp.mulVec_eq_zero_left hq ψ hψ
    have hqψ := hq.mulVec_eq_zero_left hp ψ (by rwa [add_comm])
    have hh' := congrArg (fun x => T.conjTranspose *ᵥ x) hh
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
      hTL, Matrix.one_mulVec, Matrix.mulVec_zero] at hh'
    exact ⟨hh', hQ.mp ((Matrix.conjTranspose_mul_self_mulVec_eq_zero _ _).mp hqψ)⟩
  · rintro ⟨hh, ht⟩
    change (L.conjTranspose * H * L + Q.conjTranspose * Q) *ᵥ ψ = 0
    rw [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hh,
      Matrix.mulVec_zero, ← Matrix.mulVec_mulVec, hQ.mpr ht, Matrix.mulVec_zero, add_zero]

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj] {d : ℕ}

/-- Inverse-adjoint transport, with the square of the regional reconstruction
defect added to constrain physical vectors to the site-map image.
Source: finite-region consequence of the injective deformation argument
in CPGSV21, Section IV.C.1, lines 2017–2044. -/
noncomputable def injectiveRegionParentTransport (A : Tensor Γ d)
    (hA : IsVertexInjective A) (R : Finset V)
    (H : Matrix (RegionVertexVirtualConfig A R) (RegionVertexVirtualConfig A R) ℂ) :
    Matrix (RegionPhysicalConfig (d := d) R) (RegionPhysicalConfig (d := d) R) ℂ :=
  let T := LinearMap.toMatrix' (regionVertexTensorMap A R)
  let L := LinearMap.toMatrix' (regionVertexLeftInverse A hA R)
  L.conjTranspose * H * L + (1 - T * L).conjTranspose * (1 - T * L)

/-- A positive virtual interaction gives a positive regional physical interaction.
Source: inverse-adjoint positivity in CPGSV21, lines 2017–2044. -/
theorem injectiveRegionParentTransport_posSemidef (A : Tensor Γ d)
    (hA : IsVertexInjective A) (R : Finset V)
    (H : Matrix (RegionVertexVirtualConfig A R) (RegionVertexVirtualConfig A R) ℂ)
    (hH : H.PosSemidef) : (injectiveRegionParentTransport A hA R H).PosSemidef := by
  exact (hH.conjTranspose_mul_mul_same _).add (Matrix.posSemidef_conjTranspose_mul_self _)

/-- A transported ground vector is exactly a reconstructed virtual ground vector.
Source: finite-region inverse-and-reconstruction consequence of CPGSV21,
Section IV.C.1, lines 2017–2044. -/
theorem injectiveRegionParentTransport_mulVec_eq_zero_iff (A : Tensor Γ d)
    (hA : IsVertexInjective A) (R : Finset V)
    (H : Matrix (RegionVertexVirtualConfig A R) (RegionVertexVirtualConfig A R) ℂ)
    (hH : H.PosSemidef) (ψ : RegionPhysicalConfig (d := d) R → ℂ) :
    injectiveRegionParentTransport A hA R H *ᵥ ψ = 0 ↔
      H *ᵥ regionVertexLeftInverse A hA R ψ = 0 ∧
        regionVertexTensorMap A R (regionVertexLeftInverse A hA R ψ) = ψ := by
  classical
  have hLT : LinearMap.toMatrix' (regionVertexLeftInverse A hA R) *
      LinearMap.toMatrix' (regionVertexTensorMap A R) = 1 := by
    rw [← LinearMap.toMatrix'_comp, regionVertexLeftInverse_comp_regionVertexTensorMap,
      LinearMap.toMatrix'_id]
  simpa only [injectiveRegionParentTransport, LinearMap.toMatrix'_mulVec] using
    injective_transport_mulVec_eq_zero_iff _ _ hLT H hH ψ

/-- The physical kernel is precisely the image of the virtual kernel under
the injective regional product map. Source: finite-region consequence of
the ground-space deformation in CPGSV21, Section IV.C.1, lines 2017–2044. -/
theorem ker_injectiveRegionParentTransport (A : Tensor Γ d)
    (hA : IsVertexInjective A) (R : Finset V)
    (H : Matrix (RegionVertexVirtualConfig A R) (RegionVertexVirtualConfig A R) ℂ)
    (hH : H.PosSemidef) :
    (Matrix.mulVecLin (injectiveRegionParentTransport A hA R H)).ker =
      (Matrix.mulVecLin H).ker.map (regionVertexTensorMap A R) := by
  ext ψ
  rw [LinearMap.mem_ker, Matrix.mulVecLin_apply,
    injectiveRegionParentTransport_mulVec_eq_zero_iff A hA R H hH]
  constructor
  · rintro ⟨hh, ht⟩
    exact ⟨regionVertexLeftInverse A hA R ψ, hh, ht⟩
  · rintro ⟨x, hx, rfl⟩
    have hLx : regionVertexLeftInverse A hA R (regionVertexTensorMap A R x) = x :=
      LinearMap.congr_fun (regionVertexLeftInverse_comp_regionVertexTensorMap A hA R) x
    exact ⟨by simpa only [hLx, Matrix.mulVecLin_apply] using (LinearMap.mem_ker.mp hx),
      congrArg (regionVertexTensorMap A R) hLx⟩

/-- A virtual interaction whose kernel is the genuine virtual bond space
transports to a physical PEPS parent interaction, even for rectangular
injective site maps. Source: finite-region inverse-and-reconstruction
consequence of CPGSV21, Section IV.C.1, lines 2003–2044. -/
theorem isRegionParentInteraction_injectiveRegionParentTransport (A : Tensor Γ d)
    (hA : IsVertexInjective A) (R : Finset V)
    (H : Matrix (RegionVertexVirtualConfig A R) (RegionVertexVirtualConfig A R) ℂ)
    (hH : H.PosSemidef) (hker : (Matrix.mulVecLin H).ker = (regionVirtualBondMap A R).range) :
    IsRegionParentInteraction A R (injectiveRegionParentTransport A hA R H) := by
  refine ⟨injectiveRegionParentTransport_posSemidef A hA R H hH, ?_⟩
  rw [ker_injectiveRegionParentTransport A hA R H hH, hker,
    ← regionGroundSpace_eq_map_regionVirtualBondMap_range]

end TNLean.PEPS
