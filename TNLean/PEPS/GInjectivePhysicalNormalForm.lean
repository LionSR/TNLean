/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.GInjectivePhysicalEquivalence
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# A normalized invariant-space form of G-injective tensors

An invertible physical map can turn any finite-dimensional G-injective map
into a map preserving inner products on the invariant virtual space, with
normalization factor one. The construction chooses orthonormal bases of the
invariant virtual space and of the physical range, and extends the resulting
physical range comparison to the full physical space.

Source: local physical filtering from SCP10, arXiv:1001.3807,
Definition 5.1, lines 1278–1296, and Definition `def:iso:isopeps`,
lines 1692–1697. For the regular virtual representation this produces a
normalized G-isometric tensor. It is a physical change of coordinates and
does not claim equality of the original and filtered closed PEPS states.
-/

open scoped BigOperators Matrix

namespace TNLean.PEPS

private theorem euclideanSubmoduleIsometry_inner {ι κ : Type*} [Fintype ι] [Fintype κ]
    (I : Submodule ℂ (EuclideanSpace ℂ ι)) (R : Submodule ℂ (EuclideanSpace ℂ κ))
    (J : I ≃ₗᵢ[ℂ] R) (x y : I) :
    inner ℂ (J x : EuclideanSpace ℂ κ) (J y : EuclideanSpace ℂ κ) =
      inner ℂ (x : EuclideanSpace ℂ ι) (y : EuclideanSpace ℂ ι) := by
  exact LinearIsometryEquiv.inner_map_map (𝕜 := ℂ) (E := I) (E' := R) J x y

variable {G ι κ : Type*} [Group G] [Finite G] [Fintype ι] [Fintype κ]
variable {ρ : Representation ℂ G (ι → ℂ)} {T : (ι → ℂ) →ₗ[ℂ] (κ → ℂ)}

attribute [local instance] Representation.invertibleFintypeCardComplex

/-- A G-injective map can be normalized on its invariant virtual space by an
invertible physical map. For regular virtual representations this is a
normalized G-isometric tensor. Source: local consequence of SCP10,
Definition 5.1, lines 1278–1296, and Definition `def:iso:isopeps`, lines 1692–1697. -/
theorem IsGInjective.exists_normalized_isGIsometric_physicalEquiv (hT : IsGInjective ρ T) :
    ∃ F : (κ → ℂ) ≃ₗ[ℂ] (κ → ℂ),
      IsGIsometric ρ (F.toLinearMap ∘ₗ T) ∧
      ∀ x ∈ ρ.invariants, ∀ y ∈ ρ.invariants,
        star (F (T x)) ⬝ᵥ F (T y) = star x ⬝ᵥ y := by
  classical
  let _ := Fintype.ofFinite G
  let Eι : EuclideanSpace ℂ ι ≃ₗ[ℂ] (ι → ℂ) := WithLp.linearEquiv 2 ℂ (ι → ℂ)
  let Eκ : EuclideanSpace ℂ κ ≃ₗ[ℂ] (κ → ℂ) := WithLp.linearEquiv 2 ℂ (κ → ℂ)
  let I : Submodule ℂ (EuclideanSpace ℂ ι) := ρ.invariants.map Eι.symm.toLinearMap
  let R : Submodule ℂ (EuclideanSpace ℂ κ) := T.range.map Eκ.symm.toLinearMap
  let eI : ρ.invariants ≃ₗ[ℂ] I := Eι.symm.submoduleMap ρ.invariants
  let eR : T.range ≃ₗ[ℂ] R := Eκ.symm.submoduleMap T.range
  let L : I ≃ₗ[ℂ] R := eI.symm.trans (hT.invariantsRangeEquiv.trans eR)
  obtain ⟨J⟩ : Nonempty (I ≃ₗᵢ[ℂ] R) :=
    ⟨(stdOrthonormalBasis ℂ I).equiv (stdOrthonormalBasis ℂ R) (finCongr L.finrank_eq)⟩
  let p : (ι → ℂ) →ₗ[ℂ] ρ.invariants :=
    ρ.averageMap.codRestrict ρ.invariants ρ.averageMap_invariant
  let S : (ι → ℂ) →ₗ[ℂ] (κ → ℂ) :=
    Eκ.toLinearMap ∘ₗ R.subtype ∘ₗ J.toLinearMap ∘ₗ eI.toLinearMap ∘ₗ p
  have hp (x : ρ.invariants) : p x = x :=
    Subtype.ext (ρ.averageMap_id x x.2)
  have hS (x : ρ.invariants) : S x = Eκ (J (eI x)) := by
    change Eκ (J (eI (p x))) = _
    rw [hp]
  have hAvg : ∀ g : G, ρ.averageMap ∘ₗ ρ g = ρ.averageMap := by
    intro g
    change ρ.averageMap * ρ g = ρ.averageMap
    rw [Representation.averageMap, ← Representation.asAlgebraHom_single_one,
      ← map_mul, GroupAlgebra.mul_average_right]
  have hSinv : ∀ g : G, S ∘ₗ ρ g = S := by
    intro g
    apply LinearMap.ext
    intro x
    have hp' : p (ρ g x) = p x := Subtype.ext (LinearMap.congr_fun (hAvg g) x)
    change Eκ (J (eI (p (ρ g x)))) = Eκ (J (eI (p x)))
    rw [hp']
  have hSinj : ∀ x ∈ ρ.invariants, S x = 0 → x = 0 := by
    intro x hx hzero
    let xI : ρ.invariants := ⟨x, hx⟩
    have hJ : J (eI xI) = 0 := by
      apply Subtype.ext
      apply Eκ.injective
      exact (hS xI).symm.trans (hzero.trans (map_zero Eκ).symm)
    have heI : eI xI = 0 := J.injective (hJ.trans (map_zero J).symm)
    exact congrArg Subtype.val (eI.injective (heI.trans (map_zero eI).symm))
  have hInner : ∀ x ∈ ρ.invariants, ∀ y ∈ ρ.invariants,
      star (S x) ⬝ᵥ S y = star x ⬝ᵥ y := by
    intro x hx y hy
    let xI : ρ.invariants := ⟨x, hx⟩
    let yI : ρ.invariants := ⟨y, hy⟩
    have h := euclideanSubmoduleIsometry_inner I R J (eI xI) (eI yI)
    change Eκ (J (eI yI)) ⬝ᵥ star (Eκ (J (eI xI))) = y ⬝ᵥ star x at h
    rw [hS xI, hS yI]
    simpa only [dotProduct_comm] using h
  have hSIso : IsGIsometric ρ S := by
    refine ⟨⟨hSinv, hSinj⟩, 1, zero_lt_one, ?_⟩
    simpa only [Complex.ofReal_one, one_mul] using hInner
  obtain ⟨F, hF⟩ := hT.exists_physicalEquiv hSIso.toIsGInjective
  refine ⟨F, hF ▸ hSIso, ?_⟩
  intro x hx y hy
  have hFx := LinearMap.congr_fun hF x
  have hFy := LinearMap.congr_fun hF y
  change F (T x) = S x at hFx
  change F (T y) = S y at hFy
  rw [hFx, hFy]
  exact hInner x hx y hy

end TNLean.PEPS
