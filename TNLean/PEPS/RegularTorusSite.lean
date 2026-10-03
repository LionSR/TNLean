/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.FinTupleEquiv
import TNLean.Algebra.ComplexSqrt
import TNLean.PEPS.RegularSiteGram
import TNLean.PEPS.TorusOperatorString

/-!
# Regular isometric sites in torus coordinates

The existing torus action places the regular matrix on the incoming legs and the
transpose of its inverse on the outgoing legs. For the regular representation all
four factors are the same permutation matrix. Thus the group labels on the top,
right, down, and left legs undergo simultaneous left translation.

The group-basis Gram formula and the invariance of the existing four-leg site map
follow in these coordinates. Source: Schuch, Cirac, and Pérez-García,
arXiv:1001.3807, Definition 6.1 (`Papers/1001.3807/paper_v3.tex`, lines 1692–1700)
and Observation `obs:iso:accessible-virt`, lines 1770–1810. The positive scalar
convention is recorded in `docs/paper-gaps/rmp_peps_quantum_double_g_isometry.tex`.

## References

- [arXiv:1001.3807](https://arxiv.org/abs/1001.3807) -- N. Schuch, J. I. Cirac,
  D. Pérez-García, *PEPS as ground states: degeneracy and topology*
-/

open Module LinearMap Representation Matrix
open scoped Matrix

namespace TNLean.PEPS

variable (G : Type*) [Group G] [Fintype G] [DecidableEq G]
attribute [local instance] Representation.invertibleFintypeCardComplex

/-- The standard left-regular representation, expressed by Mathlib permutation matrices. -/
def leftRegularMatrix : G →* Matrix G G ℂ :=
  Matrix.permMatrixHom.comp (MulAction.toPermHom G G)

variable {G}

/-- The regular matrix sends the group basis vector at `k` to the one at `g*k`. -/
theorem leftRegularMatrix_apply (g h k : G) :
    leftRegularMatrix G g h k = if h = g * k then 1 else 0 := by
  simp [leftRegularMatrix, Matrix.permMatrixHom_apply, Equiv.Perm.permMatrix,
    PEquiv.toMatrix_apply, MulAction.toPerm_symm_apply, eq_inv_mul_iff_mul_eq, eq_comm]

/-- The group-basis matrix of Mathlib's regular representation is the same matrix homomorphism. -/
theorem toMatrix_leftRegular_eq_leftRegularMatrix (g : G) :
    LinearMap.toMatrix (MonoidAlgebra.basis G ℂ) (MonoidAlgebra.basis G ℂ)
      (Representation.leftRegular ℂ G g) = leftRegularMatrix G g :=
  toMatrix_leftRegular g

/-- The torus four-leg matrix permutes top, right, down, and left labels by the same
left translation. Source: SCP10, Definition 6.1 and equation `eq:2d-ug-sym`. -/
theorem torusLegMatrix_leftRegularMatrix_apply (g : G)
    (η θ : G × G × G × G) :
    torusLegMatrix (leftRegularMatrix G) g η θ = if η = g • θ then 1 else 0 := by
  obtain ⟨t, r, b, l⟩ := η
  obtain ⟨t', r', b', l'⟩ := θ
  simp only [torusLegMatrix, MonoidHom.coe_mk, OneHom.coe_mk, torusLegKernel_apply,
    leftRegularMatrix_apply, eq_inv_mul_iff_mul_eq, ite_zero_mul_ite_zero, mul_one,
    Prod.smul_mk, smul_eq_mul, Prod.mk.injEq]
  simp only [and_assoc, eq_comm]

/-- The existing torus representation is the usual permutation of the regular group basis. -/
theorem torusLegRep_leftRegularMatrix_apply (g : G)
    (x : (G × G × G × G) → ℂ) (η : G × G × G × G) :
    torusLegRep (leftRegularMatrix G) g x η = x (g⁻¹ • η) := by
  classical
  rw [torusLegRep_apply]
  have heq (θ : G × G × G × G) : η = g • θ ↔ θ = g⁻¹ • η := by
    rw [eq_inv_smul_iff, eq_comm]
  simp [Matrix.mulVec, dotProduct, torusLegMatrix_leftRegularMatrix_apply,
    heq]

omit [Fintype G] [DecidableEq G] in
/-- The four-coordinate identification preserves simultaneous regular translation. -/
theorem finFourArrowEquiv_smul (g : G) (η : Fin 4 → G) :
    finFourArrowEquiv G (g • η) = g • finFourArrowEquiv G η := rfl

/-- Expressing the existing torus representation in the four-coordinate function basis
recovers the same regular incident-leg representation used for arbitrary finite graphs. -/
theorem torusLegRep_leftRegularMatrix_conj :
    ((LinearEquiv.funCongrLeft ℂ ℂ (finFourArrowEquiv G)).conjAlgEquiv ℂ).toMonoidHom.comp
        (torusLegRep (leftRegularMatrix G)) = regularLegRepresentation (G := G) (Fin 4) := by
  apply MonoidHom.ext
  intro g
  apply LinearMap.ext
  intro x
  funext η
  change torusLegRep (leftRegularMatrix G) g
    ((LinearEquiv.funCongrLeft ℂ ℂ (finFourArrowEquiv G)).symm x)
      (finFourArrowEquiv G η) = regularLegRepresentation (Fin 4) g x η
  rw [torusLegRep_leftRegularMatrix_apply, regularLegRepresentation_apply]
  change x ((finFourArrowEquiv G).symm (g⁻¹ • finFourArrowEquiv G η)) = x (g⁻¹ • η)
  rw [← finFourArrowEquiv_smul, Equiv.symm_apply_apply]

/-- The torus regular action is unitary in the four-leg group basis. -/
theorem torusLegRep_leftRegularMatrix_unitary (g : G)
    (x y : (G × G × G × G) → ℂ) :
    star (torusLegRep (leftRegularMatrix G) g x) ⬝ᵥ
      torusLegRep (leftRegularMatrix G) g y = star x ⬝ᵥ y := by
  simp only [dotProduct, Pi.star_apply, torusLegRep_leftRegularMatrix_apply]
  exact Equiv.sum_comp (MulAction.toPermHom G (G × G × G × G) g⁻¹)
    (fun η => star (x η) * y η)

/-- The torus invariant projector has the normalized common-translation kernel. -/
theorem toMatrix_averageMap_torusLegRep_leftRegularMatrix (η θ : G × G × G × G) :
    LinearMap.toMatrix' (torusLegRep (leftRegularMatrix G)).averageMap η θ =
      (Fintype.card G : ℂ)⁻¹ * ∑ g : G, if η = g • θ then 1 else 0 := by
  rw [LinearMap.toMatrix'_apply, Representation.averageMap_apply_eq_sum]
  simp only [Pi.smul_apply, Finset.sum_apply, torusLegRep_leftRegularMatrix_apply,
    Pi.single_apply, invOf_eq_inv, smul_eq_mul, inv_smul_eq_iff]

variable {Phys : Type*} [Fintype Phys] [DecidableEq Phys]

omit [Group G] [Fintype Phys] [DecidableEq Phys] in
/-- The matrix of the existing site map consists of its physical coefficients. -/
theorem toMatrix_siteMap_regular (a : G → G → G → G → Phys → ℂ) :
    LinearMap.toMatrix' (siteMap a) =
      Matrix.of fun s η => a η.1 η.2.1 η.2.2.1 η.2.2.2 s := by
  ext s η
  rw [LinearMap.toMatrix'_apply]
  exact congrFun (Matrix.mulVec_single_one
    (Matrix.of fun s η => a η.1 η.2.1 η.2.2.1 η.2.2.2 s) η) s

omit [Group G] [DecidableEq G] [Fintype Phys] [DecidableEq Phys] in
/-- Reindexing the existing four-leg site map gives the incident-leg coordinate map. -/
theorem siteMap_fourCoordinates (a : G → G → G → G → Phys → ℂ) :
    siteMap a ∘ₗ (LinearEquiv.funCongrLeft ℂ ℂ (finFourArrowEquiv G)).symm.toLinearMap =
      regularSiteMap (fun η s => a (η 0) (η 1) (η 2) (η 3) s) := by
  classical
  apply LinearMap.ext
  intro x
  funext s
  change (∑ η : G × G × G × G, a η.1 η.2.1 η.2.2.1 η.2.2.2 s *
    x ((finFourArrowEquiv G).symm η)) = ∑ η : Fin 4 → G,
      a (η 0) (η 1) (η 2) (η 3) s * x η
  have h := Equiv.sum_comp (finFourArrowEquiv G)
    (fun η => a η.1 η.2.1 η.2.2.1 η.2.2.2 s * x ((finFourArrowEquiv G).symm η))
  simp only [Equiv.symm_apply_apply] at h
  simpa only [finFourArrowEquiv_apply] using h.symm

omit [DecidableEq Phys] in
/-- Regular isometry of the existing torus site map implies simultaneous translation
invariance of its physical coefficients. Source: SCP10, Definition 6.1. -/
theorem IsGIsometric.torusRegularSite_translation
    {a : G → G → G → G → Phys → ℂ}
    (ha : IsGIsometric (torusLegRep (leftRegularMatrix G)) (siteMap a))
    (g t r b l : G) (s : Phys) : a (g * t) (g * r) (g * b) (g * l) s = a t r b l s := by
  have hsingle : torusLegRep (leftRegularMatrix G) g (Pi.single (t, r, b, l) 1) =
      Pi.single (g * t, g * r, g * b, g * l) 1 := by
    ext θ
    simp only [torusLegRep_leftRegularMatrix_apply, Pi.single_apply, inv_smul_eq_iff,
      Prod.smul_mk, smul_eq_mul]
  have h := congrFun (LinearMap.congr_fun (ha.invariant g) (Pi.single (t, r, b, l) 1)) s
  simp only [LinearMap.comp_apply, hsingle] at h
  change ((Matrix.of fun s η => a η.1 η.2.1 η.2.2.1 η.2.2.2 s) *ᵥ
      Pi.single (g * t, g * r, g * b, g * l) 1) s =
    ((Matrix.of fun s η => a η.1 η.2.1 η.2.2.1 η.2.2.2 s) *ᵥ Pi.single (t, r, b, l) 1) s at h
  rw [Matrix.mulVec_single_one, Matrix.mulVec_single_one] at h
  exact h

omit [DecidableEq Phys] in
/-- The Gram formula of an actual regular torus site map, in top, right, down, left
coordinates. Source: SCP10, Definition 6.1, lines 1692–1700. -/
theorem IsGIsometric.exists_torusRegularSiteGram
    {a : G → G → G → G → Phys → ℂ}
    (ha : IsGIsometric (torusLegRep (leftRegularMatrix G)) (siteMap a)) :
    ∃ c : ℝ, 0 < c ∧ ∀ η θ : G × G × G × G,
      (∑ s : Phys, star (a η.1 η.2.1 η.2.2.1 η.2.2.2 s) *
        a θ.1 θ.2.1 θ.2.2.1 θ.2.2.2 s) =
          ((c : ℂ) / (Fintype.card G : ℂ)) * ∑ g : G, if η = g • θ then 1 else 0 := by
  classical
  obtain ⟨c, hc, h⟩ := ha.exists_coordinateAdjoint_comp
    (averageMap_dotProduct_of_unitary _ torusLegRep_leftRegularMatrix_unitary)
  refine ⟨c, hc, fun η θ => ?_⟩
  have hmat := congrArg LinearMap.toMatrix' h
  simp only [LinearMap.toMatrix'_comp, coordinateAdjoint, LinearMap.toMatrix'_toLin',
    map_smul, toMatrix_siteMap_regular] at hmat
  have hij := congrFun (congrFun hmat η) θ
  change (∑ s : Phys, star (a η.1 η.2.1 η.2.2.1 η.2.2.2 s) *
      a θ.1 θ.2.1 θ.2.2.1 θ.2.2.2 s) =
    (c : ℂ) * LinearMap.toMatrix' (torusLegRep (leftRegularMatrix G)).averageMap η θ at hij
  rw [toMatrix_averageMap_torusLegRep_leftRegularMatrix] at hij
  simpa only [div_eq_mul_inv, mul_assoc] using hij

/-- Dividing the physical-to-virtual adjoint by the square root of the isometry factor
identifies the physical range isometrically with the invariant virtual space. Its
composition with the site map is the invariant projector times the square root of that
factor. Source: SCP10, Observation `obs:iso:accessible-virt`, lines 1770–1788. -/
theorem IsGIsometric.exists_accessibleVirtualSite
    {a : G → G → G → G → Phys → ℂ}
    (ha : IsGIsometric (torusLegRep (leftRegularMatrix G)) (siteMap a)) :
    ∃ c : ℝ, 0 < c ∧
      let J := (Real.sqrt c : ℂ)⁻¹ • coordinateAdjoint (siteMap a)
      J ∘ₗ siteMap a = (Real.sqrt c : ℂ) • (torusLegRep (leftRegularMatrix G)).averageMap ∧
        ∀ x ∈ (siteMap a).range, ∀ y ∈ (siteMap a).range,
          star (J x) ⬝ᵥ J y = star x ⬝ᵥ y := by
  classical
  let ρ := torusLegRep (leftRegularMatrix G)
  let T := siteMap a
  have hAvg := averageMap_dotProduct_of_unitary ρ torusLegRep_leftRegularMatrix_unitary
  obtain ⟨c, hc, h⟩ := ha.exists_coordinateAdjoint_comp hAvg
  have hs : (Real.sqrt c : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr hc)
  have hscalar : (Real.sqrt c : ℂ)⁻¹ * (c : ℂ) = (Real.sqrt c : ℂ) := by
    rw [← Complex.ofReal_sqrt_sq c hc.le, pow_two, ← mul_assoc, inv_mul_cancel₀ hs, one_mul]
  let J := (Real.sqrt c : ℂ)⁻¹ • coordinateAdjoint T
  have hJT : J ∘ₗ T = (Real.sqrt c : ℂ) • ρ.averageMap := by
    rw [LinearMap.smul_comp, h, smul_smul, hscalar]
  refine ⟨c, hc, hJT, ?_⟩
  intro x hx y hy
  obtain ⟨u, rfl⟩ := hx
  obtain ⟨v, rfl⟩ := hy
  have hJu := LinearMap.congr_fun hJT u
  have hJv := LinearMap.congr_fun hJT v
  simp only [LinearMap.comp_apply, LinearMap.smul_apply] at hJu hJv
  rw [hJu, hJv]
  simp only [star_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul,
    Complex.star_def, Complex.conj_ofReal]
  rw [← mul_assoc, ← pow_two, Complex.ofReal_sqrt_sq c hc.le,
    hAvg, ρ.averageMap_id _ (ρ.averageMap_invariant v)]
  have hv := LinearMap.congr_fun h v
  simp only [LinearMap.comp_apply, LinearMap.smul_apply] at hv
  rw [← coordinateAdjoint_dotProduct T u (T v), hv, dotProduct_smul, smul_eq_mul]

end TNLean.PEPS
