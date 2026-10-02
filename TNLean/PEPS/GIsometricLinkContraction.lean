/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.GIsometric

/-!
# DOC
-/

open Module LinearMap Representation
open scoped Matrix Kronecker

namespace TNLean
namespace PEPS

attribute [local instance] Representation.invertibleFintypeCardComplex

variable {G : Type*} [Group G]

section Regular

/-- The left-regular representation on the coordinate space `ℂ^G`, `(L_g f)(h) = f(g⁻¹ h)`. -/
noncomputable def leftRegularFun : Representation ℂ G (G → ℂ) where
  toFun g := LinearMap.funLeft ℂ ℂ fun h => g⁻¹ * h
  map_one' := by
    refine LinearMap.ext fun f => funext fun h => ?_
    simp [LinearMap.funLeft]
  map_mul' g g' := by
    refine LinearMap.ext fun f => funext fun h => ?_
    simp [LinearMap.funLeft, mul_assoc]

@[simp]
theorem leftRegularFun_apply (g : G) (f : G → ℂ) (h : G) :
    leftRegularFun g f h = f (g⁻¹ * h) :=
  rfl

/-- Bridge: on coefficients, the representation `leftRegularFun` is Mathlib's left-regular
representation `leftRegular ℂ G` on `ℂ[G]`, `L_g |h⟩ = |gh⟩`. -/
theorem coeff_leftRegular (g : G) (f : MonoidAlgebra ℂ G) :
    (fun h => (leftRegular ℂ G g f).coeff h) = leftRegularFun g fun h => f.coeff h := by
  funext h
  simp [coeff_ofMulAction, smul_eq_mul]

variable [Fintype G] [DecidableEq G]

theorem toMatrix'_leftRegularFun (g h h' : G) :
    LinearMap.toMatrix' (leftRegularFun g) h h' = if g * h' = h then 1 else 0 := by
  rw [LinearMap.toMatrix'_apply, leftRegularFun_apply, Pi.single_apply]
  congr 1
  exact propext ⟨fun e => by rw [← e, mul_inv_cancel_left],
    fun e => by rw [← e, inv_mul_cancel_left]⟩

theorem toMatrix'_leftRegularFun_mem_unitaryGroup (g : G) :
    LinearMap.toMatrix' (leftRegularFun g) ∈ Matrix.unitaryGroup G ℂ := by
  refine mem_unitaryGroup_of_dotProduct fun x y => ?_
  simp only [Matrix.toLin'_toMatrix', ← Matrix.toLin'_apply]
  simp only [leftRegularFun_apply, dotProduct, Pi.star_apply]
  exact Fintype.sum_equiv (Equiv.mulLeft g⁻¹) _ _ fun h => rfl

end Regular

section Kronecker

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- The tensor product `ρ ⊗ τ` of two representations on coordinate spaces, acting on
`ℂ^{ι × κ}` by the Kronecker product of their matrices. -/
noncomputable def kroneckerRep (ρ : Representation ℂ G (ι → ℂ))
    (τ : Representation ℂ G (κ → ℂ)) : Representation ℂ G (ι × κ → ℂ) where
  toFun g := Matrix.toLin' (LinearMap.toMatrix' (ρ g) ⊗ₖ LinearMap.toMatrix' (τ g))
  map_one' := by
    rw [ρ.map_one, τ.map_one, LinearMap.toMatrix'_one, LinearMap.toMatrix'_one,
      Matrix.one_kronecker_one, Matrix.toLin'_one]
    rfl
  map_mul' g h := by
    rw [ρ.map_mul, τ.map_mul, LinearMap.toMatrix'_mul, LinearMap.toMatrix'_mul,
      Matrix.mul_kronecker_mul, Matrix.toLin'_mul]
    rfl

theorem toMatrix'_kroneckerRep (ρ : Representation ℂ G (ι → ℂ))
    (τ : Representation ℂ G (κ → ℂ)) (g : G) :
    LinearMap.toMatrix' (kroneckerRep ρ τ g) =
      LinearMap.toMatrix' (ρ g) ⊗ₖ LinearMap.toMatrix' (τ g) :=
  LinearMap.toMatrix'_toLin' _

theorem toMatrix'_kroneckerRep_mem_unitaryGroup {ρ : Representation ℂ G (ι → ℂ)}
    {τ : Representation ℂ G (κ → ℂ)}
    (hρ : ∀ g, LinearMap.toMatrix' (ρ g) ∈ Matrix.unitaryGroup ι ℂ)
    (hτ : ∀ g, LinearMap.toMatrix' (τ g) ∈ Matrix.unitaryGroup κ ℂ) (g : G) :
    LinearMap.toMatrix' (kroneckerRep ρ τ g) ∈ Matrix.unitaryGroup (ι × κ) ℂ := by
  rw [toMatrix'_kroneckerRep]
  exact Matrix.kronecker_mem_unitary (hρ g) (hτ g)

end Kronecker

section Gram

variable [Fintype G] {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]

/-- For a unitary representation the projector `Π` onto the invariant subspace is
self-adjoint: `⟪Π u, w⟫ = ⟪u, Π w⟫`. -/
theorem star_averageMap_dotProduct {ρ : Representation ℂ G (ι → ℂ)}
    (hρ : ∀ g, LinearMap.toMatrix' (ρ g) ∈ Matrix.unitaryGroup ι ℂ) (u w : ι → ℂ) :
    star (ρ.averageMap u) ⬝ᵥ w = star u ⬝ᵥ ρ.averageMap w := by
  have hg : ∀ g, star (ρ g u) ⬝ᵥ w = star u ⬝ᵥ ρ g⁻¹ w := fun g => by
    have h := dotProduct_mulVec_of_mem_unitaryGroup (hρ g) u (ρ g⁻¹ w)
    simp only [← Matrix.toLin'_apply, Matrix.toLin'_toMatrix'] at h
    rw [← h, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  rw [averageMap_apply_eq_sum, averageMap_apply_eq_sum, star_smul, smul_dotProduct,
    dotProduct_smul, star_sum, sum_dotProduct, dotProduct_sum]
  simp only [hg]
  congr 1
  · simp [Invertible.invOf, star_inv₀]
  · exact Fintype.sum_equiv (Equiv.inv G) _ _ fun g => rfl

/-- Source: arXiv:1001.3807, Definition 6.1, `Papers/1001.3807/paper_v3.tex` lines 1692–1700.
If `T` is invariant under a unitary representation and preserves inner products of invariant
vectors up to `c`, then `T†T = c Π`: the left inverse of `T` is `c⁻¹ T†`. -/
theorem conjTranspose_toMatrix'_mul_toMatrix' {ρ : Representation ℂ G (ι → ℂ)}
    {T : (ι → ℂ) →ₗ[ℂ] (κ → ℂ)}
    (hρ : ∀ g, LinearMap.toMatrix' (ρ g) ∈ Matrix.unitaryGroup ι ℂ)
    (hinv : ∀ g, T ∘ₗ ρ g = T) {c : ℂ}
    (hc : ∀ x ∈ ρ.invariants, ∀ y ∈ ρ.invariants, star (T x) ⬝ᵥ T y = c * (star x ⬝ᵥ y)) :
    (LinearMap.toMatrix' T)ᴴ * LinearMap.toMatrix' T = c • LinearMap.toMatrix' ρ.averageMap := by
  ext i j
  have key : star (T (Pi.single i 1)) ⬝ᵥ T (Pi.single j 1) =
      c * ρ.averageMap (Pi.single j 1) i := by
    rw [← apply_averageMap_of_forall_comp_eq hinv, ← apply_averageMap_of_forall_comp_eq hinv (Pi.single j 1),
      hc _ (ρ.averageMap_invariant _) _ (ρ.averageMap_invariant _),
      star_averageMap_dotProduct hρ, averageMap_id _ _ (ρ.averageMap_invariant _)]
    simp [dotProduct, Pi.single_apply]
  rw [Matrix.mul_apply, Matrix.smul_apply, LinearMap.toMatrix'_apply, smul_eq_mul, ← key]
  simp [dotProduct, LinearMap.toMatrix'_apply, Matrix.conjTranspose_apply]

end Gram

end PEPS
end TNLean
