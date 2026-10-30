/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.WeakHopfParentAverage

/-!
# The weak Hopf algebra of a finite set

The algebra \(\mathbb C^m\) of functions on a finite set, with pointwise
multiplication and the comultiplication \(\Delta(\delta_k)=\delta_k\otimes\delta_k\)
of its standard idempotents, is a commutative and cocommutative
C*-weak Hopf algebra with antipode the identity. It is weak rather than
Hopf: for \(m\ge2\), \(\Delta(1)=\sum_k\delta_k\otimes\delta_k\ne1\otimes1\).
Its canonical integral is \(\Omega=1\), and
\(\sum_k\Delta(\delta_k)\Delta(\delta_k)=\Delta(1)\).

A unital star representation \(\phi\) of \(\mathbb C^m\) on the physical
space is a resolution of the identity into orthogonal projections
\(\phi(\delta_k)\), and the convolution dual acts faithfully on
\(\mathbb C^m\) by diagonal matrices. These data form a weak-Hopf MPO
representation, and the weak-Hopf average of GLM23 Appendix B becomes the
pinching
\[
  E_n(P)=\sum_k\rho_n(\delta_k)\,P\,\rho_n(\delta_k).
\]
For a compatible one-site injective MPS it fixes the support projection.

## References

* Garre-Rubio--Lootens--Molnár, arXiv:2203.12563v3, Appendix B,
  lines 2463--2466.
* Molnár et al., arXiv:2204.05940v1, Section 4.
-/

open scoped Matrix TensorProduct

noncomputable section

namespace MPOTensor.FiniteSetWeakHopf

variable {m d Dₐ n : ℕ}

/-- The comultiplication of a standard idempotent is \(\delta_k\otimes\delta_k\)
times its coefficient. -/
theorem comul_single (k : Fin m) (a : ℂ) :
    Coalgebra.comul (R := ℂ) (Pi.single k a : Fin m → ℂ) =
      (Pi.single k 1 : Fin m → ℂ) ⊗ₜ Pi.single k a := by
  simp

/-- The comultiplication in coordinates. -/
theorem comul_eq_sum (x : Fin m → ℂ) :
    Coalgebra.comul (R := ℂ) x =
      ∑ k, (Pi.single k 1 : Fin m → ℂ) ⊗ₜ Pi.single k (x k) := by
  conv_lhs => rw [← Finset.univ_sum_single x]
  simp only [map_sum, comul_single]

private theorem single_mul_single (k l : Fin m) (a b : ℂ) :
    (Pi.single k a : Fin m → ℂ) * Pi.single l b =
      if k = l then Pi.single k (a * b) else 0 := by
  funext j
  by_cases hkl : k = l
  · subst hkl
    by_cases hj : j = k <;> simp [hj]
  · by_cases hj : j = k
    · subst hj
      simp [hkl]
    · simp [hkl, hj]

/-- The comultiplication is multiplicative. -/
theorem comul_mul (x y : Fin m → ℂ) :
    Coalgebra.comul (R := ℂ) (x * y) = Coalgebra.comul x * Coalgebra.comul y := by
  rw [comul_eq_sum, comul_eq_sum, comul_eq_sum, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.sum_eq_single k]
  · rw [Algebra.TensorProduct.tmul_mul_tmul, single_mul_single, single_mul_single]
    simp
  · intro l _ hlk
    simp [Algebra.TensorProduct.tmul_mul_tmul, single_mul_single, Ne.symm hlk]
  · simp

/-- The comultiplication preserves the involution. -/
theorem comul_star (x : Fin m → ℂ) :
    Coalgebra.comul (R := ℂ) (star x) = star (Coalgebra.comul x) := by
  rw [comul_eq_sum, comul_eq_sum, star_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [TensorProduct.star_tmul, ← Pi.single_star, ← Pi.single_star, star_one]
  rfl

/-- The convolution dual acts on \(\mathbb C^m\) by the diagonal matrix of its
values on the standard idempotents. -/
def virt : WithConv ((Fin m → ℂ) →ₗ[ℂ] ℂ) →ₐ[ℂ] Matrix (Fin m) (Fin m) ℂ :=
  AlgHom.ofLinearMap
    { toFun := fun f ↦ Matrix.diagonal fun k ↦ f.ofConv (Pi.single k 1)
      map_add' := by intro f g; ext i j; simp [Matrix.diagonal_apply]; split_ifs <;> simp
      map_smul' := by intro c f; ext i j; simp [Matrix.diagonal_apply] }
    (by
      change (Matrix.diagonal fun k ↦ (1 : WithConv ((Fin m → ℂ) →ₗ[ℂ] ℂ)).ofConv
        (Pi.single k 1)) = 1
      simp [LinearMap.convOne_def])
    (by
      intro f g
      change (Matrix.diagonal fun k ↦ (f * g).ofConv (Pi.single k 1)) =
        Matrix.diagonal (fun k ↦ f.ofConv (Pi.single k 1)) *
          Matrix.diagonal fun k ↦ g.ofConv (Pi.single k 1)
      rw [Matrix.diagonal_mul_diagonal]
      congr 1
      funext k
      simp [LinearMap.convMul_def])

/-- The dual representation in coordinates. -/
theorem virt_apply (f : WithConv ((Fin m → ℂ) →ₗ[ℂ] ℂ)) :
    virt f = Matrix.diagonal fun k ↦ f.ofConv (Pi.single k 1) := rfl

/-- The diagonal representation of the convolution dual is faithful. -/
theorem virt_injective : Function.Injective (virt (m := m)) := by
  intro f g hfg
  apply WithConv.ext
  apply LinearMap.pi_ext
  intro k a
  have hk := congrArg (fun M ↦ M k k) hfg
  simp only [virt_apply, Matrix.diagonal_apply_eq] at hk
  have ha : (Pi.single k a : Fin m → ℂ) = a • Pi.single k 1 := by
    funext j
    by_cases hj : j = k <;> simp [hj]
  rw [ha, map_smul, map_smul, hk]

/-- The finite-set weak Hopf algebra with a unital star representation
\(\phi\), the canonical integral \(\Omega=1\), and \(T\) the identity. -/
def weakHopfRepresentation (φ : (Fin m → ℂ) →ₐ[ℂ] Matrix (Fin d) (Fin d) ℂ)
    (hφ : ∀ x, φ (star x) = (φ x)ᴴ) : WeakHopfRepresentation (Fin m → ℂ) d m where
  phys := φ
  phys_star := hφ
  virt := virt
  virt_injective := virt_injective
  comul_mul := comul_mul
  comul_star := comul_star
  pullThrough := LinearMap.id
  integral := 1
  mul'_map_comul_integral := by
    rw [comul_eq_sum (1 : Fin m → ℂ), map_sum, map_sum]
    simp only [Pi.one_apply, TensorProduct.map_tmul, LinearMap.comp_apply, LinearMap.id_apply,
      LinearMap.mul'_apply, ← comul_mul]
    have h1 : (∑ k : Fin m, (Pi.single k 1 : Fin m → ℂ) * Pi.single k 1) = 1 := by
      conv_rhs => rw [← Finset.univ_sum_single (1 : Fin m → ℂ)]
      apply Finset.sum_congr rfl
      intro k _
      simp [single_mul_single]
    rw [← map_sum, h1, comul_eq_sum]
    simp only [Pi.one_apply]

/-- The finite-set weak Hopf algebra is not a Hopf algebra once it has two
points: \(\Delta(1)\ne1\otimes1\). -/
theorem comul_one_ne (hm : 2 ≤ m) :
    Coalgebra.comul (R := ℂ) (1 : Fin m → ℂ) ≠ 1 ⊗ₜ 1 := by
  intro h
  let i₀ : Fin m := ⟨0, by omega⟩
  let i₁ : Fin m := ⟨1, by omega⟩
  have hne : i₀ ≠ i₁ := by simp [i₀, i₁, Fin.ext_iff]
  have := congrArg (fun t ↦ LinearMap.mul' ℂ ℂ
    (TensorProduct.map (LinearMap.proj i₀) (LinearMap.proj i₁) t)) h
  simp only [comul_eq_sum, map_sum, TensorProduct.map_tmul, LinearMap.proj_apply,
    LinearMap.mul'_apply, Pi.one_apply, mul_one] at this
  rw [Finset.sum_eq_zero] at this
  · exact zero_ne_one this
  · intro k _
    by_cases hk : k = i₀
    · subst hk
      simp [hne.symm]
    · simp [Pi.single_apply, Ne.symm hk]

/-- The standard idempotents give a Sweedler representation of
\(\Delta(\Omega)=\sum_k\delta_k\otimes\delta_k\). -/
def integralRepr (φ : (Fin m → ℂ) →ₐ[ℂ] Matrix (Fin d) (Fin d) ℂ)
    (hφ : ∀ x, φ (star x) = (φ x)ᴴ) :
    Coalgebra.Repr ℂ (weakHopfRepresentation φ hφ).integral (Fin m) where
  index := Finset.univ
  left k := Pi.single k 1
  right k := Pi.single k 1
  eq := by
    rw [show (weakHopfRepresentation φ hφ).integral = 1 from rfl, comul_eq_sum]
    rfl

/-- The weak-Hopf average of the finite-set algebra is the pinching by the
represented idempotents. -/
theorem weakHopfAverage_eq_sum (φ : (Fin m → ℂ) →ₐ[ℂ] Matrix (Fin d) (Fin d) ℂ)
    (hφ : ∀ x, φ (star x) = (φ x)ᴴ)
    (P : Module.End ℂ (EuclideanSpace ℂ (Fin n → Fin d))) :
    (weakHopfRepresentation φ hφ).weakHopfAverage n P =
      ∑ k, Matrix.toEuclideanLin ((weakHopfRepresentation φ hφ).rep n (Pi.single k 1)) * P *
        Matrix.toEuclideanLin ((weakHopfRepresentation φ hφ).rep n (Pi.single k 1)) :=
  (weakHopfRepresentation φ hφ).weakHopfAverage_eq_sum (integralRepr φ hφ) P

attribute [local instance] MPSTensor.groundSpaceES_hasOrthogonalProjection

/-- The pinching by the represented idempotents fixes the support projection
of a one-site injective MPS compatible with the MPO, at every positive
length: an instance of the weak-Hopf average of GLM23 Appendix B,
lines 2463--2466. -/
theorem sum_rep_single_mul_starProjection_mul (φ : (Fin m → ℂ) →ₐ[ℂ] Matrix (Fin d) (Fin d) ℂ)
    (hφ : ∀ x, φ (star x) = (φ x)ᴴ) {A : MPSTensor d Dₐ}
    (h : IsBoundaryCompatible (weakHopfRepresentation φ hφ).tensor A)
    (hInj : Kraus.IsInjective A) (hn : 0 < n) :
    ∑ k, Matrix.toEuclideanLin ((weakHopfRepresentation φ hφ).rep n (Pi.single k 1)) *
        (MPSTensor.groundSpaceES A n).starProjection.toLinearMap *
        Matrix.toEuclideanLin ((weakHopfRepresentation φ hφ).rep n (Pi.single k 1)) =
      (MPSTensor.groundSpaceES A n).starProjection.toLinearMap := by
  rw [← weakHopfAverage_eq_sum]
  exact (weakHopfRepresentation φ hφ).weakHopfAverage_starProjection h hInj hn

end MPOTensor.FiniteSetWeakHopf
