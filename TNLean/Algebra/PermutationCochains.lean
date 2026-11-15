/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
module

public import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree

/-!
# Cochains with permutation coefficients

For a left action of `G` on `X`, the coefficient action on `X → M` is
`(g • f) x = f (g⁻¹ • x)`. It is scoped to avoid conflicting with pointwise actions.
The cochains and differentials are those of `Rep.ofMulDistribMulAction`.

The block coordinates of arXiv:2502.20257, `eq:omega_and_Ls` and `eq:Lsymbgauge`,
use the last group argument to act on a block. In left-module coordinates a two-cochain
is therefore `F(g,h)(x) = L^{(gh)⁻¹ • x}_{g,h}`. Merely currying the indices would give
the wrong differential for a nontrivial action. The equivalences below give this change
of coordinates and the corresponding one-cochain change.

No finiteness or transitivity assumption on the action is needed. The coefficient group
is arbitrary and commutative; complex units and the circle are special cases.
-/

@[expose] public section

namespace TNLean.Algebra.PermutationCochains

universe u v w

section Cochains

variable {G : Type u} {X : Type v} {M : Type w}
  [Group G] [MulAction G X] [CommGroup M]

set_option warn.classDefReducibility false in
/-- The permutation action on functions, `(g • f)(x) = f(g⁻¹ • x)`.
It is scoped because function spaces also carry pointwise actions. -/
scoped instance permutationMulDistribMulAction : MulDistribMulAction G (X → M) where
  smul g f x := f (g⁻¹ • x)
  one_smul f := funext fun x ↦ congrArg f (by simp)
  mul_smul g h f := funext fun x ↦ congrArg f (by simp [mul_smul])
  smul_one _ := rfl
  smul_mul _ _ _ := rfl

/-- The integral representation on the additive form of the permutation coefficient group. -/
abbrev representation (G : Type u) (X : Type v) (M : Type w)
    [Group G] [MulAction G X] [CommGroup M] : Rep.{max v w} ℤ G :=
  Rep.ofMulDistribMulAction G (X → M)

/-- Evaluation of the permutation representation. -/
@[simp]
theorem representation_ρ_apply (g : G) (f : representation G X M) (x : X) :
    ((representation G X M).ρ g f).toMul x = f.toMul (g⁻¹ • x) := rfl

/-- Block one-cochains in the left-module coordinates of group cohomology.
The block-coordinate convention is arXiv:2502.20257, lines 5914--5917. -/
def oneCochainEquiv : (G → X → M) ≃ (G → representation G X M) where
  toFun γ g := Additive.ofMul (fun x ↦ γ g (g⁻¹ • x))
  invFun f g x := (f g).toMul (g • x)
  left_inv γ := by
    funext g x
    change γ g (g⁻¹ • (g • x)) = γ g x
    rw [inv_smul_smul]
  right_inv f := by
    funext g
    apply Additive.toMul.injective
    funext x
    change (f g).toMul (g • (g⁻¹ • x)) = (f g).toMul x
    rw [smul_inv_smul]

/-- Block two-cochains in left-module coordinates:
`F(g,h)(x) = L^{(gh)⁻¹ • x}_{g,h}` (arXiv:2502.20257, `eq:omega_and_Ls`). -/
def twoCochainEquiv : (X → G → G → M) ≃ (G × G → representation G X M) where
  toFun L p := Additive.ofMul (fun x ↦ L ((p.1 * p.2)⁻¹ • x) p.1 p.2)
  invFun f x g h := (f (g, h)).toMul ((g * h) • x)
  left_inv L := by
    funext x g h
    change L ((g * h)⁻¹ • ((g * h) • x)) g h = L x g h
    rw [inv_smul_smul]
  right_inv f := by
    funext p
    apply Additive.toMul.injective
    funext x
    change (f p).toMul ((p.1 * p.2) • ((p.1 * p.2)⁻¹ • x)) = (f p).toMul x
    rw [smul_inv_smul]

end Cochains

section InhomogeneousDifferentials

variable {G : Type} {X : Type v} {M : Type w}
  [Group G] [MulAction G X] [CommGroup M]

/-- The second inhomogeneous differential in tuple coordinates, with coefficients
in a permutation representation of any universe. -/
theorem inhomogeneous_d₂_apply (f : G × G → representation G X M) (p : Fin 3 → G) :
    inhomogeneousCochains.d (representation G X M) 2 (fun q ↦ f (q 0, q 1)) p =
      (representation G X M).ρ (p 0) (f (p 1, p 2)) - f (p 0 * p 1, p 2) +
        f (p 0, p 1 * p 2) - f (p 0, p 1) := by
  rw [inhomogeneousCochains.d_hom_apply, Fin.sum_univ_three]
  simp [Fin.contractNth, sub_eq_add_neg, add_assoc]

/-- The differential of a block two-cochain in inhomogeneous coordinates.
Unlike the degree-three quotient, this formula permits arbitrary universes of
block labels and coefficients (arXiv:2502.20257, lines 5918--5921). -/
theorem d_twoCochainEquiv_apply (L : X → G → G → M) (g h k : G) (x : X) :
    ((Rep.toAdditive (M := G) (G := X → M))
      (inhomogeneousCochains.d (representation G X M) 2
        (fun p ↦ twoCochainEquiv L (p 0, p 1)) ![g, h, k])).toMul
        ((g * h * k) • x) =
      (L x g (h * k) * L x h k) / (L (k • x) g h * L x (g * h) k) := by
  rw [inhomogeneous_d₂_apply]
  change L ((h * k)⁻¹ • (g⁻¹ • ((g * h * k) • x))) h k /
      L (((g * h) * k)⁻¹ • ((g * h * k) • x)) (g * h) k *
      L ((g * (h * k))⁻¹ • ((g * h * k) • x)) g (h * k) /
      L ((g * h)⁻¹ • ((g * h * k) • x)) g h = _
  simp [mul_smul, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]

/-- The L-symbol equation is a differential identity for arbitrary universes of
block labels (arXiv:2502.20257, `eq:omega_and_Ls`). -/
theorem d_eq_const_iff (L : X → G → G → M) (ω : G → G → G → M) :
    inhomogeneousCochains.d (representation G X M) 2
        (fun p ↦ twoCochainEquiv L (p 0, p 1)) =
      (fun p ↦ Additive.ofMul (fun _ : X ↦ ω (p 0) (p 1) (p 2))) ↔
      ∀ x g h k, L x g (h * k) * L x h k =
        ω g h k * L (k • x) g h * L x (g * h) k := by
  constructor
  · intro hω x g h k
    have he := congrArg (fun f ↦ ((Rep.toAdditive (M := G) (G := X → M))
      (f ![g, h, k])).toMul ((g * h * k) • x)) hω
    rw [d_twoCochainEquiv_apply] at he
    change _ = ω g h k at he
    simpa [mul_assoc] using (div_eq_iff_eq_mul.mp he)
  · intro hω
    funext p
    apply (Rep.toAdditive (M := G) (G := X → M)).injective
    apply Additive.toMul.injective
    funext y
    have he := d_twoCochainEquiv_apply L (p 0) (p 1) (p 2)
      ((p 0 * p 1 * p 2)⁻¹ • y)
    have hp : ![p 0, p 1, p 2] = p := by
      funext i
      fin_cases i <;> rfl
    simp only [hp, smul_inv_smul] at he
    rw [he]
    change _ = ω (p 0) (p 1) (p 2)
    exact div_eq_iff_eq_mul.mpr (by
      simpa [mul_assoc] using hω ((p 0 * p 1 * p 2)⁻¹ • y) (p 0) (p 1) (p 2))

end InhomogeneousDifferentials

section Differentials

variable {G X M : Type} [Group G] [MulAction G X] [CommGroup M]

/-- The one-to-two differential in block coordinates is the coboundary of
arXiv:2502.20257, lines 5914--5917. -/
theorem d₁₂_oneCochainEquiv_apply (γ : G → X → M) (g h : G) (x : X) :
    ((groupCohomology.d₁₂ (representation G X M)) (oneCochainEquiv γ) (g, h)).toMul
        ((g * h) • x) =
      γ g (h • x) * γ h x / γ (g * h) x := by
  change γ h (h⁻¹ • (g⁻¹ • ((g * h) • x))) /
      γ (g * h) ((g * h)⁻¹ • ((g * h) • x)) *
      γ g (g⁻¹ • ((g * h) • x)) = _
  simp [mul_smul, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]

/-- The two-to-three differential in block coordinates is the corrected coboundary of
arXiv:2502.20257, lines 5918--5921. The source's last group index is a typo;
see `docs/paper-gaps/fbc25_two_cochain_coboundary_index_typo.tex`. -/
theorem d₂₃_twoCochainEquiv_apply (L : X → G → G → M) (g h k : G) (x : X) :
    ((groupCohomology.d₂₃ (representation G X M)) (twoCochainEquiv L) (g, h, k)).toMul
        ((g * h * k) • x) =
      (L x g (h * k) * L x h k) / (L (k • x) g h * L x (g * h) k) := by
  change L ((h * k)⁻¹ • (g⁻¹ • ((g * h * k) • x))) h k /
      L (((g * h) * k)⁻¹ • ((g * h * k) • x)) (g * h) k *
      L ((g * (h * k))⁻¹ • ((g * h * k) • x)) g (h * k) /
      L ((g * h)⁻¹ • ((g * h * k) • x)) g h = _
  simp [mul_smul, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]

/-- Compatibility with a scalar three-cochain is equality of the differential with
its constant-function image (arXiv:2502.20257, `eq:omega_and_Ls`).
The statement uses Mathlib's differential directly. -/
theorem d₂₃_eq_const_iff (L : X → G → G → M) (ω : G → G → G → M) :
    (groupCohomology.d₂₃ (representation G X M)) (twoCochainEquiv L) =
        (fun p ↦ Additive.ofMul (fun _ : X ↦ ω p.1 p.2.1 p.2.2)) ↔
      ∀ x g h k, L x g (h * k) * L x h k =
        ω g h k * L (k • x) g h * L x (g * h) k := by
  constructor
  · intro hω x g h k
    have he := congrArg (fun f ↦ (f (g, h, k)).toMul ((g * h * k) • x)) hω
    rw [d₂₃_twoCochainEquiv_apply] at he
    change _ = ω g h k at he
    simpa [mul_assoc] using (div_eq_iff_eq_mul.mp he)
  · intro hω
    funext p
    rcases p with ⟨g, h, k⟩
    apply Additive.toMul.injective
    funext y
    have he := d₂₃_twoCochainEquiv_apply L g h k ((g * h * k)⁻¹ • y)
    simp only [smul_inv_smul] at he
    rw [he]
    change _ = ω g h k
    exact div_eq_iff_eq_mul.mpr (by simpa [mul_assoc] using hω ((g * h * k)⁻¹ • y) g h k)

end Differentials

end TNLean.Algebra.PermutationCochains
