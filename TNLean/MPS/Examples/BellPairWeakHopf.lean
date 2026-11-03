/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Algebra.Star.TensorProduct
import Mathlib.LinearAlgebra.Basis.Bilinear
import Mathlib.LinearAlgebra.Matrix.StdBasis
import TNLean.MPS.Symmetry.WeakHopfParentAverage

/-!
# The Bell-pair weak Hopf algebra

Let \(r\ge1\), \(V=\mathbb C^r\otimes\mathbb C^r\) and
\(H=\operatorname{End}(V)\), with matrix units \(e_{ij,kl}=|i,j\rangle\langle k,l|\).
The formulas
\[
  \Delta(e_{ij,kl})=\frac1r\sum_{a,b}e_{ia,kb}\otimes e_{aj,bl},\qquad
  \epsilon(e_{ij,kl})=r\,\delta_{ij}\delta_{kl},\qquad
  S(e_{ij,kl})=e_{lk,ji}
\]
define a coassociative, counital, multiplicative and star-preserving
comultiplication. The canonical integral is the Bell-pair
projector \(\Omega=\frac1r\sum_{i,k}e_{ii,kk}=|\Phi\rangle\langle\Phi|\), and with
\(T=S\) one has \(\sum\Omega_{(1)}S(\Omega_{(2)})=1\).

The defining representation of \(H\) on \(V\) is the physical representation,
and \(\psi(f)_{(i,k),(j,l)}=r^{-1}f(e_{ij,kl})\) is a faithful representation of
the convolution dual.
These data form a weak-Hopf MPO representation with physical and bond
dimension \(r^2\), and the weak-Hopf average of GLM23 Appendix B is
\[
  E_n(B)=\frac1{r^2}\sum_{p,q}\rho_n(e_{pq})\,B\,\rho_n(e_{qp}),
\]
the sum running over pairs of indices. The comultiplication is a scoped
instance, since a matrix algebra carries many coalgebra structures.

## References

* `docs/paper-gaps/glm23_wha_parent_completion.tex`, section "An elementary
  fusion-compatible test", lines 41--125.
* Garre-Rubio--Lootens--Molnár, arXiv:2203.12563v3, Appendix B,
  lines 2463--2466.
* Molnár et al., arXiv:2204.05940v1, Section 4.
-/

open scoped Matrix TensorProduct
open Matrix (single)

noncomputable section

namespace MPOTensor.BellPairWeakHopf

variable (r : ℕ)

/-- The algebra \(\operatorname{End}(\mathbb C^r\otimes\mathbb C^r)\), whose matrix
unit `single (i, j) (k, l) 1` is \(e_{ij,kl}=|i,j\rangle\langle k,l|\). -/
abbrev BellPairAlgebra : Type := Matrix (Fin r × Fin r) (Fin r × Fin r) ℂ

/-! ### The comultiplication, counit and antipode on matrix units -/

/-- The comultiplication of a matrix unit,
\(\Delta(e_{ij,kl})=r^{-1}\sum_{a,b}e_{ia,kb}\otimes e_{aj,bl}\), with the pair
\((a,b)\) written `c`. -/
def comulSingle (p q : Fin r × Fin r) : BellPairAlgebra r ⊗[ℂ] BellPairAlgebra r :=
  (r : ℂ)⁻¹ • ∑ c : Fin r × Fin r,
    single (p.1, c.1) (q.1, c.2) (1 : ℂ) ⊗ₜ[ℂ] single (c.1, p.2) (c.2, q.2) (1 : ℂ)

/-- The comultiplication of the Bell-pair weak Hopf algebra, the linear extension
of `comulSingle`. -/
def bellComul : BellPairAlgebra r →ₗ[ℂ] BellPairAlgebra r ⊗[ℂ] BellPairAlgebra r :=
  (Matrix.stdBasis ℂ (Fin r × Fin r) (Fin r × Fin r)).constr ℂ
    fun pq ↦ comulSingle r pq.1 pq.2

/-- The counit \(\epsilon(e_{ij,kl})=r\,\delta_{ij}\delta_{kl}\). -/
def bellCounit : BellPairAlgebra r →ₗ[ℂ] ℂ :=
  (Matrix.stdBasis ℂ (Fin r × Fin r) (Fin r × Fin r)).constr ℂ
    fun pq ↦ if (pq.1.1, pq.2.1) = (pq.1.2, pq.2.2) then (r : ℂ) else 0

/-- The antipode \(S(e_{ij,kl})=e_{lk,ji}\), which is also the map \(T\) used with
the canonical integral. -/
def bellAntipode : BellPairAlgebra r →ₗ[ℂ] BellPairAlgebra r :=
  (Matrix.stdBasis ℂ (Fin r × Fin r) (Fin r × Fin r)).constr ℂ
    fun pq ↦ single pq.2.swap pq.1.swap (1 : ℂ)

/-- The canonical integral, the Bell-pair projector
\(\Omega=\frac1r\sum_{i,k}e_{ii,kk}=|\Phi\rangle\langle\Phi|\). -/
def bellIntegral : BellPairAlgebra r :=
  (r : ℂ)⁻¹ • ∑ i : Fin r, ∑ k : Fin r, single (i, i) (k, k) (1 : ℂ)

theorem bellComul_single (p q : Fin r × Fin r) :
    bellComul r (single p q 1) = comulSingle r p q := by
  have h := (Matrix.stdBasis ℂ (Fin r × Fin r) (Fin r × Fin r)).constr_basis ℂ
    (fun pq ↦ comulSingle r pq.1 pq.2) (p, q)
  rw [Matrix.stdBasis_eq_single] at h
  exact h

theorem bellCounit_single (i j k l : Fin r) :
    bellCounit r (single (i, j) (k, l) 1) = if (i, k) = (j, l) then (r : ℂ) else 0 := by
  have h := (Matrix.stdBasis ℂ (Fin r × Fin r) (Fin r × Fin r)).constr_basis ℂ
    (fun pq : (Fin r × Fin r) × (Fin r × Fin r) ↦
      if (pq.1.1, pq.2.1) = (pq.1.2, pq.2.2) then (r : ℂ) else 0) ((i, j), (k, l))
  rw [Matrix.stdBasis_eq_single] at h
  exact h

theorem bellAntipode_single (p q : Fin r × Fin r) :
    bellAntipode r (single p q 1) = single q.swap p.swap 1 := by
  have h := (Matrix.stdBasis ℂ (Fin r × Fin r) (Fin r × Fin r)).constr_basis ℂ
    (fun pq : (Fin r × Fin r) × (Fin r × Fin r) ↦ single pq.2.swap pq.1.swap (1 : ℂ)) (p, q)
  rw [Matrix.stdBasis_eq_single] at h
  exact h

/-- Coassociativity: both iterated coproducts of \(e_{ij,kl}\) insert two Bell
pairs, \(r^{-2}\sum e_{ia,kb}\otimes e_{aa',bb'}\otimes e_{a'j,b'l}\). -/
theorem bellComul_coassoc :
    TensorProduct.assoc ℂ (BellPairAlgebra r) (BellPairAlgebra r) (BellPairAlgebra r) ∘ₗ
        (bellComul r).rTensor (BellPairAlgebra r) ∘ₗ bellComul r =
      (bellComul r).lTensor (BellPairAlgebra r) ∘ₗ bellComul r := by
  refine (Matrix.stdBasis ℂ (Fin r × Fin r) (Fin r × Fin r)).ext fun pq ↦ ?_
  obtain ⟨p, q⟩ := pq
  rw [Matrix.stdBasis_eq_single]
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, bellComul_single, comulSingle, map_smul,
    map_sum, LinearMap.rTensor_tmul, LinearMap.lTensor_tmul, TensorProduct.sum_tmul,
    TensorProduct.tmul_sum, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul,
    TensorProduct.assoc_tmul, Finset.smul_sum]
  exact Finset.sum_comm

/-- The comultiplication preserves the involution on matrix units. -/
theorem star_comulSingle (p q : Fin r × Fin r) :
    star (comulSingle r p q) = comulSingle r q p := by
  simp only [comulSingle, star_smul, star_sum, TensorProduct.star_tmul,
    Matrix.star_eq_conjTranspose, Matrix.conjTranspose_single, star_one, star_inv₀,
    star_natCast]
  congr 1
  exact Fintype.sum_equiv (Equiv.prodComm (Fin r) (Fin r)) _ _ fun c ↦ rfl

private theorem single_eq_smul_single (p q : Fin r × Fin r) (a : ℂ) :
    (single p q a : BellPairAlgebra r) = a • single p q 1 := by
  rw [Matrix.smul_single, smul_eq_mul, mul_one]

/-- Multiplicativity of the comultiplication on matrix units \(e_{p,q}e_{p',q'}\)
with mismatched inner indices \(q\ne p'\), where both sides vanish. -/
theorem bellComul_single_mul_single_of_ne {p q p' q' : Fin r × Fin r} (h : q ≠ p') :
    bellComul r (single p q 1 * single p' q' 1) =
      bellComul r (single p q 1) * bellComul r (single p' q' 1) := by
  rw [Matrix.single_mul_single_of_ne (h := h), map_zero, bellComul_single, bellComul_single]
  simp only [comulSingle, smul_mul_smul_comm, Finset.sum_mul_sum,
    Algebra.TensorProduct.tmul_mul_tmul]
  symm
  apply smul_eq_zero_of_right
  refine Finset.sum_eq_zero fun c _ ↦ Finset.sum_eq_zero fun c' _ ↦ ?_
  by_cases h1 : (q.1, c.2) = (p'.1, c'.1)
  · have h2 : (c.2, q.2) ≠ (c'.1, p'.2) := fun e ↦
      h (Prod.ext (Prod.ext_iff.mp h1).1 (Prod.ext_iff.mp e).2)
    simp only [Matrix.single_mul_single_of_ne (h := h2), TensorProduct.tmul_zero]
  · simp only [Matrix.single_mul_single_of_ne (h := h1), TensorProduct.zero_tmul]

/-- The dual matrix of a functional, \(\psi(f)_{(i,k),(j,l)}=r^{-1}f(e_{ij,kl})\). -/
def dualMatrix (f : WithConv (BellPairAlgebra r →ₗ[ℂ] ℂ)) :
    Matrix (Fin r × Fin r) (Fin r × Fin r) ℂ :=
  Matrix.of fun a b ↦ (r : ℂ)⁻¹ * f.ofConv (single (a.1, b.1) (a.2, b.2) 1)

theorem dualMatrix_apply (f : WithConv (BellPairAlgebra r →ₗ[ℂ] ℂ)) (a b : Fin r × Fin r) :
    dualMatrix r f a b = (r : ℂ)⁻¹ * f.ofConv (single (a.1, b.1) (a.2, b.2) 1) := rfl

private theorem sum_sum_sum_single :
    ∑ i : Fin r, ∑ _k : Fin r, ∑ c : Fin r × Fin r, single (i, c.1) (i, c.1) (1 : ℂ) =
      ((r : ℂ) * r) • (1 : Matrix (Fin r × Fin r) (Fin r × Fin r) ℂ) := by
  have hdiag : ∑ i : Fin r, ∑ a : Fin r, single (i, a) (i, a) (1 : ℂ) =
      (1 : Matrix (Fin r × Fin r) (Fin r × Fin r) ℂ) := by
    rw [← Matrix.sum_single_one, Fintype.sum_prod_type]
  simp only [Fintype.sum_prod_type, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    ← Finset.smul_sum, hdiag]
  rw [← Nat.cast_smul_eq_nsmul ℂ, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]

/-! ### The physical representation -/

/-- The defining representation of \(H\) on \(\mathbb C^r\otimes\mathbb C^r\), with the
pair index flattened to `Fin (r * r)`. -/
def phys : BellPairAlgebra r →ₐ[ℂ] Matrix (Fin (r * r)) (Fin (r * r)) ℂ :=
  (Matrix.reindexAlgEquiv ℂ ℂ finProdFinEquiv).toAlgHom

/-- The defining representation is a star representation. -/
theorem phys_star (x : BellPairAlgebra r) : phys r (star x) = (phys r x)ᴴ := by
  ext a b
  rfl

section NeZero

variable [NeZero r]

theorem rTensor_bellCounit_comp_bellComul :
    (bellCounit r).rTensor (BellPairAlgebra r) ∘ₗ bellComul r =
      TensorProduct.mk ℂ ℂ (BellPairAlgebra r) 1 := by
  have hr : (r : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne r)
  refine (Matrix.stdBasis ℂ (Fin r × Fin r) (Fin r × Fin r)).ext fun pq ↦ ?_
  obtain ⟨p, q⟩ := pq
  rw [TensorProduct.mk_apply, Matrix.stdBasis_eq_single, LinearMap.comp_apply, bellComul_single,
    comulSingle, map_smul, map_sum, Finset.sum_eq_single (p.1, q.1)]
  · dsimp only
    rw [LinearMap.rTensor_tmul, bellCounit_single, if_pos rfl, TensorProduct.smul_tmul',
      smul_eq_mul, inv_mul_cancel₀ hr]
  · rintro c - hc
    rw [LinearMap.rTensor_tmul, bellCounit_single, if_neg, TensorProduct.zero_tmul]
    exact fun h ↦ hc h.symm
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem lTensor_bellCounit_comp_bellComul :
    (bellCounit r).lTensor (BellPairAlgebra r) ∘ₗ bellComul r =
      (TensorProduct.mk ℂ (BellPairAlgebra r) ℂ).flip 1 := by
  have hr : (r : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne r)
  refine (Matrix.stdBasis ℂ (Fin r × Fin r) (Fin r × Fin r)).ext fun pq ↦ ?_
  obtain ⟨p, q⟩ := pq
  rw [LinearMap.flip_apply, TensorProduct.mk_apply, Matrix.stdBasis_eq_single,
    LinearMap.comp_apply, bellComul_single, comulSingle, map_smul, map_sum,
    Finset.sum_eq_single (p.2, q.2)]
  · dsimp only
    rw [LinearMap.lTensor_tmul, bellCounit_single, if_pos rfl, ← TensorProduct.tmul_smul,
      smul_eq_mul, inv_mul_cancel₀ hr]
  · rintro c - hc
    rw [LinearMap.lTensor_tmul, bellCounit_single, if_neg, TensorProduct.tmul_zero]
    exact fun h ↦ hc h
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- Products of matrix units with matching inner indices: the two inserted Bell
pairs contract to one, and the free index contributes the factor \(r\). -/
theorem bellComul_single_mul_single_same (p q q' : Fin r × Fin r) :
    bellComul r (single p q 1 * single q q' 1) =
      bellComul r (single p q 1) * bellComul r (single q q' 1) := by
  have hr : (r : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne r)
  have key : ∀ c : Fin r × Fin r,
      ∑ c' : Fin r × Fin r,
        (single (p.1, c.1) (q.1, c.2) (1 : ℂ) * single (q.1, c'.1) (q'.1, c'.2) 1) ⊗ₜ[ℂ]
          (single (c.1, p.2) (c.2, q.2) (1 : ℂ) * single (c'.1, q.2) (c'.2, q'.2) 1) =
        ∑ b : Fin r,
          single (p.1, c.1) (q'.1, b) (1 : ℂ) ⊗ₜ[ℂ] single (c.1, p.2) (b, q'.2) (1 : ℂ) := by
    intro c
    rw [Fintype.sum_prod_type, Finset.sum_eq_single c.2]
    · simp only [Matrix.single_mul_single_same, mul_one]
    · intro a _ ha
      refine Finset.sum_eq_zero fun b _ ↦ ?_
      have hne : (q.1, c.2) ≠ (q.1, a) := fun e ↦ ha (Prod.ext_iff.mp e).2.symm
      dsimp only
      rw [Matrix.single_mul_single_of_ne (h := hne), TensorProduct.zero_tmul]
    · intro h
      exact absurd (Finset.mem_univ _) h
  rw [Matrix.single_mul_single_same, mul_one, bellComul_single, bellComul_single,
    bellComul_single]
  simp only [comulSingle, smul_mul_smul_comm, Finset.sum_mul_sum,
    Algebra.TensorProduct.tmul_mul_tmul, key]
  simp only [Fintype.sum_prod_type, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  rw [← Finset.smul_sum, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, mul_assoc, inv_mul_cancel₀ hr,
    mul_one]

theorem bellComul_single_mul_single (p q p' q' : Fin r × Fin r) :
    bellComul r (single p q 1 * single p' q' 1) =
      bellComul r (single p q 1) * bellComul r (single p' q' 1) := by
  by_cases h : q = p'
  · subst h
    exact bellComul_single_mul_single_same r _ _ _
  · exact bellComul_single_mul_single_of_ne r h

variable {r} in
/-- The Bell-pair coalgebra structure on \(\operatorname{End}(\mathbb C^r\otimes\mathbb C^r)\).
It is scoped, since a matrix algebra carries many coalgebra structures. -/
scoped instance instCoalgebra : Coalgebra ℂ (BellPairAlgebra r) where
  comul := bellComul r
  counit := bellCounit r
  coassoc := bellComul_coassoc r
  rTensor_counit_comp_comul := rTensor_bellCounit_comp_bellComul r
  lTensor_counit_comp_comul := lTensor_bellCounit_comp_bellComul r

theorem comul_single (p q : Fin r × Fin r) :
    Coalgebra.comul (R := ℂ) (single p q 1 : BellPairAlgebra r) = comulSingle r p q :=
  bellComul_single r p q

theorem counit_single (i j k l : Fin r) :
    Coalgebra.counit (R := ℂ) (single (i, j) (k, l) 1 : BellPairAlgebra r) =
      if (i, k) = (j, l) then (r : ℂ) else 0 :=
  bellCounit_single r i j k l

/-- The comultiplication is multiplicative, \(\Delta(xy)=\Delta(x)\Delta(y)\). -/
theorem comul_mul (x y : BellPairAlgebra r) :
    Coalgebra.comul (R := ℂ) (x * y) = Coalgebra.comul x * Coalgebra.comul y := by
  have h : (LinearMap.mul ℂ (BellPairAlgebra r)).compr₂ (bellComul r) =
      (LinearMap.mul ℂ (BellPairAlgebra r ⊗[ℂ] BellPairAlgebra r)).compl₁₂ (bellComul r)
        (bellComul r) :=
    LinearMap.ext_basis (Matrix.stdBasis ℂ (Fin r × Fin r) (Fin r × Fin r))
      (Matrix.stdBasis ℂ (Fin r × Fin r) (Fin r × Fin r)) fun pq pq' ↦ by
        obtain ⟨p, q⟩ := pq
        obtain ⟨p', q'⟩ := pq'
        rw [LinearMap.compr₂_apply, LinearMap.compl₁₂_apply, LinearMap.mul_apply',
          LinearMap.mul_apply', Matrix.stdBasis_eq_single, Matrix.stdBasis_eq_single]
        exact bellComul_single_mul_single r p q p' q'
  have hxy := LinearMap.congr_fun₂ h x y
  rw [LinearMap.compr₂_apply, LinearMap.compl₁₂_apply, LinearMap.mul_apply',
    LinearMap.mul_apply'] at hxy
  exact hxy

theorem comul_star_single (p q : Fin r × Fin r) (a : ℂ) :
    Coalgebra.comul (R := ℂ) (star (single p q a : BellPairAlgebra r)) =
      star (Coalgebra.comul (R := ℂ) (single p q a : BellPairAlgebra r)) := by
  rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_single, single_eq_smul_single r q p,
    single_eq_smul_single r p q a, map_smul, map_smul, star_smul, comul_single, comul_single,
    star_comulSingle]

/-- The comultiplication preserves the involution. -/
theorem comul_star (x : BellPairAlgebra r) :
    Coalgebra.comul (R := ℂ) (star x) = star (Coalgebra.comul (R := ℂ) x) := by
  rw [Matrix.matrix_eq_sum_single x]
  simp only [star_sum, map_sum, comul_star_single]

/-! ### The dual representation -/

theorem dualMatrix_one : dualMatrix r 1 = 1 := by
  have hr : (r : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne r)
  ext a b
  rw [dualMatrix_apply, LinearMap.convOne_apply, Algebra.algebraMap_self_apply, counit_single,
    Prod.mk.eta, Prod.mk.eta, Matrix.one_apply, mul_ite, mul_zero, inv_mul_cancel₀ hr]

theorem dualMatrix_mul (f g : WithConv (BellPairAlgebra r →ₗ[ℂ] ℂ)) :
    dualMatrix r (f * g) = dualMatrix r f * dualMatrix r g := by
  ext a b
  rw [dualMatrix_apply, Matrix.mul_apply, LinearMap.convMul_apply, comul_single, comulSingle,
    map_smul, map_sum, map_smul, map_sum, smul_eq_mul, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ ↦ ?_
  rw [TensorProduct.map_tmul, LinearMap.mul'_apply, dualMatrix_apply, dualMatrix_apply]
  dsimp only
  ring

/-- The dual matrix as an algebra homomorphism from the convolution dual. -/
def dualAlgHom :
    WithConv (BellPairAlgebra r →ₗ[ℂ] ℂ) →ₐ[ℂ] Matrix (Fin r × Fin r) (Fin r × Fin r) ℂ :=
  AlgHom.ofLinearMap
    { toFun := dualMatrix r
      map_add' := fun f g ↦ by
        ext a b
        rw [Matrix.add_apply, dualMatrix_apply, dualMatrix_apply, dualMatrix_apply,
          WithConv.ofConv_add, LinearMap.add_apply, mul_add]
      map_smul' := fun c f ↦ by
        ext a b
        simp only [RingHom.id_apply, Matrix.smul_apply, dualMatrix_apply, WithConv.ofConv_smul,
          LinearMap.smul_apply, smul_eq_mul]
        ring }
    (dualMatrix_one r) (dualMatrix_mul r)

/-- The faithful representation of the convolution dual on the bond space, with
the pair index flattened to `Fin (r * r)`. -/
def virt : WithConv (BellPairAlgebra r →ₗ[ℂ] ℂ) →ₐ[ℂ] Matrix (Fin (r * r)) (Fin (r * r)) ℂ :=
  (Matrix.reindexAlgEquiv ℂ ℂ finProdFinEquiv).toAlgHom.comp (dualAlgHom r)

/-- The dual representation is faithful: the entries of \(\psi(f)\) are the values
of \(f\) on the matrix units. -/
theorem virt_injective : Function.Injective (virt r) := by
  have hr : (r : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne r)
  intro f g hfg
  have h : dualMatrix r f = dualMatrix r g := by
    apply (Matrix.reindexAlgEquiv ℂ ℂ (finProdFinEquiv (m := r) (n := r))).injective
    exact hfg
  apply WithConv.ext
  refine (Matrix.stdBasis ℂ (Fin r × Fin r) (Fin r × Fin r)).ext fun pq ↦ ?_
  obtain ⟨p, q⟩ := pq
  have hpq := congrArg (fun M ↦ M (p.1, q.1) (p.2, q.2)) h
  simp only [dualMatrix_apply] at hpq
  rw [Matrix.stdBasis_eq_single]
  exact mul_left_cancel₀ (inv_ne_zero hr) hpq

/-! ### The canonical integral -/

theorem comul_bellIntegral :
    Coalgebra.comul (R := ℂ) (bellIntegral r) =
      ∑ i : Fin r, ∑ k : Fin r, ∑ c : Fin r × Fin r,
        (((r : ℂ)⁻¹ * (r : ℂ)⁻¹) • single (i, c.1) (k, c.2) (1 : ℂ)) ⊗ₜ[ℂ]
          single (c.1, i) (c.2, k) (1 : ℂ) := by
  simp only [bellIntegral, map_smul, map_sum, comul_single, comulSingle, Finset.smul_sum,
    smul_smul, TensorProduct.smul_tmul']

/-- The integral identity in \(H\): \(\sum\Omega_{(1)}S(\Omega_{(2)})=1\). -/
theorem mul'_map_bellAntipode_comul_bellIntegral :
    LinearMap.mul' ℂ (BellPairAlgebra r)
      (TensorProduct.map LinearMap.id (bellAntipode r)
        (Coalgebra.comul (R := ℂ) (bellIntegral r))) = 1 := by
  have hr : (r : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne r)
  rw [comul_bellIntegral]
  simp only [map_sum, TensorProduct.map_tmul, LinearMap.id_apply, bellAntipode_single,
    Prod.swap_prod_mk, LinearMap.mul'_apply, smul_mul_assoc, Matrix.single_mul_single_same,
    mul_one, ← Finset.smul_sum, sum_sum_sum_single]
  rw [smul_smul, mul_mul_mul_comm, inv_mul_cancel₀ hr, one_mul, one_smul]

theorem mul'_map_comul_comp_bellAntipode (t : BellPairAlgebra r ⊗[ℂ] BellPairAlgebra r) :
    LinearMap.mul' ℂ (BellPairAlgebra r ⊗[ℂ] BellPairAlgebra r)
        (TensorProduct.map (Coalgebra.comul (R := ℂ) (A := BellPairAlgebra r))
          (Coalgebra.comul (R := ℂ) ∘ₗ bellAntipode r) t) =
      Coalgebra.comul (R := ℂ)
        (LinearMap.mul' ℂ (BellPairAlgebra r)
          (TensorProduct.map LinearMap.id (bellAntipode r) t)) := by
  induction t using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a b =>
    simp only [TensorProduct.map_tmul, LinearMap.mul'_apply, LinearMap.comp_apply,
      LinearMap.id_apply, comul_mul]
  | add s t hs ht => simp only [map_add, hs, ht]

/-- The normalization of GLM23 Appendix B for the Bell-pair integral:
\(\sum\Delta(\Omega_{(1)})\Delta(S(\Omega_{(2)}))=\Delta(1)\). -/
theorem mul'_map_comul_bellIntegral :
    LinearMap.mul' ℂ (BellPairAlgebra r ⊗[ℂ] BellPairAlgebra r)
      (TensorProduct.map (Coalgebra.comul (R := ℂ) (A := BellPairAlgebra r))
        (Coalgebra.comul (R := ℂ) ∘ₗ bellAntipode r)
        (Coalgebra.comul (R := ℂ) (bellIntegral r))) =
      Coalgebra.comul (R := ℂ) (1 : BellPairAlgebra r) := by
  rw [mul'_map_comul_comp_bellAntipode, mul'_map_bellAntipode_comul_bellIntegral]

/-! ### The weak-Hopf representation and its average -/

/-- The Bell-pair weak Hopf algebra as a weak-Hopf MPO representation, with the
defining physical representation, the dual representation `virt`, the canonical
integral \(\Omega=|\Phi\rangle\langle\Phi|\), and \(T=S\). Source:
`docs/paper-gaps/glm23_wha_parent_completion.tex`, lines 47--87. -/
def weakHopfRepresentation : WeakHopfRepresentation (BellPairAlgebra r) (r * r) (r * r) where
  phys := phys r
  phys_star := phys_star r
  virt := virt r
  virt_injective := virt_injective r
  comul_mul := comul_mul r
  comul_star := comul_star r
  pullThrough := bellAntipode r
  integral := bellIntegral r
  mul'_map_comul_integral := mul'_map_comul_bellIntegral r

/-- The Sweedler representation
\(\Delta(\Omega)=r^{-2}\sum_{p,q}e_{pq}\otimes e_{\bar p\bar q}\), where
\(\overline{(i,a)}=(a,i)\). -/
def integralRepr :
    Coalgebra.Repr ℂ (weakHopfRepresentation r).integral
      ((Fin r × Fin r) × (Fin r × Fin r)) where
  index := Finset.univ
  left pq := ((r : ℂ)⁻¹ * (r : ℂ)⁻¹) • single pq.1 pq.2 (1 : ℂ)
  right pq := single pq.1.swap pq.2.swap (1 : ℂ)
  eq := by
    rw [show (weakHopfRepresentation r).integral = bellIntegral r from rfl, comul_bellIntegral]
    simp only [Fintype.sum_prod_type, Prod.swap_prod_mk]
    exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_comm

/-- The weak-Hopf average of the Bell-pair algebra at every length,
\(E_n(B)=r^{-2}\sum_{p,q}\rho_n(e_{pq})\,B\,\rho_n(e_{qp})\). At two sites this is the
first step of the computation \(E(X)=r^{-2}\operatorname{tr}(QX)\,Q\) in
`docs/paper-gaps/glm23_wha_parent_completion.tex`, lines 110--120. -/
theorem weakHopfAverage_eq_sum_single (n : ℕ)
    (P : Module.End ℂ (EuclideanSpace ℂ (Fin n → Fin (r * r)))) :
    (weakHopfRepresentation r).weakHopfAverage n P =
      ∑ p : Fin r × Fin r, ∑ q : Fin r × Fin r, ((r : ℂ)⁻¹ * (r : ℂ)⁻¹) •
        (Matrix.toEuclideanLin ((weakHopfRepresentation r).rep n (single p q 1)) * P *
          Matrix.toEuclideanLin ((weakHopfRepresentation r).rep n (single q p 1))) := by
  rw [(weakHopfRepresentation r).weakHopfAverage_eq_sum (integralRepr r) P]
  change ∑ pq : (Fin r × Fin r) × (Fin r × Fin r), _ = _
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun p _ ↦ Finset.sum_congr rfl fun q _ ↦ ?_
  change Matrix.toEuclideanLin ((weakHopfRepresentation r).rep n
      (((r : ℂ)⁻¹ * (r : ℂ)⁻¹) • single p q 1)) * P *
    Matrix.toEuclideanLin ((weakHopfRepresentation r).rep n
      (bellAntipode r (single p.swap q.swap 1))) = _
  rw [bellAntipode_single, Prod.swap_swap, Prod.swap_swap, map_smul, map_smul, smul_mul_assoc,
    smul_mul_assoc]

end NeZero

end MPOTensor.BellPairWeakHopf
