/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Algebra.Star.TensorProduct
import Mathlib.LinearAlgebra.Basis.Bilinear
import Mathlib.LinearAlgebra.Matrix.StdBasis
import TNLean.Algebra.MatrixSingleSpan
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

The represented coproduct is \(\rho_{n+1}(e_{pq})=r^{-n}|u_p\rangle\langle u_q|\),
where \(u_{(i,j)}(\sigma)=(E_{\sigma_1}\cdots E_{\sigma_{n+1}})_{ij}\) for the matrix
units \(E_{st}\) of \(M_r\). Hence \(E_n(X)=r^{-2}\operatorname{tr}(Q_nX)\,Q_n\) with
\(Q_n=\rho_n(1)\), at two sites the displayed evaluation of the note. The state
tensor \(A^{ij}=E_{ij}/\sqrt r\) is injective at one site and compatible with
the operator tensor, its support projection is \(P_n=Q_n\), and so
\(E_n(P_n)=P_n\) while the uncompleted average \(E_n(I-P_n)\) vanishes.

## References

* `docs/paper-gaps/glm23_wha_parent_completion.tex`, section "An elementary
  fusion-compatible test", and section "The weak-Hopf realization".
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
    rw [show (single (c.1, p.2) (c.2, q.2) 1 : BellPairAlgebra r) *
        single (c'.1, p'.2) (c'.2, q'.2) 1 = 0 from
        Matrix.single_mul_single_of_ne _ _ _ _ h2 _, TensorProduct.tmul_zero]
  · rw [show (single (p.1, c.1) (q.1, c.2) 1 : BellPairAlgebra r) *
        single (p'.1, c'.1) (q'.1, c'.2) 1 = 0 from
        Matrix.single_mul_single_of_ne _ _ _ _ h1 _, TensorProduct.zero_tmul]

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
    rw [LinearMap.rTensor_tmul, bellCounit_single, ite_eq_left rfl, TensorProduct.smul_tmul',
      smul_eq_mul, inv_mul_cancel₀ hr]
  · rintro c - hc
    rw [LinearMap.rTensor_tmul, bellCounit_single, ite_eq_right, TensorProduct.zero_tmul]
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
    rw [LinearMap.lTensor_tmul, bellCounit_single, ite_eq_left rfl, ← TensorProduct.tmul_smul,
      smul_eq_mul, inv_mul_cancel₀ hr]
  · rintro c - hc
    rw [LinearMap.lTensor_tmul, bellCounit_single, ite_eq_right, TensorProduct.tmul_zero]
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
  induction t using TensorProduct.inductionOn with
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

/-! ### The Bell-pair state tensor -/

/-- The matrix units \(E_{ij}\) of \(M_r\), indexed by the flattened pair \((i,j)\). -/
def unitTensor : MPSTensor (r * r) r :=
  fun σ ↦ single (finProdFinEquiv.symm σ).1 (finProdFinEquiv.symm σ).2 1

/-- The Bell-pair state tensor \(A^{ij}=E_{ij}/\sqrt r\) of
`docs/paper-gaps/glm23_wha_parent_completion.tex`, section "An elementary
fusion-compatible test"; its states with boundary \(Y\) are the vectors
obtained from \(Y\) by inserting \(n-1\) normalized Bell pairs. -/
def stateTensor : MPSTensor (r * r) r :=
  fun σ ↦ ((Real.sqrt r : ℝ) : ℂ)⁻¹ • unitTensor r σ

/-- The entry \((E_{\sigma_1}\cdots E_{\sigma_n})_{ij}\) of a word of matrix units,
with `p = (i, j)`: it is one when consecutive letters chain from `i` to `j`, and
zero otherwise. -/
def unitWordEntry {n : ℕ} (p : Fin r × Fin r) (σ : Fin n → Fin (r * r)) : ℂ :=
  Kraus.evalWord (unitTensor r) (List.ofFn σ) p.1 p.2

theorem unitWordEntry_zero (p : Fin r × Fin r) (σ : Fin 0 → Fin (r * r)) :
    unitWordEntry r p σ = if p.1 = p.2 then 1 else 0 := by
  simp only [unitWordEntry, List.ofFn_zero, Kraus.evalWord_nil, Matrix.one_apply]

/-- Peeling off the first letter \(E_{st}\) of a word of matrix units. -/
theorem unitWordEntry_succ {n : ℕ} (p : Fin r × Fin r) (σ : Fin (n + 1) → Fin (r * r)) :
    unitWordEntry r p σ =
      if (finProdFinEquiv.symm (σ 0)).1 = p.1 then
        unitWordEntry r ((finProdFinEquiv.symm (σ 0)).2, p.2) (Fin.tail σ)
      else 0 := by
  rw [unitWordEntry, List.ofFn_succ, Kraus.evalWord_cons]
  dsimp only [unitTensor]
  split_ifs with h
  · rw [← h, Matrix.single_mul_apply_same, one_mul]
    rfl
  · exact Matrix.single_mul_apply_of_ne _ _ _ _ _ (Ne.symm h) _

/-- Summing over the first letter of a word of matrix units against a boundary
trace moves the letter into the boundary. -/
private theorem sum_unitWordEntry_mul_trace_succ (n : ℕ) (q : Fin r × Fin r)
    (Y : Matrix (Fin r) (Fin r) ℂ) :
    ∑ τ : Fin (n + 1) → Fin (r * r),
        unitWordEntry r q τ * (Y * Kraus.evalWord (unitTensor r) (List.ofFn τ)).trace =
      ∑ a : Fin r, ∑ w : Fin n → Fin (r * r),
        unitWordEntry r (a, q.2) w *
          (Y * single q.1 a 1 * Kraus.evalWord (unitTensor r) (List.ofFn w)).trace := by
  have hsplit : ∀ G : (Fin (n + 1) → Fin (r * r)) → ℂ, ∑ τ, G τ =
      ∑ s : Fin r × Fin r, ∑ w : Fin n → Fin (r * r), G (Fin.cons (finProdFinEquiv s) w) := by
    intro G
    rw [← (Fin.consEquiv fun _ ↦ Fin (r * r)).sum_comp, Fintype.sum_prod_type,
      ← finProdFinEquiv.sum_comp]
    rfl
  rw [hsplit, Fintype.sum_prod_type]
  refine (Finset.sum_eq_single q.1 (fun b _ hb ↦ ?_)
    (fun h ↦ absurd (Finset.mem_univ _) h)).trans ?_
  · simp only [unitWordEntry_succ, Fin.cons_zero, Equiv.symm_apply_apply, hb, ↓reduceIte,
      zero_mul, Finset.sum_const_zero]
  · refine Finset.sum_congr rfl fun a _ ↦ Finset.sum_congr rfl fun w _ ↦ ?_
    simp only [unitWordEntry_succ, Fin.cons_zero, Fin.tail_cons, Equiv.symm_apply_apply,
      ↓reduceIte, List.ofFn_cons, Kraus.evalWord_cons, unitTensor, Matrix.mul_assoc]

/-- The overlap of a word-entry vector with a state of boundary \(Y\) on
\(n+1\) sites: the \(r^n\) chains from `q.1` to `q.2` each contribute
\(Y_{q_2q_1}\). -/
theorem sum_unitWordEntry_mul_trace (n : ℕ) (q : Fin r × Fin r)
    (Y : Matrix (Fin r) (Fin r) ℂ) :
    ∑ τ : Fin (n + 1) → Fin (r * r),
        unitWordEntry r q τ * (Y * Kraus.evalWord (unitTensor r) (List.ofFn τ)).trace =
      (r : ℂ) ^ n * Y q.2 q.1 := by
  induction n generalizing q Y with
  | zero =>
    rw [sum_unitWordEntry_mul_trace_succ]
    simp [unitWordEntry_zero, Matrix.trace_mul_single]
  | succ n ih =>
    rw [sum_unitWordEntry_mul_trace_succ]
    simp only [ih, Matrix.mul_single_apply_same, mul_one, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, pow_succ]
    ring

theorem evalWord_stateTensor (w : List (Fin (r * r))) :
    Kraus.evalWord (stateTensor r) w =
      (((Real.sqrt r : ℝ) : ℂ)⁻¹ ^ w.length) • Kraus.evalWord (unitTensor r) w :=
  Kraus.evalWord_smul (((Real.sqrt r : ℝ) : ℂ)⁻¹) (unitTensor r) w

theorem mpvWithBoundary_stateTensor {n : ℕ} (Y : Matrix (Fin r) (Fin r) ℂ)
    (τ : Fin n → Fin (r * r)) :
    MPSTensor.mpvWithBoundary (stateTensor r) Y τ =
      ((Real.sqrt r : ℝ) : ℂ)⁻¹ ^ n *
        (Y * Kraus.evalWord (unitTensor r) (List.ofFn τ)).trace := by
  rw [MPSTensor.mpvWithBoundary, evalWord_stateTensor, List.length_ofFn, Matrix.mul_smul,
    Matrix.trace_smul, smul_eq_mul]

/-- `toEuclideanLin` turns matrix products into products of operators. -/
private theorem toEuclideanLin_mul {m : Type*} [Fintype m] [DecidableEq m]
    (M N : Matrix m m ℂ) :
    Matrix.toEuclideanLin (M * N) = Matrix.toEuclideanLin M * Matrix.toEuclideanLin N :=
  Matrix.toLpLin_mul_same 2 M N

private theorem trace_toEuclideanLin {m : Type*} [Fintype m] [DecidableEq m]
    (M : Matrix m m ℂ) : LinearMap.trace ℂ _ (Matrix.toEuclideanLin M) = M.trace :=
  Matrix.trace_toLin_eq M (EuclideanSpace.basisFun m ℂ).toBasis

section NeZero

variable [NeZero r]

/-- The represented coproduct of a matrix unit factors through words of matrix
units, \(\rho_{n+1}(e_{pq})_{\sigma\tau}=r^{-n}(E_\sigma)_p(E_\tau)_q\); this is
\(\rho_{n+1}(x)=W_{n+1}xW_{n+1}^*\) in
`docs/paper-gaps/glm23_wha_parent_completion.tex`. -/
theorem rep_single_apply (n : ℕ) (p q : Fin r × Fin r) (σ τ : Fin (n + 1) → Fin (r * r)) :
    (weakHopfRepresentation r).rep (n + 1) (single p q 1) σ τ =
      (r : ℂ)⁻¹ ^ n * unitWordEntry r p σ * unitWordEntry r q τ := by
  induction n generalizing p q with
  | zero =>
    have h1 : (weakHopfRepresentation r).rep 1 (single p q 1) σ τ =
        phys r (single p q 1) (σ 0) (τ 0) := weakHopfRep_one_apply _ _ _ _
    rw [h1, unitWordEntry_succ, unitWordEntry_succ, unitWordEntry_zero, unitWordEntry_zero]
    change single p q (1 : ℂ) (finProdFinEquiv.symm (σ 0)) (finProdFinEquiv.symm (τ 0)) = _
    generalize finProdFinEquiv.symm (σ 0) = s
    generalize finProdFinEquiv.symm (τ 0) = t
    rw [Matrix.single_apply, ← ite_and, ← ite_and, pow_zero, one_mul, ite_zero_mul_ite_zero,
      mul_one]
    exact if_congr (by simp only [Prod.ext_iff, @eq_comm _ p.1, @eq_comm _ p.2,
      @eq_comm _ q.1, @eq_comm _ q.2]) rfl rfl
  | succ n ih =>
    have hcoeff : ∀ x : BellPairAlgebra r,
        (weakHopfCoeff (weakHopfRepresentation r).phys.toLinearMap (Fin.tail σ)
          (Fin.tail τ)).ofConv x =
          (weakHopfRepresentation r).rep (n + 1) x (Fin.tail σ) (Fin.tail τ) := fun _ ↦ rfl
    have hdual : ∀ x : BellPairAlgebra r,
        (dualCoefficient (weakHopfRepresentation r).phys.toLinearMap (σ 0) (τ 0)).ofConv x =
          x (finProdFinEquiv.symm (σ 0)) (finProdFinEquiv.symm (τ 0)) := fun _ ↦ rfl
    rw [WeakHopfRepresentation.rep, weakHopfRep_succ_apply, comul_single, comulSingle]
    simp only [map_smul, map_sum, TensorProduct.map_tmul, LinearMap.mul'_apply, smul_eq_mul,
      hcoeff, hdual, ih]
    rw [unitWordEntry_succ r p σ, unitWordEntry_succ r q τ]
    generalize finProdFinEquiv.symm (σ 0) = s
    generalize finProdFinEquiv.symm (τ 0) = t
    rw [Finset.sum_eq_single (s.2, t.2)]
    · dsimp only
      by_cases h1 : s.1 = p.1
      · by_cases h2 : t.1 = q.1
        · rw [Matrix.single_apply, ite_eq_left ⟨Prod.ext h1.symm rfl, Prod.ext h2.symm rfl⟩,
            ite_eq_left h1, ite_eq_left h2, pow_succ]
          ring
        · rw [Matrix.single_apply, ite_eq_right fun h ↦ h2 (by
              have e := congrArg Prod.fst h.2
              exact e.symm), ite_eq_right h2]
          ring
      · rw [Matrix.single_apply, ite_eq_right fun h ↦ h1 (by
            have e := congrArg Prod.fst h.1
            exact e.symm), ite_eq_right h1]
        ring
    · intro c _ hc
      rw [Matrix.single_apply, ite_eq_right, zero_mul]
      rintro ⟨e1, e2⟩
      have e3 := congrArg Prod.snd e1
      have e4 := congrArg Prod.snd e2
      exact hc (Prod.ext e3 e4)
    · intro h
      exact absurd (Finset.mem_univ _) h

/-- The represented coproduct of a matrix unit is the rank-one matrix
\(r^{-n}\,|E_{\cdot}{}_p\rangle\langle E_{\cdot}{}_q|\) of word entries. -/
theorem rep_single_eq_vecMulVec (n : ℕ) (p q : Fin r × Fin r) :
    (weakHopfRepresentation r).rep (n + 1) (single p q 1) =
      (r : ℂ)⁻¹ ^ n • Matrix.vecMulVec (unitWordEntry r p) (unitWordEntry r q) := by
  ext σ τ
  rw [rep_single_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul, mul_assoc]

/-- The represented unit \(Q_{n+1}=\rho_{n+1}(1)\) as a sum of rank-one matrices. -/
theorem rep_one_eq_sum (n : ℕ) :
    (weakHopfRepresentation r).rep (n + 1) 1 =
      ∑ p : Fin r × Fin r,
        (r : ℂ)⁻¹ ^ n • Matrix.vecMulVec (unitWordEntry r p) (unitWordEntry r p) := by
  rw [show (1 : BellPairAlgebra r) = ∑ p, single p p 1 from Matrix.sum_single_one.symm,
    map_sum]
  exact Finset.sum_congr rfl fun p _ ↦ rep_single_eq_vecMulVec r n p p

/-- The matrix form of the Bell-pair average:
\(r^{-2}\sum_{p,q}\rho(e_{pq})M\rho(e_{qp})=r^{-2}\operatorname{tr}(QM)\,Q\). -/
private theorem sum_rep_single_mul_mul (n : ℕ)
    (M : Matrix (Fin (n + 1) → Fin (r * r)) (Fin (n + 1) → Fin (r * r)) ℂ) :
    ∑ p : Fin r × Fin r, ∑ q : Fin r × Fin r, ((r : ℂ)⁻¹ * (r : ℂ)⁻¹) •
        ((weakHopfRepresentation r).rep (n + 1) (single p q 1) * M *
          (weakHopfRepresentation r).rep (n + 1) (single q p 1)) =
      ((r : ℂ)⁻¹ * (r : ℂ)⁻¹ * ((weakHopfRepresentation r).rep (n + 1) 1 * M).trace) •
        (weakHopfRepresentation r).rep (n + 1) 1 := by
  have hV : ∀ p q, (weakHopfRepresentation r).rep (n + 1) (single p q 1) * M *
      (weakHopfRepresentation r).rep (n + 1) (single q p 1) =
        ((r : ℂ)⁻¹ ^ n * (r : ℂ)⁻¹ ^ n *
          ((unitWordEntry r q ᵥ* M) ⬝ᵥ unitWordEntry r q)) •
          Matrix.vecMulVec (unitWordEntry r p) (unitWordEntry r p) := by
    intro p q
    rw [rep_single_eq_vecMulVec, rep_single_eq_vecMulVec, Matrix.smul_mul, Matrix.smul_mul,
      Matrix.mul_smul, Matrix.vecMulVec_mul, Matrix.vecMulVec_mul_vecMulVec,
      Matrix.vecMulVec_smul, smul_smul, smul_smul]
  have hT : ((weakHopfRepresentation r).rep (n + 1) 1 * M).trace =
      (r : ℂ)⁻¹ ^ n * ∑ q, (unitWordEntry r q ᵥ* M) ⬝ᵥ unitWordEntry r q := by
    rw [rep_one_eq_sum, Finset.sum_mul, Matrix.trace_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ ↦ ?_
    rw [Matrix.smul_mul, Matrix.trace_smul, Matrix.vecMulVec_mul, Matrix.trace_vecMulVec,
      smul_eq_mul, dotProduct_comm]
  rw [hT, rep_one_eq_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  rw [smul_smul, Finset.mul_sum, Finset.mul_sum, Finset.sum_mul, Finset.sum_smul]
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  rw [hV, smul_smul]
  congr 1
  ring

/-- The weak-Hopf average of the Bell-pair algebra is
\(E_n(X)=r^{-2}\operatorname{tr}(Q_nX)\,Q_n\) at every positive length, with
\(Q_n=\rho_n(1)\). At two sites this is the displayed computation
\(E(X)=r^{-2}\operatorname{Tr}(QX)\,Q\) of
`docs/paper-gaps/glm23_wha_parent_completion.tex`, section "An elementary
fusion-compatible test". -/
theorem weakHopfAverage_eq_trace_smul {n : ℕ} (hn : 0 < n)
    (X : Module.End ℂ (EuclideanSpace ℂ (Fin n → Fin (r * r)))) :
    (weakHopfRepresentation r).weakHopfAverage n X =
      ((r : ℂ)⁻¹ * (r : ℂ)⁻¹ * LinearMap.trace ℂ _
          (Matrix.toEuclideanLin ((weakHopfRepresentation r).rep n 1) * X)) •
        Matrix.toEuclideanLin ((weakHopfRepresentation r).rep n 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨M, rfl⟩ := Matrix.toEuclideanLin.surjective X
  rw [weakHopfAverage_eq_sum_single, ← toEuclideanLin_mul, trace_toEuclideanLin]
  have key := congrArg (fun B ↦ Matrix.toEuclideanLin B) (sum_rep_single_mul_mul r m M)
  simp only [map_sum, map_smul, toEuclideanLin_mul] at key
  exact key

/-- The represented coproduct of a matrix unit moves a state of the Bell-pair
tensor to another one, with a boundary independent of the length:
\(\rho_n(e_{pq})\psi^n_Y=\psi^n_{Y_{q_2q_1}E_{p_2p_1}}\). -/
theorem rep_single_mulVec_mpvWithBoundary {n : ℕ} (hn : 0 < n) (p q : Fin r × Fin r)
    (Y : Matrix (Fin r) (Fin r) ℂ) :
    (weakHopfRepresentation r).rep n (single p q 1) *ᵥ
        MPSTensor.mpvWithBoundary (stateTensor r) Y =
      (MPSTensor.mpvWithBoundary (stateTensor r) (Y q.2 q.1 • single p.2 p.1 1) :
        (Fin n → Fin (r * r)) → ℂ) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hr : (r : ℂ) ^ m ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr (NeZero.ne r))
  funext σ
  simp only [Matrix.mulVec, dotProduct, rep_single_apply, mpvWithBoundary_stateTensor]
  simp only [Matrix.smul_mul, Matrix.trace_smul, Matrix.trace_single_mul, smul_eq_mul, one_mul]
  calc ∑ τ, (r : ℂ)⁻¹ ^ m * unitWordEntry r p σ * unitWordEntry r q τ *
          (((Real.sqrt r : ℝ) : ℂ)⁻¹ ^ (m + 1) *
            (Y * Kraus.evalWord (unitTensor r) (List.ofFn τ)).trace)
      = (r : ℂ)⁻¹ ^ m * unitWordEntry r p σ * ((Real.sqrt r : ℝ) : ℂ)⁻¹ ^ (m + 1) *
          ∑ τ, unitWordEntry r q τ *
            (Y * Kraus.evalWord (unitTensor r) (List.ofFn τ)).trace := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun τ _ ↦ by ring
    _ = _ := by
        have hinv : (r : ℂ)⁻¹ ^ m * (r : ℂ) ^ m = 1 := by rw [inv_pow, inv_mul_cancel₀ hr]
        rw [sum_unitWordEntry_mul_trace,
          show unitWordEntry r p σ = Kraus.evalWord (unitTensor r) (List.ofFn σ) p.1 p.2 from rfl]
        linear_combination (((Real.sqrt r : ℝ) : ℂ)⁻¹ ^ (m + 1) * Y q.2 q.1 *
          Kraus.evalWord (unitTensor r) (List.ofFn σ) p.1 p.2) * hinv

/-- The Bell-pair state tensor is compatible with the Bell-pair operator tensor,
with one output boundary for all positive lengths, in the sense of GLM23
`eq:compatible`, as asserted in
`docs/paper-gaps/glm23_wha_parent_completion.tex`, section "An elementary
fusion-compatible test". -/
theorem isBoundaryCompatible :
    IsBoundaryCompatible (weakHopfRepresentation r).tensor (stateTensor r) := by
  intro X Y
  obtain ⟨x, hx⟩ := exists_weakHopfRep_eq_mpoWithBoundary
    (weakHopfRepresentation r).phys.toLinearMap (weakHopfRepresentation r).virt X
  refine ⟨∑ p, ∑ q, (x p q * Y q.2 q.1) • single p.2 p.1 1, fun n hn ↦ ?_⟩
  have hxn : mpoWithBoundary (weakHopfRepresentation r).tensor X n =
      (weakHopfRepresentation r).rep n x := hx n
  rw [hxn]
  conv_lhs => rw [Matrix.matrix_eq_sum_single x]
  simp only [map_sum, Matrix.sum_mulVec, fun p q ↦ single_eq_smul_single r p q (x p q),
    map_smul, Matrix.smul_mulVec, rep_single_mulVec_mpvWithBoundary r hn]
  simp only [MPSTensor.mpvWithBoundary_eq_groundSpaceMap, map_sum, map_smul, smul_smul]

/-- The Bell-pair state tensor is injective at one site: its letters are
nonzero multiples of the matrix units. -/
theorem isNBlkInjective_stateTensor : Kraus.IsNBlkInjective (stateTensor r) 1 := by
  have hc : ((Real.sqrt r : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr (Nat.cast_pos.mpr (NeZero.pos r)))
  refine Submodule.eq_top_of_forall_single_mem _ fun i j ↦ ?_
  have h : single i j (1 : ℂ) = ((Real.sqrt r : ℝ) : ℂ) •
      Kraus.evalWord (stateTensor r) (List.ofFn fun _ : Fin 1 ↦ finProdFinEquiv (i, j)) := by
    rw [evalWord_stateTensor, List.length_ofFn, pow_one, smul_smul, mul_inv_cancel₀ hc,
      one_smul, List.ofFn_succ, List.ofFn_zero, Kraus.evalWord_cons, Kraus.evalWord_nil,
      Matrix.mul_one]
    dsimp only [unitTensor]
    rw [Equiv.symm_apply_apply]
  rw [h]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)

/-- Each word-entry vector is a state of the Bell-pair tensor. -/
theorem unitWordEntry_mem_groundSpace (n : ℕ) (p : Fin r × Fin r) :
    (unitWordEntry r p : (Fin n → Fin (r * r)) → ℂ) ∈
      MPSTensor.groundSpace (stateTensor r) n := by
  have hc : ((Real.sqrt r : ℝ) : ℂ)⁻¹ ^ n ≠ 0 := pow_ne_zero _ (inv_ne_zero
    (Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr (Nat.cast_pos.mpr (NeZero.pos r)))))
  refine LinearMap.mem_range.mpr
    ⟨(((Real.sqrt r : ℝ) : ℂ)⁻¹ ^ n)⁻¹ • single p.2 p.1 1, funext fun σ ↦ ?_⟩
  rw [MPSTensor.groundSpaceMap_apply, evalWord_stateTensor, List.length_ofFn, Matrix.smul_mul,
    Matrix.mul_smul, smul_smul, Matrix.trace_smul, mul_inv_cancel₀ hc, one_smul,
    Matrix.trace_mul_single, MulOpposite.op_one, one_smul]
  rfl

attribute [local instance] MPSTensor.groundSpaceES_hasOrthogonalProjection

/-- For the Bell-pair state tensor the support projection is the represented
unit, \(P_n=Q_n\), at every positive length; at two sites
\(P=Q=I_K\otimes|\Phi\rangle\langle\Phi|\otimes I_K\), as in
`docs/paper-gaps/glm23_wha_parent_completion.tex`. -/
theorem starProjection_groundSpaceES_stateTensor {n : ℕ} (hn : 0 < n) :
    (MPSTensor.groundSpaceES (stateTensor r) n).starProjection.toLinearMap =
      Matrix.toEuclideanLin ((weakHopfRepresentation r).rep n 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hQP := (weakHopfRepresentation r).toEuclideanLin_rep_one_comp_starProjection
    (isBoundaryCompatible r) (isNBlkInjective_stateTensor r) hn
  have hPQ : (MPSTensor.groundSpaceES (stateTensor r) (m + 1)).starProjection.toLinearMap ∘ₗ
      Matrix.toEuclideanLin ((weakHopfRepresentation r).rep (m + 1) 1) =
        Matrix.toEuclideanLin ((weakHopfRepresentation r).rep (m + 1) 1) := by
    refine LinearMap.ext fun v ↦ Submodule.starProjection_eq_self_iff.mpr ?_
    rw [MPSTensor.mem_groundSpaceES_iff]
    change (weakHopfRepresentation r).rep (m + 1) 1 *ᵥ
      (WithLp.linearEquiv 2 ℂ (MPSTensor.NSiteSpace (r * r) (m + 1))) v ∈ _
    rw [rep_one_eq_sum, Matrix.sum_mulVec]
    refine Submodule.sum_mem _ fun p _ ↦ ?_
    rw [Matrix.smul_mulVec, Matrix.vecMulVec_mulVec, op_smul_eq_smul]
    exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (unitWordEntry_mem_groundSpace r _ p))
  have hQ : LinearMap.adjoint (Matrix.toEuclideanLin ((weakHopfRepresentation r).rep (m + 1) 1)) =
      Matrix.toEuclideanLin ((weakHopfRepresentation r).rep (m + 1) 1) := by
    rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
      ← (weakHopfRepresentation r).rep_star, star_one]
  have hP := (Submodule.starProjection_isSymmetric
    (MPSTensor.groundSpaceES (stateTensor r) (m + 1))).adjoint_eq
  rw [← hP, ← hQP, LinearMap.adjoint_comp, hP, hQ, hPQ]

/-- The weak-Hopf average fixes the support projection of the Bell-pair state,
\(E_n(P_n)=P_n\) at every positive length: an instance of GLM23 Appendix B,
lines 2463--2466. -/
theorem weakHopfAverage_starProjection_stateTensor {n : ℕ} (hn : 0 < n) :
    (weakHopfRepresentation r).weakHopfAverage n
        (MPSTensor.groundSpaceES (stateTensor r) n).starProjection.toLinearMap =
      (MPSTensor.groundSpaceES (stateTensor r) n).starProjection.toLinearMap :=
  (weakHopfRepresentation r).weakHopfAverage_starProjection (isBoundaryCompatible r)
    (isNBlkInjective_stateTensor r) hn

/-- The uncompleted average of the canonical parent term of the Bell-pair state
vanishes, \(E_n(I-P_n)=Q_n-P_n=0\), at every positive length; see
`docs/paper-gaps/glm23_wha_parent_completion.tex`, section "An elementary
fusion-compatible test". -/
theorem weakHopfAverage_parentInteractionES_stateTensor {n : ℕ} (hn : 0 < n) :
    (weakHopfRepresentation r).weakHopfAverage n
      (MPSTensor.parentInteractionES (stateTensor r) n) = 0 := by
  rw [(weakHopfRepresentation r).weakHopfAverage_parentInteractionES (isBoundaryCompatible r)
    (isNBlkInjective_stateTensor r) hn, starProjection_groundSpaceES_stateTensor r hn, sub_self]

omit [NeZero r] in
/-- The canonical parent term \(I-P_n\) of the Bell-pair state is nonzero for
\(r\ge2\) and \(n\ge2\), although its uncompleted average vanishes; it equals the
ambient complement \(I-E_n(P_n)\). -/
theorem parentInteractionES_stateTensor_ne_zero (hr : 2 ≤ r) {n : ℕ} (hn : 2 ≤ n) :
    MPSTensor.parentInteractionES (stateTensor r) n ≠ 0 := by
  refine MPSTensor.parentInteractionES_ne_zero _ n ?_
  have h1 : r < r * r := by nlinarith
  exact lt_of_lt_of_le (Nat.pow_lt_pow_left h1 two_ne_zero)
    (Nat.pow_le_pow_right (Nat.mul_pos (by omega) (by omega)) hn)

end NeZero

end MPOTensor.BellPairWeakHopf
