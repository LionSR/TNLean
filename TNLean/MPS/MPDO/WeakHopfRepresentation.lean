/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.DualRepresentationAdjointBoundary

/-!
# Weak-Hopf representations realized by boundary operators

Let `H` be a complex algebra with a comultiplication `Δ`, a physical
representation `φ`, and a faithful representation `ψ` of the convolution dual
on the bond space. The operator tensor `T i j = ψ (fun x ↦ φ x i j)` realizes
the represented iterated coproduct
\[
  \rho_N=(\phi\otimes\cdots\otimes\phi)\circ\Delta^{(N-1)},\qquad
  \rho_N(x)_{\sigma\tau}=(f_{\sigma_1\tau_1}\cdots f_{\sigma_N\tau_N})(x),
\]
where \(f_{ij}(x)=\phi(x)_{ij}\) and the product is convolution. Every
element of `H` is represented by one boundary matrix at all chain lengths,
and, for finite-dimensional `H`, every boundary operator is of this form.

When `Δ` is multiplicative and `φ` is an algebra homomorphism, each
\(\rho_N\) with \(N>0\) is multiplicative. It need not be unital: the empty
chain gives the counit, and \(Q_N=\rho_N(1)\) is the identity at \(N=1\)
only. A canonical integral \(\Omega\) together with the linear map \(T\) of
GLM23 satisfying
\(\sum\Delta(\Omega_{(1)})\Delta(T(\Omega_{(2)}))=\Delta(1)\) therefore
gives the boundary normalization
\(\sum\rho_N(\Omega_{(1)})\rho_N(T(\Omega_{(2)}))=Q_N\) at every positive
length.

The structure `WeakHopfRepresentation` records exactly the weak-Hopf axioms
used here: multiplicativity and star compatibility of `Δ`, the physical
star representation, the faithful dual representation, and the integral
identity; coassociativity and the counit laws come from the coalgebra
structure. The remaining axioms of a C*-weak Hopf algebra (the weak unit and
weak counit identities, the antipode laws, positivity of the integral) are
not needed and are not recorded.

## References

* Garre-Rubio--Lootens--Molnár, arXiv:2203.12563v3, Section 5,
  lines 1236--1320; Appendix B, lines 2463--2466.
* Molnár et al., arXiv:2204.05940v1, Section 4, Proposition 5.4, and
  Section 6.
-/

open scoped Matrix TensorProduct
open WithConv

noncomputable section

namespace Coalgebra

/-- The comultiplication of a coalgebra is injective: applying the counit to
the first tensor factor recovers the element. -/
theorem comul_injective {R A : Type*} [CommSemiring R] [AddCommMonoid A] [Module R A]
    [Coalgebra R A] : Function.Injective (comul (R := R) (A := A)) := by
  intro x y h
  have key : ∀ z : A, TensorProduct.lid R A ((counit (R := R) (A := A)).rTensor A (comul z)) = z :=
    fun z ↦ by simp
  rw [← key x, ← key y, h]

end Coalgebra

namespace MPOTensor

variable {H : Type*} [Ring H] [Algebra ℂ H] [Coalgebra ℂ H]
variable {d D : ℕ}

/-! ### The represented iterated coproduct -/

/-- The ordered convolution product of physical coefficients, as a family of
functionals indexed by pairs of configurations. -/
def weakHopfCoeff (φ : H →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ) {N : ℕ}
    (σ τ : Fin N → Fin d) : WithConv (H →ₗ[ℂ] ℂ) :=
  (List.ofFn fun k ↦ dualCoefficient φ (σ k) (τ k)).prod

/-- The represented iterated coproduct
\(\rho_N=(\phi\otimes\cdots\otimes\phi)\circ\Delta^{(N-1)}\) on `N` sites.
Its entries are the ordered convolution products of physical coefficients;
at `N = 2` this is GLM23's \(\rho=(\phi\otimes\phi)\circ\Delta\),
arXiv:2203.12563v3, lines 2463--2466. -/
def weakHopfRep (φ : H →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ) (N : ℕ) :
    H →ₗ[ℂ] Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ where
  toFun x := Matrix.of fun σ τ ↦ (weakHopfCoeff φ σ τ).ofConv x
  map_add' x y := by ext σ τ; simp
  map_smul' c x := by ext σ τ; simp

/-- Entries of the represented coproduct are coefficient products. -/
theorem weakHopfRep_apply (φ : H →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ) {N : ℕ} (x : H)
    (σ τ : Fin N → Fin d) :
    weakHopfRep φ N x σ τ = (weakHopfCoeff φ σ τ).ofConv x := rfl

/-- At one site the represented coproduct is the physical representation. -/
theorem weakHopfRep_one_apply (φ : H →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ) (x : H)
    (σ τ : Fin 1 → Fin d) :
    weakHopfRep φ 1 x σ τ = φ x (σ 0) (τ 0) := by
  simp [weakHopfRep_apply, weakHopfCoeff, dualCoefficient]

/-- One more site splits off the first physical coefficient through the
comultiplication. -/
theorem weakHopfRep_succ_apply (φ : H →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ) {N : ℕ}
    (x : H) (σ τ : Fin (N + 1) → Fin d) :
    weakHopfRep φ (N + 1) x σ τ =
      LinearMap.mul' ℂ ℂ (TensorProduct.map (dualCoefficient φ (σ 0) (τ 0)).ofConv
        (weakHopfCoeff φ (Fin.tail σ) (Fin.tail τ)).ofConv (Coalgebra.comul x)) := by
  simp only [weakHopfRep_apply, weakHopfCoeff, List.ofFn_succ, List.prod_cons]
  rfl

omit [Coalgebra ℂ H] in
/-- Convolution of two matrix-coefficient families is again a family of
matrix coefficients, once the comultiplication is multiplicative. This is
the inductive step of the multiplicativity of the represented coproduct. -/
private theorem mul'_map_mul_eq_sum {ι κ : Type*} [Fintype ι] [Fintype κ]
    (F : ι → ι → H →ₗ[ℂ] ℂ) (G : κ → κ → H →ₗ[ℂ] ℂ)
    (hF : ∀ s t x y, F s t (x * y) = ∑ u, F s u x * F u t y)
    (hG : ∀ s t x y, G s t (x * y) = ∑ u, G s u x * G u t y)
    (s t : ι) (σ τ : κ) (p q : H ⊗[ℂ] H) :
    LinearMap.mul' ℂ ℂ (TensorProduct.map (F s t) (G σ τ) (p * q)) =
      ∑ u, ∑ υ, LinearMap.mul' ℂ ℂ (TensorProduct.map (F s u) (G σ υ) p) *
        LinearMap.mul' ℂ ℂ (TensorProduct.map (F u t) (G υ τ) q) := by
  induction p using TensorProduct.inductionOn with
  | add p p' hp hp' => simp only [add_mul, map_add, hp, hp', Finset.sum_add_distrib]
  | tmul a b =>
    induction q using TensorProduct.inductionOn with
    | add q q' hq hq' => simp only [mul_add, map_add, hq, hq', Finset.sum_add_distrib]
    | tmul a' b' =>
      simp only [Algebra.TensorProduct.tmul_mul_tmul, TensorProduct.map_tmul,
        LinearMap.mul'_apply, hF, hG, Finset.sum_mul_sum]
      apply Finset.sum_congr rfl
      intro u _
      apply Finset.sum_congr rfl
      intro υ _
      ring

/-- The represented coproduct is multiplicative at every positive length.
This uses multiplicativity of the comultiplication and of the physical
representation, as for the C*-weak-Hopf representations of
arXiv:2204.05940v1, Section 4. It is not unital in general. -/
theorem weakHopfRep_mul
    (hmul : ∀ x y : H, Coalgebra.comul (R := ℂ) (x * y) =
      Coalgebra.comul x * Coalgebra.comul y)
    (φ : H →ₐ[ℂ] Matrix (Fin d) (Fin d) ℂ) {N : ℕ} (hN : 0 < N) (x y : H) :
    weakHopfRep φ.toLinearMap N (x * y) =
      weakHopfRep φ.toLinearMap N x * weakHopfRep φ.toLinearMap N y := by
  obtain ⟨N, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN.ne'
  clear hN
  have hφ : ∀ (s t : Fin d) (x y : H),
      (dualCoefficient φ.toLinearMap s t).ofConv (x * y) =
        ∑ u, (dualCoefficient φ.toLinearMap s u).ofConv x *
          (dualCoefficient φ.toLinearMap u t).ofConv y := by
    intro s t x y
    change φ (x * y) s t = ∑ u, φ x s u * φ y u t
    rw [map_mul, Matrix.mul_apply]
  induction N generalizing x y with
  | zero =>
    ext σ τ
    rw [Matrix.mul_apply, weakHopfRep_one_apply, AlgHom.toLinearMap_apply, map_mul,
      Matrix.mul_apply, ← (Equiv.funUnique (Fin 1) (Fin d)).symm.sum_comp]
    simp [weakHopfRep_one_apply]
  | succ N ih =>
    have hG : ∀ (σ τ : Fin (N + 1) → Fin d) (x y : H),
        (weakHopfCoeff φ.toLinearMap σ τ).ofConv (x * y) =
          ∑ υ, (weakHopfCoeff φ.toLinearMap σ υ).ofConv x *
            (weakHopfCoeff φ.toLinearMap υ τ).ofConv y := by
      intro σ τ x y
      have := congrArg (fun M ↦ M σ τ) (ih x y)
      simpa only [weakHopfRep_apply, Matrix.mul_apply] using this
    ext σ τ
    rw [weakHopfRep_succ_apply, hmul,
      mul'_map_mul_eq_sum _ _ hφ hG, Matrix.mul_apply,
      ← (Fin.consEquiv fun _ ↦ Fin d).sum_comp, Fintype.sum_prod_type]
    simp only [Fin.consEquiv_apply, weakHopfRep_succ_apply, Fin.cons_zero, Fin.tail_def,
      Fin.cons_succ]

/-- The physical representation is unital, so the represented coproduct is the
identity at one site. At other positive lengths \(\rho_N(1)\) is the
projection \(Q_N\), which need not be the identity. -/
theorem weakHopfRep_one_one (φ : H →ₐ[ℂ] Matrix (Fin d) (Fin d) ℂ) :
    weakHopfRep φ.toLinearMap 1 1 = 1 := by
  ext σ τ
  rw [weakHopfRep_one_apply]
  simp only [AlgHom.toLinearMap_apply, map_one, Matrix.one_apply]
  congr 1
  exact propext ⟨fun h ↦ funext fun k ↦ by rwa [Fin.fin_one_eq_zero k],
    fun h ↦ congrFun h 0⟩

/-! ### Boundary realization -/

/-- A boundary whose trace pairing evaluates dual elements at `x` realizes
\(\rho_N(x)\) at every length, including zero. Source: arXiv:2204.05940v1,
Section 4 and Proposition 5.4. -/
theorem mpoWithBoundary_ofDualRepresentation_eq_weakHopfRep
    (φ : H →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ)
    (ψ : WithConv (H →ₗ[ℂ] ℂ) →ₐ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    {X : Matrix (Fin D) (Fin D) ℂ} {x : H}
    (hX : ∀ f : WithConv (H →ₗ[ℂ] ℂ), Matrix.trace (X * ψ f) = f.ofConv x) (N : ℕ) :
    mpoWithBoundary (ofDualRepresentation φ ψ) X N = weakHopfRep φ N x := by
  ext σ τ
  change Matrix.trace (X * evalWord (ofDualRepresentation φ ψ) (List.ofFn σ) (List.ofFn τ)) = _
  rw [evalWord_ofDualRepresentation, hX]
  rfl

/-- A faithful dual representation supplies, for each element `x`, one bond
matrix whose trace pairing is evaluation at `x`. -/
theorem exists_trace_mul_eq_ofConv_apply
    (ψ : WithConv (H →ₗ[ℂ] ℂ) →ₐ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (hψ : Function.Injective ψ) (x : H) :
    ∃ X : Matrix (Fin D) (Fin D) ℂ,
      ∀ f : WithConv (H →ₗ[ℂ] ℂ), Matrix.trace (X * ψ f) = f.ofConv x := by
  let ℓ : WithConv (H →ₗ[ℂ] ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun f ↦ f.ofConv x
      map_add' := by intro f g; simp
      map_smul' := by intro c f; simp }
  obtain ⟨θ, hθ⟩ := LinearMap.dualMap_surjective_of_injective
    (f := ψ.toLinearMap) hψ ℓ
  let X := ((Matrix.traceBilinForm (Fin D)).toDual Matrix.traceBilinForm_nondegenerate).symm θ
  have hX (M : Matrix (Fin D) (Fin D) ℂ) : θ M = Matrix.trace (X * M) := by
    rw [← Matrix.traceBilinForm_apply, LinearMap.BilinForm.apply_toDual_symm_apply]
  exact ⟨X, fun f ↦ (hX (ψ f)).symm.trans (LinearMap.congr_fun hθ f)⟩

/-- Every element of `H` is represented by one boundary at all lengths:
\(\rho_N(x)=O^N_{T,X}\). -/
theorem exists_mpoWithBoundary_eq_weakHopfRep
    (φ : H →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ)
    (ψ : WithConv (H →ₗ[ℂ] ℂ) →ₐ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (hψ : Function.Injective ψ) (x : H) :
    ∃ X : Matrix (Fin D) (Fin D) ℂ, ∀ N : ℕ,
      mpoWithBoundary (ofDualRepresentation φ ψ) X N = weakHopfRep φ N x := by
  obtain ⟨X, hX⟩ := exists_trace_mul_eq_ofConv_apply ψ hψ x
  exact ⟨X, mpoWithBoundary_ofDualRepresentation_eq_weakHopfRep φ ψ hX⟩

/-- For finite-dimensional `H`, every boundary operator is a represented
element, with one element for all lengths. Together with
`exists_mpoWithBoundary_eq_weakHopfRep`, the arbitrary-boundary range at
each length is exactly \(\rho_N(H)\). -/
theorem exists_weakHopfRep_eq_mpoWithBoundary [FiniteDimensional ℂ H]
    (φ : H →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ)
    (ψ : WithConv (H →ₗ[ℂ] ℂ) →ₐ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (X : Matrix (Fin D) (Fin D) ℂ) :
    ∃ x : H, ∀ N : ℕ,
      mpoWithBoundary (ofDualRepresentation φ ψ) X N = weakHopfRep φ N x := by
  let ℓ : Module.Dual ℂ (Module.Dual ℂ H) :=
    { toFun := fun f ↦ Matrix.trace (X * ψ (toConv f))
      map_add' := by intro f g; simp [Matrix.mul_add]
      map_smul' := by intro c f; simp [Matrix.trace_smul] }
  refine ⟨(Module.evalEquiv ℂ H).symm ℓ,
    mpoWithBoundary_ofDualRepresentation_eq_weakHopfRep φ ψ fun f ↦ ?_⟩
  rw [Module.apply_evalEquiv_symm_apply]
  rfl

/-! ### The weak-Hopf data -/

/-- The data of a complex weak-Hopf MPO representation with a canonical
integral, recording only the axioms used by the averaging of GLM23
Appendix B.

* `phys` is the physical star representation \(\phi\);
* `virt` is a faithful representation of the convolution dual on the bond
  space, which determines the operator tensor (arXiv:2204.05940v1,
  Proposition 5.4);
* the comultiplication is multiplicative and star preserving;
* `integral` is the canonical integral \(\Omega\) and `pullThrough` the
  linear map \(T\) of GLM23, normalized by the identity
  \(\sum\Delta(\Omega_{(1)})\Delta(T(\Omega_{(2)}))=\Delta(1)\) stated in
  arXiv:2203.12563v3, Appendix B, lines 2463--2466.

The weak unit and weak counit identities, the antipode axioms, and the
positivity of \(\Omega\) are not recorded, since no argument below uses
them. -/
structure WeakHopfRepresentation (H : Type*) [Ring H] [Algebra ℂ H] [Coalgebra ℂ H]
    [StarRing H] [StarModule ℂ H] (d D : ℕ) where
  /-- The physical representation \(\phi\). -/
  phys : H →ₐ[ℂ] Matrix (Fin d) (Fin d) ℂ
  /-- The physical representation preserves the involution. -/
  phys_star : ∀ x, phys (star x) = (phys x)ᴴ
  /-- The faithful representation of the convolution dual on the bond space. -/
  virt : WithConv (H →ₗ[ℂ] ℂ) →ₐ[ℂ] Matrix (Fin D) (Fin D) ℂ
  /-- Faithfulness of the bond representation. -/
  virt_injective : Function.Injective virt
  /-- The comultiplication is multiplicative. -/
  comul_mul : ∀ x y : H, Coalgebra.comul (R := ℂ) (x * y) =
    Coalgebra.comul x * Coalgebra.comul y
  /-- The comultiplication preserves the involution. -/
  comul_star : ∀ x : H, Coalgebra.comul (R := ℂ) (star x) = star (Coalgebra.comul x)
  /-- The linear map \(T\) used with the canonical integral. -/
  pullThrough : H →ₗ[ℂ] H
  /-- The canonical integral \(\Omega\). -/
  integral : H
  /-- GLM23 Appendix B: \(\sum\Delta(\Omega_{(1)})\Delta(T(\Omega_{(2)}))=\Delta(1)\). -/
  mul'_map_comul_integral :
    LinearMap.mul' ℂ (H ⊗[ℂ] H) (TensorProduct.map Coalgebra.comul
      (Coalgebra.comul ∘ₗ pullThrough) (Coalgebra.comul integral)) = Coalgebra.comul 1

namespace WeakHopfRepresentation

variable [StarRing H] [StarModule ℂ H] (W : WeakHopfRepresentation H d D)

/-- The operator tensor of the representation. -/
def tensor : MPOTensor d D := ofDualRepresentation W.phys.toLinearMap W.virt

/-- The represented iterated coproduct on `N` sites. -/
def rep (N : ℕ) : H →ₗ[ℂ] Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ :=
  weakHopfRep W.phys.toLinearMap N

/-- A chosen boundary realizing each element at every length. -/
def boundary (x : H) : Matrix (Fin D) (Fin D) ℂ :=
  (exists_mpoWithBoundary_eq_weakHopfRep W.phys.toLinearMap W.virt W.virt_injective x).choose

/-- The chosen boundary of `x` realizes \(\rho_N(x)\) at every length. -/
@[simp] theorem mpoWithBoundary_boundary (x : H) (N : ℕ) :
    mpoWithBoundary W.tensor (W.boundary x) N = W.rep N x :=
  (exists_mpoWithBoundary_eq_weakHopfRep W.phys.toLinearMap W.virt
    W.virt_injective x).choose_spec N

/-- The represented coproduct is multiplicative at positive lengths. -/
theorem rep_mul {N : ℕ} (hN : 0 < N) (x y : H) : W.rep N (x * y) = W.rep N x * W.rep N y :=
  weakHopfRep_mul W.comul_mul W.phys hN x y

/-- At one site the represented unit is the identity. -/
theorem rep_one_length_one : W.rep 1 1 = 1 := weakHopfRep_one_one W.phys

/-- The arbitrary-boundary range is closed under adjoints, with one adjoint
boundary for all lengths. This is the boundary adjoint closure needed in
GLM23 Appendix B, derived from the star compatibility of the
comultiplication and of the physical representation. -/
theorem exists_conjTranspose_mpoWithBoundary_eq (X : Matrix (Fin D) (Fin D) ℂ) :
    ∃ Y : Matrix (Fin D) (Fin D) ℂ, ∀ N : ℕ,
      (mpoWithBoundary W.tensor X N)ᴴ = mpoWithBoundary W.tensor Y N :=
  exists_adjointBoundary_of_dualRepresentation W.comul_star W.phys.toLinearMap
    W.phys_star W.virt W.virt_injective X

/-- The comultiplication intertwines multiplication of tensor factors. -/
private theorem comul_mul'_map (p : H ⊗[ℂ] H) :
    Coalgebra.comul (R := ℂ) (LinearMap.mul' ℂ H (TensorProduct.map LinearMap.id
      W.pullThrough p)) =
      LinearMap.mul' ℂ (H ⊗[ℂ] H) (TensorProduct.map Coalgebra.comul
        (Coalgebra.comul ∘ₗ W.pullThrough) p) := by
  induction p using TensorProduct.inductionOn with
  | add p q hp hq => simp only [map_add, hp, hq]
  | tmul a b => simp [W.comul_mul]

/-- The integral identity in `H`: \(\sum\Omega_{(1)}T(\Omega_{(2)})=1\).
It follows from the normalization of GLM23 Appendix B because the
comultiplication is multiplicative and injective. -/
theorem mul'_map_integral :
    LinearMap.mul' ℂ H (TensorProduct.map LinearMap.id W.pullThrough
      (Coalgebra.comul W.integral)) = 1 := by
  apply Coalgebra.comul_injective (R := ℂ)
  rw [comul_mul'_map, W.mul'_map_comul_integral]

/-- For any Sweedler representation of \(\Delta(\Omega)\), the represented
integral is normalized at every positive length:
\(\sum\rho_N(\Omega_{(1)})\rho_N(T(\Omega_{(2)}))=\rho_N(1)=Q_N\).
This is the normalization of GLM23 Appendix B, lines 2463--2466. -/
theorem sum_rep_mul_rep_pullThrough {ι : Type*} (𝓡 : Coalgebra.Repr ℂ W.integral ι)
    {N : ℕ} (hN : 0 < N) :
    ∑ i ∈ 𝓡.index, W.rep N (𝓡.left i) * W.rep N (W.pullThrough (𝓡.right i)) =
      W.rep N 1 := by
  rw [← W.mul'_map_integral, ← 𝓡.eq]
  simp only [map_sum, TensorProduct.map_tmul, LinearMap.id_apply, LinearMap.mul'_apply,
    W.rep_mul hN]

end WeakHopfRepresentation

end MPOTensor
