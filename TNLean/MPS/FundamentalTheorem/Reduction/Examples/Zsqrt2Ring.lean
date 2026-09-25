/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import Mathlib.NumberTheory.Zsqrtd.ToReal
import TNLean.Algebra.MatrixSingleSpan
import TNLean.MPS.FundamentalTheorem.Reduction.Examples.ExplicitGauge

/-!
# Exact arithmetic for the Ising twist: matrices over `ℤ[√2]` and their complex images

**Source.** Construction of this development. The ring is dictated by the Ising data of
Bultinck, Mariën, Williamson, Sahinoglu, Haegeman and Verstraete 2017 (arXiv:1511.08090),
Appendix D.2.1, `References/1511.08090/AnyonsPEPS.tex` lines 1312–1323: the quantum dimension
`d_σ = √2` and the F-symbols `±1/√2`, `-1` and `1`. After a global rescaling every entry of the
`σ` strand of the Ising topological-symmetry tensors lies in `{0, ±1, ±√2}`.

**Formalized here.** Mathlib models the quadratic ring as `ℤ√2`, with decidable equality, so an
identity between explicit matrices over `ℤ√2` is decided exactly as an identity between integer
matrices is. This file records the embedding `ℤ√2 → ℂ` sending `√2` to the positive real square
root of two, the entrywise image of a matrix along it, the compatibility of that image with
products and matrix units, its bond-space product and action, and the normality criterion of
`P6Compression.isNormal_of_single_eq_smul` transported to this ring. The compatibilities are the
instances at this embedding of the general statements of `TNLean.Algebra.ComplexOfRing` and of
`Examples/RingEmbedding.lean`. The two-object Ising example
(`Examples/IsingWeightedTwist.lean`) is built on it.

## Main definitions

* `zsqrt2ToComplex`: the embedding `ℤ√2 →+* ℂ`, `√2 ↦ √2`.
* `MPSTensor.complexOfZsqrt2`: the entrywise image of a matrix over `ℤ√2`.
* `MPSTensor.mulZsqrt2Tensor`, `MPSTensor.actZsqrt2Tensor`: the bond-space product of two
  tensors over `ℤ√2`, and the action of one on a state tensor.

## Main results

* `zsqrt2ToComplex_injective`: the embedding is injective, because two is not a square.
* `MPSTensor.complexOfZsqrt2_mul`: the entrywise image is multiplicative.
* `MPSTensor.isNormal_of_single_eq_smul_zsqrt2`: a tensor over `ℤ√2` whose letters realise
  every matrix unit up to a nonzero factor is normal at blocking length one.

## References

- [arXiv:1511.08090](https://arxiv.org/abs/1511.08090) -- N. Bultinck, M. Mariën,
  D. J. Williamson, M. B. Sahinoglu, J. Haegeman, F. Verstraete, *Anyons and matrix product
  operator algebras*
-/

open scoped Matrix Kronecker

/-- Two is not the square of an integer. -/
theorem two_ne_int_mul_self (n : ℤ) : (2 : ℤ) ≠ n * n := by
  intro hn
  refine Nat.not_exists_sq (m := 1) (n := 2) (by norm_num) (by norm_num) ⟨n.natAbs, ?_⟩
  exact_mod_cast (Int.natAbs_mul_self (a := n)).trans hn.symm

/-- The embedding of `ℤ√2` into the complex numbers sending `√2` to the positive real square
root of two. -/
noncomputable def zsqrt2ToComplex : ℤ√2 →+* ℂ :=
  Complex.ofRealHom.comp (Zsqrtd.toReal (by norm_num))

theorem zsqrt2ToComplex_injective : Function.Injective zsqrt2ToComplex :=
  fun _ _ h => Zsqrtd.toReal_injective _ two_ne_int_mul_self (Complex.ofReal_injective h)

theorem zsqrt2ToComplex_ne_zero {x : ℤ√2} (hx : x ≠ 0) : zsqrt2ToComplex x ≠ 0 :=
  fun h => hx (zsqrt2ToComplex_injective (h.trans (map_zero _).symm))

@[simp] theorem zsqrt2ToComplex_sqrtd : zsqrt2ToComplex Zsqrtd.sqrtd = (Real.sqrt 2 : ℂ) := by
  simp [zsqrt2ToComplex, Zsqrtd.sqrtd]

namespace MPSTensor

/-- The entrywise image of a matrix over `ℤ√2` in the complex matrices. -/
noncomputable abbrev complexOfZsqrt2 {m n : Type*} (X : Matrix m n (ℤ√2)) : Matrix m n ℂ :=
  complexOfRing zsqrt2ToComplex X

@[simp] theorem complexOfZsqrt2_apply {m n : Type*} (X : Matrix m n (ℤ√2)) (i : m) (j : n) :
    complexOfZsqrt2 X i j = zsqrt2ToComplex (X i j) := rfl

theorem complexOfZsqrt2_mul {m n o : Type*} [Fintype n] (X : Matrix m n (ℤ√2))
    (Y : Matrix n o (ℤ√2)) :
    complexOfZsqrt2 (X * Y) = complexOfZsqrt2 X * complexOfZsqrt2 Y :=
  complexOfRing_mul zsqrt2ToComplex X Y

theorem complexOfZsqrt2_one {n : Type*} [DecidableEq n] :
    complexOfZsqrt2 (1 : Matrix n n (ℤ√2)) = 1 :=
  complexOfRing_one zsqrt2ToComplex

theorem complexOfZsqrt2_single {m n : Type*} [DecidableEq m] [DecidableEq n] (i : m) (j : n) :
    complexOfZsqrt2 (Matrix.single i j (1 : ℤ√2)) = Matrix.single i j (1 : ℂ) :=
  complexOfRing_single zsqrt2ToComplex i j

theorem complexOfZsqrt2_smul {m n : Type*} (c : ℤ√2) (X : Matrix m n (ℤ√2)) :
    complexOfZsqrt2 (c • X) = zsqrt2ToComplex c • complexOfZsqrt2 X :=
  complexOfRing_smul zsqrt2ToComplex c X

theorem complexOfZsqrt2_submatrix {m n m' n' : Type*} (X : Matrix m n (ℤ√2)) (f : m' → m)
    (g : n' → n) : complexOfZsqrt2 (X.submatrix f g) = (complexOfZsqrt2 X).submatrix f g :=
  complexOfRing_submatrix zsqrt2ToComplex X f g

variable {d D D₁ D₂ : ℕ}

/-- The bond-space product of two tensors over `ℤ√2`,
`(M · N)^{ik} = ∑_j M^{ij} ⊗ N^{jk}`, in the bond order of `finProdFinEquiv`. -/
abbrev mulZsqrt2Tensor (M : Fin d → Fin d → Matrix (Fin D₁) (Fin D₁) (ℤ√2))
    (N : Fin d → Fin d → Matrix (Fin D₂) (Fin D₂) (ℤ√2)) (i k : Fin d) :
    Matrix (Fin (D₁ * D₂)) (Fin (D₁ * D₂)) (ℤ√2) :=
  mulTensorR M N i k

/-- The bond-space action of a matrix product operator tensor over `ℤ√2` on a state tensor over
`ℤ√2`, `(M · A)^i = ∑_j M^{ij} ⊗ A^j`, in the bond order of `finProdFinEquiv`. -/
abbrev actZsqrt2Tensor (M : Fin d → Fin d → Matrix (Fin D₁) (Fin D₁) (ℤ√2))
    (A : Fin d → Matrix (Fin D₂) (Fin D₂) (ℤ√2)) (i : Fin d) :
    Matrix (Fin (D₁ * D₂)) (Fin (D₁ * D₂)) (ℤ√2) :=
  actTensorR M A i

/-- **Normality from a table of scaled matrix units over `ℤ√2`.** A tensor whose letters are the
images of matrices over `ℤ√2` and which realises every matrix unit as a nonzero multiple of one
of its letters spans the full matrix algebra, hence is normal at blocking length one. -/
theorem isNormal_of_single_eq_smul_zsqrt2 {A : MPSTensor d D}
    (AZ : Fin d → Matrix (Fin D) (Fin D) (ℤ√2)) (hA : ∀ a, A a = complexOfZsqrt2 (AZ a))
    (ℓ : Fin D → Fin D → Fin d) (w : Fin D → Fin D → ℤ√2) (hw : ∀ x y, w x y ≠ 0)
    (h : ∀ x y, AZ (ℓ x y) = w x y • Matrix.single x y 1) :
    Kraus.IsNormal A := by
  refine Kraus.IsInjective.isNormal
    (Submodule.eq_top_of_forall_single_mem _ fun x y => ?_)
  have hAl : A (ℓ x y) = zsqrt2ToComplex (w x y) • Matrix.single x y (1 : ℂ) := by
    rw [hA, h x y, complexOfZsqrt2_smul, complexOfZsqrt2_single]
  have hne : zsqrt2ToComplex (w x y) ≠ 0 := zsqrt2ToComplex_ne_zero (hw x y)
  have hmul := Submodule.smul_mem (Submodule.span ℂ (Set.range A))
    (zsqrt2ToComplex (w x y))⁻¹ (Submodule.subset_span (Set.mem_range_self (ℓ x y)))
  rwa [hAl, smul_smul, inv_mul_cancel₀ hne, one_smul] at hmul

end MPSTensor
