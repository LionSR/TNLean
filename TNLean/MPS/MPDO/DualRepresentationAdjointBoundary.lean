/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.CoalgebraDualStar
import TNLean.MPS.MPDO.BoundaryAdjointClosed
import TNLean.MPS.SharedInfra.MatrixFamilyTracePairing

/-!
# Arbitrary-boundary adjoints from a coalgebra representation

Let `H` be a complex coalgebra with a conjugate-linear involution preserved by
comultiplication. A star-preserving physical linear map `φ` and a faithful
representation `ψ` of the convolution dual define an MPO by the letters
`T i j = ψ (fun x ↦ φ x i j)`. The intrinsic involution of the dual swaps the
physical indices and preserves convolution order. Extending a linear
functional from the image of `ψ` and using the nondegenerate matrix trace
pairing gives one adjoint boundary working simultaneously at every length,
including zero.

These are the coalgebra and representation data used in the C*-weak-Hopf
construction. No normality, periodic dual-label permutation, or boundary
adjoint-closure hypothesis occurs. This result does not construct a weak Hopf
algebra, realize a given mixed tensor by these data, or normalize an integral.

## References

* Garre-Rubio--Lootens--Molnár, arXiv:2203.12563v3, lines 1236--1320.
* Molnár et al., arXiv:2204.05940v1, Proposition 5.4 and Definition 5.8.
-/

open scoped Matrix

noncomputable section

namespace MPOTensor

variable {H : Type*} [AddCommGroup H] [Module ℂ H] [Coalgebra ℂ H]
  [StarAddMonoid H] [StarModule ℂ H]
variable {d D : ℕ}

/-- A physical matrix entry, viewed as an element of the convolution dual.
Source: arXiv:2204.05940v1, the representation construction in Section 4. -/
def dualCoefficient (φ : H →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ) (i j : Fin d) :
    WithConv (H →ₗ[ℂ] ℂ) :=
  WithConv.toConv
    { toFun := fun x ↦ φ x i j
      map_add' := by intro x y; simp
      map_smul' := by intro c x; simp }

/-- The actual MPO obtained by evaluating physical matrix coefficients in a
representation of the convolution dual. Source: arXiv:2204.05940v1, Section 4
and Proposition 5.4. -/
def ofDualRepresentation (φ : H →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ)
    (ψ : WithConv (H →ₗ[ℂ] ℂ) →ₐ[ℂ] Matrix (Fin D) (Fin D) ℂ) : MPOTensor d D :=
  fun i j ↦ ψ (dualCoefficient φ i j)

omit [Coalgebra ℂ H] in
/-- Physical star compatibility swaps coefficient indices under the intrinsic
involution of the dual, without reversing the spatial order. -/
theorem star_dualCoefficient
    (φ : H →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ)
    (hφ : ∀ x, φ (star x) = (φ x)ᴴ) (i j : Fin d) :
    star (dualCoefficient φ i j) = dualCoefficient φ j i := by
  ext x
  change star (φ (star x) i j) = φ x j i
  rw [hφ]
  simp

omit [StarAddMonoid H] [StarModule ℂ H] in
/-- The virtual word is the image of the ordered convolution product of its
physical coefficients. This includes the empty word and uses unitality of the
dual representation. -/
theorem evalWord_ofDualRepresentation
    (φ : H →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ)
    (ψ : WithConv (H →ₗ[ℂ] ℂ) →ₐ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    {N : ℕ} (σ τ : Fin N → Fin d) :
    evalWord (ofDualRepresentation φ ψ) (List.ofFn σ) (List.ofFn τ) =
      ψ (List.ofFn (fun k ↦ dualCoefficient φ (σ k) (τ k))).prod := by
  induction N with
  | zero => simp
  | succ N ih =>
    simp only [List.ofFn_succ, evalWord_cons, List.prod_cons, map_mul,
      ofDualRepresentation, ih]

/-- The intrinsic involution exchanges the two physical configurations in an
ordered coefficient product. It preserves their spatial order. -/
theorem star_dualCoefficient_prod
    (hcomul : ∀ x : H,
      Coalgebra.comul (R := ℂ) (star x) = star (Coalgebra.comul (R := ℂ) x))
    (φ : H →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ)
    (hφ : ∀ x, φ (star x) = (φ x)ᴴ)
    {N : ℕ} (σ τ : Fin N → Fin d) :
    star (List.ofFn (fun k ↦ dualCoefficient φ (σ k) (τ k))).prod =
      (List.ofFn (fun k ↦ dualCoefficient φ (τ k) (σ k))).prod := by
  induction N with
  | zero => simpa using Coalgebra.dualStar_one hcomul
  | succ N ih =>
    simp only [List.ofFn_succ, List.prod_cons, Coalgebra.dualStar_mul hcomul,
      star_dualCoefficient φ hφ, ih]

/-- A faithful dual representation turns the conjugated boundary functional
into a trace pairing with one ambient virtual matrix. The extension is made
once, independently of chain length. -/
theorem exists_boundary_trace_dualStar
    (ψ : WithConv (H →ₗ[ℂ] ℂ) →ₐ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (hψ : Function.Injective ψ) (X : Matrix (Fin D) (Fin D) ℂ) :
    ∃ Y : Matrix (Fin D) (Fin D) ℂ, ∀ f : WithConv (H →ₗ[ℂ] ℂ),
      Matrix.trace (Y * ψ f) = star (Matrix.trace (X * ψ (star f))) := by
  let ℓ : WithConv (H →ₗ[ℂ] ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun f ↦ star (Matrix.trace (X * ψ (star f)))
      map_add' := by intro f g; simp [Matrix.mul_add]
      map_smul' := by intro c f; simp [Matrix.trace_smul] }
  obtain ⟨θ, hθ⟩ := LinearMap.dualMap_surjective_of_injective
    (f := ψ.toLinearMap) hψ ℓ
  obtain ⟨Y, hY⟩ := Matrix.exists_trace_representation θ
  refine ⟨Y, fun f ↦ ?_⟩
  exact (hY (ψ f)).symm.trans (LinearMap.congr_fun hθ f)

/-- Star-compatible coalgebra data and a faithful dual representation produce
one adjoint boundary valid at every length, including zero.

This establishes the arbitrary-boundary adjoint step for the representation
construction in arXiv:2204.05940v1, Section 4 and Proposition 5.4, used in the
C*-weak-Hopf setting of GLM23, arXiv:2203.12563v3, lines 1236--1320. -/
theorem exists_adjointBoundary_of_dualRepresentation
    (hcomul : ∀ x : H,
      Coalgebra.comul (R := ℂ) (star x) = star (Coalgebra.comul (R := ℂ) x))
    (φ : H →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ)
    (hφ : ∀ x, φ (star x) = (φ x)ᴴ)
    (ψ : WithConv (H →ₗ[ℂ] ℂ) →ₐ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (hψ : Function.Injective ψ) (X : Matrix (Fin D) (Fin D) ℂ) :
    ∃ Y : Matrix (Fin D) (Fin D) ℂ, ∀ N : ℕ,
      (mpoWithBoundary (ofDualRepresentation φ ψ) X N)ᴴ =
        mpoWithBoundary (ofDualRepresentation φ ψ) Y N := by
  obtain ⟨Y, hY⟩ := exists_boundary_trace_dualStar ψ hψ X
  refine ⟨Y, fun N ↦ ?_⟩
  ext σ τ
  change star (Matrix.trace (X *
      evalWord (ofDualRepresentation φ ψ) (List.ofFn τ) (List.ofFn σ))) =
    Matrix.trace (Y *
      evalWord (ofDualRepresentation φ ψ) (List.ofFn σ) (List.ofFn τ))
  rw [evalWord_ofDualRepresentation, evalWord_ofDualRepresentation, hY,
    star_dualCoefficient_prod hcomul φ hφ]

/-- The represented MPO is arbitrary-boundary adjoint closed with one boundary
for all positive lengths. No closure or normality premise is assumed. -/
theorem isBoundaryAdjointClosed_of_dualRepresentation
    (hcomul : ∀ x : H,
      Coalgebra.comul (R := ℂ) (star x) = star (Coalgebra.comul (R := ℂ) x))
    (φ : H →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ)
    (hφ : ∀ x, φ (star x) = (φ x)ᴴ)
    (ψ : WithConv (H →ₗ[ℂ] ℂ) →ₐ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (hψ : Function.Injective ψ) : IsBoundaryAdjointClosed (ofDualRepresentation φ ψ) := by
  intro X
  obtain ⟨Y, hY⟩ := exists_adjointBoundary_of_dualRepresentation hcomul φ hφ ψ hψ X
  exact ⟨Y, fun N _ ↦ hY N⟩

end MPOTensor
