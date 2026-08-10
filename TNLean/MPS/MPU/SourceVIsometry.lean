/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.MatrixUnitaryBetween
import TNLean.MPS.MPU.SourceUV

/-!
# The dressed source-v Gram equation

This file formalizes the algebraic cancellation surrounding the source tensor
$v$ in arXiv:1703.09188, equation `vUnitary` (lines 577--600).  The right source
factors are tensorized in the exact dotted/solid leg order, and their explicit
right inverse removes the dressing from
$Y^\dagger(v^\dagger v)Y=Y^\dagger Y$.

The separate identification of this dressed equation with the supplied
fixed-witness `simple2` contraction is not asserted here.
-/

open scoped Matrix BigOperators Kronecker ComplexOrder
open Matrix

namespace MPOTensor

variable {d D : ℕ} (U : MPOTensor d D)

/-- The tensor product $Y_1\otimes Y_2$ in the source-bond order $(r,\ell)$.

Source: arXiv:1703.09188, equation `vUnitary`, lines 577--588. -/
noncomputable def sourceYTensor
    (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef) :
    Matrix (Fin r[U] × Fin ℓ[U])
      ((Fin d × Fin D) × (Fin d × Fin D)) ℂ :=
  sourceY₁ U ρ hρ ⊗ₖ sourceY₂ U

/-- The tensor product $Z_1\otimes Z_2$, the explicit right inverse of
`sourceYTensor`.

Source: arXiv:1703.09188, equations `YZ=1` and `vUnitary`, lines 495--506 and
577--588. -/
noncomputable def sourceZTensor
    (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef) :
    Matrix ((Fin d × Fin D) × (Fin d × Fin D))
      (Fin r[U] × Fin ℓ[U]) ℂ :=
  sourceZ₁ U ρ hρ ⊗ₖ sourceZ₂ U

/-- Entry formula for $Y_1\otimes Y_2$ in dotted/solid source-bond order.

Source: arXiv:1703.09188, equation `vUnitary`, lines 577--588. -/
@[simp] theorem sourceYTensor_apply
    (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef)
    (r : Fin r[U]) (l : Fin ℓ[U])
    (x₁ x₂ : Fin d × Fin D) :
    sourceYTensor U ρ hρ (r, l) (x₁, x₂) =
      sourceY₁ U ρ hρ r x₁ * sourceY₂ U l x₂ := rfl

/-- Entry formula for $Z_1\otimes Z_2$ in dotted/solid source-bond order.

Source: arXiv:1703.09188, equations `YZ=1` and `vUnitary`, lines 495--506 and
577--588. -/
@[simp] theorem sourceZTensor_apply
    (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef)
    (x₁ x₂ : Fin d × Fin D) (r : Fin r[U]) (l : Fin ℓ[U]) :
    sourceZTensor U ρ hρ (x₁, x₂) (r, l) =
      sourceZ₁ U ρ hρ x₁ r * sourceZ₂ U x₂ l := rfl

/-- The two source right inverses tensorize to
$(Y_1\otimes Y_2)(Z_1\otimes Z_2)=1$.

Source: arXiv:1703.09188, equations `YZ=1` and `vUnitary`, lines 495--506 and
577--588. -/
theorem sourceYTensor_mul_sourceZTensor
    (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef) :
    sourceYTensor U ρ hρ * sourceZTensor U ρ hρ = 1 := by
  rw [sourceYTensor, sourceZTensor, ← Matrix.mul_kronecker_mul,
    sourceY₁_mul_sourceZ₁, sourceY₂_mul_sourceZ₂, Matrix.one_kronecker_one]

/-- Regroup the two source-cut output indices into the two physical indices
and the canonically flattened pair of virtual indices.  No nested product type
is identified definitionally.

Source: arXiv:1703.09188, equation `vUnitary`, lines 577--588. -/
def sourceVRegroupEquiv :
    ((Fin d × Fin D) × (Fin d × Fin D)) ≃
      ((Fin d × Fin d) × Fin (D * D)) where
  toFun x := ((x.1.1, x.2.1), finProdFinEquiv (x.1.2, x.2.2))
  invFun x := ((x.1.1, (finProdFinEquiv.symm x.2).1),
    (x.1.2, (finProdFinEquiv.symm x.2).2))
  left_inv x := by
    rcases x with ⟨⟨i, a⟩, ⟨j, b⟩⟩
    simp
  right_inv x := by
    rcases x with ⟨⟨i, j⟩, a⟩
    change ((i, j), finProdFinEquiv (finProdFinEquiv.symm a)) = ((i, j), a)
    rw [finProdFinEquiv.apply_symm_apply]

/-- The regrouping equivalence sends two source-cut indices to their physical pair and
flattened virtual pair.

Source: arXiv:1703.09188, equation `vUnitary`, lines 577--588. -/
@[simp] theorem sourceVRegroupEquiv_apply
    (x₁ x₂ : Fin d × Fin D) :
    sourceVRegroupEquiv (d := d) (D := D) (x₁, x₂) =
      ((x₁.1, x₂.1), finProdFinEquiv (x₁.2, x₂.2)) := rfl

/-- The inverse regrouping equivalence separates a physical pair and flattened virtual pair
into two source-cut indices.

Source: arXiv:1703.09188, equation `vUnitary`, lines 577--588. -/
@[simp] theorem sourceVRegroupEquiv_symm_apply
    (p : Fin d × Fin d) (a : Fin (D * D)) :
    (sourceVRegroupEquiv (d := d) (D := D)).symm (p, a) =
      ((p.1, (finProdFinEquiv.symm a).1),
        (p.2, (finProdFinEquiv.symm a).2)) := rfl

/-- The equation $Y^\dagger(v^\dagger v)Y=Y^\dagger Y$, where
$Y=Y_1\otimes Y_2$ has source-bond order $(r,\ell)$.

Source: arXiv:1703.09188, equation `vUnitary`, lines 577--588. -/
def SourceVDressedGram
    (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef) : Prop :=
  let Y := sourceYTensor U ρ hρ
  Yᴴ * ((sourceV U ρ hρ)ᴴ * sourceV U ρ hρ) * Y = Yᴴ * Y

/-- Entrywise characterization of the dressed source-v Gram equation after the
explicit physical/virtual regrouping.  This is the finite-sum orientation to
which the supplied `simple2` contraction must be compared.

Source: arXiv:1703.09188, equation `vUnitary`, lines 577--588. -/
theorem sourceVDressedGram_iff_regrouped_entries
    (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef) :
    SourceVDressedGram U ρ hρ ↔
      ∀ p q : Fin d × Fin d, ∀ a b : Fin (D * D),
        let x := (sourceVRegroupEquiv (d := d) (D := D)).symm (p, a)
        let y := (sourceVRegroupEquiv (d := d) (D := D)).symm (q, b)
        ∑ t,
            (∑ s, star (sourceYTensor U ρ hρ s x) *
              ∑ z, star (sourceV U ρ hρ z s) * sourceV U ρ hρ z t) *
              sourceYTensor U ρ hρ t y =
          ∑ t, star (sourceYTensor U ρ hρ t x) * sourceYTensor U ρ hρ t y := by
  constructor
  · intro h p q a b
    have hentry := congrArg (fun M ↦ M
      ((sourceVRegroupEquiv (d := d) (D := D)).symm (p, a))
      ((sourceVRegroupEquiv (d := d) (D := D)).symm (q, b))) h
    simpa only [SourceVDressedGram, Matrix.mul_apply, Matrix.conjTranspose_apply]
      using hentry
  · intro h
    unfold SourceVDressedGram
    ext x y
    let px := sourceVRegroupEquiv (d := d) (D := D) x
    let py := sourceVRegroupEquiv (d := d) (D := D) y
    have hentry := h px.1 py.1 px.2 py.2
    have hx : (sourceVRegroupEquiv (d := d) (D := D)).symm (px.1, px.2) = x := by
      change (sourceVRegroupEquiv (d := d) (D := D)).symm px = x
      exact Equiv.symm_apply_apply _ x
    have hy : (sourceVRegroupEquiv (d := d) (D := D)).symm (py.1, py.2) = y := by
      change (sourceVRegroupEquiv (d := d) (D := D)).symm py = y
      exact Equiv.symm_apply_apply _ y
    rw [hx, hy] at hentry
    simpa only [Matrix.mul_apply, Matrix.conjTranspose_apply] using hentry

/-- Removing the $Y_1\otimes Y_2$ dressing with $Z_1\otimes Z_2$ gives
$v^\dagger v=1$.

Source: arXiv:1703.09188, equation `vUnitary`, lines 583--588. -/
theorem sourceVDressedGram_iff_isIsometry
    (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef) :
    SourceVDressedGram U ρ hρ ↔ (sourceV U ρ hρ).IsIsometry := by
  apply Matrix.conjTranspose_mul_mul_eq_conjTranspose_mul_iff_of_mul_eq_one
  exact sourceYTensor_mul_sourceZTensor U ρ hρ

end MPOTensor
