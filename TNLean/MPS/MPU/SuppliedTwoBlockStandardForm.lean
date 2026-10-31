/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.StandardForm
import TNLean.MPS.MPU.TwoSiteStandardFormSourceCuts
import TNLean.MPS.MPU.StaircaseUnitarity

/-!
# The literal two-block standard form

The actual cuts of a supplied square standard form give the paper's chosen
two-block gates, with its unshifted gate `v₂₃ (u ⊗ u)` and shifted gate `v₂₃`.
Only the raw cut factorizations are used in reconstructing the blocked tensor;
there is no canonical, normalization, minimality or compact-decomposition
assumption on the supplied form.

This constructs the printed blocking by two. Arbitrary blocking and the
sequential unwinding relation are separate statements.

Source: arXiv:1703.09188, `prop:sigma1-and-sigma2-equal`, lines 1657--1674,
and `eq:block-twosites`, lines 1237--1244.
-/

open scoped Matrix Kronecker BigOperators

namespace MPOTensor

private def twoBlockGateEquiv (d : ℕ) :
    ((Fin d × Fin d) × (Fin d × Fin d)) ≃ (Fin (d * d) × Fin (d * d)) :=
  finProdFinEquiv.prodCongr finProdFinEquiv

/-- The literal paper two-block input gate, with physical coordinates
ordered `(1,2,3,4)` and grouped as `(12,34)`.
Source: arXiv:1703.09188, lines 1657--1674. -/
noncomputable def twoBlockInputGate {d : ℕ}
    (u v : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    Matrix (Fin (d * d) × Fin (d * d)) (Fin (d * d) × Fin (d * d)) ℂ :=
  Matrix.reindex (twoBlockGateEquiv d) (twoBlockGateEquiv d)
    (staircaseMiddle (A := Fin d) (E := Fin d) v * (u ⊗ₖ u))

/-- The literal paper two-block shifted gate, equal to the middle `v`
with identity spectators in the same four-site order.
Source: arXiv:1703.09188, lines 1657--1674. -/
noncomputable def twoBlockOutputGate {d : ℕ}
    (v : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    Matrix (Fin (d * d) × Fin (d * d)) (Fin (d * d) × Fin (d * d)) ℂ :=
  Matrix.reindex (twoBlockGateEquiv d) (twoBlockGateEquiv d)
    (staircaseMiddle (A := Fin d) (E := Fin d) v)

/-- Every supplied square standard form has the paper's actual two-block
standard form, with gates `v₂₃(u⊗u)` and `v₂₃`. The half factors are its
explicit raw cut factors, with only the canonical pair enumeration applied.
No normalized source factorization or gauge witness is assumed.

Source: arXiv:1703.09188, `prop:sigma1-and-sigma2-equal`, lines 1657--1674,
and `eq:block-twosites`, lines 1237--1244. -/
noncomputable def TwoSiteStandardFormData.blockTwo
    {d D : ℕ} {W : MPOTensor (d * d) D}
    {u v : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ}
    (S : TwoSiteStandardFormData W u v) :
    TwoSiteStandardFormData (MPOTensor.blockTwo W)
      (twoBlockInputGate u v) (twoBlockOutputGate v) := by
  classical
  let e := (finProdFinEquiv (m := d) (n := d)).symm
  let p := twoBlockGateEquiv d
  let X₁ : Matrix (Fin (d * d) × Fin D) (Fin (d * d)) ℂ :=
    fun i s ↦ S.cutX₁ i (e s)
  let X₂ : Matrix (Fin D × Fin (d * d)) (Fin (d * d)) ℂ :=
    fun i t ↦ S.cutX₂ i (e t)
  have hvi := staircaseMiddle_isIsometry (A := Fin d) (E := Fin d) v S.v_unitary.1
  have hv : (staircaseMiddle (A := Fin d) (E := Fin d) v).IsUnitaryBetween :=
    hvi.isUnitaryBetween_of_card_eq _ rfl
  have hu := hv.mul _ _ (S.u_unitary.kronecker _ _ S.u_unitary)
  have hinput (l r j₁ j₂ : Fin (d * d)) :
      twoBlockInputGate u v (l, r) (j₁, j₂) =
        ∑ β : Fin D, S.cutY₂ (e l) (j₁, β) * S.cutY₁ (e r) (β, j₂) := by
    have h := congrArg (fun M ↦ M (e l, e r) (e j₁, e j₂))
      S.cutY₂_cutY₁_eq_staircaseMiddle_mul_kronecker
    simpa only [twoBlockInputGate, Matrix.reindex_apply, Matrix.submatrix_apply,
      twoBlockGateEquiv,
      Equiv.prodCongr_symm, Equiv.prodCongr_apply, Prod.map_apply,
      Equiv.apply_symm_apply, e] using h.symm
  refine {
    phys_pos := Nat.mul_pos S.phys_pos S.phys_pos
    bond_pos := S.bond_pos
    left_pos := Nat.mul_pos S.phys_pos S.phys_pos
    right_pos := Nat.mul_pos S.phys_pos S.phys_pos
    X₁ := X₁
    X₂ := X₂
    u_unitary := hu.reindex _ p p
    v_unitary := hv.reindex _ p p
    v_apply := ?_
    W_apply := ?_ }
  · intro i₁ i₂ s t
    have h := congrArg (fun M ↦ M (e i₁, e i₂) (e s, e t))
      S.cutX₁_cutX₂_eq_staircaseMiddle
    simpa only [twoBlockOutputGate, Matrix.reindex_apply, Matrix.submatrix_apply,
      twoBlockGateEquiv,
      Equiv.prodCongr_symm, Equiv.prodCongr_apply, Prod.map_apply,
      Equiv.apply_symm_apply, X₁, X₂, e] using h.symm
  · intro i j α γ
    let a := (finProdFinEquiv.symm i).1
    let b := (finProdFinEquiv.symm i).2
    let c := (finProdFinEquiv.symm j).1
    let f := (finProdFinEquiv.symm j).2
    let F (l r : Fin d × Fin d) := S.cutX₂ (α, a) l *
      (∑ β : Fin D, S.cutY₂ l (c, β) * S.cutY₁ r (β, f)) * S.cutX₁ (b, γ) r
    have hraw : (W a c * W b f) α γ = ∑ l, ∑ r, F l r :=
      mul_apply_eq_sum_of_sourceCut_factorizations W S.cutX₁ S.cutY₁ S.cutX₂ S.cutY₂
        S.sourceCutM₁_eq_cutX₁_mul_cutY₁ S.sourceCutM₂_eq_cutX₂_mul_cutY₂ a c b f α γ
    have hsum : (∑ l : Fin (d * d), ∑ r : Fin (d * d), F (e l) (e r)) =
        ∑ l : Fin d × Fin d, ∑ r : Fin d × Fin d, F l r := by
      calc
        _ = ∑ l : Fin (d * d), ∑ r : Fin d × Fin d, F (e l) r := by
          exact Finset.sum_congr rfl fun l _ ↦ e.sum_comp (F (e l))
        _ = _ := e.sum_comp (fun l ↦ ∑ r, F l r)
    change (W a c * W b f) α γ =
      ∑ l : Fin (d * d), ∑ r : Fin (d * d), X₂ (α, a) l *
        twoBlockInputGate u v (l, r) (c, f) * X₁ (b, γ) r
    simp only [X₁, X₂, hinput]
    exact hraw.trans hsum.symm

end MPOTensor
