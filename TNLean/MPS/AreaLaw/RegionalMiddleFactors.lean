/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.SelectedCoefficientDecomposition
import TNLean.Algebra.MatrixFactorExchange
import QICLean.Channel.FiniteProduct
import TNLean.Lattice.Sheet.Splitting
import Mathlib.Data.Fintype.EquivFin

/-!
# Regional middle factors under a change of region

A middle decomposition in three-region coordinates gives a decomposition
on the actual middle and its actual complement, retaining the prescribed
middle operators. Increasing interval coordinates are transported by their
supplied site equivalence.

For two arbitrary finite regions, the old-only sites, new-only sites,
intersection and common exterior give compatible configuration coordinates.
The existing matrix-factor exchange then produces a new middle family
before the old exterior coefficients are supplied.

These are identities of regional matrices. Physical site ordering and
matrix product representation bounds are separate statements.

## References

Supporting algebra for ALVV, arXiv:1602.08828v2,
Proposition 5.7, lines 1324–1333.
-/

open Matrix
open scoped BigOperators Kronecker
open TNLean.Lattice.Sheet

noncomputable section

namespace TNLean.MPS.AreaLaw

/-- Recombine the two exterior pieces as the actual complement of the middle.
This is a configuration identity for the regional decomposition used in ALVV,
arXiv:1602.08828v2, Proposition 5.7, lines 1324–1333. -/
private def threeSplitExteriorConfigEquiv {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (q : ℕ) (T E : Finset Ω) (hTE : Disjoint T E) :
    FiniteProduct.Configuration (fun _ : Ω ↦ Fin q) Eᶜ ≃
      ((T → Fin q) × (↥((T ∪ E)ᶜ) → Fin q)) :=
  (FiniteProduct.complementUnionEquiv (fun _ : Ω ↦ Fin q) E T hTE.symm).trans
    ((Equiv.refl _).prodCongr
      (FiniteProduct.configurationCongr (fun _ : Ω ↦ Fin q)
        (congrArg (fun S : Finset Ω ↦ Sᶜ) (Finset.union_comm E T))))

/-- Regrouping the three regional coordinates agrees with splitting off the
middle and then reading its actual complement. Supporting ALVV,
arXiv:1602.08828v2, Proposition 5.7, lines 1324–1333. -/
private theorem exteriorMiddle_threeSplit_apply
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (q : ℕ) (T E : Finset Ω) (hTE : Disjoint T E) (x : Ω → Fin q) :
    exteriorMiddleEquiv (T → Fin q) (E → Fin q) (↥((T ∪ E)ᶜ) → Fin q)
        (threeSplit q T E hTE x) =
      (threeSplitExteriorConfigEquiv q T E hTE
        ((FiniteProduct.splitEquiv (fun _ : Ω ↦ Fin q) E x).2),
        (FiniteProduct.splitEquiv (fun _ : Ω ↦ Fin q) E x).1) := by
  apply Prod.ext
  · apply Prod.ext
    · funext v
      simp [exteriorMiddleEquiv, threeSplitExteriorConfigEquiv,
        FiniteProduct.complementUnionEquiv, Equiv.prodCongr]
    · funext v
      simp [exteriorMiddleEquiv, threeSplitExteriorConfigEquiv,
        FiniteProduct.complementUnionEquiv, FiniteProduct.configurationCongr_apply,
        Equiv.prodCongr]
  · funext v
    simp [exteriorMiddleEquiv]

/-- A three-region middle decomposition is a decomposition over the actual
middle and its actual complement, with precisely the same middle family.
Only exterior coefficients are pulled back. This closes the regional
coordinate identification in ALVV, arXiv:1602.08828v2,
Proposition 5.7, lines 1324–1333. -/
private theorem exists_regional_exterior_of_threeSplit_decomposition
    {Ω ι R : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype ι] [Semiring R]
    (q : ℕ) (T E : Finset Ω) (hTE : Disjoint T E)
    (X : Matrix (Ω → Fin q) (Ω → Fin q) R)
    (V : ι → Matrix (E → Fin q) (E → Fin q) R)
    (B : ι → Matrix ((T → Fin q) × (↥((T ∪ E)ᶜ) → Fin q))
      ((T → Fin q) × (↥((T ∪ E)ᶜ) → Fin q)) R)
    (hX : X.reindex
        ((threeSplit q T E hTE).trans
          (exteriorMiddleEquiv (T → Fin q) (E → Fin q) (↥((T ∪ E)ᶜ) → Fin q)))
        ((threeSplit q T E hTE).trans
          (exteriorMiddleEquiv (T → Fin q) (E → Fin q) (↥((T ∪ E)ᶜ) → Fin q))) =
        ∑ t, B t ⊗ₖ V t) :
    ∃ M : ι → Matrix (↥(Eᶜ) → Fin q) (↥(Eᶜ) → Fin q) R,
      X = (∑ t, M t ⊗ₖ V t).submatrix
        ((FiniteProduct.splitEquiv (fun _ : Ω ↦ Fin q) E).trans (Equiv.prodComm _ _))
        ((FiniteProduct.splitEquiv (fun _ : Ω ↦ Fin q) E).trans (Equiv.prodComm _ _)) := by
  let f := (threeSplit q T E hTE).trans
    (exteriorMiddleEquiv (T → Fin q) (E → Fin q) (↥((T ∪ E)ᶜ) → Fin q))
  let M := fun t ↦ (B t).submatrix (threeSplitExteriorConfigEquiv q T E hTE)
    (threeSplitExteriorConfigEquiv q T E hTE)
  refine ⟨M, ?_⟩
  ext x y
  have hentry := congrArg (fun Z ↦ Z (f x) (f y)) hX
  change X (f.symm (f x)) (f.symm (f y)) = (∑ t, B t ⊗ₖ V t) (f x) (f y) at hentry
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply] at hentry
  have hx : f x = _ := exteriorMiddle_threeSplit_apply q T E hTE x
  have hy : f y = _ := exteriorMiddle_threeSplit_apply q T E hTE y
  rw [hx, hy] at hentry
  simpa [M, Matrix.submatrix_apply, Matrix.sum_apply, Matrix.kroneckerMap_apply] using hentry

/-- Convert increasing middle coordinates and the three-region exterior into
an operator identity on the actual middle region and its complement. The
middle family is prescribed before exterior coefficients. Supporting ALVV,
arXiv:1602.08828v2, Proposition 5.7, lines 1324–1333. -/
theorem exists_regional_exterior_of_natural_threeSplit_decomposition
    {Ω ι R : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype ι] [Semiring R]
    {q N : ℕ} (T E : Finset Ω) (hTE : Disjoint T E) (eE : Fin N ≃ E)
    (X : Matrix (Ω → Fin q) (Ω → Fin q) R)
    (V : ι → Matrix (Fin N → Fin q) (Fin N → Fin q) R)
    (B : ι → Matrix ((T → Fin q) × (↥((T ∪ E)ᶜ) → Fin q))
      ((T → Fin q) × (↥((T ∪ E)ᶜ) → Fin q)) R)
    (hX : (X.reindex
        ((threeSplit q T E hTE).trans
          (exteriorMiddleEquiv (T → Fin q) (E → Fin q) (↥((T ∪ E)ᶜ) → Fin q)))
        ((threeSplit q T E hTE).trans
          (exteriorMiddleEquiv (T → Fin q) (E → Fin q) (↥((T ∪ E)ᶜ) → Fin q)))).submatrix
          (fun x : ((T → Fin q) × (↥((T ∪ E)ᶜ) → Fin q)) × (Fin N → Fin q) ↦
            (x.1, x.2 ∘ eE.symm))
          (fun x : ((T → Fin q) × (↥((T ∪ E)ᶜ) → Fin q)) × (Fin N → Fin q) ↦
            (x.1, x.2 ∘ eE.symm)) = ∑ r, B r ⊗ₖ V r) :
    ∃ M : ι → Matrix (↥(Eᶜ) → Fin q) (↥(Eᶜ) → Fin q) R,
      X = (∑ r, M r ⊗ₖ (V r).submatrix (fun σ : E → Fin q ↦ σ ∘ eE)
          (fun σ : E → Fin q ↦ σ ∘ eE)).submatrix
        ((FiniteProduct.splitEquiv (fun _ : Ω ↦ Fin q) E).trans (Equiv.prodComm _ _))
        ((FiniteProduct.splitEquiv (fun _ : Ω ↦ Fin q) E).trans (Equiv.prodComm _ _)) := by
  let f := (threeSplit q T E hTE).trans
    (exteriorMiddleEquiv (T → Fin q) (E → Fin q) (↥((T ∪ E)ᶜ) → Fin q))
  let Vphys := fun r ↦ (V r).submatrix (fun σ : E → Fin q ↦ σ ∘ eE)
    (fun σ : E → Fin q ↦ σ ∘ eE)
  have hphys : X.reindex f f = ∑ r, B r ⊗ₖ Vphys r := by
    ext x y
    let xn := (x.1, x.2 ∘ eE)
    let yn := (y.1, y.2 ∘ eE)
    have hx : (x.1, (x.2 ∘ eE) ∘ eE.symm) = x := by
      apply Prod.ext
      · rfl
      · funext v
        simp only [Function.comp_apply, eE.apply_symm_apply]
    have hy : (y.1, (y.2 ∘ eE) ∘ eE.symm) = y := by
      apply Prod.ext
      · rfl
      · funext v
        simp only [Function.comp_apply, eE.apply_symm_apply]
    have hentry := congrArg (fun Z ↦ Z xn yn) hX
    simp only [Matrix.submatrix_apply] at hentry
    change (X.reindex f f) (x.1, (x.2 ∘ eE) ∘ eE.symm)
      (y.1, (y.2 ∘ eE) ∘ eE.symm) = (∑ r, B r ⊗ₖ V r) xn yn at hentry
    rw [hx, hy] at hentry
    simpa only [Matrix.sum_apply, Matrix.kroneckerMap_apply, Vphys,
      Matrix.submatrix_apply, xn, yn] using hentry
  exact exists_regional_exterior_of_threeSplit_decomposition
    q T E hTE X Vphys B hphys

end TNLean.MPS.AreaLaw

namespace FiniteProduct

variable {V : Type*} [Fintype V] [DecidableEq V] (β : V → Type*)

/-- Split the old middle into its removed sites and the intersection. -/
def changingOldMiddleConfigEquiv (E J : Finset V) :
    Configuration β E ≃ Configuration β (E \ J) × Configuration β (E ∩ J) :=
  (configurationCongr β (Finset.sdiff_union_inter E J).symm).trans
    (unionEquiv β (E \ J) (E ∩ J) (by
      apply Finset.disjoint_left.mpr
      intro v hA hC
      exact (Finset.mem_sdiff.mp hA).2 (Finset.mem_inter.mp hC).2))

/-- Split the old exterior into the newly retained sites and the common exterior. -/
private def changingOldExteriorConfigEquiv (E J : Finset V) :
    Configuration β Eᶜ ≃
      Configuration β (J \ E) × Configuration β (E ∪ J)ᶜ :=
  (complementUnionEquiv β E (J \ E) (by
    apply Finset.disjoint_left.mpr
    intro v hE hB
    exact (Finset.mem_sdiff.mp hB).2 hE)).trans
      ((Equiv.refl _).prodCongr
        (configurationCongr β (congrArg (fun S : Finset V ↦ Sᶜ)
          (Finset.union_sdiff_self_eq_union (s := E) (t := J)))))

/-- Split the new middle, using the same literal intersection as the old split. -/
def changingNewMiddleConfigEquiv (E J : Finset V) :
    Configuration β J ≃ Configuration β (J \ E) × Configuration β (E ∩ J) :=
  (changingOldMiddleConfigEquiv β J E).trans
    ((Equiv.refl _).prodCongr (configurationCongr β (Finset.inter_comm J E)))

/-- Split the new exterior, using the same literal common exterior. -/
private def changingNewExteriorConfigEquiv (E J : Finset V) :
    Configuration β Jᶜ ≃
      Configuration β (E \ J) × Configuration β (E ∪ J)ᶜ :=
  (changingOldExteriorConfigEquiv β J E).trans
    ((Equiv.refl _).prodCongr
      (configurationCongr β (congrArg (fun S : Finset V ↦ Sᶜ)
        (Finset.union_comm J E))))

/-- Old exterior-first coordinates refined into the four actual regions. -/
private def changingOldConfigEquiv (E J : Finset V) :
    ((v : V) → β v) ≃
      ((Configuration β (J \ E) × Configuration β (E ∪ J)ᶜ) ×
        (Configuration β (E \ J) × Configuration β (E ∩ J))) :=
  ((splitEquiv β E).trans (Equiv.prodComm _ _)).trans
    ((changingOldExteriorConfigEquiv β E J).prodCongr
      (changingOldMiddleConfigEquiv β E J))

/-- New exterior-first coordinates refined into the same four actual regions. -/
private def changingNewConfigEquiv (E J : Finset V) :
    ((v : V) → β v) ≃
      ((Configuration β (E \ J) × Configuration β (E ∪ J)ᶜ) ×
        (Configuration β (J \ E) × Configuration β (E ∩ J))) :=
  ((splitEquiv β J).trans (Equiv.prodComm _ _)).trans
    ((changingNewExteriorConfigEquiv β E J).prodCongr
      (changingNewMiddleConfigEquiv β E J))

/-- Every old four-region coordinate is the restriction to its actual sites. -/
private theorem changingOldConfigEquiv_apply (E J : Finset V)
    (x : (v : V) → β v) :
    changingOldConfigEquiv β E J x =
      ((fun v : ↥(J \ E) ↦ x v.val, fun v : ↥((E ∪ J)ᶜ) ↦ x v.val),
        (fun v : ↥(E \ J) ↦ x v.val, fun v : ↥(E ∩ J) ↦ x v.val)) := by
  apply Prod.ext
  · apply Prod.ext
    · funext v
      simp [changingOldConfigEquiv, changingOldExteriorConfigEquiv,
        Equiv.prodCongr, complementUnionEquiv]
    · funext v
      simp [changingOldConfigEquiv, changingOldExteriorConfigEquiv,
        Equiv.prodCongr, complementUnionEquiv, configurationCongr_apply]
  · apply Prod.ext
    · funext v
      simp [changingOldConfigEquiv, changingOldMiddleConfigEquiv,
        Equiv.prodCongr, unionEquiv, configurationCongr_apply]
    · funext v
      simp [changingOldConfigEquiv, changingOldMiddleConfigEquiv,
        Equiv.prodCongr, unionEquiv, configurationCongr_apply]

/-- Every new four-region coordinate is the restriction to its actual sites. -/
private theorem changingNewConfigEquiv_apply (E J : Finset V)
    (x : (v : V) → β v) :
    changingNewConfigEquiv β E J x =
      ((fun v : ↥(E \ J) ↦ x v.val, fun v : ↥((E ∪ J)ᶜ) ↦ x v.val),
        (fun v : ↥(J \ E) ↦ x v.val, fun v : ↥(E ∩ J) ↦ x v.val)) := by
  apply Prod.ext
  · apply Prod.ext
    · funext v
      simp [changingNewConfigEquiv, changingNewExteriorConfigEquiv,
        changingOldExteriorConfigEquiv, Equiv.prodCongr, complementUnionEquiv]
    · funext v
      simp [changingNewConfigEquiv, changingNewExteriorConfigEquiv,
        changingOldExteriorConfigEquiv, Equiv.prodCongr,
        complementUnionEquiv, configurationCongr_apply]
  · apply Prod.ext
    · funext v
      simp [changingNewConfigEquiv, changingNewMiddleConfigEquiv,
        changingOldMiddleConfigEquiv, Equiv.prodCongr,
        unionEquiv, configurationCongr_apply]
    · funext v
      simp [changingNewConfigEquiv, changingNewMiddleConfigEquiv,
        changingOldMiddleConfigEquiv, Equiv.prodCongr,
        unionEquiv, configurationCongr_apply]

/-- Refining the old cut then regrouping equals refining the new cut.
This is a coordinate identity on the four actual finite regions, supporting
ALVV, arXiv:1602.08828v2, Proposition 5.7, lines 1332–1333. -/
private theorem changingMiddleConfig_commutes (E J : Finset V)
    (x : (v : V) → β v) :
    Matrix.middleFactorExchangeEquiv (changingOldConfigEquiv β E J x) =
      changingNewConfigEquiv β E J x := by
  rw [changingOldConfigEquiv_apply, changingNewConfigEquiv_apply]
  rfl

end FiniteProduct

namespace FiniteProduct

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω] (β : Ω → Type*)

/-- Transfer an old middle family to a prescribed new region using only the
old middle operators and standard matrix-unit labels. The configurations
are literal restrictions to the four regions. Supporting ALVV,
arXiv:1602.08828v2, Proposition 5.7, lines 1332–1333. -/
noncomputable def changingRegionalMiddleFamily {R ι : Type*} [Semiring R]
    (E J : Finset Ω)
    (V : ι → Matrix (Configuration β E) (Configuration β E) R) :
    (ι × (Configuration β (E \ J) × Configuration β (E \ J)) ×
      (Configuration β (J \ E) × Configuration β (J \ E))) →
      Matrix (Configuration β J) (Configuration β J) R := by
  classical
  exact fun r ↦
    (Matrix.exchangedMiddleFamily
      (fun t ↦ (V t).reindex (changingOldMiddleConfigEquiv β E J)
        (changingOldMiddleConfigEquiv β E J)) r).reindex
      (changingNewMiddleConfigEquiv β E J).symm
      (changingNewMiddleConfigEquiv β E J).symm

/-- Changing regions preserves a decomposition with one fixed middle family.
The family on the new region depends only on the old middle family. All old
exterior coefficients may be supplied afterwards. No ordering or MPO
assertion is made by this purely regional matrix identity. Supporting ALVV,
arXiv:1602.08828v2, Proposition 5.7, lines 1332–1333. -/
theorem exists_changingRegional_exterior_family
    {R ι : Type*} [Semiring R] [Fintype ι] [∀ v, Fintype (β v)]
    (E J : Finset Ω)
    (V : ι → Matrix (Configuration β E) (Configuration β E) R)
    (M : ι → Matrix (Configuration β Eᶜ) (Configuration β Eᶜ) R) :
    ∃ Mnew : (ι × (Configuration β (E \ J) × Configuration β (E \ J)) ×
        (Configuration β (J \ E) × Configuration β (J \ E))) →
        Matrix (Configuration β Jᶜ) (Configuration β Jᶜ) R,
      (∑ t, M t ⊗ₖ V t).submatrix
        ((splitEquiv β E).trans (Equiv.prodComm _ _))
        ((splitEquiv β E).trans (Equiv.prodComm _ _)) =
      (∑ r, Mnew r ⊗ₖ changingRegionalMiddleFamily β E J V r).submatrix
        ((splitEquiv β J).trans (Equiv.prodComm _ _))
        ((splitEquiv β J).trans (Equiv.prodComm _ _)) := by
  classical
  let Mfour := fun t ↦ (M t).reindex (changingOldExteriorConfigEquiv β E J)
    (changingOldExteriorConfigEquiv β E J)
  let Vfour := fun t ↦ (V t).reindex (changingOldMiddleConfigEquiv β E J)
    (changingOldMiddleConfigEquiv β E J)
  let Mnew := fun r : (ι × (Configuration β (E \ J) × Configuration β (E \ J)) ×
      (Configuration β (J \ E) × Configuration β (J \ E))) ↦
    ((Matrix.single r.2.1.1 r.2.1.2 (1 : R)) ⊗ₖ
      Matrix.operatorBlock (Mfour r.1) r.2.2.1 r.2.2.2).reindex
        (changingNewExteriorConfigEquiv β E J).symm
        (changingNewExteriorConfigEquiv β E J).symm
  refine ⟨Mnew, ?_⟩
  have h := Matrix.reindex_sum_kronecker_middleFactorExchange Vfour Mfour
  ext σ τ
  have hentry := congrArg
    (fun Z ↦ Z (changingNewConfigEquiv β E J σ) (changingNewConfigEquiv β E J τ)) h
  have hσ : Matrix.middleFactorExchangeEquiv.symm (changingNewConfigEquiv β E J σ) =
      changingOldConfigEquiv β E J σ := by
    rw [← changingMiddleConfig_commutes β E J σ, Equiv.symm_apply_apply]
  have hτ : Matrix.middleFactorExchangeEquiv.symm (changingNewConfigEquiv β E J τ) =
      changingOldConfigEquiv β E J τ := by
    rw [← changingMiddleConfig_commutes β E J τ, Equiv.symm_apply_apply]
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply] at hentry
  rw [hσ, hτ] at hentry
  simpa [Matrix.submatrix_apply, Matrix.sum_apply, Matrix.kroneckerMap_apply,
    Matrix.reindex_apply, Mfour, Vfour, Mnew, changingRegionalMiddleFamily,
    changingOldConfigEquiv, changingNewConfigEquiv] using hentry

end FiniteProduct

end


section

open Matrix

open scoped BigOperators Kronecker

section

namespace FiniteProduct

/-- A common regional family can be transported and numbered before any
exterior coefficients are supplied. The cardinality is the exact cost of
the two configuration spaces transferred across the regional boundary.
Auxiliary to ALVV, arXiv:1602.08828v2, Proposition 5.7, lines 1324–1333.
No positivity, interval, spectral, bond-dimension or running-time assertion
is required for this finite matrix identity. -/
theorem exists_changingRegional_family_fin
    {Ω ι : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype ι]
    (q : ℕ) (E J : Finset Ω)
    (V : ι → Matrix (E → Fin q) (E → Fin q) ℂ) :
    ∃ (N : ℕ) (W : Fin N → Matrix (J → Fin q) (J → Fin q) ℂ),
      N = Fintype.card ι * q ^ (2 * (E \ J).card + 2 * (J \ E).card) ∧
      ∀ M : ι → Matrix (↥(Eᶜ) → Fin q) (↥(Eᶜ) → Fin q) ℂ,
        ∃ Mnew : Fin N → Matrix (↥(Jᶜ) → Fin q) (↥(Jᶜ) → Fin q) ℂ,
          (∑ t, M t ⊗ₖ V t).submatrix
              ((splitEquiv (fun _ : Ω ↦ Fin q) E).trans (Equiv.prodComm _ _))
              ((splitEquiv (fun _ : Ω ↦ Fin q) E).trans (Equiv.prodComm _ _)) =
            (∑ r, Mnew r ⊗ₖ W r).submatrix
              ((splitEquiv (fun _ : Ω ↦ Fin q) J).trans (Equiv.prodComm _ _))
              ((splitEquiv (fun _ : Ω ↦ Fin q) J).trans (Equiv.prodComm _ _)) := by
  classical
  let β := fun _ : Ω ↦ Fin q
  let A := E \ J
  let B := J \ E
  let I := ι × (Configuration β A × Configuration β A) ×
    (Configuration β B × Configuration β B)
  let Wall := changingRegionalMiddleFamily β E J V
  let e := Fintype.equivFin I
  have hcard : Fintype.card I = Fintype.card ι * q ^ (2 * A.card + 2 * B.card) := by
    calc
      Fintype.card I = Fintype.card ι * Fintype.card (Configuration β A) ^ 2 *
          Fintype.card (Configuration β B) ^ 2 := Matrix.card_exchangedMiddleFamily_index
      _ = Fintype.card ι * q ^ (2 * A.card + 2 * B.card) := by
        simp only [Configuration, β, Fintype.card_fun, Fintype.card_fin,
          Fintype.card_coe, ← pow_mul]
        rw [Nat.mul_assoc, ← pow_add]
        rw [show A.card * 2 + B.card * 2 = 2 * A.card + 2 * B.card by omega]
  refine ⟨Fintype.card I, fun r ↦ Wall (e.symm r), hcard, ?_⟩
  intro M
  obtain ⟨Mnew, hMnew⟩ := exists_changingRegional_exterior_family β E J V M
  refine ⟨fun r ↦ Mnew (e.symm r), hMnew.trans ?_⟩
  exact congrArg (fun P ↦ P.submatrix
    ((splitEquiv β J).trans (Equiv.prodComm _ _))
    ((splitEquiv β J).trans (Equiv.prodComm _ _)))
    (e.symm.sum_comp (fun r ↦ Mnew r ⊗ₖ Wall r)).symm
end FiniteProduct
end
end
