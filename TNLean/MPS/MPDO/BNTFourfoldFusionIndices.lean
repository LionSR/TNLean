/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.BNTFusionIsometries

/-!
# Reassociation of four bond coordinates

The five parenthesizations of four labels give five bond-coordinate types. Their edge
equivalences are ordinary reassociations of finite Cartesian products. The two composites
between the extreme parenthesizations are proved equal, together with the corresponding
equality of coordinate-permutation matrices.

References below to factors in the printed pentagon record only the pattern of labels and
indices. No comparison matrix between different parenthesizations is defined here, no equality
with the source's categorical multiplicities is asserted, and no pentagon identity is asserted.

## References

* [Bultinck--Marien--Williamson--Sahinoglu--Haegeman--Verstraete 2015]
  arXiv:1511.08090, `Papers/1511.08090/AnyonsPEPS.tex`, lines 279--299
-/

open Matrix

namespace MPOTensor.BNTFusionIsometryFamily

universe u

variable {Λ : Type u} [Fintype Λ] [DecidableEq Λ] {p : ℕ}
variable (Fam : BNTFusionIsometryFamily Λ p)

/-! ### Reassociation of four bond coordinates -/

/-- The bond-coordinate type for \((((\alpha\beta)\gamma)\delta)\).

Source: arXiv:1511.08090, `Papers/1511.08090/AnyonsPEPS.tex`, lines 279--299. -/
abbrev FourfoldLeftAssocBondIndex (α β γ δ : Λ) : Type :=
  Fin (((Fam.bondDim α * Fam.bondDim β) * Fam.bondDim γ) * Fam.bondDim δ)

/-- The bond-coordinate type for \(((\alpha(\beta\gamma))\delta)\).

Source: arXiv:1511.08090, `Papers/1511.08090/AnyonsPEPS.tex`, lines 279--299. -/
abbrev FourfoldLeftInnerBondIndex (α β γ δ : Λ) : Type :=
  Fin ((Fam.bondDim α * (Fam.bondDim β * Fam.bondDim γ)) * Fam.bondDim δ)

/-- The bond-coordinate type for \(\alpha((\beta\gamma)\delta)\).

Source: arXiv:1511.08090, `Papers/1511.08090/AnyonsPEPS.tex`, lines 279--299. -/
abbrev FourfoldMiddleBondIndex (α β γ δ : Λ) : Type :=
  Fin (Fam.bondDim α * ((Fam.bondDim β * Fam.bondDim γ) * Fam.bondDim δ))

/-- The bond-coordinate type for \(\alpha(\beta(\gamma\delta))\).

Source: arXiv:1511.08090, `Papers/1511.08090/AnyonsPEPS.tex`, lines 279--299. -/
abbrev FourfoldRightAssocBondIndex (α β γ δ : Λ) : Type :=
  Fin (Fam.bondDim α * (Fam.bondDim β * (Fam.bondDim γ * Fam.bondDim δ)))

/-- The bond-coordinate type for \((\alpha\beta)(\gamma\delta)\).

Source: arXiv:1511.08090, `Papers/1511.08090/AnyonsPEPS.tex`, lines 279--299. -/
abbrev FourfoldPairBondIndex (α β γ δ : Λ) : Type :=
  Fin ((Fam.bondDim α * Fam.bondDim β) * (Fam.bondDim γ * Fam.bondDim δ))

/-- Reassociate the first three bond coordinates while leaving the fourth coordinate fixed.

Source: arXiv:1511.08090, `Papers/1511.08090/AnyonsPEPS.tex`, lines 279--299,
the first edge of the three-edge route. -/
def fourfoldLeftAssocToLeftInnerBondEquiv (α β γ δ : Λ) :
    Fam.FourfoldLeftAssocBondIndex α β γ δ ≃
      Fam.FourfoldLeftInnerBondIndex α β γ δ :=
  finProdFinEquiv.symm |>.trans
    ((Equiv.prodCongr
      (mulTensorAssocEquiv (Fam.bondDim α) (Fam.bondDim β) (Fam.bondDim γ))
      (Equiv.refl (Fin (Fam.bondDim δ)))).trans finProdFinEquiv)

/-- Reassociate the three factors \(\alpha,(\beta\gamma),\delta\).

Source: arXiv:1511.08090, `Papers/1511.08090/AnyonsPEPS.tex`, lines 279--299,
the second edge of the three-edge route. -/
def fourfoldLeftInnerToMiddleBondEquiv (α β γ δ : Λ) :
    Fam.FourfoldLeftInnerBondIndex α β γ δ ≃ Fam.FourfoldMiddleBondIndex α β γ δ :=
  mulTensorAssocEquiv (Fam.bondDim α)
    (Fam.bondDim β * Fam.bondDim γ) (Fam.bondDim δ)

/-- Reassociate the last three bond coordinates while leaving the first coordinate fixed.

Source: arXiv:1511.08090, `Papers/1511.08090/AnyonsPEPS.tex`, lines 279--299,
the third edge of the three-edge route. -/
def fourfoldMiddleToRightAssocBondEquiv (α β γ δ : Λ) :
    Fam.FourfoldMiddleBondIndex α β γ δ ≃ Fam.FourfoldRightAssocBondIndex α β γ δ :=
  finProdFinEquiv.symm |>.trans
    ((Equiv.prodCongr (Equiv.refl (Fin (Fam.bondDim α)))
      (mulTensorAssocEquiv (Fam.bondDim β) (Fam.bondDim γ) (Fam.bondDim δ))).trans
        finProdFinEquiv)

/-- Reassociate the factors \((\alpha\beta),\gamma,\delta\).

Source: arXiv:1511.08090, `Papers/1511.08090/AnyonsPEPS.tex`, lines 279--299,
the first edge of the two-edge route. -/
def fourfoldLeftAssocToPairBondEquiv (α β γ δ : Λ) :
    Fam.FourfoldLeftAssocBondIndex α β γ δ ≃ Fam.FourfoldPairBondIndex α β γ δ :=
  mulTensorAssocEquiv (Fam.bondDim α * Fam.bondDim β)
    (Fam.bondDim γ) (Fam.bondDim δ)

/-- Reassociate the factors \(\alpha,\beta,(\gamma\delta)\).

Source: arXiv:1511.08090, `Papers/1511.08090/AnyonsPEPS.tex`, lines 279--299,
the second edge of the two-edge route. -/
def fourfoldPairToRightAssocBondEquiv (α β γ δ : Λ) :
    Fam.FourfoldPairBondIndex α β γ δ ≃ Fam.FourfoldRightAssocBondIndex α β γ δ :=
  mulTensorAssocEquiv (Fam.bondDim α) (Fam.bondDim β)
    (Fam.bondDim γ * Fam.bondDim δ)

/-- The two finite-coordinate reassociations from the fully left-associated bond space to the
fully right-associated bond space coincide.

This is coherence of ordinary Cartesian-product reassociation. It does not compare fusion
multiplicity spaces and does not assert the source's equation `pentagoneq`.

Source: arXiv:1511.08090, `Papers/1511.08090/AnyonsPEPS.tex`, lines 279--299,
applied only to the four bond-coordinate factors. -/
theorem fourfoldBondReassociation_threeEdge_eq_twoEdge (α β γ δ : Λ) :
    ((Fam.fourfoldLeftAssocToLeftInnerBondEquiv α β γ δ).trans
      (Fam.fourfoldLeftInnerToMiddleBondEquiv α β γ δ)).trans
        (Fam.fourfoldMiddleToRightAssocBondEquiv α β γ δ) =
      (Fam.fourfoldLeftAssocToPairBondEquiv α β γ δ).trans
        (Fam.fourfoldPairToRightAssocBondEquiv α β γ δ) := by
  apply Equiv.ext
  intro x
  rcases finProdFinEquiv.surjective x with ⟨⟨xabc, xd⟩, rfl⟩
  rcases finProdFinEquiv.surjective xabc with ⟨⟨xab, xc⟩, rfl⟩
  rcases finProdFinEquiv.surjective xab with ⟨⟨xa, xb⟩, rfl⟩
  simp [fourfoldLeftAssocToLeftInnerBondEquiv, fourfoldLeftInnerToMiddleBondEquiv,
    fourfoldMiddleToRightAssocBondEquiv, fourfoldLeftAssocToPairBondEquiv,
    fourfoldPairToRightAssocBondEquiv, mulTensorAssocEquiv]

/-- The coordinate-permutation matrix for the first edge of the three-edge bond reassociation.

Source: arXiv:1511.08090, `Papers/1511.08090/AnyonsPEPS.tex`, lines 279--299. -/
noncomputable def fourfoldLeftAssocToLeftInnerBondMatrix (α β γ δ : Λ) :
    Matrix (Fam.FourfoldLeftAssocBondIndex α β γ δ)
      (Fam.FourfoldLeftInnerBondIndex α β γ δ) ℂ :=
  (Fam.fourfoldLeftAssocToLeftInnerBondEquiv α β γ δ).toPEquiv.toMatrix

/-- The coordinate-permutation matrix for the second edge of the three-edge bond reassociation.

Source: arXiv:1511.08090, `Papers/1511.08090/AnyonsPEPS.tex`, lines 279--299. -/
noncomputable def fourfoldLeftInnerToMiddleBondMatrix (α β γ δ : Λ) :
    Matrix (Fam.FourfoldLeftInnerBondIndex α β γ δ)
      (Fam.FourfoldMiddleBondIndex α β γ δ) ℂ :=
  (Fam.fourfoldLeftInnerToMiddleBondEquiv α β γ δ).toPEquiv.toMatrix

/-- The coordinate-permutation matrix for the third edge of the three-edge bond reassociation.

Source: arXiv:1511.08090, `Papers/1511.08090/AnyonsPEPS.tex`, lines 279--299. -/
noncomputable def fourfoldMiddleToRightAssocBondMatrix (α β γ δ : Λ) :
    Matrix (Fam.FourfoldMiddleBondIndex α β γ δ)
      (Fam.FourfoldRightAssocBondIndex α β γ δ) ℂ :=
  (Fam.fourfoldMiddleToRightAssocBondEquiv α β γ δ).toPEquiv.toMatrix

/-- The coordinate-permutation matrix for the first edge of the two-edge bond reassociation.

Source: arXiv:1511.08090, `Papers/1511.08090/AnyonsPEPS.tex`, lines 279--299. -/
noncomputable def fourfoldLeftAssocToPairBondMatrix (α β γ δ : Λ) :
    Matrix (Fam.FourfoldLeftAssocBondIndex α β γ δ)
      (Fam.FourfoldPairBondIndex α β γ δ) ℂ :=
  (Fam.fourfoldLeftAssocToPairBondEquiv α β γ δ).toPEquiv.toMatrix

/-- The coordinate-permutation matrix for the second edge of the two-edge bond reassociation.

Source: arXiv:1511.08090, `Papers/1511.08090/AnyonsPEPS.tex`, lines 279--299. -/
noncomputable def fourfoldPairToRightAssocBondMatrix (α β γ δ : Λ) :
    Matrix (Fam.FourfoldPairBondIndex α β γ δ)
      (Fam.FourfoldRightAssocBondIndex α β γ δ) ℂ :=
  (Fam.fourfoldPairToRightAssocBondEquiv α β γ δ).toPEquiv.toMatrix

/-- The product of the three coordinate-permutation matrices equals the product of the two
coordinate-permutation matrices between the same extreme bond parenthesizations.

This is the matrix form of `fourfoldBondReassociation_threeEdge_eq_twoEdge`; it makes no
statement about fusion comparison matrices.

Source: arXiv:1511.08090, `Papers/1511.08090/AnyonsPEPS.tex`, lines 279--299,
applied only to the four bond-coordinate factors. -/
theorem fourfoldBondMatrix_threeEdge_eq_twoEdge (α β γ δ : Λ) :
    (Fam.fourfoldLeftAssocToLeftInnerBondMatrix α β γ δ *
        Fam.fourfoldLeftInnerToMiddleBondMatrix α β γ δ) *
      Fam.fourfoldMiddleToRightAssocBondMatrix α β γ δ =
    Fam.fourfoldLeftAssocToPairBondMatrix α β γ δ *
      Fam.fourfoldPairToRightAssocBondMatrix α β γ δ := by
  unfold fourfoldLeftAssocToLeftInnerBondMatrix fourfoldLeftInnerToMiddleBondMatrix
    fourfoldMiddleToRightAssocBondMatrix fourfoldLeftAssocToPairBondMatrix
    fourfoldPairToRightAssocBondMatrix
  rw [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans,
    ← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans,
    ← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans]
  rw [Fam.fourfoldBondReassociation_threeEdge_eq_twoEdge]

end MPOTensor.BNTFusionIsometryFamily
