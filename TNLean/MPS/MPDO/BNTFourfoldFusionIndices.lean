/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.BNTFinalSectorFusion

/-!
# Weighted coordinate spaces for fourfold fusion

The five parenthesizations of four labels give five finite weighted coordinate spaces at a fixed
final label. Their `Fin` factors come from the positive-diagonal matrices `Fam.chi`; they are
analogues of the categorical fusion-multiplicity indices in arXiv:1511.08090, not an
identification with them. This file records those spaces and the canonical coordinate
reassociations used along the three-edge and two-edge route patterns between the fully left- and
fully right-associated products.

For each edge, the source and target spaces are identified with a dependent sum in which one
factor is a weighted triple-fusion coordinate space and the remaining weighted index is
unchanged. These identifications do not identify the source and target coordinate spaces: that
change of basis belongs to the fusion comparison. The associated matrices below only permute
coordinates within each fixed parenthesization.

The same five parenthesizations also give five bond-coordinate types. Their edge equivalences are
ordinary reassociations of finite Cartesian products. The two composites between the extreme
parenthesizations are proved equal, together with the corresponding equality of coordinate-
permutation matrices.

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

/-! ### The five weighted coordinate spaces -/

/-- The weighted coordinate space for the parenthesization ((((\alpha\beta)\gamma)\delta)\)
with final label \(\varepsilon\).

Its tuples \((f,g,\mu,\nu,\rho)\) follow the index pattern for the successive fusions
\(\alpha\beta\to f\), \(f\gamma\to g\), and \(g\delta\to\varepsilon\). The `Fin` factors are
positive-diagonal weighted analogues; no equality with the categorical fusion multiplicities is
asserted.

Source: arXiv:1606.00608, Theorem IV.13(iii), lines 986--999; index pattern from
arXiv:1511.08090, `Papers/1511.08090/AnyonsPEPS.tex`, lines 279--299. -/
abbrev FourfoldLeftAssocMultiplicity (α β γ δ ε : Λ) : Type u :=
  (f : Λ) × (g : Λ) × Fin (Fam.chi.dim α β f) × Fin (Fam.chi.dim f γ g) ×
    Fin (Fam.chi.dim g δ ε)

/-- The weighted coordinate space for the parenthesization \(((\alpha(\beta\gamma))\delta)\)
with final label \(\varepsilon\).

Its tuples \((h,g,\sigma,\lambda,\rho)\) follow the index pattern for the successive fusions
\(\beta\gamma\to h\), \(\alpha h\to g\), and \(g\delta\to\varepsilon\). The `Fin` factors are
positive-diagonal weighted analogues; no equality with the categorical fusion multiplicities is
asserted.

Source: arXiv:1606.00608, Theorem IV.13(iii), lines 986--999; index pattern from
arXiv:1511.08090, `Papers/1511.08090/AnyonsPEPS.tex`, lines 279--299. -/
abbrev FourfoldLeftInnerMultiplicity (α β γ δ ε : Λ) : Type u :=
  (h : Λ) × (g : Λ) × Fin (Fam.chi.dim β γ h) × Fin (Fam.chi.dim α h g) ×
    Fin (Fam.chi.dim g δ ε)

/-- The weighted coordinate space for the parenthesization \(\alpha((\beta\gamma)\delta)\)
with final label \(\varepsilon\).

Its tuples \((h,i,\sigma,\omega,\kappa)\) follow the index pattern for the successive fusions
\(\beta\gamma\to h\), \(h\delta\to i\), and \(\alpha i\to\varepsilon\). The `Fin` factors are
positive-diagonal weighted analogues; no equality with the categorical fusion multiplicities is
asserted.

Source: arXiv:1606.00608, Theorem IV.13(iii), lines 986--999; index pattern from
arXiv:1511.08090, `Papers/1511.08090/AnyonsPEPS.tex`, lines 279--299. -/
abbrev FourfoldMiddleMultiplicity (α β γ δ ε : Λ) : Type u :=
  (h : Λ) × (i : Λ) × Fin (Fam.chi.dim β γ h) × Fin (Fam.chi.dim h δ i) ×
    Fin (Fam.chi.dim α i ε)

/-- The weighted coordinate space for the parenthesization \(\alpha(\beta(\gamma\delta))\)
with final label \(\varepsilon\).

Its tuples \((j,i,\gamma',\delta',\kappa)\) follow the index pattern for the successive fusions
\(\gamma\delta\to j\), \(\beta j\to i\), and \(\alpha i\to\varepsilon\). The `Fin` factors are
positive-diagonal weighted analogues; no equality with the categorical fusion multiplicities is
asserted.

Source: arXiv:1606.00608, Theorem IV.13(iii), lines 986--999; index pattern from
arXiv:1511.08090, `Papers/1511.08090/AnyonsPEPS.tex`, lines 279--299. -/
abbrev FourfoldRightAssocMultiplicity (α β γ δ ε : Λ) : Type u :=
  (j : Λ) × (i : Λ) × Fin (Fam.chi.dim γ δ j) × Fin (Fam.chi.dim β j i) ×
    Fin (Fam.chi.dim α i ε)

/-- The weighted coordinate space for the parenthesization \((\alpha\beta)(\gamma\delta)\)
with final label \(\varepsilon\).

Its tuples \((f,j,\mu,\gamma',\sigma)\) follow the index pattern for the successive fusions
\(\alpha\beta\to f\), \(\gamma\delta\to j\), and \(fj\to\varepsilon\). The `Fin` factors are
positive-diagonal weighted analogues; no equality with the categorical fusion multiplicities is
asserted.

Source: arXiv:1606.00608, Theorem IV.13(iii), lines 986--999; index pattern from
arXiv:1511.08090, `Papers/1511.08090/AnyonsPEPS.tex`, lines 279--299. -/
abbrev FourfoldPairMultiplicity (α β γ δ ε : Λ) : Type u :=
  (f : Λ) × (j : Λ) × Fin (Fam.chi.dim α β f) × Fin (Fam.chi.dim γ δ j) ×
    Fin (Fam.chi.dim f j ε)

/-! ### The three-edge route -/

/-- Reassociate the coordinates of \((((\alpha\beta)\gamma)\delta)\) so that the first
weighted triple-fusion coordinate space and the unchanged last weighted index are explicit.

Source: arXiv:1511.08090, `Papers/1511.08090/AnyonsPEPS.tex`, lines 279--299,
following only the route pattern of the first factor on the left-hand side of equation
`pentagoneq`. -/
def leftPathFirstSourceEquiv (α β γ δ ε : Λ) :
    Fam.FourfoldLeftAssocMultiplicity α β γ δ ε ≃
      (g : Λ) × Fam.LeftFinalMultiplicity α β γ g × Fin (Fam.chi.dim g δ ε) where
  toFun
    | ⟨f, g, μ, ν, ρ⟩ => ⟨g, ⟨f, μ, ν⟩, ρ⟩
  invFun
    | ⟨g, ⟨f, μ, ν⟩, ρ⟩ => ⟨f, g, μ, ν, ρ⟩
  left_inv x := by rcases x with ⟨f, g, μ, ν, ρ⟩; rfl
  right_inv x := by rcases x with ⟨g, ⟨f, μ, ν⟩, ρ⟩; rfl

/-- Reassociate the coordinates of \(((\alpha(\beta\gamma))\delta)\) so that the first
weighted triple-fusion coordinate space and the unchanged last weighted index are explicit.

Source: arXiv:1511.08090, `Papers/1511.08090/AnyonsPEPS.tex`, lines 279--299,
following only the route pattern of the first factor on the left-hand side of equation
`pentagoneq`. -/
def leftPathFirstTargetEquiv (α β γ δ ε : Λ) :
    Fam.FourfoldLeftInnerMultiplicity α β γ δ ε ≃
      (g : Λ) × Fam.RightFinalMultiplicity α β γ g × Fin (Fam.chi.dim g δ ε) where
  toFun
    | ⟨h, g, σ, l, ρ⟩ => ⟨g, ⟨h, σ, l⟩, ρ⟩
  invFun
    | ⟨g, ⟨h, σ, l⟩, ρ⟩ => ⟨h, g, σ, l, ρ⟩
  left_inv x := by rcases x with ⟨h, g, σ, l, ρ⟩; rfl
  right_inv x := by rcases x with ⟨g, ⟨h, σ, l⟩, ρ⟩; rfl

/-- Reassociate the coordinates of \(((\alpha(\beta\gamma))\delta)\) so that fusion of
\(\alpha,h,\delta\) is isolated, with the weighted \(\beta\gamma\to h\) index unchanged.

Source: arXiv:1511.08090, `Papers/1511.08090/AnyonsPEPS.tex`, lines 279--299,
following only the route pattern of the second factor on the left-hand side of equation
`pentagoneq`. -/
def leftPathSecondSourceEquiv (α β γ δ ε : Λ) :
    Fam.FourfoldLeftInnerMultiplicity α β γ δ ε ≃
      (h : Λ) × Fin (Fam.chi.dim β γ h) × Fam.LeftFinalMultiplicity α h δ ε where
  toFun
    | ⟨h, g, σ, l, ρ⟩ => ⟨h, σ, ⟨g, l, ρ⟩⟩
  invFun
    | ⟨h, σ, ⟨g, l, ρ⟩⟩ => ⟨h, g, σ, l, ρ⟩
  left_inv x := by rcases x with ⟨h, g, σ, l, ρ⟩; rfl
  right_inv x := by rcases x with ⟨h, σ, ⟨g, l, ρ⟩⟩; rfl

/-- Reassociate the coordinates of \(\alpha((\beta\gamma)\delta)\) so that fusion of
\(\alpha,h,\delta\) is isolated, with the weighted \(\beta\gamma\to h\) index unchanged.

Source: arXiv:1511.08090, `Papers/1511.08090/AnyonsPEPS.tex`, lines 279--299,
following only the route pattern of the second factor on the left-hand side of equation
`pentagoneq`. -/
def leftPathSecondTargetEquiv (α β γ δ ε : Λ) :
    Fam.FourfoldMiddleMultiplicity α β γ δ ε ≃
      (h : Λ) × Fin (Fam.chi.dim β γ h) × Fam.RightFinalMultiplicity α h δ ε where
  toFun
    | ⟨h, i, σ, ω, κ⟩ => ⟨h, σ, ⟨i, ω, κ⟩⟩
  invFun
    | ⟨h, σ, ⟨i, ω, κ⟩⟩ => ⟨h, i, σ, ω, κ⟩
  left_inv x := by rcases x with ⟨h, i, σ, ω, κ⟩; rfl
  right_inv x := by rcases x with ⟨h, σ, ⟨i, ω, κ⟩⟩; rfl

/-- Reassociate the coordinates of \(\alpha((\beta\gamma)\delta)\) so that fusion of
\(\beta,\gamma,\delta\) is isolated, with the weighted \(\alpha i\to\varepsilon\) index
unchanged.

Source: arXiv:1511.08090, `Papers/1511.08090/AnyonsPEPS.tex`, lines 279--299,
following only the route pattern of the third factor on the left-hand side of equation
`pentagoneq`. -/
def leftPathThirdSourceEquiv (α β γ δ ε : Λ) :
    Fam.FourfoldMiddleMultiplicity α β γ δ ε ≃
      (i : Λ) × Fam.LeftFinalMultiplicity β γ δ i × Fin (Fam.chi.dim α i ε) where
  toFun
    | ⟨h, i, σ, ω, κ⟩ => ⟨i, ⟨h, σ, ω⟩, κ⟩
  invFun
    | ⟨i, ⟨h, σ, ω⟩, κ⟩ => ⟨h, i, σ, ω, κ⟩
  left_inv x := by rcases x with ⟨h, i, σ, ω, κ⟩; rfl
  right_inv x := by rcases x with ⟨i, ⟨h, σ, ω⟩, κ⟩; rfl

/-- Reassociate the coordinates of \(\alpha(\beta(\gamma\delta))\) so that fusion of
\(\beta,\gamma,\delta\) is isolated, with the weighted \(\alpha i\to\varepsilon\) index
unchanged.

Source: arXiv:1511.08090, `Papers/1511.08090/AnyonsPEPS.tex`, lines 279--299,
following only the route pattern of the third factor on the left-hand side of equation
`pentagoneq`. -/
def leftPathThirdTargetEquiv (α β γ δ ε : Λ) :
    Fam.FourfoldRightAssocMultiplicity α β γ δ ε ≃
      (i : Λ) × Fam.RightFinalMultiplicity β γ δ i × Fin (Fam.chi.dim α i ε) where
  toFun
    | ⟨j, i, γ', δ', κ⟩ => ⟨i, ⟨j, γ', δ'⟩, κ⟩
  invFun
    | ⟨i, ⟨j, γ', δ'⟩, κ⟩ => ⟨j, i, γ', δ', κ⟩
  left_inv x := by rcases x with ⟨j, i, γ', δ', κ⟩; rfl
  right_inv x := by rcases x with ⟨i, ⟨j, γ', δ'⟩, κ⟩; rfl

/-! ### The two-edge route -/

/-- Reassociate the coordinates of \((((\alpha\beta)\gamma)\delta)\) so that fusion of
\(f,\gamma,\delta\) is isolated, with the weighted \(\alpha\beta\to f\) index unchanged.

Source: arXiv:1511.08090, `Papers/1511.08090/AnyonsPEPS.tex`, lines 279--299,
following only the route pattern of the first factor on the right-hand side of equation
`pentagoneq`. -/
def rightPathFirstSourceEquiv (α β γ δ ε : Λ) :
    Fam.FourfoldLeftAssocMultiplicity α β γ δ ε ≃
      (f : Λ) × Fin (Fam.chi.dim α β f) × Fam.LeftFinalMultiplicity f γ δ ε where
  toFun
    | ⟨f, g, μ, ν, ρ⟩ => ⟨f, μ, ⟨g, ν, ρ⟩⟩
  invFun
    | ⟨f, μ, ⟨g, ν, ρ⟩⟩ => ⟨f, g, μ, ν, ρ⟩
  left_inv x := by rcases x with ⟨f, g, μ, ν, ρ⟩; rfl
  right_inv x := by rcases x with ⟨f, μ, ⟨g, ν, ρ⟩⟩; rfl

/-- Reassociate the coordinates of \((\alpha\beta)(\gamma\delta)\) so that fusion of
\(f,\gamma,\delta\) is isolated, with the weighted \(\alpha\beta\to f\) index unchanged.

Source: arXiv:1511.08090, `Papers/1511.08090/AnyonsPEPS.tex`, lines 279--299,
following only the route pattern of the first factor on the right-hand side of equation
`pentagoneq`. -/
def rightPathFirstTargetEquiv (α β γ δ ε : Λ) :
    Fam.FourfoldPairMultiplicity α β γ δ ε ≃
      (f : Λ) × Fin (Fam.chi.dim α β f) × Fam.RightFinalMultiplicity f γ δ ε where
  toFun
    | ⟨f, j, μ, γ', σ⟩ => ⟨f, μ, ⟨j, γ', σ⟩⟩
  invFun
    | ⟨f, μ, ⟨j, γ', σ⟩⟩ => ⟨f, j, μ, γ', σ⟩
  left_inv x := by rcases x with ⟨f, j, μ, γ', σ⟩; rfl
  right_inv x := by rcases x with ⟨f, μ, ⟨j, γ', σ⟩⟩; rfl

/-- Reassociate the coordinates of \((\alpha\beta)(\gamma\delta)\) so that fusion of
\(\alpha,\beta,j\) is isolated, with the weighted \(\gamma\delta\to j\) index unchanged.

Source: arXiv:1511.08090, `Papers/1511.08090/AnyonsPEPS.tex`, lines 279--299,
following only the route pattern of the second factor on the right-hand side of equation
`pentagoneq`. -/
def rightPathSecondSourceEquiv (α β γ δ ε : Λ) :
    Fam.FourfoldPairMultiplicity α β γ δ ε ≃
      (j : Λ) × Fam.LeftFinalMultiplicity α β j ε × Fin (Fam.chi.dim γ δ j) where
  toFun
    | ⟨f, j, μ, γ', σ⟩ => ⟨j, ⟨f, μ, σ⟩, γ'⟩
  invFun
    | ⟨j, ⟨f, μ, σ⟩, γ'⟩ => ⟨f, j, μ, γ', σ⟩
  left_inv x := by rcases x with ⟨f, j, μ, γ', σ⟩; rfl
  right_inv x := by rcases x with ⟨j, ⟨f, μ, σ⟩, γ'⟩; rfl

/-- Reassociate the coordinates of \(\alpha(\beta(\gamma\delta))\) so that fusion of
\(\alpha,\beta,j\) is isolated, with the weighted \(\gamma\delta\to j\) index unchanged.

Source: arXiv:1511.08090, `Papers/1511.08090/AnyonsPEPS.tex`, lines 279--299,
following only the route pattern of the second factor on the right-hand side of equation
`pentagoneq`. -/
def rightPathSecondTargetEquiv (α β γ δ ε : Λ) :
    Fam.FourfoldRightAssocMultiplicity α β γ δ ε ≃
      (j : Λ) × Fam.RightFinalMultiplicity α β j ε × Fin (Fam.chi.dim γ δ j) where
  toFun
    | ⟨j, i, γ', δ', κ⟩ => ⟨j, ⟨i, δ', κ⟩, γ'⟩
  invFun
    | ⟨j, ⟨i, δ', κ⟩, γ'⟩ => ⟨j, i, γ', δ', κ⟩
  left_inv x := by rcases x with ⟨j, i, γ', δ', κ⟩; rfl
  right_inv x := by rcases x with ⟨j, ⟨i, δ', κ⟩, γ'⟩; rfl

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
