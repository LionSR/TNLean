/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.FNWLowerBoundary

/-!
# FNW overlap coordinates

This module begins the source-coordinate proof of Fannes--Nachtergaele--Werner,
*Communications in Mathematical Physics* 144 (1992), 443--490, Lemma 6.2.
The common physical chain is split into consecutive blocks of lengths
\(\ell,m,r\). The left overlap family applies the boundary map \(F_{\ell+m}\)
to a rho-weighted matrix family indexed by the right block, while the right
overlap family applies \(F_{m+r}\) to a rho-weighted matrix family indexed by
the left block.

The virtual convention is \(A^\mu=v(\mu)^\dagger\). Thus the aggregate matrices
have the source orientation
\[
  A_\varphi=\sum_{\mu^r}\Phi(\mu^r)\rho v(\mu^r)\rho^{-1},\qquad
  A_\psi=\sum_{\mu^\ell}v(\mu^\ell)\Psi(\mu^\ell).
\]

This file keeps the linear contribution in FNW equation (6.5) separate. It does
not assert the final projector-defect estimate or introduce its quadratic term.
-/

open scoped BigOperators ComplexOrder Matrix

namespace MPSTensor

noncomputable section

variable {d D : ℕ}

local notation "Mat" => Matrix (Fin D) (Fin D) ℂ

/-- The rho-weighted Hilbert direct sum of virtual matrices indexed by a finite
spectator configuration space. The matrix norm and inner product are supplied
locally by `Matrix.toMatrixNormedAddCommGroup` and
`Matrix.toMatrixInnerProductSpace`. -/
abbrev FNWBoundaryFamilySpace (S : Type*) [Fintype S] :=
  PiLp 2 fun _ : S => Mat

/-- Three consecutive physical configuration blocks, with the left and middle
blocks grouped before appending the right block. -/
def fnwThreeBlockConfigEquiv (d ℓ m r : ℕ) :
    (Cfg d ℓ × Cfg d m) × Cfg d r ≃ Cfg d ((ℓ + m) + r) :=
  (Equiv.prodCongr (Fin.appendEquiv ℓ m) (Equiv.refl (Cfg d r))).trans
    (Fin.appendEquiv (ℓ + m) r)

@[simp]
theorem fnwThreeBlockConfigEquiv_apply
    (d ℓ m r : ℕ) (μℓ : Cfg d ℓ) (μm : Cfg d m) (μr : Cfg d r) :
    fnwThreeBlockConfigEquiv d ℓ m r ((μℓ, μm), μr) =
      Fin.append (Fin.append μℓ μm) μr := by
  rfl

@[simp]
theorem fnwThreeBlockConfigEquiv_symm_apply_apply
    (d ℓ m r : ℕ) (μℓ : Cfg d ℓ) (μm : Cfg d m) (μr : Cfg d r) :
    (fnwThreeBlockConfigEquiv d ℓ m r).symm
      (Fin.append (Fin.append μℓ μm) μr) = ((μℓ, μm), μr) := by
  exact (fnwThreeBlockConfigEquiv d ℓ m r).symm_apply_apply ((μℓ, μm), μr)

/-- The left overlap family in FNW Lemma 6.2. For fixed right spectator
\(\mu^r\), its coefficient on the first two blocks is
\(F_{\ell+m}(\Phi(\mu^r))\). -/
noncomputable def fnwLeftOverlapMap
    (ρ : Mat) (hρ : ρ.PosDef) (A : MPSTensor d D) (ℓ m r : ℕ) :
    letI : NormedAddCommGroup Mat := Matrix.toMatrixNormedAddCommGroup ρ hρ
    letI : SeminormedAddCommGroup Mat :=
      (Matrix.toMatrixNormedAddCommGroup ρ hρ).toSeminormedAddCommGroup
    letI : InnerProductSpace ℂ Mat :=
      Matrix.toMatrixInnerProductSpace ρ hρ.posSemidef
    FNWBoundaryFamilySpace (D := D) (Cfg d r) →ₗ[ℂ]
      EuclideanSpace ℂ (Cfg d ((ℓ + m) + r)) := by
  let : NormedAddCommGroup Mat := Matrix.toMatrixNormedAddCommGroup ρ hρ
  let : SeminormedAddCommGroup Mat :=
    (Matrix.toMatrixNormedAddCommGroup ρ hρ).toSeminormedAddCommGroup
  let : InnerProductSpace ℂ Mat :=
    Matrix.toMatrixInnerProductSpace ρ hρ.posSemidef
  exact
    { toFun := fun Φ => WithLp.toLp 2 fun σ =>
        let blocks := (fnwThreeBlockConfigEquiv d ℓ m r).symm σ
        fnwBoundaryMapCLM ρ hρ A (ℓ + m) (Φ.ofLp blocks.2)
          (Fin.append blocks.1.1 blocks.1.2)
      map_add' := by
        intro Φ Ψ
        apply PiLp.ext
        intro σ
        simp
      map_smul' := by
        intro c Φ
        apply PiLp.ext
        intro σ
        simp }

/-- The right overlap family in FNW Lemma 6.2. For fixed left spectator
\(\mu^\ell\), its coefficient on the final two blocks is
\(F_{m+r}(\Psi(\mu^\ell))\). -/
noncomputable def fnwRightOverlapMap
    (ρ : Mat) (hρ : ρ.PosDef) (A : MPSTensor d D) (ℓ m r : ℕ) :
    letI : NormedAddCommGroup Mat := Matrix.toMatrixNormedAddCommGroup ρ hρ
    letI : SeminormedAddCommGroup Mat :=
      (Matrix.toMatrixNormedAddCommGroup ρ hρ).toSeminormedAddCommGroup
    letI : InnerProductSpace ℂ Mat :=
      Matrix.toMatrixInnerProductSpace ρ hρ.posSemidef
    FNWBoundaryFamilySpace (D := D) (Cfg d ℓ) →ₗ[ℂ]
      EuclideanSpace ℂ (Cfg d ((ℓ + m) + r)) := by
  let : NormedAddCommGroup Mat := Matrix.toMatrixNormedAddCommGroup ρ hρ
  let : SeminormedAddCommGroup Mat :=
    (Matrix.toMatrixNormedAddCommGroup ρ hρ).toSeminormedAddCommGroup
  let : InnerProductSpace ℂ Mat :=
    Matrix.toMatrixInnerProductSpace ρ hρ.posSemidef
  exact
    { toFun := fun Ψ => WithLp.toLp 2 fun σ =>
        let blocks := (fnwThreeBlockConfigEquiv d ℓ m r).symm σ
        fnwBoundaryMapCLM ρ hρ A (m + r) (Ψ.ofLp blocks.1.1)
          (Fin.append blocks.1.2 blocks.2)
      map_add' := by
        intro Φ Ψ
        apply PiLp.ext
        intro σ
        simp
      map_smul' := by
        intro c Φ
        apply PiLp.ext
        intro σ
        simp }

@[simp]
theorem fnwLeftOverlapMap_apply_append
    (ρ : Mat) (hρ : ρ.PosDef) (A : MPSTensor d D) (ℓ m r : ℕ)
    (Φ : FNWBoundaryFamilySpace (D := D) (Cfg d r))
    (μℓ : Cfg d ℓ) (μm : Cfg d m) (μr : Cfg d r) :
    letI : NormedAddCommGroup Mat := Matrix.toMatrixNormedAddCommGroup ρ hρ
    letI : SeminormedAddCommGroup Mat :=
      (Matrix.toMatrixNormedAddCommGroup ρ hρ).toSeminormedAddCommGroup
    letI : InnerProductSpace ℂ Mat :=
      Matrix.toMatrixInnerProductSpace ρ hρ.posSemidef
    fnwLeftOverlapMap ρ hρ A ℓ m r Φ (Fin.append (Fin.append μℓ μm) μr) =
      fnwBoundaryMapCLM ρ hρ A (ℓ + m) (Φ.ofLp μr) (Fin.append μℓ μm) := by
  let : NormedAddCommGroup Mat := Matrix.toMatrixNormedAddCommGroup ρ hρ
  let : SeminormedAddCommGroup Mat :=
    (Matrix.toMatrixNormedAddCommGroup ρ hρ).toSeminormedAddCommGroup
  let : InnerProductSpace ℂ Mat :=
    Matrix.toMatrixInnerProductSpace ρ hρ.posSemidef
  simp [fnwLeftOverlapMap]

@[simp]
theorem fnwRightOverlapMap_apply_append
    (ρ : Mat) (hρ : ρ.PosDef) (A : MPSTensor d D) (ℓ m r : ℕ)
    (Ψ : FNWBoundaryFamilySpace (D := D) (Cfg d ℓ))
    (μℓ : Cfg d ℓ) (μm : Cfg d m) (μr : Cfg d r) :
    letI : NormedAddCommGroup Mat := Matrix.toMatrixNormedAddCommGroup ρ hρ
    letI : SeminormedAddCommGroup Mat :=
      (Matrix.toMatrixNormedAddCommGroup ρ hρ).toSeminormedAddCommGroup
    letI : InnerProductSpace ℂ Mat :=
      Matrix.toMatrixInnerProductSpace ρ hρ.posSemidef
    fnwRightOverlapMap ρ hρ A ℓ m r Ψ (Fin.append (Fin.append μℓ μm) μr) =
      fnwBoundaryMapCLM ρ hρ A (m + r) (Ψ.ofLp μℓ) (Fin.append μm μr) := by
  let : NormedAddCommGroup Mat := Matrix.toMatrixNormedAddCommGroup ρ hρ
  let : SeminormedAddCommGroup Mat :=
    (Matrix.toMatrixNormedAddCommGroup ρ hρ).toSeminormedAddCommGroup
  let : InnerProductSpace ℂ Mat :=
    Matrix.toMatrixInnerProductSpace ρ hρ.posSemidef
  simp [fnwRightOverlapMap]

/-- The aggregate matrix \(A_\varphi\) in FNW Lemma 6.2, with source order
\(\Phi(\mu^r)\rho v(\mu^r)\rho^{-1}\). -/
noncomputable def fnwLeftOverlapAggregate
    (ρ : Mat) (A : MPSTensor d D) (r : ℕ)
    (Φ : FNWBoundaryFamilySpace (D := D) (Cfg d r)) : Mat :=
  ∑ μr : Cfg d r, Φ.ofLp μr * ρ *
    Kraus.evalWord (fun μ => (A μ)ᴴ) (List.ofFn μr) * ρ⁻¹

/-- The aggregate matrix \(A_\psi\) in FNW Lemma 6.2, with source order
\(v(\mu^\ell)\Psi(\mu^\ell)\). -/
noncomputable def fnwRightOverlapAggregate
    (A : MPSTensor d D) (ℓ : ℕ)
    (Ψ : FNWBoundaryFamilySpace (D := D) (Cfg d ℓ)) : Mat :=
  ∑ μℓ : Cfg d ℓ,
    Kraus.evalWord (fun μ => (A μ)ᴴ) (List.ofFn μℓ) * Ψ.ofLp μℓ

end

end MPSTensor
