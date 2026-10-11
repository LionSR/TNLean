/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.StationarySupportCompression
import TNLean.MPS.ParentHamiltonian.LocalDensitySupport
import TNLean.MPS.Core.IsometricBondCompression

/-!
# Local supports of stationary generating data

Let \(A\) be a tensor and let \(\rho \ge 0\) be a nonzero stationary virtual matrix,
\(\sum_i A_i \rho A_i^* = \rho\). The matrix \(\rho\) need not be faithful. Its
support projection \(P\) is invariant under the letters, so restricting the
boundary matrices of \(A\) to the corner \(P M_D P\) gives a subspace of the
open-boundary space. This subspace is exactly the support of the finite
local functionals determined by \((A, \rho)\): a square observable \(X^* X\) has
zero expectation iff \(X\) annihilates it, and when \(A\) is left canonical the
representing finite densities have this subspace as their range.

The proof compresses \((A, \rho)\) to faithful generating data on the support of
\(\rho\) and applies the faithful support theorems. When \(\rho\) is faithful the
corner is the whole matrix algebra and the subspace is the full
open-boundary space.

Source: Nachtergaele, arXiv:cond-mat/9410110, Section 3, equations
(3.1)--(3.5) and (defEA), lines 1398--1450, for normalized stationary
generating data,
and Section 4, lines 1724--1738, where the local support spaces are spanned
by boundary vectors of faithful generating data.

**Scope restriction (normalized stationary generating data):** The tensor
and stationary matrix are supplied. The passage from an arbitrary boundary
limit (1.1) to normalized stationary data, which the source takes from
Fannes--Nachtergaele--Werner (lines 1411--1414), and the minimality
condition of lines 1457--1467 are not formalized here; see
docs/paper-gaps/nachtergaele96_infinite_volume_ground_projection.tex.
-/

open scoped Matrix ComplexOrder
namespace MPSTensor
variable {d D E k : ℕ}

/-- The open-boundary vectors of \(A\) on \(L\) sites whose boundary matrices lie in
the corner \(P M_D P\), as a subspace of the Euclidean configuration space.
For a support projection this is the local support space of
Nachtergaele, arXiv:cond-mat/9410110, lines 1724--1738. -/
noncomputable def cornerGroundSpaceES (A : MPSTensor d D)
    (P : Matrix (Fin D) (Fin D) ℂ) (L : ℕ) :
    Submodule ℂ (EuclideanSpace ℂ (Cfg d L)) :=
  ((cornerSubmodule P).map (groundSpaceMap A L)).map
    (WithLp.linearEquiv 2 ℂ (NSiteSpace d L)).symm.toLinearMap

/-- The corner of the identity gives the full open-boundary space. -/
theorem cornerGroundSpaceES_one (A : MPSTensor d D) (L : ℕ) :
    cornerGroundSpaceES A 1 L = groundSpaceES A L := by
  have hTop : cornerSubmodule (1 : Matrix (Fin D) (Fin D) ℂ) = ⊤ :=
    eq_top_iff.mpr fun X _ => by
      change (1 : Matrix (Fin D) (Fin D) ℂ) * X * 1 = X
      rw [Matrix.one_mul, Matrix.mul_one]
  rw [cornerGroundSpaceES, hTop, Submodule.map_top]
  rfl

/-- Under an isometric letter intertwiner \(A_i V = V B_i\), the open-boundary
space of \(B\) is the image of the corner \((V V^*) M_D (V V^*)\) under the boundary map
of \(A\). Source context: Nachtergaele, arXiv:cond-mat/9410110, lines 1724--1738,
the spanning vectors of the local support spaces. -/
theorem groundSpace_eq_map_cornerSubmodule_of_isometric_bond_intertwiner
    (A : MPSTensor d D) (B : MPSTensor d E)
    (V : Matrix (Fin D) (Fin E) ℂ) (hV : Vᴴ * V = 1)
    (hInt : ∀ i, A i * V = V * B i) (L : ℕ) :
    groundSpace B L = (cornerSubmodule (V * Vᴴ)).map (groundSpaceMap A L) := by
  apply le_antisymm
  · rintro _ ⟨X, rfl⟩
    refine ⟨V * X * Vᴴ, ?_, groundSpaceMap_eq_of_isometric_bond_intertwiner A B V hV hInt L X⟩
    change V * Vᴴ * (V * X * Vᴴ) * (V * Vᴴ) = V * X * Vᴴ
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Vᴴ V, hV, Matrix.one_mul, ← Matrix.mul_assoc Vᴴ V, hV,
      Matrix.one_mul]
  · rintro _ ⟨Y, hY, rfl⟩
    refine ⟨Vᴴ * Y * V, ?_⟩
    rw [← groundSpaceMap_eq_of_isometric_bond_intertwiner A B V hV hInt L]
    congr 1
    calc
      V * (Vᴴ * Y * V) * Vᴴ = V * Vᴴ * Y * (V * Vᴴ) := by simp only [Matrix.mul_assoc]
      _ = Y := hY

/-- Euclidean form of
`groundSpace_eq_map_cornerSubmodule_of_isometric_bond_intertwiner`. -/
theorem groundSpaceES_eq_cornerGroundSpaceES_of_isometric_bond_intertwiner
    (A : MPSTensor d D) (B : MPSTensor d E)
    (V : Matrix (Fin D) (Fin E) ℂ) (hV : Vᴴ * V = 1)
    (hInt : ∀ i, A i * V = V * B i) (L : ℕ) :
    groundSpaceES B L = cornerGroundSpaceES A (V * Vᴴ) L := by
  rw [groundSpaceES, cornerGroundSpaceES,
    groundSpace_eq_map_cornerSubmodule_of_isometric_bond_intertwiner A B V hV hInt L]

/-- For a nonzero positive stationary virtual matrix \(\rho\), which need not be
faithful, a square observable has zero insertion expectation iff its factor
annihilates the open-boundary vectors with boundary matrices in the support
corner of \(\rho\). No tensor normalization is required.
Source: Nachtergaele, arXiv:cond-mat/9410110, lines 1724--1738, the local
support spaces of stationary generating data. -/
theorem observableInsertionExpectation_conjTranspose_mul_self_eq_zero_iff_of_stationary
    (A : MPSTensor d D) {ρ : Matrix (Fin D) (Fin D) ℂ} (hρ : ρ.PosSemidef)
    (htr : Matrix.trace ρ ≠ 0) (hFix : Kraus.map A ρ = ρ)
    (X : Matrix (Cfg d k) (Cfg d k) ℂ) :
    observableInsertionExpectation A ρ (Xᴴ * X) = 0 ↔
      cornerGroundSpaceES A hρ.supportProj k ≤ LinearMap.ker (Matrix.toEuclideanLin X) := by
  obtain ⟨E, hE, V, B, σ, hV, hVrange, -, -, hσ, hInt, -, -, hObs⟩ :=
    exists_faithful_stationary_supportCompression A hρ htr hFix
  have : NeZero E := ⟨hE.ne'⟩
  rw [hObs, observableInsertionExpectation_conjTranspose_mul_self_eq_zero_iff B hσ X,
    groundSpaceES_eq_cornerGroundSpaceES_of_isometric_bond_intertwiner A B V hV hInt,
    hVrange]

/-- A left-canonical tensor and a nonzero positive stationary virtual matrix,
which need not be faithful, have positive normalized finite densities whose
ranges are the open-boundary vectors with boundary matrices in the support
corner of the stationary matrix. Intervals of length zero are included.
Source: Nachtergaele, arXiv:cond-mat/9410110, equations (3.1)--(3.5) and
lines 1724--1738, the local support spaces of normalized generating data. -/
theorem exists_local_density_range_eq_cornerGroundSpaceES_of_stationary
    (A : MPSTensor d D) (hA : IsLeftCanonical A)
    {ρ : Matrix (Fin D) (Fin D) ℂ} (hρ : ρ.PosSemidef)
    (htr : Matrix.trace ρ ≠ 0) (hFix : Kraus.map A ρ = ρ) (k : ℕ) :
    ∃ σ : Matrix (Cfg d k) (Cfg d k) ℂ, σ.PosSemidef ∧ Matrix.trace σ = 1 ∧
      (∀ X, observableInsertionExpectation A ρ X = Matrix.trace (σ * X)) ∧
      LinearMap.range (Matrix.toEuclideanLin σ) = cornerGroundSpaceES A hρ.supportProj k := by
  obtain ⟨E, hE, V, B, τ, hV, hVrange, -, -, hτ, hB, hInt, -, -, hObs⟩ :=
    exists_faithful_stationary_supportCompression_of_leftCanonical A hA hρ htr hFix
  have : NeZero E := ⟨hE.ne'⟩
  obtain ⟨σ, hσ, hσtr, hrep, hrange⟩ := exists_local_density_range_eq_groundSpaceES B hB hτ k
  refine ⟨σ, hσ, hσtr, fun X => (hObs k X).trans (hrep X), ?_⟩
  rw [hrange, groundSpaceES_eq_cornerGroundSpaceES_of_isometric_bond_intertwiner A B V hV hInt,
    hVrange]

end MPSTensor
