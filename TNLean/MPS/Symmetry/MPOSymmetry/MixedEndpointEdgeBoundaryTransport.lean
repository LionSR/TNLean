/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.MPOSymmetry.MixedEndpointActiveBoundaryTransport

/-!
# Actual first- and last-edge supports in common-core coordinates

The first edge has one arbitrary outer spectator, one exposed inner bond
register, and one ordinary `A₀` physical letter. Normalizing only its first
site turns its actual boundary coefficient into `(A₀(q) Y)(b,a)`, where
`Y` is an arbitrary rectangular boundary. The last edge has the reflected
formula `(Y A₀(q))(e,c)`.

These are local support identities for the actual extended interaction.
Their rectangular boundaries are extracted from the original boundary
matrix, and the extraction maps are surjective. No many-body kernel or
spectral estimate is assumed. Source: arXiv:2203.12563, Section 5,
lines 1690–1692.
-/

open scoped Matrix BigOperators

namespace MPSTensor
namespace MPOSymmetry

noncomputable section

variable {D₀ D₁ : ℕ}

/-- Active first-edge coordinates: first boundary letter and one bulk letter.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
abbrev endpointFirstEdgeCfg (ι : Type*) (D : ℕ) := (ι × Fin D) × Fin (D * D)

/-- Active last-edge coordinates: one bulk letter and the last boundary letter.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
abbrev endpointLastEdgeCfg (ι : Type*) (D : ℕ) := Fin (D * D) × (Fin D × ι)

/-- The common first-edge support with an arbitrary exterior index type.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
def endpointFirstEdgeCoreMap (A₀ : MPSTensor (D₀ * D₀) D₀) (ι : Type*) :
    Matrix (Fin D₀) ι ℂ →ₗ[ℂ] (endpointFirstEdgeCfg ι D₀ → ℂ) where
  toFun Y := fun ((a, b), q) => (A₀ q * Y) b a
  map_add' Y Z := by ext ⟨⟨a, b⟩, q⟩; simp [Matrix.mul_add]
  map_smul' z Y := by ext ⟨⟨a, b⟩, q⟩; simp [Matrix.mul_smul]

/-- The common last-edge support with an arbitrary exterior index type.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
def endpointLastEdgeCoreMap (A₀ : MPSTensor (D₀ * D₀) D₀) (ι : Type*) :
    Matrix ι (Fin D₀) ℂ →ₗ[ℂ] (endpointLastEdgeCfg ι D₀ → ℂ) where
  toFun Y := fun (q, (c, e)) => (Y * A₀ q) e c
  map_add' Y Z := by ext ⟨q, ⟨c, e⟩⟩; simp [Matrix.add_mul]
  map_smul' z Y := by ext ⟨q, ⟨c, e⟩⟩; simp [Matrix.smul_mul]

/-- Restrict the actual two-site map to a first-edge active configuration.
Its second site is in the first diagonal physical sector.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
def mixedEndpointFirstEdgeBoundaryMap
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁) :
    Matrix (Fin D₀ ⊕ Fin D₁) (Fin D₀ ⊕ Fin D₁) ℂ →ₗ[ℂ]
      (endpointFirstEdgeCfg (Fin D₀ ⊕ Fin D₁) D₀ → ℂ) where
  toFun X := fun ((a, b), q) => mixedEndpointActiveBoundaryMap A₀ A₁ 0 X
    (a, (b, Fin.elim0, (finProdFinEquiv.symm q).1), .inl (finProdFinEquiv.symm q).2)
  map_add' X Y := by
    ext ⟨⟨a, b⟩, q⟩
    exact congrFun (map_add (mixedEndpointActiveBoundaryMap A₀ A₁ 0) X Y) _
  map_smul' z X := by
    ext ⟨⟨a, b⟩, q⟩
    exact congrFun (map_smul (mixedEndpointActiveBoundaryMap A₀ A₁ 0) z X) _

/-- Restrict the actual two-site map to a last-edge active configuration.
Its first site is in the first diagonal physical sector.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
def mixedEndpointLastEdgeBoundaryMap
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁) :
    Matrix (Fin D₀ ⊕ Fin D₁) (Fin D₀ ⊕ Fin D₁) ℂ →ₗ[ℂ]
      (endpointLastEdgeCfg (Fin D₀ ⊕ Fin D₁) D₀ → ℂ) where
  toFun X := fun (q, (c, e)) => mixedEndpointActiveBoundaryMap A₀ A₁ 0 X
    (.inl (finProdFinEquiv.symm q).1, ((finProdFinEquiv.symm q).2, Fin.elim0, c), e)
  map_add' X Y := by
    ext ⟨q, ⟨c, e⟩⟩
    exact congrFun (map_add (mixedEndpointActiveBoundaryMap A₀ A₁ 0) X Y) _
  map_smul' z X := by
    ext ⟨q, ⟨c, e⟩⟩
    exact congrFun (map_smul (mixedEndpointActiveBoundaryMap A₀ A₁ 0) z X) _

/-- Apply a first-boundary physical change while retaining the adjacent
bulk letter. Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
def firstEdgePhysicalMap
    (F : Matrix (Fin (D₀ * D₀)) (Fin (D₀ * D₀)) ℂ) :
    (endpointFirstEdgeCfg (Fin D₀ ⊕ Fin D₁) D₀ → ℂ) →ₗ[ℂ]
      (endpointFirstEdgeCfg (Fin D₀ ⊕ Fin D₁) D₀ → ℂ) where
  toFun ψ := fun (p, q) => firstBoundaryCoordinateMap F (fun r => ψ (r, q)) p
  map_add' ψ φ := by
    ext ⟨p, q⟩
    exact congrFun (map_add (firstBoundaryCoordinateMap F)
      (fun r => ψ (r, q)) (fun r => φ (r, q))) p
  map_smul' z ψ := by
    ext ⟨p, q⟩
    exact congrFun (map_smul (firstBoundaryCoordinateMap F) z (fun r => ψ (r, q))) p

/-- Apply a last-boundary physical change while retaining the adjacent
bulk letter. Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
def lastEdgePhysicalMap
    (F : Matrix (Fin (D₀ * D₀)) (Fin (D₀ * D₀)) ℂ) :
    (endpointLastEdgeCfg (Fin D₀ ⊕ Fin D₁) D₀ → ℂ) →ₗ[ℂ]
      (endpointLastEdgeCfg (Fin D₀ ⊕ Fin D₁) D₀ → ℂ) where
  toFun ψ := fun (q, p) => lastBoundaryCoordinateMap F (fun r => ψ (q, r)) p
  map_add' ψ φ := by
    ext ⟨q, p⟩
    exact congrFun (map_add (lastBoundaryCoordinateMap F)
      (fun r => ψ (q, r)) (fun r => φ (q, r))) p
  map_smul' z ψ := by
    ext ⟨q, p⟩
    exact congrFun (map_smul (lastBoundaryCoordinateMap F) z (fun r => ψ (q, r))) p

/-- Normalizing the first site of the actual first edge produces the
common first-edge core with the original boundary's first block rows.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem firstEdgePhysicalMap_actual_apply
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (hA₀ : Kraus.IsInjective A₀)
    (X : Matrix (Fin D₀ ⊕ Fin D₁) (Fin D₀ ⊕ Fin D₁) ℂ)
    (a : Fin D₀ ⊕ Fin D₁) (b : Fin D₀) (q : Fin (D₀ * D₀)) :
    firstEdgePhysicalMap (squarePhysicalCoordinates A₀)⁻¹
        (mixedEndpointFirstEdgeBoundaryMap A₀ A₁ X) ((a, b), q) =
      endpointFirstEdgeCoreMap A₀ (Fin D₀ ⊕ Fin D₁) (X.submatrix Sum.inl id) ((a, b), q) := by
  let B : Matrix (Fin D₀ ⊕ Fin D₁) (Fin D₀) ℂ →ₗ[ℂ]
      Matrix (Fin D₀) (Fin D₀ ⊕ Fin D₁) ℂ →ₗ[ℂ] ℂ :=
    endpointBoundaryTracePairing (1 : Matrix (Fin D₀) (Fin D₀) ℂ) X
  let R : Matrix (Fin D₀) (Fin D₀ ⊕ Fin D₁) ℂ := Matrix.fromCols (A₀ q) 0
  have hcoeff (p : (Fin D₀ ⊕ Fin D₁) × Fin D₀) :
      mixedEndpointFirstEdgeBoundaryMap A₀ A₁ X (p, q) =
        B (mixedEndpointFirstBoundaryLetter A₀ p.1 (.inl p.2)) R := by
    obtain ⟨⟨r, s⟩, rfl⟩ := finProdFinEquiv.surjective q
    change mixedEndpointActiveBoundaryMap A₀ A₁ 0 X _ = _
    rw [mixedEndpointActiveBoundaryMap_apply]
    simp [B, R, mixedEndpointLastBoundaryLetter]
  change firstBoundaryCoordinateMap (squarePhysicalCoordinates A₀)⁻¹
      (fun p => mixedEndpointFirstEdgeBoundaryMap A₀ A₁ X (p, q)) (a, b) = _
  simp_rw [hcoeff]
  change firstBoundaryCoordinateMap (squarePhysicalCoordinates A₀)⁻¹
      (fun p => B.flip R (mixedEndpointFirstBoundaryLetter A₀ p.1 (.inl p.2))) (a, b) = _
  rw [firstBoundaryCoordinateMap_map,
    firstBoundaryCoordinateMap_inv_actual_letters A₀ hA₀]
  change Matrix.trace (Matrix.single a b (1 : ℂ) *
      (1 : Matrix (Fin D₀) (Fin D₀) ℂ) * R * X) =
    (A₀ q * X.submatrix Sum.inl id) b a
  simp only [Matrix.mul_one, Matrix.mul_assoc, Matrix.trace_single_mul, one_mul]
  simp [R, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.submatrix_apply]

/-- Normalizing the last site of the actual last edge produces the common
last-edge core with the original boundary's first block columns.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem lastEdgePhysicalMap_actual_apply
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (hA₀ : Kraus.IsInjective A₀)
    (X : Matrix (Fin D₀ ⊕ Fin D₁) (Fin D₀ ⊕ Fin D₁) ℂ)
    (q : Fin (D₀ * D₀)) (c : Fin D₀) (e : Fin D₀ ⊕ Fin D₁) :
    lastEdgePhysicalMap (squarePhysicalCoordinates A₀)⁻¹
        (mixedEndpointLastEdgeBoundaryMap A₀ A₁ X) (q, (c, e)) =
      endpointLastEdgeCoreMap A₀ (Fin D₀ ⊕ Fin D₁) (X.submatrix id Sum.inl) (q, (c, e)) := by
  let B : Matrix (Fin D₀ ⊕ Fin D₁) (Fin D₀) ℂ →ₗ[ℂ]
      Matrix (Fin D₀) (Fin D₀ ⊕ Fin D₁) ℂ →ₗ[ℂ] ℂ :=
    endpointBoundaryTracePairing (1 : Matrix (Fin D₀) (Fin D₀) ℂ) X
  let L : Matrix (Fin D₀ ⊕ Fin D₁) (Fin D₀) ℂ := Matrix.fromRows (A₀ q) 0
  have hcoeff (p : Fin D₀ × (Fin D₀ ⊕ Fin D₁)) :
      mixedEndpointLastEdgeBoundaryMap A₀ A₁ X (q, p) =
        B L (mixedEndpointLastBoundaryLetter A₀ (.inl p.1) p.2) := by
    obtain ⟨⟨r, s⟩, rfl⟩ := finProdFinEquiv.surjective q
    change mixedEndpointActiveBoundaryMap A₀ A₁ 0 X _ = _
    rw [mixedEndpointActiveBoundaryMap_apply]
    simp [B, L, mixedEndpointFirstBoundaryLetter]
  change lastBoundaryCoordinateMap (squarePhysicalCoordinates A₀)⁻¹
      (fun p => mixedEndpointLastEdgeBoundaryMap A₀ A₁ X (q, p)) (c, e) = _
  simp_rw [hcoeff]
  rw [lastBoundaryCoordinateMap_map,
    lastBoundaryCoordinateMap_inv_actual_letters A₀ hA₀]
  change Matrix.trace (L * (1 : Matrix (Fin D₀) (Fin D₀) ℂ) *
      Matrix.single c e (1 : ℂ) * X) =
    (X.submatrix id Sum.inl * A₀ q) e c
  rw [Matrix.mul_one, Matrix.mul_assoc, Matrix.trace_mul_comm L,
    Matrix.mul_assoc, Matrix.trace_single_mul]
  simp [L, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.submatrix_apply]

/-- The normalized actual first-edge support is exactly the common
one-sided core support. Every rectangular boundary is realized by padding
it with zero second-block rows.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem map_range_firstEdgePhysicalMap_actual_eq_core
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (hA₀ : Kraus.IsInjective A₀) :
    (mixedEndpointFirstEdgeBoundaryMap A₀ A₁).range.map
      (firstEdgePhysicalMap (squarePhysicalCoordinates A₀)⁻¹) =
      (endpointFirstEdgeCoreMap A₀ (Fin D₀ ⊕ Fin D₁)).range := by
  ext ψ
  constructor
  · rintro ⟨_, ⟨X, rfl⟩, rfl⟩
    refine ⟨X.submatrix Sum.inl id, ?_⟩
    ext ⟨⟨a, b⟩, q⟩
    exact (firstEdgePhysicalMap_actual_apply A₀ A₁ hA₀ X a b q).symm
  · rintro ⟨Y, rfl⟩
    let X : Matrix (Fin D₀ ⊕ Fin D₁) (Fin D₀ ⊕ Fin D₁) ℂ := Matrix.fromRows Y 0
    refine ⟨mixedEndpointFirstEdgeBoundaryMap A₀ A₁ X, ⟨X, rfl⟩, ?_⟩
    ext ⟨⟨a, b⟩, q⟩
    rw [firstEdgePhysicalMap_actual_apply A₀ A₁ hA₀]
    rfl

/-- The normalized actual last-edge support is exactly its common core.
Every rectangular boundary is realized by padding it with zero second-block
columns. Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem map_range_lastEdgePhysicalMap_actual_eq_core
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (hA₀ : Kraus.IsInjective A₀) :
    (mixedEndpointLastEdgeBoundaryMap A₀ A₁).range.map
      (lastEdgePhysicalMap (squarePhysicalCoordinates A₀)⁻¹) =
      (endpointLastEdgeCoreMap A₀ (Fin D₀ ⊕ Fin D₁)).range := by
  ext ψ
  constructor
  · rintro ⟨_, ⟨X, rfl⟩, rfl⟩
    refine ⟨X.submatrix id Sum.inl, ?_⟩
    ext ⟨q, ⟨c, e⟩⟩
    exact (lastEdgePhysicalMap_actual_apply A₀ A₁ hA₀ X q c e).symm
  · rintro ⟨Y, rfl⟩
    let X : Matrix (Fin D₀ ⊕ Fin D₁) (Fin D₀ ⊕ Fin D₁) ℂ := Matrix.fromCols Y 0
    refine ⟨mixedEndpointLastEdgeBoundaryMap A₀ A₁ X, ⟨X, rfl⟩, ?_⟩
    ext ⟨q, ⟨c, e⟩⟩
    rw [lastEdgePhysicalMap_actual_apply A₀ A₁ hA₀]
    rfl

private theorem inv_squarePhysicalCoordinates_contract
    (A₀ : MPSTensor (D₀ * D₀) D₀) (hA₀ : Kraus.IsInjective A₀)
    (T : Matrix (Fin D₀) (Fin D₀) ℂ →ₗ[ℂ] ℂ) (p : Fin (D₀ * D₀)) :
    (∑ q, (squarePhysicalCoordinates A₀)⁻¹ p q • T (A₀ q)) =
      T (matrixUnitPhysicalTensor D₀ p) := by
  have hletter := congrArg (fun A : MPSTensor (D₀ * D₀) D₀ => A p)
    (rotatePhysical_inv_squarePhysicalCoordinates A₀ hA₀)
  calc
    _ = T (∑ q, (squarePhysicalCoordinates A₀)⁻¹ p q • A₀ q) := by
      simp only [map_sum, map_smul]
    _ = T (matrixUnitPhysicalTensor D₀ p) := congrArg T hletter

/-- The ordinary first edge, normalized at its first site only, has the
same one-sided core, with `Fin D₀` in place of the enlarged exterior index.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem normalized_groundSpaceMap_firstEdge
    (A₀ : MPSTensor (D₀ * D₀) D₀) (hA₀ : Kraus.IsInjective A₀)
    (X : Matrix (Fin D₀) (Fin D₀) ℂ) (a b : Fin D₀) (q : Fin (D₀ * D₀)) :
    (∑ p, (squarePhysicalCoordinates A₀)⁻¹ (finProdFinEquiv (a, b)) p •
      groundSpaceMap A₀ 2 X ![p, q]) =
        endpointFirstEdgeCoreMap A₀ (Fin D₀) X ((a, b), q) := by
  let T := (endpointBoundaryTracePairing (1 : Matrix (Fin D₀) (Fin D₀) ℂ) X).flip (A₀ q)
  have hcoeff (p : Fin (D₀ * D₀)) : groundSpaceMap A₀ 2 X ![p, q] = T (A₀ p) := by
    simp [T, endpointBoundaryTracePairing, groundSpaceMap_apply,
      List.ofFn_succ, Kraus.evalWord, Matrix.mul_assoc]
  simp_rw [hcoeff]
  rw [inv_squarePhysicalCoordinates_contract A₀ hA₀]
  change Matrix.trace (matrixUnitPhysicalTensor D₀ (finProdFinEquiv (a, b)) * 1 * A₀ q * X) =
    (A₀ q * X) b a
  simp [matrixUnitPhysicalTensor, Matrix.mul_assoc, Matrix.trace_single_mul]

/-- The ordinary last edge has the same reflected one-sided core after
normalizing only its last site.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem normalized_groundSpaceMap_lastEdge
    (A₀ : MPSTensor (D₀ * D₀) D₀) (hA₀ : Kraus.IsInjective A₀)
    (X : Matrix (Fin D₀) (Fin D₀) ℂ) (q : Fin (D₀ * D₀)) (c e : Fin D₀) :
    (∑ p, (squarePhysicalCoordinates A₀)⁻¹ (finProdFinEquiv (c, e)) p •
      groundSpaceMap A₀ 2 X ![q, p]) =
        endpointLastEdgeCoreMap A₀ (Fin D₀) X (q, (c, e)) := by
  let T := endpointBoundaryTracePairing (1 : Matrix (Fin D₀) (Fin D₀) ℂ) X (A₀ q)
  have hcoeff (p : Fin (D₀ * D₀)) : groundSpaceMap A₀ 2 X ![q, p] = T (A₀ p) := by
    simp [T, endpointBoundaryTracePairing, groundSpaceMap_apply,
      List.ofFn_succ, Kraus.evalWord, Matrix.mul_assoc]
  simp_rw [hcoeff]
  rw [inv_squarePhysicalCoordinates_contract A₀ hA₀]
  change Matrix.trace (A₀ q * 1 * matrixUnitPhysicalTensor D₀ (finProdFinEquiv (c, e)) * X) =
    (X * A₀ q) e c
  simp only [Matrix.mul_one, matrixUnitPhysicalTensor, Equiv.symm_apply_apply]
  rw [Matrix.mul_assoc, Matrix.trace_mul_comm (A₀ q), Matrix.mul_assoc,
    Matrix.trace_single_mul]
  simp

/-- The actual two-site map on an interior active edge: both physical
letters lie in the first diagonal sector, so neither boundary change acts.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
def mixedEndpointInteriorEdgeBoundaryMap
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁) :
    Matrix (Fin D₀ ⊕ Fin D₁) (Fin D₀ ⊕ Fin D₁) ℂ →ₗ[ℂ] NSiteSpace (D₀ * D₀) 2 where
  toFun X σ := mixedEndpointActiveBoundaryMap A₀ A₁ 0 X
    (.inl (finProdFinEquiv.symm (σ 0)).1,
      ((finProdFinEquiv.symm (σ 0)).2, Fin.elim0, (finProdFinEquiv.symm (σ 1)).1),
      .inl (finProdFinEquiv.symm (σ 1)).2)
  map_add' X Y := by
    ext σ
    exact congrFun (map_add (mixedEndpointActiveBoundaryMap A₀ A₁ 0) X Y) _
  map_smul' z X := by
    ext σ
    exact congrFun (map_smul (mixedEndpointActiveBoundaryMap A₀ A₁ 0) z X) _

/-- Actual interior coefficients recover the ordinary `A₀` boundary map
with the first virtual corner of the original boundary.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem mixedEndpointInteriorEdgeBoundaryMap_apply
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (X : Matrix (Fin D₀ ⊕ Fin D₁) (Fin D₀ ⊕ Fin D₁) ℂ)
    (σ : Cfg (D₀ * D₀) 2) :
    mixedEndpointInteriorEdgeBoundaryMap A₀ A₁ X σ =
      groundSpaceMap A₀ 2 (X.submatrix Sum.inl Sum.inl) σ := by
  change mixedEndpointActiveBoundaryMap A₀ A₁ 0 X _ = _
  rw [mixedEndpointActiveBoundaryMap_apply]
  have hindex (p : Fin (D₀ * D₀)) :
      finProdFinEquiv ((finProdFinEquiv.symm p).1, (finProdFinEquiv.symm p).2) = p :=
    finProdFinEquiv.apply_symm_apply p
  simp only [mixedEndpointFirstBoundaryLetter, mixedEndpointLastBoundaryLetter,
    hindex]
  simp [endpointBoundaryTracePairing, groundSpaceMap_apply, List.ofFn_succ,
    Kraus.evalWord, Matrix.mul_assoc, Matrix.trace, Matrix.mul_apply,
    Fintype.sum_sum_type, Matrix.submatrix_apply]

/-- The actual interior-edge range is exactly the ordinary two-site
`A₀` support. This is independent of injectivity and of the second endpoint.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem range_mixedEndpointInteriorEdgeBoundaryMap
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁) :
    (mixedEndpointInteriorEdgeBoundaryMap A₀ A₁).range = groundSpace A₀ 2 := by
  ext ψ
  constructor
  · rintro ⟨X, rfl⟩
    refine ⟨X.submatrix Sum.inl Sum.inl, ?_⟩
    ext σ
    exact (mixedEndpointInteriorEdgeBoundaryMap_apply A₀ A₁ X σ).symm
  · rintro ⟨Y, rfl⟩
    let X : Matrix (Fin D₀ ⊕ Fin D₁) (Fin D₀ ⊕ Fin D₁) ℂ := Matrix.fromBlocks Y 0 0 0
    refine ⟨X, ?_⟩
    ext σ
    rw [mixedEndpointInteriorEdgeBoundaryMap_apply]
    rfl

end

end MPOSymmetry
end MPSTensor
