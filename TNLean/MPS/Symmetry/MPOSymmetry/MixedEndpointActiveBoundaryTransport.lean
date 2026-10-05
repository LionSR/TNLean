/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.MPOSymmetry.MixedEndpointBoundaryCoordinates

/-!
# Common-core coordinates for the active extended endpoint support

After restricting the inner physical registers to the first sector, an
active configuration consists of an outer first register, an inner first
register, an `A₀` bulk word, an inner last register, and an outer last
register. The two boundary physical changes act by the inverse square
physical coordinate matrix on their diagonal sectors and by the identity
on their mixed sectors.

The resulting actual extended boundary map has coefficients
`evalWord A₀ σ b c * X e a`. Thus its range is the fixed common-core vector
tensored with the unrestricted two exterior registers. The exterior
coordinates are written as `Fin D₀ ⊕ Fin D₁`; the actual physical and
virtual indices are transported by `finSumFinEquiv` explicitly.

Source: arXiv:2203.12563, Section 5, lines 1690–1692. This file proves a
support identity, not a termwise comparison of local interactions. Equality
of global kernels alone would not supply such a comparison.
-/

open scoped Matrix BigOperators

namespace MPSTensor
namespace MPOSymmetry

noncomputable section

variable {D₀ D₁ N : ℕ}

/-- The common interior coordinates, including the two exposed inner
boundary registers. Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
abbrev endpointCoreCfg (D N : ℕ) := Fin D × Cfg (D * D) N × Fin D

/-- Active coordinates with arbitrary exterior spectator index type.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
abbrev endpointActiveCfg (ι : Type*) (D N : ℕ) := ι × endpointCoreCfg D N × ι

/-- The fixed common-core vector. All dependence on the endpoint tensor
and the chain length is here, rather than in the exterior spectators.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
def endpointCoreVector (A : MPSTensor (D₀ * D₀) D₀) (N : ℕ) :
    endpointCoreCfg D₀ N → ℂ :=
  fun (b, σ, c) => Kraus.evalWord A (List.ofFn σ) b c

/-- The common-core support map, with arbitrary exterior spectator
coordinates. Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
def endpointCoreSpectatorMap (A : MPSTensor (D₀ * D₀) D₀) (N : ℕ) (ι : Type*) :
    Matrix ι ι ℂ →ₗ[ℂ] (endpointActiveCfg ι D₀ N → ℂ) where
  toFun X := fun (a, κ, e) => endpointCoreVector A N κ * X e a
  map_add' X Y := by ext ⟨a, κ, e⟩; simp [mul_add]
  map_smul' z X := by ext ⟨a, κ, e⟩; simp [mul_left_comm]

/-- The common-core range is precisely the fixed core times an arbitrary
function of the two exterior registers. This formula does not assume that
the core vector is nonzero. Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem mem_range_endpointCoreSpectatorMap_iff
    (A : MPSTensor (D₀ * D₀) D₀) (N : ℕ) (ι : Type*)
    (ψ : endpointActiveCfg ι D₀ N → ℂ) :
    ψ ∈ (endpointCoreSpectatorMap A N ι).range ↔
      ∃ f : ι → ι → ℂ, ∀ a κ e, ψ (a, κ, e) = endpointCoreVector A N κ * f e a := by
  constructor
  · rintro ⟨X, rfl⟩
    exact ⟨X, fun _ _ _ => rfl⟩
  · rintro ⟨f, hf⟩
    refine ⟨f, ?_⟩
    ext ⟨a, κ, e⟩
    exact (hf a κ e).symm

section CoordinateActions

variable {V W : Type*} [AddCommMonoid V] [Module ℂ V]
  [AddCommMonoid W] [Module ℂ W]

/-- The first boundary physical map on active letters: `F` on the first
outer sector and the identity on the second. It is defined for arbitrary
complex coefficient modules, so it commutes with linear contractions.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
def firstBoundaryCoordinateMap (F : Matrix (Fin (D₀ * D₀)) (Fin (D₀ * D₀)) ℂ) :
    (((Fin D₀ ⊕ Fin D₁) × Fin D₀) → V) →ₗ[ℂ]
      (((Fin D₀ ⊕ Fin D₁) × Fin D₀) → V) where
  toFun v := fun (a, b) => match a with
    | .inl a => ∑ p, F (finProdFinEquiv (a, b)) p •
        v (.inl (finProdFinEquiv.symm p).1, (finProdFinEquiv.symm p).2)
    | .inr a => v (.inr a, b)
  map_add' v w := by
    ext ⟨a, b⟩
    cases a <;> simp [smul_add, Finset.sum_add_distrib]
  map_smul' z v := by
    ext ⟨a, b⟩
    cases a <;> simp [Finset.smul_sum, smul_smul, mul_comm]

/-- The last boundary physical map, with the same square coordinate change
on its first outer sector. Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
def lastBoundaryCoordinateMap (F : Matrix (Fin (D₀ * D₀)) (Fin (D₀ * D₀)) ℂ) :
    ((Fin D₀ × (Fin D₀ ⊕ Fin D₁)) → V) →ₗ[ℂ]
      ((Fin D₀ × (Fin D₀ ⊕ Fin D₁)) → V) where
  toFun v := fun (b, a) => match a with
    | .inl a => ∑ p, F (finProdFinEquiv (b, a)) p •
        v ((finProdFinEquiv.symm p).1, .inl (finProdFinEquiv.symm p).2)
    | .inr a => v (b, .inr a)
  map_add' v w := by
    ext ⟨b, a⟩
    cases a <;> simp [smul_add, Finset.sum_add_distrib]
  map_smul' z v := by
    ext ⟨b, a⟩
    cases a <;> simp [Finset.smul_sum, smul_smul, mul_comm]

/-- Boundary coordinate changes commute with every linear contraction.
Source context: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem firstBoundaryCoordinateMap_map
    (F : Matrix (Fin (D₀ * D₀)) (Fin (D₀ * D₀)) ℂ) (T : V →ₗ[ℂ] W)
    (v : ((Fin D₀ ⊕ Fin D₁) × Fin D₀) → V) (p : (Fin D₀ ⊕ Fin D₁) × Fin D₀) :
    firstBoundaryCoordinateMap F (fun q => T (v q)) p =
      T (firstBoundaryCoordinateMap F v p) := by
  obtain ⟨a, b⟩ := p
  cases a <;> simp [firstBoundaryCoordinateMap, map_sum]

/-- The last boundary coordinate change commutes with linear contraction.
Source context: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem lastBoundaryCoordinateMap_map
    (F : Matrix (Fin (D₀ * D₀)) (Fin (D₀ * D₀)) ℂ) (T : V →ₗ[ℂ] W)
    (v : (Fin D₀ × (Fin D₀ ⊕ Fin D₁)) → V) (p : Fin D₀ × (Fin D₀ ⊕ Fin D₁)) :
    lastBoundaryCoordinateMap F (fun q => T (v q)) p =
      T (lastBoundaryCoordinateMap F v p) := by
  obtain ⟨b, a⟩ := p
  cases a <;> simp [lastBoundaryCoordinateMap, map_sum]

/-- The identity matrix gives the identity first boundary map.
Source context: arXiv:2203.12563, Section 5, lines 1690–1692. -/
@[simp]
theorem firstBoundaryCoordinateMap_one :
    firstBoundaryCoordinateMap (D₁ := D₁) (V := V)
      (1 : Matrix (Fin (D₀ * D₀)) (Fin (D₀ * D₀)) ℂ) = LinearMap.id := by
  apply LinearMap.ext
  intro v
  funext ⟨a, b⟩
  cases a with
  | inl a =>
    have h : v (Sum.inl (finProdFinEquiv (a, b)).divNat, (finProdFinEquiv (a, b)).modNat) =
        v (Sum.inl a, b) := congrArg (fun p : Fin D₀ × Fin D₀ => v (Sum.inl p.1, p.2))
          (finProdFinEquiv.symm_apply_apply (a, b))
    simpa [firstBoundaryCoordinateMap, Matrix.one_apply] using h
  | inr a => simp [firstBoundaryCoordinateMap, Matrix.one_apply]

/-- The identity matrix gives the identity last boundary map.
Source context: arXiv:2203.12563, Section 5, lines 1690–1692. -/
@[simp]
theorem lastBoundaryCoordinateMap_one :
    lastBoundaryCoordinateMap (D₁ := D₁) (V := V)
      (1 : Matrix (Fin (D₀ * D₀)) (Fin (D₀ * D₀)) ℂ) = LinearMap.id := by
  apply LinearMap.ext
  intro v
  funext ⟨b, a⟩
  cases a with
  | inl a =>
    have h : v ((finProdFinEquiv (b, a)).divNat, Sum.inl (finProdFinEquiv (b, a)).modNat) =
        v (b, Sum.inl a) := congrArg (fun p : Fin D₀ × Fin D₀ => v (p.1, Sum.inl p.2))
          (finProdFinEquiv.symm_apply_apply (b, a))
    simpa [lastBoundaryCoordinateMap, Matrix.one_apply] using h
  | inr a => simp [lastBoundaryCoordinateMap, Matrix.one_apply]

private theorem sum_matrix_mul_smul {k : ℕ}
    (F G : Matrix (Fin k) (Fin k) ℂ) (v : Fin k → V) (i : Fin k) :
    (∑ q, (F * G) i q • v q) = ∑ p, F i p • ∑ q, G p q • v q := by
  simp only [Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum, smul_smul]
  exact Finset.sum_comm

/-- First boundary coordinate maps compose by multiplication of their
fixed-size physical matrices. Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem firstBoundaryCoordinateMap_mul
    (F G : Matrix (Fin (D₀ * D₀)) (Fin (D₀ * D₀)) ℂ) :
    firstBoundaryCoordinateMap (D₁ := D₁) (V := V) (F * G) =
      (firstBoundaryCoordinateMap F).comp (firstBoundaryCoordinateMap G) := by
  apply LinearMap.ext
  intro v
  funext ⟨a, b⟩
  cases a with
  | inl a =>
      simpa only [firstBoundaryCoordinateMap, LinearMap.comp_apply,
        LinearMap.coe_mk, AddHom.coe_mk, Prod.mk.eta, Equiv.apply_symm_apply] using
        sum_matrix_mul_smul F G
          (fun p => v (.inl (finProdFinEquiv.symm p).1, (finProdFinEquiv.symm p).2))
          (finProdFinEquiv (a, b))
  | inr a => rfl

/-- Last boundary coordinate maps satisfy the same composition law.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem lastBoundaryCoordinateMap_mul
    (F G : Matrix (Fin (D₀ * D₀)) (Fin (D₀ * D₀)) ℂ) :
    lastBoundaryCoordinateMap (D₁ := D₁) (V := V) (F * G) =
      (lastBoundaryCoordinateMap F).comp (lastBoundaryCoordinateMap G) := by
  apply LinearMap.ext
  intro v
  funext ⟨b, a⟩
  cases a with
  | inl a =>
      simpa only [lastBoundaryCoordinateMap, LinearMap.comp_apply,
        LinearMap.coe_mk, AddHom.coe_mk, Prod.mk.eta, Equiv.apply_symm_apply] using
        sum_matrix_mul_smul F G
          (fun p => v ((finProdFinEquiv.symm p).1, .inl (finProdFinEquiv.symm p).2))
          (finProdFinEquiv (b, a))
  | inr a => rfl

/-- Mutually inverse physical matrices give an explicit first boundary
equivalence, on a local space independent of the chain length.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
def firstBoundaryCoordinateEquiv
    (F G : Matrix (Fin (D₀ * D₀)) (Fin (D₀ * D₀)) ℂ)
    (hFG : F * G = 1) (hGF : G * F = 1) :
    (((Fin D₀ ⊕ Fin D₁) × Fin D₀) → V) ≃ₗ[ℂ]
      (((Fin D₀ ⊕ Fin D₁) × Fin D₀) → V) :=
  LinearEquiv.ofLinearMap (firstBoundaryCoordinateMap F) (firstBoundaryCoordinateMap G)
    (by rw [← firstBoundaryCoordinateMap_mul, hFG, firstBoundaryCoordinateMap_one])
    (by rw [← firstBoundaryCoordinateMap_mul, hGF, firstBoundaryCoordinateMap_one])

/-- Mutually inverse physical matrices give an explicit last boundary
equivalence, again independent of chain length.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
def lastBoundaryCoordinateEquiv
    (F G : Matrix (Fin (D₀ * D₀)) (Fin (D₀ * D₀)) ℂ)
    (hFG : F * G = 1) (hGF : G * F = 1) :
    ((Fin D₀ × (Fin D₀ ⊕ Fin D₁)) → V) ≃ₗ[ℂ]
      ((Fin D₀ × (Fin D₀ ⊕ Fin D₁)) → V) :=
  LinearEquiv.ofLinearMap (lastBoundaryCoordinateMap F) (lastBoundaryCoordinateMap G)
    (by rw [← lastBoundaryCoordinateMap_mul, hFG, lastBoundaryCoordinateMap_one])
    (by rw [← lastBoundaryCoordinateMap_mul, hGF, lastBoundaryCoordinateMap_one])

end CoordinateActions


/-- The first boundary normalization is invertible, with forward matrix
`(squarePhysicalCoordinates A₀)⁻¹` and inverse matrix `squarePhysicalCoordinates A₀`.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
def firstBoundaryNormalizationEquiv
    (A₀ : MPSTensor (D₀ * D₀) D₀) (hA₀ : Kraus.IsInjective A₀) :
    (((Fin D₀ ⊕ Fin D₁) × Fin D₀) → ℂ) ≃ₗ[ℂ]
      (((Fin D₀ ⊕ Fin D₁) × Fin D₀) → ℂ) :=
  firstBoundaryCoordinateEquiv (squarePhysicalCoordinates A₀)⁻¹ (squarePhysicalCoordinates A₀)
    (Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp
      (isUnit_squarePhysicalCoordinates A₀ hA₀)))
    (Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp
      (isUnit_squarePhysicalCoordinates A₀ hA₀)))

/-- The last boundary normalization has the same explicit inverse matrix.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
def lastBoundaryNormalizationEquiv
    (A₀ : MPSTensor (D₀ * D₀) D₀) (hA₀ : Kraus.IsInjective A₀) :
    ((Fin D₀ × (Fin D₀ ⊕ Fin D₁)) → ℂ) ≃ₗ[ℂ]
      ((Fin D₀ × (Fin D₀ ⊕ Fin D₁)) → ℂ) :=
  lastBoundaryCoordinateEquiv (squarePhysicalCoordinates A₀)⁻¹ (squarePhysicalCoordinates A₀)
    (Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp
      (isUnit_squarePhysicalCoordinates A₀ hA₀)))
    (Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp
      (isUnit_squarePhysicalCoordinates A₀ hA₀)))

/-- The first local equivalence applies the inverse physical matrix.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
@[simp]
theorem firstBoundaryNormalizationEquiv_toLinearMap
    (A₀ : MPSTensor (D₀ * D₀) D₀) (hA₀ : Kraus.IsInjective A₀) :
    (firstBoundaryNormalizationEquiv (D₁ := D₁) A₀ hA₀).toLinearMap =
      firstBoundaryCoordinateMap (squarePhysicalCoordinates A₀)⁻¹ := rfl

/-- The inverse first local equivalence applies the forward physical matrix.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
@[simp]
theorem firstBoundaryNormalizationEquiv_symm_toLinearMap
    (A₀ : MPSTensor (D₀ * D₀) D₀) (hA₀ : Kraus.IsInjective A₀) :
    (firstBoundaryNormalizationEquiv (D₁ := D₁) A₀ hA₀).symm.toLinearMap =
      firstBoundaryCoordinateMap (squarePhysicalCoordinates A₀) := rfl

/-- The last local equivalence applies the inverse physical matrix.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
@[simp]
theorem lastBoundaryNormalizationEquiv_toLinearMap
    (A₀ : MPSTensor (D₀ * D₀) D₀) (hA₀ : Kraus.IsInjective A₀) :
    (lastBoundaryNormalizationEquiv (D₁ := D₁) A₀ hA₀).toLinearMap =
      lastBoundaryCoordinateMap (squarePhysicalCoordinates A₀)⁻¹ := rfl

/-- The inverse last local equivalence applies the forward physical matrix.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
@[simp]
theorem lastBoundaryNormalizationEquiv_symm_toLinearMap
    (A₀ : MPSTensor (D₀ * D₀) D₀) (hA₀ : Kraus.IsInjective A₀) :
    (lastBoundaryNormalizationEquiv (D₁ := D₁) A₀ hA₀).symm.toLinearMap =
      lastBoundaryCoordinateMap (squarePhysicalCoordinates A₀) := rfl


/-- The fixed first-boundary equivalence in Euclidean coordinates, suitable
for fiberwise extension with a volume-independent operator norm bound.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
def firstBoundaryNormalizationEquivES
    (A₀ : MPSTensor (D₀ * D₀) D₀) (hA₀ : Kraus.IsInjective A₀) :
    EuclideanSpace ℂ ((Fin D₀ ⊕ Fin D₁) × Fin D₀) ≃ₗ[ℂ]
      EuclideanSpace ℂ ((Fin D₀ ⊕ Fin D₁) × Fin D₀) :=
  let U := WithLp.linearEquiv 2 ℂ (((Fin D₀ ⊕ Fin D₁) × Fin D₀) → ℂ)
  U.trans ((firstBoundaryNormalizationEquiv A₀ hA₀).trans U.symm)

/-- The fixed last-boundary Euclidean equivalence, likewise independent
of the chain length. Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
def lastBoundaryNormalizationEquivES
    (A₀ : MPSTensor (D₀ * D₀) D₀) (hA₀ : Kraus.IsInjective A₀) :
    EuclideanSpace ℂ (Fin D₀ × (Fin D₀ ⊕ Fin D₁)) ≃ₗ[ℂ]
      EuclideanSpace ℂ (Fin D₀ × (Fin D₀ ⊕ Fin D₁)) :=
  let U := WithLp.linearEquiv 2 ℂ ((Fin D₀ × (Fin D₀ ⊕ Fin D₁)) → ℂ)
  U.trans ((lastBoundaryNormalizationEquiv A₀ hA₀).trans U.symm)

/-- Normalize the actual first rectangular letters in both outer sectors
at once. Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem firstBoundaryCoordinateMap_inv_actual_letters
    (A₀ : MPSTensor (D₀ * D₀) D₀) (hA₀ : Kraus.IsInjective A₀)
    (a : Fin D₀ ⊕ Fin D₁) (b : Fin D₀) :
    firstBoundaryCoordinateMap (squarePhysicalCoordinates A₀)⁻¹
        (fun p => mixedEndpointFirstBoundaryLetter A₀ p.1 (.inl p.2)) (a, b) =
      Matrix.single a b 1 := by
  cases a with
  | inl a =>
      simpa [firstBoundaryCoordinateMap] using
        (inv_squarePhysicalCoordinates_firstBoundaryLetter (D₁ := D₁) A₀ hA₀
          (finProdFinEquiv (a, b)))
  | inr a => rfl

/-- Normalize the actual last rectangular letters in both outer sectors.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem lastBoundaryCoordinateMap_inv_actual_letters
    (A₀ : MPSTensor (D₀ * D₀) D₀) (hA₀ : Kraus.IsInjective A₀)
    (b : Fin D₀) (a : Fin D₀ ⊕ Fin D₁) :
    lastBoundaryCoordinateMap (squarePhysicalCoordinates A₀)⁻¹
        (fun p => mixedEndpointLastBoundaryLetter A₀ (.inl p.1) p.2) (b, a) =
      Matrix.single b a 1 := by
  cases a with
  | inl a =>
      simpa [lastBoundaryCoordinateMap] using
        (inv_squarePhysicalCoordinates_lastBoundaryLetter (D₁ := D₁) A₀ hA₀
          (finProdFinEquiv (b, a)))
  | inr a => rfl

/-- The first-site physical change on the full active chain.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
def activeFirstBoundaryMap
    (F : Matrix (Fin (D₀ * D₀)) (Fin (D₀ * D₀)) ℂ) (N : ℕ) :
    (endpointActiveCfg (Fin D₀ ⊕ Fin D₁) D₀ N → ℂ) →ₗ[ℂ]
      (endpointActiveCfg (Fin D₀ ⊕ Fin D₁) D₀ N → ℂ) where
  toFun ψ := fun (a, (b, σ, c), e) =>
    firstBoundaryCoordinateMap F (fun p => ψ (p.1, (p.2, σ, c), e)) (a, b)
  map_add' ψ φ := by
    ext ⟨a, ⟨b, σ, c⟩, e⟩
    exact congrFun (map_add (firstBoundaryCoordinateMap F)
      (fun p => ψ (p.1, (p.2, σ, c), e))
      (fun p => φ (p.1, (p.2, σ, c), e))) (a, b)
  map_smul' z ψ := by
    ext ⟨a, ⟨b, σ, c⟩, e⟩
    exact congrFun (map_smul (firstBoundaryCoordinateMap F) z
      (fun p => ψ (p.1, (p.2, σ, c), e))) (a, b)

/-- The last-site physical change on the full active chain.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
def activeLastBoundaryMap
    (F : Matrix (Fin (D₀ * D₀)) (Fin (D₀ * D₀)) ℂ) (N : ℕ) :
    (endpointActiveCfg (Fin D₀ ⊕ Fin D₁) D₀ N → ℂ) →ₗ[ℂ]
      (endpointActiveCfg (Fin D₀ ⊕ Fin D₁) D₀ N → ℂ) where
  toFun ψ := fun (a, (b, σ, c), e) =>
    lastBoundaryCoordinateMap F (fun p => ψ (a, (b, σ, p.1), p.2)) (c, e)
  map_add' ψ φ := by
    ext ⟨a, ⟨b, σ, c⟩, e⟩
    exact congrFun (map_add (lastBoundaryCoordinateMap F)
      (fun p => ψ (a, (b, σ, p.1), p.2))
      (fun p => φ (a, (b, σ, p.1), p.2))) (c, e)
  map_smul' z ψ := by
    ext ⟨a, ⟨b, σ, c⟩, e⟩
    exact congrFun (map_smul (lastBoundaryCoordinateMap F) z
      (fun p => ψ (a, (b, σ, p.1), p.2))) (c, e)


/-- The identity first-site change fixes every active-chain vector.
Source context: arXiv:2203.12563, Section 5, lines 1690–1692. -/
@[simp]
theorem activeFirstBoundaryMap_one (N : ℕ) :
    activeFirstBoundaryMap (D₁ := D₁)
      (1 : Matrix (Fin (D₀ * D₀)) (Fin (D₀ * D₀)) ℂ) N = LinearMap.id := by
  apply LinearMap.ext
  intro ψ
  funext ⟨a, ⟨b, σ, c⟩, e⟩
  change firstBoundaryCoordinateMap 1 (fun p => ψ (p.1, (p.2, σ, c), e)) (a, b) = _
  simp only [firstBoundaryCoordinateMap_one, LinearMap.id_apply]

/-- The identity last-site change fixes every active-chain vector.
Source context: arXiv:2203.12563, Section 5, lines 1690–1692. -/
@[simp]
theorem activeLastBoundaryMap_one (N : ℕ) :
    activeLastBoundaryMap (D₁ := D₁)
      (1 : Matrix (Fin (D₀ * D₀)) (Fin (D₀ * D₀)) ℂ) N = LinearMap.id := by
  apply LinearMap.ext
  intro ψ
  funext ⟨a, ⟨b, σ, c⟩, e⟩
  change lastBoundaryCoordinateMap 1 (fun p => ψ (a, (b, σ, p.1), p.2)) (c, e) = _
  simp only [lastBoundaryCoordinateMap_one, LinearMap.id_apply]

/-- First-site changes compose by the same fixed local matrix product.
Source context: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem activeFirstBoundaryMap_mul
    (F G : Matrix (Fin (D₀ * D₀)) (Fin (D₀ * D₀)) ℂ) (N : ℕ) :
    activeFirstBoundaryMap (D₁ := D₁) (F * G) N =
      (activeFirstBoundaryMap F N).comp (activeFirstBoundaryMap G N) := by
  apply LinearMap.ext
  intro ψ
  funext ⟨a, ⟨b, σ, c⟩, e⟩
  change firstBoundaryCoordinateMap (F * G)
      (fun p => ψ (p.1, (p.2, σ, c), e)) (a, b) =
    firstBoundaryCoordinateMap F
      (firstBoundaryCoordinateMap G (fun p => ψ (p.1, (p.2, σ, c), e))) (a, b)
  simp only [firstBoundaryCoordinateMap_mul, LinearMap.comp_apply]

/-- Last-site changes compose by the fixed local matrix product.
Source context: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem activeLastBoundaryMap_mul
    (F G : Matrix (Fin (D₀ * D₀)) (Fin (D₀ * D₀)) ℂ) (N : ℕ) :
    activeLastBoundaryMap (D₁ := D₁) (F * G) N =
      (activeLastBoundaryMap F N).comp (activeLastBoundaryMap G N) := by
  apply LinearMap.ext
  intro ψ
  funext ⟨a, ⟨b, σ, c⟩, e⟩
  change lastBoundaryCoordinateMap (F * G)
      (fun p => ψ (a, (b, σ, p.1), p.2)) (c, e) =
    lastBoundaryCoordinateMap F
      (lastBoundaryCoordinateMap G (fun p => ψ (a, (b, σ, p.1), p.2))) (c, e)
  simp only [lastBoundaryCoordinateMap_mul, LinearMap.comp_apply]

/-- Extend an invertible first boundary change over the full active chain.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
def activeFirstBoundaryEquiv
    (F G : Matrix (Fin (D₀ * D₀)) (Fin (D₀ * D₀)) ℂ)
    (hFG : F * G = 1) (hGF : G * F = 1) (N : ℕ) :
    (endpointActiveCfg (Fin D₀ ⊕ Fin D₁) D₀ N → ℂ) ≃ₗ[ℂ]
      (endpointActiveCfg (Fin D₀ ⊕ Fin D₁) D₀ N → ℂ) :=
  LinearEquiv.ofLinearMap (activeFirstBoundaryMap F N) (activeFirstBoundaryMap G N)
    (by rw [← activeFirstBoundaryMap_mul, hFG, activeFirstBoundaryMap_one])
    (by rw [← activeFirstBoundaryMap_mul, hGF, activeFirstBoundaryMap_one])

/-- Extend an invertible last boundary change over the full active chain.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
def activeLastBoundaryEquiv
    (F G : Matrix (Fin (D₀ * D₀)) (Fin (D₀ * D₀)) ℂ)
    (hFG : F * G = 1) (hGF : G * F = 1) (N : ℕ) :
    (endpointActiveCfg (Fin D₀ ⊕ Fin D₁) D₀ N → ℂ) ≃ₗ[ℂ]
      (endpointActiveCfg (Fin D₀ ⊕ Fin D₁) D₀ N → ℂ) :=
  LinearEquiv.ofLinearMap (activeLastBoundaryMap F N) (activeLastBoundaryMap G N)
    (by rw [← activeLastBoundaryMap_mul, hFG, activeLastBoundaryMap_one])
    (by rw [← activeLastBoundaryMap_mul, hGF, activeLastBoundaryMap_one])

/-- The two actual boundary normalizations form a global equivalence;
its inverse applies the two forward endpoint coordinate matrices.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
def activeBoundaryNormalizationEquiv
    (A₀ : MPSTensor (D₀ * D₀) D₀) (hA₀ : Kraus.IsInjective A₀) (N : ℕ) :
    (endpointActiveCfg (Fin D₀ ⊕ Fin D₁) D₀ N → ℂ) ≃ₗ[ℂ]
      (endpointActiveCfg (Fin D₀ ⊕ Fin D₁) D₀ N → ℂ) :=
  let F := squarePhysicalCoordinates A₀
  have hdet : IsUnit F.det := (Matrix.isUnit_iff_isUnit_det _).mp
    (isUnit_squarePhysicalCoordinates A₀ hA₀)
  (activeLastBoundaryEquiv F⁻¹ F
    (Matrix.nonsing_inv_mul _ hdet) (Matrix.mul_nonsing_inv _ hdet) N).trans
      (activeFirstBoundaryEquiv F⁻¹ F
        (Matrix.nonsing_inv_mul _ hdet) (Matrix.mul_nonsing_inv _ hdet) N)

/-- The global equivalence has precisely the normalization used in the
actual-map identity. Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
@[simp]
theorem activeBoundaryNormalizationEquiv_toLinearMap
    (A₀ : MPSTensor (D₀ * D₀) D₀) (hA₀ : Kraus.IsInjective A₀) (N : ℕ) :
    (activeBoundaryNormalizationEquiv (D₁ := D₁) A₀ hA₀ N).toLinearMap =
      (activeFirstBoundaryMap (squarePhysicalCoordinates A₀)⁻¹ N).comp
        (activeLastBoundaryMap (squarePhysicalCoordinates A₀)⁻¹ N) := rfl

/-- The global inverse is the reverse composition of the two forward
coordinate matrices. Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
@[simp]
theorem activeBoundaryNormalizationEquiv_symm_toLinearMap
    (A₀ : MPSTensor (D₀ * D₀) D₀) (hA₀ : Kraus.IsInjective A₀) (N : ℕ) :
    (activeBoundaryNormalizationEquiv (D₁ := D₁) A₀ hA₀ N).symm.toLinearMap =
      (activeLastBoundaryMap (squarePhysicalCoordinates A₀) N).comp
        (activeFirstBoundaryMap (squarePhysicalCoordinates A₀) N) := rfl

/-- Trace contraction of rectangular boundary letters, bilinear in those
letters. Source context: arXiv:2203.12563, Section 5, lines 1690–1692. -/
def endpointBoundaryTracePairing {ι : Type*} [Fintype ι]
    (M : Matrix (Fin D₀) (Fin D₀) ℂ) (X : Matrix ι ι ℂ) :
    Matrix ι (Fin D₀) ℂ →ₗ[ℂ] Matrix (Fin D₀) ι ℂ →ₗ[ℂ] ℂ where
  toFun L :=
    { toFun := fun R => Matrix.trace (L * M * R * X)
      map_add' R S := by simp [Matrix.mul_add, Matrix.add_mul, Matrix.trace_add]
      map_smul' z R := by simp [Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul] }
  map_add' L K := by
    ext R
    simp [Matrix.add_mul, Matrix.trace_add]
  map_smul' z L := by
    ext R
    simp [Matrix.smul_mul, Matrix.trace_smul]

private theorem trace_rectangular_boundary_reindex
    {ι κ : Type*} [Fintype ι] [Fintype κ] (e : ι ≃ κ)
    (L : Matrix ι (Fin D₀) ℂ) (M : Matrix (Fin D₀) (Fin D₀) ℂ)
    (R : Matrix (Fin D₀) ι ℂ) (X : Matrix ι ι ℂ) :
    Matrix.trace (L.submatrix e.symm id * M * R.submatrix id e.symm *
        Matrix.reindex e e X) = Matrix.trace (L * M * R * X) := by
  have hprod : L.submatrix e.symm id * M * R.submatrix id e.symm *
      Matrix.reindex e e X = (L * M * R * X).submatrix e.symm e.symm := by
    rw [← Matrix.submatrix_mul_equiv (L * M * R) X e.symm e.symm e.symm,
      ← Matrix.submatrix_mul_equiv (L * M) R e.symm (Equiv.refl _) e.symm]
    simp only [Equiv.coe_refl]
    rw [← Matrix.submatrix_mul_equiv L M e.symm (Equiv.refl _) id]
    simp only [Equiv.coe_refl, Matrix.submatrix_id_id, Matrix.reindex_apply]
  rw [hprod]
  exact e.symm.sum_comp (fun i => (L * M * R * X) i i)

/-- Embed an active configuration into the actual physical chain.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
def mixedEndpointActivePhysicalCfg
    (ξ : endpointActiveCfg (Fin D₀ ⊕ Fin D₁) D₀ N) :
    Cfg ((D₀ + D₁) * (D₀ + D₁)) (N + 1 + 1) :=
  match ξ with
  | (a, (b, σ, c), e) =>
    Fin.cons (mixedEndpointPhysicalIndex a (.inl b))
      (Fin.snoc (fun k => mixedEndpointFirstPhysicalIndex D₁ (σ k))
        (mixedEndpointPhysicalIndex (.inl c) e))

/-- Restrict the full physical coefficient space to the explicitly encoded
active configurations. Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
def mixedEndpointActiveRestriction (D₀ D₁ N : ℕ) :
    NSiteSpace ((D₀ + D₁) * (D₀ + D₁)) (N + 1 + 1) →ₗ[ℂ]
      (endpointActiveCfg (Fin D₀ ⊕ Fin D₁) D₀ N → ℂ) where
  toFun ψ ξ := ψ (mixedEndpointActivePhysicalCfg ξ)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The actual extended boundary map restricted to active physical
coordinates, with its boundary matrix expressed in direct-sum coordinates.
Both restrictions are explicit; no range or kernel identification is assumed.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
def mixedEndpointActiveBoundaryMap
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁) (N : ℕ) :
    Matrix (Fin D₀ ⊕ Fin D₁) (Fin D₀ ⊕ Fin D₁) ℂ →ₗ[ℂ]
      (endpointActiveCfg (Fin D₀ ⊕ Fin D₁) D₀ N → ℂ) where
  toFun X ξ := insertedGroundSpaceMap (mixedEndpointBase A₀ A₁)
    (bondInterpolationMatrix D₀ D₁ 0) (N + 1 + 1)
    (Matrix.reindex finSumFinEquiv finSumFinEquiv X) (mixedEndpointActivePhysicalCfg ξ)
  map_add' X Y := by
    ext ξ
    exact congrFun (map_add (insertedGroundSpaceMap (mixedEndpointBase A₀ A₁)
      (bondInterpolationMatrix D₀ D₁ 0) (N + 1 + 1))
      (Matrix.reindex finSumFinEquiv finSumFinEquiv X)
      (Matrix.reindex finSumFinEquiv finSumFinEquiv Y)) (mixedEndpointActivePhysicalCfg ξ)
  map_smul' z X := by
    ext ξ
    exact congrFun (map_smul (insertedGroundSpaceMap (mixedEndpointBase A₀ A₁)
      (bondInterpolationMatrix D₀ D₁ 0) (N + 1 + 1)) z
      (Matrix.reindex finSumFinEquiv finSumFinEquiv X)) (mixedEndpointActivePhysicalCfg ξ)

/-- The virtual reindex in the active map does not change the actual
restricted range: every original virtual boundary is represented.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem range_mixedEndpointActiveBoundaryMap
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁) (N : ℕ) :
    (mixedEndpointActiveBoundaryMap A₀ A₁ N).range =
      (insertedGroundSpaceMap (mixedEndpointBase A₀ A₁)
        (bondInterpolationMatrix D₀ D₁ 0) (N + 1 + 1)).range.map
          (mixedEndpointActiveRestriction D₀ D₁ N) := by
  ext ψ
  constructor
  · rintro ⟨X, rfl⟩
    exact ⟨_, ⟨Matrix.reindex finSumFinEquiv finSumFinEquiv X, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨X, rfl⟩, rfl⟩
    refine ⟨X.submatrix finSumFinEquiv finSumFinEquiv, ?_⟩
    have hX : Matrix.reindex finSumFinEquiv finSumFinEquiv
        (X.submatrix finSumFinEquiv finSumFinEquiv) = X := by
      ext i j
      simp [Matrix.reindex_apply, Matrix.submatrix_apply]
    ext ξ
    change insertedGroundSpaceMap _ _ _
      (Matrix.reindex finSumFinEquiv finSumFinEquiv
        (X.submatrix finSumFinEquiv finSumFinEquiv))
      (mixedEndpointActivePhysicalCfg ξ) =
        insertedGroundSpaceMap _ _ _ X (mixedEndpointActivePhysicalCfg ξ)
    rw [hX]

/-- Active actual coefficients are the bilinear contraction of the two
rectangular boundary factors with the unchanged `A₀` bulk.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem mixedEndpointActiveBoundaryMap_apply
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (X : Matrix (Fin D₀ ⊕ Fin D₁) (Fin D₀ ⊕ Fin D₁) ℂ)
    (a e : Fin D₀ ⊕ Fin D₁) (b c : Fin D₀) (σ : Cfg (D₀ * D₀) N) :
    mixedEndpointActiveBoundaryMap A₀ A₁ N X (a, (b, σ, c), e) =
      endpointBoundaryTracePairing (Kraus.evalWord A₀ (List.ofFn σ)) X
        (mixedEndpointFirstBoundaryLetter A₀ a (.inl b))
        (mixedEndpointLastBoundaryLetter A₀ (.inl c) e) := by
  change insertedGroundSpaceMap _ _ _ _
    (Fin.cons _ (Fin.snoc (fun k => mixedEndpointFirstPhysicalIndex D₁ (σ k)) _)) = _
  rw [mixedEndpoint_insertedGroundSpaceMap_sectorFactors,
    trace_rectangular_boundary_reindex]
  rfl

/-- The two boundary normalizations transform the actual active extended
map into the common-core spectator map. The bulk tensor is unchanged.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem activeBoundaryNormalization_comp_actual_eq_coreSpectator
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (hA₀ : Kraus.IsInjective A₀) (N : ℕ) :
    (activeFirstBoundaryMap (D₁ := D₁) (squarePhysicalCoordinates A₀)⁻¹ N).comp
      ((activeLastBoundaryMap (D₁ := D₁) (squarePhysicalCoordinates A₀)⁻¹ N).comp
        (mixedEndpointActiveBoundaryMap A₀ A₁ N)) =
      endpointCoreSpectatorMap A₀ N (Fin D₀ ⊕ Fin D₁) := by
  apply LinearMap.ext
  intro X
  funext ⟨a, ⟨b, σ, c⟩, e⟩
  let B : Matrix (Fin D₀ ⊕ Fin D₁) (Fin D₀) ℂ →ₗ[ℂ]
      Matrix (Fin D₀) (Fin D₀ ⊕ Fin D₁) ℂ →ₗ[ℂ] ℂ :=
    endpointBoundaryTracePairing (Kraus.evalWord A₀ (List.ofFn σ)) X
  let L : ((Fin D₀ ⊕ Fin D₁) × Fin D₀) → Matrix (Fin D₀ ⊕ Fin D₁) (Fin D₀) ℂ :=
    fun p => mixedEndpointFirstBoundaryLetter A₀ p.1 (.inl p.2)
  let R : (Fin D₀ × (Fin D₀ ⊕ Fin D₁)) → Matrix (Fin D₀) (Fin D₀ ⊕ Fin D₁) ℂ :=
    fun p => mixedEndpointLastBoundaryLetter A₀ (.inl p.1) p.2
  change firstBoundaryCoordinateMap (squarePhysicalCoordinates A₀)⁻¹
    (fun p => lastBoundaryCoordinateMap (squarePhysicalCoordinates A₀)⁻¹
      (fun q => mixedEndpointActiveBoundaryMap A₀ A₁ N X
        (p.1, (p.2, σ, q.1), q.2)) (c, e)) (a, b) = _
  simp_rw [mixedEndpointActiveBoundaryMap_apply]
  change firstBoundaryCoordinateMap (squarePhysicalCoordinates A₀)⁻¹
    (fun p => lastBoundaryCoordinateMap (squarePhysicalCoordinates A₀)⁻¹
      (fun q => B (L p) (R q)) (c, e)) (a, b) = _
  simp_rw [lastBoundaryCoordinateMap_map]
  change firstBoundaryCoordinateMap (squarePhysicalCoordinates A₀)⁻¹
    (fun p => (B.flip (lastBoundaryCoordinateMap (squarePhysicalCoordinates A₀)⁻¹
      R (c, e))) (L p)) (a, b) = _
  rw [firstBoundaryCoordinateMap_map]
  change B (firstBoundaryCoordinateMap (squarePhysicalCoordinates A₀)⁻¹ L (a, b))
    (lastBoundaryCoordinateMap (squarePhysicalCoordinates A₀)⁻¹ R (c, e)) = _
  dsimp only [L, R]
  rw [firstBoundaryCoordinateMap_inv_actual_letters A₀ hA₀,
    lastBoundaryCoordinateMap_inv_actual_letters A₀ hA₀]
  change Matrix.trace (Matrix.single a b (1 : ℂ) * Kraus.evalWord A₀ (List.ofFn σ) *
      Matrix.single c e (1 : ℂ) * X) = Kraus.evalWord A₀ (List.ofFn σ) b c * X e a
  rw [Matrix.single_mul_mul_single, Matrix.trace_single_mul]
  simp

/-- Exact global range identification after the two physical boundary
changes. This is an image of the actual active range, with no hypothesis
about a many-body kernel or any spectral gap.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem map_range_activeBoundaryNormalization_eq_coreSpectator
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (hA₀ : Kraus.IsInjective A₀) (N : ℕ) :
    (mixedEndpointActiveBoundaryMap A₀ A₁ N).range.map
      ((activeFirstBoundaryMap (D₁ := D₁) (squarePhysicalCoordinates A₀)⁻¹ N).comp
        (activeLastBoundaryMap (D₁ := D₁) (squarePhysicalCoordinates A₀)⁻¹ N)) =
      (endpointCoreSpectatorMap A₀ N (Fin D₀ ⊕ Fin D₁)).range := by
  rw [← LinearMap.range_comp, LinearMap.comp_assoc,
    activeBoundaryNormalization_comp_actual_eq_coreSpectator A₀ A₁ hA₀ N]


/-- The actual active support is carried to the common-core support by a
linear equivalence, not merely by a possibly singular map.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem map_range_activeBoundaryNormalizationEquiv_eq_coreSpectator
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (hA₀ : Kraus.IsInjective A₀) (N : ℕ) :
    (mixedEndpointActiveBoundaryMap A₀ A₁ N).range.map
      (activeBoundaryNormalizationEquiv (D₁ := D₁) A₀ hA₀ N).toLinearMap =
      (endpointCoreSpectatorMap A₀ N (Fin D₀ ⊕ Fin D₁)).range := by
  rw [activeBoundaryNormalizationEquiv_toLinearMap]
  exact map_range_activeBoundaryNormalization_eq_coreSpectator A₀ A₁ hA₀ N

/-- Membership in the actual active support is equivalent to the explicit
spectator-factorization condition after the invertible boundary changes.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem mem_range_actualActive_iff_normalized_spectatorFactorization
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (hA₀ : Kraus.IsInjective A₀) (N : ℕ)
    (ψ : endpointActiveCfg (Fin D₀ ⊕ Fin D₁) D₀ N → ℂ) :
    ψ ∈ (mixedEndpointActiveBoundaryMap A₀ A₁ N).range ↔
      ∃ f : (Fin D₀ ⊕ Fin D₁) → (Fin D₀ ⊕ Fin D₁) → ℂ, ∀ a κ e,
        activeBoundaryNormalizationEquiv A₀ hA₀ N ψ (a, κ, e) =
          endpointCoreVector A₀ N κ * f e a := by
  rw [← mem_range_endpointCoreSpectatorMap_iff,
    ← map_range_activeBoundaryNormalizationEquiv_eq_coreSpectator A₀ A₁ hA₀ N]
  constructor
  · intro hψ
    exact ⟨ψ, hψ, rfl⟩
  · rintro ⟨φ, hφ, heq⟩
    have hφψ : φ = ψ := (activeBoundaryNormalizationEquiv A₀ hA₀ N).injective heq
    obtain ⟨X, hX⟩ := hφ
    exact ⟨X, hX.trans hφψ⟩

/-- The ordinary `A₀` chain, with the inverse physical coordinates applied
only at its two boundary sites, has the same common core. Its two exterior
spectators have dimension `D₀`, whereas the extended chain has dimension
`D₀ + D₁` there. This is a coefficient identity for the actual ordinary
boundary map, rather than an assumption about its support.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem normalized_groundSpaceMap_eq_coreSpectator
    (A₀ : MPSTensor (D₀ * D₀) D₀) (hA₀ : Kraus.IsInjective A₀)
    (X : Matrix (Fin D₀) (Fin D₀) ℂ) (a b c e : Fin D₀)
    (σ : Cfg (D₀ * D₀) N) :
    (∑ p : Fin (D₀ * D₀), ∑ q : Fin (D₀ * D₀),
      ((squarePhysicalCoordinates A₀)⁻¹ (finProdFinEquiv (a, b)) p *
        (squarePhysicalCoordinates A₀)⁻¹ (finProdFinEquiv (c, e)) q) •
      groundSpaceMap A₀ (N + 1 + 1) X (Fin.cons p (Fin.snoc σ q))) =
      endpointCoreSpectatorMap A₀ N (Fin D₀) X (a, (b, σ, c), e) := by
  let F := (squarePhysicalCoordinates A₀)⁻¹
  let M := Kraus.evalWord A₀ (List.ofFn σ)
  have hletter (r s : Fin D₀) :
      ∑ p : Fin (D₀ * D₀), F (finProdFinEquiv (r, s)) p • A₀ p =
        Matrix.single r s 1 := by
    simpa [F, rotatePhysical, matrixUnitPhysicalTensor] using
      congrArg (fun A : MPSTensor (D₀ * D₀) D₀ => A (finProdFinEquiv (r, s)))
        (rotatePhysical_inv_squarePhysicalCoordinates A₀ hA₀)
  have hword (p q : Fin (D₀ * D₀)) :
      groundSpaceMap A₀ (N + 1 + 1) X (Fin.cons p (Fin.snoc σ q)) =
        Matrix.trace (A₀ p * M * A₀ q * X) := by
    rw [groundSpaceMap_apply, List.ofFn_cons, List.ofFn_snoc,
      Kraus.evalWord_cons, Kraus.evalWord_append]
    simp only [Kraus.evalWord_cons, Kraus.evalWord_nil, Matrix.mul_one, M, Matrix.mul_assoc]
  change (∑ p, ∑ q, (F (finProdFinEquiv (a, b)) p *
      F (finProdFinEquiv (c, e)) q) •
      groundSpaceMap A₀ (N + 1 + 1) X (Fin.cons p (Fin.snoc σ q))) = M b c * X e a
  simp_rw [hword, ← Matrix.trace_smul, ← Matrix.trace_sum Finset.univ]
  have hmat :
      (∑ p, ∑ q, (F (finProdFinEquiv (a, b)) p * F (finProdFinEquiv (c, e)) q) •
        (A₀ p * M * A₀ q * X)) =
      (∑ p, F (finProdFinEquiv (a, b)) p • A₀ p) * M *
        (∑ q, F (finProdFinEquiv (c, e)) q • A₀ q) * X := by
    simp only [Finset.sum_mul, Finset.mul_sum]
    conv_rhs => rw [Finset.sum_comm]
    simp [Matrix.mul_assoc, smul_smul, mul_comm]
  rw [hmat, hletter, hletter, Matrix.single_mul_mul_single, Matrix.trace_single_mul]
  simp

end

end MPOSymmetry
end MPSTensor
