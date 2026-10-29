/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Analysis.WeightedPositiveKernel
import TNLean.MPS.ParentHamiltonian.UncleGroundSpaceInclusion

/-!
# Local conditions for the actual uncle Hamiltonian kernel

The uncle interaction is a unitary conjugate of an orthogonal-complement
projection. Each cyclic restriction/adjoint summand is positive, and the
strictly positive averaging coefficient does not change their common
kernel. Thus the actual finite Hamiltonian vanishes exactly when every
cyclic restriction lies in the explicit uncle boundary space. The zero
physical dimension is handled directly through the empty configuration
space.

Source: arXiv:1210.6613, proof of Theorem thm:gs-subspace-uncle,
lines 1050–1073. This identifies the analytic kernel conditions; their
intersection and periodic closure still require separate algebraic proofs.
-/

noncomputable section

open scoped Matrix BigOperators InnerProductSpace

namespace MPSTensor

variable {d a b : ℕ}

/-- The actual uncle interaction is positive, with no injectivity premise.
Source: arXiv:1210.6613, the projector defining the uncle interaction and
proof of thm:gs-subspace-uncle, lines 1050–1073. -/
theorem uncleInteractionES_isPositive
    (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (L : Fin d → Matrix (Fin b) (Fin a) ℂ) :
    (uncleInteractionES A B R L).toLinearMap.IsPositive := by
  let e := blockedConfigLinearIsometryEquiv d 1 2
  change (e.toLinearMap ∘ₗ parentInteractionES (uncleTensor A B R L) 1 ∘ₗ
    e.symm.toLinearMap).IsPositive
  rw [← LinearIsometryEquiv.adjoint_toLinearMap_eq_symm]
  exact (parentInteractionES_isPositive (uncleTensor A B R L) 1).conj_adjoint e.toLinearMap

open scoped ComplexOrder in
/-- Every actual finite periodic uncle Hamiltonian is positive, including
empty configuration spaces and chain lengths. This is the positivity used
in the spectral conclusion of arXiv:1210.6613, proof of thm:gapless. -/
theorem uncleHamiltonianES_isPositive
    (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (L : Fin d → Matrix (Fin b) (Fin a) ℂ) (N : ℕ) :
    (uncleHamiltonianES A B R L N).toLinearMap.IsPositive := by
  classical
  rw [ContinuousLinearMap.isPositive_toLinearMap_iff]
  unfold uncleHamiltonianES
  apply ContinuousLinearMap.isPositive_sum
  intro i _
  apply ContinuousLinearMap.IsPositive.smul_of_nonneg _
    (inv_nonneg.mpr (Nat.cast_nonneg _))
  apply ContinuousLinearMap.isPositive_sum
  intro τ _
  apply (ContinuousLinearMap.isPositive_toLinearMap_iff _).mp
  change ((cyclicRestrictES (Fin.pos i) 2 i τ).adjoint ∘ₗ
    (uncleInteractionES A B R L).toLinearMap ∘ₗ
      cyclicRestrictES (Fin.pos i) 2 i τ).IsPositive
  exact (uncleInteractionES_isPositive A B R L).adjoint_conj
    (cyclicRestrictES (Fin.pos i) 2 i τ)

/-- Vanishing of the explicit uncle projector is exactly membership in its
blocked boundary space, transported to the original two physical sites.
Source: arXiv:1210.6613, eq:uncletensor-2site and the local kernel in
thm:gs-subspace-uncle, lines 1050–1073. -/
theorem uncleInteractionES_apply_eq_zero_iff
    (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (L : Fin d → Matrix (Fin b) (Fin a) ℂ)
    (v : EuclideanSpace ℂ (Cfg d 2)) :
    uncleInteractionES A B R L v = 0 ↔
      (blockedConfigLinearIsometryEquiv d 1 2).symm v ∈
        groundSpaceES (uncleTensor A B R L) 1 := by
  let e := blockedConfigLinearIsometryEquiv d 1 2
  have he : uncleInteractionES A B R L v = 0 ↔
      parentInteractionES (uncleTensor A B R L) 1 (e.symm v) = 0 := by
    change e (parentInteractionES (uncleTensor A B R L) 1 (e.symm v)) = 0 ↔ _
    exact e.map_eq_zero_iff
  rw [he]
  change (groundSpaceES (uncleTensor A B R L) 1)ᗮ.starProjection (e.symm v) = 0 ↔ _
  rw [Submodule.starProjection_orthogonal']
  simp only [sub_apply, one_apply_eq_self]
  rw [sub_eq_zero, eq_comm, Submodule.starProjection_eq_self_iff]

/-- The actual periodic uncle Hamiltonian vanishes exactly when every
cyclic two-site restriction lies in the explicit uncle local kernel.
This is the common-kernel step of arXiv:1210.6613,
thm:gs-subspace-uncle, lines 1050–1073. No perturbation injectivity is
assumed; classifying this intersection is a separate argument. -/
theorem uncleHamiltonianES_apply_eq_zero_iff
    (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (L : Fin d → Matrix (Fin b) (Fin a) ℂ)
    {N : ℕ} (hN : 2 ≤ N) (v : EuclideanSpace ℂ (Cfg d N)) :
    uncleHamiltonianES A B R L N v = 0 ↔
      ∀ (i : Fin N) (τ : Cfg d N),
        uncleInteractionES A B R L (cyclicRestrictES (Fin.pos i) 2 i τ v) = 0 := by
  classical
  let : NeZero N := ⟨by omega⟩
  by_cases hd : d = 0
  · subst d
    constructor
    · intro _ i τ
      exact Fin.elim0 (τ 0)
    · intro _
      let : IsEmpty (Cfg 0 N) := ⟨fun τ ↦ Fin.elim0 (τ 0)⟩
      simp [uncleHamiltonianES]
  let c : ℝ := ((d ^ 2 : ℕ) : ℝ)⁻¹
  have hc : 0 < c := inv_pos.mpr (Nat.cast_pos.mpr (pow_pos (Nat.pos_of_ne_zero hd) 2))
  let K : Fin N × Cfg d N → EuclideanSpace ℂ (Cfg d N) →ₗ[ℂ]
      EuclideanSpace ℂ (Cfg d N) := fun p ↦
    (cyclicRestrictES (Fin.pos p.1) 2 p.1 p.2).adjoint ∘ₗ
      (uncleInteractionES A B R L).toLinearMap ∘ₗ
        cyclicRestrictES (Fin.pos p.1) 2 p.1 p.2
  have hK : ∀ p, (K p).IsPositive := by
    intro p
    exact (uncleInteractionES_isPositive A B R L).adjoint_conj
      (cyclicRestrictES (Fin.pos p.1) 2 p.1 p.2)
  have hsum : (uncleHamiltonianES A B R L N).toLinearMap =
      ∑ p : Fin N × Cfg d N, (c : ℂ) • K p := by
    ext ψ
    simp [uncleHamiltonianES, K, c, Fintype.sum_prod_type, Finset.smul_sum]
  change (uncleHamiltonianES A B R L N).toLinearMap v = 0 ↔ _
  rw [hsum]
  refine (WeightedPositiveKernel.apply_weighted_sum_eq_zero_iff
    (w := fun _ : Fin N × Cfg d N ↦ c) (P := K) (fun _ ↦ hc) hK v).trans ?_
  constructor
  · intro h i τ
    have hz : Complex.re ⟪K (i, τ) v, v⟫_ℂ = 0 := by rw [h (i, τ)]; simp
    change Complex.re ⟪(cyclicRestrictES (Fin.pos i) 2 i τ).adjoint
      (uncleInteractionES A B R L (cyclicRestrictES (Fin.pos i) 2 i τ v)), v⟫_ℂ = 0 at hz
    rw [LinearMap.adjoint_inner_left] at hz
    exact (uncleInteractionES_isPositive A B R L).apply_eq_zero_of_re_inner_eq_zero hz
  · intro h ⟨i, τ⟩
    change (cyclicRestrictES (Fin.pos i) 2 i τ).adjoint
      (uncleInteractionES A B R L (cyclicRestrictES (Fin.pos i) 2 i τ v)) = 0
    rw [h i τ, map_zero]

end MPSTensor
