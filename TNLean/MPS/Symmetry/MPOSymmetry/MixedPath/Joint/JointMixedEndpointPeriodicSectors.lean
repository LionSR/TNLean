/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.MPOSymmetry.MixedPath.Joint.JointMixedEndpointProjectorComparison
import TNLean.MPS.Symmetry.MPOSymmetry.MixedPath.Gap.MixedEndpointOpenSectors

/-!
# Periodic phase penalties of the joint mixed endpoint

Every row and column phase on the ring contributes one complementary
projection to the phase penalty. This diagonal operator counts the exact
number of violated phases. Its kernel is the subspace supported on the
shared first endpoint alphabet at every site, with no separation of the
physical block labels inside that alphabet.

The actual endpoint Hamiltonian controls the phase penalty by a factor
two and preserves its kernel. All cyclic counting statements include rings
of length two, where both directed translates remain in the sum.

Source: GLM23, arXiv:2203.12563, Section 5, lines 1695–1777.
-/

open scoped BigOperators ComplexOrder InnerProductSpace Matrix MatrixOrder
open ManyBody.Interaction (translationInvariant)

namespace MPSTensor.MPOSymmetry

variable {d₀ d₁ r N : ℕ} {D₀ D₁ : Fin r → ℕ}

/-- A translated row-phase selector is the selector at its actual cyclic
chain site. This holds for any local window length. -/
theorem toEuclideanLin_translationInvariant_term_jointMixedRowWeight {R : ℕ}
    (hRN : R ≤ N) (i : Fin N) (site : Fin R) :
    haveI : NeZero N := NeZero.of_pos i.pos;
    Matrix.toEuclideanLin ((translationInvariant N (Matrix.diagonal
      fun ω : Cfg (jointMixedPhysicalDim d₀ d₁ D₀ D₁) R =>
        jointMixedRowWeight (ω site))).term i) =
      jointMixedRowSector d₀ d₁ D₀ D₁ (cyclicForwardSite i site.val) := by
  have : NeZero N := NeZero.of_pos i.pos
  have hs : i + Fin.castLE hRN site = cyclicForwardSite i site.val :=
    Fin.ext (by simp [cyclicForwardSite, Fin.add_def])
  rw [ManyBody.Interaction.translationInvariant_term_diagonal hRN]
  simp only [hs]
  rfl

/-- A translated column-phase selector is the selector at its actual
cyclic chain site, including a site across the periodic seam. -/
theorem toEuclideanLin_translationInvariant_term_jointMixedColumnWeight {R : ℕ}
    (hRN : R ≤ N) (i : Fin N) (site : Fin R) :
    haveI : NeZero N := NeZero.of_pos i.pos;
    Matrix.toEuclideanLin ((translationInvariant N (Matrix.diagonal
      fun ω : Cfg (jointMixedPhysicalDim d₀ d₁ D₀ D₁) R =>
        jointMixedColumnWeight (ω site))).term i) =
      jointMixedColumnSector d₀ d₁ D₀ D₁ (cyclicForwardSite i site.val) := by
  have : NeZero N := NeZero.of_pos i.pos
  have hs : i + Fin.castLE hRN site = cyclicForwardSite i site.val :=
    Fin.ext (by simp [cyclicForwardSite, Fin.add_def])
  rw [ManyBody.Interaction.translationInvariant_term_diagonal hRN]
  simp only [hs]
  rfl

private theorem cyclicForwardSite_one_eq_finRotate (i : Fin N) :
    cyclicForwardSite i 1 = finRotate N i := by
  apply Fin.ext
  simp [cyclicForwardSite, finRotate_apply, Fin.add_def]

/-- Summing a fixed local row-phase selector around the ring counts each
chain row once, also for the second site of a two-site window. -/
theorem sum_toEuclideanLin_translationInvariant_term_jointMixedRowWeight
    (hN : 2 ≤ N) (site : Fin 2) :
    haveI : NeZero N := ⟨by omega⟩;
    (∑ i : Fin N, Matrix.toEuclideanLin ((translationInvariant N (Matrix.diagonal
      fun ω : Cfg (jointMixedPhysicalDim d₀ d₁ D₀ D₁) 2 =>
        jointMixedRowWeight (ω site))).term i)) =
      ∑ i : Fin N, jointMixedRowSector d₀ d₁ D₀ D₁ i := by
  simp_rw [toEuclideanLin_translationInvariant_term_jointMixedRowWeight hN]
  fin_cases site
  · simp
  · simpa only [Fin.val_one, cyclicForwardSite_one_eq_finRotate] using
      Equiv.sum_comp (finRotate N) (jointMixedRowSector d₀ d₁ D₀ D₁)

/-- Summing a fixed local column-phase selector around the ring counts
each chain column once. -/
theorem sum_toEuclideanLin_translationInvariant_term_jointMixedColumnWeight
    (hN : 2 ≤ N) (site : Fin 2) :
    haveI : NeZero N := ⟨by omega⟩;
    (∑ i : Fin N, Matrix.toEuclideanLin ((translationInvariant N (Matrix.diagonal
      fun ω : Cfg (jointMixedPhysicalDim d₀ d₁ D₀ D₁) 2 =>
        jointMixedColumnWeight (ω site))).term i)) =
      ∑ i : Fin N, jointMixedColumnSector d₀ d₁ D₀ D₁ i := by
  simp_rw [toEuclideanLin_translationInvariant_term_jointMixedColumnWeight hN]
  fin_cases site
  · simp
  · simpa only [Fin.val_one, cyclicForwardSite_one_eq_finRotate] using
      Equiv.sum_comp (finRotate N) (jointMixedColumnSector d₀ d₁ D₀ D₁)

/-- The sum of all first-row and first-column phase penalties on a ring. -/
noncomputable def jointMixedPeriodicPhasePenalty
    (d₀ d₁ : ℕ) (D₀ D₁ : Fin r → ℕ) (N : ℕ) :
    EuclideanSpace ℂ (Cfg (jointMixedPhysicalDim d₀ d₁ D₀ D₁) N) →ₗ[ℂ]
      EuclideanSpace ℂ (Cfg (jointMixedPhysicalDim d₀ d₁ D₀ D₁) N) :=
  ∑ i : Fin N,
    ((1 - jointMixedRowSector d₀ d₁ D₀ D₁ i) +
      (1 - jointMixedColumnSector d₀ d₁ D₀ D₁ i))

/-- The phase penalty counts the failed row and column conditions at
every site, independently of the block tensors. -/
noncomputable def jointMixedPeriodicViolationCount
    (d₀ d₁ : ℕ) (D₀ D₁ : Fin r → ℕ) (N : ℕ)
    (σ : Cfg (jointMixedPhysicalDim d₀ d₁ D₀ D₁) N) : ℕ := by
  classical
  exact ∑ i : Fin N,
    ((if jointMixedRowWeight (σ i) = 1 then 0 else 1) +
      (if jointMixedColumnWeight (σ i) = 1 then 0 else 1))

/-- Every physical letter lies in the shared first endpoint alphabet. -/
def JointMixedPeriodicActive
    (σ : Cfg (jointMixedPhysicalDim d₀ d₁ D₀ D₁) N) : Prop :=
  ∀ i : Fin N, jointMixedRowWeight (σ i) = 1 ∧ jointMixedColumnWeight (σ i) = 1

private noncomputable local instance
    (σ : Cfg (jointMixedPhysicalDim d₀ d₁ D₀ D₁) N) :
    Decidable (JointMixedPeriodicActive σ) := Classical.propDecidable _

/-- The violation count vanishes precisely on the active configurations. -/
theorem jointMixedPeriodicViolationCount_eq_zero_iff
    (σ : Cfg (jointMixedPhysicalDim d₀ d₁ D₀ D₁) N) :
    jointMixedPeriodicViolationCount d₀ d₁ D₀ D₁ N σ = 0 ↔
      JointMixedPeriodicActive σ := by
  classical
  simp [jointMixedPeriodicViolationCount, JointMixedPeriodicActive,
    Finset.sum_eq_zero_iff]

open Classical in
private theorem one_sub_binary_eq_indicator {z : ℂ} (hz : z = 0 ∨ z = 1) :
    1 - z = ((if z = 1 then 0 else 1 : ℕ) : ℂ) := by
  rcases hz with rfl | rfl <;> simp

/-- Coordinate action of the periodic phase penalty is multiplication by
the exact nonnegative integer violation count. -/
theorem jointMixedPeriodicPhasePenalty_apply
    (v : EuclideanSpace ℂ (Cfg (jointMixedPhysicalDim d₀ d₁ D₀ D₁) N))
    (σ : Cfg (jointMixedPhysicalDim d₀ d₁ D₀ D₁) N) :
    jointMixedPeriodicPhasePenalty d₀ d₁ D₀ D₁ N v σ =
      (jointMixedPeriodicViolationCount d₀ d₁ D₀ D₁ N σ : ℂ) * v σ := by
  classical
  simp only [jointMixedPeriodicPhasePenalty, LinearMap.sum_apply, WithLp.ofLp_sum, Finset.sum_apply,
    LinearMap.add_apply, LinearMap.sub_apply, Module.End.one_apply, PiLp.add_apply,
    PiLp.sub_apply, jointMixedRowSector_apply, jointMixedColumnSector_apply]
  simp only [jointMixedPeriodicViolationCount, Nat.cast_sum, Nat.cast_add,
    Finset.sum_mul, add_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [← one_sub_binary_eq_indicator (jointMixedRowWeight_eq_zero_or_one (σ i)),
    ← one_sub_binary_eq_indicator (jointMixedColumnWeight_eq_zero_or_one (σ i))]
  ring

/-- A vector belongs to the penalty kernel precisely when its inactive
configuration coefficients vanish. -/
theorem mem_ker_jointMixedPeriodicPhasePenalty_iff
    (v : EuclideanSpace ℂ (Cfg (jointMixedPhysicalDim d₀ d₁ D₀ D₁) N)) :
    v ∈ LinearMap.ker (jointMixedPeriodicPhasePenalty d₀ d₁ D₀ D₁ N) ↔
      ∀ σ, ¬ JointMixedPeriodicActive σ → v σ = 0 := by
  classical
  rw [LinearMap.mem_ker]
  constructor
  · intro hv σ hσ
    have hc : jointMixedPeriodicViolationCount d₀ d₁ D₀ D₁ N σ ≠ 0 :=
      mt (jointMixedPeriodicViolationCount_eq_zero_iff σ).mp hσ
    have h := congrArg (fun w => w σ) hv
    rw [jointMixedPeriodicPhasePenalty_apply] at h
    exact (mul_eq_zero.mp h).resolve_left (Nat.cast_ne_zero.mpr hc)
  · intro hv
    apply PiLp.ext
    intro σ
    rw [jointMixedPeriodicPhasePenalty_apply]
    by_cases hσ : JointMixedPeriodicActive σ
    · rw [(jointMixedPeriodicViolationCount_eq_zero_iff σ).mpr hσ]
      simp
    · simp [hv σ hσ]

/-- The diagonal projection onto configurations with both phases zero at
every site. Shared physical block labels remain in the same subspace. -/
noncomputable def jointMixedPeriodicActiveProjection
    (d₀ d₁ : ℕ) (D₀ D₁ : Fin r → ℕ) (N : ℕ) :
    EuclideanSpace ℂ (Cfg (jointMixedPhysicalDim d₀ d₁ D₀ D₁) N) →ₗ[ℂ]
      EuclideanSpace ℂ (Cfg (jointMixedPhysicalDim d₀ d₁ D₀ D₁) N) := by
  classical
  exact Matrix.toEuclideanLin (Matrix.diagonal fun σ =>
    if JointMixedPeriodicActive σ then 1 else 0)

/-- The active projection keeps exactly the active configuration
coefficients. -/
theorem jointMixedPeriodicActiveProjection_apply
    (v : EuclideanSpace ℂ (Cfg (jointMixedPhysicalDim d₀ d₁ D₀ D₁) N))
    (σ : Cfg (jointMixedPhysicalDim d₀ d₁ D₀ D₁) N) :
    jointMixedPeriodicActiveProjection d₀ d₁ D₀ D₁ N v σ =
      if JointMixedPeriodicActive σ then v σ else 0 := by
  classical
  simp [jointMixedPeriodicActiveProjection, Matrix.toEuclideanLin,
    Matrix.toLpLin_apply, Matrix.mulVec_diagonal, ite_mul]

/-- The concrete active indicator is an orthogonal projection. -/
theorem jointMixedPeriodicActiveProjection_isSymmetricProjection :
    (jointMixedPeriodicActiveProjection d₀ d₁ D₀ D₁ N).IsSymmetricProjection := by
  classical
  constructor
  · ext v σ
    simp only [Module.End.mul_apply, jointMixedPeriodicActiveProjection_apply]
    split <;> simp_all
  · apply Matrix.isSymmetric_toEuclideanLin_iff.mpr
    apply Matrix.isHermitian_diagonal_of_self_adjoint
    funext σ
    simp only [Pi.star_apply]
    split <;> simp

/-- The range of the concrete active projection is the full penalty
kernel at every chain length. -/
theorem range_jointMixedPeriodicActiveProjection :
    LinearMap.range (jointMixedPeriodicActiveProjection d₀ d₁ D₀ D₁ N) =
      LinearMap.ker (jointMixedPeriodicPhasePenalty d₀ d₁ D₀ D₁ N) := by
  ext v
  rw [mem_ker_jointMixedPeriodicPhasePenalty_iff]
  constructor
  · rintro ⟨w, rfl⟩ σ hσ
    simp [jointMixedPeriodicActiveProjection_apply, hσ]
  · intro hv
    refine ⟨v, ?_⟩
    ext σ
    rw [jointMixedPeriodicActiveProjection_apply]
    split <;> simp_all

/-- The active indicator equals the orthogonal projector of the penalty
kernel. -/
theorem jointMixedPeriodicActiveProjection_eq_starProjection :
    jointMixedPeriodicActiveProjection d₀ d₁ D₀ D₁ N =
      (LinearMap.ker
        (jointMixedPeriodicPhasePenalty d₀ d₁ D₀ D₁ N)).starProjection.toLinearMap := by
  apply jointMixedPeriodicActiveProjection_isSymmetricProjection.ext
    (Submodule.isSymmetricProjection_starProjection _)
  rw [Submodule.range_starProjection, range_jointMixedPeriodicActiveProjection]

/-- The concrete active projection is annihilated by the entire phase
penalty. -/
theorem jointMixedPeriodicPhasePenalty_activeProjection :
    jointMixedPeriodicPhasePenalty d₀ d₁ D₀ D₁ N *
      jointMixedPeriodicActiveProjection d₀ d₁ D₀ D₁ N = 0 := by
  apply LinearMap.ext
  intro v
  exact LinearMap.mem_ker.mp
    (range_jointMixedPeriodicActiveProjection.le ⟨v, rfl⟩)

/-- Every inactive configuration violates at least one phase, so the
penalty dominates the complementary active projection. -/
theorem one_sub_jointMixedPeriodicActiveProjection_le :
    1 - jointMixedPeriodicActiveProjection d₀ d₁ D₀ D₁ N ≤
      jointMixedPeriodicPhasePenalty d₀ d₁ D₀ D₁ N := by
  classical
  let f : Cfg (jointMixedPhysicalDim d₀ d₁ D₀ D₁) N → ℂ := fun σ =>
    (jointMixedPeriodicViolationCount d₀ d₁ D₀ D₁ N σ : ℂ) -
      (if JointMixedPeriodicActive σ then 0 else 1)
  have hf : ∀ σ, 0 ≤ f σ := by
    intro σ
    by_cases hσ : JointMixedPeriodicActive σ
    · simp [f, hσ]
    · have hc : 1 ≤ jointMixedPeriodicViolationCount d₀ d₁ D₀ D₁ N σ :=
        Nat.one_le_iff_ne_zero.mpr
          (mt (jointMixedPeriodicViolationCount_eq_zero_iff σ).mp hσ)
      have hc' : (1 : ℂ) ≤ (jointMixedPeriodicViolationCount d₀ d₁ D₀ D₁ N σ : ℂ) := by
        exact_mod_cast hc
      simpa [f, hσ] using sub_nonneg.mpr hc'
  have heq : jointMixedPeriodicPhasePenalty d₀ d₁ D₀ D₁ N -
      (1 - jointMixedPeriodicActiveProjection d₀ d₁ D₀ D₁ N) =
      Matrix.toEuclideanLin (Matrix.diagonal f) := by
    ext v σ
    simp only [LinearMap.sub_apply, PiLp.sub_apply, Module.End.one_apply,
      jointMixedPeriodicPhasePenalty_apply, jointMixedPeriodicActiveProjection_apply]
    simp only [Matrix.toEuclideanLin, Matrix.toLpLin_apply, Matrix.mulVec_diagonal]
    dsimp [f]
    split <;> ring
  rw [LinearMap.le_def, heq, Matrix.isPositive_toEuclideanLin_iff]
  exact Matrix.PosSemidef.diagonal hf

/-- The sum of the outer row and column penalties of every two-site
window is exactly the per-site phase penalty. -/
theorem jointMixedPeriodicPhasePenalty_eq_sum_outer (hN : 2 ≤ N) :
    haveI : NeZero N := ⟨by omega⟩;
    jointMixedPeriodicPhasePenalty d₀ d₁ D₀ D₁ N =
      ∑ i : Fin N,
        (Matrix.toEuclideanLin ((translationInvariant N (1 - Matrix.diagonal
            fun ω : Cfg (jointMixedPhysicalDim d₀ d₁ D₀ D₁) 2 =>
              jointMixedRowWeight (ω 0))).term i) +
          Matrix.toEuclideanLin ((translationInvariant N (1 - Matrix.diagonal
            fun ω : Cfg (jointMixedPhysicalDim d₀ d₁ D₀ D₁) 2 =>
              jointMixedColumnWeight (ω 1))).term i)) := by
  have : NeZero N := ⟨by omega⟩
  have honeN : Matrix.toEuclideanLin (1 : Matrix (Cfg (jointMixedPhysicalDim d₀ d₁ D₀ D₁) N)
      (Cfg (jointMixedPhysicalDim d₀ d₁ D₀ D₁) N) ℂ) = 1 :=
    LinearMap.ext fun v => Matrix.toEuclideanLin_one_apply v
  simp only [jointMixedPeriodicPhasePenalty, ManyBody.Interaction.translationInvariant_term_sub,
    ManyBody.Interaction.translationInvariant_term_one hN, map_sub, honeN,
    Finset.sum_add_distrib, Finset.sum_sub_distrib,
    sum_toEuclideanLin_translationInvariant_term_jointMixedRowWeight hN,
    sum_toEuclideanLin_translationInvariant_term_jointMixedColumnWeight hN]

/-- Local inner-phase penalties are bounded by the actual extended
interaction. Cyclic summation counts each phase once, including at length two. -/
theorem jointMixedPeriodicPhasePenalty_le_twice
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x)) (hN : 2 ≤ N) :
    haveI : NeZero N := ⟨by omega⟩;
    jointMixedPeriodicPhasePenalty d₀ d₁ D₀ D₁ N ≤
      (2 : ℂ) • Matrix.toEuclideanLin
        (translationInvariant N (jointMixedEndpointParentInteraction A₀ A₁ 0)).hamiltonian := by
  have : NeZero N := ⟨by omega⟩
  let Rm : Matrix (Cfg (jointMixedPhysicalDim d₀ d₁ D₀ D₁) 2)
      (Cfg (jointMixedPhysicalDim d₀ d₁ D₀ D₁) 2) ℂ :=
    Matrix.diagonal fun ω => jointMixedRowWeight (ω 1)
  let Cm : Matrix (Cfg (jointMixedPhysicalDim d₀ d₁ D₀ D₁) 2)
      (Cfg (jointMixedPhysicalDim d₀ d₁ D₀ D₁) 2) ℂ :=
    Matrix.diagonal fun ω => jointMixedColumnWeight (ω 0)
  have hone : Matrix.toEuclideanLin (1 : Matrix (Cfg (jointMixedPhysicalDim d₀ d₁ D₀ D₁) 2)
      (Cfg (jointMixedPhysicalDim d₀ d₁ D₀ D₁) 2) ℂ) = 1 :=
    LinearMap.ext fun v => Matrix.toEuclideanLin_one_apply v
  have honeN : Matrix.toEuclideanLin (1 : Matrix (Cfg (jointMixedPhysicalDim d₀ d₁ D₀ D₁) N)
      (Cfg (jointMixedPhysicalDim d₀ d₁ D₀ D₁) N) ℂ) = 1 :=
    LinearMap.ext fun v => Matrix.toEuclideanLin_one_apply v
  have hrowM : 1 - Rm ≤ jointMixedEndpointParentInteraction A₀ A₁ 0 := by
    rw [← Matrix.toEuclideanLin_le_toEuclideanLin_iff]
    simpa only [map_sub, hone,
      show Matrix.toEuclideanLin Rm = jointMixedRowSector d₀ d₁ D₀ D₁ 1 from rfl] using
      jointMixedEndpoint_one_sub_rowSector_one_le_parentInteraction A₀ A₁
  have hcolM : 1 - Cm ≤ jointMixedEndpointParentInteraction A₀ A₁ 0 := by
    rw [← Matrix.toEuclideanLin_le_toEuclideanLin_iff]
    simpa only [map_sub, hone,
      show Matrix.toEuclideanLin Cm = jointMixedColumnSector d₀ d₁ D₀ D₁ 0 from rfl] using
      jointMixedEndpoint_one_sub_columnSector_zero_le_parentInteraction A₀ A₁
  have h := Finset.sum_le_sum fun (i : Fin N) (_ : i ∈ Finset.univ) =>
    add_le_add
      (Matrix.toEuclideanLin_le_toEuclideanLin_iff.mpr
        (ManyBody.Interaction.translationInvariant_term_mono (N := N) hrowM i))
      (Matrix.toEuclideanLin_le_toEuclideanLin_iff.mpr
        (ManyBody.Interaction.translationInvariant_term_mono (N := N) hcolM i))
  simp only [ManyBody.Interaction.translationInvariant_term_sub,
    ManyBody.Interaction.translationInvariant_term_one hN, map_sub, honeN, Rm, Cm,
    Finset.sum_add_distrib, Finset.sum_sub_distrib,
    sum_toEuclideanLin_translationInvariant_term_jointMixedRowWeight hN,
    sum_toEuclideanLin_translationInvariant_term_jointMixedColumnWeight hN] at h
  simpa only [jointMixedPeriodicPhasePenalty, ManyBody.Interaction.hamiltonian, map_sum,
    Finset.sum_add_distrib, Finset.sum_sub_distrib, two_smul] using h

/-- Every row phase commutes with every actual translated endpoint term. -/
theorem jointMixedRowSector_commute_translationInvariant_term
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x))
    (hN : 2 ≤ N) (i k : Fin N) :
    haveI : NeZero N := ⟨by omega⟩;
    Commute (jointMixedRowSector d₀ d₁ D₀ D₁ k)
      (Matrix.toEuclideanLin
        ((translationInvariant N (jointMixedEndpointParentInteraction A₀ A₁ 0)).term i)) :=
  ManyBody.Interaction.toEuclideanLin_translationInvariant_term_commute_siteDiagonal _ hN
    jointMixedRowWeight
    (jointMixedRowSector_commute_parentInteraction_zero A₀ A₁) i k

/-- Every column phase commutes with every actual translated endpoint term. -/
theorem jointMixedColumnSector_commute_translationInvariant_term
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x))
    (hN : 2 ≤ N) (i k : Fin N) :
    haveI : NeZero N := ⟨by omega⟩;
    Commute (jointMixedColumnSector d₀ d₁ D₀ D₁ k)
      (Matrix.toEuclideanLin
        ((translationInvariant N (jointMixedEndpointParentInteraction A₀ A₁ 0)).term i)) :=
  ManyBody.Interaction.toEuclideanLin_translationInvariant_term_commute_siteDiagonal _ hN
    jointMixedColumnWeight
    (jointMixedColumnSector_commute_parentInteraction_zero A₀ A₁) i k

/-- The full phase penalty commutes with the actual periodic endpoint
Hamiltonian, as a consequence of the individual physical phase actions. -/
theorem jointMixedPeriodicPhasePenalty_commute
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x)) (hN : 2 ≤ N) :
    haveI : NeZero N := ⟨by omega⟩;
    Commute (jointMixedPeriodicPhasePenalty d₀ d₁ D₀ D₁ N)
      (Matrix.toEuclideanLin
        (translationInvariant N
          (jointMixedEndpointParentInteraction A₀ A₁ 0)).hamiltonian) := by
  have : NeZero N := ⟨by omega⟩
  rw [ManyBody.Interaction.hamiltonian, map_sum]
  apply Commute.sum_right
  intro i _
  apply Commute.sum_left
  intro k _
  exact ((Commute.one_left _).sub_left
    (jointMixedRowSector_commute_translationInvariant_term A₀ A₁ hN i k)).add_left
      ((Commute.one_left _).sub_left
        (jointMixedColumnSector_commute_translationInvariant_term A₀ A₁ hN i k))

/-- The actual endpoint Hamiltonian reduces the concrete active
projection. Both the projection and its invariance are derived from the
physical phase conditions. -/
theorem jointMixedPeriodicActiveProjection_commute
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x)) (hN : 2 ≤ N) :
    haveI : NeZero N := ⟨by omega⟩;
    Commute (jointMixedPeriodicActiveProjection d₀ d₁ D₀ D₁ N)
      (Matrix.toEuclideanLin
        (translationInvariant N
          (jointMixedEndpointParentInteraction A₀ A₁ 0)).hamiltonian) := by
  have : NeZero N := ⟨by omega⟩
  let H := Matrix.toEuclideanLin
    (translationInvariant N (jointMixedEndpointParentInteraction A₀ A₁ 0)).hamiltonian
  let S := LinearMap.ker (jointMixedPeriodicPhasePenalty d₀ d₁ D₀ D₁ N)
  have hH : H.IsPositive := Matrix.isPositive_toEuclideanLin_iff.mpr
    (ManyBody.Interaction.posSemidef_hamiltonian_translationInvariant
      (posSemidef_jointMixedEndpointParentInteraction A₀ A₁ 0))
  have hS : S.map H ≤ S := by
    rintro _ ⟨v, hv, rfl⟩
    have hc := LinearMap.congr_fun (jointMixedPeriodicPhasePenalty_commute A₀ A₁ hN).eq v
    change jointMixedPeriodicPhasePenalty d₀ d₁ D₀ D₁ N (H v) =
      H (jointMixedPeriodicPhasePenalty d₀ d₁ D₀ D₁ N v) at hc
    rw [LinearMap.mem_ker.mp hv, map_zero] at hc
    exact hc
  rw [jointMixedPeriodicActiveProjection_eq_starProjection]
  exact (Submodule.commute_starProjection_of_invariant S H hH.isSymmetric hS).symm

/-- The complementary active projection is controlled by twice the
actual periodic endpoint Hamiltonian. -/
theorem one_sub_jointMixedPeriodicActiveProjection_le_twice
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x)) (hN : 2 ≤ N) :
    haveI : NeZero N := ⟨by omega⟩;
    1 - jointMixedPeriodicActiveProjection d₀ d₁ D₀ D₁ N ≤
      (2 : ℂ) • Matrix.toEuclideanLin
        (translationInvariant N (jointMixedEndpointParentInteraction A₀ A₁ 0)).hamiltonian :=
  one_sub_jointMixedPeriodicActiveProjection_le.trans
    (jointMixedPeriodicPhasePenalty_le_twice A₀ A₁ hN)

end MPSTensor.MPOSymmetry
