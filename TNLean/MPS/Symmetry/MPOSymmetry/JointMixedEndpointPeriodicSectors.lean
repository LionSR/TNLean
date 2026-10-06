/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.MPOSymmetry.JointMixedEndpointProjectorComparison
import TNLean.MPS.Symmetry.MPOSymmetry.MixedEndpointOpenSectors

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

open scoped BigOperators ComplexOrder InnerProductSpace Matrix

namespace MPSTensor.MPOSymmetry

variable {d₀ d₁ r N : ℕ} {D₀ D₁ : Fin r → ℕ}

/-- A translated row-phase selector is the selector at its actual cyclic
chain site. This holds for any local window length. -/
theorem periodicLocalInteractionES_jointMixedRowSector {R : ℕ}
    (hRN : R ≤ N) (i : Fin N) (site : Fin R) :
    periodicLocalInteractionES (jointMixedRowSector d₀ d₁ D₀ D₁ site) i =
      jointMixedRowSector d₀ d₁ D₀ D₁ (cyclicForwardSite i site.val) := by
  ext v σ
  rw [jointMixedRowSector_apply]
  change periodicLocalInteractionES
    (Matrix.toEuclideanLin (Matrix.diagonal fun ω => jointMixedRowWeight (ω site)))
      i v σ = _
  rw [periodicLocalInteractionES_diagonal_apply hRN]
  rfl

/-- A translated column-phase selector is the selector at its actual
cyclic chain site, including a site across the periodic seam. -/
theorem periodicLocalInteractionES_jointMixedColumnSector {R : ℕ}
    (hRN : R ≤ N) (i : Fin N) (site : Fin R) :
    periodicLocalInteractionES (jointMixedColumnSector d₀ d₁ D₀ D₁ site) i =
      jointMixedColumnSector d₀ d₁ D₀ D₁ (cyclicForwardSite i site.val) := by
  ext v σ
  rw [jointMixedColumnSector_apply]
  change periodicLocalInteractionES
    (Matrix.toEuclideanLin (Matrix.diagonal fun ω => jointMixedColumnWeight (ω site)))
      i v σ = _
  rw [periodicLocalInteractionES_diagonal_apply hRN]
  rfl

private theorem cyclicForwardSite_one_eq_finRotate (i : Fin N) :
    cyclicForwardSite i 1 = finRotate N i := by
  apply Fin.ext
  simp [cyclicForwardSite, finRotate_apply, Fin.add_def]

/-- Summing a fixed local row-phase selector around the ring counts each
chain row once, also for the second site of a two-site window. -/
theorem sum_periodicLocalInteractionES_jointMixedRowSector
    (hN : 2 ≤ N) (site : Fin 2) :
    (∑ i : Fin N,
      periodicLocalInteractionES (jointMixedRowSector d₀ d₁ D₀ D₁ site) i) =
      ∑ i : Fin N, jointMixedRowSector d₀ d₁ D₀ D₁ i := by
  simp_rw [periodicLocalInteractionES_jointMixedRowSector hN]
  fin_cases site
  · simp
  · simpa only [Fin.val_one, cyclicForwardSite_one_eq_finRotate] using
      (finRotate N).sum_comp (jointMixedRowSector d₀ d₁ D₀ D₁)

/-- Summing a fixed local column-phase selector around the ring counts
each chain column once. -/
theorem sum_periodicLocalInteractionES_jointMixedColumnSector
    (hN : 2 ≤ N) (site : Fin 2) :
    (∑ i : Fin N,
      periodicLocalInteractionES (jointMixedColumnSector d₀ d₁ D₀ D₁ site) i) =
      ∑ i : Fin N, jointMixedColumnSector d₀ d₁ D₀ D₁ i := by
  simp_rw [periodicLocalInteractionES_jointMixedColumnSector hN]
  fin_cases site
  · simp
  · simpa only [Fin.val_one, cyclicForwardSite_one_eq_finRotate] using
      (finRotate N).sum_comp (jointMixedColumnSector d₀ d₁ D₀ D₁)

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

private theorem euclidean_sum_apply {ι κ : Type*}
    (s : Finset ι) (v : ι → EuclideanSpace ℂ κ) (k : κ) :
    (∑ i ∈ s, v i) k = ∑ i ∈ s, v i k :=
  map_sum (PiLp.projₗ (𝕜 := ℂ) 2 (fun _ : κ => ℂ) k) v s

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
  simp only [jointMixedPeriodicPhasePenalty, LinearMap.sum_apply, euclidean_sum_apply,
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
      (LinearMap.ker (jointMixedPeriodicPhasePenalty d₀ d₁ D₀ D₁ N)).starProjection
        .toLinearMap := by
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
    jointMixedPeriodicPhasePenalty d₀ d₁ D₀ D₁ N =
      ∑ i : Fin N,
        (periodicLocalInteractionES (1 - jointMixedRowSector d₀ d₁ D₀ D₁ (0 : Fin 2)) i +
          periodicLocalInteractionES (1 - jointMixedColumnSector d₀ d₁ D₀ D₁ (1 : Fin 2)) i) := by
  simp only [jointMixedPeriodicPhasePenalty, periodicLocalInteractionES_sub,
    periodicLocalInteractionES_one hN, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    sum_periodicLocalInteractionES_jointMixedRowSector hN,
    sum_periodicLocalInteractionES_jointMixedColumnSector hN]

/-- Local inner-phase penalties are bounded by the actual extended
interaction. Cyclic summation counts each phase once, including at length two. -/
theorem jointMixedPeriodicPhasePenalty_le_twice
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x)) (hN : 2 ≤ N) :
    jointMixedPeriodicPhasePenalty d₀ d₁ D₀ D₁ N ≤
      (2 : ℂ) • periodicInteractionHamiltonianES
        (jointMixedEndpointParentInteraction A₀ A₁ 0).toLinearMap N := by
  have hcol (i : Fin N) := periodicLocalInteractionES_mono
    (jointMixedEndpoint_one_sub_columnSector_zero_le_parentInteraction A₀ A₁) i
  have hrow (i : Fin N) := periodicLocalInteractionES_mono
    (jointMixedEndpoint_one_sub_rowSector_one_le_parentInteraction A₀ A₁) i
  have h := Finset.sum_le_sum fun (i : Fin N) (_ : i ∈ Finset.univ) =>
    add_le_add (hrow i) (hcol i)
  simp only [periodicLocalInteractionES_sub, periodicLocalInteractionES_one hN,
    Finset.sum_add_distrib, Finset.sum_sub_distrib,
    sum_periodicLocalInteractionES_jointMixedRowSector hN,
    sum_periodicLocalInteractionES_jointMixedColumnSector hN] at h
  simpa only [jointMixedPeriodicPhasePenalty, periodicInteractionHamiltonianES,
    Finset.sum_add_distrib, Finset.sum_sub_distrib, two_smul] using h

/-- Every row phase commutes with every actual translated endpoint term. -/
theorem jointMixedRowSector_commute_periodicLocalInteraction
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x))
    (hN : 2 ≤ N) (i k : Fin N) :
    Commute (jointMixedRowSector d₀ d₁ D₀ D₁ k)
      (periodicLocalInteractionES (jointMixedEndpointParentInteraction A₀ A₁ 0).toLinearMap i) :=
  periodicLocalInteractionES_commute_siteDiagonal _ hN jointMixedRowWeight
    (jointMixedRowSector_commute_parentInteraction_zero A₀ A₁) i k

/-- Every column phase commutes with every actual translated endpoint term. -/
theorem jointMixedColumnSector_commute_periodicLocalInteraction
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x))
    (hN : 2 ≤ N) (i k : Fin N) :
    Commute (jointMixedColumnSector d₀ d₁ D₀ D₁ k)
      (periodicLocalInteractionES (jointMixedEndpointParentInteraction A₀ A₁ 0).toLinearMap i) :=
  periodicLocalInteractionES_commute_siteDiagonal _ hN jointMixedColumnWeight
    (jointMixedColumnSector_commute_parentInteraction_zero A₀ A₁) i k

/-- The full phase penalty commutes with the actual periodic endpoint
Hamiltonian, as a consequence of the individual physical phase actions. -/
theorem jointMixedPeriodicPhasePenalty_commute
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x)) (hN : 2 ≤ N) :
    Commute (jointMixedPeriodicPhasePenalty d₀ d₁ D₀ D₁ N)
      (periodicInteractionHamiltonianES
        (jointMixedEndpointParentInteraction A₀ A₁ 0).toLinearMap N) := by
  apply Commute.sum_right
  intro i _
  apply Commute.sum_left
  intro k _
  exact ((Commute.one_left _).sub_left
    (jointMixedRowSector_commute_periodicLocalInteraction A₀ A₁ hN i k)).add_left
      ((Commute.one_left _).sub_left
        (jointMixedColumnSector_commute_periodicLocalInteraction A₀ A₁ hN i k))

/-- The actual endpoint Hamiltonian reduces the concrete active
projection. Both the projection and its invariance are derived from the
physical phase conditions. -/
theorem jointMixedPeriodicActiveProjection_commute
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x)) (hN : 2 ≤ N) :
    Commute (jointMixedPeriodicActiveProjection d₀ d₁ D₀ D₁ N)
      (periodicInteractionHamiltonianES
        (jointMixedEndpointParentInteraction A₀ A₁ 0).toLinearMap N) := by
  let H := periodicInteractionHamiltonianES
    (jointMixedEndpointParentInteraction A₀ A₁ 0).toLinearMap N
  let S := LinearMap.ker (jointMixedPeriodicPhasePenalty d₀ d₁ D₀ D₁ N)
  have hH : H.IsPositive := periodicInteractionHamiltonianES_isPositive
    (jointMixedEndpointParentInteraction_isPositive A₀ A₁ 0) N
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
    1 - jointMixedPeriodicActiveProjection d₀ d₁ D₀ D₁ N ≤
      (2 : ℂ) • periodicInteractionHamiltonianES
        (jointMixedEndpointParentInteraction A₀ A₁ 0).toLinearMap N :=
  one_sub_jointMixedPeriodicActiveProjection_le.trans
    (jointMixedPeriodicPhasePenalty_le_twice A₀ A₁ hN)

end MPSTensor.MPOSymmetry
