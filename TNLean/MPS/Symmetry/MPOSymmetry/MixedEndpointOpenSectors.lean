/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.MPOSymmetry.MixedEndpointOpenKernel

/-!
# Inner physical-sector penalties on the open mixed chain

At the first endpoint, each nonwrapping extended interaction fixes the first
physical column and the second physical row in the first sector. The sum of
their complementary projections is bounded by twice the actual open-chain
Hamiltonian. Its kernel consists exactly of configurations whose inner
registers are in that sector; the first row and last column remain free.

The diagonal projection onto this active subspace satisfies `1 − Q ≤ E`.
Consequently every vector in its complementary subspace has energy at least
one half of its squared norm for the actual extended Hamiltonian. These
statements do not require injectivity and do not assert a whole-path gap.

Source: arXiv:2203.12563, Section 5, lines 1690–1692.
-/

open scoped BigOperators ComplexOrder InnerProductSpace Matrix

namespace MPSTensor

private theorem euclidean_sum_apply {ι κ : Type*}
    (s : Finset ι) (v : ι → EuclideanSpace ℂ κ) (k : κ) :
    (∑ i ∈ s, v i) k = ∑ i ∈ s, v i k := by
  exact map_sum (PiLp.projₗ (𝕜 := ℂ) 2 (fun _ : κ => ℂ) k) v s

private theorem diagonal_toEuclideanLin_apply {ι : Type*} [Fintype ι]
    [DecidableEq ι] (f : ι → ℂ) (v : EuclideanSpace ℂ ι) (i : ι) :
    Matrix.toEuclideanLin (Matrix.diagonal f) v i = f i * v i := by
  simp [Matrix.toEuclideanLin, Matrix.toLpLin_apply, Matrix.mulVec_diagonal]

/-- A translated interaction acts on the active-coordinate fiber of a
configuration. -/
theorem periodicLocalInteractionES_apply_fiber {d R N : ℕ}
    (h : EuclideanSpace ℂ (Cfg d R) →ₗ[ℂ] EuclideanSpace ℂ (Cfg d R))
    (hRN : R ≤ N) (i : Fin N) (v : EuclideanSpace ℂ (Cfg d N)) (σ : Cfg d N) :
    periodicLocalInteractionES h i v σ =
      h (WithLp.toLp 2 fun ω => v ((cyclicActiveBlockConfigEquiv d R hRN i).symm
        (ω, (cyclicActiveBlockConfigEquiv d R hRN i σ).2)))
        (cyclicActiveBlockConfigEquiv d R hRN i σ).1 := by
  unfold periodicLocalInteractionES
  rw [dite_eq_left hRN]
  change ((cyclicActiveBlockConfigLinearIsometryEquiv d R hRN i).symm
    (ContinuousLinearMap.rightFiberwiseMap (S := Cfg d (N - R))
      (LinearMap.toContinuousLinearMap h)
      (cyclicActiveBlockConfigLinearIsometryEquiv d R hRN i v))) σ = _
  rw [cyclicActiveBlockConfigLinearIsometryEquiv_symm_apply_apply]
  have hfiber :
      ContinuousLinearMap.rightFiber
          (cyclicActiveBlockConfigLinearIsometryEquiv d R hRN i v)
          (cyclicActiveBlockConfigEquiv d R hRN i σ).2 =
        (WithLp.toLp 2 (fun ω =>
          v ((cyclicActiveBlockConfigEquiv d R hRN i).symm
            (ω, (cyclicActiveBlockConfigEquiv d R hRN i σ).2))) :
          EuclideanSpace ℂ (Cfg d R)) := by
    apply PiLp.ext
    intro ω
    exact cyclicActiveBlockConfigLinearIsometryEquiv_apply_apply hRN i v _
  change h
      (ContinuousLinearMap.rightFiber
        (cyclicActiveBlockConfigLinearIsometryEquiv d R hRN i v)
        (cyclicActiveBlockConfigEquiv d R hRN i σ).2)
      (cyclicActiveBlockConfigEquiv d R hRN i σ).1 = _
  rw [hfiber]

private theorem commute_periodicLocalInteractionES_diagonal {d R N : ℕ}
    (h : EuclideanSpace ℂ (Cfg d R) →ₗ[ℂ] EuclideanSpace ℂ (Cfg d R))
    (hRN : R ≤ N) (i : Fin N) (f : Cfg d N → ℂ)
    (hf : ∀ s : Cfg d (N - R), Commute
      (Matrix.toEuclideanLin (Matrix.diagonal fun ω =>
        f ((cyclicActiveBlockConfigEquiv d R hRN i).symm (ω, s)))) h) :
    Commute (Matrix.toEuclideanLin (Matrix.diagonal f))
      (periodicLocalInteractionES h i) := by
  classical
  apply (commute_iff_eq _ _).mpr
  apply LinearMap.ext
  intro v
  apply PiLp.ext
  intro σ
  let e := cyclicActiveBlockConfigEquiv d R hRN i
  let w : EuclideanSpace ℂ (Cfg d R) :=
    WithLp.toLp 2 fun ω => v (e.symm (ω, (e σ).2))
  have hw : (WithLp.toLp 2 fun ω =>
      f (e.symm (ω, (e σ).2)) * v (e.symm (ω, (e σ).2))) =
      Matrix.toEuclideanLin (Matrix.diagonal fun ω => f (e.symm (ω, (e σ).2))) w := by
    apply PiLp.ext
    intro ω
    simp only [diagonal_toEuclideanLin_apply]
    rfl
  have hc := congrArg (fun T => T w (e σ).1) (hf (e σ).2).eq
  simp only [Module.End.mul_apply, diagonal_toEuclideanLin_apply] at hc
  simp only [Module.End.mul_apply, diagonal_toEuclideanLin_apply,
    periodicLocalInteractionES_apply_fiber h hRN]
  change f σ * h w (e σ).1 = h _ (e σ).1
  rw [hw]
  simpa only [e, Prod.mk.eta, Equiv.symm_apply_apply] using hc

/-- If a local interaction commutes with a chosen single-site diagonal
observable at every local site, every translate commutes with that observable
at every chain site, including spectator sites. -/
theorem periodicLocalInteractionES_commute_siteDiagonal {d R N : ℕ}
    (h : EuclideanSpace ℂ (Cfg d R) →ₗ[ℂ] EuclideanSpace ℂ (Cfg d R))
    (hRN : R ≤ N) (f : Fin d → ℂ)
    (hf : ∀ r : Fin R,
      Commute (Matrix.toEuclideanLin (Matrix.diagonal fun ω : Cfg d R => f (ω r))) h)
    (i k : Fin N) :
    Commute (Matrix.toEuclideanLin (Matrix.diagonal fun σ : Cfg d N => f (σ k)))
      (periodicLocalInteractionES h i) := by
  classical
  apply commute_periodicLocalInteractionES_diagonal h hRN i
  intro s
  let x := (cyclicWindowIndexEquiv R N hRN i).symm k
  have hk : cyclicWindowIndexEquiv R N hRN i x = k := by simp [x]
  rcases x with r | r
  · rw [← hk, cyclicWindowIndexEquiv_inl]
    change Commute
      (Matrix.toEuclideanLin (Matrix.diagonal fun ω : Cfg d R =>
        f ((cyclicActiveBlockConfigEquiv d R hRN i).symm (ω, s)
          (cyclicForwardSite i r.val)))) h
    simpa only [cyclicActiveBlockConfigEquiv_symm_apply_window] using hf r
  · rw [← hk, cyclicWindowIndexEquiv_inr]
    have hsite :
        (⟨(i.val + R + r.val) % N, Nat.mod_lt _ (Fin.pos i)⟩ : Fin N) =
          cyclicForwardSite i (R + r.val) := by
      apply Fin.ext
      simp only [cyclicForwardSite, Fin.val_mk, Nat.add_assoc]
    rw [hsite]
    simp only [cyclicActiveBlockConfigEquiv_symm_apply_spectator]
    apply (commute_iff_eq _ _).mpr
    apply LinearMap.ext
    intro v
    apply PiLp.ext
    intro ω
    simp only [Module.End.mul_apply, diagonal_toEuclideanLin_apply]
    have hconst : Matrix.toEuclideanLin (Matrix.diagonal fun _ : Cfg d R => f (s r)) v =
        f (s r) • v := by
      apply PiLp.ext
      intro τ
      simp only [diagonal_toEuclideanLin_apply, PiLp.smul_apply, smul_eq_mul]
    simp only [hconst, map_smul, PiLp.smul_apply, smul_eq_mul]

namespace MPOSymmetry

variable {D₀ D₁ N : ℕ}

/-- The explicit sum of the inner column and row penalties over the
nonwrapping bonds. Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
noncomputable def mixedEndpointOpenInnerPenalty (D₀ D₁ N : ℕ) :
    EuclideanSpace ℂ (Cfg ((D₀ + D₁) * (D₀ + D₁)) N) →ₗ[ℂ]
      EuclideanSpace ℂ (Cfg ((D₀ + D₁) * (D₀ + D₁)) N) :=
  ∑ i : NonwrappingStart 2 N,
    ((1 - periodicLocalInteractionES (mixedEndpointColumnSector D₀ D₁ 0) i.1) +
      (1 - periodicLocalInteractionES (mixedEndpointRowSector D₀ D₁ 1) i.1))

/-- The actual open extended interaction controls both inner register
penalties, without assumptions on either endpoint tensor.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem mixedEndpointOpenInnerPenalty_le_twice
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (hN : 2 ≤ N) :
    mixedEndpointOpenInnerPenalty D₀ D₁ N ≤
      (2 : ℂ) • openInteractionHamiltonianES
        (mixedEndpointParentInteraction A₀ A₁ 0).toLinearMap N := by
  have hcol (i : NonwrappingStart 2 N) := periodicLocalInteractionES_mono
    (mixedEndpoint_one_sub_columnSector_zero_le_parentInteraction A₀ A₁) i.1
  have hrow (i : NonwrappingStart 2 N) := periodicLocalInteractionES_mono
    (mixedEndpoint_one_sub_rowSector_one_le_parentInteraction A₀ A₁) i.1
  simp only [periodicLocalInteractionES_sub, periodicLocalInteractionES_one hN] at hcol hrow
  have h := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => add_le_add (hcol i) (hrow i)
  simpa only [mixedEndpointOpenInnerPenalty, openInteractionHamiltonianES,
    Finset.sum_add_distrib, two_smul] using h

/-- Count violated inner registers, one column and one row on every
nonwrapping bond. This is a nonnegative integer, independent of the endpoint
tensors. Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
noncomputable def mixedEndpointOpenInnerViolationCount (D₀ D₁ N : ℕ)
    (σ : Cfg ((D₀ + D₁) * (D₀ + D₁)) N) : ℕ := by
  classical
  exact ∑ i : NonwrappingStart 2 N,
    ((if bondInterpolationWeight D₀ D₁ 0
      (finProdFinEquiv.symm (extractWindow 2 i.1 σ 0)).2 = 1 then 0 else 1) +
      (if bondInterpolationWeight D₀ D₁ 0
        (finProdFinEquiv.symm (extractWindow 2 i.1 σ 1)).1 = 1 then 0 else 1))

/-- A configuration has all inner registers in the first sector. The first
row and the last column are deliberately unconstrained.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
def MixedEndpointOpenInnerActive
    (σ : Cfg ((D₀ + D₁) * (D₀ + D₁)) N) : Prop :=
  ∀ i : NonwrappingStart 2 N,
    bondInterpolationWeight D₀ D₁ 0
        (finProdFinEquiv.symm (extractWindow 2 i.1 σ 0)).2 = 1 ∧
      bondInterpolationWeight D₀ D₁ 0
        (finProdFinEquiv.symm (extractWindow 2 i.1 σ 1)).1 = 1

private noncomputable local instance
    (σ : Cfg ((D₀ + D₁) * (D₀ + D₁)) N) :
    Decidable (MixedEndpointOpenInnerActive σ) := Classical.propDecidable _

/-- Zero violations are equivalent to the explicit inner-register
constraints. Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem mixedEndpointOpenInnerViolationCount_eq_zero_iff
    (σ : Cfg ((D₀ + D₁) * (D₀ + D₁)) N) :
    mixedEndpointOpenInnerViolationCount D₀ D₁ N σ = 0 ↔
      MixedEndpointOpenInnerActive σ := by
  classical
  simp [mixedEndpointOpenInnerViolationCount, MixedEndpointOpenInnerActive,
    Finset.sum_eq_zero_iff]

open Classical in
private theorem one_sub_bondInterpolationWeight_zero (p : Fin (D₀ + D₁)) :
    1 - bondInterpolationWeight D₀ D₁ 0 p =
      ((if bondInterpolationWeight D₀ D₁ 0 p = 1 then 0 else 1 : ℕ) : ℂ) := by
  classical
  unfold bondInterpolationWeight
  split <;> simp

/-- The penalty acts diagonally by the exact number of violated inner
registers. Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem mixedEndpointOpenInnerPenalty_apply (hN : 2 ≤ N)
    (v : EuclideanSpace ℂ (Cfg ((D₀ + D₁) * (D₀ + D₁)) N))
    (σ : Cfg ((D₀ + D₁) * (D₀ + D₁)) N) :
    mixedEndpointOpenInnerPenalty D₀ D₁ N v σ =
      (mixedEndpointOpenInnerViolationCount D₀ D₁ N σ : ℂ) * v σ := by
  classical
  simp only [mixedEndpointOpenInnerPenalty, LinearMap.sum_apply, euclidean_sum_apply,
    LinearMap.add_apply, LinearMap.sub_apply, Module.End.one_apply, PiLp.add_apply,
    PiLp.sub_apply, mixedEndpointColumnSector, mixedEndpointRowSector,
    periodicLocalInteractionES_diagonal_apply hN]
  simp only [mixedEndpointOpenInnerViolationCount, Nat.cast_sum, Nat.cast_add,
    Finset.sum_mul, add_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [← one_sub_bondInterpolationWeight_zero, ← one_sub_bondInterpolationWeight_zero]
  ring

/-- The common kernel of the inner penalties is precisely the vectors
supported on the active configurations. No support assertion is assumed.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem mem_ker_mixedEndpointOpenInnerPenalty_iff (hN : 2 ≤ N)
    (v : EuclideanSpace ℂ (Cfg ((D₀ + D₁) * (D₀ + D₁)) N)) :
    v ∈ LinearMap.ker (mixedEndpointOpenInnerPenalty D₀ D₁ N) ↔
      ∀ σ, ¬ MixedEndpointOpenInnerActive σ → v σ = 0 := by
  classical
  rw [LinearMap.mem_ker]
  constructor
  · intro hv σ hσ
    have hc : mixedEndpointOpenInnerViolationCount D₀ D₁ N σ ≠ 0 :=
      mt (mixedEndpointOpenInnerViolationCount_eq_zero_iff σ).mp hσ
    have h := congrArg (fun w => w σ) hv
    rw [mixedEndpointOpenInnerPenalty_apply hN] at h
    exact (mul_eq_zero.mp h).resolve_left (Nat.cast_ne_zero.mpr hc)
  · intro hv
    apply PiLp.ext
    intro σ
    rw [mixedEndpointOpenInnerPenalty_apply hN]
    by_cases hσ : MixedEndpointOpenInnerActive σ
    · rw [(mixedEndpointOpenInnerViolationCount_eq_zero_iff σ).mpr hσ]
      simp
    · simp [hv σ hσ]

/-- Orthogonal projection onto configurations satisfying every inner-sector
constraint. Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
noncomputable def mixedEndpointOpenActiveProjection (D₀ D₁ N : ℕ) :
    EuclideanSpace ℂ (Cfg ((D₀ + D₁) * (D₀ + D₁)) N) →ₗ[ℂ]
      EuclideanSpace ℂ (Cfg ((D₀ + D₁) * (D₀ + D₁)) N) := by
  classical
  exact Matrix.toEuclideanLin (Matrix.diagonal fun σ =>
    if MixedEndpointOpenInnerActive σ then 1 else 0)

/-- Coordinate action of the active-sector projection. -/
theorem mixedEndpointOpenActiveProjection_apply
    (v : EuclideanSpace ℂ (Cfg ((D₀ + D₁) * (D₀ + D₁)) N))
    (σ : Cfg ((D₀ + D₁) * (D₀ + D₁)) N) :
    mixedEndpointOpenActiveProjection D₀ D₁ N v σ =
      if MixedEndpointOpenInnerActive σ then v σ else 0 := by
  classical
  simp [mixedEndpointOpenActiveProjection, Matrix.toEuclideanLin,
    Matrix.toLpLin_apply, Matrix.mulVec_diagonal, ite_mul]

/-- The active-sector indicator is an orthogonal projection. -/
theorem mixedEndpointOpenActiveProjection_isSymmetricProjection :
    (mixedEndpointOpenActiveProjection D₀ D₁ N).IsSymmetricProjection := by
  classical
  constructor
  · apply LinearMap.ext
    intro v
    apply PiLp.ext
    intro σ
    simp only [Module.End.mul_apply, mixedEndpointOpenActiveProjection_apply]
    split <;> simp_all
  · apply Matrix.isSymmetric_toEuclideanLin_iff.mpr
    apply Matrix.isHermitian_diagonal_of_self_adjoint
    funext σ
    simp only [Pi.star_apply]
    split <;> simp

/-- The active projection has exactly the kernel of the inner penalty as
its range. Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem range_mixedEndpointOpenActiveProjection (hN : 2 ≤ N) :
    LinearMap.range (mixedEndpointOpenActiveProjection D₀ D₁ N) =
      LinearMap.ker (mixedEndpointOpenInnerPenalty D₀ D₁ N) := by
  ext v
  rw [mem_ker_mixedEndpointOpenInnerPenalty_iff hN]
  constructor
  · rintro ⟨w, rfl⟩ σ hσ
    simp [mixedEndpointOpenActiveProjection_apply, hσ]
  · intro hv
    refine ⟨v, ?_⟩
    apply PiLp.ext
    intro σ
    rw [mixedEndpointOpenActiveProjection_apply]
    split <;> simp_all

/-- The diagonal active projection is the orthogonal kernel projector of
the explicit inner penalty. Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem mixedEndpointOpenActiveProjection_eq_starProjection (hN : 2 ≤ N) :
    mixedEndpointOpenActiveProjection D₀ D₁ N =
      (LinearMap.ker (mixedEndpointOpenInnerPenalty D₀ D₁ N)).starProjection.toLinearMap := by
  apply mixedEndpointOpenActiveProjection_isSymmetricProjection.ext
    (Submodule.isSymmetricProjection_starProjection _)
  rw [Submodule.range_starProjection, range_mixedEndpointOpenActiveProjection hN]

/-- Each inactive configuration violates at least one inner constraint,
so its complementary projection is bounded by the explicit penalty.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem one_sub_mixedEndpointOpenActiveProjection_le (hN : 2 ≤ N) :
    1 - mixedEndpointOpenActiveProjection D₀ D₁ N ≤
      mixedEndpointOpenInnerPenalty D₀ D₁ N := by
  classical
  let f : Cfg ((D₀ + D₁) * (D₀ + D₁)) N → ℂ := fun σ =>
    (mixedEndpointOpenInnerViolationCount D₀ D₁ N σ : ℂ) -
      (if MixedEndpointOpenInnerActive σ then 0 else 1)
  have hf : ∀ σ, 0 ≤ f σ := by
    intro σ
    by_cases hσ : MixedEndpointOpenInnerActive σ
    · simp [f, hσ]
    · have hc : 1 ≤ mixedEndpointOpenInnerViolationCount D₀ D₁ N σ :=
        Nat.one_le_iff_ne_zero.mpr
          (mt (mixedEndpointOpenInnerViolationCount_eq_zero_iff σ).mp hσ)
      have hc' : (1 : ℂ) ≤ (mixedEndpointOpenInnerViolationCount D₀ D₁ N σ : ℂ) := by
        exact_mod_cast hc
      simpa [f, hσ] using sub_nonneg.mpr hc'
  have heq : mixedEndpointOpenInnerPenalty D₀ D₁ N -
      (1 - mixedEndpointOpenActiveProjection D₀ D₁ N) =
      Matrix.toEuclideanLin (Matrix.diagonal f) := by
    ext v σ
    simp only [LinearMap.sub_apply, PiLp.sub_apply, Module.End.one_apply,
      mixedEndpointOpenInnerPenalty_apply hN, mixedEndpointOpenActiveProjection_apply]
    simp only [Matrix.toEuclideanLin, Matrix.toLpLin_apply, Matrix.mulVec_diagonal]
    dsimp [f]
    split <;> ring
  rw [LinearMap.le_def, heq, Matrix.isPositive_toEuclideanLin_iff]
  exact Matrix.PosSemidef.diagonal hf

/-- The explicit active-sector complement is controlled by twice the
actual extended open Hamiltonian. This is derived from its local support.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem one_sub_mixedEndpointOpenActiveProjection_le_twice
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (hN : 2 ≤ N) :
    1 - mixedEndpointOpenActiveProjection D₀ D₁ N ≤
      (2 : ℂ) • openInteractionHamiltonianES
        (mixedEndpointParentInteraction A₀ A₁ 0).toLinearMap N :=
  (one_sub_mixedEndpointOpenActiveProjection_le hN).trans
    (mixedEndpointOpenInnerPenalty_le_twice A₀ A₁ hN)

/-- The active constraints are exactly the column constraints away from
the right boundary and the row constraints away from the left boundary.
In particular neither the first row nor the last column is constrained.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem mixedEndpointOpenInnerActive_iff
    (σ : Cfg ((D₀ + D₁) * (D₀ + D₁)) N) :
    MixedEndpointOpenInnerActive σ ↔
      (∀ k : Fin N, k.val + 1 < N →
        bondInterpolationWeight D₀ D₁ 0 (finProdFinEquiv.symm (σ k)).2 = 1) ∧
      (∀ k : Fin N, 0 < k.val →
        bondInterpolationWeight D₀ D₁ 0 (finProdFinEquiv.symm (σ k)).1 = 1) := by
  have hzero (i : NonwrappingStart 2 N) : extractWindow 2 i.1 σ 0 = σ i.1 := by
    simp [extractWindow, Nat.mod_eq_of_lt i.1.isLt]
  have hone (i : NonwrappingStart 2 N) :
      extractWindow 2 i.1 σ 1 = σ ⟨i.1.val + 1, by have := i.2; omega⟩ := by
    apply congrArg σ
    apply Fin.ext
    simp [Nat.mod_eq_of_lt (show i.1.val + 1 < N by have := i.2; omega)]
  constructor
  · intro hσ
    constructor
    · intro k hk
      have h := (hσ ⟨k, by omega⟩).1
      rwa [hzero] at h
    · intro k hk
      let i : NonwrappingStart 2 N := ⟨⟨k.val - 1, by omega⟩, by
        change k.val - 1 + 2 ≤ N
        omega⟩
      have h := (hσ i).2
      rw [hone] at h
      have heq : (⟨i.1.val + 1, by have := i.2; omega⟩ : Fin N) = k := by
        apply Fin.ext
        dsimp [i]
        omega
      rwa [heq] at h
  · rintro ⟨hcol, hrow⟩ i
    rw [hzero, hone]
    exact ⟨hcol i.1 (by have := i.2; omega), hrow _ (by simp)⟩

/-- A vector orthogonal to the active sector has energy at least one half
of its squared norm. This does not assert a gap inside the active sector.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem mixedEndpointOpen_inactive_energy_lower_bound
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (hN : 2 ≤ N)
    (v : EuclideanSpace ℂ (Cfg ((D₀ + D₁) * (D₀ + D₁)) N))
    (hv : mixedEndpointOpenActiveProjection D₀ D₁ N v = 0) :
    (1 / 2 : ℝ) * ‖v‖ ^ 2 ≤
      (inner ℂ v (openInteractionHamiltonianES
        (mixedEndpointParentInteraction A₀ A₁ 0).toLinearMap N v)).re := by
  have hpos := (LinearMap.le_def.mp
    (one_sub_mixedEndpointOpenActiveProjection_le_twice A₀ A₁ hN)).re_inner_nonneg_right v
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, hv,
    sub_zero, inner_sub_right, inner_smul_right, map_sub, inner_self_eq_norm_sq] at hpos
  norm_num at hpos
  linarith


private theorem commute_projection_of_invariant
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (S : Submodule ℂ E) [S.HasOrthogonalProjection]
    (Q : E →ₗ[ℂ] E) (hQ : Q.IsSymmetric) (hS : S.map Q ≤ S) :
    Commute Q S.starProjection.toLinearMap := by
  have hmem (v : E) (hv : v ∈ S) : Q v ∈ S := hS ⟨v, hv, rfl⟩
  apply (commute_iff_eq _ _).mpr
  apply LinearMap.ext
  intro v
  change Q (S.starProjection v) = S.starProjection (Q v)
  symm
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero (K := S)
  · exact hmem _ (S.starProjection_apply_mem v)
  · intro w hw
    rw [← map_sub, hQ]
    exact Submodule.starProjection_inner_eq_zero (K := S) v (Q w) (hmem w hw)

/-- Both local row selectors reduce the actual extended first-endpoint
interaction. The inner selector fixes its support, while the outer selector
acts by boundary transport. Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem mixedEndpointRowSector_commute_parentInteraction_zero
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁) (r : Fin 2) :
    Commute (mixedEndpointRowSector D₀ D₁ r)
      (mixedEndpointParentInteraction A₀ A₁ 0).toLinearMap := by
  have hs : Commute (mixedEndpointRowSector D₀ D₁ r)
      (insertedTwoSiteMap (mixedEndpointBase A₀ A₁)
        (bondInterpolationMatrix D₀ D₁ 0)).range.starProjection.toLinearMap := by
    fin_cases r
    · exact mixedEndpointRowSector_commute_extendedSupport_starProjection A₀ A₁ _
    · apply commute_projection_of_invariant _ _ (mixedEndpointRowSector_isSymmetric 1)
      rintro _ ⟨_, ⟨v, rfl⟩, rfl⟩
      exact ⟨v, (mixedEndpointRowSector_one_insertedTwoSiteMap A₀ A₁ v).symm⟩
  exact (Commute.one_right _).sub_right hs

/-- Both local column selectors reduce the actual extended first-endpoint
interaction. Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem mixedEndpointColumnSector_commute_parentInteraction_zero
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁) (r : Fin 2) :
    Commute (mixedEndpointColumnSector D₀ D₁ r)
      (mixedEndpointParentInteraction A₀ A₁ 0).toLinearMap := by
  have hs : Commute (mixedEndpointColumnSector D₀ D₁ r)
      (insertedTwoSiteMap (mixedEndpointBase A₀ A₁)
        (bondInterpolationMatrix D₀ D₁ 0)).range.starProjection.toLinearMap := by
    fin_cases r
    · apply commute_projection_of_invariant _ _ (mixedEndpointColumnSector_isSymmetric 0)
      rintro _ ⟨_, ⟨v, rfl⟩, rfl⟩
      exact ⟨v, (mixedEndpointColumnSector_zero_insertedTwoSiteMap A₀ A₁ v).symm⟩
    · exact mixedEndpointColumnSector_commute_extendedSupport_starProjection A₀ A₁ _
  exact (Commute.one_right _).sub_right hs

/-- The first-sector row selector at an arbitrary site of the open chain.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
noncomputable def mixedEndpointChainRowSector (D₀ D₁ : ℕ) (k : Fin N) :
    EuclideanSpace ℂ (Cfg ((D₀ + D₁) * (D₀ + D₁)) N) →ₗ[ℂ]
      EuclideanSpace ℂ (Cfg ((D₀ + D₁) * (D₀ + D₁)) N) :=
  Matrix.toEuclideanLin (Matrix.diagonal fun σ =>
    bondInterpolationWeight D₀ D₁ 0 (finProdFinEquiv.symm (σ k)).1)

/-- The first-sector column selector at an arbitrary site of the open chain.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
noncomputable def mixedEndpointChainColumnSector (D₀ D₁ : ℕ) (k : Fin N) :
    EuclideanSpace ℂ (Cfg ((D₀ + D₁) * (D₀ + D₁)) N) →ₗ[ℂ]
      EuclideanSpace ℂ (Cfg ((D₀ + D₁) * (D₀ + D₁)) N) :=
  Matrix.toEuclideanLin (Matrix.diagonal fun σ =>
    bondInterpolationWeight D₀ D₁ 0 (finProdFinEquiv.symm (σ k)).2)

/-- Every physical row sector reduces the actual open endpoint Hamiltonian,
including the free first row. No global commutation is assumed.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem mixedEndpointChainRowSector_commute_openInteractionHamiltonianES
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (hN : 2 ≤ N) (k : Fin N) :
    Commute (mixedEndpointChainRowSector D₀ D₁ k)
      (openInteractionHamiltonianES (mixedEndpointParentInteraction A₀ A₁ 0).toLinearMap N) := by
  apply Commute.sum_right
  intro i _
  exact periodicLocalInteractionES_commute_siteDiagonal _ hN
    (fun p => bondInterpolationWeight D₀ D₁ 0 (finProdFinEquiv.symm p).1)
    (mixedEndpointRowSector_commute_parentInteraction_zero A₀ A₁) i.1 k

/-- Every physical column sector reduces the actual open endpoint
Hamiltonian, including the free last column.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem mixedEndpointChainColumnSector_commute_openInteractionHamiltonianES
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (hN : 2 ≤ N) (k : Fin N) :
    Commute (mixedEndpointChainColumnSector D₀ D₁ k)
      (openInteractionHamiltonianES (mixedEndpointParentInteraction A₀ A₁ 0).toLinearMap N) := by
  apply Commute.sum_right
  intro i _
  exact periodicLocalInteractionES_commute_siteDiagonal _ hN
    (fun p => bondInterpolationWeight D₀ D₁ 0 (finProdFinEquiv.symm p).2)
    (mixedEndpointColumnSector_commute_parentInteraction_zero A₀ A₁) i.1 k

/-- The explicit sum of inner-sector penalties commutes with the actual
extended open Hamiltonian. Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem mixedEndpointOpenInnerPenalty_commute_openInteractionHamiltonianES
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (hN : 2 ≤ N) :
    Commute (mixedEndpointOpenInnerPenalty D₀ D₁ N)
      (openInteractionHamiltonianES (mixedEndpointParentInteraction A₀ A₁ 0).toLinearMap N) := by
  apply Commute.sum_left
  intro i _
  have hcol : periodicLocalInteractionES (mixedEndpointColumnSector D₀ D₁ 0) i.1 =
      mixedEndpointChainColumnSector D₀ D₁ i.1 := by
    ext v σ
    simp [mixedEndpointColumnSector, mixedEndpointChainColumnSector,
      periodicLocalInteractionES_diagonal_apply hN, diagonal_toEuclideanLin_apply,
      extractWindow, Nat.mod_eq_of_lt i.1.isLt]
  have hrow : periodicLocalInteractionES (mixedEndpointRowSector D₀ D₁ 1) i.1 =
      mixedEndpointChainRowSector D₀ D₁ (cyclicForwardSite i.1 1) := by
    ext v σ
    simp [mixedEndpointRowSector, mixedEndpointChainRowSector,
      periodicLocalInteractionES_diagonal_apply hN, diagonal_toEuclideanLin_apply,
      extractWindow, cyclicForwardSite]
  rw [hcol, hrow]
  exact ((Commute.one_left _).sub_left
    (mixedEndpointChainColumnSector_commute_openInteractionHamiltonianES A₀ A₁ hN i.1)).add_left
      ((Commute.one_left _).sub_left
        (mixedEndpointChainRowSector_commute_openInteractionHamiltonianES A₀ A₁ hN _))

/-- The actual open Hamiltonian preserves the active sector and its
orthogonal complement. This is derived from the local sector actions.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem mixedEndpointOpenActiveProjection_commute_openInteractionHamiltonianES
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (hN : 2 ≤ N) :
    Commute (mixedEndpointOpenActiveProjection D₀ D₁ N)
      (openInteractionHamiltonianES (mixedEndpointParentInteraction A₀ A₁ 0).toLinearMap N) := by
  let E := EuclideanSpace ℂ (Cfg ((D₀ + D₁) * (D₀ + D₁)) N)
  let H : E →ₗ[ℂ] E :=
    openInteractionHamiltonianES (mixedEndpointParentInteraction A₀ A₁ 0).toLinearMap N
  let S : Submodule ℂ E := LinearMap.ker (mixedEndpointOpenInnerPenalty D₀ D₁ N)
  have hpos : H.IsPositive := by
    apply LinearMap.nonneg_iff_isPositive.mp
    exact Finset.sum_nonneg fun i _ => LinearMap.nonneg_iff_isPositive.mpr
      (periodicLocalInteractionES_isPositive
        (mixedEndpointParentInteraction_isPositive A₀ A₁ 0) i.1)
  have hS : S.map H ≤ S := by
    rintro _ ⟨v, hv, rfl⟩
    have hc := congrArg (fun T => T v)
      (mixedEndpointOpenInnerPenalty_commute_openInteractionHamiltonianES A₀ A₁ hN).eq
    change mixedEndpointOpenInnerPenalty D₀ D₁ N (H v) =
      H (mixedEndpointOpenInnerPenalty D₀ D₁ N v) at hc
    rw [LinearMap.mem_ker.mp hv, map_zero] at hc
    exact hc
  have hQ : mixedEndpointOpenActiveProjection D₀ D₁ N = S.starProjection.toLinearMap :=
    mixedEndpointOpenActiveProjection_eq_starProjection hN
  rw [hQ]
  exact (commute_projection_of_invariant S H hpos.isSymmetric hS).symm

end MPOSymmetry
end MPSTensor
