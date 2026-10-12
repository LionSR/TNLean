/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.Martingale.SpectatorGapEquivalence

/-!
# Norm gaps with dependent finite spectator coordinates

A finite family of active operators acts independently on coordinates
\(\Sigma_q I_q \times S_q\). Its kernel and kernel complement decompose into
the active fibers, and its squared norm is the sum of their squared norms.
For nonempty spectator fibers, a common nonnegative lower norm bound is
equivalent to the same bound for every active operator. Replacing the
nonempty spectator fibers therefore preserves that bound.

No positivity or symmetry assumption is needed, and the set of labels may be
empty. Identifying an actual Hamiltonian with this operator remains separate.
-/

open scoped BigOperators InnerProductSpace

namespace ContinuousLinearMap

section Sigma

variable {Q : Type*} {J : Q → Type*} [Fintype Q] [∀ q, Fintype (J q)]

/-- Restrict a vector on a dependent sum to one label. -/
noncomputable def sigmaFiber (x : EuclideanSpace ℂ (Σ q, J q)) (q : Q) :
    EuclideanSpace ℂ (J q) :=
  WithLp.toLp 2 fun i ↦ x ⟨q, i⟩

/-- Apply the operator assigned to each label independently on its fiber. -/
noncomputable def sigmaFiberwiseMap
    (G : ∀ q, EuclideanSpace ℂ (J q) →L[ℂ] EuclideanSpace ℂ (J q)) :
    EuclideanSpace ℂ (Σ q, J q) →L[ℂ] EuclideanSpace ℂ (Σ q, J q) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x ↦ WithLp.toLp 2 fun p ↦ G p.1 (sigmaFiber x p.1) p.2
      map_add' := by
        intro x y
        apply PiLp.ext
        rintro ⟨q, i⟩
        change G q (sigmaFiber (x + y) q) i = _
        rw [show sigmaFiber (x + y) q = sigmaFiber x q + sigmaFiber y q by
          apply PiLp.ext
          intro j
          rfl, map_add]
        rfl
      map_smul' := by
        intro c x
        apply PiLp.ext
        rintro ⟨q, i⟩
        change G q (sigmaFiber (c • x) q) i = _
        rw [show sigmaFiber (c • x) q = c • sigmaFiber x q by
          apply PiLp.ext
          intro j
          rfl, map_smul]
        rfl }

/-- The dependent sum operator evaluates using the selected active operator. -/
@[simp] theorem sigmaFiberwiseMap_apply_apply
    (G : ∀ q, EuclideanSpace ℂ (J q) →L[ℂ] EuclideanSpace ℂ (J q))
    (x : EuclideanSpace ℂ (Σ q, J q)) (q : Q) (i : J q) :
    sigmaFiberwiseMap G x ⟨q, i⟩ = G q (sigmaFiber x q) i := rfl

/-- Restriction to a label commutes with its assigned operator. -/
@[simp] theorem sigmaFiber_sigmaFiberwiseMap
    (G : ∀ q, EuclideanSpace ℂ (J q) →L[ℂ] EuclideanSpace ℂ (J q))
    (x : EuclideanSpace ℂ (Σ q, J q)) (q : Q) :
    sigmaFiber (sigmaFiberwiseMap G x) q = G q (sigmaFiber x q) := by
  apply PiLp.ext
  intro i
  rfl

/-- Membership in the kernel is equivalent to membership on every label. -/
theorem mem_ker_sigmaFiberwiseMap_iff
    (G : ∀ q, EuclideanSpace ℂ (J q) →L[ℂ] EuclideanSpace ℂ (J q))
    (x : EuclideanSpace ℂ (Σ q, J q)) :
    x ∈ LinearMap.ker (sigmaFiberwiseMap G).toLinearMap ↔
      ∀ q, sigmaFiber x q ∈ LinearMap.ker (G q).toLinearMap := by
  simp only [LinearMap.mem_ker]
  constructor
  · intro hx q
    apply PiLp.ext
    intro i
    exact congrArg (fun y : EuclideanSpace ℂ (Σ q, J q) ↦ y ⟨q, i⟩) hx
  · intro hx
    apply PiLp.ext
    rintro ⟨q, i⟩
    exact congrArg (fun y : EuclideanSpace ℂ (J q) ↦ y i) (hx q)

/-- The inner product is the sum of the inner products on the label fibers. -/
theorem inner_eq_sum_inner_sigmaFiber (x y : EuclideanSpace ℂ (Σ q, J q)) :
    ⟪x, y⟫_ℂ = ∑ q, ⟪sigmaFiber x q, sigmaFiber y q⟫_ℂ := by
  rw [PiLp.inner_apply, Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro q _
  rw [PiLp.inner_apply]
  rfl

/-- The squared norm is the sum of the squared norms on the label fibers. -/
theorem norm_sq_eq_sum_norm_sq_sigmaFiber (x : EuclideanSpace ℂ (Σ q, J q)) :
    ‖x‖ ^ 2 = ∑ q, ‖sigmaFiber x q‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro q _
  rw [EuclideanSpace.norm_sq_eq]
  rfl

/-- Extend a vector by zero outside one label. -/
noncomputable def singleSigmaFiber (q : Q) (x : EuclideanSpace ℂ (J q)) :
    EuclideanSpace ℂ (Σ q, J q) := by
  classical
  exact WithLp.toLp 2 fun p ↦
    (Pi.single (M := fun q ↦ EuclideanSpace ℂ (J q)) q x) p.1 p.2

omit [Fintype Q] [∀ q, Fintype (J q)] in
/-- Restricting an extension by zero gives the corresponding dependent single. -/
@[simp] theorem sigmaFiber_singleSigmaFiber [DecidableEq Q]
    (q r : Q) (x : EuclideanSpace ℂ (J q)) :
    sigmaFiber (singleSigmaFiber q x) r =
      Pi.single (M := fun q ↦ EuclideanSpace ℂ (J q)) q x r := by
  by_cases hr : r = q
  · subst r
    apply PiLp.ext
    intro i
    simp [sigmaFiber, singleSigmaFiber]
  · apply PiLp.ext
    intro i
    simp [sigmaFiber, singleSigmaFiber, hr]

/-- Extension by zero preserves the norm. -/
@[simp] theorem norm_singleSigmaFiber (q : Q) (x : EuclideanSpace ℂ (J q)) :
    ‖singleSigmaFiber q x‖ = ‖x‖ := by
  classical
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _),
    norm_sq_eq_sum_norm_sq_sigmaFiber, Finset.sum_eq_single q]
  · simp
  · intro r _ hr
    simp [hr]
  · simp

/-- The inner product against a vector supported on one label reads that fiber. -/
@[simp] theorem inner_singleSigmaFiber (q : Q) (x : EuclideanSpace ℂ (J q))
    (y : EuclideanSpace ℂ (Σ q, J q)) :
    ⟪singleSigmaFiber q x, y⟫_ℂ = ⟪x, sigmaFiber y q⟫_ℂ := by
  classical
  rw [inner_eq_sum_inner_sigmaFiber, Finset.sum_eq_single q]
  · simp
  · intro r _ hr
    simp [hr]
  · simp

/-- The dependent sum operator preserves support on one label. -/
@[simp] theorem sigmaFiberwiseMap_singleSigmaFiber
    (G : ∀ q, EuclideanSpace ℂ (J q) →L[ℂ] EuclideanSpace ℂ (J q))
    (q : Q) (x : EuclideanSpace ℂ (J q)) :
    sigmaFiberwiseMap G (singleSigmaFiber q x) = singleSigmaFiber q (G q x) := by
  classical
  apply PiLp.ext
  rintro ⟨r, i⟩
  rw [sigmaFiberwiseMap_apply_apply, sigmaFiber_singleSigmaFiber]
  by_cases hr : r = q
  · subst r
    simp [singleSigmaFiber]
  · simp [singleSigmaFiber, hr]

/-- Orthogonality to the kernel is equivalent to orthogonality on every label. -/
theorem mem_orthogonal_ker_sigmaFiberwiseMap_iff
    (G : ∀ q, EuclideanSpace ℂ (J q) →L[ℂ] EuclideanSpace ℂ (J q))
    (x : EuclideanSpace ℂ (Σ q, J q)) :
    x ∈ (LinearMap.ker (sigmaFiberwiseMap G).toLinearMap)ᗮ ↔
      ∀ q, sigmaFiber x q ∈ (LinearMap.ker (G q).toLinearMap)ᗮ := by
  classical
  constructor
  · intro hx q
    rw [Submodule.mem_orthogonal]
    intro y hy
    have hSingle : singleSigmaFiber q y ∈
        LinearMap.ker (sigmaFiberwiseMap G).toLinearMap := by
      rw [mem_ker_sigmaFiberwiseMap_iff]
      intro r
      by_cases hr : r = q
      · subst r
        simpa using hy
      · simp [hr]
    simpa using (Submodule.mem_orthogonal _ _).mp hx _ hSingle
  · intro hx
    rw [Submodule.mem_orthogonal]
    intro y hy
    rw [inner_eq_sum_inner_sigmaFiber]
    apply Finset.sum_eq_zero
    intro q _
    exact (Submodule.mem_orthogonal _ _).mp (hx q) _
      ((mem_ker_sigmaFiberwiseMap_iff G y).mp hy q)

/-- A common nonnegative norm gap on every label gives the same gap on the
dependent sum, including when the label type is empty. -/
theorem norm_gap_sigmaFiberwiseMap
    (G : ∀ q, EuclideanSpace ℂ (J q) →L[ℂ] EuclideanSpace ℂ (J q))
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hGap : ∀ q, ∀ x ∈ (LinearMap.ker (G q).toLinearMap)ᗮ, δ * ‖x‖ ≤ ‖G q x‖) :
    ∀ x ∈ (LinearMap.ker (sigmaFiberwiseMap G).toLinearMap)ᗮ,
      δ * ‖x‖ ≤ ‖sigmaFiberwiseMap G x‖ := by
  intro x hx
  have hFiber := (mem_orthogonal_ker_sigmaFiberwiseMap_iff G x).mp hx
  apply (sq_le_sq₀ (mul_nonneg hδ (norm_nonneg _)) (norm_nonneg _)).mp
  calc
    (δ * ‖x‖) ^ 2 = ∑ q, (δ * ‖sigmaFiber x q‖) ^ 2 := by
      rw [mul_pow, norm_sq_eq_sum_norm_sq_sigmaFiber, Finset.mul_sum]
      simp only [mul_pow]
    _ ≤ ∑ q, ‖G q (sigmaFiber x q)‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro q _
      exact (sq_le_sq₀ (mul_nonneg hδ (norm_nonneg _)) (norm_nonneg _)).mpr
        (hGap q _ (hFiber q))
    _ = ‖sigmaFiberwiseMap G x‖ ^ 2 := by
      rw [norm_sq_eq_sum_norm_sq_sigmaFiber]
      simp only [sigmaFiber_sigmaFiberwiseMap]

/-- A dependent sum has a given nonnegative norm gap exactly when every
operator in the family has that gap. The label type need not be nonempty. -/
theorem norm_gap_sigmaFiberwiseMap_iff
    (G : ∀ q, EuclideanSpace ℂ (J q) →L[ℂ] EuclideanSpace ℂ (J q))
    {δ : ℝ} (hδ : 0 ≤ δ) :
    (∀ x ∈ (LinearMap.ker (sigmaFiberwiseMap G).toLinearMap)ᗮ,
      δ * ‖x‖ ≤ ‖sigmaFiberwiseMap G x‖) ↔
      ∀ q, ∀ x ∈ (LinearMap.ker (G q).toLinearMap)ᗮ, δ * ‖x‖ ≤ ‖G q x‖ := by
  classical
  constructor
  · intro hGap q x hx
    have hSingle : singleSigmaFiber q x ∈
        (LinearMap.ker (sigmaFiberwiseMap G).toLinearMap)ᗮ := by
      rw [mem_orthogonal_ker_sigmaFiberwiseMap_iff]
      intro r
      by_cases hr : r = q
      · subst r
        simpa using hx
      · simp [hr]
    simpa only [sigmaFiberwiseMap_singleSigmaFiber, norm_singleSigmaFiber] using
      hGap (singleSigmaFiber q x) hSingle
  · exact norm_gap_sigmaFiberwiseMap G hδ

end Sigma

section DependentSpectator

variable {Q : Type*} {I S T : Q → Type*} [Fintype Q]
  [∀ q, Fintype (I q)] [∀ q, Fintype (S q)] [∀ q, Fintype (T q)]

/-- The active vector obtained by fixing a label and its spectator coordinate. -/
noncomputable def dependentRightFiber
    (x : EuclideanSpace ℂ (Σ q, I q × S q)) (q : Q) (s : S q) :
    EuclideanSpace ℂ (I q) :=
  rightFiber (sigmaFiber x q) s

/-- Apply the operator at each label independently over its spectator fiber. -/
noncomputable def dependentRightFiberwiseMap
    (G : ∀ q, EuclideanSpace ℂ (I q) →L[ℂ] EuclideanSpace ℂ (I q)) :
    EuclideanSpace ℂ (Σ q, I q × S q) →L[ℂ]
      EuclideanSpace ℂ (Σ q, I q × S q) :=
  sigmaFiberwiseMap fun q ↦ rightFiberwiseMap (S := S q) (G q)

/-- The dependent spectator operator acts on the chosen active fiber. -/
@[simp] theorem dependentRightFiberwiseMap_apply_apply
    (G : ∀ q, EuclideanSpace ℂ (I q) →L[ℂ] EuclideanSpace ℂ (I q))
    (x : EuclideanSpace ℂ (Σ q, I q × S q)) (q : Q) (i : I q) (s : S q) :
    dependentRightFiberwiseMap (S := S) G x ⟨q, i, s⟩ =
      G q (dependentRightFiber x q s) i := rfl

/-- Restricting the output to an active fiber gives its assigned operator. -/
@[simp] theorem dependentRightFiber_dependentRightFiberwiseMap
    (G : ∀ q, EuclideanSpace ℂ (I q) →L[ℂ] EuclideanSpace ℂ (I q))
    (x : EuclideanSpace ℂ (Σ q, I q × S q)) (q : Q) (s : S q) :
    dependentRightFiber (dependentRightFiberwiseMap (S := S) G x) q s =
      G q (dependentRightFiber x q s) := by
  apply PiLp.ext
  intro i
  rfl

/-- Kernel membership is equivalent to kernel membership on every active fiber. -/
theorem mem_ker_dependentRightFiberwiseMap_iff
    (G : ∀ q, EuclideanSpace ℂ (I q) →L[ℂ] EuclideanSpace ℂ (I q))
    (x : EuclideanSpace ℂ (Σ q, I q × S q)) :
    x ∈ LinearMap.ker (dependentRightFiberwiseMap (S := S) G).toLinearMap ↔
      ∀ q s, dependentRightFiber x q s ∈ LinearMap.ker (G q).toLinearMap := by
  simp only [dependentRightFiberwiseMap, mem_ker_sigmaFiberwiseMap_iff,
    mem_ker_rightFiberwiseMap_iff, dependentRightFiber]

/-- Orthogonality to the kernel is equivalent to orthogonality on every active fiber. -/
theorem mem_orthogonal_ker_dependentRightFiberwiseMap_iff
    (G : ∀ q, EuclideanSpace ℂ (I q) →L[ℂ] EuclideanSpace ℂ (I q))
    (x : EuclideanSpace ℂ (Σ q, I q × S q)) :
    x ∈ (LinearMap.ker (dependentRightFiberwiseMap (S := S) G).toLinearMap)ᗮ ↔
      ∀ q s, dependentRightFiber x q s ∈ (LinearMap.ker (G q).toLinearMap)ᗮ := by
  simp only [dependentRightFiberwiseMap, mem_orthogonal_ker_sigmaFiberwiseMap_iff,
    mem_orthogonal_ker_rightFiberwiseMap_iff, dependentRightFiber]

/-- The squared norm is the sum over labels and spectator coordinates. -/
theorem norm_sq_eq_sum_norm_sq_dependentRightFiber
    (x : EuclideanSpace ℂ (Σ q, I q × S q)) :
    ‖x‖ ^ 2 = ∑ q, ∑ s, ‖dependentRightFiber x q s‖ ^ 2 := by
  rw [norm_sq_eq_sum_norm_sq_sigmaFiber]
  simp only [norm_sq_eq_sum_norm_sq_rightFiber, dependentRightFiber]

/-- Common active norm gaps extend to dependent spectator fibers, including
empty spectator types. -/
theorem norm_gap_dependentRightFiberwiseMap
    (G : ∀ q, EuclideanSpace ℂ (I q) →L[ℂ] EuclideanSpace ℂ (I q))
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hGap : ∀ q, ∀ x ∈ (LinearMap.ker (G q).toLinearMap)ᗮ, δ * ‖x‖ ≤ ‖G q x‖) :
    ∀ x ∈ (LinearMap.ker (dependentRightFiberwiseMap (S := S) G).toLinearMap)ᗮ,
      δ * ‖x‖ ≤ ‖dependentRightFiberwiseMap (S := S) G x‖ :=
  norm_gap_sigmaFiberwiseMap _ hδ fun q ↦ norm_gap_rightFiberwiseMap (G q) hδ (hGap q)

/-- For nonempty spectator fibers, the extended operator has a common
nonnegative norm gap exactly when every active operator does. -/
theorem norm_gap_dependentRightFiberwiseMap_iff [∀ q, Nonempty (S q)]
    (G : ∀ q, EuclideanSpace ℂ (I q) →L[ℂ] EuclideanSpace ℂ (I q))
    {δ : ℝ} (hδ : 0 ≤ δ) :
    (∀ x ∈ (LinearMap.ker (dependentRightFiberwiseMap (S := S) G).toLinearMap)ᗮ,
      δ * ‖x‖ ≤ ‖dependentRightFiberwiseMap (S := S) G x‖) ↔
      ∀ q, ∀ x ∈ (LinearMap.ker (G q).toLinearMap)ᗮ, δ * ‖x‖ ≤ ‖G q x‖ := by
  exact (norm_gap_sigmaFiberwiseMap_iff
    (fun q ↦ rightFiberwiseMap (S := S q) (G q)) hδ).trans
      (forall_congr' fun q ↦ norm_gap_rightFiberwiseMap_iff (S := S q) (G q) hδ)

/-- Replacing each nonempty finite spectator fiber preserves a common
nonnegative norm gap, without any positivity assumption on the active operators. -/
theorem norm_gap_dependentRightFiberwiseMap_iff_dependentRightFiberwiseMap
    [∀ q, Nonempty (S q)] [∀ q, Nonempty (T q)]
    (G : ∀ q, EuclideanSpace ℂ (I q) →L[ℂ] EuclideanSpace ℂ (I q))
    {δ : ℝ} (hδ : 0 ≤ δ) :
    (∀ x ∈ (LinearMap.ker (dependentRightFiberwiseMap (S := S) G).toLinearMap)ᗮ,
      δ * ‖x‖ ≤ ‖dependentRightFiberwiseMap (S := S) G x‖) ↔
      ∀ x ∈ (LinearMap.ker (dependentRightFiberwiseMap (S := T) G).toLinearMap)ᗮ,
        δ * ‖x‖ ≤ ‖dependentRightFiberwiseMap (S := T) G x‖ :=
  (norm_gap_dependentRightFiberwiseMap_iff (S := S) G hδ).trans
    (norm_gap_dependentRightFiberwiseMap_iff (S := T) G hδ).symm

end DependentSpectator

end ContinuousLinearMap
