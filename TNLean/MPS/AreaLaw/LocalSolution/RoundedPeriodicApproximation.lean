/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.LocalSolution.RoundedPeriodicCoarsening
import TNLean.MPS.AreaLaw.LocalSolution.PeriodicChainApproximation
import TNLean.Lattice.GaussianFilteredTerm
import TNLean.Algebra.MatrixHermitianSum

/-!
# The quadratic logarithmic hierarchy on an arbitrary periodic chain

The periodic local terms determine the coarse operators and every spectral projection.
The derived bound `K=8ℓJ` equals `J_eff*r` for `r=ηℓ` and `J_eff=8J/η`, independently
of physical chain length. The chosen integer radius is an explicit quadratic
logarithm of the original number of sites and automatically satisfies the length
inequality for the number of blocks that this very radius produces.

The local residual estimate of equation `low` remains an input. The final physical
count uses the preceding localization estimate between each full Gaussian-filtered
term and its truncated approximation. The full filtered terms sum to the original
Hamiltonian; no small difference between an unfiltered interaction and its filtered
version is assumed. The only spectral gap is that of the original Hamiltonian.

**Local fix (periodic hierarchy):** the deficiency uses the corrected recurrence
and one additional spectral window treats the closing edge, as recorded in
`docs/paper-gaps/hastings05_hierarchical_projection.tex` and
`docs/paper-gaps/hastings05_hierarchical_energy.tex`.

Source: Hastings, arXiv:cond-mat/0508554v3, Section II, lines 609–730.
-/

open Matrix QuantumCircuit
open scoped Matrix.Norms.L2Operator InnerProductSpace

namespace TNLean.MPS.AreaLaw.LocalSolution

/-- The hierarchy determined by the actual rounded periodic pair operators.
Hastings, arXiv:cond-mat/0508554v3, Section II, lines 609–730. -/
noncomputable def roundedPeriodicProjection {M d : ℕ} (ℓ : ℕ)
    (a : Fin M → Matrix (Fin M → Fin d) (Fin M → Fin d) ℂ)
    (ψ : EuclideanSpace ℂ (Fin M → Fin d)) (J r : ℝ) :=
  periodicHierarchyProjection (extendFiniteEdges (roundedPeriodicOperator ℓ a)) ψ
    (8 * (ℓ : ℝ) * J) r (finiteHierarchyDepth (roundedPeriodicBlockCount M ℓ))

/-- Actual local residuals on an arbitrary periodic chain give a nearby retained unit vector.
Hastings, arXiv:cond-mat/0508554v3, Section II, lines 609–730. -/
theorem exists_unit_mem_roundedPeriodicProjection {M ℓ d : ℕ} (hℓ : 0 < ℓ)
    (a : Fin M → Matrix (Fin M → Fin d) (Fin M → Fin d) ℂ)
    (hsupp : ∀ i, a i ∈ supportedOperators d {v | roundedPeriodicDistance i v ≤ ℓ})
    (ha : ∀ i, (a i).IsHermitian) {ψ : EuclideanSpace ℂ (Fin M → Fin d)} (hψ : ‖ψ‖ = 1)
    {J η Δ r : ℝ} (hJ : 0 < J)
    (hr : hierarchyProjectionLength (finiteHierarchyDepth (roundedPeriodicBlockCount M ℓ))
      (8 * J / η) Δ ≤ r)
    (hres : ∀ i, ‖toEuclideanLin
      (a i - ((⟪ψ, toEuclideanLin (a i) ψ⟫_ℂ).re : ℂ) • 1) ψ‖ ≤ J * Real.exp (-r))
    (hbound : ∀ i, ‖a i‖ ≤ J) :
    let b := roundedPeriodicOperator ℓ a
    let h := finiteHierarchyDepth (roundedPeriodicBlockCount M ℓ)
    let K := 8 * (ℓ : ℝ) * J
    ∃ φ : EuclideanSpace ℂ (Fin M → Fin d), ‖φ‖ = 1 ∧
      toEuclideanLin (roundedPeriodicProjection ℓ a ψ J r) φ = φ ∧
      ‖φ - ψ‖ ≤ 2 * (((3 : ℝ) ^ (h + 1) - 1) * Real.exp (-r / 8)) ∧
      IsRetainedHierarchy
        (hierarchyProjection (hierarchyEdge (extendFiniteEdges b))
          (fun m k ↦ (⟪ψ, toEuclideanLin (hierarchyEdge (extendFiniteEdges b) m k) ψ⟫_ℂ).re)
          (hierarchyWindowRadius K r h)) h 0 φ := by
  have hℓr : (0 : ℝ) < ℓ := by exact_mod_cast hℓ
  have hK : 0 < 8 * (ℓ : ℝ) * J := by positivity
  apply exists_unit_mem_periodicHierarchyProjection_of_finite
    (ι := Fin M) (d := d) (N := roundedPeriodicBlockCount M ℓ)
    (h := finiteHierarchyDepth (roundedPeriodicBlockCount M ℓ))
    (roundedPeriodicBlock (roundedPeriodicBlockCount M ℓ) ℓ) (roundedPeriodicOperator ℓ a)
    (roundedPeriodicOperator_mem_supportedOperators hℓ a hsupp)
    (isHermitian_roundedPeriodicOperator a ha) hψ hK
    (two_le_finiteHierarchyDepth (roundedPeriodicBlockCount M ℓ)) hr
    _ (centeredNorm_roundedPeriodicOperator_le hℓ a hψ hJ.le hbound)
  intro j
  have hresj := residual_roundedPeriodicOperator_le hℓ a ψ
    (mul_nonneg hJ.le (Real.exp_pos _).le) hres j
  push_cast at hresj
  nlinarith [mul_nonneg (mul_nonneg hℓr.le hJ.le) (Real.exp_pos (-r)).le]

/-- The source-facing physical count uses the small error between the full Gaussian-filtered
terms and their truncated approximations; the unfiltered physical terms need not be close.
Hastings, arXiv:cond-mat/0508554v3, Section II, lines 609–730. -/
theorem card_le_two_mul_re_trace_of_roundedPeriodicProjection {M ℓ d : ℕ} (hℓ : 0 < ℓ)
    (a g : Fin M → Matrix (Fin M → Fin d) (Fin M → Fin d) ℂ)
    (hsupp : ∀ i, a i ∈ supportedOperators d {v | roundedPeriodicDistance i v ≤ ℓ})
    (ha : ∀ i, (a i).IsHermitian) (hg : ∀ i, (g i).IsHermitian)
    {ψ : EuclideanSpace ℂ (Fin M → Fin d)} (hψ : ‖ψ‖ = 1)
    {J η Δ r q : ℝ} (hJ : 0 < J) (hη : 0 < η) (hΔ : 0 < Δ)
    (hrscale : r = η * (ℓ : ℝ))
    (hr : hierarchyProjectionLength (finiteHierarchyDepth (roundedPeriodicBlockCount M ℓ))
      (8 * J / η) Δ ≤ r)
    (herror : ∀ i, ‖TNLean.Lattice.gaussianFilteredTerm q Δ (∑ k, g k) (g i) - a i‖ ≤
      J * Real.exp (-r))
    {P₀ : Matrix (Fin M → Fin d) (Fin M → Fin d) ℂ} (hP₀ : IsStarProjection P₀) {E₀ : ℝ}
    (hgap : ∀ v : EuclideanSpace ℂ (Fin M → Fin d),
      Δ * (‖v‖ ^ 2 - (⟪v, toEuclideanLin P₀ v⟫_ℂ).re) ≤
        (⟪v, toEuclideanLin (∑ i, g i) v⟫_ℂ).re - E₀ * ‖v‖ ^ 2)
    (hE₀ : (⟪ψ, toEuclideanLin (∑ i, g i) ψ⟫_ℂ).re = E₀)
    {κ : Type*} {φ : κ → EuclideanSpace ℂ (Fin M → Fin d)}
    (hφ : Orthonormal ℂ φ) (s : Finset κ)
    (hkeep : ∀ j ∈ s,
      toEuclideanLin (roundedPeriodicProjection ℓ a ψ J r) (φ j) = φ j) :
    (s.card : ℝ) ≤ 2 * (trace P₀).re := by
  let N := roundedPeriodicBlockCount M ℓ
  let b := roundedPeriodicOperator ℓ a
  let h := finiteHierarchyDepth N
  let K : ℝ := 8 * (ℓ : ℝ) * J
  let Jeff : ℝ := 8 * J / η
  have hℓr : (0 : ℝ) < ℓ := by exact_mod_cast hℓ
  have hK : 0 < K := by dsimp [K]; positivity
  have hJeff : 0 < Jeff := by dsimp [Jeff]; positivity
  have hKr : K = Jeff * r := by dsimp [K, Jeff]; rw [hrscale]; field_simp
  have hH : (∑ i, g i).IsHermitian := Matrix.isHermitian_sum _ (fun i _ ↦ hg i)
  have hsumg : ∑ i, TNLean.Lattice.gaussianFilteredTerm q Δ (∑ k, g k) (g i) = ∑ i, g i :=
    TNLean.Lattice.sum_gaussianFilteredTerm Finset.univ q Δ hH rfl
  have hsumerror : ‖(∑ i, g i) - ∑ i, a i‖ ≤ (M : ℝ) * J * Real.exp (-r) := by
    conv_lhs => rw [← hsumg, ← Finset.sum_sub_distrib]
    calc
      _ ≤ ∑ i, ‖TNLean.Lattice.gaussianFilteredTerm q Δ (∑ k, g k) (g i) - a i‖ :=
        norm_sum_le _ _
      _ ≤ ∑ i : Fin M, J * Real.exp (-r) := Finset.sum_le_sum fun i _ ↦ herror i
      _ = _ := by simp; ring
  have hNreal : (N : ℝ) ≤ (2 : ℝ) ^ h := by
    exact_mod_cast le_two_pow_finiteHierarchyDepth N
  have hMbound : (M : ℝ) ≤ (N : ℝ) * (4 * (ℓ : ℝ)) := by
    have hNpos : 1 ≤ N := roundedPeriodicBlockCount_pos M ℓ
    have hMhi : M < (N + 1) * (2 * ℓ) := roundedPeriodicBlockCount_upper hℓ
    have hMb : M ≤ N * (4 * ℓ) := by nlinarith
    exact_mod_cast hMb
  have hcoeff : (M : ℝ) * J ≤ (2 : ℝ) ^ h * Jeff * r := by
    have hc := mul_le_mul_of_nonneg_right hNreal hK.le
    have hm := mul_le_mul_of_nonneg_right hMbound hJ.le
    rw [mul_assoc ((2 : ℝ) ^ h) Jeff r, ← hKr]
    dsimp [K] at hc ⊢
    nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) N) (mul_nonneg hℓr.le hJ.le)]
  have happrox : ‖(∑ i, g i) - ∑ j ∈ Finset.range (2 ^ h), extendFiniteEdges b j‖ ≤
      (2 : ℝ) ^ h * Jeff * r * Real.exp (-r) := by
    rw [sum_extendFiniteEdges_of_le b (le_two_pow_finiteHierarchyDepth N)]
    change ‖(∑ i, g i) - ∑ j, roundedPeriodicOperator ℓ a j‖ ≤ _
    rw [sum_roundedPeriodicOperator]
    exact hsumerror.trans (mul_le_mul_of_nonneg_right hcoeff (Real.exp_pos _).le)
  exact card_le_two_mul_re_trace_of_periodicHierarchyProjection_of_error
    (ι := Fin M) (d := d) (roundedPeriodicBlock N ℓ) (extendFiniteEdges b)
    (extendFiniteEdges_mem_supportedOperators _ b
      (roundedPeriodicOperator_mem_supportedOperators hℓ a hsupp))
    (isHermitian_extendFiniteEdges b (isHermitian_roundedPeriodicOperator a ha))
    hψ hK (two_le_finiteHierarchyDepth N) hJeff hΔ hr hKr.le hP₀ hgap hE₀ happrox
    (hierarchyTruncationError_mul_length_le_eighth_gap
      (two_le_finiteHierarchyDepth N) hJeff hΔ hr) hφ s hkeep

/-- The sufficient projection length is quadratic in the logarithm of the original
physical chain length, with no divisibility condition on that length.
Hastings, arXiv:cond-mat/0508554v3, Section II, lines 609–730. -/
theorem hierarchyProjectionLength_roundedPeriodic_le {M : ℕ} (hM : 0 < M) (ℓ : ℕ)
    (J η Δ : ℝ) :
    hierarchyProjectionLength (finiteHierarchyDepth (roundedPeriodicBlockCount M ℓ))
      (8 * J / η) Δ ≤
      512 * ((Nat.clog 2 M : ℝ) + 2) ^ 2 *
        (1 + max 0 (Real.log ((8 * J / η) / Δ))) := by
  have hclog := Nat.clog_mono_right 2 (roundedPeriodicBlockCount_le (ℓ := ℓ) hM)
  refine (hierarchyProjectionLength_finiteHierarchyDepth_le
    (roundedPeriodicBlockCount M ℓ) (8 * J / η) Δ).trans ?_
  gcongr

/-- An explicit integer projection radius for every nonempty physical periodic chain.
Hastings, arXiv:cond-mat/0508554v3, Section II, lines 609–730. -/
noncomputable def roundedPeriodicProjectionRadius (M : ℕ) (J η Δ : ℝ) : ℕ :=
  ⌈hierarchyProjectionLength (Nat.clog 2 M + 2) (8 * J / η) Δ / η⌉₊

/-- The chosen integer radius is positive.
Hastings, arXiv:cond-mat/0508554v3, Section II, lines 609–730. -/
theorem roundedPeriodicProjectionRadius_pos (M : ℕ) (J Δ : ℝ) {η : ℝ} (hη : 0 < η) :
    0 < roundedPeriodicProjectionRadius M J η Δ := by
  unfold roundedPeriodicProjectionRadius
  apply Nat.ceil_pos.mpr
  apply div_pos _ hη
  have hb := hierarchyProjectionLength_ge_square (Nat.clog 2 M + 2) (8 * J / η) Δ
  have hh : (2 : ℝ) ≤ (Nat.clog 2 M + 2 : ℕ) := by exact_mod_cast (by omega : 2 ≤ Nat.clog 2 M + 2)
  nlinarith [sq_nonneg ((Nat.clog 2 M + 2 : ℕ) : ℝ)]

/-- The explicit integer radius automatically satisfies the hierarchy length inequality.
Hastings, arXiv:cond-mat/0508554v3, Section II, lines 609–730. -/
theorem hierarchyProjectionLength_le_chosen_roundedPeriodicRadius {M : ℕ} (hM : 0 < M)
    (J Δ : ℝ) {η : ℝ} (hη : 0 < η) :
    let ℓ := roundedPeriodicProjectionRadius M J η Δ
    hierarchyProjectionLength (finiteHierarchyDepth (roundedPeriodicBlockCount M ℓ))
      (8 * J / η) Δ ≤ η * (ℓ : ℝ) := by
  let ℓ := roundedPeriodicProjectionRadius M J η Δ
  have hbase : hierarchyProjectionLength (finiteHierarchyDepth (roundedPeriodicBlockCount M ℓ))
      (8 * J / η) Δ ≤ hierarchyProjectionLength (Nat.clog 2 M + 2) (8 * J / η) Δ := by
    simpa only [hierarchyProjectionLength, Nat.cast_add, Nat.cast_ofNat] using
      hierarchyProjectionLength_roundedPeriodic_le hM ℓ J η Δ
  have hceil := Nat.le_ceil
    (hierarchyProjectionLength (Nat.clog 2 M + 2) (8 * J / η) Δ / η)
  have hscale : hierarchyProjectionLength (Nat.clog 2 M + 2) (8 * J / η) Δ ≤ η * (ℓ : ℝ) := by
    have := (div_le_iff₀ hη).mp hceil
    simpa only [ℓ, roundedPeriodicProjectionRadius, mul_comm] using this
  exact hbase.trans hscale

/-- The chosen physical radius is at most one more than an explicit quadratic logarithm.
Hastings, arXiv:cond-mat/0508554v3, Section II, lines 609–730. -/
theorem roundedPeriodicProjectionRadius_lt (M : ℕ) (J Δ : ℝ) {η : ℝ} (hη : 0 < η) :
    (roundedPeriodicProjectionRadius M J η Δ : ℝ) <
      512 * ((Nat.clog 2 M : ℝ) + 2) ^ 2 *
        (1 + max 0 (Real.log ((8 * J / η) / Δ))) / η + 1 := by
  unfold roundedPeriodicProjectionRadius
  have hb : 0 ≤ hierarchyProjectionLength (Nat.clog 2 M + 2) (8 * J / η) Δ := by
    exact (by positivity : 0 ≤ 512 * ((Nat.clog 2 M + 2 : ℕ) : ℝ) ^ 2).trans
      (hierarchyProjectionLength_ge_square _ _ _)
  simpa only [hierarchyProjectionLength, Nat.cast_add, Nat.cast_ofNat] using
    Nat.ceil_lt_add_one (div_nonneg hb hη.le)

/-- At the explicit integer radius, actual periodic local residuals construct a nearby
unit vector retained at every node, with no separate length inequality.
Hastings, arXiv:cond-mat/0508554v3, Section II, lines 609–730. -/
theorem exists_unit_mem_roundedPeriodicProjection_of_chosen_radius {M d : ℕ} (hM : 0 < M)
    {J η Δ : ℝ} (hJ : 0 < J) (hη : 0 < η)
    (a : Fin M → Matrix (Fin M → Fin d) (Fin M → Fin d) ℂ)
    (hsupp : ∀ i, a i ∈ supportedOperators d
      {v | roundedPeriodicDistance i v ≤ roundedPeriodicProjectionRadius M J η Δ})
    (ha : ∀ i, (a i).IsHermitian) {ψ : EuclideanSpace ℂ (Fin M → Fin d)} (hψ : ‖ψ‖ = 1)
    (hres : ∀ i, ‖toEuclideanLin
      (a i - ((⟪ψ, toEuclideanLin (a i) ψ⟫_ℂ).re : ℂ) • 1) ψ‖ ≤
      J * Real.exp (-(η * (roundedPeriodicProjectionRadius M J η Δ : ℝ))))
    (hbound : ∀ i, ‖a i‖ ≤ J) :
    let ℓ := roundedPeriodicProjectionRadius M J η Δ
    let r := η * (ℓ : ℝ)
    let b := roundedPeriodicOperator ℓ a
    let h := finiteHierarchyDepth (roundedPeriodicBlockCount M ℓ)
    let K := 8 * (ℓ : ℝ) * J
    ∃ φ : EuclideanSpace ℂ (Fin M → Fin d), ‖φ‖ = 1 ∧
      toEuclideanLin (roundedPeriodicProjection ℓ a ψ J r) φ = φ ∧
      ‖φ - ψ‖ ≤ 2 * (((3 : ℝ) ^ (h + 1) - 1) * Real.exp (-r / 8)) ∧
      IsRetainedHierarchy
        (hierarchyProjection (hierarchyEdge (extendFiniteEdges b))
          (fun m k ↦ (⟪ψ, toEuclideanLin (hierarchyEdge (extendFiniteEdges b) m k) ψ⟫_ℂ).re)
          (hierarchyWindowRadius K r h)) h 0 φ :=
  exists_unit_mem_roundedPeriodicProjection (roundedPeriodicProjectionRadius_pos M J Δ hη)
    a hsupp ha hψ hJ (hierarchyProjectionLength_le_chosen_roundedPeriodicRadius hM J Δ hη)
    hres hbound

/-- The explicit quadratic logarithmic radius gives the physical final-state count from
the preceding Gaussian-localization estimate, without a supplied length or pair-norm bound.
Hastings, arXiv:cond-mat/0508554v3, Section II, lines 609–730. -/
theorem card_le_two_mul_re_trace_of_roundedPeriodicProjection_of_chosen_radius
    {M d : ℕ} (hM : 0 < M) {J η Δ q : ℝ} (hJ : 0 < J) (hη : 0 < η) (hΔ : 0 < Δ)
    (a g : Fin M → Matrix (Fin M → Fin d) (Fin M → Fin d) ℂ)
    (hsupp : ∀ i, a i ∈ supportedOperators d
      {v | roundedPeriodicDistance i v ≤ roundedPeriodicProjectionRadius M J η Δ})
    (ha : ∀ i, (a i).IsHermitian) (hg : ∀ i, (g i).IsHermitian)
    {ψ : EuclideanSpace ℂ (Fin M → Fin d)} (hψ : ‖ψ‖ = 1)
    (herror : ∀ i, ‖TNLean.Lattice.gaussianFilteredTerm q Δ (∑ k, g k) (g i) - a i‖ ≤
      J * Real.exp (-(η * (roundedPeriodicProjectionRadius M J η Δ : ℝ))))
    {P₀ : Matrix (Fin M → Fin d) (Fin M → Fin d) ℂ} (hP₀ : IsStarProjection P₀) {E₀ : ℝ}
    (hgap : ∀ v : EuclideanSpace ℂ (Fin M → Fin d),
      Δ * (‖v‖ ^ 2 - (⟪v, toEuclideanLin P₀ v⟫_ℂ).re) ≤
        (⟪v, toEuclideanLin (∑ i, g i) v⟫_ℂ).re - E₀ * ‖v‖ ^ 2)
    (hE₀ : (⟪ψ, toEuclideanLin (∑ i, g i) ψ⟫_ℂ).re = E₀)
    {κ : Type*} {φ : κ → EuclideanSpace ℂ (Fin M → Fin d)} (hφ : Orthonormal ℂ φ)
    (s : Finset κ)
    (hkeep : ∀ j ∈ s, toEuclideanLin
      (roundedPeriodicProjection (roundedPeriodicProjectionRadius M J η Δ) a ψ J
        (η * (roundedPeriodicProjectionRadius M J η Δ : ℝ))) (φ j) = φ j) :
    (s.card : ℝ) ≤ 2 * (trace P₀).re :=
  card_le_two_mul_re_trace_of_roundedPeriodicProjection
    (roundedPeriodicProjectionRadius_pos M J Δ hη) a g hsupp ha hg hψ hJ hη hΔ rfl
    (hierarchyProjectionLength_le_chosen_roundedPeriodicRadius hM J Δ hη)
    herror hP₀ hgap hE₀ hφ s hkeep

end TNLean.MPS.AreaLaw.LocalSolution
