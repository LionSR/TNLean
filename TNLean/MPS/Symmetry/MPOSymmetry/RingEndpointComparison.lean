/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.MPOSymmetry.MixedEndpointProjectorComparison
import TNLean.MPS.ParentHamiltonian.Martingale.PeriodicInteraction
import TNLean.MPS.ParentHamiltonian.Martingale.PositiveComparisonGap
import TNLean.MPS.ParentHamiltonian.CompactParentGap
import TNLean.MPS.ParentHamiltonian.UniqueGroundState
import TNLean.MPS.ParentHamiltonian.KernelChainGroundSpace

/-!
# Periodic comparison at the first mixed endpoint

The missing outer row and column sectors of one extended endpoint interaction
are the inner sectors of its preceding and following interactions. Translating
the actual local comparisons and summing them therefore gives
`H′ ≤ K ≤ 3 H′`, where `K` is the canonical parent of the embedded first
endpoint. The kernels agree, and a gap for `K` gives one third of that gap for
`H′`.

Source: arXiv:2203.12563, Section 5, lines 1690–1692. These comparisons hold on
periodic chains of length at least two. They do not infer a uniform gap along
the interpolation from finite-volume continuity.
-/

open scoped BigOperators ComplexOrder InnerProductSpace Matrix

namespace MPSTensor

variable {d R N : ℕ}

/-- Extending an interaction to a cyclic window preserves addition. -/
theorem periodicLocalInteractionES_add
    (h k : EuclideanSpace ℂ (Cfg d R) →ₗ[ℂ] EuclideanSpace ℂ (Cfg d R))
    (i : Fin N) :
    periodicLocalInteractionES (h + k) i =
      periodicLocalInteractionES h i + periodicLocalInteractionES k i := by
  unfold periodicLocalInteractionES
  split_ifs with hRN
  · simp only [map_add, ContinuousLinearMap.rightFiberwiseMap_add,
      ContinuousLinearMap.toLinearMap_add]
  · simp

/-- Extending an interaction to a cyclic window preserves subtraction. -/
theorem periodicLocalInteractionES_sub
    (h k : EuclideanSpace ℂ (Cfg d R) →ₗ[ℂ] EuclideanSpace ℂ (Cfg d R))
    (i : Fin N) :
    periodicLocalInteractionES (h - k) i =
      periodicLocalInteractionES h i - periodicLocalInteractionES k i := by
  unfold periodicLocalInteractionES
  split_ifs with hRN
  · simp only [map_sub, ContinuousLinearMap.rightFiberwiseMap_sub,
      ContinuousLinearMap.toLinearMap_sub]
  · simp

/-- A faithfully embedded local identity is the chain identity. -/
theorem periodicLocalInteractionES_one (hRN : R ≤ N) (i : Fin N) :
    periodicLocalInteractionES
      (1 : EuclideanSpace ℂ (Cfg d R) →ₗ[ℂ] EuclideanSpace ℂ (Cfg d R)) i = 1 := by
  have hone :
      (ContinuousLinearMap.rightFiberwiseMap (S := Cfg d (N - R))
        (LinearMap.toContinuousLinearMap
          (1 : EuclideanSpace ℂ (Cfg d R) →ₗ[ℂ] EuclideanSpace ℂ (Cfg d R)))).toLinearMap =
        1 := by
    ext v p
    rfl
  unfold periodicLocalInteractionES
  rw [dif_pos hRN, hone, map_one]

/-- A diagonal local operator is multiplication by its value on the actual
cyclic window. This includes a window crossing the periodic seam. -/
theorem periodicLocalInteractionES_diagonal_apply (hRN : R ≤ N) (i : Fin N)
    (f : Cfg d R → ℂ) (v : EuclideanSpace ℂ (Cfg d N)) (σ : Cfg d N) :
    periodicLocalInteractionES (Matrix.toEuclideanLin (Matrix.diagonal f)) i v σ =
      f (extractWindow R i σ) * v σ := by
  let e := cyclicActiveBlockConfigEquiv d R hRN i
  let U := cyclicActiveBlockConfigLinearIsometryEquiv d R hRN i
  have hwindow : (e σ).1 = extractWindow R i σ := by
    funext r
    have h := cyclicActiveBlockConfigEquiv_symm_apply_window hRN i
      (e σ).1 (e σ).2 r
    simpa only [Prod.mk.eta, e, Equiv.symm_apply_apply] using h.symm
  unfold periodicLocalInteractionES
  rw [dif_pos hRN]
  change (U.symm (ContinuousLinearMap.rightFiberwiseMap
    (S := Cfg d (N - R))
    (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (Matrix.diagonal f)))
    (U v))) σ = _
  rw [cyclicActiveBlockConfigLinearIsometryEquiv_symm_apply_apply]
  change ((Matrix.diagonal f).mulVec
    (fun ω => U v (ω, (e σ).2))) (e σ).1 = _
  rw [Matrix.mulVec_diagonal]
  change f (e σ).1 * U v ((e σ).1, (e σ).2) = _
  simp only [Prod.mk.eta, U, cyclicActiveBlockConfigLinearIsometryEquiv_apply_apply,
    e, Equiv.symm_apply_apply, hwindow]

private theorem extractWindow_two_zero (i : Fin N) (σ : Cfg d N) :
    extractWindow 2 i σ 0 = σ i := by
  simp [extractWindow, Nat.mod_eq_of_lt i.isLt]

private theorem extractWindow_two_one (i : Fin N) (σ : Cfg d N) :
    extractWindow 2 i σ 1 = σ (finRotate N i) := by
  apply congrArg σ
  apply Fin.ext
  simp [extractWindow, finRotate_apply, Fin.add_def]

namespace MPOSymmetry

variable {D₀ D₁ : ℕ}

/-- The first row selector on a bond is the second row selector on the
preceding bond, including the periodic seam. Source: arXiv:2203.12563,
Section 5, lines 1690–1692. -/
theorem periodicLocalInteractionES_mixedEndpointRowSector_previous
    (hN : 2 ≤ N) (i : Fin N) :
    periodicLocalInteractionES (mixedEndpointRowSector D₀ D₁ 0) i =
      periodicLocalInteractionES (mixedEndpointRowSector D₀ D₁ 1)
        ((finRotate N).symm i) := by
  ext v σ
  simp only [mixedEndpointRowSector, periodicLocalInteractionES_diagonal_apply hN,
    extractWindow_two_zero, extractWindow_two_one, Equiv.apply_symm_apply]

/-- The second column selector on a bond is the first column selector on the
following bond, including the periodic seam. Source: arXiv:2203.12563,
Section 5, lines 1690–1692. -/
theorem periodicLocalInteractionES_mixedEndpointColumnSector_next
    (hN : 2 ≤ N) (i : Fin N) :
    periodicLocalInteractionES (mixedEndpointColumnSector D₀ D₁ 1) i =
      periodicLocalInteractionES (mixedEndpointColumnSector D₀ D₁ 0)
        (finRotate N i) := by
  ext v σ
  simp only [mixedEndpointColumnSector, periodicLocalInteractionES_diagonal_apply hN,
    extractWindow_two_zero, extractWindow_two_one]

/-- The missing first row sector is penalized by the previous actual
extended interaction. Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem periodicLocalInteractionES_outerRowPenalty_le_previous
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (hN : 2 ≤ N) (i : Fin N) :
    periodicLocalInteractionES (1 - mixedEndpointRowSector D₀ D₁ 0) i ≤
      periodicLocalInteractionES (mixedEndpointParentInteraction A₀ A₁ 0).toLinearMap
        ((finRotate N).symm i) := by
  have h := periodicLocalInteractionES_mono
    (mixedEndpoint_one_sub_rowSector_one_le_parentInteraction A₀ A₁)
    ((finRotate N).symm i)
  simpa only [periodicLocalInteractionES_sub, periodicLocalInteractionES_one hN,
    periodicLocalInteractionES_mixedEndpointRowSector_previous hN i] using h

/-- The missing second column sector is penalized by the next actual
extended interaction. Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem periodicLocalInteractionES_outerColumnPenalty_le_next
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (hN : 2 ≤ N) (i : Fin N) :
    periodicLocalInteractionES (1 - mixedEndpointColumnSector D₀ D₁ 1) i ≤
      periodicLocalInteractionES (mixedEndpointParentInteraction A₀ A₁ 0).toLinearMap
        (finRotate N i) := by
  have h := periodicLocalInteractionES_mono
    (mixedEndpoint_one_sub_columnSector_zero_le_parentInteraction A₀ A₁)
    (finRotate N i)
  simpa only [periodicLocalInteractionES_sub, periodicLocalInteractionES_one hN,
    periodicLocalInteractionES_mixedEndpointColumnSector_next hN i] using h

/-- One canonical endpoint term is controlled by three adjacent actual
extended terms. No ring inequality is assumed. Source: arXiv:2203.12563,
Section 5, lines 1690–1692. -/
theorem localTermES_mixedEndpointLeftTensor_le_three_extended
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (hN : 2 ≤ N) (i : Fin N) :
    localTermES (mixedEndpointLeftTensor A₀ D₁) 2 i ≤
      periodicLocalInteractionES (mixedEndpointParentInteraction A₀ A₁ 0).toLinearMap i +
      periodicLocalInteractionES (mixedEndpointParentInteraction A₀ A₁ 0).toLinearMap
        ((finRotate N).symm i) +
      periodicLocalInteractionES (mixedEndpointParentInteraction A₀ A₁ 0).toLinearMap
        (finRotate N i) := by
  have hlocal := periodicLocalInteractionES_mono
    (parentInteractionES_mixedEndpointLeftTensor_le A₀ A₁) i
  rw [periodicLocalInteractionES_parentInteractionES _ (by decide),
    periodicLocalInteractionES_add, periodicLocalInteractionES_add] at hlocal
  exact hlocal.trans (add_le_add
    (add_le_add_left (periodicLocalInteractionES_outerRowPenalty_le_previous A₀ A₁ hN i) _)
    (periodicLocalInteractionES_outerColumnPenalty_le_next A₀ A₁ hN i))

/-- The actual extended endpoint Hamiltonian and the canonical parent of the
embedded endpoint satisfy `H′ ≤ K ≤ 3 H′` on every ring of at least two sites.
The factor three comes from counting each bond and its two neighbors.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem mixedEndpoint_periodic_comparison
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (hN : 2 ≤ N) :
    periodicInteractionHamiltonianES (mixedEndpointParentInteraction A₀ A₁ 0).toLinearMap N ≤
        parentHamiltonianES (mixedEndpointLeftTensor A₀ D₁) 2 N ∧
      parentHamiltonianES (mixedEndpointLeftTensor A₀ D₁) 2 N ≤
        (3 : ℂ) • periodicInteractionHamiltonianES
          (mixedEndpointParentInteraction A₀ A₁ 0).toLinearMap N := by
  constructor
  · simpa only [periodicInteractionHamiltonianES_parentInteractionES _ (by decide)] using
      periodicInteractionHamiltonianES_mono
        (mixedEndpointParentInteraction_zero_le_parentInteractionES A₀ A₁) N
  · have h := Finset.sum_le_sum fun (i : Fin N) (_ : i ∈ Finset.univ) =>
      localTermES_mixedEndpointLeftTensor_le_three_extended A₀ A₁ hN i
    rw [← parentHamiltonianES_eq_sum_localTermES] at h
    simp only [Finset.sum_add_distrib, Equiv.sum_comp] at h
    convert h using 1
    simp only [periodicInteractionHamiltonianES]
    module

/-- The ring kernel of the actual extended endpoint equals the canonical
endpoint kernel. Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem mixedEndpoint_periodic_ker_eq
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (hN : 2 ≤ N) :
    LinearMap.ker (periodicInteractionHamiltonianES
      (mixedEndpointParentInteraction A₀ A₁ 0).toLinearMap N) =
      LinearMap.ker (parentHamiltonianES (mixedEndpointLeftTensor A₀ D₁) 2 N) := by
  obtain ⟨hLower, hUpper⟩ := mixedEndpoint_periodic_comparison A₀ A₁ hN
  exact (periodicInteractionHamiltonianES_isPositive
    (mixedEndpointParentInteraction_isPositive A₀ A₁ 0) N).ker_eq_of_smul_le_of_le_smul
      (parentHamiltonianES_isPositive _ 2 N)
      (a := 1) (b := 1) (c := 3) (by norm_num) (by norm_num) (by norm_num)
      (by simpa only [Complex.ofReal_one, one_smul] using hLower)
      (by simpa only [Complex.ofReal_one, one_smul] using hUpper)

/-- A canonical endpoint gap `δ` transfers to the actual extended endpoint
with gap `δ / 3`. The comparison and common kernel are derived from the
mixed tensor, rather than supplied as hypotheses.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem mixedEndpoint_periodic_norm_gap
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (hN : 2 ≤ N) {δ : ℝ} (hδ : 0 < δ)
    (hGap : ∀ v ∈ (LinearMap.ker
      (parentHamiltonianES (mixedEndpointLeftTensor A₀ D₁) 2 N))ᗮ,
      δ * ‖v‖ ≤ ‖parentHamiltonianES (mixedEndpointLeftTensor A₀ D₁) 2 N v‖) :
    ∀ v ∈ (LinearMap.ker (periodicInteractionHamiltonianES
      (mixedEndpointParentInteraction A₀ A₁ 0).toLinearMap N))ᗮ,
      (δ / 3) * ‖v‖ ≤ ‖periodicInteractionHamiltonianES
        (mixedEndpointParentInteraction A₀ A₁ 0).toLinearMap N v‖ := by
  obtain ⟨hLower, hUpper⟩ := mixedEndpoint_periodic_comparison A₀ A₁ hN
  have hScaled := smul_le_smul_of_nonneg_left hLower (by norm_num : 0 ≤ (3 : ℂ))
  simpa only [one_mul] using
    (parentHamiltonianES_isPositive (mixedEndpointLeftTensor A₀ D₁) 2 N).
      norm_gap_of_smul_le_of_le_smul
        (periodicInteractionHamiltonianES_isPositive
          (mixedEndpointParentInteraction_isPositive A₀ A₁ 0) N)
        (a := 1) (b := 3) (c := 3) (by norm_num) (by norm_num) (by norm_num) hδ
        (by simpa only [Complex.ofReal_one, one_smul] using hUpper) hScaled hGap

/-- At an injective first endpoint, the actual extended periodic Hamiltonian
has precisely the embedded MPS ground line, for every ring of at least two
sites. Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem mixedEndpoint_periodic_groundSpace_eq [NeZero D₀]
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (hA₀ : Kraus.IsInjective A₀) (hN : 2 ≤ N) :
    LinearMap.ker (periodicInteractionHamiltonianES
      (mixedEndpointParentInteraction A₀ A₁ 0).toLinearMap N) =
      Submodule.span ℂ {WithLp.toLp 2
        (mpv (mixedEndpointLeftTensor A₀ D₁) :
          NSiteSpace ((D₀ + D₁) * (D₀ + D₁)) N)} := by
  rw [mixedEndpoint_periodic_ker_eq A₀ A₁ hN,
    ← parentHamiltonianGroundSpaceES_eq_ker_parentHamiltonianES,
    parentHamiltonianGroundSpaceES,
    ker_parentHamiltonian_eq_chainGroundSpace _ (by omega) hN,
    chainGroundSpace_eq_mpvSubmodule
      (isInjective_mixedEndpointLeftTensor A₀ hA₀ D₁) hN (by decide) hN,
    mpvSubmodule, Submodule.map_span, Set.image_singleton]
  rfl

/-- The actual extended first endpoint has a unique periodic ground state
on every ring of at least two sites. Source: arXiv:2203.12563, Section 5,
lines 1690–1692. -/
theorem mixedEndpoint_periodic_groundSpace_finrank [NeZero D₀]
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (hA₀ : Kraus.IsInjective A₀) (hN : 2 ≤ N) :
    Module.finrank ℂ (LinearMap.ker (periodicInteractionHamiltonianES
      (mixedEndpointParentInteraction A₀ A₁ 0).toLinearMap N)) = 1 := by
  rw [mixedEndpoint_periodic_ker_eq A₀ A₁ hN,
    ← parentHamiltonianGroundSpaceES_eq_ker_parentHamiltonianES,
    parentHamiltonianGroundSpaceES,
    ker_parentHamiltonian_eq_chainGroundSpace _ (by omega) hN,
    LinearEquiv.finrank_map_eq]
  exact groundSpace_unique_periodic
    (isInjective_mixedEndpointLeftTensor A₀ hA₀ D₁) hN (by decide) hN

/-- The extended first endpoint of the actual arbitrary mixed tensor has a
strictly positive gap uniform over every periodic length at least two.
Injectivity of the first endpoint supplies its canonical gap; the concrete
three-term comparison transfers it. No gap assumption and no continuity
argument at a rank-changing endpoint is used.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem exists_uniform_mixedEndpoint_periodic_gap [NeZero D₀]
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (hA₀ : Kraus.IsInjective A₀) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ N : ℕ, 2 ≤ N →
      ∀ v ∈ (LinearMap.ker (periodicInteractionHamiltonianES
        (mixedEndpointParentInteraction A₀ A₁ 0).toLinearMap N))ᗮ,
        δ * ‖v‖ ≤ ‖periodicInteractionHamiltonianES
          (mixedEndpointParentInteraction A₀ A₁ 0).toLinearMap N v‖ := by
  obtain ⟨δ, hδ, hGap⟩ :=
    exists_uniform_parentHamiltonianES_gap_of_compact_isInjective_all_lengths
      (fun _ : Unit => mixedEndpointLeftTensor A₀ D₁) continuous_const
      (fun _ => isInjective_mixedEndpointLeftTensor A₀ hA₀ D₁)
      (S := Set.univ) isCompact_univ
  refine ⟨δ / 3, div_pos hδ (by norm_num), fun N hN => ?_⟩
  exact mixedEndpoint_periodic_norm_gap A₀ A₁ hN hδ (hGap () (Set.mem_univ ()) N hN)

end MPOSymmetry
end MPSTensor
