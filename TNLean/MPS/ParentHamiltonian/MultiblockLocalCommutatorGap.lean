/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.BlockBoundaryObservableCompression
import TNLean.MPS.ParentHamiltonian.PrimitiveLocalParentInteractionGap
import TNLean.MPS.ParentHamiltonian.Martingale.BlockOpenGapAllLengths

import TNLean.MPS.ParentHamiltonian.CanonicalParentInteractionMatrix

/-!
# Local commutator inequalities for primitive sectors of a multiblock tensor

A centered interior observable in a distinguished primitive sector has
vanishing projection onto the full sum of sector ground spaces. Together
with a positive finite-volume gap, primitive convergence of the excitation
norm and the local commutator energy gives a local commutator inequality.
At a positive simultaneous injectivity length, the open-chain gap and
kernel identity supply one positive constant for every sector and every
centered local observable.

Source: Nachtergaele, arXiv:cond-mat/9410110, Theorem 1.2 and Section 6,
lines 2649--2675; CPGSV21, arXiv:2011.12127, lines 2170--2172.

**Scope restriction (finite-interval sector expectations):** The conclusions
are stated for the consistent finite-interval expectations of normalized
primitive sectors. The automatic existence results assume interaction range
at least one more than a supplied simultaneous injectivity length. The
completed-state and GNS formulations remain separate; see
docs/paper-gaps/nachtergaele96_infinite_volume_ground_projection.tex.
-/

open Filter
open scoped Matrix Topology ComplexOrder InnerProductSpace

namespace MPSTensor

section FiniteFamily
variable {ι : Type*} [Finite ι] {d : ℕ} {D : ι → ℕ} [∀ i, NeZero (D i)]

/-- The squared norm of the full ground projection of a sector-centered
excitation tends to zero for all bounded boundary vectors in that sector.
Source: Nachtergaele, arXiv:cond-mat/9410110, Section 6, lines 2649--2675. -/
theorem bulkObservable_iSup_groundSpace_projection_norm_sq_tendsto_zero
    (A : ∀ i, MPSTensor d (D i))
    (ρ : ∀ i, Matrix (Fin (D i)) (Fin (D i)) ℂ)
    (hP : ∀ i, IsPrimitiveMPS (A i) (ρ i)) (hρ : ∀ i, (ρ i).PosDef)
    (hDistinct : ∀ i j, i ≠ j → ∀ h : D j = D i,
      ¬ GaugePhaseEquiv (h ▸ A j) (A i))
    (α : ι) {k : ℕ} (hk : 0 < k) (X : Matrix (Cfg d k) (Cfg d k) ℂ)
    (hcenter : observableInsertionExpectation (A α) (ρ α) X = 0)
    {κ : Type*} {f : Filter κ} {ℓ r : κ → ℕ}
    (hℓ : Tendsto ℓ f atTop) (hr : Tendsto r f atTop)
    (ψ : (n : κ) → EuclideanSpace ℂ (Cfg d ((ℓ n + k) + r n)))
    (hψ : ∀ᶠ n in f, ψ n ∈ groundSpaceES (A α) ((ℓ n + k) + r n))
    (hbound : ∀ᶠ n in f, ‖ψ n‖ ≤ 1) :
    Tendsto (fun n =>
      ‖(⨆ i, groundSpaceES (A i) ((ℓ n + k) + r n)).starProjection
        ((Matrix.toEuclideanCLM (n := Cfg d ((ℓ n + k) + r n)) (𝕜 := ℂ)
          (bulkObservable X (ℓ n) (r n))) (ψ n))‖ ^ 2) f (𝓝 0) := by
  have hnorm : Tendsto (fun n =>
      ‖(⨆ i, groundSpaceES (A i) ((ℓ n + k) + r n)).starProjection
        ((Matrix.toEuclideanCLM (n := Cfg d ((ℓ n + k) + r n)) (𝕜 := ℂ)
          (bulkObservable X (ℓ n) (r n))) (ψ n))‖) f (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_
      (bulkObservable_iSup_groundSpace_compression_tendsto_zero A ρ hP hρ hDistinct
        α hk X hcenter hℓ hr)
    filter_upwards [hψ, hbound] with n hn hb
    have hfix := Submodule.starProjection_eq_self_iff.mpr hn
    let Y := Matrix.toEuclideanCLM (n := Cfg d ((ℓ n + k) + r n)) (𝕜 := ℂ)
      (bulkObservable X (ℓ n) (r n))
    calc
      _ = ‖((⨆ i, groundSpaceES (A i) ((ℓ n + k) + r n)).starProjection.comp
          (Y.comp (groundSpaceES (A α) ((ℓ n + k) + r n)).starProjection)) (ψ n)‖ := by
        simp only [ContinuousLinearMap.comp_apply, hfix, Y]
      _ ≤ _ := ContinuousLinearMap.le_opNorm _ (ψ n)
      _ ≤ _ := mul_le_of_le_one_right (norm_nonneg _) hb
  simpa only [zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using hnorm.pow 2

/-- An eventual positive gap with the full joint ground-space kernel gives
its commutator bound in every distinguished primitive sector. The excitation
norm and the full ground-projection limits are derived from the tensors.
Source: Nachtergaele, arXiv:cond-mat/9410110, Section 6, lines 2649--2675. -/
theorem multiblock_commutator_gap_of_bulkObservable_energy_limit
    (A : ∀ i, MPSTensor d (D i))
    (ρ : ∀ i, Matrix (Fin (D i)) (Fin (D i)) ℂ)
    (hP : ∀ i, IsPrimitiveMPS (A i) (ρ i)) (hρ : ∀ i, (ρ i).PosDef)
    (hDistinct : ∀ i j, i ≠ j → ∀ h : D j = D i,
      ¬ GaugePhaseEquiv (h ▸ A j) (A i))
    (α : ι) {k : ℕ} (hk : 0 < k) (X : Matrix (Cfg d k) (Cfg d k) ℂ)
    (hcenter : observableInsertionExpectation (A α) (ρ α) X = 0)
    {ℓ r : ℕ → ℕ} (hℓ : Tendsto ℓ atTop atTop) (hr : Tendsto r atTop atTop)
    (H : (n : ℕ) → EuclideanSpace ℂ (Cfg d ((ℓ n + k) + r n)) →ₗ[ℂ]
      EuclideanSpace ℂ (Cfg d ((ℓ n + k) + r n)))
    (ψ : (n : ℕ) → EuclideanSpace ℂ (Cfg d ((ℓ n + k) + r n)))
    {γ e : ℝ} (hγ : 0 ≤ γ)
    (hPos : ∀ᶠ n in atTop, (H n).IsPositive)
    (hGap : ∀ᶠ n in atTop, ∀ v ∈ (LinearMap.ker (H n))ᗮ,
      γ * ‖v‖ ≤ ‖H n v‖)
    (hKernel : ∀ᶠ n in atTop,
      LinearMap.ker (H n) = ⨆ i, groundSpaceES (A i) ((ℓ n + k) + r n))
    (hGround : ∀ᶠ n in atTop, ψ n ∈ groundSpaceES (A α) ((ℓ n + k) + r n))
    (hUnit : ∀ᶠ n in atTop, ‖ψ n‖ = 1)
    (hEnergy :
      let B (n : ℕ) := ((Matrix.toEuclideanCLM
        (n := Cfg d ((ℓ n + k) + r n)) (𝕜 := ℂ))
          (bulkObservable X (ℓ n) (r n))).toLinearMap
      Tendsto (fun n =>
        (⟪((B n).adjoint.comp ((H n).comp (B n) - (B n).comp (H n))) (ψ n),
          ψ n⟫_ℂ).re) atTop (𝓝 e)) :
    γ * (observableInsertionExpectation (A α) (ρ α) (Xᴴ * X)).re ≤ e := by
  let B (n : ℕ) := ((Matrix.toEuclideanCLM
    (n := Cfg d ((ℓ n + k) + r n)) (𝕜 := ℂ))
      (bulkObservable X (ℓ n) (r n))).toLinearMap
  have hGround' : ∀ᶠ n in atTop, ψ n ∈ LinearMap.ker (H n) := by
    filter_upwards [hKernel, hGround] with n hkern hg
    rw [hkern]
    exact (le_iSup (fun i => groundSpaceES (A i) ((ℓ n + k) + r n)) α) hg
  have hNorm : Tendsto (fun n => ‖B n (ψ n)‖ ^ 2) atTop
      (𝓝 (observableInsertionExpectation (A α) (ρ α) (Xᴴ * X)).re) :=
    (hP α).bulkObservable_groundState_norm_sq_tendsto (hρ α) X hℓ hr ψ hGround hUnit
  have hProjection : Tendsto (fun n =>
      ‖(LinearMap.ker (H n)).starProjection (B n (ψ n))‖ ^ 2) atTop (𝓝 0) := by
    apply (bulkObservable_iSup_groundSpace_projection_norm_sq_tendsto_zero
      A ρ hP hρ hDistinct α hk X hcenter hℓ hr ψ hGround
        (hUnit.mono fun _ hn => hn.le)).congr'
    filter_upwards [hKernel] with n hn
    simp only [hn, B, ContinuousLinearMap.coe_coe]
  exact FrustrationFree.commutator_gap_of_tendsto_ground_projection_zero
    H B ψ hγ hPos hGap hGround' hNorm hProjection hEnergy

/-- A positive open interaction with the joint sector kernel and an eventual
uniform gap obeys the local commutator inequality in every primitive sector.
The energy limit follows from finite-range locality and primitive convergence.
Source: Nachtergaele, arXiv:cond-mat/9410110, Section 6, lines 2649--2675. -/
theorem multiblock_localCommutator_gap_of_openInteraction_gap
    (A : ∀ i, MPSTensor d (D i))
    (ρ : ∀ i, Matrix (Fin (D i)) (Fin (D i)) ℂ)
    (hP : ∀ i, IsPrimitiveMPS (A i) (ρ i)) (hρ : ∀ i, (ρ i).PosDef)
    (hDistinct : ∀ i j, i ≠ j → ∀ h : D j = D i,
      ¬ GaugePhaseEquiv (h ▸ A j) (A i))
    (α : ι) {R k : ℕ} (h : Matrix (Cfg d R) (Cfg d R) ℂ)
    (hh : (Matrix.toEuclideanLin h).IsPositive)
    (X : Matrix (Cfg d k) (Cfg d k) ℂ) (hR : 0 < R) (hk : 0 < k)
    (hcenter : observableInsertionExpectation (A α) (ρ α) X = 0)
    (ψ : (n : ℕ) → EuclideanSpace ℂ (Cfg d ((n + (R - 1) + k) + (R - 1 + n))))
    {γ : ℝ} (hγ : 0 ≤ γ)
    (hKernel : ∀ᶠ n in atTop,
      LinearMap.ker (openInteractionHamiltonianES (Matrix.toEuclideanLin h)
        ((n + (R - 1) + k) + (R - 1 + n))) =
          ⨆ i, groundSpaceES (A i) ((n + (R - 1) + k) + (R - 1 + n)))
    (hGap : ∀ᶠ n in atTop, ∀ v ∈
      (LinearMap.ker (openInteractionHamiltonianES (Matrix.toEuclideanLin h)
        ((n + (R - 1) + k) + (R - 1 + n))))ᗮ,
      γ * ‖v‖ ≤ ‖openInteractionHamiltonianES (Matrix.toEuclideanLin h)
        ((n + (R - 1) + k) + (R - 1 + n)) v‖)
    (hGround : ∀ᶠ n in atTop,
      ψ n ∈ groundSpaceES (A α) ((n + (R - 1) + k) + (R - 1 + n)))
    (hUnit : ∀ᶠ n in atTop, ‖ψ n‖ = 1) :
    γ * (observableInsertionExpectation (A α) (ρ α) (Xᴴ * X)).re ≤
      (observableInsertionExpectation (A α) (ρ α) (localCommutatorObservable h X)).re := by
  let N (n : ℕ) := (n + (R - 1) + k) + (R - 1 + n)
  let H (n : ℕ) := openInteractionHamiltonianES (Matrix.toEuclideanLin h) (N n)
  have hEnergy :
      let B (n : ℕ) := ((Matrix.toEuclideanCLM (n := Cfg d (N n)) (𝕜 := ℂ))
        (bulkObservable X (n + (R - 1)) (R - 1 + n))).toLinearMap
      Tendsto (fun n =>
        (inner ℂ (((B n).adjoint.comp ((H n).comp (B n) - (B n).comp (H n)))
          (ψ n)) (ψ n)).re) atTop
        (𝓝 (observableInsertionExpectation (A α) (ρ α)
          (localCommutatorObservable h X)).re) := by
    apply ((hP α).localCommutatorObservable_expectation_tendsto (hρ α) h X hR hk
      N (fun n => by dsimp [N]; omega) ψ hGround hUnit).congr'
    filter_upwards [] with n
    have hH : Matrix.toEuclideanCLM (n := Cfg d (N n)) (𝕜 := ℂ)
        (openInteractionMatrix h (N n)) = (H n).toContinuousLinearMap :=
      congrArg LinearMap.toContinuousLinearMap
        (openInteractionHamiltonianES_eq_toEuclideanLin_openInteractionMatrix
          h hR (by dsimp [N]; omega)).symm
    dsimp only
    rw [map_mul, map_sub, map_mul, map_mul, ← Matrix.star_eq_conjTranspose,
      map_star, ContinuousLinearMap.star_eq_adjoint, hH,
      ← bulkObservable_eq_chainWindowOperator hk X (n + (R - 1)) (R - 1 + n)]
    rfl
  exact multiblock_commutator_gap_of_bulkObservable_energy_limit A ρ hP hρ hDistinct
    α hk X hcenter (ℓ := fun n : ℕ => n + (R - 1)) (r := fun n => (R - 1) + n)
    (tendsto_add_atTop_nat (R - 1))
    (tendsto_atTop_mono (fun n => Nat.le_add_left n (R - 1)) tendsto_id)
    H ψ hγ (Eventually.of_forall fun n => openInteractionHamiltonianES_isPositive hh (N n))
    hGap hKernel hGround hUnit hEnergy

end FiniteFamily
section BlockFamily
variable {d b : ℕ} {D : Fin b → ℕ} [NeZero d] [∀ i, NeZero (D i)]

/-- Every positive parent interaction of a weighted multiblock tensor has one
positive local commutator constant for all primitive sectors and all centered
local observables at range exceeding a supplied simultaneous injectivity length.
The finite-volume gap, joint kernel, separation, and boundary approximants are
derived internally. Source: Nachtergaele, arXiv:cond-mat/9410110, Theorem 1.2
and Section 6; CPGSV21, arXiv:2011.12127, lines 2170--2172. -/
theorem exists_pos_multiblock_localCommutator_gap_of_isParentInteraction
    (μ : Fin b → ℂ) (A : ∀ i, MPSTensor d (D i)) (hμ : ∀ i, μ i ≠ 0)
    (ρ : ∀ i, Matrix (Fin (D i)) (Fin (D i)) ℂ)
    (hP : ∀ i, IsPrimitiveMPS (A i) (ρ i)) (hρ : ∀ i, (ρ i).PosDef)
    {S R : ℕ} (hS : 0 < S) (hSpan : WordTupleSpanTop A S) (hR : S + 1 ≤ R)
    (h : Matrix (Cfg d R) (Cfg d R) ℂ)
    (hh : IsParentInteraction (toTensorFromBlocks (d := d) (μ := μ) A) R
      (Matrix.toEuclideanLin h)) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ α : Fin b, ∀ {k : ℕ}
      (X : Matrix (Cfg d k) (Cfg d k) ℂ),
      0 < k → observableInsertionExpectation (A α) (ρ α) X = 0 →
        γ * (observableInsertionExpectation (A α) (ρ α) (Xᴴ * X)).re ≤
          (observableInsertionExpectation (A α) (ρ α) (localCommutatorObservable h X)).re := by
  let T := toTensorFromBlocks (d := d) (μ := μ) A
  have hRpos : 0 < R := by omega
  have hKernel : ∀ N, R ≤ N →
      LinearMap.ker (openParentHamiltonianES T R N) = groundSpaceES T N :=
    fun N hN =>
      ker_openParentHamiltonianES_toTensorFromBlocks_eq_groundSpaceES_of_wordTupleSpanTop
        μ A hμ hS hSpan hR hN
  obtain ⟨δ, hδ, hcanonical⟩ :=
    exists_openParentHamiltonianES_toTensorFromBlocks_gap_of_wordTupleSpanTop
      μ A hμ hS hSpan hR
  obtain ⟨γ, hγ, hgap⟩ := hh.exists_open_uniform_gap_of_canonical_gap hRpos hδ
    (fun N hN v hv => hcanonical N hN v (by rwa [hKernel N hN] at hv))
  have hDistinct : ∀ i j, i ≠ j → ∀ h : D j = D i,
      ¬ GaugePhaseEquiv (h ▸ A j) (A i) := fun i j hij h => by
    simpa only [eqRec_eq_cast] using not_gaugePhaseEquiv_of_wordTupleSpanTop A hSpan i j hij h
  refine ⟨γ, hγ, ?_⟩
  intro α k X hk hcenter
  let N (n : ℕ) := (n + (R - 1) + k) + (R - 1 + n)
  have hN : Tendsto N atTop atTop :=
    tendsto_atTop_mono (fun n => by dsimp [N]; omega) tendsto_id
  obtain ⟨ψ, hg, hu⟩ := (hP α).exists_eventually_unit_groundSpaceES (hρ α) N hN
  apply multiblock_localCommutator_gap_of_openInteraction_gap
    A ρ hP hρ hDistinct α h hh.isPositive X hRpos hk hcenter ψ hγ.le
  · exact Eventually.of_forall fun n => by
      rw [hh.ker_openInteractionHamiltonianES_eq_ker_openParentHamiltonianES hRpos,
        hKernel (N n) (by dsimp [N]; omega), groundSpaceES_toTensorFromBlocks_eq_iSup μ A hμ]
  · exact Eventually.of_forall fun n => hgap (N n) (by dsimp [N]; omega)
  · exact Eventually.of_forall hg
  · exact hu

/-- The canonical parent interaction at simultaneous injectivity admits one
positive commutator constant for all primitive sectors and all centered local
observables. Source: Nachtergaele, arXiv:cond-mat/9410110, Theorem 1.2 and
Section 6, lines 2649--2675. -/
theorem exists_pos_multiblock_localCommutator_gap_of_wordTupleSpanTop
    (μ : Fin b → ℂ) (A : ∀ i, MPSTensor d (D i)) (hμ : ∀ i, μ i ≠ 0)
    (ρ : ∀ i, Matrix (Fin (D i)) (Fin (D i)) ℂ)
    (hP : ∀ i, IsPrimitiveMPS (A i) (ρ i)) (hρ : ∀ i, (ρ i).PosDef)
    {S R : ℕ} (hS : 0 < S) (hSpan : WordTupleSpanTop A S) (hR : S + 1 ≤ R) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ α : Fin b, ∀ {k : ℕ}
      (X : Matrix (Cfg d k) (Cfg d k) ℂ),
      0 < k → observableInsertionExpectation (A α) (ρ α) X = 0 →
        γ * (observableInsertionExpectation (A α) (ρ α) (Xᴴ * X)).re ≤
          (observableInsertionExpectation (A α) (ρ α) (localCommutatorObservable
            ((Matrix.toEuclideanCLM (n := Cfg d R) (𝕜 := ℂ)).symm
              (groundSpaceES (toTensorFromBlocks (d := d) (μ := μ) A) R)ᗮ.starProjection)
            X)).re := by
  let T := toTensorFromBlocks (d := d) (μ := μ) A
  let h := canonicalParentInteractionMatrix T R
  have hmatrix : Matrix.toEuclideanLin h = parentInteractionES T R :=
    toEuclideanLin_canonicalParentInteractionMatrix T R
  apply exists_pos_multiblock_localCommutator_gap_of_isParentInteraction
    μ A hμ ρ hP hρ hS hSpan hR h
  rw [hmatrix]
  exact isParentInteraction_parentInteractionES T R

end BlockFamily

end MPSTensor
