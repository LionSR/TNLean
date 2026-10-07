/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.PrimitiveLocalCommutatorGap
import TNLean.MPS.ParentHamiltonian.Martingale.OpenParentInteractionGap

/-!
# A primitive-sector local commutator bound for positive parent interactions

A positive finite-range interaction with the prescribed local MPS kernel is
comparable to the canonical parent projection. Its open-chain Hamiltonians
therefore have the same kernels and a uniform positive gap at sufficient
range. Locality and primitive transfer convergence give the corresponding
local commutator inequality, without supplied limiting energy estimates.

Source: Nachtergaele, arXiv:cond-mat/9410110, Theorem 1.2 and Section 6,
lines 2649--2675; CPGSV21, arXiv:2011.12127, lines 2170--2172.

**Scope restriction (one primitive sector):** The commutator conclusions
concern finite-interval expectations of one normalized primitive tensor. The
unconditional existence theorem assumes range at least \(D^4+1\).
The quasi-local formulation, construction of the GNS Hamiltonian, and the
pure multiblock conclusion are not treated here; see
docs/paper-gaps/nachtergaele96_infinite_volume_ground_projection.tex.
-/

open Filter
open scoped Matrix Topology ComplexOrder InnerProductSpace

namespace MPSTensor

variable {d D R k : ℕ}

/-- Positive local parent interactions and the canonical projection have
identical open-chain kernels at every length. Source: CPGSV21,
arXiv:2011.12127, lines 2170--2172. -/
theorem IsParentInteraction.ker_openInteractionHamiltonianES_eq_ker_openParentHamiltonianES
    {A : MPSTensor d D}
    {h : EuclideanSpace ℂ (Cfg d R) →ₗ[ℂ] EuclideanSpace ℂ (Cfg d R)}
    (hh : IsParentInteraction A R h) (hR : 0 < R) (N : ℕ) :
    LinearMap.ker (openInteractionHamiltonianES h N) =
      LinearMap.ker (openParentHamiltonianES A R N) := by
  obtain ⟨κ, C, hκ, hC, hComparison⟩ := hh.exists_pos_open_comparison hR
  apply ((openParentHamiltonianES_isPositive A R N).ker_eq_of_smul_le_of_le_smul
    (openInteractionHamiltonianES_isPositive hh.isPositive N) hκ zero_lt_one hC
    (by simpa only [Complex.ofReal_one, one_smul] using (hComparison N).1)
    (by simpa only [Complex.ofReal_one, one_smul] using (hComparison N).2)).symm

/-- The local commutator inequality for a positive open interaction follows
from its eventual kernel identity and uniform norm gap. Tensor convergence
derives the energy, excitation norm, and ground-projection limits.
Source: Nachtergaele, arXiv:cond-mat/9410110, Section 6, lines 2649--2675. -/
theorem IsPrimitiveMPS.localCommutator_gap_of_openInteraction_gap
    [NeZero D] {A : MPSTensor d D} {ρ : Matrix (Fin D) (Fin D) ℂ}
    (hP : IsPrimitiveMPS A ρ) (hρ : ρ.PosDef)
    (h : Matrix (Cfg d R) (Cfg d R) ℂ)
    (hh : (Matrix.toEuclideanLin h).IsPositive)
    (X : Matrix (Cfg d k) (Cfg d k) ℂ) (hR : 0 < R) (hk : 0 < k)
    (hcenter : observableInsertionExpectation A ρ X = 0)
    (ψ : (n : ℕ) → EuclideanSpace ℂ (Cfg d ((n + (R - 1) + k) + (R - 1 + n))))
    {γ : ℝ} (hγ : 0 ≤ γ)
    (hKernel : ∀ᶠ n in atTop,
      LinearMap.ker (openInteractionHamiltonianES (Matrix.toEuclideanLin h)
        ((n + (R - 1) + k) + (R - 1 + n))) =
          groundSpaceES A ((n + (R - 1) + k) + (R - 1 + n)))
    (hGap : ∀ᶠ n in atTop, ∀ v ∈
      (LinearMap.ker (openInteractionHamiltonianES (Matrix.toEuclideanLin h)
        ((n + (R - 1) + k) + (R - 1 + n))))ᗮ,
      γ * ‖v‖ ≤ ‖openInteractionHamiltonianES (Matrix.toEuclideanLin h)
        ((n + (R - 1) + k) + (R - 1 + n)) v‖)
    (hGround : ∀ᶠ n in atTop,
      ψ n ∈ groundSpaceES A ((n + (R - 1) + k) + (R - 1 + n)))
    (hUnit : ∀ᶠ n in atTop, ‖ψ n‖ = 1) :
    γ * (observableInsertionExpectation A ρ (Xᴴ * X)).re ≤
      (observableInsertionExpectation A ρ (localCommutatorObservable h X)).re := by
  let N (n : ℕ) := (n + (R - 1) + k) + (R - 1 + n)
  let H (n : ℕ) := openInteractionHamiltonianES (Matrix.toEuclideanLin h) (N n)
  have hEnergy :
      let B (n : ℕ) := ((Matrix.toEuclideanCLM (n := Cfg d (N n)) (𝕜 := ℂ))
        (bulkObservable X (n + (R - 1)) (R - 1 + n))).toLinearMap
      Tendsto (fun n =>
        (inner ℂ (((B n).adjoint.comp ((H n).comp (B n) - (B n).comp (H n)))
          (ψ n)) (ψ n)).re) atTop
        (nhds (observableInsertionExpectation A ρ (localCommutatorObservable h X)).re) := by
    apply (hP.localCommutatorObservable_expectation_tendsto hρ h X hR hk
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
  exact hP.commutator_gap_of_bulkObservable_energy_limit hρ X hcenter
    (ℓ := fun n : ℕ => n + (R - 1)) (r := fun n => (R - 1) + n)
    (tendsto_add_atTop_nat (R - 1))
    (tendsto_atTop_mono (fun n => Nat.le_add_left n (R - 1)) tendsto_id)
    H ψ hγ (Eventually.of_forall fun n => openInteractionHamiltonianES_isPositive hh (N n))
    hGap hKernel hGround hUnit hEnergy

/-- Every positive parent interaction at range at least \(D^4+1\) has one
positive local commutator bound throughout the normalized primitive sector.
All finite-volume and limiting estimates are derived internally.
Source: Nachtergaele, arXiv:cond-mat/9410110, Theorem 1.2 and Section 6;
CPGSV21, arXiv:2011.12127, lines 2170--2172. -/
theorem IsPrimitiveMPS.exists_pos_localCommutator_gap_of_isParentInteraction
    [NeZero D] {A : MPSTensor d D} {ρ : Matrix (Fin D) (Fin D) ℂ}
    (hP : IsPrimitiveMPS A ρ) (hρ : ρ.PosDef)
    (h : Matrix (Cfg d R) (Cfg d R) ℂ)
    (hh : IsParentInteraction A R (Matrix.toEuclideanLin h)) (hR : D ^ 4 + 1 ≤ R) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ {k : ℕ} (X : Matrix (Cfg d k) (Cfg d k) ℂ),
      0 < k → observableInsertionExpectation A ρ X = 0 →
        γ * (observableInsertionExpectation A ρ (Xᴴ * X)).re ≤
          (observableInsertionExpectation A ρ (localCommutatorObservable h X)).re := by
  have hNormal := isNormal_of_isPrimitiveMPS_with_posDef hP hρ
  have hD : 0 < D ^ 4 := pow_pos (NeZero.pos D) 4
  have hRpos : 0 < R := by omega
  obtain ⟨δ, hδ, hcanonicalGap⟩ :=
    exists_openParentHamiltonianES_uniform_gap_of_isNormal_of_le A hNormal hR
  obtain ⟨γ, hγ, hgap⟩ :=
    hh.exists_open_uniform_gap_of_canonical_gap hRpos hδ hcanonicalGap
  refine ⟨γ, hγ, ?_⟩
  intro k X hk hcenter
  let N (n : ℕ) := (n + (R - 1) + k) + (R - 1 + n)
  have hN : Tendsto N atTop atTop :=
    tendsto_atTop_mono (fun n => by dsimp [N]; omega) tendsto_id
  obtain ⟨ψ, hg, hu⟩ := hP.exists_eventually_unit_groundSpaceES hρ N hN
  have hInj : Kraus.IsNBlkInjective A (R - 1) :=
    isNBlkInjective_of_le hD (isNBlkInjective_pow_four_of_isNormal A hNormal) (by omega)
  have hRange : R - 1 + 1 = R := by omega
  apply hP.localCommutator_gap_of_openInteraction_gap hρ h hh.isPositive X hRpos hk
    hcenter ψ hγ.le
  · exact Eventually.of_forall fun n => by
      rw [hh.ker_openInteractionHamiltonianES_eq_ker_openParentHamiltonianES hRpos]
      simpa only [hRange] using ker_openParentHamiltonianES_eq_groundSpaceES_of_isNBlkInjective
        hInj (by omega : 0 < R - 1) (by dsimp [N]; omega : R - 1 + 1 ≤ N n)
  · exact Eventually.of_forall fun n => hgap (N n) (by dsimp [N]; omega)
  · exact Eventually.of_forall hg
  · exact hu

end MPSTensor
