/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.PrimitiveBoundaryCommutatorGap
import TNLean.MPS.ParentHamiltonian.BulkObservableCommutator
import TNLean.MPS.ParentHamiltonian.Martingale.NormalOpenGapAtWielandtRange
import TNLean.Wielandt.Primitivity.StronglyIrreducibleToFullRank

import TNLean.MPS.ParentHamiltonian.CanonicalParentInteractionMatrix

/-!
# A local commutator inequality in one primitive sector

A finite-range commutator of a fixed interior observable is supported on a
fixed interval. Primitive transfer convergence therefore determines its
limiting expectation. Combined with the finite-volume gap and the vanishing
full ground-space projection, this gives the local commutator inequality.

Source: Nachtergaele, arXiv:cond-mat/9410110, Theorem 1.2, lines 933--947,
and Section 6, lines 2649--2675.

**Scope restriction (finite-interval primitive-sector state):** The results
concern the consistent finite-interval expectations of one normalized
primitive tensor. Their quasi-local formulation is proved in
`QuasiLocalPrimitiveGap.lean`; construction of the GNS
Hamiltonian remains separate; see
`docs/paper-gaps/nachtergaele96_infinite_volume_ground_projection.tex`.
-/

open Filter
open scoped Matrix Topology ComplexOrder InnerProductSpace

namespace MPSTensor

variable {d D R k : ℕ}

private noncomputable def reindexChainVector {N M : ℕ} (h : N = M)
    (v : EuclideanSpace ℂ (Cfg d N)) : EuclideanSpace ℂ (Cfg d M) :=
  h ▸ v

private theorem reindexChainVector_norm {N M : ℕ} (h : N = M)
    (v : EuclideanSpace ℂ (Cfg d N)) : ‖reindexChainVector h v‖ = ‖v‖ := by
  subst M
  rfl

private theorem reindexChainVector_mem {N M : ℕ} (h : N = M)
    (A : MPSTensor d D) (v : EuclideanSpace ℂ (Cfg d N)) :
    reindexChainVector h v ∈ groundSpaceES A M ↔ v ∈ groundSpaceES A N := by
  subst M
  rfl

private theorem reindexChainVector_inner_window {N M : ℕ} (h : N = M)
    (v : EuclideanSpace ℂ (Cfg d N)) (a : ℕ)
    (Y : Matrix (Cfg d k) (Cfg d k) ℂ) :
    inner ℂ (reindexChainVector h v)
      ((Matrix.toEuclideanCLM (n := Cfg d M) (𝕜 := ℂ))
        (chainWindowOperator M a Y) (reindexChainVector h v)) =
      inner ℂ v ((Matrix.toEuclideanCLM (n := Cfg d N) (𝕜 := ℂ))
        (chainWindowOperator N a Y) v) := by
  subst M
  rfl

/-- The finite-volume commutator energy converges to the expectation of its
fixed local patch. No energy-limit assumption is needed.
Source: Nachtergaele, arXiv:cond-mat/9410110, Section 6, lines 2649--2675. -/
theorem IsPrimitiveMPS.localCommutatorObservable_expectation_tendsto
    [NeZero D] {A : MPSTensor d D} {ρ : Matrix (Fin D) (Fin D) ℂ}
    (hP : IsPrimitiveMPS A ρ) (hρ : ρ.PosDef)
    (h : Matrix (Cfg d R) (Cfg d R) ℂ) (X : Matrix (Cfg d k) (Cfg d k) ℂ)
    (hR : 0 < R) (hk : 0 < k)
    (N : ℕ → ℕ) (hN : ∀ n, N n = (n + ((R - 1 + k) + (R - 1))) + n)
    (ψ : (n : ℕ) → EuclideanSpace ℂ (Cfg d (N n)))
    (hGround : ∀ᶠ n in atTop, ψ n ∈ groundSpaceES A (N n))
    (hUnit : ∀ᶠ n in atTop, ‖ψ n‖ = 1) :
    Tendsto (fun n =>
      let B := chainWindowOperator (N n) (n + (R - 1)) X
      (inner ℂ (((Matrix.toEuclideanCLM (n := Cfg d (N n)) (𝕜 := ℂ))
        (Bᴴ * (openInteractionMatrix h (N n) * B - B * openInteractionMatrix h (N n))))
          (ψ n)) (ψ n)).re) atTop
      (nhds (observableInsertionExpectation A ρ (localCommutatorObservable h X)).re) := by
  let ψ' (n : ℕ) := reindexChainVector (hN n) (ψ n)
  have hg : ∀ᶠ n in atTop,
      ψ' n ∈ groundSpaceES A ((n + ((R - 1 + k) + (R - 1))) + n) := by
    filter_upwards [hGround] with n hn
    exact (reindexChainVector_mem (hN n) A (ψ n)).mpr hn
  have hu : ∀ᶠ n in atTop, ‖ψ' n‖ = 1 := by
    filter_upwards [hUnit] with n hn
    exact (reindexChainVector_norm (hN n) (ψ n)).trans hn
  have hlim := (Complex.continuous_re.tendsto _).comp
    (hP.bulkObservable_groundState_expectation_tendsto hρ
      (localCommutatorObservable h X) tendsto_id tendsto_id ψ' hg hu)
  apply hlim.congr'
  filter_upwards [] with n
  dsimp only [Function.comp_def, id_eq]
  rw [chainWindowOperator_adjoint_mul_openInteractionMatrix_commutator
    h X hR hk (by rw [hN]; omega), bulkObservable_eq_chainWindowOperator (by omega)]
  calc
    _ = (inner ℂ (ψ n) ((Matrix.toEuclideanCLM (n := Cfg d (N n)) (𝕜 := ℂ))
        (chainWindowOperator (N n) n (localCommutatorObservable h X)) (ψ n))).re :=
      congrArg Complex.re (reindexChainVector_inner_window (hN n) (ψ n) n _)
    _ = _ := by
      simpa only [← RCLike.re_eq_complex_re] using inner_re_symm (ψ n)
        ((Matrix.toEuclideanCLM (n := Cfg d (N n)) (𝕜 := ℂ))
          (chainWindowOperator (N n) n (localCommutatorObservable h X)) (ψ n))

/-- Expanding primitive MPS spaces admit normalized boundary vectors without
assuming finite-volume uniqueness. At short lengths the chosen vectors may
vanish, but their norms are eventually one. Source: Nachtergaele,
arXiv:cond-mat/9410110, Section 6, the finite-volume boundary approximation. -/
theorem IsPrimitiveMPS.exists_eventually_unit_groundSpaceES
    [NeZero D] {A : MPSTensor d D} {ρ : Matrix (Fin D) (Fin D) ℂ}
    (hP : IsPrimitiveMPS A ρ) (hρ : ρ.PosDef)
    {ι : Type*} {f : Filter ι} (N : ι → ℕ) (hN : Tendsto N f atTop) :
    ∃ ψ : (n : ι) → EuclideanSpace ℂ (Cfg d (N n)),
      (∀ n, ψ n ∈ groundSpaceES A (N n)) ∧ (∀ᶠ n in f, ‖ψ n‖ = 1) := by
  let u := (EuclideanSpace.basisFun (Fin D × Fin D) ℂ) (0, 0)
  have hu : u ≠ 0 := (EuclideanSpace.basisFun (Fin D × Fin D) ℂ).toBasis.ne_zero (0, 0)
  let ψ (n : ι) := (‖groundSpaceMapES A (N n) u‖⁻¹ : ℂ) •
    groundSpaceMapES A (N n) u
  refine ⟨ψ, ?_, ?_⟩
  · intro n
    apply (groundSpaceES A (N n)).smul_mem
    rw [← range_groundSpaceMapES]
    exact ⟨u, rfl⟩
  · filter_upwards [hN.eventually
      (hP.eventually_groundSpaceMapES_injective_and_inverseGram_bound hρ
        (a := 1 / 2) (by norm_num) (by norm_num))] with n hn
    obtain ⟨hInj, _, _⟩ := hn
    have hv : groundSpaceMapES A (N n) u ≠ 0 := by
      intro hzero
      apply hu
      exact hInj (by simpa only [map_zero] using hzero)
    exact norm_smul_inv_norm hv

/-- The local commutator inequality for the canonical open interaction follows
from its eventual ground-space identity and uniform norm gap. The commutator
energy limit is derived from locality and primitive transfer convergence.
Source: Nachtergaele, arXiv:cond-mat/9410110, Section 6, lines 2649--2675. -/
theorem IsPrimitiveMPS.localCommutator_gap_of_open_gap
    [NeZero D] {A : MPSTensor d D} {ρ : Matrix (Fin D) (Fin D) ℂ}
    (hP : IsPrimitiveMPS A ρ) (hρ : ρ.PosDef)
    (X : Matrix (Cfg d k) (Cfg d k) ℂ) (hR : 0 < R) (hk : 0 < k)
    (hcenter : observableInsertionExpectation A ρ X = 0)
    (ψ : (n : ℕ) → EuclideanSpace ℂ (Cfg d ((n + (R - 1) + k) + (R - 1 + n))))
    {γ : ℝ} (hγ : 0 ≤ γ)
    (hKernel : ∀ᶠ n in atTop,
      LinearMap.ker (openParentHamiltonianES A R ((n + (R - 1) + k) + (R - 1 + n))) =
        groundSpaceES A ((n + (R - 1) + k) + (R - 1 + n)))
    (hGap : ∀ᶠ n in atTop, ∀ v ∈
      (LinearMap.ker (openParentHamiltonianES A R ((n + (R - 1) + k) + (R - 1 + n))))ᗮ,
      γ * ‖v‖ ≤ ‖openParentHamiltonianES A R ((n + (R - 1) + k) + (R - 1 + n)) v‖)
    (hGround : ∀ᶠ n in atTop,
      ψ n ∈ groundSpaceES A ((n + (R - 1) + k) + (R - 1 + n)))
    (hUnit : ∀ᶠ n in atTop, ‖ψ n‖ = 1) :
    γ * (observableInsertionExpectation A ρ (Xᴴ * X)).re ≤
      (observableInsertionExpectation A ρ (localCommutatorObservable
        ((Matrix.toEuclideanCLM (n := Cfg d R) (𝕜 := ℂ)).symm
          (groundSpaceES A R)ᗮ.starProjection) X)).re := by
  let N (n : ℕ) := (n + (R - 1) + k) + (R - 1 + n)
  let h := canonicalParentInteractionMatrix A R
  let B (n : ℕ) := ((Matrix.toEuclideanCLM (n := Cfg d (N n)) (𝕜 := ℂ))
    (chainWindowOperator (N n) (n + (R - 1)) X)).toLinearMap
  have hGround' : ∀ᶠ n in atTop,
      ψ n ∈ LinearMap.ker (openParentHamiltonianES A R (N n)) := by
    filter_upwards [hKernel, hGround] with n hn hg
    simpa only [N, hn] using hg
  have hNorm : Tendsto (fun n => ‖B n (ψ n)‖ ^ 2) atTop
      (nhds (observableInsertionExpectation A ρ (Xᴴ * X)).re) := by
    have hnorm := hP.bulkObservable_groundState_norm_sq_tendsto hρ X
      (ℓ := fun n : ℕ => n + (R - 1)) (r := fun n => (R - 1) + n)
      (tendsto_add_atTop_nat (R - 1))
      (by simpa only [Nat.add_comm] using tendsto_add_atTop_nat (R - 1))
    simp only [bulkObservable_eq_chainWindowOperator hk] at hnorm
    exact hnorm ψ hGround hUnit
  have hProjection : Tendsto (fun n =>
      ‖(LinearMap.ker (openParentHamiltonianES A R (N n))).starProjection
        (B n (ψ n))‖ ^ 2) atTop (nhds 0) := by
    have hproj := hP.bulkObservable_groundSpace_projection_norm_sq_tendsto_zero hρ X
      hcenter (ℓ := fun n : ℕ => n + (R - 1)) (r := fun n => (R - 1) + n)
      (tendsto_add_atTop_nat (R - 1))
      (by simpa only [Nat.add_comm] using tendsto_add_atTop_nat (R - 1))
    simp only [bulkObservable_eq_chainWindowOperator hk] at hproj
    apply (hproj ψ hGround (hUnit.mono fun _ hn => hn.le)).congr'
    filter_upwards [hKernel] with n hn
    simp only [B, N, hn, ContinuousLinearMap.coe_coe]
  have hEnergy : Tendsto (fun n =>
      (inner ℂ (((B n).adjoint.comp
        ((openParentHamiltonianES A R (N n)).comp (B n) -
          (B n).comp (openParentHamiltonianES A R (N n)))) (ψ n)) (ψ n)).re)
      atTop (nhds (observableInsertionExpectation A ρ (localCommutatorObservable h X)).re) := by
    have henergy := hP.localCommutatorObservable_expectation_tendsto hρ h X hR hk
      N (fun n => by dsimp [N]; omega) ψ hGround hUnit
    apply henergy.congr'
    filter_upwards [] with n
    have hH : Matrix.toEuclideanCLM (n := Cfg d (N n)) (𝕜 := ℂ)
        (openInteractionMatrix h (N n)) =
        (openParentHamiltonianES A R (N n)).toContinuousLinearMap :=
      congrArg LinearMap.toContinuousLinearMap
        (toEuclideanCLM_openInteractionMatrix_parentInteraction A hR (by dsimp [N]; omega))
    dsimp only
    rw [map_mul, map_sub, map_mul, map_mul, ← Matrix.star_eq_conjTranspose,
      map_star, ContinuousLinearMap.star_eq_adjoint, hH]
    rfl
  exact FrustrationFree.commutator_gap_of_tendsto_ground_projection_zero
    (fun n => openParentHamiltonianES A R (N n)) B ψ hγ
    (Eventually.of_forall fun n => openParentHamiltonianES_isPositive A R (N n))
    hGap hGround' hNorm hProjection hEnergy

/-- At every range at least \(D^4+1\), a normalized primitive sector obeys
one positive local commutator bound for all centered local observables.
The finite-volume kernel, gap, and unit boundary approximants are derived
internally. Source: Nachtergaele, arXiv:cond-mat/9410110, Theorem 1.2 and
Section 6; arXiv:0909.5347, the quantum Wielandt injectivity bound. -/
theorem IsPrimitiveMPS.exists_pos_localCommutator_gap_of_wielandt_range
    [NeZero D] {A : MPSTensor d D} {ρ : Matrix (Fin D) (Fin D) ℂ}
    (hP : IsPrimitiveMPS A ρ) (hρ : ρ.PosDef) (hR : D ^ 4 + 1 ≤ R) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ {k : ℕ} (X : Matrix (Cfg d k) (Cfg d k) ℂ),
      0 < k → observableInsertionExpectation A ρ X = 0 →
        γ * (observableInsertionExpectation A ρ (Xᴴ * X)).re ≤
          (observableInsertionExpectation A ρ (localCommutatorObservable
            ((Matrix.toEuclideanCLM (n := Cfg d R) (𝕜 := ℂ)).symm
              (groundSpaceES A R)ᗮ.starProjection) X)).re := by
  have hNormal := isNormal_of_isPrimitiveMPS_with_posDef hP hρ
  obtain ⟨γ, hγ, hgap⟩ :=
    exists_openParentHamiltonianES_uniform_gap_of_isNormal_of_le A hNormal hR
  refine ⟨γ, hγ, ?_⟩
  intro k X hk hcenter
  have hD : 0 < D ^ 4 := pow_pos (NeZero.pos D) 4
  have hRpos : 0 < R := by omega
  let N (n : ℕ) := (n + (R - 1) + k) + (R - 1 + n)
  have hN : Tendsto N atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [eventually_ge_atTop b] with n hn
    dsimp [N]
    omega
  obtain ⟨ψ, hg, hu⟩ := hP.exists_eventually_unit_groundSpaceES hρ N hN
  have hInj : Kraus.IsNBlkInjective A (R - 1) :=
    isNBlkInjective_of_le hD (isNBlkInjective_pow_four_of_isNormal A hNormal) (by omega)
  have hRange : R - 1 + 1 = R := by omega
  apply hP.localCommutator_gap_of_open_gap hρ X hRpos hk hcenter ψ hγ.le
  · exact Eventually.of_forall fun n => by
      simpa only [hRange] using ker_openParentHamiltonianES_eq_groundSpaceES_of_isNBlkInjective
        hInj (by omega : 0 < R - 1) (by dsimp [N]; omega : R - 1 + 1 ≤ N n)
  · exact Eventually.of_forall fun n => hgap (N n) (by dsimp [N]; omega)
  · exact Eventually.of_forall hg
  · exact hu

end MPSTensor
