/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.PeriodicBlockFamilyParentInteractionGap
import TNLean.MPS.ParentHamiltonian.PeriodicBlockFamilyGap
import TNLean.MPS.ParentHamiltonian.PeriodicFamilyPrimitiveResolution
import TNLean.MPS.ParentHamiltonian.PhysicalResidualCoverLimit
import TNLean.MPS.ParentHamiltonian.CanonicalParentInteractionExistence
import TNLean.MPS.ParentHamiltonian.AllLengthOpenInteractionMatrix

/-!
# Uniform original-length gaps for periodic families

For every sufficiently large canonical interaction range, a finite weighted
family of normalized periodic tensors has exact open kernels and a uniform
gap at every original chain length. The inequality uses the actual kernel,
also at volumes shorter than the interaction range.

Equivalent sectors are removed without changing any finite ground space.
For a nonempty selected family, a common blocking length gives a literal
primitive isometric resolution with exact orthogonal tail Gram matrices.
The aligned gap and residual-cover limit then give a gap at every original
length. The empty family is covered directly by the aligned theorem with
blocking length one. Canonical support transport returns the bound to the
original weighted family.

The constructed canonical interaction also has a common literal
infinite-volume commutator gap for every pure zero-energy state, along
every exhaustion with divergent margins. The constants precede the
states, local observables, filters, and margins. No translation invariance
of a classified state is assumed.

**Scope restriction (tensor presentation):** These results concern finite
weighted families of normalized periodic tensors. The passage from general
GVBS data to such tensor presentations remains separate; see
`docs/paper-gaps/nachtergaele96_infinite_volume_ground_projection.tex`.

Source: Nachtergaele, arXiv:cond-mat/9410110, Theorems 1.1--1.2,
Section 4, Proposition `forintersection` and Lemma `existenceinteraction`,
and Section 6, Lemma `commutation` (ii), lines 2442--2531.
-/

open Filter SpinChain
open scoped Matrix MatrixOrder ComplexOrder BigOperators InnerProductSpace Topology
namespace MPSTensor
variable {d b R : ℕ} [NeZero d] {D : Fin b → ℕ}

private theorem exists_aligned_canonical_gap_of_periodic_family
    (A : ∀ j, MPSTensor d (D j)) (m : Fin b → ℕ)
    (hPeriodic : ∀ j, IsPeriodic (m j) (A j)) (hR : 0 < R)
    (hKernel : ∀ N, R ≤ N →
      LinearMap.ker (openParentHamiltonianES (toTensorFromBlocks (fun _ => 1) A) R N) =
        groundSpaceES (toTensorFromBlocks (fun _ => 1) A) N)
    (L : ℕ) (hL : 0 < L) (hdiv : ∀ j, m j ∣ L) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ n, ∀ v ∈
      (LinearMap.ker (openParentHamiltonianES (toTensorFromBlocks (fun _ => 1) A) R (n * L)))ᗮ,
      γ * ‖v‖ ≤ ‖openParentHamiltonianES (toTensorFromBlocks (fun _ => 1) A) R (n * L) v‖ := by
  let T := toTensorFromBlocks (fun _ => 1) A
  let h := canonicalParentInteractionMatrix T R
  have hEventual : ∀ᶠ N in atTop,
      LinearMap.ker (openInteractionHamiltonianES (Matrix.toEuclideanLin h) N) =
        groundSpaceES T N := by
    filter_upwards [eventually_ge_atTop R] with N hN
    rw [toEuclideanLin_canonicalParentInteractionMatrix,
      openInteractionHamiltonianES_parentInteractionES _ hR]
    exact hKernel N hN
  obtain ⟨γ, hγ, hGap⟩ := exists_aligned_openInteractionMatrix_gap_of_periodic_family_of_dvd
    (fun _ => 1) A (fun _ => one_ne_zero) m hPeriodic L hL hdiv h
    (canonicalParentInteractionMatrix_posSemidef T R) hR hEventual
  refine ⟨γ, hγ, ?_⟩
  intro n
  have hEq : Matrix.toEuclideanLin (openInteractionMatrix h (n * L)) =
      openParentHamiltonianES T R (n * L) := by
    rw [← openInteractionHamiltonianES_eq_toEuclideanLin_openInteractionMatrix_all h hR (n * L),
      show h = canonicalParentInteractionMatrix T R from rfl,
      toEuclideanLin_canonicalParentInteractionMatrix,
      openInteractionHamiltonianES_parentInteractionES _ hR]
  simpa only [hEq] using hGap n

private theorem exists_canonical_gap_of_empty_periodic_family {D : Fin 0 → ℕ}
    (A : ∀ j : Fin 0, MPSTensor d (D j))
    (m : Fin 0 → ℕ) (hPeriodic : ∀ j, IsPeriodic (m j) (A j)) (hR : 0 < R)
    (hKernel : ∀ N, R ≤ N →
      LinearMap.ker (openParentHamiltonianES (toTensorFromBlocks (fun _ => 1) A) R N) =
        groundSpaceES (toTensorFromBlocks (fun _ => 1) A) N) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ N, ∀ v ∈
      (LinearMap.ker (openParentHamiltonianES (toTensorFromBlocks (fun _ => 1) A) R N))ᗮ,
      δ * ‖v‖ ≤ ‖openParentHamiltonianES (toTensorFromBlocks (fun _ => 1) A) R N v‖ := by
  obtain ⟨γ, hγ, hGap⟩ := exists_aligned_canonical_gap_of_periodic_family
    A m hPeriodic hR hKernel 1 zero_lt_one (fun j => Fin.elim0 j)
  let P (N : ℕ) : Prop := ∀ v ∈ (LinearMap.ker
    (openParentHamiltonianES (toTensorFromBlocks (fun _ => 1) A) R N))ᗮ,
    γ * ‖v‖ ≤ ‖openParentHamiltonianES (toTensorFromBlocks (fun _ => 1) A) R N v‖
  refine ⟨γ, hγ, ?_⟩
  intro N
  have hN : P (N * 1) := hGap N
  change P N
  simpa only [Nat.mul_one] using hN


private theorem exists_canonical_gap_of_periodic_family
    (A : ∀ j, MPSTensor d (D j)) (m : Fin b → ℕ)
    (hPeriodic : ∀ j, IsPeriodic (m j) (A j)) (hDistinct : BlocksNotGaugePhaseEquiv A)
    (hR : 0 < R)
    (hKernel : ∀ N, R ≤ N →
      LinearMap.ker (openParentHamiltonianES (toTensorFromBlocks (fun _ => 1) A) R N) =
        groundSpaceES (toTensorFromBlocks (fun _ => 1) A) N) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ N, ∀ v ∈
      (LinearMap.ker (openParentHamiltonianES (toTensorFromBlocks (fun _ => 1) A) R N))ᗮ,
      δ * ‖v‖ ≤ ‖openParentHamiltonianES (toTensorFromBlocks (fun _ => 1) A) R N v‖ := by
  classical
  by_cases hb : b = 0
  · subst b
    exact exists_canonical_gap_of_empty_periodic_family A m hPeriodic hR hKernel
  let j₀ : Fin b := ⟨0, Nat.pos_of_ne_zero hb⟩
  have hSumDim : 0 < ∑ j, D j :=
    (Nat.pos_of_ne_zero (hPeriodic j₀).bondDim_ne_zero).trans_le
      (Finset.single_le_sum (fun j _ => Nat.zero_le (D j)) (Finset.mem_univ j₀))
  let _ : NeZero (∑ j, D j) := ⟨Nat.ne_of_gt hSumDim⟩
  let L := ∏ j, m j
  have hL : 0 < L := Finset.prod_pos fun j _ => (hPeriodic j).period_pos
  have hdiv : ∀ j, m j ∣ L := fun j =>
    Finset.dvd_prod_of_mem m (Finset.mem_univ j)
  obtain ⟨sdim, hsdim, B, V, ρ, hP, hρ, hSep, hV, hSum, hInt, hCoInt,
    Q, hQ, hGram⟩ := exists_commonBlock_primitive_sector_resolution_of_isPeriodic
      A m hPeriodic hDistinct L hL hdiv
  let _ : ∀ s, NeZero (sdim s) := fun s => ⟨Nat.ne_of_gt (hsdim s)⟩
  obtain ⟨γ, hγ, hAligned⟩ := exists_aligned_canonical_gap_of_periodic_family
    A m hPeriodic hR hKernel L hL hdiv
  exact exists_pos_openParentHamiltonianES_gap_of_aligned_gap_of_primitive_resolution
    (N₀ := R) (toTensorFromBlocks (fun _ => 1) A) B V ρ hP hρ hSep
    hV hSum hInt hCoInt Q hQ hGram hR hL hKernel hγ (fun n _ => hAligned n)

/-- A finite weighted family of normalized periodic tensors has exact canonical
open kernels and a positive gap at every original volume, for every sufficiently
large interaction range. The norm bound is above each volume's actual kernel.
Source: Nachtergaele, arXiv:cond-mat/9410110, Theorem 1.2, Section 4,
Lemma `existenceinteraction`, and Section 6, Lemma `commutation` (ii). -/
theorem exists_openParentHamiltonianES_gap_of_periodic_family
    (μ : Fin b → ℂ) (A : ∀ j, MPSTensor d (D j)) (hμ : ∀ j, μ j ≠ 0)
    (m : Fin b → ℕ) (hPeriodic : ∀ j, IsPeriodic (m j) (A j)) :
    ∃ R₀, 0 < R₀ ∧ ∀ R, R₀ ≤ R →
      (∀ N, R ≤ N →
        LinearMap.ker (openParentHamiltonianES (toTensorFromBlocks μ A) R N) =
          groundSpaceES (toTensorFromBlocks μ A) N) ∧
      ∃ δ : ℝ, 0 < δ ∧ ∀ N, ∀ v ∈
        (LinearMap.ker (openParentHamiltonianES (toTensorFromBlocks μ A) R N))ᗮ,
        δ * ‖v‖ ≤ ‖openParentHamiltonianES (toTensorFromBlocks μ A) R N v‖ := by
  obtain ⟨g, sel, hsel, hD, hP, hDistinct, hCover, hJoint⟩ :=
    exists_periodic_sector_representatives μ A hμ hPeriodic
  let B := fun j => A (sel j)
  obtain ⟨R₀, hR₀, hKernel⟩ := exists_ker_openParentHamiltonianES_of_periodic_family
    μ A hμ m hPeriodic
  refine ⟨R₀, hR₀, ?_⟩
  intro R hRR
  have hR : 0 < R := hR₀.trans_le hRR
  have hEq (N : ℕ) := openParentHamiltonianES_eq_of_groundSpaceES_eq hR (hJoint R) N
  have hKernelB (N : ℕ) (hRN : R ≤ N) :
      LinearMap.ker (openParentHamiltonianES (toTensorFromBlocks (fun _ => 1) B) R N) =
        groundSpaceES (toTensorFromBlocks (fun _ => 1) B) N := by
    rw [← hEq N]
    exact (hKernel R N hRR hRN).trans (hJoint N)
  obtain ⟨δ, hδ, hGap⟩ := exists_canonical_gap_of_periodic_family
    B (fun j => m (sel j)) hP hDistinct hR hKernelB
  refine ⟨fun N => hKernel R N hRR, δ, hδ, ?_⟩
  intro N
  simpa only [B, ← hEq N] using hGap N

/-- A periodic family admits one canonical positive interaction with exact open
kernels, a uniform finite gap at all original lengths, and a common literal
infinite-volume commutator gap for every pure zero-energy state. No sector
separation, invariant matrix, interaction, or kernel identity is supplied.
Source: Nachtergaele, arXiv:cond-mat/9410110, Theorems 1.1--1.2,
Lemma `existenceinteraction`, and Section 6, Lemma `commutation` (ii). -/
theorem exists_positive_parent_interaction_finite_quasiLocal_gap_of_periodic_family
    (μ : Fin b → ℂ) (A : ∀ j, MPSTensor d (D j)) (hμ : ∀ j, μ j ≠ 0)
    (m : Fin b → ℕ) (hPeriodic : ∀ j, IsPeriodic (m j) (A j)) :
    ∃ R : ℕ, 0 < R ∧ ∃ h : Matrix (Cfg d R) (Cfg d R) ℂ,
      h = canonicalParentInteractionMatrix (toTensorFromBlocks μ A) R ∧ h.PosSemidef ∧
      (∀ N : ℕ, R ≤ N →
        LinearMap.ker (openInteractionHamiltonianES (Matrix.toEuclideanLin h) N) =
          groundSpaceES (toTensorFromBlocks μ A) N) ∧
    ∃ δ : ℝ, 0 < δ ∧
      (∀ N, ∀ v ∈ (LinearMap.ker (Matrix.toEuclideanLin (openInteractionMatrix h N)))ᗮ,
        δ * ‖v‖ ≤ ‖Matrix.toEuclideanLin (openInteractionMatrix h N) v‖) ∧
    ∃ γ : ℝ, 0 < γ ∧
      ∀ φ : QuasiLocalAlgebra d →L[ℂ] ℂ,
        φ ∈ parentGroundStateFace h → IsPureQuasiLocalState d φ →
        ∀ (a : ℤ) {k : ℕ} (X : Matrix (Cfg d k) (Cfg d k) ℂ),
          0 < k → φ (quasiLocalIntervalObservable d a k X) = 0 →
          ∀ {ι : Type*} {f : Filter ι} {ℓ r : ι → ℕ},
            Tendsto ℓ f atTop → Tendsto r f atTop →
          ∃ e : ℂ, Tendsto (fun n => φ
            (star (quasiLocalIntervalObservable d a k X) *
              (quasiLocalIntervalObservable d (a - (ℓ n : ℤ)) ((ℓ n + k) + r n)
                  (openInteractionMatrix h ((ℓ n + k) + r n)) *
                quasiLocalIntervalObservable d a k X -
                quasiLocalIntervalObservable d a k X *
                  quasiLocalIntervalObservable d (a - (ℓ n : ℤ)) ((ℓ n + k) + r n)
                    (openInteractionMatrix h ((ℓ n + k) + r n))))) f (𝓝 e) ∧
            (γ : ℂ) * φ (star (quasiLocalIntervalObservable d a k X) *
              quasiLocalIntervalObservable d a k X) ≤ e := by
  obtain ⟨R, hR, hAll⟩ := exists_openParentHamiltonianES_gap_of_periodic_family
    μ A hμ m hPeriodic
  obtain ⟨hKernelCanonical, δ, hδ, hGapCanonical⟩ := hAll R le_rfl
  obtain ⟨h, heq, hh, hKernel⟩ :=
    exists_positive_canonical_parent_interaction_of_exact_open_kernels
      (toTensorFromBlocks μ A) hR hKernelCanonical
  have hGapMatrix (N : ℕ) : ∀ v ∈
      (LinearMap.ker (Matrix.toEuclideanLin (openInteractionMatrix h N)))ᗮ,
      δ * ‖v‖ ≤ ‖Matrix.toEuclideanLin (openInteractionMatrix h N) v‖ := by
    have hEq : Matrix.toEuclideanLin (openInteractionMatrix h N) =
        openParentHamiltonianES (toTensorFromBlocks μ A) R N := by
      rw [← openInteractionHamiltonianES_eq_toEuclideanLin_openInteractionMatrix_all h hR N,
        heq, toEuclideanLin_canonicalParentInteractionMatrix,
        openInteractionHamiltonianES_parentInteractionES _ hR]
    simpa only [hEq] using hGapCanonical N
  have hEventual := (eventually_ge_atTop R).mono fun N hN => hKernel N hN
  obtain ⟨γ, hγ, hGap⟩ := exists_pos_quasiLocalCommutator_limit_gap_of_periodic_family
    μ A hμ m hPeriodic h hR hh hEventual
  exact ⟨R, hR, h, heq, hh, hKernel, δ, hδ, hGapMatrix, γ, hγ, hGap⟩

end MPSTensor
