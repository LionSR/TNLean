/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.Periodic.PeriodicBlockFamilyParentInteractionGap
import TNLean.MPS.ParentHamiltonian.BlockGroundSpace.Sector.PrimitiveWitnessTransport
import TNLean.MPS.ParentHamiltonian.Interaction.PrimitiveFamilyIntersection
import TNLean.MPS.ParentHamiltonian.BulkObservable.BulkObservableCommutator
import TNLean.MPS.ParentHamiltonian.Interaction.ParentInteractionGap
import TNLean.MPS.ParentHamiltonian.Blocking.BlockedFiniteGapTransport
import TNLean.MPS.ParentHamiltonian.BlockGroundSpace.Sector.PeriodicBlockFamilyPresentation
import TNLean.MPS.CanonicalForm.BNT.Separation
import QICLean.Analysis.Projection.ProjectionProductDefect
import TNLean.MPS.ParentHamiltonian.ProjectorDefect.Residual.ResidualWindowFullSectorSum
import TNLean.MPS.ParentHamiltonian.ProjectorDefect.Residual.ResidualWindowLeftGroundSpace
import TNLean.MPS.ParentHamiltonian.ProjectorDefect.Residual.ResidualWindowJointProjectionDecay
import TNLean.MPS.ParentHamiltonian.Blocking.ResidueCoverGapCriterion

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
docs/paper-gaps/nachtergaele96_infinite_volume_ground_projection.tex.

Source: Nachtergaele, arXiv:cond-mat/9410110, Theorems 1.1--1.2,
Section 4, Proposition forintersection and Lemma existenceinteraction,
and Section 6, Lemma commutation (ii), lines 2442--2531.

## Gaps for a supplied positive interaction and a periodic family

Let a finite weighted family consist of normalized periodic tensors.
Every positive interaction of positive range whose open kernels eventually
equal the joint MPS boundary spaces has one gap above the kernel at every original
volume, above its actual finite-volume kernel. The canonical all-range gap
and a finite-window comparison derive the gap of the supplied interaction.
No local-kernel identity at its interaction range is assumed.

For the same supplied interaction, the literal infinite-volume commutator
energies have a common positive lower bound in every pure zero-energy state,
along every exhaustion with divergent boundary margins. No translation
invariance of the classified state, sector inequivalence, invariant matrix,
primitive presentation, finite gap, or lower interaction-range bound is
supplied. The finite family may be empty.

**Scope restriction (tensor presentation):** These statements concern finite
weighted families of normalized periodic tensors. The passage from general
GVBS data to such tensor presentations remains separate; see
docs/paper-gaps/nachtergaele96_infinite_volume_ground_projection.tex.

Source: Nachtergaele, arXiv:cond-mat/9410110, Theorems 1.1--1.2,
lines 933--947, condition C1, and Section 6, lines 2593--2675.

It also contains the following results.

* `MPSTensor.exists_aligned_hamiltonian_chainTranslates_gap_of_periodic_family_of_dvd`,
  `MPSTensor.exists_aligned_hamiltonian_chainTranslates_gap_of_periodic_family`: aligned
  finite-chain gaps for periodic block families.
* `MPSTensor.residual_cover_projection_defect_tendsto_zero_of_primitive_resolution`,
  `MPSTensor.exists_pos_hamiltonian_parentChainInteraction_gap_of_aligned_gap_of_primitive_resolution`:
  physical residual covers from a primitive-sector resolution.
-/

section PeriodicBlockFamilyGap

/-!
## Aligned finite-chain gaps for periodic block families

A finite weighted family of normalized periodic tensors admits an exact
primitive faithful presentation after blocking by any positive common period
multiple. A positive interaction with the eventual original joint MPS kernel
therefore has one gap on all volumes divisible by that blocking length.
The product of the periods supplies a positive blocking length automatically,
including the empty family, for which this product is one.

The norm inequality is measured on the orthogonal complement of the actual
finite-volume kernel. Short aligned volumes are included through the existing
finite minimum argument; no lower length bound remains in the conclusion.
The original family need not be pairwise inequivalent and no invariant
matrices are supplied.

Source: Nachtergaele, arXiv:cond-mat/9410110, Theorem 1.2,
site grouping at lines 825--836, and Section 3, equations (3.12)--(3.14),
lines 1547--1570; DCCSP17, arXiv:1708.00029,
Lemma lem:blocking-arbitrary, lines 434--451.

**Scope restriction (common-period divisible lengths):** The conclusions
concern lengths divisible by the chosen common blocking length. Uniform gaps
for the other original residue lengths and identification of general GVBS
presentations remain separate. See
docs/paper-gaps/nachtergaele96_infinite_volume_ground_projection.tex.
-/

open scoped Matrix MatrixOrder ComplexOrder InnerProductSpace BigOperators
open ManyBody.Interaction (chainTranslates)

namespace MPSTensor
variable {d r R : ℕ} [NeZero d] {dim : Fin r → ℕ}

/-- Any positive common multiple of the sector periods gives a uniform gap
on all aligned volumes, under positivity and the eventual original kernel
identity. The gap is measured above each volume's actual kernel (every eigenvalue is `0` or
at least the gap), including short volumes. Source: Nachtergaele, arXiv:cond-mat/9410110,
Theorem 1.2 and Section 3, equations (3.12)--(3.14), lines 1547--1570;
DCCSP17, arXiv:1708.00029, Lemma lem:blocking-arbitrary, lines 434--451. -/
theorem exists_aligned_hamiltonian_chainTranslates_gap_of_periodic_family_of_dvd
    (μ : Fin r → ℂ) (A : ∀ j, MPSTensor d (dim j)) (hμ : ∀ j, μ j ≠ 0)
    (m : Fin r → ℕ) (hPeriodic : ∀ j, IsPeriodic (m j) (A j))
    (L : ℕ) (hL : 0 < L) (hdiv : ∀ j, m j ∣ L)
    (h : Matrix (Cfg d R) (Cfg d R) ℂ) (hh : h.PosSemidef)
    (hker : ∀ᶠ n in Filter.atTop,
      LinearMap.ker (Matrix.toEuclideanLin (chainTranslates R n h).hamiltonian) =
        groundSpaceES (toTensorFromBlocks μ A) n) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ N,
      ∀ z : ℂ, Module.End.HasEigenvalue
        (Matrix.toEuclideanLin ((chainTranslates R (N * L) h).hamiltonian)) z →
          z = 0 ∨ (γ : ℂ) ≤ z := by
  obtain ⟨g, bdim, hdim, B, ρ, hP, hρ, hDistinct, hJoint⟩ :=
    exists_primitive_blockFamilyPresentation_of_period_dvd μ A hμ m hPeriodic L hL hdiv
  let : NeZero L := ⟨Nat.ne_of_gt hL⟩
  let : ∀ j, NeZero (bdim j) := fun j => ⟨Nat.ne_of_gt (hdim j)⟩
  have hcover : R + L ≤ (R + 1) * L + 1 := by nlinarith [hL]
  exact exists_aligned_hamiltonian_chainTranslates_gap_of_blocked_primitive_family
    (K := R + 1) (toTensorFromBlocks μ A) (fun _ => 1) B (fun _ => one_ne_zero)
    ρ hP hρ hDistinct.forall_ne_transport hJoint h hh hcover hker

/-- A finite periodic weighted family and eventual original open-chain kernels
have a positive blocking length with one gap on every aligned volume.
No faithful fixed-point witnesses or original sector inequivalence are supplied.
The family may be empty. Source: Nachtergaele, arXiv:cond-mat/9410110,
Theorem 1.2, site grouping at lines 825--836, and Section 3;
DCCSP17, arXiv:1708.00029, Lemma lem:blocking-arbitrary, lines 434--451. -/
theorem exists_aligned_hamiltonian_chainTranslates_gap_of_periodic_family
    (μ : Fin r → ℂ) (A : ∀ j, MPSTensor d (dim j)) (hμ : ∀ j, μ j ≠ 0)
    (m : Fin r → ℕ) (hPeriodic : ∀ j, IsPeriodic (m j) (A j))
    (h : Matrix (Cfg d R) (Cfg d R) ℂ) (hh : h.PosSemidef)
    (hker : ∀ᶠ n in Filter.atTop,
      LinearMap.ker (Matrix.toEuclideanLin (chainTranslates R n h).hamiltonian) =
        groundSpaceES (toTensorFromBlocks μ A) n) :
    ∃ L : ℕ, 0 < L ∧ ∃ γ : ℝ, 0 < γ ∧ ∀ N,
      ∀ z : ℂ, Module.End.HasEigenvalue
        (Matrix.toEuclideanLin ((chainTranslates R (N * L) h).hamiltonian)) z →
          z = 0 ∨ (γ : ℂ) ≤ z := by
  have hL : 0 < ∏ j, m j := Finset.prod_pos fun j _ => (hPeriodic j).period_pos
  exact ⟨∏ j, m j, hL,
    exists_aligned_hamiltonian_chainTranslates_gap_of_periodic_family_of_dvd
      μ A hμ m hPeriodic _ hL (fun j => Finset.dvd_prod_of_mem m (Finset.mem_univ j))
      h hh hker⟩
end MPSTensor

end PeriodicBlockFamilyGap

section PhysicalResidualCoverLimit

/-!
## Physical residual covers from a primitive-sector resolution

A supplied isometric resolution of a blocked tensor identifies the joint
right, left, and full residual windows with the original physical interval
spaces. Primitive faithful inequivalent sectors, together with exact
orthogonal tail Gram matrices, give vanishing projection defects in the
original physical coordinates. The product order is reversed by taking
adjoints, so no commutativity of the interval projections is assumed.

The second result is an auxiliary finite-gap criterion. It retains exact
canonical kernels and an eventual aligned gap as explicit hypotheses; the
sector-resolution assumptions then extend the gap to all original volumes,
above the actual kernel at each volume. No periodicity of the original
tensor is required by either result.

Source: Nachtergaele, arXiv:cond-mat/9410110, Section 6,
Lemma commutation (ii), lines 2442--2531, and equations (3.12)--(3.16).
-/

open scoped Matrix BigOperators ComplexOrder
open Kraus (blockPhysDim blockTensor)
namespace MPSTensor
variable {d D L : ℕ}

/-- A primitive, faithful, inequivalent isometric resolution of a blocked tensor,
with exact orthogonal correlated-tail Gram matrices, gives vanishing original
physical cover defects as the common overlap diverges. Both exterior lengths
may vary arbitrarily. Source: Nachtergaele, arXiv:cond-mat/9410110,
Lemma commutation (ii), lines 2442--2531. The sector and Gram assumptions
are supplied explicitly; no periodicity of the original tensor is required. -/
theorem residual_cover_projection_defect_tendsto_zero_of_primitive_resolution
    [NeZero D] {ι : Type*} [Fintype ι] {dim : ι → ℕ} [∀ j, NeZero (dim j)]
    (A : MPSTensor d D) (B : ∀ j, MPSTensor (blockPhysDim d L) (dim j))
    (V : ∀ j, Matrix (Fin D) (Fin (dim j)) ℂ)
    (ρ : ∀ j, Matrix (Fin (dim j)) (Fin (dim j)) ℂ)
    (hP : ∀ j, Kraus.HasComplementaryFixedPointGap (B j) (ρ j)) (hρ : ∀ j, (ρ j).PosDef)
    (hDistinct : ∀ i j, i ≠ j → ∀ e : dim j = dim i, ¬ GaugePhaseEquiv (e ▸ B j) (B i))
    (hV : ∀ j, (V j)ᴴ * V j = 1) (hSum : ∑ j, V j * (V j)ᴴ = 1)
    (hInt : ∀ j i, blockTensor A L i * V j = V j * B j i)
    (hCoInt : ∀ j i, (V j)ᴴ * blockTensor A L i = B j i * (V j)ᴴ)
    (Q : ι → ℕ → Matrix (Fin D) (Fin D) ℂ)
    (hQ : ∀ j r, IsOrthogonalProjection (Q j r))
    (hGram : ∀ j r, (∑ τ : Cfg d r, (Kraus.evalWord A (List.ofFn τ))ᴴ *
      (V j * (V j)ᴴ) * Kraus.evalWord A (List.ofFn τ) : Matrix (Fin D) (Fin D) ℂ) = Q j r)
    {κ : Type*} {f : Filter κ} {K M r : κ → ℕ} (hM : Filter.Tendsto M f Filter.atTop) :
    Filter.Tendsto (fun n =>
      ‖(groundSpaceES A (K n * L + M n * L + r n)).starProjection -
        (leftBoundaryMapES A (K n * L + M n * L) (r n)).range.starProjection.comp
          (reassocTailBoundaryMapES A (K n * L) (M n * L) (r n)).range.starProjection‖)
      f (nhds 0) := by
  have hJoint := tendsto_norm_residualWindow_joint_projection_comp_sub_zero
    A B V ρ hP hρ hDistinct Q hQ hGram (K := K) (r := r) hM
  have hNorm (n : κ) :
      ‖(⨆ j,
          (residualWindowRightMapES A (B j) (V j) (K n) (M n) (r n)).range).starProjection.comp
          (⨆ j, (residualWindowLeftMapES (B j) (K n) (M n) (r n)).range).starProjection -
        (⨆ j, (residualWindowMapES A (B j) (V j) (K n) (M n) (r n)).range).starProjection‖ =
      ‖(groundSpaceES A (K n * L + M n * L + r n)).starProjection -
        (leftBoundaryMapES A (K n * L + M n * L) (r n)).range.starProjection.comp
          (reassocTailBoundaryMapES A (K n * L) (M n * L) (r n)).range.starProjection‖ := by
    simp only [iSup_range_residualWindowRightMapES_eq_reindex_reassocTailBoundaryMapES
      A B V hSum hCoInt,
      iSup_range_residualWindowLeftMapES_eq_reindex_cover_leftBoundaryMapES
        A B V hV hSum hInt,
      iSup_range_residualWindowMapES_eq_reindex_groundSpaceES_cover A B V hSum hCoInt]
    exact Submodule.norm_map_starProjection_comp_sub_eq _ _ _ _
  simpa only [hNorm] using hJoint

/-- Exact canonical kernels and an eventual aligned gap extend to all original
volumes under the supplied primitive-sector resolution and correlated-tail
Gram hypotheses. The gap is measured above the actual kernel, including
short volumes. Source: Nachtergaele, arXiv:cond-mat/9410110, Section 6,
Lemma commutation (ii). This is an auxiliary criterion with explicit
algebraic, kernel, and aligned-gap assumptions. -/
theorem exists_pos_hamiltonian_parentChainInteraction_gap_of_aligned_gap_of_primitive_resolution
    [NeZero D] {ι : Type*} [Fintype ι] {dim : ι → ℕ} [∀ j, NeZero (dim j)]
    (A : MPSTensor d D) (B : ∀ j, MPSTensor (blockPhysDim d L) (dim j))
    (V : ∀ j, Matrix (Fin D) (Fin (dim j)) ℂ)
    (ρ : ∀ j, Matrix (Fin (dim j)) (Fin (dim j)) ℂ)
    (hP : ∀ j, Kraus.HasComplementaryFixedPointGap (B j) (ρ j)) (hρ : ∀ j, (ρ j).PosDef)
    (hDistinct : ∀ i j, i ≠ j → ∀ e : dim j = dim i, ¬ GaugePhaseEquiv (e ▸ B j) (B i))
    (hV : ∀ j, (V j)ᴴ * V j = 1) (hSum : ∑ j, V j * (V j)ᴴ = 1)
    (hInt : ∀ j i, blockTensor A L i * V j = V j * B j i)
    (hCoInt : ∀ j i, (V j)ᴴ * blockTensor A L i = B j i * (V j)ᴴ)
    (Q : ι → ℕ → Matrix (Fin D) (Fin D) ℂ)
    (hQ : ∀ j r, IsOrthogonalProjection (Q j r))
    (hGram : ∀ j r, (∑ τ : Cfg d r, (Kraus.evalWord A (List.ofFn τ))ᴴ *
      (V j * (V j)ᴴ) * Kraus.evalWord A (List.ofFn τ) : Matrix (Fin D) (Fin D) ℂ) = Q j r)
    {R N₀ : ℕ} (hR : 0 < R) (hL : 0 < L)
    (hKernel : ∀ N, R ≤ N →
      LinearMap.ker (Matrix.toEuclideanLin (parentChainInteraction A R N).hamiltonian) =
          groundSpaceES A N)
    {γ : ℝ} (hγ : 0 < γ)
    (hAligned : ∀ n ≥ N₀, ∀ μ : ℂ, Module.End.HasEigenvalue
      (Matrix.toEuclideanLin (parentChainInteraction A R (n * L)).hamiltonian) μ →
        μ = 0 ∨ (γ : ℂ) ≤ μ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ N,
      ∀ μ : ℂ, Module.End.HasEigenvalue
        (Matrix.toEuclideanLin (parentChainInteraction A R N).hamiltonian) μ →
          μ = 0 ∨ (δ : ℂ) ≤ μ :=
  exists_pos_hamiltonian_parentChainInteraction_gap_of_aligned_gap_of_residue_cover_limit
    A hR hL hKernel hγ hAligned (fun K r =>
      residual_cover_projection_defect_tendsto_zero_of_primitive_resolution
        A B V ρ hP hρ hDistinct hV hSum hInt hCoInt Q hQ hGram
        (K := K) (r := r) Filter.tendsto_id)

end MPSTensor

end PhysicalResidualCoverLimit

section PeriodicBlockFamilyOpenParentGap

section

open Filter SpinChain
open scoped Matrix MatrixOrder ComplexOrder BigOperators InnerProductSpace Topology
open ManyBody.Interaction (chainTranslates)

namespace MPSTensor
variable {d b R : ℕ} [NeZero d] {D : Fin b → ℕ}

private theorem exists_aligned_canonical_gap_of_periodic_family
    (A : ∀ j, MPSTensor d (D j)) (m : Fin b → ℕ)
    (hPeriodic : ∀ j, IsPeriodic (m j) (A j))
    (hKernel : ∀ N, R ≤ N →
      LinearMap.ker
          (Matrix.toEuclideanLin
              (parentChainInteraction (toTensorFromBlocks (fun _ => 1) A) R N).hamiltonian) =
        groundSpaceES (toTensorFromBlocks (fun _ => 1) A) N)
    (L : ℕ) (hL : 0 < L) (hdiv : ∀ j, m j ∣ L) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ n, ∀ z : ℂ, Module.End.HasEigenvalue
      (Matrix.toEuclideanLin
          (parentChainInteraction (toTensorFromBlocks (fun _ => 1) A) R (n * L)).hamiltonian) z →
        z = 0 ∨ (γ : ℂ) ≤ z := by
  let T := toTensorFromBlocks (fun _ => 1) A
  have hEventual : ∀ᶠ N in atTop,
      LinearMap.ker (Matrix.toEuclideanLin (parentChainInteraction T R N).hamiltonian) =
        groundSpaceES T N := by
    filter_upwards [eventually_ge_atTop R] with N hN using hKernel N hN
  exact exists_aligned_hamiltonian_chainTranslates_gap_of_periodic_family_of_dvd
    (fun _ => 1) A (fun _ => one_ne_zero) m hPeriodic L hL hdiv
    (LinearMap.toMatrix' (parentInteraction T R))
    (posSemidef_toMatrix'_parentInteraction T R) hEventual

private theorem exists_canonical_gap_of_empty_periodic_family {D : Fin 0 → ℕ}
    (A : ∀ j : Fin 0, MPSTensor d (D j))
    (m : Fin 0 → ℕ) (hPeriodic : ∀ j, IsPeriodic (m j) (A j))
    (hKernel : ∀ N, R ≤ N →
      LinearMap.ker
          (Matrix.toEuclideanLin
              (parentChainInteraction (toTensorFromBlocks (fun _ => 1) A) R N).hamiltonian) =
        groundSpaceES (toTensorFromBlocks (fun _ => 1) A) N) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ N, ∀ z : ℂ, Module.End.HasEigenvalue
      (Matrix.toEuclideanLin
          (parentChainInteraction (toTensorFromBlocks (fun _ => 1) A) R N).hamiltonian) z →
        z = 0 ∨ (δ : ℂ) ≤ z := by
  obtain ⟨γ, hγ, hGap⟩ := exists_aligned_canonical_gap_of_periodic_family
    A m hPeriodic hKernel 1 zero_lt_one (fun j => Fin.elim0 j)
  let P (N : ℕ) : Prop := ∀ z : ℂ, Module.End.HasEigenvalue
    (Matrix.toEuclideanLin
        (parentChainInteraction (toTensorFromBlocks (fun _ => 1) A) R N).hamiltonian) z →
      z = 0 ∨ (γ : ℂ) ≤ z
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
      LinearMap.ker
          (Matrix.toEuclideanLin
              (parentChainInteraction (toTensorFromBlocks (fun _ => 1) A) R N).hamiltonian) =
        groundSpaceES (toTensorFromBlocks (fun _ => 1) A) N) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ N, ∀ z : ℂ, Module.End.HasEigenvalue
      (Matrix.toEuclideanLin
          (parentChainInteraction (toTensorFromBlocks (fun _ => 1) A) R N).hamiltonian) z →
        z = 0 ∨ (δ : ℂ) ≤ z := by
  classical
  by_cases hb : b = 0
  · subst b
    exact exists_canonical_gap_of_empty_periodic_family A m hPeriodic hKernel
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
    A m hPeriodic hKernel L hL hdiv
  exact exists_pos_hamiltonian_parentChainInteraction_gap_of_aligned_gap_of_primitive_resolution
    (N₀ := R) (toTensorFromBlocks (fun _ => 1) A) B V ρ hP hρ hSep
    hV hSum hInt hCoInt Q hQ hGram hR hL hKernel hγ (fun n _ => hAligned n)

/-- A finite weighted family of normalized periodic tensors has exact canonical
open kernels and a positive gap at every original volume, for every sufficiently
large interaction range. The norm bound is above each volume's actual kernel.
Source: Nachtergaele, arXiv:cond-mat/9410110, Theorem 1.2, Section 4,
Lemma existenceinteraction, and Section 6, Lemma commutation (ii). -/
theorem exists_hamiltonian_parentChainInteraction_gap_of_periodic_family
    (μ : Fin b → ℂ) (A : ∀ j, MPSTensor d (D j)) (hμ : ∀ j, μ j ≠ 0)
    (m : Fin b → ℕ) (hPeriodic : ∀ j, IsPeriodic (m j) (A j)) :
    ∃ R₀, 0 < R₀ ∧ ∀ R, R₀ ≤ R →
      (∀ N, R ≤ N →
        LinearMap.ker
            (Matrix.toEuclideanLin
                (parentChainInteraction (toTensorFromBlocks μ A) R N).hamiltonian) =
          groundSpaceES (toTensorFromBlocks μ A) N) ∧
      ∃ δ : ℝ, 0 < δ ∧ ∀ N, ∀ z : ℂ, Module.End.HasEigenvalue
        (Matrix.toEuclideanLin
            (parentChainInteraction (toTensorFromBlocks μ A) R N).hamiltonian) z →
          z = 0 ∨ (δ : ℂ) ≤ z := by
  obtain ⟨g, sel, hsel, hD, hP, hDistinct, hCover, hJoint⟩ :=
    exists_periodic_sector_representatives μ A hμ hPeriodic
  let B := fun j => A (sel j)
  obtain ⟨R₀, hR₀, hKernel⟩ := exists_ker_hamiltonian_parentChainInteraction_of_periodic_family
    μ A hμ m hPeriodic
  refine ⟨R₀, hR₀, ?_⟩
  intro R hRR
  have hR : 0 < R := hR₀.trans_le hRR
  have hEq (N : ℕ) := hamiltonian_parentChainInteraction_eq_of_groundSpaceES_eq (hJoint R) N
  have hKernelB (N : ℕ) (hRN : R ≤ N) :
      LinearMap.ker
          (Matrix.toEuclideanLin
              (parentChainInteraction (toTensorFromBlocks (fun _ => 1) B) R N).hamiltonian) =
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
Lemma existenceinteraction, and Section 6, Lemma commutation (ii). -/
theorem exists_positive_parent_interaction_finite_quasiLocal_gap_of_periodic_family
    (μ : Fin b → ℂ) (A : ∀ j, MPSTensor d (D j)) (hμ : ∀ j, μ j ≠ 0)
    (m : Fin b → ℕ) (hPeriodic : ∀ j, IsPeriodic (m j) (A j)) :
    ∃ R : ℕ, 0 < R ∧ ∃ h : Matrix (Cfg d R) (Cfg d R) ℂ,
      h = LinearMap.toMatrix' (parentInteraction (toTensorFromBlocks μ A) R) ∧ h.PosSemidef ∧
      (∀ N : ℕ, R ≤ N →
        LinearMap.ker (Matrix.toEuclideanLin (chainTranslates R N h).hamiltonian) =
          groundSpaceES (toTensorFromBlocks μ A) N) ∧
    ∃ δ : ℝ, 0 < δ ∧
      (∀ N, ∀ z : ℂ, Module.End.HasEigenvalue
        (Matrix.toEuclideanLin ((chainTranslates R N h).hamiltonian)) z →
          z = 0 ∨ (δ : ℂ) ≤ z) ∧
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
                  ((chainTranslates R ((ℓ n + k) + r n) h).hamiltonian) *
                quasiLocalIntervalObservable d a k X -
                quasiLocalIntervalObservable d a k X *
                  quasiLocalIntervalObservable d (a - (ℓ n : ℤ)) ((ℓ n + k) + r n)
                    ((chainTranslates R ((ℓ n + k) + r n) h).hamiltonian)))) f (𝓝 e) ∧
            (γ : ℂ) * φ (star (quasiLocalIntervalObservable d a k X) *
              quasiLocalIntervalObservable d a k X) ≤ e := by
  obtain ⟨R, hR, hAll⟩ := exists_hamiltonian_parentChainInteraction_gap_of_periodic_family
    μ A hμ m hPeriodic
  obtain ⟨hKernelCanonical, δ, hδ, hGapCanonical⟩ := hAll R le_rfl
  obtain ⟨h, heq, hh, hKernel⟩ :=
    exists_posSemidef_eq_toMatrix'_parentInteraction_of_ker_hamiltonian_parentChainInteraction
      (toTensorFromBlocks μ A) hKernelCanonical
  have hGapMatrix (N : ℕ) : ∀ z : ℂ, Module.End.HasEigenvalue
    (Matrix.toEuclideanLin ((chainTranslates R N h).hamiltonian)) z →
      z = 0 ∨ (δ : ℂ) ≤ z := by
    rw [heq]
    exact hGapCanonical N
  have hEventual := (eventually_ge_atTop R).mono fun N hN => hKernel N hN
  obtain ⟨γ, hγ, hGap⟩ := exists_pos_quasiLocalCommutator_limit_gap_of_periodic_family
    μ A hμ m hPeriodic h hR hh hEventual
  exact ⟨R, hR, h, heq, hh, hKernel, δ, hδ, hGapMatrix, γ, hγ, hGap⟩

end MPSTensor

end

section

open Filter SpinChain
open scoped Matrix MatrixOrder ComplexOrder BigOperators Topology
open ManyBody.Interaction (chainTranslates)

namespace MPSTensor
variable {d b R : ℕ} [NeZero d] {D : Fin b → ℕ}

/-- Every positive finite-range interaction with eventual joint open kernels
for a finite periodic family has a uniform gap at every original volume,
above the actual finite-volume kernel. No local parent-kernel identity or
interaction-range lower bound is required. Source: Nachtergaele,
arXiv:cond-mat/9410110, Theorem 1.2, lines 933--947, condition C1,
and Section 6, lines 2593--2675. -/
theorem exists_hamiltonian_chainTranslates_gap_of_periodic_family_of_eventual_kernel
    (μ : Fin b → ℂ) (A : ∀ j, MPSTensor d (D j)) (hμ : ∀ j, μ j ≠ 0)
    (m : Fin b → ℕ) (hPeriodic : ∀ j, IsPeriodic (m j) (A j))
    (h : Matrix (Cfg d R) (Cfg d R) ℂ) (hh : h.PosSemidef)
    (hKernel : ∀ᶠ N in atTop,
      LinearMap.ker (Matrix.toEuclideanLin (chainTranslates R N h).hamiltonian) =
        groundSpaceES (toTensorFromBlocks μ A) N) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ N,
      ∀ z : ℂ, Module.End.HasEigenvalue
        (Matrix.toEuclideanLin ((chainTranslates R N h).hamiltonian)) z →
          z = 0 ∨ (δ : ℂ) ≤ z := by
  obtain ⟨R₀, hR₀, hCanonical⟩ := exists_hamiltonian_parentChainInteraction_gap_of_periodic_family
    μ A hμ m hPeriodic
  exact exists_toEuclideanLin_hamiltonian_chainTranslates_gap_of_canonical_gaps_of_eventual_kernel
    (toTensorFromBlocks μ A) hR₀ hCanonical h hh hKernel

/-- One supplied positive interaction with eventual periodic-family open
kernels has both an all-length finite gap and a common literal infinite-volume
commutator gap for every pure zero-energy state. The constants precede all
states, observables, filters, and divergent margins. Source: Nachtergaele,
arXiv:cond-mat/9410110, Theorems 1.1--1.2 and Section 6, lines 2593--2675. -/
theorem exists_finite_quasiLocal_gap_of_periodic_family_of_eventual_kernel
    (μ : Fin b → ℂ) (A : ∀ j, MPSTensor d (D j)) (hμ : ∀ j, μ j ≠ 0)
    (m : Fin b → ℕ) (hPeriodic : ∀ j, IsPeriodic (m j) (A j))
    (h : Matrix (Cfg d R) (Cfg d R) ℂ) (hR : 0 < R) (hh : h.PosSemidef)
    (hKernel : ∀ᶠ N in atTop,
      LinearMap.ker (Matrix.toEuclideanLin (chainTranslates R N h).hamiltonian) =
        groundSpaceES (toTensorFromBlocks μ A) N) :
    ∃ δ : ℝ, 0 < δ ∧
      (∀ N, ∀ z : ℂ, Module.End.HasEigenvalue
        (Matrix.toEuclideanLin ((chainTranslates R N h).hamiltonian)) z →
          z = 0 ∨ (δ : ℂ) ≤ z) ∧
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
                  ((chainTranslates R ((ℓ n + k) + r n) h).hamiltonian) *
                quasiLocalIntervalObservable d a k X -
                quasiLocalIntervalObservable d a k X *
                  quasiLocalIntervalObservable d (a - (ℓ n : ℤ)) ((ℓ n + k) + r n)
                    ((chainTranslates R ((ℓ n + k) + r n) h).hamiltonian)))) f (𝓝 e) ∧
            (γ : ℂ) * φ (star (quasiLocalIntervalObservable d a k X) *
              quasiLocalIntervalObservable d a k X) ≤ e := by
  obtain ⟨δ, hδ, hFinite⟩ :=
    exists_hamiltonian_chainTranslates_gap_of_periodic_family_of_eventual_kernel
      μ A hμ m hPeriodic h hh hKernel
  obtain ⟨γ, hγ, hInfinite⟩ := exists_pos_quasiLocalCommutator_limit_gap_of_periodic_family
    μ A hμ m hPeriodic h hR hh hKernel
  exact ⟨δ, hδ, hFinite, γ, hγ, hInfinite⟩

end MPSTensor

end

end PeriodicBlockFamilyOpenParentGap
