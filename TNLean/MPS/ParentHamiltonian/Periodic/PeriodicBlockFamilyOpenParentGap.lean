/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.Periodic.PeriodicBlockFamilyParentInteractionGap
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
import QICLean.Kraus.PrimitiveFixedPoint.Blocking
import TNLean.MPS.Transfer.Irreducible.PhysicalReindexTransport
import TNLean.MPS.ParentHamiltonian.BlockGroundSpace.Sector.PeriodicGroundSpaceIndependence
import TNLean.MPS.ParentHamiltonian.BlockGroundSpace.Sector.ResidualBoundaryGram
import TNLean.MPS.Tensor.DirectSum.BlockAssembly
import TNLean.MPS.CanonicalForm.NormalBlocks.Blocking

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
* `residual_cover_projection_defect_tendsto_zero_of_primitive_resolution`,
  `exists_pos_hamiltonian_parentChainInteraction_gap_of_aligned_gap_of_primitive_resolution`
  (in `MPSTensor`): physical residual covers from a primitive-sector resolution.
* `MPSTensor.IsPeriodic.exists_powered_cyclic_primitive_sector_resolution`,
  `MPSTensor.exists_commonBlock_primitive_sector_resolution_of_isPeriodic`: primitive
  sector resolutions of periodic tensors at a common blocking length, from
  `Kraus.HasComplementaryFixedPointGap.blockTensor` and `.reindexPhysical`.
-/

open MPTensor

section PoweredCyclicPrimitiveResolution

/-!
## Literal cyclic sectors at a common blocking length

A positive multiple of the period preserves the cyclic support projections
and their isometries. The primitive tensors on these supports are powered,
with the stationary matrices unchanged. Their separation follows from the
original-chain boundary-space angle estimate, rather than from an assumption
that inequivalence survives blocking.

Source: arXiv:1708.00029, Lemma bdcf and Lemma lem:blocking-arbitrary;
Nachtergaele, arXiv:cond-mat/9410110, Section 6, lines 2649--2675.

### A common-block primitive resolution of a periodic family

A finite family of pairwise inequivalent normalized periodic tensors admits
an isometric primitive resolution at every positive common multiple of the
periods. The isometries live in the original unit-weight direct sum and
retain both letter intertwiners. The correlated-tail Gram matrices are
embedded shifted cyclic projections, derived for every tail length.

Within each original tensor, separation is proved after powering its
minimum-period primitive sectors. Between different original tensors,
separation follows from their original-chain boundary-space angle decay.
Thus no inequivalence assumption on compressed or powered corners is added.
The finite index may be empty; no positive ambient dimension is assumed.

Source: arXiv:1708.00029, Lemma bdcf and equation Aoffdiag;
Nachtergaele, arXiv:cond-mat/9410110, Lemma commutation (ii),
lines 2442--2531, and Section 6, lines 2649--2675.
-/

section

open scoped Matrix BigOperators InnerProductSpace ComplexOrder
open Filter
open Kraus (blockPhysDim blockTensor)
namespace MPSTensor
variable {d D m : ℕ}

private theorem powered_cyclic_intertwine
    {E : ℕ} (A : MPSTensor d D) (B : MPSTensor (blockPhysDim d m) E)
    (V : Matrix (Fin D) (Fin E) ℂ)
    (hInt : ∀ i, blockTensor A m i * V = V * B i) (q : ℕ)
    (i : Fin (blockPhysDim d (m * q))) :
    blockTensor A (m * q) i * V =
      V * Kraus.reindexPhysical (directIteratedBlockEquiv d m q) (blockTensor B q) i := by
  let e := directIteratedBlockEquiv d m q
  have h := Kraus.evalWord_intertwine (blockTensor A m) B V hInt
    (Kraus.wordOfBlock (blockPhysDim d m) q (e i))
  change blockTensor (blockTensor A m) q (e i) * V = V * blockTensor B q (e i) at h
  rw [blockTensor_blockTensor_apply] at h
  have he : iteratedBlockIndex d m q (e i) = i := e.symm_apply_apply i
  simpa only [he, Kraus.reindexPhysical, e] using h

private theorem powered_cyclic_cointertwine
    {E : ℕ} (A : MPSTensor d D) (B : MPSTensor (blockPhysDim d m) E)
    (V : Matrix (Fin D) (Fin E) ℂ)
    (hInt : ∀ i, Vᴴ * blockTensor A m i = B i * Vᴴ) (q : ℕ)
    (i : Fin (blockPhysDim d (m * q))) :
    Vᴴ * blockTensor A (m * q) i =
      Kraus.reindexPhysical (directIteratedBlockEquiv d m q) (blockTensor B q) i * Vᴴ := by
  let e := directIteratedBlockEquiv d m q
  have h := Kraus.evalWord_intertwine B (blockTensor A m) Vᴴ (fun i => (hInt i).symm)
    (Kraus.wordOfBlock (blockPhysDim d m) q (e i))
  change blockTensor B q (e i) * Vᴴ = Vᴴ * blockTensor (blockTensor A m) q (e i) at h
  rw [blockTensor_blockTensor_apply] at h
  have he : iteratedBlockIndex d m q (e i) = i := e.symm_apply_apply i
  simpa only [he, Kraus.reindexPhysical, e] using h.symm

/-- A common positive multiple of the period retains the literal cyclic
isometries and gives pairwise inequivalent primitive sectors with the same
faithful stationary matrices. The correlated tail Gram projections are
derived for every tail length. Source: arXiv:1708.00029, Lemma bdcf and
Lemma lem:blocking-arbitrary; Nachtergaele, arXiv:cond-mat/9410110,
Lemma commutation (ii), lines 2442--2531, and Section 6. -/
theorem IsPeriodic.exists_powered_cyclic_primitive_sector_resolution
    {A : MPSTensor d D} (hA : IsPeriodic m A) (L : ℕ)
    (hL : 0 < L) (hdiv : m ∣ L) :
    let _ : NeZero m := ⟨Nat.ne_of_gt hA.period_pos⟩
    ∃ (dim : Fin m → ℕ) (hdim : ∀ j, 0 < dim j),
      let _ : ∀ j, NeZero (dim j) := fun j => ⟨Nat.ne_of_gt (hdim j)⟩
      ∃ (B : (j : Fin m) → MPSTensor (blockPhysDim d L) (dim j))
        (P : Fin m → Matrix (Fin D) (Fin D) ℂ)
        (V : (j : Fin m) → Matrix (Fin D) (Fin (dim j)) ℂ)
        (ρ : (j : Fin m) → Matrix (Fin (dim j)) (Fin (dim j)) ℂ),
        (∀ j, Kraus.HasComplementaryFixedPointGap (B j) (ρ j)) ∧ (∀ j, (ρ j).PosDef) ∧
        BlocksNotGaugePhaseEquiv B ∧
        (∀ j, IsOrthogonalProjection (P j)) ∧ (∑ j, P j) = 1 ∧
        (∀ j i, P (j + 1) * A i = A i * P j) ∧
        (∀ j, (V j)ᴴ * V j = 1) ∧ (∀ j, V j * (V j)ᴴ = P j) ∧
        (∀ j i, blockTensor A L i * V j = V j * B j i) ∧
        (∀ j i, (V j)ᴴ * blockTensor A L i = B j i * (V j)ᴴ) ∧
        (∀ j r, (∑ τ : Cfg d r, (Kraus.evalWord A (List.ofFn τ))ᴴ * P j *
          Kraus.evalWord A (List.ofFn τ)) = P (j - r • (1 : Fin m))) := by
  classical
  obtain ⟨q, rfl⟩ := hdiv
  have hq : 0 < q := Nat.pos_of_mul_pos_left hL
  let : NeZero m := ⟨Nat.ne_of_gt hA.period_pos⟩
  obtain ⟨dim, hdim, B, P, V, ρ, hP, hρ, hDistinct, hProj, hSum, hShift, hIso, hV,
    hInt, hCoInt⟩ := hA.exists_cyclic_primitive_sector_resolution
  let : ∀ j, NeZero (dim j) := fun j => ⟨Nat.ne_of_gt (hdim j)⟩
  let C : (j : Fin m) → MPSTensor (blockPhysDim d (m * q)) (dim j) := fun j =>
    Kraus.reindexPhysical (directIteratedBlockEquiv d m q) (blockTensor (B j) q)
  have hC (j : Fin m) : Kraus.HasComplementaryFixedPointGap (C j) (ρ j) :=
    ((hP j).blockTensor (hρ j) hq).reindexPhysical (directIteratedBlockEquiv d m q)
  have hOne (j : Fin m) : IsPeriodic 1 (B j) :=
    (IsPeriodic.one_iff_primitive (B j)).2
      ⟨(hP j).isIrreducibleFamily_of_posDef (hρ j), (hP j).norm, (hP j).isPrimitive⟩
  have hSep : BlocksNotGaugePhaseEquiv C := by
    intro j k hjk e hGauge
    have hRaw : GaugePhaseEquiv
        (Kraus.reindexPhysical (directIteratedBlockEquiv d m q)
          (cast (congrArg (MPSTensor (blockPhysDim (blockPhysDim d m) q)) e)
            (blockTensor (B j) q)))
        (Kraus.reindexPhysical (directIteratedBlockEquiv d m q) (blockTensor (B k) q)) := by
      rw [reindexPhysical_cast_dim (directIteratedBlockEquiv d m q) e (blockTensor (B j) q)]
      exact hGauge
    have hBlocked := (gaugePhaseEquiv_reindexPhysical_equiv
      (directIteratedBlockEquiv d m q) _ _).mp hRaw
    have hSepOriginal : ∀ e' : dim j = dim k, ¬ GaugePhaseEquiv (e' ▸ B j) (B k) := by
      intro e' h
      exact hDistinct j k hjk e' (by simpa only [eqRec_eq_cast] using h)
    have hNo := (hOne k).not_gaugePhaseEquiv_of_primitive_corners (hOne j)
      hSepOriginal hq (blockTensor (B k) q) (blockTensor (B j) q) 1 1
      ((hP k).blockTensor (hρ k) hq) (hρ k) (by simp) (by simp)
      (fun i => by simp) (fun i => by simp) e
    exact hNo (by simpa only [eqRec_eq_cast] using hBlocked)
  exact ⟨dim, hdim, C, P, V, ρ, hC, hρ, hSep, hProj, hSum, hShift, hIso, hV,
    (fun j i => powered_cyclic_intertwine A (B j) (V j) (hInt j) q i),
    (fun j i => powered_cyclic_cointertwine A (B j) (V j) (hCoInt j) q i),
    (fun j r => sum_word_conjTranspose_inverseCyclic_projection_mul_word
      A P hA.leftCanonical hShift j r)⟩

end MPSTensor

end

section

open scoped Matrix BigOperators ComplexOrder
open Kraus (blockPhysDim blockTensor)
namespace MPSTensor
variable {d D : ℕ}

private theorem embedded_word_gram
    {E : ℕ} (A : MPSTensor d D) (B : MPSTensor d E)
    (J : Matrix (Fin D) (Fin E) ℂ) (P : Matrix (Fin E) (Fin E) ℂ)
    (hCo : ∀ i, Jᴴ * A i = B i * Jᴴ) (r : ℕ) :
    (∑ τ : Cfg d r, (Kraus.evalWord A (List.ofFn τ))ᴴ *
      (J * P * Jᴴ) * Kraus.evalWord A (List.ofFn τ)) =
      J * (∑ τ : Cfg d r, (Kraus.evalWord B (List.ofFn τ))ᴴ * P *
        Kraus.evalWord B (List.ofFn τ)) * Jᴴ := by
  classical
  rw [Matrix.mul_sum, Matrix.sum_mul]
  refine Finset.sum_congr rfl (fun τ _ => ?_)
  have hWord := (Kraus.evalWord_intertwine B A Jᴴ (fun i => (hCo i).symm)
    (List.ofFn τ)).symm
  have hAdj := congrArg Matrix.conjTranspose hWord
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose] at hAdj
  calc
    _ = ((Kraus.evalWord A (List.ofFn τ))ᴴ * J) * P *
        (Jᴴ * Kraus.evalWord A (List.ofFn τ)) := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hAdj, hWord]; simp only [Matrix.mul_assoc]

/-- A finite pairwise gauge-phase inequivalent normalized periodic family
has a literal primitive sector resolution at every common positive multiple
of its periods. The global isometries resolve the unit-weight direct sum,
retain both block intertwiners, and give orthogonal correlated-tail Gram
matrices for every tail length. No separation assumption on the blocked
corners is supplied. Source: arXiv:1708.00029, Lemma bdcf and equation
Aoffdiag; Nachtergaele, arXiv:cond-mat/9410110, Lemma commutation (ii),
lines 2442--2531, and Section 6, lines 2649--2675. -/
theorem exists_commonBlock_primitive_sector_resolution_of_isPeriodic
    {r : ℕ} {dim : Fin r → ℕ} (A : ∀ j, MPSTensor d (dim j))
    (m : Fin r → ℕ) (hPeriodic : ∀ j, IsPeriodic (m j) (A j))
    (hDistinct : BlocksNotGaugePhaseEquiv A) (L : ℕ) (hL : 0 < L)
    (hdiv : ∀ j, m j ∣ L) :
    ∃ (sdim : (j : Fin r) × Fin (m j) → ℕ) (hsdim : ∀ s, 0 < sdim s),
      let _ : ∀ s, NeZero (sdim s) := fun s => ⟨Nat.ne_of_gt (hsdim s)⟩
      ∃ (B : ∀ s, MPSTensor (blockPhysDim d L) (sdim s))
        (V : ∀ s, Matrix (Fin (∑ j, dim j)) (Fin (sdim s)) ℂ)
        (ρ : ∀ s, Matrix (Fin (sdim s)) (Fin (sdim s)) ℂ),
        (∀ s, Kraus.HasComplementaryFixedPointGap (B s) (ρ s)) ∧ (∀ s, (ρ s).PosDef) ∧
        (∀ s t, s ≠ t → ∀ e : sdim t = sdim s, ¬ GaugePhaseEquiv (e ▸ B t) (B s)) ∧
        (∀ s, (V s)ᴴ * V s = 1) ∧ (∑ s, V s * (V s)ᴴ) = 1 ∧
        (∀ s i, blockTensor (toTensorFromBlocks (fun _ => 1) A) L i * V s = V s * B s i) ∧
        (∀ s i, (V s)ᴴ * blockTensor (toTensorFromBlocks (fun _ => 1) A) L i = B s i * (V s)ᴴ) ∧
        ∃ Q : ((j : Fin r) × Fin (m j)) → ℕ → Matrix (Fin (∑ j, dim j)) (Fin (∑ j, dim j)) ℂ,
          (∀ s t, IsOrthogonalProjection (Q s t)) ∧
          (∀ s t, (∑ τ : Cfg d t,
            (Kraus.evalWord (toTensorFromBlocks (fun _ => 1) A) (List.ofFn τ))ᴴ *
            (V s * (V s)ᴴ) *
            Kraus.evalWord (toTensorFromBlocks (fun _ => 1) A) (List.ofFn τ)) = Q s t) := by
  classical
  let : ∀ j, NeZero (m j) := fun j => ⟨Nat.ne_of_gt (hPeriodic j).period_pos⟩
  choose edim hedim C P W ρ hP hρ hSep hProj hSum hShift hIso hV hInt hCoInt hGram using
    fun j => (hPeriodic j).exists_powered_cyclic_primitive_sector_resolution L hL (hdiv j)
  let : ∀ j k, NeZero (edim j k) := fun j k => ⟨Nat.ne_of_gt (hedim j k)⟩
  let sdim : (j : Fin r) × Fin (m j) → ℕ := fun s => edim s.1 s.2
  let B : ∀ s, MPSTensor (blockPhysDim d L) (sdim s) := fun s => C s.1 s.2
  let V : ∀ s, Matrix (Fin (∑ j, dim j)) (Fin (sdim s)) ℂ :=
    fun s => blockInclusion dim s.1 * W s.1 s.2
  have hBsep : ∀ s t, s ≠ t → ∀ e : sdim t = sdim s,
      ¬ GaugePhaseEquiv (e ▸ B t) (B s) := by
    rintro ⟨j, a⟩ ⟨k, b⟩ hst e hGauge
    dsimp only [sdim, B] at e hGauge
    by_cases hjk : j = k
    · subst k
      have hba : b ≠ a := fun h => hst (by cases h; rfl)
      exact hSep j b a hba e (by simpa only [eqRec_eq_cast] using hGauge)
    · have hOrig : ∀ e' : dim k = dim j, ¬ GaugePhaseEquiv (e' ▸ A k) (A j) := by
        intro e' h
        exact hDistinct k j (Ne.symm hjk) e' (by simpa only [eqRec_eq_cast] using h)
      exact (hPeriodic j).not_gaugePhaseEquiv_of_primitive_corners (hPeriodic k) hOrig hL
        (C j a) (C k b) (W j a) (W k b) (hP j a) (hρ j a)
        (hIso j a) (hIso k b) (hCoInt j a) (hCoInt k b) e hGauge
  have hVIso (s) : (V s)ᴴ * V s = 1 := by
    change (blockInclusion dim s.1 * W s.1 s.2)ᴴ *
      (blockInclusion dim s.1 * W s.1 s.2) = 1
    calc
      _ = (W s.1 s.2)ᴴ * ((blockInclusion dim s.1)ᴴ * blockInclusion dim s.1) *
        W s.1 s.2 := by simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = 1 := by rw [blockInclusion_conjTranspose_mul_self, Matrix.mul_one, hIso]
  have hSupport (s) : V s * (V s)ᴴ =
      blockInclusion dim s.1 * P s.1 s.2 * (blockInclusion dim s.1)ᴴ := by
    calc
      _ = blockInclusion dim s.1 * (W s.1 s.2 * (W s.1 s.2)ᴴ) *
        (blockInclusion dim s.1)ᴴ := by simp only [V, Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by rw [hV]
  have hVSum : ∑ s, V s * (V s)ᴴ = 1 := by
    have hInner (j : Fin r) :
        (∑ a, blockInclusion dim j * P j a * (blockInclusion dim j)ᴴ) =
        blockInclusion dim j * (blockInclusion dim j)ᴴ := by
      rw [← Matrix.sum_mul, ← Matrix.mul_sum, hSum j, Matrix.mul_one]
    simp only [hSupport, Fintype.sum_sigma, hInner, sum_blockInclusion_mul_conjTranspose]
  have hGlobalInt (s) (i) :
      blockTensor (toTensorFromBlocks (fun _ => 1) A) L i * V s = V s * B s i := by
    simp only [V, B, blockTensor_toTensorFromBlocks_apply, one_pow, ← Matrix.mul_assoc,
      toTensorFromBlocks_mul_blockInclusion, one_smul]
    rw [Matrix.mul_assoc, hInt, ← Matrix.mul_assoc]
  have hGlobalCoInt (s) (i) :
      (V s)ᴴ * blockTensor (toTensorFromBlocks (fun _ => 1) A) L i = B s i * (V s)ᴴ := by
    simp only [V, B, Matrix.conjTranspose_mul, blockTensor_toTensorFromBlocks_apply,
      one_pow, Matrix.mul_assoc, blockInclusion_conjTranspose_mul_toTensorFromBlocks, one_smul]
    rw [← Matrix.mul_assoc, hCoInt, Matrix.mul_assoc]
  let Q : ((j : Fin r) × Fin (m j)) → ℕ →
      Matrix (Fin (∑ j, dim j)) (Fin (∑ j, dim j)) ℂ := fun s t =>
    blockInclusion dim s.1 * P s.1 (s.2 - t • (1 : Fin (m s.1))) *
      (blockInclusion dim s.1)ᴴ
  have hQ (s) (t) : IsOrthogonalProjection (Q s t) := by
    have hJ : (blockInclusion dim s.1)ᴴ * ((blockInclusion dim s.1)ᴴ)ᴴ = 1 := by
      rw [Matrix.conjTranspose_conjTranspose, blockInclusion_conjTranspose_mul_self]
    have hProj' := (hProj s.1 (s.2 - t • (1 : Fin (m s.1)))).isStarProjection
    simpa only [Q, Matrix.conjTranspose_conjTranspose] using
      (hProj'.conjTranspose_mul_mul_of_mul_conjTranspose_eq_one
        ((blockInclusion dim s.1)ᴴ) hJ).isOrthogonalProjection
  have hGlobalGram (s) (t) :
      (∑ τ : Cfg d t,
        (Kraus.evalWord (toTensorFromBlocks (fun _ => 1) A) (List.ofFn τ))ᴴ *
        (V s * (V s)ᴴ) *
        Kraus.evalWord (toTensorFromBlocks (fun _ => 1) A) (List.ofFn τ)) = Q s t := by
    rw [hSupport]
    have hCo : ∀ i, (blockInclusion dim s.1)ᴴ *
        toTensorFromBlocks (fun _ => 1) A i = A s.1 i * (blockInclusion dim s.1)ᴴ := by
      intro i
      simpa only [one_smul] using
        blockInclusion_conjTranspose_mul_toTensorFromBlocks (fun _ => 1) A s.1 i
    rw [embedded_word_gram (toTensorFromBlocks (fun _ => 1) A) (A s.1)
      (blockInclusion dim s.1) (P s.1 s.2) hCo t, hGram]
  exact ⟨sdim, (fun s => hedim s.1 s.2), B, V, (fun s => ρ s.1 s.2),
    (fun s => hP s.1 s.2), (fun s => hρ s.1 s.2), hBsep, hVIso, hVSum,
    hGlobalInt, hGlobalCoInt, Q, hQ, hGlobalGram⟩


end MPSTensor

end

end PoweredCyclicPrimitiveResolution

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
        ((groundSpace (toTensorFromBlocks μ A) n).map (WithLp.linearEquiv 2 ℂ _).symm.toLinearMap)) :
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
        ((groundSpace (toTensorFromBlocks μ A) n).map (WithLp.linearEquiv 2 ℂ _).symm.toLinearMap)) :
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
      ‖((groundSpace A (K n * L + M n * L + r n)).map (WithLp.linearEquiv 2 ℂ _).symm.toLinearMap).starProjection -
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
      ‖((groundSpace A (K n * L + M n * L + r n)).map (WithLp.linearEquiv 2 ℂ _).symm.toLinearMap).starProjection -
        (leftBoundaryMapES A (K n * L + M n * L) (r n)).range.starProjection.comp
          (reassocTailBoundaryMapES A (K n * L) (M n * L) (r n)).range.starProjection‖ := by
    simp only [iSup_range_residualWindowRightMapES_eq_reindex_reassocTailBoundaryMapES
      A B V hSum hCoInt,
      iSup_range_residualWindowLeftMapES_eq_reindex_cover_leftBoundaryMapES
        A B V hV hSum hInt,
      iSup_range_residualWindowMapES_eq_reindex_map_groundSpace_cover A B V hSum hCoInt]
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
          ((groundSpace A N).map (WithLp.linearEquiv 2 ℂ _).symm.toLinearMap))
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
        ((groundSpace (toTensorFromBlocks (fun _ => 1) A) N).map (WithLp.linearEquiv 2 ℂ _).symm.toLinearMap))
    (L : ℕ) (hL : 0 < L) (hdiv : ∀ j, m j ∣ L) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ n, ∀ z : ℂ, Module.End.HasEigenvalue
      (Matrix.toEuclideanLin
          (parentChainInteraction (toTensorFromBlocks (fun _ => 1) A) R (n * L)).hamiltonian) z →
        z = 0 ∨ (γ : ℂ) ≤ z := by
  let T := toTensorFromBlocks (fun _ => 1) A
  have hEventual : ∀ᶠ N in atTop,
      LinearMap.ker (Matrix.toEuclideanLin (parentChainInteraction T R N).hamiltonian) =
        ((groundSpace T N).map (WithLp.linearEquiv 2 ℂ _).symm.toLinearMap) := by
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
        ((groundSpace (toTensorFromBlocks (fun _ => 1) A) N).map (WithLp.linearEquiv 2 ℂ _).symm.toLinearMap)) :
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
        ((groundSpace (toTensorFromBlocks (fun _ => 1) A) N).map (WithLp.linearEquiv 2 ℂ _).symm.toLinearMap)) :
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
          ((groundSpace (toTensorFromBlocks μ A) N).map (WithLp.linearEquiv 2 ℂ _).symm.toLinearMap)) ∧
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
  have hEq (N : ℕ) := hamiltonian_parentChainInteraction_eq_of_map_groundSpace_eq (hJoint R) N
  have hKernelB (N : ℕ) (hRN : R ≤ N) :
      LinearMap.ker
          (Matrix.toEuclideanLin
              (parentChainInteraction (toTensorFromBlocks (fun _ => 1) B) R N).hamiltonian) =
        ((groundSpace (toTensorFromBlocks (fun _ => 1) B) N).map (WithLp.linearEquiv 2 ℂ _).symm.toLinearMap) := by
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
          ((groundSpace (toTensorFromBlocks μ A) N).map (WithLp.linearEquiv 2 ℂ _).symm.toLinearMap)) ∧
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
        ((groundSpace (toTensorFromBlocks μ A) N).map (WithLp.linearEquiv 2 ℂ _).symm.toLinearMap)) :
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
        ((groundSpace (toTensorFromBlocks μ A) N).map (WithLp.linearEquiv 2 ℂ _).symm.toLinearMap)) :
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
