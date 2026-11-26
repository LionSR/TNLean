/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.CanonicalForm.NormalBlocks.PrimitiveBlocks
import TNLean.MPS.Transfer.Irreducible.PhysicalReindexTransport
import TNLean.MPS.ParentHamiltonian.BlockGroundSpace.Sector.PeriodicGroundSpaceIndependence
import TNLean.MPS.ParentHamiltonian.BlockGroundSpace.Sector.ResidualBoundaryGram
import TNLean.MPS.Tensor.DirectSum.BlockAssembly
import TNLean.MPS.CanonicalForm.NormalBlocks.Blocking

/-!
# Primitive fixed-point witnesses under blocking and physical relabelling

Positive blocking preserves a primitive tensor with its supplied faithful
stationary matrix. A bijective change of the physical alphabet preserves
the same witness without any additional faithfulness assumption. These
statements retain the stationary matrix, rather than choosing another
representative of its ray.

Source: De las Cuevas--Cirac--Schuch--Perez-Garcia, arXiv:1708.00029,
Lemma lem:blocking-arbitrary, lines 434--451; Nachtergaele,
arXiv:cond-mat/9410110, equations (3.1)--(3.2b), lines 1394--1435,
and the grouping argument in Section 6, lines 2649--2675.

It also contains the following results.

* `MPSTensor.IsPeriodic.exists_powered_cyclic_primitive_sector_resolution`,
  `MPSTensor.exists_commonBlock_primitive_sector_resolution_of_isPeriodic`: literal cyclic sectors
  at a common blocking length.
-/

section PrimitiveWitnessTransport

open scoped Matrix BigOperators ComplexOrder
open Kraus (blockTensor)
namespace MPSTensor
variable {d D : ℕ} [NeZero D]

/-- Every positive blocking retains the same faithful primitive fixed-point
witness. Source: DCCSP17, arXiv:1708.00029, Lemma lem:blocking-arbitrary,
lines 434--451, specialized to a period-one tensor; Nachtergaele,
arXiv:cond-mat/9410110, Section 6, lines 2649--2675. -/
theorem _root_.Kraus.HasComplementaryFixedPointGap.blockTensor {A : MPSTensor d D}
    {ρ : Matrix (Fin D) (Fin D) ℂ} (hP : Kraus.HasComplementaryFixedPointGap A ρ)
    (hρ : ρ.PosDef) {q : ℕ} (hq : 0 < q) :
    Kraus.HasComplementaryFixedPointGap (blockTensor A q) ρ := by
  obtain ⟨hTP, hPrim, hIrr⟩ := tp_primitive_irreducible_extra_blocking A
    hP.norm hP.isPrimitive (hP.isIrreducibleFamily_of_posDef hρ) hq
  have hFix := transferMap_blockTensor_fixedPoint A q ρ hP.fixedPoint_is_fixed
  obtain ⟨htr, hGap⟩ :=
    spectralRadius_compl_lt_one_of_primitive_fixedPoint_of_irreducible_channel
      (Kraus.transferMap (Kraus.blockTensor A q)) (Kraus.isChannel_mapLM _ hTP)
      (Kraus.isIrreducibleMap_mapLM_of_isIrreducibleFamily _ hIrr)
      hPrim ρ hP.fixedPoint_psd hP.fixedPoint_ne_zero hFix
  exact ⟨hTP, hP.fixedPoint_ne_zero, hP.fixedPoint_psd, hFix, hGap⟩

/-- A bijective relabelling of physical letters preserves a primitive
fixed-point witness, since both the Kraus normalization and transfer map
are unchanged. Source: Nachtergaele, arXiv:cond-mat/9410110,
equations (3.1)--(3.2b), lines 1394--1435. -/
theorem _root_.Kraus.HasComplementaryFixedPointGap.reindexPhysical {d₁ d₂ : ℕ} {A : MPSTensor d₂ D}
    {ρ : Matrix (Fin D) (Fin D) ℂ} (hP : Kraus.HasComplementaryFixedPointGap A ρ)
    (e : Fin d₁ ≃ Fin d₂) :
    Kraus.HasComplementaryFixedPointGap (Kraus.reindexPhysical e A) ρ := by
  have hMap : Kraus.mapLM (Kraus.reindexPhysical e A) = Kraus.mapLM A :=
    transferMap_reindexPhysical_equiv e A
  refine ⟨(leftCanonical_reindexPhysical_equiv e A).mpr hP.norm,
    hP.fixedPoint_ne_zero, hP.fixedPoint_psd, ?_, ?_⟩
  · simpa only [hMap] using hP.fixedPoint_is_fixed
  · simpa only [hMap] using hP.complementary_transfer_map_gap

end MPSTensor

end PrimitiveWitnessTransport

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
