/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.PoweredCyclicPrimitiveResolution
import TNLean.MPS.SharedInfra.BlockInclusionResolution
import TNLean.MPS.CanonicalForm.CPSVBlocking

/-!
# A common-block primitive resolution of a periodic family

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
Nachtergaele, arXiv:cond-mat/9410110, Lemma `commutation` (ii),
lines 2442--2531, and Section 6, lines 2649--2675.
-/

open scoped Matrix BigOperators ComplexOrder
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
Aoffdiag; Nachtergaele, arXiv:cond-mat/9410110, Lemma `commutation` (ii),
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
        (∀ s, IsPrimitiveMPS (B s) (ρ s)) ∧ (∀ s, (ρ s).PosDef) ∧
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
