/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.CanonicalFormReduction
import TNLean.Channel.PerronFrobeniusExistence
import TNLean.MPS.IrreducibleFormII
import TNLean.MPS.BlockingPeriodicityCFII_viaAdjoint
import TNLean.MPS.PeripheralToSpectralGap
import TNLean.MPS.CanonicalFormFromPeripheralPrimitive

open scoped Matrix BigOperators ComplexOrder MatrixOrder
open Filter

/-!
# Canonical form existence pipeline (arXiv:1606.00608, §2.3 + Appendix A)

This file is a **glue layer for the early, honest arbitrary-input part** of the
canonical-form construction for MPS tensors from Cirac–Pérez-García–Schuch–Verstraete,
arXiv:1606.00608.

We currently have (sorry-free) components for:

* §2.3: iterated invariant-projection splitting → irreducible block decomposition.
* Appendix A (PF / TP gauge): irreducible + nonzero Kraus operator → Perron--Frobenius
  eigenvector → TP-normalized representative.
* Appendix A (CFII part): inside that TP gauge, unitary conjugation → diagonal PD fixed point.
* Appendix A (periodicity): TP + irreducible → primitive after blocking.

We also keep a couple of downstream compatibility wrappers for already-normalized primitive /
injective block families, but those are **not** assembled from arbitrary input in this file.

Note: the Appendix-A CFII story is genuinely two-step:
first a generally non-unitary TP similarity from the adjoint Perron--Frobenius eigenvector,
then a unitary diagonalization **within** that TP gauge.

What is **not** yet assembled end-to-end here:

* Thread the TP-gauge and periodicity theorems through the irreducible block decomposition while
  handling possible zero blocks honestly under `SameMPV₂` (which remembers the `N = 0` sector).
* Resolve the post-blocking cyclic-sector / equal-weight issues needed to produce a primitive
  weighted block family with strictly ordered nonzero weights.
* Bridge that data to the later block-injective / `IsCanonicalForm` builders and downstream FT
  assembly.

Accordingly, this file should be read as a collection of early-stage pipeline lemmas plus explicit
handoffs, **not** as a near-endpoint canonical-form existence theorem for arbitrary input tensors.
-/

namespace MPSTensor

variable {d D : ℕ}

/-!
## (1) Irreducible block decomposition (1606.00608 §2.3)

This is a re-export of `MPSTensor.exists_irreducible_blockDecomp` with a pipeline-oriented name.
-/

/-- **Pipeline step (1606.00608 §2.3).**

Every tensor is `SameMPV₂`-equivalent to a block-diagonal tensor whose blocks are irreducible
(with respect to invariant orthogonal projections).

This is just `MPSTensor.exists_irreducible_blockDecomp`. -/
theorem exists_irreducible_blockDecomp_pipeline1606 (A : MPSTensor d D) :
    ∃ r : ℕ, ∃ dim : Fin r → ℕ,
    ∃ blocks : (k : Fin r) → MPSTensor d (dim k),
      (∀ k, IsIrreducibleTensor (blocks k)) ∧
      SameMPV₂ A (toTensorFromBlocks (d := d) (μ := fun _ : Fin r => (1 : ℂ)) blocks) := by
  simpa using (exists_irreducible_blockDecomp (d := d) (D := D) A)


/-!
## (2) Perron–Frobenius / TP gauge for irreducible blocks (1606.00608 Appendix A)

This is a re-export of `MPSTensor.exists_tp_data_of_irreducible` with a pipeline-oriented name.
-/

/-- **Pipeline step (1606.00608 Appendix A, PF / TP gauge).**

For an irreducible tensor `A` with `0 < D` and some nonzero Kraus operator, there exist

* a positive real `r`,
* a positive definite matrix `σ`,
* a TP tensor `B` gauge-equivalent to `(1/√r) • A`.

This is just `MPSTensor.exists_tp_data_of_irreducible`. -/
theorem exists_tp_data_of_irreducible_pipeline1606
    [NeZero D]
    (A : MPSTensor d D)
    (hIrr : IsIrreducibleTensor (d := d) (D := D) A)
    (hA : ∃ i, A i ≠ 0) :
    ∃ (B : MPSTensor d D) (r : ℝ) (σ : Matrix (Fin D) (Fin D) ℂ),
      σ.PosDef ∧ 0 < r ∧
      (∀ i : Fin d,
        B i = CFC.sqrt σ *
          ((↑((Real.sqrt r)⁻¹) : ℂ) • A i) * (CFC.sqrt σ)⁻¹) ∧
      (∑ i : Fin d, (B i)ᴴ * B i = 1) ∧
      GaugeEquiv (d := d) (D := D)
        (fun i => (↑((Real.sqrt r)⁻¹) : ℂ) • A i) B := by
  simpa using (exists_tp_data_of_irreducible (A := A) hIrr hA)


/-!
## (3) CFII normalization for irreducible TP blocks (1606.00608 Appendix A)

We package `exists_unitary_diag_posDef_fixedPoint_of_TP_of_isIrreducibleTensor` together with the
fact that unitary conjugation preserves MPVs.

Important: this is the **second** half of the Appendix-A normalization story. The preceding
PF / TP-gauge step is generally a non-unitary similarity; the unitary appearing here acts only
after one has already moved into the one-sided TP gauge.
-/

/-- **Pipeline step (1606.00608 Appendix A, CFII).**

For an irreducible tensor `A` in the TP gauge (`∑ Aᵢ†Aᵢ = I`) and with `0 < D`, there exist

* a unitary `U`,
* a diagonal positive-definite matrix `Λ`,

such that the unitary conjugate tensor
`B i := U† * A i * U` is still TP, has `Λ` as a fixed point of its transfer map, and is
`SameMPV₂`-equivalent to `A` (unitary gauge equivalence).

This is the formal analogue of bringing a block into **Canonical Form II** (CFII) *after*
one has already chosen a TP representative; it does not say that the original pre-TP-gauge tensor
is related to a CFII representative by a unitary similarity alone. -/
theorem exists_CFII_data_of_TP_of_isIrreducibleTensor
    (A : MPSTensor d D)
    (hTP : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hIrr : IsIrreducibleTensor (d := d) (D := D) A)
    (hD : 0 < D) :
    ∃ (U : Matrix.unitaryGroup (Fin D) ℂ)
      (Λ : Matrix (Fin D) (Fin D) ℂ),
        let B : MPSTensor d D :=
          fun i =>
            (↑U : Matrix (Fin D) (Fin D) ℂ)ᴴ * A i * (↑U : Matrix (Fin D) (Fin D) ℂ);
        SameMPV₂ A B ∧
        Λ.PosDef ∧ Λ.IsDiag ∧
        (∑ i : Fin d, (B i)ᴴ * (B i) = 1) ∧
        transferMap (d := d) (D := D) B Λ = Λ := by
  classical
  obtain ⟨U, Λ, hΛ_pd, hΛ_diag, hTP_conj, hΛ_fix⟩ :=
    exists_unitary_diag_posDef_fixedPoint_of_TP_of_isIrreducibleTensor
      (d := d) (D := D) A hTP hIrr hD
  refine ⟨U, Λ, ?_⟩
  -- MPV is invariant under unitary conjugation.
  have hSame :
      SameMPV₂ A
        (fun i =>
          (↑U : Matrix (Fin D) (Fin D) ℂ)ᴴ * A i * (↑U : Matrix (Fin D) (Fin D) ℂ)) := by
    -- Existing lemma is stated with `star` rather than `ᴴ`.
    simpa [Matrix.star_eq_conjTranspose] using sameMPV_conj_unitary (d := d) (D := D) A U
  -- Assemble the packaged data under the `let B := ...` binder.
  -- The goal is definitionally a conjunction about the explicit conjugated tensor.
  simpa using And.intro hSame (And.intro hΛ_pd (And.intro hΛ_diag (And.intro hTP_conj hΛ_fix)))


/-!
## (4) Periodicity removal by blocking (1606.00608 Appendix A)

This is the Appendix-A periodicity-removal step for TP irreducible blocks, routed through the
adjoint-transfer formulation.
-/

/-- **Pipeline step (1606.00608 Appendix A): periodicity removal by blocking.**

If `A` is trace-preserving and irreducible (tensor sense), then some physical blocking makes the
transfer map primitive. -/
theorem exists_blockTensor_isPrimitive_pipeline1606
    [NeZero D]
    (A : MPSTensor d D)
    (hTP : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hIrr : IsIrreducibleTensor (d := d) (D := D) A) :
    ∃ p : ℕ, 0 < p ∧
      _root_.IsPrimitive
        (transferMap (d := blockPhysDim d p) (D := D) (blockTensor (d := d) (D := D) A p)) := by
  have hDpos : 0 < D := Nat.pos_of_ne_zero (NeZero.ne D)
  simpa using
    (exists_blockTensor_isPrimitive_of_TP_of_isIrreducibleTensor (A := A) hTP hIrr hDpos)


/-!
## (5) Downstream compatibility wrappers

The next two theorems are compatibility aliases for later-stage builder lemmas. They are useful
once one already has irreducible / injective peripheral-primitive blocks, but this file does **not**
construct those hypotheses from an arbitrary tensor.
-/

/-- **Compatibility wrapper:** if `A` is already irreducible, left-canonical, and
peripheral-spectrum primitive, then `mpvOverlap A A N` tends to `1`.

This is a late-stage blockwise lemma; it is not an arbitrary-input existence theorem. -/
theorem overlap_tendsto_one_of_peripheralPrimitive_pipeline1606
    [NeZero D]
    (A : MPSTensor d D)
    (hIrr : IsIrreducibleTensor (d := d) (D := D) A)
    (hNorm : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hPrim : PeripheralSpectrum.IsPrimitive (transferMap (d := d) (D := D) A)) :
    Tendsto (fun N => mpvOverlap (d := d) A A N) atTop (nhds (1 : ℂ)) := by
  simpa using
    (MPSTensor.overlap_tendsto_one_of_peripheralPrimitive_of_irreducible
      (A := A) hIrr hNorm hPrim)


/-- **Compatibility wrapper:** build `IsCanonicalForm` from peripheral-spectrum primitivity
hypotheses (on each block), together with injectivity + the one-sided normalization
`∑ Aᵢ† Aᵢ = I` (left-canonical normalization) + μ ordering + μ ≠ 0.

This is a downstream builder theorem; it is not produced from arbitrary input in this file. -/
theorem isCanonicalForm_of_peripheralPrimitive_pipeline1606
    {r : ℕ} {dim : Fin r → ℕ} [∀ k, NeZero (dim k)]
    {μ : Fin r → ℂ} {A : (k : Fin r) → MPSTensor d (dim k)}
    (hInj : ∀ k, IsInjective (A k))
    (hDS : ∀ k, ∑ i : Fin d, (A k i)ᴴ * (A k i) = 1)
    (hμanti : StrictAnti (fun k : Fin r => ‖μ k‖))
    (hμne : ∀ k, μ k ≠ 0)
    (hPrimPer :
      ∀ k, PeripheralSpectrum.IsPrimitive (transferMap (d := d) (D := dim k) (A k))) :
    MPSTensor.IsCanonicalForm (d := d) (μ := μ) A := by
  simpa using
    (MPSTensor.isCanonicalForm_of_peripheralPrimitive
      (hInj := hInj) (hDS := hDS) (hμanti := hμanti) (hμne := hμne) (hPrimPer := hPrimPer))


/-!
## Honest arbitrary-input handoffs (still far from the endpoint)

The last honest arbitrary-input step currently available here is the blockwise PF / TP-gauge
continuation below: after decomposing `A` into irreducible blocks, one may continue on each block
once one separately knows that the block has a nonzero Kraus operator. This explicit side condition
is essential because, under the current `SameMPV₂` relation, zero scalar blocks cannot simply be
discarded: the `N = 0` sector is remembered.

The newer file `TNLean.MPS.NormalCanonicalFormPipeline` packages a later stage once one already has
a primitive weighted block family with positive bond dimensions and distinct nonzero weights. This
file does **not** currently construct that input from an arbitrary tensor.

Remaining gap for a full end-to-end canonical-form existence theorem:

* Thread `exists_tp_data_of_irreducible_pipeline1606` blockwise through
  `exists_irreducible_blockDecomp_pipeline1606` while handling possible zero blocks honestly.
* Apply `exists_blockTensor_isPrimitive_pipeline1606` and then perform the post-blocking cyclic
  sector / equal-weight bookkeeping needed for strict nonzero weight ordering.
* Use the resulting data to reach the stronger normal / injective-by-blocking hypotheses needed by
  `TNLean.MPS.NormalCanonicalFormPipeline` and the downstream `IsCanonicalForm` builders.
-/

/-- **Honest TP-gauge handoff for the 1606 pipeline (1606.00608 §2.3 + App. A).**

From an arbitrary tensor `A` we produce an irreducible block decomposition. Moreover, for each
resulting block, if one separately knows that the block has some nonzero Kraus operator, then the
Perron--Frobenius / TP-gauge step can be applied to that block.

This is the next honest continuation from arbitrary input under the current API. The nonzero side
condition is explicit because `SameMPV₂` remembers the `N = 0` sector, so zero scalar blocks cannot
be silently discarded. -/
theorem exists_irreducible_blockDecomp_with_tpGauge_handoff
    (A : MPSTensor d D) :
    ∃ r : ℕ, ∃ dim : Fin r → ℕ,
    ∃ blocks : (k : Fin r) → MPSTensor d (dim k),
      (∀ k, IsIrreducibleTensor (blocks k)) ∧
      SameMPV₂ A (toTensorFromBlocks (d := d) (μ := fun _ : Fin r => (1 : ℂ)) blocks) ∧
      (∀ k,
        (∃ i, blocks k i ≠ 0) →
        ∃ (B : MPSTensor d (dim k)) (r : ℝ) (σ : Matrix (Fin (dim k)) (Fin (dim k)) ℂ),
          σ.PosDef ∧ 0 < r ∧
          (∀ i : Fin d,
            B i = CFC.sqrt σ *
              ((↑((Real.sqrt r)⁻¹) : ℂ) • blocks k i) * (CFC.sqrt σ)⁻¹) ∧
          (∑ i : Fin d, (B i)ᴴ * B i = 1) ∧
          GaugeEquiv (d := d) (D := dim k)
            (fun i => (↑((Real.sqrt r)⁻¹) : ℂ) • blocks k i) B) := by
  classical
  obtain ⟨r, dim, blocks, hIrr, hSame⟩ :=
    exists_irreducible_blockDecomp_pipeline1606 (d := d) (D := D) A
  refine ⟨r, dim, blocks, hIrr, hSame, ?_⟩
  intro k hNonzero
  have hdim_ne : dim k ≠ 0 := by
    intro hk0
    rcases hNonzero with ⟨i, hi⟩
    have hEmpty : IsEmpty (Fin (dim k)) := by
      rw [hk0]
      infer_instance
    have hzero : blocks k i = 0 := by
      ext a b
      exact (hEmpty.false a).elim
    exact hi hzero
  letI : NeZero (dim k) := ⟨hdim_ne⟩
  simpa using
    (exists_tp_data_of_irreducible_pipeline1606 (d := d) (D := dim k)
      (A := blocks k) (hIrr := hIrr k) (hA := hNonzero))

/-- **Legacy CFII handoff for the 1606 pipeline (1606.00608 §2.3 + App. A).**

From an arbitrary tensor `A` we produce an irreducible block decomposition. Moreover, for each
block, assuming one has already supplied (i) a TP representative and (ii) positive bond dimension,
we can produce CFII fixed-point data (unitary conjugation + diagonal PD fixed point).

This is an optional Appendix-A side branch, not a near-endpoint theorem: it does not thread the PF
/ TP-gauge or periodicity-removal steps through the block decomposition. Later packaging into
normal canonical form, once primitive weighted blocks are already in hand, lives in
`TNLean.MPS.NormalCanonicalFormPipeline`. -/
theorem exists_irreducible_blockDecomp_with_CFII_handoff
    (A : MPSTensor d D) :
    ∃ r : ℕ, ∃ dim : Fin r → ℕ,
    ∃ blocks : (k : Fin r) → MPSTensor d (dim k),
      (∀ k, IsIrreducibleTensor (blocks k)) ∧
      SameMPV₂ A (toTensorFromBlocks (d := d) (μ := fun _ : Fin r => (1 : ℂ)) blocks) ∧
      (∀ k,
        (∑ i : Fin d, (blocks k i)ᴴ * blocks k i = 1) →
        0 < dim k →
        ∃ (U : Matrix.unitaryGroup (Fin (dim k)) ℂ)
          (Λ : Matrix (Fin (dim k)) (Fin (dim k)) ℂ),
            let B : MPSTensor d (dim k) :=
              fun i => (↑U : Matrix (Fin (dim k)) (Fin (dim k)) ℂ)ᴴ *
                blocks k i *
                (↑U : Matrix (Fin (dim k)) (Fin (dim k)) ℂ);
            SameMPV₂ (blocks k) B ∧
            Λ.PosDef ∧ Λ.IsDiag ∧
            (∑ i : Fin d, (B i)ᴴ * (B i) = 1) ∧
            transferMap (d := d) (D := dim k) B Λ = Λ) := by
  classical
  obtain ⟨r, dim, blocks, hIrr, hSame⟩ :=
    exists_irreducible_blockDecomp_pipeline1606 (d := d) (D := D) A
  refine ⟨r, dim, blocks, hIrr, hSame, ?_⟩
  intro k hTPk hDk
  -- Apply the packaged CFII lemma to the k-th block.
  simpa using
    (exists_CFII_data_of_TP_of_isIrreducibleTensor (d := d) (D := dim k)
      (A := blocks k) (hTP := hTPk) (hIrr := hIrr k) (hD := hDk))

end MPSTensor
