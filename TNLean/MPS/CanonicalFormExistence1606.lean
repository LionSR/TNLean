/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.CanonicalFormReduction
import TNLean.MPS.IrreducibleFormII
import TNLean.MPS.BlockingPeriodicity
import TNLean.MPS.PeripheralToSpectralGap
import TNLean.MPS.CanonicalFormFromPeripheralPrimitive

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.longLine false

open scoped Matrix BigOperators ComplexOrder
open Filter

/-!
# Canonical form existence pipeline (arXiv:1606.00608, §2.3 + Appendix A)

This file is a **glue layer** assembling already-proved steps of the
canonical-form construction for MPS tensors from Cirac–Pérez-García–Schuch–Verstraete,
arXiv:1606.00608.

We currently have (sorry-free) components for:

* §2.3: iterated invariant-projection splitting → irreducible block decomposition.
* Appendix A (CFII part): TP + irreducible → unitary conjugate with diagonal PD fixed point.
* Appendix A (periodicity): irreducible + doubly stochastic → primitive after blocking.
* peripheral primitive → spectral gap → overlap convergence.
* peripheral primitive + DS gauge + injective + μ ordering → `IsCanonicalForm`.

What is **not** yet assembled end-to-end here:

* A Perron–Frobenius / gauge step turning an arbitrary irreducible block into the TP gauge.
* A route from CFII data to the doubly-stochastic hypothesis needed by the current periodicity
  removal lemma.
* The bridge from primitivity to normality / injectivity-by-blocking (quantum Wielandt), needed
  to feed the final canonical-form builder.

Accordingly, the final theorem in this file stops at an irreducible block decomposition and
provides CFII data **conditionally** on a TP-gauge hypothesis for each block.
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
## (2) CFII normalization for irreducible TP blocks (1606.00608 Appendix A)

We package `exists_unitary_diag_posDef_fixedPoint_of_TP_of_isIrreducibleTensor` together with the
fact that unitary conjugation preserves MPVs.
-/

/-- **Pipeline step (1606.00608 Appendix A, CFII).**

For an irreducible tensor `A` in the TP gauge (`∑ Aᵢ†Aᵢ = I`) and with `0 < D`, there exist

* a unitary `U`,
* a diagonal positive-definite matrix `Λ`,

such that the unitary conjugate tensor
`B i := U† * A i * U` is still TP, has `Λ` as a fixed point of its transfer map, and is
`SameMPV₂`-equivalent to `A` (unitary gauge equivalence).

This is the formal analogue of bringing a block into **Canonical Form II** (CFII). -/
theorem exists_CFII_data_of_TP_of_isIrreducibleTensor
    (A : MPSTensor d D)
    (hTP : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hIrr : IsIrreducibleTensor (d := d) (D := D) A)
    (hD : 0 < D) :
    ∃ (U : Matrix.unitaryGroup (Fin D) ℂ)
      (Λ : Matrix (Fin D) (Fin D) ℂ),
        let B : MPSTensor d D :=
          fun i => (↑U : Matrix (Fin D) (Fin D) ℂ)ᴴ * A i * (↑U : Matrix (Fin D) (Fin D) ℂ);
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
        (fun i => (↑U : Matrix (Fin D) (Fin D) ℂ)ᴴ * A i * (↑U : Matrix (Fin D) (Fin D) ℂ)) := by
    -- Existing lemma is stated with `star` rather than `ᴴ`.
    simpa [Matrix.star_eq_conjTranspose] using
      (sameMPV_conj_unitary (d := d) (D := D) A U)
  -- Assemble the packaged data under the `let B := ...` binder.
  -- The goal is definitionally a conjunction about the explicit conjugated tensor.
  -- We therefore `simpa` using the existing data.
  simpa using (And.intro hSame (And.intro hΛ_pd (And.intro hΛ_diag (And.intro hTP_conj hΛ_fix))))


/-!
## (3) Periodicity removal by blocking (1606.00608 Appendix A)

At present the library lemma is formulated for **doubly stochastic** Kraus families.
We simply re-export it with a pipeline name.
-/

/-- **Pipeline step (1606.00608 Appendix A): periodicity removal by blocking.**

Current library version: assumes the Kraus family is doubly stochastic (unital + TP) and
irreducible, and concludes that some physical blocking makes the transfer map primitive. -/
theorem exists_blockTensor_isPrimitive_pipeline1606
    {d D : ℕ} [NeZero D]
    (A : MPSTensor d D)
    (h_unital : KadisonSchwarz.IsUnitalKraus A)
    (h_tp : KadisonSchwarz.IsTPKraus A)
    (hIrr : IsIrreducibleMap (transferMap (d := d) (D := D) A)) :
    ∃ p : ℕ, 0 < p ∧
      _root_.IsPrimitive
        (transferMap (d := blockPhysDim d p) (D := D) (blockTensor (d := d) (D := D) A p)) := by
  simpa using
    (exists_blockTensor_isPrimitive_of_irreducible_doubly_stochastic
      (A := A) h_unital h_tp hIrr)


/-!
## (4) Peripheral primitive ⇒ spectral gap ⇒ overlap → 1

This is a direct re-export of the existing lemma.
-/

/-- **Pipeline step:** peripheral-spectrum primitivity of `transferMap A` implies the overlap
`mpvOverlap A A N` tends to `1`. -/
theorem overlap_tendsto_one_of_peripheralPrimitive_pipeline1606
    {d D : ℕ} [NeZero D]
    (A : MPSTensor d D)
    (hInj : IsInjective A)
    (hNorm : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hPrim : PeripheralSpectrum.IsPrimitive (transferMap (d := d) (D := D) A)) :
    Tendsto (fun N => mpvOverlap (d := d) A A N) atTop (nhds (1 : ℂ)) := by
  simpa using
    (MPSTensor.overlap_tendsto_one_of_peripheralPrimitive (A := A) hInj hNorm hPrim)


/-!
## (5) Canonical form builder from peripheral primitivity

Again, this is just a re-export with a pipeline name.
-/

/-- **Pipeline step:** build `IsCanonicalForm` from peripheral-spectrum primitivity hypotheses
(on each block), together with injectivity + DS gauge + μ ordering + μ ≠ 0. -/
theorem isCanonicalForm_of_peripheralPrimitive_pipeline1606
    {d : ℕ} {r : ℕ} {dim : Fin r → ℕ} [∀ k, NeZero (dim k)]
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
## Near-final existence theorem (up to CFII data)

We now combine steps (1) and (2). Since step (2) currently assumes the TP gauge,
we state the result **conditionally**: each irreducible block admits CFII fixed-point data
*once a TP gauge is provided*.

TODO (for full end-to-end canonical form existence):

* Prove an existence theorem putting each irreducible block into TP gauge.
* Relate CFII data to the doubly-stochastic hypotheses needed for periodicity removal.
* Use blocking/primitivity to derive normality / injectivity-by-blocking (quantum Wielandt).
* Feed the resulting data into `isCanonicalForm_of_peripheralPrimitive_pipeline1606`.
-/

/-- **Canonical-form pipeline, assembled up to CFII (1606.00608 §2.3 + App. A).**

From an arbitrary tensor `A` we produce an irreducible block decomposition. Moreover, for each
block, assuming (i) TP gauge and (ii) positive bond dimension, we can produce CFII fixed-point
data (unitary conjugation + diagonal PD fixed point).

This theorem is intended as a convenient “handoff point” for the remaining steps of the
canonical-form construction. -/
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
