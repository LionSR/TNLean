/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.CanonicalForm.Reduction
import TNLean.Channel.PerronFrobenius.Existence
import TNLean.MPS.Irreducible.FormII
import TNLean.MPS.CanonicalForm.BlockingViaAdjoint
import TNLean.MPS.Overlap.PeripheralToSpectralGap
import TNLean.MPS.CanonicalForm.FromPeripheralPrimitive
import TNLean.Wielandt.Primitivity.StronglyIrreducibleToFullRank

open scoped Matrix BigOperators ComplexOrder MatrixOrder
open Filter

/-!
# Canonical form existence reduction (arXiv:1606.00608, §2.3 + Appendix A)

This file is an **intermediate construction for the early arbitrary-input part** of the
canonical-form construction for MPS tensors from Cirac–Pérez-García–Schuch–Verstraete,
arXiv:1606.00608.

We currently have the following components:

* §2.3: iterated invariant-projection splitting → irreducible block decomposition.
* Appendix A (PF / TP gauge): irreducible + nonzero Kraus operator → Perron--Frobenius
  eigenvector → TP-normalized representative.
* Appendix A (CFII part): inside that TP gauge, unitary conjugation → diagonal PD fixed point.
* Appendix A (periodicity): TP + irreducible → primitive after blocking.

We also keep a couple of downstream compatibility formulations for already-normalized primitive /
injective block families, but those are **not** assembled from arbitrary input in this file.

Note: the Appendix-A CFII story is genuinely two-step:
first a generally non-unitary TP similarity from the adjoint Perron--Frobenius eigenvector,
then a unitary diagonalization **within** that TP gauge.

What is **not** yet assembled end-to-end here:

* Thread the TP-gauge and periodicity theorems through the irreducible block decomposition while
  handling possible zero blocks exactly under `SameMPV₂` (which remembers the `N = 0` sector).
* Resolve the post-blocking cyclic-sector / equal-weight issues needed to produce a primitive
  weighted block family with strictly ordered nonzero weights.
* Pass that data to the later block-injective / `IsCanonicalForm` builders and downstream FT
  results.

Accordingly, this file should be read as a collection of early-stage
reduction lemmas plus explicit continuation statements, **not** as a
near-final canonical-form existence theorem for arbitrary input tensors.
-/

namespace MPSTensor

variable {d D : ℕ}

/-!
## (1) Irreducible block decomposition (1606.00608 §2.3)

We use `MPSTensor.exists_irreducible_blockDecomp` from `Reduction.lean` directly below.
-/


/-!
## (2) Perron–Frobenius / TP gauge for irreducible blocks (1606.00608 Appendix A)

We use `MPSTensor.exists_tp_data_of_irreducible` from
`Channel/PerronFrobenius/Existence.lean` directly below.
-/


/-!
## (3) CFII normalization for irreducible TP blocks (1606.00608 Appendix A)

We package `exists_unitary_diag_posDef_fixedPoint_of_TP_of_isIrreducibleTensor` together with the
fact that unitary conjugation preserves MPVs.

Important: this is the **second** half of the Appendix-A normalization story. The preceding
PF / TP-gauge step is generally a non-unitary similarity; the unitary appearing here acts only
after one has already moved into the one-sided TP gauge.
-/

/-- **Reduction step (1606.00608 Appendix A, CFII).**

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
    simpa only [Matrix.star_eq_conjTranspose] using
      sameMPV_conj_unitary (d := d) (D := D) A U
  -- Assemble the packaged data under the `let B := ...` binder.
  exact ⟨hSame, hΛ_pd, hΛ_diag, hTP_conj, hΛ_fix⟩


/-!
## (4) Periodicity removal by blocking (1606.00608 Appendix A)

This is the Appendix-A periodicity-removal step for TP irreducible blocks, routed through the
adjoint-transfer formulation.
-/

/-- **Reduction step (1606.00608 Appendix A): periodicity removal by blocking.**

If `A` is trace-preserving and irreducible (tensor sense), then some physical blocking makes the
transfer map primitive. -/
theorem exists_blockTensor_isPrimitive
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

/-- **Reduction step (1606.00608 Appendix A, TP normalization after blocking).**

If `A` is trace-preserving and irreducible, then some physical blocking makes the
blocked transfer map primitive, and the blocked tensor remains left-canonical. -/
theorem exists_blockTensor_leftCanonical_isPrimitive
    [NeZero D]
    (A : MPSTensor d D)
    (hTP : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hIrr : IsIrreducibleTensor (d := d) (D := D) A) :
    ∃ p : ℕ, 0 < p ∧
      (∑ i : Fin (blockPhysDim d p),
          (blockTensor (d := d) (D := D) A p i)ᴴ *
            blockTensor (d := d) (D := D) A p i = 1) ∧
      _root_.IsPrimitive
        (transferMap (d := blockPhysDim d p) (D := D) (blockTensor (d := d) (D := D) A p)) := by
  obtain ⟨p, hp, hPrim⟩ :=
    exists_blockTensor_isPrimitive (A := A) hTP hIrr
  refine ⟨p, hp, leftCanonical_blockTensor (d := d) (D := D) (A := A) (L := p) hTP, hPrim⟩

/-- **Reduction compatibility theorem:** spectral-gap primitivity with a positive-definite
fixed point implies normality. -/
theorem isNormal_of_isPrimitiveMPS
    [NeZero D]
    {A : MPSTensor d D} {ρ : Matrix (Fin D) (Fin D) ℂ}
    (hPrim : IsPrimitiveMPS A ρ)
    (hPD : ρ.PosDef) :
    IsNormal A :=
  isNormal_of_isPrimitiveMPS_with_posDef hPrim hPD


/-!
## (5) Downstream compatibility imports

For later-stage overlap and canonical-form builders we use the dedicated results from
`PeripheralToSpectralGap.lean` and `FromPeripheralPrimitive.lean` directly.
-/

/-!
## Zero-block vanishing at positive length

These are the first low-level facts needed for a complete treatment of zero blocks.
They show that an all-zero tensor contributes nothing on nonempty words, hence nothing to MPVs for
system sizes `N ≥ 1`. This still does **not** permit silently discarding zero scalar blocks under
`SameMPV₂`, because the `N = 0` sector continues to remember the total bond dimension.
-/

/-- An all-zero tensor evaluates to zero on every nonempty word. -/
theorem evalWord_eq_zero_of_all_zero (A : MPSTensor d D)
    (hzero : ∀ i : Fin d, A i = 0)
    (w : List (Fin d)) (hw : w ≠ []) :
    evalWord A w = 0 := by
  cases w with
  | nil =>
      exact (hw rfl).elim
  | cons i w =>
      simp only [evalWord, hzero i, zero_mul]

/-- An all-zero tensor contributes zero to the MPV for every positive system size. -/
theorem mpv_eq_zero_of_all_zero (A : MPSTensor d D)
    (hzero : ∀ i : Fin d, A i = 0)
    {N : ℕ} (σ : Fin N → Fin d) (hN : 0 < N) :
    mpv A σ = 0 := by
  have hw : List.ofFn σ ≠ [] := by
    intro hnil
    have hlen : N = 0 := by
      simpa [List.length_ofFn] using congrArg List.length hnil
    exact (Nat.ne_of_gt hN) hlen
  unfold mpv coeff
  rw [evalWord_eq_zero_of_all_zero (A := A) hzero (w := List.ofFn σ) hw]
  simp only [Matrix.trace_zero]

/-- If an irreducible tensor has bond dimension at least `2`, then some Kraus operator is
nonzero. -/
theorem exists_nonzero_kraus_of_isIrreducibleTensor
    (A : MPSTensor d D)
    (hIrr : IsIrreducibleTensor (d := d) (D := D) A)
    (hD : 1 < D) :
    ∃ i : Fin d, A i ≠ 0 := by
  classical
  by_contra hA
  push Not at hA
  let i0 : Fin D := ⟨0, lt_trans Nat.zero_lt_one hD⟩
  let i1 : Fin D := ⟨1, hD⟩
  let P : Matrix (Fin D) (Fin D) ℂ :=
    Matrix.diagonal (fun j => if j = i0 then (1 : ℂ) else 0)
  have hPproj : IsOrthogonalProjection P := by
    refine ⟨?_, ?_⟩
    · change P.conjTranspose = P
      simp [P]
    · simp [P]
  have hi10 : i1 ≠ i0 := by
    intro hEq
    have hval : (1 : ℕ) = 0 := by
      simpa [i1, i0] using congrArg Fin.val hEq
    exact Nat.one_ne_zero hval
  have hP0 : P ≠ 0 := by
    intro hP
    have hEntry : (1 : ℂ) = 0 := by
      simpa [P] using congrArg (fun M : Matrix (Fin D) (Fin D) ℂ => M i0 i0) hP
    exact one_ne_zero hEntry
  have hP1 : P ≠ 1 := by
    intro hP
    have hEntry : (0 : ℂ) = 1 := by
      simpa [P, hi10] using congrArg (fun M : Matrix (Fin D) (Fin D) ℂ => M i1 i1) hP
    exact zero_ne_one hEntry
  have hLower : ∀ i : Fin d, (1 - P) * A i * P = 0 := by
    intro i
    simp [hA i]
  exact hIrr ⟨P, hPproj, hP0, hP1, hLower⟩

/-- An all-zero irreducible tensor can have bond dimension at most `1`. -/
theorem isIrreducibleTensor_allZero_dim_le_one
    (A : MPSTensor d D)
    (hIrr : IsIrreducibleTensor (d := d) (D := D) A)
    (hzero : ∀ i : Fin d, A i = 0) :
    D ≤ 1 := by
  by_contra hD
  have hD' : 1 < D := Nat.lt_of_not_ge hD
  rcases exists_nonzero_kraus_of_isIrreducibleTensor
      (A := A) hIrr hD' with ⟨i, hi⟩
  exact hi (hzero i)


/-!
## Unconditional arbitrary-input continuations

The last unconditional arbitrary-input step currently available here is the blockwise PF / TP-gauge
continuation below: after decomposing `A` into irreducible blocks, one may continue on each block
once one separately knows that the block has a nonzero Kraus operator. This explicit side condition
is essential because, under the current `SameMPV₂` relation, zero scalar blocks cannot simply be
discarded: the `N = 0` sector is remembered.

The newer normal-canonical-form packaging file packages a later stage once one already has
a primitive weighted block family with positive bond dimensions and distinct nonzero weights. This
file does **not** currently construct that input from an arbitrary tensor.

Remaining gap for a full end-to-end canonical-form existence theorem:

* Apply the irreducible-to-TP-gauge theorem blockwise through the irreducible block decomposition
  while handling possible zero blocks exactly.
* Apply the TP-irreducible-to-primitive blocking theorem and then perform the post-blocking cyclic
  sector and equal-weight arguments needed for strict nonzero weight ordering.
* Use the resulting data to reach the stronger normal / injective-by-blocking hypotheses needed by
  the later normal-canonical-form packaging lemmas and the downstream `IsCanonicalForm` builders.
-/

/-- **Unconditional TP-gauge continuation for the 1606 reduction (1606.00608 §2.3 + App. A).**

From an arbitrary tensor `A` we produce an irreducible block decomposition. Moreover, for each
resulting block, if one separately knows that the block has some nonzero Kraus operator, then the
Perron--Frobenius / TP-gauge step can be applied to that block.

This is the next unconditional continuation from arbitrary input under the
current API. The nonzero side condition is explicit because `SameMPV₂`
remembers the `N = 0` sector, so zero scalar blocks cannot be silently
discarded. -/
theorem exists_irreducible_blockDecomp_with_tpGauge
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
    exists_irreducible_blockDecomp (d := d) (D := D) A
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
    (exists_tp_data_of_irreducible (d := d) (D := dim k)
      (A := blocks k) (hIrr := hIrr k) (hA := hNonzero))

/-- **Legacy CFII continuation for the 1606 reduction (1606.00608 §2.3 + App. A).**

From an arbitrary tensor `A` we produce an irreducible block decomposition. Moreover, for each
block, assuming one has already supplied (i) a TP representative and (ii) positive bond dimension,
we can produce CFII fixed-point data (unitary conjugation + diagonal PD fixed point).

This is an optional Appendix-A side branch, not a near-final theorem: it does not thread the PF
/ TP-gauge or periodicity-removal steps through the block decomposition. Later packaging into
normal canonical form, once primitive weighted blocks are already in hand, lives in the later
normal-canonical-form packaging file. -/
theorem exists_irreducible_blockDecomp_with_CFII
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
    exists_irreducible_blockDecomp (d := d) (D := D) A
  refine ⟨r, dim, blocks, hIrr, hSame, ?_⟩
  intro k hTPk hDk
  -- Apply the packaged CFII lemma to the k-th block.
  simpa using
    (exists_CFII_data_of_TP_of_isIrreducibleTensor (d := d) (D := dim k)
      (A := blocks k) (hTP := hTPk) (hIrr := hIrr k) (hD := hDk))

/-!
## Zero-block separation (1606.00608 §2.3: partition into zero tail + nonzero blocks)

The irreducible block decomposition may produce all-zero blocks. Because `SameMPV₂`
at `N = 0` includes the identity `trace(I_D) = D`, we cannot silently drop these.
Instead we accumulate them into a **zero tail** of dimension `zeroTailDim` (the sum
of their bond dimensions) and retain a family of **nonzero blocks** (each having at
least one nonzero Kraus operator).

Key facts:
- All-zero irreducible blocks have `dim ≤ 1` (`isIrreducibleTensor_allZero_dim_le_one`).
- For `N > 0`, all-zero blocks contribute `0` to the MPV (`mpv_eq_zero_of_all_zero`).
- For `N = 0`, each block of dimension `Dₖ` contributes `Dₖ` (the trace of the identity).

The zero tail is represented as a single all-zero tensor of dimension `zeroTailDim`; its MPV is
`zeroTailDim` at `N = 0` and `0` for `N > 0`.
-/

/-- The all-zero MPS tensor of given physical and bond dimension.

Every Kraus operator is the zero matrix. At `N = 0`, its mpv equals the bond dimension (the trace
of the identity); at `N > 0`, its mpv is `0`. -/
def zeroMPSTensor (d D : ℕ) : MPSTensor d D := fun _ => 0

theorem mpv_zeroMPSTensor {N : ℕ} (σ : Fin N → Fin d') (D' : ℕ) :
    mpv (zeroMPSTensor d' D') σ = if N = 0 then (D' : ℂ) else 0 := by
  split
  case isTrue hN =>
    subst hN
    simp [mpv, coeff, Matrix.trace_one]
  case isFalse hN =>
    have hpos : 0 < N := Nat.pos_of_ne_zero hN
    exact mpv_eq_zero_of_all_zero (zeroMPSTensor d' D')
      (fun _ => rfl) σ hpos

/-- At `N = 0`, the mpv of an arbitrary tensor `A : MPSTensor d D` on the unique
spin configuration `σ : Fin 0 → Fin d` equals `(D : ℂ)` (the trace of the identity). -/
private theorem mpv_eq_dim_at_zero (A : MPSTensor d' D') (σ : Fin 0 → Fin d') :
    mpv A σ = (D' : ℂ) := by
  simp [mpv, coeff, Matrix.trace_one]

/-- **Zero-block separation (1606.00608 §2.3).**

Every MPS tensor `A : MPSTensor d D` admits an irreducible block decomposition that faithfully
partitioned into:

* a **zero tail** of dimension `zeroTailDim` (accumulating all-zero irreducible blocks), and
* a family of **nonzero blocks** `blocks k : MPSTensor d (dim k)` for `k : Fin r`, each with at
  least one nonzero Kraus operator, positive bond dimension, and irreducibility.

The MPV relationship is:

  `mpv A σ = mpv (zeroMPSTensor d zeroTailDim) σ + mpv (toTensorFromBlocks μ≡1 blocks) σ`

which at `N = 0` reduces to `D = zeroTailDim + ∑ k, dim k` and at `N > 0` reduces to
`mpv A σ = mpv (toTensorFromBlocks μ≡1 blocks) σ` (zero tail vanishes).

This separation is **exact**: the zero tail is not silently discarded, and the length-zero
identity is preserved. -/
theorem exists_irreducible_blockDecomp_nonzeroBlocks (A : MPSTensor d D) :
    ∃ (zeroTailDim : ℕ) (r : ℕ) (dim : Fin r → ℕ)
      (blocks : (k : Fin r) → MPSTensor d (dim k)),
      (∀ k, IsIrreducibleTensor (blocks k)) ∧
      (∀ k, ∃ i, blocks k i ≠ 0) ∧
      (∀ k, 0 < dim k) ∧
      (∀ (N : ℕ) (σ : Fin N → Fin d),
        mpv A σ = mpv (zeroMPSTensor d zeroTailDim) σ +
          mpv (toTensorFromBlocks (d := d) (μ := fun _ : Fin r => (1 : ℂ)) blocks) σ) := by
  classical
  -- Step 1: Obtain the irreducible block decomposition.
  obtain ⟨r₀, dim₀, blocks₀, hIrr₀, hSame₀⟩ :=
    exists_irreducible_blockDecomp (d := d) (D := D) A
  -- Step 2: Classify blocks as "live" or "zero".
  -- Use `set` to avoid `let ... in` scoping issues with big-operator notation.
  set isLive : Fin r₀ → Prop := fun k => ∃ i, blocks₀ k i ≠ 0 with isLive_def
  set liveSet : Finset (Fin r₀) := Finset.univ.filter (fun k => isLive k) with liveSet_def
  set zeroSet : Finset (Fin r₀) := Finset.univ.filter (fun k => ¬ isLive k) with zeroSet_def
  -- The zero tail dimension is the sum of bond dimensions of zero blocks.
  set zeroTailDim : ℕ := zeroSet.sum dim₀ with zeroTailDim_def
  -- Reindex nonzero blocks via a bijection with `Fin liveSet.card`.
  set liveEquiv : liveSet ≃ Fin liveSet.card := liveSet.equivFin with liveEquiv_def
  -- Define the new live block family.
  set r := liveSet.card with r_def
  set dim : Fin r → ℕ := fun j => dim₀ (liveEquiv.symm j).1 with dim_def
  set newBlocks : (k : Fin r) → MPSTensor d (dim k) :=
    fun j => blocks₀ (liveEquiv.symm j).1 with newBlocks_def
  -- Step 3: Prove all properties.
  refine ⟨zeroTailDim, r, dim, newBlocks, ?_, ?_, ?_, ?_⟩
  -- (a) Irreducibility of nonzero blocks.
  · intro k
    exact hIrr₀ (liveEquiv.symm k).1
  -- (b) Each live block has a nonzero Kraus operator.
  · intro k
    have hMem := (liveEquiv.symm k).2
    -- `(liveEquiv.symm k).1 ∈ liveSet` means `isLive (liveEquiv.symm k).1`.
    have hLive : isLive (liveEquiv.symm k).1 :=
      (Finset.mem_filter.mp hMem).2
    exact hLive
  -- (c) Each live block has positive bond dimension.
  · intro k
    have hMem := (liveEquiv.symm k).2
    have hLive : isLive (liveEquiv.symm k).1 :=
      (Finset.mem_filter.mp hMem).2
    rcases hLive with ⟨i, hi⟩
    by_contra h
    push Not at h
    have hd0 : dim k = 0 := Nat.le_zero.mp h
    have hEmpty : IsEmpty (Fin (dim k)) := by rw [hd0]; infer_instance
    have hzero : newBlocks k i = 0 := by ext a b; exact (hEmpty.false a).elim
    exact hi hzero
  -- (d) MPV relationship.
  · intro N σ
    -- Expand A's MPV via the original decomposition.
    have hA : mpv A σ = ∑ k : Fin r₀, mpv (blocks₀ k) σ := by
      have h := hSame₀ N σ
      rw [h, mpv_toTensorFromBlocks_eq_sum]
      simp only [one_pow, one_smul]
    -- Expand the live-block toTensorFromBlocks.
    have hLive : mpv (toTensorFromBlocks (d := d) (μ := fun _ : Fin r => (1 : ℂ)) newBlocks) σ =
        ∑ j : Fin r, mpv (newBlocks j) σ := by
      rw [mpv_toTensorFromBlocks_eq_sum]
      simp only [one_pow, one_smul]
    -- Split the original sum into live and zero parts.
    have hDisj : Disjoint liveSet zeroSet := by
      simp only [liveSet_def, zeroSet_def]
      exact Finset.disjoint_filter_filter_not _ _ _
    have hUnion : liveSet ∪ zeroSet = Finset.univ := by
      simp only [liveSet_def, zeroSet_def]
      ext k
      simp [Finset.mem_filter, Finset.mem_union, em]
    have hSplit : ∑ k : Fin r₀, mpv (blocks₀ k) σ =
        liveSet.sum (fun k => mpv (blocks₀ k) σ) +
          zeroSet.sum (fun k => mpv (blocks₀ k) σ) := by
      rw [← Finset.sum_union hDisj, hUnion]
    -- The nonzero-block sum equals ∑ over the reindexed blocks.
    have hLiveSum : liveSet.sum (fun k => mpv (blocks₀ k) σ) =
        ∑ j : Fin r, mpv (newBlocks j) σ := by
      rw [← liveSet.sum_coe_sort (fun k => mpv (blocks₀ k) σ)]
      exact (liveEquiv.symm.sum_comp (fun x : liveSet => mpv (blocks₀ x.1) σ)).symm
    -- The zero sum: at N > 0, each zero block contributes 0; at N = 0, it contributes dim.
    have hZeroSum : zeroSet.sum (fun k => mpv (blocks₀ k) σ) =
        if N = 0 then (zeroTailDim : ℂ) else 0 := by
      split
      case isTrue hN =>
        subst hN
        -- Each block contributes `dim₀ k` at N=0 (trace of identity).
        have : zeroSet.sum (fun k => mpv (blocks₀ k) σ) =
            zeroSet.sum (fun k => (dim₀ k : ℂ)) :=
          Finset.sum_congr rfl (fun k _ => mpv_eq_dim_at_zero (blocks₀ k) σ)
        rw [this, ← Nat.cast_sum]
      case isFalse hN =>
        apply Finset.sum_eq_zero
        intro k hk
        have hkz : ∀ i, blocks₀ k i = 0 := by
          by_contra hne
          push Not at hne
          have hkLive : k ∈ liveSet :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ k, hne⟩
          exact absurd hkLive (Finset.disjoint_right.mp hDisj hk)
        exact mpv_eq_zero_of_all_zero (blocks₀ k) hkz σ (Nat.pos_of_ne_zero hN)
    -- Expand the zero-tail MPV.
    have hZeroTail : mpv (zeroMPSTensor d zeroTailDim) σ =
        if N = 0 then (zeroTailDim : ℂ) else 0 :=
      mpv_zeroMPSTensor σ zeroTailDim
    -- Chain everything together.
    rw [hA, hSplit, hLiveSum, hZeroSum, hZeroTail, hLive, add_comm]

end MPSTensor
