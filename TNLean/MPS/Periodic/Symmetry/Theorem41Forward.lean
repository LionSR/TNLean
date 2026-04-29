/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.Periodic.Symmetry.Theorem41Defs

/-!
# Theorem 4.1, forward direction

This module contains the forward half of Theorem 4.1 together with the pullback
lemmas used in its current conditional formalization.
-/

open scoped Matrix BigOperators

namespace MPSTensor

/-! ## Theorem 4.1 — forward direction (`p`-refinability ⇒ `p`-divisibility) -/

section Theorem41Forward

variable {d D : ℕ}

/-- **Rectangular Kraus isometry mixing.**

For a (possibly rectangular) isometry `W : Fin m → Fin d` with `Wᴴ · W = 1`,
the `W`-pullback family `C τ := ∑_σ W(τ, σ) · B σ` has the same transfer map
as `B`. This is an adapter from
`kraus_same_map_of_isometry_combination` to the `MPSTensor.transferMap` API. -/
theorem transferMap_kraus_isometry
    {m : ℕ} (B : MPSTensor d D)
    (W : Matrix (Fin m) (Fin d) ℂ) (hW : Wᴴ * W = 1) :
    transferMap (fun τ : Fin m => ∑ σ : Fin d, W τ σ • B σ) = transferMap B := by
  ext X : 1
  simpa [transferMap_apply] using
    kraus_same_map_of_isometry_combination
      (K := fun τ : Fin m => ∑ σ : Fin d, W τ σ • B σ)
      (K' := B) W hW (fun _ => rfl) X

/-- Evaluation of a `W`-pulled-back tensor on a blocked word is a `W`-weighted sum
of evaluations of the original tensor.

If `C τ = ∑_σ W(τ, σ) • B σ` is the isometric mixing of an MPS tensor
`B : MPSTensor d D` by `W : Matrix (Fin m) (Fin d) ℂ`, then for every `N` and
every `τ : Fin N → Fin m`,
`evalWord C (List.ofFn τ) = ∑_σ (∏_k W (τ k) (σ k)) • evalWord B (List.ofFn σ)`.

This is the coefficient-expansion identity used in both directions of Theorem 4.1:
in the forward direction it rewrites a refinement witness as `SameMPV` for the
`W`-pullback tensor, and in the reverse direction it expands the blocked witness
produced by Wolf Theorem 2.18. -/
theorem evalWord_sum_smul_ofFn
    {m : ℕ} (B : MPSTensor d D) (W : Matrix (Fin m) (Fin d) ℂ) :
    ∀ (N : ℕ) (τ : Fin N → Fin m),
      evalWord (fun τ' : Fin m => ∑ σ' : Fin d, W τ' σ' • B σ') (List.ofFn τ) =
        ∑ σ : Fin N → Fin d,
          (∏ k : Fin N, W (τ k) (σ k)) • evalWord B (List.ofFn σ) := by
  intro N
  induction N with
  | zero =>
      intro τ
      classical
      simp
  | succ N ih =>
      intro τ
      classical
      rw [List.ofFn_succ, evalWord_cons]
      rw [ih (fun i : Fin N => τ i.succ)]
      rw [Finset.sum_mul_sum]
      let eqv : (Fin d × (Fin N → Fin d)) ≃ (Fin (N + 1) → Fin d) :=
        Fin.consEquiv (fun _ => Fin d)
      have hreindex :
          (∑ σ : Fin (N + 1) → Fin d,
              (∏ k : Fin (N + 1), W (τ k) (σ k)) • evalWord B (List.ofFn σ)) =
            ∑ p : Fin d × (Fin N → Fin d),
              (∏ k : Fin (N + 1), W (τ k) ((eqv p) k)) • evalWord B (List.ofFn (eqv p)) :=
        (Fintype.sum_equiv eqv
          (f := fun p : Fin d × (Fin N → Fin d) =>
            (∏ k : Fin (N + 1), W (τ k) ((eqv p) k)) • evalWord B (List.ofFn (eqv p)))
          (g := fun σ : Fin (N + 1) → Fin d =>
            (∏ k : Fin (N + 1), W (τ k) (σ k)) • evalWord B (List.ofFn σ))
          (by intro p; rfl)).symm
      rw [hreindex, ← Fintype.sum_prod_type']
      refine Finset.sum_congr rfl ?_
      rintro ⟨i, σt⟩ _
      have hprod :
          (∏ k : Fin (N + 1), W (τ k) ((eqv (i, σt)) k)) =
            W (τ 0) i * ∏ k : Fin N, W (τ k.succ) (σt k) := by
        rw [Fin.prod_univ_succ]
        simp [eqv, Fin.consEquiv]
      have hList :
          List.ofFn (eqv (i, σt)) = i :: List.ofFn σt := by
        simp [eqv, Fin.consEquiv]
      rw [hprod, hList, evalWord_cons, smul_mul_smul_comm]

private theorem mpv_sum_smul_ofFn
    {m : ℕ} (B : MPSTensor d D) (W : Matrix (Fin m) (Fin d) ℂ)
    (N : ℕ) (τ : Fin N → Fin m) :
    mpv (fun τ' : Fin m => ∑ σ' : Fin d, W τ' σ' • B σ') τ =
      ∑ σ : Fin N → Fin d,
        (∏ k : Fin N, W (τ k) (σ k)) * coeff B (List.ofFn σ) := by
  simp [mpv_eq, coeff_eq, evalWord_sum_smul_ofFn, Matrix.trace_sum, Matrix.trace_smul]

/-- Physical-index mixing by a fixed matrix preserves `SameMPV₂`. -/
theorem sameMPV₂_sum_smul_ofFn
    {m D₁ D₂ : ℕ} (A : MPSTensor d D₁) (B : MPSTensor d D₂)
    (W : Matrix (Fin m) (Fin d) ℂ)
    (hAB : SameMPV₂ A B) :
    SameMPV₂
      (fun τ : Fin m => ∑ σ : Fin d, W τ σ • A σ)
      (fun τ : Fin m => ∑ σ : Fin d, W τ σ • B σ) := by
  intro N τ
  calc
    mpv (fun τ' : Fin m => ∑ σ' : Fin d, W τ' σ' • A σ') τ =
        ∑ σ : Fin N → Fin d,
          (∏ k : Fin N, W (τ k) (σ k)) * coeff A (List.ofFn σ) := by
          exact mpv_sum_smul_ofFn A W N τ
    _ = ∑ σ : Fin N → Fin d,
          (∏ k : Fin N, W (τ k) (σ k)) * coeff B (List.ofFn σ) := by
          refine Finset.sum_congr rfl ?_
          intro σ _
          simpa [mpv_eq, coeff_eq] using
            congrArg
              (fun z : ℂ => (∏ k : Fin N, W (τ k) (σ k)) * z)
              (hAB N σ)
    _ = mpv (fun τ' : Fin m => ∑ σ' : Fin d, W τ' σ' • B σ') τ := by
          symm
          exact mpv_sum_smul_ofFn B W N τ

/-- A physical-index isometry preserves left-canonicality. -/
theorem isLeftCanonical_kraus_isometry
    {m : ℕ} (B : MPSTensor d D)
    (W : Matrix (Fin m) (Fin d) ℂ) (hW : Wᴴ * W = 1)
    (hB : IsLeftCanonical B) :
    IsLeftCanonical (fun τ : Fin m => ∑ σ : Fin d, W τ σ • B σ) := by
  let C : MPSTensor m D := fun τ => ∑ σ : Fin d, W τ σ • B σ
  have hCh : IsChannel (transferMap C) := by
    have hEq : transferMap C = transferMap B := by
      simpa [C] using transferMap_kraus_isometry B W hW
    simpa [hEq] using transferMap_isChannel B hB
  simpa [C] using
    kraus_sum_conjTranspose_mul_of_tp C (transferMap C)
      (fun X => by simp [transferMap_apply]) hCh.tp

/-- A physical-index isometry preserves periodicity and its period. -/
theorem isPeriodic_kraus_isometry
    {m p : ℕ} (B : MPSTensor d D)
    (W : Matrix (Fin m) (Fin d) ℂ) (hW : Wᴴ * W = 1)
    (hB : IsPeriodic p B) :
    IsPeriodic p (fun τ : Fin m => ∑ σ : Fin d, W τ σ • B σ) := by
  let C : MPSTensor m D := fun τ => ∑ σ : Fin d, W τ σ • B σ
  have hEq : transferMap C = transferMap B := by
    simpa [C] using transferMap_kraus_isometry B W hW
  have hIrrMapB : IsIrreducibleMap (transferMap B) :=
    isIrreducibleMap_of_isIrreducibleTensor B hB.irreducible
  have hIrrMapC : IsIrreducibleMap (transferMap C) := by
    simpa [hEq] using hIrrMapB
  refine ⟨isIrreducibleTensor_of_isIrreducibleMap C hIrrMapC,
    isLeftCanonical_kraus_isometry B W hW hB.leftCanonical,
    hB.period_pos, ?_, hB.primitiveRoot⟩
  simpa [C, hEq] using hB.peripheral_eq

private theorem sameMPV₂_toTensorFromBlocks_sum_smul_ofFn
    {m r : ℕ} {dim : Fin r → ℕ}
    (μ : Fin r → ℂ)
    (blocks : (k : Fin r) → MPSTensor d (dim k))
    (W : Matrix (Fin m) (Fin d) ℂ) :
    SameMPV₂
      (fun τ : Fin m => ∑ σ : Fin d, W τ σ •
        toTensorFromBlocks (d := d) (μ := μ) blocks σ)
      (toTensorFromBlocks (d := m) (μ := μ)
        (fun k : Fin r => fun τ : Fin m => ∑ σ : Fin d, W τ σ • blocks k σ)) := by
  intro N τ
  calc
    mpv (fun τ' : Fin m => ∑ σ' : Fin d, W τ' σ' •
        toTensorFromBlocks (d := d) (μ := μ) blocks σ') τ =
        ∑ σ : Fin N → Fin d,
          (∏ k : Fin N, W (τ k) (σ k)) *
            mpv (toTensorFromBlocks (d := d) (μ := μ) blocks) σ := by
          simpa [mpv_eq, coeff_eq] using
            mpv_sum_smul_ofFn (B := toTensorFromBlocks (d := d) (μ := μ) blocks) W N τ
    _ = ∑ σ : Fin N → Fin d,
          (∏ k : Fin N, W (τ k) (σ k)) *
            ∑ j : Fin r, (μ j) ^ N * mpv (blocks j) σ := by
          refine Finset.sum_congr rfl ?_
          intro σ _
          rw [mpv_toTensorFromBlocks_eq_sum]
          simp only [smul_eq_mul]
    _ = ∑ σ : Fin N → Fin d,
          ∑ j : Fin r,
            (∏ k : Fin N, W (τ k) (σ k)) *
              ((μ j) ^ N * mpv (blocks j) σ) := by
          simp_rw [Finset.mul_sum]
    _ = ∑ j : Fin r,
          ∑ σ : Fin N → Fin d,
            (∏ k : Fin N, W (τ k) (σ k)) *
              ((μ j) ^ N * mpv (blocks j) σ) := by
          rw [Finset.sum_comm]
    _ = ∑ j : Fin r,
          (μ j) ^ N *
            ∑ σ : Fin N → Fin d,
              (∏ k : Fin N, W (τ k) (σ k)) * mpv (blocks j) σ := by
          refine Finset.sum_congr rfl ?_
          intro j _
          calc
            ∑ σ : Fin N → Fin d,
                (∏ k : Fin N, W (τ k) (σ k)) *
                  ((μ j) ^ N * mpv (blocks j) σ)
                = ∑ σ : Fin N → Fin d,
                    (μ j) ^ N *
                      ((∏ k : Fin N, W (τ k) (σ k)) * mpv (blocks j) σ) := by
                    refine Finset.sum_congr rfl ?_
                    intro σ _
                    simp [mul_assoc, mul_comm]
            _ = (μ j) ^ N *
                  ∑ σ : Fin N → Fin d,
                    (∏ k : Fin N, W (τ k) (σ k)) * mpv (blocks j) σ := by
                    rw [← Finset.mul_sum]
    _ = ∑ j : Fin r,
          (μ j) ^ N *
            mpv (fun τ' : Fin m => ∑ σ' : Fin d, W τ' σ' • blocks j σ') τ := by
          refine Finset.sum_congr rfl ?_
          intro j _
          congr 1
          symm
          simpa [mpv_eq, coeff_eq] using mpv_sum_smul_ofFn (B := blocks j) W N τ
    _ = mpv (toTensorFromBlocks (d := m) (μ := μ)
          (fun k : Fin r => fun τ' : Fin m => ∑ σ : Fin d, W τ' σ • blocks k σ)) τ := by
          symm
          rw [mpv_toTensorFromBlocks_eq_sum]
          simp only [smul_eq_mul]

/-- A physical-index isometry preserves irreducible form II. -/
noncomputable def isIrreducibleForm_kraus_isometry
    {m : ℕ} (B : MPSTensor d D)
    (W : Matrix (Fin m) (Fin d) ℂ) (hW : Wᴴ * W = 1)
    (hB : IsIrreducibleForm B) :
    IsIrreducibleForm (fun τ : Fin m => ∑ σ : Fin d, W τ σ • B σ) := by
  refine
    { r := hB.r
      dim := hB.dim
      blocks := fun k : Fin hB.r =>
        fun τ : Fin m => ∑ σ : Fin d, W τ σ • hB.blocks k σ
      μ := hB.μ
      period := hB.period
      periodic := ?_
      weight_pos := hB.weight_pos
      sameMPV := ?_ }
  · intro k
    exact isPeriodic_kraus_isometry (B := hB.blocks k) W hW (hB.periodic k)
  · have hPullbackSame :
        SameMPV₂
          (fun τ : Fin m => ∑ σ : Fin d, W τ σ • B σ)
          (fun τ : Fin m => ∑ σ : Fin d, W τ σ •
            toTensorFromBlocks (d := d) (μ := hB.μ) hB.blocks σ) :=
        sameMPV₂_sum_smul_ofFn B
          (toTensorFromBlocks (d := d) (μ := hB.μ) hB.blocks) W hB.sameMPV
    have hBlocksSame :
        SameMPV₂
          (fun τ : Fin m => ∑ σ : Fin d, W τ σ •
            toTensorFromBlocks (d := d) (μ := hB.μ) hB.blocks σ)
          (toTensorFromBlocks (d := m) (μ := hB.μ)
            (fun k : Fin hB.r => fun τ : Fin m => ∑ σ : Fin d, W τ σ • hB.blocks k σ)) :=
        sameMPV₂_toTensorFromBlocks_sum_smul_ofFn hB.μ hB.blocks W
    intro N τ
    exact (hPullbackSame N τ).trans (hBlocksSame N τ)

/-- **Pullback stage of the forward canonicalization roadmap for Theorem 4.1.**

From a `p`-refinement witness `(A, W)` for `B`, the `W`-pullback tensor
`C τ := ∑_σ W(τ, σ) • B σ` has the same transfer map as `B` and the same MPV
family as `blockTensor A p`.

This proves the first three steps of the forward-direction condition
`PRefinementCanonicalization`: construct the pullback, identify its transfer map
using `transferMap_kraus_isometry`, and rewrite the coefficient-level refinement
identity as a `SameMPV` statement. The remaining gap is therefore exactly the
periodic equal-case / canonical-gauge reduction from this `SameMPV` statement to
a left-canonical root witness. -/
theorem pRefinementCanonicalization_pullback
    (B : MPSTensor d D) (p : ℕ)
    (hRefine : IsPRefinable B p) :
    ∃ (A : MPSTensor d D)
      (W : Matrix (Fin (blockPhysDim d p)) (Fin d) ℂ),
      Wᴴ * W = 1 ∧
      transferMap (fun τ : Fin (blockPhysDim d p) => ∑ σ : Fin d, W τ σ • B σ) =
        transferMap B ∧
      SameMPV (fun τ : Fin (blockPhysDim d p) => ∑ σ : Fin d, W τ σ • B σ)
        (blockTensor A p) := by
  rcases hRefine with ⟨A, W, hW, hCoeff⟩
  refine ⟨A, W, hW, transferMap_kraus_isometry B W hW, ?_⟩
  intro N τ
  calc
    mpv (fun τ' : Fin (blockPhysDim d p) => ∑ σ' : Fin d, W τ' σ' • B σ') τ =
        ∑ σ : Fin N → Fin d,
          (∏ k : Fin N, W (τ k) (σ k)) * coeff B (List.ofFn σ) := by
          simp [mpv_eq, coeff_eq, evalWord_sum_smul_ofFn, Matrix.trace_sum, Matrix.trace_smul]
    _ = mpv (blockTensor A p) τ := by
          simpa [mpv_eq] using (hCoeff N τ).symm

/-- **Pullback stage with irreducible-form input for Theorem 4.1.**

If the refined tensor `B` is already in irreducible form II, then the pullback
`C τ := ∑_σ W(τ, σ) • B σ` coming from a `p`-refinement witness is again in
irreducible form II, has the same transfer map as `B`, and has the same MPV
family as `blockTensor A p`. This isolates the genuinely new input now
available on `main`: the first stage of the paper's proof preserves the
periodic block structure of `B`; the remaining forward-direction gap is the
blocked equal-case / root-reconstruction stage after this theorem. -/
theorem pRefinementCanonicalization_pullback_of_irreducibleForm
    (B : MPSTensor d D) (hB : IsIrreducibleForm B) (p : ℕ)
    (hRefine : IsPRefinable B p) :
    ∃ (A : MPSTensor d D)
      (W : Matrix (Fin (blockPhysDim d p)) (Fin d) ℂ)
      (_ : IsIrreducibleForm
        (fun τ : Fin (blockPhysDim d p) => ∑ σ : Fin d, W τ σ • B σ)),
      Wᴴ * W = 1 ∧
      transferMap (fun τ : Fin (blockPhysDim d p) => ∑ σ : Fin d, W τ σ • B σ) =
        transferMap B ∧
      SameMPV (fun τ : Fin (blockPhysDim d p) => ∑ σ : Fin d, W τ σ • B σ)
        (blockTensor A p) := by
  obtain ⟨A, W, hW, hTransfer, hSame⟩ :=
    pRefinementCanonicalization_pullback B p hRefine
  exact ⟨A, W, isIrreducibleForm_kraus_isometry B W hW hB, hW, hTransfer, hSame⟩

/-- **Theorem 4.1, forward direction (witness-based form).**

If we can produce a witness `A : MPSTensor d D` for the `p`-refinement of `B`
satisfying *both* left-canonical normalization (`∑ᵢ Aᵢᴴ · Aᵢ = 1`, so that the
transfer map `E_A` is a CPTP channel) *and* the channel-level matching
`E_B = E_{A^{[p]}}`, then `E_B` is `p`-divisible: concretely, it equals
`(E_A)^p`.

The proof combines the channel-level blocking identity `E_{A^{[p]}} = (E_A)^p`
(`MPSTensor.transferMap_blockTensor`) with the left-canonical channel property
`MPSTensor.transferMap_isChannel`. The bridging from the raw coefficient-level
`IsPRefinable B p` hypothesis to this witness is handled in
`thm_4_1_p_refinement_forward` below. -/
theorem thm_4_1_p_refinement_forward_witness
    (B : MPSTensor d D) (p : ℕ)
    (A : MPSTensor d D)
    (hA_norm : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hTransferEq : transferMap B = transferMap (blockTensor A p)) :
    IsPDivisibleChannel (transferMap B) p :=
  ⟨transferMap A, transferMap_isChannel A hA_norm, by
    rw [hTransferEq, transferMap_blockTensor]⟩

/-- **Blocked Z-gauge extraction for the periodic equal-case stage.**

This Prop isolates the existence half of the blocked equal-case argument needed
for Theorem 4.1: whenever an irreducible-form blocked tensor `C` has the same
MPV family as a blocked root `blockTensor A p`, one can extract a periodic
`Z`-gauge witness between `C` and `blockTensor A p`.

Compared with `PeripheralEqualCasePeriodicFTOfSameMPV`, this does **not** yet
recover a left-canonical root. It only asserts the blocked equal-case
Fundamental Theorem / Z-phase existence step. -/
def PeripheralEqualCaseZGaugeOfSameMPV (d D p : ℕ) : Prop :=
  ∀ {A : MPSTensor d D} {C : MPSTensor (blockPhysDim d p) D},
    IsIrreducibleForm C →
    SameMPV C (blockTensor A p) →
      ∃ m : ℕ, 0 < m ∧ ZGaugeEquiv m C (blockTensor A p)

/-- **Blocked-to-root reconstruction from a periodic `Z`-gauge witness.**

This Prop isolates the second half of the blocked equal-case argument: once a
blocked tensor `C` is related to `blockTensor A p` by a periodic `Z`-gauge,
one can distribute that blocked phase data across a root tensor `A'` so that
`A'` is left-canonical and `E_C = E_{A'^{[p]}}`.

In the paper this is the blocked-to-root phase-distribution step after the
periodic equal-case Fundamental Theorem. -/
def PeripheralEqualCaseRootFromZGauge (d D p : ℕ) : Prop :=
  ∀ {A : MPSTensor d D} {C : MPSTensor (blockPhysDim d p) D} {m : ℕ},
    IsIrreducibleForm C →
    0 < m →
    ZGaugeEquiv m C (blockTensor A p) →
      ∃ A' : MPSTensor d D,
        (∑ i : Fin d, (A' i)ᴴ * A' i = 1) ∧
        transferMap C = transferMap (blockTensor A' p)

/-- **Blocked equal-case/root-reconstruction hypothesis for Theorem 4.1.**

This Prop isolates exactly the remaining forward input after
`pRefinementCanonicalization_pullback_of_irreducibleForm`: whenever an
irreducible-form blocked tensor `C` has the same MPV family as a blocked root
`blockTensor A p`, one can replace `A` by a left-canonical root `A'` with the
same blocked transfer map, `E_C = E_{A'^{[p]}}`.

In the paper this is the point where the blocked equal-case Fundamental Theorem
(Theorem 3.8 of arXiv:1708.00029) is combined with the blocked-to-root
reconstruction that distributes the resulting `Z`-gauge across the cyclic
sectors of `A`. Formalizing that existence step is the remaining forward
obstruction, so we keep the resulting existence statement as a separate hypothesis. The theorem
`peripheralEqualCase_periodicFT_of_sameMPV` below shows that this statement
follows from the sharper split into blocked `Z`-gauge extraction and
blocked-to-root reconstruction. -/
def PeripheralEqualCasePeriodicFTOfSameMPV (d D p : ℕ) : Prop :=
  ∀ {A : MPSTensor d D} {C : MPSTensor (blockPhysDim d p) D},
    IsIrreducibleForm C →
    SameMPV C (blockTensor A p) →
      ∃ A' : MPSTensor d D,
        (∑ i : Fin d, (A' i)ᴴ * A' i = 1) ∧
        transferMap C = transferMap (blockTensor A' p)

/-- **Blocked equal-case continuation from Z-gauge extraction and reconstruction.**

If we can first extract a blocked periodic `Z`-gauge from
`SameMPV C (blockTensor A p)` and then distribute that blocked `Z`-phase back
to a left-canonical root, then the continuation hypothesis
`PeripheralEqualCasePeriodicFTOfSameMPV` holds.

This splits the blocked equal-case continuation into two explicit obligations:
the blocked equal-case `Z`-gauge existence step and the subsequent
blocked-to-root reconstruction. -/
theorem peripheralEqualCase_periodicFT_of_sameMPV
    (hZGauge : PeripheralEqualCaseZGaugeOfSameMPV d D p)
    (hRoot : PeripheralEqualCaseRootFromZGauge d D p) :
    PeripheralEqualCasePeriodicFTOfSameMPV d D p := by
  intro A C hC hSame
  obtain ⟨m, hm, hZ⟩ := hZGauge (A := A) (C := C) hC hSame
  exact hRoot (A := A) (C := C) (m := m) hC hm hZ

/-- **Canonicalization hypothesis for the forward direction of Theorem 4.1.**

This Prop states the analytic content that remains between the
coefficient-level `IsPRefinable B p` (a trace-level MPV identity) and the
channel-level conclusion needed to exhibit `E_B` as a `p`-th power: any
`p`-refinement of `B` can be *canonicalized* to a witness that is both
left-canonical and produces a matching transfer map under `p`-blocking.

Morally, the canonicalization is produced as follows. Given a witness
`(A, W)` from `IsPRefinable B p`, form the `W`-pullback tensor
`C τ := ∑_σ W(τ, σ) · B σ`. The theorems
`pRefinementCanonicalization_pullback` and
`pRefinementCanonicalization_pullback_of_irreducibleForm` now cover this
first stage, giving `E_C = E_B`, `SameMPV C (blockTensor A p)`, and preserving
irreducible form II when `B` already has it. The periodic equal-case
Fundamental Theorem (Theorem 3.8 of arXiv:1708.00029, available here as the
hypothesis `PeriodicEqualCaseFT`) then supplies a `Z`-gauge equivalence
between `C` and `blockTensor A p`, which — combined with a unitary
canonical-form reduction for irreducible form II and Wolf Theorem 2.18 —
produces the sought left-canonical witness. Formalizing this remaining second
stage in Lean still requires infrastructure (canonical unitary gauge, Kraus
uniqueness), so we expose the end-result predicate as a hypothesis. The theorem
`pRefinementCanonicalization_of_peripheralEqualCase_periodicFT_of_sameMPV`
below shows that this coarse hypothesis follows from the sharper blocked-stage
hypothesis `PeripheralEqualCasePeriodicFTOfSameMPV`. -/
def PRefinementCanonicalization (d D p : ℕ) : Prop :=
  ∀ {B : MPSTensor d D}, IsIrreducibleForm B → IsPRefinable B p →
    ∃ A : MPSTensor d D,
      (∑ i : Fin d, (A i)ᴴ * A i = 1) ∧
      transferMap B = transferMap (blockTensor A p)

/-- **Reduction of forward canonicalization to the blocked equal-case stage.**

Assuming `PeripheralEqualCasePeriodicFTOfSameMPV`, the pullback theorem
`pRefinementCanonicalization_pullback_of_irreducibleForm` already yields the
full forward-side canonicalization hypothesis `PRefinementCanonicalization`.
Thus the remaining forward gap in Theorem 4.1 is exactly the blocked
equal-case/root-reconstruction step captured by
`PeripheralEqualCasePeriodicFTOfSameMPV`. -/
theorem pRefinementCanonicalization_of_peripheralEqualCase_periodicFT_of_sameMPV
    (hPeripheralEq : PeripheralEqualCasePeriodicFTOfSameMPV d D p) :
    PRefinementCanonicalization d D p := by
  intro B hB hRefine
  obtain ⟨A, W, hC, _hW, hTransfer, hSame⟩ :=
    pRefinementCanonicalization_pullback_of_irreducibleForm B hB p hRefine
  let C : MPSTensor (blockPhysDim d p) D :=
    fun τ : Fin (blockPhysDim d p) => ∑ σ : Fin d, W τ σ • B σ
  have hC' : IsIrreducibleForm C := by
    simpa [C] using hC
  have hTransfer' : transferMap C = transferMap B := by
    simpa [C] using hTransfer
  have hSame' : SameMPV C (blockTensor A p) := by
    simpa [C] using hSame
  obtain ⟨A', hA'_norm, hTransferA'⟩ := hPeripheralEq (A := A) (C := C) hC' hSame'
  refine ⟨A', hA'_norm, ?_⟩
  calc
    transferMap B = transferMap C := hTransfer'.symm
    _ = transferMap (blockTensor A' p) := hTransferA'

/-- **Forward direction of Theorem 4.1 from the blocked equal-case stage.**

This restates `thm_4_1_p_refinement_forward` after replacing the coarse
hypothesis `PRefinementCanonicalization` by the sharper blocked-stage
hypothesis `PeripheralEqualCasePeriodicFTOfSameMPV`. -/
theorem thm_4_1_p_refinement_forward_of_peripheralEqualCase_periodicFT_of_sameMPV
    (B : MPSTensor d D) (hB : IsIrreducibleForm B)
    (p : ℕ)
    (hPeripheralEq : PeripheralEqualCasePeriodicFTOfSameMPV d D p)
    (hRefine : IsPRefinable B p) :
    IsPDivisibleChannel (transferMap B) p := by
  obtain ⟨A, hA_norm, hTransferEq⟩ :=
    (pRefinementCanonicalization_of_peripheralEqualCase_periodicFT_of_sameMPV
      hPeripheralEq) hB hRefine
  exact thm_4_1_p_refinement_forward_witness B p A hA_norm hTransferEq

/-- **Forward direction of Theorem 4.1 (conditional form).**

Let `B` be an MPS tensor in irreducible form II. Assume
`PRefinementCanonicalization`, which states the remaining analytic passage from
`IsPRefinable B p` to a left-canonical witness with matching transfer map. Then
`IsPRefinable B p` implies `IsPDivisibleChannel (transferMap B) p`.

This follows the same conditional pattern as
`MPSTensor.cor_4_1_physical_symmetry_zgauge`: analytic inputs beyond the
repository's current reach are exposed as explicit hypotheses, while the
algebraic structure — the blocking-commutes-with-power identity and the
left-canonical-channel lemma — is formalized here. -/
theorem thm_4_1_p_refinement_forward
    (B : MPSTensor d D) (hB : IsIrreducibleForm B)
    (p : ℕ)
    (hCanonical : PRefinementCanonicalization d D p)
    (hRefine : IsPRefinable B p) :
    IsPDivisibleChannel (transferMap B) p := by
  obtain ⟨A, hA_norm, hTransferEq⟩ := hCanonical hB hRefine
  exact thm_4_1_p_refinement_forward_witness B p A hA_norm hTransferEq

end Theorem41Forward

end MPSTensor
