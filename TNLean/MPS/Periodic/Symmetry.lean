/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.Periodic.FundamentalTheorem
import TNLean.MPS.FundamentalTheorem.Applications
import TNLean.MPS.Symmetry.Defs
import TNLean.MPS.Core.Blocking
import TNLean.MPS.Core.BlockingTransfer
import TNLean.MPS.Core.CPPrimitive
import TNLean.Channel.Basic
import TNLean.Channel.Peripheral.CyclicDecomposition

/-!
# Periodic MPS — physical symmetries and `p`-refinement (arXiv:1708.00029, §4)

This file formalizes the §4 results of de las Cuevas–Schuch–Pérez-García–Cirac
*Irreducible forms of matrix product states: theory and applications* (arXiv:1708.00029)
for periodic MPS in irreducible form.

## Main results

* `MPSTensor.cor_4_1_physical_symmetry_zgauge` — **Corollary 4.1**: a physical on-site
  symmetry `U : G →* Mat_d ℂ` (acting unitarily) on a tensor `A` in irreducible form II
  lifts, for every `g ∈ G`, to a `Z_m`-gauge equivalence between `A` and the rotated
  tensor `twistedTensor A U g`. The matrix `Z` produced by the periodic equal-case
  Fundamental Theorem satisfies `Z^m = 1` and commutes with each `A^i`; the bond-space
  `Y(g)` is the conjugating gauge.

* `MPSTensor.IsPDivisibleChannel`, `MPSTensor.IsPRefinable` — definitions appearing in
  Theorem 4.1 (`p`-divisibility of the transfer channel and `p`-refinement of an MPS
  tensor). The full equivalence `IsPRefinable B p ↔ IsPDivisibleChannel (transferMap B) p`
  is left to a follow-up PR: it relies on the channel-level identity
  `E_{blockTensor A p} = (transferMap A)^p` (forward direction) and the Stinespring/Kraus
  uniqueness lemma (reverse direction), neither of which is yet available in the repo.

## Status of the dependency on `periodicOverlapDichotomy` (#78 / #81)

The corollary invokes the **periodic equal-case Fundamental Theorem of MPS** (Theorem 3.8
in arXiv:1708.00029, formalized as `fundamentalTheorem_periodic_equalCase` in
`MPS/Periodic/FundamentalTheorem.lean`). That theorem is in turn currently stated as a
direct consumer of `PeriodicOverlapHypothesis`, which can be discharged by
`periodicOverlapDichotomy` (PR #573, follow-ups #607–#609). The dichotomy's proof in
`MPS/Periodic/Overlap.lean` still relies on several admitted sub-lemmas, so this file
follows the established convention (see `Applications.lean`,
`zGaugeEquiv_of_isIrreducibleForm_sameMPV_rotatePhysical`) of taking the equal-case FT
as an explicit hypothesis named `hPeriodicEq`. Callers are free to discharge this
hypothesis by whatever means become available.

## References

* arXiv:1708.00029 §4 (de las Cuevas–Schuch–Pérez-García–Cirac, 2017)
* arXiv:0802.0447 §III (Pérez-García–Wolf–Sanz–Verstraete–Cirac, *Characterizing
  Symmetries in a Projected Entangled Pair State*) — original symmetry corollary in the
  injective case.
* M. M. Wolf, *Quantum Channels & Operations*, Ch. 6.
-/

open scoped Matrix BigOperators

namespace MPSTensor

/-! ## Periodic equal-case Fundamental Theorem stated as a hypothesis -/

section PeriodicEqualCaseFTHyp

variable {d D : ℕ}

/-- The **periodic equal-case Fundamental Theorem of MPS** (Theorem 3.8 of
arXiv:1708.00029) stated as a Prop, suitable for use as an explicit hypothesis.

Given two tensors of the same physical/bond dimensions in irreducible form II that
generate the same matrix-product-vector family, this hypothesis asserts the existence
of a positive period `m` and a `Z_m`-gauge equivalence between the two tensors.

Note that the Lean theorem `fundamentalTheorem_periodic_equalCase` in
`MPS/Periodic/FundamentalTheorem.lean` requires four extra hypotheses beyond
irreducibility and `SameMPV` (non-repetition of blocks for both tensors, the periodic
overlap dichotomy, and a per-block weight-power equality). The Prop introduced here
asserts the *unconditional* equal-case FT, so it is strictly stronger than the current
repo theorem; callers committing to it are committing to the missing analytic content
of `periodicOverlapDichotomy` (#78 / #81). The convention follows the analogous
hypothesis in `MPS/FundamentalTheorem/Applications.lean`. -/
def PeriodicEqualCaseFT (d D : ℕ) : Prop :=
  ∀ {X Y : MPSTensor d D},
    IsIrreducibleForm X → IsIrreducibleForm Y →
    SameMPV X Y →
    ∃ m : ℕ, 0 < m ∧ ZGaugeEquiv m X Y

end PeriodicEqualCaseFTHyp

/-! ## Corollary 4.1 — Physical on-site symmetry → virtual `Z`-gauge -/

section Corollary41

variable {d D : ℕ} {G : Type*} [Group G]

/-- The symmetry-twisted tensor (with `U` acting on the physical leg) coincides with the
physical-index rotation by `U g`. -/
lemma twistedTensor_eq_rotatePhysical
    (A : MPSTensor d D) (U : G →* Matrix (Fin d) (Fin d) ℂ) (g : G) :
    twistedTensor A U g = rotatePhysical (U g) A := rfl

/-- **Corollary 4.1 (arXiv:1708.00029, §4.2): physical symmetry → virtual `Z`-gauge.**

Let `A` be in irreducible form II and let `U : G →* Mat_d ℂ` be a representation of a
group `G` on the physical leg, acting unitarily. If `A` is on-site symmetric under `U`
(i.e. each twisted tensor `twistedTensor A U g` has the same MPV family as `A`), then
for each `g ∈ G` there exists a positive period `m_g` and a `Z_{m_g}`-gauge equivalence
between `A` and `twistedTensor A U g`.

In paper notation, for each `g` there exist matrices `Z_g, Y_g` with `Z_g^{m_g} = 1`,
`[A^i, Z_g] = 0`, and
`Z_g · A^i = Y_g · (twistedTensor A U g)^i · Y_g⁻¹`.

This generalises the single-`u` corollary obtained via
`zGaugeEquiv_of_isIrreducibleForm_sameMPV_rotatePhysical` to a full group of symmetries.
The projective-representation upgrade (joint factor system on the family `(Y_g)_{g∈G}`)
is left to downstream SPT classification work; see
`MPS/Symmetry/VirtualRepresentation.lean` for the analogous injective construction.

The periodic equal-case FT is taken as an explicit hypothesis `hPeriodicEq` (see file
header for the rationale and status). -/
theorem cor_4_1_physical_symmetry_zgauge
    (A : MPSTensor d D)
    (hA : IsIrreducibleForm A)
    (U : G →* Matrix (Fin d) (Fin d) ℂ)
    (hUnit : ∀ g : G, (U g) * (U g)ᴴ = 1)
    (hSym : IsOnSiteSymmetric A U)
    (hPeriodicEq : PeriodicEqualCaseFT d D) :
    ∀ g : G, ∃ m : ℕ, 0 < m ∧ ZGaugeEquiv m A (twistedTensor A U g) := by
  intro g
  -- Twisting by `U g` is the same as the physical-index rotation by `U g`.
  have hRotEq : twistedTensor A U g = rotatePhysical (U g) A :=
    twistedTensor_eq_rotatePhysical A U g
  -- The rotated tensor is again in irreducible form II (preserved by unitary rotation).
  have hRot : IsIrreducibleForm (rotatePhysical (U g) A) :=
    isIrreducibleForm_rotatePhysical A (U g) (hUnit g) hA
  -- The on-site symmetry hypothesis gives `SameMPV A (rotatePhysical (U g) A)`.
  have hSame : SameMPV A (rotatePhysical (U g) A) := by
    have := hSym g
    rwa [hRotEq] at this
  -- Apply the periodic equal-case Fundamental Theorem.
  rcases hPeriodicEq hA hRot hSame with ⟨m, hm_pos, hZGauge⟩
  exact ⟨m, hm_pos, by rw [hRotEq]; exact hZGauge⟩

/-- **A convenient reformulation of `cor_4_1_physical_symmetry_zgauge`** in the form most
useful for downstream SPT arguments: extract the gauge `Y(g)` and matrix `Z(g)`
explicitly. -/
theorem cor_4_1_physical_symmetry_zgauge_explicit
    (A : MPSTensor d D)
    (hA : IsIrreducibleForm A)
    (U : G →* Matrix (Fin d) (Fin d) ℂ)
    (hUnit : ∀ g : G, (U g) * (U g)ᴴ = 1)
    (hSym : IsOnSiteSymmetric A U)
    (hPeriodicEq : PeriodicEqualCaseFT d D) :
    ∀ g : G, ∃ (m : ℕ) (Y : GL (Fin D) ℂ) (Z : Matrix (Fin D) (Fin D) ℂ),
      0 < m ∧
      Z ^ m = 1 ∧
      (∀ i : Fin d, Z * A i = A i * Z) ∧
      (∀ i : Fin d,
        Z * A i =
          (Y : Matrix (Fin D) (Fin D) ℂ) * twistedTensor A U g i *
            (((Y⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ))) := by
  intro g
  rcases cor_4_1_physical_symmetry_zgauge A hA U hUnit hSym hPeriodicEq g with
    ⟨m, hm_pos, Y, Z, hZpow, hComm, hRel⟩
  exact ⟨m, Y, Z, hm_pos, hZpow, hComm, hRel⟩

end Corollary41

/-! ## Theorem 4.1 — `p`-refinement and `p`-divisibility (definitions only) -/

section Theorem41

variable {d D : ℕ}

/-- **`p`-divisibility of a CP linear endomorphism.**

A linear endomorphism `E` of `Mat_D ℂ` is *`p`-divisible* if it equals the `p`-fold
composition of some CPTP map `E'`. This is the channel-theoretic notion appearing in
arXiv:1708.00029, §4.1. -/
def IsPDivisibleChannel
    (E : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ) (p : ℕ) : Prop :=
  ∃ E' : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ,
    IsChannel E' ∧ E = E' ^ p

/-- **`p`-refinement of an MPS tensor (arXiv:1708.00029, §4.1, Eq. (4.1)).**

`B : MPSTensor d D` admits a `p`-refinement if there exists another tensor
`A : MPSTensor d D` and an isometry `W : ℂ^d → (ℂ^d)^{⊗p}` (encoded as a matrix
`Matrix (Fin (blockPhysDim d p)) (Fin d) ℂ` with `Wᴴ * W = 1`) such that the `p`-blocked
`A` matches the `W`-image of `B` at the level of MPV coefficients:
`coeff (blockTensor A p) (List.ofFn τ) = ∑_σ (∏_k W (τ k) (σ k)) · coeff B (List.ofFn σ)`
for every length `N` and every `τ : Fin N → Fin (blockPhysDim d p)`.

In paper notation, this encodes `|V_{pN}(A)⟩ = W^{⊗N} |V_N(B)⟩` for every `N`. -/
def IsPRefinable (B : MPSTensor d D) (p : ℕ) : Prop :=
  ∃ (A : MPSTensor d D)
    (W : Matrix (Fin (blockPhysDim d p)) (Fin d) ℂ),
    Wᴴ * W = 1 ∧
    ∀ (N : ℕ) (τ : Fin N → Fin (blockPhysDim d p)),
      coeff (blockTensor A p) (List.ofFn τ) =
        ∑ σ : Fin N → Fin d,
          (∏ k : Fin N, W (τ k) (σ k)) * coeff B (List.ofFn σ)

end Theorem41

/-! ## Theorem 4.1 — forward direction (`p`-refinability ⇒ `p`-divisibility) -/

section Theorem41Forward

variable {d D : ℕ}

/-- **Rectangular Kraus isometry mixing.**

For a (possibly rectangular) isometry `W : Fin m → Fin d` with `Wᴴ · W = 1`,
the `W`-pullback family `C τ := ∑_σ W(τ, σ) · B σ` has the same transfer map
as `B`. This is the rectangular analogue of the Kraus unitary-freedom identity
`kraus_same_map_of_unitary_combination` (Wolf, *Quantum Channels & Operations*,
Theorem 2.1 item 4 / Theorem 2.18). It is the `∑_τ C_τ · X · C_τᴴ = ∑_σ B_σ · X · B_σᴴ`
identity specialised to our `MPSTensor` API. -/
theorem transferMap_kraus_isometry
    {m : ℕ} (B : MPSTensor d D)
    (W : Matrix (Fin m) (Fin d) ℂ) (hW : Wᴴ * W = 1) :
    transferMap (fun τ : Fin m => ∑ σ : Fin d, W τ σ • B σ) = transferMap B := by
  ext X : 1
  simp only [transferMap_apply]
  -- Extract the orthogonality relation `∑_τ conj(W τ σ') · W τ σ = δ_{σ σ'}` from `Wᴴ · W = 1`.
  have hW_entry : ∀ σ σ' : Fin d,
      ∑ τ : Fin m, (starRingEnd ℂ) (W τ σ') * W τ σ =
        if σ' = σ then 1 else 0 := by
    intro σ σ'
    have h := congrArg (fun M : Matrix (Fin d) (Fin d) ℂ => M σ' σ) hW
    simpa [Matrix.mul_apply, Matrix.one_apply, Matrix.conjTranspose_apply] using h
  calc ∑ τ : Fin m,
      (∑ σ : Fin d, W τ σ • B σ) * X * (∑ σ : Fin d, W τ σ • B σ)ᴴ
      = ∑ τ : Fin m, ∑ σ : Fin d, ∑ σ' : Fin d,
            ((starRingEnd ℂ) (W τ σ') * W τ σ) • (B σ * X * (B σ')ᴴ) := by
        simp_rw [Matrix.sum_mul, Matrix.conjTranspose_sum, Matrix.conjTranspose_smul,
          Matrix.mul_sum, smul_mul_assoc, mul_smul_comm, Matrix.mul_assoc, smul_smul]
        simp [mul_comm]
    _ = ∑ σ : Fin d, ∑ σ' : Fin d,
            (∑ τ : Fin m, (starRingEnd ℂ) (W τ σ') * W τ σ) •
              (B σ * X * (B σ')ᴴ) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl; intro σ _
        rw [Finset.sum_comm]
        simp_rw [← Finset.sum_smul]
    _ = ∑ σ : Fin d, ∑ σ' : Fin d,
            (if σ' = σ then (1 : ℂ) else 0) • (B σ * X * (B σ')ᴴ) := by
        simp_rw [hW_entry]
    _ = ∑ σ : Fin d, B σ * X * (B σ)ᴴ := by simp

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

/-- **Canonicalization hypothesis for the forward direction of Theorem 4.1.**

This Prop packages the analytic content that remains between the
coefficient-level `IsPRefinable B p` (a trace-level MPV identity) and the
channel-level conclusion needed to exhibit `E_B` as a `p`-th power: any
`p`-refinement of `B` can be *canonicalized* to a witness that is both
left-canonical and produces a matching transfer map under `p`-blocking.

Morally, the canonicalization is produced as follows. Given a witness
`(A, W)` from `IsPRefinable B p`, form the `W`-pullback tensor
`C τ := ∑_σ W(τ, σ) · B σ`; the rectangular Kraus identity
(`transferMap_kraus_isometry`) gives `E_C = E_B`, while the MPV hypothesis
gives `SameMPV C (blockTensor A p)`. The periodic equal-case Fundamental
Theorem (Theorem 3.8 of arXiv:1708.00029, available here as the hypothesis
`PeriodicEqualCaseFT`) then supplies a `Z`-gauge equivalence between `C` and
`blockTensor A p`, which — combined with a unitary canonical-form reduction
for irreducible form II and Wolf Theorem 2.18 — produces the sought
left-canonical witness. Packaging this full chain in Lean requires
infrastructure (canonical unitary gauge, Kraus uniqueness) that is tracked as
follow-up work, so we expose the end-result predicate as a hypothesis. -/
def PRefinementCanonicalization (d D p : ℕ) : Prop :=
  ∀ {B : MPSTensor d D}, IsPRefinable B p →
    ∃ A : MPSTensor d D,
      (∑ i : Fin d, (A i)ᴴ * A i = 1) ∧
      transferMap B = transferMap (blockTensor A p)

/-- **Forward direction of Theorem 4.1 (conditional form).**

Let `B` be an MPS tensor in irreducible form II and `p ≥ 1`. Assume the
periodic equal-case Fundamental Theorem (`PeriodicEqualCaseFT`) at the blocked
dimension and the `PRefinementCanonicalization` hypothesis supplying a
left-canonical witness with matching transfer map. Then `IsPRefinable B p`
implies `IsPDivisibleChannel (transferMap B) p`.

This follows the same conditional pattern as
`MPSTensor.cor_4_1_physical_symmetry_zgauge`: analytic inputs beyond the
repository's current reach are exposed as explicit hypotheses, while the
algebraic structure — the blocking-commutes-with-power identity and the
left-canonical-channel lemma — is formalized here. -/
theorem thm_4_1_p_refinement_forward
    (B : MPSTensor d D) (_hB : IsIrreducibleForm B)
    (p : ℕ) (_hp : 0 < p)
    (_hPeriodicEq : PeriodicEqualCaseFT (blockPhysDim d p) D)
    (hCanonical : PRefinementCanonicalization d D p)
    (hRefine : IsPRefinable B p) :
    IsPDivisibleChannel (transferMap B) p := by
  obtain ⟨A, hA_norm, hTransferEq⟩ := hCanonical hRefine
  exact thm_4_1_p_refinement_forward_witness B p A hA_norm hTransferEq

end Theorem41Forward

end MPSTensor
