/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.Periodic.FundamentalTheorem
import TNLean.MPS.Periodic.Applications
import TNLean.MPS.Symmetry.Defs
import TNLean.MPS.Core.Blocking
import TNLean.MPS.Core.BlockingTransfer
import TNLean.MPS.Core.CPPrimitive
import TNLean.Channel.Basic
import TNLean.Channel.KrausRepresentation
import TNLean.Channel.KrausUnitaryFreedom
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
  tensor).

* `MPSTensor.thm_4_1_p_refinement_forward` — **Theorem 4.1, forward direction**:
  `p`-refinability of `B` implies `p`-divisibility of its transfer map, conditional on a
  canonicalization hypothesis `PRefinementCanonicalization`.

* `MPSTensor.thm_4_1_p_refinement_reverse` — **Theorem 4.1, reverse direction**:
  `p`-divisibility of the transfer map implies `p`-refinability of `B`, conditional on an
  inverse canonicalization hypothesis `PRefinementInverseCanonicalization`. The algebraic
  heart is Wolf Theorem 2.18 (`kraus_isometry_freedom_iff`) applied to the `p`-blocked
  Kraus family.

* `MPSTensor.thm_4_1_p_refinement` — the bidirectional equivalence, bundling the forward
  and reverse directions under both conditional hypotheses.

## Status of the dependency on `periodicOverlapDichotomy` (#78 / #81)

The corollary invokes the **periodic equal-case Fundamental Theorem of MPS** (Theorem 3.8
in arXiv:1708.00029, formalized as `fundamentalTheorem_periodic_equalCase` in
`MPS/Periodic/FundamentalTheorem.lean`). That theorem is in turn currently stated as a
direct consumer of `PeriodicOverlapHypothesis`, which can be discharged by
`periodicOverlapDichotomy` (PR #573, follow-ups #607–#609). The dichotomy's proof in
`MPS/Periodic/Overlap.lean` still relies on several admitted sub-lemmas, so this file
follows the established convention (see `Periodic/Applications.lean`,
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
hypothesis in `MPS/Periodic/Applications.lean`. -/
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

/-- **Pullback stage of the forward canonicalization roadmap for Theorem 4.1.**

From a `p`-refinement witness `(A, W)` for `B`, the `W`-pullback tensor
`C τ := ∑_σ W(τ, σ) • B σ` has the same transfer map as `B` and the same MPV
family as `blockTensor A p`.

This packages the first three steps of the forward-direction plan recorded in
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

This Prop states the analytic content that remains between the
coefficient-level `IsPRefinable B p` (a trace-level MPV identity) and the
channel-level conclusion needed to exhibit `E_B` as a `p`-th power: any
`p`-refinement of `B` can be *canonicalized* to a witness that is both
left-canonical and produces a matching transfer map under `p`-blocking.

Morally, the canonicalization is produced as follows. Given a witness
`(A, W)` from `IsPRefinable B p`, form the `W`-pullback tensor
`C τ := ∑_σ W(τ, σ) · B σ`; the theorem
`pRefinementCanonicalization_pullback` now packages this first stage, giving
`E_C = E_B` together with `SameMPV C (blockTensor A p)`. The periodic
equal-case Fundamental Theorem (Theorem 3.8 of arXiv:1708.00029, available here
as the hypothesis `PeriodicEqualCaseFT`) then supplies a `Z`-gauge equivalence
between `C` and `blockTensor A p`, which — combined with a unitary
canonical-form reduction for irreducible form II and Wolf Theorem 2.18 —
produces the sought left-canonical witness. Formalizing this remaining second
stage in Lean still requires infrastructure (canonical unitary gauge, Kraus
uniqueness), so we expose the end-result predicate as a hypothesis. -/
def PRefinementCanonicalization (d D p : ℕ) : Prop :=
  ∀ {B : MPSTensor d D}, IsIrreducibleForm B → IsPRefinable B p →
    ∃ A : MPSTensor d D,
      (∑ i : Fin d, (A i)ᴴ * A i = 1) ∧
      transferMap B = transferMap (blockTensor A p)

/-- **Forward direction of Theorem 4.1 (conditional form).**

Let `B` be an MPS tensor in irreducible form II. Assume
`PRefinementCanonicalization`, which records the remaining analytic bridge from
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

/-! ## Theorem 4.1 — reverse direction (`p`-divisibility ⇒ `p`-refinability) -/

section Theorem41Reverse

variable {d D : ℕ}


/-- **Inverse canonicalization hypothesis for the reverse direction of Theorem 4.1.**

This Prop packages the analytic content that bridges `IsPDivisibleChannel (transferMap B) p`
(a channel-level `p`-th-root statement) to the existence of a witness tensor
`A : MPSTensor d D` whose `p`-blocked transfer map matches that of `B`.

Morally, if `transferMap B = (E')^p` for a CPTP map `E'`, one would like to choose a Kraus
representation `A` of `E'` with exactly `d` Kraus operators. In general the minimum Kraus
rank of `E'` may exceed `d`, so formalising this step requires a Kraus-rank reduction /
canonical-form argument (the analogue of left-canonical reduction used for the forward
direction). We expose the end-result as a hypothesis in the same style as
`PRefinementCanonicalization`. -/
def PRefinementInverseCanonicalization (d D p : ℕ) : Prop :=
  ∀ {B : MPSTensor d D}, IsIrreducibleForm B →
    IsPDivisibleChannel (transferMap B) p →
    ∃ A : MPSTensor d D, transferMap B = transferMap (blockTensor A p)

/-- **Reverse direction of Theorem 4.1 (conditional form).**

Let `B` be an MPS tensor in irreducible form II and let `p ≥ 1`. Assume the inverse
canonicalization hypothesis `PRefinementInverseCanonicalization` (which records the
remaining analytic bridge from `p`-divisibility of `transferMap B` to a compatible
Kraus-reducible witness). Then `IsPDivisibleChannel (transferMap B) p` implies
`IsPRefinable B p`.

The proof follows the paper (arXiv:1708.00029 §4.1, converse paragraph): from the inverse
canonicalization we obtain `A : MPSTensor d D` with
`transferMap B = transferMap (blockTensor A p)`; this matches two Kraus representations of
the same CP map (`blockTensor A p` with `d^p` operators and `B` with `d` operators), so
Wolf Theorem 2.18 (`kraus_isometry_freedom_iff`) supplies an isometry
`V : Matrix (Fin (d^p)) (Fin d) ℂ` with `Vᴴ V = 1` and
`blockTensor A p α = ∑_j V α j • B j`. Expanding `coeff (blockTensor A p) (ofFn τ)` with
the helper `evalWord_sum_smul_ofFn` and linearity of `trace` produces exactly the
`W`-weighted coefficient identity defining `IsPRefinable B p`. -/
theorem thm_4_1_p_refinement_reverse
    (B : MPSTensor d D) (hB : IsIrreducibleForm B)
    (p : ℕ) (hp : 0 < p)
    (hInverse : PRefinementInverseCanonicalization d D p)
    (hDivisible : IsPDivisibleChannel (transferMap B) p) :
    IsPRefinable B p := by
  obtain ⟨A, hTransferEq⟩ := hInverse hB hDivisible
  classical
  -- `d ≤ d^p = blockPhysDim d p` whenever `p ≥ 1`: the Kraus-rank comparison needed by
  -- Wolf Theorem 2.18.
  have hCard : Fintype.card (Fin d) ≤ Fintype.card (Fin (blockPhysDim d p)) := by
    simp only [Fintype.card_fin, blockPhysDim_eq_pow]
    exact Nat.le_self_pow hp.ne' d
  -- Translate the linear-map equality into the Kraus-family equality needed by the freedom
  -- lemma.
  have hKraus :
      ∀ X : Matrix (Fin D) (Fin D) ℂ,
        ∑ α : Fin (blockPhysDim d p), blockTensor A p α * X * (blockTensor A p α)ᴴ =
          ∑ j : Fin d, B j * X * (B j)ᴴ := by
    intro X
    have hEq : transferMap (blockTensor A p) X = transferMap B X := by
      rw [← hTransferEq]
    simpa [transferMap_apply] using hEq
  -- Extract the isometric mixing matrix `V` from Wolf Thm 2.18.
  obtain ⟨V, hV, hBA⟩ :=
    (kraus_isometry_freedom_iff (blockTensor A p) B hCard).mp hKraus
  refine ⟨A, V, hV, ?_⟩
  intro N τ
  simp only [coeff_eq]
  -- Pointwise rewrite `blockTensor A p` as the `V`-mixing of `B`.
  have hAeq : (blockTensor A p : MPSTensor (blockPhysDim d p) D) =
      fun α => ∑ j : Fin d, V α j • B j := funext hBA
  rw [hAeq, evalWord_sum_smul_ofFn B V N τ, Matrix.trace_sum]
  refine Finset.sum_congr rfl ?_
  intro σ _
  rw [Matrix.trace_smul]
  rfl

end Theorem41Reverse

/-! ## Theorem 4.1 — bidirectional equivalence -/

section Theorem41Bundle

variable {d D : ℕ}

/-- **Theorem 4.1 (bidirectional, conditional form).**

Let `B` be an MPS tensor in irreducible form II and let `p ≥ 1`. Under both the forward
canonicalization hypothesis `PRefinementCanonicalization` and the inverse canonicalization
hypothesis `PRefinementInverseCanonicalization`, `p`-refinability of `B` is equivalent to
`p`-divisibility of its transfer map. This bundles
`thm_4_1_p_refinement_forward` and `thm_4_1_p_refinement_reverse` into a single iff. -/
theorem thm_4_1_p_refinement
    (B : MPSTensor d D) (hB : IsIrreducibleForm B)
    (p : ℕ) (hp : 0 < p)
    (hCanonical : PRefinementCanonicalization d D p)
    (hInverse : PRefinementInverseCanonicalization d D p) :
    IsPRefinable B p ↔ IsPDivisibleChannel (transferMap B) p :=
  ⟨thm_4_1_p_refinement_forward B hB p hCanonical,
   thm_4_1_p_refinement_reverse B hB p hp hInverse⟩

end Theorem41Bundle

end MPSTensor
