/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Data.Nat.Log
import Mathlib.Data.Fintype.EquivFin
import TNLean.MPS.Overlap.Basic

/-!
# Registers for the recursive MPU circuit

For each internal physical cut, allocate two bond registers of width
`q = ⌈log_d D⌉` and two amplification flags. The logical register consists
of the physical chain and these auxiliary sites. A second copy of the
auxiliary site set is a common initialized scratch pool. Thus there are
`N + 4 * (N - 1) * (q + 1)` sites altogether, at most `5 * N * (q + 1)`.

The site types distinguish physical, bond, flag, and scratch coordinates.
They are explicitly equivalent to consecutive finite site sets, so the
existing neighboring-pair circuit model applies. A positive bond dimension
`r ≤ D` embeds in the common bond register with its zero label mapped to
the all-zero configuration.

This is the register allocation in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. At `N = 1` the layout
has only one site; a two-qudit synthesis on that chain is handled separately
by adding one initialized padding site.
-/

open MPSTensor

namespace MPUCircuit

/-- The common number of qudits per bond register. Source: register allocation
in Section 5 of `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
def bondRegisterWidth (d D : ℕ) : ℕ := Nat.clog d D

/-- Index the internal cuts by their positions between physical sites.
The index `j` denotes cut `j + 1`, excluding the two endpoint cuts.
Source: Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
def internalCutEmbedding (N : ℕ) : Fin (N - 1) ↪ Fin (N + 1) where
  toFun j := ⟨j.val + 1, by omega⟩
  inj' i j hij := by
    apply Fin.ext
    have hval := congrArg Fin.val hij
    change i.val + 1 = j.val + 1 at hval
    omega

/-- Every indexed internal cut lies strictly between the endpoint cuts.
Source: Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem internalCutEmbedding_bounds (N : ℕ) (j : Fin (N - 1)) :
    0 < (internalCutEmbedding N j).val ∧ (internalCutEmbedding N j).val < N := by
  change 0 < j.val + 1 ∧ j.val + 1 < N
  have := j.isLt
  omega

/-- Bond sites are indexed by the internal cut, left or right side, and the
qudit coordinate of the bond register. Source: Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
abbrev BondRegisterSite (d D N : ℕ) :=
  Fin (N - 1) × Fin 2 × Fin (bondRegisterWidth d D)

/-- Two amplification flags are allocated at each internal cut. Source:
Section 5 of `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
abbrev AmplificationFlagSite (N : ℕ) := Fin (N - 1) × Fin 2

/-- The logical auxiliary sites consist of bond-register sites and flags.
Source: Section 5 of `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
abbrev AuxiliarySite (d D N : ℕ) := BondRegisterSite d D N ⊕ AmplificationFlagSite N

/-- Physical sites and logical auxiliary sites form the logical register.
Source: Section 5 of `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
abbrev LogicalSite (d D N : ℕ) := Fin N ⊕ AuxiliarySite d D N

/-- The global register appends one common scratch pool of the same size as
the logical auxiliary register. Source: Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
abbrev GlobalSite (d D N : ℕ) := LogicalSite d D N ⊕ AuxiliarySite d D N

/-- Number of logical auxiliary sites, and size of the shared scratch pool.
Source: Section 5 of `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
def auxiliarySiteCount (d D N : ℕ) : ℕ := 2 * (N - 1) * (bondRegisterWidth d D + 1)

/-- Number of sites in the logical register. Source: Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
def logicalSiteCount (d D N : ℕ) : ℕ := N + auxiliarySiteCount d D N

/-- Number of physical, logical auxiliary, and shared scratch sites together.
Source: Section 5 of `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
def globalSiteCount (d D N : ℕ) : ℕ := logicalSiteCount d D N + auxiliarySiteCount d D N

/-- Exact cardinality of the bond sites. Source: Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem card_bondRegisterSite (d D N : ℕ) :
    Fintype.card (BondRegisterSite d D N) = 2 * (N - 1) * bondRegisterWidth d D := by
  simp only [BondRegisterSite, Fintype.card_prod, Fintype.card_fin]
  ring

/-- Exact cardinality of the amplification flags. Source: Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem card_amplificationFlagSite (N : ℕ) :
    Fintype.card (AmplificationFlagSite N) = 2 * (N - 1) := by
  simp only [AmplificationFlagSite, Fintype.card_prod, Fintype.card_fin]
  ring

/-- The auxiliary and scratch site types have the claimed common cardinality.
Source: Section 5 of `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem card_auxiliarySite (d D N : ℕ) :
    Fintype.card (AuxiliarySite d D N) = auxiliarySiteCount d D N := by
  simp only [AuxiliarySite, Fintype.card_sum, card_bondRegisterSite,
    card_amplificationFlagSite, auxiliarySiteCount]
  ring

/-- Exact cardinality of the logical register. Source: Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem card_logicalSite (d D N : ℕ) :
    Fintype.card (LogicalSite d D N) = logicalSiteCount d D N := by
  change Fintype.card (Fin N ⊕ AuxiliarySite d D N) = _
  rw [Fintype.card_sum, Fintype.card_fin, card_auxiliarySite]
  rfl

/-- Exact cardinality of the full register with the shared scratch pool.
Source: Section 5 of `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem card_globalSite (d D N : ℕ) :
    Fintype.card (GlobalSite d D N) = globalSiteCount d D N := by
  change Fintype.card (LogicalSite d D N ⊕ AuxiliarySite d D N) = _
  rw [Fintype.card_sum, card_logicalSite, card_auxiliarySite]
  rfl

/-- The full register has `N + 4(N-1)(q+1)` sites. Source: Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem globalSiteCount_eq (d D N : ℕ) :
    globalSiteCount d D N = N + 4 * (N - 1) * (bondRegisterWidth d D + 1) := by
  simp only [globalSiteCount, logicalSiteCount, auxiliarySiteCount]
  ring

/-- The register allocation is linear in chain length and bond-register
width. Source: Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem globalSiteCount_le (d D N : ℕ) :
    globalSiteCount d D N ≤ 5 * N * (bondRegisterWidth d D + 1) := by
  rw [globalSiteCount_eq]
  have hN : N ≤ N * (bondRegisterWidth d D + 1) := by
    exact Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
  have hcut : 4 * (N - 1) * (bondRegisterWidth d D + 1) ≤
      4 * N * (bondRegisterWidth d D + 1) := by
    gcongr
    exact Nat.sub_le _ _
  nlinarith

/-- Consecutive indexing of the logical auxiliary sites. Source: Section 5
of `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
noncomputable def auxiliarySiteEquivFin (d D N : ℕ) :
    AuxiliarySite d D N ≃ Fin (auxiliarySiteCount d D N) :=
  (Fintype.equivFin _).trans (finCongr (card_auxiliarySite d D N))

/-- Consecutive indexing of the logical register. Source: Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
noncomputable def logicalSiteEquivFin (d D N : ℕ) :
    LogicalSite d D N ≃ Fin (logicalSiteCount d D N) :=
  (Equiv.sumCongr (Equiv.refl (Fin N)) (auxiliarySiteEquivFin d D N)).trans finSumFinEquiv

/-- Consecutive indexing of the complete register. Source: Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
noncomputable def globalSiteEquivFin (d D N : ℕ) :
    GlobalSite d D N ≃ Fin (globalSiteCount d D N) :=
  (Equiv.sumCongr (logicalSiteEquivFin d D N) (auxiliarySiteEquivFin d D N)).trans
    finSumFinEquiv

/-- Physical sites embed in the logical register. Source: Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
def physicalSiteEmbedding (d D N : ℕ) : Fin N ↪ LogicalSite d D N :=
  Function.Embedding.inl

/-- Bond-register sites embed in the logical register. Source: Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
def bondSiteEmbedding (d D N : ℕ) : BondRegisterSite d D N ↪ LogicalSite d D N :=
  Function.Embedding.inl.trans Function.Embedding.inr

/-- Amplification flags embed in the logical register. Source: Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
def amplificationFlagEmbedding (d D N : ℕ) : AmplificationFlagSite N ↪ LogicalSite d D N :=
  Function.Embedding.inr.trans Function.Embedding.inr

/-- Logical auxiliary sites embed in the logical register. Source: Section 5
of `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
def auxiliarySiteEmbedding (d D N : ℕ) : AuxiliarySite d D N ↪ LogicalSite d D N :=
  Function.Embedding.inr

/-- The logical register embeds in the global register. Source: Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
def logicalSiteEmbedding (d D N : ℕ) : LogicalSite d D N ↪ GlobalSite d D N :=
  Function.Embedding.inl

/-- The common scratch pool is a disjoint copy of the auxiliary site type.
Source: Section 5 of `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
def scratchSiteEmbedding (d D N : ℕ) : AuxiliarySite d D N ↪ GlobalSite d D N :=
  Function.Embedding.inr

/-- Consecutive physical coordinates inside the logical register. Source:
Section 5 of `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
noncomputable def physicalLogicalSites (d D N : ℕ) : Fin N ↪ Fin (logicalSiteCount d D N) :=
  (physicalSiteEmbedding d D N).trans (logicalSiteEquivFin d D N).toEmbedding

/-- Consecutive auxiliary coordinates inside the logical register. Source:
Section 5 of `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
noncomputable def auxiliaryLogicalSites (d D N : ℕ) :
    AuxiliarySite d D N ↪ Fin (logicalSiteCount d D N) :=
  (auxiliarySiteEmbedding d D N).trans (logicalSiteEquivFin d D N).toEmbedding

/-- Consecutive physical coordinates precede all logical auxiliary sites.
Source: the initialized logical register in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
@[simp] theorem physicalLogicalSites_apply (d D N : ℕ) (i : Fin N) :
    physicalLogicalSites d D N i = Fin.castAdd (auxiliarySiteCount d D N) i := by
  change finSumFinEquiv (Sum.inl i) = _
  exact finSumFinEquiv_apply_left _

/-- Logical auxiliary coordinates follow the physical sites in their common
auxiliary-coordinate order. Source: Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
@[simp] theorem auxiliaryLogicalSites_apply (d D N : ℕ) (i : AuxiliarySite d D N) :
    auxiliaryLogicalSites d D N i = Fin.natAdd N (auxiliarySiteEquivFin d D N i) := by
  change finSumFinEquiv (Sum.inr (auxiliarySiteEquivFin d D N i)) = _
  exact finSumFinEquiv_apply_right _

/-- Consecutive logical coordinates inside the full register. Source:
Section 5 of `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
noncomputable def logicalGlobalSites (d D N : ℕ) :
    LogicalSite d D N ↪ Fin (globalSiteCount d D N) :=
  (logicalSiteEmbedding d D N).trans (globalSiteEquivFin d D N).toEmbedding

/-- Consecutive scratch coordinates inside the full register. Source:
Section 5 of `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
noncomputable def scratchGlobalSites (d D N : ℕ) :
    AuxiliarySite d D N ↪ Fin (globalSiteCount d D N) :=
  (scratchSiteEmbedding d D N).trans (globalSiteEquivFin d D N).toEmbedding

/-- The global numbering places logical sites before all scratch sites.
This is the numbering used by the zero-workspace embedding in the clean
circuit statements. Source: Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
@[simp] theorem logicalGlobalSites_apply (d D N : ℕ) (i : LogicalSite d D N) :
    logicalGlobalSites d D N i =
      Fin.castAdd (auxiliarySiteCount d D N) (logicalSiteEquivFin d D N i) := by
  change finSumFinEquiv (Sum.inl (logicalSiteEquivFin d D N i)) = _
  exact finSumFinEquiv_apply_left _

/-- The global numbering places the common scratch pool after the logical
register, in the same auxiliary-coordinate order. Source: Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
@[simp] theorem scratchGlobalSites_apply (d D N : ℕ) (i : AuxiliarySite d D N) :
    scratchGlobalSites d D N i =
      Fin.natAdd (logicalSiteCount d D N) (auxiliarySiteEquivFin d D N i) := by
  change finSumFinEquiv (Sum.inr (auxiliarySiteEquivFin d D N i)) = _
  exact finSumFinEquiv_apply_right _

/-- The common bond register accommodates every bond dimension at most `D`.
Source: Section 5 of `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem bondDim_le_registerCapacity {d D : ℕ} (hd : 2 ≤ d) :
    D ≤ d ^ bondRegisterWidth d D :=
  Nat.le_pow_clog (by omega) D

/-- The padded bond-register dimension is at most `dD`, so synthesis on a
bounded number of bond registers is polynomial in `D` at fixed `d`.
Source: the leaf and merger registers in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem registerCapacity_le_mul_bondDim {d D : ℕ} (hd : 2 ≤ d) (hD : 0 < D) :
    d ^ bondRegisterWidth d D ≤ d * D := by
  by_cases hDone : D = 1
  · subst D
    simp only [bondRegisterWidth, Nat.clog_one_right, pow_zero, Nat.mul_one]
    omega
  · have hDlarge : 1 < D := by omega
    have hq : 0 < bondRegisterWidth d D := Nat.clog_pos (by omega) hDlarge
    have hsmall := Nat.pow_pred_clog_lt_self (by omega : 1 < d) hDlarge
    change d ^ (bondRegisterWidth d D - 1) < D at hsmall
    calc
      d ^ bondRegisterWidth d D = d ^ (bondRegisterWidth d D - 1) * d := by
        rw [← pow_succ]
        congr 1
        omega
      _ ≤ D * d := Nat.mul_le_mul_right d hsmall.le
      _ = d * D := Nat.mul_comm _ _

section Encoding

variable {d D r : ℕ} [NeZero d]

/-- Embed a positive bond alphabet of dimension `r ≤ D` in the common qudit
register, sending its zero label to the zero configuration. First choose a
cardinality embedding, then swap its zero image with the zero configuration.
Source: the bond-label encoding in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
noncomputable def bondRegisterEncoding (hd : 2 ≤ d) (hr : 0 < r) (hbound : r ≤ D) :
    Fin r ↪ Cfg d (bondRegisterWidth d D) := by
  classical
  have hcard : Fintype.card (Fin r) ≤ Fintype.card (Cfg d (bondRegisterWidth d D)) := by
    simpa only [Fintype.card_fin, Fintype.card_fun] using
      hbound.trans (bondDim_le_registerCapacity hd)
  let e : Fin r ↪ Cfg d (bondRegisterWidth d D) :=
    Classical.choice (Function.Embedding.nonempty_of_card_le hcard)
  exact e.trans (Equiv.swap (e ⟨0, hr⟩) 0).toEmbedding

/-- The common bond encoding preserves the distinguished zero label.
Source: the initialized bond registers in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem bondRegisterEncoding_zero (hd : 2 ≤ d) (hr : 0 < r) (hbound : r ≤ D) :
    bondRegisterEncoding hd hr hbound ⟨0, hr⟩ = 0 := by
  classical
  unfold bondRegisterEncoding
  exact Equiv.swap_apply_left _ _

end Encoding

end MPUCircuit
