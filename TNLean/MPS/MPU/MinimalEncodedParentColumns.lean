/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.JoiningResetColumns
import TNLean.MPS.MPU.IntervalJointOutputReset
import TNLean.MPS.MPU.MinimalIntervalColumns

/-!
# The actual parent columns after encoded interval merging

The normalized joining contraction of two adjacent minimal intervals gives
exactly the weighted parent interval, with the shared bond pair reset to zero.
This file places that contraction inside the concrete parent output inclusion.
It retains an arbitrary outside configuration, and hence also retains states
entangled with the outside register. The equality preserves every scalar phase.

The coordinate lemmas first assume a product-coordinate description of the
actual joint output inclusion. That description is independently established
by `IntervalJointSuffixFactorization`. The final column identity uses the
actual minimal cut encodings; it supplies no parent column or reset equality
as a hypothesis. These are algebraic column identities, rather than statements
of circuit existence or circuit resource bounds.

Source: Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`.
-/

open Matrix MPSPreparation MPSTensor QuantumCircuit
open scoped Kronecker Matrix ComplexOrder MatrixOrder

namespace MPUCircuit

/-- Returning the physical rows of a transported basis inclusion to their
original site coordinates recovers its original initialized basis matrix.
Source: the coordinate changes in Section 5 of the local MPU circuit audit. -/
theorem initializedBasisMatrix_pullback_rows {d a n : ℕ} {α : Type*}
    (E : α ↪ Cfg d n) (e : Fin a ≃ Fin n) :
    (initializedBasisMatrix (pullbackBasisEmbedding E e)).submatrix
      (fun x : Cfg d n ↦ x ∘ e) id = initializedBasisMatrix E := by
  classical
  ext x p
  simp only [initializedBasisMatrix, Matrix.submatrix_apply, id_eq, Matrix.one_apply,
    pullbackBasisEmbedding_apply]
  have h : x ∘ e = E p ∘ e ↔ x = E p := by
    constructor
    · intro hh
      funext s
      have hs := congrFun hh (e.symm s)
      simpa only [Function.comp_apply, Equiv.apply_symm_apply] using hs
    · rintro rfl
      rfl
  simp only [h]

/-- In a prescribed product-coordinate description of the joint output
inclusion, the encoded joining parent returns to the original physical rows
as the same normalized joining contraction inside that inclusion. An arbitrary
input-coordinate bijection cancels exactly.
This is a conditional algebraic coordinate identity; it assumes neither a
circuit nor any parent or cleanup equation.
Source: Section 5 of `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem encodedJoiningParent_pullback_columns {d r q a n : ℕ} {ρ μ β : Type*}
    [Fintype ρ] [DecidableEq ρ]
    (hd : 2 ≤ d) (hr : 0 < r)
    (E : (ρ × (Fin r × Fin r)) ↪ Cfg d n)
    (siteEquiv : Fin (a + (2 * q + 2)) ≃ Fin n)
    (f : ρ ↪ Cfg d a) (e : Fin r ↪ Cfg d q)
    (hEncoding : pullbackBasisEmbedding E siteEquiv = appendBasisEmbedding f
      ((joiningChildBasisEmbedding (r := r) hd).trans
        (compatibleBondDilationEmbedding hd e)))
    (P : Matrix (Fin r) (Fin r) ℂ) (V : Matrix (ρ × (Fin r × Fin r)) μ ℂ)
    (u : μ ≃ β) :
    (encodedJoiningParent hd hr f e P (V.submatrix id u.symm)).submatrix
      (fun x : Cfg d n ↦ x ∘ siteEquiv) u =
      initializedBasisMatrix E * normalizedJoiningParent hr P V := by
  rw [encodedJoiningParent,
    ← initializedBasisMatrix_append_joiningChild hd f e, ← hEncoding]
  change (initializedBasisMatrix (pullbackBasisEmbedding E siteEquiv) *
    (normalizedJoiningParent hr P V).submatrix id u.symm).submatrix
      (fun x : Cfg d n ↦ x ∘ siteEquiv) u = _
  rw [← Matrix.submatrix_mul_equiv _ _ _ (Equiv.refl _) u]
  simp only [Equiv.coe_refl, Matrix.submatrix_submatrix, Function.comp_def,
    id_eq, Equiv.symm_apply_apply]
  change (initializedBasisMatrix (pullbackBasisEmbedding E siteEquiv)).submatrix
    (fun x : Cfg d n ↦ x ∘ siteEquiv) id * normalizedJoiningParent hr P V = _
  rw [initializedBasisMatrix_pullback_rows]



/-- The actual regrouped joint output with both shared bond labels reset to
a zero-preserving distinguished label is the parent output inclusion. The
outside configuration is retained by the underlying outside-site bijection.
The joining flags are initialized by the concrete outside inclusion.
Source: Section 5 of `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem regroupedIntervalJointOutputEmbedding_reset_apply
    {d D N r l n : ℕ} [NeZero d]
    (c : Fin (N - 1)) (j k : Fin (N + 1))
    (hjm : j.val < (internalCutEmbedding N c).val)
    (hmk : (internalCutEmbedding N c).val < k.val)
    (em : Fin r ↪ Cfg d (cutBondRegisterWidth d D N (internalCutEmbedding N c)))
    (ej : Fin l ↪ Cfg d (cutBondRegisterWidth d D N j))
    (ek : Fin n ↪ Cfg d (cutBondRegisterWidth d D N k))
    (q0 : Fin r) (hem : em q0 = 0)
    (p : (((CutIntervalConfig d N j.val (internalCutEmbedding N c).val ×
      CutIntervalConfig d N (internalCutEmbedding N c).val k.val) × (Fin n × Fin l)) ×
      ({s // s ∉ intervalJointOutsideFlagSet (d := d) (D := D) j
        (internalCutEmbedding N c) k hjm hmk} → Fin d))) :
    regroupedIntervalJointOutputEmbedding c j k hjm hmk em ej ek (p, (q0, q0)) =
      placedBasisEmbedding (intervalPacketSites d D N j.val k.val)
        (intervalOutputEmbedding j k ek ej) (Function.Embedding.refl _)
        ((joinCutInterval j.val (internalCutEmbedding N c).val k.val
          p.1.1.1 p.1.1.2, p.1.2),
          Equiv.arrowCongr (intervalJointRemainingSiteEquiv (d := d) (D := D)
            j (internalCutEmbedding N c) k hjm hmk) (Equiv.refl (Fin d)) p.2) := by
  rw [regroupedIntervalJointOutputEmbedding_apply]
  exact intervalJointOutputEmbedding_zero_eq_parent j (internalCutEmbedding N c) k
    hjm hmk em ej ek q0 hem p.1 p.2

section MinimalIntervals

variable {d D N : ℕ} [NeZero d]
variable (hd : 2 ≤ d) (U : Matrix (Cfg d N) (Cfg d N) ℂ)
  (hU : U ∈ unitaryGroup (Cfg d N) ℂ)
  (hbound : ∀ t : Fin (N + 1), cutRank (operatorCoefficientTensor U) t.val ≤ D)
  (B : ∀ t, Module.Basis (Fin (cutRank (operatorCoefficientTensor U) t))
    ℂ (cutColumnSpace (operatorCoefficientTensor U) t))
  (P : ∀ t : Fin (N + 1), Matrix (Fin (cutRank (operatorCoefficientTensor U) t.val))
    (Fin (cutRank (operatorCoefficientTensor U) t.val)) ℂ)
  (c : Fin (N - 1)) (j k : Fin (N + 1))
  (hjm : j.val < (internalCutEmbedding N c).val)
  (hmk : (internalCutEmbedding N c).val < k.val)

local notation "m" => internalCutEmbedding N c
local notation "hr" => cutRank_pos (operatorCoefficientTensor U)
  (operatorCoefficientTensor_ne_zero (by omega : 0 < d) U hU) (Fin.val (internalCutEmbedding N c))
local notation "em" => minimalCutBondRegisterEncoding hd U hU hbound m
local notation "ej" => minimalCutBondRegisterEncoding hd U hU hbound j
local notation "ek" => minimalCutBondRegisterEncoding hd U hU hbound k
local notation "RemainingCfg" => ({s // s ∉ intervalJointOutsideFlagSet (d := d) (D := D)
  j m k hjm hmk} → Fin d)
local notation "ChildPhysical" => (CutIntervalConfig d N j.val
  (Fin.val (internalCutEmbedding N c)) × CutIntervalConfig d N
  (Fin.val (internalCutEmbedding N c)) k.val)
local notation "OuterLabels" => (Fin (cutRank (operatorCoefficientTensor U) k.val) ×
  Fin (cutRank (operatorCoefficientTensor U) j.val))
local notation "ChildRows" => (((ChildPhysical × OuterLabels) × RemainingCfg) ×
  (Fin (cutRank (operatorCoefficientTensor U) (Fin.val (internalCutEmbedding N c))) ×
    Fin (cutRank (operatorCoefficientTensor U) (Fin.val (internalCutEmbedding N c)))))
local notation "ChildColumns" => (ChildPhysical × RemainingCfg)
local notation "child" => balancedIntervalChildren
  (minimalOperatorInterval U B (Nat.le_of_lt hjm))
    (minimalOperatorInterval U B (Nat.le_of_lt hmk))
  (CFC.sqrt (P j)) (CFC.sqrt (dualGramMetric (P k))) (P m)
local notation "E" => regroupedIntervalJointOutputEmbedding c j k hjm hmk em ej ek
local notation "parent" => vectorizedWeightedInterval
  (minimalOperatorInterval U B (Nat.le_of_lt (Nat.lt_trans hjm hmk)))
  (CFC.sqrt (P j)) (CFC.sqrt (dualGramMetric (P k)))
local notation "parentOutside" => OutsidePlacedConfig d
  (intervalPacketSites d D N j.val k.val)

open scoped Classical in
/-- The actual normalized joining contraction of two adjacent minimal
intervals, including an arbitrary unchanged outside state, gives exactly the
actual weighted parent columns. The bond reset and physical-output equality
are derived from the concrete interval encodings and the positive joining
metric. No parent-column or reset witness is assumed.
Source: Section 5 of `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem initializedBasisMatrix_regroupedOutput_mul_normalizedParent
    (hP : (P m).PosDef) :
    initializedBasisMatrix E *
      normalizedJoiningParent hr (P m) (joiningSpectatorColumns (τ := RemainingCfg) child) =
      (initializedBasisMatrix (minimalIntervalOutputEmbedding hd U hU hbound j k) *
        (parent ⊗ₖ (1 : Matrix parentOutside parentOutside ℂ))).submatrix id
          (intervalJointInputConfigEquiv j m k hjm hmk) := by
  classical
  have hcontract := normalizedJoiningParent_joiningSpectatorColumns
    (τ := RemainingCfg) hr (P m) child
  have hminimal := normalizedJoiningParent_minimalOperatorIntervals U B hjm.le hmk.le hr
    (CFC.sqrt (P j)) (CFC.sqrt (dualGramMetric (P k))) hP
  have hspectator := congrArg (joiningSpectatorColumns (τ := RemainingCfg)) hminimal
  have hnormal := hcontract.trans hspectator
  have hcolumns := congrArg
    (fun V : Matrix ChildRows ChildColumns ℂ ↦ initializedBasisMatrix E * V) hnormal
  rw [joiningSpectatorColumns_basisResetOutput,
    initializedBasisMatrix_mul_basisResetOutput] at hcolumns
  let eout : ((ChildPhysical × OuterLabels) × RemainingCfg) ≃
      ((CutIntervalConfig d N j.val k.val × OuterLabels) × parentOutside) := Equiv.prodCongr
    (Equiv.prodCongr (cutIntervalSplitEquiv d N j.val (Fin.val m) k.val hjm.le hmk.le).symm
      (Equiv.refl (Fin (cutRank (operatorCoefficientTensor U) k.val) ×
        Fin (cutRank (operatorCoefficientTensor U) j.val))))
    (Equiv.arrowCongr (intervalJointRemainingSiteEquiv (d := d) (D := D) j m k hjm hmk)
      (Equiv.refl (Fin d)))
  have hreset : ((Function.Embedding.sectL _ (⟨0, hr⟩, ⟨0, hr⟩)).trans E) =
      eout.toEmbedding.trans (minimalIntervalOutputEmbedding hd U hU hbound j k) := by
    apply Function.Embedding.ext
    intro p
    change E (p, (⟨0, hr⟩, ⟨0, hr⟩)) =
      minimalIntervalOutputEmbedding hd U hU hbound j k (eout p)
    exact regroupedIntervalJointOutputEmbedding_reset_apply
      (d := d) (D := D) (N := N)
      (r := cutRank (operatorCoefficientTensor U) (Fin.val m))
      (l := cutRank (operatorCoefficientTensor U) j.val)
      (n := cutRank (operatorCoefficientTensor U) k.val) c j k hjm hmk em ej ek
      ⟨0, hr⟩ (minimalCutBondRegisterEncoding_zero hd U hU hbound m) p
  rw [hreset] at hcolumns
  let Wsplit : Matrix (ChildPhysical × OuterLabels) ChildPhysical ℂ :=
    reindexLinearEquiv ℂ ℂ
      (Equiv.prodCongr (cutIntervalSplitEquiv d N j.val (Fin.val m) k.val hjm.le hmk.le)
        (Equiv.refl OuterLabels))
      (cutIntervalSplitEquiv d N j.val (Fin.val m) k.val hjm.le hmk.le) parent
  have hweighted : Wsplit ⊗ₖ (1 : Matrix RemainingCfg RemainingCfg ℂ) =
      (parent ⊗ₖ (1 : Matrix parentOutside parentOutside ℂ)).submatrix eout
        (intervalJointInputConfigEquiv (d := d) (D := D) j m k hjm hmk) := by
    ext ⟨⟨⟨x, y⟩, labels⟩, z⟩ ⟨⟨a, b⟩, w⟩
    change parent (joinCutInterval j.val (Fin.val m) k.val x y, labels)
        (joinCutInterval j.val (Fin.val m) k.val a b) *
        (1 : Matrix RemainingCfg RemainingCfg ℂ) z w =
      parent (joinCutInterval j.val (Fin.val m) k.val x y, labels)
        (joinCutInterval j.val (Fin.val m) k.val a b) *
        (1 : Matrix parentOutside parentOutside ℂ)
          ((Equiv.arrowCongr (intervalJointRemainingSiteEquiv (d := d) (D := D)
            j m k hjm hmk) (Equiv.refl (Fin d))) z)
          ((Equiv.arrowCongr (intervalJointRemainingSiteEquiv (d := d) (D := D)
            j m k hjm hmk) (Equiv.refl (Fin d))) w)
    simp only [Matrix.one_apply, Equiv.apply_eq_iff_eq]
  have htransport : initializedBasisMatrix
      (eout.toEmbedding.trans (minimalIntervalOutputEmbedding hd U hU hbound j k)) *
        (Wsplit ⊗ₖ (1 : Matrix RemainingCfg RemainingCfg ℂ)) =
      (initializedBasisMatrix (minimalIntervalOutputEmbedding hd U hU hbound j k) *
        (parent ⊗ₖ (1 : Matrix parentOutside parentOutside ℂ))).submatrix id
          (intervalJointInputConfigEquiv (d := d) (D := D) j m k hjm hmk) := by
    change (initializedBasisMatrix (minimalIntervalOutputEmbedding hd U hU hbound j k)).submatrix
      id eout * (Wsplit ⊗ₖ (1 : Matrix RemainingCfg RemainingCfg ℂ)) = _
    rw [hweighted, Matrix.submatrix_mul_equiv]
  convert hcolumns.trans htransport using 1
  congr!


open scoped Classical in
/-- After returning the encoded joining parent to the original physical
rows and cancelling an arbitrary input-coordinate bijection, its columns are
the actual weighted parent interval in its minimal output inclusion. The
product-coordinate premise is the one established for actual intervals by
`IntervalJointSuffixFactorization`; the parent and bond-reset equations are
proved here. This theorem asserts the algebraic column identity used by the
circuit construction, without asserting circuit existence or a resource bound.
Source: Section 5 of `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem encodedJoiningParent_minimalIntervalColumns {a : ℕ} {β : Type*}
    (siteEquiv : Fin (a + (2 * cutBondRegisterWidth d D N m + 2)) ≃
      Fin (logicalSiteCount d D N))
    (f : ((ChildPhysical × OuterLabels) × RemainingCfg) ↪ Cfg d a)
    (hEncoding : pullbackBasisEmbedding E siteEquiv = appendBasisEmbedding f
      ((joiningChildBasisEmbedding
        (r := cutRank (operatorCoefficientTensor U) (Fin.val m)) hd).trans
          (compatibleBondDilationEmbedding hd em)))
    (hP : (P m).PosDef) (u : ChildColumns ≃ β) :
    (encodedJoiningParent hd hr f em (P m)
      ((joiningSpectatorColumns (τ := RemainingCfg) child).submatrix id u.symm)).submatrix
        (fun x : Cfg d (logicalSiteCount d D N) ↦ x ∘ siteEquiv) u =
      (initializedBasisMatrix (minimalIntervalOutputEmbedding hd U hU hbound j k) *
        (parent ⊗ₖ (1 : Matrix parentOutside parentOutside ℂ))).submatrix id
          (intervalJointInputConfigEquiv j m k hjm hmk) := by
  classical
  have htransport := encodedJoiningParent_pullback_columns hd hr E siteEquiv f em
    hEncoding (P m) (joiningSpectatorColumns (τ := RemainingCfg) child) u
  have hparent := initializedBasisMatrix_regroupedOutput_mul_normalizedParent
    hd U hU hbound B P c j k hjm hmk hP
  exact htransport.trans hparent

end MinimalIntervals

end MPUCircuit
