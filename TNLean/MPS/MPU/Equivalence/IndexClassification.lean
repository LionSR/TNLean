/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.Equivalence.EquivalenceIndex
import TNLean.MPS.MPU.CanonicalForm.CanonicalFormAncillaBlocking
import TNLean.MPS.MPU.CanonicalForm.MPUCanonicalForm
import TNLean.MPS.MPU.StandardForm.StandardFormInterpolation
import TNLean.MPS.MPU.StandardForm.StandardFormFromGates
import TNLean.MPS.MPU.Index.CompositionIndex

/-!
# Tensors with the same index are equivalent

This file proves the "if" half of clause (iv) of the Index Theorem,
arXiv:1703.09188, Theorem `IndexTh`, lines 857--865: two MPU tensors in
canonical form with the same index are equivalent.

The source argument attaches ancillas so that the physical dimensions agree,
blocks until both tensors are simple, and joins the gates \(u\) and \(v\) of the
two standard forms, which have the same input and output dimensions, by paths
of unitaries. The step from the gates back to the blocked tensors is not spelled
out in the source. Here it is supplied as follows, for an MPU tensor \(W\) in
canonical form of bond dimension \(D\) and \(m\ge D^2\).

1. \(W\) is gauge equivalent to a tensor \(Y\) in canonical form II
   (`IsMPU.exists_gauge_isMPUCanonicalFormII_of_isMPUCanonicalForm`), and a path
   of invertible gauges joins \(W_{2m}\) to \(Y_{2m}\).
2. \(Y_m\) is simple, and \(Y_{2m}\) is the two-site block of \(Y_m\), which has a
   standard form with the gates \(u,v\) of \(Y_m\).
3. The tensor built from \(u\) and \(v\) has a standard form with the same gates,
   and the two presentations are joined by interpolating their half factors
   (`TwoSiteStandardFormData.joinedIn_padBond`).

**Local fix (missing step, arXiv:1703.09188, lines 857--865):** the source
passes from the gates to the tensors without connecting a tensor to the tensor
built from its own gates; steps 1--3 above supply this. See
`docs/paper-gaps/mpu_index_classification_tensor_to_gates.tex`.

## Main statements

* `MPOTensor.IsMPU.exists_joinedIn_standardFormTensorOfGates`: \(W_{2m}\) is
  joined, after padding, to the tensor built from two unitary gates whose
  intermediate dimensions record the index of \(W\).
* `MPOTensor.IsMPU.strictlyEquivalent_blockTensor_of_index_eq`: tensors of equal
  physical dimension and equal index are strictly equivalent after blocking.
* `MPOTensor.IsMPU.equivalent_of_index_eq`: tensors with the same index are
  equivalent.
* `MPOTensor.IsMPU.equivalent_iff_index_eq`: clause (iv) of the Index Theorem.
-/

open scoped Matrix

namespace MPOTensor

variable {c D : ℕ}

private theorem reindexPhysical_finCongr_refl' {d D : ℕ} (U : MPOTensor d D) (h : d = d) :
    reindexPhysical (finCongr h).symm U = U := by
  funext i j
  simp [reindexPhysical]

/-- **A blocked tensor is joined to the tensor of its standard-form gates.** Let
\(W\) be an MPU tensor in canonical form of bond dimension \(D\), and let
\(m\ge D^2\). There are unitary gates \(u,v\) between \(n^2\)-dimensional
physical space and an \(\ell\times r\) intermediate space, \(n=c^m\), with
\(r\ell=c^{2m}\) and
\(\operatorname{ind}(W)=\tfrac12(\log_2 r-\log_2\ell)\), such that \(W_{2m}\) and
the tensor built from \(u,v\), relabelled as a tensor on blocks of \(2m\) sites,
are joined by a path of MPU tensors after adjoining unused bond directions up to
\(D+nr\).

Source: arXiv:1703.09188, proof of Theorem `IndexTh` (iv), "if",
lines 857--865, with equation `StandardForm` and Definition `SF`,
lines 603--622, and Definition `def:index`, lines 681--688. -/
theorem IsMPU.exists_joinedIn_standardFormTensorOfGates [NeZero c] [NeZero D]
    {W : MPOTensor c D} (hW : IsMPU W)
    (hcf : MPTensor.IsMPUCanonicalForm W.toMPSTensor) {m : ℕ} (hm : D * D ≤ m) :
    ∃ (ℓ r : ℕ) (_ : NeZero ℓ) (_ : NeZero r)
      (u : Matrix (Fin ℓ × Fin r)
        (Fin (Kraus.blockPhysDim c m) × Fin (Kraus.blockPhysDim c m)) ℂ)
      (v : Matrix (Fin (Kraus.blockPhysDim c m) × Fin (Kraus.blockPhysDim c m))
        (Fin r × Fin ℓ) ℂ),
      u.IsUnitaryBetween ∧ v.IsUnitaryBetween ∧ r * ℓ = c ^ (2 * m) ∧
        hW.index = (1 / 2 : ℝ) * (Real.logb 2 r - Real.logb 2 ℓ) ∧
        JoinedIn {X | IsMPU X}
          (MPOTensor.padBond (MPOTensor.blockTensor W (2 * m)) (D + Kraus.blockPhysDim c m * r)
            (Nat.le_add_right _ _))
          (MPOTensor.reindexPhysical (twoSiteDirectBlockEquiv c m)
            (MPOTensor.padBond (standardFormTensorOfGates u v)
              (D + Kraus.blockPhysDim c m * r) (Nat.le_add_left _ _))) := by
  have hm0 : 0 < m := lt_of_lt_of_le (Nat.mul_pos (NeZero.pos D) (NeZero.pos D)) hm
  have : NeZero (Kraus.blockPhysDim c m) := ⟨by
    rw [Kraus.blockPhysDim_eq_pow]
    exact pow_ne_zero m (NeZero.ne c)⟩
  obtain ⟨X, ⟨hY⟩⟩ := hW.exists_gauge_isMPUCanonicalFormII_of_isMPUCanonicalForm hcf
  set Y := MPOTensor.virtualSandwich (X : Matrix (Fin D) (Fin D) ℂ) W
    ((X⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) with hYdef
  have hYm := hY.blockTensor m hm0
  have hsimple : IsMPUSimple (MPOTensor.blockTensor Y m) :=
    hY.isMPU.blockTensor_isMPUSimple_of_sq_le hm
  let S := hYm.twoSiteStandardFormData hsimple
  have : NeZero ℓ[MPOTensor.blockTensor Y m] := ⟨S.left_pos.ne'⟩
  have : NeZero r[MPOTensor.blockTensor Y m] := ⟨S.right_pos.ne'⟩
  let S' := standardFormTensorOfGatesData _ _ S.u_unitary S.v_unitary
  refine ⟨ℓ[MPOTensor.blockTensor Y m], r[MPOTensor.blockTensor Y m], inferInstance,
    inferInstance, _, _, S.u_unitary, S.v_unitary,
    hY.rightRank_mul_leftRank_blockTensor hm0 hsimple, ?_, ?_⟩
  · have hmpo : ∀ N : ℕ, 0 < N → mpo Y N = mpo W N := fun N _ ↦
      mpo_virtualSandwich _ W _ (Units.inv_mul X) N
    rw [hW.index_eq_canonical_representative hY hmpo,
      hY.index_eq_logb_of_isMPUSimple_blockTensor hm0 hsimple]
  · have hC := JoinedIn.reindexPhysical (twoSiteDirectBlockEquiv c m) (S.joinedIn_padBond S')
    have hleft : MPOTensor.reindexPhysical (twoSiteDirectBlockEquiv c m)
        (MPOTensor.padBond (blockTwo (MPOTensor.blockTensor Y m))
          (D + Kraus.blockPhysDim c m * r[MPOTensor.blockTensor Y m])
          (Nat.le_add_right _ _)) =
        MPOTensor.padBond (MPOTensor.blockTensor Y (2 * m))
          (D + Kraus.blockPhysDim c m * r[MPOTensor.blockTensor Y m])
          (Nat.le_add_right _ _) := by
      rw [← reindexPhysical_blockTwo_blockTensor_two_mul Y m]
      rfl
    rw [hleft] at hC
    have hdet : IsUnit (X : Matrix (Fin D) (Fin D) ℂ).det :=
      (Matrix.isUnit_iff_isUnit_det _).mp X.isUnit
    have hG := JoinedIn.padBond
      ((hW.blockTensor (2 * m) (by omega)).joinedIn_virtualSandwich hdet)
      (D + Kraus.blockPhysDim c m * r[MPOTensor.blockTensor Y m]) (Nat.le_add_right _ _)
    have hYk : MPOTensor.virtualSandwich (X : Matrix (Fin D) (Fin D) ℂ)
        (MPOTensor.blockTensor W (2 * m)) (X : Matrix (Fin D) (Fin D) ℂ)⁻¹ =
        MPOTensor.blockTensor Y (2 * m) := by
      rw [hYdef, blockTensor_virtualSandwich _ _ _ (Units.inv_mul X), Matrix.coe_units_inv]
    rw [hYk] at hG
    exact hG.trans hC

/-- Equal index and equal rank product force equal ranks. -/
private theorem rank_eq_of_index_eq {ℓ₁ r₁ ℓ₂ r₂ : ℕ} (hℓ₁ : 0 < ℓ₁) (hr₁ : 0 < r₁)
    (hℓ₂ : 0 < ℓ₂) (hr₂ : 0 < r₂) (hprod : r₁ * ℓ₁ = r₂ * ℓ₂)
    (hidx : (1 / 2 : ℝ) * (Real.logb 2 r₁ - Real.logb 2 ℓ₁) =
      (1 / 2 : ℝ) * (Real.logb 2 r₂ - Real.logb 2 ℓ₂)) :
    r₁ = r₂ ∧ ℓ₁ = ℓ₂ := by
  have hprod' : Real.logb 2 r₁ + Real.logb 2 ℓ₁ = Real.logb 2 r₂ + Real.logb 2 ℓ₂ := by
    rw [← Real.logb_mul (by positivity) (by positivity),
      ← Real.logb_mul (by positivity) (by positivity)]
    exact_mod_cast congrArg (fun n : ℕ ↦ Real.logb 2 (n : ℝ)) hprod
  have hr : Real.logb 2 r₁ = Real.logb 2 r₂ := by linarith
  have hℓ : Real.logb 2 ℓ₁ = Real.logb 2 ℓ₂ := by linarith
  have hinj : ∀ {a b : ℕ}, 0 < a → 0 < b → Real.logb 2 a = Real.logb 2 b → a = b := by
    intro a b ha hb h
    have := Real.logb_injOn_pos (b := 2) (by norm_num)
      (Set.mem_Ioi.mpr (by exact_mod_cast ha)) (Set.mem_Ioi.mpr (by exact_mod_cast hb)) h
    exact_mod_cast this
  exact ⟨hinj hr₁ hr₂ hr, hinj hℓ₁ hℓ₂ hℓ⟩

/-- **Tensors of equal physical dimension and equal index are strictly
equivalent after blocking.** Let \(W_1\), \(W_2\) be MPU tensors in canonical
form of the same physical dimension and bond dimensions \(D_1\), \(D_2\), with
the same index, and let \(m\ge D_1^2,D_2^2\). Then their blocks of \(2m\) sites
are strictly equivalent.

Source: arXiv:1703.09188, proof of Theorem `IndexTh` (iv), "if",
lines 857--865, and Definition `def:strictly-equivalent-tensors`,
lines 708--714. -/
theorem IsMPU.strictlyEquivalent_blockTensor_of_index_eq {c₁ c₂ D₁ D₂ : ℕ}
    [NeZero c₁] [NeZero c₂] [NeZero D₁] [NeZero D₂]
    {W₁ : MPOTensor c₁ D₁} {W₂ : MPOTensor c₂ D₂} (h₁ : IsMPU W₁) (h₂ : IsMPU W₂)
    (hcf₁ : MPTensor.IsMPUCanonicalForm W₁.toMPSTensor)
    (hcf₂ : MPTensor.IsMPUCanonicalForm W₂.toMPSTensor)
    (hc : c₁ = c₂) (hidx : h₁.index = h₂.index) {m : ℕ}
    (hm₁ : D₁ * D₁ ≤ m) (hm₂ : D₂ * D₂ ≤ m)
    (hphys : Kraus.blockPhysDim c₁ (2 * m) = Kraus.blockPhysDim c₂ (2 * m)) :
    StrictlyEquivalent (MPOTensor.blockTensor W₁ (2 * m)) (MPOTensor.blockTensor W₂ (2 * m))
      hphys := by
  subst hc
  have hm0 : 0 < m := lt_of_lt_of_le (Nat.mul_pos (NeZero.pos D₁) (NeZero.pos D₁)) hm₁
  have : NeZero (Kraus.blockPhysDim c₁ m) := ⟨by
    rw [Kraus.blockPhysDim_eq_pow]
    exact pow_ne_zero m (NeZero.ne c₁)⟩
  obtain ⟨ℓ₁, r₁, _, _, u₁, v₁, hu₁, hv₁, hprod₁, hi₁, hP₁⟩ :=
    h₁.exists_joinedIn_standardFormTensorOfGates hcf₁ hm₁
  obtain ⟨ℓ₂, r₂, _, _, u₂, v₂, hu₂, hv₂, hprod₂, hi₂, hP₂⟩ :=
    h₂.exists_joinedIn_standardFormTensorOfGates hcf₂ hm₂
  obtain ⟨rfl, rfl⟩ := rank_eq_of_index_eq (NeZero.pos ℓ₁) (NeZero.pos r₁)
    (NeZero.pos ℓ₂) (NeZero.pos r₂) (hprod₁.trans hprod₂.symm) (hi₁.symm.trans
      (hidx.trans hi₂))
  set D' := D₁ + D₂ + Kraus.blockPhysDim c₁ m * r₁
  have hle₁ : D₁ + Kraus.blockPhysDim c₁ m * r₁ ≤ D' := by omega
  have hle₂ : D₂ + Kraus.blockPhysDim c₁ m * r₁ ≤ D' := by omega
  refine ⟨h₁.isMPUCanonicalForm_blockTensor hcf₁ (by omega),
    h₂.isMPUCanonicalForm_blockTensor hcf₂ (by omega), D', by omega, by omega, ?_⟩
  rw [reindexPhysical_finCongr_refl']
  have hQ₁ := JoinedIn.padBond hP₁ D' hle₁
  have hQ₂ := JoinedIn.padBond hP₂ D' hle₂
  have hG := JoinedIn.reindexPhysical (twoSiteDirectBlockEquiv c₁ m)
    (JoinedIn.padBond (joinedIn_standardFormTensorOfGates hu₁ hu₂ hv₁ hv₂) D' (by omega))
  have hpad : ∀ {D₀ E : ℕ} (X : MPOTensor (Kraus.blockPhysDim c₁ m *
      Kraus.blockPhysDim c₁ m) D₀) (ha : D₀ ≤ E) (hb : E ≤ D'),
      MPOTensor.padBond (MPOTensor.reindexPhysical (twoSiteDirectBlockEquiv c₁ m)
        (MPOTensor.padBond X E ha)) D' hb =
      MPOTensor.reindexPhysical (twoSiteDirectBlockEquiv c₁ m)
        (MPOTensor.padBond X D' (ha.trans hb)) := by
    intro D₀ E X ha hb
    change MPOTensor.reindexPhysical _ (MPOTensor.padBond (MPOTensor.padBond X E ha) D' hb) = _
    rw [padBond_padBond]
  rw [padBond_padBond, hpad] at hQ₁
  rw [padBond_padBond, hpad] at hQ₂
  exact (hQ₁.trans hG).trans hQ₂.symm

/-- **Tensors with the same index are equivalent.** Two MPU tensors in canonical
form, of positive physical and bond dimensions, with the same index are
equivalent: after attaching coprime identity ancillas that equalize their
physical dimensions and blocking, they are strictly equivalent.

Source: arXiv:1703.09188, Theorem `IndexTh` (iv), "if", lines 857--865, and
Definition `def:equivalent-tensors`, lines 716--724. -/
theorem IsMPU.equivalent_of_index_eq {da db Da Db : ℕ}
    [NeZero da] [NeZero db] [NeZero Da] [NeZero Db]
    {U : MPOTensor da Da} {V : MPOTensor db Db} (hU : IsMPU U) (hV : IsMPU V)
    (hUcf : MPTensor.IsMPUCanonicalForm U.toMPSTensor)
    (hVcf : MPTensor.IsMPUCanonicalForm V.toMPSTensor)
    (h : hU.index = hV.index) : Equivalent U V := by
  set g := Nat.gcd da db with hg
  have hg0 : 0 < g := Nat.gcd_pos_of_pos_left _ (NeZero.pos da)
  set pa := db / g
  set pb := da / g
  have hda : da = g * pb := (Nat.mul_div_cancel' (Nat.gcd_dvd_left da db)).symm
  have hdb : db = g * pa := (Nat.mul_div_cancel' (Nat.gcd_dvd_right da db)).symm
  have hpa : 0 < pa := Nat.div_pos (Nat.le_of_dvd (NeZero.pos db) (Nat.gcd_dvd_right _ _)) hg0
  have hpb : 0 < pb := Nat.div_pos (Nat.le_of_dvd (NeZero.pos da) (Nat.gcd_dvd_left _ _)) hg0
  have hcop : Nat.Coprime pa pb :=
    (Nat.coprime_div_gcd_div_gcd hg0 : Nat.Coprime (da / g) (db / g)).symm
  have hphys : pa * da = pb * db := by
    rw [hda, hdb]
    ring
  have : NeZero pa := ⟨hpa.ne'⟩
  have : NeZero pb := ⟨hpb.ne'⟩
  set m := Da * Da + Db * Db
  have hm₁ : Da * Da ≤ m := Nat.le_add_right _ _
  have hm₂ : Db * Db ≤ m := Nat.le_add_left _ _
  have hk : 0 < 2 * m := by
    have := Nat.mul_pos (NeZero.pos Da) (NeZero.pos Da)
    omega
  refine ⟨hU, hV, 2 * m, pa, pb, hk, hpa, hpb, hcop, hphys, ?_⟩
  apply IsMPU.strictlyEquivalent_blockTensor_of_index_eq (hU.tensorPhysicalId pa hpa)
    (hV.tensorPhysicalId pb hpb) (hU.isMPUCanonicalForm_tensorPhysicalId hUcf hpa)
    (hV.isMPUCanonicalForm_tensorPhysicalId hVcf hpb)
    (by rw [Nat.mul_comm da, Nat.mul_comm db]; exact hphys) _ hm₁ hm₂
  rw [hU.index_tensorPhysicalId pa, hV.index_tensorPhysicalId pb, h]

/-- **Clause (iv) of the Index Theorem.** Two MPU tensors in canonical form, of
positive physical and bond dimensions, have the same index if and only if they
are equivalent.

The canonical-form hypotheses `hUcf` and `hVcf` are the source's, not added
hypotheses. The compared tensors are in canonical form: "Two tensors
\(\mathcal U\) and \(\mathcal V\) in CF are strictly equivalent if … there
exist a continuous path \(\mathcal W(p)\) of tensors, not necessarily in CF"
(Definition `def:strictly-equivalent-tensors`, arXiv:1703.09188,
lines 708--714). The qualifier "not necessarily in CF" attaches only to the
path: "we do not impose that the tensors in the path are in CF"
(lines 733--736). Equivalence (lines 716--721) is strict equivalence of the
blocked tensors with ancilla, which are in canonical form when \(\mathcal U\)
and \(\mathcal V\) are (`IsMPU.isMPUCanonicalForm_blockTensor_tensorPhysicalId`).
This is also the standing convention of lines 325--326. The standard form used in
the proof is that of a simple tensor in canonical form II, the reading recorded in
`docs/paper-gaps/mpu_standard_form_canonical_convention.tex`.

Source: arXiv:1703.09188, Theorem `IndexTh` (iv), lines 830--831 and
852--865. -/
theorem IsMPU.equivalent_iff_index_eq {da db Da Db : ℕ}
    [NeZero da] [NeZero db] [NeZero Da] [NeZero Db]
    {U : MPOTensor da Da} {V : MPOTensor db Db} (hU : IsMPU U) (hV : IsMPU V)
    (hUcf : MPTensor.IsMPUCanonicalForm U.toMPSTensor)
    (hVcf : MPTensor.IsMPUCanonicalForm V.toMPSTensor) :
    Equivalent U V ↔ hU.index = hV.index :=
  ⟨fun h' ↦ h'.index_eq hU hV, hU.equivalent_of_index_eq hV hUcf hVcf⟩

/-- **The Index Theorem.** For MPU tensors of positive physical and bond
dimensions, the index

1. does not change under positive blocking;
2. is additive under tensor products and composition;
3. is constant along continuous paths of MPU tensors, not necessarily in
   canonical form;
4. agrees for two tensors in canonical form exactly when they are equivalent.

Clauses (i)--(iii) hold for every positive-dimensional MPU tensor. In clause
(iv), canonical form is the source's standing convention (arXiv:1703.09188,
lines 325--326); see `IsMPU.equivalent_iff_index_eq`.

Source: arXiv:1703.09188, Theorem `IndexTh`, lines 824--865. -/
theorem IsMPU.indexTheorem :
    (∀ {d D : ℕ} [NeZero d] [NeZero D] {U : MPOTensor d D} (hU : IsMPU U)
      (p : ℕ) (hp : 0 < p), (hU.blockTensor p hp).index = hU.index) ∧
    (∀ {d D e E : ℕ} [NeZero d] [NeZero D] [NeZero e] [NeZero E]
      {U : MPOTensor d D} {V : MPOTensor e E} (hU : IsMPU U) (hV : IsMPU V),
      (hU.tensorProduct hV).index = hU.index + hV.index) ∧
    (∀ {d D₁ D₂ : ℕ} [NeZero d] [NeZero D₁] [NeZero D₂]
      {U : MPOTensor d D₁} {V : MPOTensor d D₂} (hU : IsMPU U) (hV : IsMPU V),
      (hU.mulTensor hV).index = hU.index + hV.index) ∧
    (∀ {d D : ℕ} [NeZero d] [NeZero D] {W : unitInterval → MPOTensor d D}
      (_ : Continuous W) (hMPU : ∀ x, IsMPU (W x)) (x y : unitInterval),
      (hMPU x).index = (hMPU y).index) ∧
    (∀ {da db Da Db : ℕ} [NeZero da] [NeZero db] [NeZero Da] [NeZero Db]
      {U : MPOTensor da Da} {V : MPOTensor db Db} (hU : IsMPU U) (hV : IsMPU V),
      MPTensor.IsMPUCanonicalForm U.toMPSTensor →
      MPTensor.IsMPUCanonicalForm V.toMPSTensor →
      (Equivalent U V ↔ hU.index = hV.index)) :=
  ⟨fun hU p hp ↦ hU.index_blockTensor p hp, fun hU hV ↦ hU.index_tensorProduct hV,
    fun hU hV ↦ IsMPU.index_mulTensor hU hV,
    fun hW hMPU x y ↦ IsMPU.index_const_of_continuous hW hMPU x y,
    fun hU hV hUcf hVcf ↦ hU.equivalent_iff_index_eq hV hUcf hVcf⟩

end MPOTensor
