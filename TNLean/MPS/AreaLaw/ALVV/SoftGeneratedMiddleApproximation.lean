/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.SoftTruncatedHamiltonianMPO
import TNLean.MPS.AreaLaw.NativeIntervalMPOApproximation
import TNLean.MPS.AreaLaw.RetainedCoreFamilies
import TNLean.MPS.AreaLaw.PhysicalIntervalTransport
import TNLean.MPS.AreaLaw.RegionalBondRestriction
import TNLean.Circuit.SiteEmbeddingNorm
import TNLean.Circuit.SupportedFunctionalCalculus
import TNLean.MPS.MPDO.TraceChainHermitian
import QICLean.Analysis.PrincipalSubmatrixNorm

/-!
# A native middle approximation of the same soft Hamiltonian

The middle soft term is approximated on its actual interval. A fixed exterior
configuration restricts the constructed operator tensors to that interval without
increasing their virtual dimension. Placing the resulting native matrix back on the
original chain preserves the error. The exterior soft terms and the two unchanged
windows are retained exactly.

These operator constructions support ALVV, arXiv:1602.08828v2,
`prop:Cheby-AGSP-eff` and `t:aisefficient`, source lines 1309–1333 and 1373–1420.
They do not assert a spectral gap, an improving family, or a running-time bound.

**Local fix (cluster selector and normalization):** the middle approximation uses
the corrected interaction-label cluster estimate and its energy normalization,
rather than the false printed physical-support estimate; see
`docs/paper-gaps/alvv16_cluster_approximation.tex`.
-/

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace TNLean.MPS.AreaLaw.ALVV

/-- The actual soft replacement of an interval has Hermitian native
operator tensors at any prescribed norm accuracy. The virtual dimension is
explicit. Its placement on the original chain approximates precisely the same
soft term. Auxiliary to ALVV, arXiv:1602.08828v2, `lem:exp-approx-eff`,
`prop:Cheby-AGSP-eff`, lines 1262–1268 and 1309–1333.

The lower energy is a scalar parameter satisfying the defining order condition;
no native Hamiltonian, heat approximation, operator tensor or rank bound is supplied. -/
theorem exists_native_soft_middle_mpo_approximation {N q l r m : ℕ}
    (hq : 0 < q) (hlr : l ≤ r) (hrL : r ≤ N + 1) (hm : 0 < m)
    (h : Fin N → Matrix (Fin (N + 1) → Fin q) (Fin (N + 1) → Fin q) ℂ)
    (hs : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin (N + 1) ↦ q)
      (h i) (interval (N + 1) i.val (i.val + 2)))
    (h0 : ∀ i, 0 ≤ h i) (h1 : ∀ i, h i ≤ 1)
    (p t xi : ℝ)
    (hlo : (p : ℂ) • 1 ≤ ∑ i ∈ Finset.univ.filter
      (fun i : Fin N ↦ l ≤ i.val ∧ i.val + 1 < r), h i)
    (hscale : 3 * (m : ℝ) ≤ t) (hxi : 0 < xi) :
    let A := ∑ i ∈ Finset.univ.filter
      (fun i : Fin N ↦ l ≤ i.val ∧ i.val + 1 < r), h i
    let P := (p : ℂ) • 1 + cfc (Real.softTruncation t m) (A - (p : ℂ) • 1)
    let sigma0 : Fin (N + 1) → Fin q := fun _ ↦ ⟨0, hq⟩
    let insert := insertInterval (L := r - l) l sigma0
    let eJ := intervalShiftOrderIso hlr hrL
    let W := t * (2 : ℝ) ^ (m + 1)
    let b := 2 * (Real.exp (1 / 3 : ℝ) - 1)
    let order := max 1 ⌈(Real.log (max 1 ((N : ℝ) ^ 2)) -
      Real.log (Real.log (1 + xi / W))) / (-Real.log b)⌉₊
    let bond := ((1 + N * q ^ 2) + (order ^ 2 * q ^ order) * (m + 1)) * 2
    ∃ (Acore : Fin (r - l) → MPOTensor q bond)
      (C0 : Matrix (Fin bond) (Fin bond) ℂ),
      let Z := MPOTensor.traceChainOperator Acore C0
      let Zphys := QuantumCircuit.embedOp
        (Subtype.val : interval (N + 1) l r → Fin (N + 1))
        (QuantumCircuit.embedOp eJ Z)
      Z.IsHermitian ∧ Zphys.IsHermitian ∧
        P = QuantumCircuit.embedOp
          (Subtype.val : interval (N + 1) l r → Fin (N + 1))
          (QuantumCircuit.embedOp eJ (P.submatrix insert insert)) ∧
        ‖P.submatrix insert insert - Z‖ ≤ xi ∧ ‖P - Zphys‖ ≤ xi := by
  classical
  intro A P sigma0 insert eJ W b order bond
  let g := intervalBondRestriction (L := N + 1) l r h
  have hgs (i : Fin N) : Entropy.IsSupportedOn (n := fun _ : Fin (N + 1) ↦ q)
      (g i) {i.castSucc, i.succ} := by
    apply (intervalBondRestriction_supported (L := N + 1) (q := q) l r h hs i).mono
    intro j hj
    have hj' := mem_interval.mp hj
    simp only [Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]
    change j.val = i.val ∨ j.val = i.val + 1
    omega
  have hsumg : (∑ i, g i) = A :=
    sum_intervalBondRestriction (L := N + 1) (q := q) l r h
  obtain ⟨Aglobal, hGlobal⟩ :=
    let hb : ∀ i : Fin N, 0 ≤ g i ∧ g i ≤ 1 := fun i ↦
      intervalBondRestriction_bounds (L := N + 1) (q := q) l r h h0 h1 i
    exists_softTruncatedHamiltonian_mpo_of_accuracy (N := N) (q := q) (m := m)
      (by omega) hm g hgs
      (fun i ↦ (hb i).1.posSemidef.isHermitian)
      (fun i ↦ (CStarAlgebra.norm_le_one_iff_of_nonneg (g i) (hb i).1).mpr (hb i).2)
      Finset.univ p t xi
      (hlo.trans_eq hsumg.symm) hscale hxi
  have hP : P.IsHermitian :=
    (isHermitian_one.smul (by simp [isSelfAdjoint_iff])).add
      (cfc_predicate (Real.softTruncation t m) (A - (p : ℂ) • 1))
  have hGlobalError : ‖P - MPOTensor.traceChainOperator Aglobal 1‖ ≤ xi := by
    change ‖((∑ i, g i) - (∑ i, g i) + (p : ℂ) • 1 +
      cfc (Real.softTruncation t m) ((∑ i, g i) - (p : ℂ) • 1)) -
      MPOTensor.traceChainOperator Aglobal 1‖ ≤ xi at hGlobal
    rw [sub_self, zero_add, hsumg] at hGlobal
    exact hGlobal
  obtain ⟨Ah, hAh, hAhError⟩ :=
    MPOTensor.exists_hermitian_traceChainOperator_approximation (by omega) hP Aglobal hGlobalError
  have hPs : Entropy.IsSupportedOn (n := fun _ : Fin (N + 1) ↦ q)
      P (interval (N + 1) l r) := by
    let V := QuantumCircuit.supportedOperators q
      (interval (N + 1) l r : Set (Fin (N + 1)))
    have hAs : A ∈ V := QuantumCircuit.mem_supportedOperators_of_isSupportedOn
      (isSupportedOn_sum_internal_bonds (N + 1) q l r h hs)
    have hp : (p : ℂ) • (1 : Matrix (Fin (N + 1) → Fin q)
        (Fin (N + 1) → Fin q) ℂ) ∈ V :=
      V.smul_mem _ (QuantumCircuit.one_mem_supportedOperators _)
    exact QuantumCircuit.isSupportedOn_of_mem_supportedOperators
      (V.add_mem hp (QuantumCircuit.cfc_mem_supportedOperators _ (V.sub_mem hAs hp)))
  obtain ⟨Acore, C0, hZ, hZphys, hRecon, hNativeError, hPlacedError⟩ :=
    exists_native_interval_slice_of_mpo_approximation hq hlr hrL P hPs Ah hAh xi hAhError
  refine ⟨Acore, C0, hZ, ?_, ?_, hNativeError, ?_⟩
  · simpa only [QuantumCircuit.embedOp_embedOp Subtype.val_injective,
      eJ, insert, sigma0, Function.comp_def] using hZphys
  · simpa only [QuantumCircuit.embedOp_embedOp Subtype.val_injective,
      eJ, insert, sigma0, Function.comp_def] using hRecon
  · simpa only [QuantumCircuit.embedOp_embedOp Subtype.val_injective,
      eJ, insert, sigma0, Function.comp_def] using hPlacedError

/-- Replacing only the middle term by its constructed native approximation
preserves the exact exterior soft terms, all unchanged regions and the actual
crossing bonds. The resulting full matrix is Hermitian and has the requested
error from the same five-region soft Hamiltonian. Operator auxiliary to ALVV,
arXiv:1602.08828v2, `t:aisefficient`, source lines 1373–1420.

The regional shifts are arbitrary real scalars. The only lower-energy condition
needed for this representation is that of the middle soft term. In applications
the shifts and this condition are those already constructed by
`exists_five_region_soft_representation`; they are not chosen a second time. -/
theorem exists_five_region_soft_middle_mpo_approximation {N q k1 k2 k3 k4 m : ℕ}
    (hq : 0 < q) (_h12 : k1 ≤ k2) (h23 : k2 ≤ k3)
    (h34 : k3 ≤ k4) (h4L : k4 ≤ N + 1) (hm : 0 < m)
    (h : Fin N → Matrix (Fin (N + 1) → Fin q) (Fin (N + 1) → Fin q) ℂ)
    (hs : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin (N + 1) ↦ q)
      (h i) (interval (N + 1) i.val (i.val + 2)))
    (h0 : ∀ i, 0 ≤ h i) (h1 : ∀ i, h i ≤ 1)
    (e p : Fin 5 → ℝ) (S : Finset (Fin 5)) (h2S : 2 ∈ S)
    (t xi : ℝ)
    (hlo : (p 2 : ℂ) • 1 ≤ ∑ i ∈ Finset.univ.filter
      (fun i : Fin N ↦ k2 ≤ i.val ∧ i.val + 1 < k3), h i)
    (hscale : 3 * (m : ℝ) ≤ t) (hxi : 0 < xi) :
    let k : Fin 6 → ℕ := ![0, k1, k2, k3, k4, N + 1]
    let A := fun j : Fin 5 ↦ ∑ i ∈ Finset.univ.filter
      (fun i : Fin N ↦ k j.castSucc ≤ i.val ∧ i.val + 1 < k j.succ), h i
    let Y := ∑ i ∈ Finset.univ.filter
      (fun i : Fin N ↦ i.val + 1 ∈ ({k1, k2, k3, k4} : Finset ℕ)), h i
    let F := fun j : Fin 5 ↦ (p j : ℂ) • 1 +
      cfc (Real.softTruncation t m) (A j - (p j : ℂ) • 1)
    let G := (∑ j, ((if j ∈ S then F j else A j) - (e j : ℂ) • 1)) + Y
    let eJ := intervalShiftOrderIso h23 (h34.trans h4L)
    let W := t * (2 : ℝ) ^ (m + 1)
    let b := 2 * (Real.exp (1 / 3 : ℝ) - 1)
    let order := max 1 ⌈(Real.log (max 1 ((N : ℝ) ^ 2)) -
      Real.log (Real.log (1 + xi / W))) / (-Real.log b)⌉₊
    let bond := ((1 + N * q ^ 2) + (order ^ 2 * q ^ order) * (m + 1)) * 2
    ∃ (Acore : Fin (k3 - k2) → MPOTensor q bond)
      (C0 : Matrix (Fin bond) (Fin bond) ℂ),
      let Z := MPOTensor.traceChainOperator Acore C0
      let Zphys := QuantumCircuit.embedOp
        (Subtype.val : interval (N + 1) k2 k3 → Fin (N + 1))
        (QuantumCircuit.embedOp eJ Z)
      let Ghat := (∑ j, ((if j = 2 then Zphys else
        if j ∈ S then F j else A j) - (e j : ℂ) • 1)) + Y
      Z.IsHermitian ∧ G.IsHermitian ∧ Ghat.IsHermitian ∧
        Ghat = G - F 2 + Zphys ∧ ‖G - Ghat‖ ≤ xi := by
  classical
  intro k A Y F G eJ W b order bond
  obtain ⟨Acore, C0, hZ, hZphys, _hRecon, _hNativeError, hMiddleError⟩ :=
    exists_native_soft_middle_mpo_approximation hq h23 (h34.trans h4L) hm
      h hs h0 h1 (p 2) t xi hlo hscale hxi
  let Z := MPOTensor.traceChainOperator Acore C0
  let Zphys := QuantumCircuit.embedOp
    (Subtype.val : interval (N + 1) k2 k3 → Fin (N + 1))
    (QuantumCircuit.embedOp eJ Z)
  change Z.IsHermitian at hZ
  change Zphys.IsHermitian at hZphys
  change ‖F 2 - Zphys‖ ≤ xi at hMiddleError
  have hA (j : Fin 5) : (A j).IsHermitian :=
    (show 0 ≤ A j from Finset.sum_nonneg fun i _ ↦ h0 i).posSemidef.isHermitian
  have hF (j : Fin 5) : (F j).IsHermitian :=
    (isHermitian_one.smul (by simp [isSelfAdjoint_iff])).add
      (cfc_predicate (Real.softTruncation t m) (A j - (p j : ℂ) • 1))
  have hG : G.IsHermitian := by
    apply Matrix.IsHermitian.add
    · apply isHermitian_sum
      intro j _
      apply Matrix.IsHermitian.sub
      · split_ifs
        · exact hF j
        · exact hA j
      · exact isHermitian_one.smul (by simp [isSelfAdjoint_iff])
    · exact isHermitian_sum _ (fun i _ ↦ (h0 i).posSemidef.isHermitian)
  let Ghat := (∑ j, ((if j = 2 then Zphys else
    if j ∈ S then F j else A j) - (e j : ℂ) • 1)) + Y
  have hreplace (j : Fin 5) :
      ((if j = 2 then Zphys else if j ∈ S then F j else A j) - (e j : ℂ) • 1) =
        ((if j ∈ S then F j else A j) - (e j : ℂ) • 1) +
          (if j = 2 then Zphys - F 2 else 0) := by
    by_cases hj : j = 2
    · subst j
      simp only [ite_true, ite_eq_left h2S]
      abel
    · simp only [ite_eq_right hj, add_zero]
  have hhat : Ghat = G - F 2 + Zphys := by
    have hsum : (∑ j, ((if j = 2 then Zphys else
        if j ∈ S then F j else A j) - (e j : ℂ) • 1)) =
        (∑ j, ((if j ∈ S then F j else A j) - (e j : ℂ) • 1)) + (Zphys - F 2) := by
      simp_rw [hreplace]
      rw [Finset.sum_add_distrib]
      simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    change (∑ j, ((if j = 2 then Zphys else
      if j ∈ S then F j else A j) - (e j : ℂ) • 1)) + Y = G - F 2 + Zphys
    rw [hsum]
    change _ = ((∑ j, ((if j ∈ S then F j else A j) - (e j : ℂ) • 1)) + Y) - F 2 + Zphys
    abel
  have hGhat : Ghat.IsHermitian := by
    rw [hhat]
    exact (hG.sub (hF 2)).add hZphys
  have hDifference : G - Ghat = F 2 - Zphys := by
    rw [hhat]
    abel
  exact ⟨Acore, C0, hZ, hG, hGhat, hhat,
    (congrArg norm hDifference).le.trans hMiddleError⟩

end TNLean.MPS.AreaLaw.ALVV
