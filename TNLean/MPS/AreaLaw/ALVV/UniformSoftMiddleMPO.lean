/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.NativeIntervalMPOApproximation
import TNLean.MPS.AreaLaw.SoftTruncationMPOAccuracy
import TNLean.MPS.AreaLaw.RegionalBondRestriction
import TNLean.MPS.MPDO.TraceChainHermitian
import TNLean.Circuit.SupportedFunctionalCalculus
import QICLean.Analysis.SoftTruncationHeatExpansion
import Mathlib.Tactic.Module

/-!
# A common middle approximation before the estimated energy

The heat operators are constructed at one lower regional energy. Their
Hermitian native approximations are chosen once. The estimated energy enters
only through powers of one scalar in the closing matrix; the site tensors
are fixed before that estimate is supplied.

These are supporting operator constructions for ALVV, arXiv:1602.08828v2,
`lem:exp-approx-eff` and `prop:Cheby-AGSP-eff`, lines 1262–1268 and
1311–1333. No spectral gap or running-time estimate is asserted.

**Local fix (cluster cutoff and normalization):** the approximants use the
corrected interaction-label cluster estimate and its lower-energy
normalization. See `docs/paper-gaps/alvv16_cluster_approximation.tex`.
The physical lower-estimate convention remains that of `def:soft-trunc`.
-/

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace TNLean.MPS.AreaLaw.ALVV

private theorem heat_shift_to_fixed_center
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (e p t : ℝ) (a : ℕ) :
    NormedSpace.exp (-(((a : ℝ) / t) • (A - (p : ℂ) • 1))) =
      (Real.exp ((p - e) / t)) ^ a •
        NormedSpace.exp (-(((a : ℝ) / t) • (A - (e : ℂ) • 1))) := by
  have harg : -(((a : ℝ) / t) • (A - (p : ℂ) • 1)) =
      -(((a : ℝ) / t) • (A - (e : ℂ) • 1)) +
        ((a : ℝ) / t * (p - e)) • (1 : Matrix n n ℂ) := by
    simp only [smul_sub, neg_sub, ← Complex.coe_smul]
    module
  rw [harg, Matrix.exp_add_smul_one, ← Real.exp_nat_mul]
  congr 2
  ring

/-- The native soft middle has one fixed family of site tensors and
polynomial closing coefficients before every estimated lower energy. The
scalar estimated-energy identity is left outside the middle approximation.
All heat atoms are constructed from the original positive nearest-neighbour
interactions. Supporting ALVV, arXiv:1602.08828v2, `def:soft-trunc`,
`lem:exp-approx-eff` and `prop:Cheby-AGSP-eff`, lines 1178–1189,
1262–1268 and 1311–1333. -/
theorem exists_uniform_native_soft_middle_mpo {N q l r m : ℕ}
    (hq : 0 < q) (hlr : l ≤ r) (hrL : r ≤ N + 1) (hm : 0 < m)
    (h : Fin N → Matrix (Fin (N + 1) → Fin q) (Fin (N + 1) → Fin q) ℂ)
    (hs : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin (N + 1) ↦ q)
      (h i) (interval (N + 1) i.val (i.val + 2)))
    (h0 : ∀ i, 0 ≤ h i) (h1 : ∀ i, h i ≤ 1)
    (e t xi : ℝ)
    (hlo : (e : ℂ) • 1 ≤ ∑ i ∈ Finset.univ.filter
      (fun i : Fin N ↦ l ≤ i.val ∧ i.val + 1 < r), h i)
    (hscale : 3 * (m : ℝ) ≤ t) (hxi : 0 < xi) :
    let A := ∑ i ∈ Finset.univ.filter
      (fun i : Fin N ↦ l ≤ i.val ∧ i.val + 1 < r), h i
    let sigma0 : Fin (N + 1) → Fin q := fun _ ↦ ⟨0, hq⟩
    let insert := insertInterval (L := r - l) l sigma0
    let eJ := intervalShiftOrderIso hlr hrL
    let W := t * (2 : ℝ) ^ (m + 1)
    let base := 2 * (Real.exp (1 / 3 : ℝ) - 1)
    let order := max 1 ⌈(Real.log (max 1 ((N : ℝ) ^ 2)) -
      Real.log (Real.log (1 + xi / W))) / (-Real.log base)⌉₊
    let bond := ((order ^ 2 * q ^ order) * 2) * (m + 1)
    ∃ (Acore : Fin (r - l) → MPOTensor q bond)
      (C : Fin (m + 1) → Matrix (Fin bond) (Fin bond) ℂ),
      let Z := fun z : ℂ ↦ MPOTensor.traceChainOperator Acore
        (∑ a : Fin (m + 1), z ^ a.val • C a)
      let Zphys := fun z : ℂ ↦ QuantumCircuit.embedOp
        (Subtype.val : interval (N + 1) l r → Fin (N + 1))
        (QuantumCircuit.embedOp eJ (Z z))
      (∀ z : ℝ, (Z (z : ℂ)).IsHermitian ∧ (Zphys (z : ℂ)).IsHermitian) ∧
      ∀ p : ℝ, p ≤ e →
        let z := Real.exp ((p - e) / t)
        let P := cfc (Real.softTruncation t m) (A - (p : ℂ) • 1)
        0 < z ∧ z ≤ 1 ∧
          ‖P.submatrix insert insert - Z (z : ℂ)‖ ≤ xi ∧
          ‖P - Zphys (z : ℂ)‖ ≤ xi := by
  classical
  intro A sigma0 insert eJ W base order bond
  let g := intervalBondRestriction (L := N + 1) l r h
  have hgs (i : Fin N) : Entropy.IsSupportedOn (n := fun _ : Fin (N + 1) ↦ q)
      (g i) {i.castSucc, i.succ} := by
    apply (intervalBondRestriction_supported (L := N + 1) (q := q) l r h hs i).mono
    intro j hj
    have hj' := mem_interval.mp hj
    simp only [Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]
    change j.val = i.val ∨ j.val = i.val + 1
    omega
  have hgb (i : Fin N) : 0 ≤ g i ∧ g i ≤ 1 :=
    intervalBondRestriction_bounds (L := N + 1) (q := q) l r h h0 h1 i
  have hsumg : (∑ i, g i) = A := sum_intervalBondRestriction (L := N + 1) l r h
  have hA : A.IsHermitian := by
    rw [← hsumg]
    exact isHermitian_sum _ (fun i _ ↦ (hgb i).1.posSemidef.isHermitian)
  let U := A - (e : ℂ) • 1
  have hU : U.IsHermitian := hA.sub (isHermitian_one.smul (by simp [isSelfAdjoint_iff]))
  have hmR : 0 < (m : ℝ) := Nat.cast_pos.mpr hm
  have ht : 0 < t := lt_of_lt_of_le (by positivity : 0 < 3 * (m : ℝ)) hscale
  have hb := softHeat_base_bounds
  have hbasePos : 0 < base := hb.1
  have hbudget := Real.exponential_geometric_tail_order (N : ℝ) W base xi
    (by dsimp only [W]; positivity) hb.1 hb.2 hxi
  change 0 < order ∧ W * (Real.exp ((N : ℝ) ^ 2 * base ^ order) - 1) ≤ xi at hbudget
  let delta := Real.exp ((N : ℝ) ^ 2 * base ^ order) - 1
  have hdelta : 0 ≤ delta := sub_nonneg.mpr (Real.one_le_exp
    (mul_nonneg (sq_nonneg (N : ℝ)) (pow_nonneg hbasePos.le order)))
  have htime (a : Fin (m + 1)) : 0 ≤ (a.val : ℝ) / t ∧ (a.val : ℝ) / t ≤ 1 / 3 := by
    refine ⟨by positivity, (div_le_iff₀ ht).mpr ?_⟩
    have ha : (a.val : ℝ) ≤ m := by exact_mod_cast Nat.le_of_lt_succ a.isLt
    linarith only [ha, hscale]
  let heat := fun a : Fin (m + 1) ↦ NormedSpace.exp (-(((a.val : ℝ) / t) • U))
  have hheat (a : Fin (m + 1)) : (heat a).IsHermitian :=
    (hU.smul (IsSelfAdjoint.all ((a.val : ℝ) / t))).neg.isSelfAdjoint.exp.isHermitian
  have hheatSupport (a : Fin (m + 1)) :
      Entropy.IsSupportedOn (n := fun _ : Fin (N + 1) ↦ q)
        (heat a) (interval (N + 1) l r) := by
    let V := QuantumCircuit.supportedOperators q
      (interval (N + 1) l r : Set (Fin (N + 1)))
    have hAs : A ∈ V := QuantumCircuit.mem_supportedOperators_of_isSupportedOn
      (isSupportedOn_sum_internal_bonds (N + 1) q l r h hs)
    have hUs : U ∈ V := V.sub_mem hAs
      (V.smul_mem _ (QuantumCircuit.one_mem_supportedOperators _))
    dsimp only [heat]
    rw [← neg_smul, hU.exp_smul_eq_cfc]
    exact QuantumCircuit.isSupportedOn_of_mem_supportedOperators
      (QuantumCircuit.cfc_mem_supportedOperators _ hUs)
  have hglobal (a : Fin (m + 1)) :
      ∃ B : Fin (N + 1) → MPOTensor q ((order ^ 2 * q ^ order) * 2),
        (MPOTensor.traceChainOperator B 1).IsHermitian ∧
          ‖heat a - MPOTensor.traceChainOperator B 1‖ ≤ delta := by
    obtain ⟨B, hB⟩ := exists_shifted_heat_mpo (N := N) (q := q) (r := order)
      (by omega) hbudget.1 g hgs
      (fun i ↦ (hgb i).1.posSemidef.isHermitian)
      (fun i ↦ (CStarAlgebra.norm_le_one_iff_of_nonneg (g i) (hgb i).1).mpr (hgb i).2)
      e ((a.val : ℝ) / t) (hlo.trans_eq hsumg.symm) (htime a).1
      ((mul_le_mul_of_nonneg_left
        (sub_le_sub_right (Real.exp_le_exp.mpr (htime a).2) 1) (by norm_num)).trans hb.2.le)
    have hErr : ‖heat a - MPOTensor.traceChainOperator B 1‖ ≤ delta := by
      change ‖NormedSpace.exp (-(((a.val : ℝ) / t) •
        ((∑ i, g i) - (e : ℂ) • 1))) - _‖ ≤ _ at hB
      rw [hsumg] at hB
      refine hB.trans ?_
      have hba : 0 ≤ 2 * (Real.exp ((a.val : ℝ) / t) - 1) :=
        mul_nonneg (by norm_num) (sub_nonneg.mpr (Real.one_le_exp (htime a).1))
      have hbaseBound : 2 * (Real.exp ((a.val : ℝ) / t) - 1) ≤ base :=
        mul_le_mul_of_nonneg_left
          (sub_le_sub_right (Real.exp_le_exp.mpr (htime a).2) 1) (by norm_num)
      exact sub_le_sub_right (Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hba hbaseBound order)
          (sq_nonneg (N : ℝ)))) 1
    exact MPOTensor.exists_hermitian_traceChainOperator_approximation
      (by omega) (hheat a) B hErr
  let sites : Fin (r - l) → Fin (N + 1) := fun u ↦ (eJ u).val
  have hsites : Function.Injective sites := Subtype.val_injective.comp eJ.injective
  have hnative (a : Fin (m + 1)) :
      ∃ (B : Fin (r - l) → MPOTensor q ((order ^ 2 * q ^ order) * 2))
        (C : Matrix (Fin ((order ^ 2 * q ^ order) * 2))
          (Fin ((order ^ 2 * q ^ order) * 2)) ℂ),
        (MPOTensor.traceChainOperator B C).IsHermitian ∧
          heat a = QuantumCircuit.embedOp sites ((heat a).submatrix insert insert) ∧
          ‖(heat a).submatrix insert insert - MPOTensor.traceChainOperator B C‖ ≤ delta := by
    obtain ⟨B, hBH, hErr⟩ := hglobal a
    obtain ⟨Bcore, C, hZ, _hZphys, hRecon, hNativeErr, _hPlacedErr⟩ :=
      exists_native_interval_slice_of_mpo_approximation hq hlr hrL (heat a)
        (hheatSupport a) B hBH delta hErr
    exact ⟨Bcore, C, hZ, hRecon, hNativeErr⟩
  choose Binput Cinput hinputHerm hinputRecon hinputErr using hnative
  obtain ⟨Acore, Cbase, hrepr⟩ :=
    MPOTensor.exists_traceChainOperator_common_linearCombination Binput Cinput
  let C : Fin (m + 1) → Matrix (Fin bond) (Fin bond) ℂ :=
    fun a ↦ (Real.softTruncationHeatCoefficient t m a.val : ℂ) • Cbase a
  refine ⟨Acore, C, ?_⟩
  intro Z Zphys
  have hreprZ (z : ℂ) : Z z = ∑ a : Fin (m + 1),
      ((Real.softTruncationHeatCoefficient t m a.val : ℂ) * z ^ a.val) •
        MPOTensor.traceChainOperator (Binput a) (Cinput a) := by
    simpa only [Z, C, smul_smul, mul_comm] using
      (hrepr (fun a ↦ (Real.softTruncationHeatCoefficient t m a.val : ℂ) * z ^ a.val)).symm
  have hZH (z : ℝ) : (Z (z : ℂ)).IsHermitian := by
    rw [hreprZ]
    exact isHermitian_sum _ (fun a _ ↦ (hinputHerm a).smul (by simp [isSelfAdjoint_iff]))
  refine ⟨fun z ↦ ⟨hZH z, ?_⟩, ?_⟩
  · have hplaced : (QuantumCircuit.embedOp sites (Z (z : ℂ))).IsHermitian :=
      (QuantumCircuit.embedOp_conjTranspose sites _).trans
        (congrArg (QuantumCircuit.embedOp sites) (hZH z).eq)
    simpa only [Zphys, QuantumCircuit.embedOp_embedOp Subtype.val_injective,
      sites, Function.comp_def] using hplaced
  intro p hp z P
  have hz : 0 < z := Real.exp_pos _
  have hz1 : z ≤ 1 := Real.exp_le_one_iff.mpr
    (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hp) ht.le)
  have hsoft : P = ∑ a : Fin (m + 1),
      ((Real.softTruncationHeatCoefficient t m a.val : ℂ) * (z : ℂ) ^ a.val) • heat a := by
    change cfc (Real.softTruncation t m) (A - (p : ℂ) • 1) = _
    have hAP : (A - (p : ℂ) • 1).IsHermitian :=
      hA.sub (isHermitian_one.smul (by simp [isSelfAdjoint_iff]))
    have hexpansion := hAP.cfc_softTruncation_eq_sum_heat t m
    rw [← Fin.sum_univ_eq_sum_range] at hexpansion
    rw [hexpansion]
    apply Finset.sum_congr rfl
    intro a _ha
    rw [heat_shift_to_fixed_center A e p t a.val]
    simp only [heat, U, z, smul_smul, ← Complex.coe_smul,
      Complex.ofReal_pow]
  have hsoftNative : P.submatrix insert insert = ∑ a : Fin (m + 1),
      ((Real.softTruncationHeatCoefficient t m a.val : ℂ) * (z : ℂ) ^ a.val) •
        (heat a).submatrix insert insert := by
    ext sigma tau
    have hentry := congrArg (fun X ↦ X (insert sigma) (insert tau)) hsoft
    simpa only [Matrix.submatrix_apply, Matrix.sum_apply, Matrix.smul_apply] using hentry
  have hcoeff (a : Fin (m + 1)) :
      ‖(Real.softTruncationHeatCoefficient t m a.val : ℂ) * (z : ℂ) ^ a.val‖ ≤
        |Real.softTruncationHeatCoefficient t m a.val| := by
    simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hz]
    exact mul_le_of_le_one_right (abs_nonneg _)
      (pow_le_one₀ hz.le hz1)
  have hNativeErr : ‖P.submatrix insert insert - Z (z : ℂ)‖ ≤ xi := by
    rw [hsoftNative, hreprZ, ← Finset.sum_sub_distrib]
    simp only [← smul_sub]
    have hc := Real.sum_abs_softTruncationHeatCoefficient_le t m ht.le
    rw [← Fin.sum_univ_eq_sum_range] at hc
    calc
      _ ≤ ∑ a : Fin (m + 1),
          ‖((Real.softTruncationHeatCoefficient t m a.val : ℂ) * (z : ℂ) ^ a.val) •
            ((heat a).submatrix insert insert -
              MPOTensor.traceChainOperator (Binput a) (Cinput a))‖ := norm_sum_le _ _
      _ ≤ ∑ a : Fin (m + 1), |Real.softTruncationHeatCoefficient t m a.val| * delta := by
        apply Finset.sum_le_sum
        intro a _ha
        rw [norm_smul]
        exact mul_le_mul (hcoeff a) (hinputErr a) (norm_nonneg _) (abs_nonneg _)
      _ = (∑ a : Fin (m + 1), |Real.softTruncationHeatCoefficient t m a.val|) * delta :=
        (Finset.sum_mul _ _ _).symm
      _ ≤ W * delta := mul_le_mul_of_nonneg_right hc hdelta
      _ ≤ xi := hbudget.2
  let E := QuantumCircuit.embedOpLinearMap (d := q) sites
  have hRecon : P = E (P.submatrix insert insert) := by
    rw [hsoftNative, map_sum]
    simp only [map_smul]
    rw [hsoft]
    apply Finset.sum_congr rfl
    intro a _ha
    exact congrArg (fun X ↦
      ((Real.softTruncationHeatCoefficient t m a.val : ℂ) * (z : ℂ) ^ a.val) • X)
      (hinputRecon a)
  have hDifference : P - QuantumCircuit.embedOp sites (Z (z : ℂ)) =
      QuantumCircuit.embedOp sites (P.submatrix insert insert - Z (z : ℂ)) := by
    exact (congrArg (fun X ↦ X - QuantumCircuit.embedOp sites (Z (z : ℂ))) hRecon).trans
      (QuantumCircuit.embedOp_sub sites (P.submatrix insert insert) (Z (z : ℂ))).symm
  have hPlacedErr : ‖P - QuantumCircuit.embedOp sites (Z (z : ℂ))‖ ≤ xi := by
    rw [hDifference]
    exact (QuantumCircuit.norm_embedOp_le sites hsites _).trans hNativeErr
  exact ⟨hz, hz1, hNativeErr, by
    simpa only [Zphys, QuantumCircuit.embedOp_embedOp Subtype.val_injective,
      sites, Function.comp_def] using hPlacedErr⟩

end TNLean.MPS.AreaLaw.ALVV
