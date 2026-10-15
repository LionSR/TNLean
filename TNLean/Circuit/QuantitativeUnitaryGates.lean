/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Circuit.Gates.TwoSiteUniversality
import TNLean.Algebra.IsometryUnitaryExtension

/-!
# Quantitative synthesis by neighboring two-qudit gates

The synthesis in `UnitaryGates` can be counted explicitly. A controlled
single-site two-level operation with at most `k` controls costs at most
`4 * n * 3 ^ k` neighboring two-qudit gates. Combining this estimate with
Givens elimination gives a polynomial bound in the Hilbert-space dimension.
The decomposition is an exact matrix equality, including the global phase,
and uses no auxiliary sites.

This is a quantitative refinement of the synthesis used in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`; it is a derived result,
not a theorem quoted from arXiv:2508.08160.
-/

open QuantumCircuit

open Matrix
open scoped BigOperators ComplexConjugate

namespace QuantumCircuit

variable {d n : ℕ}

/-- Every two-level rotation or phase on `n` sites has an exact
neighboring-pair decomposition of length at most
`(2 * n + 1) * (4 * n * 3 ^ n)`. No auxiliary sites are added.
Derived synthesis estimate for Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem isPairProduct_twoLevel_le_exponential (hd : 0 < d) (hn : 2 ≤ n) :
    ∀ a b : (Fin n → Fin d), a ≠ b → ∀ g, IsSpecialTwo g →
      IsPairProduct d n ((2 * n + 1) * (4 * n * 3 ^ n)) (twoLevel a b g) :=
  isPairProduct_twoLevel_of_ctrlOp (isPairProduct_ctrlOp_le_exponential hd hn n)

/-- Explicit neighboring-pair gate count obtained from controlled rotations
and Givens elimination. Derived synthesis estimate for Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
def unitaryGateCount (d n : ℕ) : ℕ :=
  2 * n + 3 * (d ^ n) * (d ^ n) * ((2 * n + 1) * (4 * n * 3 ^ n))

/-- Every unitary on `n ≥ 2` sites admits a neighboring two-qudit circuit
with the explicit gate count `unitaryGateCount d n`. The circuit agrees
with the unitary as a matrix, including its global phase, on all inputs,
and adds no auxiliary sites. Derived synthesis theorem for Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem isPairProduct_unitaryGateCount (hd : 0 < d) (hn : 2 ≤ n) :
    ∀ X : Matrix ((Fin n → Fin d)) ((Fin n → Fin d)) ℂ,
      X ∈ unitary (Matrix ((Fin n → Fin d)) ((Fin n → Fin d)) ℂ) →
        IsPairProduct d n (unitaryGateCount d n) X := by
  let K₂ := (2 * n + 1) * (4 * n * 3 ^ n)
  have hK₂ := isPairProduct_twoLevel_le_exponential hd hn
  set m := Fintype.card ((Fin n → Fin d))
  have hm : 0 < m := Fintype.card_pos_iff.mpr ⟨fun _ => ⟨0, hd⟩⟩
  have hcost : unitaryGateCount d n = 2 * n + 3 * m * m * K₂ := by
    simp only [unitaryGateCount, m, K₂, Fintype.card_fun, Fintype.card_fin]
  rw [hcost]
  intro X hX
  obtain ⟨μ, hμ⟩ := IsAlgClosed.exists_pow_nat_eq X.det hm
  have hdetn : ‖X.det‖ = 1 := by
    have h := congrArg det (Unitary.star_mul_self_of_mem hX)
    rw [det_mul, det_one, star_eq_conjTranspose, det_conjTranspose, Complex.star_def,
      Complex.conj_mul'] at h
    exact_mod_cast (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp
      (by exact_mod_cast h)
  have hμn : ‖μ‖ = 1 := by
    have h : ‖μ‖ ^ m = 1 := by rw [← norm_pow, hμ, hdetn]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hm.ne').mp h
  have hμ0 : μ ≠ 0 := fun h => by simp [h] at hμn
  set X' := μ⁻¹ • X with hX'
  have hX'u : X' ∈ unitary (Matrix ((Fin n → Fin d)) ((Fin n → Fin d)) ℂ) := by
    have hu := isPairProduct_smul_one (d := d) hd hn (μ := μ⁻¹) (by simp [hμn])
    have : X' = (μ⁻¹ • (1 : Matrix ((Fin n → Fin d)) ((Fin n → Fin d)) ℂ)) * X := by
      rw [hX', smul_mul_assoc, Matrix.one_mul]
    rw [this]
    exact Submonoid.mul_mem _ hu.mem_unitary hX
  have hX'det : X'.det = 1 := by
    rw [hX', det_smul, inv_pow, hμ, inv_mul_cancel₀]
    intro h; rw [h] at hdetn; simp at hdetn
  obtain ⟨l, hl, hlg, hlX⟩ := isTwoLevelWord_of_det_eq_one hX'u hX'det
  have hprod : IsPairProduct d n (l.length * K₂)
      (l.map fun p => twoLevel p.1 p.2.1 p.2.2).prod := by
    have := IsPairProduct.list_prod (K := K₂) (l.map fun p => twoLevel p.1 p.2.1 p.2.2)
      (fun Y hY => by
        obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hY
        exact hK₂ _ _ (hlg p hp).1 _ (hlg p hp).2)
    simpa using this
  have hXeq : X = (μ • (1 : Matrix ((Fin n → Fin d)) ((Fin n → Fin d)) ℂ)) * X' := by
    rw [hX', smul_mul_assoc, Matrix.one_mul, smul_smul, mul_inv_cancel₀ hμ0, one_smul]
  rw [hXeq, hlX]
  refine ((isPairProduct_smul_one hd hn hμn).mul hprod).mono ?_
  have : l.length * K₂ ≤ 3 * m * m * K₂ := Nat.mul_le_mul_right _ hl
  omega


/-- The explicit neighboring-pair synthesis count is at most
`38 * (d ^ n) ^ 6` for `d ≥ 2`. Thus its cost is polynomial in the
Hilbert-space dimension. Derived estimate for Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem unitaryGateCount_le_hilbertDimension_pow (hd : 2 ≤ d) :
    unitaryGateCount d n ≤ 38 * (d ^ n) ^ 6 := by
  let m := d ^ n
  have hm : 1 ≤ m := Nat.one_le_pow n d (by omega)
  have hnm : n ≤ m := Nat.lt_two_pow_self.le.trans (Nat.pow_le_pow_left hd n)
  have hthree : 3 ^ n ≤ m ^ 2 := by
    have hbase : 3 ≤ d ^ 2 := by nlinarith
    simpa only [m, ← pow_mul, Nat.mul_comm] using Nat.pow_le_pow_left hbase n
  have hpower : m ≤ m ^ 6 := by
    simpa using Nat.pow_le_pow_right (show 0 < m by omega) (show 1 ≤ 6 by norm_num)
  calc
    unitaryGateCount d n ≤
        2 * m + 3 * m * m * ((3 * m) * (4 * m * m ^ 2)) := by
      dsimp only [unitaryGateCount]
      change 2 * n + 3 * m * m * ((2 * n + 1) * (4 * n * 3 ^ n)) ≤ _
      gcongr
      omega
    _ = 2 * m + 36 * m ^ 6 := by ring
    _ ≤ 38 * m ^ 6 := by nlinarith

/-- Every unitary on `n ≥ 2` sites of local dimension `d ≥ 2` is an exact
product of at most `38 * (d ^ n) ^ 6` neighboring two-qudit gates, with no
auxiliary sites, retaining the exact global phase. Derived synthesis theorem
for Section 5 of `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem isPairProduct_le_hilbertDimension_pow (hd : 2 ≤ d) (hn : 2 ≤ n)
    {X : Matrix ((Fin n → Fin d)) ((Fin n → Fin d)) ℂ}
    (hX : X ∈ unitary (Matrix ((Fin n → Fin d)) ((Fin n → Fin d)) ℂ)) :
    IsPairProduct d n (38 * (d ^ n) ^ 6) X := by
  exact (isPairProduct_unitaryGateCount (by omega) hn X hX).mono
    (unitaryGateCount_le_hilbertDimension_pow hd)

/-- An isometry placed on selected input basis states extends to a full
unitary admitting an exact neighboring-pair circuit with at most
`38 * (d ^ n) ^ 6` gates. This derives both the circuit and its prescribed
columns; no synthesis witness is assumed. Derived leaf-construction theorem
for Section 5 of `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem exists_isPairProduct_apply_embedding_eq {κ : Type*} [DecidableEq κ]
    (hd : 2 ≤ d) (hn : 2 ≤ n) {V : Matrix ((Fin n → Fin d)) κ ℂ}
    (hV : V.IsIsometry) (e : κ ↪ (Fin n → Fin d)) :
    ∃ U : Matrix ((Fin n → Fin d)) ((Fin n → Fin d)) ℂ,
      IsPairProduct d n (38 * (d ^ n) ^ 6) U ∧
      ∀ u k, U u (e k) = V u k := by
  obtain ⟨U, hU, hUV⟩ := Matrix.exists_mem_unitaryGroup_apply_embedding_eq hV e
  exact ⟨U, isPairProduct_le_hilbertDimension_pow hd hn hU, hUV⟩

end QuantumCircuit
